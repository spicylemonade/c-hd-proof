import Frontier.CHD.RamLevel
import Frontier.CHD.RamSlot
import Frontier.CHD.RamMark
import Frontier.RAMWP

/-!
# RamSpineCode — RAM text of the spine phases owned by agent-08 (scratch, B-L4)

Level `l ≥ 1` in register `lvl`; the child level is `lvl - 1`.  Arrays per `RamLevel`:
groups `sp.gm/gs/gl/gp/gpos/g`, count `sp.np`; rows `S`, `U`, `W`, `Q`; `sp.inU` (membership in
this call's `U`), `sp.mk` (marked groups of this iteration, a row of group indices with length
`sp.mk.len[lvl]`), `sp.xm` (the mark bitmap used to deduplicate the child's frontier).
Label comparisons go through agent-02's B-LAB (`loadLab`, `ltB`, `cmp`) on the bound slots of
`RamSlot` (`slotBi l` = the pull bound `B_i`).
-/

namespace Frontier.CHD.RamSpine

open Frontier.RAM WExpr Stmt Frontier.CHD.RamLevel

/-- `lvl * n + e` (current row) -/
def cr (e : WExpr) : WExpr := add (mul (var "lvl") (var "n")) e
/-- `(lvl - 1) * n + e` (child row) -/
def chr (e : WExpr) : WExpr := add (mul (sub (var "lvl") (lit 1)) (var "n")) e

/-- `x := x + 1` -/
def incr (x : String) : Stmt := wset x (add (var x) (lit 1))

/-! ## BM.11–12: expansion of the pulled keys by the groups of pulled pivots

The pulled keys `ks` are the prefix `[0, sp.np0)` of the child's `S` row (written by `dsPull`).
They are marked (`sp.xm[x] = 1`); for each pulled `x` that is the current pivot of its group `j`,
every member `v` of group `j` with `d[v] < B_i` and no mark is appended.  Groups are disjoint and
distinct pulled pivots have distinct groups, so a member can only collide with a pulled key: the
marks never change during the scans.  Finally the marks of the pulled prefix are cleared. -/
def expandGroup (ltBi : Stmt) : Stmt :=
  seq (wset "sp.q" (load "sp.gs" (cr (var "sp.j"))))
  (seq (wset "sp.qe" (add (var "sp.q") (load "sp.gl" (cr (var "sp.j")))))
  (.while (lt (var "sp.q") (var "sp.qe"))
     (seq (wset "px" (load "sp.gm" (cr (var "sp.q"))))
     (seq ltBi
     (seq (ite (var "sp.lt")
             (ite (load "sp.xm" (var "px")) skip
               (seq (wset "lvl" (sub (var "lvl") (lit 1)))
               (seq (RamLevel.rowAppend "S" "S.len" (var "px"))
                    (wset "lvl" (add (var "lvl") (lit 1))))))
             skip)
          (incr "sp.q"))))))

/-- The scan over the pulled prefix: groups of pulled pivots. -/
def expandScan (ltBi : Stmt) : Stmt :=
  seq (wset "sp.i" (lit 0))
  (.while (lt (var "sp.i") (var "sp.np0"))
     (seq (wset "lvl" (sub (var "lvl") (lit 1)))
     (seq (RamLevel.rowGet "px" "S" (var "sp.i"))
     (seq (wset "lvl" (add (var "lvl") (lit 1)))
     (seq (wset "sp.j" (load "sp.g" (cr (var "px"))))
     (seq (ite (var "sp.j")
             (seq (wset "sp.j" (sub (var "sp.j") (lit 1)))
                  (ite (eq (load "sp.gp" (cr (var "sp.j"))) (var "px")) (expandGroup ltBi) skip))
             skip)
          (incr "sp.i")))))))

/-- BM.11–12. -/
def expand (ltBi : Stmt) : Stmt :=
  seq (wset "sp.np0" (load "S.len" (sub (var "lvl") (lit 1))))
  (seq (wset "lvl" (sub (var "lvl") (lit 1)))
  (seq (RamMark.markRow "sp.xm" "S" "sp.np0" 1)          -- mark the pulled keys (child row)
  (seq (wset "lvl" (add (var "lvl") (lit 1)))
  (seq (expandScan ltBi)
  (seq (wset "lvl" (sub (var "lvl") (lit 1)))
  (seq (RamMark.markRow "sp.xm" "S" "sp.np0" 0)          -- clear them
       (wset "lvl" (add (var "lvl") (lit 1)))))))))

/-! ## BM.15–18: the child's `U_i` leaves `D` and its groups; groups whose pivot left are marked

`dsDelB` (B-L3, procedure) deletes the keys of the child's `U` row from the level-`lvl` store.
For each `u ∈ U_i` in a group `j`: `gDel` removes it; if `u` was the pivot of `j`, the group is
marked (`sp.mk` row; groups that end up empty are skipped at BM.23). -/
def removeU (dsDelB : Stmt) (gDelS : Stmt) : Stmt :=
  seq dsDelB
  (seq (wstore "sp.mk.len" (var "lvl") (lit 0))
  (seq (wset "sp.i" (lit 0))
       (.while (lt (var "sp.i") (load "U.len" (sub (var "lvl") (lit 1))))
          (seq (wset "px" (load "U" (chr (var "sp.i"))))
          (seq (wset "sp.j" (load "sp.g" (cr (var "px"))))
          (seq (ite (var "sp.j")
                  (seq (wset "sp.j" (sub (var "sp.j") (lit 1)))
                  (seq (wset "sp.pv" (eq (load "sp.gp" (cr (var "sp.j"))) (var "px")))
                  (seq gDelS
                       (ite (var "sp.pv")
                          (seq (wstore "sp.mk" (cr (load "sp.mk.len" (var "lvl"))) (var "sp.j"))
                               (wstore "sp.mk.len" (var "lvl")
                                 (add (load "sp.mk.len" (var "lvl")) (lit 1))))
                          skip))))
                  skip)
               (incr "sp.i")))))))

/-! ## BM.24: `U := U ∪ U_i`, `B' := B'_i` -/

/-- Append the child's `U` row to this level's `U` row and set the `inU` bits; copy the child's
returned bound into this level's `B'` slot (`copySlot` from B-LAB/RamSlot). -/
def appendU (copyBp : Stmt) : Stmt :=
  seq (wset "sp.i" (lit 0))
  (seq (.while (lt (var "sp.i") (load "U.len" (sub (var "lvl") (lit 1))))
     (seq (wset "px" (load "U" (chr (var "sp.i"))))
     (seq (wstore "U" (cr (load "U.len" (var "lvl"))) (var "px"))
     (seq (wstore "U.len" (var "lvl") (add (load "U.len" (var "lvl")) (lit 1)))
     (seq (wstore "sp.inU" (cr (var "px")) (lit 1))
          (incr "sp.i"))))))
       copyBp)

/-! ## BM.19–21: the window scan

For `u ∈ U_i` (child's `U` row): scan the sorted CSR range of `u` from `sp.ptr[u]` while the
candidate `d[u] ⊕ e` is `< B` (B-LAB's `candB` with the bound slot of this level, bit `sp.lt`);
each scanned edge is relaxed (`relaxW`: B-LAB `relaxBM`-core with insertion into `D` when valid
and `B_i ≤ cand`, parameter); finally `sp.ptr[u] := p`.  By the pointer invariant the scanned
edges are exactly the window edges `B_i ≤ cand < B` (BMCost `LoopC.step`'s list `L'`). -/
def windowScan (candLtB : Stmt) (relaxWin : Stmt) : Stmt :=
  seq (wset "sp.i" (lit 0))
  (.while (lt (var "sp.i") (load "U.len" (sub (var "lvl") (lit 1))))
     (seq (wset "ru" (load "U" (chr (var "sp.i"))))
     (seq (wset "sp.p" (load "sp.ptr" (var "ru")))
     (seq (wset "sp.pe" (load "gSt" (add (var "ru") (lit 1))))
     (seq (wset "sp.go" (lit 1))
     (seq (.while (var "sp.go")
            (seq (ite (lt (var "sp.p") (var "sp.pe"))
                    (seq (wset "re" (var "sp.p")) candLtB)
                    (wset "sp.lt" (lit 0)))
            (ite (var "sp.lt")
               (seq relaxWin (incr "sp.p"))
               (wset "sp.go" (lit 0)))))
     (seq (wstore "sp.ptr" (var "ru") (var "sp.p"))
          (incr "sp.i"))))))))

/-! ## BM.23: re-selection of the marked groups

For each marked group `j` that is still nonempty: the least current label among its members
(B-LAB's table–table compare `cmpTT`, inputs `tt.ra`, `tt.rb`, bit `lab.bit`) becomes the new
pivot, which is inserted into `D` (`dsIns`, B-L3, vertex in `px`, key `d[px]`). -/
def reselect (cmpTT dsIns : Stmt) : Stmt :=
  seq (wset "sp.i" (lit 0))
  (.while (lt (var "sp.i") (load "sp.mk.len" (var "lvl")))
     (seq (wset "sp.j" (load "sp.mk" (cr (var "sp.i"))))
     (seq (ite (load "sp.gl" (cr (var "sp.j")))
             (seq (wset "sp.q" (load "sp.gs" (cr (var "sp.j"))))
             (seq (wset "sp.qe" (add (var "sp.q") (load "sp.gl" (cr (var "sp.j")))))
             (seq (wset "sp.b" (load "sp.gm" (cr (var "sp.q"))))
             (seq (incr "sp.q")
             (seq (.while (lt (var "sp.q") (var "sp.qe"))
                    (seq (wset "tt.ra" (load "sp.gm" (cr (var "sp.q"))))
                    (seq (wset "tt.rb" (var "sp.b"))
                    (seq cmpTT
                    (seq (ite (var "lab.bit") (wset "sp.b" (var "tt.ra")) skip)
                         (incr "sp.q"))))))
             (seq (wstore "sp.gp" (cr (var "sp.j")) (var "sp.b"))
             (seq (wset "px" (var "sp.b")) dsIns)))))))
             skip)
          (incr "sp.i"))))

/-! ## One iteration of the main loop (BM.10–BM.24) -/

/-- The procedure numbers of the fragments called by the spine. -/
def P_bmssp : ℕ := 0
def P_dsPull : ℕ := 1
def P_dsMerge : ℕ := 2
def P_dsDelB : ℕ := 3
def P_dsIns : ℕ := 4
def P_cmpTT : ℕ := 5

/-- The loop body: pull, expand, recursive call, merge, FIX-STALE deletion / group removal,
window scan, re-selection, `U` append.  Fragments are procedures; label tests are statements
supplied by B-LAB (`ltBi` = `[d[px] < B_i]`, `candLtB` = `[d[ru] ⊕ re < B]`, `relaxWin`). -/
def loopBody (ltBi candLtB relaxWin copyChild copyBp gDelS : Stmt) : Stmt :=
  seq (call P_dsPull)                       -- BM.10: keys → child S row, B_i → slot B_i[lvl]
  (seq (expand ltBi)                        -- BM.11–12
  (seq copyChild                            -- child slots: B[l-1] := B_i[l], B_low[l-1] := B'[l]
  (seq (wset "lvl" (sub (var "lvl") (lit 1)))
  (seq (call P_bmssp)                       -- BM.13
  (seq (wset "lvl" (add (var "lvl") (lit 1)))
  (seq (call P_dsMerge)                     -- BM.14
  (seq (removeU (call P_dsDelB) gDelS)      -- BM.15–18
  (seq (windowScan candLtB relaxWin)        -- BM.19–21
  (seq (reselect (call P_cmpTT) (call P_dsIns)) -- BM.23
       (appendU copyBp))))))))))            -- BM.24

/-! ## Specifications of BM.11–12 -/

section expandSpec

variable {V : Type} {ops : VOps V}

/-- The scratch registers of the expansion. -/
def expRegs : List String := ["sp.q", "sp.qe", "px", "sp.j", "sp.i", "sp.np0", "lvl", "mk.i", "sp.lt"]

/-- The registers written by one group expansion (besides the label test's). -/
def grpRegs : List String := ["sp.q", "sp.qe", "px", "lvl"]

theorem grpRegs_sub (LW : List String) : grpRegs ++ LW ⊆ expRegs ++ LW := by
  intro a ha
  rcases List.mem_append.1 ha with h | h
  · apply List.mem_append_left
    simp only [grpRegs, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> simp [expRegs]
  · exact List.mem_append_right _ h

/-- The label-test interface for `sp.lt := [lt px]` (instantiated by B-LAB's `headLtB` with the
bound `B_i` in a register block): `KR` is the key representation (label table + bound block),
stable under the expansion's own writes. -/
structure LtI (ops : VOps V) (ltBi : Stmt) (KR : State V → Prop) (lt : ℕ → Prop)
    [DecidablePred lt] (C : ℕ) (LW LV : List String) : Prop where
  run : ∀ st, KR st → st.w "px" < st.w "n" →
    Runs ops ltBi st (fun r => r.w "sp.lt" = (if lt (st.w "px") then 1 else 0) ∧
    Unchanged st r [] [] LW LV ∧ st.cost ≤ r.cost ∧ r.cost ≤ st.cost + C ∧ KR r)
  frame : ∀ st r, KR st → Unchanged st r ["S", "S.len", "sp.xm"] [] (expRegs ++ LW) LV →
    st.cost ≤ r.cost → KR r
  lt_mem : "sp.lt" ∈ LW
  regs : ∀ a ∈ LW, a ∉ ["sp.q", "sp.qe", "px", "sp.j", "sp.i", "sp.np0", "lvl", "n", "mk.i"]

/-- The members of group `j` of level `l`, in segment order. -/
def mlist (st : State V) (l n j : ℕ) : List ℕ :=
  (List.range (gl st l n j)).map fun q => gmem st l n (gs st l n j + q)

end expandSpec

section grpFrame
variable {V : Type}

theorem GrpRep.of_eq {st st' : State V} {l n p : ℕ} {P : ℕ → Finset ℕ} {piv : ℕ → ℕ}
    (h : GrpRep st l n p P piv) (hwa : ∀ a ∈ grpArrs, st'.wa a = st.wa a)
    (hwl : ∀ a ∈ grpArrs, st'.wlen a = st.wlen a) : GrpRep st' l n p P piv := by
  have e1 := hwa "sp.gm" (by simp [grpArrs]); have e2 := hwa "sp.gs" (by simp [grpArrs])
  have e3 := hwa "sp.gl" (by simp [grpArrs]); have e4 := hwa "sp.gp" (by simp [grpArrs])
  have e5 := hwa "sp.gpos" (by simp [grpArrs]); have e6 := hwa "sp.g" (by simp [grpArrs])
  have gs' : ∀ j, gs st' l n j = gs st l n j := fun j => by simp only [gs, e2]
  have gl' : ∀ j, gl st' l n j = gl st l n j := fun j => by simp only [gl, e3]
  have gm' : ∀ q, gmem st' l n q = gmem st l n q := fun q => by simp only [gmem, e1]
  refine ⟨by rw [hwl _ (by simp [grpArrs])]; exact h.len_gm, by rw [hwl _ (by simp [grpArrs])]; exact h.len_gs,
    by rw [hwl _ (by simp [grpArrs])]; exact h.len_gl, by rw [hwl _ (by simp [grpArrs])]; exact h.len_gp,
    by rw [hwl _ (by simp [grpArrs])]; exact h.len_gpos, by rw [hwl _ (by simp [grpArrs])]; exact h.len_g,
    h.p_le, fun j hj => by rw [gs', gl']; exact h.seg j hj,
    fun j hj q hq => by rw [gl'] at hq; rw [gs', gm']; exact h.mem_lt j hj q hq,
    fun j hj q hq => by rw [gl'] at hq; rw [gs', gm', e5]; exact h.pos j hj q hq,
    fun j hj q hq => by rw [gl'] at hq; rw [gs', gm', e6]; exact h.memb j hj q hq,
    fun j hj => by rw [h.img j hj, gl']; apply Finset.image_congr; intro q _; simp only [gs', gm'],
    fun x hx => by rw [e6]; rcases h.nomemb x hx with h0 | ⟨j, hj, hg, hxP⟩
                   · exact Or.inl h0
                   · exact Or.inr ⟨j, hj, hg, hxP⟩,
    fun j hj => by rw [e4]; exact h.pivs j hj,
    fun j hj j' hj' hne => by rw [gs', gl', gs', gl']; exact h.disj j hj j' hj' hne⟩

end grpFrame

section expandGroupSpec

variable {V : Type} {ops : VOps V}

theorem mlist_length (st : State V) (l n j : ℕ) : (mlist st l n j).length = gl st l n j := by
  simp [mlist]

theorem mlist_get (st : State V) (l n j q : ℕ) (hq : q < (mlist st l n j).length) :
    (mlist st l n j)[q] = gmem st l n (gs st l n j + q) := by
  simp [mlist]

theorem unch_charge3 {V : Type} (r : State V) (wa va wr vr : List String) :
    Unchanged r (((r.charge 1).charge 1).charge 1) wa va wr vr :=
  ((Unchanged.charge r 1 _ _ _ _).trans (Unchanged.charge _ 1 _ _ _ _)).trans
    (Unchanged.charge _ 1 _ _ _ _)

theorem unch_charge2 {V : Type} (r : State V) (wa va wr vr : List String) :
    Unchanged r ((r.charge 1).charge 1) wa va wr vr :=
  (Unchanged.charge r 1 _ _ _ _).trans (Unchanged.charge _ 1 _ _ _ _)

theorem take_succ_filter {α : Type} (l : List α) (F : α → Prop) [DecidablePred F] {q : ℕ}
    (hq : q < l.length) :
    (l.take (q + 1)).filter (fun x => decide (F x)) =
      (l.take q).filter (fun x => decide (F x)) ++ (if F l[q] then [l[q]] else []) := by
  rw [List.take_succ, List.getElem?_eq_getElem hq, Option.toList_some, List.filter_append]
  by_cases h : F l[q] <;> simp [h]

theorem filter_take_lt {α : Type} (l : List α) (F : α → Prop) [DecidablePred F] {q : ℕ}
    (hq : q < l.length) (hF : F l[q]) :
    ((l.take q).filter (fun x => decide (F x))).length < (l.filter (fun x => decide (F x))).length := by
  have h1 := take_succ_filter l F hq
  rw [if_pos hF] at h1
  have h2 : ((l.take (q + 1)).filter (fun x => decide (F x))).length ≤
      (l.filter (fun x => decide (F x))).length :=
    ((List.take_sublist (q + 1) l).filter _).length_le
  rw [h1, List.length_append, List.length_singleton] at h2
  omega

/-- **One pulled group** (BM.12): the members `v` of group `j` with `lt v` and no mark are
appended to the child's `S` row, in segment order. -/
theorem expandGroup_spec {ltBi : Stmt} {KR : State V → Prop} {lt : ℕ → Prop} [DecidablePred lt]
    {C : ℕ} {LW LV : List String} (hI : LtI ops ltBi KR lt C LW LV) (st : State V) {l n p : ℕ}
    {P : ℕ → Finset ℕ} {piv : ℕ → ℕ} (hG : GrpRep st l n p P piv) (hl : st.w "lvl" = l)
    (hl1 : 1 ≤ l) (hn : st.w "n" = n) {j : ℕ} (hj : st.w "sp.j" = j) (hjp : j < p)
    {R : List ℕ} (hR : RowRep st "S" "S.len" n (l - 1) R) (mk : ℕ → Prop) [DecidablePred mk]
    (hroom : R.length + ((mlist st l n j).filter (fun v => lt v ∧ ¬ mk v)).length ≤ n)
    (hxm : ∀ x < n, st.wa "sp.xm" x = if mk x then 1 else 0) (hxml : n ≤ st.wlen "sp.xm")
    (hK : KR st) (hcap : (l + 1) * n < st.cap) (hc2 : 2 < st.cap) :
    Runs ops (expandGroup ltBi) st (fun r =>
      RowRep r "S" "S.len" n (l - 1) (R ++ (mlist st l n j).filter (fun v => lt v ∧ ¬ mk v)) ∧
      KR r ∧ r.w "lvl" = l ∧ r.w "n" = n ∧ r.w "sp.j" = j ∧
      Unchanged st r ["S", "S.len"] [] (grpRegs ++ LW) LV ∧ r.wlen = st.wlen ∧
      (∀ i, (i < (l - 1) * n ∨ l * n ≤ i) → r.wa "S" i = st.wa "S" i) ∧
      (∀ l', l' ≠ l - 1 → r.wa "S.len" l' = st.wa "S.len" l') ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + 2 + gl st l n j * (C + 10) + 1) := by
  have hgs := hG.seg j hjp
  have hn1 : n ≤ (l + 1) * n := Nat.le_mul_of_pos_left n (by omega)
  have hlnj : l * n + j < (l + 1) * n := row_index_lt (by have := hG.p_le; omega)
  have fln : l * n < st.cap := by omega
  have flnj : l * n + j < st.cap := by omega
  have hgsl : l * n + j < st.wlen "sp.gs" := by have := hG.len_gs; omega
  have hgll : l * n + j < st.wlen "sp.gl" := by have := hG.len_gl; omega
  have hFilt := fun q => ((mlist st l n j).take q).filter (fun v => lt v ∧ ¬ mk v)
  -- `sp.q := gs[l n + j]`
  have e1 : evalW st (load "sp.gs" (cr (var "sp.j"))) = some (gs st l n j) := by
    simp only [cr, evalW_load', evalW_add', evalW_mul', evalW_var, hl, hn, hj, Option.bind_some,
      fit_of_lt fln, fit_of_lt flnj, hgsl, ite_true]; rfl
  refine runs_seq (runs_wset e1 ?_)
  set st1 := (st.setW "sp.q" (gs st l n j)).charge 1 with hst1
  have e2 : evalW st1 (add (var "sp.q") (load "sp.gl" (cr (var "sp.j")))) =
      some (gs st l n j + gl st l n j) := by
    have f3 : gs st l n j + gl st l n j < st1.cap := by
      simp only [hst1, State.charge_cap, State.setW_cap]; omega
    simp only [cr, evalW_load', evalW_add', evalW_mul', evalW_var, hst1, State.charge_w,
      State.setW_w, State.charge_wa, State.setW_wa, State.charge_wlen, State.setW_wlen,
      State.charge_cap, State.setW_cap]
    simp (config := { decide := true }) only [ite_true, ite_false, hl, hn, hj, Option.bind_some,
      fit_of_lt fln, fit_of_lt flnj, hgll]
    rw [show st.wa "sp.gl" (l * n + j) = gl st l n j from rfl]
    exact fit_of_lt (by simpa [hst1] using f3)
  refine runs_seq (runs_wset e2 ?_)
  set st2 := (st1.setW "sp.qe" (gs st l n j + gl st l n j)).charge 1 with hst2
  have hU02 : Unchanged st st2 [] [] ["sp.q", "sp.qe"] [] :=
    ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      simp [hst2, hst1, State.setW, State.charge, hz.1, hz.2],
      fun _ _ => rfl, rfl, rfl⟩
  have hml : (mlist st l n j).length = gl st l n j := mlist_length st l n j
  have hsub02 : ["sp.q", "sp.qe"] ⊆ grpRegs ++ LW := by
    intro a ha
    apply List.mem_append_left
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> simp [grpRegs]
  have gsub := grpRegs_sub LW
  refine runs_while_nat (fun k r => ∃ q, k = gl st l n j - q ∧ q ≤ gl st l n j ∧
      r.w "sp.q" = gs st l n j + q ∧ r.w "sp.qe" = gs st l n j + gl st l n j ∧
      r.w "sp.j" = j ∧ r.w "lvl" = l ∧ r.w "n" = n ∧
      RowRep r "S" "S.len" n (l - 1) (R ++ ((mlist st l n j).take q).filter (fun v => lt v ∧ ¬ mk v)) ∧
      KR r ∧ Unchanged st r ["S", "S.len"] [] (grpRegs ++ LW) LV ∧ r.wlen = st.wlen ∧
      (∀ i, (i < (l - 1) * n ∨ l * n ≤ i) → r.wa "S" i = st.wa "S" i) ∧
      (∀ l', l' ≠ l - 1 → r.wa "S.len" l' = st.wa "S.len" l') ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + 2 + q * (C + 10)) _ ?_ (gl st l n j) st2
    ⟨0, by simp, Nat.zero_le _, by simp [hst2, hst1, State.setW, State.charge],
      by simp [hst2, hst1, State.setW, State.charge], by
        rw [hU02.wreg _ (by simp)]; exact hj, by rw [hU02.wreg _ (by simp)]; exact hl,
      by rw [hU02.wreg _ (by simp)]; exact hn,
      by simp only [List.take_zero, List.filter_nil, List.append_nil]
         exact hR.of_eq (st' := st2) rfl rfl rfl (fun _ _ => rfl),
      hI.frame st st2 hK (hU02.mono (by simp) (by simp) (fun a ha => gsub (hsub02 ha)) (by simp))
        (by simp only [hst2, hst1, State.charge_cost, State.setW_cost]; omega),
      hU02.mono (by simp) (by simp) hsub02 (by simp), rfl,
      fun _ _ => rfl, fun _ _ => rfl, by simp only [hst2, hst1, State.charge_cost, State.setW_cost]; omega,
      by simp only [hst2, hst1, State.charge_cost, State.setW_cost]; omega⟩
  rintro k r ⟨q, rfl, hq, hrq, hrqe, hrj, hrl, hrn, hRr, hKr, hUr, hwlr, hSr, hSLr, hcl, hch⟩
  have hcapr : r.cap = st.cap := hUr.cap
  refine ⟨if gs st l n j + q < gs st l n j + gl st l n j then 1 else 0, by
    rw [evalW_lt_of (by rw [evalW_var, hrq]) (by rw [evalW_var, hrqe]) (by omega)],
    fun hx => ?_, fun hx => ?_⟩
  · -- one more member
    have hqL : q < gl st l n j := by by_contra h; rw [if_neg (by omega)] at hx; exact hx rfl
    set v := gmem st l n (gs st l n j + q) with hv
    have hvn : v < n := hG.mem_lt j hjp q hqL
    have hgm : r.wa "sp.gm" = st.wa "sp.gm" := (hUr.warr "sp.gm" (by simp)).1
    have hxmr : r.wa "sp.xm" = st.wa "sp.xm" := (hUr.warr "sp.xm" (by simp)).1
    have hidx : l * n + (gs st l n j + q) < (l + 1) * n := row_index_lt (by omega)
    have hgml : l * n + (gs st l n j + q) < r.wlen "sp.gm" := by
      rw [hwlr]; have := hG.len_gm; omega
    have f1 : l * n < r.cap := by rw [hcapr]; omega
    have f2 : l * n + (gs st l n j + q) < r.cap := by rw [hcapr]; omega
    -- `px := gm[l n + q']`
    have ev : evalW (r.charge 1) (load "sp.gm" (cr (var "sp.q"))) = some v := by
      simp only [cr, evalW_load', evalW_add', evalW_mul', evalW_var, State.charge_w, State.charge_cap,
        State.charge_wlen, State.charge_wa, hrl, hrn, hrq, Option.bind_some, fit_of_lt f1,
        fit_of_lt f2, hgml, ite_true, hgm]; rfl
    refine runs_seq (runs_wset ev ?_)
    set r1 := ((r.charge 1).setW "px" v).charge 1 with hr1
    have hU1 : Unchanged r r1 [] [] ["px"] [] :=
      ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun z hz => by
        simp only [List.mem_singleton] at hz; simp [hr1, State.setW, State.charge, hz],
        fun _ _ => rfl, rfl, rfl⟩
    have hsubpx : ["px"] ⊆ grpRegs ++ LW := fun a ha => List.mem_append_left _ (by
      simp only [List.mem_singleton] at ha; subst ha; simp [grpRegs])
    have hK1 : KR r1 := hI.frame r r1 hKr (hU1.mono (by simp) (by simp) (fun a ha => gsub (hsubpx ha)) (by simp))
      (by simp only [hr1, State.charge_cost, State.setW_cost]; omega)
    -- the label test
    have hpxn : r1.w "px" < r1.w "n" := by
      have e1 : r1.w "px" = v := by simp [hr1, State.setW, State.charge]
      have e2 : r1.w "n" = n := by simp [hr1, State.setW, State.charge, hrn]
      rw [e1, e2]; exact hvn
    refine runs_seq ((hI.run r1 hK1 hpxn).mono ?_)
    rintro r2 ⟨hlt2, hU2, hc2l, hc2, hK2⟩
    have hpx1 : r1.w "px" = v := by simp [hr1, State.setW, State.charge]
    rw [hpx1] at hlt2
    have hU02 : Unchanged st r2 ["S", "S.len"] [] (grpRegs ++ LW) LV :=
      (hUr.trans (hU1.mono (by simp) (by simp) hsubpx (by simp))).trans
        (hU2.mono (by simp) (by simp) (List.subset_append_right _ _) (by simp))
    have hreg2 : ∀ z, z ∉ LW → z ≠ "px" → r2.w z = r.w z := by
      intro z hz hzp; rw [hU2.wreg z hz]; simp [hr1, State.setW, State.charge, hzp]
    have nLW : ∀ z ∈ ["sp.q", "sp.qe", "px", "sp.j", "sp.i", "sp.np0", "lvl", "n", "mk.i"], z ∉ LW :=
      fun z hz h => hI.regs z h hz
    have hpx2 : r2.w "px" = v := by rw [hU2.wreg "px" (nLW _ (by simp))]; exact hpx1
    have hl2 : r2.w "lvl" = l := by rw [hreg2 _ (nLW _ (by simp)) (by decide), hrl]
    have hn2 : r2.w "n" = n := by rw [hreg2 _ (nLW _ (by simp)) (by decide), hrn]
    have hq2 : r2.w "sp.q" = gs st l n j + q := by rw [hreg2 _ (nLW _ (by simp)) (by decide), hrq]
    have hwl2 : r2.wlen = st.wlen := by
      rw [show r2.wlen = r1.wlen from funext fun a => (hU2.warr a (by simp)).2]; exact hwlr
    have hcap2 : r2.cap = st.cap := hU02.cap
    have hRr2 : RowRep r2 "S" "S.len" n (l - 1)
        (R ++ ((mlist st l n j).take q).filter (fun v => lt v ∧ ¬ mk v)) := by
      have e1 := hU2.warr "S" (by simp); have e2 := hU2.warr "S.len" (by simp)
      exact (hRr.of_eq (st' := r1) rfl rfl rfl (fun _ _ => rfl)).of_eq e1.2 e2.2 (by rw [e2.1])
        (fun i _ => by rw [e1.1])
    have hxm2 : r2.wa "sp.xm" v = if mk v then 1 else 0 := by
      rw [(hU2.warr "sp.xm" (by simp)).1, show r1.wa = r.wa from rfl, hxmr]; exact hxm v hvn
    have hmq : (mlist st l n j)[q]'(by rw [hml]; exact hqL) = v := mlist_get st l n j q _
    -- the conditional append
    have hcase : Runs ops (seq (ite (var "sp.lt") (ite (load "sp.xm" (var "px")) skip
        (seq (wset "lvl" (sub (var "lvl") (lit 1))) (seq (RamLevel.rowAppend "S" "S.len" (var "px"))
          (wset "lvl" (add (var "lvl") (lit 1)))))) skip) (incr "sp.q")) r2
        (fun r' => ∃ k', k' < gl st l n j - q ∧ ∃ q', k' = gl st l n j - q' ∧ q' ≤ gl st l n j ∧
          r'.w "sp.q" = gs st l n j + q' ∧ r'.w "sp.qe" = gs st l n j + gl st l n j ∧
          r'.w "sp.j" = j ∧ r'.w "lvl" = l ∧ r'.w "n" = n ∧
          RowRep r' "S" "S.len" n (l - 1)
            (R ++ ((mlist st l n j).take q').filter (fun v => lt v ∧ ¬ mk v)) ∧
          KR r' ∧ Unchanged st r' ["S", "S.len"] [] (grpRegs ++ LW) LV ∧ r'.wlen = st.wlen ∧
          (∀ i, (i < (l - 1) * n ∨ l * n ≤ i) → r'.wa "S" i = st.wa "S" i) ∧
          (∀ l', l' ≠ l - 1 → r'.wa "S.len" l' = st.wa "S.len" l') ∧
          st.cost ≤ r'.cost ∧ r'.cost ≤ st.cost + 2 + q' * (C + 10)) := by
      -- the final `q := q + 1`, from any state `r3` with the row extended by `ext`
      have fin : ∀ (r3 : State V) (ext : List ℕ), r3.w "sp.q" = gs st l n j + q →
          r3.w "sp.qe" = gs st l n j + gl st l n j → r3.w "sp.j" = j → r3.w "lvl" = l →
          r3.w "n" = n → ext = (if (lt v ∧ ¬ mk v) then [v] else []) →
          RowRep r3 "S" "S.len" n (l - 1)
            (R ++ ((mlist st l n j).take q).filter (fun v => lt v ∧ ¬ mk v) ++ ext) →
          KR r3 → Unchanged st r3 ["S", "S.len"] [] (grpRegs ++ LW) LV → r3.wlen = st.wlen →
          (∀ i, (i < (l - 1) * n ∨ l * n ≤ i) → r3.wa "S" i = st.wa "S" i) →
          (∀ l', l' ≠ l - 1 → r3.wa "S.len" l' = st.wa "S.len" l') →
          st.cost ≤ r3.cost → r3.cost ≤ st.cost + 2 + q * (C + 10) + (C + 9) →
          Runs ops (incr "sp.q") r3 (fun r' => ∃ k', k' < gl st l n j - q ∧ ∃ q',
            k' = gl st l n j - q' ∧ q' ≤ gl st l n j ∧
            r'.w "sp.q" = gs st l n j + q' ∧ r'.w "sp.qe" = gs st l n j + gl st l n j ∧
            r'.w "sp.j" = j ∧ r'.w "lvl" = l ∧ r'.w "n" = n ∧
            RowRep r' "S" "S.len" n (l - 1)
              (R ++ ((mlist st l n j).take q').filter (fun v => lt v ∧ ¬ mk v)) ∧
            KR r' ∧ Unchanged st r' ["S", "S.len"] [] (grpRegs ++ LW) LV ∧ r'.wlen = st.wlen ∧
            (∀ i, (i < (l - 1) * n ∨ l * n ≤ i) → r'.wa "S" i = st.wa "S" i) ∧
            (∀ l', l' ≠ l - 1 → r'.wa "S.len" l' = st.wa "S.len" l') ∧
            st.cost ≤ r'.cost ∧ r'.cost ≤ st.cost + 2 + q' * (C + 10)) := by
        intro r3 ext h1 h2 h3 h4 h5 hext h6 h7 h8 h9 h10 h11 h12 h13
        have hc3 : gs st l n j + q + 1 < r3.cap := by rw [h8.cap]; omega
        refine runs_wset (a := gs st l n j + q + 1) (evalW_add_of (by rw [evalW_var, h1])
          (evalW_lit_of (by omega)) hc3) ?_
        set r4 := (r3.setW "sp.q" (gs st l n j + q + 1)).charge 1 with hr4
        have hU34 : Unchanged r3 r4 [] [] ["sp.q"] [] :=
          ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun z hz => by
            simp only [List.mem_singleton] at hz; simp [hr4, State.setW, State.charge, hz],
            fun _ _ => rfl, rfl, rfl⟩
        have hsubq : ["sp.q"] ⊆ grpRegs ++ LW := fun a ha => List.mem_append_left _ (by
          simp only [List.mem_singleton] at ha; subst ha; simp [grpRegs])
        refine ⟨gl st l n j - (q + 1), by omega, q + 1, rfl, by omega,
          by simp [hr4, State.setW, State.charge]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_⟩
        · rw [hU34.wreg _ (by simp)]; exact h2
        · rw [hU34.wreg _ (by simp)]; exact h3
        · rw [hU34.wreg _ (by simp)]; exact h4
        · rw [hU34.wreg _ (by simp)]; exact h5
        · have := h6.of_eq (st' := r4) rfl rfl rfl (fun _ _ => rfl)
          rw [List.append_assoc, hext] at this
          rw [take_succ_filter _ _ (by rw [hml]; exact hqL), hmq]
          simpa using this
        · exact hI.frame r3 r4 h7 (hU34.mono (by simp) (by simp) (fun a ha => gsub (hsubq ha)) (by simp))
            (by simp only [hr4, State.charge_cost, State.setW_cost]; omega)
        · exact h8.trans (hU34.mono (by simp) (by simp) hsubq (by simp))
        · simp [hr4, State.setW, State.charge, h9]
        · intro i hi; simp [hr4, State.setW, State.charge, h10 i hi]
        · intro l' hl'; simp [hr4, State.setW, State.charge, h11 l' hl']
        · simp only [hr4, State.charge_cost, State.setW_cost]; omega
        · simp only [hr4, State.charge_cost, State.setW_cost]
          have e : (q + 1) * (C + 10) = q * (C + 10) + (C + 10) := by ring
          omega
      have hc2' : r2.cost ≤ st.cost + 2 + q * (C + 10) + C + 2 := by
        simp only [hr1, State.charge_cost, State.setW_cost] at hc2; omega
      have hc2l' : st.cost ≤ r2.cost := by
        simp only [hr1, State.charge_cost, State.setW_cost] at hc2l; omega
      have hbase : ∀ z, z ∉ LW → z ≠ "px" → r2.w z = r.w z := hreg2
      by_cases hlt : lt v
      · have hltb : r2.w "sp.lt" = 1 := by rw [hlt2, if_pos hlt]
        refine runs_seq (runs_ite_true (x := 1) (by rw [evalW_var, hltb]) one_ne_zero ?_)
        have hxml2 : v < (r2.charge 1).wlen "sp.xm" := by
          simp only [State.charge_wlen, hwl2]; omega
        by_cases hmk : mk v
        · -- marked: nothing appended
          have hxmv : r2.wa "sp.xm" v = 1 := by rw [hxm2, if_pos hmk]
          refine runs_ite_true (x := 1) (evalW_load_of (by rw [evalW_var]; simp [State.charge, hpx2])
            hxml2 |>.trans (by simp [State.charge, hxmv])) one_ne_zero (runs_skip ?_)
          refine fin _ [] (by simp [State.charge, hq2]) (by
              simp [State.charge]; rw [hreg2 _ (nLW _ (by simp)) (by decide), hrqe])
            (by simp [State.charge]; rw [hreg2 _ (nLW _ (by simp)) (by decide), hrj])
            (by simp [State.charge, hl2]) (by simp [State.charge, hn2])
            (by simp [hmk]) (by rw [List.append_nil]; exact hRr2)
            (hI.frame r2 _ hK2 (unch_charge3 r2 _ _ _ _) (by simp only [State.charge_cost]; omega))
            (hU02.trans (unch_charge3 r2 _ _ _ _))
            (by simp only [State.charge_wlen]; exact hwl2)
            (fun i hi => by
              simp [State.charge]; rw [(hU2.warr "S" (by simp)).1]; exact hSr i hi)
            (fun l' hl' => by
              simp [State.charge]; rw [(hU2.warr "S.len" (by simp)).1]; exact hSLr l' hl')
            (by simp only [State.charge_cost]; omega) (by simp only [State.charge_cost]; omega)
        · -- unmarked: append `v` to the child row
          have hxmv : r2.wa "sp.xm" v = 0 := by rw [hxm2, if_neg hmk]
          refine runs_ite_false (evalW_load_of (by rw [evalW_var]; simp [State.charge, hpx2])
            hxml2 |>.trans (by simp [State.charge, hxmv])) ?_
          set ra0 := (r2.charge 1).charge 1 with hra0
          have hl0 : ra0.w "lvl" = l := by simp [hra0, State.charge, hl2]
          have hc1a : 1 < ra0.cap := by simp only [hra0, State.charge_cap, hcap2]; omega
          refine runs_seq (runs_wset (a := l - 1) (by
            simp only [evalW_sub', evalW_var, evalW_lit', hl0, Option.bind_some, fit_of_lt hc1a]) ?_)
          set ra1 := (ra0.setW "lvl" (l - 1)).charge 1 with hra1
          have hU01 : Unchanged r2 ra1 [] [] ["lvl"] [] :=
            ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun z hz => by
              simp only [List.mem_singleton] at hz; simp [hra1, hra0, State.setW, State.charge, hz],
              fun _ _ => rfl, rfl, rfl⟩
          have hR1 : RowRep ra1 "S" "S.len" n (l - 1)
              (R ++ ((mlist st l n j).take q).filter (fun v => lt v ∧ ¬ mk v)) := hRr2
          have hlen_row : (R ++ ((mlist st l n j).take q).filter (fun v => lt v ∧ ¬ mk v)).length
              < n := by
            have h1 := filter_take_lt (mlist st l n j) (fun v => lt v ∧ ¬ mk v)
              (show q < (mlist st l n j).length by rw [hml]; exact hqL) (by rw [hmq]; exact ⟨hlt, hmk⟩)
            simp only [List.length_append]; omega
          have hcapa1 : ra1.cap = st.cap := hcap2
          refine runs_seq ((RamLevel.rowAppend_spec (v := v) ra1 (by decide) hR1
            (by simp [hra1, State.setW, State.charge]) (by
              simp [hra1, hra0, State.setW, State.charge]; exact hn2) hlen_row
            (by simp [hra1, hra0, State.setW, State.charge, hpx2])
            (by rw [hcapa1, show l - 1 + 1 = l by omega]; omega)).mono ?_)
          rintro ra2 ⟨hR2, hU2a, hS2a, hSL2a, hoth2, hc2a, hwl2a⟩
          have hlvl2a : ra2.w "lvl" = l - 1 := by
            rw [hU2a.wreg "lvl" (by simp)]; simp [hra1, State.setW, State.charge]
          have hl1n : l + 1 ≤ (l + 1) * n := Nat.le_mul_of_pos_right _ (by omega)
          refine runs_wset (a := l - 1 + 1) (evalW_add_of (by rw [evalW_var, hlvl2a])
            (evalW_lit_of (by rw [hU2a.cap, hcapa1]; omega)) (by rw [hU2a.cap, hcapa1]; omega)) ?_
          set r3 := (ra2.setW "lvl" (l - 1 + 1)).charge 1 with hr3
          have hU23 : Unchanged ra2 r3 [] [] ["lvl"] [] :=
            ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun z hz => by
              simp only [List.mem_singleton] at hz; simp [hr3, State.setW, State.charge, hz],
              fun _ _ => rfl, rfl, rfl⟩
          have hreg3 : ∀ z, z ≠ "lvl" → r3.w z = r2.w z := by
            intro z hz
            rw [hU23.wreg z (by simpa using hz), hU2a.wreg z (by simp), hU01.wreg z (by simpa using hz)]
          have hsubl : ["lvl"] ⊆ grpRegs ++ LW := fun a ha => List.mem_append_left _ (by
            simp only [List.mem_singleton] at ha; subst ha; simp [grpRegs])
          have hU23' : Unchanged r2 r3 ["S", "S.len"] [] ["lvl"] [] :=
            ((hU01.mono (by simp) (by simp) (by simp) (by simp)).trans
              (hU2a.mono (by simp) (by simp) (by simp) (by simp))).trans
              (hU23.mono (by simp) (by simp) (by simp) (by simp))
          refine fin r3 [v] (by rw [hreg3 _ (by decide), hq2]) (by
              rw [hreg3 _ (by decide), hreg2 _ (nLW _ (by simp)) (by decide), hrqe])
            (by rw [hreg3 _ (by decide), hreg2 _ (nLW _ (by simp)) (by decide), hrj])
            (by simp [hr3, State.setW, State.charge]; omega) (by rw [hreg3 _ (by decide), hn2])
            (by simp [hlt, hmk]) (hR2.of_eq rfl rfl rfl (fun _ _ => rfl))
            (hI.frame r2 r3 hK2 (hU23'.mono (by simp) (by simp) (fun a ha => gsub (hsubl ha)) (by simp)) (by
              simp only [hr3, State.charge_cost, State.setW_cost]
              rw [hc2a]; simp only [hra1, hra0, State.charge_cost, State.setW_cost]; omega))
            (hU02.trans (hU23'.mono (by simp) (by simp) hsubl (by simp)))
            (by rw [show r3.wlen = ra2.wlen from rfl, hwl2a]; exact hwl2)
            (fun i hi => by
              have hne : i ≠ (l - 1) * n + (R ++ ((mlist st l n j).take q).filter
                  (fun v => lt v ∧ ¬ mk v)).length := by
                have h1 : (l - 1 + 1) * n = l * n := by rw [show l - 1 + 1 = l by omega]
                rcases hi with hi | hi
                · have : (l - 1) * n ≤ (l - 1) * n + (R ++ ((mlist st l n j).take q).filter
                    (fun v => lt v ∧ ¬ mk v)).length := Nat.le_add_right _ _
                  omega
                · rw [Nat.succ_mul] at h1; omega
              rw [show r3.wa = ra2.wa from rfl, hS2a i hne, show ra1.wa = r2.wa from rfl,
                (hU2.warr "S" (by simp)).1]
              exact hSr i hi)
            (fun l' hl' => by
              rw [show r3.wa = ra2.wa from rfl, hSL2a l' hl', show ra1.wa = r2.wa from rfl,
                (hU2.warr "S.len" (by simp)).1]
              exact hSLr l' hl')
            (by simp only [hr3, State.charge_cost, State.setW_cost]; rw [hc2a]
                simp only [hra1, hra0, State.charge_cost, State.setW_cost]; omega)
            (by simp only [hr3, State.charge_cost, State.setW_cost]; rw [hc2a]
                simp only [hra1, hra0, State.charge_cost, State.setW_cost]; omega)
      · -- the test fails: nothing appended
        have hltb : r2.w "sp.lt" = 0 := by rw [hlt2, if_neg hlt]
        refine runs_seq (runs_ite_false (by rw [evalW_var, hltb]) (runs_skip ?_))
        refine fin _ [] (by simp [State.charge, hq2]) (by
            simp [State.charge]; rw [hreg2 _ (nLW _ (by simp)) (by decide), hrqe])
          (by simp [State.charge]; rw [hreg2 _ (nLW _ (by simp)) (by decide), hrj])
          (by simp [State.charge, hl2]) (by simp [State.charge, hn2])
          (by simp [hlt]) (by rw [List.append_nil]; exact hRr2)
          (hI.frame r2 _ hK2 (unch_charge2 r2 _ _ _ _) (by simp only [State.charge_cost]; omega))
          (hU02.trans (unch_charge2 r2 _ _ _ _))
          (by simp only [State.charge_wlen]; exact hwl2)
          (fun i hi => by
            simp [State.charge]; rw [(hU2.warr "S" (by simp)).1]; exact hSr i hi)
          (fun l' hl' => by
            simp [State.charge]; rw [(hU2.warr "S.len" (by simp)).1]; exact hSLr l' hl')
          (by simp only [State.charge_cost]; omega) (by simp only [State.charge_cost]; omega)
    exact hcase
  · -- all members scanned
    have hqL : q = gl st l n j := by
      by_contra h; rw [if_pos (by omega)] at hx; exact one_ne_zero hx
    subst hqL
    rw [← hml, List.take_length] at hRr
    refine ⟨hRr.of_eq rfl rfl rfl (fun _ _ => rfl),
      hI.frame r (r.charge 1) hKr (Unchanged.charge r 1 _ _ _ _) (by simp [State.charge]),
      by simp [State.charge, hrl], by simp [State.charge, hrn], by simp [State.charge, hrj],
      hUr.trans (Unchanged.charge r 1 _ _ _ _), by simp [State.charge, hwlr],
      fun i hi => by simp [State.charge, hSr i hi], fun l' hl' => by simp [State.charge, hSLr l' hl'],
      by simp [State.charge]; omega, by simp [State.charge]; omega⟩

end expandGroupSpec

/-! ## The scan over the pulled prefix (BM.11–12) -/

section expandScanSpec

variable {V : Type} {ops : VOps V}

/-- The group index of `x` at level `l` (meaningful when `sp.g[l n + x] ≠ 0`). -/
def grpOf (st : State V) (l n x : ℕ) : ℕ := st.wa "sp.g" (l * n + x) - 1

/-- `x` is the current pivot of its group. -/
def isPiv (st : State V) (l n x : ℕ) : Prop :=
  st.wa "sp.g" (l * n + x) ≠ 0 ∧ st.wa "sp.gp" (l * n + grpOf st l n x) = x

instance isPiv.dec (st : State V) (l n : ℕ) : DecidablePred (isPiv st l n) := fun x =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- The members appended for the pulled key `x`. -/
def extOf (st : State V) (l n : ℕ) (lt mk : ℕ → Prop) [DecidablePred lt] [DecidablePred mk]
    (x : ℕ) : List ℕ :=
  if isPiv st l n x then (mlist st l n (grpOf st l n x)).filter (fun v => lt v ∧ ¬ mk v) else []

/-- The scan work for the pulled key `x` (the length of the scanned group). -/
def scanW (st : State V) (l n x : ℕ) : ℕ :=
  if isPiv st l n x then gl st l n (grpOf st l n x) else 0

theorem mlist_of_eq {st st' : State V} {l n : ℕ} (h1 : st'.wa "sp.gm" = st.wa "sp.gm")
    (h2 : st'.wa "sp.gs" = st.wa "sp.gs") (h3 : st'.wa "sp.gl" = st.wa "sp.gl") (j : ℕ) :
    mlist st' l n j = mlist st l n j := by
  simp only [mlist, gl, gs, gmem, h1, h2, h3]

theorem flatMap_take_succ {α β : Type} (l : List α) (f : α → List β) {i : ℕ} (hi : i < l.length) :
    (l.take (i + 1)).flatMap f = (l.take i).flatMap f ++ f l[i] := by
  rw [List.take_succ, List.getElem?_eq_getElem hi, Option.toList_some, List.flatMap_append]
  simp

theorem sum_take_succ {α : Type} (l : List α) (f : α → ℕ) {i : ℕ} (hi : i < l.length) :
    ((l.take (i + 1)).map f).sum = ((l.take i).map f).sum + f l[i] := by
  rw [List.take_succ, List.getElem?_eq_getElem hi, Option.toList_some, List.map_append,
    List.sum_append]
  simp

theorem flatMap_take_le {α β : Type} (l : List α) (f : α → List β) (i : ℕ) :
    ((l.take i).flatMap f).length ≤ (l.flatMap f).length := by
  conv_rhs => rw [← List.take_append_drop i l]
  rw [List.flatMap_append, List.length_append]; omega

theorem unch_setW (r : State V) {x : String} (a : ℕ) {wr : List String} {vr : List String}
    (hx : x ∈ wr) : Unchanged r ((r.setW x a).charge 1) [] [] wr vr :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun z hz => by
    have : z ≠ x := fun h => hz (h ▸ hx)
    simp [State.setW, State.charge, this], fun _ _ => rfl, rfl, rfl⟩

theorem rowRep_of_unch {st st' : State V} {arr len : String} {n l : ℕ} {xs : List ℕ}
    {wa va wr vr : List String} (h : RowRep st arr len n l xs) (hU : Unchanged st st' wa va wr vr)
    (ha : arr ∉ wa) (hl : len ∉ wa) : RowRep st' arr len n l xs :=
  h.of_eq (hU.warr arr ha).2 (hU.warr len hl).2 (by rw [(hU.warr len hl).1])
    (fun i _ => by rw [(hU.warr arr ha).1])

theorem grpRep_of_unch {st st' : State V} {l n p : ℕ} {P : ℕ → Finset ℕ} {piv : ℕ → ℕ}
    {wa va wr vr : List String} (h : GrpRep st l n p P piv) (hU : Unchanged st st' wa va wr vr)
    (hd : ∀ a ∈ grpArrs, a ∉ wa) : GrpRep st' l n p P piv :=
  GrpRep.of_eq h (fun a ha => (hU.warr a (hd a ha)).1) (fun a ha => (hU.warr a (hd a ha)).2)

theorem evalW_cr {s : State V} {l n x : ℕ} {e : WExpr} (hl : s.w "lvl" = l) (hn : s.w "n" = n)
    (he : evalW s e = some x) (hc : l * n + x < s.cap) : evalW s (cr e) = some (l * n + x) := by
  simp only [cr, evalW_add', evalW_mul', evalW_var, hl, hn, he, Option.bind_some,
    fit_of_lt (show l * n < s.cap by omega), fit_of_lt hc]

/-- **The pulled-prefix scan** (BM.11–12 without the marking): for each pulled key `x` (the
prefix `ks` of the child's `S` row) that is the current pivot of its group, the group's members
`v` with `lt v` and no mark are appended. -/
theorem expandScan_spec {ltBi : Stmt} {KR : State V → Prop} {lt : ℕ → Prop} [DecidablePred lt]
    {C : ℕ} {LW LV : List String} (hI : LtI ops ltBi KR lt C LW LV) (st : State V) {l n p : ℕ}
    {P : ℕ → Finset ℕ} {piv : ℕ → ℕ} (hG : GrpRep st l n p P piv) (hl : st.w "lvl" = l)
    (hl1 : 1 ≤ l) (hn : st.w "n" = n) {ks : List ℕ} (hR : RowRep st "S" "S.len" n (l - 1) ks)
    (hks : ∀ x ∈ ks, x < n) (hnp : st.w "sp.np0" = ks.length) (mk : ℕ → Prop) [DecidablePred mk]
    (hroom : ks.length + (ks.flatMap (extOf st l n lt mk)).length ≤ n)
    (hxm : ∀ x < n, st.wa "sp.xm" x = if mk x then 1 else 0) (hxml : n ≤ st.wlen "sp.xm")
    (hK : KR st) (hcap : (l + 1) * n < st.cap) (hc2 : 2 < st.cap) :
    Runs ops (expandScan ltBi) st (fun r =>
      RowRep r "S" "S.len" n (l - 1) (ks ++ ks.flatMap (extOf st l n lt mk)) ∧
      KR r ∧ r.w "lvl" = l ∧ r.w "n" = n ∧ r.w "sp.np0" = ks.length ∧
      Unchanged st r ["S", "S.len"] [] (expRegs ++ LW) LV ∧ r.wlen = st.wlen ∧
      (∀ i, (i < (l - 1) * n ∨ l * n ≤ i) → r.wa "S" i = st.wa "S" i) ∧
      (∀ l', l' ≠ l - 1 → r.wa "S.len" l' = st.wa "S.len" l') ∧
      st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + 2 + ks.length * 12 + (ks.map (scanW st l n)).sum * (C + 10)) := by
  have gsub := grpRegs_sub LW
  have nLW : ∀ z ∈ ["sp.q", "sp.qe", "px", "sp.j", "sp.i", "sp.np0", "lvl", "n", "mk.i"], z ∉ LW :=
    fun z hz h => hI.regs z h hz
  have mE : ∀ z ∈ expRegs, z ∈ expRegs ++ LW := fun z hz => List.mem_append_left _ hz
  have hsubW : ["lvl", "px", "sp.j"] ⊆ expRegs ++ LW := by
    intro a ha
    apply List.mem_append_left
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> simp [expRegs]
  have hc1 : 1 < st.cap := by omega
  have hl0 : l - 1 + 1 = l := by omega
  have hn1 : n ≤ (l + 1) * n := Nat.le_mul_of_pos_left n (by omega)
  have hln1 : l * n ≤ (l + 1) * n := Nat.mul_le_mul_right _ (Nat.le_succ l)
  have hdS : ∀ a ∈ grpArrs, a ∉ ["S", "S.len"] := by decide
  -- `sp.i := 0`
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by omega)) ?_)
  have hU01 : Unchanged st ((st.setW "sp.i" 0).charge 1) [] [] (expRegs ++ LW) LV :=
    (unch_setW (vr := []) st 0 (mE _ (by simp [expRegs]))).mono (List.Subset.refl _) (List.Subset.refl _)
      (List.Subset.refl _) (List.nil_subset _)
  refine runs_while_nat (fun k r => ∃ i, k = ks.length - i ∧ i ≤ ks.length ∧
      r.w "sp.i" = i ∧ r.w "sp.np0" = ks.length ∧ r.w "lvl" = l ∧ r.w "n" = n ∧
      RowRep r "S" "S.len" n (l - 1) (ks ++ (ks.take i).flatMap (extOf st l n lt mk)) ∧
      Unchanged st r ["S", "S.len"] [] (expRegs ++ LW) LV ∧ r.wlen = st.wlen ∧
      (∀ i, (i < (l - 1) * n ∨ l * n ≤ i) → r.wa "S" i = st.wa "S" i) ∧
      (∀ l', l' ≠ l - 1 → r.wa "S.len" l' = st.wa "S.len" l') ∧
      st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + 1 + i * 12 + ((ks.take i).map (scanW st l n)).sum * (C + 10)) _ ?_
    ks.length ((st.setW "sp.i" 0).charge 1)
    ⟨0, by simp, Nat.zero_le _, by simp [State.setW, State.charge],
      by simp [State.setW, State.charge, hnp], by simp [State.setW, State.charge, hl],
      by simp [State.setW, State.charge, hn],
      by have e : ks ++ (ks.take 0).flatMap (extOf st l n lt mk) = ks := by simp
         rw [e]; exact rowRep_of_unch hR hU01 (by simp) (by simp),
      hU01.mono (by simp) (by simp) (List.Subset.refl _) (by simp), rfl,
      fun _ _ => rfl, fun _ _ => rfl,
      by simp only [State.charge_cost, State.setW_cost]; omega,
      by simp only [State.charge_cost, State.setW_cost, List.take_zero, List.map_nil,
        List.sum_nil]; omega⟩
  rintro k r ⟨i, rfl, hi, hri, hrnp, hrl, hrn, hRr, hUr, hwlr, hSr, hSLr, hcl, hch⟩
  have hcapr : r.cap = st.cap := hUr.cap
  refine ⟨if i < ks.length then 1 else 0,
    evalW_lt_of (by rw [evalW_var, hri]) (by rw [evalW_var, hrnp]) (by rw [hcapr]; omega),
    fun hx => ?_, fun hx => ?_⟩
  · have hik : i < ks.length := by
      by_contra h; rw [if_neg h] at hx; exact hx rfl
    have hxn : ks[i] < n := hks _ (List.getElem_mem hik)
    have hl1n : l + 1 ≤ (l + 1) * n := Nat.le_mul_of_pos_right _ (by omega)
    obtain ⟨gx, hgx⟩ : ∃ g, st.wa "sp.g" (l * n + ks[i]) = g := ⟨_, rfl⟩
    -- the final `sp.i := sp.i + 1`
    have fin : ∀ (r8 : State V) (ext : List ℕ), r8.w "sp.i" = i → r8.w "sp.np0" = ks.length →
        r8.w "lvl" = l → r8.w "n" = n → ext = extOf st l n lt mk ks[i] →
        RowRep r8 "S" "S.len" n (l - 1) (ks ++ (ks.take i).flatMap (extOf st l n lt mk) ++ ext) →
        Unchanged st r8 ["S", "S.len"] [] (expRegs ++ LW) LV → r8.wlen = st.wlen →
        (∀ i, (i < (l - 1) * n ∨ l * n ≤ i) → r8.wa "S" i = st.wa "S" i) →
        (∀ l', l' ≠ l - 1 → r8.wa "S.len" l' = st.wa "S.len" l') →
        r.cost ≤ r8.cost → r8.cost ≤ r.cost + 11 + scanW st l n ks[i] * (C + 10) →
        Runs ops (incr "sp.i") r8 (fun r' => ∃ k', k' < ks.length - i ∧ ∃ i', k' = ks.length - i' ∧
          i' ≤ ks.length ∧ r'.w "sp.i" = i' ∧ r'.w "sp.np0" = ks.length ∧ r'.w "lvl" = l ∧
          r'.w "n" = n ∧
          RowRep r' "S" "S.len" n (l - 1) (ks ++ (ks.take i').flatMap (extOf st l n lt mk)) ∧
          Unchanged st r' ["S", "S.len"] [] (expRegs ++ LW) LV ∧ r'.wlen = st.wlen ∧
          (∀ i, (i < (l - 1) * n ∨ l * n ≤ i) → r'.wa "S" i = st.wa "S" i) ∧
          (∀ l', l' ≠ l - 1 → r'.wa "S.len" l' = st.wa "S.len" l') ∧
          st.cost ≤ r'.cost ∧
          r'.cost ≤ st.cost + 1 + i' * 12 + ((ks.take i').map (scanW st l n)).sum * (C + 10)) := by
      intro r8 ext h1 h2 h3 h4 hext h5 h6 h7 h8 h9 h10 h11
      have hc8 : i + 1 < r8.cap := by rw [h6.cap]; omega
      refine runs_wset (a := i + 1) (evalW_add_of (by rw [evalW_var, h1])
        (evalW_lit_of (by rw [h6.cap]; omega)) hc8) ?_
      have hU89 : Unchanged r8 ((r8.setW "sp.i" (i + 1)).charge 1) [] [] (expRegs ++ LW) LV :=
        unch_setW _ _ (mE _ (by simp [expRegs]))
      refine ⟨ks.length - (i + 1), by omega, i + 1, rfl, by omega, by simp [State.setW, State.charge],
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [State.setW, State.charge, h2]
      · simp [State.setW, State.charge, h3]
      · simp [State.setW, State.charge, h4]
      · rw [flatMap_take_succ _ _ hik, ← List.append_assoc, ← hext]
        exact rowRep_of_unch h5 hU89 (by simp) (by simp)
      · exact h6.trans (hU89.mono (by simp) (by simp) (List.Subset.refl _) (by simp))
      · simp only [State.charge_wlen, State.setW_wlen]; exact h7
      · intro j hj; simp [State.setW, State.charge, h8 j hj]
      · intro l' hl'; simp [State.setW, State.charge, h9 l' hl']
      · simp only [State.charge_cost, State.setW_cost]; omega
      · rw [sum_take_succ _ _ hik]; simp only [State.charge_cost, State.setW_cost]
        have e : (i + 1) * 12 = i * 12 + 12 := by ring
        have e2 : (((ks.take i).map (scanW st l n)).sum + scanW st l n ks[i]) * (C + 10) =
            ((ks.take i).map (scanW st l n)).sum * (C + 10) + scanW st l n ks[i] * (C + 10) := by
          ring
        omega
    -- `lvl := lvl - 1`
    have hc1r : 1 < (r.charge 1).cap := by simp only [State.charge_cap, hcapr]; omega
    refine runs_seq (runs_wset (a := l - 1) (by
      simp only [evalW_sub', evalW_var, evalW_lit', State.charge_w, hrl, Option.bind_some,
        fit_of_lt hc1r]) ?_)
    set r1 := ((r.charge 1).setW "lvl" (l - 1)).charge 1 with hr1
    have hUa : Unchanged r r1 [] [] ["lvl", "px", "sp.j"] [] :=
      (Unchanged.charge r 1 _ _ _ _).trans (unch_setW _ _ (by simp))
    -- `px := S[(l - 1) n + i]`
    have hxs : i < (ks ++ (ks.take i).flatMap (extOf st l n lt mk)).length := by
      simp only [List.length_append]; omega
    refine runs_seq ((RamLevel.rowGet_spec (x := "px") r1 (rowRep_of_unch hRr hUa (by simp) (by simp))
      (by simp [hr1, State.setW, State.charge]) (by simp [hr1, State.setW, State.charge, hrn])
      (by rw [evalW_var]; simp [hr1, State.setW, State.charge, hri]) hxs
      (by rw [hl0, hUa.cap, hcapr]; omega)).mono ?_)
    intro r2 hr2
    rw [List.getElem_append_left hik] at hr2
    subst hr2
    set r2 := (r1.setW "px" ks[i]).charge 1 with hr2
    have hUb : Unchanged r r2 [] [] ["lvl", "px", "sp.j"] [] := hUa.trans (unch_setW _ _ (by simp))
    have hl2 : r2.w "lvl" = l - 1 := by simp [hr2, hr1, State.setW, State.charge]
    -- `lvl := lvl + 1`
    have hc2r : r2.cap = st.cap := by rw [hUb.cap, hcapr]
    refine runs_seq (runs_wset (a := l) (by
      rw [evalW_add_of (x := l - 1) (y := 1) (by rw [evalW_var, hl2]) (evalW_lit_of (by rw [hc2r]; omega))
        (by rw [hc2r]; omega), hl0]) ?_)
    set r3 := (r2.setW "lvl" l).charge 1 with hr3
    have hUc : Unchanged r r3 [] [] ["lvl", "px", "sp.j"] [] := hUb.trans (unch_setW _ _ (by simp))
    have hU03 : Unchanged st r3 ["S", "S.len"] [] (expRegs ++ LW) LV :=
      hUr.trans (hUc.mono (by simp) (by simp) hsubW (by simp))
    have hl3 : r3.w "lvl" = l := by simp [hr3, State.setW, State.charge]
    have hn3 : r3.w "n" = n := by rw [hUc.wreg _ (by simp)]; exact hrn
    have hpx3 : r3.w "px" = ks[i] := by simp [hr3, hr2, State.setW, State.charge]
    have hidx : l * n + ks[i] < (l + 1) * n := row_index_lt hxn
    -- `sp.j := sp.g[l n + px]`
    have hgl3 : l * n + ks[i] < r3.wlen "sp.g" := by
      rw [(hU03.warr "sp.g" (by simp)).2]; have := hG.len_g; omega
    refine runs_seq (runs_wset (a := gx) (by
      rw [evalW_load_of (evalW_cr hl3 hn3 (by rw [evalW_var, hpx3]) (by rw [hU03.cap]; omega)) hgl3,
        (hU03.warr "sp.g" (by simp)).1, hgx]) ?_)
    set r4 := (r3.setW "sp.j" gx).charge 1 with hr4
    have hUd : Unchanged r r4 [] [] ["lvl", "px", "sp.j"] [] := hUc.trans (unch_setW _ _ (by simp))
    have hU04 : Unchanged st r4 ["S", "S.len"] [] (expRegs ++ LW) LV :=
      hUr.trans (hUd.mono (by simp) (by simp) hsubW (by simp))
    have hj4 : r4.w "sp.j" = gx := by simp [hr4, State.setW, State.charge]
    have hR4 : RowRep r4 "S" "S.len" n (l - 1) (ks ++ (ks.take i).flatMap (extOf st l n lt mk)) :=
      rowRep_of_unch hRr hUd (by simp) (by simp)
    have hc4 : r4.cost = r.cost + 5 := by
      simp only [hr4, hr3, hr2, hr1, State.charge_cost, State.setW_cost] <;> omega
    have hwl4 : r4.wlen = st.wlen := by
      rw [show r4.wlen = r.wlen from funext fun a => (hUd.warr a (by simp)).2]; exact hwlr
    have hS4 : ∀ j, (j < (l - 1) * n ∨ l * n ≤ j) → r4.wa "S" j = st.wa "S" j := by
      intro j hj; rw [(hUd.warr "S" (by simp)).1]; exact hSr j hj
    have hSL4 : ∀ l', l' ≠ l - 1 → r4.wa "S.len" l' = st.wa "S.len" l' := by
      intro l' hl'; rw [(hUd.warr "S.len" (by simp)).1]; exact hSLr l' hl'
    by_cases hg0 : gx = 0
    · -- `px` is in no group
      have hnp' : ¬ isPiv st l n ks[i] := fun h => h.1 (by rw [hgx]; exact hg0)
      refine runs_seq (runs_ite_false (by rw [evalW_var, hj4, hg0]) (runs_skip ?_))
      refine fin _ [] (by simp [State.charge]; rw [hUd.wreg _ (by simp)]; exact hri)
        (by simp [State.charge]; rw [hUd.wreg _ (by simp)]; exact hrnp)
        (by simp [State.charge, hr4, hl3]) (by simp [State.charge, hr4, hn3])
        (by simp [extOf, hnp']) (by rw [List.append_nil]; exact hR4.of_eq rfl rfl rfl (fun _ _ => rfl))
        (hU04.trans (unch_charge2 r4 _ _ _ _)) (by simp only [State.charge_wlen]; exact hwl4)
        (fun j hj => by simp only [State.charge_wa]; exact hS4 j hj)
        (fun l' hl' => by simp only [State.charge_wa]; exact hSL4 l' hl')
        (by simp only [State.charge_cost]; omega) (by simp only [State.charge_cost]; omega)
    · obtain ⟨j, hjp, hgj, hxP⟩ : ∃ j < p, st.wa "sp.g" (l * n + ks[i]) = j + 1 ∧ ks[i] ∈ P j := by
        rcases hG.nomemb _ hxn with h | h
        · exact absurd (h ▸ hgx.symm) hg0
        · exact h
      have hj : gx - 1 = j := by omega
      refine runs_seq (runs_ite_true (x := gx) (by rw [evalW_var, hj4]) hg0 ?_)
      -- `sp.j := sp.j - 1`
      have hc4' : 1 < (r4.charge 1).cap := by simp only [State.charge_cap, hU04.cap]; omega
      refine runs_seq (runs_wset (a := gx - 1) (by
        simp only [evalW_sub', evalW_var, evalW_lit', State.charge_w, hj4, Option.bind_some,
          fit_of_lt hc4']) ?_)
      set r5 := ((r4.charge 1).setW "sp.j" (gx - 1)).charge 1 with hr5
      have hUe : Unchanged r r5 [] [] ["lvl", "px", "sp.j"] [] :=
        (hUd.trans (Unchanged.charge _ 1 _ _ _ _)).trans (unch_setW _ _ (by simp))
      have hU05 : Unchanged st r5 ["S", "S.len"] [] (expRegs ++ LW) LV :=
        hUr.trans (hUe.mono (by simp) (by simp) hsubW (by simp))
      have hl5 : r5.w "lvl" = l := by simp [hr5, State.setW, State.charge, hr4, hl3]
      have hn5 : r5.w "n" = n := by rw [hUe.wreg _ (by simp)]; exact hrn
      have hpx5 : r5.w "px" = ks[i] := by simp [hr5, State.setW, State.charge, hr4, hpx3]
      have hj5 : r5.w "sp.j" = j := by simp [hr5, State.setW, State.charge, hj]
      have hjn : l * n + j < (l + 1) * n := row_index_lt (by have := hG.p_le; omega)
      have hgp5 : l * n + j < r5.wlen "sp.gp" := by
        rw [(hU05.warr "sp.gp" (by simp)).2]; have := hG.len_gp; omega
      have ev : evalW r5 (eq (load "sp.gp" (cr (var "sp.j"))) (var "px")) =
          some (if st.wa "sp.gp" (l * n + j) = ks[i] then 1 else 0) := by
        rw [evalW_eq_of (evalW_load_of (evalW_cr hl5 hn5 (by rw [evalW_var, hj5])
          (by rw [hU05.cap]; omega)) hgp5) (by rw [evalW_var, hpx5]) (by rw [hU05.cap]; omega),
          (hU05.warr "sp.gp" (by simp)).1]
      have hc5 : r5.cost = r.cost + 7 := by
        simp only [hr5, State.charge_cost, State.setW_cost, hc4]
      have hwl5 : r5.wlen = st.wlen := by
        rw [show r5.wlen = r.wlen from funext fun a => (hUe.warr a (by simp)).2]; exact hwlr
      have hR5 : RowRep r5 "S" "S.len" n (l - 1) (ks ++ (ks.take i).flatMap (extOf st l n lt mk)) :=
        rowRep_of_unch hRr hUe (by simp) (by simp)
      have hS5 : ∀ j, (j < (l - 1) * n ∨ l * n ≤ j) → r5.wa "S" j = st.wa "S" j := by
        intro j hj; rw [(hUe.warr "S" (by simp)).1]; exact hSr j hj
      have hSL5 : ∀ l', l' ≠ l - 1 → r5.wa "S.len" l' = st.wa "S.len" l' := by
        intro l' hl'; rw [(hUe.warr "S.len" (by simp)).1]; exact hSLr l' hl'
      have hgrp : grpOf st l n ks[i] = j := by simp only [grpOf, hgx, hj]
      by_cases hpv : st.wa "sp.gp" (l * n + j) = ks[i]
      · -- `px` is the pivot of group `j`: expand the group
        have hisP : isPiv st l n ks[i] := ⟨by rw [hgx]; exact hg0, by rw [hgrp]; exact hpv⟩
        refine runs_ite_true (x := 1) (by rw [ev, if_pos hpv]) one_ne_zero ?_
        have hU06 : Unchanged st (r5.charge 1) ["S", "S.len"] [] (expRegs ++ LW) LV :=
          hU05.trans (Unchanged.charge _ 1 _ _ _ _)
        have hml : ∀ j', mlist (r5.charge 1) l n j' = mlist st l n j' :=
          mlist_of_eq (hU06.warr "sp.gm" (by simp)).1 (hU06.warr "sp.gs" (by simp)).1
            (hU06.warr "sp.gl" (by simp)).1
        have hext : extOf st l n lt mk ks[i] = (mlist st l n j).filter (fun v => lt v ∧ ¬ mk v) := by
          simp only [extOf, if_pos hisP, hgrp]
        have hroom6 : (ks ++ (ks.take i).flatMap (extOf st l n lt mk)).length +
            ((mlist (r5.charge 1) l n j).filter (fun v => lt v ∧ ¬ mk v)).length ≤ n := by
          rw [hml, ← hext]
          have h1 := flatMap_take_le ks (extOf st l n lt mk) (i + 1)
          rw [flatMap_take_succ _ _ hik, List.length_append] at h1
          simp only [List.length_append]; omega
        refine ((expandGroup_spec hI (r5.charge 1) (grpRep_of_unch hG hU06 hdS)
          (by simp [State.charge, hl5]) hl1 (by simp [State.charge, hn5])
          (by simp [State.charge, hj5]) hjp (hR5.of_eq rfl rfl rfl (fun _ _ => rfl)) mk hroom6
          (fun x hx => by rw [(hU06.warr "sp.xm" (by simp)).1]; exact hxm x hx)
          (by rw [(hU06.warr "sp.xm" (by simp)).2]; exact hxml)
          (hI.frame st _ hK (hU06.mono (by simp) (by simp) (List.Subset.refl _) (by simp))
            (by simp only [State.charge_cost]; omega))
          (by rw [hU06.cap]; exact hcap) (by rw [hU06.cap]; exact hc2)).mono ?_)
        rintro r7 ⟨hR7, -, hl7, hn7, -, hU7, hwl7, hS7, hSL7, hc7l, hc7⟩
        have nG : ∀ z, z ∉ grpRegs → z ∉ LW → z ∉ grpRegs ++ LW := fun z h1 h2 h => by
          rcases List.mem_append.1 h with h | h
          exacts [h1 h, h2 h]
        have hgl7 : gl (r5.charge 1) l n j = scanW st l n ks[i] := by
          simp only [scanW, if_pos hisP, hgrp, gl]
          rw [(hU06.warr "sp.gl" (by simp)).1]
        have hU7' : ∀ z, z ∉ grpRegs → z ∉ LW → z ∉ ["lvl", "px", "sp.j"] → r7.w z = r.w z :=
          fun z h1 h2 h3 => by rw [hU7.wreg _ (nG _ h1 h2), State.charge_w, hUe.wreg _ h3]
        refine fin r7 _ (by rw [hU7' _ (by simp [grpRegs]) (nLW _ (by simp)) (by simp)]; exact hri)
          (by rw [hU7' _ (by simp [grpRegs]) (nLW _ (by simp)) (by simp)]; exact hrnp) hl7 hn7
          (by rw [hml, hext]) hR7 (hU06.trans (hU7.mono (by simp) (by simp) gsub (by simp)))
          (by rw [hwl7]; simp only [State.charge_wlen]; exact hwl5)
          (fun j hj => by rw [hS7 j hj]; simp only [State.charge_wa]; exact hS5 j hj)
          (fun l' hl' => by rw [hSL7 l' hl']; simp only [State.charge_wa]; exact hSL5 l' hl')
          (by simp only [State.charge_cost] at hc7l; omega)
          (by rw [hgl7] at hc7; simp only [State.charge_cost] at hc7; omega)
      · refine runs_ite_false (by rw [ev, if_neg hpv]) (runs_skip ?_)
        have hnp' : ¬ isPiv st l n ks[i] := fun h => hpv (by rw [← hgrp]; exact h.2)
        refine fin _ [] (by simp [State.charge]; rw [hUe.wreg _ (by simp)]; exact hri)
          (by simp [State.charge]; rw [hUe.wreg _ (by simp)]; exact hrnp)
          (by simp [State.charge, hl5]) (by simp [State.charge, hn5])
          (by simp [extOf, hnp']) (by rw [List.append_nil]; exact hR5.of_eq rfl rfl rfl (fun _ _ => rfl))
          (hU05.trans (unch_charge2 r5 _ _ _ _)) (by simp only [State.charge_wlen]; exact hwl5)
          (fun j hj => by simp only [State.charge_wa]; exact hS5 j hj)
          (fun l' hl' => by simp only [State.charge_wa]; exact hSL5 l' hl')
          (by simp only [State.charge_cost]; omega) (by simp only [State.charge_cost]; omega)
  · -- the scan is complete
    have hik : i = ks.length := by
      by_contra h; rw [if_pos (by omega)] at hx; exact one_ne_zero hx
    subst hik
    rw [List.take_length] at hRr hch
    refine ⟨rowRep_of_unch hRr (Unchanged.charge r 1 [] [] [] []) (by simp) (by simp),
      hI.frame st (r.charge 1) hK ((hUr.trans (Unchanged.charge r 1 _ _ _ _)).mono (by simp) (by simp)
        (List.Subset.refl _) (by simp)) (by simp [State.charge]; omega),
      by simp [State.charge, hrl], by simp [State.charge, hrn], by simp [State.charge, hrnp],
      hUr.trans (Unchanged.charge r 1 _ _ _ _), by simp [State.charge, hwlr],
      fun i hi => by simp [State.charge, hSr i hi], fun l' hl' => by simp [State.charge, hSLr l' hl'],
      by simp [State.charge]; omega, by simp [State.charge]; omega⟩

end expandScanSpec

/-! ## BM.11–12: marking, scan, clearing -/

section expandSpec2

variable {V : Type} {ops : VOps V}

theorem extOf_of_eq {st st' : State V} {l n : ℕ} (lt mk : ℕ → Prop) [DecidablePred lt]
    [DecidablePred mk] (h : ∀ a ∈ grpArrs, st'.wa a = st.wa a) :
    extOf st' l n lt mk = extOf st l n lt mk := by
  have e1 := h "sp.gm" (by simp [grpArrs]); have e2 := h "sp.gs" (by simp [grpArrs])
  have e3 := h "sp.gl" (by simp [grpArrs]); have e4 := h "sp.gp" (by simp [grpArrs])
  have e6 := h "sp.g" (by simp [grpArrs])
  have hp : ∀ x, isPiv st' l n x ↔ isPiv st l n x := fun x => by
    simp only [isPiv, grpOf, e6, e4]
  have hg : ∀ x, grpOf st' l n x = grpOf st l n x := fun x => by simp only [grpOf, e6]
  funext x
  unfold extOf
  by_cases h1 : isPiv st l n x
  · rw [if_pos ((hp x).2 h1), if_pos h1, hg, mlist_of_eq e1 e2 e3]
  · rw [if_neg (fun h => h1 ((hp x).1 h)), if_neg h1]

theorem scanW_of_eq {st st' : State V} {l n : ℕ} (h : ∀ a ∈ grpArrs, st'.wa a = st.wa a) :
    scanW st' l n = scanW st l n := by
  have e3 := h "sp.gl" (by simp [grpArrs]); have e4 := h "sp.gp" (by simp [grpArrs])
  have e6 := h "sp.g" (by simp [grpArrs])
  have hp : ∀ x, isPiv st' l n x ↔ isPiv st l n x := fun x => by
    simp only [isPiv, grpOf, e6, e4]
  have hg : ∀ x, grpOf st' l n x = grpOf st l n x := fun x => by simp only [grpOf, e6]
  funext x
  unfold scanW
  by_cases h1 : isPiv st l n x
  · rw [if_pos ((hp x).2 h1), if_pos h1, hg]; simp only [gl, e3]
  · rw [if_neg (fun h => h1 ((hp x).1 h)), if_neg h1]

theorem extOf_lt {st : State V} {l n p : ℕ} {P : ℕ → Finset ℕ} {piv : ℕ → ℕ}
    (hG : GrpRep st l n p P piv) {lt mk : ℕ → Prop} [DecidablePred lt] [DecidablePred mk]
    {x : ℕ} (hx : x < n) {v : ℕ} (hv : v ∈ extOf st l n lt mk x) : v < n := by
  unfold extOf at hv
  split_ifs at hv with hp
  · have hv' := List.mem_of_mem_filter hv
    obtain ⟨j, hj, hg, -⟩ : ∃ j < p, st.wa "sp.g" (l * n + x) = j + 1 ∧ x ∈ P j := by
      rcases hG.nomemb x hx with h | h
      · exact absurd h hp.1
      · exact h
    have hjj : grpOf st l n x = j := by simp only [grpOf, hg]; omega
    rw [hjj] at hv'
    simp only [mlist, List.mem_map, List.mem_range] at hv'
    obtain ⟨q, hq, rfl⟩ := hv'
    exact hG.mem_lt j hj q hq
  · simp at hv

/-- **BM.11–12**: the pulled keys `ks` (prefix of the child's `S` row) are marked, the groups of
pulled current pivots are scanned (members with `lt` and no mark appended), and the marks are
cleared again (`sp.xm` is restored exactly). -/
theorem expand_spec {ltBi : Stmt} {KR : State V → Prop} {lt : ℕ → Prop} [DecidablePred lt]
    {C : ℕ} {LW LV : List String} (hI : LtI ops ltBi KR lt C LW LV) (st : State V) {l n p : ℕ}
    {P : ℕ → Finset ℕ} {piv : ℕ → ℕ} (hG : GrpRep st l n p P piv) (hl : st.w "lvl" = l)
    (hl1 : 1 ≤ l) (hn : st.w "n" = n) {ks : List ℕ} (hR : RowRep st "S" "S.len" n (l - 1) ks)
    (hks : ∀ x ∈ ks, x < n)
    (hroom : ks.length + (ks.flatMap (extOf st l n lt (fun x => x ∈ ks))).length ≤ n)
    (hxm : ∀ x < n, st.wa "sp.xm" x = 0) (hxml : n ≤ st.wlen "sp.xm")
    (hK : KR st) (hcap : (l + 1) * n < st.cap) (hc2 : 2 < st.cap) (hlc : l + 1 < st.cap) :
    Runs ops (expand ltBi) st (fun r =>
      RowRep r "S" "S.len" n (l - 1) (ks ++ ks.flatMap (extOf st l n lt (fun x => x ∈ ks))) ∧
      KR r ∧ r.w "lvl" = l ∧ r.w "n" = n ∧ r.wa "sp.xm" = st.wa "sp.xm" ∧
      Unchanged st r ["S", "S.len", "sp.xm"] [] (expRegs ++ LW) LV ∧ r.wlen = st.wlen ∧
      (∀ i, (i < (l - 1) * n ∨ l * n ≤ i) → r.wa "S" i = st.wa "S" i) ∧
      (∀ l', l' ≠ l - 1 → r.wa "S.len" l' = st.wa "S.len" l') ∧
      st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + 11 + ks.length * 18 + (ks.map (scanW st l n)).sum * (C + 10)) := by
  have mE : ∀ z ∈ expRegs, z ∈ expRegs ++ LW := fun z hz => List.mem_append_left _ hz
  have nE : ∀ z, z ∉ expRegs → z ∉ LW → z ∉ expRegs ++ LW := fun z h1 h2 h => by
    rcases List.mem_append.1 h with h | h
    exacts [h1 h, h2 h]
  have nLW : ∀ z ∈ ["sp.q", "sp.qe", "px", "sp.j", "sp.i", "sp.np0", "lvl", "n", "mk.i"], z ∉ LW :=
    fun z hz h => hI.regs z h hz
  have hc1 : 1 < st.cap := by omega
  have hl0 : l - 1 + 1 = l := by omega
  have hn1 : n ≤ (l + 1) * n := Nat.le_mul_of_pos_left n (by omega)
  have hln1 : l * n ≤ (l + 1) * n := Nat.mul_le_mul_right _ (Nat.le_succ l)
  have hlen0 : l - 1 < st.wlen "S.len" := hR.2.2.1
  have hv0 : st.wa "S.len" (l - 1) = ks.length := hR.2.2.2.1
  have hmk : ["mk.i"] ⊆ expRegs ++ LW := fun a ha => mE _ (by
    simp only [List.mem_singleton] at ha; subst ha; simp [expRegs])
  -- 1. `sp.np0 := S.len[lvl - 1]`
  refine runs_seq (runs_wset (a := ks.length) (by
    rw [evalW_load_of (j := l - 1) (by simp only [evalW_sub', evalW_var, evalW_lit', hl,
      Option.bind_some, fit_of_lt hc1]) hlen0, hv0]) ?_)
  set e1 := (st.setW "sp.np0" ks.length).charge 1 with he1
  have hU1 : Unchanged st e1 [] [] (expRegs ++ LW) LV :=
    (unch_setW (vr := []) st _ (mE _ (by simp [expRegs]))).mono (List.Subset.refl _) (List.Subset.refl _)
      (List.Subset.refl _) (List.nil_subset _)
  have hl1e : e1.w "lvl" = l := by simp [he1, State.setW, State.charge, hl]
  have hc1e : 1 < e1.cap := by rw [hU1.cap]; exact hc1
  -- 2. `lvl := lvl - 1`
  refine runs_seq (runs_wset (a := l - 1) (by
    simp only [evalW_sub', evalW_var, evalW_lit', hl1e, Option.bind_some, fit_of_lt hc1e]) ?_)
  set e2 := (e1.setW "lvl" (l - 1)).charge 1 with he2
  have hU2 : Unchanged st e2 [] [] (expRegs ++ LW) LV :=
    hU1.trans (unch_setW _ _ (mE _ (by simp [expRegs])))
  -- 3. mark the pulled keys
  refine runs_seq ((RamMark.markRow_spec (arr := "sp.xm") (rw := "S") (rk := "sp.np0") (val := 1)
    e2 (by decide) (by decide) (rowRep_of_unch hR hU2 (by simp) (by simp)) (le_refl _)
    (by simp [he2, he1, State.setW, State.charge]) (by decide)
    (by simp [he2, State.setW, State.charge]) (by simp [he2, he1, State.setW, State.charge, hn])
    (by decide) (by decide)
    (fun x hx => by rw [(hU2.warr "sp.xm" (by simp)).2]; have := hks x hx; omega)
    (by rw [hl0, hU2.cap]; omega) (by rw [hU2.cap]; omega) (by rw [hU2.cap]; omega)).mono ?_)
  rintro e3 ⟨hxm3, hU3, hwl3, hc3⟩
  have hU3' : Unchanged st e3 ["sp.xm"] [] (expRegs ++ LW) LV :=
    (hU2.mono (by simp) (by simp) (List.Subset.refl _) (by simp)).trans
      (hU3.mono (by simp) (by simp) hmk (by simp))
  have hl3 : e3.w "lvl" = l - 1 := by
    rw [hU3.wreg _ (by simp)]; simp [he2, State.setW, State.charge]
  -- 4. `lvl := lvl + 1`
  refine runs_seq (runs_wset (a := l) (by
    rw [evalW_add_of (x := l - 1) (y := 1) (by rw [evalW_var, hl3])
      (evalW_lit_of (by rw [hU3'.cap]; omega)) (by rw [hU3'.cap]; omega), hl0]) ?_)
  set e4 := (e3.setW "lvl" l).charge 1 with he4
  have hU4 : Unchanged st e4 ["sp.xm"] [] (expRegs ++ LW) LV :=
    hU3'.trans ((unch_setW (vr := []) _ _ (mE _ (by simp [expRegs]))).mono (by simp) (by simp)
      (List.Subset.refl _) (by simp))
  have hA4 : ∀ a ∈ grpArrs, e4.wa a = st.wa a := fun a ha => (hU4.warr a (by
    revert a; decide)).1
  have hxm4 : ∀ x < n, e4.wa "sp.xm" x = if x ∈ ks then 1 else 0 := by
    intro x hx
    rw [show e4.wa = e3.wa from rfl, hxm3 x, List.take_length, (hU2.warr "sp.xm" (by simp)).1, hxm x hx]
  have hwl4 : e4.wlen = st.wlen := by
    rw [show e4.wlen = e3.wlen from rfl, hwl3]; exact funext fun a => (hU2.warr a (by simp)).2
  have hc4 : e4.cost = st.cost + 3 * ks.length + 5 := by
    simp only [he4, State.charge_cost, State.setW_cost, hc3, he2, he1] <;> omega
  -- 5. the scan
  refine runs_seq ((expandScan_spec hI e4 (grpRep_of_unch hG hU4 (by decide))
    (by simp [he4, State.setW, State.charge]) hl1
    (by rw [hU4.wreg _ (nE _ (by simp [expRegs]) (nLW _ (by simp)))]; exact hn)
    (rowRep_of_unch hR hU4 (by simp) (by simp)) hks
    (by simp [he4, State.setW, State.charge]; rw [hU3.wreg _ (by simp)]
        simp [he2, he1, State.setW, State.charge])
    (fun x => x ∈ ks) (by rw [extOf_of_eq _ _ hA4]; exact hroom) hxm4
    (by rw [hwl4]; exact hxml)
    (hI.frame st e4 hK (hU4.mono (by simp) (by simp) (List.Subset.refl _) (by simp)) (by omega))
    (by rw [hU4.cap]; exact hcap) (by rw [hU4.cap]; exact hc2)).mono ?_)
  rintro e5 ⟨hR5, -, hl5, hn5, hnp5, hU5, hwl5, hS5, hSL5, hc5l, hc5⟩
  rw [extOf_of_eq _ _ hA4] at hR5
  rw [scanW_of_eq hA4] at hc5
  have hU5' : Unchanged st e5 ["S", "S.len", "sp.xm"] [] (expRegs ++ LW) LV :=
    (hU4.mono (by simp) (by simp) (List.Subset.refl _) (by simp)).trans
      (hU5.mono (by simp) (by simp) (List.Subset.refl _) (by simp))
  -- 6. `lvl := lvl - 1`
  have hc5e : 1 < e5.cap := by rw [hU5'.cap]; exact hc1
  refine runs_seq (runs_wset (a := l - 1) (by
    simp only [evalW_sub', evalW_var, evalW_lit', hl5, Option.bind_some, fit_of_lt hc5e]) ?_)
  set e6 := (e5.setW "lvl" (l - 1)).charge 1 with he6
  have hU6 : Unchanged st e6 ["S", "S.len", "sp.xm"] [] (expRegs ++ LW) LV :=
    hU5'.trans ((unch_setW (vr := []) _ _ (mE _ (by simp [expRegs]))).mono (by simp) (by simp)
      (List.Subset.refl _) (by simp))
  -- 7. clear the marks
  have hwl6 : e6.wlen = st.wlen := by
    rw [show e6.wlen = e5.wlen from rfl, hwl5, show e4.wlen = e3.wlen from rfl, hwl3]
    exact funext fun a => (hU2.warr a (by simp)).2
  have hext_lt : ∀ x ∈ ks ++ ks.flatMap (extOf st l n lt (fun x => x ∈ ks)), x < n := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact hks x h
    · obtain ⟨y, hy, hxy⟩ := List.mem_flatMap.1 h
      exact extOf_lt hG (hks y hy) hxy
  refine runs_seq ((RamMark.markRow_spec (arr := "sp.xm") (rw := "S") (rk := "sp.np0") (val := 0)
    (k := ks.length) e6 (by decide) (by decide) (rowRep_of_unch hR5 (unch_setW e5 (l - 1) (wr := ["lvl"]) (vr := []) (by simp))
      (by simp) (by simp)) (by simp)
    (by simp [he6, State.setW, State.charge, hnp5]) (by decide)
    (by simp [he6, State.setW, State.charge]) (by simp [he6, State.setW, State.charge, hn5])
    (by decide) (by decide)
    (fun x hx => by rw [hwl6]; have := hext_lt x hx; omega)
    (by rw [hl0, hU6.cap]; omega) (by rw [hU6.cap]; omega) (by rw [hU6.cap]; omega)).mono ?_)
  rintro e7 ⟨hxm7, hU7, hwl7, hc7⟩
  have hU7' : Unchanged st e7 ["S", "S.len", "sp.xm"] [] (expRegs ++ LW) LV :=
    hU6.trans (hU7.mono (by simp) (by simp) hmk (by simp))
  have hl7 : e7.w "lvl" = l - 1 := by
    rw [hU7.wreg _ (by simp)]; simp [he6, State.setW, State.charge]
  -- 8. `lvl := lvl + 1`
  refine runs_wset (a := l) (by
    rw [evalW_add_of (x := l - 1) (y := 1) (by rw [evalW_var, hl7])
      (evalW_lit_of (by rw [hU7'.cap]; omega)) (by rw [hU7'.cap]; omega), hl0]) ?_
  have hU8 : Unchanged st ((e7.setW "lvl" l).charge 1) ["S", "S.len", "sp.xm"] [] (expRegs ++ LW) LV :=
    hU7'.trans ((unch_setW (vr := []) _ _ (mE _ (by simp [expRegs]))).mono (by simp) (by simp)
      (List.Subset.refl _) (by simp))
  have hSe : ∀ a, a ≠ "sp.xm" → e7.wa a = e5.wa a := fun a ha => by
    rw [(hU7.warr a (by simpa using ha)).1]; rfl
  have hc6 : e6.cost = e5.cost + 1 := by simp only [he6, State.charge_cost, State.setW_cost]
  refine ⟨?_, hI.frame st _ hK (hU8.mono (by simp) (by simp) (List.Subset.refl _) (by simp))
      (by simp only [State.charge_cost, State.setW_cost]; omega),
    by simp [State.setW, State.charge], ?_, ?_, hU8, ?_, ?_, ?_, ?_, ?_⟩
  · -- the row
    refine RowRep.of_eq hR5 ?_ ?_ ?_ ?_
    · simp only [State.charge_wlen, State.setW_wlen, hwl7, he6]
    · simp only [State.charge_wlen, State.setW_wlen, hwl7, he6]
    · simp only [State.charge_wa, State.setW_wa]; rw [hSe _ (by decide)]
    · intro i _; simp only [State.charge_wa, State.setW_wa]; rw [hSe _ (by decide)]
  · rw [hU8.wreg _ (nE _ (by simp [expRegs]) (nLW _ (by simp)))]; exact hn
  · funext x
    simp only [State.charge_wa, State.setW_wa]
    rw [hxm7 x, show (ks ++ ks.flatMap (extOf st l n lt (fun x => x ∈ ks))).take ks.length = ks by
      simp, show e6.wa = e5.wa from rfl, (hU5.warr "sp.xm" (by simp)).1, show e4.wa = e3.wa from rfl,
      hxm3 x, List.take_length, (hU2.warr "sp.xm" (by simp)).1]
    by_cases hx : x ∈ ks
    · rw [if_pos hx, hxm x (hks x hx)]
    · rw [if_neg hx, if_neg hx]
  · simp only [State.charge_wlen, State.setW_wlen, hwl7]; exact hwl6
  · intro i hi; simp only [State.charge_wa, State.setW_wa]; rw [hSe _ (by decide)]
    rw [hS5 i hi, (hU4.warr "S" (by simp)).1]
  · intro l' hl'; simp only [State.charge_wa, State.setW_wa]; rw [hSe _ (by decide)]
    rw [hSL5 l' hl', (hU4.warr "S.len" (by simp)).1]
  · simp only [State.charge_cost, State.setW_cost]; omega
  · simp only [State.charge_cost, State.setW_cost, hc7]; omega

end expandSpec2

end Frontier.CHD.RamSpine
