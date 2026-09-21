import Frontier.CHD.RamLevel
import Frontier.CHD.RamSpine
import Frontier.RAMWP

/-!
# RemoveU — BM.15–18 of the recursive spine: the child's `U_i` leaves the groups (agent-06; B-L4, NON-GATE)

Program text = agent-08's `RamSpine.removeU` (RamSpineCode.lean), with the mark written as
`RamLevel.rowAppend "sp.mk" "sp.mk.len" (var "sp.j")` (definitionally the same statement).
For each `x` of the child's `U` row (level `lvl - 1`, in row order) that is a member of group `j`:
`gDel` removes it (swap with the last member), and if `x` is `j`'s pivot the group index `j` is
appended to the mark row `sp.mk` (level `lvl`).

Main theorems:
* `removeLoop_spec`: from `GrpRep st l n p P piv` and the `U` row `xs` (nodup, entries `< n`) with an empty mark
  row, the loop ends with `GrpRep r l n p (fun j => P j \ xs.toFinset) piv` and a mark row `mks` (nodup) with
  `j ∈ mks ↔ j < p ∧ piv j ∈ xs ∧ piv j ∈ P j`, in `≤ 25 |xs| + 1` steps, with an exact frame;
* `removeTail_spec`: the same for `removeTail` (mark-row reset; `sp.i := 0`; loop), `≤ 25 |xs| + 3`;
* `ramSpine_removeU_eq : RamSpine.removeU dsDelB gDelS = removeU dsDelB gDelS := rfl` and
  `removeU_eq_tail : removeU dsDelB gDelS = seq dsDelB (removeTail gDelS) := rfl` (so BM.15–18 is `dsDelB`
  (B-L3 delete) followed by `removeTail_spec`).
Helpers: `inGrp_spec` (one member: `gDel` + pivot mark), `gDel_j` (`gDel` leaves `sp.j = j`), `Runs.and'`
(conjunction of two runs by `exec_det`), `Runs.keep_len'` (length preservation of allocation-free code, from
agent-04's `exec_noalloc_len`), `grpRep_of_eq`, `grpRep_congr`.
-/

namespace Frontier.CHD.RamSpineU

open Frontier.RAM WExpr Stmt Frontier.CHD.RamLevel

variable {V : Type} {ops : VOps V}

/-! ## The program -/

/-- `lvl * n + e` (current row) -/
def cr (e : WExpr) : WExpr := add (mul (var "lvl") (var "n")) e
/-- `(lvl - 1) * n + e` (child row) -/
def chr (e : WExpr) : WExpr := add (mul (sub (var "lvl") (lit 1)) (var "n")) e
/-- `x := x + 1` -/
def incr (x : String) : Stmt := wset x (add (var x) (lit 1))

/-- mark group `sp.j` -/
def markS : Stmt := rowAppend "sp.mk" "sp.mk.len" (var "sp.j")

/-- `px` is a member of group `sp.j - 1`: remove it, mark the group if `px` was its pivot -/
def inGrp (gDelS : Stmt) : Stmt :=
  seq (wset "sp.j" (sub (var "sp.j") (lit 1)))
  (seq (wset "sp.pv" (eq (load "sp.gp" (cr (var "sp.j"))) (var "px")))
  (seq gDelS (ite (var "sp.pv") markS skip)))

def removeBody (gDelS : Stmt) : Stmt :=
  seq (wset "px" (load "U" (chr (var "sp.i"))))
  (seq (wset "sp.j" (load "sp.g" (cr (var "px"))))
  (seq (ite (var "sp.j") (inGrp gDelS) skip)
       (incr "sp.i")))

def removeLoop (gDelS : Stmt) : Stmt :=
  .while (lt (var "sp.i") (load "U.len" (sub (var "lvl") (lit 1)))) (removeBody gDelS)

/-- BM.15–18 -/
def removeU (dsDelB gDelS : Stmt) : Stmt :=
  seq dsDelB
  (seq (wstore "sp.mk.len" (var "lvl") (lit 0))
  (seq (wset "sp.i" (lit 0)) (removeLoop gDelS)))

/-- arrays written by the loop -/
def rmArrs : List String := ["sp.gm", "sp.gpos", "sp.gl", "sp.g", "sp.mk", "sp.mk.len"]
/-- registers written by the loop -/
def rmRegs : List String := ["px", "sp.j", "sp.pv", "sp.i", "sp.q", "sp.t", "sp.y"]
/-- registers written by `inGrp gDel` -/
def igRegs : List String := ["sp.j", "sp.pv", "sp.q", "sp.t", "sp.y"]

/-! ## Generic helpers -/

theorem Runs.and' {c : Stmt} {s : State V} {Q₁ Q₂ : State V → Prop} (h₁ : Runs ops c s Q₁)
    (h₂ : Runs ops c s Q₂) : Runs ops c s (fun r => Q₁ r ∧ Q₂ r) := by
  obtain ⟨f₁, r₁, e₁, q₁⟩ := h₁
  obtain ⟨f₂, r₂, e₂, q₂⟩ := h₂
  obtain rfl := exec_det ops e₁ e₂
  exact ⟨f₁, r₁, e₁, q₁, q₂⟩

/-! Copied from agent-04's `DGlobal` (`NoAlloc`, `exec_noalloc_len`) to avoid a dependency on a module under
revision. -/

/-- no allocation and no procedure call -/
def NoAllocS : Stmt → Prop
  | .walloc _ _ => False
  | .valloc _ _ => False
  | .call _ => False
  | .seq a b => NoAllocS a ∧ NoAllocS b
  | .ite _ a b => NoAllocS a ∧ NoAllocS b
  | .while _ b => NoAllocS b
  | _ => True

/-- the array lengths of a state -/
def LensS {V : Type} (st : State V) : (String → ℕ) × (String → ℕ) := (st.wlen, st.vlen)

theorem exec_noallocS_len {V : Type} (ops : VOps V) :
    ∀ (f : ℕ) (c : Stmt) (st r : State V), NoAllocS c → exec ops f c st = some r → LensS r = LensS st := by
  intro f
  induction f with
  | zero => intro c st r _ h; simp [exec] at h
  | succ f ih =>
    intro c st r hc h
    cases c with
    | skip => simp [exec] at h; subst h; rfl
    | wset x e =>
      cases he : evalW st e with
      | none => simp [exec, he] at h
      | some a => simp [exec, he] at h; subst h; rfl
    | vset x e =>
      cases he : evalV ops st e with
      | none => simp [exec, he] at h
      | some a => simp [exec, he] at h; subst h; rfl
    | vle x a b =>
      cases h1 : evalV ops st a with
      | none => simp [exec, h1] at h
      | some p =>
        cases h2 : evalV ops st b with
        | none => simp [exec, h1, h2] at h
        | some q =>
          cases h3 : fit st.cap (if ops.le p q then 1 else 0) with
          | none => simp [exec, h1, h2, h3] at h
          | some bit => simp [exec, h1, h2, h3] at h; subst h; rfl
    | wstore arr i e =>
      cases h1 : evalW st i with
      | none => simp [exec, h1] at h
      | some j =>
        cases h2 : evalW st e with
        | none => simp [exec, h1, h2] at h
        | some a =>
          by_cases hj : j < st.wlen arr
          · simp [exec, h1, h2, hj] at h; subst h; rfl
          · simp [exec, h1, h2, hj] at h
    | vstore arr i e =>
      cases h1 : evalW st i with
      | none => simp [exec, h1] at h
      | some j =>
        cases h2 : evalV ops st e with
        | none => simp [exec, h1, h2] at h
        | some a =>
          by_cases hj : j < st.vlen arr
          · simp [exec, h1, h2, hj] at h; subst h; rfl
          · simp [exec, h1, h2, hj] at h
    | walloc arr e => exact absurd hc (by simp [NoAllocS])
    | valloc arr e => exact absurd hc (by simp [NoAllocS])
    | call p => exact absurd hc (by simp [NoAllocS])
    | seq a b =>
      rw [exec_seq, Option.bind_eq_some_iff] at h
      obtain ⟨s', h1, h2⟩ := h
      exact (ih b s' r hc.2 h2).trans (ih a st s' hc.1 h1)
    | ite c a b =>
      rw [exec_ite, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h2⟩ := h
      split_ifs at h2
      · exact (ih a _ r hc.1 h2).trans rfl
      · exact (ih b _ r hc.2 h2).trans rfl
    | «while» c b =>
      rw [exec_while, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h2⟩ := h
      split_ifs at h2
      · rw [Option.bind_eq_some_iff] at h2
        obtain ⟨s', h3, h4⟩ := h2
        exact (ih _ s' r hc h4).trans ((ih b _ s' hc h3).trans rfl)
      · simp at h2; subst h2; rfl


/-- `Runs` of an allocation-free statement keeps all array lengths (from agent-04's `exec_noalloc_len`). -/
theorem Runs.keep_len' {c : Stmt} {st : State V} {Q : State V → Prop} (h : Runs ops c st Q)
    (hc : NoAllocS c) : Runs ops c st (fun r => Q r ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen) := by
  obtain ⟨f, r, h1, h2⟩ := h
  have := exec_noallocS_len ops f c st r hc h1
  simp only [LensS, Prod.mk.injEq] at this
  exact ⟨f, r, h1, h2, this.1, this.2⟩

/-- A group table only reads the six group arrays (agent-08's `GrpRep.of_eq`, restated). -/
theorem grpRep_of_eq {st st' : State V} {l n p : ℕ} {P : ℕ → Finset ℕ} {piv : ℕ → ℕ}
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

/-- A group table only sees the groups `j < p`. -/
theorem grpRep_congr {st : State V} {l n p : ℕ} {P P' : ℕ → Finset ℕ} {piv : ℕ → ℕ}
    (h : GrpRep st l n p P piv) (hP : ∀ j < p, P' j = P j) : GrpRep st l n p P' piv := by
  refine ⟨h.len_gm, h.len_gs, h.len_gl, h.len_gp, h.len_gpos, h.len_g, h.p_le, h.seg, h.mem_lt, h.pos,
    h.memb, fun j hj => by rw [hP j hj]; exact h.img j hj, fun x hx => ?_, h.pivs, h.disj⟩
  rcases h.nomemb x hx with h0 | ⟨j, hj, hg, hxP⟩
  · exact Or.inl h0
  · exact Or.inr ⟨j, hj, hg, by rw [hP j hj]; exact hxP⟩

/-- `gDel` leaves the group index of `px` in `sp.j`. -/
theorem gDel_j (st : State V) {l n p : ℕ} {P : ℕ → Finset ℕ} {piv : ℕ → ℕ}
    (h : GrpRep st l n p P piv) (hl : st.w "lvl" = l) (hn : st.w "n" = n) {x j : ℕ}
    (hpx : st.w "px" = x) (hj : j < p) (hxj : x ∈ P j) (hcap : (l + 1) * n < st.cap) :
    Runs ops gDel st (fun st' => st'.w "sp.j" = j) := by
  have hx : x < n ∧ st.wa "sp.g" (l * n + x) = j + 1 := (h.mem_iff hj).mp hxj
  have hxj' := hxj
  rw [h.img j hj, Finset.mem_image] at hxj'
  obtain ⟨qx, hqx, hxq⟩ := hxj'
  rw [Finset.mem_range] at hqx
  have hq0 : st.wa "sp.gpos" (l * n + x) = gs st l n j + qx := by
    rw [← hxq]; exact h.pos j hj qx hqx
  have hseg := h.seg j hj
  have hpn := h.p_le
  have hyl : gl st l n j - 1 < gl st l n j := by omega
  have hylt : gmem st l n (gs st l n j + (gl st l n j - 1)) < n := h.mem_lt j hj _ hyl
  have hyeq : gs st l n j + gl st l n j - 1 = gs st l n j + (gl st l n j - 1) := by omega
  have hrow : ∀ a, a < n → l * n + a < (l + 1) * n := fun a ha => row_index_lt ha
  have hln : l * n < st.cap := by
    have := hrow x hx.1; omega
  have c1 : 1 < st.cap := by have := hrow x hx.1; omega
  have c0 : 0 < st.cap := by omega
  have hadd : gs st l n j + gl st l n j < st.cap := by
    have : n ≤ (l + 1) * n := Nat.le_mul_of_pos_left n (by omega)
    omega
  have f1 : l * n + x < st.cap := by have := hrow x hx.1; omega
  have f2 : l * n + j < st.cap := by have := hrow j (by omega); omega
  have f3 : l * n + (gs st l n j + gl st l n j - 1) < st.cap := by
    have := hrow (gs st l n j + gl st l n j - 1) (by omega); omega
  have f4 : l * n + (gs st l n j + qx) < st.cap := by
    have := hrow (gs st l n j + qx) (by omega); omega
  have f5 : l * n + gmem st l n (gs st l n j + (gl st l n j - 1)) < st.cap := by
    have := hrow _ hylt; omega
  have i1 : l * n + x < st.wlen "sp.g" := by have := hrow x hx.1; have := h.len_g; omega
  have i2 : l * n + x < st.wlen "sp.gpos" := by have := hrow x hx.1; have := h.len_gpos; omega
  have i3 : l * n + j < st.wlen "sp.gs" := by have := hrow j (by omega); have := h.len_gs; omega
  have i4 : l * n + j < st.wlen "sp.gl" := by have := hrow j (by omega); have := h.len_gl; omega
  have i5 : l * n + (gs st l n j + gl st l n j - 1) < st.wlen "sp.gm" := by
    have := hrow (gs st l n j + gl st l n j - 1) (by omega); have := h.len_gm; omega
  have i6 : l * n + (gs st l n j + qx) < st.wlen "sp.gm" := by
    have := hrow (gs st l n j + qx) (by omega); have := h.len_gm; omega
  have i7 : l * n + gmem st l n (gs st l n j + (gl st l n j - 1)) < st.wlen "sp.gpos" := by
    have := hrow _ hylt; have := h.len_gpos; omega
  have hgx : st.wa "sp.g" (l * n + x) = j + 1 := hx.2
  have hgsj : st.wa "sp.gs" (l * n + j) = gs st l n j := rfl
  have hglj : st.wa "sp.gl" (l * n + j) = gl st l n j := rfl
  have hymem : st.wa "sp.gm" (l * n + (gs st l n j + gl st l n j - 1)) =
      gmem st l n (gs st l n j + (gl st l n j - 1)) := by rw [hyeq]; rfl
  apply wp_sound
  simp (config := { decide := true }) only [wp, gDel, rb, evalW_var, evalW_add', evalW_mul',
    evalW_sub', evalW_load', evalW_lit', State.charge_w, State.setW_w, State.charge_wa,
    State.setW_wa, State.storeW_wa, State.charge_wlen, State.setW_wlen, State.storeW_wlen,
    State.charge_cap, State.setW_cap, State.storeW_cap, State.storeW_w, hl, hn, hpx,
    Option.bind_some, fit_of_lt hln, fit_of_lt c1, fit_of_lt c0, fit_of_lt f1, fit_of_lt f2,
    fit_of_lt f3, fit_of_lt f4, fit_of_lt f5, fit_of_lt hadd, i1, i2, i3, i4, i5, i6, i7,
    if_true, hgx, Nat.add_sub_cancel, hgsj, hglj, hq0, hymem, ite_true, ite_false]

/-! ## The loop invariant -/

section Loop

/-- Invariant of the removal loop after `i` rows of the child's `U` row `xs`. -/
structure RInv (st : State V) (l n p : ℕ) (P : ℕ → Finset ℕ) (piv : ℕ → ℕ) (xs : List ℕ) (i : ℕ)
    (t : State V) : Prop where
  ri : t.w "sp.i" = i
  rl : t.w "lvl" = l
  rn : t.w "n" = n
  ile : i ≤ xs.length
  grp : GrpRep t l n p (fun j => P j \ (xs.take i).toFinset) piv
  mkr : ∃ mks : List ℕ, RowRep t "sp.mk" "sp.mk.len" n l mks ∧ mks.Nodup ∧ mks.length ≤ i ∧
    ∀ j, j ∈ mks ↔ j < p ∧ piv j ∈ xs.take i ∧ piv j ∈ P j
  urow : RowRep t "U" "U.len" n (l - 1) xs
  warr : ∀ a, a ∉ rmArrs → t.wa a = st.wa a
  wlen : t.wlen = st.wlen
  va : t.va = st.va
  vlen : t.vlen = st.vlen
  cap : t.cap = st.cap
  procs : t.procs = st.procs
  v : t.v = st.v
  wreg : ∀ y, y ∉ rmRegs → t.w y = st.w y
  rows : ∀ b ∈ grpArrs ++ ["sp.mk"], ∀ q, (q < l * n ∨ (l + 1) * n ≤ q) → t.wa b q = st.wa b q
  mklen : ∀ l', l' ≠ l → t.wa "sp.mk.len" l' = st.wa "sp.mk.len" l'
  lo : st.cost ≤ t.cost
  cost : t.cost ≤ st.cost + 25 * i

theorem take_succ_toFinset {xs : List ℕ} {i : ℕ} (hi : i < xs.length) :
    (xs.take (i + 1)).toFinset = insert xs[i] (xs.take i).toFinset := by
  have h : xs.take (i + 1) = xs.take i ++ [xs[i]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
  rw [h, List.toFinset_append]
  ext y
  simp [or_comm]

theorem getElem_not_mem_take {xs : List ℕ} (hnd : xs.Nodup) {i : ℕ} (hi : i < xs.length) :
    xs[i] ∉ xs.take i := by
  intro h
  obtain ⟨j, hj, hji⟩ := List.getElem_of_mem h
  rw [List.length_take] at hj
  rw [List.getElem_take] at hji
  have := (List.Nodup.getElem_inj_iff hnd).mp hji
  omega

theorem ev_px {s : State V} {l n i : ℕ} {xs : List ℕ} (hl : s.w "lvl" = l) (hl1 : 1 ≤ l) (hn : s.w "n" = n)
    (hi : s.w "sp.i" = i) (hU : RowRep s "U" "U.len" n (l - 1) xs) (hix : i < xs.length)
    (hcap : (l + 1) * n < s.cap) (h1 : 1 < s.cap) :
    evalW s (load "U" (chr (var "sp.i"))) = some xs[i] := by
  obtain ⟨hU1, hU2, -, -, hU5⟩ := hU
  have hle : l - 1 + 1 = l := by omega
  rw [hle] at hU2
  have hidx : (l - 1) * n + i < l * n := by
    have : (l - 1) * n + n = l * n := by
      conv_rhs => rw [← hle]
      ring
    omega
  have hln : l * n ≤ (l + 1) * n := Nat.mul_le_mul_right _ (by omega)
  have c1 : (l - 1) * n < s.cap := by omega
  have c2 : (l - 1) * n + i < s.cap := by omega
  simp only [chr, evalW_load', evalW_add', evalW_mul', evalW_sub', evalW_lit', evalW_var, hl, hn, hi,
    fit_of_lt h1, Option.bind_some, fit_of_lt c1, fit_of_lt c2]
  rw [if_pos (by omega), hU5 i hix]

theorem ev_g {s : State V} {l n x : ℕ} {p : ℕ} {P : ℕ → Finset ℕ} {piv : ℕ → ℕ} (hl : s.w "lvl" = l)
    (hn : s.w "n" = n) (hx : s.w "px" = x) (hxn : x < n) (hG : GrpRep s l n p P piv)
    (hcap : (l + 1) * n < s.cap) :
    evalW s (load "sp.g" (cr (var "px"))) = some (s.wa "sp.g" (l * n + x)) := by
  have hidx : l * n + x < (l + 1) * n := row_index_lt hxn
  have c1 : l * n < s.cap := by omega
  have c2 : l * n + x < s.cap := by omega
  simp only [cr, evalW_load', evalW_add', evalW_mul', evalW_var, hl, hn, hx, Option.bind_some, fit_of_lt c1,
    fit_of_lt c2]
  rw [if_pos (by have := hG.len_g; omega)]

theorem ev_pv {s : State V} {l n x j : ℕ} {p : ℕ} {P : ℕ → Finset ℕ} {piv : ℕ → ℕ} (hl : s.w "lvl" = l)
    (hn : s.w "n" = n) (hx : s.w "px" = x) (hj : s.w "sp.j" = j) (hjp : j < p) (hG : GrpRep s l n p P piv)
    (hcap : (l + 1) * n < s.cap) (h1 : 1 < s.cap) :
    evalW s (eq (load "sp.gp" (cr (var "sp.j"))) (var "px")) = some (if piv j = x then 1 else 0) := by
  have hjn : j < n := lt_of_lt_of_le hjp hG.p_le
  have hidx : l * n + j < (l + 1) * n := row_index_lt hjn
  have c1 : l * n < s.cap := by omega
  have c2 : l * n + j < s.cap := by omega
  rw [evalW_eq_of (x := piv j) (y := x) ?_ (by simp [hx]) h1]
  simp only [cr, evalW_load', evalW_add', evalW_mul', evalW_var, hl, hn, hj, Option.bind_some, fit_of_lt c1,
    fit_of_lt c2]
  rw [if_pos (by have := hG.len_gp; omega), hG.pivs j hjp]

end Loop

/-! ## One member of a group: `inGrp` -/

section InGrp

/-- **`px` leaves its group `j`** (`sp.j = j+1` on entry); `j` is marked iff `px` was its pivot. -/
theorem inGrp_spec {s : State V} {l n p : ℕ} {Pc : ℕ → Finset ℕ} {piv : ℕ → ℕ} {x j : ℕ} {mks : List ℕ}
    (hl : s.w "lvl" = l) (hn : s.w "n" = n) (hx : s.w "px" = x) (hj1 : s.w "sp.j" = j + 1) (hjp : j < p)
    (hG : GrpRep s l n p Pc piv) (hxj : x ∈ Pc j) (hmk : RowRep s "sp.mk" "sp.mk.len" n l mks)
    (hml : mks.length < n) (hcap : (l + 1) * n + 2 < s.cap) :
    Runs ops (inGrp gDel) s (fun r =>
      GrpRep r l n p (Function.update Pc j ((Pc j).erase x)) piv ∧
      RowRep r "sp.mk" "sp.mk.len" n l (if piv j = x then mks ++ [j] else mks) ∧
      (∀ a, a ∉ rmArrs → r.wa a = s.wa a) ∧ r.wlen = s.wlen ∧ r.va = s.va ∧ r.vlen = s.vlen ∧
      r.cap = s.cap ∧ r.procs = s.procs ∧ r.v = s.v ∧ (∀ y, y ∉ igRegs → r.w y = s.w y) ∧
      (∀ b ∈ grpArrs ++ ["sp.mk"], ∀ q, (q < l * n ∨ (l + 1) * n ≤ q) → r.wa b q = s.wa b q) ∧
      (∀ l', l' ≠ l → r.wa "sp.mk.len" l' = s.wa "sp.mk.len" l') ∧
      r.w "lvl" = l ∧ r.w "n" = n ∧ s.cost ≤ r.cost ∧ r.cost ≤ s.cost + 14) := by
  have h1 : 1 < s.cap := by omega
  have hml' : l * n + mks.length < (l + 1) * n := row_index_lt hml
  unfold inGrp
  apply runs_seq
  refine runs_wset (a := j) (by simp [hj1, fit_of_lt h1]) ?_
  apply runs_seq
  refine runs_wset (a := if piv j = x then 1 else 0)
    (ev_pv (s := (s.setW "sp.j" j).charge 1) (by simp [hl]) (by simp [hn]) (by simp [hx]) (by simp) hjp
      (grpRep_of_eq hG (fun _ _ => rfl) (fun _ _ => rfl)) (by simp; omega) (by simpa using h1)) ?_
  apply runs_seq
  have hG4 : GrpRep ((((s.setW "sp.j" j).charge 1).setW "sp.pv" (if piv j = x then 1 else 0)).charge 1)
      l n p Pc piv := grpRep_of_eq hG (fun _ _ => rfl) (fun _ _ => rfl)
  refine (Runs.keep_len' (Runs.and' (gDel_spec (ops := ops) _ hG4 (by simp [hl]) (by simp [hn]) (by simp [hx]) hjp
    hxj (by simp; omega)) (gDel_j (ops := ops) _ hG4 (by simp [hl]) (by simp [hn]) (by simp [hx]) hjp hxj
    (by simp; omega))) (by simp [NoAllocS, gDel])).mono (fun t3 ht3 => ?_)
  obtain ⟨⟨⟨hG3, hU3, hrows3, hc3⟩, hj3⟩, hwl3, hvl3⟩ := ht3
  have hpv3 : t3.w "sp.pv" = if piv j = x then 1 else 0 := by rw [hU3.wreg _ (by decide)]; simp
  have hc3' : t3.cost = s.cost + 10 := by rw [hc3]; simp only [State.charge_cost, State.setW_cost]
  have hwa3 : ∀ a, a ∉ ["sp.gm", "sp.gpos", "sp.gl", "sp.g"] → t3.wa a = s.wa a :=
    fun a ha => (hU3.warr a ha).1
  have hl3 : t3.w "lvl" = l := by rw [hU3.wreg _ (by decide)]; simp [hl]
  have hn3 : t3.w "n" = n := by rw [hU3.wreg _ (by decide)]; simp [hn]
  have hcap3 : t3.cap = s.cap := hU3.cap
  have hpr3 : t3.procs = s.procs := hU3.procs
  have hva3 : t3.va = s.va := funext fun a => (hU3.varr a (by simp)).1
  have hv3 : t3.v = s.v := funext fun a => hU3.vreg a (by simp)
  have hreg3 : ∀ y, y ∉ igRegs → t3.w y = s.w y := by
    intro y hy
    have h' : y ∉ ["sp.j", "sp.q", "sp.t", "sp.y"] := fun h => hy (by simp [igRegs] at h ⊢; tauto)
    rw [hU3.wreg y h']
    have hy1 : y ≠ "sp.pv" := fun e => hy (by simp [e, igRegs])
    have hy2 : y ≠ "sp.j" := fun e => hy (by simp [e, igRegs])
    simp [hy1, hy2]
  have hmkwa : t3.wa "sp.mk" = s.wa "sp.mk" := hwa3 "sp.mk" (by decide)
  have hmklwa : t3.wa "sp.mk.len" = s.wa "sp.mk.len" := hwa3 "sp.mk.len" (by decide)
  have hmk3 : RowRep (t3.charge 1) "sp.mk" "sp.mk.len" n l mks :=
    RowRep.of_eq hmk (by simp [hwl3]) (by simp [hwl3]) (by simp [hmklwa]) (fun q _ => by simp [hmkwa])
  have hgrpne : ∀ a ∈ grpArrs, a ≠ "sp.mk" ∧ a ≠ "sp.mk.len" := by
    intro a ha
    simp only [grpArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
  have hrmne : ∀ a, a ∉ rmArrs → a ≠ "sp.mk" ∧ a ≠ "sp.mk.len" ∧ a ∉ ["sp.gm", "sp.gpos", "sp.gl", "sp.g"] := by
    intro a ha
    refine ⟨fun e => ha (by simp [e, rmArrs]), fun e => ha (by simp [e, rmArrs]), fun h => ha ?_⟩
    simp [rmArrs] at h ⊢; tauto
  by_cases hpx : piv j = x
  · refine runs_ite_true (by rw [evalW_var, hpv3, if_pos hpx]) one_ne_zero ?_
    refine (Runs.keep_len' (rowAppend_spec (ops := ops) (v := j) (t3.charge 1) (by decide) hmk3 (by simp [hl3])
      (by simp [hn3]) hml (by simp [hj3]) (by simp [hcap3]; omega)) (by simp [NoAllocS, rowAppend])).mono
      (fun t4 ht4 => ?_)
    obtain ⟨⟨hmk4, hU4, harr4, hlen4, hoth4, hc4, -⟩, hwl4, hvl4⟩ := ht4
    refine ⟨grpRep_of_eq hG3 (fun a ha => (hoth4 a (hgrpne a ha).1 (hgrpne a ha).2))
      (fun a _ => by rw [hwl4]; rfl), by rw [if_pos hpx]; exact hmk4,
      fun a ha => by rw [hoth4 a (hrmne a ha).1 (hrmne a ha).2.1]; exact hwa3 a (hrmne a ha).2.2,
      by rw [hwl4]; exact hwl3, ?_, by rw [hvl4]; exact hvl3, by rw [hU4.cap]; exact hcap3,
      by rw [hU4.procs]; exact hpr3, ?_, fun y hy => by rw [hU4.wreg y (by simp)]; exact hreg3 y hy,
      fun b hb q hq => ?_, fun l' hl' => by rw [hlen4 l' hl']; exact congrFun hmklwa l',
      by rw [hU4.wreg _ (by simp)]; exact hl3, by rw [hU4.wreg _ (by simp)]; exact hn3,
      by rw [hc4]; simp; omega, by rw [hc4]; simp; omega⟩
    · funext a; rw [(hU4.varr a (by simp)).1]; exact congrFun hva3 a
    · funext a; rw [hU4.vreg a (by simp)]; exact congrFun hv3 a
    · rcases List.mem_append.mp hb with hb | hb
      · rw [hoth4 b (hgrpne b hb).1 (hgrpne b hb).2, State.charge_wa, hrows3 b hb q hq]; rfl
      · simp only [List.mem_singleton] at hb
        subst hb
        have hq' : q ≠ l * n + mks.length := by omega
        rw [harr4 q hq']
        exact congrFun hmkwa q
  · refine runs_ite_false (by rw [evalW_var, hpv3, if_neg hpx]) (runs_skip ?_)
    have hmk5 : RowRep ((t3.charge 1).charge 1) "sp.mk" "sp.mk.len" n l (if piv j = x then mks ++ [j] else mks) := by
      rw [if_neg hpx]; exact RowRep.of_eq hmk3 rfl rfl rfl (fun _ _ => rfl)
    refine ⟨grpRep_of_eq hG3 (fun _ _ => rfl) (fun _ _ => rfl), hmk5, fun a ha => hwa3 a (hrmne a ha).2.2, hwl3, hva3, hvl3, hcap3, hpr3, hv3,
      fun y hy => hreg3 y hy, fun b hb q hq => ?_, fun l' _ => congrFun hmklwa l', hl3, hn3,
      by simp; omega, by simp; omega⟩
    rcases List.mem_append.mp hb with hb | hb
    · exact hrows3 b hb q hq
    · simp only [List.mem_singleton] at hb
      subst hb
      exact congrFun hmkwa q

end InGrp

/-! ## The loop step -/

section Step

theorem rstep {st t : State V} {l n p : ℕ} {P : ℕ → Finset ℕ} {piv : ℕ → ℕ} {xs : List ℕ} {i : ℕ}
    (hG0 : GrpRep st l n p P piv) (hl1 : 1 ≤ l) (hnd : xs.Nodup) (hxs : ∀ x ∈ xs, x < n)
    (hcap : (l + 1) * n + 2 < st.cap) (hR : RInv st l n p P piv xs i t) (hi : i < xs.length) :
    Runs ops (removeBody gDel) (t.charge 1) (RInv st l n p P piv xs (i + 1)) := by
  obtain ⟨mks, hmk, hmnd, hmlen, hmiff⟩ := hR.mkr
  have hcapt : (l + 1) * n + 2 < t.cap := by rw [hR.cap]; exact hcap
  have h1 : 1 < t.cap := by omega
  have hxn : xs[i] < n := hxs _ (List.getElem_mem hi)
  have hxnot : xs[i] ∉ xs.take i := getElem_not_mem_take hnd hi
  have hxnotF : xs[i] ∉ (xs.take i).toFinset := by simpa using hxnot
  have hins := take_succ_toFinset hi
  have hxsn : xs.length ≤ n := hR.urow.1
  have hnln : n ≤ (l + 1) * n := Nat.le_mul_of_pos_left n (by omega)
  have huniq : ∀ j j', j < p → j' < p → xs[i] ∈ P j → xs[i] ∈ P j' → j = j' := by
    intro j j' hj hj' h h'
    have e1 := ((hG0.mem_iff hj).mp h).2
    have e2 := ((hG0.mem_iff hj').mp h').2
    omega
  have hmemI : ∀ y, y ∈ xs.take (i + 1) ↔ y ∈ xs.take i ∨ y = xs[i] := by
    intro y
    have := congrArg (fun S : Finset ℕ => y ∈ S) hins
    simpa [or_comm] using this
  unfold removeBody
  -- `px := U[(l-1) n + i]`
  apply runs_seq
  refine runs_wset (a := xs[i]) (ev_px (s := t.charge 1) (by simpa using hR.rl) hl1 (by simpa using hR.rn)
    (by simpa using hR.ri) (RowRep.of_eq hR.urow rfl rfl rfl (fun _ _ => rfl)) hi (by simp; omega)
    (by simpa using h1)) ?_
  -- `sp.j := g[l n + px]`
  apply runs_seq
  have hG1 : GrpRep (((t.charge 1).setW "px" xs[i]).charge 1) l n p (fun j => P j \ (xs.take i).toFinset) piv :=
    grpRep_of_eq hR.grp (fun _ _ => rfl) (fun _ _ => rfl)
  refine runs_wset (a := t.wa "sp.g" (l * n + xs[i]))
    (ev_g (s := ((t.charge 1).setW "px" xs[i]).charge 1) (by simp [hR.rl]) (by simp [hR.rn]) (by simp)
    hxn hG1 (by simp; omega)) ?_
  apply runs_seq
  rcases hR.grp.nomemb xs[i] hxn with h0 | ⟨j, hj, hgj, hxj⟩
  · -- not a member of any group
    refine runs_ite_false (by simp [h0]) (runs_skip ?_)
    refine runs_wset (evalW_add_of (x := i) (y := 1) (by simp [hR.ri]) (evalW_lit_of (by simpa using h1))
      (by simp; omega)) ?_
    have hnotP : ∀ j < p, xs[i] ∉ P j := by
      intro j hj hx
      have hx' : xs[i] ∈ P j \ (xs.take i).toFinset := Finset.mem_sdiff.mpr ⟨hx, hxnotF⟩
      have := ((hR.grp.mem_iff hj).mp hx').2
      omega
    refine ⟨by simp, by simp [hR.rl], by simp [hR.rn], by omega, ?_, ⟨mks, RowRep.of_eq hmk rfl rfl rfl
      (fun _ _ => rfl), hmnd, by omega, fun j' => ?_⟩, RowRep.of_eq hR.urow rfl rfl rfl (fun _ _ => rfl),
      fun a ha => hR.warr a ha, hR.wlen, hR.va, hR.vlen, hR.cap, hR.procs, hR.v, fun y hy => ?_,
      fun b hb q hq => hR.rows b hb q hq, fun l' hl' => hR.mklen l' hl', by simp; have := hR.lo; omega,
      by simp; have := hR.cost; omega⟩
    · refine grpRep_congr (grpRep_of_eq hR.grp (fun _ _ => rfl) (fun _ _ => rfl)) (fun j' hj' => ?_)
      rw [hins, Finset.sdiff_insert_of_notMem (hnotP j' hj')]
    · rw [hmiff j', hmemI]
      constructor
      · rintro ⟨h1', h2', h3'⟩; exact ⟨h1', Or.inl h2', h3'⟩
      · rintro ⟨h1', h2' | h2', h3'⟩
        · exact ⟨h1', h2', h3'⟩
        · exact absurd (h2' ▸ h3') (hnotP j' h1')
    · have hy' : y ≠ "px" ∧ y ≠ "sp.j" ∧ y ≠ "sp.i" := by
        refine ⟨fun e => hy (by simp [e, rmRegs]), fun e => hy (by simp [e, rmRegs]),
          fun e => hy (by simp [e, rmRegs])⟩
      simp [hy'.1, hy'.2.1, hy'.2.2]
      exact hR.wreg y hy
  · -- member of group `j`
    have hxPj : xs[i] ∈ P j := (Finset.mem_sdiff.mp hxj).1
    have hotherP : ∀ j' < p, j' ≠ j → xs[i] ∉ P j' := fun j' hj' hne hx => hne (huniq j' j hj' hj hx hxPj)
    refine runs_ite_true (x := j + 1) (by simp [hgj]) (by omega) ?_
    refine (inGrp_spec (s := (((((t.charge 1).setW "px" xs[i]).charge 1).setW "sp.j"
        (t.wa "sp.g" (l * n + xs[i]))).charge 1).charge 1) (x := xs[i]) (j := j) (mks := mks)
      (Pc := fun j => P j \ (xs.take i).toFinset) (by simp [hR.rl]) (by simp [hR.rn]) (by simp) (by simp [hgj]) hj
      (grpRep_of_eq hR.grp (fun _ _ => rfl) (fun _ _ => rfl)) hxj (RowRep.of_eq hmk rfl rfl rfl (fun _ _ => rfl))
      (by omega) (by simp; omega)).mono (fun r hr => ?_)
    obtain ⟨hGr, hmkr, hwar, hwlr, hvar, hvlr, hcapr, hprr, hvr, hregr, hrowsr, hmklr, hlr, hnr, hlor, hcr⟩ := hr
    have hir : r.w "sp.i" = i := by rw [hregr _ (by decide)]; simp [hR.ri]
    refine runs_wset (evalW_add_of (x := i) (y := 1) (by simp [hir]) (evalW_lit_of (by rw [hcapr]; simp; omega))
      (by rw [hcapr]; simp; omega)) ?_
    have hjnot : piv j = xs[i] → j ∉ mks := fun hpx h => hxnot (by rw [← hpx]; exact ((hmiff j).mp h).2.1)
    refine ⟨by simp, by simp [hlr], by simp [hnr], by omega, ?_, ⟨if piv j = xs[i] then mks ++ [j] else mks,
      RowRep.of_eq hmkr rfl rfl rfl (fun _ _ => rfl), ?_, ?_, fun j' => ?_⟩, ?_, fun a ha => ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, fun y hy => ?_, fun b hb q hq => ?_, fun l' hl' => ?_, ?_, ?_⟩
    · refine grpRep_congr (grpRep_of_eq hGr (fun _ _ => rfl) (fun _ _ => rfl)) (fun j' hj' => ?_)
      rw [hins]
      by_cases hjj : j' = j
      · subst hjj
        rw [Function.update_self]
        exact Finset.sdiff_insert _ _ _
      · rw [Function.update_of_ne hjj, Finset.sdiff_insert_of_notMem (hotherP j' hj' hjj)]
    · by_cases hpx : piv j = xs[i]
      · rw [if_pos hpx]
        exact hmnd.append (List.nodup_singleton _) (by simpa using hjnot hpx)
      · rw [if_neg hpx]; exact hmnd
    · by_cases hpx : piv j = xs[i]
      · rw [if_pos hpx]; simp; omega
      · rw [if_neg hpx]; omega
    · rw [hmemI]
      by_cases hpx : piv j = xs[i]
      · rw [if_pos hpx, List.mem_append, List.mem_singleton, hmiff j']
        constructor
        · rintro (⟨h1, h2, h3⟩ | rfl)
          · exact ⟨h1, Or.inl h2, h3⟩
          · exact ⟨hj, Or.inr hpx, hpx ▸ hxPj⟩
        · rintro ⟨h1, h2 | h2, h3⟩
          · exact Or.inl ⟨h1, h2, h3⟩
          · exact Or.inr (huniq j' j h1 hj (h2 ▸ h3) hxPj)
      · rw [if_neg hpx, hmiff j']
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨h1, Or.inl h2, h3⟩
        · rintro ⟨h1, h2 | h2, h3⟩
          · exact ⟨h1, h2, h3⟩
          · exfalso
            have := huniq j' j h1 hj (h2 ▸ h3) hxPj
            subst this
            exact hpx h2
    · refine RowRep.of_eq hR.urow ?_ ?_ ?_ (fun q _ => ?_)
      · simp only [State.charge_wlen, State.setW_wlen]; rw [hwlr]; rfl
      · simp only [State.charge_wlen, State.setW_wlen]; rw [hwlr]; rfl
      · simp only [State.charge_wa, State.setW_wa]; rw [hwar "U.len" (by decide)]; rfl
      · simp only [State.charge_wa, State.setW_wa]; rw [hwar "U" (by decide)]; rfl
    · simp only [State.charge_wa, State.setW_wa]; rw [hwar a ha]; exact hR.warr a ha
    · simp only [State.charge_wlen, State.setW_wlen]; rw [hwlr]; exact hR.wlen
    · simp only [State.charge_va, State.setW_va]; rw [hvar]; exact hR.va
    · simp only [State.charge_vlen, State.setW_vlen]; rw [hvlr]; exact hR.vlen
    · simp only [State.charge_cap, State.setW_cap]; rw [hcapr]; exact hR.cap
    · simp only [State.charge_procs, State.setW_procs]; rw [hprr]; exact hR.procs
    · simp only [State.charge_v, State.setW_v]; rw [hvr]; exact hR.v
    · have hyi : y ≠ "sp.i" := fun e => hy (by simp [e, rmRegs])
      have hyg : y ∉ igRegs := fun h => hy (by simp [igRegs] at h; simp [rmRegs]; tauto)
      have hyp : y ≠ "px" := fun e => hy (by simp [e, rmRegs])
      have hyj : y ≠ "sp.j" := fun e => hy (by simp [e, rmRegs])
      simp only [State.charge_w, State.setW_w, if_neg hyi]
      rw [hregr y hyg]
      simp [hyp, hyj]
      exact hR.wreg y hy
    · simp only [State.charge_wa, State.setW_wa]; rw [hrowsr b hb q hq]; exact hR.rows b hb q hq
    · simp only [State.charge_wa, State.setW_wa]; rw [hmklr l' hl']; exact hR.mklen l' hl'
    · have h1 := hR.lo; simp at hlor ⊢; omega
    · have h2 := hR.cost; simp at hcr ⊢; omega

end Step

/-! ## The removal loop (BM.15–18 after `dsDelB` and the mark reset) -/

section LoopSpec

theorem ev_ulen {s : State V} {l n : ℕ} {xs : List ℕ} (hl : s.w "lvl" = l) (hl1 : 1 ≤ l)
    (hU : RowRep s "U" "U.len" n (l - 1) xs) (h1 : 1 < s.cap) :
    evalW s (load "U.len" (sub (var "lvl") (lit 1))) = some xs.length := by
  obtain ⟨-, -, hU3, hU4, -⟩ := hU
  simp only [evalW_load', evalW_sub', evalW_lit', evalW_var, hl, fit_of_lt h1, Option.bind_some]
  rw [if_pos hU3, hU4]

/-- **BM.15–18's loop**: every vertex of the child's `U` row leaves its group; the groups whose pivot left
while a member are listed (once each) in the mark row. -/
theorem removeLoop_spec {st : State V} {l n p : ℕ} {P : ℕ → Finset ℕ} {piv : ℕ → ℕ} {xs : List ℕ}
    (hl : st.w "lvl" = l) (hl1 : 1 ≤ l) (hn : st.w "n" = n) (hi0 : st.w "sp.i" = 0)
    (hG : GrpRep st l n p P piv) (hU : RowRep st "U" "U.len" n (l - 1) xs) (hnd : xs.Nodup)
    (hxs : ∀ x ∈ xs, x < n) (hM : RowRep st "sp.mk" "sp.mk.len" n l []) (hcap : (l + 1) * n + 2 < st.cap) :
    Runs ops (removeLoop gDel) st (fun r =>
      GrpRep r l n p (fun j => P j \ xs.toFinset) piv ∧
      (∃ mks : List ℕ, RowRep r "sp.mk" "sp.mk.len" n l mks ∧ mks.Nodup ∧
        ∀ j, j ∈ mks ↔ j < p ∧ piv j ∈ xs ∧ piv j ∈ P j) ∧
      (∀ a, a ∉ rmArrs → r.wa a = st.wa a) ∧ r.wlen = st.wlen ∧ r.va = st.va ∧ r.vlen = st.vlen ∧
      r.cap = st.cap ∧ r.procs = st.procs ∧ r.v = st.v ∧ (∀ y, y ∉ rmRegs → r.w y = st.w y) ∧
      (∀ b ∈ grpArrs ++ ["sp.mk"], ∀ q, (q < l * n ∨ (l + 1) * n ≤ q) → r.wa b q = st.wa b q) ∧
      (∀ l', l' ≠ l → r.wa "sp.mk.len" l' = st.wa "sp.mk.len" l') ∧
      r.w "lvl" = l ∧ r.w "n" = n ∧ r.w "sp.i" = xs.length ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + 25 * xs.length + 1) := by
  have h1 : 1 < st.cap := by omega
  unfold removeLoop
  refine runs_while (fun i t => RInv st l n p P piv xs i t) xs.length _ ?_ ?_ st
    ⟨hi0, hl, hn, Nat.zero_le _, grpRep_congr hG (fun j _ => by simp), ⟨[], hM, List.nodup_nil, le_rfl,
      fun j => by simp⟩, hU, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ _ _ => rfl,
      fun _ _ => rfl, le_rfl, by simp⟩
  · intro i hi t hR
    have ht1 : 1 < t.cap := by rw [hR.cap]; exact h1
    refine ⟨1, ?_, one_ne_zero, rstep hG hl1 hnd hxs hcap hR hi⟩
    rw [evalW_lt_of (x := i) (y := xs.length) (by simp [hR.ri]) (ev_ulen hR.rl hl1 hR.urow ht1) ht1, if_pos hi]
  · intro t hR
    have ht1 : 1 < t.cap := by rw [hR.cap]; exact h1
    obtain ⟨mks, hmk, hmnd, -, hmiff⟩ := hR.mkr
    have htake : xs.take xs.length = xs := List.take_length
    refine ⟨?_, ?_⟩
    · rw [evalW_lt_of (x := xs.length) (y := xs.length) (by simp [hR.ri]) (ev_ulen hR.rl hl1 hR.urow ht1) ht1]
      simp
    · refine ⟨grpRep_congr (grpRep_of_eq hR.grp (fun _ _ => rfl) (fun _ _ => rfl)) (fun j _ => by rw [htake]),
        ⟨mks, RowRep.of_eq hmk rfl rfl rfl (fun _ _ => rfl), hmnd, fun j => by rw [hmiff j, htake]⟩,
        fun a ha => hR.warr a ha, hR.wlen, hR.va, hR.vlen, hR.cap, hR.procs, hR.v, fun y hy => hR.wreg y hy,
        fun b hb q hq => hR.rows b hb q hq, fun l' hl' => hR.mklen l' hl', by simp [hR.rl], by simp [hR.rn],
        by simp [hR.ri], by simp; have := hR.lo; omega, by simp; have := hR.cost; omega⟩

end LoopSpec

/-! ## BM.15–18 after the `D` deletion, and the link to agent-08's program text -/

section Tail

/-- The part of `removeU` after the `D` deletion `dsDelB`. -/
def removeTail (gDelS : Stmt) : Stmt :=
  seq (wstore "sp.mk.len" (var "lvl") (lit 0)) (seq (wset "sp.i" (lit 0)) (removeLoop gDelS))

theorem removeU_eq_tail (dsDelB gDelS : Stmt) : removeU dsDelB gDelS = seq dsDelB (removeTail gDelS) := rfl

/-- **agent-08's program text is ours** (`RamSpine.removeU`, installed 17:16). -/
theorem ramSpine_removeU_eq (dsDelB gDelS : Stmt) : RamSpine.removeU dsDelB gDelS = removeU dsDelB gDelS := rfl

/-- **BM.15–18 after `dsDelB`**: reset the mark row, then the removal loop. -/
theorem removeTail_spec {st : State V} {l n p : ℕ} {P : ℕ → Finset ℕ} {piv : ℕ → ℕ} {xs : List ℕ}
    (hl : st.w "lvl" = l) (hl1 : 1 ≤ l) (hn : st.w "n" = n)
    (hG : GrpRep st l n p P piv) (hU : RowRep st "U" "U.len" n (l - 1) xs) (hnd : xs.Nodup)
    (hxs : ∀ x ∈ xs, x < n) (hmkl : (l + 1) * n ≤ st.wlen "sp.mk") (hmkll : l < st.wlen "sp.mk.len")
    (hcap : (l + 1) * n + 2 < st.cap) :
    Runs ops (removeTail gDel) st (fun r =>
      GrpRep r l n p (fun j => P j \ xs.toFinset) piv ∧
      (∃ mks : List ℕ, RowRep r "sp.mk" "sp.mk.len" n l mks ∧ mks.Nodup ∧
        ∀ j, j ∈ mks ↔ j < p ∧ piv j ∈ xs ∧ piv j ∈ P j) ∧
      (∀ a, a ∉ rmArrs → r.wa a = st.wa a) ∧ r.wlen = st.wlen ∧ r.va = st.va ∧ r.vlen = st.vlen ∧
      r.cap = st.cap ∧ r.procs = st.procs ∧ r.v = st.v ∧ (∀ y, y ∉ rmRegs → r.w y = st.w y) ∧
      (∀ b ∈ grpArrs ++ ["sp.mk"], ∀ q, (q < l * n ∨ (l + 1) * n ≤ q) → r.wa b q = st.wa b q) ∧
      (∀ l', l' ≠ l → r.wa "sp.mk.len" l' = st.wa "sp.mk.len" l') ∧
      r.w "lvl" = l ∧ r.w "n" = n ∧ st.cost ≤ r.cost ∧ r.cost ≤ st.cost + 25 * xs.length + 3) := by
  have h1 : 1 < st.cap := by omega
  unfold removeTail
  apply runs_seq
  refine (Runs.keep_len' (rowReset_spec (ops := ops) (arr := "sp.mk") (len := "sp.mk.len") (n := n) st hl hmkll
    hmkl (by omega)) (by simp [NoAllocS, rowReset])).mono (fun s1 hs1 => ?_)
  obtain ⟨⟨hM1, hU1, hlen1, hoth1, hc1⟩, hwl1, hvl1⟩ := hs1
  have hwa1 : ∀ b, b ≠ "sp.mk.len" → s1.wa b = st.wa b := hoth1
  apply runs_seq
  refine runs_wset (evalW_lit_of (by rw [hU1.cap]; omega)) ?_
  have hl1' : ((s1.setW "sp.i" 0).charge 1).w "lvl" = l := by simp; rw [hU1.wreg _ (by simp)]; exact hl
  have hn1' : ((s1.setW "sp.i" 0).charge 1).w "n" = n := by simp; rw [hU1.wreg _ (by simp)]; exact hn
  have hgrp : ∀ a ∈ grpArrs, ((s1.setW "sp.i" 0).charge 1).wa a = st.wa a := by
    intro a ha
    simp only [State.charge_wa, State.setW_wa]
    refine hwa1 a ?_
    simp only [grpArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine (removeLoop_spec (ops := ops) hl1' hl1 hn1' (by simp)
    (grpRep_of_eq hG hgrp (fun a _ => by simp [hwl1]))
    (RowRep.of_eq hU (by simp [hwl1]) (by simp [hwl1]) (by simp; rw [hwa1 _ (by decide)])
      (fun q _ => by simp; rw [hwa1 _ (by decide)]))
    hnd hxs (RowRep.of_eq hM1 rfl rfl rfl (fun _ _ => rfl)) (by simp [hU1.cap]; omega)).mono (fun r hr => ?_)
  obtain ⟨hGr, hmkr, hwar, hwlr, hvar, hvlr, hcapr, hprr, hvr, hregr, hrowsr, hmklr, hlr, hnr, -, hlor, hcr⟩ := hr
  refine ⟨hGr, hmkr, fun a ha => ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun y hy => ?_, fun b hb q hq => ?_, fun l' hl' => ?_,
    hlr, hnr, ?_, ?_⟩
  · have hne : a ≠ "sp.mk.len" := fun e => ha (by simp [e, rmArrs])
    rw [hwar a ha]; simp only [State.charge_wa, State.setW_wa]; exact hwa1 a hne
  · rw [hwlr]; simp only [State.charge_wlen, State.setW_wlen]; exact hwl1
  · rw [hvar]; simp only [State.charge_va, State.setW_va]; exact funext fun a => (hU1.varr a (by simp)).1
  · rw [hvlr]; simp only [State.charge_vlen, State.setW_vlen]; exact hvl1
  · rw [hcapr]; simp only [State.charge_cap, State.setW_cap]; exact hU1.cap
  · rw [hprr]; simp only [State.charge_procs, State.setW_procs]; exact hU1.procs
  · rw [hvr]; simp only [State.charge_v, State.setW_v]; exact funext fun a => hU1.vreg a (by simp)
  · have hyi : y ≠ "sp.i" := fun e => hy (by simp [e, rmRegs])
    rw [hregr y hy]; simp only [State.charge_w, State.setW_w, if_neg hyi]; exact hU1.wreg y (by simp)
  · rw [hrowsr b hb q hq]; simp only [State.charge_wa, State.setW_wa]
    refine congrFun (hwa1 b ?_) q
    rcases List.mem_append.mp hb with hb | hb
    · simp only [grpArrs, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · simp only [List.mem_singleton] at hb; subst hb; decide
  · rw [hmklr l' hl']; simp only [State.charge_wa, State.setW_wa]; exact hlen1 l' hl'
  · simp at hlor; omega
  · simp at hcr; omega

end Tail

end Frontier.CHD.RamSpineU
