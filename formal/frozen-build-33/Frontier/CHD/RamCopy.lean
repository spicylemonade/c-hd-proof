import Frontier.CHD.RamInit
import Frontier.CHD.PartitionRAM3

/-!
# Frontier.CHD.RamCopy — BM.4½: the groups of FindPivots into the level-`l` group table (agent-01)

**NON-GATE** (B-L4, Layer B).  FindPivots/PT (agent-03's `ptProg`) leaves the groups `Gs` in the
compact scratch layout `GrpOut` (`pt.ng`, `pt.GO`, `pt.GL`, `pt.GV`).  `copyGrp` copies them into
row `l = lvl` of agent-08's group table (`RamLevel.GrpRep`: `sp.gs/gl/gm/gpos/g`, count `sp.np[l]`),
where they live for the whole call (children overwrite the `pt.*` scratch).
-/

namespace Frontier.CHD.RamInit

open Frontier.RAM WExpr Stmt Frontier.CHD.RamLevel Frontier.CHD.PartitionRAM

variable {V : Type} {ops : VOps V}

/-! ## Offsets -/

/-- The offset of group `j` in the compact layout. -/
def goff (Gs : List (List ℕ)) (j : ℕ) : ℕ := ((Gs.take j).map List.length).sum

theorem goff_succ (Gs : List (List ℕ)) {j : ℕ} (hj : j < Gs.length) :
    goff Gs (j + 1) = goff Gs j + Gs[j].length := by
  unfold goff
  rw [List.take_succ, List.map_append, List.sum_append, List.getElem?_eq_getElem hj]
  simp

theorem goff_mono (Gs : List (List ℕ)) {j j' : ℕ} (h : j ≤ j') : goff Gs j ≤ goff Gs j' := by
  unfold goff
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, List.map_append, List.sum_append]
  omega

theorem goff_le_total (Gs : List (List ℕ)) (j : ℕ) : goff Gs j ≤ (Gs.map List.length).sum := by
  unfold goff
  exact List.Sublist.sum_le_sum ((List.take_sublist j Gs).map _) (fun _ _ => Nat.zero_le _)

theorem goff_add_le (Gs : List (List ℕ)) {j : ℕ} (hj : j < Gs.length) :
    goff Gs j + Gs[j].length ≤ (Gs.map List.length).sum := by
  rw [← goff_succ Gs hj]; exact goff_le_total Gs (j + 1)

/-- Distinct slots of the compact layout have distinct offsets. -/
theorem goff_inj (Gs : List (List ℕ)) {j j' q q' : ℕ} (hj : j < Gs.length) (hj' : j' < Gs.length)
    (hq : q < Gs[j].length) (hq' : q' < Gs[j'].length) (h : goff Gs j + q = goff Gs j' + q') :
    j = j' ∧ q = q' := by
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · have h1 := goff_succ Gs hj
    have h2 := goff_mono Gs (show j + 1 ≤ j' by omega)
    omega
  · subst heq; exact ⟨rfl, by omega⟩
  · have h1 := goff_succ Gs hj'
    have h2 := goff_mono Gs (show j' + 1 ≤ j by omega)
    omega

/-! ## The program -/

def cgRegs : List String := ["cg.j", "cg.o", "cg.len", "cg.q", "cg.x"]
def cgArrs : List String := ["sp.np", "sp.gs", "sp.gl", "sp.gm", "sp.gpos", "sp.g"]

/-- The members of the current group `cg.j`. -/
def cgInner : Stmt :=
  .while (lt (var "cg.q") (var "cg.len"))
    (seq (wset "cg.x" (load "pt.GV" (add (var "cg.o") (var "cg.q"))))
    (seq (wstore "sp.gm" (rb (add (var "cg.o") (var "cg.q"))) (var "cg.x"))
    (seq (wstore "sp.gpos" (rb (var "cg.x")) (add (var "cg.o") (var "cg.q")))
    (seq (wstore "sp.g" (rb (var "cg.x")) (add (var "cg.j") (lit 1)))
         (incr "cg.q")))))

/-- One group. -/
def cgBody : Stmt :=
  seq (wset "cg.o" (load "pt.GO" (var "cg.j")))
  (seq (wset "cg.len" (load "pt.GL" (var "cg.j")))
  (seq (wset "cg.q" (lit 0))
  (seq cgInner
  (seq (wstore "sp.gs" (rb (var "cg.j")) (var "cg.o"))
  (seq (wstore "sp.gl" (rb (var "cg.j")) (var "cg.len"))
       (incr "cg.j"))))))

/-- **BM.4½**: copy the groups into row `lvl` of the group table. -/
def copyGrp : Stmt :=
  seq (wstore "sp.np" (var "lvl") (var "pt.ng"))
  (seq (wset "cg.j" (lit 0))
  (.while (lt (var "cg.j") (var "pt.ng")) cgBody))

/-! ## The invariant -/

/-- The copy state after all of the groups `j' < j` and the first `q` members of group `j`. -/
structure CgInv (st r : State V) (l n : ℕ) (Gs : List (List ℕ)) (j q : ℕ) : Prop where
  gs : ∀ j' (h : j' < Gs.length), j' < j → r.wa "sp.gs" (l * n + j') = goff Gs j'
  gl : ∀ j' (h : j' < Gs.length), j' < j → r.wa "sp.gl" (l * n + j') = Gs[j'].length
  done : ∀ j' (h : j' < Gs.length) q' (hq : q' < Gs[j'].length), (j' < j ∨ (j' = j ∧ q' < q)) →
    r.wa "sp.gm" (l * n + (goff Gs j' + q')) = Gs[j'][q'] ∧
    r.wa "sp.gpos" (l * n + Gs[j'][q']) = goff Gs j' + q' ∧
    r.wa "sp.g" (l * n + Gs[j'][q']) = j' + 1
  fresh : ∀ x < n, (∀ j' (h : j' < Gs.length) q' (hq : q' < Gs[j'].length),
    (j' < j ∨ (j' = j ∧ q' < q)) → Gs[j'][q'] ≠ x) → r.wa "sp.g" (l * n + x) = 0
  np : r.wa "sp.np" l = Gs.length
  unch : Unchanged st r cgArrs [] cgRegs []
  wlen : r.wlen = st.wlen
  rows : ∀ a ∈ cgArrs, a ≠ "sp.np" → ∀ i, (i < l * n ∨ (l + 1) * n ≤ i) → r.wa a i = st.wa a i
  npo : ∀ l', l' ≠ l → r.wa "sp.np" l' = st.wa "sp.np" l'

theorem CgInv.charge {st r : State V} {l n : ℕ} {Gs : List (List ℕ)} {j q : ℕ}
    (h : CgInv st r l n Gs j q) (k : ℕ) : CgInv st (r.charge k) l n Gs j q :=
  ⟨h.gs, h.gl, h.done, h.fresh, h.np, by rw [unch_charge]; exact h.unch, by simp [h.wlen], h.rows,
    h.npo⟩

theorem CgInv.setW {st r : State V} {l n : ℕ} {Gs : List (List ℕ)} {j q : ℕ}
    (h : CgInv st r l n Gs j q) {x : String} (hx : x ∈ cgRegs) (a : ℕ) :
    CgInv st (r.setW x a) l n Gs j q :=
  ⟨h.gs, h.gl, h.done, h.fresh, h.np, by rw [unch_setW hx]; exact h.unch, by simp [h.wlen], h.rows,
    h.npo⟩


/-! ## The copy is correct -/

section copySpec

variable {st0 : State V} {l n : ℕ} {Gs : List (List ℕ)}

/-- The standing hypotheses of the copy. -/
structure CgHyp (st0 : State V) (l n : ℕ) (Gs : List (List ℕ)) : Prop where
  out : GrpOut st0 Gs
  lvl : st0.w "lvl" = l
  nn : st0.w "n" = n
  mem : ∀ j (h : j < Gs.length) q (hq : q < Gs[j].length), Gs[j][q] < n
  dist : ∀ j (h : j < Gs.length) q (hq : q < Gs[j].length) j' (h' : j' < Gs.length)
    q' (hq' : q' < Gs[j'].length), Gs[j][q] = Gs[j'][q'] → j = j' ∧ q = q'
  ne : ∀ j (h : j < Gs.length), Gs[j] ≠ []
  tot : (Gs.map List.length).sum ≤ n
  g0 : ∀ x < n, st0.wa "sp.g" (l * n + x) = 0
  lgm : (l + 1) * n ≤ st0.wlen "sp.gm"
  lgs : (l + 1) * n ≤ st0.wlen "sp.gs"
  lgl : (l + 1) * n ≤ st0.wlen "sp.gl"
  lgp : (l + 1) * n ≤ st0.wlen "sp.gp"
  lgpos : (l + 1) * n ≤ st0.wlen "sp.gpos"
  lg : (l + 1) * n ≤ st0.wlen "sp.g"
  lnp : l < st0.wlen "sp.np"
  lGV : (Gs.map List.length).sum ≤ st0.wlen "pt.GV"
  lGO : Gs.length ≤ st0.wlen "pt.GO"
  lGL : Gs.length ≤ st0.wlen "pt.GL"
  cap : (l + 1) * n + n + 2 < st0.cap

theorem CgHyp.len_le (h : CgHyp st0 l n Gs) : Gs.length ≤ n := by
  have : Gs.length ≤ (Gs.map List.length).sum := by
    have key : ∀ (L : List (List ℕ)), (∀ j (h : j < L.length), L[j] ≠ []) →
        L.length ≤ (L.map List.length).sum := by
      intro L
      induction L with
      | nil => intro _; simp
      | cons a L ih =>
        intro hL
        have ha : a ≠ [] := hL 0 (by simp)
        have hal : 1 ≤ a.length := List.length_pos_iff.mpr ha
        have := ih (fun j hj => hL (j + 1) (by simp; omega))
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        omega
    exact key Gs h.ne
  exact this.trans h.tot

/-- One member of group `j`. -/
theorem cgStep (h : CgHyp st0 l n Gs) {j : ℕ} (hj : j < Gs.length) (q : ℕ)
    (hq : q < Gs[j].length) (s : State V) (hI : CgInv st0 s l n Gs j q) (hjr : s.w "cg.j" = j)
    (ho : s.w "cg.o" = goff Gs j) (hlen : s.w "cg.len" = Gs[j].length) (hqr : s.w "cg.q" = q) :
    Runs ops (seq (wset "cg.x" (load "pt.GV" (add (var "cg.o") (var "cg.q"))))
      (seq (wstore "sp.gm" (rb (add (var "cg.o") (var "cg.q"))) (var "cg.x"))
      (seq (wstore "sp.gpos" (rb (var "cg.x")) (add (var "cg.o") (var "cg.q")))
      (seq (wstore "sp.g" (rb (var "cg.x")) (add (var "cg.j") (lit 1)))
           (incr "cg.q"))))) s
      (fun r => CgInv st0 r l n Gs j (q + 1) ∧ r.w "cg.j" = j ∧ r.w "cg.o" = goff Gs j ∧
        r.w "cg.len" = Gs[j].length ∧ r.w "cg.q" = q + 1 ∧ r.cost = s.cost + 5) := by
  classical
  have hcap : s.cap = st0.cap := hI.unch.cap
  have hls : s.w "lvl" = l := by rw [hI.unch.wreg "lvl" (by simp [cgRegs])]; exact h.lvl
  have hns : s.w "n" = n := by rw [hI.unch.wreg "n" (by simp [cgRegs])]; exact h.nn
  have hGV : s.wa "pt.GV" = st0.wa "pt.GV" := (hI.unch.warr "pt.GV" (by simp [cgArrs])).1
  have hwl := hI.wlen
  have hga := goff_add_le Gs hj
  have hjn := h.len_le
  have htot := h.tot
  have hcapb := h.cap
  have hln : (l + 1) * n = l * n + n := Nat.succ_mul l n
  set v := Gs[j][q] with hv
  have hvn : v < n := h.mem j hj q hq
  have hseg : st0.wa "pt.GV" (goff Gs j + q) = v := (h.out.2.2 j hj).2.2 q hq
  -- `cg.x := pt.GV[cg.o + cg.q]`
  have e1 : evalW s (load "pt.GV" (add (var "cg.o") (var "cg.q"))) = some v := by
    have hi : goff Gs j + q < s.wlen "pt.GV" := by rw [hwl]; have := h.lGV; omega
    simp [ho, hqr, hcap, fit_of_lt (show goff Gs j + q < st0.cap by omega), hi, hGV, hseg]
  refine runs_seq (runs_wset e1 ?_)
  set s1 := (s.setW "cg.x" v).charge 1 with hs1
  -- `sp.gm[lvl n + cg.o + cg.q] := cg.x`
  have hidx1 : l * n + (goff Gs j + q) < (l + 1) * n := row_index_lt (by omega)
  have e2 : evalW s1 (rb (add (var "cg.o") (var "cg.q"))) = some (l * n + (goff Gs j + q)) := by
    simp [rb, hs1, ho, hqr, hls, hns, hcap, fit_of_lt (show goff Gs j + q < st0.cap by omega),
      fit_of_lt (show l * n < st0.cap by omega), fit_of_lt (show l * n + (goff Gs j + q) < st0.cap by omega)]
  refine runs_seq (runs_wstore e2 (by simp [hs1] : evalW s1 (var "cg.x") = some v)
    (by simp [hs1, hwl]; have := h.lgm; omega) ?_)
  set s2 := (s1.storeW "sp.gm" (l * n + (goff Gs j + q)) v).charge 1 with hs2
  -- `sp.gpos[lvl n + cg.x] := cg.o + cg.q`
  have hidx2 : l * n + v < (l + 1) * n := row_index_lt hvn
  have e3 : evalW s2 (rb (var "cg.x")) = some (l * n + v) := by
    simp [rb, hs2, hs1, hls, hns, hcap, fit_of_lt (show l * n < st0.cap by omega),
      fit_of_lt (show l * n + v < st0.cap by omega)]
  have e3v : evalW s2 (add (var "cg.o") (var "cg.q")) = some (goff Gs j + q) := by
    simp [hs2, hs1, ho, hqr, hcap, fit_of_lt (show goff Gs j + q < st0.cap by omega)]
  refine runs_seq (runs_wstore e3 e3v (by simp [hs2, hs1, hwl]; have := h.lgpos; omega) ?_)
  set s3 := (s2.storeW "sp.gpos" (l * n + v) (goff Gs j + q)).charge 1 with hs3
  -- `sp.g[lvl n + cg.x] := cg.j + 1`
  have e4 : evalW s3 (rb (var "cg.x")) = some (l * n + v) := by
    simp [rb, hs3, hs2, hs1, hls, hns, hcap, fit_of_lt (show l * n < st0.cap by omega),
      fit_of_lt (show l * n + v < st0.cap by omega)]
  have e4v : evalW s3 (add (var "cg.j") (lit 1)) = some (j + 1) := by
    simp [hs3, hs2, hs1, hjr, hcap, fit_of_lt (show j + 1 < st0.cap by omega),
      fit_of_lt (show 1 < st0.cap by omega)]
  refine runs_seq (runs_wstore e4 e4v (by simp [hs3, hs2, hs1, hwl]; have := h.lg; omega) ?_)
  set s4 := (s3.storeW "sp.g" (l * n + v) (j + 1)).charge 1 with hs4
  -- `cg.q := cg.q + 1`
  have e5 : evalW s4 (add (var "cg.q") (lit 1)) = some (q + 1) := by
    simp [hs4, hs3, hs2, hs1, hqr, hcap, fit_of_lt (show q + 1 < st0.cap by omega),
      fit_of_lt (show 1 < st0.cap by omega)]
  refine runs_wset e5 ?_
  set s5 := (s4.setW "cg.q" (q + 1)).charge 1 with hs5
  have hwa5 : ∀ a i, s5.wa a i =
      if a = "sp.g" ∧ i = l * n + v then j + 1 else
      if a = "sp.gpos" ∧ i = l * n + v then goff Gs j + q else
      if a = "sp.gm" ∧ i = l * n + (goff Gs j + q) then v else s.wa a i := by
    intro a i; simp [hs5, hs4, hs3, hs2, hs1]
  have mq : "cg.q" ∈ cgRegs := by simp [cgRegs]
  have mx : "cg.x" ∈ cgRegs := by simp [cgRegs]
  have hU5 : Unchanged st0 s5 cgArrs [] cgRegs [] := by
    rw [hs5, unch_charge, unch_setW mq, hs4, unch_charge, unch_storeW (by simp [cgArrs]), hs3,
      unch_charge, unch_storeW (by simp [cgArrs]), hs2, unch_charge,
      unch_storeW (by simp [cgArrs]), hs1, unch_charge, unch_setW mx]
    exact hI.unch
  refine ⟨⟨fun j' hj' hlt => ?_, fun j' hj' hlt => ?_, fun j' hj' q' hq' hor => ?_,
    fun x hx hnot => ?_, ?_, hU5, by simp [hs5, hs4, hs3, hs2, hs1, hwl], fun a ha hne i hi => ?_,
    fun l' hl' => ?_⟩, by simp [hs5, hs4, hs3, hs2, hs1, hjr], by simp [hs5, hs4, hs3, hs2, hs1, ho],
    by simp [hs5, hs4, hs3, hs2, hs1, hlen], by simp [hs5], by simp [hs5, hs4, hs3, hs2, hs1]⟩
  · rw [hwa5]; simp; exact hI.gs j' hj' hlt
  · rw [hwa5]; simp; exact hI.gl j' hj' hlt
  · by_cases hjq : j' = j ∧ q' = q
    · obtain ⟨rfl, rfl⟩ := hjq
      refine ⟨?_, ?_, ?_⟩
      · rw [hwa5]; simp [hv]
      · rw [hwa5]; simp [hv]
      · rw [hwa5]; simp [hv]
    · have hor' : j' < j ∨ (j' = j ∧ q' < q) := by
        rcases hor with h1 | ⟨h1, h2⟩
        · exact Or.inl h1
        · right; refine ⟨h1, ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h3 | h3
          · exact h3
          · exact absurd ⟨h1, h3⟩ hjq
      obtain ⟨d1, d2, d3⟩ := hI.done j' hj' q' hq' hor'
      have hne1 : l * n + (goff Gs j' + q') ≠ l * n + (goff Gs j + q) := by
        intro he
        have := goff_inj Gs hj' hj hq' hq (by omega)
        exact hjq ⟨this.1, this.2⟩
      have hne2 : l * n + Gs[j'][q'] ≠ l * n + v := by
        intro he
        have := h.dist j' hj' q' hq' j hj q hq (by omega)
        exact hjq ⟨this.1, this.2⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [hwa5]; simp only [hne1]; simp; exact d1
      · rw [hwa5]; simp only [hne2]; simp; exact d2
      · rw [hwa5]; simp only [hne2]; simp; exact d3
  · have hxv : v ≠ x := hnot j hj q hq (Or.inr ⟨rfl, Nat.lt_succ_self q⟩)
    have hne' : l * n + x ≠ l * n + v := by omega
    rw [hwa5]; simp only [hne']; simp
    exact hI.fresh x hx (fun j' hj' q' hq' hor => hnot j' hj' q' hq' (by
      rcases hor with h1 | ⟨h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, by omega⟩))
  · rw [hwa5]; simp; exact hI.np
  · have hi1 : i ≠ l * n + v := by omega
    have hi2 : i ≠ l * n + (goff Gs j + q) := by omega
    rw [hwa5]; simp only [hi1, hi2]; simp; exact hI.rows a ha hne i hi
  · rw [hwa5]; simp; exact hI.npo l' hl'

/-- The members of group `j`. -/
theorem cgInner_spec (h : CgHyp st0 l n Gs) {j : ℕ} (hj : j < Gs.length) (s : State V)
    (hI : CgInv st0 s l n Gs j 0) (hjr : s.w "cg.j" = j) (ho : s.w "cg.o" = goff Gs j)
    (hlen : s.w "cg.len" = Gs[j].length) (hqr : s.w "cg.q" = 0) :
    Runs ops cgInner s (fun r => CgInv st0 r l n Gs j Gs[j].length ∧ r.w "cg.j" = j ∧
      r.w "cg.o" = goff Gs j ∧ r.w "cg.len" = Gs[j].length ∧
      r.cost = s.cost + 6 * Gs[j].length + 1) := by
  have hcapb := h.cap
  have hjn := h.len_le
  have hga := goff_add_le Gs hj
  have htot := h.tot
  refine runs_while_nat (fun m r => ∃ q, m = Gs[j].length - q ∧ q ≤ Gs[j].length ∧
      CgInv st0 r l n Gs j q ∧ r.w "cg.j" = j ∧ r.w "cg.o" = goff Gs j ∧
      r.w "cg.len" = Gs[j].length ∧ r.w "cg.q" = q ∧ r.cost = s.cost + 6 * q) _ ?_
    Gs[j].length s ⟨0, by simp, by omega, hI, hjr, ho, hlen, hqr, by simp⟩
  rintro m r ⟨q, rfl, hql, hIr, hjr', hor, hlr, hqr', hcr⟩
  have hcap : r.cap = st0.cap := hIr.unch.cap
  refine ⟨if q < Gs[j].length then 1 else 0, by
    rw [evalW_lt_of (by rw [evalW_var, hqr']) (by rw [evalW_var, hlr]) (by rw [hcap]; omega)],
    fun hx => ?_, fun hx => ?_⟩
  · have hq : q < Gs[j].length := by by_contra hc; rw [if_neg hc] at hx; exact hx rfl
    refine (cgStep h hj q hq (r.charge 1) (hIr.charge 1) (by simpa using hjr') (by simpa using hor)
      (by simpa using hlr) (by simpa using hqr')).mono ?_
    rintro r' ⟨hI', hj', ho', hl', hq', hc'⟩
    refine ⟨Gs[j].length - (q + 1), by omega, q + 1, rfl, by omega, hI', hj', ho', hl', hq', ?_⟩
    simp at hc'; omega
  · have hq : q = Gs[j].length := by by_contra hc; rw [if_pos (by omega)] at hx; exact one_ne_zero hx
    subst hq
    exact ⟨hIr.charge 1, by simpa using hjr', by simpa using hor, by simpa using hlr, by simp [hcr]⟩

/-- One group `j`: its members, then its segment. -/
theorem cgBody_spec (h : CgHyp st0 l n Gs) {j : ℕ} (hj : j < Gs.length) (s : State V)
    (hI : CgInv st0 s l n Gs j 0) (hjr : s.w "cg.j" = j) :
    Runs ops cgBody s (fun r => CgInv st0 r l n Gs (j + 1) 0 ∧ r.w "cg.j" = j + 1 ∧
      r.cost = s.cost + 7 + 6 * Gs[j].length) := by
  classical
  have hcap : s.cap = st0.cap := hI.unch.cap
  have hcapb := h.cap
  have hjn := h.len_le
  have htot := h.tot
  have hga := goff_add_le Gs hj
  have hln : (l + 1) * n = l * n + n := Nat.succ_mul l n
  have hls : s.w "lvl" = l := by rw [hI.unch.wreg "lvl" (by simp [cgRegs])]; exact h.lvl
  have hns : s.w "n" = n := by rw [hI.unch.wreg "n" (by simp [cgRegs])]; exact h.nn
  have hGO : s.wa "pt.GO" = st0.wa "pt.GO" := (hI.unch.warr "pt.GO" (by simp [cgArrs])).1
  have hGL : s.wa "pt.GL" = st0.wa "pt.GL" := (hI.unch.warr "pt.GL" (by simp [cgArrs])).1
  have hwl := hI.wlen
  have hGOj : st0.wa "pt.GO" j = goff Gs j := (h.out.2.2 j hj).1
  have hGLj : st0.wa "pt.GL" j = Gs[j].length := (h.out.2.2 j hj).2.1
  -- `cg.o := pt.GO[cg.j]`
  have e1 : evalW s (load "pt.GO" (var "cg.j")) = some (goff Gs j) := by
    have hi : j < s.wlen "pt.GO" := by rw [hwl]; have := h.lGO; omega
    simp [hjr, hi, hGO, hGOj]
  refine runs_seq (runs_wset e1 ?_)
  set s1 := (s.setW "cg.o" (goff Gs j)).charge 1 with hs1
  have e2 : evalW s1 (load "pt.GL" (var "cg.j")) = some Gs[j].length := by
    have hi : j < s.wlen "pt.GL" := by rw [hwl]; have := h.lGL; omega
    simp [hs1, hjr, hi, hGL, hGLj]
  refine runs_seq (runs_wset e2 ?_)
  set s2 := (s1.setW "cg.len" Gs[j].length).charge 1 with hs2
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by simp [hs2, hs1, hcap]; omega)) ?_)
  set s3 := (s2.setW "cg.q" 0).charge 1 with hs3
  have hI3 : CgInv st0 s3 l n Gs j 0 := by
    rw [hs3]; refine ((((hI.setW (by simp [cgRegs]) _).charge 1).setW (by simp [cgRegs]) _).charge 1
      |>.setW (by simp [cgRegs]) _ |>.charge 1)
  refine runs_seq ((cgInner_spec h hj s3 hI3 (by simp [hs3, hs2, hs1, hjr]) (by simp [hs3, hs2, hs1])
    (by simp [hs3, hs2]) (by simp [hs3])).mono ?_)
  rintro r ⟨hIr, hjr', hor, hlr, hcr⟩
  have hcapr : r.cap = st0.cap := hIr.unch.cap
  have hlr' : r.w "lvl" = l := by rw [hIr.unch.wreg "lvl" (by simp [cgRegs])]; exact h.lvl
  have hnr' : r.w "n" = n := by rw [hIr.unch.wreg "n" (by simp [cgRegs])]; exact h.nn
  have hwlr := hIr.wlen
  -- `sp.gs[lvl n + cg.j] := cg.o`
  have hidx : l * n + j < (l + 1) * n := row_index_lt (by omega)
  have eI : evalW r (rb (var "cg.j")) = some (l * n + j) := by
    simp [rb, hlr', hnr', hjr', hcapr, fit_of_lt (show l * n < st0.cap by omega),
      fit_of_lt (show l * n + j < st0.cap by omega)]
  refine runs_seq (runs_wstore eI (by simp [hor] : evalW r (var "cg.o") = some (goff Gs j))
    (by rw [hwlr]; have := h.lgs; omega) ?_)
  set r1 := (r.storeW "sp.gs" (l * n + j) (goff Gs j)).charge 1 with hr1
  have eI1 : evalW r1 (rb (var "cg.j")) = some (l * n + j) := by
    simp [rb, hr1, hlr', hnr', hjr', hcapr, fit_of_lt (show l * n < st0.cap by omega),
      fit_of_lt (show l * n + j < st0.cap by omega)]
  refine runs_seq (runs_wstore eI1 (by simp [hr1, hlr] : evalW r1 (var "cg.len") = some Gs[j].length)
    (by simp [hr1, hwlr]; have := h.lgl; omega) ?_)
  set r2 := (r1.storeW "sp.gl" (l * n + j) Gs[j].length).charge 1 with hr2
  have e5 : evalW r2 (add (var "cg.j") (lit 1)) = some (j + 1) := by
    simp [hr2, hr1, hjr', hcapr, fit_of_lt (show j + 1 < st0.cap by omega),
      fit_of_lt (show 1 < st0.cap by omega)]
  refine runs_wset e5 ?_
  set r3 := (r2.setW "cg.j" (j + 1)).charge 1 with hr3
  have hwa3 : ∀ a i, r3.wa a i =
      if a = "sp.gl" ∧ i = l * n + j then Gs[j].length else
      if a = "sp.gs" ∧ i = l * n + j then goff Gs j else r.wa a i := by
    intro a i; simp [hr3, hr2, hr1]
  have mj : "cg.j" ∈ cgRegs := by simp [cgRegs]
  have hU3 : Unchanged st0 r3 cgArrs [] cgRegs [] := by
    rw [hr3, unch_charge, unch_setW mj, hr2, unch_charge, unch_storeW (by simp [cgArrs]), hr1,
      unch_charge, unch_storeW (by simp [cgArrs])]
    exact hIr.unch
  refine ⟨⟨fun j' hj' hlt => ?_, fun j' hj' hlt => ?_, fun j' hj' q' hq' hor' => ?_,
    fun x hx hnot => ?_, ?_, hU3, by simp [hr3, hr2, hr1, hwlr], fun a ha hne i hi => ?_,
    fun l' hl' => ?_⟩, by simp [hr3], by simp [hr3, hr2, hr1, hcr, hs3, hs2, hs1]; omega⟩
  · have hval : r3.wa "sp.gs" (l * n + j') =
        if j' = j then goff Gs j else r.wa "sp.gs" (l * n + j') := by rw [hwa3]; simp
    rw [hval]
    split_ifs with hjj
    · subst hjj; rfl
    · exact hIr.gs j' hj' (by omega)
  · have hval : r3.wa "sp.gl" (l * n + j') =
        if j' = j then Gs[j].length else r.wa "sp.gl" (l * n + j') := by rw [hwa3]; simp
    rw [hval]
    split_ifs with hjj
    · subst hjj; rfl
    · exact hIr.gl j' hj' (by omega)
  · have hor'' : j' < j ∨ (j' = j ∧ q' < Gs[j].length) := by
      rcases hor' with h1 | ⟨h1, h2⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h3 | h3
        · exact Or.inl h3
        · subst h3; exact Or.inr ⟨rfl, hq'⟩
      · omega
    obtain ⟨d1, d2, d3⟩ := hIr.done j' hj' q' hq' hor''
    refine ⟨?_, ?_, ?_⟩ <;> rw [hwa3] <;> simp <;> assumption
  · rw [hwa3]; simp
    exact hIr.fresh x hx (fun j' hj' q' hq' hor' => hnot j' hj' q' hq' (by
      rcases hor' with h1 | ⟨h1, h2⟩
      · exact Or.inl (by omega)
      · subst h1; exact Or.inl (Nat.lt_succ_self _)))
  · rw [hwa3]; simp; exact hIr.np
  · have hi' : i ≠ l * n + j := by omega
    rw [hwa3]; simp only [hi']; simp; exact hIr.rows a ha hne i hi
  · rw [hwa3]; simp; exact hIr.npo l' hl'

/-- The pieces of the group table in terms of the groups. -/
noncomputable def grpP (Gs : List (List ℕ)) (j : ℕ) : Finset ℕ :=
  if h : j < Gs.length then (Gs[j]).toFinset else ∅

/-- **BM.4½ is correct**: row `l` of the group table represents the groups of FindPivots. -/
theorem copyGrp_spec (h : CgHyp st0 l n Gs) :
    Runs ops copyGrp st0 (fun r =>
      GrpRep r l n Gs.length (grpP Gs) (fun j => r.wa "sp.gp" (l * n + j)) ∧
      NpRep r l Gs.length ∧ Unchanged st0 r cgArrs [] cgRegs [] ∧ r.wlen = st0.wlen ∧
      (∀ a ∈ cgArrs, a ≠ "sp.np" → ∀ i, (i < l * n ∨ (l + 1) * n ≤ i) → r.wa a i = st0.wa a i) ∧
      (∀ l', l' ≠ l → r.wa "sp.np" l' = st0.wa "sp.np" l') ∧
      r.cost = st0.cost + 3 + 8 * Gs.length + 6 * (Gs.map List.length).sum) := by
  classical
  have hcapb := h.cap
  have hjn := h.len_le
  have htot := h.tot
  have hln : (l + 1) * n = l * n + n := Nat.succ_mul l n
  -- `sp.np[lvl] := pt.ng`
  have eL : evalW st0 (var "lvl") = some l := by simp [h.lvl]
  have eN : evalW st0 (var "pt.ng") = some Gs.length := by simp [h.out.1]
  refine runs_seq (runs_wstore eL eN h.lnp ?_)
  set s1 := (st0.storeW "sp.np" l Gs.length).charge 1 with hs1
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by simp [hs1]; omega)) ?_)
  set s2 := (s1.setW "cg.j" 0).charge 1 with hs2
  have hI2 : CgInv st0 s2 l n Gs 0 0 := by
    refine ⟨fun j' _ h' => absurd h' (by omega), fun j' _ h' => absurd h' (by omega),
      fun j' _ q' _ h' => by omega, fun x hx _ => by simp [hs2, hs1]; exact h.g0 x hx,
      by simp [hs2, hs1], ?_, by simp [hs2, hs1], fun a ha hne i _ => by simp [hs2, hs1, hne],
      fun l' hl' => by simp [hs2, hs1, hl']⟩
    rw [hs2, unch_charge, unch_setW (by simp [cgRegs]), hs1, unch_charge,
      unch_storeW (by simp [cgArrs])]
    exact Unchanged.refl _ _ _ _ _
  refine runs_while_nat (fun m r => ∃ j, m = Gs.length - j ∧ j ≤ Gs.length ∧
      CgInv st0 r l n Gs j 0 ∧ r.w "cg.j" = j ∧
      r.cost = st0.cost + 2 + 8 * j + 6 * goff Gs j) _ ?_ Gs.length s2
    ⟨0, by simp, by omega, hI2, by simp [hs2], by simp [hs2, hs1, goff]⟩
  rintro m r ⟨j, rfl, hjl, hIr, hjr, hcr⟩
  have hcapr : r.cap = st0.cap := hIr.unch.cap
  have hng : r.w "pt.ng" = Gs.length := by
    rw [hIr.unch.wreg "pt.ng" (by simp [cgRegs])]; exact h.out.1
  refine ⟨if j < Gs.length then 1 else 0, by
    rw [evalW_lt_of (by rw [evalW_var, hjr]) (by rw [evalW_var, hng]) (by rw [hcapr]; omega)],
    fun hx => ?_, fun hx => ?_⟩
  · have hj : j < Gs.length := by by_contra hc; rw [if_neg hc] at hx; exact hx rfl
    refine (cgBody_spec h hj (r.charge 1) (hIr.charge 1) (by simpa using hjr)).mono ?_
    rintro r' ⟨hI', hj', hc'⟩
    refine ⟨Gs.length - (j + 1), by omega, j + 1, rfl, by omega, hI', hj', ?_⟩
    rw [goff_succ Gs hj]; simp at hc'; omega
  · have hj : j = Gs.length := by by_contra hc; rw [if_pos (by omega)] at hx; exact one_ne_zero hx
    subst hj
    have hI := hIr.charge 1
    set r' := r.charge 1 with hr'
    have hwl' : r'.wlen = st0.wlen := hI.wlen
    have hgoff : goff Gs Gs.length = (Gs.map List.length).sum := by
      unfold goff; rw [List.take_of_length_le le_rfl]
    have hgs : ∀ j (hj : j < Gs.length), gs r' l n j = goff Gs j := fun j hj => hI.gs j hj hj
    have hgl : ∀ j (hj : j < Gs.length), gl r' l n j = Gs[j].length := fun j hj => hI.gl j hj hj
    have hgm : ∀ j (hj : j < Gs.length) q (hq : q < Gs[j].length),
        gmem r' l n (goff Gs j + q) = Gs[j][q] := fun j hj q hq => (hI.done j hj q hq (Or.inl hj)).1
    refine ⟨⟨by rw [hwl']; exact h.lgm, by rw [hwl']; exact h.lgs, by rw [hwl']; exact h.lgl,
      by rw [hwl']; exact h.lgp, by rw [hwl']; exact h.lgpos, by rw [hwl']; exact h.lg, hjn,
      fun j hj => ?_, fun j hj q hq => ?_, fun j hj q hq => ?_, fun j hj q hq => ?_,
      fun j hj => ?_, fun x hx => ?_, fun j _ => rfl, fun j hj j' hj' hne => ?_⟩,
      ⟨by rw [hwl']; exact h.lnp, hI.np⟩, hI.unch, hwl', hI.rows, hI.npo, ?_⟩
    · rw [hgs j hj, hgl j hj]; exact (goff_add_le Gs hj).trans htot
    · rw [hgl j hj] at hq; rw [hgs j hj, hgm j hj q hq]; exact h.mem j hj q hq
    · rw [hgl j hj] at hq; rw [hgs j hj, hgm j hj q hq]; exact (hI.done j hj q hq (Or.inl hj)).2.1
    · rw [hgl j hj] at hq; rw [hgs j hj, hgm j hj q hq]; exact (hI.done j hj q hq (Or.inl hj)).2.2
    · rw [hgl j hj]
      ext x
      simp only [grpP, dif_pos hj, List.mem_toFinset, Finset.mem_image, Finset.mem_range]
      constructor
      · intro hx
        obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.mp hx
        exact ⟨q, hq, by rw [hgs j hj, hgm j hj q hq]⟩
      · rintro ⟨q, hq, rfl⟩
        rw [hgs j hj, hgm j hj q hq]
        exact List.getElem_mem hq
    · by_cases hex : ∃ j, ∃ hj : j < Gs.length, ∃ q, ∃ hq : q < Gs[j].length, Gs[j][q] = x
      · obtain ⟨j, hj, q, hq, rfl⟩ := hex
        right
        refine ⟨j, hj, (hI.done j hj q hq (Or.inl hj)).2.2, ?_⟩
        simp only [grpP, dif_pos hj, List.mem_toFinset]
        exact List.getElem_mem hq
      · left
        exact hI.fresh x hx (fun j hj q hq _ he => hex ⟨j, hj, q, hq, he⟩)
    · rw [hgs j hj, hgl j hj, hgs j' hj', hgl j' hj']
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · left; rw [← goff_succ Gs hj]; exact goff_mono Gs (by omega)
      · right; rw [← goff_succ Gs hj']; exact goff_mono Gs (by omega)
    · simp [hr', hcr, hgoff]; omega

end copySpec
end Frontier.CHD.RamInit
