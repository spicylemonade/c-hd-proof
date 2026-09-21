import Frontier.CHD.RamInit
import Frontier.CHD.BMLazy

/-!
# Frontier.CHD.RamPiv — BM.5–6 of the RAM spine: the new level structure and its pivots (agent-01)

**NON-GATE** (B-L4, Layer B).  `pivIns dsNew dsIns`: create the level-`l` structure (`dsNew`,
Layer A `newC M B`), then insert the pivots `sp.gp[l·n + j]`, `j < p`, in order (`dsIns`, vertex in
register `px`, Layer A `insC dlOps T g D v (f v)`).  The result is exactly `BMLazy.initD` with
`lpiv = List.ofFn piv`.

The `D` procedures are abstract (`DNewI`, `DInsI`), to be instantiated by B-L3 (agent-04's
`DGlobal`/`DLRep` wrappers): a representation predicate `DR st g D` (global lazy state `g`, the
level-`l` structure `D`), framed by the loop's own register writes.
-/

namespace Frontier.CHD.RamInit

open Frontier Frontier.RAM WExpr Stmt Frontier.CHD.RamLevel Frontier.CHD.BM

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}

/-- The registers written by `pivIns` itself. -/
def piRegs : List String := ["sp.j", "px"]

/-- **Creating the level structure** `newC M B`. -/
structure DNewI (ops : VOps V) (dsNew : Stmt) (DR0 : State V → DGl G s → Prop)
    (DR : State V → DGl G s → DStrM G s → Prop) (M : ℕ) (B : WLab G s) (C : ℕ)
    (NA NVA NW NVR : List String) (U : State V → ℕ) (Ucap : ℕ) : Prop where
  run : ∀ st g, DR0 st g → U st + 1 ≤ Ucap → Runs ops dsNew st (fun r => DR r g (newC M B) ∧
    Unchanged st r NA NVA NW NVR ∧ st.cost ≤ r.cost ∧ r.cost ≤ st.cost + C ∧
    r.wlen = st.wlen ∧ r.vlen = st.vlen ∧ U r ≤ U st + 1)

/-- **One insertion** of the vertex in `px` with key `f px`, under a Layer-A invariant `Inv`. -/
structure DInsI (ops : VOps V) (dsIns : Stmt) (DR : State V → DGl G s → DStrM G s → Prop)
    (Inv : DGl G s → DStrM G s → Prop) (f : Fin G.n → WLab G s) (T K C : ℕ)
    (IA IVA IW IVR FR : List String) (Pv : Fin G.n → Prop) (U : State V → ℕ) (Ucap : ℕ) : Prop where
  run : ∀ st g D (v : Fin G.n), DR st g D → Inv g D → Pv v → st.w "px" = v →
    U st + ((BM.insC (dlOps G s) T g D v (f v)).2.2 + 1) ≤ Ucap →
    Runs ops dsIns st (fun r => DR r (BM.insC (dlOps G s) T g D v (f v)).1
        (BM.insC (dlOps G s) T g D v (f v)).2.1 ∧
      Unchanged st r IA IVA IW IVR ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + K * (BM.insC (dlOps G s) T g D v (f v)).2.2 + C ∧
      r.wlen = st.wlen ∧ r.vlen = st.vlen ∧ U r ≤ U st + ((BM.insC (dlOps G s) T g D v (f v)).2.2 + 1))
  /-- `DR` survives the calling loop's writes to its registers `FR` -/
  frame : ∀ st r g D, DR st g D → Unchanged st r [] [] FR [] → st.cost ≤ r.cost → DR r g D
  /-- the resource counter only depends on the insertion's own registers -/
  uframe : ∀ st r (wa va wr vr : List String), Unchanged st r wa va wr vr → (∀ a ∈ wr, a ∉ IW) →
    U r = U st
  regs : ∀ a ∈ IW, a ∉ FR ∧ a ≠ "lvl" ∧ a ≠ "n"
  arrs : ∀ a ∈ IA, a ≠ "sp.gp" ∧ a ≠ "sp.np" ∧ a ≠ "S" ∧ a ≠ "S.len"

/-- **BM.5–6**: `newC`, then insert the pivots of the level-`l` groups in order. -/
def pivIns (dsNew dsIns : Stmt) : Stmt :=
  seq dsNew
  (seq (wset "sp.j" (lit 0))
  (.while (lt (var "sp.j") (load "sp.np" (var "lvl")))
    (seq (wset "px" (load "sp.gp" (rb (var "sp.j"))))
    (seq dsIns (incr "sp.j")))))

/-- Inserting one more vertex at the end of the list. -/
theorem insManyC_snoc (T : ℕ) (f : Fin G.n → WLab G s) (y : Fin G.n) :
    ∀ (l : List (Fin G.n)) (g : DGl G s) (D : DStrM G s),
      BM.insManyC (dlOps G s) T f (l ++ [y]) g D =
        ((BM.insC (dlOps G s) T (BM.insManyC (dlOps G s) T f l g D).1
            (BM.insManyC (dlOps G s) T f l g D).2.1 y (f y)).1,
         (BM.insC (dlOps G s) T (BM.insManyC (dlOps G s) T f l g D).1
            (BM.insManyC (dlOps G s) T f l g D).2.1 y (f y)).2.1,
         (BM.insManyC (dlOps G s) T f l g D).2.2 +
           (BM.insC (dlOps G s) T (BM.insManyC (dlOps G s) T f l g D).1
            (BM.insManyC (dlOps G s) T f l g D).2.1 y (f y)).2.2)
  | [], g, D => by simp [BM.insManyC]
  | x :: l, g, D => by
    have ih := insManyC_snoc T f y l (BM.insC (dlOps G s) T g D x (f x)).1
      (BM.insC (dlOps G s) T g D x (f x)).2.1
    simp only [List.cons_append, BM.insManyC] at ih ⊢
    rw [ih]
    simp only [Prod.mk.injEq, true_and]
    ring

/-- `insManyC` along an append. -/
theorem insManyC_append (T : ℕ) (f : Fin G.n → WLab G s) :
    ∀ (l1 l2 : List (Fin G.n)) (g : DGl G s) (D : DStrM G s),
      BM.insManyC (dlOps G s) T f (l1 ++ l2) g D =
        ((BM.insManyC (dlOps G s) T f l2 (BM.insManyC (dlOps G s) T f l1 g D).1
            (BM.insManyC (dlOps G s) T f l1 g D).2.1).1,
         (BM.insManyC (dlOps G s) T f l2 (BM.insManyC (dlOps G s) T f l1 g D).1
            (BM.insManyC (dlOps G s) T f l1 g D).2.1).2.1,
         (BM.insManyC (dlOps G s) T f l1 g D).2.2 +
           (BM.insManyC (dlOps G s) T f l2 (BM.insManyC (dlOps G s) T f l1 g D).1
            (BM.insManyC (dlOps G s) T f l1 g D).2.1).2.2)
  | [], l2, g, D => by simp [BM.insManyC]
  | x :: l1, l2, g, D => by
    have ih := insManyC_append T f l1 l2 (BM.insC (dlOps G s) T g D x (f x)).1
      (BM.insC (dlOps G s) T g D x (f x)).2.1
    simp only [List.cons_append, BM.insManyC] at ih ⊢
    rw [ih]
    simp only [Prod.mk.injEq, true_and]
    ring

/-- The cost of a prefix of the insertions is at most the total. -/
theorem insManyC_cost_append_le (T : ℕ) (f : Fin G.n → WLab G s) (l1 l2 : List (Fin G.n))
    (g : DGl G s) (D : DStrM G s) :
    (BM.insManyC (dlOps G s) T f l1 g D).2.2 ≤ (BM.insManyC (dlOps G s) T f (l1 ++ l2) g D).2.2 := by
  rw [insManyC_append]; exact Nat.le_add_right _ _

theorem insManyC_cost_take_le (T : ℕ) (f : Fin G.n → WLab G s) (l : List (Fin G.n)) (k : ℕ)
    (g : DGl G s) (D : DStrM G s) :
    (BM.insManyC (dlOps G s) T f (l.take k) g D).2.2 ≤ (BM.insManyC (dlOps G s) T f l g D).2.2 := by
  have := insManyC_cost_append_le T f (l.take k) (l.drop k) g D
  rwa [List.take_append_drop] at this

/-- **BM.5–6 is `initD`**: the level structure after `pivIns` is `insManyC … (ofFn piv) g (newC M B)`. -/
theorem pivIns_spec {dsNew dsIns : Stmt} {DR0 : State V → DGl G s → Prop}
    {DR : State V → DGl G s → DStrM G s → Prop} {Inv : DGl G s → DStrM G s → Prop}
    {f : Fin G.n → WLab G s} {T K C Cn : ℕ} {M : ℕ} {B : WLab G s} {NA NVA NW NVR IA IVA IW IVR : List String}
    {Pv : Fin G.n → Prop} {U : State V → ℕ} {Ucap : ℕ}
    (hN : DNewI ops dsNew DR0 DR M B Cn NA NVA NW NVR U Ucap)
    (hI : DInsI ops dsIns DR Inv f T K C IA IVA IW IVR piRegs Pv U Ucap)
    (hNW : ∀ a ∈ NW, a ≠ "lvl" ∧ a ≠ "n") (hNA : ∀ a ∈ NA, a ≠ "sp.gp" ∧ a ≠ "sp.np")
    (st : State V) (g : DGl G s) (hD0 : DR0 st g) {l n p : ℕ} (piv : Fin p → Fin G.n)
    (hl : st.w "lvl" = l) (hn : st.w "n" = n) (hnp : st.wa "sp.np" l = p)
    (hnpl : l < st.wlen "sp.np") (hpv : ∀ j (hj : j < p), st.wa "sp.gp" (l * n + j) = piv ⟨j, hj⟩)
    (hgpl : l * n + p ≤ st.wlen "sp.gp") (hcap : l * n + p + 2 < st.cap)
    (hInv : ∀ k ≤ p, Inv (BM.insManyC (dlOps G s) T f ((List.ofFn piv).take k) g (newC M B)).1
      (BM.insManyC (dlOps G s) T f ((List.ofFn piv).take k) g (newC M B)).2.1)
    (hPv : ∀ j, Pv (piv j))
    (hUb : U st + 1 + (BM.insManyC (dlOps G s) T f (List.ofFn piv) g (newC M B)).2.2 + p ≤ Ucap) :
    Runs ops (pivIns dsNew dsIns) st (fun r =>
      DR r (BM.insManyC (dlOps G s) T f (List.ofFn piv) g (newC M B)).1
        (BM.insManyC (dlOps G s) T f (List.ofFn piv) g (newC M B)).2.1 ∧
      Unchanged st r (NA ++ IA) (NVA ++ IVA) (piRegs ++ NW ++ IW) (NVR ++ IVR) ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + Cn + 2 + K * (BM.insManyC (dlOps G s) T f (List.ofFn piv) g (newC M B)).2.2 +
        p * (C + 5) ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen ∧
      U r ≤ U st + 1 + (BM.insManyC (dlOps G s) T f (List.ofFn piv) g (newC M B)).2.2 + p) := by
  classical
  have hpv' : ∀ j (hj : j < p), (List.ofFn piv)[j]'(by simpa using hj) = piv ⟨j, hj⟩ := by
    intro j hj; simp
  set IM := fun k : ℕ => BM.insManyC (dlOps G s) T f ((List.ofFn piv).take k) g (newC M B) with hIM
  refine runs_seq ((hN.run st g hD0 (by omega)).mono ?_)
  rintro r0 ⟨hDR0, hU0, hc0a, hc0b, hwl0, hvl0, hu0⟩
  have hnIW : ∀ a ∈ piRegs, a ∉ IW := fun a ha h => (hI.regs a h).1 ha
  have hcap0 : r0.cap = st.cap := hU0.cap
  have hl0 : r0.w "lvl" = l := by rw [hU0.wreg "lvl" (fun h => (hNW _ h).1 rfl)]; exact hl
  have hn0 : r0.w "n" = n := by rw [hU0.wreg "n" (fun h => (hNW _ h).2 rfl)]; exact hn
  have hnp0 : r0.wa "sp.np" = st.wa "sp.np" := (hU0.warr "sp.np" (fun h => (hNA _ h).2 rfl)).1
  have hnpl0 : r0.wlen "sp.np" = st.wlen "sp.np" := (hU0.warr "sp.np" (fun h => (hNA _ h).2 rfl)).2
  have hgp0 : r0.wa "sp.gp" = st.wa "sp.gp" := (hU0.warr "sp.gp" (fun h => (hNA _ h).1 rfl)).1
  have hgpl0 : r0.wlen "sp.gp" = st.wlen "sp.gp" := (hU0.warr "sp.gp" (fun h => (hNA _ h).1 rfl)).2
  have mj : "sp.j" ∈ piRegs ++ NW ++ IW := by simp [piRegs]
  have mpx : "px" ∈ piRegs ++ NW ++ IW := by simp [piRegs]
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by rw [hcap0]; omega)) ?_)
  set r1 := (r0.setW "sp.j" 0).charge 1 with hr1
  have hDR1 : DR r1 g (newC M B) := hI.frame r0 r1 g _ hDR0 (by
    rw [hr1, unch_charge, unch_setW (by simp [piRegs])]; exact Unchanged.refl _ _ _ _ _)
    (by simp [hr1])
  have hIM0 : IM 0 = (g, newC M B, 0) := by simp [hIM, BM.insManyC]
  have hu1 : U r1 = U r0 := hI.uframe r0 r1 [] [] piRegs [] (by
    rw [hr1, unch_charge, unch_setW (by simp [piRegs])]; exact Unchanged.refl _ _ _ _ _) hnIW
  have hIMle : ∀ k, (IM k).2.2 ≤ (BM.insManyC (dlOps G s) T f (List.ofFn piv) g (newC M B)).2.2 :=
    fun k => insManyC_cost_take_le T f (List.ofFn piv) k g (newC M B)
  have hregs : ∀ a, a = "lvl" ∨ a = "n" → a ∉ piRegs ++ NW ++ IW := by
    intro a ha hm
    simp only [List.mem_append] at hm
    rcases hm with (h1 | h1) | h1
    · simp [piRegs] at h1; rcases ha with rfl | rfl <;> simp at h1
    · rcases ha with rfl | rfl
      · exact (hNW _ h1).1 rfl
      · exact (hNW _ h1).2 rfl
    · rcases ha with rfl | rfl
      · exact (hI.regs _ h1).2.1 rfl
      · exact (hI.regs _ h1).2.2 rfl
  have harrs : ∀ a, a = "sp.gp" ∨ a = "sp.np" → a ∉ NA ++ IA := by
    intro a ha hm
    simp only [List.mem_append] at hm
    rcases hm with h1 | h1
    · rcases ha with rfl | rfl
      · exact (hNA _ h1).1 rfl
      · exact (hNA _ h1).2 rfl
    · rcases ha with rfl | rfl
      · exact (hI.arrs _ h1).1 rfl
      · exact (hI.arrs _ h1).2.1 rfl
  have htake : ∀ j (hj : j < p), (List.ofFn piv).take (j + 1) = (List.ofFn piv).take j ++ [piv ⟨j, hj⟩] := by
    intro j hj
    rw [List.take_succ, List.getElem?_eq_getElem (by simpa using hj)]
    simp
  refine runs_while_nat (fun m r => ∃ j, m = p - j ∧ j ≤ p ∧ r.w "sp.j" = j ∧
      DR r (IM j).1 (IM j).2.1 ∧
      Unchanged st r (NA ++ IA) (NVA ++ IVA) (piRegs ++ NW ++ IW) (NVR ++ IVR) ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + Cn + 1 + K * (IM j).2.2 + j * (C + 5) ∧ r.wlen = st.wlen ∧
      r.vlen = st.vlen ∧ U r ≤ U st + 1 + (IM j).2.2 + j) _ ?_ p r1 ?_
  swap
  · refine ⟨0, by simp, by omega, by simp [hr1], by rw [hIM0]; exact hDR1, ?_, by simp [hr1]; omega,
      by rw [hIM0]; simp [hr1]; omega, by simp [hr1, hwl0], by simp [hr1, hvl0],
      by rw [hIM0, hu1]; simp; omega⟩
    rw [hr1, unch_charge, unch_setW mj]
    exact hU0.mono (by simp) (by simp) (by simp) (by simp)
  rintro m r ⟨j, rfl, hjp, hjr, hDRr, hUr, hc1, hc2, hwlr, hvlr, hur⟩
  have hcapr : r.cap = st.cap := hUr.cap
  have hlr : r.w "lvl" = l := by rw [hUr.wreg "lvl" (hregs _ (Or.inl rfl))]; exact hl
  have hnr : r.w "n" = n := by rw [hUr.wreg "n" (hregs _ (Or.inr rfl))]; exact hn
  have hnpr := hUr.warr "sp.np" (harrs _ (Or.inr rfl))
  have hgpr := hUr.warr "sp.gp" (harrs _ (Or.inl rfl))
  have eT : evalW r (lt (var "sp.j") (load "sp.np" (var "lvl"))) = some (if j < p then 1 else 0) := by
    rw [evalW_lt_of (by rw [evalW_var, hjr]) (x := j) (y := p)
      (by simp [hlr, hnpr.1, hnpr.2, hnpl, hnp]) (by rw [hcapr]; omega)]
  refine ⟨if j < p then 1 else 0, eT, fun hx => ?_, fun hx => ?_⟩
  · have hj : j < p := by by_contra hc; rw [if_neg hc] at hx; exact hx rfl
    -- `px := sp.gp[lvl n + sp.j]`
    have eP : evalW (r.charge 1) (load "sp.gp" (rb (var "sp.j"))) = some (piv ⟨j, hj⟩ : ℕ) := by
      rw [eval_row_load (r.charge 1) "sp.gp" (e := var "sp.j") (i := j) (by simpa using hlr)
        (by simpa using hnr) (by simp [hjr]) (by simp [hgpr.2]; omega) (by simp [hcapr]; omega)]
      simp [hgpr.1, hpv j hj]
    refine runs_seq (runs_wset eP ?_)
    set r2 := ((r.charge 1).setW "px" (piv ⟨j, hj⟩ : ℕ)).charge 1 with hr2
    have hU12 : Unchanged r r2 [] [] piRegs [] := by
      rw [hr2, unch_charge, unch_setW (by simp [piRegs]), unch_charge]; exact Unchanged.refl _ _ _ _ _
    have hDR2 : DR r2 (IM j).1 (IM j).2.1 := hI.frame r r2 _ _ hDRr hU12 (by simp [hr2] <;> omega)
    have hIMs : IM (j + 1) =
        ((BM.insC (dlOps G s) T (IM j).1 (IM j).2.1 (piv ⟨j, hj⟩) (f (piv ⟨j, hj⟩))).1,
         (BM.insC (dlOps G s) T (IM j).1 (IM j).2.1 (piv ⟨j, hj⟩) (f (piv ⟨j, hj⟩))).2.1,
         (IM j).2.2 + (BM.insC (dlOps G s) T (IM j).1 (IM j).2.1 (piv ⟨j, hj⟩) (f (piv ⟨j, hj⟩))).2.2) := by
      simp only [hIM]
      rw [htake j hj, insManyC_snoc]
    have hu2 : U r2 = U r := hI.uframe r r2 [] [] piRegs [] hU12 hnIW
    have hcs := hIMle (j + 1)
    rw [hIMs] at hcs
    simp only at hcs
    refine runs_seq ((hI.run r2 (IM j).1 (IM j).2.1 (piv ⟨j, hj⟩) hDR2 (hInv j hjp) (hPv _)
      (by simp [hr2]) (by rw [hu2]; omega)).mono ?_)
    rintro r3 ⟨hDR3, hU3, hc3a, hc3b, hwl3, hvl3, hu3⟩
    have hj3 : r3.w "sp.j" = j := by
      rw [hU3.wreg "sp.j" (fun h => (hI.regs _ h).1 (by simp [piRegs]))]; simp [hr2, hjr]
    have hcap3 : r3.cap = st.cap := by rw [hU3.cap]; simp [hr2, hcapr]
    have e5 : evalW r3 (add (var "sp.j") (lit 1)) = some (j + 1) := by
      simp [hj3, hcap3, fit_of_lt (show j + 1 < st.cap by omega), fit_of_lt (show 1 < st.cap by omega)]
    refine runs_wset e5 ?_
    set r4 := (r3.setW "sp.j" (j + 1)).charge 1 with hr4
    have hDR4 : DR r4 (IM (j + 1)).1 (IM (j + 1)).2.1 := by
      rw [hIMs]
      exact hI.frame r3 r4 _ _ hDR3 (by
        rw [hr4, unch_charge, unch_setW (by simp [piRegs])]; exact Unchanged.refl _ _ _ _ _)
        (by simp [hr4])
    have hu4 : U r4 = U r3 := hI.uframe r3 r4 [] [] piRegs [] (by
      rw [hr4, unch_charge, unch_setW (by simp [piRegs])]; exact Unchanged.refl _ _ _ _ _) hnIW
    refine ⟨p - (j + 1), by omega, j + 1, rfl, by omega, by simp [hr4], hDR4, ?_, ?_, ?_,
      by simp [hr4, hwl3, hr2, hwlr], by simp [hr4, hvl3, hr2, hvlr], by rw [hu4, hIMs]; simp only; omega⟩
    · rw [hr4, unch_charge, unch_setW mj]
      refine (hUr.trans ?_)
      refine (Unchanged.charge r 1 _ _ _ _).trans ?_
      refine (show Unchanged (r.charge 1) r2 (NA ++ IA) (NVA ++ IVA) (piRegs ++ NW ++ IW) (NVR ++ IVR) by
        rw [hr2, unch_charge, unch_setW mpx]; exact Unchanged.refl _ _ _ _ _).trans ?_
      exact hU3.mono (by simp) (by simp) (by simp) (by simp)
    · simp [hr4]; simp [hr2] at hc3a; omega
    · rw [hIMs]
      simp only [hr4, State.charge_cost, State.setW_cost]
      simp [hr2] at hc3b
      rw [Nat.mul_add]
      rw [Nat.add_mul]
      omega
  · have hj : j = p := by by_contra hc; rw [if_pos (by omega)] at hx; exact one_ne_zero hx
    subst hj
    have htk : (List.ofFn piv).take j = List.ofFn piv := List.take_of_length_le (by simp)
    have hIMp : IM j = BM.insManyC (dlOps G s) T f (List.ofFn piv) g (newC M B) := by
      simp only [hIM, htk]
    rw [hIMp] at hDRr hc2 hur
    have huc : U (r.charge 1) = U r :=
      hI.uframe r _ [] [] [] [] (Unchanged.charge r 1 _ _ _ _) (by simp)
    refine ⟨hI.frame r _ _ _ hDRr (by rw [unch_charge]; exact Unchanged.refl _ _ _ _ _) (by simp),
      by rw [unch_charge]; exact hUr, by simp; omega, by simp; omega, by simp [hwlr], by simp [hvlr],
      by rw [huc]; exact hur⟩

end Frontier.CHD.RamInit
