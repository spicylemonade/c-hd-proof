import Frontier.CHD.RamPiv

/-!
# Frontier.CHD.InsSeg — a new level structure filled from a stored key segment (owner agent-03)

**NON-GATE** (B-L4 glue, Layer B).  `insSeg dsNew dsIns arr eb elen`: evaluate `b := eb`, `len := elen`, create the
structure (`dsNew`, Layer A `newC M B`), then insert `arr[b + j]` for `j < len` in order (`dsIns`, vertex in `px`,
Layer A `insC dlOps T g D v (f v)`).  `insSeg_spec`: the result is `insManyC … L g (newC M B)` for the list `L` stored at
`arr[b, b + len)` — the shape of `BMLazy.BaseDH`'s leftover conversion (keys from the heap's slot array) and of
`initD`.  The `D` procedures are agent-01's abstract `DNewI` / `DInsI` (instantiated by B-L3).
-/

namespace Frontier.CHD.RamInit

open Frontier Frontier.RAM WExpr Stmt Frontier.CHD.RamLevel Frontier.CHD.BM

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}

/-- The registers written by `insSeg` itself. -/
def cvRegs : List String := ["cv.b", "cv.e", "cv.j", "px"]

/-- Evaluate the segment, create the structure, insert the segment's keys in order. -/
def insSeg (dsNew dsIns : Stmt) (arr : String) (eb elen : WExpr) : Stmt :=
  seq (wset "cv.b" eb)
  (seq (wset "cv.e" elen)
  (seq dsNew
  (seq (wset "cv.j" (lit 0))
  (.while (lt (var "cv.j") (var "cv.e"))
    (seq (wset "px" (load arr (add (var "cv.b") (var "cv.j"))))
    (seq dsIns (wset "cv.j" (add (var "cv.j") (lit 1)))))))))

/-- **The segment insertion is `insManyC` over the stored list.** -/
theorem insSeg_spec {dsNew dsIns : Stmt} {DR0 : State V → DGl G s → Prop}
    {DR : State V → DGl G s → DStrM G s → Prop} {Inv : DGl G s → DStrM G s → Prop}
    {f : Fin G.n → WLab G s} {T K C Cn M : ℕ} {B : WLab G s} {NA NVA NW NVR IA IVA IW IVR : List String}
    {arr : String} {eb elen : WExpr}
    {Pv : Fin G.n → Prop} {U : State V → ℕ} {Ucap : ℕ}
    (hN : DNewI ops dsNew DR0 DR M B Cn NA NVA NW NVR U Ucap)
    (hI : DInsI ops dsIns DR Inv f T K C IA IVA IW IVR cvRegs Pv U Ucap)
    (hNW : ∀ a ∈ NW, a ∉ cvRegs) (hNA : arr ∉ NA) (hIA : arr ∉ IA)
    (st : State V) (g : DGl G s) {b : ℕ} {L : List (Fin G.n)}
    (hD0 : ∀ r : State V, Unchanged st r [] [] ["cv.b", "cv.e"] [] → DR0 r g)
    (hb : evalW st eb = some b) (he : evalW ((st.setW "cv.b" b).charge 1) elen = some L.length)
    (hseg : ∀ j (h : j < L.length), st.wa arr (b + j) = (L[j] : ℕ)) (hL : b + L.length ≤ st.wlen arr)
    (hcap : b + L.length + 2 < st.cap)
    (hInv : ∀ k ≤ L.length, Inv (BM.insManyC (dlOps G s) T f (L.take k) g (newC M B)).1
      (BM.insManyC (dlOps G s) T f (L.take k) g (newC M B)).2.1)
    (hPv : ∀ j (h : j < L.length), Pv L[j])
    (hUb : U st + 1 + (BM.insManyC (dlOps G s) T f L g (newC M B)).2.2 + L.length ≤ Ucap) :
    Runs ops (insSeg dsNew dsIns arr eb elen) st (fun r =>
      DR r (BM.insManyC (dlOps G s) T f L g (newC M B)).1 (BM.insManyC (dlOps G s) T f L g (newC M B)).2.1 ∧
      Unchanged st r (NA ++ IA) (NVA ++ IVA) (cvRegs ++ NW ++ IW) (NVR ++ IVR) ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + Cn + 4 + K * (BM.insManyC (dlOps G s) T f L g (newC M B)).2.2 +
        L.length * (C + 5)) := by
  classical
  set IM := fun k : ℕ => BM.insManyC (dlOps G s) T f (L.take k) g (newC M B) with hIM
  -- `cv.b := eb ; cv.e := elen`
  refine runs_seq (runs_wset hb ?_)
  refine runs_seq (runs_wset he ?_)
  set s2 := ((((st.setW "cv.b" b).charge 1).setW "cv.e" L.length).charge 1) with hs2
  have hU2 : Unchanged st s2 [] [] ["cv.b", "cv.e"] [] := by
    rw [hs2, unch_charge, unch_setW (by simp), unch_charge, unch_setW (by simp)]
    exact Unchanged.refl _ _ _ _ _
  have hnotIW : ∀ x ∈ cvRegs, x ∉ IW := fun x hx h => (hI.regs x h).1 hx
  have hus2 : U s2 = U st := hI.uframe st s2 [] [] ["cv.b", "cv.e"] [] hU2 (fun a ha =>
    hnotIW a (by simp at ha; rcases ha with rfl | rfl <;> simp [cvRegs]))
  -- `dsNew`
  refine runs_seq ((hN.run s2 g (hD0 s2 hU2) (by omega)).mono ?_)
  rintro r0 ⟨hDR0, hU0, hc0a, hc0b, -, -, hu0⟩
  have hcap0 : r0.cap = st.cap := by rw [hU0.cap]; simp [hs2]
  have hb0 : r0.w "cv.b" = b := by
    rw [hU0.wreg "cv.b" (fun h => hNW _ h (by simp [cvRegs]))]; simp [hs2]
  have he0 : r0.w "cv.e" = L.length := by
    rw [hU0.wreg "cv.e" (fun h => hNW _ h (by simp [cvRegs]))]; simp [hs2]
  have ha0 : r0.wa arr = st.wa arr := by rw [(hU0.warr arr hNA).1]; simp [hs2]
  have hal0 : r0.wlen arr = st.wlen arr := by rw [(hU0.warr arr hNA).2]; simp [hs2]
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by rw [hcap0]; omega)) ?_)
  set r1 := (r0.setW "cv.j" 0).charge 1 with hr1
  have hDR1 : DR r1 g (newC M B) := hI.frame r0 r1 g _ hDR0 (by
    rw [hr1, unch_charge, unch_setW (by simp [cvRegs])]; exact Unchanged.refl _ _ _ _ _)
    (by simp [hr1])
  have hIM0 : IM 0 = (g, newC M B, 0) := by simp [hIM, BM.insManyC]
  have hu1 : U r1 = U r0 := hI.uframe r0 r1 [] [] cvRegs [] (by
    rw [hr1, unch_charge, unch_setW (by simp [cvRegs])]; exact Unchanged.refl _ _ _ _ _) hnotIW
  have hIMle : ∀ k, (IM k).2.2 ≤ (BM.insManyC (dlOps G s) T f L g (newC M B)).2.2 :=
    fun k => insManyC_cost_take_le T f L k g (newC M B)
  have htake : ∀ j (hj : j < L.length), L.take (j + 1) = L.take j ++ [L[j]] := by
    intro j hj
    rw [List.take_succ, List.getElem?_eq_getElem hj]
    simp
  -- the frame of the whole run
  have hU20 : Unchanged st r1 (NA ++ IA) (NVA ++ IVA) (cvRegs ++ NW ++ IW) (NVR ++ IVR) := by
    rw [hr1, unch_charge, unch_setW (by simp [cvRegs])]
    exact (hU2.mono (by simp) (by simp) (by intro x hx; simp at hx ⊢; rcases hx with rfl | rfl <;> simp [cvRegs])
      (by simp)).trans (hU0.mono (by simp) (by simp) (by simp) (by simp))
  refine runs_while_nat (fun m r => ∃ j, m = L.length - j ∧ j ≤ L.length ∧ r.w "cv.j" = j ∧
      r.w "cv.b" = b ∧ r.w "cv.e" = L.length ∧ r.wa arr = st.wa arr ∧ r.wlen arr = st.wlen arr ∧
      DR r (IM j).1 (IM j).2.1 ∧
      Unchanged st r (NA ++ IA) (NVA ++ IVA) (cvRegs ++ NW ++ IW) (NVR ++ IVR) ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + Cn + 3 + K * (IM j).2.2 + j * (C + 5) ∧
      U r ≤ U st + 1 + (IM j).2.2 + j) _ ?_ L.length r1 ?_
  swap
  · refine ⟨0, by simp, by omega, by simp [hr1], by simp [hr1, hb0], by simp [hr1, he0], by simp [hr1, ha0],
      by simp [hr1, hal0], by rw [hIM0]; exact hDR1, hU20, by simp [hr1, hs2] at hc0a ⊢; omega, ?_,
      by rw [hIM0, hu1]; simp; omega⟩
    rw [hIM0]; simp [hr1, hs2] at hc0b ⊢; omega
  rintro m r ⟨j, rfl, hjL, hjr, hbr, her, har, halr, hDRr, hUr, hc1, hc2, hur⟩
  have hcapr : r.cap = st.cap := hUr.cap
  have eT : evalW r (lt (var "cv.j") (var "cv.e")) = some (if j < L.length then 1 else 0) := by
    simp only [evalW_lt', evalW_var, hjr, her, Option.bind_some]
    split_ifs <;> simp [fit_of_lt (show 1 < r.cap by rw [hcapr]; omega), fit_of_lt (show 0 < r.cap by omega)]
  refine ⟨if j < L.length then 1 else 0, eT, fun hx => ?_, fun hx => ?_⟩
  · have hj : j < L.length := by by_contra hc; rw [if_neg hc] at hx; exact hx rfl
    -- `px := arr[cv.b + cv.j]`
    have eP : evalW (r.charge 1) (load arr (add (var "cv.b") (var "cv.j"))) = some (L[j] : ℕ) := by
      simp [hbr, hjr, fit_of_lt (show b + j < r.cap by rw [hcapr]; omega), halr,
        show b + j < st.wlen arr by omega, har, hseg j hj]
    refine runs_seq (runs_wset eP ?_)
    set r2 := ((r.charge 1).setW "px" (L[j] : ℕ)).charge 1 with hr2
    have hU12 : Unchanged r r2 [] [] cvRegs [] := by
      rw [hr2, unch_charge, unch_setW (by simp [cvRegs]), unch_charge]; exact Unchanged.refl _ _ _ _ _
    have hDR2 : DR r2 (IM j).1 (IM j).2.1 := hI.frame r r2 _ _ hDRr hU12 (by simp [hr2] <;> omega)
    have hIMs : IM (j + 1) =
        ((BM.insC (dlOps G s) T (IM j).1 (IM j).2.1 L[j] (f L[j])).1,
         (BM.insC (dlOps G s) T (IM j).1 (IM j).2.1 L[j] (f L[j])).2.1,
         (IM j).2.2 + (BM.insC (dlOps G s) T (IM j).1 (IM j).2.1 L[j] (f L[j])).2.2) := by
      simp only [hIM]
      rw [htake j hj, insManyC_snoc]
    have hu2 : U r2 = U r := hI.uframe r r2 [] [] cvRegs [] hU12 hnotIW
    have hcs := hIMle (j + 1)
    rw [hIMs] at hcs
    simp only at hcs
    refine runs_seq ((hI.run r2 (IM j).1 (IM j).2.1 L[j] hDR2 (hInv j hjL) (hPv j hj)
      (by simp [hr2]) (by rw [hu2]; omega)).mono ?_)
    rintro r3 ⟨hDR3, hU3, hc3a, hc3b, -, -, hu3⟩
    have hj3 : r3.w "cv.j" = j := by
      rw [hU3.wreg "cv.j" (hnotIW _ (by simp [cvRegs]))]; simp [hr2, hjr]
    have hb3 : r3.w "cv.b" = b := by
      rw [hU3.wreg "cv.b" (hnotIW _ (by simp [cvRegs]))]; simp [hr2, hbr]
    have he3 : r3.w "cv.e" = L.length := by
      rw [hU3.wreg "cv.e" (hnotIW _ (by simp [cvRegs]))]; simp [hr2, her]
    have ha3 : r3.wa arr = st.wa arr := by rw [(hU3.warr arr hIA).1]; simp [hr2, har]
    have hal3 : r3.wlen arr = st.wlen arr := by rw [(hU3.warr arr hIA).2]; simp [hr2, halr]
    have hcap3 : r3.cap = st.cap := by rw [hU3.cap]; simp [hr2, hcapr]
    have e5 : evalW r3 (add (var "cv.j") (lit 1)) = some (j + 1) := by
      simp [hj3, hcap3, fit_of_lt (show j + 1 < st.cap by omega), fit_of_lt (show 1 < st.cap by omega)]
    refine runs_wset e5 ?_
    set r4 := (r3.setW "cv.j" (j + 1)).charge 1 with hr4
    have hDR4 : DR r4 (IM (j + 1)).1 (IM (j + 1)).2.1 := by
      rw [hIMs]
      exact hI.frame r3 r4 _ _ hDR3 (by
        rw [hr4, unch_charge, unch_setW (by simp [cvRegs])]; exact Unchanged.refl _ _ _ _ _)
        (by simp [hr4])
    have hu4 : U r4 = U r3 := hI.uframe r3 r4 [] [] cvRegs [] (by
      rw [hr4, unch_charge, unch_setW (by simp [cvRegs])]; exact Unchanged.refl _ _ _ _ _) hnotIW
    refine ⟨L.length - (j + 1), by omega, j + 1, rfl, by omega, by simp [hr4], by simp [hr4, hb3],
      by simp [hr4, he3], by simp [hr4, ha3], by simp [hr4, hal3], hDR4, ?_, ?_, ?_,
      by rw [hu4, hIMs]; simp only; omega⟩
    · rw [hr4, unch_charge, unch_setW (by simp [cvRegs])]
      refine (hUr.trans ?_)
      refine (Unchanged.charge r 1 _ _ _ _).trans ?_
      refine (show Unchanged (r.charge 1) r2 (NA ++ IA) (NVA ++ IVA) (cvRegs ++ NW ++ IW) (NVR ++ IVR) by
        rw [hr2, unch_charge, unch_setW (by simp [cvRegs])]; exact Unchanged.refl _ _ _ _ _).trans ?_
      exact hU3.mono (by simp) (by simp) (by simp) (by simp)
    · simp [hr4]; simp [hr2] at hc3a; omega
    · rw [hIMs]
      simp only [hr4, State.charge_cost, State.setW_cost]
      simp [hr2] at hc3b
      rw [Nat.mul_add, Nat.add_mul]
      omega
  · have hj : j = L.length := by by_contra hc; rw [if_pos (by omega)] at hx; exact one_ne_zero hx
    subst hj
    have htk : L.take L.length = L := List.take_length
    have hIMp : IM L.length = BM.insManyC (dlOps G s) T f L g (newC M B) := by
      simp only [hIM, htk]
    rw [hIMp] at hDRr hc2
    refine ⟨hI.frame r _ _ _ hDRr (by rw [unch_charge]; exact Unchanged.refl _ _ _ _ _) (by simp),
      by rw [unch_charge]; exact hUr, by simp; omega, by simp; omega⟩

end Frontier.CHD.RamInit
