import Frontier.CHD.RamPiv

/-!
# Frontier.CHD.RamT6 — BM.25 of the RAM spine: re-insertion of the frontier `T6` (agent-01)

**NON-GATE** (B-L4, Layer B).  `t6Prog tst dsIns`: for every `x` of the level-`l` `S` row (in row
order), `tst` decides `P x` (bit `t6.b`; instantiated by B-LAB with `P x := B'f ≤ d x ∧ d x < B`)
and, if it holds, `dsIns` inserts `x` with key `f x`.  Layer A: `insManyC … f (xs.filter P) g D`,
i.e. finD's `T6` insertions with `lT6 = xs.filter P`.
-/

namespace Frontier.CHD.RamInit

open Frontier Frontier.RAM WExpr Stmt Frontier.CHD.RamLevel Frontier.CHD.BM

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}

/-- The registers written by `t6Prog` itself. -/
def t6Regs : List String := ["t6.i", "px"]

/-- **A vertex test**: `t6.b := [P px]`, writing only the registers `TW`, cost at most `C`,
keeping the representation `DR` of the `D` state. -/
structure TestI (ops : VOps V) (tst : Stmt) (DR : State V → DGl G s → DStrM G s → Prop)
    (P : ℕ → Prop) [DecidablePred P] (C : ℕ) (TW TV : List String) : Prop where
  run : ∀ st g D, DR st g D → st.w "px" < G.n → Runs ops tst st (fun r =>
    r.w "t6.b" = (if P (st.w "px") then 1 else 0) ∧ Unchanged st r [] [] TW TV ∧
    st.cost ≤ r.cost ∧ r.cost ≤ st.cost + C ∧ DR r g D)
  regs : ∀ a ∈ TW, a ≠ "t6.i" ∧ a ≠ "px" ∧ a ≠ "lvl" ∧ a ≠ "n"
  bit : "t6.b" ∈ TW

/-- **BM.25**: the frontier members with `P` are re-inserted. -/
def t6Prog (tst dsIns : Stmt) : Stmt :=
  seq (wset "t6.i" (lit 0))
  (.while (lt (var "t6.i") (load "S.len" (var "lvl")))
    (seq (wset "px" (load "S" (rb (var "t6.i"))))
    (seq tst
    (seq (ite (var "t6.b") dsIns skip)
         (incr "t6.i")))))


/-- **BM.25 is correct**: the `D` state becomes `insManyC … f (lS.filter P) g D`, where `lS` is the
`S` row. -/
theorem t6Prog_spec {tst dsIns : Stmt} {DR : State V → DGl G s → DStrM G s → Prop}
    {Inv : DGl G s → DStrM G s → Prop} {f : Fin G.n → WLab G s} {T K C Ct : ℕ}
    {IA IVA IW IVR TW TV : List String} {P : ℕ → Prop} [DecidablePred P]
    {Pv : Fin G.n → Prop} {U : State V → ℕ} {Ucap : ℕ}
    (hT : TestI ops tst DR P Ct TW TV)
    (hI : DInsI ops dsIns DR Inv f T K C IA IVA IW IVR t6Regs Pv U Ucap)
    (st : State V) (g : DGl G s) (D : DStrM G s) (hDR : DR st g D) {l n : ℕ} {lS : List (Fin G.n)}
    (hS : RowRep st "S" "S.len" n l (lS.map (fun x : Fin G.n => (x : ℕ))))
    (hl : st.w "lvl" = l) (hn : st.w "n" = n) (hcap : (l + 1) * n + 2 < st.cap)
    (hInv : ∀ k (hk : k < lS.length), P (lS[k] : ℕ) →
      Inv (BM.insManyC (dlOps G s) T f ((lS.take k).filter (fun x : Fin G.n => decide (P (x : ℕ)))) g D).1
        (BM.insManyC (dlOps G s) T f ((lS.take k).filter (fun x : Fin G.n => decide (P (x : ℕ)))) g D).2.1)
    (hPv : ∀ k (hk : k < lS.length), P (lS[k] : ℕ) → Pv lS[k]) (hTU : ∀ a ∈ TW, a ∉ IW)
    (hUb : U st + (BM.insManyC (dlOps G s) T f (lS.filter (fun x : Fin G.n => decide (P (x : ℕ)))) g D).2.2 +
      lS.length ≤ Ucap) :
    Runs ops (t6Prog tst dsIns) st (fun r =>
      DR r (BM.insManyC (dlOps G s) T f (lS.filter (fun x : Fin G.n => decide (P (x : ℕ)))) g D).1
        (BM.insManyC (dlOps G s) T f (lS.filter (fun x : Fin G.n => decide (P (x : ℕ)))) g D).2.1 ∧
      Unchanged st r IA IVA (t6Regs ++ TW ++ IW) (TV ++ IVR) ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + 2 + K * (BM.insManyC (dlOps G s) T f (lS.filter (fun x : Fin G.n => decide (P (x : ℕ)))) g D).2.2 +
        lS.length * (Ct + C + 6) ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen ∧
      U r ≤ U st + (BM.insManyC (dlOps G s) T f (lS.filter (fun x : Fin G.n => decide (P (x : ℕ)))) g D).2.2 +
        lS.length) := by
  classical
  have hxl := hS.1
  simp only [List.length_map] at hxl
  have hn1 : n ≤ (l + 1) * n := Nat.le_mul_of_pos_left n (by omega)
  have hSlen : l < st.wlen "S.len" := hS.2.2.1
  have hSl : st.wa "S.len" l = lS.length := by have := hS.2.2.2.1; simpa using this
  set IM := fun k : ℕ => BM.insManyC (dlOps G s) T f ((lS.take k).filter (fun x : Fin G.n => decide (P (x : ℕ)))) g D with hIM
  have hIM0 : IM 0 = (g, D, 0) := by simp [hIM, BM.insManyC]
  have hnIW : ∀ a ∈ t6Regs, a ∉ IW := fun a ha h => (hI.regs a h).1 ha
  have hIMle : ∀ k, (IM k).2.2 ≤
      (BM.insManyC (dlOps G s) T f (lS.filter (fun x : Fin G.n => decide (P (x : ℕ)))) g D).2.2 := by
    intro k
    have := insManyC_cost_append_le T f ((lS.take k).filter (fun x : Fin G.n => decide (P (x : ℕ))))
      ((lS.drop k).filter (fun x : Fin G.n => decide (P (x : ℕ)))) g D
    rwa [← List.filter_append, List.take_append_drop] at this
  have mi : "t6.i" ∈ t6Regs ++ TW ++ IW := by simp [t6Regs]
  have mpx : "px" ∈ t6Regs ++ TW ++ IW := by simp [t6Regs]
  have hregs : ∀ a, a = "lvl" ∨ a = "n" → a ∉ t6Regs ++ TW ++ IW := by
    intro a ha hm
    simp only [List.mem_append] at hm
    rcases hm with (h1 | h1) | h1
    · simp [t6Regs] at h1; rcases ha with rfl | rfl <;> simp at h1
    · rcases ha with rfl | rfl
      · exact (hT.regs _ h1).2.2.1 rfl
      · exact (hT.regs _ h1).2.2.2 rfl
    · rcases ha with rfl | rfl
      · exact (hI.regs _ h1).2.1 rfl
      · exact (hI.regs _ h1).2.2 rfl
  have harrs : ∀ a, a = "S" ∨ a = "S.len" → a ∉ IA := by
    intro a ha hm
    rcases ha with rfl | rfl
    · exact (hI.arrs _ hm).2.2.1 rfl
    · exact (hI.arrs _ hm).2.2.2 rfl
  have hfilt : ∀ k (hk : k < lS.length), (lS.take (k + 1)).filter (fun x : Fin G.n => decide (P (x : ℕ))) =
      (lS.take k).filter (fun x : Fin G.n => decide (P (x : ℕ))) ++
        (if P (lS[k] : ℕ) then ([lS[k]] : List (Fin G.n)) else []) := by
    intro k hk
    rw [List.take_succ, List.getElem?_eq_getElem hk, List.filter_append]
    simp only [Option.toList_some, List.filter_cons, List.filter_nil]
    split_ifs <;> simp_all
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by omega)) ?_)
  set r1 := (st.setW "t6.i" 0).charge 1 with hr1
  have hDR1 : DR r1 g D := hI.frame st r1 g D hDR (by
    rw [hr1, unch_charge, unch_setW (by simp [t6Regs])]; exact Unchanged.refl _ _ _ _ _)
    (by simp [hr1])
  have hu1 : U r1 = U st := hI.uframe st r1 [] [] t6Regs [] (by
    rw [hr1, unch_charge, unch_setW (by simp [t6Regs])]; exact Unchanged.refl _ _ _ _ _) hnIW
  refine runs_while_nat (fun m r => ∃ k, m = lS.length - k ∧ k ≤ lS.length ∧ r.w "t6.i" = k ∧
      DR r (IM k).1 (IM k).2.1 ∧ Unchanged st r IA IVA (t6Regs ++ TW ++ IW) (TV ++ IVR) ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + 1 + K * (IM k).2.2 + k * (Ct + C + 6) ∧ r.wlen = st.wlen ∧
      r.vlen = st.vlen ∧ U r ≤ U st + (IM k).2.2 + k) _ ?_ lS.length r1 ?_
  swap
  · refine ⟨0, by simp, by omega, by simp [hr1], by rw [hIM0]; exact hDR1, ?_, by simp [hr1],
      by rw [hIM0]; simp [hr1], by simp [hr1], by simp [hr1], by rw [hIM0, hu1]; simp⟩
    rw [hr1, unch_charge, unch_setW mi]; exact Unchanged.refl _ _ _ _ _
  rintro m r ⟨k, rfl, hkl, hkr, hDRr, hUr, hc1, hc2, hwlr, hvlr, hur⟩
  have hcapr : r.cap = st.cap := hUr.cap
  have hlr : r.w "lvl" = l := by rw [hUr.wreg "lvl" (hregs _ (Or.inl rfl))]; exact hl
  have hnr : r.w "n" = n := by rw [hUr.wreg "n" (hregs _ (Or.inr rfl))]; exact hn
  have hSr := hUr.warr "S" (harrs _ (Or.inl rfl))
  have hSlr := hUr.warr "S.len" (harrs _ (Or.inr rfl))
  have eT : evalW r (lt (var "t6.i") (load "S.len" (var "lvl"))) =
      some (if k < lS.length then 1 else 0) := by
    rw [evalW_lt_of (by rw [evalW_var, hkr]) (x := k) (y := lS.length)
      (by simp [hlr, hSlr.1, hSlr.2, hSlen, hSl]) (by rw [hcapr]; omega)]
  refine ⟨if k < lS.length then 1 else 0, eT, fun hx => ?_, fun hx => ?_⟩
  · have hk : k < lS.length := by by_contra hc; rw [if_neg hc] at hx; exact hx rfl
    set x := lS[k] with hxdef
    -- `px := S[lvl n + t6.i]`
    have eP : evalW (r.charge 1) (load "S" (rb (var "t6.i"))) = some (x : ℕ) := by
      have hlt : l * n + k < st.wlen "S" := by have := hS.2.1; have := row_index_lt (l := l) (show k < n by omega); omega
      rw [eval_row_load (r.charge 1) "S" (e := var "t6.i") (i := k) (by simpa using hlr)
        (by simpa using hnr) (by simp [hkr]) (by simp [hSr.2]; exact hlt)
        (by simp [hcapr]; have := row_index_lt (l := l) (show k < n by omega); omega)]
      have := hS.2.2.2.2 k (by simpa using hk)
      simp only [List.getElem_map] at this
      simp [hSr.1, this, hxdef]
    refine runs_seq (runs_wset eP ?_)
    set r2 := ((r.charge 1).setW "px" (x : ℕ)).charge 1 with hr2
    have hc2r : r2.cost = r.cost + 2 := by simp [hr2]
    have hDR2 : DR r2 (IM k).1 (IM k).2.1 := hI.frame r r2 _ _ hDRr (by
      rw [hr2, unch_charge, unch_setW (by simp [t6Regs]), unch_charge]; exact Unchanged.refl _ _ _ _ _)
      (by simp [hr2] <;> omega)
    refine runs_seq ((hT.run r2 _ _ hDR2 (by simp [hr2])).mono ?_)
    rintro r3 ⟨hb3, hU3, hc3a, hc3b, hDR3⟩
    have hwl3 : r3.wlen = r.wlen := by
      funext a; rw [(hU3.warr a (by simp)).2]; simp [hr2]
    have hvl3 : r3.vlen = r.vlen := by
      funext a; rw [(hU3.varr a (by simp)).2]; simp [hr2]
    have hpx3 : r3.w "px" = (x : ℕ) := by
      rw [hU3.wreg "px" (fun h => (hT.regs _ h).2.1 rfl)]; simp [hr2]
    have hk3 : r3.w "t6.i" = k := by
      rw [hU3.wreg "t6.i" (fun h => (hT.regs _ h).1 rfl)]; simp [hr2, hkr]
    have hcap3 : r3.cap = st.cap := by rw [hU3.cap]; simp [hr2, hcapr]
    have hpx2 : r2.w "px" = (x : ℕ) := by simp [hr2]
    rw [hpx2] at hb3
    have hu2 : U r2 = U r := hI.uframe r r2 [] [] t6Regs [] (by
      rw [hr2, unch_charge, unch_setW (by simp [t6Regs]), unch_charge]; exact Unchanged.refl _ _ _ _ _)
      hnIW
    have hu3 : U r3 = U r2 := hI.uframe r2 r3 [] [] TW TV hU3 hTU
    have hU23 : Unchanged st r3 IA IVA (t6Regs ++ TW ++ IW) (TV ++ IVR) := by
      refine hUr.trans ((Unchanged.charge r 1 _ _ _ _).trans ?_)
      refine (show Unchanged (r.charge 1) r2 IA IVA (t6Regs ++ TW ++ IW) (TV ++ IVR) by
        rw [hr2, unch_charge, unch_setW mpx]; exact Unchanged.refl _ _ _ _ _).trans ?_
      exact hU3.mono (by simp) (by simp) (by intro a ha; simp [ha]) (by simp)
    refine runs_seq ?_
    by_cases hPx : P (x : ℕ)
    · have h1 : r3.w "t6.b" = 1 := by rw [hb3, if_pos hPx]
      refine runs_ite_true (by simp [h1]) one_ne_zero ?_
      have hInvk := hInv k hk hPx
      have hIMs : IM (k + 1) = ((BM.insC (dlOps G s) T (IM k).1 (IM k).2.1 x (f x)).1,
          (BM.insC (dlOps G s) T (IM k).1 (IM k).2.1 x (f x)).2.1,
          (IM k).2.2 + (BM.insC (dlOps G s) T (IM k).1 (IM k).2.1 x (f x)).2.2) := by
        simp only [hIM]
        rw [hfilt k hk, if_pos hPx, insManyC_snoc]
      have hcs := hIMle (k + 1)
      rw [hIMs] at hcs
      simp only at hcs
      have hu3c : U (r3.charge 1) = U r3 :=
        hI.uframe r3 _ [] [] [] [] (Unchanged.charge r3 1 _ _ _ _) (by simp)
      refine ((hI.run (r3.charge 1) (IM k).1 (IM k).2.1 x (by
        exact hI.frame r3 _ _ _ hDR3 (by rw [unch_charge]; exact Unchanged.refl _ _ _ _ _) (by simp))
        hInvk (hPv k hk hPx) (by simp [hpx3]) (by rw [hu3c, hu3, hu2]; omega)).mono ?_)
      rintro r4 ⟨hDR4, hU4, hc4a, hc4b, hwl4, hvl4, hu4⟩
      have hk4 : r4.w "t6.i" = k := by
        rw [hU4.wreg "t6.i" (fun h => (hI.regs _ h).1 (by simp [t6Regs]))]; simp [hk3]
      have hcap4 : r4.cap = st.cap := by rw [hU4.cap]; simp [hcap3]
      have e5 : evalW r4 (add (var "t6.i") (lit 1)) = some (k + 1) := by
        simp [hk4, hcap4, fit_of_lt (show k + 1 < st.cap by omega), fit_of_lt (show 1 < st.cap by omega)]
      refine runs_wset e5 ?_
      set r5 := (r4.setW "t6.i" (k + 1)).charge 1 with hr5
      have hu5 : U r5 = U r4 := hI.uframe r4 r5 [] [] t6Regs [] (by
        rw [hr5, unch_charge, unch_setW (by simp [t6Regs])]; exact Unchanged.refl _ _ _ _ _) hnIW
      refine ⟨lS.length - (k + 1), by omega, k + 1, rfl, by omega, by simp [hr5], ?_, ?_, ?_, ?_,
        by simp [hr5, hwl4, hwl3, hwlr], by simp [hr5, hvl4, hvl3, hvlr],
        by rw [hu5, hIMs]; simp only; rw [hu3c, hu3, hu2] at hu4; omega⟩
      · rw [hIMs]
        exact hI.frame r4 r5 _ _ hDR4 (by
          rw [hr5, unch_charge, unch_setW (by simp [t6Regs])]; exact Unchanged.refl _ _ _ _ _)
          (by simp [hr5])
      · rw [hr5, unch_charge, unch_setW mi]
        exact hU23.trans ((Unchanged.charge r3 1 _ _ _ _).trans
          (hU4.mono (by simp) (by simp) (by intro a ha; simp [ha]) (by simp)))
      · simp [hr5]; simp at hc4a; omega
      · rw [hIMs]
        simp only [hr5, State.charge_cost, State.setW_cost]
        simp only [State.charge_cost] at hc4b
        simp [hr2] at hc3b
        rw [Nat.mul_add, Nat.add_mul]
        omega
    · have h0 : r3.w "t6.b" = 0 := by rw [hb3, if_neg hPx]
      refine runs_ite_false (by simp [h0]) ?_
      refine runs_skip ?_
      set r4 := (r3.charge 1).charge 1 with hr4
      have e5 : evalW r4 (add (var "t6.i") (lit 1)) = some (k + 1) := by
        simp [hr4, hk3, hcap3, fit_of_lt (show k + 1 < st.cap by omega), fit_of_lt (show 1 < st.cap by omega)]
      refine runs_wset e5 ?_
      set r5 := (r4.setW "t6.i" (k + 1)).charge 1 with hr5
      have hIMs : IM (k + 1) = IM k := by
        simp only [hIM]; rw [hfilt k hk, if_neg hPx, List.append_nil]
      have hu5 : U r5 = U r3 := hI.uframe r3 r5 [] [] t6Regs [] (by
        rw [hr5, unch_charge, unch_setW (by simp [t6Regs]), hr4, unch_charge, unch_charge]
        exact Unchanged.refl _ _ _ _ _) hnIW
      refine ⟨lS.length - (k + 1), by omega, k + 1, rfl, by omega, by simp [hr5], ?_, ?_, ?_, ?_,
        by simp [hr5, hr4, hwl3, hwlr], by simp [hr5, hr4, hvl3, hvlr],
        by rw [hu5, hIMs, hu3, hu2]; omega⟩
      · rw [hIMs]
        exact hI.frame r3 r5 _ _ hDR3 (by
          rw [hr5, unch_charge, unch_setW (by simp [t6Regs]), hr4, unch_charge, unch_charge]
          exact Unchanged.refl _ _ _ _ _)
          (by simp [hr5, hr4] <;> omega)
      · rw [hr5, unch_charge, unch_setW mi, hr4, unch_charge, unch_charge]; exact hU23
      · simp [hr5, hr4]; omega
      · rw [hIMs]
        simp only [hr5, hr4, State.charge_cost, State.setW_cost]
        simp [hr2] at hc3b
        rw [Nat.add_mul]
        omega
  · have hk : k = lS.length := by by_contra hc; rw [if_pos (by omega)] at hx; exact one_ne_zero hx
    subst hk
    have htk : lS.take lS.length = lS := List.take_length
    have hIMp : IM lS.length = BM.insManyC (dlOps G s) T f (lS.filter (fun x : Fin G.n => decide (P (x : ℕ)))) g D := by
      simp only [hIM, htk]
    rw [hIMp] at hDRr hc2 hur
    have huc : U (r.charge 1) = U r :=
      hI.uframe r _ [] [] [] [] (Unchanged.charge r 1 _ _ _ _) (by simp)
    refine ⟨hI.frame r _ _ _ hDRr (by rw [unch_charge]; exact Unchanged.refl _ _ _ _ _) (by simp),
      by rw [unch_charge]; exact hUr, by simp; omega, by simp; omega, by simp [hwlr], by simp [hvlr],
      by rw [huc]; exact hur⟩

end Frontier.CHD.RamInit
