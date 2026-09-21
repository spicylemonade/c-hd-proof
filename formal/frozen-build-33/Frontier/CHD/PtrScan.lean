import Frontier.CHD.WinScanC

/-!
# PtrScan — the pure pointer advance (base case sets `sp.ptr`; agent-02, NON-GATE)

`ptrInner Kb kbf` is the window inner loop with `relaxWin := skip`: from `sp.p` it advances
while the candidate `d[ru] ⊕ e` is below the bound `B` (block `Kb`, B-LAB's `candB`).
`ptrSet Kb kbf` runs it from the head `gSt[ru]` of `ru`'s CSR range and stores the stop slot into
`sp.ptr[ru]`, establishing the window pointer invariant `PtrAt r (d u) u B` (agent-08, 17:27:
the base case must set the pointers of the extracted vertices).  Only registers and the cell
`sp.ptr[u]` are written; cost `≤ 25 · deg u + 30`.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.WinScan

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.MLab Frontier.CHD.LabTab
  Frontier.CHD.DIns Frontier.CHD.RelaxIns Frontier.CHD.RamBaseCase WExpr Stmt

variable {G : Graph} {s : Fin G.n}

/-- The pointer-advance loop (`windowScan`'s inner loop with `relaxWin := skip`). -/
def ptrInner (Kb : LReg) (kbf : String) : Stmt :=
  .while (var "sp.go")
    (seq (ite (lt (var "sp.p") (var "sp.pe"))
            (seq (wset "re" (var "sp.p")) (LabRAM.candB Kb kbf "sp.lt"))
            (wset "sp.lt" (lit 0)))
    (ite (var "sp.lt")
       (seq skip (wset "sp.p" (add (var "sp.p") (lit 1))))
       (wset "sp.go" (lit 0))))

/-- `ptr[ru] :=` the first slot of `ru`'s range whose candidate is not below the bound. -/
def ptrSet (Kb : LReg) (kbf : String) : Stmt :=
  seq (wset "sp.p" (load "gSt" (var "ru")))
  (seq (wset "sp.pe" (load "gSt" (add (var "ru") (lit 1))))
  (seq (wset "sp.go" (lit 1))
  (seq (ptrInner Kb kbf)
       (wstore "sp.ptr" (var "ru") (var "sp.p")))))

/-- Registers written by the pointer advance. -/
def ptrW : List String := ["re", "sp.lt", "sp.p", "sp.go"] ++ X0.ws ++ ["lab.c1", "lab.c2"]

/-- Register hygiene of the bound block. -/
structure PtrHyg (Kb : LReg) (kbf : String) : Prop where
  kb : BoundRegs Kb kbf
  w : ∀ a ∈ Kb.ws ++ [kbf], a ∉ ptrW ++ ["ru", "sp.pe"]

open Classical in
/-- **The pointer advance** from `sp.p = p0` inside `u`'s range `[.., pe)`. -/
theorem ptrInner_spec {c0 : ℕ} {Kb : LReg} {kbf : String} (hy : PtrHyg Kb kbf)
    (st : State ℝ≥0) (d : Labels G s) (H : Fin G.n → ℕ → List (Fin G.m))
    (hL : LabAt st d H c0) (hg : GraphAt st G) (hcsr : CSRAt st G) (B : WLab G s)
    (hK : WHolds st Kb kbf H (vc st) B) (u : Fin G.n) (hfin : d u ≠ ⊤) (p0 pe : ℕ)
    (hp0 : st.w "sp.p" = p0) (hpe : st.w "sp.pe" = pe) (hgo : st.w "sp.go" = 1)
    (hru : st.w "ru" = u)
    (hrange : st.wa "gSt" u ≤ p0 ∧ p0 ≤ pe ∧ pe = st.wa "gSt" ((u : ℕ) + 1))
    (hB : st.cost + (pe - p0 + 1) * 25 + 32 ≤ c0 + st.cap) (hm : G.m + 2 ≤ st.cap) :
    Runs realOps (ptrInner Kb kbf) st (fun r => ∃ q, p0 ≤ q ∧ q ≤ pe ∧ r.w "sp.p" = q ∧
      (∀ j (hj : j < G.m), p0 ≤ j → j < q → ext (d u) ⟨j, hj⟩ < B) ∧
      (q < pe → ∃ hq : q < G.m, ¬ ext (d u) ⟨q, hq⟩ < B) ∧
      Unchanged st r [] [] ptrW [X0.l] ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + (q - p0) * 25 + 26) := by
  have hpeM : pe ≤ G.m := by rw [hrange.2.2]; exact hcsr.le_m u
  have hKw : ∀ a ∈ Kb.ws, a ∉ ptrW := fun a ha h =>
    hy.w a (by simp [ha]) (List.mem_append_left _ h)
  have hKf : kbf ∉ ptrW := fun h => hy.w kbf (by simp) (List.mem_append_left _ h)
  have hKl : Kb.l ∉ [X0.l] := fun h => hy.kb.l (by
    simp only [X0, List.mem_singleton] at h; rw [h]; decide)
  -- the state facts carried along
  have hS : ∀ r : State ℝ≥0, Unchanged st r [] [] ptrW [X0.l] → st.cost ≤ r.cost →
      LabAt r d H c0 ∧ GraphAt r G ∧ WHolds r Kb kbf H (vc r) B ∧ r.cap = st.cap := by
    intro r hU hc
    have hvc : vc (G := G) r = vc st := vc_of_unchanged hU (by simp)
    refine ⟨hL.of_unchanged hU (by simp) (by simp) hc, graphAt_of_unchanged hU (by simp)
      (by simp) hg, ?_, hU.cap⟩
    rw [hvc]; exact hK.of_unchanged hU hKw hKl hKf
  let I : State ℝ≥0 → Prop := fun r => ∃ p, r.w "sp.p" = p ∧ p0 ≤ p ∧ p ≤ pe ∧
    (r.w "sp.go" = 0 ∨ r.w "sp.go" = 1) ∧
    (∀ j (hj : j < G.m), p0 ≤ j → j < p → ext (d u) ⟨j, hj⟩ < B) ∧
    (r.w "sp.go" = 0 → (p = pe ∨ ∃ hp : p < G.m, ¬ ext (d u) ⟨p, hp⟩ < B)) ∧
    Unchanged st r [] [] ptrW [X0.l] ∧ st.cost ≤ r.cost ∧
    r.cost ≤ st.cost + (p - p0) * 25 + (if r.w "sp.go" = 0 then 25 else 0)
  let μ : State ℝ≥0 → ℕ := fun r => 2 * (pe - r.w "sp.p") + r.w "sp.go"
  refine runs_while_var I μ _ (fun r hI => ?_) st ⟨p0, hp0, le_rfl, hrange.2.1, Or.inr hgo,
    fun j _ h1 h2 => absurd h2 (by omega), fun h => by rw [hgo] at h; exact absurd h one_ne_zero,
    Unchanged.refl _ _ _ _ _, le_rfl, by rw [hgo]; simp⟩
  obtain ⟨p, hp, hp0p, hppe, hgo', hwin, hstop, hU, hclo, hchi⟩ := hI
  have hpe' : r.w "sp.pe" = pe := by rw [hU.wreg "sp.pe" (by decide)]; exact hpe
  have hru' : r.w "ru" = u := by rw [hU.wreg "ru" (by decide)]; exact hru
  have hcap' : r.cap = st.cap := hU.cap
  refine ⟨r.w "sp.go", by simp, fun hne => ?_, fun hz => ?_⟩
  · have hg1 : r.w "sp.go" = 1 := by rcases hgo' with h | h; exact absurd h hne; exact h
    rw [hg1] at hchi
    simp only [if_neg one_ne_zero, add_zero] at hchi
    have h1c : 1 < r.cap := by omega
    apply runs_seq
    by_cases hpl : p < pe
    · have hpm : p < G.m := lt_of_lt_of_le hpl hpeM
      set e : Fin G.m := ⟨p, hpm⟩ with he
      have hsrc : G.src e = u := (hcsr.src e u).mpr
        ⟨le_trans hrange.1 hp0p, lt_of_lt_of_eq hpl hrange.2.2⟩
      have hmulB : (p - p0 + 1) * 25 ≤ (pe - p0 + 1) * 25 := Nat.mul_le_mul_right _ (by omega)
      have hlt1 : evalW (r.charge 1) (lt (var "sp.p") (var "sp.pe")) = some 1 := by
        rw [evalW_lt_of (s := r.charge 1) (x := p) (y := pe)
          (by rw [evalW_var]; exact congrArg some hp)
          (by rw [evalW_var]; exact congrArg some hpe') h1c, if_pos hpl]
      apply runs_ite_true hlt1 one_ne_zero
      apply runs_seq
      refine runs_wset_val (a := p) (by rw [evalW_var]; exact congrArg some hp)
        (fun r3 hre3 hU3 hc3 => ?_)
      have hU13 : Unchanged r r3 [] [] ["re"] [] :=
        (unch_charge_left 1).mp ((unch_charge_left 1).mp hU3)
      have hc3' : r3.cost = r.cost + 3 := by rw [hc3]; rfl
      have hUs3 : Unchanged st r3 [] [] ptrW [X0.l] :=
        hU.trans (hU13.mono (by simp) (by simp) (by decide) (by simp))
      obtain ⟨hL3, hg3, hK3, hcap3⟩ := hS r3 hUs3 (by omega)
      have hru3 : r3.w "ru" = G.src e := by rw [hU13.wreg "ru" (by decide), hru', hsrc]
      refine (candB_spec r3 d H c0 hL3 hg3 e hru3 hre3 (by rw [hsrc]; exact hfin) Kb kbf "sp.lt"
        hy.kb (by decide) B hK3 (by rw [hcap3]; omega) (by rw [hcap3]; exact hm)).mono ?_
      rintro r4 ⟨-, -, -, -, hlt4, hU4, hc4a, hc4b⟩
      rw [hsrc] at hlt4
      have hUs4 : Unchanged st r4 [] [] ptrW [X0.l] :=
        hUs3.trans (hU4.mono (by simp) (by simp) (by decide) (by simp))
      have hp4 : r4.w "sp.p" = p := by
        rw [hU4.wreg "sp.p" (by decide), hU13.wreg "sp.p" (by decide)]; exact hp
      by_cases hc : ext (d u) e < B
      · rw [if_pos hc] at hlt4
        apply runs_ite_true (x := 1) (by rw [evalW_var, hlt4]) one_ne_zero
        apply runs_seq
        apply runs_skip
        refine runs_wset_val (evalW_add_of (x := p) (y := 1)
          (by rw [evalW_var]; exact congrArg some hp4)
          (evalW_lit_of (by show 1 < r4.cap; rw [hU4.cap, hcap3]; omega))
          (by show p + 1 < r4.cap; rw [hU4.cap, hcap3]; omega)) (fun r7 hp7 hU67 hc7 => ?_)
        have hU47 : Unchanged r4 r7 [] [] ["sp.p"] [] :=
          (unch_charge_left 1).mp ((unch_charge_left 1).mp hU67)
        have hgo7 : r7.w "sp.go" = 1 := by
          rw [hU47.wreg "sp.go" (by decide), hU4.wreg "sp.go" (by decide),
            hU13.wreg "sp.go" (by decide)]; exact hg1
        have hc7' : r7.cost = r4.cost + 3 := by rw [hc7]; rfl
        refine ⟨⟨p + 1, hp7, by omega, by omega, Or.inr hgo7, ?_,
          fun h => absurd (h.symm.trans hgo7) zero_ne_one,
          hUs4.trans (hU47.mono (by simp) (by simp) (by decide) (by simp)), by omega, ?_⟩, ?_⟩
        · intro j hj h1 h2
          rcases Nat.lt_or_ge j p with h3 | h3
          · exact hwin j hj h1 h3
          · have hjp : (⟨j, hj⟩ : Fin G.m) = e := Fin.ext (by show j = p; omega)
            rw [hjp]; exact hc
        · rw [hgo7, if_neg one_ne_zero, add_zero]
          have : (p + 1 - p0) * 25 = (p - p0) * 25 + 25 := by
            rw [show p + 1 - p0 = p - p0 + 1 by omega]; ring
          omega
        · show 2 * (pe - r7.w "sp.p") + r7.w "sp.go" < 2 * (pe - r.w "sp.p") + r.w "sp.go"
          rw [hp7, hgo7, hp, hg1]; omega
      · rw [if_neg hc] at hlt4
        apply runs_ite_false (by rw [evalW_var, hlt4])
        refine runs_wset_val (evalW_lit_of (by show 0 < r4.cap; rw [hU4.cap, hcap3]; omega))
          (fun r7 hgo7 hU47 hc7 => ?_)
        have hU47' : Unchanged r4 r7 [] [] ["sp.go"] [] := (unch_charge_left 1).mp hU47
        have hc7' : r7.cost = r4.cost + 2 := by rw [hc7]; rfl
        have hp7 : r7.w "sp.p" = p := by rw [hU47'.wreg "sp.p" (by decide)]; exact hp4
        refine ⟨⟨p, hp7, hp0p, hppe, Or.inl hgo7, hwin, fun _ => Or.inr ⟨hpm, hc⟩,
          hUs4.trans (hU47'.mono (by simp) (by simp) (by decide) (by simp)), by omega, ?_⟩, ?_⟩
        · rw [hgo7, if_pos rfl]; omega
        · show 2 * (pe - r7.w "sp.p") + r7.w "sp.go" < 2 * (pe - r.w "sp.p") + r.w "sp.go"
          rw [hp7, hgo7, hp, hg1]; omega
    · have hpe_eq : p = pe := by omega
      have hlt0 : evalW (r.charge 1) (lt (var "sp.p") (var "sp.pe")) = some 0 := by
        rw [evalW_lt_of (s := r.charge 1) (x := p) (y := pe)
          (by rw [evalW_var]; exact congrArg some hp)
          (by rw [evalW_var]; exact congrArg some hpe') h1c, if_neg hpl]
      apply runs_ite_false hlt0
      refine runs_wset_val (evalW_lit_of (by show 0 < r.cap; omega)) (fun r3 hlt3 hU3 hc3 => ?_)
      have hU13 : Unchanged r r3 [] [] ["sp.lt"] [] :=
        (unch_charge_left 1).mp ((unch_charge_left 1).mp hU3)
      apply runs_ite_false (by rw [evalW_var, hlt3])
      refine runs_wset_val (evalW_lit_of (by show 0 < r3.cap; rw [hU13.cap]; omega))
        (fun r4 hgo4 hU4 hc4 => ?_)
      have hU34 : Unchanged r3 r4 [] [] ["sp.go"] [] := (unch_charge_left 1).mp hU4
      have hp4 : r4.w "sp.p" = p := by
        rw [hU34.wreg "sp.p" (by decide), hU13.wreg "sp.p" (by decide)]; exact hp
      have hc4' : r4.cost = r.cost + 5 := by rw [hc4]; show r3.cost + 1 + 1 = _; rw [hc3]; rfl
      refine ⟨⟨p, hp4, hp0p, hppe, Or.inl hgo4, hwin, fun _ => Or.inl hpe_eq,
        hU.trans ((hU13.mono (by simp) (by simp) (by decide) (by simp)).trans
          (hU34.mono (by simp) (by simp) (by decide) (by simp))), by omega, ?_⟩, ?_⟩
      · rw [hgo4, if_pos rfl]; omega
      · show 2 * (pe - r4.w "sp.p") + r4.w "sp.go" < 2 * (pe - r.w "sp.p") + r.w "sp.go"
        rw [hp4, hgo4, hp, hg1]; omega
  · have hcost : r.cost ≤ st.cost + (p - p0) * 25 + 25 := by
      rw [hz, if_pos rfl] at hchi; exact hchi
    refine ⟨p, hp0p, hppe, hp, hwin, fun hq => ?_, (unch_charge 1).mpr hU,
      by show st.cost ≤ r.cost + 1; omega, by show r.cost + 1 ≤ _; omega⟩
    rcases hstop hz with h | h
    · omega
    · exact h

open Classical in
/-- **`ptr[u]` from the range head** (for the base case): afterwards `PtrAt r (d u) u B`. -/
theorem ptrSet_spec {c0 : ℕ} {Kb : LReg} {kbf : String} (hy : PtrHyg Kb kbf)
    (st : State ℝ≥0) (d : Labels G s) (H : Fin G.n → ℕ → List (Fin G.m))
    (hL : LabAt st d H c0) (hg : GraphAt st G) (hcsr : CSRAt st G) (B : WLab G s)
    (hK : WHolds st Kb kbf H (vc st) B) (u : Fin G.n) (hfin : d u ≠ ⊤) (hru : st.w "ru" = u)
    (hptrl : G.n ≤ st.wlen "sp.ptr") (hncap : G.n + 2 ≤ st.cap) (hm : G.m + 2 ≤ st.cap)
    (hB : st.cost + (st.wa "gSt" ((u : ℕ) + 1) - st.wa "gSt" u + 1) * 25 + 40 ≤ c0 + st.cap) :
    Runs realOps (ptrSet Kb kbf) st (fun r => PtrAt r (d u) u B ∧
      (∀ w : ℕ, w ≠ u → r.wa "sp.ptr" w = st.wa "sp.ptr" w) ∧
      r.wlen "sp.ptr" = st.wlen "sp.ptr" ∧ LabAt r d H c0 ∧
      Unchanged st r ["sp.ptr"] [] (ptrW ++ ["sp.pe"]) [X0.l] ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + (st.wa "gSt" ((u : ℕ) + 1) - st.wa "gSt" u) * 25 + 30) := by
  have hu := u.isLt
  have hle := hcsr.le u
  have hlen := hcsr.len
  have h1c : 1 < st.cap := by omega
  -- `sp.p := gSt[ru]`
  apply runs_seq
  refine runs_wset_val (evalW_load_of (j := (u : ℕ)) (by rw [evalW_var]; exact congrArg some hru)
    (by omega)) (fun r1 hp1 hU1 hc1 => ?_)
  -- `sp.pe := gSt[ru + 1]`
  have hru1 : r1.w "ru" = u := by rw [hU1.wreg "ru" (by decide)]; exact hru
  have hg1 := hU1.warr "gSt" (by simp)
  apply runs_seq
  refine runs_wset_val (evalW_load_of (evalW_add_of (x := (u : ℕ)) (y := 1)
    (by rw [evalW_var]; exact congrArg some hru1) (evalW_lit_of (by rw [hU1.cap]; omega))
    (by rw [hU1.cap]; omega)) (by rw [hg1.2]; omega)) (fun r2 hpe2 hU2 hc2 => ?_)
  -- `sp.go := 1`
  apply runs_seq
  refine runs_wset_val (evalW_lit_of (by rw [hU2.cap, hU1.cap]; omega))
    (fun r3 hgo3 hU3 hc3 => ?_)
  have hU03 : Unchanged st r3 [] [] ["sp.p", "sp.pe", "sp.go"] [] :=
    ((hU1.mono (by simp) (by simp) (by simp) (by simp)).trans
      (hU2.mono (by simp) (by simp) (by simp) (by simp))).trans
      (hU3.mono (by simp) (by simp) (by simp) (by simp))
  have hvc3 : vc (G := G) r3 = vc st := vc_of_unchanged hU03 (by simp)
  have hKw : ∀ a ∈ Kb.ws, a ∉ ["sp.p", "sp.pe", "sp.go"] := fun a ha h =>
    hy.w a (by simp [ha]) (by
      simp only [ptrW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)
  have hKf : kbf ∉ ["sp.p", "sp.pe", "sp.go"] := fun h =>
    hy.w kbf (by simp) (by
      simp only [ptrW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)
  have hL3 : LabAt r3 d H c0 := hL.of_unchanged hU03 (by simp) (by simp) (by omega)
  have hK3 : WHolds r3 Kb kbf H (vc r3) B := by
    rw [hvc3]; exact hK.of_unchanged hU03 hKw (by simp) hKf
  have hg3 := Unchanged.warr hU03 "gSt" (by simp)
  have hcap3 : r3.cap = st.cap := hU03.cap
  have hp3 : r3.w "sp.p" = st.wa "gSt" u := by
    rw [hU3.wreg "sp.p" (by decide), hU2.wreg "sp.p" (by decide), hp1]
  have hpe3 : r3.w "sp.pe" = st.wa "gSt" ((u : ℕ) + 1) := by
    rw [hU3.wreg "sp.pe" (by decide), hpe2, hg1.1]
  have hru3 : r3.w "ru" = u := by
    rw [hU3.wreg "ru" (by decide), hU2.wreg "ru" (by decide)]; exact hru1
  -- the pointer advance from the head
  apply runs_seq
  refine (ptrInner_spec hy r3 d H hL3 (graphAt_of_unchanged hU03 (by simp) (by simp) hg)
    (CSRAt.of_unchanged hcsr hU03 (by simp)) B hK3 u hfin (st.wa "gSt" u)
    (st.wa "gSt" ((u : ℕ) + 1)) hp3 hpe3 hgo3 hru3 ⟨by rw [hg3.1], hle, by rw [hg3.1]⟩
    (by rw [hcap3]; omega) (by rw [hcap3]; exact hm)).mono ?_
  rintro r4 ⟨q, hq0, hqe, hp4, hwin4, hstop4, hU4, hc4lo, hc4hi⟩
  have hru4 : r4.w "ru" = u := by rw [hU4.wreg "ru" (by decide)]; exact hru3
  have hptr4 := hU4.warr "sp.ptr" (by simp)
  have hptr3 := Unchanged.warr hU03 "sp.ptr" (by simp)
  -- `sp.ptr[ru] := sp.p`
  refine runs_wstore_val (j := (u : ℕ)) (a := q) (by rw [evalW_var]; exact congrArg some hru4)
    (by rw [evalW_var]; exact congrArg some hp4) (by rw [hptr4.2, hptr3.2]; omega)
    (fun r5 hst5 hU5 hwl5 hc5 => ?_)
  have hg5 : r5.wa "gSt" = st.wa "gSt" := by
    rw [(hU5.warr "gSt" (by simp)).1, (hU4.warr "gSt" (by simp)).1, hg3.1]
  have hU05 : Unchanged st r5 ["sp.ptr"] [] (ptrW ++ ["sp.pe"]) [X0.l] :=
    ((hU03.mono (by decide) (by decide) (by decide) (by decide)).trans
      (hU4.mono (by decide) (by decide) (by decide) (by decide))).trans
      (hU5.mono (by decide) (by decide) (by decide) (by decide))
  refine ⟨?_, fun w hw => ?_, by rw [hwl5, hptr4.2, hptr3.2], ?_, hU05, by omega, by omega⟩
  · unfold PtrAt ScanStop
    rw [hg5, hst5, if_pos rfl]
    refine ⟨hq0, hqe, fun j hj h1 h2 => hwin4 j hj h1 h2, fun hq hqlt => ?_⟩
    obtain ⟨hq', h⟩ := hstop4 hqlt
    exact h
  · rw [hst5, if_neg hw, hptr4.1, hptr3.1]
  · exact hL3.of_unchanged (hU4.comp hU5) (by decide) (by simp) (by omega)

end Frontier.CHD.WinScan
