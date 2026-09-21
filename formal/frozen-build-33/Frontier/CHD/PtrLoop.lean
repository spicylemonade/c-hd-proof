import Frontier.CHD.PtrScan
import Frontier.CHD.SpineLoop

/-!
# Frontier.CHD.PtrLoop — the base case's pointer pass over the returned vertices (owner agent-03)

**NON-GATE** (B-L4, Layer B).  After the heap base case, every returned vertex `u` (the level-0 `U` row) gets
`sp.ptr[u] :=` the first slot of its sorted CSR range whose candidate is not below the call bound `B` (slot `B[0]`,
loaded into the base block `KB`), by agent-02's `ptrSet`.  `ptrLoop_spec`: afterwards `PtrAt r (d u) u B` (= the
spine's `PtrOK`) for every returned `u`, all other pointers untouched, labels untouched, cost
`9 + Σ_{u ∈ U} (25 · deg u + 33)`.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamSpine

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamLevel Frontier.CHD.BM
  Frontier.CHD.RamBaseCase Frontier.CHD.LabTab Frontier.CHD.WinScan WExpr Stmt

variable {G : Graph} {s : Fin G.n}

theorem GraphAt.of_unch {st r : State ℝ≥0} {wa va wr vr : List String} (h : GraphAt st G)
    (hu : Unchanged st r wa va wr vr) (hw : "gHead" ∉ wa) (hv : "gW" ∉ va) : GraphAt r G := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := h
  have e1 := hu.warr "gHead" hw
  have e2 := hu.varr "gW" hv
  exact ⟨⟨by rw [e1.2]; exact h1, fun i hi => by rw [e1.1]; exact h2 i hi⟩,
    ⟨by rw [e2.2]; exact h3, fun i hi => by rw [e2.1]; exact h4 i hi⟩⟩

/-- `PtrAt` only reads `gSt` and the pointer of `u`. -/
theorem PtrAt.of_eq {st r : State ℝ≥0} {du : WLab G s} {u : Fin G.n} {B : WLab G s} (h : PtrAt st du u B)
    (hg : r.wa "gSt" = st.wa "gSt") (hp : r.wa "sp.ptr" u = st.wa "sp.ptr" u) : PtrAt r du u B := by
  unfold PtrAt ScanStop at *
  rw [hg, hp]; exact h

/-- The registers written by the pointer pass. -/
def ptrLoopWR : List String := ["sl.i", "sp.i", "ru"] ++ ("bc.bf" :: KB.ws) ++ ptrW ++ ["sp.pe"]

/-- (Base case) Pointers of the returned vertices of level 0, for the bound in slot `B[0]`. -/
def ptrLoop : Stmt :=
  seq (wset "sl.i" (lit (slotB 0)))
  (seq (loadSlot KB "bc.bf")
  (seq (wset "sp.i" (lit 0))
  (.while (lt (var "sp.i") (load "U.len" (lit 0)))
    (seq (wset "ru" (load "U" (var "sp.i")))
    (seq (ptrSet KB "bc.bf") (wset "sp.i" (add (var "sp.i") (lit 1))))))))

theorem ptrHyg_KB : PtrHyg KB "bc.bf" := ⟨boundRegs_KB, by decide⟩

theorem slotFresh_KB : SlotFresh KB "bc.bf" := ⟨by decide⟩

/-- The per-vertex cost of the pass. -/
def ptrCostOf (st : State ℝ≥0) (x : ℕ) : ℕ := 25 * (st.wa "gSt" (x + 1) - st.wa "gSt" x) + 33

/-- **The base case's pointer pass.** -/
theorem ptrLoop_spec {c0 : ℕ} (st : State ℝ≥0) (d : Labels G s) (H : Hist G) (B : WLab G s)
    {xs : List ℕ} (hrow : RowRep st "U" "U.len" G.n 0 xs) (hxs : xs.Nodup) (hxN : ∀ x ∈ xs, x < G.n)
    (hfin : ∀ x (hx : x ∈ xs), d ⟨x, hxN x hx⟩ ≠ ⊤)
    (hL : LabAt st d H c0) (hg : GraphAt st G) (hcsr : CSRAt st G)
    (hB : SlotHolds st (slotB 0) H (vc st) B) (hsl : SlotLens st (slotB 0))
    (hptrl : G.n ≤ st.wlen "sp.ptr") (hncap : G.n + 2 ≤ st.cap) (hm : G.m + 2 ≤ st.cap)
    (hbud : st.cost + 8 + (xs.map (ptrCostOf st)).sum + 65 ≤ c0 + st.cap) :
    Runs realOps ptrLoop st (fun r => (∀ x (hx : x ∈ xs), PtrAt r (d ⟨x, hxN x hx⟩) ⟨x, hxN x hx⟩ B) ∧
      (∀ w : ℕ, w ∉ xs → r.wa "sp.ptr" w = st.wa "sp.ptr" w) ∧ LabAt r d H c0 ∧
      Unchanged st r ["sp.ptr"] [] ptrLoopWR [KB.l, X0.l] ∧ r.wlen = st.wlen ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + 9 + (xs.map (ptrCostOf st)).sum) := by
  classical
  obtain ⟨hlen, hUl, hULl, hUL, hUx⟩ := hrow
  have hcap1 : 1 < st.cap := by omega
  have hslc : slotB 0 < st.cap := by simp [slotB]; omega
  -- `sl.i := slotB 0 ; KB := slot B[0] ; sp.i := 0`
  refine runs_seq (runs_wset (a := slotB 0) (evalW_lit_of hslc) ?_)
  set s1 := (st.setW "sl.i" (slotB 0)).charge 1 with hs1
  have hU1 : Unchanged st s1 [] [] ["sl.i"] [] := by
    rw [hs1, Frontier.RAM.unch_charge, Frontier.RAM.unch_setW (by simp)]; exact Unchanged.refl _ _ _ _ _
  refine runs_seq ((loadSlot_spec KB "bc.bf" slotFresh_KB s1 (by simp [hs1])
    (SlotLens.of_unchanged hsl hU1 (by simp) (by simp)) (hB.of_unchanged hU1 (by simp) (by simp))).mono ?_)
  rintro s2 ⟨hK2, hU2, hc2⟩
  have hU02 : Unchanged st s2 [] [] (["sl.i"] ++ ("bc.bf" :: KB.ws)) ([] ++ [KB.l]) := hU1.comp hU2
  have hvc2 : vc (G := G) s2 = vc st := vc_of_unchanged hU02 (by simp)
  have hcap2 : s2.cap = st.cap := hU02.cap
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by rw [hcap2]; omega)) ?_)
  set s3 := (s2.setW "sp.i" 0).charge 1 with hs3
  have hc3 : s3.cost = st.cost + 8 := by
    simp only [hs3, State.charge_cost, State.setW_cost, hc2, hs1]
  have hU23 : Unchanged s2 s3 [] [] ["sp.i"] [] := by
    rw [hs3, Frontier.RAM.unch_charge, Frontier.RAM.unch_setW (by simp)]; exact Unchanged.refl _ _ _ _ _
  have hU03 : Unchanged st s3 ["sp.ptr"] [] ptrLoopWR [KB.l, X0.l] :=
    (hU02.mono (by simp) (by simp) (by intro x hx; simp [ptrLoopWR] at hx ⊢; tauto) (by simp)).trans
      (hU23.mono (by simp) (by simp) (by simp [ptrLoopWR]) (by simp))
  have hL3 : LabAt s3 d H c0 := hL.of_unchanged hU03 (by simp [labW]) (by simp) (by omega)
  have hK3 : WHolds s3 KB "bc.bf" H (vc s3) B := by
    rw [show vc (G := G) s3 = vc st from (show vc (G := G) s3 = vc s2 from rfl).trans hvc2]
    exact hK2.of_unchanged hU23 (by decide) (by simp) (by decide)
  have hwl3 : s3.wlen = st.wlen := funext fun a => (hU02.warr a (by simp)).2
  -- the loop
  refine runs_while_nat (fun m r => ∃ j, m = xs.length - j ∧ j ≤ xs.length ∧ r.w "sp.i" = j ∧
      (∀ i (hi : i < j) (hi' : i < xs.length), PtrAt r (d ⟨xs[i], hxN _ (List.getElem_mem hi')⟩)
        ⟨xs[i], hxN _ (List.getElem_mem hi')⟩ B) ∧
      (∀ w : ℕ, w ∉ xs.take j → r.wa "sp.ptr" w = st.wa "sp.ptr" w) ∧
      LabAt r d H c0 ∧ WHolds r KB "bc.bf" H (vc r) B ∧ vc (G := G) r = vc st ∧
      Unchanged st r ["sp.ptr"] [] ptrLoopWR [KB.l, X0.l] ∧ r.wlen = st.wlen ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + 8 + ((xs.take j).map (ptrCostOf st)).sum) _ ?_ xs.length s3 ?_
  swap
  · refine ⟨0, by simp, by omega, by simp [hs3], fun i hi => absurd hi (by omega), fun w _ => ?_, hL3, hK3,
      by rw [show vc (G := G) s3 = vc s2 from rfl, hvc2], hU03, hwl3, by omega, by simp [hc3]⟩
    show s3.wa "sp.ptr" w = st.wa "sp.ptr" w
    rw [show s3.wa = s2.wa from rfl, (hU02.warr "sp.ptr" (by simp)).1]
  rintro m r ⟨j, rfl, hjL, hjr, hptr, hfr, hLr, hKr, hvcr, hUr, hwlr, hc1, hc2⟩
  have hcapr : r.cap = st.cap := hUr.cap
  have hUlenr : r.wa "U.len" 0 = xs.length := by
    rw [(hUr.warr "U.len" (by simp)).1]; exact hUL
  have hULlr : 0 < r.wlen "U.len" := by rw [hwlr]; exact hULl
  have eT : evalW r (lt (var "sp.i") (load "U.len" (lit 0))) = some (if j < xs.length then 1 else 0) := by
    have e1 : evalW r (load "U.len" (lit 0)) = some xs.length := by
      simp [fit_of_lt (show 0 < r.cap by omega), hULlr, hUlenr]
    simp only [evalW_lt', evalW_var, hjr, e1, Option.bind_some]
    split_ifs <;> simp [fit_of_lt (show 1 < r.cap by rw [hcapr]; omega), fit_of_lt (show 0 < r.cap by omega)]
  refine ⟨if j < xs.length then 1 else 0, eT, fun hx => ?_, fun hx => ?_⟩
  · have hj : j < xs.length := by by_contra hc; rw [if_neg hc] at hx; exact hx rfl
    have hxj : xs[j] < G.n := hxN _ (List.getElem_mem hj)
    -- `ru := U[sp.i]`
    have eR : evalW (r.charge 1) (load "U" (var "sp.i")) = some xs[j] := by
      have hUj := hUx j hj
      simp only [Nat.zero_mul, Nat.zero_add] at hUj
      have hjU : j < r.wlen "U" := by rw [hwlr]; simp at hUl; omega
      simp [hjr, hjU, (hUr.warr "U" (by simp)).1, hUj]
    refine runs_seq (runs_wset eR ?_)
    set r2 := ((r.charge 1).setW "ru" xs[j]).charge 1 with hr2
    have hU12 : Unchanged r r2 [] [] ["ru"] [] := by
      rw [hr2, Frontier.RAM.unch_charge, Frontier.RAM.unch_setW (by simp), Frontier.RAM.unch_charge]
      exact Unchanged.refl _ _ _ _ _
    have hvc2' : vc (G := G) r2 = vc r := rfl
    have hc2' : r2.cost = r.cost + 2 := by simp [hr2]
    have hL2 : LabAt r2 d H c0 := hLr.of_unchanged hU12 (by simp) (by simp) (by omega)
    have hK2' : WHolds r2 KB "bc.bf" H (vc r2) B := by
      rw [hvc2']; exact hKr.of_unchanged hU12 (by decide) (by simp) (by decide)
    have hUsr2 : Unchanged st r2 ["sp.ptr"] [] ptrLoopWR [KB.l, X0.l] :=
      hUr.trans (hU12.mono (by simp) (by simp) (by simp [ptrLoopWR]) (by simp))
    have hg2 : GraphAt r2 G := GraphAt.of_unch hg hUsr2 (by simp) (by simp)
    have hcsr2 : CSRAt r2 G := hcsr.of_unchanged hUsr2 (by simp)
    have hgSt2 : r2.wa "gSt" = st.wa "gSt" := (hUsr2.warr "gSt" (by simp)).1
    have hwl2 : r2.wlen = st.wlen := by rw [← hwlr]; rfl
    have htk : xs.take (j + 1) = xs.take j ++ [xs[j]] := by
      rw [List.take_succ, List.getElem?_eq_getElem hj]; simp
    have hsum_le : ((xs.take j).map (ptrCostOf st)).sum + ptrCostOf st xs[j] ≤ (xs.map (ptrCostOf st)).sum := by
      have e2 : ((xs.take (j + 1)).map (ptrCostOf st)).sum ≤ (xs.map (ptrCostOf st)).sum := by
        conv_rhs => rw [← List.take_append_drop (j + 1) xs]
        rw [List.map_append, List.sum_append]; omega
      rw [htk, List.map_append, List.sum_append] at e2
      simpa using e2
    have hpc : ptrCostOf st xs[j] = 25 * (st.wa "gSt" (xs[j] + 1) - st.wa "gSt" xs[j]) + 33 := rfl
    have hbud2 : r2.cost + (r2.wa "gSt" ((⟨xs[j], hxj⟩ : Fin G.n) + 1) - r2.wa "gSt" (⟨xs[j], hxj⟩ : Fin G.n) + 1) * 25
        + 40 ≤ c0 + r2.cap := by
      rw [hgSt2, show r2.cap = st.cap by simp [hr2, hcapr], hc2']
      simp only [Fin.val_mk]
      omega
    refine runs_seq ((ptrSet_spec ptrHyg_KB r2 d H hL2 hg2 hcsr2 B hK2' ⟨xs[j], hxj⟩
      (hfin _ (List.getElem_mem hj)) (by simp [hr2]) (by rw [hwl2]; exact hptrl)
      (by simp [hr2, hcapr]; omega) (by simp [hr2, hcapr]; omega) hbud2).mono ?_)
    rintro r3 ⟨hP3, hfr3, hwl3', hL3', hU3, hc3a, hc3b⟩
    have hj3 : r3.w "sp.i" = j := by
      rw [hU3.wreg "sp.i" (by decide)]; simp [hr2, hjr]
    have hcap3 : r3.cap = st.cap := by rw [hU3.cap]; simp [hr2, hcapr]
    have e5 : evalW r3 (add (var "sp.i") (lit 1)) = some (j + 1) := by
      simp [hj3, hcap3, fit_of_lt (show j + 1 < st.cap by omega), fit_of_lt (show 1 < st.cap by omega)]
    refine runs_wset e5 ?_
    set r4 := (r3.setW "sp.i" (j + 1)).charge 1 with hr4
    have hU34 : Unchanged r3 r4 [] [] ["sp.i"] [] := by
      rw [hr4, Frontier.RAM.unch_charge, Frontier.RAM.unch_setW (by simp)]; exact Unchanged.refl _ _ _ _ _
    have hU24 : Unchanged r2 r4 ["sp.ptr"] [] ptrLoopWR [KB.l, X0.l] :=
      (hU3.mono (by simp) (by simp) (by intro x hx; simp [ptrLoopWR] at hx ⊢; tauto) (by simp)).trans
        (hU34.mono (by simp) (by simp) (by simp [ptrLoopWR]) (by simp))
    have hgSt4 : r4.wa "gSt" = r.wa "gSt" := (hU24.warr "gSt" (by simp)).1
    have hvc4 : vc (G := G) r4 = vc st := by
      rw [vc_of_unchanged hU24 (by simp), hvc2', hvcr]
    refine ⟨xs.length - (j + 1), by omega, j + 1, rfl, by omega, by simp [hr4], ?_, ?_, ?_, ?_, hvc4,
      hUsr2.trans hU24, ?_, ?_, ?_⟩
    · intro i hi hi'
      by_cases hij : i = j
      · subst hij
        exact PtrAt.of_eq hP3 rfl rfl
      · have hi2 : i < j := by omega
        refine PtrAt.of_eq (hptr i hi2 hi') hgSt4 ?_
        have hne : xs[i] ≠ xs[j] := fun h => hij ((List.Nodup.getElem_inj_iff hxs).mp h)
        simp only [hr4, State.charge_wa, State.setW_wa, Fin.val_mk]
        rw [hfr3 _ hne]
        rfl
    · intro w hw
      have hw' : w ∉ xs.take j := fun h => hw (by rw [htk]; exact List.mem_append_left _ h)
      have hwj : w ≠ xs[j] := fun h => hw (by rw [htk, h]; exact List.mem_append_right _ (List.mem_singleton_self _))
      simp only [hr4, State.charge_wa, State.setW_wa]
      rw [hfr3 w hwj]
      exact hfr w hw'
    · exact hL3'.of_unchanged hU34 (by simp) (by simp) (by simp [hr4])
    · have e : vc (G := G) r4 = vc r2 := by rw [vc_of_unchanged hU24 (by simp)]
      rw [e]
      have h3 : WHolds r3 KB "bc.bf" H (vc r2) B := hK2'.of_unchanged hU3 (by decide) (by decide) (by decide)
      exact h3.of_unchanged hU34 (by decide) (by simp) (by decide)
    · have e3 : r3.wlen = r2.wlen := funext fun a => by
        by_cases ha : a = "sp.ptr"
        · subst ha; exact hwl3'
        · exact (hU3.warr a (by simp [ha])).2
      rw [← hwl2, ← e3]; rfl
    · simp [hr4]; omega
    · rw [htk, List.map_append, List.sum_append]
      simp only [hr4, State.charge_cost, State.setW_cost, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      rw [hgSt2] at hc3b
      simp only [Fin.val_mk] at hc3b
      omega
  · have hj : j = xs.length := by by_contra hc; rw [if_pos (by omega)] at hx; exact one_ne_zero hx
    subst hj
    refine ⟨fun x hx => ?_, fun w hw => ?_, hLr.of_unchanged (Unchanged.charge r 1 [] [] [] []) (by simp) (by simp)
      (by simp), by rw [Frontier.RAM.unch_charge]; exact hUr, by simp [hwlr], by simp; omega, ?_⟩
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      exact PtrAt.of_eq (hptr i hi hi) rfl rfl
    · have := hfr w (by rw [List.take_length]; exact hw)
      simpa using this
    · rw [List.take_length] at hc2
      simp; omega

end Frontier.CHD.RamSpine
