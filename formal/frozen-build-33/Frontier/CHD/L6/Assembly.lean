import Frontier.CHD.L6.LevelRoute
import Frontier.CHD.L6.DCap
import Frontier.CHD.BaseCall0

/-!
# The final assembly with the base case discharged (agent-10)

The concrete cost parameters of the C-HD run:
* `SbF cn cm l = 3 k · M_{l+1}`: the frontier-size bound of a level-`l` call (agent-03's
  `expand_card_le`: a sub-call of a level-`(l+1)` call has `|S| ≤ 3k · M_{l+1}`);
* `KhF cn cm = SbF 0 + 5 dd · τ_0`: the base-case heap size bound, so that one heap operation costs
  `copF KhF = O(log t + log dd)`;
* `chdP cn cm = ⟨1, k, chdDC cn cm⟩`: FindPivots' charges `hins = 1`, `hext = k`, and the base
  heap costs `bins = 2 copF KhF + 76`, `bext = copF KhF + 7` (exactly agent-03's `callSpec_zero`
  requirements).
`goodP_chdP`: these parameters are in agent-06's master class `GoodP chdP 1 1 1000`.

`chdTarget_of_step`: the frozen Gate-C target from
* the D layer (instance `DLf`, uniform constant `KD`, closed texts `newS`/`insS`, the D hook `hD`);
* the level step `hs` (agent-01's level body);
* the decidable side conditions.
The base case `h0` is discharged here from `callSpec_zero` (with the `rfl` bridge
`baseProg_closed`), GoodP from `goodP_chdP`, `hps` by `rfl`, `hSb` by arithmetic.
NON-GATE (composition).
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.LabTab WExpr Stmt

/-! ## The base case, discharged from agent-03's `callSpec_zero` -/

theorem baseBud_le {H : Graph} {src : Fin H.n} {cn cm : ℕ} (hMI : MasterIn H src cn cm) :
    RamBaseCase.baseBud (IHeapLab.heapI H src (KhF cn cm)) H (SbF cn cm 0)
      (BM.chdTau (CostSkeleton.tF cn cm) 0) + 112 ≤ baseReq cn cm := by
  have hm := hMI.sizeM
  show (SbF cn cm 0 + 1) * (copF (KhF cn cm) + 3) +
      (BM.chdTau (CostSkeleton.tF cn cm) 0 + 1) *
        ((H.m + 1) * (copF (KhF cn cm) + 77) + 2 * copF (KhF cn cm) + 100) +
      copF (KhF cn cm) + 60 + 112 ≤ baseReq cn cm
  unfold baseReq
  have h1 : (H.m + 1) * (copF (KhF cn cm) + 77) ≤ (2 * cm + 1) * (copF (KhF cn cm) + 77) :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 := Nat.mul_le_mul_left (BM.chdTau (CostSkeleton.tF cn cm) 0 + 1)
    (Nat.add_le_add_right (Nat.add_le_add_right h1 (2 * copF (KhF cn cm))) 100)
  omega

/-- **The level-0 contract of the final body** (agent-03's `callSpec_zero`, with the closed
text `baseProgC newS insS` by the `rfl` bridge `baseProg_closed`). -/
theorem callSpec_base (newS insS recC : Stmt)
    {DLf : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), RamSpine.DLayer H src Tz}
    (hnew : ∀ H src cn cm, (DLf H src cn cm).new = newS)
    (hinsS : ∀ H src cn cm, (DLf H src cn cm).ins = insS)
    {KD K : ℕ} (hKD : ∀ H src cn cm, (DLf H src cn cm).K ≤ KD) (hK : 2 * KD + 82 ≤ K)
    (hDW : ∀ H src cn cm, ∀ a ∈ RamBaseCase.baseWR (IHeapLab.heapI H src (KhF cn cm)) ++
      RamSpine.ptrLoopWR, a ∉ (DLf H src cn cm).dWR)
    (hPW : ∀ H src cn cm, ∀ a ∈ (PIfOf chdP H src cn cm).pWR,
      a ∉ RamBaseCase.baseWR (IHeapLab.heapI H src (KhF cn cm)) ++ RamSpine.ptrLoopWR ++
        (DLf H src cn cm).dWR)
    (hPA : ∀ H src cn cm, ∀ a ∈ (PIfOf chdP H src cn cm).pWA, a ∉ (DLf H src cn cm).dWA)
    {Slf : ℕ → ℕ → ℕ} (hSl0 : ∀ cn cm, baseReq cn cm ≤ Slf cn cm)
    (H : Graph) (src : Fin H.n) (cn cm : ℕ) (hMI : MasterIn H src cn cm) :
    RamSpine.CallSpec (DLf H src cn cm) (PIfOf chdP H src cn cm).PhiR (DelInv H src)
      (fpC H src (outL H) (CostSkeleton.kF cn cm) (chdP cn cm).hins (chdP cn cm).hext)
      (chdP cn cm).DCb (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm))
      (CostSkeleton.LF cn cm) (RamSpine.bmsspProc (RamSpine.baseProgC newS insS) recC) K
      (Slf cn cm) (SbF cn cm) 0 := by
  have h := RamSpine.callSpec_zero (DLf H src cn cm) (PIfOf chdP H src cn cm) (Inv := DelInv H src)
    (FPC := fpC H src (outL H) (CostSkeleton.kF cn cm) (chdP cn cm).hins (chdP cn cm).hext)
    (DCb := (chdP cn cm).DCb) (Mf := BM.chdM (CostSkeleton.tF cn cm))
    (τf := BM.chdTau (CostSkeleton.tF cn cm)) (LF := CostSkeleton.LF cn cm) (rec := recC) (K := K)
    (Sl := Slf cn cm) (Kh := KhF cn cm) (δ := 5 * CostSkeleton.dd cn cm) (Sb := SbF cn cm)
    (chdM_pos _ (by have := CostSkeleton.sixteen_le_tF cn cm; omega)) rfl le_rfl le_rfl
    (outdeg_le_of_masterIn hMI) le_rfl
    (by have := baseBud_le hMI; have := hSl0 cn cm; omega)
    (by have := hKD H src cn cm; omega) (hDW H src cn cm) (hPW H src cn cm) (hPA H src cn cm)
  rw [RamSpine.baseProg_closed, hnew H src cn cm, hinsS H src cn cm] at h
  exact h

/-! ## The frozen target from the D layer and the level step -/

/-- The final body and procedure table for closed D texts `newS`/`insS` and level body `recC`. -/
abbrev chdBodyP (newS insS recC : Stmt) : Stmt := RamSpine.bmsspProc (RamSpine.baseProgC newS insS) recC
/-- The procedure table: `P_bmssp = 0` is the BMSSP procedure; `extra` holds the further
procedures the D layer calls (agent-05's recursive select `selBody entLess 1` at index 1). -/
abbrev chdPs (newS insS recC : Stmt) (extra : List Stmt) : List Stmt :=
  RamSpine.bmsspProc (RamSpine.baseProgC newS insS) recC :: extra

/-- **The C-HD target from the D layer and the level step** (everything else discharged). -/
theorem chdTarget_of_step (e : ℕ) (he : 32 ≤ e) (newS insS recC : Stmt) (extra : List Stmt)
    {DLf : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), RamSpine.DLayer H src Tz}
    (hnew : ∀ H src cn cm, (DLf H src cn cm).new = newS)
    (hinsS : ∀ H src cn cm, (DLf H src cn cm).ins = insS)
    {KD K : ℕ} (hKD : ∀ H src cn cm, (DLf H src cn cm).K ≤ KD) (hK : 2 * KD + 82 ≤ K)
    (hucapF : ∀ H src cn cm, 12 * kmN * CostSkeleton.Tnat cn cm + 2 ≤ (DLf H src cn cm).ucap)
    (hDW : ∀ H src cn cm, ∀ a ∈ RamBaseCase.baseWR (IHeapLab.heapI H src (KhF cn cm)) ++
      RamSpine.ptrLoopWR, a ∉ (DLf H src cn cm).dWR)
    (hPW : ∀ H src cn cm, ∀ a ∈ (PIfOf chdP H src cn cm).pWR,
      a ∉ RamBaseCase.baseWR (IHeapLab.heapI H src (KhF cn cm)) ++ RamSpine.ptrLoopWR ++
        (DLf H src cn cm).dWR)
    (hPA : ∀ H src cn cm, ∀ a ∈ (PIfOf chdP H src cn cm).pWA, a ∉ (DLf H src cn cm).dWA)
    {dPro : Stmt} {dwa dva dwr dvr : List String} {Kd : ℕ}
    (hD : HookSpec e (chdPs newS insS recC extra) dPro (fun H src cn cm r => (∃ Ds : ℕ → BM.DStrM H src,
        (DLf H src cn cm).DR r (H0 (G := H)) BM.DGl.init Ds (CostSkeleton.LF cn cm + 1)) ∧
        (DLf H src cn cm).use r ≤ 2)
        dwa dva dwr dvr Kd)
    (hPd : ∀ H src cn cm, (∀ a ∈ (PIfOf chdP H src cn cm).pWA, a ∉ dwa) ∧
      (∀ a ∈ (PIfOf chdP H src cn cm).pWR, a ∉ dwr))
    (hPb : ∀ H src cn cm, (∀ a ∈ (PIfOf chdP H src cn cm).pWA, a ∉ slotW ++ ["S", "S.len"]) ∧
      (∀ a ∈ (PIfOf chdP H src cn cm).pWR, a ∉ blowWR ++ ["lvl"]))
    (hfoot : SpineFoot (chdPs newS insS recC extra))
    {Kpol Dp : ℕ} {Slf : ℕ → ℕ → ℕ} (hSl0 : ∀ cn cm, baseReq cn cm ≤ Slf cn cm) (hDp : 2 ≤ Dp)
    (hSl : ∀ n m, Slf n m ≤ Kpol * (n + m + 2) ^ Dp)
    (hs : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
      ∀ l : ℕ, l < CostSkeleton.LF cn cm →
      RamSpine.CallSpec (DLf H src cn cm) (PIfOf chdP H src cn cm).PhiR (DelInv H src)
        (fpC H src (outL H) (CostSkeleton.kF cn cm) (chdP cn cm).hins (chdP cn cm).hext)
        (chdP cn cm).DCb (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm))
        (CostSkeleton.LF cn cm) (chdBodyP newS insS recC) K (Slf cn cm) (SbF cn cm) l →
      RamSpine.CallSpec (DLf H src cn cm) (PIfOf chdP H src cn cm).PhiR (DelInv H src)
        (fpC H src (outL H) (CostSkeleton.kF cn cm) (chdP cn cm).hins (chdP cn cm).hext)
        (chdP cn cm).DCb (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm))
        (CostSkeleton.LF cn cm) (chdBodyP newS insS recC) K (Slf cn cm) (SbF cn cm) (l + 1))
    (hbig : 12 + ((K : ℝ) + (13000 + 34 * ((100 : ℕ) + (Kd : ℝ))) + 0) * (kmaster 1 1 1000 + 1) +
      |(0 : ℝ)| + |(Kpol : ℝ)| ≤ (4 : ℝ) ^ (e + 1 - Dp)) :
    GateCTarget.CHDTarget GateCCalc.F :=
  chdTarget_of_levels e he (chdPs newS insS recC extra) (chdBodyP newS insS recC)
    rfl hfoot goodP_chdP hD hPd hPb hDp (fun cn cm => sbF_pos cn cm _) hSl (hucap_of hucapF)
    (fun H src cn cm hMI => callSpec_base newS insS recC hnew hinsS hKD hK hDW hPW hPA hSl0
      H src cn cm hMI) hs hbig

/-- **The named C-HD witness** for the D layer and the level step: the explicit program
`chdProg e (chdPs newS insS recC extra) (coreTop (spineOf (spinePro BL2.fpAlloc dPro)))` is exact and runs
within a constant times `Tdisp F n m`. -/
theorem chdProg_of_step (e : ℕ) (he : 32 ≤ e) (newS insS recC : Stmt) (extra : List Stmt)
    {DLf : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), RamSpine.DLayer H src Tz}
    (hnew : ∀ H src cn cm, (DLf H src cn cm).new = newS)
    (hinsS : ∀ H src cn cm, (DLf H src cn cm).ins = insS)
    {KD K : ℕ} (hKD : ∀ H src cn cm, (DLf H src cn cm).K ≤ KD) (hK : 2 * KD + 82 ≤ K)
    (hucapF : ∀ H src cn cm, 12 * kmN * CostSkeleton.Tnat cn cm + 2 ≤ (DLf H src cn cm).ucap)
    (hDW : ∀ H src cn cm, ∀ a ∈ RamBaseCase.baseWR (IHeapLab.heapI H src (KhF cn cm)) ++
      RamSpine.ptrLoopWR, a ∉ (DLf H src cn cm).dWR)
    (hPW : ∀ H src cn cm, ∀ a ∈ (PIfOf chdP H src cn cm).pWR,
      a ∉ RamBaseCase.baseWR (IHeapLab.heapI H src (KhF cn cm)) ++ RamSpine.ptrLoopWR ++
        (DLf H src cn cm).dWR)
    (hPA : ∀ H src cn cm, ∀ a ∈ (PIfOf chdP H src cn cm).pWA, a ∉ (DLf H src cn cm).dWA)
    {dPro : Stmt} {dwa dva dwr dvr : List String} {Kd : ℕ}
    (hD : HookSpec e (chdPs newS insS recC extra) dPro (fun H src cn cm r => (∃ Ds : ℕ → BM.DStrM H src,
        (DLf H src cn cm).DR r (H0 (G := H)) BM.DGl.init Ds (CostSkeleton.LF cn cm + 1)) ∧
        (DLf H src cn cm).use r ≤ 2)
        dwa dva dwr dvr Kd)
    (hPd : ∀ H src cn cm, (∀ a ∈ (PIfOf chdP H src cn cm).pWA, a ∉ dwa) ∧
      (∀ a ∈ (PIfOf chdP H src cn cm).pWR, a ∉ dwr))
    (hPb : ∀ H src cn cm, (∀ a ∈ (PIfOf chdP H src cn cm).pWA, a ∉ slotW ++ ["S", "S.len"]) ∧
      (∀ a ∈ (PIfOf chdP H src cn cm).pWR, a ∉ blowWR ++ ["lvl"]))
    (hfoot : SpineFoot (chdPs newS insS recC extra))
    {Kpol Dp : ℕ} {Slf : ℕ → ℕ → ℕ} (hSl0 : ∀ cn cm, baseReq cn cm ≤ Slf cn cm) (hDp : 2 ≤ Dp)
    (hSl : ∀ n m, Slf n m ≤ Kpol * (n + m + 2) ^ Dp)
    (hs : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
      ∀ l : ℕ, l < CostSkeleton.LF cn cm →
      RamSpine.CallSpec (DLf H src cn cm) (PIfOf chdP H src cn cm).PhiR (DelInv H src)
        (fpC H src (outL H) (CostSkeleton.kF cn cm) (chdP cn cm).hins (chdP cn cm).hext)
        (chdP cn cm).DCb (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm))
        (CostSkeleton.LF cn cm) (chdBodyP newS insS recC) K (Slf cn cm) (SbF cn cm) l →
      RamSpine.CallSpec (DLf H src cn cm) (PIfOf chdP H src cn cm).PhiR (DelInv H src)
        (fpC H src (outL H) (CostSkeleton.kF cn cm) (chdP cn cm).hins (chdP cn cm).hext)
        (chdP cn cm).DCb (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm))
        (CostSkeleton.LF cn cm) (chdBodyP newS insS recC) K (Slf cn cm) (SbF cn cm) (l + 1))
    (hbig : 12 + ((K : ℝ) + (13000 + 34 * ((100 : ℕ) + (Kd : ℝ))) + 0) * (kmaster 1 1 1000 + 1) +
      |(0 : ℝ)| + |(Kpol : ℝ)| ≤ (4 : ℝ) ^ (e + 1 - Dp)) :
    let core := coreTop (spineOf (spinePro BL2.fpAlloc dPro))
    let Kc : ℝ := ((K : ℝ) + (13000 + 34 * ((100 : ℕ) + (Kd : ℝ))) + 0) * (kmaster 1 1 1000 + 1) + 250
    (chdProg e (chdPs newS insS recC extra) core).Exact ∧ ∀ (G : Graph) (s : Fin G.n),
      (chdProg e (chdPs newS insS recC extra) core).RunsWithin G s
        ((bodyC Kc + 65536 * 9 + 100) * GateCTarget.Tdisp GateCCalc.F G.n G.m) :=
  chdProg_of_levels e he (chdPs newS insS recC extra) (chdBodyP newS insS recC)
    rfl hfoot goodP_chdP hD hPd hPb hDp (fun cn cm => sbF_pos cn cm _) hSl (hucap_of hucapF)
    (fun H src cn cm hMI => callSpec_base newS insS recC hnew hinsS hKD hK hDW hPW hPA hSl0
      H src cn cm hMI) hs hbig

end Frontier.CHD.L6


#print axioms Frontier.CHD.L6.callSpec_base
#print axioms Frontier.CHD.L6.chdTarget_of_step
#print axioms Frontier.CHD.L6.chdProg_of_step

