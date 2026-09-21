import Frontier.CHD.L6.Assembly
import Frontier.CHD.L6.StepInst
import Frontier.CHD.L6.SlackF
import Frontier.CHD.SpineLoopInst
import Frontier.CHD.BL2Step

/-!
# The final composition, generic in the D layer (agent-10)

`chdProg_of_DLayer`: the named C-HD witness program
`chdProg e (chdPs newS insS (recText fpAtRaw newS insS emptyS (iterText pullS mergeS delBS insS) finP) extra)
  (coreTop (spineOf (spinePro BL2.fpAlloc dPro)))`
is exact and runs within `C · Tdisp F n m`, for ANY D-layer family `DLf` whose operations are the
closed texts `newS insS emptyS pullS mergeS delBS`, with a uniform constant, the capacity
`12·kmN·Tnat + 2`, block bound `NB = nbF`, top level `≥ LF`, the D hook `dPro`, the finalization
`FinB`, and the decidable name facts.  The slack is `SlfC K 27` (`L6.SlackF`), polynomial of degree 8.

Everything else is discharged here: the base case (`callSpec_base`), the level step
(`hs_of_parts` with FindPivots `hFP_of` (agent-09) and the loop `hLoop_of_parts` (agent-08)),
GoodP, the slack bounds, the capacity.  NON-GATE (composition).
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamLevel Frontier.CHD.BM
  Frontier.CHD.RamBaseCase Frontier.CHD.LabTab Frontier.CHD.RamSpine Frontier.CHD.RamInit
  Frontier.CHD.RamBody WExpr Stmt

set_option maxHeartbeats 1000000 in
/-- **The named C-HD witness from a D layer.** -/
theorem chdProg_of_DLayer (e : ℕ) (he : 32 ≤ e)
    {DLf : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), RamSpine.DLayer H src Tz}
    {newS insS emptyS pullS mergeS delBS finP dPro : Stmt} (extra : List Stmt)
    -- the closed texts of the D operations
    (hnew : ∀ H src cn cm, (DLf H src cn cm).new = newS)
    (hinsS : ∀ H src cn cm, (DLf H src cn cm).ins = insS)
    (hemp : ∀ H src cn cm, (DLf H src cn cm).empty = emptyS)
    (hpull : ∀ H src cn cm, (DLf H src cn cm).pull = pullS)
    (hmerge : ∀ H src cn cm, (DLf H src cn cm).merge = mergeS)
    (hdelB : ∀ H src cn cm, (DLf H src cn cm).delB = delBS)
    -- constants and capacities
    {KD K Ko Kfin Cfin : ℕ}
    (hKD : ∀ H src cn cm, (DLf H src cn cm).K ≤ KD)
    (hK : 524 + 351 + Ko + Kfin + Cfin + 2 * KD + 60 ≤ K) (hKb : 2 * KD + 82 ≤ K)
    (hKo : ∀ H src cn cm, (DLf H src cn cm).K + 22 + 71 + postK (DLf H src cn cm).K 27 + 1 ≤ Ko)
    (hucapF : ∀ H src cn cm, 12 * kmN * CostSkeleton.Tnat cn cm + 2 ≤ (DLf H src cn cm).ucap)
    (hNB : ∀ H src cn cm, (DLf H src cn cm).NB = nbF cn cm)
    (hKK : ∀ H src cn cm, (DLf H src cn cm).K ≤ K)
    (hLT : ∀ H src cn cm, CostSkeleton.LF cn cm ≤ (DLf H src cn cm).LT)
    -- the D hook
    {dwa dva dwr dvr : List String} {Kd : ℕ}
    (hD : HookSpec e (chdPs newS insS (recText BL2Inst.fpAtRaw newS insS emptyS
        (iterText pullS mergeS delBS insS) finP) extra) dPro
        (fun H src cn cm r => (∃ Ds : ℕ → BM.DStrM H src,
          (DLf H src cn cm).DR r (H0 (G := H)) BM.DGl.init Ds (CostSkeleton.LF cn cm + 1)) ∧
          (DLf H src cn cm).use r ≤ 2)
        dwa dva dwr dvr Kd)
    -- the finalization
    (hFin : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
      ∀ l : ℕ, l < CostSkeleton.LF cn cm →
      FinB (DLf H src cn cm) (PIfOf chdP H src cn cm) (CostSkeleton.LF cn cm)
        (bmsspProc (RamSpine.baseProgC newS insS) (recText BL2Inst.fpAtRaw newS insS emptyS
          (iterText pullS mergeS delBS insS) finP))
        (BM.chdTau (CostSkeleton.tF cn cm)) (BM.chdM (CostSkeleton.tF cn cm)) finP Kfin Cfin
        (finCst H (DLf H src cn cm).K (DLf H src cn cm).NB) l)
    -- the decidable name facts
    (hDW : ∀ H src cn cm, ∀ a ∈ RamBaseCase.baseWR (IHeapLab.heapI H src (KhF cn cm)) ++
      RamSpine.ptrLoopWR, a ∉ (DLf H src cn cm).dWR)
    (hPW : ∀ H src cn cm, ∀ a ∈ (PIfOf chdP H src cn cm).pWR,
      a ∉ RamBaseCase.baseWR (IHeapLab.heapI H src (KhF cn cm)) ++ RamSpine.ptrLoopWR ++
        (DLf H src cn cm).dWR)
    (hPA : ∀ H src cn cm, ∀ a ∈ (PIfOf chdP H src cn cm).pWA, a ∉ (DLf H src cn cm).dWA)
    (hPd : ∀ H src cn cm, (∀ a ∈ (PIfOf chdP H src cn cm).pWA, a ∉ dwa) ∧
      (∀ a ∈ (PIfOf chdP H src cn cm).pWR, a ∉ dwr))
    (hPb : ∀ H src cn cm, (∀ a ∈ (PIfOf chdP H src cn cm).pWA, a ∉ slotW ++ ["S", "S.len"]) ∧
      (∀ a ∈ (PIfOf chdP H src cn cm).pWR, a ∉ blowWR ++ ["lvl"]))
    (hfoot : SpineFoot (chdPs newS insS (recText BL2Inst.fpAtRaw newS insS emptyS
        (iterText pullS mergeS delBS insS) finP) extra))
    {RW : List String}
    (hNm : ∀ H src cn cm, BodyNames (DLf H src cn cm) (PIfOf chdP H src cn cm) RW)
    (hy : ∀ H src cn cm, PostHyg (DLf H src cn cm) (PIfOf chdP H src cn cm)
      ("lab.bit" :: IHeapLab.cmpScratchW))
    (hLWd : ∀ H src cn cm, ∀ a ∈ WinScan.ltW, a ∉ (DLf H src cn cm).dWR)
    (hLWp : ∀ H src cn cm, ∀ a ∈ WinScan.ltW, a ∉ (PIfOf chdP H src cn cm).pWR)
    (hDP : ∀ H src cn cm, ∀ a ∈ (DLf H src cn cm).dWA, a ∉ (PIfOf chdP H src cn cm).pWA)
    (hDPr : ∀ H src cn cm, ∀ a ∈ (DLf H src cn cm).dWR, a ∉ (PIfOf chdP H src cn cm).pWR)
    (hDLA : ∀ H src cn cm, ∀ a ∈ (DLf H src cn cm).dWA, a ∉ BL2Inst.fpAtWA (G := H) (s := src))
    (hDLV : ∀ H src cn cm, ∀ a ∈ (DLf H src cn cm).dVA, a ∉ BL2Inst.fpAtVA (G := H) (s := src))
    (hDLR : ∀ H src cn cm, ∀ a ∈ (DLf H src cn cm).dWR, a ∉ BL2Inst.fpAtWR (G := H) (s := src))
    -- the word exponent
    (hbig : 12 + ((K : ℝ) + (13000 + 34 * ((100 : ℕ) + (Kd : ℝ))) + 0) * (kmaster 1 1 1000 + 1) +
      |(0 : ℝ)| + |((10 ^ 9 + 64 * (K + 27 + 1) ^ 4 * 10 ^ 56 : ℕ) : ℝ)| ≤ (4 : ℝ) ^ (e + 1 - 8)) :
    let core := coreTop (spineOf (spinePro BL2.fpAlloc dPro))
    let ps := chdPs newS insS (recText BL2Inst.fpAtRaw newS insS emptyS
        (iterText pullS mergeS delBS insS) finP) extra
    let Kc : ℝ := ((K : ℝ) + (13000 + 34 * ((100 : ℕ) + (Kd : ℝ))) + 0) * (kmaster 1 1 1000 + 1) + 250
    (chdProg e ps core).Exact ∧ ∀ (G : Graph) (s : Fin G.n),
      (chdProg e ps core).RunsWithin G s
        ((bodyC Kc + 65536 * 9 + 100) * GateCTarget.Tdisp GateCCalc.F G.n G.m) := by
  intro core ps Kc
  -- the level step
  have hs := hs_of_parts (DLf := DLf) (body0 := RamSpine.baseProgC newS insS) (fp := BL2Inst.fpAtRaw)
    (iterB := iterText pullS mergeS delBS insS) (finP := finP) hnew hinsS hemp hNm
    (K := K) (Ko := Ko) (Kf := 524) (Cf := 351) (Kfin := Kfin) (Cfin := Cfin) (KD := KD)
    (Slf := SlfC K 27)
    (Cstf := fun H src cn cm => finCst H (DLf H src cn cm).K (DLf H src cn cm).NB) hKD hK
    (fun H src cn cm hMI => by
      show finCst H (DLf H src cn cm).K (DLf H src cn cm).NB + 2 ≤ SlfC K 27 cn cm
      rw [hNB]
      exact le_trans (by
        unfold finCst
        have h1 := hKK H src cn cm
        have hc : WinScan.CED (DLf H src cn cm).K (nbF cn cm) ≤ WinScan.CED K (nbF cn cm) := by
          unfold WinScan.CED; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h1) _
        have h2 := Nat.mul_le_mul_right (H.n * (Nat.log 2 (nbF cn cm) + 4)) h1
        have h3 := Nat.mul_le_mul_left (H.m + 1) hc
        have h4 := Nat.mul_le_mul_left (H.n + 1) (Nat.add_le_add_right h3 101)
        omega) (finCst_le_SlfC K 27 cn cm hMI.sizeN hMI.sizeM))
    (hFP_of hDLA hDLV hDLR _)
    (hLoop_of_parts hpull hmerge hdelB hinsS hy hLWd hLWp hDP hDPr
      (fun H src cn cm hMI => by
        rw [hNB]
        exact le_trans (by
          unfold RamSpine.postS
          have h1 := hKK H src cn cm
          have hc : WinScan.CED (DLf H src cn cm).K (2 * nbF cn cm) ≤ WinScan.CED K (2 * nbF cn cm) := by
            unfold WinScan.CED; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h1) _
          have h2 := Nat.mul_le_mul_right (H.n * (Nat.log 2 (2 * nbF cn cm) + 4)) h1
          have h3 := Nat.mul_le_mul_left (H.m + 1) hc
          have h4 := Nat.mul_le_mul_left (H.n + 1) (Nat.add_le_add_right h3 101)
          have h5 := Nat.mul_le_mul_left H.n (Nat.add_le_add_right h1 3)
          omega) (postS_le_SlfC K 27 cn cm hMI.sizeN hMI.sizeM))
      hLT hKo)
    hFin
  -- the top
  exact chdProg_of_step e he newS insS (recText BL2Inst.fpAtRaw newS insS emptyS
      (iterText pullS mergeS delBS insS) finP) extra hnew hinsS hKD hKb hucapF hDW hPW hPA hD hPd hPb
    hfoot (fun cn cm => baseReq_le_SlfC K 27 cn cm) (by norm_num) (fun n m => SlfC_le K 27 n m)
    hs hbig

/-- **The word exponent 160 fits the final constants** (for `K ≤ 10^6`, `Kd ≤ 10^14`). -/
theorem hbig160 {K Kd : ℕ} (hK : K ≤ 10 ^ 6) (hKd : Kd ≤ 10 ^ 14) :
    12 + ((K : ℝ) + (13000 + 34 * ((100 : ℕ) + (Kd : ℝ))) + 0) * (kmaster 1 1 1000 + 1) +
      |(0 : ℝ)| + |((10 ^ 9 + 64 * (K + 27 + 1) ^ 4 * 10 ^ 56 : ℕ) : ℝ)| ≤ (4 : ℝ) ^ (160 + 1 - 8) := by
  have hk := kmN_le
  have h1 : (K + 27 + 1) ^ 4 ≤ (10 ^ 6 + 28) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have h2 : (K + (13000 + 34 * (100 + Kd))) * (kmN + 1) ≤
      (10 ^ 6 + (13000 + 34 * (100 + 10 ^ 14))) * (10 ^ 11 + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h3 : 10 ^ 9 + 64 * (K + 27 + 1) ^ 4 * 10 ^ 56 ≤ 10 ^ 9 + 64 * (10 ^ 6 + 28) ^ 4 * 10 ^ 56 := by
    have := Nat.mul_le_mul_right (10 ^ 56) (Nat.mul_le_mul_left 64 h1); omega
  have hnat : 12 + (K + (13000 + 34 * (100 + Kd))) * (kmN + 1) +
      (10 ^ 9 + 64 * (K + 27 + 1) ^ 4 * 10 ^ 56) ≤ 4 ^ 153 := by
    have h4 : 12 + (10 ^ 6 + (13000 + 34 * (100 + 10 ^ 14))) * (10 ^ 11 + 1) +
        (10 ^ 9 + 64 * (10 ^ 6 + 28) ^ 4 * 10 ^ 56) ≤ (4 : ℕ) ^ 153 := by norm_num
    omega
  have hR : ((12 + (K + (13000 + 34 * (100 + Kd))) * (kmN + 1) +
      (10 ^ 9 + 64 * (K + 27 + 1) ^ 4 * 10 ^ 56) : ℕ) : ℝ) ≤ ((4 ^ 153 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  rw [kmaster_eq, abs_zero, abs_of_nonneg (Nat.cast_nonneg _)]
  have e153 : (160 + 1 - 8 : ℕ) = 153 := by norm_num
  rw [e153]
  push_cast at hR ⊢
  linarith

end Frontier.CHD.L6

#print axioms Frontier.CHD.L6.chdProg_of_DLayer
#print axioms Frontier.CHD.L6.hbig160
