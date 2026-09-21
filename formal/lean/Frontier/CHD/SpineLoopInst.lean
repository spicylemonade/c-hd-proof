import Frontier.CHD.L6.StepInst
import Frontier.CHD.SpineLoopB
import Frontier.CHD.SpinePostB
import Frontier.CHD.LtBiI
import Frontier.CHD.CSRSortedOf

/-!
# SpineLoopInst — the loop input `hLoop` of the C-HD level step (agent-08, B-L4, NON-GATE)

`hLoop_of_parts` is exactly the `hLoop` hypothesis of agent-10's `L6.hs_of_parts`: for every
instance and every level `l < LF`, the level IH `CallSpec … l` gives agent-01's `LoopSpecB` of the
main loop with
`iterB = seq (firstHalf pullS (ltBi KBi "sp.bif")) (postI mergeS delBS insS (cmpLab ttRa ttRb "lab.bit"))`.
Ingredients: `loopSpecB_of_loop2` (agent-08), agent-06's second half `postHalf_cmpTT`, agent-02's
expansion test `ltBi_ltI` and `csrSorted_of_outL`, agent-01's Layer-A package `levelPkg`.  What is
left are the closed D texts, name facts (decidable on the instance), the slack and the constants.
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamLevel Frontier.CHD.BM
  Frontier.CHD.RamBaseCase Frontier.CHD.LabTab Frontier.CHD.RamSpine Frontier.CHD.RamInit
  Frontier.CHD.RamBody WExpr Stmt

/-- The iteration body of the C-HD main loop: first half, then agent-06's second half with the
B-LAB comparison `cmpTT`. -/
def iterText (pullS mergeS delBS insS : Stmt) : Stmt :=
  seq (firstHalf pullS (WinScan.ltBi KBi "sp.bif"))
    (postI mergeS delBS insS (IHeapLab.cmpLab IHeapLab.ttRa IHeapLab.ttRb "lab.bit"))

/-- **The loop input of `hs_of_parts`.** -/
theorem hLoop_of_parts
    {DLf : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), RamSpine.DLayer H src Tz}
    {pullS mergeS delBS insS : Stmt}
    (hpull : ∀ H src cn cm, (DLf H src cn cm).pull = pullS)
    (hmerge : ∀ H src cn cm, (DLf H src cn cm).merge = mergeS)
    (hdelB : ∀ H src cn cm, (DLf H src cn cm).delB = delBS)
    (hins : ∀ H src cn cm, (DLf H src cn cm).ins = insS)
    {body : Stmt} {K Ko : ℕ} {Slf : ℕ → ℕ → ℕ}
    (hy : ∀ H src cn cm, PostHyg (DLf H src cn cm) (PIfOf chdP H src cn cm)
      ("lab.bit" :: IHeapLab.cmpScratchW))
    (hLWd : ∀ H src cn cm, ∀ a ∈ WinScan.ltW, a ∉ (DLf H src cn cm).dWR)
    (hLWp : ∀ H src cn cm, ∀ a ∈ WinScan.ltW, a ∉ (PIfOf chdP H src cn cm).pWR)
    (hDP : ∀ H src cn cm, ∀ a ∈ (DLf H src cn cm).dWA, a ∉ (PIfOf chdP H src cn cm).pWA)
    (hDPr : ∀ H src cn cm, ∀ a ∈ (DLf H src cn cm).dWR, a ∉ (PIfOf chdP H src cn cm).pWR)
    (hSlP : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
      postS (DLf H src cn cm).K 27 H.n H.m (2 * (DLf H src cn cm).NB) ≤ Slf cn cm)
    (hLT : ∀ H src cn cm, CostSkeleton.LF cn cm ≤ (DLf H src cn cm).LT)
    (hKo : ∀ H src cn cm, (DLf H src cn cm).K + 22 + 71 + postK (DLf H src cn cm).K 27 + 1 ≤ Ko) :
    ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
      ∀ l : ℕ, l < CostSkeleton.LF cn cm →
      RamSpine.CallSpec (DLf H src cn cm) (PIfOf chdP H src cn cm).PhiR (DelInv H src)
        (fpC H src (outL H) (CostSkeleton.kF cn cm) (chdP cn cm).hins (chdP cn cm).hext)
        (chdP cn cm).DCb (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm))
        (CostSkeleton.LF cn cm) body K (Slf cn cm) (SbF cn cm) l →
      LoopSpecB (DLf H src cn cm) (PIfOf chdP H src cn cm) (DelInv H src)
        (fpC H src (outL H) (CostSkeleton.kF cn cm) (chdP cn cm).hins (chdP cn cm).hext)
        (chdP cn cm).DCb (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm))
        (CostSkeleton.LF cn cm) body (DLf H src cn cm).empty (iterText pullS mergeS delBS insS) K Ko
        (Slf cn cm) (SbF cn cm) l := by
  intro H src cn cm hMI l hl hIH
  have hk2 : 2 ≤ CostSkeleton.kF cn cm := CostSkeleton.two_le_kF cn cm
  have ht1 : 1 ≤ CostSkeleton.tF cn cm := le_trans (by norm_num) (CostSkeleton.sixteen_le_tF cn cm)
  have hout : ∀ u e, e ∈ outL H u ↔ H.src e = u := fun _ _ => outL_mem
  obtain ⟨DC, subC, hsimsub, hsubC, hDC, hsubT⟩ := RamBody.levelPkg
    (fpC H src (outL H) (CostSkeleton.kF cn cm) (chdP cn cm).hins (chdP cn cm).hext)
    (chdP cn cm).DCb Tz (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm))
    (fpC_sound hout hMI.sorted hMI.simple hk2)
    (fun l' Blow B S d0 φ hpre _ => fpC_total hout hMI.sorted l' Blow B S d0 φ hpre)
    (chdTau_pos _ ht1) (fun _ => trivial) (chdM_pos _ ht1) l
  have hKo' := hKo H src cn cm
  have h := loopSpecB_of_loop2 (DLf H src cn cm) (PIfOf chdP H src cn cm) hIH
    (fun d H' c0 Bi => WinScan.ltBi_ltI d H' c0 Bi) (hLWd H src cn cm) (hLWp H src cn cm)
    (by decide) (hDP H src cn cm) (hDPr H src cn cm)
    (postHalf_cmpTT (DLf H src cn cm) (PIfOf chdP H src cn cm) (hy H src cn cm)
      (WinScan.csrSorted_of_outL hMI.sorted) hsimsub hsubC (hSlP H src cn cm hMI) (hLT H src cn cm))
    (fun _ => trivial) (DC := DC) hsimsub hsubC hDC (chdTau_pos _ ht1 l) hsubT hKo' (by omega)
  rw [hpull, hmerge, hdelB, hins] at h
  exact h

end Frontier.CHD.L6
