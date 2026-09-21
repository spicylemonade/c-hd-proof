import Frontier.CHD.L6.DCap
import Frontier.CHD.L6.SbA
import Frontier.CHD.L6.FPHook
import Frontier.CHD.RamBodySpec

/-!
# The level step of the C-HD instance (agent-10; from agent-01's `callSpec_succ`)

`recText`: the closed level-body text for closed phase texts (agent-01's `bodyProg` shape with
`fp`/`iterB`/`finP` and the D texts `newS`/`insS`/`emptyS`).

`hs_of_parts`: the level-step hypothesis `hs` of `L6.chdTarget_of_step`, for the procedure body
`bmsspProc body0 (recText …)`, from exactly the three remaining phase interfaces
* `hFP`   — FindPivots at level `l+1` (agent-09's `fpB_raw`),
* `hLoop` — the main loop from the level IH (agent-08's `loopSpecB_of_loop2`),
* `hFin`  — the finalization (agent-03's `FinB`),
plus the decidable body names and the constants.  Everything else of `callSpec_succ` is discharged
here: FindPivots soundness/totality (`fpC_sound`/`fpC_total`), `1 ≤ τ`, `1 ≤ M`, `mergeM`, the
expansion size (`hSbA_chd`); `2·Mf(l+1)+2 < cap` is agent-01's own `Static.MCap` step.  NON-GATE (composition).
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamLevel Frontier.CHD.BM
  Frontier.CHD.RamBaseCase Frontier.CHD.LabTab Frontier.CHD.RamSpine Frontier.CHD.RamInit
  Frontier.CHD.RamBody WExpr Stmt

/-- The closed level-body text (agent-01's `bodyProg` shape). -/
def recText (fp newS insS emptyS iterB finP : Stmt) : Stmt :=
  seq fp (seq copyGrp (seq (pivProg cmpTTc) (seq (pivIns newS insS) (seq b8Setup
    (seq Frontier.CHD.SpineLab.b8Prog (seq (rowReset "U.len") (seq (mainLoop emptyS iterB) finP)))))))

theorem chdTau_pos (t : ℕ) (ht : 1 ≤ t) (l : ℕ) : 1 ≤ BM.chdTau t l := by
  unfold BM.chdTau
  have h1 : 1 ≤ t ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ 2 ^ (l * t) := Nat.one_le_two_pow
  calc 1 = 1 * 1 := by norm_num
    _ ≤ t ^ 3 * 2 ^ (l * t) := Nat.mul_le_mul h1 h2

/-- **The level step of the C-HD instance** from the three phase interfaces. -/
theorem hs_of_parts
    {DLf : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), RamSpine.DLayer H src Tz}
    {newS insS emptyS fp iterB finP body0 : Stmt}
    (hnew : ∀ H src cn cm, (DLf H src cn cm).new = newS)
    (hinsS : ∀ H src cn cm, (DLf H src cn cm).ins = insS)
    (hemp : ∀ H src cn cm, (DLf H src cn cm).empty = emptyS)
    {RW : List String}
    (hNm : ∀ H src cn cm, BodyNames (DLf H src cn cm) (PIfOf chdP H src cn cm) RW)
    {K Ko Kf Cf Kfin Cfin KD : ℕ} {Slf : ℕ → ℕ → ℕ}
    {Cstf : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), ℕ}
    (hKD : ∀ H src cn cm, (DLf H src cn cm).K ≤ KD)
    (hK : Kf + Cf + Ko + Kfin + Cfin + 2 * KD + 60 ≤ K)
    (hSl : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
      Cstf H src cn cm + 2 ≤ Slf cn cm)
    (hFP : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
      ∀ l : ℕ, l < CostSkeleton.LF cn cm →
      FPB (DLf H src cn cm) (PIfOf chdP H src cn cm) (DelInv H src)
        (fpC H src (outL H) (CostSkeleton.kF cn cm) (chdP cn cm).hins (chdP cn cm).hext)
        (CostSkeleton.LF cn cm) (bmsspProc body0 (recText fp newS insS emptyS iterB finP)) fp
        (BM.chdTau (CostSkeleton.tF cn cm)) (BM.chdM (CostSkeleton.tF cn cm)) Kf Cf (l + 1))
    (hLoop : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
      ∀ l : ℕ, l < CostSkeleton.LF cn cm →
      RamSpine.CallSpec (DLf H src cn cm) (PIfOf chdP H src cn cm).PhiR (DelInv H src)
        (fpC H src (outL H) (CostSkeleton.kF cn cm) (chdP cn cm).hins (chdP cn cm).hext)
        (chdP cn cm).DCb (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm))
        (CostSkeleton.LF cn cm) (bmsspProc body0 (recText fp newS insS emptyS iterB finP)) K
        (Slf cn cm) (SbF cn cm) l →
      LoopSpecB (DLf H src cn cm) (PIfOf chdP H src cn cm) (DelInv H src)
        (fpC H src (outL H) (CostSkeleton.kF cn cm) (chdP cn cm).hins (chdP cn cm).hext)
        (chdP cn cm).DCb (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm))
        (CostSkeleton.LF cn cm) (bmsspProc body0 (recText fp newS insS emptyS iterB finP))
        (DLf H src cn cm).empty iterB K Ko (Slf cn cm) (SbF cn cm) l)
    (hFin : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
      ∀ l : ℕ, l < CostSkeleton.LF cn cm →
      FinB (DLf H src cn cm) (PIfOf chdP H src cn cm) (CostSkeleton.LF cn cm)
        (bmsspProc body0 (recText fp newS insS emptyS iterB finP))
        (BM.chdTau (CostSkeleton.tF cn cm)) (BM.chdM (CostSkeleton.tF cn cm)) finP Kfin Cfin
        (Cstf H src cn cm) l) :
    ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
      ∀ l : ℕ, l < CostSkeleton.LF cn cm →
      RamSpine.CallSpec (DLf H src cn cm) (PIfOf chdP H src cn cm).PhiR (DelInv H src)
        (fpC H src (outL H) (CostSkeleton.kF cn cm) (chdP cn cm).hins (chdP cn cm).hext)
        (chdP cn cm).DCb (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm))
        (CostSkeleton.LF cn cm) (bmsspProc body0 (recText fp newS insS emptyS iterB finP)) K
        (Slf cn cm) (SbF cn cm) l →
      RamSpine.CallSpec (DLf H src cn cm) (PIfOf chdP H src cn cm).PhiR (DelInv H src)
        (fpC H src (outL H) (CostSkeleton.kF cn cm) (chdP cn cm).hins (chdP cn cm).hext)
        (chdP cn cm).DCb (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm))
        (CostSkeleton.LF cn cm) (bmsspProc body0 (recText fp newS insS emptyS iterB finP)) K
        (Slf cn cm) (SbF cn cm) (l + 1) := by
  intro H src cn cm hMI l hl hIH
  have hk2 : 2 ≤ CostSkeleton.kF cn cm := CostSkeleton.two_le_kF cn cm
  have ht1 : 1 ≤ CostSkeleton.tF cn cm := le_trans (by norm_num) (CostSkeleton.sixteen_le_tF cn cm)
  have hout : ∀ u e, e ∈ outL H u ↔ H.src e = u := fun _ _ => outL_mem
  refine callSpec_succ (DLf H src cn cm) (PIfOf chdP H src cn cm) (hNm H src cn cm)
    (body0 := body0) (fp := fp) (iterB := iterB) (finP := finP) ?_
    (hFP H src cn cm hMI l hl) (hLoop H src cn cm hMI l hl hIH) (hFin H src cn cm hMI l hl)
    (fpC_sound hout hMI.sorted hMI.simple hk2)
    (fun l' Blow B S d0 φ hpre _ => fpC_total hout hMI.sorted l' Blow B S d0 φ hpre)
    (chdTau_pos _ ht1) (fun _ => trivial) (chdM_pos _ ht1)
    (hSbA_chd hMI Tz (BM.chdTau (CostSkeleton.tF cn cm)) l)
    (by have := hKD H src cn cm; omega) (hSl H src cn cm hMI)
  · simp only [recText, hnew, hinsS, hemp]

end Frontier.CHD.L6

#print axioms Frontier.CHD.L6.hs_of_parts
