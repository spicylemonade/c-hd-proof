import Frontier.CHD.L6.DCap
import Frontier.CHD.SizeFacts
import Frontier.CHD.FPBind

/-!
# The expansion-size bound of the level step (agent-10; `callSpec_succ`'s `hSbA`)

`hSbA_chd`: for the C-HD instantiation (FindPivots `fpC … kF 1 kF`, the lazy D-structure `dlOps`,
`Mf := chdM tF`), every sub-call frontier of a level-`(l+1)` call is small: for every FindPivots
outcome and every non-final loop configuration satisfying agent-08's `ALoop`, the expansion of the
pulled key set has at most `SbF cn cm l = 3·kF·chdM tF (l+1)` vertices.

Proof: the pull returns at most `M = chdM tF (l+1)` keys (`DOps.pull_post` from `SInv`/`KeyInj`,
`ALoop.M`); the FindPivots groups have `< 3k` vertices (`fpC_spec`) and are pairwise disjoint
(`fpC_sound` / `FPContract.gdisj`), and the loop's groups are subsets (`LInv.Psub`); so agent-03's
`expand_card_le` gives `≤ 3k·|ks| ≤ 3k·M`.  NON-GATE (Layer A).
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamLevel Frontier.CHD.BM
  Frontier.CHD.RamBaseCase Frontier.CHD.LabTab Frontier.CHD.RamSpine

theorem hSbA_chd {H : Graph} {src : Fin H.n} {cn cm : ℕ} (hMI : MasterIn H src cn cm)
    (T : ℕ → ℕ) (τ : ℕ → ℕ) (l : ℕ) :
    ∀ (Blow B : WLab H src) (S : Finset (Fin H.n)) (d0 : Labels H src) (φ : Finset (Fin H.m))
      (d1 : Labels H src) (p : ℕ) (P0 : Fin p → Finset (Fin H.n)) (Q W : Finset (Fin H.n))
      (φ1 : Finset (Fin H.m)) (ω : FPData H src) (cfp : ℕ) (B'0 : WLab H src) (f0 : ℕ)
      (L0 : LiveM H src) (c' : LoopCfgD H src (Finset (Fin H.m)) p),
      fpC H src (outL H) (CostSkeleton.kF cn cm) (chdP cn cm).hins (chdP cn cm).hext (l + 1)
        Blow B S d0 φ d1 p P0 Q W φ1 ω cfp → CallPre B S d0 → DelInv H src φ →
      (∀ x ∈ S, Blow ≤ d0 x) →
      ALoop (dlOps H src) (DelInv H src) (BM.chdM (CostSkeleton.tF cn cm)) l B S d0 d1 P0 B'0 f0 L0
        c' → ¬ LoopDoneD (τ (l + 1)) c' →
      ∀ ks Bi g1 Dc1 cp, pullC (dlOps H src) (T (l + 1)) c'.cs.g c'.cs.Dc = (ks, Bi, g1, Dc1, cp) →
      (BM.expand c'.cs.lit ks.toFinset Bi).card ≤ SbF cn cm l := by
  intro Blow B S d0 φ d1 p P0 Q W φ1 ω cfp B'0 f0 L0 c' hfp hpre hI hlow hA _ ks Bi g1 Dc1 cp hpull
  have hk2 : 2 ≤ CostSkeleton.kF cn cm := CostSkeleton.two_le_kF cn cm
  have hout : ∀ u e, e ∈ outL H u ↔ H.src e = u := fun _ _ => outL_mem
  -- the FindPivots groups: `< 3k` vertices each, pairwise disjoint
  obtain ⟨-, -, hP0, -, -⟩ := fpC_spec hout hMI.sorted hMI.simple hk2 hpre hI hfp
  obtain ⟨hcon, -⟩ := fpC_sound hout hMI.sorted hMI.simple hk2 (l + 1) Blow B S d0 φ d1 p P0 Q W φ1
    ω cfp hpre hI hlow hfp
  have hPk : ∀ j, (c'.cs.lit.P j).card < 3 * CostSkeleton.kF cn cm := fun j =>
    lt_of_le_of_lt (Finset.card_le_card (hA.linv.Psub j)) (hP0 j)
  have hPd : ∀ i j, i ≠ j → Disjoint (c'.cs.lit.P i) (c'.cs.lit.P j) := fun i j hij =>
    Finset.disjoint_of_subset_left (hA.linv.Psub i)
      (Finset.disjoint_of_subset_right (hA.linv.Psub j) (hcon.gdisj i j hij))
  have hexp := expand_card_le c'.cs.lit ks.toFinset Bi (by omega) hPk hPd
  -- the pull returns at most `M = chdM tF (l+1)` keys
  have hks : ks = ((dlOps H src).pull (T (l + 1)) c'.cs.g.L c'.cs.Dc).1 := by
    have h := congrArg Prod.fst hpull
    simp only [pullC] at h
    exact h.symm
  have hlen := ((dlOps H src).pull_post (T (l + 1)) hA.sinv.wf hA.kinj hA.sinv.ids hA.sinv.M1).1
  have hcard : ks.toFinset.card ≤ BM.chdM (CostSkeleton.tF cn cm) (l + 1) := by
    calc ks.toFinset.card ≤ ks.length := List.toFinset_card_le _
      _ ≤ c'.cs.Dc.M := by rw [hks]; exact hlen
      _ = _ := hA.M
  unfold SbF
  calc (BM.expand c'.cs.lit ks.toFinset Bi).card ≤ 3 * CostSkeleton.kF cn cm * ks.toFinset.card :=
        hexp
    _ ≤ 3 * CostSkeleton.kF cn cm * BM.chdM (CostSkeleton.tF cn cm) (l + 1) :=
        Nat.mul_le_mul_left _ hcard

end Frontier.CHD.L6

#print axioms Frontier.CHD.L6.hSbA_chd
