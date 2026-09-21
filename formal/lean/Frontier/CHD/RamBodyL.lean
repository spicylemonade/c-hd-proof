import Frontier.CHD.RamBodySpec
import Frontier.CHD.SizeFacts
import Frontier.CHD.FPBind

/-!
# Frontier.CHD.RamBodyL — the level step's Layer-A size premise for FindPivots-HD (owner: agent-01)

**NON-GATE** (Layer A).  `sbA_fpC`: for `FPC := fpC …` (groups of size `< 3k`), every expansion of
a pulled set in the main loop of a level-`(l+1)` call has at most `3k · M_{l+1}` vertices — the
premise `hSbA` of `callSpec_succ` (agent-08's `hSb` of `loop2_spec`), from agent-03's
`expand_card_le` and the pull's size bound.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamBody

open Frontier Frontier.CHD Frontier.CHD.BM Frontier.CHD.RamSpine

variable {G : Graph} {s : Fin G.n} {T : ℕ → ℕ}

/-- **The expansion bound** of the main loop for FindPivots-HD. -/
theorem sbA_fpC {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}
    (hout : ∀ u e, e ∈ out u ↔ G.src e = u) (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hsimp : ∀ u, ((out u).map G.dst).Nodup) (hk : 2 ≤ k) {Mf τ : ℕ → ℕ} {l : ℕ}
    (Blow B : WLab G s) (S : Finset (Fin G.n)) (d0 : Labels G s) (φ : Finset (Fin G.m))
    (d1 : Labels G s) (p : ℕ) (P0 : Fin p → Finset (Fin G.n)) (Q W : Finset (Fin G.n))
    (φ1 : Finset (Fin G.m)) (ω : FPData G s) (cfp : ℕ) (B'0 : WLab G s) (f0 : ℕ) (L0 : LiveM G s)
    (c' : LoopCfgD G s (Finset (Fin G.m)) p)
    (hf : fpC G s out k hins hext (l + 1) Blow B S d0 φ d1 p P0 Q W φ1 ω cfp)
    (hpre : CallPre B S d0) (hI : DelInv G s φ) (hlow : ∀ x ∈ S, Blow ≤ d0 x)
    (hA : ALoop (dlOps G s) (DelInv G s) Mf l B S d0 d1 P0 B'0 f0 L0 c')
    (_hnd : ¬ LoopDoneD (τ (l + 1)) c') (ks : List (Fin G.n)) (Bi : WLab G s) (g1 : DGl G s)
    (Dc1 : DStrM G s) (cp : ℕ)
    (hpull : pullC (dlOps G s) (T (l + 1)) c'.cs.g c'.cs.Dc = (ks, Bi, g1, Dc1, cp)) :
    (BM.expand c'.cs.lit ks.toFinset Bi).card ≤ 3 * k * Mf (l + 1) := by
  obtain ⟨-, -, hP0, -, -⟩ := fpC_spec hout hsort hsimp hk hpre hI hf
  obtain ⟨hfp, -⟩ := fpC_sound (hins := hins) (hext := hext) hout hsort hsimp hk (l + 1) Blow B S d0 φ
    d1 p P0 Q W φ1 ω cfp hpre hI hlow hf
  have hP : ∀ j, (c'.cs.lit.P j).card < 3 * k := fun j =>
    lt_of_le_of_lt (Finset.card_le_card (hA.linv.Psub j)) (hP0 j)
  have hdisj : ∀ i j, i ≠ j → Disjoint (c'.cs.lit.P i) (c'.cs.lit.P j) := fun i j hij =>
    Finset.disjoint_of_subset_left (hA.linv.Psub i)
      (Finset.disjoint_of_subset_right (hA.linv.Psub j) (hfp.gdisj i j hij))
  have h1 := expand_card_le c'.cs.lit ks.toFinset Bi (by omega) hP hdisj
  obtain ⟨-, hks, -⟩ := pull_sim hA.sinv hA.kinj hpull
  have h2 : 3 * k * ks.toFinset.card ≤ 3 * k * Mf (l + 1) := by
    rw [← hA.M]; exact Nat.mul_le_mul_left _ hks
  omega

end Frontier.CHD.RamBody
