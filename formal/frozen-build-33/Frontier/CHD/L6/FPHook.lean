import Frontier.CHD.L6.ProFinal
import Frontier.CHD.BL2Pro
import Frontier.CHD.BL2FPB

/-!
# The FindPivots allocation hook of the spine prologue (agent-10, from agent-09's `fpAlloc_phiR`)

`fpHook`: B-L2's `fpAlloc` is a `HookSpec`: from the prologue's hook state (`CoreIn`, `cp.k = kF`)
it establishes B-L2's `phiR … ∅` (the `PhiI` instance `BL2.phiI` with `k = kF cn cm` and the cost
parameters of `P`), writes only `fpAllocWA` / `fpAllocWR`, and costs `34 n + 2 k + 41 ≤ 100 (Tnat+1)`.
NON-GATE (glue).
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD.LabTab WExpr Stmt

/-- The B-L2 `PhiI` family of the spine for the cost parameters `P`. -/
def PIfOf (P : ℕ → ℕ → CostPar) : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ),
    RamSpine.PhiI (Finset (Fin H.m)) :=
  fun H src cn cm => BL2Inst.phiI H src (CostSkeleton.kF cn cm) (P cn cm).hins (P cn cm).hext
    (CostSkeleton.LF cn cm)

theorem fpHook (e : ℕ) (he : 32 ≤ e) (ps : List Stmt) (P : ℕ → ℕ → CostPar) :
    HookSpec e ps BL2.fpAlloc (fun H src cn cm r => (PIfOf P H src cn cm).PhiR r ∅)
      BL2.fpAllocWA [] BL2.fpAllocWR [] 100 := by
  refine ⟨by decide, by simp, by decide, ?_⟩
  intro H src cn cm c0 st hH
  have hc := hH.pre.core
  have hcapB := capBig he hc
  have hcn1 := hc.cn_pos
  have hcm1 := hc.cm_pos
  refine (BL2.fpAlloc_phiR (G := H) (s := src) (hins := (P cn cm).hins) (hext := (P cn cm).hext)
    hc.gN hH.pre.k hc.gM hc.graph hc.csr hc.hdLen hc.nxtLen hc.hd hc.nxt (by nlinarith)).mono ?_
  rintro r ⟨hphi, hU, hcost⟩
  have hcapPhi : (2 * CostSkeleton.LF cn cm + 5) * H.n + 4 * CostSkeleton.LF cn cm +
      2 * CostSkeleton.kF cn cm + 8 < r.cap := by
    rw [hU.cap]
    have hX4 : 4 ≤ cn + cm + 2 := by omega
    have h6 := X_pow_ge hcn1 hcm1 he hc.cap
    have hsq := sq_lt_pow6 (cn + cm + 2) hX4
    have hL := LF_le cn cm hcn1
    have hN := hc.sizeN
    have hk : CostSkeleton.kF cn cm ≤ CostSkeleton.tF cn cm := CostSkeleton.kF_le_tF cn cm
    have hT : CostSkeleton.tF cn cm ≤ 16 + cn :=
      (CostSkeleton.tF_le cn cm).trans (by have := lgN_le_self hcn1; omega)
    have : (2 * CostSkeleton.LF cn cm + 5) * H.n + 4 * CostSkeleton.LF cn cm +
        2 * CostSkeleton.kF cn cm + 8 ≤ 64 * (cn + cm + 2) ^ 2 := by nlinarith
    omega
  refine ⟨⟨hphi, hcapPhi⟩, hU, by omega, ?_⟩
  have hk : CostSkeleton.kF cn cm ≤ CostSkeleton.tF cn cm := CostSkeleton.kF_le_tF cn cm
  have hN := hc.sizeN
  have hT : CostSkeleton.tF cn cm + cn ≤ CostSkeleton.Tnat cn cm := by
    unfold CostSkeleton.Tnat; nlinarith
  rw [hcost]
  nlinarith

end Frontier.CHD.L6

#print axioms Frontier.CHD.L6.fpHook
