import Frontier.CHD.DPro
import Frontier.CHD.L6.DCap
import Frontier.CHD.L6.FPHook

/-!
# The D-layer allocation hook of the C-HD program (owner agent-09, NON-GATE)

`dProC = dPro (12 · kmN)`: the use capacity `ucap = 12·kmN·Tnat + 2` is exactly agent-10's
`hucapF` capacity (`L6.hucap_of`), and the word-size condition of `dProSpec` holds for every
`e ≥ 32` (`kmN ≤ 10^11`, `L6.kmN_le`).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.DPro

open Frontier Frontier.RAM Frontier.CHD Frontier.CHD.L6

/-- **The D-layer allocation hook of the C-HD program.** -/
abbrev dProC : Stmt := dPro (12 * kmN)

/-- **The D-layer parameters of the C-HD program.** -/
abbrev dParC (cn cm : ℕ) : DLI.DPar := dPar (12 * kmN) cn cm

theorem hCw_C {e : ℕ} (he : 32 ≤ e) : 64 * (12 * kmN) + 128 ≤ 4 ^ (e - 1) := by
  have hk := kmN_le
  have h1 : (4 : ℕ) ^ 31 ≤ 4 ^ (e - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 64 * (12 * kmN) + 128 ≤ 64 * (12 * 10 ^ 11) + 128 := by
    have := Nat.mul_le_mul_left 12 hk
    omega
  have h3 : 64 * (12 * 10 ^ 11) + 128 ≤ (4 : ℕ) ^ 31 := by norm_num
  omega

/-- the capacity agent-10's `hucap_of` asks for -/
theorem dParC_ucap (cn cm : ℕ) : 12 * kmN * CostSkeleton.Tnat cn cm + 2 ≤ (dParC cn cm).ucap :=
  le_rfl

/-- **The D-layer allocation hook of the C-HD program** (`L6.HookSpec`, the route's `hD` shape). -/
theorem dProSpecC (e : ℕ) (he : 32 ≤ e) (ps : List Stmt)
    (hsel : ps[1]? = some (SelectRAM.selBody SelectRAM.entLess 1)) :
    HookSpec e ps dProC
      (fun H src cn cm r => (∃ Ds : ℕ → BM.DStrM H src,
          DLI.DRI (G := H) (s := src) (dParC cn cm) r (LabRAM.H0 (G := H)) BM.DGl.init Ds
            (CostSkeleton.LF cn cm + 1)) ∧ r.w "ds.fresh" + r.w "blk.fresh" ≤ 2)
      dProWA dProVA dProWR [] (dKd (12 * kmN)) :=
  dProSpec e (by omega) ps (12 * kmN) (hCw_C he) hsel

/-- the full form (raw facts `DAlloc`, `use = 1`, the procedure-table fact) -/
theorem dProSpecC_full (e : ℕ) (he : 32 ≤ e) (ps : List Stmt)
    (hsel : ps[1]? = some (SelectRAM.selBody SelectRAM.entLess 1)) :
    HookSpec e ps dProC
      (fun H src cn cm r => DLI.DRI (G := H) (s := src) (dParC cn cm) r (LabRAM.H0 (G := H))
          BM.DGl.init (fun _ => BM.newC 0 ⊤) (CostSkeleton.LF cn cm + 1) ∧
        r.w "ds.fresh" + r.w "blk.fresh" = 1 ∧ DAlloc (12 * kmN) cn cm H src r ∧
        r.procs[1]? = some (SelectRAM.selBody SelectRAM.entLess 1))
      dProWA dProVA dProWR [] (dKd (12 * kmN)) :=
  dProSpec_full e (by omega) ps (12 * kmN) (hCw_C he) hsel

/-- **The route's `hPd`** (B-L2's persistent FindPivots state survives `dPro`): the footprint of
`PhiR` avoids `dPro`'s writes, for every cost-parameter family `P`. -/
theorem hPd_dPro (P : ℕ → ℕ → CostPar) : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ),
    (∀ a ∈ (PIfOf P H src cn cm).pWA, a ∉ dProWA) ∧ (∀ a ∈ (PIfOf P H src cn cm).pWR, a ∉ dProWR) :=
  fun _ _ _ _ => ⟨show ∀ a ∈ BL2.phWA, a ∉ dProWA by decide,
    show ∀ a ∈ BL2.phWR, a ∉ dProWR by decide⟩

end Frontier.CHD.DPro

#print axioms Frontier.CHD.DPro.dProSpecC
#print axioms Frontier.CHD.DPro.dProSpecC_full
#print axioms Frontier.CHD.DPro.dProC
#print axioms Frontier.CHD.DPro.hPd_dPro
