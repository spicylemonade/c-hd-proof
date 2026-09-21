import Frontier.CHD.BMTele

/-!
# Frontier.CHD.BMTeleParams — the insertion bound in terms of the budget ratio (owner: agent-01)

**NON-GATE** (Layer A, arithmetic).  For block parameter `M ≥ 1` and a placement budget `E ≤ ρ·M`,
the amortized insertion bound of `BMTele` satisfies

  `insBound M (2M + 2E) ≤ 211 · log₂ (8ρ + 8) + 441`,

so `DC.ins l := insBound (M_l) (2M_l + 2·Emax_l)` is `O(log(Emax_l / M_l) + 1)` (checklist I13).
-/

namespace Frontier
namespace CHD
namespace BM

/-- Dividing by the small-block threshold costs at most a factor `5` over dividing by `M`. -/
theorem div_thr_le {M E ρ : ℕ} (hM : 1 ≤ M) (hE : E ≤ ρ * M) :
    (M + E) / DL.thr M ≤ 5 + 5 * ρ := by
  by_cases h3 : M ≤ 2
  · have ht : DL.thr M = 1 := by unfold DL.thr; omega
    rw [ht, Nat.div_one]
    have : ρ * M ≤ ρ * 2 := Nat.mul_le_mul_left ρ h3
    omega
  · have ht : DL.thr M = M / 3 := by unfold DL.thr; omega
    rw [ht]
    apply Nat.div_le_of_le_mul
    have h5 : M ≤ 5 * (M / 3) := by omega
    have hA : M + E ≤ (1 + ρ) * M := by rw [Nat.add_mul, Nat.one_mul]; omega
    calc M + E ≤ (1 + ρ) * M := hA
      _ ≤ (1 + ρ) * (5 * (M / 3)) := Nat.mul_le_mul_left _ h5
      _ = M / 3 * (5 + 5 * ρ) := by ring

/-- **The insertion bound is logarithmic in the budget ratio.** -/
theorem insBound_le {M E ρ : ℕ} (hM : 1 ≤ M) (hE : E ≤ ρ * M) :
    insBound M (2 * M + 2 * E) ≤ 211 * Nat.log 2 (8 * ρ + 8) + 441 := by
  have hP2 : (2 * M + 2 * E) / 2 = M + E := by omega
  have hPM : (2 * M + 2 * E) / M ≤ 2 + 2 * ρ := by
    apply Nat.div_le_of_le_mul
    have : 2 * E ≤ 2 * (ρ * M) := Nat.mul_le_mul_left 2 hE
    calc 2 * M + 2 * E ≤ 2 * M + 2 * (ρ * M) := by omega
      _ = M * (2 + 2 * ρ) := by ring
  have hT := div_thr_le hM hE
  have hB : (2 * M + 2 * E) / M + (M + E) / DL.thr M ≤ 8 * ρ + 8 := by omega
  have hEll : (M + E + 1) / M ≤ 8 * ρ + 8 := by
    apply Nat.div_le_of_le_mul
    have : ρ * M ≤ M * (8 * ρ) := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left M (by omega)
    calc M + E + 1 ≤ M + ρ * M + M := by omega
      _ ≤ M * (8 * ρ + 8) := by nlinarith
  unfold insBound DL.bsCost DL.ell
  rw [hP2]
  have h1 : Nat.log 2 ((2 * M + 2 * E) / M + (M + E) / DL.thr M) ≤ Nat.log 2 (8 * ρ + 8) :=
    Nat.log_mono_right hB
  have h2 : Nat.log 2 ((M + E + 1) / M) ≤ Nat.log 2 (8 * ρ + 8) := Nat.log_mono_right hEll
  omega

end BM
end CHD
end Frontier
