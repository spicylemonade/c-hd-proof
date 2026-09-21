import Frontier.CHD.SizeFacts

/-!
# Frontier.CHD.SizeParams — the closed form of the returned-set cap (tracker O12 (B3); owner agent-03)

**NON-GATE** (Layer A).  With the C-HD parameters `M_{l+1} = t · 2^{lt}` and `τ_l = t³ · 2^{lt}` (reviewer's master
theorem), `3k ≤ t` and `t ≥ 3`: `ucap l Sb ≤ 2 τ_l` for every `Sb ≤ 3k · M_{l+1}` (in particular for the root,
`Sb = |{s}| = 1`).  So every call at level `l` returns at most `2 t³ 2^{lt}` vertices ((B3) with `Λ_l = τ_l`).
-/

namespace Frontier
namespace CHD
namespace BM

theorem ucap_le {DC : DCost} {k t : ℕ} {τ : ℕ → ℕ} (hM : ∀ l, DC.M (l + 1) = t * 2 ^ (l * t))
    (hτ : ∀ l, τ l = t ^ 3 * 2 ^ (l * t)) (h3k : 3 * k ≤ t) (ht : 3 ≤ t) :
    ∀ l, ucap DC k τ l (3 * k * DC.M (l + 1)) ≤ 2 * τ l
  | 0 => by simp only [ucap]; omega
  | l + 1 => by
    have ih := ucap_le hM hτ h3k ht l
    simp only [ucap]
    rw [hτ l] at ih
    rw [hM (l + 1), hτ (l + 1)]
    set P := 2 ^ (l * t) with hP
    set P' := 2 ^ ((l + 1) * t) with hP'
    have hPP : P' = P * 2 ^ t := by rw [hP', hP, Nat.succ_mul, pow_add]
    have h8 : 8 ≤ 2 ^ t := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht
    have hA1 : 3 * (k * (3 * k * (t * P'))) ≤ t ^ 3 * P' := by
      have hkk : 3 * k * (3 * k) ≤ t * t := Nat.mul_le_mul h3k h3k
      calc 3 * (k * (3 * k * (t * P'))) = (3 * k * (3 * k)) * (t * P') := by ring
        _ ≤ (t * t) * (t * P') := Nat.mul_le_mul_right _ hkk
        _ = t ^ 3 * P' := by ring
    have hA2 : 8 * (t ^ 3 * P) ≤ t ^ 3 * P' := by
      rw [hPP]
      calc 8 * (t ^ 3 * P) = t ^ 3 * P * 8 := by ring
        _ ≤ t ^ 3 * P * 2 ^ t := Nat.mul_le_mul_left _ h8
        _ = t ^ 3 * (P * 2 ^ t) := by ring
    omega

/-- **(B3) closed form**: a call at level `l` with `|S| ≤ 3k · M_{l+1}` returns at most `2 τ_l` vertices. -/
theorem ucap_le_of {DC : DCost} {k t : ℕ} {τ : ℕ → ℕ} (hM : ∀ l, DC.M (l + 1) = t * 2 ^ (l * t))
    (hτ : ∀ l, τ l = t ^ 3 * 2 ^ (l * t)) (h3k : 3 * k ≤ t) (ht : 3 ≤ t) (l : ℕ) {Sb : ℕ}
    (hSb : Sb ≤ 3 * k * DC.M (l + 1)) : ucap DC k τ l Sb ≤ 2 * τ l :=
  (ucap_mono l hSb).trans (ucap_le hM hτ h3k ht l)

end BM
end CHD
end Frontier
