import Frontier.CHD.L6.CoreSpecProof
import Frontier.CHD.BaseCostDeg

/-!
# Word-capacity facts for the per-level tables (agent-10)

`tau_M_cap`: from the core's word capacity `(cn+cm+2)^(e+1) ≤ cap` with `e ≥ 32`, every per-level
value fits in a word with room: `chdTau tF l + 2 < cap` for `l ≤ LF` and `chdM tF l + 2 < cap` for
`l ≤ LF + 1`.  (For the spine's `Static.tauCap` / `Static.MCap`.)  NON-GATE (arithmetic).
-/

namespace Frontier.CHD.L6

theorem tau_M_cap (cn cm e cap : ℕ) (hcn : 1 ≤ cn) (hcm : 1 ≤ cm) (he : 32 ≤ e)
    (hcap : (cn + cm + 2) ^ (e + 1) ≤ cap) :
    (∀ l ≤ CostSkeleton.LF cn cm, BM.chdTau (CostSkeleton.tF cn cm) l + 2 < cap) ∧
    (∀ l ≤ CostSkeleton.LF cn cm + 1, BM.chdM (CostSkeleton.tF cn cm) l + 2 < cap) := by
  have hL := levelTab_cap cn cm e cap hcn hcm he hcap
  have hT1 : 1 ≤ CostSkeleton.tF cn cm := le_trans (by norm_num) (CostSkeleton.sixteen_le_tF cn cm)
  generalize CostSkeleton.tF cn cm = T at hL hT1 ⊢
  generalize CostSkeleton.LF cn cm = L at hL ⊢
  have hbig : T * T * T * 2 ^ ((L + 1) * T) + 2 < cap := by
    have h5 : T * T * T * 2 ^ ((L + 1) * T) + 2 ≤
        T * T * T * 2 ^ ((L + 1) * T) + 2 ^ (T + 1) + L + T + 5 := by
      generalize T * T * T * 2 ^ ((L + 1) * T) = A
      generalize 2 ^ (T + 1) = P
      omega
    exact lt_of_le_of_lt h5 hL
  refine ⟨fun l hl => ?_, fun l hl => ?_⟩
  · have h1 : 2 ^ (l * T) ≤ 2 ^ ((L + 1) * T) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega))
    have h2 : BM.chdTau T l ≤ T * T * T * 2 ^ ((L + 1) * T) := by
      show T ^ 3 * 2 ^ (l * T) ≤ _
      have : T ^ 3 = T * T * T := by ring
      rw [this]; exact Nat.mul_le_mul_left _ h1
    generalize T * T * T * 2 ^ ((L + 1) * T) = A at h2 hbig
    omega
  · cases l with
    | zero =>
      show 1 + 2 < cap
      have h1 : 1 ≤ T * T * T * 2 ^ ((L + 1) * T) := by
        have hTTT : 1 ≤ T * T * T := Nat.one_le_iff_ne_zero.mpr (by positivity)
        have hP : 1 ≤ 2 ^ ((L + 1) * T) := Nat.one_le_two_pow
        calc 1 = 1 * 1 := by norm_num
          _ ≤ T * T * T * 2 ^ ((L + 1) * T) := Nat.mul_le_mul hTTT hP
      generalize T * T * T * 2 ^ ((L + 1) * T) = A at h1 hbig
      omega
    | succ l =>
      have h1 : 2 ^ (l * T) ≤ 2 ^ ((L + 1) * T) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega))
      have hTT : T ≤ T * T * T := by nlinarith
      have h2 : BM.chdM T (l + 1) ≤ T * T * T * 2 ^ ((L + 1) * T) := by
        show T * 2 ^ (l * T) ≤ _
        exact Nat.mul_le_mul hTT h1
      generalize T * T * T * 2 ^ ((L + 1) * T) = A at h2 hbig
      omega

/-- **Doubled level parameter fits** (for the D layer's split guard `2·M + 1` and `new_spec`'s
`2·M + 2 < cap`): `2 · chdM tF l + 2 < cap` for `l ≤ LF + 1`, from the core's word capacity. -/
theorem chdM_two_cap (cn cm e cap : ℕ) (hcn : 1 ≤ cn) (hcm : 1 ≤ cm) (he : 32 ≤ e)
    (hcap : (cn + cm + 2) ^ (e + 1) ≤ cap) :
    ∀ l ≤ CostSkeleton.LF cn cm + 1, 2 * BM.chdM (CostSkeleton.tF cn cm) l + 2 < cap := by
  have hL := levelTab_cap cn cm e cap hcn hcm he hcap
  have hT16 : 16 ≤ CostSkeleton.tF cn cm := CostSkeleton.sixteen_le_tF cn cm
  generalize CostSkeleton.tF cn cm = T at hL hT16 ⊢
  generalize CostSkeleton.LF cn cm = L at hL ⊢
  have hbig : T * T * T * 2 ^ ((L + 1) * T) + 5 < cap := by
    have h5 : T * T * T * 2 ^ ((L + 1) * T) + 5 ≤
        T * T * T * 2 ^ ((L + 1) * T) + 2 ^ (T + 1) + L + T + 5 := by
      generalize T * T * T * 2 ^ ((L + 1) * T) = A
      generalize 2 ^ (T + 1) = P
      omega
    exact lt_of_le_of_lt h5 hL
  intro l hl
  cases l with
  | zero =>
    show 2 * 1 + 2 < cap
    have h1 : 1 ≤ T * T * T * 2 ^ ((L + 1) * T) := by
      have hTTT : 1 ≤ T * T * T := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have hP : 1 ≤ 2 ^ ((L + 1) * T) := Nat.one_le_two_pow
      calc 1 = 1 * 1 := by norm_num
        _ ≤ T * T * T * 2 ^ ((L + 1) * T) := Nat.mul_le_mul hTTT hP
    generalize T * T * T * 2 ^ ((L + 1) * T) = A at h1 hbig
    omega
  | succ l =>
    have h1 : 2 ^ (l * T) ≤ 2 ^ ((L + 1) * T) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega))
    have hTT : 2 * T ≤ T * T * T := by nlinarith
    have h2 : 2 * BM.chdM T (l + 1) ≤ T * T * T * 2 ^ ((L + 1) * T) := by
      show 2 * (T * 2 ^ (l * T)) ≤ _
      rw [← mul_assoc]
      exact Nat.mul_le_mul hTT h1
    generalize T * T * T * 2 ^ ((L + 1) * T) = A at h2 hbig
    omega

/-- `MasterIn`'s degree bound in the `BM.outdeg` form used by the base case (`callSpec_zero.hdeg`). -/
theorem outdeg_le_of_masterIn {H : Graph} {src : Fin H.n} {cn cm : ℕ} (h : MasterIn H src cn cm)
    (u : Fin H.n) : BM.outdeg (G := H) u ≤ 5 * CostSkeleton.dd cn cm := by
  have e : BM.outdeg (G := H) u = (BM.Eout H {u}).card := by
    unfold BM.outdeg BM.Eout
    congr 1
    ext e
    simp
  rw [e]
  exact h.deg u

end Frontier.CHD.L6

#print axioms Frontier.CHD.L6.tau_M_cap
#print axioms Frontier.CHD.L6.chdM_two_cap
