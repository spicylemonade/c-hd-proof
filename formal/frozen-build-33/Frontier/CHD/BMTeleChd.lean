import Frontier.CHD.BMTeleParams

/-!
# Frontier.CHD.BMTeleChd — the C-HD instance of the telescoping parameters (owner: agent-01)

**NON-GATE** (Layer A, parameters).  The block sizes `M_0 = 1`, `M_{l+1} = t·2^{lt}`, the workload
caps `τ_l = t³·2^{lt}` (reviewer's master theorem), the subtree placement budgets
* `Emax 0 = 3kt + δt³` (a base call: `|S| ≤ 3k·M_1`, `|U| ≤ τ_0`, `δ` out-edges per vertex),
* `Emax (l+1) = (3(L0+1) + 3δ) · 2τ_{l+1}` (agent-03's (B4′) with `|U| ≤ 2τ_l`),

and the amortized DLazy cost parameters `chdDC` over a heap base `DCb`.  Proved: the hypotheses of
`BMTeleLoop.bmsspDL_tele_top'` for `chdDC`, and the uniform insertion bound
`chdDC.ins (l+1) ≤ 211·log₂(8ρ + 8) + 441` with `ρ = (3(L0+1)+3δ)·2t²·2^t` (checklist I13).
-/

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-- The C-HD block sizes: `M_0 = 1`, `M_{l+1} = t·2^{lt}`. -/
def chdM (t : ℕ) : ℕ → ℕ
  | 0 => 1
  | l + 1 => t * 2 ^ (l * t)

/-- The C-HD workload caps `τ_l = t³·2^{lt}`. -/
def chdTau (t l : ℕ) : ℕ := t ^ 3 * 2 ^ (l * t)

/-- The subtree placement budgets of the C-HD run. -/
def chdEmax (t k δ L0 : ℕ) : ℕ → ℕ
  | 0 => 3 * k * t + δ * t ^ 3
  | l + 1 => (3 * (L0 + 1) + 3 * δ) * (2 * chdTau t (l + 1))

/-- The per-level insertion charge. -/
noncomputable def chdIns (t k δ L0 l : ℕ) : ℕ :=
  insBound (chdM t l) (2 * chdM t l + 2 * chdEmax t k δ L0 l)

/-- **The amortized DLazy cost parameters of the C-HD run** over a heap base `DCb`. -/
noncomputable def chdDC (t k δ L0 : ℕ) (DCb : DCost) : DCost where
  M := chdM t
  new := fun _ => 3
  ins := chdIns t k δ L0
  del := fun _ x => 5 * x + 1
  pull := fun _ x => 735 * x + 950
  merge := fun _ _ => 14
  bins := DCb.bins + chdIns t k δ L0 0 + 3
  bext := DCb.bext

theorem chdM_pos {t : ℕ} (ht : 1 ≤ t) : ∀ l, 1 ≤ chdM t l
  | 0 => le_rfl
  | l + 1 => by
    show 1 ≤ t * 2 ^ (l * t)
    have : 1 ≤ 2 ^ (l * t) := Nat.one_le_two_pow
    nlinarith

theorem chdM_three {t : ℕ} (ht : 3 ≤ t) : ∀ l, 3 * chdM t l ≤ chdM t (l + 1)
  | 0 => by show 3 * 1 ≤ t * 2 ^ (0 * t); simp; omega
  | l + 1 => by
    show 3 * (t * 2 ^ (l * t)) ≤ t * 2 ^ ((l + 1) * t)
    have h8 : 3 ≤ 2 ^ t := by
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e : 2 ^ ((l + 1) * t) = 2 ^ (l * t) * 2 ^ t := by rw [Nat.succ_mul, pow_add]
    rw [e]
    calc 3 * (t * 2 ^ (l * t)) = t * 2 ^ (l * t) * 3 := by ring
      _ ≤ t * 2 ^ (l * t) * 2 ^ t := Nat.mul_le_mul_left _ h8
      _ = t * (2 ^ (l * t) * 2 ^ t) := by ring

/-- The insertion hypothesis of the telescoping for `chdDC`. -/
theorem chdDC_ins {t k δ L0 : ℕ} {DCb : DCost} (ht : 1 ≤ t) :
    ∀ l, ∀ D : DStrM G s, D.M = chdM t l → DL.psi D ≤ 2 * chdM t l + 2 * chdEmax t k δ L0 l →
      insCharge D ≤ (chdDC t k δ L0 DCb).ins l := by
  intro l D hM hP
  have hM1 : 1 ≤ D.M := hM ▸ chdM_pos ht l
  have := insCharge_le hP hM1
  rw [hM] at this
  exact this

/-- The budget ratio of the recursive levels. -/
def chdRho (t δ L0 : ℕ) : ℕ := (3 * (L0 + 1) + 3 * δ) * (2 * t ^ 2 * 2 ^ t)

theorem chdEmax_le {t k δ L0 : ℕ} (l : ℕ) :
    chdEmax t k δ L0 (l + 1) ≤ chdRho t δ L0 * chdM t (l + 1) := by
  show (3 * (L0 + 1) + 3 * δ) * (2 * (t ^ 3 * 2 ^ ((l + 1) * t))) ≤
    (3 * (L0 + 1) + 3 * δ) * (2 * t ^ 2 * 2 ^ t) * (t * 2 ^ (l * t))
  have e : 2 ^ ((l + 1) * t) = 2 ^ (l * t) * 2 ^ t := by rw [Nat.succ_mul, pow_add]
  rw [e]
  apply le_of_eq
  ring

/-- **The uniform insertion bound of the recursive levels** (checklist I13). -/
theorem chdIns_le {t k δ L0 : ℕ} (ht : 1 ≤ t) (l : ℕ) :
    chdIns t k δ L0 (l + 1) ≤ 211 * Nat.log 2 (8 * chdRho t δ L0 + 8) + 441 :=
  insBound_le (chdM_pos ht (l + 1)) (chdEmax_le l)

/-- The insertion bound of the base level (the level-0 conversion charge, `M_0 = 1`). -/
theorem chdIns_zero_le {t k δ L0 : ℕ} :
    chdIns t k δ L0 0 ≤ 211 * Nat.log 2 (8 * (3 * k * t + δ * t ^ 3) + 8) + 441 :=
  insBound_le (M := 1) (E := 3 * k * t + δ * t ^ 3) le_rfl (by simp)

end BM
end CHD
end Frontier
