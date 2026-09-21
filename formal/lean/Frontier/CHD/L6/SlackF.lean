import Frontier.CHD.L6.DCap
import Frontier.CHD.SpinePost
import Frontier.CHD.RamBodyFinB

/-!
# The final budget slack of the C-HD instance (agent-10)

`SlfC K C cn cm = baseReq cn cm + stepReq K C cn cm`: the look-ahead slack every level contract
carries.  It dominates
* the base case's `baseBud + 112` (`baseReq`, `L6.Assembly.callSpec_base`),
* the finalization's `finCst H K NB + 2` (agent-01's `finB_of_finSpec` / `callSpec_succ.hSl`),
* the second half's `postS K C n m (2·NB)` (agent-08's `loopSpecB_of_postSpec.hSl`),
for every graph with `H.n ≤ 2cn`, `H.m ≤ 2cm` and the D-layer block bound `NB = ucap` of the
instance (`12·kmN·Tnat + 2`); and it is polynomial: `SlfC ≤ (10^9 + 64·(K+C+1)^4·10^56) · (cn+cm+2)^8`.
NON-GATE (arithmetic).
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.CHD Frontier.CHD.RamSpine

/-- The D layer's block bound of the instance (`DPro.dParC`'s `ucap`). -/
def nbF (cn cm : ℕ) : ℕ := 12 * kmN * CostSkeleton.Tnat cn cm + 2

/-- The step's static slack: the finalization's `finCst + 2` plus the second half's `postS`. -/
def stepReq (K C cn cm : ℕ) : ℕ :=
  (K * ((2 * cn) * (Nat.log 2 (nbF cn cm) + 4)) +
    (2 * cn + 1) * ((2 * cm + 1) * WinScan.CED K (nbF cn cm) + 101) + 2) +
  RamSpine.postS K C (2 * cn) (2 * cm) (2 * nbF cn cm)

/-- **The final slack.** -/
def SlfC (K C cn cm : ℕ) : ℕ := baseReq cn cm + stepReq K C cn cm

theorem baseReq_le_SlfC (K C cn cm : ℕ) : baseReq cn cm ≤ SlfC K C cn cm := Nat.le_add_right _ _

theorem finCst_le_SlfC {G : Graph} (K C cn cm : ℕ) (hn : G.n ≤ 2 * cn) (hm : G.m ≤ 2 * cm) :
    RamBody.finCst G K (nbF cn cm) + 2 ≤ SlfC K C cn cm := by
  unfold SlfC stepReq RamBody.finCst
  have h1 : K * (G.n * (Nat.log 2 (nbF cn cm) + 4)) ≤ K * ((2 * cn) * (Nat.log 2 (nbF cn cm) + 4)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hn)
  have h2 : (G.n + 1) * ((G.m + 1) * WinScan.CED K (nbF cn cm) + 101) ≤
      (2 * cn + 1) * ((2 * cm + 1) * WinScan.CED K (nbF cn cm) + 101) :=
    Nat.mul_le_mul (by omega) (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _)
  omega

theorem postS_mono_nm (K C : ℕ) {n n' m m' : ℕ} (nb : ℕ) (hn : n ≤ n') (hm : m ≤ m') :
    RamSpine.postS K C n m nb ≤ RamSpine.postS K C n' m' nb := by
  unfold RamSpine.postS
  have h1 : (n + 1) * ((m + 1) * WinScan.CED K nb + 101) ≤ (n' + 1) * ((m' + 1) * WinScan.CED K nb + 101) :=
    Nat.mul_le_mul (by omega) (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _)
  have h2 : 8 * n ≤ 8 * n' := Nat.mul_le_mul_left _ hn
  have h3 : n * (C + 8) ≤ n' * (C + 8) := Nat.mul_le_mul_right _ hn
  have h4 : K * (n * (Nat.log 2 nb + 4)) ≤ K * (n' * (Nat.log 2 nb + 4)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hn)
  have h5 : n * (K + 3) ≤ n' * (K + 3) := Nat.mul_le_mul_right _ hn
  omega

theorem postS_le_SlfC {G : Graph} (K C cn cm : ℕ) (hn : G.n ≤ 2 * cn) (hm : G.m ≤ 2 * cm) :
    RamSpine.postS K C G.n G.m (2 * nbF cn cm) ≤ SlfC K C cn cm := by
  have := postS_mono_nm K C (2 * nbF cn cm) hn hm
  unfold SlfC stepReq
  omega

/-! ## The slack is polynomial -/

theorem nbF_le (cn cm : ℕ) : nbF cn cm ≤ 3 * 10 ^ 13 * (cn + cm + 2) ^ 2 := by
  have hT := Tnat_le_X2 cn cm
  have hk := kmN_le
  unfold nbF
  have h1 : 12 * kmN * CostSkeleton.Tnat cn cm ≤ 12 * 10 ^ 11 * (22 * (cn + cm + 2) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hk) hT
  have h2 : 1 ≤ (cn + cm + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  nlinarith

/-- The atom bound: every factor of `stepReq` is at most `Z = (K+C+1)·10^14·(cn+cm+2)^2`. -/
def Zs (K C cn cm : ℕ) : ℕ := (K + C + 1) * (10 ^ 14 * (cn + cm + 2) ^ 2)

theorem pow4_facts (Z : ℕ) (hZ1 : 1 ≤ Z) :
    Z ≤ Z ^ 4 ∧ Z * Z ≤ Z ^ 4 ∧ Z * (Z * Z) ≤ Z ^ 4 ∧ Z * (Z * (Z + Z * Z) + Z) ≤ 3 * Z ^ 4 ∧
      Z * (Z + 8) ≤ 9 * Z ^ 4 ∧ Z * (Z + 3) ≤ 4 * Z ^ 4 := by
  have a1 : Z ^ 1 ≤ Z ^ 4 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have a2 : Z ^ 2 ≤ Z ^ 4 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have a3 : Z ^ 3 ≤ Z ^ 4 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have e1 : Z = Z ^ 1 := (pow_one Z).symm
  have e2 : Z * Z = Z ^ 2 := by ring
  have e3 : Z * (Z * Z) = Z ^ 3 := by ring
  have e4 : Z * (Z * (Z + Z * Z) + Z) = Z ^ 3 + Z ^ 4 + Z ^ 2 := by ring
  have e5 : Z * (Z + 8) = Z ^ 2 + 8 * Z ^ 1 := by ring
  have e6 : Z * (Z + 3) = Z ^ 2 + 3 * Z ^ 1 := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc Z = Z ^ 1 := (pow_one Z).symm
      _ ≤ Z ^ 4 := a1
  · rw [e2]; exact a2
  · rw [e3]; exact a3
  · rw [e4]; omega
  · rw [e5]; omega
  · rw [e6]; omega

set_option maxHeartbeats 1000000 in
theorem stepReq_le (K C cn cm : ℕ) : stepReq K C cn cm ≤ 64 * Zs K C cn cm ^ 4 := by
  obtain ⟨X, hX⟩ : ∃ X, X = cn + cm + 2 := ⟨_, rfl⟩
  have hX2 : 2 ≤ X := by omega
  have hNB := nbF_le cn cm
  rw [← hX] at hNB
  obtain ⟨N, hN⟩ : ∃ N, N = nbF cn cm := ⟨_, rfl⟩
  rw [← hN] at hNB
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = Zs K C cn cm := ⟨_, rfl⟩
  have hX4 : 4 ≤ X ^ 2 := by nlinarith
  have hQ : 4 * 10 ^ 14 ≤ 10 ^ 14 * X ^ 2 := by nlinarith
  have hZQ : 10 ^ 14 * X ^ 2 ≤ Z := by
    rw [hZ]; unfold Zs; rw [← hX]; nlinarith
  have hZK : K ≤ Z := by
    rw [hZ]; unfold Zs; rw [← hX]
    have : 1 ≤ 10 ^ 14 * X ^ 2 := by omega
    nlinarith
  have hZC : C ≤ Z := by
    rw [hZ]; unfold Zs; rw [← hX]
    have : 1 ≤ 10 ^ 14 * X ^ 2 := by omega
    nlinarith
  have hXX : X ≤ X ^ 2 := by nlinarith
  have hn : 2 * cn + 1 ≤ Z := by omega
  have hm : 2 * cm + 1 ≤ Z := by omega
  have hlog : Nat.log 2 N ≤ N := Nat.log_le_self 2 N
  have hlog2 : Nat.log 2 (2 * N) ≤ 2 * N := Nat.log_le_self 2 _
  have hl1 : Nat.log 2 N + 5 ≤ Z := by omega
  have hl2 : Nat.log 2 (2 * N) + 5 ≤ Z := by omega
  have h113 : 113 ≤ Z := by omega
  have hZ1 : 1 ≤ Z := by omega
  unfold stepReq RamSpine.postS WinScan.CED
  rw [← hN]
  -- the terms, each by monotonicity
  have t1 : K * ((2 * cn) * (Nat.log 2 N + 4)) ≤ Z * (Z * Z) := by
    apply Nat.mul_le_mul hZK; apply Nat.mul_le_mul <;> omega
  have c1 : 113 + K * (Nat.log 2 N + 5) ≤ Z + Z * Z := by
    have := Nat.mul_le_mul hZK hl1; omega
  have c2 : 113 + K * (Nat.log 2 (2 * N) + 5) ≤ Z + Z * Z := by
    have := Nat.mul_le_mul hZK hl2; omega
  have t2 : (2 * cn + 1) * ((2 * cm + 1) * (113 + K * (Nat.log 2 N + 5)) + 101) ≤
      Z * (Z * (Z + Z * Z) + Z) := by
    apply Nat.mul_le_mul hn
    have := Nat.mul_le_mul hm c1; omega
  have t3 : (2 * cn + 1) * ((2 * cm + 1) * (113 + K * (Nat.log 2 (2 * N) + 5)) + 101) ≤
      Z * (Z * (Z + Z * Z) + Z) := by
    apply Nat.mul_le_mul hn
    have := Nat.mul_le_mul hm c2; omega
  have t4 : 8 * (2 * cn) ≤ 8 * Z := by omega
  have t5 : (2 * cn) * (C + 8) ≤ Z * (Z + 8) := Nat.mul_le_mul (by omega) (by omega)
  have t6 : K * ((2 * cn) * (Nat.log 2 (2 * N) + 4)) ≤ Z * (Z * Z) := by
    apply Nat.mul_le_mul hZK; apply Nat.mul_le_mul <;> omega
  have t7 : (2 * cn) * (K + 3) ≤ Z * (Z + 3) := Nat.mul_le_mul (by omega) (by omega)
  -- collect: everything is at most a multiple of Z^4
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := pow4_facts Z hZ1
  have hZ4 : Z ^ 4 = Zs K C cn cm ^ 4 := by rw [hZ]
  rw [← hZ4]
  omega

theorem Zs_pow (K C cn cm : ℕ) :
    Zs K C cn cm ^ 4 = (K + C + 1) ^ 4 * 10 ^ 56 * (cn + cm + 2) ^ 8 := by
  unfold Zs; ring

theorem SlfC_le (K C cn cm : ℕ) :
    SlfC K C cn cm ≤ (10 ^ 9 + 64 * (K + C + 1) ^ 4 * 10 ^ 56) * (cn + cm + 2) ^ 8 := by
  have h1 := baseReq_le cn cm
  have h2 := stepReq_le K C cn cm
  rw [Zs_pow] at h2
  have h58 : (cn + cm + 2) ^ 5 ≤ (cn + cm + 2) ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
  unfold SlfC
  have h3 : 10 ^ 9 * (cn + cm + 2) ^ 5 ≤ 10 ^ 9 * (cn + cm + 2) ^ 8 := Nat.mul_le_mul_left _ h58
  calc baseReq cn cm + stepReq K C cn cm
      ≤ 10 ^ 9 * (cn + cm + 2) ^ 8 + 64 * ((K + C + 1) ^ 4 * 10 ^ 56 * (cn + cm + 2) ^ 8) := by omega
    _ = (10 ^ 9 + 64 * (K + C + 1) ^ 4 * 10 ^ 56) * (cn + cm + 2) ^ 8 := by ring

end Frontier.CHD.L6

#print axioms Frontier.CHD.L6.finCst_le_SlfC
#print axioms Frontier.CHD.L6.postS_le_SlfC
#print axioms Frontier.CHD.L6.SlfC_le
