import Frontier.CHD.L6.TopGlue
import Frontier.CHD.L6.MasterGlue
import Frontier.CHD.L6.TauCap
import Frontier.CHD.L6.Tnat
import Frontier.CHD.L6.ProMain

/-!
# The D-layer capacity of the C-HD run (agent-10)

* `kmN`: the master constant `kmaster 1 1 1000` as an ℕ literal (`kmaster_eq`); `kmN ≤ 10^11`.
* `ucap_cover` / `hucap_of`: an instance capacity `12·kmN·Tnat cn cm + 2 ≤ DL.ucap` covers the
  post-prologue use (`≤ 2`) plus the doubled master bound `2·kmaster·Tchd` of every top-level run
  (the route's `hucap`).  So the prologue allocates `ucap := 12·kmN·pr.tn + 2` (O(Tnat) cells).
* `cbig_of_cap`: the D layer's combined word-capacity fact
  `(LF+3)·(n+2) + 2·ecap + 300 < cap` for `ecap ≤ 12·kmN·Tnat + 100`, `n ≤ 2 cn`, from the core's
  word capacity `(cn+cm+2)^(e+1) ≤ cap`, `e ≥ 32` (agent-05's DLens `cbig`).
NON-GATE (arithmetic).
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM Frontier.CHD

/-- The master constant as an ℕ literal (`kmaster 1 1 1000 = kmN`). -/
def kmN : ℕ := 5100 * BM.cMaster (2 * (CHD.scanC + 1) + 1 + 2) 1000 * 56

theorem kmaster_eq : kmaster 1 1 1000 = (kmN : ℝ) := by
  unfold kmaster kmN; push_cast; ring

theorem kmN_le : kmN ≤ 10 ^ 11 := by
  unfold kmN BM.cMaster BM.cValid CHD.scanC; norm_num

theorem tF_le_X (cn cm : ℕ) : CostSkeleton.tF cn cm ≤ 17 * (cn + cm + 2) := by
  have h1 := CostSkeleton.tF_le cn cm
  have h2 : CostSkeleton.lgN cn ≤ cn + 1 := by
    unfold CostSkeleton.lgN; exact max_le (by omega) (by have := Nat.log_le_self 2 cn; omega)
  omega

theorem dd_le_X (cn cm : ℕ) : CostSkeleton.dd cn cm ≤ cn + cm + 2 := by
  unfold CostSkeleton.dd; have := Nat.div_le_self cm cn; omega

theorem Tnat_le_X2 (cn cm : ℕ) : CostSkeleton.Tnat cn cm ≤ 22 * (cn + cm + 2) ^ 2 := by
  have ht := tF_le_X cn cm
  have hd := dd_le_X cn cm
  have hl : Nat.log 2 (CostSkeleton.dd cn cm + 1) ≤ CostSkeleton.dd cn cm + 1 := Nat.log_le_self 2 _
  unfold CostSkeleton.Tnat
  obtain ⟨X, hX⟩ : ∃ X, X = cn + cm + 2 := ⟨_, rfl⟩
  rw [← hX] at ht hd ⊢
  have hm : cm ≤ X := by omega
  have hn : cn ≤ X := by omega
  have h1 : CostSkeleton.tF cn cm + Nat.log 2 (CostSkeleton.dd cn cm + 1) + 3 ≤ 21 * X := by omega
  have h2 : cm * (CostSkeleton.tF cn cm + Nat.log 2 (CostSkeleton.dd cn cm + 1) + 3) ≤ X * (21 * X) :=
    Nat.mul_le_mul hm h1
  nlinarith

/-- The D capacity the prologue must allocate. -/
theorem ucap_cover (cn cm : ℕ) (hn : 1 ≤ cn) (hm : 1 ≤ cm) (hnm : cn ≤ cm + 1) :
    2 + 2 * (kmaster 1 1 1000 * GateCCalc.Tchd cn cm) ≤
      ((12 * kmN * CostSkeleton.Tnat cn cm + 2 : ℕ) : ℝ) := by
  have h := CostSkeleton.Tchd_le_Tnat cn cm hn hm hnm
  rw [kmaster_eq]
  have hk : (0 : ℝ) ≤ kmN := Nat.cast_nonneg _
  push_cast
  nlinarith

/-- The route's capacity hypothesis `hucap` from the instance's capacity. -/
theorem hucap_of {DLf : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), RamSpine.DLayer H src Tz}
    (hucapF : ∀ H src cn cm, 12 * kmN * CostSkeleton.Tnat cn cm + 2 ≤ (DLf H src cn cm).ucap)
    (H : Graph) (src : Fin H.n) (cn cm : ℕ) (hMI : MasterIn H src cn cm) :
    2 + 2 * (kmaster 1 1 1000 * GateCCalc.Tchd cn cm) ≤ ((DLf H src cn cm).ucap : ℝ) :=
  (ucap_cover cn cm hMI.cn_pos hMI.cm_pos hMI.cn_le).trans (by exact_mod_cast hucapF H src cn cm)

/-- **The D layer's combined word-capacity fact** (agent-05's DLens `cbig`). -/
theorem cbig_of_cap (cn cm e cap : ℕ) (hcn : 1 ≤ cn) (hcm : 1 ≤ cm) (he : 32 ≤ e)
    (hcap : (cn + cm + 2) ^ (e + 1) ≤ cap) (n ecap : ℕ) (hn : n ≤ 2 * cn)
    (hec : ecap ≤ 12 * kmN * CostSkeleton.Tnat cn cm + 100) :
    (CostSkeleton.LF cn cm + 1 + 2) * (n + 2) + 2 * ecap + 300 < cap := by
  obtain ⟨X, hX⟩ : ∃ X, X = cn + cm + 2 := ⟨_, rfl⟩
  have hX4 : 4 ≤ X := by omega
  have hL := LF_le cn cm hcn
  have hT := Tnat_le_X2 cn cm
  have hk := kmN_le
  rw [← hX] at hT hcap
  -- the pieces, each at most a constant times X^2
  have p1 : (CostSkeleton.LF cn cm + 1 + 2) * (n + 2) ≤ (2 * X) * (2 * X) :=
    Nat.mul_le_mul (by omega) (by omega)
  have p2 : 12 * kmN * CostSkeleton.Tnat cn cm ≤ 12 * 10 ^ 11 * (22 * X ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hk) hT
  have hX2 : 16 ≤ X ^ 2 := by nlinarith
  have hsum : (CostSkeleton.LF cn cm + 1 + 2) * (n + 2) + 2 * ecap + 300 ≤ 10 ^ 15 * X ^ 2 := by
    nlinarith
  -- X^(e+1) ≥ X^33 = X^31 · X^2 ≥ 4^31 · X^2 > 10^15 · X^2
  have h31 : 4 ^ 31 ≤ X ^ 31 := Nat.pow_le_pow_left hX4 31
  have h33 : X ^ 33 ≤ X ^ (e + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hsplit : X ^ 33 = X ^ 31 * X ^ 2 := by ring
  have hc : (10 : ℕ) ^ 15 < 4 ^ 31 := by norm_num
  have hX2pos : 0 < X ^ 2 := by positivity
  have hlt : 10 ^ 15 * X ^ 2 < X ^ 31 * X ^ 2 :=
    Nat.mul_lt_mul_of_pos_right (lt_of_lt_of_le hc h31) hX2pos
  calc (CostSkeleton.LF cn cm + 1 + 2) * (n + 2) + 2 * ecap + 300 ≤ 10 ^ 15 * X ^ 2 := hsum
    _ < X ^ 31 * X ^ 2 := hlt
    _ = X ^ 33 := hsplit.symm
    _ ≤ X ^ (e + 1) := h33
    _ ≤ cap := hcap

/-! ## The cost parameters of the C-HD run (moved from Assembly) -/

/-- Frontier-size bound per level. -/
def SbF (cn cm l : ℕ) : ℕ := 3 * CostSkeleton.kF cn cm * BM.chdM (CostSkeleton.tF cn cm) (l + 1)

/-- Base-case heap size bound. -/
def KhF (cn cm : ℕ) : ℕ :=
  SbF cn cm 0 + 5 * CostSkeleton.dd cn cm * BM.chdTau (CostSkeleton.tF cn cm) 0

/-- The cost of one IHeap operation for heap size bound `K` (agent-06's `heapI … K`.Cop). -/
def copF (K : ℕ) : ℕ := 74 * (Nat.log 2 (K + 1) + 1) + 12

/-- The D-cost parameters of the C-HD run. -/
def chdDC (cn cm : ℕ) : BM.DCost where
  M := BM.chdM (CostSkeleton.tF cn cm)
  new := fun _ => 0
  ins := fun _ => 0
  del := fun _ _ => 0
  pull := fun _ _ => 0
  merge := fun _ _ => 0
  bins := 2 * copF (KhF cn cm) + 76
  bext := copF (KhF cn cm) + 7

/-- The cost parameters of the C-HD run. -/
def chdP (cn cm : ℕ) : CostPar := ⟨1, CostSkeleton.kF cn cm, chdDC cn cm⟩

theorem chdM_pos (t : ℕ) (ht : 1 ≤ t) : ∀ l, 1 ≤ BM.chdM t l
  | 0 => by simp [BM.chdM]
  | l + 1 => by
    simp only [BM.chdM]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by positivity))

theorem KhF_le (cn cm : ℕ) :
    KhF cn cm + 1 ≤ 16 * (CostSkeleton.dd cn cm + 1) * (CostSkeleton.tF cn cm + 1) ^ 3 := by
  have hk := CostSkeleton.kF_le_tF cn cm
  have ht := CostSkeleton.sixteen_le_tF cn cm
  have hd := CostSkeleton.one_le_dd cn cm
  unfold KhF SbF
  simp only [BM.chdM, BM.chdTau, zero_mul, pow_zero, mul_one]
  generalize CostSkeleton.kF cn cm = k at hk ⊢
  generalize CostSkeleton.tF cn cm = t at hk ht ⊢
  generalize CostSkeleton.dd cn cm = d at hd ⊢
  have h1 : 3 * k * t ≤ 3 * t ^ 3 := by
    have : k * t ≤ t * t := Nat.mul_le_mul_right _ hk
    have : t * t ≤ t ^ 3 := by nlinarith
    nlinarith
  have h2 : t ^ 3 ≤ (t + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h3 : 1 ≤ (t + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  nlinarith

theorem log_KhF_le (cn cm : ℕ) :
    Nat.log 2 (KhF cn cm + 1) ≤
      3 * Nat.log 2 (CostSkeleton.tF cn cm + 1) + Nat.log 2 (CostSkeleton.dd cn cm + 1) + 7 := by
  set a := Nat.log 2 (CostSkeleton.tF cn cm + 1)
  set b := Nat.log 2 (CostSkeleton.dd cn cm + 1)
  have ha : CostSkeleton.tF cn cm + 1 < 2 ^ (a + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hb : CostSkeleton.dd cn cm + 1 < 2 ^ (b + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hK := KhF_le cn cm
  have h3 : (CostSkeleton.tF cn cm + 1) ^ 3 ≤ (2 ^ (a + 1)) ^ 3 := Nat.pow_le_pow_left ha.le 3
  have hlt : KhF cn cm + 1 < 2 ^ (3 * a + b + 8) := by
    have e : (2 : ℕ) ^ (3 * a + b + 8) = 16 * 2 ^ (b + 1) * (2 ^ (a + 1)) ^ 3 := by
      rw [← pow_mul]; rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add, ← pow_add]; congr 1; ring
    rw [e]
    calc KhF cn cm + 1 ≤ 16 * (CostSkeleton.dd cn cm + 1) * (CostSkeleton.tF cn cm + 1) ^ 3 := hK
      _ < 16 * 2 ^ (b + 1) * (2 ^ (a + 1)) ^ 3 := by
        have hpos : 0 < (CostSkeleton.tF cn cm + 1) ^ 3 := by positivity
        calc 16 * (CostSkeleton.dd cn cm + 1) * (CostSkeleton.tF cn cm + 1) ^ 3
            < 16 * 2 ^ (b + 1) * (CostSkeleton.tF cn cm + 1) ^ 3 := by
              apply Nat.mul_lt_mul_of_pos_right _ hpos; omega
          _ ≤ 16 * 2 ^ (b + 1) * (2 ^ (a + 1)) ^ 3 := Nat.mul_le_mul_left _ h3
  have := (Nat.log_lt_iff_lt_pow (by norm_num) (by omega)).mpr hlt
  omega

/-- **The C-HD cost parameters are in the master class.** -/
theorem goodP_chdP : GoodP chdP 1 1 1000 where
  hins _ _ := le_rfl
  hext cn cm := by show CostSkeleton.kF cn cm ≤ 1 * (CostSkeleton.kF cn cm + 1); omega
  bins cn cm := by
    show 2 * copF (KhF cn cm) + 76 ≤ _
    have := log_KhF_le cn cm
    unfold copF; omega
  bext cn cm := by
    show copF (KhF cn cm) + 7 ≤ _
    have := log_KhF_le cn cm
    unfold copF; omega

/-- The base case's look-ahead slack for every graph with `H.m ≤ 2 cm` (`baseBud + 112`). -/
def baseReq (cn cm : ℕ) : ℕ :=
  (SbF cn cm 0 + 1) * (copF (KhF cn cm) + 3) +
    (BM.chdTau (CostSkeleton.tF cn cm) 0 + 1) *
      ((2 * cm + 1) * (copF (KhF cn cm) + 77) + 2 * copF (KhF cn cm) + 100) +
    copF (KhF cn cm) + 60 + 112

theorem sbF_pos (cn cm l : ℕ) : 1 ≤ SbF cn cm l := by
  unfold SbF
  have hk := CostSkeleton.two_le_kF cn cm
  have hM := chdM_pos (CostSkeleton.tF cn cm) (by have := CostSkeleton.sixteen_le_tF cn cm; omega) (l + 1)
  have : 1 ≤ 3 * CostSkeleton.kF cn cm := by omega
  nlinarith

/-! ## The base slack is polynomial -/

theorem copF_KhF_le (cn cm : ℕ) : copF (KhF cn cm) ≤ 4700 * (cn + cm + 2) := by
  have h := log_KhF_le cn cm
  have ht := tF_le_X cn cm
  have hd := dd_le_X cn cm
  have h1 : Nat.log 2 (CostSkeleton.tF cn cm + 1) ≤ CostSkeleton.tF cn cm + 1 := Nat.log_le_self 2 _
  have h2 : Nat.log 2 (CostSkeleton.dd cn cm + 1) ≤ CostSkeleton.dd cn cm + 1 := Nat.log_le_self 2 _
  unfold copF; omega

/-- **The base case's slack is polynomial**: `baseReq ≤ 10^9 · (cn+cm+2)^5`. -/
theorem baseReq_le (cn cm : ℕ) : baseReq cn cm ≤ 10 ^ 9 * (cn + cm + 2) ^ 5 := by
  obtain ⟨X, hX⟩ : ∃ X, X = cn + cm + 2 := ⟨_, rfl⟩
  have hX2 : 2 ≤ X := by omega
  have ht := tF_le_X cn cm
  have hk := CostSkeleton.kF_le_tF cn cm
  have hc := copF_KhF_le cn cm
  rw [← hX] at ht hc
  unfold baseReq SbF
  simp only [BM.chdM, BM.chdTau, zero_mul, pow_zero, mul_one]
  rw [← hX]
  generalize copF (KhF cn cm) = c at hc ⊢
  generalize CostSkeleton.kF cn cm = k at hk ⊢
  generalize CostSkeleton.tF cn cm = t at hk ht ⊢
  have hcm : 2 * cm + 1 ≤ 2 * X := by omega
  have hkt : k * t ≤ 289 * X ^ 2 := by nlinarith
  have ht3 : t ^ 3 ≤ 4913 * X ^ 3 := by
    calc t ^ 3 ≤ (17 * X) ^ 3 := Nat.pow_le_pow_left ht 3
      _ = 4913 * X ^ 3 := by ring
  have hX1 : 1 ≤ X := by omega
  have hXp : ∀ a b : ℕ, a ≤ b → X ^ a ≤ X ^ b := fun a b h => Nat.pow_le_pow_right hX1 h
  have e1 := hXp 1 5 (by norm_num)
  have e2 := hXp 2 5 (by norm_num)
  have e3 := hXp 3 5 (by norm_num)
  have e4 := hXp 4 5 (by norm_num)
  have e0 : 1 ≤ X ^ 5 := Nat.one_le_pow _ _ (by omega)
  have p1 : (3 * k * t + 1) * (c + 3) ≤ (867 * X ^ 2 + 1) * (4700 * X + 3) := by
    have : 3 * k * t ≤ 867 * X ^ 2 := by nlinarith
    exact Nat.mul_le_mul (by omega) (by omega)
  have p2 : (t ^ 3 + 1) * ((2 * cm + 1) * (c + 77) + 2 * c + 100) ≤
      (4913 * X ^ 3 + 1) * (2 * X * (4700 * X + 77) + 2 * (4700 * X) + 100) := by
    refine Nat.mul_le_mul (by omega) ?_
    have : (2 * cm + 1) * (c + 77) ≤ 2 * X * (4700 * X + 77) := Nat.mul_le_mul hcm (by omega)
    omega
  have q1 : (867 * X ^ 2 + 1) * (4700 * X + 3) ≤ 4077504 * X ^ 5 := by
    have : X ^ 2 * X = X ^ 3 := by ring
    nlinarith
  have q2 : (4913 * X ^ 3 + 1) * (2 * X * (4700 * X + 77) + 2 * (4700 * X) + 100) ≤
      500000000 * X ^ 5 := by
    have h1 : X ^ 3 * X ^ 2 = X ^ 5 := by ring
    have h2 : X ^ 3 * X = X ^ 4 := by ring
    nlinarith
  have : c + 60 + 112 ≤ 5000 * X ^ 5 := by nlinarith
  omega

end Frontier.CHD.L6

#print axioms Frontier.CHD.L6.kmN_le
#print axioms Frontier.CHD.L6.hucap_of
#print axioms Frontier.CHD.L6.cbig_of_cap
#print axioms Frontier.CHD.L6.goodP_chdP
#print axioms Frontier.CHD.L6.baseReq_le
