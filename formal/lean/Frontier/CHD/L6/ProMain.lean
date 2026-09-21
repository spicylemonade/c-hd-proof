import Frontier.CHD.L6.ProBlow
import Frontier.CHD.L6.TopGlue
import Frontier.CHD.L6.CoreSpecProof

/-!
# The spine prologue, part 3: allocation phase and the assembly of `ProSpec` (agent-10)

`partA` = `sizeProg ; tnProg ; allocWs spAllocW ; allocVs spAllocV` allocates every spine array
agent-08's `Static` asks for (rows `(LF+2) n`, level tables `LF+2`, `sp.xm`/`sp.ptr` of size `n`,
bound slots `4 (LF+2)`), all zero.  NON-GATE (Layer B, spine prologue).
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD.LabTab WExpr Stmt

/-- The spine's word arrays with their size registers. -/
def spAllocW : List (String × String) :=
  RamSpine.rowArrs.map (fun a => (a, "sp.zr")) ++ RamSpine.lenArrs.map (fun a => (a, "sp.zl")) ++
    [("sp.xm", "n"), ("sp.ptr", "n")] ++ slotW.map (fun a => (a, "sp.zs"))

/-- The spine's value arrays with their size registers. -/
def spAllocV : List (String × String) := [("sl.l", "sp.zs")]

theorem spAllocW_nodup : (spAllocW.map Prod.fst).Nodup := by
  simp [spAllocW, RamSpine.rowArrs, RamSpine.lenArrs, slotW]

/-- Part A of the prologue. -/
def partA : Stmt :=
  seq sizeProg (seq tnProg (seq (AllocList.allocWs spAllocW) (AllocList.allocVs spAllocV)))

/-! ## Capacity arithmetic -/

theorem X_pow_ge {cn cm e cap : ℕ} (hcn : 1 ≤ cn) (hcm : 1 ≤ cm) (he : 32 ≤ e)
    (hcap : (cn + cm + 2) ^ (e + 1) ≤ cap) : (cn + cm + 2) ^ 6 ≤ cap :=
  (Nat.pow_le_pow_right (by omega) (by omega)).trans hcap

theorem sq_lt_pow6 (X : ℕ) (hX : 4 ≤ X) : 64 * X ^ 2 < X ^ 6 := by
  have h1 : 256 ≤ X ^ 4 := by
    calc 256 = 4 ^ 4 := by norm_num
      _ ≤ X ^ 4 := Nat.pow_le_pow_left hX 4
  have h2 : X ^ 6 = X ^ 4 * X ^ 2 := by ring
  have h3 : 0 < X ^ 2 := by positivity
  nlinarith

theorem LF_le (cn cm : ℕ) (hcn : 1 ≤ cn) : CostSkeleton.LF cn cm ≤ cn + 1 := by
  have h1 : CostSkeleton.LF cn cm = CostSkeleton.lgN cn / CostSkeleton.tF cn cm + 1 := rfl
  have h2 := Nat.div_le_self (CostSkeleton.lgN cn) (CostSkeleton.tF cn cm)
  have h3 := lgN_le_self hcn
  omega

theorem Tnat_le_sq (cn cm : ℕ) (hcn : 1 ≤ cn) :
    CostSkeleton.Tnat cn cm + CostSkeleton.dd cn cm + 4 ≤ 8 * (cn + cm + 2) ^ 2 := by
  have hT : CostSkeleton.tF cn cm ≤ 16 + cn :=
    (CostSkeleton.tF_le cn cm).trans (by have := lgN_le_self hcn; omega)
  have hd : CostSkeleton.dd cn cm ≤ cm + 1 := by
    unfold CostSkeleton.dd; have := Nat.div_le_self cm cn; omega
  have hl : Nat.log 2 (CostSkeleton.dd cn cm + 1) ≤ cm + 2 :=
    (Nat.log_le_self 2 _).trans (by omega)
  unfold CostSkeleton.Tnat
  nlinarith

/-! ## Part A -/

/-- The facts established by part A. -/
structure AOut (H : Graph) (cn cm : ℕ) (t r : State ℝ≥0) : Prop where
  n : r.w "n" = H.n
  tn : r.w "pr.tn" = CostSkeleton.Tnat cn cm
  rows : ∀ a ∈ RamSpine.rowArrs, r.wlen a = (CostSkeleton.LF cn cm + 2) * H.n ∧ ∀ i, r.wa a i = 0
  lens : ∀ a ∈ RamSpine.lenArrs, r.wlen a = CostSkeleton.LF cn cm + 2 ∧ ∀ i, r.wa a i = 0
  xm : r.wlen "sp.xm" = H.n ∧ ∀ i, r.wa "sp.xm" i = 0
  ptr : r.wlen "sp.ptr" = H.n
  slotw : ∀ a ∈ slotW, r.wlen a = 4 * (CostSkeleton.LF cn cm + 2) ∧ ∀ i, r.wa a i = 0
  slotv : r.vlen "sl.l" = 4 * (CostSkeleton.LF cn cm + 2) ∧ ∀ i, r.va "sl.l" i = 0
  U : Unchanged t r (spAllocW.map Prod.fst) ["sl.l"] (sizeWR ++ tnWR) []
  c : r.cost ≤ t.cost + 50 * ((CostSkeleton.LF cn cm + 2) * (H.n + 1)) +
    3 * Nat.log 2 (CostSkeleton.dd cn cm + 1) + 100

theorem partA_runs {e : ℕ} (he : 32 ≤ e) {ps : List Stmt} {H : Graph} {src : Fin H.n}
    {cn cm c0 : ℕ} {t : State ℝ≥0} (hP : PreIn e ps H src cn cm c0 t) :
    Runs realOps partA t (fun r => AOut H cn cm t r) := by
  have hc := hP.core
  have hcn1 := hc.cn_pos
  have hcm1 := hc.cm_pos
  obtain ⟨L, hLdef⟩ : ∃ L, L = CostSkeleton.LF cn cm := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N, N = H.n := ⟨_, rfl⟩
  have hX4 : 4 ≤ cn + cm + 2 := by omega
  have h6 := X_pow_ge hcn1 hcm1 he hc.cap
  have hsq := sq_lt_pow6 (cn + cm + 2) hX4
  have hLle : L ≤ cn + 1 := by rw [hLdef]; exact LF_le cn cm hcn1
  have hNle : N ≤ 2 * cn := by rw [hNdef]; exact hc.sizeN
  have hA : 4 * ((L + 2) * (N + 1)) < t.cap := by
    have : 4 * ((L + 2) * (N + 1)) ≤ 64 * (cn + cm + 2) ^ 2 := by nlinarith
    omega
  have hT := Tnat_le_sq cn cm hcn1
  unfold partA
  refine runs_seq ((sizeProg_runs (ops := realOps) t N L (by rw [hNdef]; exact hc.gN)
    (by rw [hLdef]; exact hP.L) hA).mono ?_)
  rintro t1 ⟨h1n, h1l, h1r, h1s, hU1, hc1⟩
  have e1 : ∀ x, x ∉ sizeWR → t1.w x = t.w x := hU1.wreg
  have hcap1 : t1.cap = t.cap := hU1.cap
  refine runs_seq ((tnProg_runs (ops := realOps) t1 cn cm (by rw [e1 _ (by simp [sizeWR])]; exact hc.cnR)
    (by rw [e1 _ (by simp [sizeWR])]; exact hc.cmR) (by rw [e1 _ (by simp [sizeWR])]; exact hP.dd)
    (by rw [e1 _ (by simp [sizeWR])]; exact hP.tt) hcm1 (by rw [hcap1]; omega)).mono ?_)
  rintro t2 ⟨h2tn, hU2, hc2⟩
  have e2 : ∀ x, x ∉ tnWR → t2.w x = t1.w x := hU2.wreg
  have h2n : t2.w "n" = N := by rw [e2 _ (by simp [tnWR]), h1n]
  have h2l : t2.w "sp.zl" = L + 2 := by rw [e2 _ (by simp [tnWR]), h1l]
  have h2r : t2.w "sp.zr" = (L + 2) * N := by rw [e2 _ (by simp [tnWR]), h1r]
  have h2s : t2.w "sp.zs" = 4 * (L + 2) := by rw [e2 _ (by simp [tnWR]), h1s]
  refine runs_seq ((AllocList.allocWs_runs (ops := realOps) spAllocW spAllocW_nodup t2).mono ?_)
  rintro t3 ⟨h3a, hU3, hc3⟩
  refine (AllocList.allocVs_runs (ops := realOps) spAllocV (by simp [spAllocV]) t3).mono ?_
  rintro t4 ⟨h4a, hU4, hc4⟩
  have e4w : ∀ a, t4.wa a = t3.wa a ∧ t4.wlen a = t3.wlen a := fun a => hU4.warr a (by simp)
  have e4r : ∀ x, t4.w x = t3.w x := fun x => hU4.wreg x (by simp)
  have e3r : ∀ x, t3.w x = t2.w x := fun x => hU3.wreg x (by simp)
  have hW : ∀ p ∈ spAllocW, t4.wlen p.1 = t2.w p.2 ∧ ∀ i, t4.wa p.1 i = 0 := by
    intro p hp
    obtain ⟨l1, l2⟩ := h3a p hp
    exact ⟨by rw [(e4w _).2, l1], fun i => by rw [(e4w _).1, l2]⟩
  subst hLdef hNdef
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e4r, e3r, h2n]
  · rw [e4r, e3r, h2tn]
  · intro a ha
    have hp : (a, "sp.zr") ∈ spAllocW := by simp [spAllocW, ha]
    obtain ⟨l1, l2⟩ := hW _ hp
    exact ⟨by rw [l1, h2r], l2⟩
  · intro a ha
    have hp : (a, "sp.zl") ∈ spAllocW := by simp [spAllocW, ha]
    obtain ⟨l1, l2⟩ := hW _ hp
    exact ⟨by rw [l1, h2l], l2⟩
  · have hp : ("sp.xm", "n") ∈ spAllocW := by simp [spAllocW]
    obtain ⟨l1, l2⟩ := hW _ hp
    exact ⟨by rw [l1, h2n], l2⟩
  · have hp : ("sp.ptr", "n") ∈ spAllocW := by simp [spAllocW]
    obtain ⟨l1, -⟩ := hW _ hp
    rw [l1, h2n]
  · intro a ha
    have hp : (a, "sp.zs") ∈ spAllocW := by simp [spAllocW, ha]
    obtain ⟨l1, l2⟩ := hW _ hp
    exact ⟨by rw [l1, h2s], l2⟩
  · obtain ⟨l1, l2⟩ := h4a ("sl.l", "sp.zs") (by simp [spAllocV])
    exact ⟨by rw [l1, e3r, h2s], fun i => by rw [l2]; rfl⟩
  · have u1 : Unchanged t t1 (spAllocW.map Prod.fst) ["sl.l"] (sizeWR ++ tnWR) [] :=
      hU1.mono (by simp) (by simp) (by simp) (by simp)
    have u2 : Unchanged t1 t2 (spAllocW.map Prod.fst) ["sl.l"] (sizeWR ++ tnWR) [] :=
      hU2.mono (by simp) (by simp) (by simp) (by simp)
    have u3 : Unchanged t2 t3 (spAllocW.map Prod.fst) ["sl.l"] (sizeWR ++ tnWR) [] :=
      hU3.mono (List.Subset.refl _) (by simp) (by simp) (by simp)
    have u4 : Unchanged t3 t4 (spAllocW.map Prod.fst) ["sl.l"] (sizeWR ++ tnWR) [] :=
      hU4.mono (by simp) (by simp [spAllocV]) (by simp) (by simp)
    exact ((u1.trans u2).trans u3).trans u4
  · have key : ∀ (l : List String) (reg : String),
        ((l.map (fun a => (a, reg))).map (fun p : String × String => t2.w p.2 + 1)).sum =
          l.length * (t2.w reg + 1) := by
      intro l reg
      induction l with
      | nil => simp
      | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring
    have hcW : AllocList.allocCost t2 spAllocW = 12 * ((CostSkeleton.LF cn cm + 2) * H.n + 1) +
        6 * (CostSkeleton.LF cn cm + 2 + 1) + 2 * (H.n + 1) +
        5 * (4 * (CostSkeleton.LF cn cm + 2) + 1) + 1 := by
      unfold AllocList.allocCost spAllocW
      simp only [List.map_append, List.sum_append, key]
      have l1 : RamSpine.rowArrs.length = 12 := rfl
      have l2 : RamSpine.lenArrs.length = 6 := rfl
      have l3 : slotW.length = 5 := rfl
      rw [l1, l2, l3, h2r, h2l, h2s]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2n]
      ring
    have hcV : AllocList.allocCost t3 spAllocV = 4 * (CostSkeleton.LF cn cm + 2) + 1 + 1 := by
      unfold AllocList.allocCost spAllocV
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e3r, h2s]
      omega
    rw [hc4, hcV, hc3, hcW]
    have hNL : (CostSkeleton.LF cn cm + 2) * H.n ≤ (CostSkeleton.LF cn cm + 2) * (H.n + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hL1 : CostSkeleton.LF cn cm + 2 ≤ (CostSkeleton.LF cn cm + 2) * (H.n + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have hN1 : H.n + 1 ≤ (CostSkeleton.LF cn cm + 2) * (H.n + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega

end Frontier.CHD.L6

#print axioms Frontier.CHD.L6.partA_runs
