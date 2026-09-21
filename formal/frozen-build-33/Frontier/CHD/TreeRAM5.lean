import Frontier.CHD.TreeRAM4

/-!
# Frontier.CHD.TreeRAM5 — (T2, part 3) the path clear of `mergeTree` (owner agent-03)

**NON-GATE** (Layer B).  `pcLoop` walks `kpath kpar x f u` again (fuel-exact) and resets `tr.inP` on it, so the
temporary bitmap is all-zero again after a merge.
-/

namespace Frontier.CHD.PartitionRAM

open Frontier Frontier.RAM Frontier.CHD.Partition

variable {V : Type} {ops : VOps V}

/-- Invariant of the path clear after the cleared prefix `Pr` of the path `P`. -/
structure PCI (st0 : State V) {N : ℕ} (kpar : Fin N → Fin N) (x : Fin N) (P : List (Fin N)) (c0 : ℕ)
    (n : ℕ) (Pr : List (Fin N)) (st : State V) : Prop where
  pre : Pr <+: P
  ctl : (n = 0 ∧ Pr = P ∧ st.w "tr.x" = 0) ∨
    (0 < n ∧ st.w "tr.x" = 1 ∧ ∃ (c : Fin N) (f : ℕ), st.w "tr.c" = c.val ∧ st.w "tr.f" = f ∧ n = f + 1 ∧
      Pr ++ kpath kpar x f c = P)
  inP : ∀ i, st.wa "tr.inP" i = if i ∈ Pr.map Fin.val then 0 else st0.wa "tr.inP" i
  arr : ∀ arr i, arr ≠ "tr.inP" → st.wa arr i = st0.wa arr i
  reg : ∀ y, y ≠ "tr.c" → y ≠ "tr.f" → y ≠ "tr.x" → st.w y = st0.w y
  wlen : st.wlen = st0.wlen
  cap : st.cap = st0.cap
  cost : st.cost + 6 * n ≤ c0

theorem pcLoop_spec {st0 : State V} {N : ℕ} {kpar : Fin N → Fin N} {x : Fin N} {P K : List (Fin N)} {c0 : ℕ}
    (hPnd : P.Nodup) (hPK : ∀ w ∈ P, w ∈ K)
    (hkp : ∀ w ∈ K, st0.wa "fp.kp" w.val = (kpar w).val) (hx : st0.w "fp.x" = x.val)
    (hlens : N ≤ st0.wlen "tr.inP" ∧ N ≤ st0.wlen "fp.kp") (hcap : N + 2 < st0.cap) :
    ∀ n st, (∃ Pr, PCI st0 kpar x P c0 n Pr st) →
      Runs ops pcLoop st (fun st' => PCI st0 kpar x P (c0 + 1) 0 P st') := by
  obtain ⟨l1, l2⟩ := hlens
  apply runs_while_nat
  rintro n st ⟨Pr, hI⟩
  have hcap1 : 1 < st.cap := by rw [hI.cap]; omega
  have hcost0 := hI.cost
  refine ⟨st.w "tr.x", by simp, fun hx0 => ?_, fun hx0 => ?_⟩
  · rcases hI.ctl with ⟨rfl, -, h0⟩ | ⟨hn, hx1, c, f, hc, hf, hnf, hPr⟩
    · exact absurd h0 hx0
    have hcP : c ∈ P := by rw [← hPr, kpath_step]; split_ifs <;> simp
    have hcK := hPK c hcP
    have hPr' : Pr ++ [c] <+: P := by
      rw [← hPr, kpath_step]
      split_ifs
      · exact List.prefix_refl _
      · exact ⟨kpath kpar x (f - 1) (kpar c), by simp⟩
    have hcl : c.val < st.wlen "tr.inP" := by rw [hI.wlen]; have := c.2; omega
    have hfit0 : fit st.cap 0 = some 0 := fit_of_lt (by omega)
    apply runs_seq
    refine runs_wstore (j := c.val) (a := 0) (by simpa using hc) (by simp [hfit0]) (by simpa using hcl) ?_
    generalize hs1 : ((st.charge 1).storeW "tr.inP" c.val 0).charge 1 = s1
    have h1wa : ∀ arr i, s1.wa arr i = if arr = "tr.inP" ∧ i = c.val then 0 else st.wa arr i := by
      intro arr i; rw [← hs1]; simp only [State.charge_wa, State.storeW_wa]
    have h1w : ∀ y, s1.w y = st.w y := by intro y; rw [← hs1]; rfl
    have h1len : s1.wlen = st.wlen := by rw [← hs1]; rfl
    have h1cap : s1.cap = st.cap := by rw [← hs1]; rfl
    have h1cost : s1.cost = st.cost + 2 := by rw [← hs1]; simp
    have hinP1 : ∀ i, s1.wa "tr.inP" i = if i ∈ (Pr ++ [c]).map Fin.val then 0 else st0.wa "tr.inP" i := by
      intro i
      rw [h1wa, hI.inP]
      simp only [true_and, List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton]
      by_cases hic : i = c.val
      · simp [hic]
      · simp [hic]
    have harr1 : ∀ arr i, arr ≠ "tr.inP" → s1.wa arr i = st0.wa arr i := by
      intro arr i ha; rw [h1wa, if_neg (by rintro ⟨h, -⟩; exact ha h)]; exact hI.arr arr i ha
    have hcap1' : 1 < s1.cap := by rw [h1cap]; exact hcap1
    have hfit0' : fit s1.cap 0 = some 0 := fit_of_lt (by omega)
    have hfit1' : fit s1.cap 1 = some 1 := fit_of_lt hcap1'
    have h1c : s1.w "tr.c" = c.val := by rw [h1w]; exact hc
    have h1f : s1.w "tr.f" = f := by rw [h1w]; exact hf
    have h1xx : s1.w "fp.x" = x.val := by rw [h1w, hI.reg _ (by decide) (by decide) (by decide)]; exact hx
    have hmk : ∀ (n' : ℕ) (s' : State V), s'.wa = s1.wa → (∀ y, y ≠ "tr.c" → y ≠ "tr.f" → y ≠ "tr.x" → s'.w y = s1.w y) →
        s'.wlen = s1.wlen → s'.cap = s1.cap →
        ((n' = 0 ∧ Pr ++ [c] = P ∧ s'.w "tr.x" = 0) ∨
          (0 < n' ∧ s'.w "tr.x" = 1 ∧ ∃ (c' : Fin N) (f' : ℕ), s'.w "tr.c" = c'.val ∧ s'.w "tr.f" = f' ∧
            n' = f' + 1 ∧ (Pr ++ [c]) ++ kpath kpar x f' c' = P)) →
        s'.cost + 6 * n' ≤ c0 → PCI st0 kpar x P c0 n' (Pr ++ [c]) s' := by
      intro n' s' hwa hreg hlen hcap' hctl hcost'
      exact ⟨hPr', hctl, fun i => by rw [hwa]; exact hinP1 i, fun arr i ha => by rw [hwa]; exact harr1 arr i ha,
        fun y a b c'' => by rw [hreg y a b c'', h1w]; exact hI.reg y a b c'', by rw [hlen, h1len]; exact hI.wlen,
        by rw [hcap', h1cap]; exact hI.cap, hcost'⟩
    by_cases hcx : c = x
    · subst hcx
      refine runs_ite_true (x := 1) (by simp [h1c, h1xx, hfit1']) one_ne_zero ?_
      refine runs_wset (a := 0) (by simp [hfit0']) ?_
      have hP : Pr ++ [c] = P := by rw [← hPr, kpath_step]; simp
      exact ⟨0, by omega, Pr ++ [c], hmk 0 _ rfl (fun y _ _ hy => by simp [hy]) rfl rfl
        (Or.inl ⟨rfl, hP, by simp⟩) (by simp; omega)⟩
    · have hcx' : c.val ≠ x.val := fun h => hcx (Fin.ext h)
      refine runs_ite_false (by simp [h1c, h1xx, hcx', hfit0']) ?_
      by_cases hf0 : f = 0
      · subst hf0
        refine runs_ite_true (x := 1) (by simp [h1f, hfit1', hfit0']) one_ne_zero ?_
        refine runs_wset (a := 0) (by simp [hfit0']) ?_
        have hP : Pr ++ [c] = P := by rw [← hPr, kpath_step]; simp
        exact ⟨0, by omega, Pr ++ [c], hmk 0 _ rfl (fun y _ _ hy => by simp [hy]) rfl rfl
          (Or.inl ⟨rfl, hP, by simp⟩) (by simp; omega)⟩
      · refine runs_ite_false (by simp [h1f, hf0, hfit0']) ?_
        have hkpc : s1.wa "fp.kp" c.val = (kpar c).val := by
          rw [h1wa, if_neg (by rintro ⟨h, -⟩; exact absurd h (by decide)), hI.arr _ _ (by decide)]
          exact hkp c hcK
        have hckl : c.val < s1.wlen "fp.kp" := by rw [h1len, hI.wlen]; have := c.2; omega
        apply runs_seq
        refine runs_wset (a := (kpar c).val) (by simp [h1c, hckl, hkpc]) ?_
        refine runs_wset (a := f - 1) (by simp [h1f, hfit1']) ?_
        have hkp' : (Pr ++ [c]) ++ kpath kpar x (f - 1) (kpar c) = P := by
          rw [List.append_assoc, List.singleton_append, ← hPr, kpath_step kpar x f c]
          simp [hcx, hf0]
        have hx1' : s1.w "tr.x" = 1 := by rw [h1w]; exact hx1
        exact ⟨f, by omega, Pr ++ [c], hmk f _ rfl (fun y hy1 hy2 _ => by simp [hy1, hy2]) rfl rfl
          (Or.inr ⟨by omega, by simp [hx1'], kpar c, f - 1, by simp, by simp, by omega, hkp'⟩)
          (by simp; omega)⟩
  · rcases hI.ctl with ⟨rfl, hPP, h0⟩ | ⟨hn, hx1, -⟩
    · subst hPP
      exact ⟨List.prefix_refl _, Or.inl ⟨rfl, rfl, by simpa using h0⟩, hI.inP, hI.arr, hI.reg, hI.wlen, hI.cap,
        by simp; omega⟩
    · rw [hx1] at hx0; exact absurd hx0 one_ne_zero

end Frontier.CHD.PartitionRAM
