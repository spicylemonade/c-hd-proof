import Mathlib.Data.NNReal.Basic
import Mathlib.Data.List.GetD

/-!
# L6 dedup model (agent-10, scratch): the first minimum-weight edge to every head

`bst dst wt u L v` scans the edge list `L` (all tails `u`) and returns the first edge of minimum
weight among the non-loop edges of `L` with head `v` (`none` if there is none, and for `v = u`).
This is exactly what the RAM scan `dedupLoop` computes with its stamp array.
-/

open scoped NNReal

namespace Frontier.CHD.L6

section Model

variable (dst : ℕ → ℕ) (wt : ℕ → ℝ≥0) (u : ℕ)

noncomputable def bstStep (acc : ℕ → Option ℕ) (e : ℕ) : ℕ → Option ℕ :=
  if dst e = u then acc else
  match acc (dst e) with
  | none => Function.update acc (dst e) (some e)
  | some b => if wt b ≤ wt e then acc else Function.update acc (dst e) (some e)

noncomputable def bst (L : List ℕ) : ℕ → Option ℕ := L.foldl (bstStep dst wt u) (fun _ => none)

@[simp] theorem bst_nil : bst dst wt u [] = fun _ => none := rfl

theorem bst_concat (L : List ℕ) (e : ℕ) :
    bst dst wt u (L ++ [e]) = bstStep dst wt u (bst dst wt u L) e := by
  simp [bst, List.foldl_append]

variable {dst wt u}

/-- (B1) The chosen edge is an edge of the list with the right head, and heads are never `u`. -/
theorem bst_some {L : List ℕ} {v b : ℕ} (h : bst dst wt u L v = some b) :
    b ∈ L ∧ dst b = v ∧ v ≠ u := by
  induction L using List.reverseRecOn generalizing v b with
  | nil => simp at h
  | append_singleton L e ih =>
    rw [bst_concat] at h
    unfold bstStep at h
    by_cases hl : dst e = u
    · rw [if_pos hl] at h
      obtain ⟨h1, h2, h3⟩ := ih h
      exact ⟨List.mem_append_left _ h1, h2, h3⟩
    · rw [if_neg hl] at h
      cases hacc : bst dst wt u L (dst e) with
      | none =>
        rw [hacc] at h
        simp only at h
        by_cases hv : v = dst e
        · subst hv
          simp at h
          subst h
          exact ⟨by simp, rfl, hl⟩
        · rw [Function.update_of_ne hv] at h
          obtain ⟨h1, h2, h3⟩ := ih h
          exact ⟨List.mem_append_left _ h1, h2, h3⟩
      | some b' =>
        rw [hacc] at h
        simp only at h
        split_ifs at h with hw
        · obtain ⟨h1, h2, h3⟩ := ih h
          exact ⟨List.mem_append_left _ h1, h2, h3⟩
        · by_cases hv : v = dst e
          · subst hv
            simp at h
            subst h
            exact ⟨by simp, rfl, hl⟩
          · rw [Function.update_of_ne hv] at h
            obtain ⟨h1, h2, h3⟩ := ih h
            exact ⟨List.mem_append_left _ h1, h2, h3⟩

/-- (B3) Every non-loop head of the list gets an edge. -/
theorem bst_isSome {L : List ℕ} {f : ℕ} (hf : f ∈ L) (hfu : dst f ≠ u) :
    (bst dst wt u L (dst f)).isSome := by
  induction L using List.reverseRecOn with
  | nil => simp at hf
  | append_singleton L e ih =>
    rw [bst_concat]
    unfold bstStep
    have hold : f ≠ e → f ∈ L := by
      intro hne
      rcases List.mem_append.mp hf with h | h
      · exact h
      · simp at h; exact absurd h hne
    by_cases hl : dst e = u
    · rw [if_pos hl]
      have hne : f ≠ e := by rintro rfl; exact hfu hl
      exact ih (hold hne)
    · rw [if_neg hl]
      cases hacc : bst dst wt u L (dst e) with
      | none =>
        simp only
        by_cases hv : dst f = dst e
        · rw [hv, Function.update_self]; simp
        · rw [Function.update_of_ne hv]
          have hne : f ≠ e := by rintro rfl; exact hv rfl
          exact ih (hold hne)
      | some b' =>
        simp only
        split_ifs with hw
        · by_cases hfe : f = e
          · subst hfe; rw [hacc]; simp
          · exact ih (hold hfe)
        · by_cases hv : dst f = dst e
          · rw [hv, Function.update_self]; simp
          · rw [Function.update_of_ne hv]
            have hne : f ≠ e := by rintro rfl; exact hv rfl
            exact ih (hold hne)

/-- (B2) The chosen edge has minimum weight among the list's edges with that head. -/
theorem bst_min {L : List ℕ} {v b : ℕ} (h : bst dst wt u L v = some b) :
    ∀ e ∈ L, dst e = v → wt b ≤ wt e := by
  induction L using List.reverseRecOn generalizing v b with
  | nil => simp at h
  | append_singleton L e ih =>
    intro f hf hfv
    have hvu : v ≠ u := (bst_some h).2.2
    rw [bst_concat] at h
    unfold bstStep at h
    rcases List.mem_append.mp hf with hf | hf
    · -- f is an old edge
      by_cases hl : dst e = u
      · rw [if_pos hl] at h; exact ih h f hf hfv
      · rw [if_neg hl] at h
        cases hacc : bst dst wt u L (dst e) with
        | none =>
          rw [hacc] at h; simp only at h
          by_cases hv : v = dst e
          · exfalso
            have hs := bst_isSome (dst := dst) (wt := wt) hf (by rw [hfv]; exact hvu)
            rw [hfv, hv, hacc] at hs
            simp at hs
          · rw [Function.update_of_ne hv] at h; exact ih h f hf hfv
        | some b' =>
          rw [hacc] at h; simp only at h
          split_ifs at h with hw
          · exact ih h f hf hfv
          · by_cases hv : v = dst e
            · subst hv
              rw [Function.update_self] at h; simp at h; subst h
              have := ih hacc f hf hfv
              exact le_trans (le_of_lt (not_le.mp hw)) this
            · rw [Function.update_of_ne hv] at h; exact ih h f hf hfv
    · -- f = e, the new edge
      simp at hf; subst hf
      have hl : dst f ≠ u := by rw [hfv]; exact hvu
      rw [if_neg hl] at h
      cases hacc : bst dst wt u L (dst f) with
      | none =>
        rw [hacc] at h; simp only at h
        rw [← hfv, Function.update_self] at h
        simp at h; subst h; exact le_rfl
      | some b' =>
        rw [hacc] at h; simp only at h
        split_ifs at h with hw
        · rw [← hfv, hacc] at h; simp at h; subst h; exact hw
        · rw [← hfv, Function.update_self] at h
          simp at h; subst h; exact le_rfl

theorem bst_self (L : List ℕ) : bst dst wt u L u = none := by
  cases h : bst dst wt u L u with
  | none => rfl
  | some b => exact absurd rfl (bst_some h).2.2

end Model

end Frontier.CHD.L6
