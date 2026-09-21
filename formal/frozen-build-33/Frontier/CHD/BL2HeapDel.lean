import Frontier.CHD.BL2Rep

/-!
# Frontier.CHD.BL2HeapDel — swap-with-last deletion from the unsorted heap array (agent-09, NON-GATE)

Pure list facts: deleting position `b` of a duplicate-free list `hl` by moving the last element
into position `b` and dropping the last position yields a duplicate-free list with the elements
of `hl` except `hl[b]`.
-/

namespace Frontier.CHD.BL2

variable {α : Type} [DecidableEq α]

/-- The list after swap-with-last deletion of position `b`. -/
def swapDel (hl : List α) (b : ℕ) (h : hl ≠ []) : List α :=
  List.ofFn (fun j : Fin (hl.length - 1) => if (j : ℕ) = b then hl.getLast h else hl[(j : ℕ)]'(by omega))

theorem swapDel_length (hl : List α) (b : ℕ) (h : hl ≠ []) :
    (swapDel hl b h).length = hl.length - 1 := by simp [swapDel]

theorem swapDel_getElem (hl : List α) (b : ℕ) (h : hl ≠ []) (j : ℕ)
    (hj : j < (swapDel hl b h).length) :
    (swapDel hl b h)[j] = if j = b then hl.getLast h else hl[j]'(by
      rw [swapDel_length] at hj; omega) := by
  simp [swapDel]

theorem getLast_eq_getElem' (hl : List α) (h : hl ≠ []) :
    hl.getLast h = hl[hl.length - 1]'(by
      have : 0 < hl.length := List.length_pos_of_ne_nil h
      omega) := List.getLast_eq_getElem h

theorem mem_swapDel (hl : List α) (b : ℕ) (h : hl ≠ []) (hb : b < hl.length) (hnd : hl.Nodup)
    (x : α) : x ∈ swapDel hl b h ↔ x ∈ hl ∧ x ≠ hl[b] := by
  have hpos : 0 < hl.length := List.length_pos_of_ne_nil h
  constructor
  · intro hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    rw [swapDel_getElem]
    rw [swapDel_length] at hj
    by_cases hjb : j = b
    · subst hjb
      rw [if_pos rfl, getLast_eq_getElem']
      refine ⟨List.getElem_mem _, fun heq => ?_⟩
      have := (List.Nodup.getElem_inj_iff hnd).mp heq
      omega
    · rw [if_neg hjb]
      refine ⟨List.getElem_mem _, fun heq => ?_⟩
      exact hjb ((List.Nodup.getElem_inj_iff hnd).mp heq)
  · rintro ⟨hx, hxb⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    by_cases hjl : j < hl.length - 1
    · have hjb : j ≠ b := fun h' => hxb (by subst h'; rfl)
      have hj' : j < (swapDel hl b h).length := by rw [swapDel_length]; exact hjl
      have := swapDel_getElem hl b h j hj'
      rw [if_neg hjb] at this
      rw [← this]; exact List.getElem_mem _
    · have hjeq : j = hl.length - 1 := by omega
      have hbl : b ≠ hl.length - 1 := fun h' => hxb (by subst hjeq; simp [h'])
      have hb' : b < (swapDel hl b h).length := by rw [swapDel_length]; omega
      have := swapDel_getElem hl b h b hb'
      rw [if_pos rfl, getLast_eq_getElem'] at this
      rw [show hl[j] = hl[hl.length - 1] by simp [hjeq], ← this]
      exact List.getElem_mem _

theorem swapDel_nodup (hl : List α) (b : ℕ) (h : hl ≠ []) (hb : b < hl.length) (hnd : hl.Nodup) :
    (swapDel hl b h).Nodup := by
  rw [List.nodup_iff_injective_get]
  intro i j hij
  have hL := swapDel_length hl b h
  have hi : (i : ℕ) < hl.length - 1 := by have := i.isLt; omega
  have hj : (j : ℕ) < hl.length - 1 := by have := j.isLt; omega
  simp only [List.get_eq_getElem] at hij
  rw [swapDel_getElem, swapDel_getElem] at hij
  apply Fin.ext
  by_cases hib : (i : ℕ) = b <;> by_cases hjb : (j : ℕ) = b
  · omega
  · rw [if_pos hib, if_neg hjb, getLast_eq_getElem'] at hij
    have := (List.Nodup.getElem_inj_iff hnd).mp hij
    omega
  · rw [if_neg hib, if_pos hjb, getLast_eq_getElem'] at hij
    have := (List.Nodup.getElem_inj_iff hnd).mp hij
    omega
  · rw [if_neg hib, if_neg hjb] at hij
    exact (List.Nodup.getElem_inj_iff hnd).mp hij

theorem swapDel_toFinset (hl : List α) (b : ℕ) (h : hl ≠ []) (hb : b < hl.length)
    (hnd : hl.Nodup) : (swapDel hl b h).toFinset = hl.toFinset.erase hl[b] := by
  ext x
  simp only [List.mem_toFinset, Finset.mem_erase]
  rw [mem_swapDel hl b h hb hnd]
  tauto

end Frontier.CHD.BL2
