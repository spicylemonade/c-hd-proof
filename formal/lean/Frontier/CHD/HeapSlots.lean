import Frontier.CHD.IHeapLab
import Frontier.CHD.BaseHeap

/-!
# HeapSlots — the slot list of an IHeap (agent-06; NON-GATE)

For agent-03's `InsSeg` (the base case's leftover conversion `insSeg dsNew dsIns "hp_A" (lit 0) (var "hp_n")`):
a heap in IHeap's representation stores its vertex set `T` as the duplicate-free slot list
`hp_A[0], …, hp_A[hp_n - 1]`.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.IHeapLab

open Frontier Frontier.RAM Frontier.CHD.IHeap

variable {G : Graph} {s : Fin G.n}

/-- The slots `A 0, …, A (n-1)` of a heap with positions `P` are duplicate-free and spell `T A n`. -/
theorem posOK_slots {N : ℕ} {A P : ℕ → ℕ} {n : ℕ} (h : PosOK N A P n) :
    ((List.range n).map A).Nodup ∧ ((List.range n).map A).toFinset = IHeap.T A n := by
  refine ⟨List.Nodup.map_on (fun x hx y hy e => h.inj (List.mem_range.mp hx) (List.mem_range.mp hy) e)
    List.nodup_range, ?_⟩
  ext v
  simp [IHeap.T]

/-- **The slot list of `heapI`'s representation** (`HR = HRL`): `T` is the duplicate-free list stored in
`hp_A[0, hp_n)`. -/
theorem HRL.slotList {st : State ℝ≥0} {T : Finset (Fin G.n)} {key : Fin G.n → WLab G s} (h : HRL st T key) :
    ∃ l : List (Fin G.n), l.Nodup ∧ l.toFinset = T ∧ l.length = st.w "hp_n" ∧
      ∀ j (hj : j < l.length), st.wa "hp_A" j = (l[j] : ℕ) := by
  obtain ⟨hn, -, -, -, hpos, -, hT⟩ := h
  refine ⟨(List.range T.card).pmap (fun j hj => (⟨st.wa "hp_A" j, (hpos.slots j hj).1⟩ : Fin G.n))
    (fun j hj => List.mem_range.mp hj), ?_, ?_, by simp [hn], fun j hj => by simp⟩
  · refine List.Nodup.pmap (fun a ha b hb e => ?_) List.nodup_range
    exact hpos.inj ha hb (Fin.mk.inj_iff.mp e)
  · ext u
    simp only [List.mem_toFinset, List.mem_pmap, List.mem_range]
    rw [← mem_T_iff hT u]
    simp only [IHeap.T, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
    · rintro ⟨j, hj, e⟩; exact ⟨j, hj, Fin.ext e⟩

/-- The same for agent-08's `RamBaseCase.HRL` (the representation of `heapL`). -/
theorem baseHRL_slots {st : State ℝ≥0} {T : Finset (Fin G.n)} {key : Labels G s}
    (h : RamBaseCase.HRL (s := s) st T key) :
    ∃ l : List (Fin G.n), l.Nodup ∧ l.toFinset = T ∧ l.length = st.w "hp_n" ∧
      ∀ j (hj : j < l.length), st.wa "hp_A" j = (l[j] : ℕ) := by
  obtain ⟨n, hn, -, -, -, hpos, -, hT⟩ := h
  refine ⟨(List.range n).pmap (fun j hj => (⟨st.wa "hp_A" j, (hpos.slots j hj).1⟩ : Fin G.n))
    (fun j hj => List.mem_range.mp hj), ?_, ?_, by simp [hn], fun j hj => by simp⟩
  · refine List.Nodup.pmap (fun a ha b hb e => ?_) List.nodup_range
    exact hpos.inj ha hb (Fin.mk.inj_iff.mp e)
  · ext u
    simp only [List.mem_toFinset, List.mem_pmap, List.mem_range]
    rw [← mem_T_iff hT u]
    simp only [IHeap.T, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
    · rintro ⟨j, hj, e⟩; exact ⟨j, hj, Fin.ext e⟩

end Frontier.CHD.IHeapLab
