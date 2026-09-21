import Frontier.CHD.BMCost

/-!
# Base-case glue (Layer A side): the store as a vertex set with keys = current labels

In `BaseLoopC` every stored key equals the current label (`BM.BInv.stored`), so the RAM keeps only
the vertex set `T` of the heap; `Dof T d` is the induced store.  `relaxIns` with `lo = none`
preserves this shape (`relaxIns_Dof`); `outList u` is the list of out-edges of `u` in increasing
edge order (the CSR slot order of L6 v2), which `Enumerates` `{u}`.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-- The store with keys = current labels on the vertex set `T`. -/
def Dof (T : Finset (Fin G.n)) (d : Labels G s) : DS G s := fun y => if y ∈ T then some (d y) else none

theorem Dof_apply (T : Finset (Fin G.n)) (d : Labels G s) (y : Fin G.n) :
    Dof T d y = if y ∈ T then some (d y) else none := rfl

open Classical in
/-- **Relaxation keeps the shape**: with keys = labels, `relaxIns B none` adds the head of a valid
relaxation to the set. -/
theorem relaxIns_Dof (B : WLab G s) (T : Finset (Fin G.n)) (d : Labels G s) (e : Fin G.m) :
    relaxIns G s B none (d, Dof T d) e =
      if ValidRelax G s d B e then
        (Function.update d (G.dst e) (ext (d (G.src e)) e),
          Dof (insert (G.dst e) T) (Function.update d (G.dst e) (ext (d (G.src e)) e)))
      else (d, Dof T d) := by
  unfold relaxIns
  by_cases hv : ValidRelax G s d B e
  · simp only [hv, if_true]
    congr 1
    funext y
    simp only [DS.insert, Dof_apply, Finset.mem_insert]
    by_cases hy : y = G.dst e
    · subst hy
      simp only [Function.update_self, true_or, if_true]
      by_cases hT : G.dst e ∈ T
      · simp only [hT, if_true, DS.mergeVal]
        have hle := hv.1
        rw [min_eq_right hle]
      · simp only [hT, if_false, DS.mergeVal]
    · simp only [Function.update_of_ne hy, hy, false_or]
      exact Dof_apply T d y
  · simp only [hv, if_false]

/-- The out-edges of `u` in increasing edge order. -/
def outList (u : Fin G.n) : List (Fin G.m) :=
  (List.finRange G.m).filter fun e => decide (G.src e = u)

theorem outList_enumerates (u : Fin G.n) : Enumerates G (outList u) {u} := by
  refine ⟨(List.nodup_finRange G.m).filter _, fun e => ?_⟩
  simp [outList]

theorem Dof_deleteSet (T : Finset (Fin G.n)) (d : Labels G s) (u : Fin G.n) :
    (Dof T d).deleteSet {u} = Dof (T.erase u) d := by
  funext y
  simp only [DS.deleteSet, Dof_apply, Finset.mem_singleton, Finset.mem_erase]
  by_cases hy : y = u <;> simp [hy]

theorem Dof_isEmpty_iff (T : Finset (Fin G.n)) (d : Labels G s) :
    (Dof T d).IsEmpty ↔ T = ∅ := by
  constructor
  · intro h
    ext y
    simp only [Finset.notMem_empty, iff_false]
    intro hy
    have := h y
    simp [Dof_apply, hy] at this
  · rintro rfl y
    simp [Dof_apply]

/-- With keys = labels, the extracted minimum is not yet in `U` (`BInv.keysU`). -/
theorem notMem_U_of_bInv {B : WLab G s} {S : Finset (Fin G.n)} {d0 d : Labels G s}
    {T U : Finset (Fin G.n)} (h : BInv G s B S d0 d (Dof T d) U) {u : Fin G.n} (hu : u ∈ T) :
    u ∉ U :=
  h.keysU u (d u) (by simp [Dof_apply, hu])

theorem insertMany_empty_Dof (S : Finset (Fin G.n)) (d0 : Labels G s) :
    insertMany G s DS.empty S d0 = Dof S d0 := by
  funext y
  simp only [insertMany, DS.empty, Dof_apply, DS.mergeVal]

end Frontier.CHD.BM
