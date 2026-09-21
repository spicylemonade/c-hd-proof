import Frontier.Density

/-!
# Frontier.Homes — homes of vertices at a call (PAPER_CHD §5.3; owner agent-03)

**NON-GATE** (Layer A, cost side, tracker O10).  At a call `X`, the HOME of a vertex is the child whose returned
set contains it; a vertex outside `U X` (a foreign leaf) is homed by its FIXED value: the child whose handled range
contains it.  An edge whose ends have different homes is either a CROSSING edge (both ends in `U X`, no child
contains both; `CostAggregate.Valid.cr_cross`) or a kind-(β) edge whose tail SPLITS the head's value at `X`
(`Density.Ranges.Split`, hence charged once globally by `beta_sum_le`).
-/

namespace Frontier.Density.Ranges

open Frontier.CostCharging

variable {ι V α : Type*} [LinearOrder α] {F : CallForest ι V α} (R : Ranges F) (val : V → α)

/-- The home of `v` at the call `X`. -/
noncomputable def home (X : ι) (v : V) : Option ι := by
  classical
  exact if h : ∃ Y, F.parent Y = some X ∧ v ∈ F.U Y then some h.choose
    else if h' : v ∉ F.U X ∧ ∃ Y, F.parent Y = some X ∧ R.inR Y (val v) then some h'.2.choose
    else none

variable {R val}

/-- A vertex of a child's returned set is homed at that child. -/
theorem home_of_mem {X Y : ι} {v : V} (hY : F.parent Y = some X) (hv : v ∈ F.U Y) :
    R.home val X v = some Y := by
  classical
  have h : ∃ Y, F.parent Y = some X ∧ v ∈ F.U Y := ⟨Y, hY, hv⟩
  unfold home
  rw [dif_pos h]
  congr 1
  obtain ⟨h1, h2⟩ := h.choose_spec
  by_contra hne
  exact Finset.disjoint_left.mp (F.siblings_disjoint _ _ X h1 hY hne) h2 hv

/-- A vertex outside `U X` whose value lies in a child's range is homed at that child. -/
theorem home_of_range {X Y : ι} {v : V} (hY : F.parent Y = some X) (hvX : v ∉ F.U X)
    (hr : R.inR Y (val v)) : R.home val X v = some Y := by
  classical
  have hno : ¬ ∃ Y, F.parent Y = some X ∧ v ∈ F.U Y := by
    rintro ⟨Y', hY', hv'⟩
    exact hvX (F.U_sub Y' X hY' hv')
  have h' : v ∉ F.U X ∧ ∃ Y, F.parent Y = some X ∧ R.inR Y (val v) := ⟨hvX, Y, hY, hr⟩
  unfold home
  rw [dif_neg hno, dif_pos h']
  congr 1
  obtain ⟨h1, h2⟩ := h'.2.choose_spec
  by_contra hne
  exact R.sib _ _ X h1 hY hne (val v) h2.1 h2.2 hr.1 hr.2

/-- **Different homes, both ends returned: a crossing edge** (no child contains both ends). -/
theorem cross_of_home_ne {X : ι} {u v : V} (hne : R.home val X u ≠ R.home val X v) :
    ∀ Y, F.parent Y = some X → ¬ (u ∈ F.U Y ∧ v ∈ F.U Y) := by
  rintro Y hY ⟨hu, hv⟩
  exact hne ((home_of_mem hY hu).trans (home_of_mem hY hv).symm)

/-- **Different homes, head foreign: the tail splits the head's value** (`Split`). -/
theorem split_of_home_ne {X : ι} {u v : V} (hu : u ∈ F.U X) (hvX : v ∉ F.U X) (hr : R.inR X (val v))
    (hne : R.home val X u ≠ R.home val X v) : R.Split u (val v) X := by
  refine ⟨hu, hr, fun Y hY huY hrY => hne ?_⟩
  exact (home_of_mem hY huY).trans (home_of_range hY hvX hrY).symm

/-- A child meeting a set `P` contributes a home value of `P`: the children meeting `P` are at most the distinct
homes of `P`'s members. -/
theorem card_children_meeting_le [Fintype ι] [DecidableEq ι] [DecidableEq V] (X : ι) (P : Finset V) :
    (Finset.univ.filter (fun Y => F.parent Y = some X ∧ (P ∩ F.U Y).Nonempty)).card ≤
      (P.image (R.home val X)).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun Y => some Y) ?_ ?_
  · intro Y hY
    obtain ⟨hYp, v, hv⟩ := (Finset.mem_filter.mp hY).2
    obtain ⟨hvP, hvU⟩ := Finset.mem_inter.mp hv
    exact Finset.mem_image.mpr ⟨v, hvP, home_of_mem hYp hvU⟩
  · intro Y1 _ Y2 _ h
    exact Option.some.inj h

end Frontier.Density.Ranges
