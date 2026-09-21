import Frontier.RAMLogic
import Frontier.RAMRep
import Frontier.CHD.L6.Util

/-!
# Allocation of a list of arrays (agent-10, spine prologue tooling)

`allocWs L` allocates, for every pair `(arr, reg)` of `L`, the word array `arr` with length
`w reg` (all cells `0`); `allocVs L` does the same for value arrays (cells `ops.zero`).  Sizes are
read from registers, so the prologue first computes them (e.g. `(LF + 2) · gN`).
`allocWs_runs` / `allocVs_runs`: exact lengths and contents, frame (only the allocated arrays
change), exact cost `Σ (size + 1) + 1`.
NON-GATE (Layer B tooling).
-/

namespace Frontier.CHD.AllocList

open Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V}

/-- Allocate the word arrays of `L` (array name, size register). -/
def allocWs : List (String × String) → Stmt
  | [] => .skip
  | (a, r) :: rest => .seq (.walloc a (.var r)) (allocWs rest)

/-- Allocate the value arrays of `L` (array name, size register). -/
def allocVs : List (String × String) → Stmt
  | [] => .skip
  | (a, r) :: rest => .seq (.valloc a (.var r)) (allocVs rest)

/-- The cost of an allocation list read in state `st`. -/
def allocCost (st : State V) (L : List (String × String)) : ℕ :=
  (L.map (fun p => st.w p.2 + 1)).sum + 1

theorem allocWs_runs (L : List (String × String)) (hnd : (L.map Prod.fst).Nodup)
    (st : State V) :
    Runs ops (allocWs L) st (fun r => (∀ p ∈ L, r.wlen p.1 = st.w p.2 ∧ ∀ i, r.wa p.1 i = 0) ∧
      Unchanged st r (L.map Prod.fst) [] [] [] ∧ r.cost = st.cost + allocCost st L) := by
  induction L generalizing st with
  | nil =>
    refine runs_skip ⟨by simp, by simp, by simp [allocCost]⟩
  | cons p rest ih =>
    obtain ⟨a, reg⟩ := p
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨ha, hnd⟩ := hnd
    refine runs_seq (runs_walloc (k := st.w reg) (evalW_var' _ _) ?_)
    refine (ih hnd _).mono ?_
    rintro r ⟨hr, hU, hc⟩
    have hw : ∀ x, ((st.allocW a (st.w reg)).charge (st.w reg + 1)).w x = st.w x := fun x => rfl
    refine ⟨?_, ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · have e := hU.warr a ha
        refine ⟨?_, fun i => ?_⟩
        · rw [e.2]; simp [State.allocW, State.charge]
        · rw [e.1]; simp [State.allocW, State.charge]
      · have := hr q hq
        rw [hw] at this
        exact this
    · have h0 : Unchanged st ((st.allocW a (st.w reg)).charge (st.w reg + 1))
          (a :: rest.map Prod.fst) [] [] [] := by
        rw [unchanged_charge_iff, unchanged_allocW_iff (by simp)]
        simp
      exact h0.trans (hU.mono (by intro x hx; simp [hx]) (by simp) (by simp) (by simp))
    · rw [hc]
      simp only [allocCost, List.map_cons, List.sum_cons, State.charge_cost]
      have : (rest.map (fun p => ((st.allocW a (st.w reg)).charge (st.w reg + 1)).w p.2 + 1)) =
          (rest.map (fun p => st.w p.2 + 1)) := by
        congr 1
      rw [this]
      simp only [State.allocW]
      ring

theorem allocVs_runs (L : List (String × String)) (hnd : (L.map Prod.fst).Nodup)
    (st : State V) :
    Runs ops (allocVs L) st (fun r => (∀ p ∈ L, r.vlen p.1 = st.w p.2 ∧ ∀ i, r.va p.1 i = ops.zero) ∧
      Unchanged st r [] (L.map Prod.fst) [] [] ∧ r.cost = st.cost + allocCost st L) := by
  induction L generalizing st with
  | nil =>
    refine runs_skip ⟨by simp, by simp, by simp [allocCost]⟩
  | cons p rest ih =>
    obtain ⟨a, reg⟩ := p
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨ha, hnd⟩ := hnd
    refine runs_seq (runs_valloc (k := st.w reg) (evalW_var' _ _) ?_)
    refine (ih hnd _).mono ?_
    rintro r ⟨hr, hU, hc⟩
    have hw : ∀ x, ((st.allocV a (st.w reg) ops.zero).charge (st.w reg + 1)).w x = st.w x :=
      fun x => rfl
    refine ⟨?_, ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · have e := hU.varr a ha
        refine ⟨?_, fun i => ?_⟩
        · rw [e.2]; simp [State.allocV, State.charge]
        · rw [e.1]; simp [State.allocV, State.charge]
      · have := hr q hq
        rw [hw] at this
        exact this
    · have h0 : Unchanged st ((st.allocV a (st.w reg) ops.zero).charge (st.w reg + 1))
          [] (a :: rest.map Prod.fst) [] [] := by
        rw [unchanged_charge_iff, unchanged_allocV_iff (by simp)]
        simp
      exact h0.trans (hU.mono (by simp) (by intro x hx; simp [hx]) (by simp) (by simp))
    · rw [hc]
      simp only [allocCost, List.map_cons, List.sum_cons, State.charge_cost]
      have : (rest.map (fun p => ((st.allocV a (st.w reg) ops.zero).charge (st.w reg + 1)).w p.2 + 1)) =
          (rest.map (fun p => st.w p.2 + 1)) := by
        congr 1
      rw [this]
      simp only [State.allocV]
      ring

end Frontier.CHD.AllocList
