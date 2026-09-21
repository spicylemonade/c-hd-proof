import Frontier.CostAggregate

/-!
# Frontier/Counterexamples (agent-07, reviewer #1 lane): kernel-checked interface counterexamples. NON-GATE.

These are small facts. Each one shows that an abstract hypothesis of a kernel-checked C-HD lemma CANNOT be discharged in a
situation the real algorithm produces. Each points to a required interface fix. None of them is a result.

## O22(b): the Q-witness of the source (history)
The first `CostAggregate.Valid` (sha 4ad2cd0a) demanded, for every full call `X` and EVERY `v ∈ Q X`, a witness in-edge
`wit X v ∈ inE v`. The real run can put the source `s` into `Q X` of one full call with no inserting event. This was observed in
603/4000 runs of agent-07's simulator. If `s` has no in-edge, that `Valid` was unsatisfiable.
- agent-06 fixed it at 12:45 (CostAggregate b0c47bf6): `Valid … src` exempts `src` from `wit_mem` and adds `src_once`.
- The lemma below is restated for the FIXED `Valid`. The exemption is exactly the source: any OTHER `Q`-vertex of a full call
  must still have an in-edge. The real run satisfies this, since such a vertex was inserted by a relaxation along an in-edge.
-/

namespace Frontier.Counterexamples

open Frontier.CostAggregate Finset

set_option linter.unusedSectionVars false

variable {ι V E α : Type*} [Fintype ι] [Fintype V] [Fintype E] [DecidableEq ι] [DecidableEq V]
  [DecidableEq E] [LinearOrder α]

/-- For the fixed `Valid` (with the source exemption): a non-source `Q`-vertex of a full call without in-edges refutes
`Valid`. So the only exemption is the source, and `wit_mem` still needs a real in-edge witness for every other `Q`-vertex. -/
theorem not_valid_of_Q_vertex_without_inedge (C : CallCounters ι V E α) {t k c Lmax M0 : ℕ}
    {inE : V → Finset E} {wit : ι → V → E} {src : V} {X : ι} {v : V}
    (hfull : C.full X = true) (hQ : v ∈ C.Q X) (hv : v ≠ src) (hin : inE v = ∅) :
    ¬ C.Valid t k c Lmax M0 inE wit src := by
  intro h
  have hmem := h.wit_mem X hfull v hQ hv
  rw [hin] at hmem
  exact absurd hmem (Finset.notMem_empty _)

end Frontier.Counterexamples

#print axioms Frontier.Counterexamples.not_valid_of_Q_vertex_without_inedge
