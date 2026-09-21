import Frontier.CHD.FPBridge

/-!
# Frontier.CHD.FPBridge2 — the pivot groups of an invocation are duplicate-free and nonempty (owner agent-03)

**NON-GATE** (Layer A).  For agent-01's `RamBody.FPB` (`(Gs[j]).Nodup`): every group of `forestGroups S Q k trees` over a
forest satisfying `FInv` (parent-first trees of `≥ k` vertices) is nonempty, duplicate-free and inside `S \ Q`
(agent-03's `forest_groups_spec`).
-/

namespace Frontier
namespace CHD

open Frontier Graph Frontier.CHD.Partition

variable {G : Graph} {s : Fin G.n}

theorem forestGroups_facts {c : FPCtx G s} {ι : IState G s} (hF : FInv c ι) (hk : 2 ≤ c.k)
    (S Q : Finset (Fin G.n)) :
    ∀ g ∈ forestGroups S Q c.k ι.trees, g ≠ [] ∧ g.Nodup ∧ ∀ x ∈ g, x ∈ S ∧ x ∉ Q :=
  (forest_groups_spec S Q hk ι.trees hF.pf hF.size).1

theorem forestGroups_getElem_nodup {c : FPCtx G s} {ι : IState G s} (hF : FInv c ι) (hk : 2 ≤ c.k)
    (S Q : Finset (Fin G.n)) (j : ℕ) (hj : j < (forestGroups S Q c.k ι.trees).length) :
    ((forestGroups S Q c.k ι.trees)[j]).Nodup :=
  (forestGroups_facts hF hk S Q _ (List.getElem_mem hj)).2.1

end CHD
end Frontier
