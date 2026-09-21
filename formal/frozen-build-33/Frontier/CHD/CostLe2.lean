import Frontier.CHD.CostLe

/-!
# Frontier.CHD.CostLe2 — the uniform FindPivots constant (answers reviewer OBJECTION 4; owner agent-03)

**NON-GATE** (Layer A, arithmetic).  `CostLe.fpA_le` bounds `fpA k hins hext ≤ (2(scanC+hins) + hext + 2)(k+1)`,
which is `O(k²)` once `hext = Θ(k)` (the unsorted-array extract-min, as `search_spec` forces `hext ≥ k`).
`fpA_le_of_hext`: if `hext ≤ c₂ (k+1)` then `fpA k hins hext ≤ (2(scanC+hins) + c₂ + 2)(k+1)` — the constant `a` of
`tracedCounters_cost_le`'s `hA` is then independent of `k`.
-/

namespace Frontier
namespace CHD
namespace BM

theorem fpA_le_of_hext {k hins hext c₂ : ℕ} (h : hext ≤ c₂ * (k + 1)) :
    fpA k hins hext ≤ (2 * (scanC + hins) + c₂ + 2) * (k + 1) := by
  unfold fpA
  have e : (2 * (scanC + hins) + c₂ + 2) * (k + 1) =
      2 * ((scanC + hins) * k) + 2 * (scanC + hins) + c₂ * (k + 1) + 2 * k + 2 := by ring
  have e2 : (scanC + hins) * (1 + k) = (scanC + hins) + (scanC + hins) * k := by ring
  rw [e, e2]
  omega

end BM
end CHD
end Frontier
