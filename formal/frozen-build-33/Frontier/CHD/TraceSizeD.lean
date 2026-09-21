import Frontier.CHD.TraceSize
import Frontier.CHD.BMPlace

/-!
# Frontier.CHD.TraceSizeD — (B4') for agent-01's own-placement sums (tracker O12; owner agent-03)

**NON-GATE** (Layer A).  `ownSum_le`: over any `LogInv` log with root `([], r0)`, the own-placement sum of
`BMPlace` (`Log.ownSum`, which bounds the entries of every structure of the run by `bmsspD_place`) is at most
`(3(L0+1) + 3δ) · |U_root|`, given `|S| ≤ |U|` on every record and out-degrees at most `δ`.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n} {Ω : Type}
variable {τ : ℕ → ℕ} {L0 : ℕ} {lg : Log G s Ω}

/-- agent-01's `ownB` is at most the weight `wB` (using `p ≤ |S|`). -/
theorem ownB_le_wB (hL : LogInv τ L0 lg) {q : List ℕ} {r : CallRec G s Ω} (h : (q, r) ∈ lg) :
    ownB r ≤ wB r := by
  classical
  have hp := (hL.facts q r h).p_le
  unfold ownB wB Eout
  split_ifs <;> omega

/-- **(B4') over the log**: `ownSum lg ≤ (3(L0+1) + 3δ) · |U_root|`. -/
theorem ownSum_le (hL : LogInv τ L0 lg) (δ : ℕ) (hdeg : ∀ u, (Eout G {u}).card ≤ δ)
    (hSU : ∀ q r, (q, r) ∈ lg → r.S.card ≤ r.U.card) {r0 : CallRec G s Ω} (h0 : ([], r0) ∈ lg) :
    Log.ownSum lg ≤ (3 * (L0 + 1) + 3 * δ) * r0.U.card := by
  calc Log.ownSum lg = (lg.map fun x => ownB x.2).sum := rfl
    _ ≤ (lg.map fun x => wB x.2).sum :=
        Reselect.map_sum_le _ _ _ (fun qr hqr => ownB_le_wB hL (q := qr.1) hqr)
    _ ≤ (3 * (L0 + 1) + 3 * δ) * r0.U.card := wB_sum_le hL δ hdeg hSU h0

end BM
end CHD
end Frontier
