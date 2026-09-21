import Frontier.CHD.LtBiTest
import Frontier.CHD.SpineIter

/-!
# LtBiI — the expansion test instantiates the spine's `LtI` (BM.12; agent-02, NON-GATE)

`ltBi_ltI`: `ltBi KBi "sp.bif"` (`sp.lt := [d px < B_i]`, the bound `B_i` in the spine's block
`KBi`) is an instance of `RamSpine.LtI` for the state predicate `ltKR d H c0 Bi` (label table,
`B_i` in `KBi`, `1 < cap`, `n = |V|`), with word footprint `ltW`, value footprint `["sp.yl"]` and
cost `≤ 22`.  This is the `hLt` hypothesis of `firstHalf_spec` / `loop2_spec`.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.WinScan

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.LabTab Frontier.CHD.MLab
  WExpr Stmt

variable {G : Graph} {s : Fin G.n}

/-- The state predicate of the expansion test: the label table, the bound `B_i` in `KBi`, the word
capacity and `n = |V|`. -/
def ltKR (d : Labels G s) (H : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ) (Bi : WLab G s)
    (st : State ℝ≥0) : Prop :=
  LabAt st d H c0 ∧ WHolds st RamSpine.KBi "sp.bif" H (vc st) Bi ∧ 1 < st.cap ∧ st.w "n" = G.n

theorem ltHyg_KBi : LtHyg RamSpine.KBi "sp.bif" := ⟨by decide, by decide⟩

/-- **The expansion test instantiates `LtI`** (writes `ltW`, the value register `sp.yl`, cost
`≤ 22`). -/
theorem ltBi_ltI (d : Labels G s) (H : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ) (Bi : WLab G s)
    {inst : DecidablePred (fun v => ∃ h : v < G.n, d ⟨v, h⟩ < Bi)} :
    @RamSpine.LtI _ realOps (ltBi RamSpine.KBi "sp.bif") (ltKR d H c0 Bi)
      (fun v => ∃ h : v < G.n, d ⟨v, h⟩ < Bi) inst 22 ltW ["sp.yl"] where
  run st hK hpx := by
    obtain ⟨hL, hKh, hcap, hn⟩ := hK
    have hv : st.w "px" < G.n := hn ▸ hpx
    refine (ltBi_spec ltHyg_KBi st d H c0 hL ⟨st.w "px", hv⟩ rfl Bi hKh hcap).mono ?_
    rintro r ⟨h1, hU, hc1, hc2, hLr, hKr⟩
    refine ⟨?_, hU, hc1, hc2, hLr, hKr, hU.cap ▸ hcap,
      by rw [hU.wreg "n" (by decide)]; exact hn⟩
    rw [h1]
    by_cases hlt : d ⟨st.w "px", hv⟩ < Bi
    · rw [if_pos hlt, if_pos ⟨hv, hlt⟩]
    · rw [if_neg hlt, if_neg (fun ⟨_, h'⟩ => hlt h')]
  frame st r hK hU hc := by
    obtain ⟨hL, hKh, hcap, hn⟩ := hK
    refine ⟨hL.of_unchanged hU (by decide) (by decide) hc, ?_, hU.cap ▸ hcap,
      by rw [hU.wreg "n" (by decide)]; exact hn⟩
    rw [vc_of_unchanged hU (by decide)]
    exact hKh.of_unchanged hU (by decide) (by decide) (by decide)
  lt_mem := by decide
  regs := by decide

end Frontier.CHD.WinScan
