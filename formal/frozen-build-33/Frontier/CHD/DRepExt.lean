import Frontier.CHD.DRep

/-!
# DRepExt — the D representation survives history growth and label-table-only steps
(agent-02, B-L3/B-L4 glue, NON-GATE)

A strict relaxation extends the ghost history (`LabTab.HExt`).  Every stored D entry and separator
is a machine-label COPY, so the whole representation (`BlkRep`, `DRep`, `LiveRep`) transports along
`HExt` (`Rep.ext`).  Together with `DRep.of_unchanged` this lets the spine interleave label-table
fragments and D operations.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.DIns

open Frontier Frontier.CHD Frontier.CHD.DB Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD.MLab
  Frontier.CHD.LabTab

variable {G : Graph} {s : Fin G.n}

theorem SepRep.ext {st : State ℝ≥0} {H H' : Fin G.n → ℕ → List (Fin G.m)} {V V' : Fin G.n → ℕ}
    {bid : ℕ} {sp : WithBot (WLab G s)} (h : SepRep st H V bid sp) (hE : HExt H V H' V') :
    SepRep st H' V' bid sp := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  rcases h2 with h2 | ⟨m, q, hA, hR, hq⟩
  · exact Or.inl h2
  · exact Or.inr ⟨m, q, hA, Rep.ext hR hE, hq⟩

theorem BlkRep.ext {st : State ℝ≥0} {H H' : Fin G.n → ℕ → List (Fin G.m)} {V V' : Fin G.n → ℕ}
    {bid : ℕ} {b : Block (Fin G.n) (WLab G s)} (h : BlkRep st H V bid b) (hE : HExt H V H' V') :
    BlkRep st H' V' bid b := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1.ext hE, h2, fun x hx => (h3 x hx).ext hE, h4, h5⟩

theorem DRep.ext {st : State ℝ≥0} {H H' : Fin G.n → ℕ → List (Fin G.m)} {V V' : Fin G.n → ℕ}
    {bcap lv bse : ℕ} {D : DStr (Fin G.n) (WLab G s)} (h : DRep st H V bcap lv bse D)
    (hE : HExt H V H' V') : DRep st H' V' bcap lv bse D :=
  ⟨h.sz, h.szb, h.stkb, fun i hi => (h.blk i hi).ext hE, h.inj, h.bidb⟩

theorem LiveRep.ext {st : State ℝ≥0} {H H' : Fin G.n → ℕ → List (Fin G.m)} {V V' : Fin G.n → ℕ}
    {L : Live (Fin G.n) (WLab G s)} (h : LiveRep st H V L) (hE : HExt H V H' V') :
    LiveRep st H' V' L :=
  ⟨h.1, fun v => ⟨(h.2 v).1, fun i a hia => ((h.2 v).2 i a hia).ext hE⟩⟩

/-- The label-table arrays are disjoint from the D arrays, so B-LAB fragments keep `DRep`. -/
theorem labW_disj_dW : ∀ a ∈ labW, a ∉ dW := by decide
theorem labV_disj_dV : ∀ a ∈ labV, a ∉ dV := by decide

end Frontier.CHD.DIns
