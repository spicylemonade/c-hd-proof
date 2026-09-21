import Frontier.CHD.BMLazy
import Frontier.Refine

/-!
# Frontier.CHD.SpineBridgeD — Layer-A glue for the RAM spine over the lazy `D` (BMSSPD)

Owner: agent-08.  NON-GATE.

As `SpineBridge` for `BMCost.LoopC`, but for agent-01's `BMLazy.LoopD` (concrete lazy structures,
actual costs), which is what Layer B refines: `IterRelD` is one iteration (the premises of
`LoopD.step`, cost `iterCostD + merge + sub-log cost`) on configurations `(i, cs, φ)`, and
`loopD_of_relLoop` turns generic loop runs into `LoopD` derivations.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.BM

open Frontier Graph Frontier.RAM

variable {G : Graph} {s : Fin G.n}

/-- A loop configuration over the lazy structure. -/
structure LoopCfgD (G : Graph) (s : Fin G.n) (Φ : Type) (p : ℕ) where
  i : ℕ
  cs : CSt G s p
  φ : Φ

section iter

variable {Φ Ω : Type} {p : ℕ} (ops : DOps G s) (T : ℕ) (sub : SubRelD G s Φ Ω) (B : WLab G s)
  (τ : ℕ)

/-- The loop stops when the cap is exceeded or the view of `D` is empty (BM.9). -/
def LoopDoneD (c : LoopCfgD G s Φ p) : Prop := τ < c.cs.U.card ∨ (c.cs.g.view c.cs.Dc).IsEmpty

/-- One iteration (BM.10–BM.24) over the lazy structure: the premises of `LoopD.step`. -/
def IterRelD (c c' : LoopCfgD G s Φ p) (k : ℕ) : Prop :=
  ∃ (ks : List (Fin G.n)) (Bi : WLab G s) (g1 : DGl G s) (Dc1 : DStrM G s) (cp : ℕ)
    (B'i : WLab G s) (Ui : Finset (Fin G.n)) (Dci : DStrM G s) (d1 : Labels G s) (g2 : DGl G s)
    (lUi : List (Fin G.n)) (L' : List (Fin G.m)) (piv' : Fin p → Fin G.n) (lres : List (Fin G.n))
    (lg : Log G s Ω) (φ1 : Φ),
    c.cs.U.card ≤ τ ∧ ¬ (c.cs.g.view c.cs.Dc).IsEmpty ∧
    pullC ops T c.cs.g c.cs.Dc = (ks, Bi, g1, Dc1, cp) ∧
    sub c.cs.B' Bi (expand c.cs.lit ks.toFinset Bi) c.cs.d c.φ g1 (B'i, Ui, Dci, d1) φ1 g2 lg ∧
    lUi.Nodup ∧ lUi.toFinset = Ui ∧
    L'.Nodup ∧
    (∀ e, e ∈ L' ↔ G.src e ∈ Ui ∧ Bi ≤ ext (d1 (G.src e)) e ∧ ext (d1 (G.src e)) e < B) ∧
    Reselect c.cs.lit Ui (L'.foldl (relaxInsCc ops T B (some Bi))
      ⟨d1, (delC g2 lUi).1, (ops.merge T Dc1 Dci).1, 0⟩).d piv' ∧
    lres.Nodup ∧ lres.toFinset = reselected c.cs.lit Ui piv' ∧
    c' = { i := c.i + 1, cs := nextD ops T B c.cs Bi B'i Ui Dc1 Dci d1 g2 lUi L' piv' lres,
           φ := φ1 } ∧
    k = iterCostD ops T B c.cs ks.toFinset cp Bi Ui Dc1 Dci d1 g2 lUi L' lres
      + (ops.merge T Dc1 Dci).2 + lg.cost

/-- **Bridge**: generic loop runs of `IterRelD` are `LoopD` derivations, with total cost
`c + cm + lg.cost`. -/
theorem loopD_of_relLoop :
    ∀ {c c' : LoopCfgD G s Φ p} {k : ℕ},
      RelLoop (IterRelD (Ω := Ω) ops T sub B τ) (LoopDoneD τ) c c' k →
      ∃ lg J cm cc, LoopD G s ops T sub B τ c.i c.cs c.φ c'.cs c'.φ lg J cm cc ∧
        k = cc + cm + lg.cost := by
  intro c c' k h
  induction h with
  | stop a hd =>
    exact ⟨[], ∅, 0, 1, LoopD.stop a.i a.cs a.φ hd, by simp [Log.cost]⟩
  | step a a' a'' k k' hnd hR _ ih =>
    obtain ⟨lg, J, cm, cc, hL, hk'⟩ := ih
    obtain ⟨ks, Bi, g1, Dc1, cp, B'i, Ui, Dci, d1, g2, lUi, L', piv', lres, lgs, φ1, hU, hD, hpull,
      hsub, hnd1, hlU, hnd2, hmem, hres, hnd3, hlres, rfl, rfl⟩ := hR
    refine ⟨lgs.shift a.i ++ lg, L'.toFinset ∪ J, (ops.merge T Dc1 Dci).2 + cm,
      iterCostD ops T B a.cs ks.toFinset cp Bi Ui Dc1 Dci d1 g2 lUi L' lres + cc,
      LoopD.step a.i a.cs a''.cs a.φ φ1 a''.φ ks Bi g1 Dc1 cp B'i Ui Dci d1 g2 lUi L' piv' lres lgs
        lg J cm cc hU hD hpull hsub hnd1 hlU hnd2 hmem hres hnd3 hlres hL, ?_⟩
    rw [hk']
    simp only [Log.cost, Log.shift, List.map_append, List.sum_append, List.map_map,
      Function.comp_def]
    ring

end iter

end Frontier.CHD.BM
