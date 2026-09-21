import Frontier.CHD.BMCost
import Frontier.Refine

/-!
# Frontier.CHD.SpineBridge — Layer-A glue for the RAM spine (B-L4)

Owner: agent-08.  NON-GATE.

The RAM main loop (BM.9–BM.24) is refined with `RefinesP.loopVar`, i.e. against the generic loop
runs `RelLoop R done` of one-iteration relations `R`.  This file defines the one-iteration
relation `IterRel` read off the `step` constructor of agent-01's `BMCost.LoopC` (its premises in
program order, its cost `iterCost + merge + sub-log cost`) on loop configurations `(i, σ, φ)`, and
proves the bridge `RelLoop IterRel done ⇒ LoopC` with matching total cost
(`k = c + cm + lg.cost`), plus the facts the loop rule needs (variant, totality shape).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.BM

open Frontier Graph Frontier.RAM

variable {G : Graph} {s : Fin G.n}

/-- A loop configuration: iteration index, loop state, persistent FindPivots state. -/
structure LoopCfg (G : Graph) (s : Fin G.n) (Φ : Type) (p : ℕ) where
  i : ℕ
  σ : LState G s p
  φ : Φ

section iter

variable {Φ Ω : Type} {p : ℕ} (DC : DCost) (sub : SubRelC G s Φ Ω) (lv : ℕ) (B : WLab G s)
  (τ : ℕ)

/-- The loop stops when the workload cap is exceeded or `D` is empty (BM.9). -/
def LoopDone (c : LoopCfg G s Φ p) : Prop := τ < c.σ.U.card ∨ c.σ.D.IsEmpty

/-- One iteration (BM.10–BM.24): the premises of `LoopC.step`, with cost
`iterCost + merge + (cost of the sub-call's log)`. -/
def IterRel (c c' : LoopCfg G s Φ p) (k : ℕ) : Prop :=
  ∃ (S0 : Finset (Fin G.n)) (Bi : WLab G s) (D1 : DS G s) (B'i : WLab G s)
    (Ui : Finset (Fin G.n)) (Di : DS G s) (d1 : Labels G s) (L' : List (Fin G.m))
    (piv' : Fin p → Fin G.n) (lg : Log G s Ω) (φ1 : Φ),
    c.σ.U.card ≤ τ ∧ ¬ c.σ.D.IsEmpty ∧
    PullSpec c.σ.D B S0 Bi D1 ∧ S0.card ≤ DC.M lv ∧ (S0.card < DC.M lv → D1.IsEmpty ∧ Bi = B) ∧
    sub c.σ.B' Bi (expand c.σ S0 Bi) c.σ.d c.φ (B'i, Ui, Di, d1) φ1 lg ∧
    L'.Nodup ∧
    (∀ e, e ∈ L' ↔ G.src e ∈ Ui ∧ Bi ≤ ext (d1 (G.src e)) e ∧ ext (d1 (G.src e)) e < B) ∧
    Reselect c.σ Ui (L'.foldl (relaxIns G s B (some Bi)) (d1, (D1.merge Di).deleteSet Ui)).1
      piv' ∧
    c' = { i := c.i + 1, σ := nextState B c.σ Bi B'i Ui D1 Di d1 L' piv', φ := φ1 } ∧
    k = iterCost DC lv c.σ S0 Ui L'.length + DC.merge lv (keyCount G s Di) + lg.cost

theorem Log.cost_append {lg lg' : Log G s Ω} : (lg ++ lg').cost = lg.cost + lg'.cost := by
  simp [Log.cost]

theorem Log.cost_shift (i : ℕ) (lg : Log G s Ω) : (lg.shift i).cost = lg.cost := by
  simp [Log.cost, Log.shift, List.map_map, Function.comp_def]

/-- **Bridge**: generic loop runs of `IterRel` are `LoopC` derivations, with total cost
`c + cm + lg.cost`. -/
theorem loopC_of_relLoop :
    ∀ {c c' : LoopCfg G s Φ p} {k : ℕ},
      RelLoop (IterRel (Ω := Ω) DC sub lv B τ) (LoopDone τ) c c' k →
      ∃ lg J cm cc, LoopC G s DC sub lv B τ c.i c.σ c.φ c'.σ c'.φ lg J cm cc ∧
        k = cc + cm + lg.cost := by
  intro c c' k h
  induction h with
  | stop a hd =>
    exact ⟨[], ∅, 0, 1, LoopC.stop a.i a.σ a.φ hd, by simp [Log.cost]⟩
  | step a a' a'' k k' hnd hR _ ih =>
    obtain ⟨lg, J, cm, cc, hL, hk'⟩ := ih
    obtain ⟨S0, Bi, D1, B'i, Ui, Di, d1, L', piv', lgs, φ1, hU, hD, hpull, hM, hSP, hsub, hnd', hmem,
      hres, rfl, rfl⟩ := hR
    refine ⟨lgs.shift a.i ++ lg, L'.toFinset ∪ J, DC.merge lv (keyCount G s Di) + cm,
      iterCost DC lv a.σ S0 Ui L'.length + cc,
      LoopC.step a.i a.σ a''.σ a.φ φ1 a''.φ S0 Bi D1 B'i Ui Di d1 L' piv' lgs lg J cm cc hU hD
        hpull hM hSP hsub hnd' hmem hres hL, ?_⟩
    rw [hk', Log.cost_append, Log.cost_shift]
    ring

end iter

end Frontier.CHD.BM
