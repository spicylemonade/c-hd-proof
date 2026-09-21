import Frontier.CHD.SpineBridgeD

/-!
# SpineLoopW — weighted iterations: own work at `Ko`, sub-calls at `K` (agent-08, B-L4, NON-GATE)

For the level induction with ONE sub-call constant `K`, an iteration's own work (its `iterCostD`
and merge cost) is weighted by `Ko` and its sub-call log by `K`.  `IterRelW` is `IterRelD` with this
weighted cost; `loopDW_of_relLoop` turns loop runs of it into `LoopD` derivations with
`kw + Ko = Ko · (cc + cm) + K · lg.cost + 1` (the final test has unit weight in the run and weight
`Ko` in `cc`).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.BM

open Frontier Graph Frontier.RAM

variable {G : Graph} {s : Fin G.n}

section iterW

variable {Φ Ω : Type} {p : ℕ} (ops : DOps G s) (T : ℕ) (sub : SubRelD G s Φ Ω) (B : WLab G s)
  (τ : ℕ) (Ko K : ℕ)

/-- One iteration (the premises of `LoopD.step`) with the weighted cost
`Ko · (iterCostD + merge) + K · (sub-call log)`. -/
def IterRelW (c c' : LoopCfgD G s Φ p) (kw : ℕ) : Prop :=
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
    kw = Ko * (iterCostD ops T B c.cs ks.toFinset cp Bi Ui Dc1 Dci d1 g2 lUi L' lres
      + (ops.merge T Dc1 Dci).2) + K * lg.cost

variable {ops T sub B τ Ko K}

/-- A weighted iteration is an unweighted one. -/
theorem IterRelW.toD {c c' : LoopCfgD G s Φ p} {kw : ℕ} (h : IterRelW ops T sub B τ Ko K c c' kw) :
    ∃ k, IterRelD (Ω := Ω) ops T sub B τ c c' k := by
  obtain ⟨ks, Bi, g1, Dc1, cp, B'i, Ui, Dci, d1, g2, lUi, L', piv', lres, lg, φ1, h1, h2, h3, h4, h5,
    h6, h7, h8, h9, h10, h11, h12, -⟩ := h
  exact ⟨_, ks, Bi, g1, Dc1, cp, B'i, Ui, Dci, d1, g2, lUi, L', piv', lres, lg, φ1, h1, h2, h3, h4,
    h5, h6, h7, h8, h9, h10, h11, h12, rfl⟩

/-- An unweighted iteration is a weighted one. -/
theorem IterRelD.toW {c c' : LoopCfgD G s Φ p} {k : ℕ} (h : IterRelD (Ω := Ω) ops T sub B τ c c' k) :
    ∃ kw, IterRelW ops T sub B τ Ko K c c' kw := by
  obtain ⟨ks, Bi, g1, Dc1, cp, B'i, Ui, Dci, d1, g2, lUi, L', piv', lres, lg, φ1, h1, h2, h3, h4, h5,
    h6, h7, h8, h9, h10, h11, h12, -⟩ := h
  exact ⟨_, ks, Bi, g1, Dc1, cp, B'i, Ui, Dci, d1, g2, lUi, L', piv', lres, lg, φ1, h1, h2, h3, h4,
    h5, h6, h7, h8, h9, h10, h11, h12, rfl⟩

/-- **Bridge**: loop runs of weighted iterations are `LoopD` derivations; the weighted total plus
`Ko` is `Ko · (cc + cm) + K · lg.cost + 1`. -/
theorem loopDW_of_relLoop :
    ∀ {c c' : LoopCfgD G s Φ p} {kw : ℕ},
      RelLoop (IterRelW (Ω := Ω) ops T sub B τ Ko K) (LoopDoneD τ) c c' kw →
      ∃ lg J cm cc, LoopD G s ops T sub B τ c.i c.cs c.φ c'.cs c'.φ lg J cm cc ∧
        kw + Ko = Ko * (cc + cm) + K * lg.cost + 1 := by
  intro c c' kw h
  induction h with
  | stop a hd =>
    exact ⟨[], ∅, 0, 1, LoopD.stop a.i a.cs a.φ hd, by simp [Log.cost]; ring⟩
  | step a a' a'' k k' hnd hR _ ih =>
    obtain ⟨lg, J, cm, cc, hL, hk'⟩ := ih
    obtain ⟨ks, Bi, g1, Dc1, cp, B'i, Ui, Dci, d1, g2, lUi, L', piv', lres, lgs, φ1, hU, hD, hpull,
      hsub, hnd1, hlU, hnd2, hmem, hres, hnd3, hlres, rfl, rfl⟩ := hR
    refine ⟨lgs.shift a.i ++ lg, L'.toFinset ∪ J, (ops.merge T Dc1 Dci).2 + cm,
      iterCostD ops T B a.cs ks.toFinset cp Bi Ui Dc1 Dci d1 g2 lUi L' lres + cc,
      LoopD.step a.i a.cs a''.cs a.φ φ1 a''.φ ks Bi g1 Dc1 cp B'i Ui Dci d1 g2 lUi L' piv' lres lgs
        lg J cm cc hU hD hpull hsub hnd1 hlU hnd2 hmem hres hnd3 hlres hL, ?_⟩
    have hsh : (lgs.shift a.i ++ lg).cost = lgs.cost + lg.cost := by
      simp only [Log.cost, Log.shift, List.map_append, List.sum_append, List.map_map,
        Function.comp_def]
    rw [hsh]
    have e : Ko * (iterCostD ops T B a.cs ks.toFinset cp Bi Ui Dc1 Dci d1 g2 lUi L' lres + cc +
        ((ops.merge T Dc1 Dci).2 + cm)) =
        Ko * (iterCostD ops T B a.cs ks.toFinset cp Bi Ui Dc1 Dci d1 g2 lUi L' lres +
          (ops.merge T Dc1 Dci).2) + Ko * (cc + cm) := by ring
    rw [e]
    have e2 : K * (lgs.cost + lg.cost) = K * lgs.cost + K * lg.cost := by ring
    rw [e2]
    omega

end iterW

/-! ## Iterations with their use

The `D` layer's resource counter is a second resource of the loop, charged `2` per unit of the
iteration's own work and of its sub-call's log.  `IterRelU` pairs the configuration with the use
spent so far; its weighted RAM cost is `IterRelW`'s. -/

section iterU

variable {Φ Ω : Type} {p : ℕ} (ops : DOps G s) (T : ℕ) (sub : SubRelD G s Φ Ω) (B : WLab G s)
  (τ : ℕ) (Ko K : ℕ)

/-- One weighted iteration on configurations paired with the use spent so far, which grows by
`2 · (iterCostD + merge) + 2 · (sub-call log)` (= the cost of `IterRelW` at weights `2, 2`). -/
def IterRelU (a a' : LoopCfgD G s Φ p × ℕ) (kw : ℕ) : Prop :=
  ∃ (ks : List (Fin G.n)) (Bi : WLab G s) (g1 : DGl G s) (Dc1 : DStrM G s) (cp : ℕ)
    (B'i : WLab G s) (Ui : Finset (Fin G.n)) (Dci : DStrM G s) (d1 : Labels G s) (g2 : DGl G s)
    (lUi : List (Fin G.n)) (L' : List (Fin G.m)) (piv' : Fin p → Fin G.n) (lres : List (Fin G.n))
    (lg : Log G s Ω) (φ1 : Φ),
    a.1.cs.U.card ≤ τ ∧ ¬ (a.1.cs.g.view a.1.cs.Dc).IsEmpty ∧
    pullC ops T a.1.cs.g a.1.cs.Dc = (ks, Bi, g1, Dc1, cp) ∧
    sub a.1.cs.B' Bi (expand a.1.cs.lit ks.toFinset Bi) a.1.cs.d a.1.φ g1 (B'i, Ui, Dci, d1) φ1 g2
      lg ∧
    lUi.Nodup ∧ lUi.toFinset = Ui ∧
    L'.Nodup ∧
    (∀ e, e ∈ L' ↔ G.src e ∈ Ui ∧ Bi ≤ ext (d1 (G.src e)) e ∧ ext (d1 (G.src e)) e < B) ∧
    Reselect a.1.cs.lit Ui (L'.foldl (relaxInsCc ops T B (some Bi))
      ⟨d1, (delC g2 lUi).1, (ops.merge T Dc1 Dci).1, 0⟩).d piv' ∧
    lres.Nodup ∧ lres.toFinset = reselected a.1.cs.lit Ui piv' ∧
    a'.1 = { i := a.1.i + 1, cs := nextD ops T B a.1.cs Bi B'i Ui Dc1 Dci d1 g2 lUi L' piv' lres,
             φ := φ1 } ∧
    kw = Ko * (iterCostD ops T B a.1.cs ks.toFinset cp Bi Ui Dc1 Dci d1 g2 lUi L' lres
      + (ops.merge T Dc1 Dci).2) + K * lg.cost ∧
    a'.2 = a.2 + (2 * (iterCostD ops T B a.1.cs ks.toFinset cp Bi Ui Dc1 Dci d1 g2 lUi L' lres
      + (ops.merge T Dc1 Dci).2) + 2 * lg.cost)

variable {ops T sub B τ Ko K}

/-- The configuration part of an iteration with its use is a weighted iteration. -/
theorem IterRelU.toW {a a' : LoopCfgD G s Φ p × ℕ} {kw : ℕ}
    (h : IterRelU (Ω := Ω) ops T sub B τ Ko K a a' kw) :
    IterRelW (Ω := Ω) ops T sub B τ Ko K a.1 a'.1 kw := by
  obtain ⟨ks, Bi, g1, Dc1, cp, B'i, Ui, Dci, d1, g2, lUi, L', piv', lres, lg, φ1, h1, h2, h3, h4, h5,
    h6, h7, h8, h9, h10, h11, h12, h13, -⟩ := h
  exact ⟨ks, Bi, g1, Dc1, cp, B'i, Ui, Dci, d1, g2, lUi, L', piv', lres, lg, φ1, h1, h2, h3, h4,
    h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- The use only grows. -/
theorem IterRelU.le_snd {a a' : LoopCfgD G s Φ p × ℕ} {kw : ℕ}
    (h : IterRelU (Ω := Ω) ops T sub B τ Ko K a a' kw) : a.2 ≤ a'.2 := by
  obtain ⟨ks, Bi, g1, Dc1, cp, B'i, Ui, Dci, d1, g2, lUi, L', piv', lres, lg, φ1, -, -, -, -, -,
    -, -, -, -, -, -, -, -, h14⟩ := h
  omega

/-- A use-weighted iteration (weights `2, 2`) is an iteration with its use, at every use so far. -/
theorem IterRelW.toU_use {c c' : LoopCfgD G s Φ p} {ku : ℕ}
    (h : IterRelW (Ω := Ω) ops T sub B τ 2 2 c c' ku) (u : ℕ) :
    ∃ kw, IterRelU (Ω := Ω) ops T sub B τ Ko K (c, u) (c', u + ku) kw := by
  obtain ⟨ks, Bi, g1, Dc1, cp, B'i, Ui, Dci, d1, g2, lUi, L', piv', lres, lg, φ1, h1, h2, h3, h4, h5,
    h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨_, ks, Bi, g1, Dc1, cp, B'i, Ui, Dci, d1, g2, lUi, L', piv', lres, lg, φ1, h1, h2, h3, h4,
    h5, h6, h7, h8, h9, h10, h11, h12, rfl, by rw [h13]⟩

/-- A weighted iteration is an iteration with its use, at every use so far. -/
theorem IterRelW.toU_cost {c c' : LoopCfgD G s Φ p} {kw : ℕ}
    (h : IterRelW (Ω := Ω) ops T sub B τ Ko K c c' kw) (u : ℕ) :
    ∃ u', IterRelU (Ω := Ω) ops T sub B τ Ko K (c, u) (c', u') kw := by
  obtain ⟨ks, Bi, g1, Dc1, cp, B'i, Ui, Dci, d1, g2, lUi, L', piv', lres, lg, φ1, h1, h2, h3, h4, h5,
    h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨_, ks, Bi, g1, Dc1, cp, B'i, Ui, Dci, d1, g2, lUi, L', piv', lres, lg, φ1, h1, h2, h3, h4,
    h5, h6, h7, h8, h9, h10, h11, h12, h13, rfl⟩

/-- An unweighted iteration is an iteration with its use, at every use so far. -/
theorem IterRelD.toU {c c' : LoopCfgD G s Φ p} {k : ℕ}
    (h : IterRelD (Ω := Ω) ops T sub B τ c c' k) (u : ℕ) :
    ∃ u' kw, IterRelU (Ω := Ω) ops T sub B τ Ko K (c, u) (c', u') kw := by
  obtain ⟨kw, hW⟩ := h.toW (Ko := Ko) (K := K)
  obtain ⟨u', hU⟩ := hW.toU_cost u
  exact ⟨u', kw, hU⟩

/-- The use only grows along a loop run. -/
theorem RelLoop.le_snd_U {done : LoopCfgD G s Φ p × ℕ → Prop} :
    ∀ {a a' : LoopCfgD G s Φ p × ℕ} {kw : ℕ},
      RelLoop (IterRelU (Ω := Ω) ops T sub B τ Ko K) done a a' kw → a.2 ≤ a'.2 := by
  intro a a' kw h
  induction h with
  | stop => exact le_rfl
  | step _ _ _ _ _ _ hR _ ih => exact hR.le_snd.trans ih

/-- **Bridge with the use**: loop runs of iterations with their use are `LoopD` derivations; the
weighted cost is as in `loopDW_of_relLoop`, and the use grows by `2 · (cc + cm + lg.cost) - 2` (the
final test has no use). -/
theorem loopDU_of_relLoop :
    ∀ {a a' : LoopCfgD G s Φ p × ℕ} {kw : ℕ},
      RelLoop (IterRelU (Ω := Ω) ops T sub B τ Ko K) (fun a => LoopDoneD τ a.1) a a' kw →
      ∃ lg J cm cc, LoopD G s ops T sub B τ a.1.i a.1.cs a.1.φ a'.1.cs a'.1.φ lg J cm cc ∧
        kw + Ko = Ko * (cc + cm) + K * lg.cost + 1 ∧ a'.2 + 2 = a.2 + 2 * (cc + cm + lg.cost) := by
  intro a a' kw h
  induction h with
  | stop a hd =>
    exact ⟨[], ∅, 0, 1, LoopD.stop a.1.i a.1.cs a.1.φ hd, by simp [Log.cost]; ring,
      by simp [Log.cost]⟩
  | step a b a'' k k' hnd hR _ ih =>
    obtain ⟨lg, J, cm, cc, hL, hk', hu'⟩ := ih
    obtain ⟨ks, Bi, g1, Dc1, cp, B'i, Ui, Dci, d1, g2, lUi, L', piv', lres, lgs, φ1, hU, hD, hpull,
      hsub, hnd1, hlU, hnd2, hmem, hres, hnd3, hlres, hb1, rfl, hb2⟩ := hR
    rw [hb1] at hL
    refine ⟨lgs.shift a.1.i ++ lg, L'.toFinset ∪ J, (ops.merge T Dc1 Dci).2 + cm,
      iterCostD ops T B a.1.cs ks.toFinset cp Bi Ui Dc1 Dci d1 g2 lUi L' lres + cc,
      LoopD.step a.1.i a.1.cs a''.1.cs a.1.φ φ1 a''.1.φ ks Bi g1 Dc1 cp B'i Ui Dci d1 g2 lUi L' piv'
        lres lgs lg J cm cc hU hD hpull hsub hnd1 hlU hnd2 hmem hres hnd3 hlres hL, ?_, ?_⟩
    · have hsh : (lgs.shift a.1.i ++ lg).cost = lgs.cost + lg.cost := by
        simp only [Log.cost, Log.shift, List.map_append, List.sum_append, List.map_map,
          Function.comp_def]
      rw [hsh]
      have e : Ko * (iterCostD ops T B a.1.cs ks.toFinset cp Bi Ui Dc1 Dci d1 g2 lUi L' lres + cc +
          ((ops.merge T Dc1 Dci).2 + cm)) =
          Ko * (iterCostD ops T B a.1.cs ks.toFinset cp Bi Ui Dc1 Dci d1 g2 lUi L' lres +
            (ops.merge T Dc1 Dci).2) + Ko * (cc + cm) := by ring
      rw [e]
      have e2 : K * (lgs.cost + lg.cost) = K * lgs.cost + K * lg.cost := by ring
      rw [e2]
      omega
    · have hsh : (lgs.shift a.1.i ++ lg).cost = lgs.cost + lg.cost := by
        simp only [Log.cost, Log.shift, List.map_append, List.sum_append, List.map_map,
          Function.comp_def]
      rw [hsh, hu', hb2]
      ring

end iterU

end Frontier.CHD.BM
