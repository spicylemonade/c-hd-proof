import Frontier.Spec
import Frontier.CostModel
import Frontier.Audit

/-!
# Frontier.AuditBridge — bridges from agent-09's independent spec to Frontier.Spec / CostModel

Owner: agent-09.  (1) `Inst.adist` (recursive walks, `ℝ≥0∞` weights) agrees with
`Frontier.Graph.dist`.  (2) Audit facts about the RAM machine of `Frontier.CostModel`:
allocated space never exceeds charged cost.
-/

open scoped ENNReal NNReal

namespace Frontier.Audit

/-- Forget nothing: the same five fields. -/
abbrev ofGraph (G : Frontier.Graph) : Inst := ⟨G.n, G.m, G.src, G.dst, G.w⟩

theorem walk_iff_isWalk (G : Frontier.Graph) {u v : Fin G.n} {p : List (Fin G.m)} :
    (ofGraph G).Walk u p v ↔ G.IsWalk u v p := by
  induction p generalizing u with
  | nil => exact ⟨fun h => h ▸ Frontier.Graph.IsWalk.nil _, fun h => (Frontier.Graph.isWalk_nil_iff.mp h)⟩
  | cons e p ih =>
    rw [Frontier.Graph.isWalk_cons_iff]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, ih.mp h2⟩, fun ⟨h1, h2⟩ => ⟨h1, ih.mpr h2⟩⟩

theorem wt_eq_len (G : Frontier.Graph) (p : List (Fin G.m)) :
    (ofGraph G).wt p = ((G.len p : ℝ≥0) : ℝ≥0∞) := by
  induction p with
  | nil => show (0 : ℝ≥0∞) = ((G.len [] : ℝ≥0) : ℝ≥0∞); simp
  | cons e p ih =>
    show ((G.w e : ℝ≥0) : ℝ≥0∞) + (ofGraph G).wt p = _
    rw [ih, Frontier.Graph.len_cons, ENNReal.coe_add]

/-- **Bridge (spec)**: agent-09's independent distance equals agent-08's `Graph.dist`. -/
theorem adist_eq_dist (G : Frontier.Graph) (s v : Fin G.n) :
    (ofGraph G).adist s v = G.dist s v := by
  unfold Inst.adist Frontier.Graph.dist
  refine le_antisymm ?_ ?_
  · refine le_iInf₂ fun p hp => ?_
    rw [← wt_eq_len]
    exact iInf₂_le p ((walk_iff_isWalk G).mpr hp)
  · refine le_iInf₂ fun p hp => ?_
    have := wt_eq_len G p
    rw [this]
    exact iInf₂_le p ((walk_iff_isWalk G).mp hp)

theorem isSSSP_iff (G : Frontier.Graph) (s : Fin G.n) (d : Fin G.n → ℝ≥0∞) :
    G.IsSSSP s d ↔ d = (ofGraph G).adist s := by
  constructor
  · intro h; funext v; rw [h v, adist_eq_dist]
  · rintro rfl v; exact adist_eq_dist G s v

/-! ## Audit fact: space is bounded by cost in the RAM machine -/

namespace RAMAudit
open Frontier.RAM

variable {V : Type} (ops : VOps V)

/-- Invariant: `space - space₀ ≤ cost - cost₀` along every successful run. -/
theorem exec_space_le_cost : ∀ (f : ℕ) (c : Stmt) (s r : State V), exec ops f c s = some r →
    s.space ≤ r.space ∧ s.cost ≤ r.cost ∧ r.space - s.space ≤ r.cost - s.cost
  | 0, _, _, _, h => by simp [exec] at h
  | f + 1, c, s, r, h => by
    cases c with
    | skip => simp [exec] at h; subst h; simp [State.charge]
    | wset x e =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨a, _, h⟩ := h; simp at h; subst h; simp [State.charge, State.setW]
    | vset x e =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨a, _, h⟩ := h; simp at h; subst h; simp [State.charge, State.setV]
    | vle x a b =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨p, _, q, _, bit, _, h⟩ := h; simp at h; subst h; simp [State.charge, State.setW]
    | wstore arr i e =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨j, _, a, _, h⟩ := h
      split_ifs at h; simp at h; subst h; simp [State.charge, State.storeW]
    | vstore arr i e =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨j, _, a, _, h⟩ := h
      split_ifs at h; simp at h; subst h; simp [State.charge, State.storeV]
    | walloc arr e =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨k, _, h⟩ := h; simp at h; subst h; simp [State.charge, State.allocW]
    | valloc arr e =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨k, _, h⟩ := h; simp at h; subst h; simp [State.charge, State.allocV]
    | seq a b =>
      rw [exec_seq, Option.bind_eq_some_iff] at h
      obtain ⟨s', h1, h2⟩ := h
      have i1 := exec_space_le_cost f a s s' h1
      have i2 := exec_space_le_cost f b s' r h2
      omega
    | ite c a b =>
      rw [exec_ite, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h2⟩ := h
      split_ifs at h2
      · have := exec_space_le_cost f a _ r h2; simp [State.charge] at this; omega
      · have := exec_space_le_cost f b _ r h2; simp [State.charge] at this; omega
    | «while» c b =>
      rw [exec_while, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h2⟩ := h
      split_ifs at h2
      · rw [Option.bind_eq_some_iff] at h2
        obtain ⟨s', h3, h4⟩ := h2
        have i1 := exec_space_le_cost f b _ s' h3
        have i2 := exec_space_le_cost f (.while c b) s' r h4
        simp [State.charge] at i1; omega
      · simp at h2; subst h2; simp [State.charge]
    | call p =>
      rw [exec_call] at h
      cases hp : s.procs[p]? with
      | none => rw [hp] at h; exact absurd h (by simp)
      | some body =>
        rw [hp] at h
        have := exec_space_le_cost f body _ r h; simp [State.enter] at this; omega

/-- In every terminating run from an initial state, allocated space ≤ charged cost. -/
theorem run_space_le_cost (P : Program) (fuel : ℕ) (G : Frontier.Graph) (s : Fin G.n)
    (r : State ℝ≥0) (h : P.run fuel G s = some r) : r.space ≤ r.cost := by
  have := exec_space_le_cost realOps fuel P.body _ r h
  simp [initState] at this
  omega

end RAMAudit

/-! ## The RAM machine as an instance of the independent `Audit.Model` (audit item F-v2-4) -/

/-- Back-conversion (definitionally the identity on fields). -/
abbrev toGraph (G : Inst) : Frontier.Graph := ⟨G.n, G.m, G.src, G.dst, G.w⟩

theorem ofGraph_toGraph (G : Inst) : ofGraph (toGraph G) = G := rfl

open Frontier.RAM in
/-- The terminating run of `P` on `(G, s)`, if any (unique by `exec_det`). -/
noncomputable def ramRun (P : Program) (G : Inst) (s : Fin G.n) : Option (State ℝ≥0) :=
  open Classical in
  if h : ∃ fuel r, P.run fuel (toGraph G) s = some r then some (Classical.choose (Classical.choose_spec h))
  else none

open Frontier.RAM in
theorem ramRun_spec {P : Program} {G : Inst} {s : Fin G.n} {r : State ℝ≥0} (h : ramRun P G s = some r) :
    ∃ fuel, P.run fuel (toGraph G) s = some r := by
  unfold ramRun at h
  split_ifs at h with hh
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨Classical.choose hh, Classical.choose_spec (Classical.choose_spec hh)⟩

open Frontier.RAM in
theorem ramRun_of_run {P : Program} {G : Inst} {s : Fin G.n} {fuel : ℕ} {r : State ℝ≥0}
    (h : P.run fuel (toGraph G) s = some r) : ramRun P G s = some r := by
  have hh : ∃ fuel r, P.run fuel (toGraph G) s = some r := ⟨fuel, r, h⟩
  unfold ramRun
  rw [dif_pos hh]
  congr 1
  have hf' : P.run (Classical.choose hh) (toGraph G) s = some (Classical.choose (Classical.choose_spec hh)) :=
    Classical.choose_spec (Classical.choose_spec hh)
  exact exec_det realOps hf' h

open Frontier.RAM in
/-- The RAM machine of `Frontier.CostModel`, viewed as an `Audit.Model`.  `out` decodes the unique
terminating run; `time`/`space` are its charged cost and allocated space (0 if it does not halt). -/
noncomputable def ramModel : Model where
  Prog := Program
  out := fun P G s => (ramRun P G s).map (fun r v => r.label v)
  time := fun P G s => match ramRun P G s with | some r => r.cost | none => 0
  space := fun P G s => match ramRun P G s with | some r => r.space | none => 0

open Frontier.RAM in
/-- `Program.Exact` implies `Audit.Solves` for the RAM instance (the independent spec is met). -/
theorem solves_of_exact {P : Program} (hP : P.Exact) : Solves ramModel P := by
  intro G s
  obtain ⟨fuel, r, hrun, hsol⟩ := hP (toGraph G) s
  simp only [ramModel, ramRun_of_run hrun, Option.map_some]
  congr 1
  funext v
  have h2 := hsol.2.2 v
  have h3 := adist_eq_dist (toGraph G) s v
  exact h2.trans h3.symm

open Frontier.RAM in
/-- A RunsWithin bound transfers to the Audit time. -/
theorem time_le_of_runsWithin {P : Program} {G : Inst} {s : Fin G.n} {T : ℝ}
    (h : P.RunsWithin (toGraph G) s T) : (ramModel.time P G s : ℝ) ≤ T := by
  obtain ⟨fuel, r, hrun, hc⟩ := h
  simp only [ramModel, ramRun_of_run hrun]
  exact hc

open Frontier.RAM in
theorem space_le_time_ram {P : Program} {G : Inst} {s : Fin G.n} :
    ramModel.space P G s ≤ ramModel.time P G s := by
  simp only [ramModel]
  cases h : ramRun P G s with
  | none => simp
  | some r =>
    obtain ⟨fuel, hrun⟩ := ramRun_spec h
    exact RAMAudit.run_space_le_cost P fuel (toGraph G) s r hrun

/-- **Bridge (Gate E).** The CostModel gate implies agent-09's independent gate for the RAM instance. -/
theorem gateE_bridge : Frontier.GateE → GateE ramModel := by
  rintro ⟨P, hP, C, hC⟩
  refine ⟨P, solves_of_exact hP, Nat.ceil (max C 0), fun G s => ?_⟩
  have h1 := time_le_of_runsWithin (hC (toGraph G) s)
  have hle : (ramModel.time P G s : ℝ) ≤ (Nat.ceil (max C 0) : ℝ) * ((G.n : ℝ) + G.m) := by
    refine h1.trans ?_
    have : C ≤ (Nat.ceil (max C 0) : ℝ) := (le_max_left C 0).trans (Nat.le_ceil _)
    have hnm : (0 : ℝ) ≤ (G.n : ℝ) + G.m := by positivity
    exact mul_le_mul_of_nonneg_right this hnm
  have ht : ramModel.time P G s ≤ Nat.ceil (max C 0) * (G.n + G.m) := by exact_mod_cast hle
  exact ⟨ht, space_le_time_ram.trans ht⟩

end Frontier.Audit

#print axioms Frontier.Audit.adist_eq_dist
#print axioms Frontier.Audit.isSSSP_iff
#print axioms Frontier.Audit.RAMAudit.run_space_le_cost
#print axioms Frontier.Audit.solves_of_exact
#print axioms Frontier.Audit.gateE_bridge
