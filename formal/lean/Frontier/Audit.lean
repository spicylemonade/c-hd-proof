import Mathlib.Basic.ENNReal.Operations
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Frontier.Audit — independent specification and gate propositions (owner: agent-09)

This file proves NO algorithmic result.  It fixes, independently of `Frontier.Spec` and
`Frontier.CostModel`, what an accepted gate theorem must say, so candidates are judged against
a target written before any candidate exists.

* `Inst`: explicit instance (`n`, `m`, `src`, `dst`, `w : Fin m → ℝ≥0`); parallel edges,
  self-loops, zero weights and zero-weight cycles allowed.
* `Walk` (recursive), `wt`, `adist` (walk infimum in `ℝ≥0∞`, `⊤` iff unreachable:
  `adist_eq_top_iff`).
* `bf`: purely recursive Bellman–Ford values; `bf_eq_adist : bf (n-1) = adist`
  (independent cross-characterization; uses the simple-path shortcut `walk_shortcut`).
* Non-vacuity: `pathInst_adist`, `pathInst_not_const` (every size), `mixInst_adist`
  (parallel edge + self-loop + zero cycle + unreachable vertex).
* `Model`, `Solves`, and the gate propositions `GateA`, `GateB`, `GateC`, `GateE`, `GateF`,
  `GateFNonuniform` with safe logs `lg`, `sqlg` and `∃ C` outside `∀ G`.
* Sanity: `gateE_imp_gateA/B/C`, `gateFNonuniform_imp_gateF`, `gateF_imp_not_gateE`,
  `oracle_gateE` (a dishonest model satisfies the gates: the model itself must be audited),
  `not_quad_gateA` (the gates are not tautologies).

The gate propositions are NECESSARY conditions only: reviewers must additionally audit the
model instance, the novelty clause of each gate, and the paper-to-Lean correspondence.
-/

open scoped ENNReal NNReal

namespace Frontier.Audit

structure Inst where
  n : ℕ
  m : ℕ
  src : Fin m → Fin n
  dst : Fin m → Fin n
  w : Fin m → ℝ≥0

namespace Inst
variable (G : Inst)

def Walk : Fin G.n → List (Fin G.m) → Fin G.n → Prop
  | u, [], v => u = v
  | u, e :: p, v => G.src e = u ∧ Walk (G.dst e) p v

def wt : List (Fin G.m) → ℝ≥0∞
  | [] => 0
  | e :: p => (G.w e : ℝ≥0∞) + wt p

noncomputable def adist (s v : Fin G.n) : ℝ≥0∞ := ⨅ (p : List (Fin G.m)) (_ : G.Walk s p v), G.wt p

noncomputable def bf (s : Fin G.n) : ℕ → Fin G.n → ℝ≥0∞
  | 0, v => if v = s then 0 else ⊤
  | k + 1, v => min (bf s k v) (⨅ e : Fin G.m, if G.dst e = v then bf s k (G.src e) + G.w e else ⊤)

def verts (u : Fin G.n) (p : List (Fin G.m)) : List (Fin G.n) := u :: p.map G.dst

variable {G}

@[simp] theorem walk_nil {u v : Fin G.n} : G.Walk u [] v ↔ u = v := Iff.rfl
@[simp] theorem walk_cons {u v : Fin G.n} {e : Fin G.m} {p : List (Fin G.m)} :
    G.Walk u (e :: p) v ↔ G.src e = u ∧ G.Walk (G.dst e) p v := Iff.rfl

@[simp] theorem wt_nil : G.wt [] = 0 := rfl
@[simp] theorem wt_cons (e : Fin G.m) (p : List (Fin G.m)) : G.wt (e :: p) = G.w e + G.wt p := rfl

theorem wt_append (p q : List (Fin G.m)) : G.wt (p ++ q) = G.wt p + G.wt q := by
  induction p with
  | nil => simp
  | cons e p ih => simp [ih, add_assoc]

theorem wt_lt_top (p : List (Fin G.m)) : G.wt p < ⊤ := by
  induction p with
  | nil => simp
  | cons e p ih => exact ENNReal.add_lt_top.mpr ⟨ENNReal.coe_lt_top, ih⟩

theorem walk_append {u x : Fin G.n} {p q : List (Fin G.m)} :
    G.Walk u (p ++ q) x ↔ ∃ v, G.Walk u p v ∧ G.Walk v q x := by
  induction p generalizing u with
  | nil => simp
  | cons e p ih =>
    simp only [List.cons_append, walk_cons, ih]
    constructor
    · rintro ⟨h1, v, h2, h3⟩; exact ⟨v, ⟨h1, h2⟩, h3⟩
    · rintro ⟨v, ⟨h1, h2⟩, h3⟩; exact ⟨h1, v, h2, h3⟩

theorem walk_concat {u x : Fin G.n} {p : List (Fin G.m)} {e : Fin G.m} :
    G.Walk u (p ++ [e]) x ↔ G.Walk u p (G.src e) ∧ G.dst e = x := by
  rw [walk_append]
  constructor
  · rintro ⟨v, hp, h1, h2⟩; subst h1; exact ⟨hp, h2⟩
  · rintro ⟨hp, h⟩; exact ⟨G.src e, hp, rfl, h⟩

theorem verts_cons (u : Fin G.n) (e : Fin G.m) (p : List (Fin G.m)) :
    G.verts u (e :: p) = u :: G.verts (G.dst e) p := rfl

@[simp] theorem length_verts (u : Fin G.n) (p : List (Fin G.m)) :
    (G.verts u p).length = p.length + 1 := by simp [verts]

theorem walk_split_at_mem {x v : Fin G.n} {q : List (Fin G.m)} (hq : G.Walk x q v)
    {u : Fin G.n} (hu : u ∈ G.verts x q) :
    ∃ pre suf, q = pre ++ suf ∧ G.Walk x pre u ∧ G.Walk u suf v ∧
      G.verts u suf <:+ G.verts x q := by
  induction q generalizing x with
  | nil =>
    simp only [verts, List.map_nil, List.mem_singleton] at hu
    subst hu
    exact ⟨[], [], rfl, rfl, hq, List.suffix_refl _⟩
  | cons e q ih =>
    obtain ⟨h1, h2⟩ := hq
    rw [verts_cons, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact ⟨[], e :: q, rfl, rfl, ⟨h1, h2⟩, List.suffix_refl _⟩
    · obtain ⟨pre, suf, rfl, hpre, hsuf, hsx⟩ := ih h2 hu
      refine ⟨e :: pre, suf, rfl, ⟨h1, hpre⟩, hsuf, ?_⟩
      rw [verts_cons]
      exact hsx.trans (List.suffix_cons _ _)

theorem walk_shortcut {u v : Fin G.n} {p : List (Fin G.m)} (hp : G.Walk u p v) :
    ∃ q, G.Walk u q v ∧ G.wt q ≤ G.wt p ∧ (G.verts u q).Nodup := by
  induction p generalizing u with
  | nil => exact ⟨[], hp, le_rfl, by simp [verts]⟩
  | cons e p ih =>
    obtain ⟨h1, h2⟩ := hp
    subst h1
    obtain ⟨q, hq, hlen, hnd⟩ := ih h2
    by_cases hmem : G.src e ∈ G.verts (G.dst e) q
    · obtain ⟨pre, suf, rfl, _, hsuf, hsx⟩ := walk_split_at_mem hq hmem
      refine ⟨suf, hsuf, ?_, hnd.sublist hsx.sublist⟩
      rw [wt_append] at hlen
      rw [wt_cons]
      calc G.wt suf ≤ G.wt pre + G.wt suf := le_add_self
        _ ≤ G.wt p := hlen
        _ ≤ G.w e + G.wt p := le_add_self
    · refine ⟨e :: q, ⟨rfl, hq⟩, ?_, ?_⟩
      · rw [wt_cons, wt_cons]; exact add_le_add le_rfl hlen
      · rw [verts_cons]; exact List.nodup_cons.mpr ⟨hmem, hnd⟩

theorem length_lt_of_nodup {u : Fin G.n} {q : List (Fin G.m)} (h : (G.verts u q).Nodup) :
    q.length < G.n := by
  have := h.length_le_card
  simp only [length_verts, Fintype.card_fin] at this
  omega

/-! ### Hop-bounded infima and the Bellman–Ford characterization -/

/-- Infimum of weights of `s`–`v` walks with at most `k` edges. -/
noncomputable def hopInf (G : Inst) (s : Fin G.n) (k : ℕ) (v : Fin G.n) : ℝ≥0∞ :=
  ⨅ (p : List (Fin G.m)) (_ : G.Walk s p v) (_ : p.length ≤ k), G.wt p

variable {s : Fin G.n}

theorem adist_le {v : Fin G.n} {p : List (Fin G.m)} (hp : G.Walk s p v) : G.adist s v ≤ G.wt p :=
  iInf₂_le p hp

theorem le_adist {v : Fin G.n} {a : ℝ≥0∞} (h : ∀ p, G.Walk s p v → a ≤ G.wt p) : a ≤ G.adist s v :=
  le_iInf₂ h

theorem hopInf_le {k : ℕ} {v : Fin G.n} {p : List (Fin G.m)} (hp : G.Walk s p v)
    (hl : p.length ≤ k) : hopInf G s k v ≤ G.wt p :=
  (iInf_le _ p).trans ((iInf_le _ hp).trans (iInf_le _ hl))

theorem le_hopInf {k : ℕ} {v : Fin G.n} {a : ℝ≥0∞}
    (h : ∀ p, G.Walk s p v → p.length ≤ k → a ≤ G.wt p) : a ≤ hopInf G s k v :=
  le_iInf fun p => le_iInf fun hp => le_iInf fun hl => h p hp hl

theorem hopInf_zero (v : Fin G.n) : hopInf G s 0 v = if v = s then 0 else ⊤ := by
  split_ifs with hv
  · subst hv
    exact le_antisymm (by simpa using hopInf_le (s := v) (k := 0) (p := []) rfl le_rfl) zero_le
  · refine top_le_iff.mp (le_hopInf fun p hp hl => ?_)
    have : p = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    subst this
    exact absurd (walk_nil.mp hp).symm hv

theorem hopInf_mono {k k' : ℕ} (h : k ≤ k') (v : Fin G.n) :
    hopInf G s k' v ≤ hopInf G s k v :=
  le_hopInf fun _ hp hl => hopInf_le hp (hl.trans h)

theorem hopInf_succ_le_edge (k : ℕ) (e : Fin G.m) :
    hopInf G s (k + 1) (G.dst e) ≤ hopInf G s k (G.src e) + (G.w e : ℝ≥0∞) := by
  unfold hopInf
  simp only [ENNReal.iInf_add]
  refine le_iInf fun p => le_iInf fun hp => le_iInf fun hl => ?_
  have hw : G.Walk s (p ++ [e]) (G.dst e) := walk_concat.mpr ⟨hp, rfl⟩
  have hl' : (p ++ [e]).length ≤ k + 1 := by simp [hl]
  calc (⨅ (q : List (Fin G.m)) (_ : G.Walk s q (G.dst e)) (_ : q.length ≤ k + 1), G.wt q)
        ≤ G.wt (p ++ [e]) := hopInf_le hw hl'
    _ = G.wt p + (G.w e : ℝ≥0∞) := by rw [wt_append]; simp

/-- The recursion `bf` computes the hop-bounded infima. -/
theorem bf_eq_hopInf : ∀ (k : ℕ) (v : Fin G.n), G.bf s k v = hopInf G s k v
  | 0, v => by rw [bf, hopInf_zero]
  | k + 1, v => by
    have ih : ∀ u, G.bf s k u = hopInf G s k u := bf_eq_hopInf k
    rw [bf]
    refine le_antisymm ?_ ?_
    · refine le_hopInf fun p hp hl => ?_
      rcases List.eq_nil_or_concat p with rfl | ⟨L, e, rfl⟩
      · refine min_le_left _ _ |>.trans ?_
        rw [ih]
        exact hopInf_le hp (Nat.zero_le _)
      · rw [List.concat_eq_append] at hp hl ⊢
        obtain ⟨hL, he⟩ := walk_concat.mp hp
        have hLl : L.length ≤ k := by simpa using hl
        refine (min_le_right _ _).trans ?_
        refine (iInf_le _ e).trans ?_
        simp only [he, ↓reduceIte]
        rw [ih, wt_append]
        simp only [wt_cons, wt_nil, add_zero]
        exact add_le_add (hopInf_le hL hLl) le_rfl
    · refine le_min ?_ ?_
      · rw [ih]; exact hopInf_mono (Nat.le_succ k) v
      · refine le_iInf fun e => ?_
        split_ifs with he
        · rw [ih, ← he]
          exact hopInf_succ_le_edge k e
        · exact le_top

theorem adist_le_hopInf (k : ℕ) (v : Fin G.n) : G.adist s v ≤ hopInf G s k v :=
  le_hopInf fun _ hp _ => adist_le hp

/-- With at least `n - 1` hops the hop-bounded infimum is the exact distance. -/
theorem hopInf_eq_adist {k : ℕ} (hk : G.n - 1 ≤ k) (v : Fin G.n) :
    hopInf G s k v = G.adist s v := by
  refine le_antisymm (le_adist fun p hp => ?_) (adist_le_hopInf k v)
  obtain ⟨q, hq, hwt, hnd⟩ := walk_shortcut hp
  have := length_lt_of_nodup hnd
  exact (hopInf_le hq (by omega)).trans hwt

/-- **Independent characterization.** `n - 1` Bellman–Ford rounds give the specification
distance (walk infimum), including `⊤` for unreachable vertices. -/
theorem bf_eq_adist (v : Fin G.n) : G.bf s (G.n - 1) v = G.adist s v := by
  rw [bf_eq_hopInf, hopInf_eq_adist le_rfl]

theorem bf_eq_adist_of_le {k : ℕ} (hk : G.n - 1 ≤ k) (v : Fin G.n) :
    G.bf s k v = G.adist s v := by
  rw [bf_eq_hopInf, hopInf_eq_adist hk]

/-- `⊤` exactly for unreachable vertices. -/
theorem adist_eq_top_iff {v : Fin G.n} : G.adist s v = ⊤ ↔ ¬ ∃ p, G.Walk s p v := by
  constructor
  · rintro h ⟨p, hp⟩
    exact absurd (h ▸ adist_le hp) (not_le.mpr (wt_lt_top p))
  · intro h
    exact top_le_iff.mp (le_adist fun p hp => absurd ⟨p, hp⟩ h)

theorem adist_self : G.adist s s = 0 :=
  le_antisymm (by simpa using adist_le (s := s) (v := s) (p := []) rfl) zero_le

/-- Lower-bound certificate: any feasible potential lies below the distance. -/
theorem le_adist_of_potential (φ : Fin G.n → ℝ≥0∞) (h0 : φ s = 0)
    (hrel : ∀ e : Fin G.m, φ (G.dst e) ≤ φ (G.src e) + G.w e) (v : Fin G.n) :
    φ v ≤ G.adist s v := by
  suffices key : ∀ (p : List (Fin G.m)) (u : Fin G.n), G.Walk u p v → φ v ≤ φ u + G.wt p by
    exact le_adist fun p hp => by simpa [h0] using key p s hp
  intro p
  induction p with
  | nil => intro u hu; rw [walk_nil] at hu; subst hu; simp
  | cons e p ih =>
    intro u hu
    obtain ⟨h1, h2⟩ := hu
    subst h1
    calc φ v ≤ φ (G.dst e) + G.wt p := ih _ h2
      _ ≤ (φ (G.src e) + G.w e) + G.wt p := add_le_add (hrel e) le_rfl
      _ = φ (G.src e) + G.wt (e :: p) := by rw [wt_cons, add_assoc]

end Inst

/-! ## Gate propositions, stated for an abstract costed model

The gate propositions below are parametric in a `Model`.  They are only as meaningful as the
model: `oracleModel` below satisfies every algorithmic gate (see `oracle_gateE`), so any claimed
gate theorem must be instantiated with a model whose honesty (every comparison, addition, RAM,
control and data-structure step charged; words of O(log n) bits; no free precomputation) has
been audited separately.  Logarithms are safe natural-number logarithms. -/

/-- safe `log₂`: `max 1 ⌊log₂ n⌋` -/
def lg (n : ℕ) : ℕ := max 1 (Nat.log 2 n)

/-- safe `√log₂`: `max 1 ⌊√⌊log₂ n⌋⌋` -/
def sqlg (n : ℕ) : ℕ := max 1 (Nat.sqrt (Nat.log 2 n))

/-- An abstract costed computation model for labeled SSSP programs. -/
structure Model where
  /-- programs (one finite object per algorithm: uniform) -/
  Prog : Type
  /-- `out P G s = some d`: `P` halts on `(G,s)` and its decoded labeled output is `d`
  (`⊤` = reported unreachable); `none`: does not halt or faults -/
  out : Prog → (G : Inst) → Fin G.n → Option (Fin G.n → ℝ≥0∞)
  /-- total charged work of the run -/
  time : Prog → (G : Inst) → Fin G.n → ℕ
  /-- memory cells used by the run -/
  space : Prog → (G : Inst) → Fin G.n → ℕ

variable (M : Model)

/-- `P` solves exact labeled SSSP on every explicit instance and source. -/
def Solves (P : M.Prog) : Prop :=
  ∀ (G : Inst) (s : Fin G.n), M.out P G s = some (G.adist s)

/-- **Gate A**: one exact program with worst-case time and space `O(n + m √log n)`. -/
def GateA : Prop :=
  ∃ P : M.Prog, Solves M P ∧ ∃ C : ℕ, ∀ (G : Inst) (s : Fin G.n),
    M.time P G s ≤ C * (G.n + G.m * sqlg G.n) ∧ M.space P G s ≤ C * (G.n + G.m * sqlg G.n)

/-- **Gate B**: an explicit general-graph bound `T n m` (valid for all graphs) that is
`o(n √log n)` whenever `m = O(n)`. -/
def GateB : Prop :=
  ∃ P : M.Prog, Solves M P ∧ ∃ T : ℕ → ℕ → ℕ,
    (∀ (G : Inst) (s : Fin G.n), M.time P G s ≤ T G.n G.m ∧ M.space P G s ≤ T G.n G.m) ∧
    ∀ c K : ℕ, ∃ N, ∀ n m, N ≤ n → m ≤ c * n → K * T n m ≤ n * sqlg n

/-- **Gate C**: `o(n log n)` worst case on all graphs with `m ≤ n f(n)` for a density
function `f(n) ≥ √log n / c₀`, i.e. inside the regime where Dijkstra is currently best. -/
def GateC : Prop :=
  ∃ P : M.Prog, Solves M P ∧ ∃ f : ℕ → ℕ, (∃ c₀ : ℕ, 0 < c₀ ∧ ∀ n, sqlg n ≤ c₀ * f n) ∧
    ∀ K : ℕ, ∃ N, ∀ (G : Inst) (s : Fin G.n), N ≤ G.n → G.m ≤ G.n * f G.n →
      K * M.time P G s ≤ G.n * lg G.n

/-- **Gate E**: exact linear time and space. -/
def GateE : Prop :=
  ∃ P : M.Prog, Solves M P ∧ ∃ C : ℕ, ∀ (G : Inst) (s : Fin G.n),
    M.time P G s ≤ C * (G.n + G.m) ∧ M.space P G s ≤ C * (G.n + G.m)

/-- A weightless topology; weights are the adversary's choice. -/
structure Topo where
  n : ℕ
  m : ℕ
  src : Fin m → Fin n
  dst : Fin m → Fin n

/-- The instance with topology `T` and weights `w`. -/
def Topo.inst (T : Topo) (w : Fin T.m → ℝ≥0) : Inst := ⟨T.n, T.m, T.src, T.dst, w⟩

/-- A sparse topology family: sizes unbounded, `m ≤ c n`, every vertex reachable from the source. -/
structure SparseFamily where
  topo : ℕ → Topo
  source : ∀ k, Fin (topo k).n
  c : ℕ
  sparse : ∀ k, (topo k).m ≤ c * (topo k).n
  grows : ∀ k, k ≤ (topo k).n
  reach : ∀ k (v : Fin (topo k).n), ∃ p, ((topo k).inst fun _ => 0).Walk (source k) p v

/-- **Gate F (uniform form)**: an explicit sparse family on which EVERY program of the model
that is correct on all weightings of the family has time `ω(n)`: for every `C`, for all large
members, some weighting forces more than `C (n + m)` work. -/
def GateF : Prop :=
  ∃ F : SparseFamily, ∀ P : M.Prog,
    (∀ k (w : Fin (F.topo k).m → ℝ≥0),
      M.out P ((F.topo k).inst w) (F.source k) = some (((F.topo k).inst w).adist (F.source k))) →
    ∀ C : ℕ, ∃ K, ∀ k, K ≤ k → ∃ w : Fin (F.topo k).m → ℝ≥0,
      C * ((F.topo k).n + (F.topo k).m) < M.time P ((F.topo k).inst w) (F.source k)

/-- **Gate F (nonuniform form)**: even a separate program for each member of the family
(topology advice, decision-tree style) needs `ω(n)` work.  Implies `GateF`. -/
def GateFNonuniform : Prop :=
  ∃ F : SparseFamily, ∀ P : ℕ → M.Prog,
    (∀ k (w : Fin (F.topo k).m → ℝ≥0),
      M.out (P k) ((F.topo k).inst w) (F.source k) = some (((F.topo k).inst w).adist (F.source k))) →
    ∀ C : ℕ, ∃ K, ∀ k, K ≤ k → ∃ w : Fin (F.topo k).m → ℝ≥0,
      C * ((F.topo k).n + (F.topo k).m) < M.time (P k) ((F.topo k).inst w) (F.source k)

/-! ## Non-vacuity of the specification

(1) On the unit-weight directed path with `n+1` vertices the distances are `0,1,…,n`, so for
every size `n ≥ 1` a constant output is wrong.  (2) One instance exercising a parallel edge,
a self-loop, a zero-weight cycle and an unreachable vertex. -/

namespace Examples
open Inst

/-- Directed path `0 → 1 → ⋯ → n` with unit weights. -/
abbrev pathInst (n : ℕ) : Inst where
  n := n + 1
  m := n
  src := fun i => ⟨i.val, by omega⟩
  dst := fun i => ⟨i.val + 1, by omega⟩
  w := fun _ => 1

theorem pathInst_wt_single (n : ℕ) (e : Fin n) : (pathInst n).wt [e] = 1 := by
  show ((1 : ℝ≥0) : ℝ≥0∞) + 0 = 1
  simp

theorem pathInst_walk (n : ℕ) : ∀ (i : ℕ) (hi : i < n + 1),
    ∃ p, (pathInst n).Walk 0 p ⟨i, hi⟩ ∧ (pathInst n).wt p = i
  | 0, _ => ⟨[], rfl, by simp only [Nat.cast_zero]; rfl⟩
  | i + 1, hi => by
    obtain ⟨p, hp, hw⟩ := pathInst_walk n i (by omega)
    refine ⟨p ++ [(⟨i, by omega⟩ : Fin n)], walk_concat.mpr ⟨hp, rfl⟩, ?_⟩
    rw [wt_append, hw, pathInst_wt_single]
    push_cast
    rfl

theorem pathInst_adist (n : ℕ) (v : Fin (n + 1)) : (pathInst n).adist 0 v = v.val := by
  refine le_antisymm ?_ ?_
  · obtain ⟨p, hp, hw⟩ := pathInst_walk n v.val v.isLt
    exact (adist_le hp).trans (le_of_eq hw)
  · refine le_adist_of_potential (G := pathInst n) (fun u => (u.val : ℝ≥0∞)) (by simp) ?_ v
    intro e
    show ((e.val + 1 : ℕ) : ℝ≥0∞) ≤ (e.val : ℝ≥0∞) + ((1 : ℝ≥0) : ℝ≥0∞)
    push_cast
    exact le_rfl

/-- For every size, the exact contract rejects every constant output. -/
theorem pathInst_not_const (n : ℕ) (hn : 1 ≤ n) (c : ℝ≥0∞) :
    (pathInst n).adist 0 ≠ fun _ => c := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h ⟨1, show 1 < n + 1 by omega⟩
  rw [pathInst_adist] at h0 h1
  simp only [Fin.val_zero, Nat.cast_zero] at h0
  simp only [Nat.cast_one] at h1
  rw [← h0] at h1
  exact one_ne_zero h1

/-- Parallel edges `0→1` (weights 2 and 1), self-loop `1→1` (0), zero cycle `1→2→1`, and
vertex `3` unreachable from `0` (its only edge is `3→0`). -/
abbrev mixInst : Inst where
  n := 4
  m := 6
  src := ![0, 0, 1, 1, 2, 3]
  dst := ![1, 1, 1, 2, 1, 0]
  w := ![2, 1, 0, 0, 0, 1]

/-- The claimed labels. -/
noncomputable def mixD : Fin 4 → ℝ≥0∞ := ![0, 1, 1, ⊤]

theorem mixInst_adist : mixInst.adist 0 = mixD := by
  funext v
  refine le_antisymm ?_ (le_adist_of_potential (G := mixInst) mixD (by simp [mixD]) ?_ v)
  · fin_cases v
    · exact (adist_le (G := mixInst) (s := 0) (v := 0) (p := []) rfl).trans
        (show (0 : ℝ≥0∞) ≤ mixD 0 from zero_le)
    · have h : mixInst.Walk 0 [1] 1 := ⟨rfl, rfl⟩
      refine (adist_le h).trans ?_
      show ((1 : ℝ≥0) : ℝ≥0∞) + 0 ≤ mixD 1
      simp [mixD]
    · have h : mixInst.Walk 0 [1, 3] 2 := ⟨rfl, rfl, rfl⟩
      refine (adist_le h).trans ?_
      show ((1 : ℝ≥0) : ℝ≥0∞) + (((0 : ℝ≥0) : ℝ≥0∞) + 0) ≤ mixD 2
      simp [mixD]
    · simp [mixD]
  · intro e
    fin_cases e <;> simp [mixD, mixInst]

theorem mixInst_unreachable : mixInst.adist 0 3 = ⊤ := by
  rw [mixInst_adist]; rfl

end Examples

/-! ## Sanity theorems about the gate propositions -/

theorem one_le_sqlg (n : ℕ) : 1 ≤ sqlg n := le_max_left _ _
theorem one_le_lg (n : ℕ) : 1 ≤ lg n := le_max_left _ _

/-- `√log` is unbounded (so the gates are genuinely asymptotic statements). -/
theorem sqlg_unbounded (A : ℕ) : ∃ N, ∀ n, N ≤ n → A ≤ sqlg n :=
  ⟨2 ^ (A * A), fun _ hn =>
    le_max_of_le_right (Nat.le_sqrt.mpr (Nat.le_log_of_pow_le (by norm_num) hn))⟩

/-- `log n` eventually dominates `A (1 + √log n)`. -/
theorem lg_dominates (A : ℕ) : ∃ N, ∀ n, N ≤ n → A * (1 + sqlg n) ≤ lg n := by
  refine ⟨2 ^ ((2 * A + 1) * (2 * A + 1)), fun n hn => ?_⟩
  have hx : (2 * A + 1) * (2 * A + 1) ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
  have hs : 2 * A + 1 ≤ Nat.sqrt (Nat.log 2 n) := Nat.le_sqrt.mpr hx
  have hsq : Nat.sqrt (Nat.log 2 n) * Nat.sqrt (Nat.log 2 n) ≤ Nat.log 2 n := Nat.sqrt_le _
  have h1 : sqlg n = Nat.sqrt (Nat.log 2 n) := max_eq_right (by omega)
  have h2 : Nat.log 2 n ≤ lg n := le_max_right _ _
  rw [h1]
  set t := Nat.sqrt (Nat.log 2 n)
  calc A * (1 + t) ≤ (2 * A + 1) * t := by nlinarith
    _ ≤ t * t := Nat.mul_le_mul_right _ hs
    _ ≤ Nat.log 2 n := hsq
    _ ≤ lg n := h2

theorem gateE_imp_gateA : GateE M → GateA M := by
  rintro ⟨P, hP, C, hC⟩
  refine ⟨P, hP, C, fun G s => ?_⟩
  have hm : G.m ≤ G.m * sqlg G.n := Nat.le_mul_of_pos_right _ (one_le_sqlg _)
  obtain ⟨h1, h2⟩ := hC G s
  exact ⟨h1.trans (Nat.mul_le_mul_left _ (by omega)), h2.trans (Nat.mul_le_mul_left _ (by omega))⟩

theorem gateE_imp_gateB : GateE M → GateB M := by
  rintro ⟨P, hP, C, hC⟩
  refine ⟨P, hP, fun n m => C * (n + m), fun G s => hC G s, fun c K => ?_⟩
  obtain ⟨N, hN⟩ := sqlg_unbounded (K * C * (1 + c))
  refine ⟨N, fun n m hn hm => ?_⟩
  have := hN n hn
  calc K * (C * (n + m)) ≤ K * (C * (n + c * n)) := by gcongr
    _ = (K * C * (1 + c)) * n := by ring
    _ ≤ sqlg n * n := Nat.mul_le_mul_right _ this
    _ = n * sqlg n := Nat.mul_comm _ _

theorem gateE_imp_gateC : GateE M → GateC M := by
  rintro ⟨P, hP, C, hC⟩
  refine ⟨P, hP, sqlg, ⟨1, one_pos, fun n => by simp⟩, fun K => ?_⟩
  obtain ⟨N, hN⟩ := lg_dominates (K * C)
  refine ⟨N, fun G s hn hm => ?_⟩
  have := hN G.n hn
  calc K * M.time P G s ≤ K * (C * (G.n + G.m)) := Nat.mul_le_mul_left _ (hC G s).1
    _ ≤ K * (C * (G.n + G.n * sqlg G.n)) := by gcongr
    _ = G.n * ((K * C) * (1 + sqlg G.n)) := by ring
    _ ≤ G.n * lg G.n := Nat.mul_le_mul_left _ this

theorem gateFNonuniform_imp_gateF : GateFNonuniform M → GateF M := by
  rintro ⟨F, hF⟩
  exact ⟨F, fun P hP => hF (fun _ => P) hP⟩

/-- A lower bound (Gate F) refutes linear time (Gate E) in the same model. -/
theorem gateF_imp_not_gateE : GateF M → ¬ GateE M := by
  rintro ⟨F, hF⟩ ⟨P, hP, C, hC⟩
  obtain ⟨K, hK⟩ := hF P (fun k w => hP _ _) C
  obtain ⟨w, hw⟩ := hK K le_rfl
  have h1 := (hC ((F.topo K).inst w) (F.source K)).1
  exact (not_le.mpr hw) h1

/-! ### Why the model must be audited: an oracle model satisfies every algorithmic gate -/

/-- A dishonest model: the "program" returns the distances for free. -/
noncomputable def oracleModel : Model where
  Prog := Unit
  out := fun _ G s => some (G.adist s)
  time := fun _ _ _ => 0
  space := fun _ _ _ => 0

theorem oracle_gateE : GateE oracleModel :=
  ⟨(), fun _ _ => rfl, 0, fun _ _ => ⟨Nat.zero_le _, Nat.zero_le _⟩⟩

theorem oracle_gateA : GateA oracleModel := gateE_imp_gateA _ oracle_gateE

/-- ...and the gate propositions are not tautologies: a model charging `n²` fails Gate A. -/
noncomputable def quadModel : Model where
  Prog := Unit
  out := fun _ G s => some (G.adist s)
  time := fun _ G _ => G.n * G.n
  space := fun _ _ _ => 0

theorem not_quad_gateA : ¬ GateA quadModel := by
  rintro ⟨P, -, C, hC⟩
  let G : Inst := ⟨C + 1, 0, Fin.elim0, Fin.elim0, Fin.elim0⟩
  have := (hC G 0).1
  simp only [quadModel, G, zero_mul, add_zero] at this
  nlinarith

end Frontier.Audit

#print axioms Frontier.Audit.Inst.bf_eq_adist
#print axioms Frontier.Audit.Inst.adist_eq_top_iff
#print axioms Frontier.Audit.Inst.le_adist_of_potential
#print axioms Frontier.Audit.Examples.pathInst_adist
#print axioms Frontier.Audit.Examples.pathInst_not_const
#print axioms Frontier.Audit.Examples.mixInst_adist
#print axioms Frontier.Audit.gateE_imp_gateA
#print axioms Frontier.Audit.gateE_imp_gateB
#print axioms Frontier.Audit.gateE_imp_gateC
#print axioms Frontier.Audit.gateF_imp_not_gateE
#print axioms Frontier.Audit.gateFNonuniform_imp_gateF
#print axioms Frontier.Audit.oracle_gateE
#print axioms Frontier.Audit.not_quad_gateA
