import Frontier.Spec
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Frontier.CostModel — computation models and the exact gate statements (v2, theory-only)

Owner: agent-08.  This file fixes the *computation models* and the *exact Lean statements* of the
gates A, B, C, E, F of `/research/GOAL.md`.  It contains no algorithm and no gate result.

## Why a deep embedding (closes the archived audit findings F1/F2/F3)

A shallow (monadic, polymorphic) cost model cannot charge pure Lean computation: an algorithm
can learn the topology with a few charged operations and then run an arbitrary *free* pure
planner (e.g. Cai-style exhaustive search for an optimal decision tree).  Its charged cost would
be the nonuniform CA complexity, not a running time.  Therefore every runtime gate (A, B, C, E) is
stated over a **deep-embedded RAM + comparison–addition machine**:

* An algorithm is a `Program`: a *finite* syntax tree `Stmt` (no Lean functions inside, so no
  free computation and no noncomputable choice can hide in it) plus a word-size exponent.
  One program serves all inputs (uniformity).
* **Words** are natural numbers that must stay `< cap = (n + m + 2) ^ (wordExp + 1)`
  (`O(log n)`-bit words).  An operation producing a larger word is *stuck* (the run fails), so
  word-size abuse is impossible.  Word operations: `+ - * /` (truncated subtraction, division by
  zero is stuck), `<`, `=`, array reads.  This is the standard unit-cost word RAM.
* **Values** (weights and distances) live in a separate sort.  Their only operations are the
  constant `0`, addition, array reads, and the comparison statement `vle x a b` which stores the
  bit `[a ≤ b]` in word register `x`.  There is no conversion from values to words other than
  such comparison bits, and none from words to values.  This is exactly the comparison–addition
  model: no floor, hashing, truncation or bit access on reals.
* **Cost**: every executed statement, every branch/loop test costs `1`; allocating an array of
  size `k` costs `k + 1` (initialisation).  Expression sizes are program constants, so this is
  unit-cost RAM up to a program-dependent constant factor.  Because allocation is charged,
  `space ≤ cost` always (`exec_space_le_cost` style bounds are immediate); the state still
  records `space` so it can be reported.
* **Input**: registers `n`, `m`, `s`; read-only arrays `src`, `dst` (words) and `w` (values) of
  length `m`, exactly the explicit edge list of `Frontier.Graph` (parallel edges, self loops,
  zero weights allowed).  Reading them is charged per access.
* **Output**: the program must allocate value array `dist` and word array `reach` of length `n`.
  Vertex `v` is reported unreachable iff `reach[v] = 0`, otherwise its label is `dist[v]`.
  The output contract is `Graph.IsSSSP` (exact labeled distances; no order required).

* **Procedures** (Layer-B extension): `Stmt.call p` runs procedure `p` of the program's finite
  procedure table `Program.procs` (a list of `Stmt`, no Lean functions), charging `1` unit of cost
  and `1` cell of space (the return point; space is total allocation, never freed, so
  `space ≤ cost` still holds).  There are no automatic frames: procedures share the global
  registers and arrays, and a program that needs local state saves it explicitly (charged).
  Justification (audit item P10): a plain word RAM simulates `call`/return with an explicit
  return-point stack in an array and a return dispatch whose size is a program constant, i.e.
  `O(1)` RAM steps per call and per return; the return point is never observable as a word.

## The full comparison–addition model for lower bounds (gate F)

`CATree top k` is a *nonuniform, adaptive* comparison–addition decision tree for one fixed
topology: registers start as the `m` edge weights and the constant `0`; an `add` node creates a
new register `r_i + r_j`; a `cmp` node branches on `r_i ≤ r_j`; a leaf outputs, for every vertex,
a register or `⊤`.  Additions and comparisons each cost `1`; copying and control are free.  This is
the full (nonuniform, adaptive) comparison–addition class, so a lower bound for `CATree`s is a lower
bound for all deterministic comparison–addition algorithms, counting total work on values (not a
fixed addition budget).  **Not yet kernel-checked (audit finding F-v2-1):** the transfer "a `Program`
running within budget `K` on every weighting of a topology yields a `CAProg` of cost
`≤ K_P · K`" (`K_P` = the program's maximal value-expression size).  It is needed only to phrase a
gate-F result as a lower bound for this RAM model, and will be formalised if a gate-F candidate
exists.
-/

open scoped ENNReal NNReal

namespace Frontier

/-! ## The RAM + comparison–addition machine -/

namespace RAM

/-- Word expressions (unit-cost RAM on `O(log n)`-bit words). -/
inductive WExpr where
  | lit : ℕ → WExpr
  | var : String → WExpr
  | add : WExpr → WExpr → WExpr
  /-- truncated subtraction -/
  | sub : WExpr → WExpr → WExpr
  | mul : WExpr → WExpr → WExpr
  /-- integer division; stuck on division by zero -/
  | div : WExpr → WExpr → WExpr
  /-- `1` if `a < b`, else `0` -/
  | lt : WExpr → WExpr → WExpr
  /-- `1` if `a = b`, else `0` -/
  | eq : WExpr → WExpr → WExpr
  /-- read a word array; stuck out of bounds -/
  | load : String → WExpr → WExpr
  deriving Repr, Inhabited

/-- Value expressions: the comparison–addition sort.  Only `0`, addition and array reads. -/
inductive VExpr where
  | zero : VExpr
  | var : String → VExpr
  | add : VExpr → VExpr → VExpr
  /-- read a value array at a word index; stuck out of bounds -/
  | load : String → WExpr → VExpr
  deriving Repr, Inhabited

/-- Statements. -/
inductive Stmt where
  | skip : Stmt
  | wset : String → WExpr → Stmt
  | vset : String → VExpr → Stmt
  /-- `vle x a b`: word register `x := [a ≤ b]` — the only way values influence control -/
  | vle : String → VExpr → VExpr → Stmt
  | wstore : String → WExpr → WExpr → Stmt
  | vstore : String → WExpr → VExpr → Stmt
  /-- allocate (or re-allocate) a zero-initialised word array; costs `size + 1` -/
  | walloc : String → WExpr → Stmt
  /-- allocate (or re-allocate) a value array initialised to `0`; costs `size + 1` -/
  | valloc : String → WExpr → Stmt
  | seq : Stmt → Stmt → Stmt
  | ite : WExpr → Stmt → Stmt → Stmt
  | while : WExpr → Stmt → Stmt
  /-- call procedure number `p` of the program's procedure table (cost `1` and one cell of stack
  space, plus the body's cost).  Procedures share the global registers and arrays; recursion is
  allowed (fuel-bounded); an unknown procedure is stuck. -/
  | call : ℕ → Stmt
  deriving Repr, Inhabited

/-- The operations available on values.  The semantics is generic; `realOps` is the
intended one. -/
structure VOps (V : Type) where
  zero : V
  add : V → V → V
  le : V → V → Bool

/-- Exact nonnegative-real semantics. -/
noncomputable def realOps : VOps ℝ≥0 where
  zero := 0
  add a b := a + b
  le a b := decide (a ≤ b)

/-- Machine state.  Arrays are total functions with a length (`0` = unallocated). -/
structure State (V : Type) where
  w : String → ℕ
  v : String → V
  wa : String → ℕ → ℕ
  va : String → ℕ → V
  wlen : String → ℕ
  vlen : String → ℕ
  /-- every word must stay below `cap` -/
  cap : ℕ
  /-- charged cost so far -/
  cost : ℕ
  /-- cells allocated so far -/
  space : ℕ
  /-- the program's procedure table (never modified by any statement) -/
  procs : List Stmt := []

namespace State

variable {V : Type}

def setW (s : State V) (x : String) (a : ℕ) : State V :=
  { s with w := fun y => if y = x then a else s.w y }
def setV (s : State V) (x : String) (a : V) : State V :=
  { s with v := fun y => if y = x then a else s.v y }
def storeW (s : State V) (arr : String) (i a : ℕ) : State V :=
  { s with wa := fun b j => if b = arr ∧ j = i then a else s.wa b j }
def storeV (s : State V) (arr : String) (i : ℕ) (a : V) : State V :=
  { s with va := fun b j => if b = arr ∧ j = i then a else s.va b j }
def allocW (s : State V) (arr : String) (k : ℕ) : State V :=
  { s with wa := fun b j => if b = arr then 0 else s.wa b j,
           wlen := fun b => if b = arr then k else s.wlen b,
           space := s.space + k }
def allocV (s : State V) (arr : String) (k : ℕ) (z : V) : State V :=
  { s with va := fun b j => if b = arr then z else s.va b j,
           vlen := fun b => if b = arr then k else s.vlen b,
           space := s.space + k }
/-- charge `k` units -/
def charge (s : State V) (k : ℕ) : State V := { s with cost := s.cost + k }
/-- entering a procedure: cost `1` and one cell of (never freed) stack space for the return
point -/
def enter (s : State V) : State V := { s with cost := s.cost + 1, space := s.space + 1 }

end State

variable {V : Type} (ops : VOps V)

/-- Checked word result: stuck if it does not fit in a word. -/
def fit (cap a : ℕ) : Option ℕ := if a < cap then some a else none

/-- Evaluate a word expression (`none` = stuck). -/
def evalW (s : State V) : WExpr → Option ℕ
  | .lit a => fit s.cap a
  | .var x => some (s.w x)
  | .add a b => do let x ← evalW s a; let y ← evalW s b; fit s.cap (x + y)
  | .sub a b => do let x ← evalW s a; let y ← evalW s b; pure (x - y)
  | .mul a b => do let x ← evalW s a; let y ← evalW s b; fit s.cap (x * y)
  | .div a b => do let x ← evalW s a; let y ← evalW s b; if y = 0 then none else pure (x / y)
  | .lt a b => do let x ← evalW s a; let y ← evalW s b; fit s.cap (if x < y then 1 else 0)
  | .eq a b => do let x ← evalW s a; let y ← evalW s b; fit s.cap (if x = y then 1 else 0)
  | .load arr i => do let j ← evalW s i; if j < s.wlen arr then pure (s.wa arr j) else none

/-- Evaluate a value expression (`none` = stuck). -/
def evalV (s : State V) : VExpr → Option V
  | .zero => some ops.zero
  | .var x => some (s.v x)
  | .add a b => do let x ← evalV s a; let y ← evalV s b; pure (ops.add x y)
  | .load arr i => do let j ← evalW s i; if j < s.vlen arr then pure (s.va arr j) else none

/-- Fuel-bounded big-step semantics.  Every statement and every test costs `1`, allocation of
`k` cells costs `k + 1`.  `none` means stuck or out of fuel. -/
def exec : ℕ → Stmt → State V → Option (State V)
  | 0, _, _ => none
  | _ + 1, .skip, s => some (s.charge 1)
  | _ + 1, .wset x e, s => do let a ← evalW s e; pure ((s.setW x a).charge 1)
  | _ + 1, .vset x e, s => do let a ← evalV ops s e; pure ((s.setV x a).charge 1)
  | _ + 1, .vle x a b, s => do
      let p ← evalV ops s a; let q ← evalV ops s b
      let bit ← fit s.cap (if ops.le p q then 1 else 0)
      pure ((s.setW x bit).charge 1)
  | _ + 1, .wstore arr i e, s => do
      let j ← evalW s i; let a ← evalW s e
      if j < s.wlen arr then pure ((s.storeW arr j a).charge 1) else none
  | _ + 1, .vstore arr i e, s => do
      let j ← evalW s i; let a ← evalV ops s e
      if j < s.vlen arr then pure ((s.storeV arr j a).charge 1) else none
  | _ + 1, .walloc arr e, s => do
      let k ← evalW s e; pure ((s.allocW arr k).charge (k + 1))
  | _ + 1, .valloc arr e, s => do
      let k ← evalW s e; pure ((s.allocV arr k ops.zero).charge (k + 1))
  | f + 1, .seq a b, s => do let s' ← exec f a s; exec f b s'
  | f + 1, .ite c a b, s => do
      let x ← evalW s c
      if x ≠ 0 then exec f a (s.charge 1) else exec f b (s.charge 1)
  | f + 1, .while c b, s => do
      let x ← evalW s c
      if x ≠ 0 then do
        let s' ← exec f b (s.charge 1)
        exec f (.while c b) s'
      else pure (s.charge 1)
  | f + 1, .call p, s => match s.procs[p]? with
      | some body => exec f body s.enter
      | none => none

/-! ### Basic semantic facts -/

theorem exec_seq (f : ℕ) (a b : Stmt) (s : State V) :
    exec ops (f + 1) (.seq a b) s = (exec ops f a s).bind (fun s' => exec ops f b s') := rfl

theorem exec_ite (f : ℕ) (c : WExpr) (a b : Stmt) (s : State V) :
    exec ops (f + 1) (.ite c a b) s = (evalW s c).bind (fun x =>
      if x ≠ 0 then exec ops f a (s.charge 1) else exec ops f b (s.charge 1)) := rfl

theorem exec_while (f : ℕ) (c : WExpr) (b : Stmt) (s : State V) :
    exec ops (f + 1) (.while c b) s = (evalW s c).bind (fun x =>
      if x ≠ 0 then (exec ops f b (s.charge 1)).bind (fun s' => exec ops f (.while c b) s')
      else some (s.charge 1)) := rfl

theorem exec_call (f : ℕ) (p : ℕ) (s : State V) :
    exec ops (f + 1) (.call p) s = match s.procs[p]? with
      | some body => exec ops f body s.enter
      | none => none := rfl

/-- More fuel never changes a successful result. -/
theorem exec_succ {f : ℕ} {c : Stmt} {s r : State V} (h : exec ops f c s = some r) :
    exec ops (f + 1) c s = some r := by
  induction f generalizing c s r with
  | zero => simp [exec] at h
  | succ f ih =>
    cases c with
    | seq a b =>
      rw [exec_seq, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨s', h1, h2⟩ := h
      exact ⟨s', ih h1, ih h2⟩
    | ite c a b =>
      rw [exec_ite, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨x, hx, h2⟩ := h
      refine ⟨x, hx, ?_⟩
      split_ifs at h2 ⊢
      · exact ih h2
      · exact ih h2
    | «while» c b =>
      rw [exec_while, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨x, hx, h2⟩ := h
      refine ⟨x, hx, ?_⟩
      split_ifs at h2 ⊢
      · rw [Option.bind_eq_some_iff] at h2 ⊢
        obtain ⟨s', h3, h4⟩ := h2
        exact ⟨s', ih h3, ih h4⟩
      · exact h2
    | call p =>
      rw [exec_call] at h ⊢
      cases hp : s.procs[p]? with
      | none => rw [hp] at h; exact absurd h (by simp)
      | some body => rw [hp] at h; exact ih h
    | _ => simpa [exec] using h

theorem exec_mono {f f' : ℕ} {c : Stmt} {s r : State V} (h : exec ops f c s = some r)
    (hf : f ≤ f') : exec ops f' c s = some r := by
  induction hf with
  | refl => exact h
  | step _ ih => exact exec_succ ops ih

/-- The machine is deterministic: all successful runs agree. -/
theorem exec_det {f f' : ℕ} {c : Stmt} {s r r' : State V} (h : exec ops f c s = some r)
    (h' : exec ops f' c s = some r') : r = r' := by
  have h1 := exec_mono ops h (le_max_left f f')
  have h2 := exec_mono ops h' (le_max_right f f')
  rw [h1] at h2
  exact Option.some.inj h2

/-! ### Programs, input encoding, output decoding -/

/-- A uniform algorithm: one finite program for all inputs, with a fixed word-size exponent. -/
structure Program where
  body : Stmt
  /-- words must stay below `(n + m + 2) ^ (wordExp + 1)` -/
  wordExp : ℕ
  /-- procedure table for `Stmt.call` (default: no procedures) -/
  procs : List Stmt := []
  deriving Repr

/-- The initial machine state for graph `G` and source `s` (input arrays loaded, nothing else
allocated, cost and space `0`). -/
noncomputable def initState (P : Program) (G : Graph) (s : Fin G.n) : State ℝ≥0 where
  w := fun x => if x = "n" then G.n else if x = "m" then G.m else if x = "s" then (s : ℕ) else 0
  v := fun _ => 0
  wa := fun a j =>
    if a = "src" then (if h : j < G.m then (G.src ⟨j, h⟩ : ℕ) else 0)
    else if a = "dst" then (if h : j < G.m then (G.dst ⟨j, h⟩ : ℕ) else 0) else 0
  va := fun a j => if a = "w" then (if h : j < G.m then G.w ⟨j, h⟩ else 0) else 0
  wlen := fun a => if a = "src" then G.m else if a = "dst" then G.m else 0
  vlen := fun a => if a = "w" then G.m else 0
  cap := (G.n + G.m + 2) ^ (P.wordExp + 1)
  cost := 0
  space := 0
  procs := P.procs

/-- Run the program with the given fuel under the exact real semantics. -/
noncomputable def Program.run (P : Program) (fuel : ℕ) (G : Graph) (s : Fin G.n) :
    Option (State ℝ≥0) :=
  exec realOps fuel P.body (initState P G s)

/-- Decoded output label of vertex `v` in a final state. -/
noncomputable def State.label (r : State ℝ≥0) (v : ℕ) : ℝ≥0∞ :=
  if r.wa "reach" v = 0 then ⊤ else ((r.va "dist" v : ℝ≥0) : ℝ≥0∞)

/-- The final state carries a well-formed output for `n` vertices whose labels are exactly the
shortest-path distances from `s`. -/
def State.Solves (r : State ℝ≥0) (G : Graph) (s : Fin G.n) : Prop :=
  r.wlen "reach" = G.n ∧ r.vlen "dist" = G.n ∧ G.IsSSSP s (fun v => r.label v)

/-- **Exactness**: on every graph (every topology, every choice of nonnegative real weights,
including zero-weight cycles, parallel edges, self loops and unreachable vertices) and every
source, the program terminates without getting stuck and outputs the exact distances. -/
def Program.Exact (P : Program) : Prop :=
  ∀ (G : Graph) (s : Fin G.n), ∃ fuel r, P.run fuel G s = some r ∧ r.Solves G s

/-- The (unique, by `exec_det`) terminating run on `(G, s)` costs at most `T`. -/
def Program.RunsWithin (P : Program) (G : Graph) (s : Fin G.n) (T : ℝ) : Prop :=
  ∃ fuel r, P.run fuel G s = some r ∧ (r.cost : ℝ) ≤ T

theorem Program.runsWithin_unique {P : Program} {G : Graph} {s : Fin G.n} {T : ℝ}
    (h : P.RunsWithin G s T) {fuel : ℕ} {r : State ℝ≥0} (hr : P.run fuel G s = some r) :
    (r.cost : ℝ) ≤ T := by
  obtain ⟨f, r', h', hc⟩ := h
  rw [exec_det realOps hr h']
  exact hc

end RAM

/-! ## Gate statements for algorithms (A, B, C, E)

Safe logarithm: `Real.log (n + 2) > 0` for all `n`.  In every statement the program and the
constant are chosen *before* the graph. -/

open RAM

/-- **Gate A**: a uniform deterministic `O(n + m √log n)` exact algorithm (no iterated logs). -/
def GateA : Prop :=
  ∃ P : Program, P.Exact ∧ ∃ C : ℝ, ∀ (G : Graph) (s : Fin G.n),
    P.RunsWithin G s (C * ((G.n : ℝ) + (G.m : ℝ) * Real.sqrt (Real.log ((G.n : ℝ) + 2))))

/-- **Gate B**: an honest bound `T n m` valid on *every* graph which is `o(n √log n)` on sparse
graphs (`m ≤ c n`, every fixed `c`).  (Novelty — "a genuinely new mechanism, not an iterated-log
tweak" — is a review judgement the proposition cannot encode.) -/
def GateB : Prop :=
  ∃ P : Program, P.Exact ∧ ∃ T : ℕ → ℕ → ℝ,
    (∀ (G : Graph) (s : Fin G.n), P.RunsWithin G s (T G.n G.m)) ∧
    ∀ c : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≤ c * n,
      T n m ≤ ε * ((n : ℝ) * Real.sqrt (Real.log ((n : ℝ) + 2)))

/-- **Gate C**: an honest bound `T n m` valid on every graph and a density profile `m = μ n`
inside the window where Dijkstra's `O(m + n log n)` is the best known bound
(`n √log n ≤ μ n ≤ n log n`: there `min(m + n log n, m √log n + √(m n log n loglog n))`
is `Θ(n log n)`), along which `T = o(n log n)`.  (That the improvement is *new* is a review
judgement.) -/
def GateC : Prop :=
  ∃ P : Program, P.Exact ∧ ∃ T : ℕ → ℕ → ℝ,
    (∀ (G : Graph) (s : Fin G.n), P.RunsWithin G s (T G.n G.m)) ∧
    ∃ μ : ℕ → ℕ,
      (∀ᶠ n : ℕ in Filter.atTop,
        (n : ℝ) * Real.sqrt (Real.log ((n : ℝ) + 2)) ≤ (μ n : ℝ) ∧
        (μ n : ℝ) ≤ (n : ℝ) * Real.log ((n : ℝ) + 2)) ∧
      Filter.Tendsto (fun n : ℕ => T n (μ n) / ((n : ℝ) * Real.log ((n : ℝ) + 2)))
        Filter.atTop (nhds 0)

/-- **Gate E**: exact linear time `O(n + m)`. -/
def GateE : Prop :=
  ∃ P : Program, P.Exact ∧ ∃ C : ℝ, ∀ (G : Graph) (s : Fin G.n),
    P.RunsWithin G s (C * ((G.n : ℝ) + (G.m : ℝ)))

/-! ## The comparison–addition decision-tree model (gate F)

This is Cai's topology-specialized comparison–addition program class (2609.04825v1, §2.2)
in decision-tree form: nonuniform (one tree per topology), adaptive, with finitely many real
literal constants, charged binary additions and charged three-way comparisons, free copying,
selection and control, and outputs that must be held registers. -/

/-- A graph topology without weights. -/
structure Topology where
  n : ℕ
  m : ℕ
  src : Fin m → Fin n
  dst : Fin m → Fin n

/-- The weighted graph obtained from a topology and a weight vector. -/
def Topology.withW (T : Topology) (w : Fin T.m → ℝ≥0) : Graph := ⟨T.n, T.m, T.src, T.dst, w⟩

/-- A comparison–addition decision tree producing labels for `n` vertices, with `k` registers
currently available.  Registers hold real numbers. -/
inductive CATree (n : ℕ) : ℕ → Type where
  /-- output: for each vertex a held register (its distance) or `none` (`⊤`, unreachable) -/
  | leaf {k : ℕ} (out : Fin n → Option (Fin k)) : CATree n k
  /-- new register `r_k := r_i + r_j` (cost 1) -/
  | add {k : ℕ} (i j : Fin k) (next : CATree n (k + 1)) : CATree n k
  /-- three-way branch on `r_i < r_j`, `r_i = r_j`, `r_i > r_j` (cost 1) -/
  | cmp {k : ℕ} (i j : Fin k) (lt eq gt : CATree n k) : CATree n k

namespace CATree

variable {n : ℕ}

/-- The output labels reached on register file `r` (`none` = `⊤`). -/
noncomputable def labels : {k : ℕ} → CATree n k → (Fin k → ℝ) → Fin n → Option ℝ
  | _, .leaf out, r => fun v => (out v).map r
  | _, .add i j t, r => t.labels (Fin.snoc r (r i + r j))
  | _, .cmp i j t₁ t₂ t₃, r =>
      if r i < r j then t₁.labels r else if r i = r j then t₂.labels r else t₃.labels r

/-- Number of additions and comparisons executed on register file `r` (total charged work on
values, both resources on the same execution). -/
noncomputable def cost : {k : ℕ} → CATree n k → (Fin k → ℝ) → ℕ
  | _, .leaf _, _ => 0
  | _, .add i j t, r => t.cost (Fin.snoc r (r i + r j)) + 1
  | _, .cmp i j t₁ t₂ t₃, r =>
      (if r i < r j then t₁.cost r else if r i = r j then t₂.cost r else t₃.cost r) + 1

end CATree

/-- Reading a distance as an optional real (`⊤ ↦ none`). -/
noncomputable def toOptReal (x : ℝ≥0∞) : Option ℝ := if x = ⊤ then none else some x.toReal

/-- A nonuniform comparison–addition program for one topology: finitely many real literal
constants and a decision tree over the registers `w_0, …, w_{m-1}, 0, lit_0, …`. -/
structure CAProg (T : Topology) where
  lits : List ℝ
  tree : CATree T.n (T.m + 1 + lits.length)

/-- Initial register file: the weights, the constant `0`, then the literals. -/
noncomputable def CAProg.initRegs {T : Topology} (P : CAProg T) (w : Fin T.m → ℝ≥0) :
    Fin (T.m + 1 + P.lits.length) → ℝ :=
  fun j => if h : (j : ℕ) < T.m then (w ⟨j, h⟩ : ℝ)
    else if h' : (j : ℕ) - (T.m + 1) < P.lits.length then
      (if (j : ℕ) = T.m then 0 else P.lits.get ⟨(j : ℕ) - (T.m + 1), h'⟩)
    else 0

/-- The program solves exact SSSP from `s` on topology `T` for *every* nonnegative weighting:
each label is `⊤` exactly for unreachable vertices and otherwise equals the distance. -/
def CAProg.Solves {T : Topology} (P : CAProg T) (s : Fin T.n) : Prop :=
  ∀ w : Fin T.m → ℝ≥0, ∀ v : Fin T.n,
    P.tree.labels (P.initRegs w) v = toOptReal ((T.withW w).dist s v)

/-- Charged cost of the program on weighting `w`. -/
noncomputable def CAProg.cost {T : Topology} (P : CAProg T) (w : Fin T.m → ℝ≥0) : ℕ :=
  P.tree.cost (P.initRegs w)

/-- **Gate F**: a sparse family of topologies with sources, every vertex reachable, such that for
every constant `C`, eventually *every* correct comparison–addition program for the topology
(nonuniform, adaptive, real literals, free control and copying; additions and three-way
comparisons both charged on the same execution) costs `> C (n + m)` on some weighting.  Every
deterministic algorithm in the comparison–addition model yields such a program per topology (the
transfer from `RAM.Program` is informal so far, see F-v2-1 above), so this is a superlinear lower
bound for all of them; by Cai's Cor. 8.2 it is equivalent to `OPT_DIST = ω(n + m)` on the family. -/
def GateF : Prop :=
  ∃ (T : ℕ → Topology) (src : ∀ N, Fin (T N).n) (c : ℕ),
    (∀ N, (T N).m ≤ c * ((T N).n + 1)) ∧
    (∀ N (v : Fin (T N).n), ∃ p, ((T N).withW fun _ => 0).IsWalk (src N) v p) ∧
    ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ P : CAProg (T N), P.Solves (src N) →
      ∃ w : Fin (T N).m → ℝ≥0, C * (((T N).n : ℝ) + ((T N).m : ℝ)) < (P.cost w : ℝ)

end Frontier
