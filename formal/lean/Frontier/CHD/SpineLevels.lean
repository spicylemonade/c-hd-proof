import Frontier.CHD.SpineLoop

/-!
# SpineLevels — the recursive procedure and the level induction (agent-08, B-L4, NON-GATE)

`bmsspProc base rec` is the body of procedure `P_bmssp`: the base case at level `0`, the
recursive body at levels `≥ 1`.  `callSpec_all` is the induction over the levels: the base case's
`CallSpec 0` (agent-03) and the level step `CallSpec l → CallSpec (l+1)` at the same constant
(agent-01's `body_spec`) give `CallSpec l` at every level.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamSpine

open Frontier Frontier.RAM Frontier.CHD Frontier.CHD.BM WExpr Stmt

/-- **The procedure `P_bmssp`**: base case at level `0`, recursive body above. -/
def bmsspProc (base rec : Stmt) : Stmt := ite (var "lvl") rec base

/-- The procedure table of the spine. -/
def spinePs (base rec : Stmt) : List Stmt := [bmsspProc base rec]

theorem spinePs_proc (base rec : Stmt) : (spinePs base rec)[P_bmssp]? = some (bmsspProc base rec) :=
  rfl

variable {V : Type} {ops : VOps V}

/-- A call at level `0` runs the base case (after the call and the test charges). -/
theorem runs_call_base {st : State V} {base rec : Stmt} {Q : State V → Prop}
    (hp : st.procs[P_bmssp]? = some (bmsspProc base rec)) (hl : st.w "lvl" = 0)
    (h : Runs ops base (st.enter.charge 1) Q) : Runs ops (call P_bmssp) st Q :=
  runs_call hp (runs_ite_false (by simp [State.enter, hl]) h)

/-- A call at level `l + 1` runs the recursive body. -/
theorem runs_call_rec {st : State V} {base rec : Stmt} {Q : State V → Prop} {l : ℕ}
    (hp : st.procs[P_bmssp]? = some (bmsspProc base rec)) (hl : st.w "lvl" = l + 1)
    (h : Runs ops rec (st.enter.charge 1) Q) : Runs ops (call P_bmssp) st Q :=
  runs_call hp (runs_ite_true (x := l + 1) (by simp [State.enter, hl]) (by omega) h)

section induction

variable {G : Graph} {s : Fin G.n} {T : ℕ → ℕ} {Φ Ω : Type}

/-- **The level induction**: `CallSpec` at every level, from the base case and the level step
at the same constants. -/
theorem callSpec_all {DL : DLayer G s T} {PhiR : State ℝ≥0 → Φ → Prop} {Inv : Φ → Prop}
    {FPC : FPRelC G s Φ Ω} {DCb : DCost} {Mf τ : ℕ → ℕ} {LF : ℕ} {body : Stmt} {K Sl : ℕ}
    {Sb : ℕ → ℕ}
    (hbase : CallSpec DL PhiR Inv FPC DCb Mf τ LF body K Sl Sb 0)
    (hstep : ∀ l, CallSpec DL PhiR Inv FPC DCb Mf τ LF body K Sl Sb l →
      CallSpec DL PhiR Inv FPC DCb Mf τ LF body K Sl Sb (l + 1)) :
    ∀ l, CallSpec DL PhiR Inv FPC DCb Mf τ LF body K Sl Sb l
  | 0 => hbase
  | l + 1 => hstep l (callSpec_all hbase hstep l)

end induction

end Frontier.CHD.RamSpine
