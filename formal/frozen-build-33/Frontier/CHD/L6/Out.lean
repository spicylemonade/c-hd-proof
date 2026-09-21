import Frontier.CHD.L6.Util
import Frontier.CHD.L6.Prog
import Frontier.CHD.Preprocess

/-!
# L6 output mapping (agent-10): `reach[v], dist[v]` from the core's label table

After the core, the label table of the reduced graph `H` (agent-02's `dfin`/`dlen`) holds the exact
distances from `rep s`.  `outProg` copies `dfin[gRep v]`, `dlen[gRep v]` for kept `v` and leaves
`reach[v] = 0` for dropped `v`; by `KReduction.dist_rep` / `dist_top` this solves `G`.
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM WExpr Stmt

/-- The core's output contract on `H` from source `src`: the label table decodes to the exact
distances. -/
structure CoreOut (H : Graph) (src : Fin H.n) (t : State ℝ≥0) : Prop where
  finL : H.n ≤ t.wlen "dfin"
  lenL : H.n ≤ t.vlen "dlen"
  exact : ∀ x : Fin H.n,
    (if t.wa "dfin" x = 0 then (⊤ : ℝ≥0∞) else ((t.va "dlen" x : ℝ≥0) : ℝ≥0∞)) = H.dist src x

def outWR : List String := ["g_v"]

structure OInv (G : Graph) (keep : Fin G.n → Prop) [DecidablePred keep] (rp : Fin G.n → ℕ)
    (t0 : State ℝ≥0) (v : ℕ) (t : State ℝ≥0) : Prop where
  gv : t.w "g_v" = v
  reach : ∀ u : Fin G.n, t.wa "reach" u = if (u : ℕ) < v ∧ keep u then t0.wa "dfin" (rp u) else 0
  dist : ∀ u : Fin G.n, t.va "dist" u = if (u : ℕ) < v ∧ keep u then t0.va "dlen" (rp u) else 0
  rL : t.wlen "reach" = G.n
  dL : t.vlen "dist" = G.n
  U : Unchanged t0 t ["reach"] ["dist"] outWR []
  c : t.cost ≤ t0.cost + 9 * v

theorem outLoop_runs {G H : Graph} {s : Fin G.n} (R : KReduction G H s) [DecidablePred R.keep]
    (t0 : State ℝ≥0) (hn : t0.w "n" = G.n) (hv0 : t0.w "g_v" = 0)
    (hkeepL : G.n ≤ t0.wlen "gKeep") (hkeep : ∀ v : Fin G.n, t0.wa "gKeep" v ≠ 0 ↔ R.keep v)
    (hrepL : G.n ≤ t0.wlen "gRep") (hrep : ∀ v : Fin G.n, R.keep v → t0.wa "gRep" v = (R.rep v : ℕ))
    (hcore : CoreOut H (R.rep s) t0)
    (hrL : t0.wlen "reach" = G.n) (hdL : t0.vlen "dist" = G.n)
    (hr0 : ∀ u : Fin G.n, t0.wa "reach" u = 0) (hd0 : ∀ u : Fin G.n, t0.va "dist" u = 0)
    (hcap : G.n + 2 < t0.cap) :
    Runs realOps (.while (lt (var "g_v") (var "n")) outBody) t0
      (fun r => ∃ t, OInv G R.keep (fun u => (R.rep u : ℕ)) t0 G.n t ∧ r = t.charge 1) := by
  refine runs_while (fun v t => OInv G R.keep (fun u => (R.rep u : ℕ)) t0 v t) G.n _ ?_ ?_ t0
    ⟨hv0, fun u => by simp [hr0], fun u => by simp [hd0], hrL, hdL, by simp, by simp⟩
  · intro v hv t hI
    have hU := hI.U
    have htcap : t.cap = t0.cap := hU.cap
    have htn : t.w "n" = G.n := by rw [hU.wreg _ (by simp [outWR])]; exact hn
    have htkeep : t.wa "gKeep" = t0.wa "gKeep" := (hU.warr _ (by simp)).1
    have htkeepL : t.wlen "gKeep" = t0.wlen "gKeep" := (hU.warr _ (by simp)).2
    have htrep : t.wa "gRep" = t0.wa "gRep" := (hU.warr _ (by simp)).1
    have htrepL : t.wlen "gRep" = t0.wlen "gRep" := (hU.warr _ (by simp)).2
    have htfin : t.wa "dfin" = t0.wa "dfin" := (hU.warr _ (by simp)).1
    have htfinL : t.wlen "dfin" = t0.wlen "dfin" := (hU.warr _ (by simp)).2
    have htlen : t.va "dlen" = t0.va "dlen" := (hU.varr _ (by simp)).1
    have htlenL : t.vlen "dlen" = t0.vlen "dlen" := (hU.varr _ (by simp)).2
    set u : Fin G.n := ⟨v, hv⟩ with hudef
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of (x := v) (y := G.n) (by rw [evalW_var, hI.gv]) (by rw [evalW_var, htn])
        (by omega)]
      simp [hv]
    · apply wp_sound
      by_cases hk : R.keep u
      · have hkv : t0.wa "gKeep" v ≠ 0 := (hkeep u).mpr hk
        have hrv : t0.wa "gRep" v = (R.rep u : ℕ) := hrep u hk
        have hrb : (R.rep u : ℕ) < H.n := (R.rep u).2
        simp [outBody, inc, wp, hI.gv, htkeep, htkeepL, hkv, htrep, htrepL, hrv, htfin, htfinL, htlen,
          htlenL, fit, htcap, hI.rL, hI.dL, hv, show 0 < t0.cap by omega, show 1 < t0.cap by omega,
          show v < t0.wlen "gKeep" by omega, show v < t0.wlen "gRep" by omega,
          show (R.rep u : ℕ) < t0.wlen "dfin" by have := hcore.finL; omega,
          show (R.rep u : ℕ) < t0.vlen "dlen" by have := hcore.lenL; omega,
          show v + 1 < t0.cap by omega]
        refine ⟨by simp, fun u' => ?_, fun u' => ?_, by simp [hI.rL], by simp [hI.dL],
          by simpa [outWR] using hU, by simp; have := hI.c; omega⟩
        · by_cases hu : (u' : ℕ) = v
          · have e : u' = u := Fin.ext hu
            subst e
            have hv' : ((u : Fin G.n) : ℕ) = v := rfl
            simp [hv', hk]
          · have hlt : (u' : ℕ) < v + 1 ↔ (u' : ℕ) < v := by omega
            simp only [State.charge_wa, State.setW_wa, State.storeV_wa, State.storeW_wa, true_and, hu,
              if_false, hI.reach u', hlt]
        · by_cases hu : (u' : ℕ) = v
          · have e : u' = u := Fin.ext hu
            subst e
            have hv' : ((u : Fin G.n) : ℕ) = v := rfl
            simp [hv', hk]
          · have hlt : (u' : ℕ) < v + 1 ↔ (u' : ℕ) < v := by omega
            simp only [State.charge_va, State.setW_va, State.storeV_va, State.storeW_va, true_and, hu,
              if_false, hI.dist u', hlt]
      · have hkv : t0.wa "gKeep" v = 0 := by
          by_contra h; exact hk ((hkeep u).mp h)
        simp [outBody, inc, wp, hI.gv, htkeep, htkeepL, hkv, fit, htcap, hv,
          show 0 < t0.cap by omega, show 1 < t0.cap by omega, show v < t0.wlen "gKeep" by omega,
          show v + 1 < t0.cap by omega]
        refine ⟨by simp, fun u' => ?_, fun u' => ?_, by simp [hI.rL], by simp [hI.dL],
          by simpa [outWR] using hU, by simp; have := hI.c; omega⟩
        · simp only [State.charge_wa, State.setW_wa]
          rw [hI.reach u']
          by_cases hu : (u' : ℕ) = v
          · have e : u' = u := Fin.ext hu
            subst e
            simp [hk]
          · have hlt : (u' : ℕ) < v + 1 ↔ (u' : ℕ) < v := by omega
            simp only [hlt]
        · simp only [State.charge_va, State.setW_va]
          rw [hI.dist u']
          by_cases hu : (u' : ℕ) = v
          · have e : u' = u := Fin.ext hu
            subst e
            simp [hk]
          · have hlt : (u' : ℕ) < v + 1 ↔ (u' : ℕ) < v := by omega
            simp only [hlt]
  · intro t hI
    have htcap : t.cap = t0.cap := hI.U.cap
    have htn : t.w "n" = G.n := by rw [hI.U.wreg _ (by simp [outWR])]; exact hn
    refine ⟨?_, t, hI, rfl⟩
    rw [evalW_lt_of (x := G.n) (y := G.n) (by rw [evalW_var, hI.gv]) (by rw [evalW_var, htn])
      (by omega)]
    simp

/-- The output of `outProg` solves `G`. -/
theorem solves_of_oinv {G H : Graph} {s : Fin G.n} (R : KReduction G H s) [DecidablePred R.keep]
    {t0 t : State ℝ≥0} (hcore : CoreOut H (R.rep s) t0)
    (hI : OInv G R.keep (fun u => (R.rep u : ℕ)) t0 G.n t) : (t.charge 1).Solves G s := by
  refine ⟨by simpa using hI.rL, by simpa using hI.dL, fun v => ?_⟩
  show (if (t.charge 1).wa "reach" v = 0 then ⊤ else (((t.charge 1).va "dist" v : ℝ≥0) : ℝ≥0∞)) =
    G.dist s v
  simp only [State.charge_wa, State.charge_va, hI.reach v, hI.dist v]
  by_cases hk : R.keep v
  · simp only [v.2, hk, and_self, if_true]
    have := hcore.exact (R.rep v)
    rw [this, R.dist_rep hk]
  · simp only [hk, and_false, if_false, if_true]
    exact (R.dist_top hk).symm

end Frontier.CHD.L6
