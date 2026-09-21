import Frontier.CHD.BMLazy

/-!
# Frontier.CHD.BMFresh — the fresh-id counter is bounded by the actual cost (owner: agent-01)

**NON-GATE** (Layer A).  Along every concrete run over agent-04's DLazy (`dlOps`), the global
fresh-id counter grows by at most the actual cost of the run: `gE.fresh ≤ g.fresh + lg.cost`.
Only a non-skipped `insertL` creates an entry (fresh `+1`, cost `≥ 3`); `pull`, `merge`, `delete`
and new structures create none.  With `MasterBound` (`lg.cost ≤ Km·Tchd`) this sizes the RAM
entry pool without any RAM-clock argument (agent-07, 17:37).
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

section fresh

variable {T : ℕ}

theorem insC_fresh_le (g : DGl G s) (Dc : DStrM G s) (v : Fin G.n) (lam : WLab G s) :
    (insC (dlOps G s) T g Dc v lam).1.fresh ≤ g.fresh + (insC (dlOps G s) T g Dc v lam).2.2 := by
  show (DL.insertL g.L g.fresh Dc v lam).2.1 ≤ g.fresh + (DL.insertL g.L g.fresh Dc v lam).2.2.2
  unfold DL.insertL DB.insert
  by_cases h : DB.skipIns g.L v lam = true
  · simp [h]
  · simp only [h, Bool.false_eq_true, if_false]
    omega

theorem insManyC_fresh_le (f : Fin G.n → WLab G s) :
    ∀ (l : List (Fin G.n)) (g : DGl G s) (Dc : DStrM G s),
      (insManyC (dlOps G s) T f l g Dc).1.fresh ≤ g.fresh + (insManyC (dlOps G s) T f l g Dc).2.2
  | [], g, Dc => by simp [insManyC]
  | y :: l, g, Dc => by
    have h1 := insC_fresh_le (T := T) g Dc y (f y)
    have h2 := insManyC_fresh_le f l (insC (dlOps G s) T g Dc y (f y)).1
      (insC (dlOps G s) T g Dc y (f y)).2.1
    show (insManyC (dlOps G s) T f l (insC (dlOps G s) T g Dc y (f y)).1
        (insC (dlOps G s) T g Dc y (f y)).2.1).1.fresh ≤
      g.fresh + ((insC (dlOps G s) T g Dc y (f y)).2.2 +
        (insManyC (dlOps G s) T f l (insC (dlOps G s) T g Dc y (f y)).1
          (insC (dlOps G s) T g Dc y (f y)).2.1).2.2)
    omega

theorem relaxInsCc_fresh_le (B : WLab G s) (lo : Option (WLab G s)) (st : RSt G s) (e : Fin G.m) :
    (relaxInsCc (dlOps G s) T B lo st e).g.fresh + st.c ≤
      st.g.fresh + (relaxInsCc (dlOps G s) T B lo st e).c := by
  classical
  have hins := insC_fresh_le (T := T) st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)
  unfold relaxInsCc
  split_ifs with hv
  · cases lo with
    | none =>
      show (insC (dlOps G s) T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).1.fresh + st.c ≤
        st.g.fresh + (st.c + 1 + (insC (dlOps G s) T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).2.2)
      omega
    | some b =>
      simp only
      split_ifs
      · show (insC (dlOps G s) T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).1.fresh + st.c ≤
          st.g.fresh + (st.c + 1 + (insC (dlOps G s) T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).2.2)
        omega
      · show st.g.fresh + st.c ≤ st.g.fresh + (st.c + 1)
        omega
  · show st.g.fresh + st.c ≤ st.g.fresh + (st.c + 1)
    omega

theorem fold_fresh_le (B : WLab G s) (lo : Option (WLab G s)) :
    ∀ (L : List (Fin G.m)) (st : RSt G s),
      (L.foldl (relaxInsCc (dlOps G s) T B lo) st).g.fresh + st.c ≤
        st.g.fresh + (L.foldl (relaxInsCc (dlOps G s) T B lo) st).c
  | [], st => le_rfl
  | e :: L, st => by
    rw [List.foldl_cons]
    have h1 := relaxInsCc_fresh_le (T := T) B lo st e
    have h2 := fold_fresh_le B lo L (relaxInsCc (dlOps G s) T B lo st e)
    omega

theorem finD_fresh_le (B B'f : WLab G s) (d : Labels G s) (g : DGl G s) (Dc : DStrM G s)
    (lT6 : List (Fin G.n)) (L : List (Fin G.m)) (lW' : List (Fin G.n)) :
    (finD (dlOps G s) T B B'f d g Dc lT6 L lW').2.1.fresh ≤
      g.fresh + (finD (dlOps G s) T B B'f d g Dc lT6 L lW').2.2.2 := by
  have h1 := insManyC_fresh_le (T := T) d lT6 g Dc
  have h2 := fold_fresh_le (T := T) B (some B'f) L
    ⟨d, (insManyC (dlOps G s) T d lT6 g Dc).1, (insManyC (dlOps G s) T d lT6 g Dc).2.1, 0⟩
  show (delC (L.foldl (relaxInsCc (dlOps G s) T B (some B'f))
      ⟨d, (insManyC (dlOps G s) T d lT6 g Dc).1, (insManyC (dlOps G s) T d lT6 g Dc).2.1, 0⟩).g lW').1.fresh ≤
    g.fresh + ((insManyC (dlOps G s) T d lT6 g Dc).2.2 + (L.foldl (relaxInsCc (dlOps G s) T B (some B'f))
      ⟨d, (insManyC (dlOps G s) T d lT6 g Dc).1, (insManyC (dlOps G s) T d lT6 g Dc).2.1, 0⟩).c
      + (delC (L.foldl (relaxInsCc (dlOps G s) T B (some B'f))
      ⟨d, (insManyC (dlOps G s) T d lT6 g Dc).1, (insManyC (dlOps G s) T d lT6 g Dc).2.1, 0⟩).g lW').2)
  have e : (delC (L.foldl (relaxInsCc (dlOps G s) T B (some B'f))
      ⟨d, (insManyC (dlOps G s) T d lT6 g Dc).1, (insManyC (dlOps G s) T d lT6 g Dc).2.1, 0⟩).g lW').1.fresh =
      (L.foldl (relaxInsCc (dlOps G s) T B (some B'f))
      ⟨d, (insManyC (dlOps G s) T d lT6 g Dc).1, (insManyC (dlOps G s) T d lT6 g Dc).2.1, 0⟩).g.fresh := rfl
  rw [e]
  simp only at h2
  omega

end fresh

section freshLoop

variable {Φ Ω : Type} {T : ℕ}

/-- **The loop.** -/
theorem loopD_fresh_le {subD : SubRelD G s Φ Ω} {B : WLab G s} {τl : ℕ} {p : ℕ}
    (hsub : ∀ Blow B S d φ g res φ' g' lg, subD Blow B S d φ g res φ' g' lg →
      g'.fresh ≤ g.fresh + Log.cost lg) :
    ∀ i (cs : CSt G s p) φ cs' φ' lg J cm c,
      LoopD G s (dlOps G s) T subD B τl i cs φ cs' φ' lg J cm c →
      cs'.g.fresh ≤ cs.g.fresh + c + Log.cost lg := by
  intro i cs φ cs' φ' lg J cm c hloop
  induction hloop with
  | stop i cs φ _ => simp [Log.cost]
  | step i cs cs' φ φ1 φ' ks Bi g1 Dc1 cp B'i Ui Dci d1' g2 lUi L' piv' lres lg lg' J' cm c
      _ _ hpull hsubD _ _ _ _ _ _ _ _ ih =>
    have hg1 : g1.fresh = cs.g.fresh := by
      simp only [pullC, Prod.mk.injEq] at hpull
      rw [← hpull.2.2.1]
    have h2 := hsub _ _ _ _ _ _ _ _ _ _ hsubD
    have h3 := fold_fresh_le (T := T) B (some Bi) L' ⟨d1', (delC g2 lUi).1, ((dlOps G s).merge T Dc1 Dci).1, 0⟩
    have h4 := insManyC_fresh_le (T := T)
      (L'.foldl (relaxInsCc (dlOps G s) T B (some Bi)) ⟨d1', (delC g2 lUi).1, ((dlOps G s).merge T Dc1 Dci).1, 0⟩).d
      lres (L'.foldl (relaxInsCc (dlOps G s) T B (some Bi)) ⟨d1', (delC g2 lUi).1, ((dlOps G s).merge T Dc1 Dci).1, 0⟩).g
      (L'.foldl (relaxInsCc (dlOps G s) T B (some Bi)) ⟨d1', (delC g2 lUi).1, ((dlOps G s).merge T Dc1 Dci).1, 0⟩).Dc
    have hdel : (delC g2 lUi).1.fresh = g2.fresh := rfl
    simp only at h3
    have hcost : Log.cost (lg.shift i ++ lg') = Log.cost lg + Log.cost lg' := by
      unfold Log.cost Log.shift; rw [List.map_append, List.sum_append, List.map_map]; rfl
    rw [hcost]
    have hit : (L'.foldl (relaxInsCc (dlOps G s) T B (some Bi))
          ⟨d1', (delC g2 lUi).1, ((dlOps G s).merge T Dc1 Dci).1, 0⟩).c +
        (insManyC (dlOps G s) T (L'.foldl (relaxInsCc (dlOps G s) T B (some Bi))
            ⟨d1', (delC g2 lUi).1, ((dlOps G s).merge T Dc1 Dci).1, 0⟩).d lres
          (L'.foldl (relaxInsCc (dlOps G s) T B (some Bi)) ⟨d1', (delC g2 lUi).1, ((dlOps G s).merge T Dc1 Dci).1, 0⟩).g
          (L'.foldl (relaxInsCc (dlOps G s) T B (some Bi))
            ⟨d1', (delC g2 lUi).1, ((dlOps G s).merge T Dc1 Dci).1, 0⟩).Dc).2.2 ≤
        iterCostD (dlOps G s) T B cs ks.toFinset cp Bi Ui Dc1 Dci d1' g2 lUi L' lres := by
      unfold iterCostD; omega
    have hnext : (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).g.fresh =
        (insManyC (dlOps G s) T (L'.foldl (relaxInsCc (dlOps G s) T B (some Bi))
            ⟨d1', (delC g2 lUi).1, ((dlOps G s).merge T Dc1 Dci).1, 0⟩).d lres
          (L'.foldl (relaxInsCc (dlOps G s) T B (some Bi)) ⟨d1', (delC g2 lUi).1, ((dlOps G s).merge T Dc1 Dci).1, 0⟩).g
          (L'.foldl (relaxInsCc (dlOps G s) T B (some Bi))
            ⟨d1', (delC g2 lUi).1, ((dlOps G s).merge T Dc1 Dci).1, 0⟩).Dc).1.fresh := rfl
    rw [hnext] at ih
    omega

end freshLoop

section freshLevels

variable {Φ Ω : Type} {T : ℕ → ℕ} {DCb : DCost}

/-- **Every concrete run over DLazy**: the fresh-id counter grows by at most the actual cost. -/
theorem bmsspD_fresh_le {FPC : FPRelC G s Φ Ω} {Mf : ℕ → ℕ} (τ : ℕ → ℕ) :
    ∀ l Blow B S d φ g res φ' g' lg,
      BMSSPD G s (dlOps G s) FPC DCb T Mf τ l Blow B S d φ g res φ' g' lg →
      g'.fresh ≤ g.fresh + Log.cost lg
  | 0 => by
    intro Blow B S d φ g res φ' g' lg hrel
    obtain ⟨st, c, lK, -, -, -, -, -, -, hgE, -, -, -, hlg⟩ := hrel
    subst hlg
    rw [hgE]
    have h := insManyC_fresh_le (T := T 0) st.1 lK g (newC (Mf 0) B)
    simp only [Log.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  | l + 1 => by
    intro Blow B S d φ g res φ' g' lg hrel
    obtain ⟨d1, p, P, Q, W, φ1, ω, cfp, piv, lpiv, cs, lgc, J, cm, cl, L, B'f, lT6, W', lW', -,
      -, -, -, hloop, -, -, -, -, -, -, -, -, -, hgE, hlg⟩ := hrel
    have hsub := bmsspD_fresh_le (FPC := FPC) (Mf := Mf) τ l
    have hL := loopD_fresh_le (T := T (l + 1)) (fun Blow B S d φ g res φ' g' lg h => hsub Blow B S d φ g res φ' g' lg h)
      _ _ _ _ _ _ _ _ _ hloop
    have hI := insManyC_fresh_le (T := T (l + 1)) d1 lpiv g (newC (Mf (l + 1)) B)
    have hF := finD_fresh_le (T := T (l + 1)) B B'f cs.d cs.g cs.Dc lT6 L lW'
    subst hlg
    rw [hgE]
    simp only [Log.cost, List.map_cons, List.sum_cons] at hL ⊢
    change (finD (dlOps G s) (T (l + 1)) B B'f cs.d cs.g cs.Dc lT6 L lW').2.1.fresh ≤ _
    have hi : (initD (dlOps G s) (T (l + 1)) (Mf (l + 1)) B d1 lpiv g).1.fresh ≤
        g.fresh + (initD (dlOps G s) (T (l + 1)) (Mf (l + 1)) B d1 lpiv g).2.2 := hI
    have hcs0 : (CSt.mk (p := p) d1 P piv ∅ (initB' B d1 piv)
        (initD (dlOps G s) (T (l + 1)) (Mf (l + 1)) B d1 lpiv g).1
        (initD (dlOps G s) (T (l + 1)) (Mf (l + 1)) B d1 lpiv g).2.1).g.fresh =
        (initD (dlOps G s) (T (l + 1)) (Mf (l + 1)) B d1 lpiv g).1.fresh := rfl
    omega

end freshLevels

end BM
end CHD
end Frontier
