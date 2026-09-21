import Frontier.CHD.CostLog

/-!
# Frontier.CHD.RecFPLog — per-record FindPivots facts of the traced run (owner agent-03)

**NON-GATE** (Layer A).  Every record of every `BMSSPC` derivation with `FPC := fpC …` satisfies
`FPForeign.RecFP` (the FindPivots relation at the record's `B, S` under `CallPre`, `U = Ũ(B', S)`,
`B_low ≤ B`, `B_low ≤ dis` on `S`) and `CrBe.RecForest` (parent-first, disjoint trees whose edges have an
extracted source), plus a duplicate-free forest.  These discharge the interface hypotheses of FPForeign and CrBe.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

section RecFPSec

variable {DC : DCost} {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}

/-- All per-record facts needed by the cost chain. -/
def RecAll (out : Fin G.n → List (Fin G.m)) (k hins hext : ℕ) (r : CallRec G s (FPData G s)) : Prop :=
  RecFP out k hins hext r ∧ RecForest r ∧
    (∀ ω, r.fp = some ω → (ω.trees.flatMap (fun T => T.ord)).Nodup) ∧ (r.base = false → ∃ ω, r.fp = some ω)

/-- Sub-calls whose logs carry `RecAll`. -/
def SubAll (sub : SubRelC G s (Finset (Fin G.m)) (FPData G s)) : Prop :=
  ∀ Blow B S d φ res φ' lg, CallPre B S d → DelInv G s φ → (∀ x ∈ S, Blow ≤ dis (s := s) x) → Blow ≤ B →
    sub Blow B S d φ res φ' lg → ∀ q r, (q, r) ∈ lg → RecAll out k hins hext r

end RecFPSec

section ForestFacts

variable {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}

/-- **The forest of an `fpC` run is parent-first and vertex-disjoint** (agent-05's `FInv`, at the relation level). -/
theorem fpC_forest (hout : ∀ u e, e ∈ out u ↔ G.src e = u) (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    {l : ℕ} {Blow B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {Din Dout : Finset (Fin G.m)}
    {p : ℕ} {P : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {ω : FPData G s} {c : ℕ}
    (hpre : CallPre B S d0) (h : fpC G s out k hins hext l Blow B S d0 Din d1 p P Q W Dout ω c) :
    (∀ T ∈ ω.trees, Partition.ParentFirst T.par T.root T.ord) ∧
      ω.trees.Pairwise (fun a b => ∀ w ∈ a.ord, w ∉ b.ord) := by
  obtain ⟨⟨SL, ι', -, hSL, hrun, -, -, -, -, htr, -⟩, -⟩ := h
  set c := pinCtx out k hins hext B (lxOf B S d0)
  have hout' : OutOK c := hout
  have hsort' : OutSorted c := hsort
  have hpre' : CallPre c.B S d0 := hpre
  have hF0 : FInv c (⟨d0, Din, ∅, ∅, ∅, []⟩ : IState G s) :=
    ⟨fun T hT => absurd hT List.not_mem_nil, fun T hT => absurd hT List.not_mem_nil,
      fun v => by simp, List.Pairwise.nil⟩
  have hF := Invoke.forest hout' hsort' hpre' hrun (fun x hx => (hSL x).mp hx) hpre.walk (fun _ => le_rfl) hF0
  rw [htr]
  exact ⟨hF.pf, hF.disj⟩

end ForestFacts

section LoopAll

variable {DC : DCost} {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}
variable {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {p : ℕ}
  {P0 : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {B'0 : WLab G s}

/-- **The loop log's records are sub-call records** (so they inherit `RecAll`). -/
theorem loopC_recall (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W)
    {τ : ℕ → ℕ} {sub : SubRelC G s (Finset (Fin G.m)) (FPData G s)} {l : ℕ}
    (hsub : GoodSub G s τ (DelInv G s) l sub) (hsuba : SubAll (out := out) (k := k) (hins := hins) (hext := hext) sub)
    {τl : ℕ} :
    ∀ i (σ : LState G s p) φ σ' φ' lg J cm c,
      LoopC G s DC sub (l + 1) B τl i σ φ σ' φ' lg J cm c →
      LInv G s B S d0 d1 P0 B'0 σ → DelInv G s φ → ∀ q r, (q, r) ∈ lg → RecAll out k hins hext r := by
  intro i σ φ σ' φ' lg J cm c hloop
  induction hloop with
  | stop i σ φ hstop =>
    intro _ _ q r h; exact absurd h List.not_mem_nil
  | step i σ σ' φ φ1 φ' S0 Bi D1 B'i Ui Di dsub L' piv' lg lg' J' cm c _ hne hpull' _ _ hsubrel
      hnd hmem hres _ ih =>
    intro h hI
    have hsp : CallPre Bi (expand σ S0 Bi) σ.d := step_pre hpre hfp h hpull'
    have hlowdis : ∀ x ∈ expand σ S0 Bi, σ.B' ≤ dis (s := s) x :=
      fun x hx => (Si_facts h hpull' hx).1.2.2
    have hSne : S0.Nonempty := by
      apply hpull'.nonempty
      simp only [DS.IsEmpty, not_forall] at hne
      exact hne
    obtain ⟨x0, hx0⟩ := hSne
    have hx0S : x0 ∈ expand σ S0 Bi := mem_expand.mpr (Or.inl hx0)
    have hBlt : σ.B' < Bi := by
      obtain ⟨⟨-, -, hB⟩, hlt⟩ := Si_facts h hpull' hx0S
      exact lt_of_le_of_lt (hB.trans (h.walk.sound x0)) hlt
    obtain ⟨hpost, hI1, -⟩ := hsub σ.B' Bi (expand σ S0 Bi) σ.d φ (B'i, Ui, Di, dsub) φ1 lg
      hsp hI hlowdis hBlt.le hsubrel
    have hra := hsuba σ.B' Bi (expand σ S0 Bi) σ.d φ (B'i, Ui, Di, dsub) φ1 lg hsp hI hlowdis hBlt.le hsubrel
    have hmem' : ∀ e, e ∈ L' ↔ G.src e ∈ Ui ∧ Bi ≤ ext (dis (s := s) (G.src e)) e ∧
        ext (dis (s := s) (G.src e)) e < B := by
      intro e
      rw [hmem e]
      constructor
      · rintro ⟨hu, h1, h2⟩
        have hc : dsub (G.src e) = dis (s := s) (G.src e) := hpost.U_complete _ hu
        rw [hc] at h1 h2
        exact ⟨hu, h1, h2⟩
      · rintro ⟨hu, h1, h2⟩
        have hc : dsub (G.src e) = dis (s := s) (G.src e) := hpost.U_complete _ hu
        rw [← hc] at h1 h2
        exact ⟨hu, h1, h2⟩
    obtain ⟨L, hL, hfold⟩ :=
      window_scan_step hpull'.bound hpost ((D1.merge Di).deleteSet Ui) hnd hmem'
    have hres' : Reselect σ Ui
        (L.foldl (relaxIns G s B (some Bi)) (dsub, (D1.merge Di).deleteSet Ui)).1 piv' := by
      rw [hfold]; exact hres
    have hnext := step_post hpre hfp h hne hpull' hpost hL hres'
    rw [hfold] at hnext
    have ih' := ih hnext hI1
    intro q r hqr
    rcases List.mem_append.mp hqr with h1 | h2
    · obtain ⟨q', -, hq'⟩ := mem_shift.mp h1
      exact hra q' r hq'
    · exact ih' q r h2

end LoopAll

section CallAll

variable {DC : DCost} {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}

theorem recForest_of_run (hout : ∀ u e, e ∈ out u ↔ G.src e = u) (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    {l : ℕ} {Blow B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {Din Dout : Finset (Fin G.m)}
    {p : ℕ} {P : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {ω : FPData G s} {c : ℕ}
    (hpre : CallPre B S d0) (hI : DelInv G s Din)
    (h : fpC G s out k hins hext l Blow B S d0 Din d1 p P Q W Dout ω c) (r : CallRec G s (FPData G s))
    (hr : r.fp = some ω) (hrB : r.B = B) (hrS : r.S = S) :
    RecForest r ∧ ∀ ω', r.fp = some ω' → (ω'.trees.flatMap (fun T => T.ord)).Nodup := by
  obtain ⟨hpf, hdisj⟩ := fpC_forest hout hsort hpre h
  obtain ⟨hedge, hnd⟩ := fpC_tedge hout hsort hpre hI h
  have hω : ∀ ω', r.fp = some ω' → ω' = ω := fun ω' h' => by rw [hr] at h'; exact (Option.some.inj h').symm
  refine ⟨⟨fun ω' h' => (hω ω' h') ▸ hpf, fun ω' h' => (hω ω' h') ▸ hdisj, ?_⟩, fun ω' h' => (hω ω' h') ▸ hnd⟩
  intro ω' h' T hT x hx
  obtain rfl := hω ω' h'
  have hpfT := hpf T hT
  have hxo : x ∈ T.ord := List.mem_of_mem_tail hx
  have hxr : x ≠ T.root := by
    obtain ⟨hnd', hhead, -⟩ := hpfT
    cases hord : T.ord with
    | nil => rw [hord] at hx; simp at hx
    | cons a t =>
      rw [hord] at hx hhead hnd'
      simp only [List.head?_cons, Option.some.injEq] at hhead
      simp only [List.tail_cons] at hx
      intro hxa
      exact (List.nodup_cons.mp hnd').1 (hhead ▸ hxa ▸ hx)
  obtain ⟨e, he, hsrc⟩ := hedge T hT x hxo hxr
  exact ⟨e, he, by rw [hrB, hrS]; exact hsrc⟩

/-- **Every record of every `BMSSPC` derivation carries `RecAll`** (all levels). -/
theorem bmsspC_recall (hout : ∀ u e, e ∈ out u ↔ G.src e = u) (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hsimp : ∀ u, ((out u).map G.dst).Nodup) (hk : 2 ≤ k) (τ : ℕ → ℕ) :
    ∀ l, SubAll (out := out) (k := k) (hins := hins) (hext := hext)
      (BMSSPC G s (fpC G s out k hins hext) DC τ l)
  | 0 => by
    intro Blow B S d φ res φ' lg hpre hI hlow hBB hrel
    obtain ⟨hpost, -, -⟩ := baseC_log hpre hlow hrel
    obtain ⟨st, c, -, hU, -, -, -, -, -, rfl⟩ := hrel
    intro q r hqr
    rcases List.mem_singleton.mp hqr with heq
    obtain ⟨-, rfl⟩ := Prod.mk.inj heq
    refine ⟨⟨hBB, fun v => ?_, hlow, fun _ => rfl, fun ω h => by simp at h⟩,
      ⟨fun ω h => by simp at h, fun ω h => by simp at h, fun ω h => by simp at h⟩, fun ω h => by simp at h,
      fun h => by simp at h⟩
    exact hpost.U_eq v
  | l + 1 => by
    intro Blow B S d φ res φ' lg hpre hI hlow hBB hrel
    have hsub := bmsspC_log (DC := DC) (fpC_sound (hins := hins) (hext := hext) hout hsort hsimp hk) τ l
    have hsuba := bmsspC_recall hout hsort hsimp hk τ l
    obtain ⟨hpost, -, -⟩ := callC_log (fpC_sound (hins := hins) (hext := hext) hout hsort hsimp hk) hsub hpre hI hlow hBB hrel
    obtain ⟨d1, p, P, Q, W, φ1, ω, cfp, piv, σ, lgc, J, cm, cl, L, B'f, T6, W', hfprel, hpiv,
      hloop, hB'e, hB'n, hT6, hW', hL, hres, rfl⟩ := hrel
    have hlow' : ∀ x ∈ S, Blow ≤ d x := fun x hx => (hlow x hx).trans (hpre.walk.sound x)
    obtain ⟨hfp, hI1⟩ := fpC_sound hout hsort hsimp hk _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpre hI hlow' hfprel
    have h0 := linv_init hpre hfp hpiv
    have hloopall := loopC_recall (DC := DC) hpre hfp hsub hsuba _ _ _ _ _ _ _ _ _ hloop h0 hI1
    intro q r hqr
    rcases List.mem_cons.mp hqr with heq | hmem
    · obtain ⟨-, rfl⟩ := Prod.mk.inj heq
      refine ⟨⟨hBB, fun v => ?_, hlow, fun h => by simp at h, fun ω' h' => ?_⟩,
        (recForest_of_run hout hsort hpre hI hfprel _ rfl rfl rfl).1,
        (recForest_of_run hout hsort hpre hI hfprel _ rfl rfl rfl).2, fun _ => ⟨ω, rfl⟩⟩
      · have := hpost.U_eq v
        rw [hres] at this
        exact this
      · simp only [Option.some.injEq] at h'
        subst h'
        exact ⟨d, d1, φ, φ1, P, cfp, hpre, hI, hfprel⟩
    · exact hloopall q r hmem

end CallAll

end BM
end CHD
end Frontier
