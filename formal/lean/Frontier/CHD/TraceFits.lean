import Frontier.CHD.TraceSizeD
import Frontier.CHD.SizeParams
import Frontier.CHD.BMTeleLoop
import Frontier.CHD.BMTeleChd

/-!
# Frontier.CHD.TraceFits — the subtree placement budgets of the C-HD run (owner: agent-01)

**NON-GATE** (Layer A).  Discharges the budget hypothesis `Fits` of `BMTeleLoop.bmsspDL_tele_top'`
for the C-HD parameters, from agent-03's trace-size facts (used as black boxes):

* `wB_sub_le` / `ownSum_sub_le`: the (B4′) sum of agent-03's `wB_sum_le` at ANY record of a
  `LogInv` log: `ownSum (subLog lg x) ≤ (3(L0+1) + 3δ)·|U_x|` (same proof with the root replaced by
  `x`; `sub_U_le` and `sub_events_le` are already per record);
* `ownSum_sub_base`: a base record's subtree is the record itself;
* `bmsspC_recU`: every record of a traced `fpC` run returns `|U| ≤ ucap lvl |S|` and is a base
  record exactly at level `0` (an induction over derivations with agent-03's `bmsspC_sizes`);
* `fits_of_top`: with `ChildS` (children have `|S| ≤ 3k·M`), `ucap_le` (`ucap ≤ 2τ`) and
  `|S| ≤ |U|` on every record, the top run fits `chdEmax`;
* `chdDL_tele_top`: **the top-level DLazy run's actual cost is at most its literal twin's cost
  with `chdDC`**, for the C-HD parameters, with no further hypothesis.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-! ## Subtree sums -/

section SubT

variable {Ω : Type} {τ : ℕ → ℕ} {L0 : ℕ} {lg : Log G s Ω} (hL : LogInv τ L0 lg)
include hL

omit hL in
theorem Eout_card_le {δ : ℕ} (hdeg : ∀ u, (Eout G {u}).card ≤ δ) (U : Finset (Fin G.n)) :
    (Eout G U).card ≤ δ * U.card := by
  classical
  have : Eout G U = U.biUnion (fun u => Eout G {u}) := by
    ext e; simp [Eout]
  rw [this]
  calc _ ≤ ∑ u ∈ U, (Eout G {u}).card := Finset.card_biUnion_le
    _ ≤ ∑ u ∈ U, δ := Finset.sum_le_sum (fun u _ => hdeg u)
    _ = δ * U.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- **Trace-size sum of a subtree** (agent-03's `wB_sum_le` at any record `x`). -/
theorem wB_sub_le (δ : ℕ) (hdeg : ∀ u, (Eout G {u}).card ≤ δ)
    (hSU : ∀ q r, (q, r) ∈ lg → r.S.card ≤ r.U.card) {x : List ℕ} {rx : CallRec G s Ω}
    (hx : (x, rx) ∈ lg) :
    ((subLog lg x).map (fun qr => wB qr.2)).sum ≤ (3 * (L0 + 1) + 3 * δ) * rx.U.card := by
  classical
  have hnd : (subLog lg x).Pairwise (fun a b => a.1 ≠ b.1) :=
    (List.pairwise_map.mp hL.nodup).sublist List.filter_sublist
  have hUsub : ∀ qr ∈ subLog lg x, qr.2.U ⊆ rx.U := by
    intro qr hqr
    obtain ⟨hmem, hpre⟩ := mem_subLog.mp hqr
    obtain ⟨r1, hr1, hU, -⟩ := prefix_rec' hL hmem (q0 := x) hpre
    have := rec_unique hL.nodup hr1 hx
    subst this
    exact hU
  have hE : (Eout G rx.U).card ≤ δ * rx.U.card := Eout_card_le hdeg rx.U
  -- (1) frontiers
  have hS : ((subLog lg x).map (fun qr => qr.2.S.card)).sum ≤ (L0 + 1) * rx.U.card :=
    le_trans (Reselect.map_sum_le _ _ _ (fun qr hqr => hSU qr.1 qr.2 (mem_subLog.mp hqr).1))
      (sub_U_le hL hx)
  -- (2) jumps of recursive records
  have hJ : ((subLog lg x).map (fun qr => if qr.2.base = true then 0 else qr.2.J.card)).sum ≤
      (Eout G rx.U).card := by
    have h2 := sub_events_le hL hx
    refine le_trans (Reselect.map_sum_le _ _ _ (fun qr hqr => ?_)) h2
    split_ifs with hb
    · exact Nat.zero_le _
    · refine Finset.card_le_card (fun e he => ?_)
      unfold evOf
      rw [if_neg hb]
      exact Finset.mem_union_left _ he
  -- (3) `W'` relaxations
  have hW : ((subLog lg x).map (fun qr => qr.2.Wr.card)).sum ≤ (Eout G rx.U).card := by
    refine sum_disjoint_le (subLog lg x) (fun qr => qr.2.Wr) _
      (hnd.imp_of_mem (fun {a b} ha hb hne => ?_)) (fun qr hqr e he => ?_)
    · exact wr_disjoint hL (mem_subLog.mp ha).1 (mem_subLog.mp hb).1 hne
    · simp only [Eout, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hUsub qr hqr (hL.wr qr.1 qr.2 (mem_subLog.mp hqr).1 e he).1
  -- (4) out-edges of base calls
  have hB : ((subLog lg x).map (fun qr => if qr.2.base = true then (Eout G qr.2.U).card else 0)).sum ≤
      (Eout G rx.U).card := by
    have e1 : ((subLog lg x).map (fun qr => if qr.2.base = true then (Eout G qr.2.U).card else 0)) =
        ((subLog lg x).map (fun qr => (if qr.2.base = true then Eout G qr.2.U else ∅).card)) := by
      refine List.map_congr_left (fun qr _ => ?_)
      split_ifs <;> simp
    rw [e1]
    refine sum_disjoint_le (subLog lg x) (fun qr => if qr.2.base = true then Eout G qr.2.U else ∅) _
      (hnd.imp_of_mem (fun {a b} ha hb hne => ?_)) (fun qr hqr e he => ?_)
    · by_cases hba : a.2.base = true
      · by_cases hbb : b.2.base = true
        · simp only [hba, hbb, if_true]
          rw [Finset.disjoint_left]
          intro e hea heb
          simp only [Eout, Finset.mem_filter, Finset.mem_univ, true_and] at hea heb
          exact Finset.disjoint_left.mp
            (base_disjoint hL (mem_subLog.mp ha).1 (mem_subLog.mp hb).1 hba hbb hne) hea heb
        · simp [hbb]
      · simp [hba]
    · split_ifs at he with hb
      · simp only [Eout, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
        exact hUsub qr hqr he
      · simp at he
  -- assemble
  have hpt : ∀ qr ∈ subLog lg x, wB qr.2 ≤ 3 * qr.2.S.card +
      (if qr.2.base = true then 0 else qr.2.J.card) + qr.2.Wr.card +
      (if qr.2.base = true then (Eout G qr.2.U).card else 0) := by
    intro qr _
    unfold wB
    split_ifs <;> omega
  have hsum := Reselect.map_sum_le _ _ _ hpt
  rw [List.sum_map_add, List.sum_map_add, List.sum_map_add, List.sum_map_mul_left] at hsum
  have : (3 * (L0 + 1) + 3 * δ) * rx.U.card = 3 * ((L0 + 1) * rx.U.card) + 3 * (δ * rx.U.card) := by
    ring
  omega

/-- **(B4′) at any record**: the own placements of the subtree of `x`. -/
theorem ownSum_sub_le (δ : ℕ) (hdeg : ∀ u, (Eout G {u}).card ≤ δ)
    (hSU : ∀ q r, (q, r) ∈ lg → r.S.card ≤ r.U.card) {x : List ℕ} {rx : CallRec G s Ω}
    (hx : (x, rx) ∈ lg) :
    Log.ownSum (subLog lg x) ≤ (3 * (L0 + 1) + 3 * δ) * rx.U.card := by
  calc Log.ownSum (subLog lg x) = ((subLog lg x).map fun qr => ownB qr.2).sum := rfl
    _ ≤ ((subLog lg x).map fun qr => wB qr.2).sum :=
        Reselect.map_sum_le _ _ _ (fun qr hqr => ownB_le_wB hL (q := qr.1) (mem_subLog.mp hqr).1)
    _ ≤ _ := wB_sub_le hL δ hdeg hSU hx

/-- A base record's subtree is the record itself. -/
theorem ownSum_sub_base {x : List ℕ} {rx : CallRec G s Ω} (hx : (x, rx) ∈ lg)
    (hb : rx.base = true) : Log.ownSum (subLog lg x) = ownB rx := by
  classical
  have hall : ∀ qr ∈ subLog lg x, qr = (x, rx) := by
    rintro ⟨q', r'⟩ hqr
    obtain ⟨hmem, ⟨tl, htl⟩⟩ := mem_subLog.mp hqr
    have htl' : x ++ tl = q' := htl
    clear htl
    rcases tl with _ | ⟨a, tl'⟩
    · simp only [List.append_nil] at htl'
      subst htl'
      have := rec_unique hL.nodup hmem hx
      subst this
      rfl
    · exfalso
      obtain ⟨r0, hr0, -, -⟩ := prefix_rec' hL hmem (q0 := x ++ [a]) ⟨tl', by rw [← htl']; simp⟩
      exact hL.base x rx hx hb a r0 hr0
  have hmem : (x, rx) ∈ subLog lg x := mem_subLog.mpr ⟨hx, List.prefix_refl x⟩
  have hnd : ((subLog lg x).map Prod.fst).Nodup := ((List.filter_sublist).map _).nodup hL.nodup
  generalize subLog lg x = l at hall hmem hnd ⊢
  rcases l with _ | ⟨a, _ | ⟨b, l'⟩⟩
  · simp at hmem
  · rw [hall a List.mem_cons_self]
    simp [Log.ownSum]
  · exfalso
    have ha := hall a List.mem_cons_self
    have hb' := hall b (List.mem_cons_of_mem _ List.mem_cons_self)
    have h1 := (List.nodup_cons.mp hnd).1
    apply h1
    rw [ha, List.map_cons, hb']
    exact List.mem_cons_self

end SubT

/-! ## Per-record returned-set caps -/

section RecU

variable {DC : DCost} {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}
variable {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {p : ℕ}
  {P0 : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {B'0 : WLab G s}

/-- Per-record size facts: the returned-set cap, and base records are exactly the level-`0` ones. -/
def RecU (DC : DCost) (k : ℕ) (τ : ℕ → ℕ) (lg : Log G s (FPData G s)) : Prop :=
  ∀ q r, (q, r) ∈ lg → r.U.card ≤ ucap DC k τ r.lvl r.S.card ∧ (r.base = true ↔ r.lvl = 0)

theorem loopC_recU (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W)
    {τ : ℕ → ℕ} {Inv : Finset (Fin G.m) → Prop}
    {sub : SubRelC G s (Finset (Fin G.m)) (FPData G s)} {l : ℕ}
    (hsub : GoodSub G s τ Inv l sub)
    (hsubU : ∀ Blow B S d φ res φ' lg, CallPre B S d → Inv φ → (∀ x ∈ S, Blow ≤ dis (s := s) x) →
      Blow ≤ B → sub Blow B S d φ res φ' lg → RecU DC k τ lg)
    {τl : ℕ} :
    ∀ i (σ : LState G s p) φ σ' φ' lg J cm c,
      LoopC G s DC sub (l + 1) B τl i σ φ σ' φ' lg J cm c →
      LInv G s B S d0 d1 P0 B'0 σ → Inv φ → RecU DC k τ lg := by
  intro i σ φ σ' φ' lg J cm c hloop
  induction hloop with
  | stop i σ φ hstop => intro _ _ q r h; exact absurd h List.not_mem_nil
  | step i σ σ' φ φ1 φ' S0 Bi D1 B'i Ui Di dsub L' piv' lg lg' J' cm c hUτ hne hpull' hSM _ hsubrel
      hnd hmem hres hrest ih =>
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
    have hU1 := hsubU σ.B' Bi (expand σ S0 Bi) σ.d φ (B'i, Ui, Di, dsub) φ1 lg
      hsp hI hlowdis hBlt.le hsubrel
    -- the next state
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
    · obtain ⟨q', -, hq'r⟩ := mem_shift.mp h1
      exact hU1 q' r hq'r
    · exact ih' q r h2

/-- **Per-record caps for every traced `fpC` run.** -/
theorem bmsspC_recU (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s)) (hsimp : ∀ u, ((out u).map G.dst).Nodup)
    (hk : 2 ≤ k) (τ : ℕ → ℕ) :
    ∀ l Blow B S d φ res φ' lg, CallPre B S d → DelInv G s φ → (∀ x ∈ S, Blow ≤ dis (s := s) x) →
      Blow ≤ B → BMSSPC G s (fpC G s out k hins hext) DC τ l Blow B S d φ res φ' lg →
      RecU DC k τ lg
  | 0 => by
    intro Blow B S d φ res φ' lg hpre hI hlow hBB hrel
    have hsz := (bmsspC_sizes hout hsort hsimp hk τ 0 Blow B S d φ res φ' lg hpre hI hlow hBB hrel).1
    obtain ⟨st, c, -, -, -, -, -, -, -, rfl⟩ := hrel
    intro q r hqr
    rcases List.mem_singleton.mp hqr with heq
    obtain ⟨-, rfl⟩ := Prod.mk.inj heq
    exact ⟨hsz, by simp⟩
  | l + 1 => by
    intro Blow B S d φ res φ' lg hpre hI hlow hBB hrel
    have hsz := (bmsspC_sizes hout hsort hsimp hk τ (l + 1) Blow B S d φ res φ' lg hpre hI hlow hBB
      hrel).1
    have hsub := bmsspC_log (DC := DC) (fpC_sound (hins := hins) (hext := hext) hout hsort hsimp hk)
      τ l
    obtain ⟨d1, p, P, Q, W, φ1, ω, cfp, piv, σ, lgc, J, cm, cl, L, B'f, T6, W', hfprel, hpiv,
      hloop, hB'e, hB'n, hT6, hW', hL, hres, hlg⟩ := hrel
    have hlow' : ∀ x ∈ S, Blow ≤ d x := fun x hx => (hlow x hx).trans (hpre.walk.sound x)
    obtain ⟨hfp, hI1⟩ := fpC_sound hout hsort hsimp hk _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpre hI hlow'
      hfprel
    have h0 := linv_init hpre hfp hpiv
    have hloopU := loopC_recU (k := k) hpre hfp hsub (bmsspC_recU hout hsort hsimp hk τ l)
      _ _ _ _ _ _ _ _ _ hloop h0 hI1
    subst hlg
    intro q r hqr
    rcases List.mem_cons.mp hqr with heq | h'
    · obtain ⟨-, rfl⟩ := Prod.mk.inj heq
      refine ⟨?_, by simp⟩
      rw [hres] at hsz
      exact hsz
    · exact hloopU q r h'

end RecU

/-! ## The C-HD budgets fit -/

section FitsT

variable {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}

/-- **Every literal top-level run with the C-HD parameters fits the budgets `chdEmax`.** -/
theorem fits_of_top (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s)) (hsimp : ∀ u, ((out u).map G.dst).Nodup)
    {t δ L0 : ℕ} (hk : 2 ≤ k) (h3k : 3 * k ≤ t) (ht : 3 ≤ t)
    (hdeg : ∀ u, (Eout G {u}).card ≤ δ) {DCb : DCost} {Blow : WLab G s}
    (hlow : Blow ≤ initLabels s s) {φ φ' : Finset (Fin G.m)} (hI : DelInv G s φ)
    {res : Result G s} {lgC : Log G s (FPData G s)}
    (hrel : BMSSPC G s (fpC G s out k hins hext) (chdDC t k δ L0 DCb) (chdTau t) L0 Blow ⊤ {s}
      (initLabels s) φ res φ' lgC) :
    Fits (chdEmax t k δ L0) lgC := by
  classical
  have hlow' : ∀ x ∈ ({s} : Finset (Fin G.n)), Blow ≤ dis (s := s) x := by
    intro x hx
    rw [Finset.mem_singleton.mp hx, ← initLabels_source]
    exact hlow
  obtain ⟨-, -, hlog⟩ := bmsspC_log (DC := chdDC t k δ L0 DCb)
    (fpC_sound (hins := hins) (hext := hext) hout hsort hsimp hk) (chdTau t) L0 Blow ⊤ {s}
    (initLabels s) φ res φ' lgC callPre_top hI hlow' le_top hrel
  have hL := hlog.inv
  obtain ⟨R, hR, -, -, -, hRS, -, -⟩ := hlog.root
  have hCS := (bmsspC_sizes hout hsort hsimp hk (chdTau t) L0 Blow ⊤ {s} (initLabels s) φ res φ' lgC
    callPre_top hI hlow' le_top hrel).2
  have hRU := bmsspC_recU hout hsort hsimp hk (chdTau t) L0 Blow ⊤ {s} (initLabels s) φ res φ' lgC
    callPre_top hI hlow' le_top hrel
  -- parameters
  have hM : ∀ l, (chdDC t k δ L0 DCb).M (l + 1) = t * 2 ^ (l * t) := fun l => rfl
  have hτ : ∀ l, chdTau t l = t ^ 3 * 2 ^ (l * t) := fun l => rfl
  have hMpos : ∀ l, 1 ≤ (chdDC t k δ L0 DCb).M l := chdM_pos (by omega)
  -- the frontier bound of every record: `|S| ≤ 3k·M_{lvl+1}`
  have hSb : ∀ q r, (q, r) ∈ lgC → r.S.card ≤ 3 * k * (chdDC t k δ L0 DCb).M (r.lvl + 1) := by
    intro q r hqr
    rcases List.eq_nil_or_concat' q with rfl | ⟨q0, a, rfl⟩
    · have := rec_unique hL.nodup hqr hR
      subst this
      rw [hRS, Finset.card_singleton]
      have := hMpos (r.lvl + 1)
      have : 1 ≤ 3 * k := by omega
      nlinarith
    · obtain ⟨r0, hr0, hS0⟩ := hCS q0 a r hqr
      have d1 := hL.depth _ _ hqr
      have d2 := hL.depth _ _ hr0
      simp only [List.length_append, List.length_singleton] at d1
      have e : r0.lvl = r.lvl + 1 := by omega
      rw [e] at hS0
      exact hS0
  -- the returned-set bound of every record: `|U| ≤ 2τ_lvl`
  have hU2 : ∀ q r, (q, r) ∈ lgC → r.U.card ≤ 2 * chdTau t r.lvl := fun q r hqr =>
    ((hRU q r hqr).1.trans (ucap_mono _ (hSb q r hqr))).trans (ucap_le hM hτ h3k ht r.lvl)
  -- `|S| ≤ |U|` on every record
  have hSτ : ∀ l, 3 * k * (chdDC t k δ L0 DCb).M (l + 1) ≤ chdTau t l := by
    intro l
    rw [hM, hτ]
    have h1a : 3 * k * t ≤ t * t := Nat.mul_le_mul_right t h3k
    have h1b : t * t ≤ t ^ 3 := by
      calc t * t = t * t * 1 := by ring
        _ ≤ t * t * t := Nat.mul_le_mul_left _ (by omega)
        _ = t ^ 3 := by ring
    have h1 : 3 * k * t ≤ t ^ 3 := h1a.trans h1b
    calc 3 * k * (t * 2 ^ (l * t)) = 3 * k * t * 2 ^ (l * t) := by ring
      _ ≤ t ^ 3 * 2 ^ (l * t) := Nat.mul_le_mul_right _ h1
  have hSU : ∀ q r, (q, r) ∈ lgC → r.S.card ≤ r.U.card := by
    intro q r hqr
    have hf := hL.facts q r hqr
    rcases lt_or_eq_of_le hf.B'_le with hlt | heq
    · have hτU := hf.partial_card hlt
      have h1 := hSb q r hqr
      have h2 := hSτ r.lvl
      omega
    · exact Finset.card_le_card (hf.full_S heq)
  intro x rx hx
  by_cases hb : rx.base = true
  · -- a base record: its subtree is itself
    have hl0 : rx.lvl = 0 := ((hRU x rx hx).2).mp hb
    rw [ownSum_sub_base hL hx hb, ownB_of_base rx hb, hl0]
    have hS0 := hSb x rx hx
    rw [hl0] at hS0
    have hS0' : rx.S.card ≤ 3 * k * t := by
      have e : (chdDC t k δ L0 DCb).M (0 + 1) = t := by
        show t * 2 ^ (0 * t) = t
        simp
      rw [e] at hS0
      exact hS0
    have hU0 : rx.U.card ≤ t ^ 3 := by
      have := (hRU x rx hx).1
      rw [hl0] at this
      have e : ucap (chdDC t k δ L0 DCb) k (chdTau t) 0 rx.S.card = t ^ 3 := by
        simp [ucap, chdTau]
      rw [e] at this
      exact this
    have hE := Eout_card_le (G := G) hdeg rx.U
    have hE' : (Finset.univ.filter fun e => G.src e ∈ rx.U).card ≤ δ * rx.U.card := hE
    have hδ : δ * rx.U.card ≤ δ * t ^ 3 := Nat.mul_le_mul_left δ hU0
    show rx.S.card + (Finset.univ.filter fun e => G.src e ∈ rx.U).card ≤ 3 * k * t + δ * t ^ 3
    omega
  · -- a recursive record: agent-03's (B4′) at `x`
    have hl : rx.lvl ≠ 0 := fun h0 => hb (((hRU x rx hx).2).mpr h0)
    obtain ⟨l', hl'⟩ := Nat.exists_eq_succ_of_ne_zero hl
    have h1 := ownSum_sub_le hL δ hdeg hSU hx
    have h2 := hU2 x rx hx
    rw [hl'] at h2 ⊢
    show Log.ownSum (subLog lgC x) ≤ (3 * (L0 + 1) + 3 * δ) * (2 * chdTau t (l' + 1))
    calc _ ≤ (3 * (L0 + 1) + 3 * δ) * rx.U.card := h1
      _ ≤ _ := Nat.mul_le_mul_left _ h2

/-- **The top-level run over agent-04's DLazy with the C-HD parameters costs at most its literal
twin with the amortized parameters `chdDC`** (no hypothesis beyond the parameters). -/
theorem chdDL_tele_top (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s)) (hsimp : ∀ u, ((out u).map G.dst).Nodup)
    {t δ : ℕ} (hk : 2 ≤ k) (h3k : 3 * k ≤ t) (ht : 3 ≤ t)
    (hdeg : ∀ u, (Eout G {u}).card ≤ δ) {DCb : DCost} {T : ℕ → ℕ} (L0 : ℕ) {Blow : WLab G s}
    (hlow : Blow ≤ initLabels s s) {φ φ' : Finset (Fin G.m)} (hI : DelInv G s φ)
    {res : ResultD G s} {gE : DGl G s} {lg : Log G s (FPData G s)}
    (hrel : BMSSPD G s (dlOps G s) (fpC G s out k hins hext) DCb T (chdM t) (chdTau t) L0 Blow ⊤
      {s} (initLabels s) φ DGl.init res φ' gE lg) :
    ∃ lgC, BMSSPC G s (fpC G s out k hins hext) (chdDC t k δ L0 DCb) (chdTau t) L0 Blow ⊤ {s}
        (initLabels s) φ (res.lit gE) φ' lgC ∧
      Log.strip lgC = Log.strip lg ∧ lg.cost ≤ lgC.cost :=
  bmsspDL_tele_top' (T := T) (fpC_sound (hins := hins) (hext := hext) hout hsort hsimp hk)
    (chdTau t) (Emax := chdEmax t k δ L0) (chdM_pos (by omega)) (chdM_three ht)
    (DC := chdDC t k δ L0 DCb) (DCb := DCb) (fun _ => rfl) (chdDC_ins (by omega))
    (fun _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) le_rfl le_rfl
    L0 hlow hI hrel (fun lgC hC => fits_of_top hout hsort hsimp hk h3k ht hdeg hlow hI hC)

end FitsT

end BM
end CHD
end Frontier
