import Frontier.CHD.CostLe
import Frontier.CHD.QWitValid
import Frontier.CHD.QWitProv
import Frontier.CHD.MergeTotal
import Frontier.CHD.TraceFits
import Frontier.CHD.SizeFacts
import Frontier.CostFinal

/-!
# Frontier.CHD.MasterCost — the Layer-A MASTER COST theorem of the C-HD run (agent-06, COORD G2-8 (b); NON-GATE)

For the traced C-HD run (FindPivots `fpC … k`, amortized DLazy parameters `chdDC t k δ L0 DCb`, caps `chdTau t`,
top level `L0`) with the parameters `t = tF n m`, `k = kF n m`, `L0 = LF n m`, the total cost index is
`≤ 5100 · c · a · Tchd n m` (`CostFinal.total_le_Tchd`, with `Valid` for agent-03's `tracedCounters`).

* Part 1: every BASE record costs `≤ |S|(1+bins) + |U|(1+bext) + |Eout U|(1+bins) + 2` (`bmsspC_basecost`; each
  base-loop step extracts a new vertex, `BInv.keysU`), via the generic loop transfer `loopC_allP`.
* Part 2: parameter facts: `k(k+1) ≤ 2t`, `τ(LF) > 2n`, `lgN ≤ 16 t⁶` and the recursive insertion charge
  `211 log₂(8ρ+8) + 441 ≤ 3826 t` on the dispatch branch `dd ≤ F + 1` (`mc_ins_le`), the base conversion charge
  `chdIns … 0 ≤ 1300 (log₂(t+1) + log₂(dd+1) + 2)` (`mc_ins0_le`).
* Part 3: `valid_traced` — `Valid (tF) (kF) (cValid) (LF) (14 (LF+1)|V|) (inEdges G) wit s` for agent-03's
  `tracedCounters` (all fields from bmsspC_log/recall/reccost/sizes/merge/S_ne/chain/qwit + CostLe/QWitValid/
  MergeTotal transfers; `partial_S` from the root `S = {s}` and ChildS `|S| ≤ 3k M`).
* Part 4: `master_cost_C` — literal run: `lg.cost ≤ 5100 · cMaster · 56 · Tchd n m`.
* Part 5: `master_cost_D` — the concrete DLazy run (what the RAM core refines), via `chdDL_tele_top`.

Hypotheses beyond the run: `|V| ≤ 2n`, `1 ≤ |E| ≤ 2m` (**`0 < G.m` is needed: `Valid.wit` needs an edge
type**), out-degree `≤ δ ≤ 5 dd`, `dd ≤ F n + 1` (CoreIn.dens), `1 ≤ n`, `1 ≤ m`, `n ≤ m + 1`, and the base heap
cost `DCb.bins, DCb.bext ≤ cb (log₂(t+1) + log₂(dd+1) + 2)`.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-! ## Part 1: base records -/

section BaseCost

variable {DC : DCost} {B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s}

/-- The base loop's cost: one extraction per new vertex of `U`, one relaxation per out-edge of it. -/
theorem baseLoopC_cost_le (hpre : CallPre B S d0) {τ : ℕ} :
    ∀ {st st' : Labels G s × DS G s × Finset (Fin G.n)} {c : ℕ}, BaseLoopC G s DC B τ st st' c →
      BInv G s B S d0 st.1 st.2.1 st.2.2 →
      c + st.2.2.card * (1 + DC.bext) + (Eout G st.2.2).card * (1 + DC.bins) ≤
        st'.2.2.card * (1 + DC.bext) + (Eout G st'.2.2).card * (1 + DC.bins) + 1 := by
  intro st st' c h
  induction h with
  | stop st _ => intro _; omega
  | step d D U u val L st' c hu hmin hcard hL _ ih =>
    intro hB
    have hB' := bInv_step hpre hB hu hmin hL
    have huU : u ∉ U := hB.keysU u val hu
    have ih' := ih hB'
    have hEu : (Eout G {u}).card = L.length := by
      rw [← List.toFinset_card_of_nodup hL.1]
      congr 1
      ext e
      simp only [Eout, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset, hL.2 e]
    have hdisj : Disjoint (Eout G U) (Eout G {u}) := by
      rw [Finset.disjoint_left]
      intro e he he'
      simp only [Eout, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at he he'
      exact huU (he' ▸ he)
    have hEins : Eout G (insert u U) = Eout G U ∪ Eout G {u} := by
      ext e
      simp only [Eout, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_union,
        Finset.mem_singleton]
      tauto
    have hE : (Eout G (insert u U)).card = (Eout G U).card + L.length := by
      rw [hEins, Finset.card_union_of_disjoint hdisj, hEu]
    simp only at ih' ⊢
    rw [Finset.card_insert_of_notMem huU, hE] at ih'
    nlinarith [ih']

/-- A record property of every record of every sub-call log. -/
def SubP (P : CallRec G s (FPData G s) → Prop) (sub : SubRelC G s (Finset (Fin G.m)) (FPData G s)) : Prop :=
  ∀ Blow B S d φ res φ' lg, CallPre B S d → DelInv G s φ → (∀ x ∈ S, Blow ≤ dis (s := s) x) → Blow ≤ B →
    sub Blow B S d φ res φ' lg → ∀ q r, (q, r) ∈ lg → P r

end BaseCost

section LoopAllP

variable {DC : DCost}
variable {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {p : ℕ}
  {P0 : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {B'0 : WLab G s}

/-- **The loop log's records are sub-call records** (generic form of agent-03's `loopC_recall`). -/
theorem loopC_allP {P : CallRec G s (FPData G s) → Prop} (hpre : CallPre B S d0)
    (hfp : FPContract B S d0 d1 p P0 Q W)
    {τ : ℕ → ℕ} {sub : SubRelC G s (Finset (Fin G.m)) (FPData G s)} {l : ℕ}
    (hsub : GoodSub G s τ (DelInv G s) l sub) (hsubp : SubP P sub) {τl : ℕ} :
    ∀ i (σ : LState G s p) φ σ' φ' lg J cm c,
      LoopC G s DC sub (l + 1) B τl i σ φ σ' φ' lg J cm c →
      LInv G s B S d0 d1 P0 B'0 σ → DelInv G s φ → ∀ q r, (q, r) ∈ lg → P r := by
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
    have hra := hsubp σ.B' Bi (expand σ S0 Bi) σ.d φ (B'i, Ui, Di, dsub) φ1 lg hsp hI hlowdis hBlt.le hsubrel
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

end LoopAllP

section BaseAll

variable {DC : DCost} {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}

/-- The base-record cost bound. -/
def BaseCostOK (DC : DCost) (r : CallRec G s (FPData G s)) : Prop :=
  r.base = true → r.cost ≤ r.S.card * (1 + DC.bins) + r.U.card * (1 + DC.bext) + (Eout G r.U).card * (1 + DC.bins) + 2

/-- **Every base record of every `BMSSPC` derivation costs at most
`|S|(1+bins) + |U|(1+bext) + |Eout U|(1+bins) + 2`** (all levels). -/
theorem bmsspC_basecost (hout : ∀ u e, e ∈ out u ↔ G.src e = u) (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hsimp : ∀ u, ((out u).map G.dst).Nodup) (hk : 2 ≤ k) (τ : ℕ → ℕ) :
    ∀ l, SubP (BaseCostOK DC) (BMSSPC G s (fpC G s out k hins hext) DC τ l)
  | 0 => by
    intro Blow B S d φ res φ' lg hpre _ _ _ hrel
    obtain ⟨st, c, hloop, hU, -, -, -, -, -, rfl⟩ := hrel
    intro q r hqr hb
    rcases List.mem_singleton.mp hqr with heq
    obtain ⟨-, rfl⟩ := Prod.mk.inj heq
    have key := baseLoopC_cost_le hpre hloop (bInv_init hpre)
    simp only [Finset.card_empty, zero_mul, add_zero] at key
    have hE0 : (Eout G (∅ : Finset (Fin G.n))).card = 0 := by simp [Eout]
    rw [hE0, zero_mul, add_zero] at key
    show S.card * (1 + DC.bins) + c + 1 ≤ S.card * (1 + DC.bins) + res.2.1.card * (1 + DC.bext) +
      (Eout G res.2.1).card * (1 + DC.bins) + 2
    rw [hU]
    omega
  | l + 1 => by
    intro Blow B S d φ res φ' lg hpre hI hlow hBB hrel
    have hsub := bmsspC_log (DC := DC) (fpC_sound (hins := hins) (hext := hext) hout hsort hsimp hk) τ l
    have hsubp := bmsspC_basecost hout hsort hsimp hk τ l
    obtain ⟨d1, p, P, Q, W, φ1, ω, cfp, piv, σ, lgc, J, cm, cl, L, B'f, T6, W', hfprel, hpiv,
      hloop, hB'e, hB'n, hT6, hW', hL, hres, rfl⟩ := hrel
    have hlow' : ∀ x ∈ S, Blow ≤ d x := fun x hx => (hlow x hx).trans (hpre.walk.sound x)
    obtain ⟨hfp, hI1⟩ := fpC_sound hout hsort hsimp hk _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpre hI hlow' hfprel
    have h0 := linv_init hpre hfp hpiv
    have hloopall := loopC_allP (DC := DC) hpre hfp hsub hsubp _ _ _ _ _ _ _ _ _ hloop h0 hI1
    intro q r hqr
    rcases List.mem_cons.mp hqr with heq | hmem
    · obtain ⟨-, rfl⟩ := Prod.mk.inj heq
      intro hb
      exact absurd hb (by simp)
    · exact hloopall q r hmem

end BaseAll

/-! ## Part 2: parameter facts -/

section Params

open Frontier.CostSkeleton

theorem mc_kk (n m : ℕ) : kF n m * (kF n m + 1) ≤ 2 * tF n m := by
  have h1 := kF_le_sqrt_succ n m
  have h4 := four_le_sqrt_tF n m
  have hs : Nat.sqrt (tF n m) * Nat.sqrt (tF n m) ≤ tF n m := Nat.sqrt_le _
  have h2 : kF n m * (kF n m + 1) ≤ (Nat.sqrt (tF n m) + 1) * (Nat.sqrt (tF n m) + 2) :=
    Nat.mul_le_mul h1 (by omega)
  nlinarith

theorem mc_LF_pos (n m : ℕ) : 1 ≤ LF n m := by unfold LF; exact Nat.le_add_left 1 _

theorem mc_lgN_lt (n m : ℕ) : lgN n + 1 ≤ LF n m * tF n m := by
  unfold LF
  have e1 := Nat.div_add_mod (lgN n) (tF n m)
  have e2 := Nat.mod_lt (lgN n) (show 0 < tF n m by have := sixteen_le_tF n m; omega)
  rw [Nat.add_mul, one_mul]
  nlinarith

/-- The top cap exceeds `2n` (so `τ(LF) > |V(H)|` for `|V(H)| ≤ 2n`). -/
theorem mc_tau_top (n m : ℕ) : 2 * n < chdTau (tF n m) (LF n m) := by
  have ht : 16 ≤ tF n m := sixteen_le_tF n m
  have hLt := mc_lgN_lt n m
  have hn2 : n < 2 ^ (lgN n + 1) := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
    have hle : Nat.log 2 n ≤ lgN n := le_max_right _ _
    exact lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h2 : 2 ^ (lgN n + 1) ≤ 2 ^ (LF n m * tF n m) := Nat.pow_le_pow_right (by norm_num) hLt
  have ht3 : 2 ≤ tF n m ^ 3 := by
    have : 16 ^ 3 ≤ tF n m ^ 3 := Nat.pow_le_pow_left ht 3
    omega
  unfold chdTau
  calc 2 * n < 2 * 2 ^ (LF n m * tF n m) := by omega
    _ ≤ tF n m ^ 3 * 2 ^ (LF n m * tF n m) := Nat.mul_le_mul_right _ ht3

/-- `F n ≤ lgN n`. -/
theorem mc_F_le (n : ℕ) : Frontier.GateCCalc.F n ≤ lgN n := by
  have h4 := F_pow_four_le n
  have hle : Nat.log 2 n ≤ lgN n := le_max_right _ _
  have hl1 : 1 ≤ lgN n := one_le_lgN n
  have h3 : Frontier.GateCCalc.F n ^ 4 ≤ lgN n ^ 4 := by
    calc Frontier.GateCCalc.F n ^ 4 ≤ Nat.log 2 n ^ 3 := h4
      _ ≤ lgN n ^ 3 := Nat.pow_le_pow_left hle 3
      _ ≤ lgN n ^ 4 := Nat.pow_le_pow_right hl1 (by norm_num)
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h3

/-- On the dispatch branch `lgN n ≤ 16 t⁶`. -/
theorem mc_lgN_le (n m : ℕ) (hdd : dd n m ≤ Frontier.GateCCalc.F n + 1) : lgN n ≤ 16 * tF n m ^ 6 := by
  set f := Frontier.GateCCalc.F n with hf
  set A := tpar n m with hA
  have hspec := (tpar_spec n m).2
  have h1 : lgN n ^ 2 ≤ A ^ 3 * (f + 1) ^ 2 :=
    le_trans hspec (Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left hdd 2))
  have hl1 : 1 ≤ lgN n := one_le_lgN n
  have hlog_le : Nat.log 2 n ≤ lgN n := le_max_right _ _
  have hf4 : f ^ 4 ≤ lgN n ^ 3 := le_trans (F_pow_four_le n) (Nat.pow_le_pow_left hlog_le 3)
  have hf1 : (f + 1) ^ 4 ≤ 16 * lgN n ^ 3 := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0]; have : 1 ≤ lgN n ^ 3 := Nat.one_le_pow _ _ hl1; omega
    · have : f + 1 ≤ 2 * f := by omega
      calc (f + 1) ^ 4 ≤ (2 * f) ^ 4 := Nat.pow_le_pow_left this 4
        _ = 16 * f ^ 4 := by ring
        _ ≤ 16 * lgN n ^ 3 := by omega
  have h2 : lgN n ^ 4 ≤ A ^ 6 * (f + 1) ^ 4 := by
    have := Nat.pow_le_pow_left h1 2
    calc lgN n ^ 4 = (lgN n ^ 2) ^ 2 := by ring
      _ ≤ (A ^ 3 * (f + 1) ^ 2) ^ 2 := this
      _ = A ^ 6 * (f + 1) ^ 4 := by ring
  have h3 : lgN n ^ 4 ≤ A ^ 6 * (16 * lgN n ^ 3) := le_trans h2 (Nat.mul_le_mul le_rfl hf1)
  have h4 : lgN n ≤ 16 * A ^ 6 := by
    have hpos : 0 < lgN n ^ 3 := by positivity
    have : lgN n * lgN n ^ 3 ≤ (16 * A ^ 6) * lgN n ^ 3 := by
      calc lgN n * lgN n ^ 3 = lgN n ^ 4 := by ring
        _ ≤ A ^ 6 * (16 * lgN n ^ 3) := h3
        _ = (16 * A ^ 6) * lgN n ^ 3 := by ring
    exact Nat.le_of_mul_le_mul_right this hpos
  exact h4.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (tpar_le_tF n m) 6))

/-- **The recursive-level insertion charge is `O(t)` on the dispatch branch** (checklist I7/I13):
`211 log₂(8ρ + 8) + 441 ≤ 3826 t` for `ρ = chdRho t δ L0`, `δ ≤ 5 dd`, `dd ≤ F + 1`. -/
theorem mc_ins_le (n m δ : ℕ) (hδ : δ ≤ 5 * dd n m) (hdd : dd n m ≤ Frontier.GateCCalc.F n + 1) :
    211 * Nat.log 2 (8 * chdRho (tF n m) δ (LF n m) + 8) + 441 ≤ 3826 * tF n m := by
  have ht : 16 ≤ tF n m := sixteen_le_tF n m
  have hlg := mc_lgN_le n m hdd
  have hF := mc_F_le n
  have hLF : LF n m ≤ lgN n + 1 := by unfold LF; have := Nat.div_le_self (lgN n) (tF n m); omega
  have hl1 : 1 ≤ lgN n := one_le_lgN n
  have hA : 3 * (LF n m + 1) + 3 * δ ≤ 864 * tF n m ^ 6 := by
    have : 3 * (LF n m + 1) + 3 * δ ≤ 54 * lgN n := by
      have : δ ≤ 5 * (Frontier.GateCCalc.F n + 1) := le_trans hδ (by omega)
      omega
    omega
  have hrho : chdRho (tF n m) δ (LF n m) ≤ 864 * tF n m ^ 6 * (2 * tF n m ^ 2 * 2 ^ tF n m) := by
    unfold chdRho; exact Nat.mul_le_mul_right _ hA
  have ht2 : tF n m < 2 ^ tF n m := Nat.lt_two_pow_self
  have hP : 8 ≤ tF n m ^ 8 * 2 ^ tF n m := by
    have h8 : 2 ^ 3 ≤ 2 ^ tF n m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : 1 ≤ tF n m ^ 8 := Nat.one_le_pow _ _ (by omega)
    have := Nat.mul_le_mul h1 h8
    simpa using this
  have e1 : 8 * chdRho (tF n m) δ (LF n m) + 8 ≤ 13825 * (tF n m ^ 8 * 2 ^ tF n m) := by
    have : 864 * tF n m ^ 6 * (2 * tF n m ^ 2 * 2 ^ tF n m) = 1728 * (tF n m ^ 8 * 2 ^ tF n m) := by ring
    rw [this] at hrho
    omega
  have e2 : tF n m ^ 8 < 2 ^ (8 * tF n m) := by
    have := Nat.pow_lt_pow_left ht2 (show (8 : ℕ) ≠ 0 by norm_num)
    rwa [← pow_mul, mul_comm] at this
  have e4 : tF n m ^ 8 * 2 ^ tF n m < 2 ^ (8 * tF n m) * 2 ^ tF n m :=
    Nat.mul_lt_mul_of_pos_right e2 (by positivity)
  have e6 : 2 ^ (8 * tF n m) * 2 ^ tF n m = 2 ^ (9 * tF n m) := by
    rw [← pow_add]; congr 1; ring
  rw [e6] at e4
  have e7 : 13825 * (tF n m ^ 8 * 2 ^ tF n m) < 2 ^ 14 * 2 ^ (9 * tF n m) := by
    have h14 : (13825 : ℕ) < 2 ^ 14 := by norm_num
    calc 13825 * (tF n m ^ 8 * 2 ^ tF n m) ≤ 13825 * 2 ^ (9 * tF n m) := Nat.mul_le_mul_left _ e4.le
      _ < 2 ^ 14 * 2 ^ (9 * tF n m) := Nat.mul_lt_mul_of_pos_right h14 (by positivity)
  have e8 : 2 ^ 14 * 2 ^ (9 * tF n m) ≤ 2 ^ (18 * tF n m) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlog : Nat.log 2 (8 * chdRho (tF n m) δ (LF n m) + 8) < 18 * tF n m :=
    Nat.log_lt_of_lt_pow (by omega) (by omega)
  omega

/-- **The base-level conversion charge is `O(log t + log dd)`**: `chdIns t k δ L0 0 ≤ 1300 (log₂(t+1) + log₂(dd+1) + 2)`. -/
theorem mc_ins0_le (n m δ : ℕ) (hδ : δ ≤ 5 * dd n m) :
    chdIns (tF n m) (kF n m) δ (LF n m) 0 ≤
      1300 * (Nat.log 2 (tF n m + 1) + Nat.log 2 (dd n m + 1) + 2) := by
  have h0 := chdIns_zero_le (t := tF n m) (k := kF n m) (δ := δ) (L0 := LF n m)
  have hh := heap_log_le n m δ hδ
  have hX : 8 * (3 * kF n m * tF n m + δ * tF n m ^ 3) + 8 ≤
      8 * (tF n m * (3 * kF n m + 1) + δ * tF n m ^ 3 + 3) := by
    have : 3 * kF n m * tF n m ≤ tF n m * (3 * kF n m + 1) := by nlinarith
    omega
  have hlog8 : Nat.log 2 (8 * (tF n m * (3 * kF n m + 1) + δ * tF n m ^ 3 + 3)) ≤
      Nat.log 2 (tF n m * (3 * kF n m + 1) + δ * tF n m ^ 3 + 3) + 3 := by
    set X := tF n m * (3 * kF n m + 1) + δ * tF n m ^ 3 + 3 with hXd
    have hx := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) X
    have h8 : 8 * X < 2 ^ (Nat.log 2 X + 4) := by
      rw [pow_add]; norm_num; omega
    have := Nat.log_lt_of_lt_pow (by omega) h8
    omega
  have hmono := Nat.log_mono_right (b := 2) hX
  omega

end Params

/-! ## Part 3: `Valid` for the traced counters of the C-HD run -/

section ValidTraced

open Frontier.CostSkeleton

variable {out : Fin G.n → List (Fin G.m)} {hins hext : ℕ}

/-- The per-call constant of `Valid.cost_le` for the C-HD run (`a` bounds the FindPivots constant:
`fpA k hins hext ≤ a (k+1)`). -/
def cValid (a : ℕ) : ℕ :=
  scanC + 5 * a + 1 + 5 * 952 + (735 + 5 + 4) + 7 * 3826 + 5 + 1 + 30

/-- The FindPivots constant for bounded `hins ≤ ch` and `hext ≤ ce (k+1)` (e.g. an unsorted-array heap of
size `≤ k`): `fpA k hins hext ≤ (2 (scanC + ch) + ce + 2)(k + 1)`. -/
theorem fpA_le_of {k hins hext ch ce : ℕ} (hh : hins ≤ ch) (he : hext ≤ ce * (k + 1)) :
    fpA k hins hext ≤ (2 * (scanC + ch) + ce + 2) * (k + 1) := by
  unfold fpA
  have h1 : (scanC + hins) * (1 + k) ≤ (scanC + ch) * (k + 1) := by
    rw [Nat.add_comm 1 k]; exact Nat.mul_le_mul_right _ (by omega)
  nlinarith

/-- **`CostAggregate.Valid` for agent-03's `tracedCounters` of the literal C-HD run** with the parameters
`t = tF n m`, `k = kF n m`, `L0 = LF n m`, `M0 = 14 (L0+1) |V|`, on the dispatch branch (`dd ≤ F + 1`,
out-degree `δ ≤ 5 dd`), for a graph with at least one edge. -/
theorem valid_traced (hout : ∀ u e, e ∈ out u ↔ G.src e = u) (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hsimp : ∀ u, ((out u).map G.dst).Nodup) {n m δ : ℕ} (hδ : δ ≤ 5 * dd n m)
    (hdd : dd n m ≤ Frontier.GateCCalc.F n + 1) (e0 : Fin G.m) {a : ℕ}
    (ha : fpA (kF n m) hins hext ≤ a * (kF n m + 1))
    {DCb : DCost} {Blow : WLab G s} (hlow : Blow ≤ initLabels s s) {φ φ' : Finset (Fin G.m)}
    (hI : DelInv G s φ) {res : Result G s} {lg : Log G s (FPData G s)}
    (hrel : BMSSPC G s (fpC G s out (kF n m) hins hext) (chdDC (tF n m) (kF n m) δ (LF n m) DCb)
      (chdTau (tF n m)) (LF n m) Blow ⊤ {s} (initLabels s) φ res φ' lg) :
    ∃ (hL : LogInv (chdTau (tF n m)) (LF n m) lg) (wit : lg.Call → Fin G.n → Fin G.m),
      (tracedCounters hL).Valid (tF n m) (kF n m) (cValid a) (LF n m)
        (14 * ((LF n m + 1) * G.n)) (inEdges G) wit s := by
  have ht16 : 16 ≤ tF n m := sixteen_le_tF n m
  have hk2 : 2 ≤ kF n m := two_le_kF n m
  have hkt : kF n m ≤ tF n m := kF_le_tF n m
  have h3k : 3 * kF n m ≤ tF n m := three_kF_le_tF n m
  have hFPC := fpC_sound (hins := hins) (hext := hext) hout hsort hsimp hk2
  have hlow' : ∀ x ∈ ({s} : Finset (Fin G.n)), Blow ≤ dis (s := s) x := by
    intro x hx
    rw [Finset.mem_singleton.mp hx, ← initLabels_source]
    exact hlow
  -- the log invariant and the root record
  have hlog := (bmsspC_log (DC := chdDC (tF n m) (kF n m) δ (LF n m) DCb) hFPC (chdTau (tF n m)) (LF n m)
    Blow ⊤ {s} (initLabels s) φ res φ' lg callPre_top hI hlow' le_top hrel).2.2
  have hL : LogInv (chdTau (tF n m)) (LF n m) lg := hlog.inv
  obtain ⟨r0, hr0, hr0l, -, -, hr0S, -, -⟩ := hlog.root
  -- Q-witnesses
  obtain ⟨-, wit, hw1, hw2, hw3⟩ := bmsspC_qwit hFPC (chdTau (tF n m)) callPre_top hI hlow' le_top
    (le_of_eq initLabels_source) (Finset.Subset.refl _) hrel e0
  refine ⟨hL, wit, ?_⟩
  -- record facts
  have hRA : ∀ q r, (q, r) ∈ lg → RecAll out (kF n m) hins hext r :=
    bmsspC_recall (DC := chdDC (tF n m) (kF n m) δ (LF n m) DCb) hout hsort hsimp hk2 (chdTau (tF n m)) (LF n m)
      Blow ⊤ {s} (initLabels s) φ res φ' lg callPre_top hI hlow' le_top hrel
  have hrec : ∀ q r, (q, r) ∈ lg → RecFP out (kF n m) hins hext r := fun q r h => (hRA q r h).1
  have hF : ∀ q r, (q, r) ∈ lg → RecForest r := fun q r h => (hRA q r h).2.1
  have hnd : ∀ q r, (q, r) ∈ lg → ∀ ω, r.fp = some ω → (ω.trees.flatMap (fun T => T.ord)).Nodup :=
    fun q r h => (hRA q r h).2.2.1
  have hS : ∀ q r, (q, r) ∈ lg → r.S.Nonempty :=
    bmsspC_S_ne (chdTau (tF n m)) (LF n m) Blow ⊤ {s} (initLabels s) φ res φ' lg hrel
      (Finset.singleton_nonempty s)
  have hτ : ∀ l, 1 ≤ chdTau (tF n m) l := fun l => by
    unfold chdTau
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hne : ∀ q r, (q, r) ∈ lg → r.U.Nonempty := U_ne_of_S_ne hL hτ hS
  have hOK : MergeOK 14 lg := (bmsspC_merge (DC := chdDC (tF n m) (kF n m) δ (LF n m) DCb)
    (FPC := fpC G s out (kF n m) hins hext) (cmax := 14) (fun _ _ => le_rfl) (chdTau (tF n m)) (LF n m)
    Blow ⊤ {s} (initLabels s) φ res φ' lg hrel).1
  have hsz := (bmsspC_sizes (DC := chdDC (tF n m) (kF n m) δ (LF n m) DCb) hout hsort hsimp hk2
    (chdTau (tF n m)) (LF n m) Blow ⊤ {s} (initLabels s) φ res φ' lg callPre_top hI hlow' le_top hrel).2
  have hchain := bmsspC_chain (DC := chdDC (tF n m) (kF n m) δ (LF n m) DCb)
    (fpC_chain_hyp (k := kF n m) (hins := hins) (hext := hext) hout hsort) (chdTau (tF n m)) (LF n m)
    Blow ⊤ {s} (initLabels s) φ res φ' lg hrel
  have hMτ : ∀ l, (chdDC (tF n m) (kF n m) δ (LF n m) DCb).M (l + 1) ≤ chdTau (tF n m) l := by
    intro l
    show tF n m * 2 ^ (l * tF n m) ≤ tF n m ^ 3 * 2 ^ (l * tF n m)
    exact Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) _)
  have hgMτ : ∀ l, 3 * kF n m * (chdDC (tF n m) (kF n m) δ (LF n m) DCb).M (l + 1) ≤ chdTau (tF n m) l := by
    intro l
    show 3 * kF n m * (tF n m * 2 ^ (l * tF n m)) ≤ tF n m ^ 3 * 2 ^ (l * tF n m)
    have e : 3 * kF n m * (tF n m * 2 ^ (l * tF n m)) = (3 * kF n m * tF n m) * 2 ^ (l * tF n m) := by ring
    rw [e]
    refine Nat.mul_le_mul_right _ ?_
    have : 3 * kF n m * tF n m ≤ tF n m * tF n m := Nat.mul_le_mul_right _ h3k
    have : tF n m * tF n m ≤ tF n m ^ 3 := by
      have : tF n m ^ 3 = tF n m * tF n m * tF n m := by ring
      rw [this]; exact Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hRC := bmsspC_reccost (DC := chdDC (tF n m) (kF n m) δ (LF n m) DCb) (hins := hins) (hext := hext)
    hout hsort hsimp hk2 (chdTau (tF n m))
    (ap := 735) (bp := 950) (ad := 5) (bd := 1)
    (I := 211 * Nat.log 2 (8 * chdRho (tF n m) δ (LF n m) + 8) + 441) (nw := 3)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun l => chdIns_le (by omega) l) (fun _ => le_rfl) hMτ hgMτ
    (LF n m) Blow ⊤ {s} (initLabels s) φ res φ' lg callPre_top hI hlow' le_top hrel
  -- `partial_S`: `t |S| ≤ τ(lvl) ≤ |U|`
  have hpS : ∀ X, (tracedCounters hL).full X = false →
      tF n m * ((tracedCounters hL).S X).card ≤ ((tracedCounters hL).F.U X).card := by
    intro X hX
    have hU := countersC_partial_card hL (fun X => foOf (lg.recOf X)) (crOf hL) (beOf hL)
      (fun X => delOf (fun ω : FPData G s => ω.Din) (fun ω => ω.Dout) (lg.recOf X)) X hX
    refine le_trans ?_ hU
    show tF n m * (lg.recOf X).S.card ≤ chdTau (tF n m) (lg.recOf X).lvl
    have hmem := recOf_mem X
    by_cases h0 : X.1 = []
    · have hX0 : lg.recOf X = r0 := recOf_eq hL.nodup (by rw [h0]; exact hr0)
      rw [hX0, hr0S, hr0l, Finset.card_singleton, mul_one]
      unfold chdTau
      have : tF n m ≤ tF n m ^ 3 := Nat.le_self_pow (by norm_num) _
      have : 1 ≤ 2 ^ (LF n m * tF n m) := Nat.one_le_two_pow
      nlinarith
    · obtain ⟨q, a, hq⟩ := exists_concat_of_ne_nil h0
      have hmem' : (q ++ [a], lg.recOf X) ∈ lg := hq ▸ hmem
      obtain ⟨r1, hr1, hSle⟩ := hsz q a (lg.recOf X) hmem'
      have hd1 := hL.depth _ _ hr1
      have hd2 := hL.depth _ _ hmem'
      simp only [List.length_append, List.length_singleton] at hd2
      have hlv : r1.lvl = (lg.recOf X).lvl + 1 := by omega
      rw [hlv] at hSle
      have hM : (chdDC (tF n m) (kF n m) δ (LF n m) DCb).M ((lg.recOf X).lvl + 1) =
          tF n m * 2 ^ ((lg.recOf X).lvl * tF n m) := rfl
      rw [hM] at hSle
      unfold chdTau
      have e : tF n m * (3 * kF n m * (tF n m * 2 ^ ((lg.recOf X).lvl * tF n m))) =
          (3 * kF n m) * (tF n m * tF n m * 2 ^ ((lg.recOf X).lvl * tF n m)) := by ring
      have e2 : tF n m ^ 3 * 2 ^ ((lg.recOf X).lvl * tF n m) =
          tF n m * (tF n m * tF n m * 2 ^ ((lg.recOf X).lvl * tF n m)) := by ring
      calc tF n m * (lg.recOf X).S.card ≤ tF n m * (3 * kF n m * (tF n m * 2 ^ ((lg.recOf X).lvl * tF n m))) :=
            Nat.mul_le_mul_left _ hSle
        _ = (3 * kF n m) * (tF n m * tF n m * 2 ^ ((lg.recOf X).lvl * tF n m)) := e
        _ ≤ tF n m * (tF n m * tF n m * 2 ^ ((lg.recOf X).lvl * tF n m)) := Nat.mul_le_mul_right _ h3k
        _ = tF n m ^ 3 * 2 ^ ((lg.recOf X).lvl * tF n m) := e2.symm
  -- the per-call inequality
  have hcost := tracedCounters_cost_le hL hout hsort hsimp hk2 (C0 := 1 + 950 + 1) (C1 := 735 + 5 + 4)
    (I := 211 * Nat.log 2 (8 * chdRho (tF n m) δ (LF n m) + 8) + 441) (ad := 5) (bd := 1) (nw := 3)
    (a := a) (cI := 3826) (cn := 1) (c9 := 952) (t := tF n m)
    (c := cValid a) hRC hRA hS hτ ha (mc_kk n m) h3k (mc_ins_le n m δ hδ hdd) (by omega) le_rfl
    (by unfold cValid; omega)
  -- the merge total
  have hd : ∀ X : lg.Call, X.1.length ≤ LF n m := fun X => by
    have := hL.depth _ _ (recOf_mem X); omega
  have hmerge := counters_merge_total hL hOK hne hd (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) (fun _ => ∅)
  rw [Fintype.card_fin] at hmerge
  have hw := tracedCounters_wit hL wit hw1 hw2 hw3
  exact {
    two_le_k := hk2
    k_le_t := hkt
    depth_le := countersC_depth_le hL _ _ _ _
    jump_window := countersC_jump_window hL _ _ _ _
    wr_own := countersC_wr_own hL _ _ _ _
    cr_cross := tracedCounters_cr_cross hL hF
    partial_S := hpS
    partial_Fo := tracedCounters_partial_Fo hL hout hsort (by omega) hkt hrec hpS
    partial_p := fun X _ => countersC_p_le hL _ _ _ _ X
    full_S := countersC_full_S hL _ _ _ _
    full_p := tracedCounters_full_p hL hout hsort hsimp hk2 hrec hnd
    Q_sub := countersC_Q_sub hL _ _ _ _
    wit_mem := hw.1
    wit_inj := hw.2.1
    src_once := hw.2.2
    inE_card := inEdges_card
    foreign_level := tracedCounters_foreign_level hL hout hsort hrec
    merge_total := hmerge
    be_total := tracedCounters_be_total hL hout hsort hrec hF
    del_disj := tracedCounters_del_disj hL hchain
    cost_le := hcost
    base_leaf := countersC_base_leaf hL _ _ _ _ }

end ValidTraced

/-! ## Part 4: the master cost theorems -/

section Master

open Frontier.CostSkeleton

variable {out : Fin G.n → List (Fin G.m)} {hins hext : ℕ}

theorem valid_mono_c {ι V E α : Type*} [Fintype ι] [Fintype V] [Fintype E] [LinearOrder α]
    {C : CostAggregate.CallCounters ι V E α} {t k c c' Lmax M0 : ℕ} {inE : V → Finset E} {wit : ι → V → E}
    {src : V} (h : C.Valid t k c Lmax M0 inE wit src) (hc : c ≤ c') : C.Valid t k c' Lmax M0 inE wit src :=
  { h with cost_le := fun X hX => (h.cost_le X hX).trans (Nat.mul_le_mul_right _ hc) }

/-- The constant of the master theorem. -/
def cMaster (a cb : ℕ) : ℕ := cValid a + (2 * cb + 1304)

/-- **Layer-A MASTER COST theorem, literal run** (agent-06, COORD G2-8 (b)).  For the traced C-HD run on a
graph with `|V| ≤ 2n`, `1 ≤ |E| ≤ 2m`, out-degree `≤ δ ≤ 5 dd`, on the dispatch branch `dd ≤ F n + 1`, with
parameters `(tF, kF, LF)(n, m)`, FindPivots `fpC … (kF n m) hins hext`, the amortized DLazy costs over a base
heap `DCb` of per-operation cost `≤ cb (log₂(t+1) + log₂(dd+1) + 2)`, the total cost index is
`≤ 5100 · cMaster · 56 · Tchd n m`. -/
theorem master_cost_C (hout : ∀ u e, e ∈ out u ↔ G.src e = u) (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hsimp : ∀ u, ((out u).map G.dst).Nodup) {n m δ : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m + 1)
    (hGn : G.n ≤ 2 * n) (hGm : G.m ≤ 2 * m) (hm0 : 0 < G.m) (hδ : δ ≤ 5 * dd n m)
    (hdd : dd n m ≤ Frontier.GateCCalc.F n + 1) {a : ℕ} (ha : fpA (kF n m) hins hext ≤ a * (kF n m + 1))
    {DCb : DCost} {cb : ℕ}
    (hbins : DCb.bins ≤ cb * (Nat.log 2 (tF n m + 1) + Nat.log 2 (dd n m + 1) + 1 + 1))
    (hbext : DCb.bext ≤ cb * (Nat.log 2 (tF n m + 1) + Nat.log 2 (dd n m + 1) + 1 + 1))
    {Blow : WLab G s} (hlow : Blow ≤ initLabels s s) {φ φ' : Finset (Fin G.m)}
    (hI : DelInv G s φ) {res : Result G s} {lg : Log G s (FPData G s)}
    (hrel : BMSSPC G s (fpC G s out (kF n m) hins hext) (chdDC (tF n m) (kF n m) δ (LF n m) DCb)
      (chdTau (tF n m)) (LF n m) Blow ⊤ {s} (initLabels s) φ res φ' lg) :
    (lg.cost : ℝ) ≤ 5100 * (cMaster a cb : ℕ) * ((56 : ℕ) : ℝ) * Frontier.GateCCalc.Tchd n m := by
  have ht16 : 16 ≤ tF n m := sixteen_le_tF n m
  have hk2 : 2 ≤ kF n m := two_le_kF n m
  obtain ⟨hL, wit, hV⟩ := valid_traced hout hsort hsimp hδ hdd ⟨0, hm0⟩ ha hlow hI hrel
  have hV' := valid_mono_c hV (show cValid a ≤ cMaster a cb by unfold cMaster; omega)
  have hlow' : ∀ x ∈ ({s} : Finset (Fin G.n)), Blow ≤ dis (s := s) x := by
    intro x hx
    rw [Finset.mem_singleton.mp hx, ← initLabels_source]
    exact hlow
  have hS : ∀ q r, (q, r) ∈ lg → r.S.Nonempty :=
    bmsspC_S_ne (chdTau (tF n m)) (LF n m) Blow ⊤ {s} (initLabels s) φ res φ' lg hrel
      (Finset.singleton_nonempty s)
  have hτ : ∀ l, 1 ≤ chdTau (tF n m) l := fun l => by
    unfold chdTau
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hne : ∀ q r, (q, r) ∈ lg → r.U.Nonempty := U_ne_of_S_ne hL hτ hS
  have hBC := bmsspC_basecost (DC := chdDC (tF n m) (kF n m) δ (LF n m) DCb) (hins := hins) (hext := hext)
    hout hsort hsimp hk2 (chdTau (tF n m)) (LF n m) Blow ⊤ {s} (initLabels s) φ res φ' lg callPre_top hI hlow'
    le_top hrel
  have hins0 := mc_ins0_le n m δ hδ
  set Λ := Nat.log 2 (tF n m + 1) + Nat.log 2 (dd n m + 1) + 1 + 1 with hΛ
  have hΛ2 : 2 ≤ Λ := by omega
  have hbase : ∀ X, (tracedCounters hL).base X = true → (tracedCounters hL).cost X ≤
      cMaster a cb * Λ * (((tracedCounters hL).F.U X).card +
        (CostAggregate.CallCounters.Eout (C := tracedCounters hL) X).card) := by
    intro X hb
    have hmem := recOf_mem X
    have hcost := hBC X.1 (lg.recOf X) hmem hb
    have hSU : (lg.recOf X).S.card ≤ (lg.recOf X).U.card := by
      cases hfull : (tracedCounters hL).full X
      · have h1 := hV.partial_S X hfull
        have h2 : (tracedCounters hL).S X = (lg.recOf X).S := rfl
        have h3 : (tracedCounters hL).F.U X = (lg.recOf X).U := rfl
        rw [h2, h3] at h1
        exact le_trans (Nat.le_mul_of_pos_left _ (by omega)) h1
      · exact Finset.card_le_card (hV.full_S X hfull)
    have hU1 : 1 ≤ (lg.recOf X).U.card := Finset.card_pos.mpr (hne _ _ hmem)
    show (lg.recOf X).cost ≤ cMaster a cb * Λ * ((lg.recOf X).U.card + (Eout G (lg.recOf X).U).card)
    set S := (lg.recOf X).S.card
    set U := (lg.recOf X).U.card
    set E := (Eout G (lg.recOf X).U).card
    set bi := DCb.bins
    set be := DCb.bext
    set ci := chdIns (tF n m) (kF n m) δ (LF n m) 0
    have hc' : (lg.recOf X).cost ≤ S * (1 + (bi + ci + 3)) + U * (1 + be) + E * (1 + (bi + ci + 3)) + 2 :=
      hcost
    have h1 : S * (1 + (bi + ci + 3)) ≤ U * (1 + (bi + ci + 3)) := Nat.mul_le_mul_right _ hSU
    have hstep : (lg.recOf X).cost ≤ (U + E) * (7 + bi + ci + be) := by
      nlinarith [Nat.zero_le (E * be), Nat.zero_le (E * 3)]
    have hK : 7 + bi + ci + be ≤ cMaster a cb * Λ := by
      have hci : ci ≤ 1300 * Λ := by
        have : ci ≤ 1300 * (Nat.log 2 (tF n m + 1) + Nat.log 2 (dd n m + 1) + 2) := hins0
        omega
      have hcM : 2 * cb + 1304 ≤ cMaster a cb := by unfold cMaster; omega
      have := Nat.mul_le_mul_right Λ hcM
      nlinarith
    calc (lg.recOf X).cost ≤ (U + E) * (7 + bi + ci + be) := hstep
      _ ≤ (U + E) * (cMaster a cb * Λ) := Nat.mul_le_mul_left _ hK
      _ = cMaster a cb * Λ * (U + E) := by ring
  have hLF := mc_LF_pos n m
  have hT := CostFinal.total_le_Tchd (tracedCounters hL) n m hn hm hnm (a := 56) hV'
    (by rw [Fintype.card_fin]; omega) (by rw [Fintype.card_fin]; omega) (by omega)
    (by nlinarith) hbase
  have hsum : ∑ X, (tracedCounters hL).cost X = lg.cost := countersC_cost_sum hL _ _ _ _
  rw [hsum] at hT
  exact hT

end Master

/-! ## Part 5: the master cost theorem for the concrete DLazy run -/

section MasterD

open Frontier.CostSkeleton

variable {out : Fin G.n → List (Fin G.m)} {hins hext : ℕ}

/-- **Layer-A MASTER COST theorem for the concrete run over agent-04's DLazy** (the run the RAM core
refines): its actual cost index is at most that of its literal twin (agent-01's telescoping
`chdDL_tele_top`), hence `≤ 5100 · cMaster · 56 · Tchd n m`. -/
theorem master_cost_D (hout : ∀ u e, e ∈ out u ↔ G.src e = u) (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hsimp : ∀ u, ((out u).map G.dst).Nodup) {n m δ : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m + 1)
    (hGn : G.n ≤ 2 * n) (hGm : G.m ≤ 2 * m) (hm0 : 0 < G.m)
    (hdeg : ∀ u, (Eout G {u}).card ≤ δ) (hδ : δ ≤ 5 * dd n m)
    (hdd : dd n m ≤ Frontier.GateCCalc.F n + 1) {a : ℕ} (ha : fpA (kF n m) hins hext ≤ a * (kF n m + 1))
    {DCb : DCost} {cb : ℕ}
    (hbins : DCb.bins ≤ cb * (Nat.log 2 (tF n m + 1) + Nat.log 2 (dd n m + 1) + 1 + 1))
    (hbext : DCb.bext ≤ cb * (Nat.log 2 (tF n m + 1) + Nat.log 2 (dd n m + 1) + 1 + 1))
    {T : ℕ → ℕ} {Blow : WLab G s} (hlow : Blow ≤ initLabels s s) {φ φ' : Finset (Fin G.m)}
    (hI : DelInv G s φ) {res : ResultD G s} {gE : DGl G s} {lg : Log G s (FPData G s)}
    (hrel : BMSSPD G s (dlOps G s) (fpC G s out (kF n m) hins hext) DCb T (chdM (tF n m)) (chdTau (tF n m))
      (LF n m) Blow ⊤ {s} (initLabels s) φ DGl.init res φ' gE lg) :
    (lg.cost : ℝ) ≤ 5100 * (cMaster a cb : ℕ) * ((56 : ℕ) : ℝ) * Frontier.GateCCalc.Tchd n m := by
  have ht16 : 16 ≤ tF n m := sixteen_le_tF n m
  obtain ⟨lgC, hC, -, hle⟩ := chdDL_tele_top (t := tF n m) (δ := δ) hout hsort hsimp (two_le_kF n m)
    (three_kF_le_tF n m) (by omega) hdeg (LF n m) hlow hI hrel
  have h := master_cost_C hout hsort hsimp hn hm hnm hGn hGm hm0 hδ hdd ha hbins hbext hlow hI hC
  have hle' : (lg.cost : ℝ) ≤ (lgC.cost : ℝ) := by exact_mod_cast hle
  exact hle'.trans h

end MasterD

end BM
end CHD
end Frontier
