import Frontier.CHD.DBlocks
import Mathlib.Data.Nat.Log

/-!
# Frontier.CHD.DLazy — the `D` structure with LAZY splitting (owner: agent-04; L3-4, NON-GATE)

Layer-A model of the block structure that B-L3 implements.  The block index is a sorted STACK
(top = the front block), searched by binary search, so no balanced search tree is needed.  Every
structural change happens at the top of the stack:

* `insertL` appends the entry to its block (binary search, `bsCost`; no split).  Blocks away from
  the front may be arbitrarily large.
* `pullL` first *prepares* the front with `prepList`: every block that `pull` is about to take is
  split at its median (`prep`) while it holds more than `2M+1` live entries.  Then it runs
  `DB.pull` on the prepared list, charging one unit per popped block.
* `merge` is `DB.merge`: the groups are pushed on the stack.

**Specifications.**  They are inherited from `Frontier.CHD.DBlocks`, because the prepared list has
the same live entries and the same interval invariant:
* `pullL_spec`: `PullSpec` on views;
* `pullL_post`: `|S| = M` or exhausted;
* `insertL_spec`: view update, frame;
* `merge_spec` and `lazy_merge_eq_literal` apply verbatim.

**Potential** `potL = 2·stale + Σ_b (3 + 420·(|b| - M) + 210·S_M(|b|))`, with
`S_M(s) = Σ_{i ≤ s} log₂ ⌊i/M⌋`.  Amortized costs (`cost + Φ' ≤ Φ + …`):
* `pullL_amortized`: `735 M + 950`.  A median split of a large block releases at least half its
  size (`Ssum_split`); every split pays for itself (`split_step`).
* `insertL_amortized`: `bsCost(#blocks) + 425 + 210·log₂ ⌊(|D|+1)/M⌋`.
* `mergeL_amortized`: `4·#groups + 4`, provided the child has `3M' ≤ M`.  Blocks moving to the
  larger parameter lose potential (`Ssum_Mchange`, `group_weight`).
* `deleteKeys_amortizedL`: `3|ks| + 1`.
* `potL_new`: a new structure has potential `3`.
* Family lemmas for a shared live map: `staleCnt_insertL_others` (`≤ +1`),
  `staleCnt_pullL_others` (`= `), `wf_insertL_others`, `wf_pullL_others`.
* Invariants: `pullL_aux`, `insertL_aux`, `merge_ids`.

**O(1)-amortized merge.**  `potM = potL + ⌊12·|entries|/M⌋`.  With it:
* `mergeM_amortized`: `cost + Φ(merged) ≤ Φ(D) + Φ(D') + 14`, for `3M' ≤ M` and `M' ≥ 1`;
* `pullM_amortized`: `735 M + 950`;
* `insertM_amortized`: `bsCost + 438 + 210·ℓ`;
* `deleteKeys_amortizedM`: `3|ks| + 1`;
* `potM_new`: `3`.
-/

namespace Frontier.CHD.DL

open Frontier.CHD Frontier.CHD.DB

/-! ## The logarithmic potential -/

/-- `ℓ_M(i) = log₂ ⌊i / M⌋` -/
def ell (M i : ℕ) : ℕ := Nat.log 2 (i / M)

/-- `S_M(s) = Σ_{i=1}^{s} ℓ_M(i)` -/
def Ssum (M : ℕ) : ℕ → ℕ
  | 0 => 0
  | s + 1 => Ssum M s + ell M (s + 1)

theorem ell_mono {M i j : ℕ} (h : i ≤ j) : ell M i ≤ ell M j :=
  Nat.log_mono_right (Nat.div_le_div_right h)

theorem ell_anti {M M' i : ℕ} (hM : 0 < M) (h : M ≤ M') : ell M' i ≤ ell M i :=
  Nat.log_mono_right (Nat.div_le_div_left h hM)

theorem ell_of_lt {M i : ℕ} (h : i < 2 * M) : ell M i = 0 := by
  unfold ell
  apply Nat.log_of_lt
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  · rw [Nat.div_lt_iff_lt_mul hM]; linarith

/-- doubling the argument raises `ℓ` by one (once `i ≥ M`) -/
theorem ell_double {M i : ℕ} (hM : 0 < M) (hi : M ≤ i) : ell M i + 1 ≤ ell M (2 * i) := by
  unfold ell
  have hq : 0 < i / M := Nat.div_pos hi hM
  have h2 : i / M * 2 ≤ 2 * i / M := by
    rw [Nat.le_div_iff_mul_le hM]
    have := Nat.div_mul_le_self i M
    nlinarith
  calc Nat.log 2 (i / M) + 1 = Nat.log 2 (i / M * 2) := (Nat.log_mul_base (by norm_num) (by omega)).symm
    _ ≤ Nat.log 2 (2 * i / M) := Nat.log_mono_right h2

theorem ell_two_mul {M : ℕ} (hM : 0 < M) : 1 ≤ ell M (2 * M) := by
  unfold ell
  rw [Nat.mul_div_cancel _ hM]
  exact Nat.log_pos (by norm_num) le_rfl

theorem Ssum_mono {M : ℕ} : ∀ {s s' : ℕ}, s ≤ s' → Ssum M s ≤ Ssum M s'
  | s, 0, h => by rw [Nat.le_zero.mp h]
  | s, s' + 1, h => by
      rcases Nat.lt_or_ge s (s' + 1) with h' | h'
      · have := Ssum_mono (M := M) (s := s) (s' := s') (by omega)
        simp only [Ssum]; omega
      · rw [show s = s' + 1 by omega]

theorem Ssum_of_le {M s : ℕ} (h : s < 2 * M) : Ssum M s = 0 := by
  induction s with
  | zero => rfl
  | succ s ih => simp only [Ssum, ih (by omega), ell_of_lt h]

/-- adding `a` entries to a block of size `b` raises `S` by at most `a · ℓ(b + a)` -/
theorem Ssum_add_le (M b : ℕ) : ∀ a, Ssum M (b + a) ≤ Ssum M b + a * ell M (b + a)
  | 0 => by simp
  | a + 1 => by
      have ih := Ssum_add_le M b a
      have hm : ell M (b + a) ≤ ell M (b + (a + 1)) := ell_mono (by omega)
      rw [show b + (a + 1) = (b + a) + 1 by omega]
      simp only [Ssum]
      rw [show b + a + 1 = b + (a + 1) by omega]
      nlinarith

/-- **median split**: for `a ≤ b` and `b ≥ 2M`, `S(a) + S(b) + a ≤ S(a + b)` -/
theorem Ssum_split {M b : ℕ} (hM : 0 < M) (hb : 2 * M ≤ b) :
    ∀ a, a ≤ b → Ssum M a + Ssum M b + a ≤ Ssum M (b + a)
  | 0, _ => by simp [Ssum]
  | a + 1, ha => by
      have ih := Ssum_split hM hb a (by omega)
      have key : ell M (a + 1) + 1 ≤ ell M (b + (a + 1)) := by
        by_cases hlt : a + 1 < M
        · rw [ell_of_lt (by omega)]
          exact le_trans (ell_two_mul hM) (ell_mono (by omega))
        · exact le_trans (ell_double hM (by omega)) (ell_mono (by omega))
      rw [show b + (a + 1) = (b + a) + 1 by omega] at key ⊢
      simp only [Ssum]
      omega

/-- a larger parameter gives a smaller potential -/
theorem Ssum_anti {M M' : ℕ} (hM : 0 < M) (h : M ≤ M') : ∀ s, Ssum M' s ≤ Ssum M s
  | 0 => le_rfl
  | s + 1 => by
      have := Ssum_anti hM h s
      have := ell_anti (i := s + 1) hM h
      simp only [Ssum]; omega

/-- moving a block from parameter `M'` to `M ≥ 3M'` releases one unit per entry beyond `M` -/
theorem Ssum_Mchange {M M' : ℕ} (hM' : 0 < M') (h3 : 3 * M' ≤ M) :
    ∀ s, Ssum M s + (s + 1 - M) ≤ Ssum M' s
  | 0 => by simp [Ssum]; omega
  | s + 1 => by
      have ih := Ssum_Mchange hM' h3 s
      have hM : 0 < M := by omega
      simp only [Ssum]
      by_cases hs : s + 1 < M
      · have := ell_anti (i := s + 1) hM' (by omega : M' ≤ M)
        have e : s + 1 + 1 - M = 0 := by omega
        have e' : s + 1 - M = 0 := by omega
        omega
      · -- `ℓ_{M'}(s+1) ≥ ℓ_M(s+1) + 1`
        have key : ell M (s + 1) + 1 ≤ ell M' (s + 1) := by
          unfold ell
          have hq : 0 < (s + 1) / M := Nat.div_pos (by omega) hM
          have h2 : (s + 1) / M * 2 ≤ (s + 1) / M' := by
            rw [Nat.le_div_iff_mul_le hM']
            have := Nat.div_mul_le_self (s + 1) M
            nlinarith
          calc Nat.log 2 ((s + 1) / M) + 1 = Nat.log 2 ((s + 1) / M * 2) :=
                (Nat.log_mul_base (by norm_num) (by omega)).symm
            _ ≤ Nat.log 2 ((s + 1) / M') := Nat.log_mono_right h2
        omega

/-! ## Median split of the front block and preparation of the front -/

section Ops

variable {κ α : Type*} [DecidableEq κ] [LinearOrder α] [Inhabited α]

/-- the median of the live values of a block -/
def medOf (L : Live κ α) (b : Block κ α) : α :=
  (selectC ((liveOf L b.ents).map (·.val)) ((liveOf L b.ents).length / 2)).1

/-- live entries below the median -/
def loOf (L : Live κ α) (b : Block κ α) : List (Entry κ α) :=
  (liveOf L b.ents).filter (fun e => decide (e.val < medOf L b))

/-- live entries at or above the median -/
def hiOf (L : Live κ α) (b : Block κ α) : List (Entry κ α) :=
  (liveOf L b.ents).filter (fun e => decide (medOf L b ≤ e.val))

/-- cost of one median split: scan, selection, partition -/
def splitCost (L : Live κ α) (b : Block κ α) : ℕ :=
  b.ents.length + (selectC ((liveOf L b.ents).map (·.val)) ((liveOf L b.ents).length / 2)).2 +
    2 * (liveOf L b.ents).length + 1

omit [DecidableEq κ] in
theorem loOf_length_lt {L : Live κ α} {b : Block κ α} (h : 0 < (liveOf L b.ents).length) :
    (loOf L b).length < (liveOf L b.ents).length := by
  have hk : (liveOf L b.ents).length / 2 < ((liveOf L b.ents).map (·.val)).length := by
    simp; omega
  have hkth := selectC_isKth _ hk
  have h1 := hkth.2.1
  have e : (loOf L b).length = cntLt ((liveOf L b.ents).map (·.val)) (medOf L b) := by
    unfold loOf cntLt; rw [← List.countP_eq_length_filter, List.countP_map]; rfl
  unfold medOf at e
  omega

omit [DecidableEq κ] in
theorem liveOf_all_live {L : Live κ α} {es : List (Entry κ α)} (h : ∀ e ∈ es, e.IsLive L) :
    liveOf L es = es := by
  unfold liveOf; rw [List.filter_eq_self]; intro e he; simp [h e he]

omit [DecidableEq κ] in
theorem loOf_live {L : Live κ α} {b : Block κ α} : ∀ e ∈ loOf L b, e.IsLive L :=
  fun _ he => of_decide_eq_true (List.mem_filter.mp (List.mem_filter.mp he).1).2

omit [DecidableEq κ] in
theorem hiOf_live {L : Live κ α} {b : Block κ α} : ∀ e ∈ hiOf L b, e.IsLive L :=
  fun _ he => of_decide_eq_true (List.mem_filter.mp (List.mem_filter.mp he).1).2

omit [DecidableEq κ] in
theorem lo_hi_length (L : Live κ α) (b : Block κ α) :
    (loOf L b).length + (hiOf L b).length = (liveOf L b.ents).length := by
  unfold loOf hiOf
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  have := List.length_eq_countP_add_countP (l := liveOf L b.ents) (fun e : Entry κ α => e.val < medOf L b)
  rw [this]; congr 1; apply List.countP_congr; intro e _; simp

/-- The split guard: more than `2M+1` live entries and a nonempty lower half. -/
def SplitG (L : Live κ α) (M : ℕ) (b : Block κ α) : Prop :=
  2 * M + 1 < (liveOf L b.ents).length ∧ loOf L b ≠ []

instance (L : Live κ α) (M : ℕ) (b : Block κ α) : Decidable (SplitG L M b) := by
  unfold SplitG; infer_instance

/-- **prep**: split the front block at its median while it holds more than `2M+1` live entries. -/
def prep (L : Live κ α) (M : ℕ) : List (Block κ α) → List (Block κ α) × ℕ
  | [] => ([], 0)
  | b :: bs =>
    if h : SplitG L M b then
      ((prep L M (⟨b.sep, loOf L b⟩ :: ⟨((medOf L b : α) : WithBot α), hiOf L b⟩ :: bs)).1,
       (prep L M (⟨b.sep, loOf L b⟩ :: ⟨((medOf L b : α) : WithBot α), hiOf L b⟩ :: bs)).2 + splitCost L b)
    else (b :: bs, 0)
termination_by bs => match bs with | [] => 0 | b :: _ => (liveOf L b.ents).length
decreasing_by
  show (liveOf L (loOf L b)).length < (liveOf L b.ents).length
  rw [liveOf_all_live loOf_live]
  exact loOf_length_lt (by unfold SplitG at h; omega)

/-! ### `prep` via `fixBlock`: the split step is `fixBlock`'s median split -/

omit [DecidableEq κ] in
theorem length_liveOf_le (L : Live κ α) (es : List (Entry κ α)) : (liveOf L es).length ≤ es.length :=
  List.length_filter_le _ _

theorem fixBlock_of_splitG (T : ℕ) {L : Live κ α} {M : ℕ} {b : Block κ α} (h : SplitG L M b) :
    (fixBlock T L M b).1 = [⟨b.sep, loOf L b⟩, ⟨((medOf L b : α) : WithBot α), hiOf L b⟩] := by
  obtain ⟨h1, h2⟩ := h
  have hl := length_liveOf_le L b.ents
  have hlen : ¬ b.ents.length ≤ 2 * M + 1 := by omega
  have hlen2 : ¬ (liveOf L b.ents).length ≤ M := by omega
  have h2' : ¬ ((liveOf L b.ents).filter (fun e => decide (e.val <
      (selectC ((liveOf L b.ents).map (·.val)) ((liveOf L b.ents).length / 2)).1))) = [] := h2
  unfold fixBlock
  rw [ite_eq_right_iff.mpr (fun h => absurd h hlen), ite_eq_right_iff.mpr (fun h => absurd h hlen2),
    ite_eq_right_iff.mpr (fun h => absurd h h2')]
  rfl

/-- the head block after one split step keeps the interval invariant -/
theorem intervalOK_split_head {L : Live κ α} {M : ℕ} {b : Block κ α} {bs : List (Block κ α)}
    {lo hi : WithBot α} (hs : SplitG L M b) (h : IntervalOK L (b :: bs) lo hi) :
    IntervalOK L (⟨b.sep, loOf L b⟩ :: ⟨((medOf L b : α) : WithBot α), hiOf L b⟩ :: bs) lo hi := by
  have hf := fixBlock_of_splitG 0 hs
  rcases bs with _ | ⟨b', bs'⟩
  · obtain ⟨hsep, hlt, hb⟩ := h
    have k := (intervalOK_fixBlock 0 (M := M) (b := b) (hi := hi) (by rw [hsep]; exact hlt) hb).1
    rw [hf] at k
    rw [← hsep]; exact k
  · obtain ⟨hsep, hlt, hb, hrest⟩ := h
    have k := (intervalOK_fixBlock 0 (M := M) (b := b) (hi := b'.sep) (by rw [hsep]; exact hlt) hb).1
    rw [hf] at k
    have := IntervalOK.append_cons k (List.cons_ne_nil _ _) hrest
    rw [← hsep]; simpa using this

theorem mem_liveVals_split_head {L : Live κ α} {M : ℕ} {b : Block κ α} {bs : List (Block κ α)}
    (hs : SplitG L M b) (x : Entry κ α) :
    x ∈ liveVals L (⟨b.sep, loOf L b⟩ :: ⟨((medOf L b : α) : WithBot α), hiOf L b⟩ :: bs) ↔
      x ∈ liveVals L (b :: bs) := by
  have hf := fixBlock_of_splitG 0 hs
  have key := mem_liveVals_fixBlock 0 (L := L) (M := M) (b := b) (e := x)
  rw [hf] at key
  rw [show (⟨b.sep, loOf L b⟩ :: ⟨((medOf L b : α) : WithBot α), hiOf L b⟩ :: bs : List (Block κ α)) =
      [⟨b.sep, loOf L b⟩, ⟨((medOf L b : α) : WithBot α), hiOf L b⟩] ++ bs from rfl,
    liveVals_append, List.mem_append, key, mem_liveVals_cons']

theorem allEnts_split_head_subperm {L : Live κ α} {M : ℕ} {b : Block κ α} {bs : List (Block κ α)}
    (hs : SplitG L M b) :
    (allEnts (⟨b.sep, loOf L b⟩ :: ⟨((medOf L b : α) : WithBot α), hiOf L b⟩ :: bs)).Subperm
      (allEnts (b :: bs)) := by
  have hf := fixBlock_of_splitG 0 hs
  have key := allEnts_fixBlock_subperm 0 (L := L) (M := M) (b := b)
  rw [hf] at key
  have e1 : allEnts (⟨b.sep, loOf L b⟩ :: ⟨((medOf L b : α) : WithBot α), hiOf L b⟩ :: bs) =
      allEnts [⟨b.sep, loOf L b⟩, ⟨((medOf L b : α) : WithBot α), hiOf L b⟩] ++ allEnts bs := by
    simp [allEnts]
  have e2 : allEnts (b :: bs) = b.ents ++ allEnts bs := by simp [allEnts]
  rw [e1, e2]
  exact subperm_append' key (subperm_refl' _)

/-! ### Specifications of `prep` -/

theorem prep_liveVals (L : Live κ α) (M : ℕ) :
    ∀ bs (x : Entry κ α), x ∈ liveVals L (prep L M bs).1 ↔ x ∈ liveVals L bs := by
  intro bs
  induction bs using prep.induct (L := L) (M := M) with
  | case1 => intro x; simp [prep]
  | case2 b bs h ih =>
    intro x
    rw [prep, dif_pos h]
    rw [ih x, mem_liveVals_split_head h]
  | case3 b bs h =>
    intro x
    rw [prep, dif_neg h]

theorem prep_intervalOK (L : Live κ α) (M : ℕ) :
    ∀ bs {lo hi : WithBot α}, IntervalOK L bs lo hi → IntervalOK L (prep L M bs).1 lo hi := by
  intro bs
  induction bs using prep.induct (L := L) (M := M) with
  | case1 => intro lo hi h; simpa [prep] using h
  | case2 b bs h ih =>
    intro lo hi hI
    rw [prep, dif_pos h]
    exact ih (intervalOK_split_head h hI)
  | case3 b bs h =>
    intro lo hi hI
    rw [prep, dif_neg h]; exact hI

theorem prep_subperm (L : Live κ α) (M : ℕ) :
    ∀ bs, (allEnts (prep L M bs).1).Subperm (allEnts bs) := by
  intro bs
  induction bs using prep.induct (L := L) (M := M) with
  | case1 => simp only [prep]; exact subperm_refl' _
  | case2 b bs h ih =>
    rw [prep, dif_pos h]
    exact ih.trans (allEnts_split_head_subperm h)
  | case3 b bs h =>
    rw [prep, dif_neg h]

theorem prep_ne_nil (L : Live κ α) (M : ℕ) :
    ∀ bs, bs ≠ [] → (prep L M bs).1 ≠ [] := by
  intro bs
  induction bs using prep.induct (L := L) (M := M) with
  | case1 => intro h; exact absurd rfl h
  | case2 b bs h ih =>
    intro _
    rw [prep, dif_pos h]
    exact ih (List.cons_ne_nil _ _)
  | case3 b bs h =>
    intro _
    rw [prep, dif_neg h]; exact List.cons_ne_nil _ _

theorem prep_nil (L : Live κ α) (M : ℕ) : (prep L M []).1 = [] := by simp [prep]

theorem prep_nextSep (L : Live κ α) (M : ℕ) (hi : WithBot α) :
    ∀ bs, nextSep (prep L M bs).1 hi = nextSep bs hi := by
  intro bs
  induction bs using prep.induct (L := L) (M := M) with
  | case1 => simp [prep]
  | case2 b bs h ih =>
    rw [prep, dif_pos h]; simp only; rw [ih]; rfl
  | case3 b bs h =>
    rw [prep, dif_neg h]

/-- termination measure for `prepList` -/
def wt (bs : List (Block κ α)) : ℕ := (bs.map (fun b => b.ents.length ^ 2 + 1)).sum

omit [DecidableEq κ] in
theorem wt_cons (b : Block κ α) (bs : List (Block κ α)) :
    wt (b :: bs) = b.ents.length ^ 2 + 1 + wt bs := by simp [wt]

omit [DecidableEq κ] in
theorem prep_wt (L : Live κ α) (M : ℕ) : ∀ bs, wt (prep L M bs).1 ≤ wt bs := by
  intro bs
  induction bs using prep.induct (L := L) (M := M) with
  | case1 => simp [prep]
  | case2 b bs h ih =>
    rw [prep, dif_pos h]
    refine le_trans ih ?_
    rw [wt_cons, wt_cons, wt_cons]
    simp only
    have hsum := lo_hi_length L b
    have hl := length_liveOf_le L b.ents
    have hlt := loOf_length_lt (L := L) (b := b) (by unfold SplitG at h; omega)
    have hlo : 1 ≤ (loOf L b).length := by
      have := h.2
      rcases hh : loOf L b with _ | ⟨x, xs⟩
      · exact absurd hh this
      · simp
    set x := (loOf L b).length
    set y := (hiOf L b).length
    set P := b.ents.length
    have hy : 1 ≤ y := by omega
    have hxy : 1 ≤ x * y := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hsq : (x + y) ^ 2 ≤ P ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have e : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * (x * y) := by ring
    omega
  | case3 b bs h =>
    rw [prep, dif_neg h]

/-- **prepList**: prepare every block that `pull` will take (while at most `M` live entries have
been passed). -/
def prepList (L : Live κ α) (M : ℕ) (cnt : ℕ) : List (Block κ α) → List (Block κ α) × ℕ
  | [] => ([], 0)
  | b :: rest =>
    if M < cnt then (b :: rest, 0)
    else
      match h : (prep L M (b :: rest)).1 with
      | [] => ([], (prep L M (b :: rest)).2)
      | b' :: bs' =>
        (b' :: (prepList L M (cnt + (liveOf L b'.ents).length) bs').1,
         (prepList L M (cnt + (liveOf L b'.ents).length) bs').2 + (prep L M (b :: rest)).2)
termination_by bs => wt bs
decreasing_by
  have := prep_wt L M (b :: rest)
  rw [h, wt_cons, wt_cons] at this
  rw [wt_cons]
  omega

theorem prepList_liveVals (L : Live κ α) (M : ℕ) :
    ∀ cnt bs (x : Entry κ α), x ∈ liveVals L (prepList L M cnt bs).1 ↔ x ∈ liveVals L bs := by
  intro cnt bs
  induction cnt, bs using prepList.induct (L := L) (M := M) with
  | case1 cnt => intro x; simp [prepList]
  | case2 cnt b rest h => intro x; rw [prepList, if_pos h]
  | case3 cnt b rest h hp =>
    intro x
    exact absurd hp (prep_ne_nil L M _ (List.cons_ne_nil _ _))
  | case4 cnt b rest h b' bs' hp ih =>
    intro x
    rw [prepList, if_neg h]
    split
    · next hp' => exact absurd hp' (prep_ne_nil L M _ (List.cons_ne_nil _ _))
    · next b'' bs'' hp' =>
      rw [hp] at hp'
      obtain ⟨rfl, rfl⟩ := List.cons.inj hp'
      rw [mem_liveVals_cons', ih x, ← mem_liveVals_cons', ← hp, prep_liveVals]

theorem prepList_nil_iff (L : Live κ α) (M : ℕ) :
    ∀ cnt bs, (prepList L M cnt bs).1 = [] ↔ bs = [] := by
  intro cnt bs
  induction cnt, bs using prepList.induct (L := L) (M := M) with
  | case1 cnt => simp [prepList]
  | case2 cnt b rest h => rw [prepList, if_pos h]
  | case3 cnt b rest h hp => exact absurd hp (prep_ne_nil L M _ (List.cons_ne_nil _ _))
  | case4 cnt b rest h b' bs' hp ih =>
    rw [prepList, if_neg h]
    split
    · next hp' => exact absurd hp' (prep_ne_nil L M _ (List.cons_ne_nil _ _))
    · simp

theorem prepList_nextSep (L : Live κ α) (M : ℕ) (hi : WithBot α) :
    ∀ cnt bs, nextSep (prepList L M cnt bs).1 hi = nextSep bs hi := by
  intro cnt bs
  induction cnt, bs using prepList.induct (L := L) (M := M) with
  | case1 cnt => simp [prepList]
  | case2 cnt b rest h => rw [prepList, if_pos h]
  | case3 cnt b rest h hp => exact absurd hp (prep_ne_nil L M _ (List.cons_ne_nil _ _))
  | case4 cnt b rest h b' bs' hp ih =>
    rw [prepList, if_neg h]
    split
    · next hp' => exact absurd hp' (prep_ne_nil L M _ (List.cons_ne_nil _ _))
    · next b'' bs'' hp' =>
      rw [hp] at hp'
      obtain ⟨rfl, rfl⟩ := List.cons.inj hp'
      have := prep_nextSep L M hi (b :: rest)
      rw [hp] at this
      simpa [nextSep] using this

theorem prepList_intervalOK (L : Live κ α) (M : ℕ) :
    ∀ cnt bs {lo hi : WithBot α}, IntervalOK L bs lo hi →
      IntervalOK L (prepList L M cnt bs).1 lo hi := by
  intro cnt bs
  induction cnt, bs using prepList.induct (L := L) (M := M) with
  | case1 cnt => intro lo hi h; simpa [prepList] using h
  | case2 cnt b rest h => intro lo hi hI; rw [prepList, if_pos h]; exact hI
  | case3 cnt b rest h hp => exact absurd hp (prep_ne_nil L M _ (List.cons_ne_nil _ _))
  | case4 cnt b rest h b' bs' hp ih =>
    intro lo hi hI
    rw [prepList, if_neg h]
    split
    · next hp' => exact absurd hp' (prep_ne_nil L M _ (List.cons_ne_nil _ _))
    · next b'' bs'' hp' =>
      rw [hp] at hp'
      obtain ⟨rfl, rfl⟩ := List.cons.inj hp'
      have h1 := prep_intervalOK L M (b :: rest) hI
      rw [hp] at h1
      have h2 := (IntervalOK.split (bs₁ := [b']) (bs₂ := bs') (List.cons_ne_nil _ _) h1).2
      exact IntervalOK.cons_of h1 (ih h2) (prepList_nextSep L M hi _ _) (prepList_nil_iff L M _ _)

theorem prepList_subperm (L : Live κ α) (M : ℕ) :
    ∀ cnt bs, (allEnts (prepList L M cnt bs).1).Subperm (allEnts bs) := by
  intro cnt bs
  induction cnt, bs using prepList.induct (L := L) (M := M) with
  | case1 cnt => simp only [prepList]; exact subperm_refl' _
  | case2 cnt b rest h => rw [prepList, if_pos h]
  | case3 cnt b rest h hp => exact absurd hp (prep_ne_nil L M _ (List.cons_ne_nil _ _))
  | case4 cnt b rest h b' bs' hp ih =>
    rw [prepList, if_neg h]
    split
    · next hp' => exact absurd hp' (prep_ne_nil L M _ (List.cons_ne_nil _ _))
    · next b'' bs'' hp' =>
      rw [hp] at hp'
      obtain ⟨rfl, rfl⟩ := List.cons.inj hp'
      have h1 := prep_subperm L M (b :: rest)
      rw [hp] at h1
      have e : allEnts (b' :: (prepList L M (cnt + (liveOf L b'.ents).length) bs').1) =
          b'.ents ++ allEnts (prepList L M (cnt + (liveOf L b'.ents).length) bs').1 := by
        simp [allEnts]
      have e' : allEnts (b' :: bs') = b'.ents ++ allEnts bs' := by simp [allEnts]
      rw [e]
      rw [e'] at h1
      exact (subperm_append' (subperm_refl' _) ih).trans h1

/-! ## Pull with lazy splitting -/

variable (T : ℕ)

/-- **pullL**: prepare the front, then `DB.pull` (charging `T` per removed block). -/
def pullL (L : Live κ α) (D : DStr κ α) : List κ × α × Live κ α × DStr κ α × ℕ :=
  ((pull T L { D with blocks := (prepList L D.M 0 D.blocks).1 }).1,
   (pull T L { D with blocks := (prepList L D.M 0 D.blocks).1 }).2.1,
   (pull T L { D with blocks := (prepList L D.M 0 D.blocks).1 }).2.2.1,
   (pull T L { D with blocks := (prepList L D.M 0 D.blocks).1 }).2.2.2.1,
   (pull T L { D with blocks := (prepList L D.M 0 D.blocks).1 }).2.2.2.2 +
     (prepList L D.M 0 D.blocks).2)

/-- the prepared structure -/
def prepD (L : Live κ α) (D : DStr κ α) : DStr κ α := { D with blocks := (prepList L D.M 0 D.blocks).1 }

theorem view_prepD (L : Live κ α) (D : DStr κ α) (y : κ) : view L (prepD L D) y = view L D y := by
  have hiff : HasKey L (prepD L D) y ↔ HasKey L D y := by
    unfold HasKey prepD
    simp only
    constructor
    · rintro ⟨e, he, hk⟩; exact ⟨e, (prepList_liveVals L D.M 0 D.blocks e).mp he, hk⟩
    · rintro ⟨e, he, hk⟩; exact ⟨e, (prepList_liveVals L D.M 0 D.blocks e).mpr he, hk⟩
  unfold view
  by_cases h : HasKey L D y
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hiff.mp h')), ite_eq_right h]

theorem wf_prepD {L : Live κ α} {D : DStr κ α} (hwf : WF L D) : WF L (prepD L D) :=
  ⟨fun h => hwf.1 ((prepList_nil_iff L D.M 0 D.blocks).mp h),
   prepList_intervalOK L D.M 0 D.blocks hwf.2⟩

theorem idsNodup_prepD {L : Live κ α} {D : DStr κ α} (hid : IdsNodup D) : IdsNodup (prepD L D) :=
  subperm_nodup' (subperm_map' _ (prepList_subperm L D.M 0 D.blocks)) hid

theorem pullL_eq (L : Live κ α) (D : DStr κ α) :
    pullL T L D = ((pull T L (prepD L D)).1, (pull T L (prepD L D)).2.1,
      (pull T L (prepD L D)).2.2.1, (pull T L (prepD L D)).2.2.2.1,
      (pull T L (prepD L D)).2.2.2.2 + (prepList L D.M 0 D.blocks).2) := rfl

/-- **Correctness of `pullL`** (`PullSpec` on views), inherited from `pull_spec`. -/
theorem pullL_spec {L : Live κ α} {D : DStr κ α} (hwf : WF L D) :
    (∀ y, y ∈ (pullL T L D).1 ↔ ∃ a, view L D y = some a ∧ a < (pullL T L D).2.1) ∧
    (∀ y, view (pullL T L D).2.2.1 (pullL T L D).2.2.2.1 y =
        if y ∈ (pullL T L D).1 then none else view L D y) ∧
    (pullL T L D).2.1 ≤ D.Bd ∧
    WF (pullL T L D).2.2.1 (pullL T L D).2.2.2.1 ∧
    (pullL T L D).2.2.1 = clearKeys L (pullL T L D).1 ∧
    (pullL T L D).2.2.2.1.M = D.M ∧ (pullL T L D).2.2.2.1.Bd = D.Bd := by
  have h := pull_spec T (wf_prepD hwf)
  rw [pullL_eq]
  simp only [view_prepD] at h
  exact h

/-- sizes and bounds of `pullL` (from `pull_post`) -/
theorem pullL_post {L : Live κ α} {D : DStr κ α} {kof : α → κ} (hwf : WF L D)
    (hK : KeyInj L kof) (hid : IdsNodup D) (hM : 1 ≤ D.M) :
    (pullL T L D).1.length ≤ D.M ∧
    ((pullL T L D).2.1 = D.Bd ∨ (pullL T L D).1.length = D.M) ∧
    ((∃ y, HasKey L D y) → (pullL T L D).1 ≠ []) ∧
    (∀ e ∈ liveVals (pullL T L D).2.2.1 (pullL T L D).2.2.2.1.blocks, (pullL T L D).2.1 ≤ e.val) ∧
    (∀ b ∈ (pullL T L D).2.2.2.1.blocks.tail, ((pullL T L D).2.1 : WithBot α) < b.sep) := by
  have h := pull_post T (wf_prepD hwf) hK (idsNodup_prepD hid) hM
  have hk : (∃ y, HasKey L (prepD L D) y) ↔ (∃ y, HasKey L D y) := by
    constructor
    · rintro ⟨y, e, he, hk⟩; exact ⟨y, e, (prepList_liveVals L D.M 0 D.blocks e).mp he, hk⟩
    · rintro ⟨y, e, he, hk⟩; exact ⟨y, e, (prepList_liveVals L D.M 0 D.blocks e).mpr he, hk⟩
  rw [pullL_eq]
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, fun hh => h3 (hk.mpr hh), h4, h5⟩

/-! ## The lazy potential -/

/-- structural weight of a block: `3` (its stack slot), `420` per entry beyond `M`, `210 · S_M`. -/
def bw (M : ℕ) (b : Block κ α) : ℕ := 3 + 420 * (b.ents.length - M) + 210 * Ssum M b.ents.length

/-- structural potential of a block list -/
def spot (M : ℕ) (bs : List (Block κ α)) : ℕ := (bs.map (bw M)).sum

/-- **the lazy potential** of a structure -/
def potL (L : Live κ α) (D : DStr κ α) : ℕ := 2 * staleCnt L D.blocks + spot D.M D.blocks

theorem spot_nil (M : ℕ) : spot M ([] : List (Block κ α)) = 0 := rfl

theorem spot_cons (M : ℕ) (b : Block κ α) (bs : List (Block κ α)) :
    spot M (b :: bs) = bw M b + spot M bs := by simp [spot]

theorem spot_append (M : ℕ) (bs₁ bs₂ : List (Block κ α)) :
    spot M (bs₁ ++ bs₂) = spot M bs₁ + spot M bs₂ := by simp [spot]

theorem three_le_bw (M : ℕ) (b : Block κ α) : 3 ≤ bw M b := by unfold bw; omega

theorem three_mul_length_le_spot (M : ℕ) : ∀ bs : List (Block κ α), 3 * bs.length ≤ spot M bs
  | [] => by simp [spot_nil]
  | b :: bs => by
      rw [spot_cons, List.length_cons]
      have := three_le_bw M b
      have := three_mul_length_le_spot M bs
      omega

theorem stale_block_split (L : Live κ α) (b : Block κ α) :
    b.ents.length = (liveOf L b.ents).length + b.ents.countP (fun e => !decide (e.IsLive L)) := by
  have := List.length_eq_countP_add_countP (l := b.ents) (fun e : Entry κ α => e.IsLive L)
  rw [this]; unfold liveOf; rw [List.countP_eq_length_filter]; congr 1
  apply List.countP_congr; intro x _; simp

/-- **one median split pays for itself** (distinct live values, `M ≥ 1`) -/
theorem split_step {L : Live κ α} {M : ℕ} {b : Block κ α} (hM : 1 ≤ M) (hs : SplitG L M b)
    (hd : ((liveOf L b.ents).map (·.val)).Nodup) :
    splitCost L b + bw M ⟨b.sep, loOf L b⟩ + bw M ⟨((medOf L b : α) : WithBot α), hiOf L b⟩ ≤
      2 * b.ents.countP (fun e => !decide (e.IsLive L)) + bw M b := by
  have hst := stale_block_split L b
  have hsum := lo_hi_length L b
  obtain ⟨hbig, -⟩ := hs
  have hpos : 0 < (liveOf L b.ents).length := by omega
  have hlo : (loOf L b).length = (liveOf L b.ents).length / 2 := split_sizes hd hpos
  have hsel := selectC_cost ((liveOf L b.ents).map (·.val)) (k := (liveOf L b.ents).length / 2)
    (by simp; omega)
  simp only [List.length_map] at hsel
  unfold splitCost bw
  simp only
  set sl := (liveOf L b.ents).length with hsl
  set P := b.ents.length with hP
  set st := b.ents.countP (fun e => !decide (e.IsLive L)) with hst'
  set lo := (loOf L b).length with hlo'
  set hi := (hiOf L b).length with hhi'
  set sc := (selectC ((liveOf L b.ents).map (·.val)) (sl / 2)).2 with hsc
  have hmono : Ssum M sl ≤ Ssum M P := Ssum_mono (by omega)
  by_cases hh : 2 * M ≤ hi
  · have hsp := Ssum_split (M := M) (b := hi) (by omega) hh lo (by omega)
    rw [show hi + lo = sl by omega] at hsp
    omega
  · have h1 : Ssum M lo = 0 := Ssum_of_le (by omega)
    have h2 : Ssum M hi = 0 := Ssum_of_le (by omega)
    omega

/-- distinct live values inside a block -/
def LVnd (L : Live κ α) (b : Block κ α) : Prop := ((liveOf L b.ents).map (·.val)).Nodup

theorem lvnd_lo {L : Live κ α} {b : Block κ α} (h : LVnd L b) : LVnd L ⟨b.sep, loOf L b⟩ := by
  unfold LVnd at h ⊢
  simp only
  rw [liveOf_all_live loOf_live]
  exact (List.filter_sublist.map _).nodup h

theorem lvnd_hi {L : Live κ α} {b : Block κ α} (h : LVnd L b) :
    LVnd L ⟨((medOf L b : α) : WithBot α), hiOf L b⟩ := by
  unfold LVnd at h ⊢
  simp only
  rw [liveOf_all_live hiOf_live]
  exact (List.filter_sublist.map _).nodup h

theorem prep_lvnd (L : Live κ α) (M : ℕ) :
    ∀ bs, (∀ c ∈ bs, LVnd L c) → ∀ c ∈ (prep L M bs).1, LVnd L c := by
  intro bs
  induction bs using prep.induct (L := L) (M := M) with
  | case1 => intro _ c hc; simp [prep] at hc
  | case2 b bs h ih =>
    intro hnd c hc
    rw [prep, dif_pos h] at hc
    refine ih ?_ c hc
    intro c' hc'
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact lvnd_lo (hnd b List.mem_cons_self)
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact lvnd_hi (hnd b List.mem_cons_self)
    · exact hnd c' (List.mem_cons_of_mem _ hc')
  | case3 b bs h =>
    intro hnd c hc
    rw [prep, dif_neg h] at hc
    exact hnd c hc

theorem staleCnt_split_head (L : Live κ α) (b : Block κ α) (bs : List (Block κ α)) :
    staleCnt L (⟨b.sep, loOf L b⟩ :: ⟨((medOf L b : α) : WithBot α), hiOf L b⟩ :: bs) =
      staleCnt L bs := by
  rw [staleCnt_cons, staleCnt_cons]
  have h1 : (loOf L b).countP (fun e => !decide (e.IsLive L)) = 0 := by
    rw [List.countP_eq_zero]; intro e he; simp [loOf_live e he]
  have h2 : (hiOf L b).countP (fun e => !decide (e.IsLive L)) = 0 := by
    rw [List.countP_eq_zero]; intro e he; simp [hiOf_live e he]
  simp only at h1 h2 ⊢
  rw [h1, h2]; simp

/-- **amortized cost of `prep`**: every split is paid by the potential -/
theorem prep_amortized {L : Live κ α} {M : ℕ} (hM : 1 ≤ M) :
    ∀ bs, (∀ c ∈ bs, LVnd L c) →
      (prep L M bs).2 + 2 * staleCnt L (prep L M bs).1 + spot M (prep L M bs).1 ≤
        2 * staleCnt L bs + spot M bs := by
  intro bs
  induction bs using prep.induct (L := L) (M := M) with
  | case1 => intro _; simp [prep, spot_nil]
  | case2 b bs h ih =>
    intro hnd
    rw [prep, dif_pos h]
    have hnd' : ∀ c ∈ (⟨b.sep, loOf L b⟩ :: ⟨((medOf L b : α) : WithBot α), hiOf L b⟩ :: bs :
        List (Block κ α)), LVnd L c := by
      intro c' hc'
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact lvnd_lo (hnd b List.mem_cons_self)
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact lvnd_hi (hnd b List.mem_cons_self)
      · exact hnd c' (List.mem_cons_of_mem _ hc')
    have k1 := ih hnd'
    have k2 := split_step hM h (hnd b List.mem_cons_self)
    rw [staleCnt_split_head, spot_cons, spot_cons] at k1
    dsimp only
    rw [staleCnt_cons, spot_cons]
    omega
  | case3 b bs h =>
    intro _
    rw [prep, dif_neg h]
    simp

theorem prepList_lvnd (L : Live κ α) (M : ℕ) :
    ∀ cnt bs, (∀ c ∈ bs, LVnd L c) → ∀ c ∈ (prepList L M cnt bs).1, LVnd L c := by
  intro cnt bs
  induction cnt, bs using prepList.induct (L := L) (M := M) with
  | case1 cnt => intro _ c hc; simp [prepList] at hc
  | case2 cnt b rest h => intro hnd c hc; rw [prepList, if_pos h] at hc; exact hnd c hc
  | case3 cnt b rest h hp => exact absurd hp (prep_ne_nil L M _ (List.cons_ne_nil _ _))
  | case4 cnt b rest h b' bs' hp ih =>
    intro hnd c hc
    rw [prepList, if_neg h] at hc
    split at hc
    · next hp' => exact absurd hp' (prep_ne_nil L M _ (List.cons_ne_nil _ _))
    · next b'' bs'' hp' =>
      rw [hp] at hp'
      obtain ⟨rfl, rfl⟩ := List.cons.inj hp'
      have hP := prep_lvnd L M (b :: rest) hnd
      rw [hp] at hP
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hP c List.mem_cons_self
      · exact ih (fun c' hc' => hP c' (List.mem_cons_of_mem _ hc')) c hc

theorem prepList_amortized {L : Live κ α} {M : ℕ} (hM : 1 ≤ M) :
    ∀ cnt bs, (∀ c ∈ bs, LVnd L c) →
      (prepList L M cnt bs).2 + 2 * staleCnt L (prepList L M cnt bs).1 +
        spot M (prepList L M cnt bs).1 ≤ 2 * staleCnt L bs + spot M bs := by
  intro cnt bs
  induction cnt, bs using prepList.induct (L := L) (M := M) with
  | case1 cnt => intro _; simp [prepList, spot_nil]
  | case2 cnt b rest h => intro _; rw [prepList, if_pos h]; simp
  | case3 cnt b rest h hp => exact absurd hp (prep_ne_nil L M _ (List.cons_ne_nil _ _))
  | case4 cnt b rest h b' bs' hp ih =>
    intro hnd
    rw [prepList, if_neg h]
    split
    · next hp' => exact absurd hp' (prep_ne_nil L M _ (List.cons_ne_nil _ _))
    · next b'' bs'' hp' =>
      rw [hp] at hp'
      obtain ⟨rfl, rfl⟩ := List.cons.inj hp'
      have hP := prep_lvnd L M (b :: rest) hnd
      rw [hp] at hP
      have k1 := prep_amortized hM (b :: rest) hnd
      rw [hp, staleCnt_cons, spot_cons] at k1
      have k2 := ih (fun c' hc' => hP c' (List.mem_cons_of_mem _ hc'))
      simp only
      rw [staleCnt_cons, spot_cons]
      omega

/-! ### The blocks taken by `pull` after preparation are small -/

/-- every block that `collect` examines (starting with `cnt` collected live entries) holds at
most `2M+1` live entries -/
def PrepOK (L : Live κ α) (M : ℕ) : ℕ → List (Block κ α) → Prop
  | _, [] => True
  | cnt, b :: bs => M < cnt ∨ ((liveOf L b.ents).length ≤ 2 * M + 1 ∧
      PrepOK L M (cnt + (liveOf L b.ents).length) bs)

theorem prep_head_small (L : Live κ α) (M : ℕ) :
    ∀ bs, (∀ c ∈ bs, LVnd L c) → ∀ c cs, (prep L M bs).1 = c :: cs →
      (liveOf L c.ents).length ≤ 2 * M + 1 := by
  intro bs
  induction bs using prep.induct (L := L) (M := M) with
  | case1 => intro _ c cs h; simp [prep] at h
  | case2 b bs h ih =>
    intro hnd c cs hc
    rw [prep, dif_pos h] at hc
    refine ih ?_ c cs hc
    intro c' hc'
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact lvnd_lo (hnd b List.mem_cons_self)
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact lvnd_hi (hnd b List.mem_cons_self)
    · exact hnd c' (List.mem_cons_of_mem _ hc')
  | case3 b bs h =>
    intro hnd c cs hc
    rw [prep, dif_neg h] at hc
    obtain ⟨rfl, rfl⟩ := List.cons.inj hc
    by_contra hbig
    apply h
    refine ⟨by omega, ?_⟩
    have hlo : (loOf L b).length = (liveOf L b.ents).length / 2 :=
      split_sizes (hnd b List.mem_cons_self) (by omega)
    intro h0
    rw [h0] at hlo
    simp at hlo
    omega

theorem prepList_prepOK (L : Live κ α) (M : ℕ) :
    ∀ cnt bs, (∀ c ∈ bs, LVnd L c) → PrepOK L M cnt (prepList L M cnt bs).1 := by
  intro cnt bs
  induction cnt, bs using prepList.induct (L := L) (M := M) with
  | case1 cnt => intro _; simp [prepList, PrepOK]
  | case2 cnt b rest h => intro _; rw [prepList, if_pos h]; exact Or.inl h
  | case3 cnt b rest h hp => exact absurd hp (prep_ne_nil L M _ (List.cons_ne_nil _ _))
  | case4 cnt b rest h b' bs' hp ih =>
    intro hnd
    rw [prepList, if_neg h]
    split
    · next hp' => exact absurd hp' (prep_ne_nil L M _ (List.cons_ne_nil _ _))
    · next b'' bs'' hp' =>
      rw [hp] at hp'
      obtain ⟨rfl, rfl⟩ := List.cons.inj hp'
      have hP := prep_lvnd L M (b :: rest) hnd
      rw [hp] at hP
      refine Or.inr ⟨prep_head_small L M (b :: rest) hnd b' bs' hp, ?_⟩
      exact ih (fun c' hc' => hP c' (List.mem_cons_of_mem _ hc'))

theorem collect_acc_le (L : Live κ α) (M : ℕ) :
    ∀ (bs : List (Block κ α)) (acc : List (Entry κ α)), PrepOK L M acc.length bs →
      acc.length ≤ M → (collect L M acc bs).1.length ≤ 3 * M + 1
  | [], acc, _, h => by simp [collect]; omega
  | b :: bs, acc, hP, h => by
      rcases hP with hP | ⟨hb, hP⟩
      · omega
      · simp only [collect]
        split_ifs with hc
        · simp only [List.length_append]; omega
        · refine collect_acc_le L M bs _ ?_ (by simp at hc ⊢; omega)
          simpa using hP

theorem Ssum_two_mul_add_one {M : ℕ} (hM : 1 ≤ M) : Ssum M (2 * M + 1) ≤ 2 := by
  have h0 : Ssum M (2 * M - 1) = 0 := Ssum_of_le (by omega)
  have hle : ∀ i, i ≤ 3 * M → ell M i ≤ 1 := by
    intro i hi
    unfold ell
    have hq : i / M ≤ 3 := Nat.div_le_of_le_mul (by linarith)
    calc Nat.log 2 (i / M) ≤ Nat.log 2 3 := Nat.log_mono_right hq
      _ = 1 := by decide
  have e : 2 * M + 1 = (2 * M - 1) + 1 + 1 := by omega
  rw [e]
  simp only [Ssum]
  have h1 := hle (2 * M - 1 + 1) (by omega)
  have h2 := hle (2 * M - 1 + 1 + 1) (by omega)
  omega

/-! ### Amortized cost of `pullL` -/

/-- `pull` (one unit per removed block) on a prepared structure -/
theorem pull_lazy_amortized {L : Live κ α} {D : DStr κ α} {kof : α → κ} (hwf : WF L D)
    (hK : KeyInj L kof) (hid : IdsNodup D) (hM : 1 ≤ D.M) (hP : PrepOK L D.M 0 D.blocks) :
    (pull 1 L D).2.2.2.2 + potL (pull 1 L D).2.2.1 (pull 1 L D).2.2.2.1 ≤
      potL L D + (735 * D.M + 950) := by
  have hpost := pull_post 1 hwf hK hid hM
  obtain ⟨hne, hint⟩ := hwf
  unfold pull at hpost ⊢
  obtain ⟨pre, hbs, hacc, hk, hsc, hrem, hpre⟩ := collect_spec L D.M D.blocks []
  simp only [List.nil_append] at hacc
  set acc := (collect L D.M [] D.blocks).1 with hacc_def
  set rem := (collect L D.M [] D.blocks).2.1 with hrem_def
  have hacc_le : acc.length ≤ 3 * D.M + 1 :=
    collect_acc_le L D.M D.blocks [] (by simpa using hP) (by simp)
  have hsc' : (collect L D.M [] D.blocks).2.2.2 = acc.length + staleCnt L pre := by
    rw [hsc, sum_length_allEnts, length_allEnts L pre, ← hacc]
  have hpotD : potL L D = 2 * (staleCnt L pre + staleCnt L rem) + spot D.M pre + spot D.M rem := by
    unfold potL; rw [hbs, staleCnt_append, spot_append]; ring
  have hpre3 := three_mul_length_le_spot D.M pre
  by_cases hsmall : acc.length ≤ D.M
  · rw [ite_eq_left hsmall] at hpost ⊢
    dsimp only at hpost ⊢
    have hpot' : potL (clearKeys L (acc.map (·.key))) ⟨D.M, D.Bd, [⟨⊥, []⟩]⟩ = 3 := by
      simp [potL, staleCnt, allEnts, spot, bw, Ssum]
    rw [hpot', hsc', hk]
    omega
  · rw [ite_eq_right hsmall] at hpost ⊢
    dsimp only at hpost ⊢
    obtain ⟨hlen, hxB, -, -, -⟩ := hpost
    set x := (selectC (acc.map (·.val)) D.M).1 with hx
    set S := acc.filter (fun e => decide (e.val < x)) with hS
    set R := acc.filter (fun e => decide (x ≤ e.val)) with hR
    set ks := S.map (·.key) with hks
    have hM' : D.M < acc.length := by omega
    have hsel := selectC_cost (acc.map (·.val)) (k := D.M) (by simpa using hM')
    simp only [List.length_map] at hsel
    have hSR : S.length + R.length = acc.length := by
      rw [hS, hR, ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
      have := List.length_eq_countP_add_countP (l := acc) (fun e : Entry κ α => e.val < x)
      rw [this]; congr 1; apply List.countP_congr; intro e _; simp
    have hxneq : x ≠ D.Bd := by
      have hkth : IsKth (acc.map (·.val)) D.M x := selectC_isKth _ (by simpa using hM')
      obtain ⟨e0, he0, hex⟩ := List.mem_map.mp hkth.1
      rw [hacc] at he0
      obtain ⟨⟨b, hb, heb⟩, hl⟩ := mem_liveVals.mp he0
      have := (hint.bounds b (by rw [hbs]; exact List.mem_append_left _ hb) e0 heb hl).2
      intro h; rw [hex, h] at this
      exact absurd this (lt_irrefl _)
    have hSlen : S.length = D.M := by
      rcases hxB with h | h
      · exact absurd h hxneq
      · simpa [hks] using h
    have hRlive : ∀ e ∈ R, e.IsLive (clearKeys L ks) := by
      intro e he
      have he' := (List.mem_filter.mp he)
      rw [hacc] at he'
      have hl := (mem_liveVals.mp he'.1).2
      rw [isLive_clearKeys]
      refine ⟨hl, fun hk' => ?_⟩
      obtain ⟨e', he's, hkk⟩ := List.mem_map.mp hk'
      have h1 := List.mem_filter.mp he's
      rw [hacc] at h1
      have hl' := (mem_liveVals.mp h1.1).2
      have := (live_key_unique hl hl' hkk.symm).2
      have hxe : x ≤ e.val := by simpa using he'.2
      have hex : e'.val < x := by simpa using h1.2
      rw [this] at hxe
      exact absurd hex (not_lt.mpr hxe)
    have hstaleR : staleCnt (clearKeys L ks) [⟨⊥, R⟩] = 0 := by
      simp only [staleCnt, allEnts, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil]
      rw [List.countP_eq_zero]
      intro e he; simp [hRlive e he]
    have hstaleRem : staleCnt (clearKeys L ks) rem ≤ staleCnt L rem := by
      unfold staleCnt
      apply List.countP_mono_left
      intro e he h
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h ⊢
      intro hl
      apply h
      rw [isLive_clearKeys]
      refine ⟨hl, fun hk' => ?_⟩
      obtain ⟨e', he's, hkk⟩ := List.mem_map.mp hk'
      have h1 := List.mem_filter.mp he's
      rw [hacc] at h1
      obtain ⟨⟨b', hb', heb'⟩, hl'⟩ := mem_liveVals.mp h1.1
      have hide := (live_key_unique hl hl' hkk.symm).1
      have hnd := hid
      unfold IdsNodup at hnd
      rw [hbs] at hnd
      simp only [allEnts, List.map_append, List.flatten_append] at hnd
      have hnd' := List.nodup_append.mp hnd
      exact hnd'.2.2 _ (List.mem_map.mpr ⟨e', (show e' ∈ allEnts pre from
        mem_allEnts.mpr ⟨b', hb', heb'⟩), rfl⟩) _ (List.mem_map.mpr ⟨e, he, rfl⟩) hide.symm
    have hRS : Ssum D.M R.length ≤ 2 :=
      le_trans (Ssum_mono (by omega)) (Ssum_two_mul_add_one hM)
    have hpot' : potL (clearKeys L ks) ⟨D.M, D.Bd, ⟨⊥, R⟩ :: rem⟩ ≤
        2 * staleCnt L rem + (3 + 420 * (R.length - D.M) + 210 * 2) + spot D.M rem := by
      unfold potL
      simp only
      rw [show (⟨⊥, R⟩ :: rem : List (Block κ α)) = [⟨⊥, R⟩] ++ rem from rfl, staleCnt_append,
        spot_append, hstaleR]
      simp only [spot, bw, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      omega
    rw [hsc', hk]
    omega

theorem lvnd_of_inv {L : Live κ α} {D : DStr κ α} {kof : α → κ} (hK : KeyInj L kof)
    (hid : IdsNodup D) : ∀ c ∈ D.blocks, LVnd L c := by
  intro c hc
  unfold LVnd
  have hsub : (c.ents.map (·.id)).Sublist ((allEnts D.blocks).map (·.id)) := by
    apply List.Sublist.map
    unfold allEnts
    exact List.sublist_flatten_of_mem (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hnd : ((liveOf L c.ents).map (·.id)).Nodup :=
    ((List.filter_sublist).map _ |>.trans hsub).nodup hid
  exact nodup_vals_of_live hK hnd (fun e he => (mem_liveOf.mp he).2)

/-- **Amortized cost of `pullL`**: `cost + Φ' ≤ Φ + 735 M + 950`. -/
theorem pullL_amortized {L : Live κ α} {D : DStr κ α} {kof : α → κ} (hwf : WF L D)
    (hK : KeyInj L kof) (hid : IdsNodup D) (hM : 1 ≤ D.M) :
    (pullL 1 L D).2.2.2.2 + potL (pullL 1 L D).2.2.1 (pullL 1 L D).2.2.2.1 ≤
      potL L D + (735 * D.M + 950) := by
  have hnd := lvnd_of_inv hK hid
  have h1 := prepList_amortized hM 0 D.blocks hnd
  have hP := prepList_prepOK L D.M 0 D.blocks hnd
  have h2 := pull_lazy_amortized (D := prepD L D) (wf_prepD hwf) hK (idsNodup_prepD hid) hM hP
  have e1 : potL L (prepD L D) = 2 * staleCnt L (prepList L D.M 0 D.blocks).1 +
      spot D.M (prepList L D.M 0 D.blocks).1 := rfl
  have e2 : potL L D = 2 * staleCnt L D.blocks + spot D.M D.blocks := rfl
  have e3 : (prepD L D).M = D.M := rfl
  rw [e1, e3] at h2
  rw [pullL_eq, e2]
  dsimp only
  omega

/-! ## Insert without splitting -/

/-- a parameter so large that `fixBlock` never splits after one insertion -/
def bigM (D : DStr κ α) : ℕ := (allEnts D.blocks).length + 1

/-- binary search over `n` blocks of the stack: `⌊log₂ n⌋ + 1` probes -/
def bsCost (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- **insertL**: binary search, then prepend the entry to its block (no split). -/
def insertL (L : Live κ α) (fresh : ℕ) (D : DStr κ α) (v : κ) (lam : α) :
    Live κ α × ℕ × DStr κ α × ℕ :=
  ((insert 0 L fresh { D with M := bigM D } v lam).1,
   (insert 0 L fresh { D with M := bigM D } v lam).2.1,
   { (insert 0 L fresh { D with M := bigM D } v lam).2.2.1 with M := D.M },
   if skipIns L v lam then 2 else bsCost D.blocks.length + 3)

/-- **Correctness of `insertL`** (views, well-formedness, freshness, frame), from `insert_spec`. -/
theorem insertL_spec {L : Live κ α} {fresh : ℕ} {D : DStr κ α} {v : κ} {lam : α}
    (hwf : WF L D) (hfr : FreshOK fresh D) (hB : lam < D.Bd)
    (hdisc : skipIns L v lam = true → HasKey L D v) :
    (∀ y, view (insertL L fresh D v lam).1 (insertL L fresh D v lam).2.2.1 y =
        if y = v then some (insVal (view L D v) lam) else view L D y) ∧
    WF (insertL L fresh D v lam).1 (insertL L fresh D v lam).2.2.1 ∧
    FreshOK (insertL L fresh D v lam).2.1 (insertL L fresh D v lam).2.2.1 ∧
    fresh ≤ (insertL L fresh D v lam).2.1 ∧
    (insertL L fresh D v lam).2.2.1.M = D.M ∧ (insertL L fresh D v lam).2.2.1.Bd = D.Bd ∧
    (∀ (D' : DStr κ α), FreshOK fresh D' → ∀ y, y ≠ v →
        view (insertL L fresh D v lam).1 D' y = view L D' y) := by
  have h := insert_spec 0 (D := { D with M := bigM D }) hwf hfr hB hdisc
  obtain ⟨h1, h2, h3, h4, -, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, rfl, h6, h7⟩

theorem fixBlock_small (T : ℕ) {L : Live κ α} {M : ℕ} {b : Block κ α}
    (h : b.ents.length ≤ 2 * M + 1) : fixBlock T L M b = ([b], 1) := by
  unfold fixBlock; rw [if_pos h]

/-- with a large parameter, `addTo` prepends the entry to exactly one block -/
theorem addTo_noSplit (T : ℕ) {L : Live κ α} {M : ℕ} {lam : α} {e : Entry κ α} :
    ∀ bs : List (Block κ α), bs ≠ [] → (∀ c ∈ bs, c.ents.length + 1 ≤ 2 * M + 1) →
      ∃ pre c post, bs = pre ++ c :: post ∧
        (addTo T L M lam e bs).1 = pre ++ ⟨c.sep, e :: c.ents⟩ :: post
  | [], h, _ => absurd rfl h
  | [b], _, hs => by
      refine ⟨[], b, [], rfl, ?_⟩
      simp only [addTo]
      rw [fixBlock_small T (by simpa using hs b (List.mem_singleton_self _))]
      rfl
  | b :: b' :: bs, _, hs => by
      simp only [addTo]
      split_ifs with hsep
      · obtain ⟨pre, c, post, h1, h2⟩ := addTo_noSplit T (b' :: bs) (List.cons_ne_nil _ _)
          (fun c hc => hs c (List.mem_cons_of_mem _ hc))
        exact ⟨b :: pre, c, post, by rw [h1]; rfl, by rw [h2]; rfl⟩
      · refine ⟨[], b, b' :: bs, rfl, ?_⟩
        rw [fixBlock_small T (by simpa using hs b List.mem_cons_self)]
        rfl

theorem length_le_allEnts {bs : List (Block κ α)} {c : Block κ α} (hc : c ∈ bs) :
    c.ents.length ≤ (allEnts bs).length := by
  unfold allEnts
  exact (List.sublist_flatten_of_mem (List.mem_map.mpr ⟨c, hc, rfl⟩)).length_le

/-- **Amortized cost of `insertL`**: binary search plus `O(log (|D|/M))`. -/
theorem insertL_amortized {L : Live κ α} {fresh : ℕ} {D : DStr κ α} {v : κ} {lam : α}
    (hwf : WF L D) (hfr : FreshOK fresh D) (hid : IdsNodup D) :
    (insertL L fresh D v lam).2.2.2 +
        potL (insertL L fresh D v lam).1 (insertL L fresh D v lam).2.2.1 ≤
      potL L D + bsCost D.blocks.length + 425 + 210 * ell D.M ((allEnts D.blocks).length + 1) := by
  unfold insertL DB.insert
  by_cases hskip : skipIns L v lam = true
  · simp only [hskip, if_true]
    refine le_trans (Nat.add_le_add_left (le_of_eq (show potL L _ = potL L D from rfl)) 2) ?_
    omega
  · simp only [hskip, Bool.false_eq_true, if_false]
    set L' := Function.update L v (some (fresh, lam)) with hL'
    set e : Entry κ α := ⟨fresh, v, lam⟩ with he
    obtain ⟨pre, c, post, hbs, hres⟩ := addTo_noSplit 0 (L := L') (M := bigM D) (lam := lam)
      (e := e) D.blocks hwf.1 (fun c hc => by
        have := length_le_allEnts hc; unfold bigM; omega)
    have hcm : c ∈ D.blocks := by rw [hbs]; simp
    have hcl := length_le_allEnts hcm
    unfold potL
    simp only
    rw [hres]
    -- stale entries: the new entry is live, the old entries gain at most one stale entry
    have hst : staleCnt L' (pre ++ ⟨c.sep, e :: c.ents⟩ :: post) ≤ staleCnt L D.blocks + 1 := by
      have h1 : staleCnt L' (pre ++ ⟨c.sep, e :: c.ents⟩ :: post) = staleCnt L' D.blocks := by
        rw [hbs, staleCnt_append, staleCnt_append, staleCnt_cons, staleCnt_cons]
        have : (e :: c.ents).countP (fun x => !decide (x.IsLive L')) =
            c.ents.countP (fun x => !decide (x.IsLive L')) := by
          rw [List.countP_cons]
          have hl : e.IsLive L' := by simp [Entry.IsLive, hL', he]
          simp [hl]
        simp only at this ⊢
        rw [this]
      rw [h1]
      exact staleCnt_update_le hfr hid
    have hsp : spot D.M (pre ++ ⟨c.sep, e :: c.ents⟩ :: post) ≤
        spot D.M D.blocks + 420 + 210 * ell D.M ((allEnts D.blocks).length + 1) := by
      have hA := ell_mono (M := D.M) (show c.ents.length + 1 ≤ (allEnts D.blocks).length + 1 by omega)
      generalize ell D.M ((allEnts D.blocks).length + 1) = E at hA ⊢
      rw [hbs, spot_append, spot_append, spot_cons, spot_cons]
      simp only [bw, List.length_cons, Ssum]
      omega
    have hsz : (pre ++ ⟨c.sep, e :: c.ents⟩ :: post).length = D.blocks.length := by
      rw [hbs]; simp
    omega

/-! ## Merge: groups of child blocks move to the parameter `M ≥ 3M'` -/

/-- **one group**: `A < M/3` entries accumulated in front of a child block of size `s` -/
theorem group_weight {M M' A s : ℕ} (hM' : 1 ≤ M') (h3 : 3 * M' ≤ M) (hA : 3 * A < M) :
    420 * (A + s - M) + 210 * Ssum M (A + s) ≤ 420 * (s - M') + 210 * Ssum M' s := by
  by_cases hsm : A + s < 2 * M
  · rw [Ssum_of_le hsm]
    have := Nat.zero_le (Ssum M' s)
    omega
  · have hM : 0 < M := by omega
    have h1 := Ssum_add_le M s A
    rw [show s + A = A + s by omega] at h1
    have h2 := Ssum_Mchange hM' h3 s
    set E := ell M (A + s) with hE
    set q := (A + s) / M with hq
    have hEq : E ≤ q := Nat.log_le_self 2 _
    have hqM : q * M ≤ A + s := Nat.div_mul_le_self _ _
    have hq1 : 1 ≤ q := Nat.le_div_iff_mul_le hM |>.mpr (by omega)
    have hAE : A * E ≤ A * q := Nat.mul_le_mul_left _ hEq
    have hAq : 3 * (A * q) < M * q := by
      have := Nat.mul_lt_mul_of_pos_right hA (show 0 < q by omega)
      linarith
    have hMq : M * q = q * M := Nat.mul_comm _ _
    omega

theorem bw_group {M M' : ℕ} {c b : Block κ α} (hM' : 1 ≤ M') (h3 : 3 * M' ≤ M)
    (hc : 3 * c.ents.length < M) (sep : WithBot α) :
    bw M ⟨sep, c.ents ++ b.ents⟩ ≤ bw M' b := by
  unfold bw
  simp only [List.length_append]
  have := group_weight (A := c.ents.length) (s := b.ents.length) hM' h3 hc
  omega

theorem bw_anti {M M' : ℕ} {b : Block κ α} (hM' : 1 ≤ M') (h3 : 3 * M' ≤ M) :
    bw M b ≤ bw M' b := by
  have := bw_group (c := (⟨⊥, []⟩ : Block κ α)) (b := b) hM' h3 (by simp; omega) b.sep
  simpa using this

/-- the structural potential of the groups -/
theorem spot_groupAux {M M' : ℕ} (hM' : 1 ≤ M') (h3 : 3 * M' ≤ M) :
    ∀ (cur : Option (Block κ α)) (bs : List (Block κ α)),
      (∀ c0, cur = some c0 → c0.ents.length < M / 3) →
      spot M (groupAux (M / 3) cur bs) + 3 * bs.length ≤
        spot M' bs + 3 * (groupAux (M / 3) cur bs).length
  | none, [], _ => by simp [groupAux, spot_nil]
  | some c, [], hc => by
      have h := hc c rfl
      simp only [groupAux, spot_cons, spot_nil, List.length_cons, List.length_nil]
      unfold bw
      rw [Ssum_of_le (by omega)]
      omega
  | none, b :: bs, _ => by
      simp only [groupAux]
      split_ifs with hg
      · have ih := spot_groupAux hM' h3 none bs (by simp)
        have := bw_anti (b := b) hM' h3
        rw [spot_cons, spot_cons, List.length_cons, List.length_cons]
        omega
      · have ih := spot_groupAux hM' h3 (some b) bs (by
          intro c0 h; cases h; omega)
        have := three_le_bw M' b
        rw [spot_cons, List.length_cons]
        omega
  | some c, b :: bs, hc => by
      have hcl := hc c rfl
      simp only [groupAux]
      split_ifs with hg
      · have ih := spot_groupAux hM' h3 none bs (by simp)
        have := bw_group (c := c) (b := b) hM' h3 (by omega) c.sep
        rw [spot_cons, spot_cons, List.length_cons, List.length_cons]
        omega
      · have ih := spot_groupAux hM' h3 (some ⟨c.sep, c.ents ++ b.ents⟩) bs (by
          intro c0 h; cases h; simp only [List.length_append] at hg ⊢; omega)
        have := three_le_bw M' b
        rw [spot_cons, List.length_cons]
        omega

/-- **Amortized cost of `merge`** (one unit per stack push) under the lazy potential:
`cost + Φ(merged) ≤ Φ(D) + Φ(D') + 4·#groups + 4`; the number of groups is at most
`E(D')/(M/3) + 1` (`groupAux_count`). -/
theorem mergeL_amortized {L : Live κ α} {D D' : DStr κ α} (hne : D.blocks ≠ []) (hM' : 1 ≤ D'.M)
    (h3 : 3 * D'.M ≤ D.M) :
    (merge 1 D D').2 + potL L (merge 1 D D').1 ≤
      potL L D + potL L D' + 4 * (groupAux (D.M / 3) none D'.blocks).length + 4 := by
  rcases hD : D.blocks with _ | ⟨f, rest⟩
  · exact absurd hD hne
  have hmD : merge 1 D D' = ({ D with blocks := groupAux (D.M / 3) none D'.blocks ++
        (if ltSep D'.Bd (nextSep rest (D.Bd : WithBot α))
          then ⟨(D'.Bd : WithBot α), f.ents⟩ :: rest else rest) },
      D'.blocks.length + 1 * ((groupAux (D.M / 3) none D'.blocks).length + 2) + 2) := by
    unfold merge; rw [hD]
  rw [hmD]
  unfold potL
  simp only
  set gs := groupAux (D.M / 3) none D'.blocks with hgs
  have hsg := spot_groupAux (M := D.M) (M' := D'.M) hM' h3 none D'.blocks (by simp)
  rw [← hgs] at hsg
  have hstg : staleCnt L gs = staleCnt L D'.blocks := by
    rw [hgs, staleCnt_groupAux]; simp
  have htail : staleCnt L (if ltSep D'.Bd (nextSep rest (D.Bd : WithBot α))
      then ⟨(D'.Bd : WithBot α), f.ents⟩ :: rest else rest) ≤ staleCnt L D.blocks ∧
      spot D.M (if ltSep D'.Bd (nextSep rest (D.Bd : WithBot α))
        then ⟨(D'.Bd : WithBot α), f.ents⟩ :: rest else rest) ≤ spot D.M D.blocks := by
    rw [hD]
    split_ifs
    · rw [staleCnt_cons, staleCnt_cons, spot_cons, spot_cons]
      simp [bw]
    · rw [staleCnt_cons, spot_cons]; omega
  rw [staleCnt_append, spot_append, hstg]
  omega

/-! ## Auxiliary invariants (distinct ids, fresh ids, key injectivity) -/

/-- the entries of the structure after `pull` are a sub-permutation of the old entries -/
theorem pull_subperm (T : ℕ) (L : Live κ α) (D : DStr κ α) :
    (allEnts (pull T L D).2.2.2.1.blocks).Subperm (allEnts D.blocks) := by
  unfold pull
  obtain ⟨pre, hbs, hacc, -, -, -, -⟩ := collect_spec L D.M D.blocks []
  simp only [List.nil_append] at hacc
  split_ifs
  · simp only [allEnts, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil]
    exact List.nil_subperm
  · simp only
    have hsp : (allEnts (⟨⊥, (collect L D.M [] D.blocks).1.filter (fun e => decide
        ((selectC ((collect L D.M [] D.blocks).1.map (·.val)) D.M).1 ≤ e.val))⟩ ::
          (collect L D.M [] D.blocks).2.1)).Sublist (allEnts D.blocks) := by
      conv_rhs => rw [hbs]
      simp only [allEnts, List.map_cons, List.flatten_cons, List.map_append, List.flatten_append]
      apply List.Sublist.append _ (List.Sublist.refl _)
      rw [hacc]
      exact List.filter_sublist.trans (liveVals_sublist_allEnts L pre)
    exact hsp.subperm

theorem pull_live_clear (T : ℕ) (L : Live κ α) (D : DStr κ α) :
    (pull T L D).2.2.1 = clearKeys L (pull T L D).1 := by
  unfold pull; split_ifs <;> rfl

theorem pullL_aux {L : Live κ α} {D : DStr κ α} {kof : α → κ} {fresh : ℕ} (hK : KeyInj L kof)
    (hid : IdsNodup D) (hfr : FreshOK fresh D) :
    IdsNodup (pullL 1 L D).2.2.2.1 ∧ FreshOK fresh (pullL 1 L D).2.2.2.1 ∧
      KeyInj (pullL 1 L D).2.2.1 kof := by
  have h1 := pull_subperm 1 L (prepD L D)
  have h2 := prepList_subperm L D.M 0 D.blocks
  have h12 : (allEnts (pullL 1 L D).2.2.2.1.blocks).Subperm (allEnts D.blocks) := h1.trans h2
  refine ⟨subperm_nodup' (subperm_map' _ h12) hid, fun x hx => hfr x (h12.subset hx), ?_⟩
  rw [pullL_eq, pull_live_clear]
  exact keyInj_clearKeys hK

theorem insertL_aux {L : Live κ α} {fresh : ℕ} {D : DStr κ α} {v : κ} {lam : α} {kof : α → κ}
    (hfr : FreshOK fresh D) (hid : IdsNodup D) (hK : KeyInj L kof) (hkv : kof lam = v) :
    IdsNodup (insertL L fresh D v lam).2.2.1 ∧ KeyInj (insertL L fresh D v lam).1 kof := by
  refine ⟨insert_idsNodup 0 (D := { D with M := bigM D }) hfr hid, ?_⟩
  unfold insertL DB.insert
  split_ifs
  · exact hK
  · exact keyInj_update hK hkv

/-- `merge` keeps distinct ids (for disjoint id sets) and fresh ids -/
theorem merge_ids (T : ℕ) {D D' : DStr κ α} {fresh : ℕ} (hne : D.blocks ≠ []) (hid : IdsNodup D)
    (hid' : IdsNodup D') (hdisj : ∀ x ∈ allEnts D.blocks, ∀ y ∈ allEnts D'.blocks, x.id ≠ y.id)
    (hfr : FreshOK fresh D) (hfr' : FreshOK fresh D') :
    IdsNodup (merge T D D').1 ∧ FreshOK fresh (merge T D D').1 := by
  rcases hD : D.blocks with _ | ⟨f, rest⟩
  · exact absurd hD hne
  have hmD : (merge T D D').1 = { D with blocks := groupAux (D.M / 3) none D'.blocks ++
        (if ltSep D'.Bd (nextSep rest (D.Bd : WithBot α))
          then ⟨(D'.Bd : WithBot α), f.ents⟩ :: rest else rest) } := by
    unfold merge; rw [hD]
  rw [hmD]
  set gs := groupAux (D.M / 3) none D'.blocks with hgs
  have hgsE : ∀ x, x ∈ allEnts gs ↔ x ∈ allEnts D'.blocks := by
    intro x; rw [hgs, mem_allEnts_groupAux]; simp
  have hgsperm : (allEnts gs).Perm (allEnts D'.blocks) := by
    have key : ∀ (cur : Option (Block κ α)) (bs : List (Block κ α)),
        (allEnts (groupAux (D.M / 3) cur bs)).Perm
          ((match cur with | none => [] | some c0 => c0.ents) ++ allEnts bs) := by
      intro cur bs
      induction bs generalizing cur with
      | nil => cases cur <;> simp [groupAux, allEnts]
      | cons b0 bs ih =>
        cases cur with
        | none =>
          simp only [groupAux]
          split_ifs
          · have := ih none
            simp only [allEnts, List.map_cons, List.flatten_cons] at this ⊢
            simpa using List.Perm.append_left b0.ents this
          · have := ih (some b0)
            simpa [allEnts] using this
        | some c0 =>
          simp only [groupAux]
          split_ifs
          · have := ih none
            simp only [allEnts, List.map_cons, List.flatten_cons] at this ⊢
            simpa [List.append_assoc] using List.Perm.append_left (c0.ents ++ b0.ents) this
          · have := ih (some ⟨c0.sep, c0.ents ++ b0.ents⟩)
            simpa [allEnts, List.append_assoc] using this
    simpa using key none D'.blocks
  have htailE : ∀ x, x ∈ allEnts (if ltSep D'.Bd (nextSep rest (D.Bd : WithBot α))
      then ⟨(D'.Bd : WithBot α), f.ents⟩ :: rest else rest) → x ∈ allEnts D.blocks := by
    intro x hx
    rw [hD]
    split_ifs at hx
    · simpa [allEnts] using hx
    · simp only [allEnts, List.map_cons, List.flatten_cons, List.mem_append] at hx ⊢
      exact Or.inr hx
  refine ⟨?_, ?_⟩
  · unfold IdsNodup
    simp only
    rw [allEnts, List.map_append, List.flatten_append, List.map_append, List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · exact (hgsperm.map _).nodup_iff.mpr hid'
    · have hsub : ((if ltSep D'.Bd (nextSep rest (D.Bd : WithBot α))
          then ⟨(D'.Bd : WithBot α), f.ents⟩ :: rest else rest).map (·.ents)).flatten.Sublist
          (allEnts D.blocks) := by
        rw [hD]
        split_ifs
        · simp [allEnts]
        · simp only [allEnts, List.map_cons, List.flatten_cons]
          exact List.sublist_append_right _ _
      exact (hsub.map _).nodup hid
    · intro a ha b hb hab
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
      exact hdisj y (htailE y hy) x ((hgsE x).mp hx) hab.symm
  · intro x hx
    rw [allEnts, List.map_append, List.flatten_append, List.mem_append] at hx
    rcases hx with hx | hx
    · exact hfr' x ((hgsE x).mp hx)
    · exact hfr x (htailE x hx)

/-! ## Deletion, new structures, and the family of structures sharing `L` -/

/-- **Amortized cost of `deleteKeys`** under the lazy potential -/
theorem deleteKeys_amortizedL {L : Live κ α} {D : DStr κ α} {ks : List κ} (hid : IdsNodup D) :
    (deleteKeys L ks).2 + potL (deleteKeys L ks).1 D ≤ potL L D + 3 * ks.length + 1 := by
  have h := staleCnt_clearKeys_le (L := L) (ks := ks) (os := D.blocks) hid
  simp only [deleteKeys, potL]
  omega

/-- a new, empty structure has lazy potential `3` -/
theorem potL_new (L : Live κ α) (M : ℕ) (Bd : α) : potL L ⟨M, Bd, [⟨⊥, []⟩]⟩ = 3 := by
  simp [potL, staleCnt, allEnts, spot, bw, Ssum]

/-- an `insertL` makes at most one entry of the other structures stale -/
theorem staleCnt_insertL_others {L : Live κ α} {fresh : ℕ} {D : DStr κ α} {v : κ} {lam : α}
    {os : List (Block κ α)} (hfr : ∀ x ∈ allEnts os, x.id < fresh)
    (hnd : ((allEnts os).map (·.id)).Nodup) :
    staleCnt (insertL L fresh D v lam).1 os ≤ staleCnt L os + 1 :=
  staleCnt_insert_others 0 (D := { D with M := bigM D }) hfr hnd

/-- a `pullL` does not change the stale count of the other structures -/
theorem staleCnt_pullL_others {L : Live κ α} {D : DStr κ α} {os : List (Block κ α)}
    (hwf : WF L D) (hdisj : ∀ x ∈ allEnts D.blocks, ∀ z ∈ allEnts os, x.id ≠ z.id) :
    staleCnt (pullL 1 L D).2.2.1 os = staleCnt L os := by
  rw [pullL_eq]
  exact staleCnt_pull_others 1 (wf_prepD hwf) (fun x hx z hz =>
    hdisj x ((prepList_subperm L D.M 0 D.blocks).subset hx) z hz)

theorem wf_insertL_others {L : Live κ α} {fresh : ℕ} {D D₂ : DStr κ α} {v : κ} {lam : α}
    (hwf : WF L D₂) (hfr : FreshOK fresh D₂) : WF (insertL L fresh D v lam).1 D₂ :=
  wf_insert_others 0 (D := { D with M := bigM D }) hwf hfr

theorem wf_pullL_others {L : Live κ α} {D D₂ : DStr κ α} (hwf : WF L D) (hwf₂ : WF L D₂) :
    WF (pullL 1 L D).2.2.1 D₂ := by
  rw [pullL_eq]
  exact wf_pull_others 1 (wf_prepD hwf) hwf₂

/-! ## O(1)-amortized merge: an entry potential

`epot D = ⌊12 · |entries of D| / M⌋`.  A child structure with parameter `M' ≤ M/3` holds three
times as much entry potential as the same entries in the parent, which pays for the `O(E'/M + 1)`
groups of a merge; `potM = potL + epot`. -/

/-- entry potential -/
def epot (D : DStr κ α) : ℕ := 12 * (allEnts D.blocks).length / D.M

/-- the potential with the entry term -/
def potM (L : Live κ α) (D : DStr κ α) : ℕ := potL L D + epot D

theorem groupAux_allEnts_perm (g : ℕ) :
    ∀ (cur : Option (Block κ α)) (bs : List (Block κ α)),
      (allEnts (groupAux g cur bs)).Perm
        ((match cur with | none => [] | some c0 => c0.ents) ++ allEnts bs) := by
  intro cur bs
  induction bs generalizing cur with
  | nil => cases cur <;> simp [groupAux, allEnts]
  | cons b0 bs ih =>
    cases cur with
    | none =>
      simp only [groupAux]
      split_ifs
      · have := ih none
        simp only [allEnts, List.map_cons, List.flatten_cons] at this ⊢
        simpa using List.Perm.append_left b0.ents this
      · have := ih (some b0)
        simpa [allEnts] using this
    | some c0 =>
      simp only [groupAux]
      split_ifs
      · have := ih none
        simp only [allEnts, List.map_cons, List.flatten_cons] at this ⊢
        simpa [List.append_assoc] using List.Perm.append_left (c0.ents ++ b0.ents) this
      · have := ih (some ⟨c0.sep, c0.ents ++ b0.ents⟩)
        simpa [allEnts, List.append_assoc] using this

theorem merge_entries_length (T : ℕ) {D D' : DStr κ α} (hne : D.blocks ≠ []) :
    (allEnts (merge T D D').1.blocks).length ≤
      (allEnts D.blocks).length + (allEnts D'.blocks).length ∧ (merge T D D').1.M = D.M := by
  rcases hD : D.blocks with _ | ⟨f, rest⟩
  · exact absurd hD hne
  have hmD : (merge T D D').1 = { D with blocks := groupAux (D.M / 3) none D'.blocks ++
        (if ltSep D'.Bd (nextSep rest (D.Bd : WithBot α))
          then ⟨(D'.Bd : WithBot α), f.ents⟩ :: rest else rest) } := by
    unfold merge; rw [hD]
  rw [hmD]
  refine ⟨?_, rfl⟩
  simp only
  have hp := (groupAux_allEnts_perm (D.M / 3) none D'.blocks).length_eq
  simp only [List.nil_append] at hp
  have ht : (allEnts (if ltSep D'.Bd (nextSep rest (D.Bd : WithBot α))
      then ⟨(D'.Bd : WithBot α), f.ents⟩ :: rest else rest)).length ≤ (allEnts (f :: rest)).length := by
    split_ifs
    · simp [allEnts]
    · simp [allEnts]
  have e : allEnts (groupAux (D.M / 3) none D'.blocks ++ (if ltSep D'.Bd (nextSep rest (D.Bd : WithBot α))
      then ⟨(D'.Bd : WithBot α), f.ents⟩ :: rest else rest)) =
      allEnts (groupAux (D.M / 3) none D'.blocks) ++ allEnts (if ltSep D'.Bd (nextSep rest (D.Bd : WithBot α))
      then ⟨(D'.Bd : WithBot α), f.ents⟩ :: rest else rest) := by
    simp [allEnts]
  rw [e, List.length_append, hp]
  omega

/-- **O(1)-amortized merge**: `cost + Φ(merged) ≤ Φ(D) + Φ(D') + 14` (for `3M' ≤ M`, `M' ≥ 1`) -/
theorem mergeM_amortized {L : Live κ α} {D D' : DStr κ α} (hne : D.blocks ≠ []) (hM' : 1 ≤ D'.M)
    (h3 : 3 * D'.M ≤ D.M) :
    (merge 1 D D').2 + potM L (merge 1 D D').1 ≤ potM L D + potM L D' + 14 := by
  have h1 := mergeL_amortized (L := L) hne hM' h3
  obtain ⟨hlen, hM⟩ := merge_entries_length 1 (D' := D') hne
  set G := (groupAux (D.M / 3) none D'.blocks).length with hG
  set E := (allEnts D.blocks).length with hE
  set E' := (allEnts D'.blocks).length with hE'
  set Em := (allEnts (merge 1 D D').1.blocks).length with hEm
  set M := D.M with hMdef
  set M' := D'.M with hM'def
  have hM3 : 3 ≤ M := by omega
  have hMpos : 0 < M := by omega
  set g := M / 3 with hg
  have hg1 : 1 ≤ g := by omega
  have hcount := groupAux_count (κ := κ) (α := α) (g := g) hg1 (cur := none) (bs := D'.blocks) (by simp)
  simp only [add_zero] at hcount
  rw [← hG, ← hE'] at hcount
  -- `4G ≤ 2 ⌊12E'/M⌋ + 9`
  set P := 12 * E' / M with hP
  have hP1 : 12 * E' < M * (P + 1) := by
    have := Nat.lt_mul_div_succ (12 * E') hMpos
    rw [hP]; linarith
  have h6g : M ≤ 6 * g := by omega
  have h3g : 3 * g ≤ M := by omega
  have hMG : M * G ≤ 6 * E' + 2 * M := by
    have : M * G ≤ 6 * g * G := Nat.mul_le_mul_right _ h6g
    nlinarith
  have h4G : 4 * G ≤ 2 * P + 9 := by
    by_contra hcon
    push_neg at hcon
    have : M * (2 * P + 10) ≤ M * (4 * G) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  -- entry potentials
  have hem : epot (merge 1 D D').1 ≤ 12 * E / M + P + 1 := by
    unfold epot
    rw [hM]
    calc 12 * Em / M ≤ (12 * E + 12 * E') / M := Nat.div_le_div_right (by omega)
      _ ≤ 12 * E / M + 12 * E' / M + 1 := by
        rw [Nat.add_div hMpos]; split_ifs <;> omega
  have hed' : 3 * P ≤ epot D' := by
    unfold epot
    rw [← hE', ← hM'def]
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    have hPM : P * M ≤ 12 * E' := Nat.div_mul_le_self _ _
    have : 3 * P * M' ≤ P * M := by nlinarith
    linarith
  have hed : epot D = 12 * E / M := rfl
  unfold potM
  omega

/-- `insertL` raises the entry potential by at most `13` -/
theorem epot_insertL {L : Live κ α} {fresh : ℕ} {D : DStr κ α} {v : κ} {lam : α} (hwf : WF L D)
    (hM : 1 ≤ D.M) : epot (insertL L fresh D v lam).2.2.1 ≤ epot D + 13 := by
  unfold epot insertL DB.insert
  split_ifs
  · simp
  · simp only
    obtain ⟨pre, c, post, hbs, hres⟩ := addTo_noSplit 0
      (L := Function.update L v (some (fresh, lam))) (M := bigM D) (lam := lam)
      (e := ⟨fresh, v, lam⟩) D.blocks hwf.1 (fun c hc => by
        have := length_le_allEnts hc; unfold bigM; omega)
    rw [hres]
    have hl : (allEnts (pre ++ ⟨c.sep, ⟨fresh, v, lam⟩ :: c.ents⟩ :: post)).length =
        (allEnts D.blocks).length + 1 := by
      rw [hbs]; simp [allEnts]; omega
    rw [hl]
    calc 12 * ((allEnts D.blocks).length + 1) / D.M
        = (12 * (allEnts D.blocks).length + 12) / D.M := by ring_nf
      _ ≤ 12 * (allEnts D.blocks).length / D.M + 12 / D.M + 1 := by
        rw [Nat.add_div (by omega)]; split_ifs <;> omega
      _ ≤ 12 * (allEnts D.blocks).length / D.M + 13 := by
        have : 12 / D.M ≤ 12 := Nat.div_le_self _ _
        omega

/-- `pullL` does not raise the entry potential -/
theorem epot_pullL {L : Live κ α} {D : DStr κ α} : epot (pullL 1 L D).2.2.2.1 ≤ epot D := by
  rw [pullL_eq]
  have h1 := pull_subperm 1 L (prepD L D)
  have h2 := prepList_subperm L D.M 0 D.blocks
  have hle := (h1.trans h2).length_le
  have hM : (pull 1 L (prepD L D)).2.2.2.1.M = D.M := by
    unfold pull; split_ifs <;> rfl
  unfold epot
  dsimp only
  rw [hM]
  exact Nat.div_le_div_right (by omega)

/-- **amortized bounds with the entry potential** -/
theorem pullM_amortized {L : Live κ α} {D : DStr κ α} {kof : α → κ} (hwf : WF L D)
    (hK : KeyInj L kof) (hid : IdsNodup D) (hM : 1 ≤ D.M) :
    (pullL 1 L D).2.2.2.2 + potM (pullL 1 L D).2.2.1 (pullL 1 L D).2.2.2.1 ≤
      potM L D + (735 * D.M + 950) := by
  have := pullL_amortized hwf hK hid hM
  have := epot_pullL (L := L) (D := D)
  unfold potM; omega

theorem insertM_amortized {L : Live κ α} {fresh : ℕ} {D : DStr κ α} {v : κ} {lam : α}
    (hwf : WF L D) (hfr : FreshOK fresh D) (hid : IdsNodup D) (hM : 1 ≤ D.M) :
    (insertL L fresh D v lam).2.2.2 +
        potM (insertL L fresh D v lam).1 (insertL L fresh D v lam).2.2.1 ≤
      potM L D + bsCost D.blocks.length + 438 + 210 * ell D.M ((allEnts D.blocks).length + 1) := by
  have := insertL_amortized (v := v) (lam := lam) hwf hfr hid
  have := epot_insertL (fresh := fresh) (v := v) (lam := lam) hwf hM
  unfold potM; omega

theorem deleteKeys_amortizedM {L : Live κ α} {D : DStr κ α} {ks : List κ} (hid : IdsNodup D) :
    (deleteKeys L ks).2 + potM (deleteKeys L ks).1 D ≤ potM L D + 3 * ks.length + 1 := by
  have := deleteKeys_amortizedL (L := L) (ks := ks) hid
  unfold potM; simp only [deleteKeys] at this ⊢; omega

theorem potM_new (L : Live κ α) (M : ℕ) (Bd : α) : potM L ⟨M, Bd, [⟨⊥, []⟩]⟩ = 3 := by
  simp [potM, potL, epot, staleCnt, allEnts, spot, bw, Ssum]

end Ops

end Frontier.CHD.DL
