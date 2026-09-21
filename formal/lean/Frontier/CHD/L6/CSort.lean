import Frontier.RAMRep
import Mathlib.Data.List.GetD
import Frontier.CHD.L6.Prog
import Frontier.CHD.L6.Util

/-!
# L6 counting sort by source (agent-10, scratch) — RAM text and proof
-/

namespace Frontier.CHD.L6

open Frontier Frontier.RAM WExpr Stmt

/-! ## Counting functions -/

def cntk (s : ℕ → ℕ) (k u : ℕ) : ℕ := ((List.range k).filter (fun e => s e = u)).length

theorem cntk_succ (s : ℕ → ℕ) (k u : ℕ) :
    cntk s (k + 1) u = cntk s k u + (if s k = u then 1 else 0) := by
  unfold cntk
  rw [List.range_succ, List.filter_append]
  by_cases h : s k = u <;> simp [h]

theorem cntk_le (s : ℕ → ℕ) (k u : ℕ) : cntk s k u ≤ k := by
  unfold cntk
  calc ((List.range k).filter (fun e => s e = u)).length ≤ (List.range k).length :=
        List.length_filter_le _ _
    _ = k := List.length_range

/-- The count array after `k` edges. -/
def cntArr (s : ℕ → ℕ) (k : ℕ) : ℕ → ℕ := fun j => if j = 0 then 0 else cntk s k (j - 1)

theorem cntArr_succ (s : ℕ → ℕ) (k : ℕ) :
    cntArr s (k + 1) = Function.update (cntArr s k) (s k + 1 - 0) (cntArr s k (s k + 1) + 1) := by
  funext j
  simp only [Nat.sub_zero]
  by_cases hj : j = s k + 1
  · subst hj
    simp [cntArr, cntk_succ]
  · rw [Function.update_of_ne hj]
    simp only [cntArr]
    split_ifs with h0
    · rfl
    · rw [cntk_succ]
      have : s k ≠ j - 1 := by omega
      simp [this]

variable {V : Type} {ops : VOps V}

theorem countLoop_runs (st : State V) (n m : ℕ) (s : ℕ → ℕ) (hm : st.w "m" = m)
    (hsrc : ∀ e < m, st.wa "src" e = s e) (hsrcL : m ≤ st.wlen "src") (hs : ∀ e < m, s e < n)
    (hcap : n + m + 2 < st.cap) (hcnt : WSeg st "g_cnt" 0 (n + 1) (cntArr s 0))
    (he : st.w "g_e" = 0) :
    Runs ops countLoop st (fun r => WSeg r "g_cnt" 0 (n + 1) (cntArr s m) ∧
      Unchanged st r ["g_cnt"] [] ["g_e", "g_u"] [] ∧ r.cost = st.cost + 4 * m + 1) := by
  refine runs_while (fun k t => WSeg t "g_cnt" 0 (n + 1) (cntArr s k) ∧
      Unchanged st t ["g_cnt"] [] ["g_e", "g_u"] [] ∧ t.w "g_e" = k ∧ t.cost = st.cost + 4 * k)
    m _ ?_ ?_ st ⟨hcnt, Unchanged.refl _ _ _ _ _, he, by simp⟩
  · intro k hk t ⟨hW, hU, hek, hc⟩
    have htcap : t.cap = st.cap := hU.cap
    have htm : t.w "m" = m := by rw [hU.wreg "m" (by simp)]; exact hm
    have htsrc : t.wa "src" k = s k := by rw [(hU.warr "src" (by simp)).1]; exact hsrc k hk
    have htsrcL : t.wlen "src" = st.wlen "src" := (hU.warr "src" (by simp)).2
    have hsk : s k < n := hs k hk
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of (x := k) (y := m) (by rw [evalW_var, hek]) (by rw [evalW_var, htm])
        (by rw [htcap]; omega)]
      simp [hk]
    · unfold countBody
      set t1 := t.charge 1 with ht1
      have ht1cap : t1.cap = st.cap := htcap
      refine runs_seq (runs_wset (a := s k) ?_ ?_)
      · rw [evalW_load_of (j := k) (by rw [evalW_var]; simp [ht1, State.charge, hek])
          (by simp [ht1, State.charge, htsrcL]; omega)]
        simp [ht1, State.charge, htsrc]
      set t2 := (t1.setW "g_u" (s k)).charge 1 with ht2
      have ht2cap : t2.cap = st.cap := htcap
      have hW2 : WSeg t2 "g_cnt" 0 (n + 1) (cntArr s k) :=
        ((hW.charge 1).setW _ _).charge 1
      have hidx : evalW t2 (add (var "g_u") (lit 1)) = some (s k + 1) :=
        evalW_add_of (by rw [evalW_var]; simp [ht2, State.setW, State.charge])
          (evalW_lit_of (by rw [ht2cap]; omega)) (by rw [ht2cap]; omega)
      have hval : cntArr s k (s k + 1) ≤ k := by
        simp only [cntArr]; simp; exact cntk_le s k (s k)
      refine runs_seq (runs_wstore (j := s k + 1) (a := cntArr s k (s k + 1) + 1) hidx ?_ ?_ ?_)
      · refine evalW_add_of (hW2.evalW_load (i := s k + 1) (by simpa using hidx) (by omega))
          (evalW_lit_of (by rw [ht2cap]; omega)) (by rw [ht2cap]; omega)
      · have := hW2.1; omega
      set t3 := (t2.storeW "g_cnt" (s k + 1) (cntArr s k (s k + 1) + 1)).charge 1 with ht3
      have ht3cap : t3.cap = st.cap := htcap
      refine runs_wset (a := k + 1) (evalW_add_of (by rw [evalW_var]; simp [ht3, ht2, ht1,
          State.setW, State.charge, State.storeW, hek]) (evalW_lit_of (by rw [ht3cap]; omega))
          (by rw [ht3cap]; omega)) ?_
      refine ⟨?_, ?_, ?_, ?_⟩
      · have := (hW2.storeW_in (j := s k + 1) (by omega) (by omega)
          (cntArr s k (s k + 1) + 1)).charge 1
        rw [cntArr_succ]
        exact (this.setW _ _).charge 1
      · refine hU.trans ?_
        refine ⟨fun a ha => ?_, fun a _ => ⟨rfl, rfl⟩, fun x hx => ?_, fun _ _ => rfl, rfl, rfl⟩
        · have : a ≠ "g_cnt" := by simpa using ha
          simp [ht3, ht2, ht1, State.setW, State.charge, State.storeW, this]
        · have h1 : x ≠ "g_e" := by intro h; simp [h] at hx
          have h2 : x ≠ "g_u" := by intro h; simp [h] at hx
          simp [ht3, ht2, ht1, State.setW, State.charge, State.storeW, h1, h2]
      · simp [State.setW, State.charge]
      · simp [ht3, ht2, ht1, State.setW, State.charge, State.storeW, hc]; ring
  · intro t ⟨hW, hU, hek, hc⟩
    have htcap : t.cap = st.cap := hU.cap
    have htm : t.w "m" = m := by rw [hU.wreg "m" (by simp)]; exact hm
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [evalW_lt_of (x := m) (y := m) (by rw [evalW_var, hek]) (by rw [evalW_var, htm])
        (by rw [htcap]; omega)]
      simp
    · exact hW.charge 1
    · exact hU.trans (Unchanged.charge _ _ _ _ _ _)
    · simp [State.charge, hc]


/-! ## Prefix sums -/

def pfx (s : ℕ → ℕ) (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => pfx s m i + cntk s m i

theorem pfx_succ (s : ℕ → ℕ) (m i : ℕ) : pfx s m (i + 1) = pfx s m i + cntk s m i := rfl

theorem pfx_mono (s : ℕ → ℕ) (m : ℕ) {i j : ℕ} (h : i ≤ j) : pfx s m i ≤ pfx s m j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [pfx_succ]; omega

/-- The count array during the prefix loop after `j` steps. -/
def prefArr (s : ℕ → ℕ) (m j : ℕ) : ℕ → ℕ := fun i => if i ≤ j then pfx s m i else cntArr s m i

theorem prefArr_zero (s : ℕ → ℕ) (m : ℕ) : prefArr s m 0 = cntArr s m := by
  funext i
  simp only [prefArr]
  split_ifs with h
  · have : i = 0 := by omega
    subst this; simp [pfx, cntArr]
  · rfl

theorem prefArr_succ (s : ℕ → ℕ) (m j : ℕ) :
    prefArr s m (j + 1) = Function.update (prefArr s m j) (j + 1 - 0)
      (prefArr s m j (j + 1) + prefArr s m j j) := by
  funext i
  simp only [Nat.sub_zero]
  by_cases hi : i = j + 1
  · subst hi
    simp [prefArr, cntArr, pfx_succ]; ring
  · rw [Function.update_of_ne hi]
    simp only [prefArr]
    by_cases h1 : i ≤ j
    · simp [h1, show i ≤ j + 1 by omega]
    · simp [h1, show ¬ i ≤ j + 1 by omega]

theorem pfx_le (s : ℕ → ℕ) (m : ℕ) (i : ℕ) : pfx s m i ≤ i * m := by
  induction i with
  | zero => simp [pfx]
  | succ i ih => rw [pfx_succ]; have := cntk_le s m i; nlinarith

theorem prefLoop_runs (st : State V) (n m : ℕ) (s : ℕ → ℕ) (hn : st.w "n" = n)
    (hcap : (n + 1) * (m + 1) + 2 < st.cap) (hW : WSeg st "g_cnt" 0 (n + 1) (cntArr s m))
    (hu : st.w "g_u" = 0) :
    Runs ops prefLoop st (fun r => WSeg r "g_cnt" 0 (n + 1) (prefArr s m n) ∧
      Unchanged st r ["g_cnt"] [] ["g_u"] [] ∧ r.cost = st.cost + 3 * n + 1) := by
  refine runs_while (fun j t => WSeg t "g_cnt" 0 (n + 1) (prefArr s m j) ∧
      Unchanged st t ["g_cnt"] [] ["g_u"] [] ∧ t.w "g_u" = j ∧ t.cost = st.cost + 3 * j)
    n _ ?_ ?_ st ⟨by rw [prefArr_zero]; exact hW, Unchanged.refl _ _ _ _ _, hu, by simp⟩
  · intro j hj t ⟨hW', hU, huj, hc⟩
    have htcap : t.cap = st.cap := hU.cap
    have htn : t.w "n" = n := by rw [hU.wreg "n" (by simp)]; exact hn
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of (x := j) (y := n) (by rw [evalW_var, huj]) (by rw [evalW_var, htn])
        (by rw [htcap]; nlinarith)]
      simp [hj]
    · unfold prefBody
      set t1 := t.charge 1 with ht1
      have hW1 : WSeg t1 "g_cnt" 0 (n + 1) (prefArr s m j) := hW'.charge 1
      have ht1cap : t1.cap = st.cap := htcap
      have hidx : evalW t1 (add (var "g_u") (lit 1)) = some (j + 1) :=
        evalW_add_of (by rw [evalW_var]; simp [ht1, State.charge, huj])
          (evalW_lit_of (by rw [ht1cap]; nlinarith)) (by rw [ht1cap]; nlinarith)
      have hidx0 : evalW t1 (var "g_u") = some (0 + j) := by
        rw [evalW_var]; simp [ht1, State.charge, huj]
      -- value bounds
      have hv1 : prefArr s m j (j + 1) ≤ m := by
        simp only [prefArr, show ¬ j + 1 ≤ j by omega, if_false, cntArr]; simp
        exact cntk_le s m j
      have hv2 : prefArr s m j j ≤ n * m := by
        simp only [prefArr, le_refl, if_true]
        exact (pfx_le s m j).trans (Nat.mul_le_mul_right _ hj.le)
      refine runs_seq (runs_wstore (j := j + 1)
        (a := prefArr s m j (j + 1) + prefArr s m j j) hidx ?_ ?_ ?_)
      · exact evalW_add_of (hW1.evalW_load (i := j + 1) (by simpa using hidx) (by omega))
          (hW1.evalW_load (i := j) hidx0 (by omega)) (by rw [ht1cap]; nlinarith)
      · have := hW1.1; omega
      set t2 := (t1.storeW "g_cnt" (j + 1) (prefArr s m j (j + 1) + prefArr s m j j)).charge 1
        with ht2
      have ht2cap : t2.cap = st.cap := htcap
      refine runs_wset (a := j + 1) (evalW_add_of (by rw [evalW_var]; simp [ht2, ht1,
          State.charge, State.storeW, huj]) (evalW_lit_of (by rw [ht2cap]; nlinarith))
          (by rw [ht2cap]; nlinarith)) ?_
      refine ⟨?_, ?_, ?_, ?_⟩
      · have := (hW1.storeW_in (j := j + 1) (by omega) (by omega)
          (prefArr s m j (j + 1) + prefArr s m j j)).charge 1
        rw [prefArr_succ]
        exact (this.setW _ _).charge 1
      · refine hU.trans ?_
        refine ⟨fun a ha => ?_, fun a _ => ⟨rfl, rfl⟩, fun x hx => ?_, fun _ _ => rfl, rfl, rfl⟩
        · have : a ≠ "g_cnt" := by simpa using ha
          simp [ht2, ht1, State.setW, State.charge, State.storeW, this]
        · have h1 : x ≠ "g_u" := by intro h; simp [h] at hx
          simp [ht2, ht1, State.setW, State.charge, State.storeW, h1]
      · simp [State.setW, State.charge]
      · simp [ht2, ht1, State.setW, State.charge, State.storeW, hc]; ring
  · intro t ⟨hW', hU, huj, hc⟩
    have htcap : t.cap = st.cap := hU.cap
    have htn : t.w "n" = n := by rw [hU.wreg "n" (by simp)]; exact hn
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [evalW_lt_of (x := n) (y := n) (by rw [evalW_var, huj]) (by rw [evalW_var, htn])
        (by rw [htcap]; nlinarith)]
      simp
    · exact hW'.charge 1
    · exact hU.trans (Unchanged.charge _ _ _ _ _ _)
    · simp [State.charge, hc]

theorem prefArr_n (s : ℕ → ℕ) (m n : ℕ) {i : ℕ} (hi : i ≤ n) : prefArr s m n i = pfx s m i := by
  simp [prefArr, hi]


/-! ## Copy loop `g_pos[u] := g_cnt[u]` -/

theorem copyLoop_runs (st : State V) (n : ℕ) (f : ℕ → ℕ) (hn : st.w "n" = n)
    (hcap : n + 3 < st.cap) (hW : WSeg st "g_cnt" 0 (n + 1) f)
    (hP : WSeg st "g_pos" 0 (n + 1) (fun _ => 0)) (hf : ∀ i ≤ n, f i < st.cap)
    (hu : st.w "g_u" = 0) :
    Runs ops copyLoop st (fun r => WSeg r "g_cnt" 0 (n + 1) f ∧ WSeg r "g_pos" 0 (n + 1) f ∧
      Unchanged st r ["g_pos"] [] ["g_u"] [] ∧ r.cost = st.cost + 3 * (n + 1) + 1) := by
  refine runs_while (fun j t => WSeg t "g_cnt" 0 (n + 1) f ∧
      WSeg t "g_pos" 0 (n + 1) (fun i => if i < j then f i else 0) ∧
      Unchanged st t ["g_pos"] [] ["g_u"] [] ∧ t.w "g_u" = j ∧ t.cost = st.cost + 3 * j)
    (n + 1) _ ?_ ?_ st ⟨hW, by simpa using hP, Unchanged.refl _ _ _ _ _, hu, by simp⟩
  · intro j hj t ⟨hW', hP', hU, huj, hc⟩
    have htcap : t.cap = st.cap := hU.cap
    have htn : t.w "n" = n := by rw [hU.wreg "n" (by simp)]; exact hn
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of (x := j) (y := n + 1) (by rw [evalW_var, huj])
        (evalW_add_of (by rw [evalW_var, htn]) (evalW_lit_of (by rw [htcap]; omega))
          (by rw [htcap]; omega)) (by rw [htcap]; omega)]
      simp [hj]
    · unfold copyBody
      set t1 := t.charge 1 with ht1
      have hidx : evalW t1 (var "g_u") = some (0 + j) := by
        rw [evalW_var]; simp [ht1, State.charge, huj]
      refine runs_seq (runs_wstore (j := j) (a := f j) (by simpa using hidx)
        ((hW'.charge 1).evalW_load hidx hj) (by have := hP'.1; simp [ht1, State.charge]; omega) ?_)
      set t2 := (t1.storeW "g_pos" j (f j)).charge 1 with ht2
      have ht2cap : t2.cap = st.cap := htcap
      refine runs_wset (a := j + 1) (evalW_add_of (by rw [evalW_var]; simp [ht2, ht1,
          State.charge, State.storeW, huj]) (evalW_lit_of (by rw [ht2cap]; omega))
          (by rw [ht2cap]; omega)) ?_
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact (((hW'.charge 1).storeW_ne (by decide) _ _).charge 1 |>.setW _ _).charge 1
      · have := ((hP'.charge 1).storeW_in (j := j) (by omega) (by omega) (f j)).charge 1
        have heq : (Function.update (fun i => if i < j then f i else 0) (j - 0) (f j)) =
            (fun i => if i < j + 1 then f i else 0) := by
          funext i
          simp only [Nat.sub_zero]
          by_cases hi : i = j
          · subst hi; simp
          · rw [Function.update_of_ne hi]
            by_cases h2 : i < j
            · simp [h2, show i < j + 1 by omega]
            · simp [h2, show ¬ i < j + 1 by omega]
        rw [heq] at this
        exact (this.setW _ _).charge 1
      · refine hU.trans ?_
        refine ⟨fun a ha => ?_, fun a _ => ⟨rfl, rfl⟩, fun x hx => ?_, fun _ _ => rfl, rfl, rfl⟩
        · have : a ≠ "g_pos" := by simpa using ha
          simp [ht2, ht1, State.setW, State.charge, State.storeW, this]
        · have h1 : x ≠ "g_u" := by intro h; simp [h] at hx
          simp [ht2, ht1, State.setW, State.charge, State.storeW, h1]
      · simp [State.setW, State.charge]
      · simp [ht2, ht1, State.setW, State.charge, State.storeW, hc]; ring
  · intro t ⟨hW', hP', hU, huj, hc⟩
    have htcap : t.cap = st.cap := hU.cap
    have htn : t.w "n" = n := by rw [hU.wreg "n" (by simp)]; exact hn
    refine ⟨?_, hW'.charge 1, ?_, hU.trans (Unchanged.charge _ _ _ _ _ _), by simp [State.charge, hc]⟩
    · rw [evalW_lt_of (x := n + 1) (y := n + 1) (by rw [evalW_var, huj])
        (evalW_add_of (by rw [evalW_var, htn]) (evalW_lit_of (by rw [htcap]; omega))
          (by rw [htcap]; omega)) (by rw [htcap]; omega)]
      simp
    · have := hP'.charge 1
      refine ⟨this.1, fun i hi => ?_⟩
      rw [this.2 i hi]; simp [show i < n + 1 by omega]


/-! ## Placement loop -/

def grpk (s : ℕ → ℕ) (k u : ℕ) : List ℕ := (List.range k).filter (fun e => s e = u)

theorem grpk_length (s : ℕ → ℕ) (k u : ℕ) : (grpk s k u).length = cntk s k u := rfl

theorem grpk_succ (s : ℕ → ℕ) (k u : ℕ) :
    grpk s (k + 1) u = grpk s k u ++ (if s k = u then [k] else []) := by
  unfold grpk
  rw [List.range_succ, List.filter_append]
  by_cases h : s k = u <;> simp [h]

theorem cntk_mono (s : ℕ → ℕ) {k k' : ℕ} (h : k ≤ k') (u : ℕ) : cntk s k u ≤ cntk s k' u := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [cntk_succ]; omega

theorem pfx_add_cnt (s : ℕ → ℕ) (m u : ℕ) : pfx s m u + cntk s m u = pfx s m (u + 1) := rfl

theorem filter_le_length (s : ℕ → ℕ) (u : ℕ) (l : List ℕ) :
    (l.filter (fun e => s e ≤ u)).length =
      (l.filter (fun e => s e < u)).length + (l.filter (fun e => s e = u)).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h1 : s a < u
    · simp [List.filter_cons, h1, h1.le, h1.ne, ih]; omega
    · by_cases h2 : s a = u
      · simp [List.filter_cons, h2, ih]; omega
      · have h3 : ¬ s a ≤ u := by omega
        simp [List.filter_cons, h1, h2, h3, ih]

theorem pfx_eq_count (s : ℕ → ℕ) (m u : ℕ) :
    pfx s m u = ((List.range m).filter (fun e => s e < u)).length := by
  induction u with
  | zero => simp [pfx]
  | succ u ih =>
    rw [pfx_succ, ih]
    have : (List.range m).filter (fun e => s e < u + 1) = (List.range m).filter (fun e => s e ≤ u) := by
      congr 1; funext e; simp [Nat.lt_succ_iff]
    rw [this, filter_le_length]; rfl

/-- Total: all edges have their source below `n`. -/
theorem pfx_total (s : ℕ → ℕ) (m n : ℕ) (hs : ∀ e < m, s e < n) : pfx s m n = m := by
  rw [pfx_eq_count]
  have : (List.range m).filter (fun e => s e < n) = List.range m := by
    apply List.filter_eq_self.mpr
    intro e he
    simp at he
    simpa using hs e he
  rw [this, List.length_range]


def posK (s : ℕ → ℕ) (m k : ℕ) : ℕ → ℕ := fun u => pfx s m u + cntk s k u

def OrdK (s : ℕ → ℕ) (m n k : ℕ) (t : State V) : Prop :=
  ∀ u < n, ∀ i < cntk s k u, t.wa "g_ord" (pfx s m u + i) = (grpk s k u).getD i 0

theorem grpk_getD_succ_self (s : ℕ → ℕ) (k : ℕ) :
    (grpk s (k + 1) (s k)).getD (cntk s k (s k)) 0 = k := by
  rw [grpk_succ]; simp [← grpk_length]

theorem grpk_getD_succ_lt (s : ℕ → ℕ) (k u i : ℕ) (hi : i < cntk s k u) :
    (grpk s (k + 1) u).getD i 0 = (grpk s k u).getD i 0 := by
  rw [grpk_succ]
  exact List.getD_append _ _ 0 i (by rw [grpk_length]; exact hi)

/-- Disjointness of the group intervals. -/
theorem pos_ne_of_ne (s : ℕ → ℕ) (m : ℕ) {u u' i j : ℕ} (hne : u' ≠ u) (hi : i < cntk s m u')
    (hj : j < cntk s m u) : pfx s m u' + i ≠ pfx s m u + j := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : pfx s m (u' + 1) ≤ pfx s m u := pfx_mono s m h
    rw [← pfx_add_cnt] at this
    omega
  · have : pfx s m (u + 1) ≤ pfx s m u' := pfx_mono s m h
    rw [← pfx_add_cnt] at this
    omega

theorem placeLoop_runs (st : State V) (n m : ℕ) (s : ℕ → ℕ) (hm : st.w "m" = m)
    (hsrc : ∀ e < m, st.wa "src" e = s e) (hsrcL : m ≤ st.wlen "src") (hs : ∀ e < m, s e < n)
    (hcap : n + m + 2 < st.cap) (hP : WSeg st "g_pos" 0 (n + 1) (pfx s m))
    (hOL : st.wlen "g_ord" = m) (he : st.w "g_e" = 0) :
    Runs ops placeLoop st (fun r => OrdK s m n m r ∧ r.wlen "g_ord" = m ∧
      Unchanged st r ["g_ord", "g_pos"] [] ["g_e", "g_u"] [] ∧ r.cost = st.cost + 5 * m + 1) := by
  have hpm : pfx s m n = m := pfx_total s m n hs
  refine runs_while (fun k t => WSeg t "g_pos" 0 (n + 1) (posK s m k) ∧ OrdK s m n k t ∧
      t.wlen "g_ord" = m ∧ Unchanged st t ["g_ord", "g_pos"] [] ["g_e", "g_u"] [] ∧
      t.w "g_e" = k ∧ t.cost = st.cost + 5 * k)
    m _ ?_ ?_ st ⟨by
      have : posK s m 0 = pfx s m := by funext u; simp [posK, cntk]
      rw [this]; exact hP, fun u _ i hi => by simp [cntk] at hi,
      hOL, Unchanged.refl _ _ _ _ _, he, by simp⟩
  · intro k hk t ⟨hPk, hOk, hOLk, hU, hek, hc⟩
    have htcap : t.cap = st.cap := hU.cap
    have htm : t.w "m" = m := by rw [hU.wreg "m" (by simp)]; exact hm
    have htsrc : t.wa "src" k = s k := by rw [(hU.warr "src" (by simp)).1]; exact hsrc k hk
    have htsrcL : t.wlen "src" = st.wlen "src" := (hU.warr "src" (by simp)).2
    set u := s k with hu_def
    have hun : u < n := hs k hk
    have hcl : cntk s k u < cntk s m u := by
      have h1 := cntk_mono s (show k + 1 ≤ m by omega) u
      rw [cntk_succ] at h1
      simp [← hu_def] at h1; omega
    have hpos_lt : posK s m k u < m := by
      have : pfx s m (u + 1) ≤ pfx s m n := pfx_mono s m (by omega)
      rw [← pfx_add_cnt] at this
      simp only [posK]; omega
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of (x := k) (y := m) (by rw [evalW_var, hek]) (by rw [evalW_var, htm])
        (by rw [htcap]; omega)]
      simp [hk]
    · unfold placeBody
      set t1 := t.charge 1 with ht1
      refine runs_seq (runs_wset (a := u) ?_ ?_)
      · rw [evalW_load_of (j := k) (by rw [evalW_var]; simp [ht1, State.charge, hek])
          (by simp [ht1, State.charge, htsrcL]; omega)]
        simp [ht1, State.charge, htsrc, hu_def]
      set t2 := (t1.setW "g_u" u).charge 1 with ht2
      have ht2cap : t2.cap = st.cap := htcap
      have hP2 : WSeg t2 "g_pos" 0 (n + 1) (posK s m k) := ((hPk.charge 1).setW _ _).charge 1
      have hu2 : evalW t2 (var "g_u") = some (0 + u) := by
        rw [evalW_var]; simp [ht2, State.setW, State.charge]
      have hldpos : evalW t2 (load "g_pos" (var "g_u")) = some (posK s m k u) :=
        hP2.evalW_load hu2 (by omega)
      refine runs_seq (runs_wstore (j := posK s m k u) (a := k) hldpos
        (by rw [evalW_var]; simp [ht2, ht1, State.setW, State.charge, hek])
        (by simp [ht2, ht1, State.setW, State.charge, hOLk]; exact hpos_lt) ?_)
      set t3 := (t2.storeW "g_ord" (posK s m k u) k).charge 1 with ht3
      have ht3cap : t3.cap = st.cap := htcap
      have hP3 : WSeg t3 "g_pos" 0 (n + 1) (posK s m k) :=
        (hP2.storeW_ne (by decide) _ _).charge 1
      have hu3 : evalW t3 (var "g_u") = some (0 + u) := by
        rw [evalW_var]; simp [ht3, ht2, State.setW, State.charge, State.storeW]
      have hldpos3 : evalW t3 (load "g_pos" (var "g_u")) = some (posK s m k u) :=
        hP3.evalW_load hu3 (by omega)
      refine runs_seq (runs_wstore (j := u) (a := posK s m k u + 1) (by simpa using hu3)
        (evalW_add_of hldpos3 (evalW_lit_of (by rw [ht3cap]; omega)) (by rw [ht3cap]; omega))
        (by have := hP3.1; omega) ?_)
      set t4 := (t3.storeW "g_pos" u (posK s m k u + 1)).charge 1 with ht4
      have ht4cap : t4.cap = st.cap := htcap
      refine runs_wset (a := k + 1) (evalW_add_of (by rw [evalW_var]; simp [ht4, ht3, ht2, ht1,
          State.setW, State.charge, State.storeW, hek]) (evalW_lit_of (by rw [ht4cap]; omega))
          (by rw [ht4cap]; omega)) ?_
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · have := (hP3.storeW_in (j := u) (by omega) (by omega) (posK s m k u + 1)).charge 1
        have heq : Function.update (posK s m k) (u - 0) (posK s m k u + 1) = posK s m (k + 1) := by
          funext x
          simp only [Nat.sub_zero]
          by_cases hx : x = u
          · subst hx; simp [posK, cntk_succ, ← hu_def]; ring
          · rw [Function.update_of_ne hx]
            simp only [posK, cntk_succ]
            have : s k ≠ x := fun h => hx (by rw [← h])
            simp [this]
        rw [heq] at this
        exact (this.setW _ _).charge 1
      · intro u' hu' i hi
        -- the store into g_ord happened at t2; later steps only touch g_pos and registers
        have hread : ((t4.setW "g_e" (k + 1)).charge 1).wa "g_ord" (pfx s m u' + i) =
            t3.wa "g_ord" (pfx s m u' + i) := by
          simp [ht4, State.setW, State.charge, State.storeW]
        rw [hread]
        by_cases hsame : u' = u ∧ i = cntk s k u
        · obtain ⟨rfl, rfl⟩ := hsame
          simp [ht3, State.charge, State.storeW, posK]
          rw [hu_def]; exact (grpk_getD_succ_self s k).symm
        · have hne : pfx s m u' + i ≠ posK s m k u := by
            simp only [posK]
            by_cases hu'u : u' = u
            · rw [hu'u]
              have : i ≠ cntk s k u := fun h => hsame ⟨hu'u, h⟩
              omega
            · have hi' : i < cntk s m u' := lt_of_lt_of_le hi (cntk_mono s (by omega) u')
              exact pos_ne_of_ne s m hu'u hi' (lt_of_le_of_lt le_rfl hcl)
          have hi2 : i < cntk s k u' := by
            rw [cntk_succ] at hi
            by_cases hsk : s k = u'
            · have : u' = u := by rw [hu_def]; exact hsk.symm
              subst this
              have : i ≠ cntk s k u := fun h => hsame ⟨rfl, h⟩
              simp [hsk] at hi; omega
            · simp [hsk] at hi; exact hi
          have hold : t3.wa "g_ord" (pfx s m u' + i) = t.wa "g_ord" (pfx s m u' + i) := by
            simp only [ht3, ht2, ht1, State.charge, State.storeW, State.setW]
            rw [if_neg (by rintro ⟨-, h⟩; exact hne h)]
          rw [hold, hOk u' hu' i hi2, grpk_getD_succ_lt s k u' i hi2]
      · simp [ht4, ht3, ht2, ht1, State.setW, State.charge, State.storeW, hOLk]
      · refine hU.trans ?_
        refine ⟨fun a ha => ?_, fun a _ => ⟨rfl, rfl⟩, fun x hx => ?_, fun _ _ => rfl, rfl, rfl⟩
        · have h1 : a ≠ "g_ord" := by intro h; simp [h] at ha
          have h2 : a ≠ "g_pos" := by intro h; simp [h] at ha
          simp [ht4, ht3, ht2, ht1, State.setW, State.charge, State.storeW, h1, h2]
        · have h1 : x ≠ "g_e" := by intro h; simp [h] at hx
          have h2 : x ≠ "g_u" := by intro h; simp [h] at hx
          simp [ht4, ht3, ht2, ht1, State.setW, State.charge, State.storeW, h1, h2]
      · simp [State.setW, State.charge]
      · simp [ht4, ht3, ht2, ht1, State.setW, State.charge, State.storeW, hc]; ring
  · intro t ⟨hPk, hOk, hOLk, hU, hek, hc⟩
    have htcap : t.cap = st.cap := hU.cap
    have htm : t.w "m" = m := by rw [hU.wreg "m" (by simp)]; exact hm
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [evalW_lt_of (x := m) (y := m) (by rw [evalW_var, hek]) (by rw [evalW_var, htm])
        (by rw [htcap]; omega)]
      simp
    · intro u' hu' i hi; exact hOk u' hu' i hi
    · simpa [State.charge] using hOLk
    · exact hU.trans (Unchanged.charge _ _ _ _ _ _)
    · simp [State.charge, hc]


/-! ## The whole counting sort -/

/-- Names written by the counting sort. -/
def csortWA : List String := ["g_cnt", "g_pos", "g_ord"]
def csortWR : List String := ["g_e", "g_u"]

theorem csort_runs (st : State V) (n m : ℕ) (s : ℕ → ℕ) (hn : st.w "n" = n) (hm : st.w "m" = m)
    (hsrc : ∀ e < m, st.wa "src" e = s e) (hsrcL : m ≤ st.wlen "src") (hs : ∀ e < m, s e < n)
    (hcap : (n + 1) * (m + 1) + n + m + 4 < st.cap) :
    Runs ops csortProg st (fun r => WSeg r "g_cnt" 0 (n + 1) (pfx s m) ∧ OrdK s m n m r ∧
      r.wlen "g_ord" = m ∧ Unchanged st r csortWA [] csortWR [] ∧
      r.cost ≤ st.cost + 12 * (n + m) + 20) := by
  have hcap1 : n + m + 2 < st.cap := by nlinarith
  unfold csortProg
  -- walloc g_cnt
  refine runs_seq (runs_walloc (k := n + 1) (evalW_add_of (by rw [evalW_var, hn])
    (evalW_lit_of (by omega)) (by omega)) ?_)
  set s1 := (st.allocW "g_cnt" (n + 1)).charge (n + 1 + 1) with hs1
  have hU1 : Unchanged st s1 csortWA [] csortWR [] :=
    (Unchanged.allocW' (by simp [csortWA]) _).trans (Unchanged.charge _ _ _ _ _ _)
  have hW1 : WSeg s1 "g_cnt" 0 (n + 1) (cntArr s 0) := by
    have := (WSeg.of_allocW st "g_cnt" (n + 1)).charge (n + 1 + 1)
    have h0 : cntArr s 0 = fun _ => 0 := by funext j; simp [cntArr, cntk]
    rw [h0]; exact this
  -- g_e := 0
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by rw [hU1.cap]; omega)) ?_)
  set s2 := (s1.setW "g_e" 0).charge 1 with hs2
  have hU2 : Unchanged st s2 csortWA [] csortWR [] :=
    hU1.trans ((Unchanged.setW' (by simp [csortWR]) _).trans (Unchanged.charge _ _ _ _ _ _))
  have hc2 : s2.cost = st.cost + (n + 2) + 1 := by simp [hs2, hs1, State.setW, State.charge, State.allocW]
  refine runs_seq ((countLoop_runs s2 n m s (by rw [hU2.wreg "m" (by simp [csortWR])]; exact hm)
    (fun e he => by rw [(hU2.warr "src" (by simp [csortWA])).1]; exact hsrc e he)
    (by rw [(hU2.warr "src" (by simp [csortWA])).2]; exact hsrcL) hs (by rw [hU2.cap]; exact hcap1)
    (((hW1.setW _ _).charge 1)) (by simp [hs2, State.setW, State.charge])).mono ?_)
  rintro s3 ⟨hW3, hU3, hc3⟩
  have hU3' : Unchanged st s3 csortWA [] csortWR [] :=
    hU2.trans (hU3.mono (by simp [csortWA]) (by simp) (by simp [csortWR]) (by simp))
  -- g_u := 0
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by rw [hU3'.cap]; omega)) ?_)
  set s4 := (s3.setW "g_u" 0).charge 1 with hs4
  have hU4 : Unchanged st s4 csortWA [] csortWR [] :=
    hU3'.trans ((Unchanged.setW' (by simp [csortWR]) _).trans (Unchanged.charge _ _ _ _ _ _))
  refine runs_seq ((prefLoop_runs s4 n m s (by rw [hU4.wreg "n" (by simp [csortWR])]; exact hn)
    (by rw [hU4.cap]; nlinarith) ((hW3.setW _ _).charge 1)
    (by simp [hs4, State.setW, State.charge])).mono ?_)
  rintro s5 ⟨hW5, hU5, hc5⟩
  have hU5' : Unchanged st s5 csortWA [] csortWR [] :=
    hU4.trans (hU5.mono (by simp [csortWA]) (by simp) (by simp [csortWR]) (by simp))
  have hW5' : WSeg s5 "g_cnt" 0 (n + 1) (pfx s m) := by
    refine ⟨hW5.1, fun i hi => ?_⟩
    rw [hW5.2 i hi]; exact prefArr_n s m n (by omega)
  -- walloc g_pos
  have hn5 : s5.w "n" = n := by rw [hU5'.wreg "n" (by simp [csortWR])]; exact hn
  refine runs_seq (runs_walloc (k := n + 1) (evalW_add_of (by rw [evalW_var, hn5])
    (evalW_lit_of (by rw [hU5'.cap]; omega)) (by rw [hU5'.cap]; omega)) ?_)
  set s6 := (s5.allocW "g_pos" (n + 1)).charge (n + 1 + 1) with hs6
  have hU6 : Unchanged st s6 csortWA [] csortWR [] :=
    hU5'.trans ((Unchanged.allocW' (by simp [csortWA]) _).trans (Unchanged.charge _ _ _ _ _ _))
  have hW6 : WSeg s6 "g_cnt" 0 (n + 1) (pfx s m) := (hW5'.allocW_ne (by decide) _).charge _
  have hP6 : WSeg s6 "g_pos" 0 (n + 1) (fun _ => 0) := (WSeg.of_allocW s5 "g_pos" (n + 1)).charge _
  -- g_u := 0
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by rw [hU6.cap]; omega)) ?_)
  set s7 := (s6.setW "g_u" 0).charge 1 with hs7
  have hU7 : Unchanged st s7 csortWA [] csortWR [] :=
    hU6.trans ((Unchanged.setW' (by simp [csortWR]) _).trans (Unchanged.charge _ _ _ _ _ _))
  have hpfx_lt : ∀ i ≤ n, pfx s m i < s7.cap := by
    intro i hi
    have := pfx_mono s m hi
    rw [pfx_total s m n hs] at this
    rw [hU7.cap]; omega
  refine runs_seq ((copyLoop_runs s7 n (pfx s m) (by rw [hU7.wreg "n" (by simp [csortWR])]; exact hn)
    (by rw [hU7.cap]; omega) ((hW6.setW _ _).charge 1) ((hP6.setW _ _).charge 1) hpfx_lt
    (by simp [hs7, State.setW, State.charge])).mono ?_)
  rintro s8 ⟨hW8, hP8, hU8, hc8⟩
  have hU8' : Unchanged st s8 csortWA [] csortWR [] :=
    hU7.trans (hU8.mono (by simp [csortWA]) (by simp) (by simp [csortWR]) (by simp))
  -- walloc g_ord
  have hm8 : s8.w "m" = m := by rw [hU8'.wreg "m" (by simp [csortWR])]; exact hm
  refine runs_seq (runs_walloc (k := m) (by rw [evalW_var, hm8]) ?_)
  set s9 := (s8.allocW "g_ord" m).charge (m + 1) with hs9
  have hU9 : Unchanged st s9 csortWA [] csortWR [] :=
    hU8'.trans ((Unchanged.allocW' (by simp [csortWA]) _).trans (Unchanged.charge _ _ _ _ _ _))
  have hW9 : WSeg s9 "g_cnt" 0 (n + 1) (pfx s m) := (hW8.allocW_ne (by decide) _).charge _
  have hP9 : WSeg s9 "g_pos" 0 (n + 1) (pfx s m) := (hP8.allocW_ne (by decide) _).charge _
  have hOL9 : s9.wlen "g_ord" = m := by simp [hs9, State.allocW, State.charge]
  -- g_e := 0
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by rw [hU9.cap]; omega)) ?_)
  set s10 := (s9.setW "g_e" 0).charge 1 with hs10
  have hU10 : Unchanged st s10 csortWA [] csortWR [] :=
    hU9.trans ((Unchanged.setW' (by simp [csortWR]) _).trans (Unchanged.charge _ _ _ _ _ _))
  refine ((placeLoop_runs s10 n m s (by rw [hU10.wreg "m" (by simp [csortWR])]; exact hm)
    (fun e he => by rw [(hU10.warr "src" (by simp [csortWA])).1]; exact hsrc e he)
    (by rw [(hU10.warr "src" (by simp [csortWA])).2]; exact hsrcL) hs
    (by rw [hU10.cap]; exact hcap1) ((hP9.setW _ _).charge 1) (by simp [hs10, State.setW,
      State.charge, hOL9]) (by simp [hs10, State.setW, State.charge])).mono ?_)
  rintro r ⟨hO, hOL, hUr, hcr⟩
  refine ⟨?_, hO, hOL, hU10.trans (hUr.mono (by simp [csortWA]) (by simp) (by simp [csortWR]) (by simp)), ?_⟩
  · have hW10 : WSeg s10 "g_cnt" 0 (n + 1) (pfx s m) := (hW9.setW _ _).charge 1
    exact hW10.of_unchanged hUr (by simp)
  · have e1 : s4.cost = s3.cost + 1 := by simp [hs4, State.setW, State.charge]
    have e2 : s6.cost = s5.cost + (n + 2) := by simp [hs6, State.allocW, State.charge]
    have e3 : s7.cost = s6.cost + 1 := by simp [hs7, State.setW, State.charge]
    have e4 : s9.cost = s8.cost + (m + 1) := by simp [hs9, State.allocW, State.charge]
    have e5 : s10.cost = s9.cost + 1 := by simp [hs10, State.setW, State.charge]
    omega

end Frontier.CHD.L6
