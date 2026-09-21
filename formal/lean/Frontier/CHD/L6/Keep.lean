import Frontier.RAMRep
import Frontier.RAMWP
import Frontier.CHD.L6.Prog
import Frontier.CHD.L6.Util

/-!
# L6 keep pass (agent-10, scratch): `gKeep[v] = 1` iff `v = s` or a non-loop edge enters `v`
-/

namespace Frontier.CHD.L6

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V}

/-- `v` has a non-loop in-edge among the first `k` edges. -/
def hasIn (src dst : ℕ → ℕ) (k v : ℕ) : Prop := ∃ e < k, dst e = v ∧ src e ≠ v

open Classical in
noncomputable def keepArr (src dst : ℕ → ℕ) (k : ℕ) : ℕ → ℕ :=
  fun v => if hasIn src dst k v then 1 else 0

theorem hasIn_succ (src dst : ℕ → ℕ) (k v : ℕ) :
    hasIn src dst (k + 1) v ↔ hasIn src dst k v ∨ (dst k = v ∧ src k ≠ v) := by
  constructor
  · rintro ⟨e, he, h1, h2⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp he with he | rfl
    · exact Or.inl ⟨e, he, h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  · rintro (⟨e, he, h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨e, by omega, h1, h2⟩
    · exact ⟨k, by omega, h1, h2⟩

theorem keepArr_zero (src dst : ℕ → ℕ) : keepArr src dst 0 = fun _ => 0 := by
  funext v; simp [keepArr, hasIn]

/-- One store per loop iteration. -/
theorem keepArr_succ (src dst : ℕ → ℕ) (k : ℕ) :
    keepArr src dst (k + 1) =
      if src k = dst k then keepArr src dst k
      else Function.update (keepArr src dst k) (dst k) 1 := by
  funext v
  have key := hasIn_succ src dst k v
  by_cases hl : src k = dst k
  · have : hasIn src dst (k + 1) v ↔ hasIn src dst k v := by
      rw [key]; constructor
      · rintro (h | ⟨h1, h2⟩)
        · exact h
        · exact absurd (hl.trans h1) h2
      · exact Or.inl
    simp only [hl, if_true]
    unfold keepArr
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (this.mp h1) h2
    · exact absurd (this.mpr h2) h1
    · rfl
  · simp only [hl, if_false]
    by_cases hv : v = dst k
    · subst hv
      have : hasIn src dst (k + 1) (dst k) := key.mpr (Or.inr ⟨rfl, hl⟩)
      simp [keepArr, this]
    · rw [Function.update_of_ne hv]
      have : hasIn src dst (k + 1) v ↔ hasIn src dst k v := by
        rw [key]; constructor
        · rintro (h | ⟨h1, h2⟩)
          · exact h
          · exact absurd h1.symm hv
        · exact Or.inl
      unfold keepArr
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd (this.mp h1) h2
      · exact absurd (this.mpr h2) h1
      · rfl

theorem keepLoop_runs (st : State V) (n m : ℕ) (src dst : ℕ → ℕ) (hm : st.w "m" = m)
    (hsrc : ∀ e < m, st.wa "src" e = src e) (hsrcL : m ≤ st.wlen "src")
    (hdst : ∀ e < m, st.wa "dst" e = dst e) (hdstL : m ≤ st.wlen "dst")
    (hd : ∀ e < m, dst e < n) (hcap : m + 2 < st.cap)
    (hK : WSeg st "gKeep" 0 n (keepArr src dst 0)) (he : st.w "g_e" = 0) :
    Runs ops keepLoop st (fun r => WSeg r "gKeep" 0 n (keepArr src dst m) ∧
      Unchanged st r ["gKeep"] [] ["g_e", "g_u", "g_v"] [] ∧ r.cost = st.cost + 6 * m + 1) := by
  refine runs_while (fun k t => WSeg t "gKeep" 0 n (keepArr src dst k) ∧
      Unchanged st t ["gKeep"] [] ["g_e", "g_u", "g_v"] [] ∧ t.w "g_e" = k ∧
      t.cost = st.cost + 6 * k)
    m _ ?_ ?_ st ⟨hK, Unchanged.refl _ _ _ _ _, he, by simp⟩
  · intro k hk t ⟨hW, hU, hek, hc⟩
    have htcap : t.cap = st.cap := hU.cap
    have htm : t.w "m" = m := by rw [hU.wreg "m" (by simp)]; exact hm
    have htsrc : t.wa "src" k = src k := by rw [(hU.warr "src" (by simp)).1]; exact hsrc k hk
    have htsrcL : t.wlen "src" = st.wlen "src" := (hU.warr "src" (by simp)).2
    have htdst : t.wa "dst" k = dst k := by rw [(hU.warr "dst" (by simp)).1]; exact hdst k hk
    have htdstL : t.wlen "dst" = st.wlen "dst" := (hU.warr "dst" (by simp)).2
    have hdk : dst k < n := hd k hk
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of (x := k) (y := m) (by rw [evalW_var, hek]) (by rw [evalW_var, htm])
        (by rw [htcap]; omega)]
      simp [hk]
    · apply wp_sound
      have hkL : k < t.wlen "src" := by rw [htsrcL]; omega
      have hkL' : k < t.wlen "dst" := by rw [htdstL]; omega
      have hKL : n ≤ t.wlen "gKeep" := by have := hW.1; omega
      by_cases hl : src k = dst k
      · simp [keepBody, inc, wp, hek, hkL, hkL', htsrc, htdst, hl, fit, htcap,
          show 1 < st.cap by omega, show k + 1 < st.cap by omega]
        refine ⟨?_, ?_, ?_⟩
        · rw [keepArr_succ, if_pos hl]; exact hW
        · refine hU.trans ?_
          refine ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun y hy => ?_, fun _ _ => rfl, rfl, rfl⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
          simp [hy.1, hy.2.1, hy.2.2]
        · rw [hc]; ring
      · simp [keepBody, inc, wp, hek, hkL, hkL', htsrc, htdst, hl, fit, htcap,
          show 1 < st.cap by omega, show 0 < st.cap by omega, show k + 1 < st.cap by omega,
          show dst k < t.wlen "gKeep" by omega]
        refine ⟨?_, ?_, ?_⟩
        · rw [keepArr_succ, if_neg hl]
          have h1 := (((((hW.charge 1).setW "g_u" (src k)).charge 1).setW "g_v" (dst k)).charge 1).charge 1
          have h2 := h1.storeW_in (j := dst k) (by omega) (by omega) 1
          have h3 := ((h2.charge 1).setW "g_e" (k + 1)).charge 1
          simpa using h3
        · refine hU.trans ?_
          refine ⟨fun a ha => ⟨funext fun i => ?_, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun y hy => ?_,
            fun _ _ => rfl, rfl, rfl⟩
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
            simp [ha]
          · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
            simp [hy.1, hy.2.1, hy.2.2]
        · rw [hc]; ring
  · intro t ⟨hW, hU, hek, hc⟩
    have htcap : t.cap = st.cap := hU.cap
    have htm : t.w "m" = m := by rw [hU.wreg "m" (by simp)]; exact hm
    refine ⟨?_, hW.charge 1, hU.trans (Unchanged.charge _ _ _ _ _ _), by simp [hc]⟩
    rw [evalW_lt_of (x := m) (y := m) (by rw [evalW_var, hek]) (by rw [evalW_var, htm])
      (by rw [htcap]; omega)]
    simp

/-- Final keep flags. -/
noncomputable def keepF (src dst : ℕ → ℕ) (m s : ℕ) : ℕ → ℕ :=
  Function.update (keepArr src dst m) s 1

theorem keepF_eq_one (src dst : ℕ → ℕ) (m s v : ℕ) :
    keepF src dst m s v = 1 ↔ v = s ∨ hasIn src dst m v := by
  unfold keepF
  by_cases hv : v = s
  · subst hv; simp
  · rw [Function.update_of_ne hv]; unfold keepArr; split_ifs with h <;> simp [hv, h]

theorem keepF_eq_zero (src dst : ℕ → ℕ) (m s v : ℕ) :
    keepF src dst m s v = 0 ↔ ¬ (v = s ∨ hasIn src dst m v) := by
  rw [← keepF_eq_one]
  unfold keepF
  by_cases hv : v = s
  · subst hv; simp
  · rw [Function.update_of_ne hv]; unfold keepArr; split_ifs <;> simp

def keepWR : List String := ["g_e", "g_u", "g_v"]

theorem keepProg_runs (st : State V) (n m s : ℕ) (src dst : ℕ → ℕ) (hn : st.w "n" = n)
    (hm : st.w "m" = m) (hs : st.w "s" = s) (hsn : s < n)
    (hsrc : ∀ e < m, st.wa "src" e = src e) (hsrcL : m ≤ st.wlen "src")
    (hdst : ∀ e < m, st.wa "dst" e = dst e) (hdstL : m ≤ st.wlen "dst")
    (hd : ∀ e < m, dst e < n) (hcap : n + m + 2 < st.cap) :
    Runs ops keepProg st (fun r => WSeg r "gKeep" 0 n (keepF src dst m s) ∧
      Unchanged st r ["gKeep"] [] keepWR [] ∧ r.cost = st.cost + n + 6 * m + 4) := by
  unfold keepProg
  refine runs_seq (runs_walloc (k := n) (by rw [evalW_var, hn]) ?_)
  set s1 := (st.allocW "gKeep" n).charge (n + 1) with hs1
  have hU1 : Unchanged st s1 ["gKeep"] [] keepWR [] :=
    (Unchanged.allocW' (by simp) _).trans (Unchanged.charge _ _ _ _ _ _)
  have hW1 : WSeg s1 "gKeep" 0 n (keepArr src dst 0) := by
    rw [keepArr_zero]; exact (WSeg.of_allocW st "gKeep" n).charge _
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by rw [hU1.cap]; omega)) ?_)
  set s2 := (s1.setW "g_e" 0).charge 1 with hs2
  have hU2 : Unchanged st s2 ["gKeep"] [] keepWR [] :=
    hU1.trans ((Unchanged.setW' (by simp [keepWR]) _).trans (Unchanged.charge _ _ _ _ _ _))
  refine runs_seq ((keepLoop_runs s2 n m src dst
    (by rw [hU2.wreg "m" (by simp [keepWR])]; exact hm)
    (fun e he => by rw [(hU2.warr "src" (by simp)).1]; exact hsrc e he)
    (by rw [(hU2.warr "src" (by simp)).2]; exact hsrcL)
    (fun e he => by rw [(hU2.warr "dst" (by simp)).1]; exact hdst e he)
    (by rw [(hU2.warr "dst" (by simp)).2]; exact hdstL) hd (by rw [hU2.cap]; omega)
    ((hW1.setW _ _).charge 1) (by simp [hs2])).mono ?_)
  rintro s3 ⟨hW3, hU3, hc3⟩
  have hU3' : Unchanged st s3 ["gKeep"] [] keepWR [] := hU2.trans hU3
  have hs3 : s3.w "s" = s := by rw [hU3'.wreg "s" (by simp [keepWR])]; exact hs
  refine runs_wstore (j := s) (a := 1) (by rw [evalW_var, hs3])
    (evalW_lit_of (by rw [hU3'.cap]; omega)) (by have := hW3.1; omega) ?_
  refine ⟨?_, hU3'.trans ((Unchanged.storeW' (by simp) _ _).trans (Unchanged.charge _ _ _ _ _ _)), ?_⟩
  · have := (hW3.storeW_in (j := s) (by omega) (by omega) 1).charge 1
    simpa [keepF] using this
  · simp [hc3, hs2, hs1]; ring

/-! ## Parameters -/

def paramWR : List String := ["g_t", "gD", "cn", "cm"]

/-- `gD = max 3 ⌈2m/n⌉`, `cn = min n (m+1)`, `cm = m`. -/
def deltaF (n m : ℕ) : ℕ := max 3 ((m + m + (n - 1)) / n)

theorem paramProg_runs (st : State V) (n m : ℕ) (hn : st.w "n" = n) (hm : st.w "m" = m)
    (hn1 : 1 ≤ n) (hcap : 3 * (n + m) + 4 < st.cap) :
    Runs ops paramProg st (fun r => r.w "gD" = deltaF n m ∧ r.w "cn" = min n (m + 1) ∧
      r.w "cm" = m ∧ Unchanged st r [] [] paramWR [] ∧ r.cost = st.cost + 6) := by
  apply wp_sound
  have hq : (m + m + (n - 1)) / n ≤ m + m + (n - 1) := Nat.div_le_self _ _
  have hn0 : n ≠ 0 := by omega
  by_cases h3 : (m + m + (n - 1)) / n < 3 <;> by_cases hc : m + 1 < n <;>
    simp [paramProg, wp, hn, hm, fit, hn0, h3, hc, paramWR, deltaF, show 1 < st.cap by omega,
      show 3 < st.cap by omega, show m + m < st.cap by omega, show m + m + (n - 1) < st.cap by omega,
      show m + 1 < st.cap by omega, show 0 < st.cap by omega] <;> omega

end Frontier.CHD.L6
