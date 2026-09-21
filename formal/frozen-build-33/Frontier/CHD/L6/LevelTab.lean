import Frontier.CHD.L6.Util
import Frontier.CHD.L6.Prog
import Frontier.CHD.BMTeleChd

/-!
# Per-level parameter table (agent-10, part of O16)

`levelTab` fills `cp.tau[l] = chdTau t l = t³·2^{lt}` for `l ≤ L` and `cp.M[l] = chdM t l`
(`1` at `l = 0`, `t·2^{(l-1)t}` above) for `l ≤ L + 1`, from the registers `cp.t = t`, `cp.L = L`.
NON-GATE (a core fragment).
-/

namespace Frontier.CHD.L6

open Frontier Frontier.RAM WExpr Stmt Frontier.CHD.BM

def ltPowBody : Stmt := seq (wset "cp.p" (mul (var "cp.p") (lit 2))) (inc "cp.i")
def ltPowLoop : Stmt := .while (lt (var "cp.i") (var "cp.t")) ltPowBody

def ltBody : Stmt :=
  seq (wstore "cp.tau" (var "cp.l") (mul (var "cp.c") (var "cp.q")))
  (seq (wstore "cp.M" (add (var "cp.l") (lit 1)) (mul (var "cp.t") (var "cp.q")))
  (seq (wset "cp.q" (mul (var "cp.q") (var "cp.p")))
  (inc "cp.l")))
def ltLoop : Stmt := .while (lt (var "cp.l") (add (var "cp.L") (lit 1))) ltBody

def levelTab : Stmt :=
  seq (wset "cp.p" (lit 1))
  (seq (wset "cp.i" (lit 0))
  (seq ltPowLoop
  (seq (walloc "cp.tau" (add (var "cp.L") (lit 1)))
  (seq (walloc "cp.M" (add (var "cp.L") (lit 2)))
  (seq (wstore "cp.M" (lit 0) (lit 1))
  (seq (wset "cp.c" (mul (mul (var "cp.t") (var "cp.t")) (var "cp.t")))
  (seq (wset "cp.q" (lit 1))
  (seq (wset "cp.l" (lit 0)) ltLoop))))))))

def ltWR : List String := ["cp.p", "cp.i", "cp.c", "cp.q", "cp.l"]

variable {V : Type} {ops : VOps V}

/-! ## `cp.p := 2^t` -/

structure PInv (st : State V) (j : ℕ) (t : State V) : Prop where
  p : t.w "cp.p" = 2 ^ j
  i : t.w "cp.i" = j
  U : Unchanged st t [] [] ["cp.p", "cp.i"] []
  c : t.cost = st.cost + 3 * j

theorem ltPowLoop_runs (st : State V) (T : ℕ) (ht : st.w "cp.t" = T) (hp : st.w "cp.p" = 1)
    (hi : st.w "cp.i" = 0) (hcap : 2 ^ (T + 1) + T + 2 < st.cap) :
    Runs ops ltPowLoop st (fun r => ∃ t, PInv st T t ∧ r = t.charge 1) := by
  have hTp : T < 2 ^ (T + 1) := by
    have := Nat.lt_two_pow_self (n := T + 1); omega
  refine runs_while (fun j t => PInv st j t) T _ ?_ ?_ st ⟨by simp [hp], hi, by simp, by simp⟩
  · intro j hj t hI
    have htcap : t.cap = st.cap := hI.U.cap
    have htt : t.w "cp.t" = T := by rw [hI.U.wreg _ (by simp)]; exact ht
    have hpow : 2 ^ (j + 1) ≤ 2 ^ (T + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of (x := j) (y := T) (by rw [evalW_var, hI.i]) (by rw [evalW_var, htt])
        (by omega)]
      simp [hj]
    · apply wp_sound
      have h2 : 2 ^ j * 2 < st.cap := by rw [← pow_succ]; omega
      simp [ltPowBody, inc, wp, hI.p, hI.i, fit, htcap, h2, show 2 < st.cap by omega,
        show 1 < st.cap by omega, show j + 1 < st.cap by omega]
      exact ⟨by simp [pow_succ], by simp, by simpa using hI.U, by simp [hI.c]; ring⟩
  · intro t hI
    have htcap : t.cap = st.cap := hI.U.cap
    have htt : t.w "cp.t" = T := by rw [hI.U.wreg _ (by simp)]; exact ht
    refine ⟨?_, t, hI, rfl⟩
    rw [evalW_lt_of (x := T) (y := T) (by rw [evalW_var, hI.i]) (by rw [evalW_var, htt])
      (by omega)]
    simp

/-! ## The level loop -/

structure LInv (st : State V) (T L : ℕ) (l : ℕ) (t : State V) : Prop where
  l_ : t.w "cp.l" = l
  q : t.w "cp.q" = 2 ^ (l * T)
  tau : ∀ l' < l, t.wa "cp.tau" l' = chdTau T l'
  M : ∀ l' ≤ l, t.wa "cp.M" l' = chdM T l'
  tauL : t.wlen "cp.tau" = L + 1
  ML : t.wlen "cp.M" = L + 2
  U : Unchanged st t ["cp.tau", "cp.M"] [] ["cp.q", "cp.l"] []
  c : t.cost = st.cost + 5 * l

theorem ltLoop_runs (st : State V) (T L : ℕ) (hT : 1 ≤ T) (ht : st.w "cp.t" = T)
    (hL : st.w "cp.L" = L) (hp : st.w "cp.p" = 2 ^ T) (hc : st.w "cp.c" = T * T * T)
    (hq : st.w "cp.q" = 1) (hl : st.w "cp.l" = 0) (htauL : st.wlen "cp.tau" = L + 1)
    (hML : st.wlen "cp.M" = L + 2) (hM0 : st.wa "cp.M" 0 = 1)
    (hcap : T * T * T * 2 ^ ((L + 1) * T) + L + 3 < st.cap) :
    Runs ops ltLoop st (fun r => ∃ t, LInv st T L (L + 1) t ∧ r = t.charge 1) := by
  have hT3 : 1 ≤ T * T * T := by nlinarith
  have hpowL : ∀ l ≤ L + 1, 2 ^ (l * T) ≤ 2 ^ ((L + 1) * T) := fun l hl =>
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hl)
  have hbig : ∀ l ≤ L + 1, T * T * T * 2 ^ (l * T) < st.cap := by
    intro l hl
    have := Nat.mul_le_mul_left (T * T * T) (hpowL l hl); omega
  have hbigq : ∀ l ≤ L + 1, 2 ^ (l * T) < st.cap := by
    intro l hl
    have h1 := hbig l hl
    have : 2 ^ (l * T) ≤ T * T * T * 2 ^ (l * T) := Nat.le_mul_of_pos_left _ hT3
    omega
  have hbigt : ∀ l ≤ L + 1, T * 2 ^ (l * T) < st.cap := by
    intro l hl
    have h1 := hbig l hl
    have : T * 2 ^ (l * T) ≤ T * T * T * 2 ^ (l * T) := by
      apply Nat.mul_le_mul_right
      nlinarith
    omega
  refine runs_while (fun l t => LInv st T L l t) (L + 1) _ ?_ ?_ st
    ⟨hl, by simp [hq], fun l' h => absurd h (Nat.not_lt_zero _),
     fun l' h => by rw [Nat.le_zero.mp h]; simpa [chdM] using hM0, htauL, hML, by simp, by simp⟩
  · intro l hlL t hI
    have htcap : t.cap = st.cap := hI.U.cap
    have htt : t.w "cp.t" = T := by rw [hI.U.wreg _ (by simp)]; exact ht
    have htL : t.w "cp.L" = L := by rw [hI.U.wreg _ (by simp)]; exact hL
    have htp : t.w "cp.p" = 2 ^ T := by rw [hI.U.wreg _ (by simp)]; exact hp
    have htc : t.w "cp.c" = T * T * T := by rw [hI.U.wreg _ (by simp)]; exact hc
    have hqq : 2 ^ (l * T) * 2 ^ T = 2 ^ ((l + 1) * T) := by rw [← pow_add]; ring_nf
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of (x := l) (y := L + 1) (by rw [evalW_var, hI.l_])
        (evalW_add_of (by rw [evalW_var, htL]) (evalW_lit_of (by omega)) (by omega)) (by omega)]
      simp [hlL]
    · apply wp_sound
      have h1 := hbig l (by omega)
      have h2 := hbigt l (by omega)
      have h3 := hbigq (l + 1) (by omega)
      rw [← hqq] at h3
      simp [ltBody, inc, wp, hI.l_, hI.q, htc, htt, htp, fit, htcap, h1, h2, h3, hI.tauL, hI.ML,
        show l < L + 1 by omega, show l + 1 < L + 2 by omega, show 1 < st.cap by omega,
        show l + 1 < st.cap by omega]
      refine ⟨by simp, by simp [hqq], fun l' hl' => ?_, fun l' hl' => ?_, by simp [hI.tauL],
        by simp [hI.ML], by simpa using hI.U, by simp [hI.c]; ring⟩
      · by_cases he : l' = l
        · subst he; simp [chdTau]; ring
        · simp [he]; exact hI.tau l' (by omega)
      · by_cases he : l' = l + 1
        · subst he; simp [chdM]
        · simp [he]; exact hI.M l' (by omega)
  · intro t hI
    have htcap : t.cap = st.cap := hI.U.cap
    have htL : t.w "cp.L" = L := by rw [hI.U.wreg _ (by simp)]; exact hL
    refine ⟨?_, t, hI, rfl⟩
    rw [evalW_lt_of (x := L + 1) (y := L + 1) (by rw [evalW_var, hI.l_])
      (evalW_add_of (by rw [evalW_var, htL]) (evalW_lit_of (by omega)) (by omega)) (by omega)]
    simp

/-! ## The whole table -/

theorem levelTab_runs (st : State V) (T L : ℕ) (hT : 1 ≤ T) (ht : st.w "cp.t" = T)
    (hL : st.w "cp.L" = L)
    (hcap : T * T * T * 2 ^ ((L + 1) * T) + 2 ^ (T + 1) + L + T + 5 < st.cap) :
    Runs ops levelTab st (fun r => (∀ l ≤ L, r.wa "cp.tau" l = chdTau T l) ∧
      (∀ l ≤ L + 1, r.wa "cp.M" l = chdM T l) ∧ r.wlen "cp.tau" = L + 1 ∧ r.wlen "cp.M" = L + 2 ∧
      Unchanged st r ["cp.tau", "cp.M"] [] ltWR [] ∧
      r.cost ≤ st.cost + 3 * T + 7 * L + 30) := by
  have hA0 : T * T * T ≤ T * T * T * 2 ^ ((L + 1) * T) := Nat.le_mul_of_pos_right _ (by positivity)
  generalize hA : T * T * T * 2 ^ ((L + 1) * T) = A at hcap hA0
  generalize hP : 2 ^ (T + 1) = P at hcap
  have hT3 : T * T * T < st.cap := by omega
  have hPc : P + T + 2 < st.cap := by omega
  unfold levelTab
  refine runs_seq (runs_wset (a := 1) (evalW_lit_of (by omega)) ?_)
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by simp; omega)) ?_)
  refine runs_seq ((ltPowLoop_runs _ T (by simp [ht]) (by simp) (by simp) (by simp [← hP]; omega)).mono ?_)
  rintro _ ⟨t1, h1, rfl⟩
  have ht1cap : t1.cap = st.cap := by rw [h1.U.cap]; simp
  have ht1t : t1.w "cp.t" = T := by rw [h1.U.wreg _ (by simp)]; simp [ht]
  have ht1L : t1.w "cp.L" = L := by rw [h1.U.wreg _ (by simp)]; simp [hL]
  have hc1 := h1.c
  simp only [State.charge_cost, State.setW_cost] at hc1
  apply wp_sound
  simp [wp, ht1L, ht1t, fit, ht1cap, show L + 1 < st.cap by omega, show L + 2 < st.cap by omega,
    show 2 < st.cap by omega,
    show 1 < st.cap by omega, show 0 < st.cap by omega, show T * T < st.cap by nlinarith, hT3]
  show Runs ops ltLoop _ _
  refine (ltLoop_runs _ T L hT (by simp [ht1t]) (by simp [ht1L]) (by simp [h1.p]) (by simp)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [ht1cap, hA]; omega)).mono ?_
  rintro _ ⟨t2, h2, rfl⟩
  refine ⟨fun l hl => h2.tau l (by omega), fun l hl => h2.M l hl, h2.tauL, h2.ML, ?_, ?_⟩
  · have hU1 : Unchanged st t1 ["cp.tau", "cp.M"] [] ltWR [] := by
      have h0 : Unchanged st ((((st.setW "cp.p" 1).charge 1).setW "cp.i" 0).charge 1)
          ["cp.tau", "cp.M"] [] ltWR [] := by simp [ltWR]
      exact h0.trans (h1.U.mono (by simp) (List.Subset.refl _) (by simp [ltWR]) (List.Subset.refl _))
    have hU2 := h2.U.mono (List.Subset.refl ["cp.tau", "cp.M"]) (List.Subset.refl [])
      (show ["cp.q", "cp.l"] ⊆ ltWR by simp [ltWR]) (List.Subset.refl [])
    have := hU1.trans ((show Unchanged t1 _ ["cp.tau", "cp.M"] [] ltWR [] by simp [ltWR]).trans hU2)
    simpa using this
  · have hc2 := h2.c
    simp only [State.charge_cost, State.setW_cost, State.storeW_cost, State.allocW_cost] at hc2 ⊢
    omega

end Frontier.CHD.L6

#print axioms Frontier.CHD.L6.levelTab_runs
