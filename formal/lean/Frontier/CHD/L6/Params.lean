import Frontier.CHD.L6.Util
import Frontier.CHD.L6.Prog
import Frontier.CHD.Dispatch
import Frontier.CostSkeleton

/-!
# Core parameters at RAM level (agent-10, obligation O16)

From the registers `cn`, `cm` (set by L6), `paramsProg` computes exactly the cost-chain parameters
of `Frontier.CostSkeleton`:
`cp.lg = lgN cn`, `cp.dd = dd cn cm`, `cp.t = tF cn cm`, `cp.k = kF cn cm`, `cp.L = LF cn cm`,
in `O(lgN cn)` steps.  NON-GATE (a core fragment).
-/

namespace Frontier.CHD.L6

open Frontier Frontier.RAM WExpr Stmt Frontier.CostSkeleton

def cpLgBody : Stmt := seq (wset "cp.x" (div (var "cp.x") (lit 2))) (inc "cp.lg")
def cpLgLoop : Stmt := .while (lt (lit 1) (var "cp.x")) cpLgBody

/-- the loop test `t³ dd² < lg²` -/
def cpTCond : WExpr :=
  lt (mul (mul (mul (var "cp.t") (var "cp.t")) (var "cp.t")) (mul (var "cp.dd") (var "cp.dd")))
    (mul (var "cp.lg") (var "cp.lg"))
def cpTLoop : Stmt := .while cpTCond (inc "cp.t")

/-- the loop test `(r+1)² ≤ t` -/
def cpSqCond : WExpr :=
  lt (mul (add (var "cp.r") (lit 1)) (add (var "cp.r") (lit 1))) (add (var "cp.t") (lit 1))
def cpSqLoop : Stmt := .while cpSqCond (inc "cp.r")

/-- `r := ⌊√t⌋`, `k := ⌈√t⌉`, `L := lg / t + 1`. -/
def sqTail : Stmt :=
  seq (wset "cp.r" (lit 0))
  (seq cpSqLoop
  (seq (ite (eq (mul (var "cp.r") (var "cp.r")) (var "cp.t")) (wset "cp.k" (var "cp.r"))
          (wset "cp.k" (add (var "cp.r") (lit 1))))
       (wset "cp.L" (add (div (var "cp.lg") (var "cp.t")) (lit 1)))))

/-- `dd`, `t = max 16 tpar`, then `sqTail`. -/
def tTail : Stmt :=
  seq (wset "cp.dd" (add (div (var "cm") (var "cn")) (lit 1)))
  (seq (wset "cp.t" (lit 1))
  (seq cpTLoop
  (seq (ite (lt (var "cp.t") (lit 16)) (wset "cp.t" (lit 16)) skip) sqTail)))

def paramsProg : Stmt :=
  seq (wset "cp.x" (var "cn"))
  (seq (wset "cp.lg" (lit 0))
  (seq cpLgLoop
  (seq (ite (lt (var "cp.lg") (lit 1)) (wset "cp.lg" (lit 1)) skip) tTail)))

def cpWR : List String := ["cp.x", "cp.lg", "cp.dd", "cp.t", "cp.r", "cp.k", "cp.L"]

variable {V : Type} {ops : VOps V}

/-! ## The halving loop: `cp.lg = Nat.log 2 cn` -/

structure LgInv (st : State V) (cn : ℕ) (j : ℕ) (t : State V) : Prop where
  x : t.w "cp.x" = cn / 2 ^ j
  lg : t.w "cp.lg" = j
  U : Unchanged st t [] [] ["cp.x", "cp.lg"] []
  c : t.cost = st.cost + 3 * j

theorem cpLgLoop_runs (st : State V) (cn : ℕ) (hx : st.w "cp.x" = cn) (hlg : st.w "cp.lg" = 0)
    (hcn1 : 1 ≤ cn) (hcap : cn + 2 < st.cap) :
    Runs ops cpLgLoop st (fun r => ∃ t, LgInv st cn (Nat.log 2 cn) t ∧ r = t.charge 1) := by
  refine runs_while (fun j t => LgInv st cn j t) (Nat.log 2 cn) _ ?_ ?_ st
    ⟨by simp [hx], hlg, by simp, by simp⟩
  · intro j hj t hI
    have htcap : t.cap = st.cap := hI.U.cap
    have h1 : 1 < cn / 2 ^ j := Dispatch.one_lt_div_pow_of_lt_log hj
    have hle : cn / 2 ^ j ≤ cn := Nat.div_le_self _ _
    have hlog : Nat.log 2 cn ≤ cn := Nat.log_le_self 2 cn
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of (x := 1) (y := cn / 2 ^ j) (evalW_lit_of (by rw [htcap]; omega))
        (by rw [evalW_var, hI.x]) (by rw [htcap]; omega)]
      simp [h1]
    · apply wp_sound
      simp [cpLgBody, inc, wp, hI.x, hI.lg, fit, htcap, show 2 < st.cap by omega,
        show 1 < st.cap by omega, show j + 1 < st.cap by omega]
      refine ⟨by simp [Nat.div_div_eq_div_mul, pow_succ], by simp, by simpa using hI.U,
        by simp [hI.c]; ring⟩
  · intro t hI
    have htcap : t.cap = st.cap := hI.U.cap
    have h2 : cn / 2 ^ Nat.log 2 cn < 2 := Dispatch.div_pow_log_lt_two cn
    refine ⟨?_, t, hI, rfl⟩
    rw [evalW_lt_of (x := 1) (y := cn / 2 ^ Nat.log 2 cn) (evalW_lit_of (by rw [htcap]; omega))
      (by rw [evalW_var, hI.x]) (by rw [htcap]; omega)]
    have : ¬ (1 < cn / 2 ^ Nat.log 2 cn) := by omega
    simp [this]

/-! ## The linear search for `tpar` -/

structure TInv (st : State V) (j : ℕ) (t : State V) : Prop where
  tt : t.w "cp.t" = j + 1
  U : Unchanged st t [] [] ["cp.t"] []
  c : t.cost = st.cost + 2 * j

theorem tpar_bounds (cn cm : ℕ) (hcn1 : 1 ≤ cn) {t : ℕ} (htc : t ≤ cn) :
    t * t * t * (dd cn cm * dd cn cm) < (cn + cm + 2) ^ 6 ∧ lgN cn * lgN cn < (cn + cm + 2) ^ 6 ∧
    t * t < (cn + cm + 2) ^ 6 ∧ t * t * t < (cn + cm + 2) ^ 6 ∧
    dd cn cm * dd cn cm < (cn + cm + 2) ^ 6 := by
  have hlgle : lgN cn ≤ cn := by unfold lgN; exact max_le hcn1 (Nat.log_le_self 2 cn)
  have hddle : dd cn cm ≤ cm + 1 := by unfold dd; have := Nat.div_le_self cm cn; omega
  have hk : 2 ≤ cn + cm + 2 := by omega
  have p3 : t * t * t ≤ (cn + cm + 2) ^ 3 := by
    calc t * t * t = t ^ 3 := by ring
      _ ≤ (cn + cm + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have p2 : dd cn cm * dd cn cm ≤ (cn + cm + 2) ^ 2 := by
    calc dd cn cm * dd cn cm = dd cn cm ^ 2 := by ring
      _ ≤ (cn + cm + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have p2' : t * t ≤ (cn + cm + 2) ^ 2 := by
    calc t * t = t ^ 2 := by ring
      _ ≤ (cn + cm + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have pl : lgN cn * lgN cn ≤ (cn + cm + 2) ^ 2 := by
    calc lgN cn * lgN cn = lgN cn ^ 2 := by ring
      _ ≤ (cn + cm + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have p5 : t * t * t * (dd cn cm * dd cn cm) ≤ (cn + cm + 2) ^ 5 := by
    calc t * t * t * (dd cn cm * dd cn cm) ≤ (cn + cm + 2) ^ 3 * (cn + cm + 2) ^ 2 :=
          Nat.mul_le_mul p3 p2
      _ = (cn + cm + 2) ^ 5 := by ring
  have q5 : (cn + cm + 2) ^ 5 < (cn + cm + 2) ^ 6 := Nat.pow_lt_pow_right (by omega) (by omega)
  have q2 : (cn + cm + 2) ^ 2 ≤ (cn + cm + 2) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (cn + cm + 2) ^ 3 ≤ (cn + cm + 2) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem cpTLoop_runs (st : State V) (cn cm : ℕ) (hcn1 : 1 ≤ cn)
    (hlg : st.w "cp.lg" = lgN cn) (hdd : st.w "cp.dd" = dd cn cm) (ht : st.w "cp.t" = 1)
    (hcap : (cn + cm + 2) ^ 6 ≤ st.cap) :
    Runs ops cpTLoop st (fun r => ∃ t, TInv st (tpar cn cm - 1) t ∧ r = t.charge 1) := by
  have hspec := tpar_spec cn cm
  have htle : tpar cn cm ≤ lgN cn := tpar_le_lgN cn cm
  have hlgle : lgN cn ≤ cn := by unfold lgN; exact max_le hcn1 (Nat.log_le_self 2 cn)
  have h6 : (cn + cm + 2) ^ 1 < (cn + cm + 2) ^ 6 :=
    Nat.pow_lt_pow_right (by omega) (by norm_num)
  have hcapS : cn + cm + 2 < st.cap := by rw [pow_one] at h6; omega
  refine runs_while (fun j t => TInv st j t) (tpar cn cm - 1) _ ?_ ?_ st
    ⟨ht, by simp, by simp⟩
  · intro j hj t hI
    have htcap : t.cap = st.cap := hI.U.cap
    have htlg : t.w "cp.lg" = lgN cn := by rw [hI.U.wreg _ (by simp)]; exact hlg
    have htdd : t.w "cp.dd" = dd cn cm := by rw [hI.U.wreg _ (by simp)]; exact hdd
    obtain ⟨b1, b2, b3, b4, b5⟩ := tpar_bounds cn cm hcn1 (t := j + 1) (by omega)
    have hlt : (j + 1) * (j + 1) * (j + 1) * (dd cn cm * dd cn cm) < lgN cn * lgN cn := by
      have hmin := Nat.find_min (tpar_exists cn cm) (show j + 1 < tpar cn cm by omega)
      have : ¬ lgN cn ^ 2 ≤ (j + 1) ^ 3 * dd cn cm ^ 2 := fun h => hmin ⟨by omega, h⟩
      have e1 : lgN cn ^ 2 = lgN cn * lgN cn := by ring
      have e2 : (j + 1) ^ 3 * dd cn cm ^ 2 = (j + 1) * (j + 1) * (j + 1) * (dd cn cm * dd cn cm) := by
        ring
      omega
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · simp [cpTCond, hI.tt, htlg, htdd, fit, htcap, hlt, show 1 < st.cap by omega,
        show (j + 1) * (j + 1) < st.cap by omega, show (j + 1) * (j + 1) * (j + 1) < st.cap by omega,
        show dd cn cm * dd cn cm < st.cap by omega,
        show (j + 1) * (j + 1) * (j + 1) * (dd cn cm * dd cn cm) < st.cap by omega,
        show lgN cn * lgN cn < st.cap by omega]
    · apply wp_sound
      simp [inc, wp, hI.tt, fit, htcap, show 1 < st.cap by omega, show j + 1 + 1 < st.cap by omega]
      exact ⟨by simp, by simpa using hI.U, by simp [hI.c]; ring⟩
  · intro t hI
    have htcap : t.cap = st.cap := hI.U.cap
    have htlg : t.w "cp.lg" = lgN cn := by rw [hI.U.wreg _ (by simp)]; exact hlg
    have htdd : t.w "cp.dd" = dd cn cm := by rw [hI.U.wreg _ (by simp)]; exact hdd
    have hj1 : tpar cn cm - 1 + 1 = tpar cn cm := by omega
    obtain ⟨b1, b2, b3, b4, b5⟩ := tpar_bounds cn cm hcn1 (t := tpar cn cm) (by omega)
    have hge : ¬ (tpar cn cm * tpar cn cm * tpar cn cm * (dd cn cm * dd cn cm) < lgN cn * lgN cn) := by
      have := hspec.2
      have e1 : lgN cn ^ 2 = lgN cn * lgN cn := by ring
      have e2 : tpar cn cm ^ 3 * dd cn cm ^ 2 =
          tpar cn cm * tpar cn cm * tpar cn cm * (dd cn cm * dd cn cm) := by ring
      omega
    refine ⟨?_, t, hI, rfl⟩
    have htt : t.w "cp.t" = tpar cn cm := by rw [hI.tt, hj1]
    simp [cpTCond, htt, htlg, htdd, fit, htcap, hge, show 1 < st.cap by omega,
      show 0 < st.cap by omega,
      show tpar cn cm * tpar cn cm < st.cap by omega,
      show tpar cn cm * tpar cn cm * tpar cn cm < st.cap by omega,
      show dd cn cm * dd cn cm < st.cap by omega,
      show tpar cn cm * tpar cn cm * tpar cn cm * (dd cn cm * dd cn cm) < st.cap by omega,
      show lgN cn * lgN cn < st.cap by omega]

/-! ## The integer square root -/

structure SqInv (st : State V) (j : ℕ) (t : State V) : Prop where
  r : t.w "cp.r" = j
  U : Unchanged st t [] [] ["cp.r"] []
  c : t.cost = st.cost + 2 * j

theorem cpSqLoop_runs (st : State V) (T : ℕ) (ht : st.w "cp.t" = T) (hr : st.w "cp.r" = 0)
    (hcap : (T + 2) * (T + 2) < st.cap) :
    Runs ops cpSqLoop st (fun r => ∃ t, SqInv st (Nat.sqrt T) t ∧ r = t.charge 1) := by
  have hsq := Nat.sqrt_le' T
  have hsq2 := Nat.lt_succ_sqrt' T
  have hsT : Nat.sqrt T ≤ T := Nat.sqrt_le_self T
  refine runs_while (fun j t => SqInv st j t) (Nat.sqrt T) _ ?_ ?_ st ⟨hr, by simp, by simp⟩
  · intro j hj t hI
    have htcap : t.cap = st.cap := hI.U.cap
    have htt : t.w "cp.t" = T := by rw [hI.U.wreg _ (by simp)]; exact ht
    have hle : (j + 1) * (j + 1) ≤ T := by
      have : (j + 1) ^ 2 ≤ Nat.sqrt T ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have e : (j + 1) ^ 2 = (j + 1) * (j + 1) := by ring
      omega
    have hb : (j + 1) * (j + 1) ≤ (T + 2) * (T + 2) := Nat.mul_le_mul (by omega) (by omega)
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · simp [cpSqCond, hI.r, htt, fit, htcap, show 1 < st.cap by nlinarith,
        show j + 1 < st.cap by nlinarith, show (j + 1) * (j + 1) < st.cap by omega,
        show T + 1 < st.cap by nlinarith, hle]
    · apply wp_sound
      simp [inc, wp, hI.r, fit, htcap, show 1 < st.cap by nlinarith, show j + 1 < st.cap by nlinarith]
      exact ⟨by simp, by simpa using hI.U, by simp [hI.c]; ring⟩
  · intro t hI
    have htcap : t.cap = st.cap := hI.U.cap
    have htt : t.w "cp.t" = T := by rw [hI.U.wreg _ (by simp)]; exact ht
    have hgt : ¬ ((Nat.sqrt T + 1) * (Nat.sqrt T + 1) < T + 1) := by
      have e : (Nat.sqrt T + 1) ^ 2 = (Nat.sqrt T + 1) * (Nat.sqrt T + 1) := by ring
      have : T < (Nat.sqrt T + 1) ^ 2 := by have := hsq2; nlinarith
      omega
    have hb : (Nat.sqrt T + 1) * (Nat.sqrt T + 1) ≤ (T + 2) * (T + 2) := Nat.mul_le_mul (by omega) (by omega)
    have hlt' : T < (Nat.sqrt T + 1) * (Nat.sqrt T + 1) := by omega
    refine ⟨?_, t, hI, rfl⟩
    simp [cpSqCond, hI.r, htt, fit, htcap, hgt, hlt', not_le.mpr hlt', show 1 < st.cap by nlinarith,
      show 0 < st.cap by nlinarith, show Nat.sqrt T + 1 < st.cap by nlinarith,
      show (Nat.sqrt T + 1) * (Nat.sqrt T + 1) < st.cap by omega, show T + 1 < st.cap by nlinarith]

/-! ## The tails and the whole parameter block -/

theorem sqTail_runs (u : State V) (T lgv : ℕ) (ht : u.w "cp.t" = T) (hlg : u.w "cp.lg" = lgv)
    (hT : 1 ≤ T) (hcap : (T + 2) * (T + 2) < u.cap) (hlgc : lgv + 1 < u.cap) :
    Runs ops sqTail u (fun r => r.w "cp.k" = Nat.sqrt T + (if Nat.sqrt T * Nat.sqrt T = T then 0 else 1) ∧
      r.w "cp.L" = lgv / T + 1 ∧ r.w "cp.t" = T ∧ r.w "cp.lg" = lgv ∧
      Unchanged u r [] [] ["cp.r", "cp.k", "cp.L"] [] ∧ r.cost ≤ u.cost + 2 * Nat.sqrt T + 8) := by
  have hsT : Nat.sqrt T ≤ T := Nat.sqrt_le_self T
  have hsq' : Nat.sqrt T * Nat.sqrt T ≤ T := Nat.sqrt_le T
  have hTc : T < u.cap := by nlinarith
  unfold sqTail
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by nlinarith)) ?_)
  refine runs_seq ((cpSqLoop_runs _ T (by simp [ht]) (by simp) (by simpa using hcap)).mono ?_)
  rintro _ ⟨t1, h1, rfl⟩
  have ht1cap : t1.cap = u.cap := by rw [h1.U.cap]; simp
  have ht1t : t1.w "cp.t" = T := by rw [h1.U.wreg _ (by simp)]; simp [ht]
  have ht1lg : t1.w "cp.lg" = lgv := by rw [h1.U.wreg _ (by simp)]; simp [hlg]
  have hT0 : T ≠ 0 := by omega
  apply wp_sound
  by_cases hsq : Nat.sqrt T * Nat.sqrt T = T
  · simp [wp, h1.r, ht1t, ht1lg, fit, ht1cap, hsq, hT0, hTc, show Nat.sqrt T * Nat.sqrt T < u.cap by nlinarith,
      show 1 < u.cap by nlinarith, show 0 < u.cap by nlinarith, show lgv / T + 1 < u.cap by
        have := Nat.div_le_self lgv T; omega]
    refine ⟨?_, ?_⟩
    · have hU1 : Unchanged ((u.setW "cp.r" 0).charge 1) t1 [] [] ["cp.r", "cp.k", "cp.L"] [] :=
        h1.U.mono (List.Subset.refl _) (List.Subset.refl _) (by simp) (List.Subset.refl _)
      have hU0 : Unchanged u ((u.setW "cp.r" 0).charge 1) [] [] ["cp.r", "cp.k", "cp.L"] [] := by simp
      simpa using hU0.trans hU1
    · have := h1.c; simp at this ⊢; omega
  · simp [wp, h1.r, ht1t, ht1lg, fit, ht1cap, hsq, hT0, hTc, show Nat.sqrt T * Nat.sqrt T < u.cap by nlinarith,
      show 1 < u.cap by nlinarith, show 0 < u.cap by nlinarith, show Nat.sqrt T + 1 < u.cap by nlinarith,
      show lgv / T + 1 < u.cap by have := Nat.div_le_self lgv T; omega]
    refine ⟨?_, ?_⟩
    · have hU1 : Unchanged ((u.setW "cp.r" 0).charge 1) t1 [] [] ["cp.r", "cp.k", "cp.L"] [] :=
        h1.U.mono (List.Subset.refl _) (List.Subset.refl _) (by simp) (List.Subset.refl _)
      have hU0 : Unchanged u ((u.setW "cp.r" 0).charge 1) [] [] ["cp.r", "cp.k", "cp.L"] [] := by simp
      simpa using hU0.trans hU1
    · have := h1.c; simp at this ⊢; omega

theorem tTail_runs (u : State V) (cn cm : ℕ) (hcn : u.w "cn" = cn) (hcm : u.w "cm" = cm)
    (hlg : u.w "cp.lg" = lgN cn) (hcn1 : 1 ≤ cn) (hcap : (cn + cm + 2) ^ 6 ≤ u.cap) :
    Runs ops tTail u (fun r => r.w "cp.dd" = dd cn cm ∧ r.w "cp.t" = tF cn cm ∧
      r.w "cp.k" = kF cn cm ∧ r.w "cp.L" = LF cn cm ∧ r.w "cp.lg" = lgN cn ∧
      Unchanged u r [] [] ["cp.dd", "cp.t", "cp.r", "cp.k", "cp.L"] [] ∧
      r.cost ≤ u.cost + 2 * tF cn cm + 2 * Nat.sqrt (tF cn cm) + 20) := by
  have h6 : (cn + cm + 2) ^ 1 < (cn + cm + 2) ^ 6 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  have hcapS : cn + cm + 2 < u.cap := by rw [pow_one] at h6; omega
  have htF : tF cn cm ≤ 16 + lgN cn := tF_le cn cm
  have hlgle : lgN cn ≤ cn := by unfold lgN; exact max_le hcn1 (Nat.log_le_self 2 cn)
  have hsq : (tF cn cm + 2) * (tF cn cm + 2) < u.cap := by
    have hA : (tF cn cm + 2) * (tF cn cm + 2) ≤ (cn + 18) * (cn + 18) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hB : (cn + 18) * (cn + 18) < 81 * ((cn + 2) * (cn + 2)) := by nlinarith
    have hC : 81 ≤ (cn + 2) ^ 4 := by
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ (cn + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have hD : 81 * ((cn + 2) * (cn + 2)) ≤ (cn + 2) ^ 6 := by
      calc 81 * ((cn + 2) * (cn + 2)) ≤ (cn + 2) ^ 4 * ((cn + 2) * (cn + 2)) :=
            Nat.mul_le_mul_right _ hC
        _ = (cn + 2) ^ 6 := by ring
    have hE : (cn + 2) ^ 6 ≤ (cn + cm + 2) ^ 6 := Nat.pow_le_pow_left (by omega) 6
    omega
  have hddv : cm / cn + 1 = dd cn cm := rfl
  have hddc : cm / cn + 1 < u.cap := by have := Nat.div_le_self cm cn; omega
  have hc729 : 729 ≤ u.cap := le_trans (by
    calc 729 = 3 ^ 6 := by norm_num
      _ ≤ (cn + cm + 2) ^ 6 := Nat.pow_le_pow_left (by omega) 6) hcap
  unfold tTail
  refine runs_seq (runs_wset (a := cm / cn + 1) (evalW_add_of
    (Dispatch.evalW_div_of (by rw [evalW_var, hcm]) (by rw [evalW_var, hcn]) (by omega))
    (evalW_lit_of (by omega)) hddc) ?_)
  refine runs_seq (runs_wset (a := 1) (evalW_lit_of (by simp; omega)) ?_)
  refine runs_seq ((cpTLoop_runs _ cn cm hcn1 (by simp [hlg]) (by simp [hddv]) (by simp)
    (by simpa using hcap)).mono ?_)
  rintro _ ⟨t2, h2, rfl⟩
  have ht2cap : t2.cap = u.cap := by rw [h2.U.cap]; simp
  have hspec := tpar_spec cn cm
  have htp : t2.w "cp.t" = tpar cn cm := by rw [h2.tt]; omega
  have ht2lg : t2.w "cp.lg" = lgN cn := by rw [h2.U.wreg _ (by simp)]; simp [hlg]
  have ht2dd : t2.w "cp.dd" = dd cn cm := by rw [h2.U.wreg _ (by simp)]; simp [hddv]
  have hU2 : Unchanged u t2 [] [] ["cp.dd", "cp.t", "cp.r", "cp.k", "cp.L"] [] := by
    have h0 : Unchanged u ((((u.setW "cp.dd" (cm / cn + 1)).charge 1).setW "cp.t" 1).charge 1)
        [] [] ["cp.dd", "cp.t", "cp.r", "cp.k", "cp.L"] [] := by simp
    exact h0.trans (h2.U.mono (List.Subset.refl _) (List.Subset.refl _) (by simp) (List.Subset.refl _))
  have hc2 := h2.c
  simp only [State.charge_cost, State.setW_cost] at hc2
  refine runs_seq ?_
  by_cases h16 : tpar cn cm < 16
  · have htF16 : tF cn cm = 16 := by unfold tF; omega
    refine runs_ite_true (x := 1) (by
      rw [evalW_lt_of (x := tpar cn cm) (y := 16) (by rw [evalW_var]; simpa using htp)
        (evalW_lit_of (by simp [ht2cap]; omega)) (by simp [ht2cap]; omega)]
      simp [h16]) one_ne_zero ?_
    refine runs_wset (a := 16) (evalW_lit_of (by simp [ht2cap]; omega)) ?_
    refine (sqTail_runs _ 16 (lgN cn) (by simp) (by simp [ht2lg]) (by norm_num)
      (by simp [ht2cap]; rw [htF16] at hsq; omega) (by simp [ht2cap]; omega)).mono ?_
    rintro r ⟨hk, hL, ht, hlg', hU3, hc3⟩
    refine ⟨?_, by rw [ht, htF16], ?_, ?_, hlg', ?_, ?_⟩
    · rw [(hU3.wreg _ (by simp))]; simp [ht2dd]
    · rw [hk]; unfold kF; rw [htF16]
    · rw [hL]; unfold LF; rw [htF16]
    · have h4 : Unchanged t2 ((((t2.charge 1).charge 1).setW "cp.t" 16).charge 1)
          [] [] ["cp.dd", "cp.t", "cp.r", "cp.k", "cp.L"] [] := by simp
      exact hU2.trans (h4.trans (hU3.mono (List.Subset.refl _) (List.Subset.refl _) (by simp)
        (List.Subset.refl _)))
    · simp only [State.charge_cost, State.setW_cost] at hc3
      rw [htF16]
      have : tpar cn cm - 1 ≤ 15 := by omega
      omega
  · have htFp : tF cn cm = tpar cn cm := by unfold tF; omega
    refine runs_ite_false (by
      rw [evalW_lt_of (x := tpar cn cm) (y := 16) (by rw [evalW_var]; simpa using htp)
        (evalW_lit_of (by simp [ht2cap]; omega)) (by simp [ht2cap]; omega)]
      simp [h16]) (runs_skip ?_)
    refine (sqTail_runs _ (tpar cn cm) (lgN cn) (by simpa using htp) (by simp [ht2lg]) hspec.1
      (by simp [ht2cap]; rw [← htFp]; exact hsq) (by simp [ht2cap]; omega)).mono ?_
    rintro r ⟨hk, hL, ht, hlg', hU3, hc3⟩
    refine ⟨?_, by rw [ht, htFp], ?_, ?_, hlg', ?_, ?_⟩
    · rw [(hU3.wreg _ (by simp))]; simp [ht2dd]
    · rw [hk]; unfold kF; rw [htFp]
    · rw [hL]; unfold LF; rw [htFp]
    · have h4 : Unchanged t2 (((t2.charge 1).charge 1).charge 1)
          [] [] ["cp.dd", "cp.t", "cp.r", "cp.k", "cp.L"] [] := by simp
      exact hU2.trans (h4.trans (hU3.mono (List.Subset.refl _) (List.Subset.refl _) (by simp)
        (List.Subset.refl _)))
    · simp only [State.charge_cost] at hc3
      rw [htFp]
      omega

/-- **O16**: the parameter block computes exactly `lgN`, `dd`, `tF`, `kF`, `LF` of `(cn, cm)`. -/
theorem paramsProg_runs (st : State V) (cn cm : ℕ) (hcn : st.w "cn" = cn) (hcm : st.w "cm" = cm)
    (hcn1 : 1 ≤ cn) (hcap : (cn + cm + 2) ^ 6 ≤ st.cap) :
    Runs ops paramsProg st (fun r => r.w "cp.lg" = lgN cn ∧ r.w "cp.dd" = dd cn cm ∧
      r.w "cp.t" = tF cn cm ∧ r.w "cp.k" = kF cn cm ∧ r.w "cp.L" = LF cn cm ∧
      Unchanged st r [] [] cpWR [] ∧
      r.cost ≤ st.cost + 3 * cn + 2 * tF cn cm + 2 * Nat.sqrt (tF cn cm) + 30) := by
  have h6 : (cn + cm + 2) ^ 1 < (cn + cm + 2) ^ 6 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  have hcapS : cn + cm + 2 < st.cap := by rw [pow_one] at h6; omega
  have hlog : Nat.log 2 cn ≤ cn := Nat.log_le_self 2 cn
  unfold paramsProg
  refine runs_seq (runs_wset (a := cn) (by rw [evalW_var, hcn]) ?_)
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by simp; omega)) ?_)
  refine runs_seq ((cpLgLoop_runs _ cn (by simp) (by simp) hcn1 (by simp; omega)).mono ?_)
  rintro _ ⟨t1, h1, rfl⟩
  have ht1cap : t1.cap = st.cap := by rw [h1.U.cap]; simp
  have ht1cn : t1.w "cn" = cn := by rw [h1.U.wreg _ (by simp)]; simp [hcn]
  have ht1cm : t1.w "cm" = cm := by rw [h1.U.wreg _ (by simp)]; simp [hcm]
  have hU1 : Unchanged st t1 [] [] cpWR [] := by
    have h0 : Unchanged st ((((st.setW "cp.x" cn).charge 1).setW "cp.lg" 0).charge 1)
        [] [] cpWR [] := by simp [cpWR]
    exact h0.trans (h1.U.mono (List.Subset.refl _) (List.Subset.refl _) (by simp [cpWR])
      (List.Subset.refl _))
  have hc1 := h1.c
  simp only [State.charge_cost, State.setW_cost] at hc1
  refine runs_seq ?_
  by_cases hl1 : Nat.log 2 cn < 1
  · have hlg1 : lgN cn = 1 := by unfold lgN; omega
    refine runs_ite_true (x := 1) (by
      rw [evalW_lt_of (x := Nat.log 2 cn) (y := 1) (by rw [evalW_var]; simpa using h1.lg)
        (evalW_lit_of (by simp [ht1cap]; omega)) (by simp [ht1cap]; omega)]
      simp [hl1]) one_ne_zero ?_
    refine runs_wset (a := 1) (evalW_lit_of (by simp [ht1cap]; omega)) ?_
    refine (tTail_runs _ cn cm (by simp [ht1cn]) (by simp [ht1cm]) (by simp [hlg1]) hcn1
      (by simp [ht1cap]; exact hcap)).mono ?_
    rintro r ⟨hdd, ht, hk, hL, hlg, hU2, hc2⟩
    refine ⟨hlg, hdd, ht, hk, hL, ?_, ?_⟩
    · have h4 : Unchanged t1 ((((t1.charge 1).charge 1).setW "cp.lg" 1).charge 1) [] [] cpWR [] := by
        simp [cpWR]
      exact hU1.trans (h4.trans (hU2.mono (List.Subset.refl _) (List.Subset.refl _) (by simp [cpWR])
        (List.Subset.refl _)))
    · simp only [State.charge_cost, State.setW_cost] at hc2; omega
  · have hlgv : lgN cn = Nat.log 2 cn := by unfold lgN; omega
    refine runs_ite_false (by
      rw [evalW_lt_of (x := Nat.log 2 cn) (y := 1) (by rw [evalW_var]; simpa using h1.lg)
        (evalW_lit_of (by simp [ht1cap]; omega)) (by simp [ht1cap]; omega)]
      simp [hl1]) (runs_skip ?_)
    refine (tTail_runs _ cn cm (by simp [ht1cn]) (by simp [ht1cm]) (by simp [h1.lg, hlgv]) hcn1
      (by simp [ht1cap]; exact hcap)).mono ?_
    rintro r ⟨hdd, ht, hk, hL, hlg, hU2, hc2⟩
    refine ⟨hlg, hdd, ht, hk, hL, ?_, ?_⟩
    · have h4 : Unchanged t1 (((t1.charge 1).charge 1).charge 1) [] [] cpWR [] := by simp
      exact hU1.trans (h4.trans (hU2.mono (List.Subset.refl _) (List.Subset.refl _) (by simp [cpWR])
        (List.Subset.refl _)))
    · simp only [State.charge_cost] at hc2; omega

end Frontier.CHD.L6

#print axioms Frontier.CHD.L6.paramsProg_runs
