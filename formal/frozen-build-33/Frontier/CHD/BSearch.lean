import Frontier.RAMRep
import Frontier.RAMWP
import Frontier.CHD.LabRAM

/-!
# BSearch — a verified RAM binary search with a pluggable probe (agent-02, for B-L3, NON-GATE)

Finds the FIRST index `j < sz` satisfying a monotone predicate `P` with `P (sz - 1)`, using a probe
fragment `T` that sets `bs.p := [P (bs.mid)]`.  Registers: `bs.sz` (input), `bs.lo` (output),
`bs.hi`, `bs.mid`, `bs.p`.  Cost `≤ 3 + (CT + 5) · (log₂ (sz - 1) + 1)`.

Use in DS' Insert: `P j := sep(stk[b + j]) ⪯ key` on the separator stack (front = top = smallest),
probe = load the separator block of `stk[b + mid]` (`loadA`) and `cmp` the key against it.
-/

namespace Frontier.RAM.BSearch

open Frontier.RAM WExpr Stmt LabRAM

variable {V : Type} {ops : VOps V}

/-- Registers owned by the search. -/
def bsRegs : List String := ["bs.lo", "bs.hi", "bs.mid", "bs.p"]

/-- The search, with probe `T`. -/
def bsearch (T : Stmt) : Stmt :=
  seq (wset "bs.lo" (lit 0))
  (seq (wset "bs.hi" (sub (var "bs.sz") (lit 1)))
  (.while (lt (var "bs.lo") (var "bs.hi"))
    (seq (wset "bs.mid" (div (add (var "bs.lo") (var "bs.hi")) (lit 2)))
    (seq T
    (ite (var "bs.p") (wset "bs.hi" (var "bs.mid"))
                      (wset "bs.lo" (add (var "bs.mid") (lit 1))))))))

/-- What the probe must satisfy: from any state satisfying the context predicate `TPre` with
`bs.mid = j < sz`, it sets `bs.p := [P j]`, keeps `bs.lo bs.hi bs.mid bs.sz`, keeps `TPre`, the
cap, and costs between `0` and `CT`. -/
def ProbeSpec (T : Stmt) (TPre : State V → Prop) (P : ℕ → Prop) [DecidablePred P] (sz CT : ℕ) :
    Prop :=
  ∀ st : State V, TPre st → st.w "bs.mid" < sz →
    Runs ops T st (fun r => TPre r ∧ r.w "bs.p" = (if P (st.w "bs.mid") then 1 else 0) ∧
      r.w "bs.lo" = st.w "bs.lo" ∧ r.w "bs.hi" = st.w "bs.hi" ∧ r.w "bs.mid" = st.w "bs.mid" ∧
      r.w "bs.sz" = st.w "bs.sz" ∧ r.cap = st.cap ∧ st.cost ≤ r.cost ∧ r.cost ≤ st.cost + CT)

/-- The context predicate is stable under the search's own register writes and charges. -/
def PreStable (TPre : State V → Prop) : Prop :=
  (∀ st k, TPre st → TPre (st.charge k)) ∧
  (∀ st x a, x ∈ bsRegs → TPre st → TPre (st.setW x a))

theorem div2_le_of {lo hi : ℕ} (h : lo ≤ hi) : (lo + hi) / 2 - lo = (hi - lo) / 2 := by omega

@[simp] theorem evalW_div' (s : State V) (a b : WExpr) :
    evalW s (.div a b) = (evalW s a).bind (fun x => (evalW s b).bind
      (fun y => if y = 0 then none else some (x / y))) := rfl

/-- **Spec of `bsearch`.**  `P` monotone on `[0, sz)` with `P (sz - 1)`, `1 ≤ sz`, `2 sz < cap`:
the result `bs.lo = j` is the least index with `P j`, and the cost is logarithmic. -/
theorem bsearch_spec (T : Stmt) (TPre : State V → Prop) (P : ℕ → Prop) [DecidablePred P]
    (sz CT : ℕ) (hT : ProbeSpec (ops := ops) T TPre P sz CT) (hS : PreStable TPre)
    (hmono : ∀ i j, i ≤ j → j < sz → P i → P j) (hsz : 1 ≤ sz) (hlast : P (sz - 1))
    (st : State V) (hpre : TPre st) (hszr : st.w "bs.sz" = sz) (hcap : 2 * sz + 2 < st.cap) :
    Runs ops (bsearch T) st (fun r => TPre r ∧ r.w "bs.lo" < sz ∧ P (r.w "bs.lo") ∧
      (∀ i < r.w "bs.lo", ¬ P i) ∧ r.cap = st.cap ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + 3 + (CT + 5) * (Nat.log 2 (sz - 1) + 1)) := by
  -- the loop invariant (with the iteration count `k` and the cost)
  let c0 := st.cost + 2
  let I : State V → Prop := fun q => ∃ k lo hi, q.w "bs.lo" = lo ∧ q.w "bs.hi" = hi ∧
    q.w "bs.sz" = sz ∧ lo ≤ hi ∧ hi < sz ∧ P hi ∧ (∀ i < lo, ¬ P i) ∧
    hi - lo ≤ (sz - 1) / 2 ^ k ∧ (k = 0 ∨ 2 ^ (k - 1) ≤ sz - 1) ∧
    c0 ≤ q.cost ∧ q.cost ≤ c0 + (CT + 5) * k ∧ TPre q ∧ q.cap = st.cap
  have hcap1 : 1 < st.cap := by omega
  apply wp_sound
  rw [bsearch, wp_seq, wp_wset_of (a := 0) (by simp [fit_of_lt hcap1, fit, show 0 < st.cap by omega]),
    wp_seq, wp_wset_of (a := sz - 1) (by
      simp [hszr, fit_of_lt hcap1])]
  -- the loop
  show Runs ops _ _ _
  refine runs_while_var I (fun q => q.w "bs.hi" - q.w "bs.lo") _ ?_ _ ?_
  · rintro q ⟨k, lo, hi, hlo, hhi, hszq, hle, hhisz, hPhi, hlow, hw, hk, hc0, hc, hpq, hcapq⟩
    have hcq : 1 < q.cap := by rw [hcapq]; exact hcap1
    have hev : evalW q (lt (var "bs.lo") (var "bs.hi")) = some (if lo < hi then 1 else 0) := by
      rw [evalW_lt', evalW_var, evalW_var, hlo, hhi]
      simp only [Option.bind_some]
      exact fit_bit hcq _
    refine ⟨if lo < hi then 1 else 0, hev, ?_, ?_⟩
    · -- one iteration
      intro hne
      have hlt : lo < hi := by by_contra h; exact hne (by simp [h])
      have hmid : (lo + hi) / 2 < sz := by omega
      apply runs_seq
      apply wp_sound
      rw [wp_wset_of (a := (lo + hi) / 2) (by
        have h2 : lo + hi < q.cap := by rw [hcapq]; omega
        simp [hlo, hhi, fit_of_lt h2, fit_of_lt (show 2 < q.cap by rw [hcapq]; omega)])]
      set q1 := ((q.charge 1).setW "bs.mid" ((lo + hi) / 2)).charge 1 with hq1
      have hpre1 : TPre q1 := hS.1 _ _ (hS.2 _ _ _ (by simp [bsRegs]) (hS.1 _ _ hpq))
      have hmid1 : q1.w "bs.mid" = (lo + hi) / 2 := by simp [hq1]
      apply runs_seq
      refine (hT q1 hpre1 (by rw [hmid1]; exact hmid)).mono ?_
      rintro r ⟨hpr, hp, hlor, hhir, hmidr, hszr', hcapr, hcr1, hcr2⟩
      rw [hmid1] at hp hmidr
      have hlor' : r.w "bs.lo" = lo := by rw [hlor]; simp [hq1, hlo]
      have hhir' : r.w "bs.hi" = hi := by rw [hhir]; simp [hq1, hhi]
      have hszr'' : r.w "bs.sz" = sz := by rw [hszr']; simp [hq1, hszq]
      have hcapr' : r.cap = st.cap := by rw [hcapr]; simp [hq1, hcapq]
      have hq1c : q1.cost = q.cost + 2 := by simp [hq1]
      have hcr : 1 < r.cap := by rw [hcapr']; exact hcap1
      apply wp_sound
      rw [wp_ite_var]
      refine ⟨fun hp1 => ?_, fun hp0 => ?_⟩
      · -- `P mid`: `hi := mid`
        have hPm : P ((lo + hi) / 2) := by
          by_contra h; rw [hp, if_neg h] at hp1; exact hp1 rfl
        rw [wp_wset_of (a := (lo + hi) / 2) (by simp [hmidr])]
        refine ⟨⟨k + 1, lo, (lo + hi) / 2, by simp [hlor'], by simp, by simp [hszr''], by omega,
          hmid, hPm, hlow, ?_, Or.inr ?_, ?_, ?_, hS.1 _ _ (hS.2 _ _ _ (by simp [bsRegs])
          (hS.1 _ _ hpr)), by simp [hcapr']⟩, ?_⟩
        · rw [div2_le_of (show lo ≤ hi by omega), Nat.pow_succ, ← Nat.div_div_eq_div_mul]
          exact Nat.div_le_div_right hw
        · simp only [Nat.add_sub_cancel]
          have h1 : 1 ≤ (sz - 1) / 2 ^ k := by omega
          have := (Nat.le_div_iff_mul_le (by positivity)).mp h1
          simpa using this
        · simp only [State.charge_cost, State.setW_cost]; omega
        · simp only [State.charge_cost, State.setW_cost]; rw [Nat.mul_succ]; omega
        · simp only [State.charge_w, State.setW_w, ↓reduceIte, hlor', hlo, hhi]
          simp only [show ("bs.lo" = "bs.hi") = False from by decide, if_false, hlor']; omega
      · -- `¬ P mid`: `lo := mid + 1`
        have hPm : ¬ P ((lo + hi) / 2) := by
          intro h; rw [hp, if_pos h] at hp0; exact one_ne_zero hp0
        rw [wp_wset_of (a := (lo + hi) / 2 + 1) (by
          have h2 : (lo + hi) / 2 + 1 < r.cap := by rw [hcapr']; omega
          simp [hmidr, fit_of_lt h2, fit_of_lt hcr])]
        refine ⟨⟨k + 1, (lo + hi) / 2 + 1, hi, by simp, by simp [hhir'], by simp [hszr''],
          by omega, hhisz, hPhi, ?_, ?_, Or.inr ?_, ?_, ?_, hS.1 _ _ (hS.2 _ _ _
          (by simp [bsRegs]) (hS.1 _ _ hpr)), by simp [hcapr']⟩, ?_⟩
        · intro i hi'
          by_cases hil : i < lo
          · exact hlow i hil
          · intro hPi; exact hPm (hmono i _ (by omega) hmid hPi)
        · rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
          have : hi - ((lo + hi) / 2 + 1) ≤ (hi - lo) / 2 := by omega
          exact this.trans (Nat.div_le_div_right hw)
        · simp only [Nat.add_sub_cancel]
          have h1 : 1 ≤ (sz - 1) / 2 ^ k := by omega
          have := (Nat.le_div_iff_mul_le (by positivity)).mp h1
          simpa using this
        · simp only [State.charge_cost, State.setW_cost]; omega
        · simp only [State.charge_cost, State.setW_cost]; rw [Nat.mul_succ]; omega
        · simp only [State.charge_w, State.setW_w, ↓reduceIte, hhir', hlo, hhi]
          simp only [show ("bs.hi" = "bs.lo") = False from by decide, if_false, hhir']; omega
    · -- exit
      intro hz
      have hlh : lo = hi := by
        by_contra h; have : lo < hi := by omega
        simp [this] at hz
      subst hlh
      refine ⟨hS.1 _ _ hpq, by simp [hlo]; omega, by simp [hlo]; exact hPhi, ?_, by simp [hcapq],
        ?_, ?_⟩
      · simp [hlo]; exact hlow
      · simp; omega
      · simp only [State.charge_cost]
        have hkb : k ≤ Nat.log 2 (sz - 1) + 1 := by
          rcases hk with hk | hk
          · omega
          · have := Nat.le_log_of_pow_le (by norm_num) hk
            omega
        have := Nat.mul_le_mul_left (CT + 5) hkb
        omega
  · -- initial invariant
    refine ⟨0, 0, sz - 1, by simp, by simp, by simp [hszr], by omega, by omega, hlast,
      fun i hi => absurd hi (Nat.not_lt_zero _), by simp, Or.inl rfl, by simp [c0], by simp [c0],
      hS.1 _ _ (hS.2 _ _ _ (by simp [bsRegs]) (hS.1 _ _ (hS.2 _ _ _ (by simp [bsRegs]) hpre))),
      by simp⟩

end Frontier.RAM.BSearch
