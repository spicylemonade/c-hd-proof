import Frontier.CHD.L6.Util
import Frontier.CHD.L6.Prog
import Frontier.CHD.L6.DedupModel

/-!
# L6 dedup scan (agent-10, scratch): `dedupLoop` computes `bst` in the stamp/best arrays
-/

open scoped NNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM WExpr Stmt

/-- The stamp/best arrays represent the accumulator `acc` for stamp `z` on `[0, n)`. -/
def DRep (n z : ℕ) (acc : ℕ → Option ℕ) (t : State ℝ≥0) : Prop :=
  (∀ v < n, acc v = none → t.wa "g_mark" v < z) ∧
  (∀ v < n, ∀ b, acc v = some b → t.wa "g_mark" v = z ∧ t.wa "g_best" v = b)

def dedupWA : List String := ["g_mark", "g_best"]
def dedupWR : List String := ["g_j", "g_e", "g_v", "g_b"]

theorem take_succ_getD (L : List ℕ) {j : ℕ} (hj : j < L.length) :
    L.take (j + 1) = L.take j ++ [L.getD j 0] := by
  rw [List.take_succ, List.getElem?_eq_getElem hj, List.getD_eq_getElem _ _ hj]
  rfl

theorem getD_mem (L : List ℕ) {j : ℕ} (hj : j < L.length) : L.getD j 0 ∈ L := by
  rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj

/-- Loop invariant of the dedup scan after `j` steps. -/
structure DInv (st : State ℝ≥0) (n u p0 : ℕ) (acc : ℕ → Option ℕ) (j : ℕ) (t : State ℝ≥0) :
    Prop where
  gj : t.w "g_j" = p0 + j
  rep : DRep n (u + 1) acc t
  mL : t.wlen "g_mark" = n
  bL : t.wlen "g_best" = n
  U : Unchanged st t dedupWA [] dedupWR []
  c : t.cost ≤ st.cost + 9 * j

theorem inGroup_eval {t : State ℝ≥0} {u a b : ℕ} (hu : t.w "g_u" = u) (hj : t.w "g_j" = a)
    (hL : u + 1 < t.wlen "g_cnt") (hc : t.wa "g_cnt" (u + 1) = b) (hcap : u + 2 < t.cap)
    (hcap' : 1 < t.cap) :
    evalW t inGroup = some (if a < b then 1 else 0) := by
  unfold inGroup
  rw [evalW_lt_of (x := a) (y := b) (by rw [evalW_var, hj])
    (by rw [evalW_load_of (j := u + 1) (evalW_add_of (by rw [evalW_var, hu])
      (evalW_lit_of (by omega)) (by omega)) hL, hc]) hcap']

theorem dedupLoop_runs (st : State ℝ≥0) (n m u p0 : ℕ) (dst : ℕ → ℕ) (wt : ℕ → ℝ≥0)
    (L : List ℕ) (hu : st.w "g_u" = u) (hz : st.w "g_z" = u + 1) (hj : st.w "g_j" = p0)
    (hcntL : u + 1 < st.wlen "g_cnt") (hcnt : st.wa "g_cnt" (u + 1) = p0 + L.length)
    (hordL : p0 + L.length ≤ st.wlen "g_ord")
    (hord : ∀ i < L.length, st.wa "g_ord" (p0 + i) = L.getD i 0)
    (hLm : ∀ e ∈ L, e < m) (hLd : ∀ e ∈ L, dst e < n)
    (hdst : ∀ e < m, st.wa "dst" e = dst e) (hdstL : m ≤ st.wlen "dst")
    (hw : ∀ e < m, st.va "w" e = wt e) (hwL : m ≤ st.vlen "w")
    (hmarkL : st.wlen "g_mark" = n) (hbestL : st.wlen "g_best" = n)
    (hrep : DRep n (u + 1) (fun _ => none) st)
    (hcap : p0 + L.length + u + 2 < st.cap) :
    Runs realOps dedupLoop st (fun r => DRep n (u + 1) (bst dst wt u L) r ∧
      r.wlen "g_mark" = n ∧ r.wlen "g_best" = n ∧
      Unchanged st r dedupWA [] dedupWR [] ∧ r.cost ≤ st.cost + 9 * L.length + 1) := by
  refine runs_while (fun j t => DInv st n u p0 (bst dst wt u (L.take j)) j t)
    L.length _ ?_ ?_ st ⟨by simp [hj], by simpa using hrep, hmarkL, hbestL, by simp, by simp⟩
  · intro j hjL t hI
    have htcap : t.cap = st.cap := hI.U.cap
    have hwr : ∀ x, x ∉ dedupWR → t.w x = st.w x := hI.U.wreg
    have hwa : ∀ a, a ∉ dedupWA → t.wa a = st.wa a ∧ t.wlen a = st.wlen a := hI.U.warr
    have hva : t.va "w" = st.va "w" ∧ t.vlen "w" = st.vlen "w" := hI.U.varr "w" (by simp)
    have htu : t.w "g_u" = u := by rw [hwr _ (by simp [dedupWR])]; exact hu
    have htz : t.w "g_z" = u + 1 := by rw [hwr _ (by simp [dedupWR])]; exact hz
    have htcnt : t.wa "g_cnt" (u + 1) = p0 + L.length := by
      rw [(hwa "g_cnt" (by simp [dedupWA])).1]; exact hcnt
    have htcntL : u + 1 < t.wlen "g_cnt" := by rw [(hwa "g_cnt" (by simp [dedupWA])).2]; exact hcntL
    have htord : t.wa "g_ord" (p0 + j) = L.getD j 0 := by
      rw [(hwa "g_ord" (by simp [dedupWA])).1]; exact hord j hjL
    have htordL : p0 + j < t.wlen "g_ord" := by
      rw [(hwa "g_ord" (by simp [dedupWA])).2]; omega
    set e := L.getD j 0 with he
    have heL : e ∈ L := getD_mem L hjL
    have hem : e < m := hLm e heL
    have hen : dst e < n := hLd e heL
    have htdst : t.wa "dst" e = dst e := by
      rw [(hwa "dst" (by simp [dedupWA])).1]; exact hdst e hem
    have htdstL : e < t.wlen "dst" := by rw [(hwa "dst" (by simp [dedupWA])).2]; omega
    have htw : ∀ f < m, t.va "w" f = wt f := fun f hf => by rw [hva.1]; exact hw f hf
    have htwL : m ≤ t.vlen "w" := by rw [hva.2]; exact hwL
    have htake : L.take (j + 1) = L.take j ++ [e] := take_succ_getD L hjL
    have hR := hI.rep
    have hmL := hI.mL
    have hbL := hI.bL
    have hU := hI.U
    have hc := hI.c
    have htj := hI.gj
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [inGroup_eval htu htj htcntL htcnt (by omega) (by omega)]
      simp [hjL]
    · apply wp_sound
      rw [htake, bst_concat]
      set acc := bst dst wt u (L.take j) with hacc
      by_cases hl : dst e = u
      · -- self-loop: skipped
        have hstep : bstStep dst wt u acc e = acc := by simp [bstStep, hl]
        rw [hstep]
        simp [dedupBody, inc, wp, htj, htord, htordL, htdst, htdstL, hl, htu, fit, htcap,
          show 1 < st.cap by omega, show p0 + j + 1 < st.cap by omega]
        refine ⟨by simp; ring, ⟨fun v hv h => by simpa using hR.1 v hv h,
          fun v hv b h => by simpa using hR.2 v hv b h⟩, by simpa using hmL, by simpa using hbL,
          by simpa [dedupWR] using hU, by simp; omega⟩
      · cases hav : acc (dst e) with
        | none =>
          have hmk : t.wa "g_mark" (dst e) < u + 1 := hR.1 _ hen hav
          have hmk' : t.wa "g_mark" (dst e) ≠ u + 1 := by omega
          have hstep : bstStep dst wt u acc e = Function.update acc (dst e) (some e) := by
            simp [bstStep, hl, hav]
          rw [hstep]
          simp [dedupBody, inc, wp, htj, htord, htordL, htdst, htdstL, hl, htu, htz, fit, htcap,
            show 1 < st.cap by omega, show 0 < st.cap by omega, show p0 + j + 1 < st.cap by omega,
            hmk', hmL, hbL, hen]
          refine ⟨by simp; ring, ⟨fun v hv h => ?_, fun v hv b h => ?_⟩, by simpa using hmL,
            by simpa using hbL, by simpa [dedupWR, dedupWA] using hU, by simp; omega⟩
          · by_cases hve : v = dst e
            · subst hve; simp at h
            · rw [Function.update_of_ne hve] at h
              simp [hve]
              have := hR.1 v hv h; omega
          · by_cases hve : v = dst e
            · subst hve; simp at h; subst h; simp
            · rw [Function.update_of_ne hve] at h
              simp [hve]
              exact hR.2 v hv b h
        | some b =>
          obtain ⟨hmk, hbst⟩ := hR.2 _ hen b hav
          have hbL' : b ∈ L := by
            have := (bst_some (dst := dst) (wt := wt) (u := u) (L := L.take j) hav).1
            exact List.mem_of_mem_take this
          have hbm : b < m := hLm b hbL'
          by_cases hwle : wt b ≤ wt e
          · have hstep : bstStep dst wt u acc e = acc := by simp [bstStep, hl, hav, hwle]
            rw [hstep]
            simp [dedupBody, inc, wp, htj, htord, htordL, htdst, htdstL, hl, htu, htz, fit, htcap,
              show 1 < st.cap by omega, show 0 < st.cap by omega, show p0 + j + 1 < st.cap by omega,
              hmk, hbst, hmL, hbL, hen, realOps, htw b hbm, htw e hem,
              show b < t.vlen "w" by omega, show e < t.vlen "w" by omega, hwle]
            refine ⟨by simp; ring, ⟨fun v hv h => by simpa using hR.1 v hv h,
              fun v hv b h => by simpa using hR.2 v hv b h⟩, by simpa using hmL, by simpa using hbL,
              by simpa [dedupWR] using hU, by simp; omega⟩
          · have hstep : bstStep dst wt u acc e = Function.update acc (dst e) (some e) := by
              simp [bstStep, hl, hav, hwle]
            rw [hstep]
            simp [dedupBody, inc, wp, htj, htord, htordL, htdst, htdstL, hl, htu, htz, fit, htcap,
              show 1 < st.cap by omega, show 0 < st.cap by omega, show p0 + j + 1 < st.cap by omega,
              hmk, hbst, hmL, hbL, hen, realOps, htw b hbm, htw e hem,
              show b < t.vlen "w" by omega, show e < t.vlen "w" by omega, hwle]
            refine ⟨by simp; ring, ⟨fun v hv h => ?_, fun v hv b' h => ?_⟩, by simpa using hmL,
              by simpa using hbL, by simpa [dedupWR, dedupWA] using hU, by simp; omega⟩
            · by_cases hve : v = dst e
              · subst hve; simp at h
              · rw [Function.update_of_ne hve] at h
                simpa using hR.1 v hv h
            · by_cases hve : v = dst e
              · subst hve; simp at h; subst h; simp [hmk]
              · rw [Function.update_of_ne hve] at h
                simp [hve]
                exact hR.2 v hv b' h
  · intro t hI
    have htcap : t.cap = st.cap := hI.U.cap
    have htu : t.w "g_u" = u := by rw [hI.U.wreg _ (by simp [dedupWR])]; exact hu
    have htcnt : t.wa "g_cnt" (u + 1) = p0 + L.length := by
      rw [(hI.U.warr "g_cnt" (by simp [dedupWA])).1]; exact hcnt
    have htcntL : u + 1 < t.wlen "g_cnt" := by
      rw [(hI.U.warr "g_cnt" (by simp [dedupWA])).2]; exact hcntL
    refine ⟨?_, ?_, hI.mL, hI.bL, by simpa using hI.U, by have := hI.c; simp; omega⟩
    · rw [inGroup_eval htu hI.gj htcntL htcnt (by omega) (by omega)]
      simp
    · have := hI.rep
      rw [List.take_length] at this
      exact ⟨fun v hv h => this.1 v hv h, fun v hv b h => this.2 v hv b h⟩

/-! ## Flagging the kept edges -/

/-- `e` (an edge of `u`'s group `L`) is kept: not a loop, and the chosen edge for its head. -/
def keptP (dst : ℕ → ℕ) (wt : ℕ → ℝ≥0) (u : ℕ) (L : List ℕ) (e : ℕ) : Prop :=
  dst e ≠ u ∧ bst dst wt u L (dst e) = some e

noncomputable instance (dst : ℕ → ℕ) (wt : ℕ → ℝ≥0) (u : ℕ) (L : List ℕ) (e : ℕ) :
    Decidable (keptP dst wt u L e) := by unfold keptP; infer_instance

def flagWA : List String := ["g_kept"]
def flagWR : List String := ["g_j", "g_e", "g_v", "g_d"]

/-- Loop invariant of the flag scan after `j` steps. -/
structure FInv (st : State ℝ≥0) (u p0 : ℕ) (P : ℕ → Prop) [DecidablePred P] (L : List ℕ)
    (j : ℕ) (t : State ℝ≥0) : Prop where
  gj : t.w "g_j" = p0 + j
  gd : t.w "g_d" = ((L.take j).filter (fun e => decide (P e))).length
  kept : t.wa "g_kept" = fun e => if e ∈ L.take j ∧ P e then 1 else st.wa "g_kept" e
  kL : t.wlen "g_kept" = st.wlen "g_kept"
  U : Unchanged st t flagWA [] flagWR []
  c : t.cost ≤ st.cost + 8 * j

theorem flagLoop_runs (st : State ℝ≥0) (n m u p0 : ℕ) (dst : ℕ → ℕ) (wt : ℕ → ℝ≥0)
    (L : List ℕ) (hu : st.w "g_u" = u) (hj : st.w "g_j" = p0) (hd0 : st.w "g_d" = 0)
    (hcntL : u + 1 < st.wlen "g_cnt") (hcnt : st.wa "g_cnt" (u + 1) = p0 + L.length)
    (hordL : p0 + L.length ≤ st.wlen "g_ord")
    (hord : ∀ i < L.length, st.wa "g_ord" (p0 + i) = L.getD i 0)
    (hLm : ∀ e ∈ L, e < m) (hLd : ∀ e ∈ L, dst e < n)
    (hdst : ∀ e < m, st.wa "dst" e = dst e) (hdstL : m ≤ st.wlen "dst")
    (hbestL : st.wlen "g_best" = n) (hkeptL : m ≤ st.wlen "g_kept")
    (hrep : DRep n (u + 1) (bst dst wt u L) st)
    (hcap : p0 + L.length + u + 2 < st.cap) :
    Runs realOps flagLoop st (fun r =>
      r.w "g_d" = (L.filter (fun e => decide (keptP dst wt u L e))).length ∧
      r.wa "g_kept" = (fun e => if e ∈ L ∧ keptP dst wt u L e then 1 else st.wa "g_kept" e) ∧
      r.wlen "g_kept" = st.wlen "g_kept" ∧
      Unchanged st r flagWA [] flagWR [] ∧ r.cost ≤ st.cost + 8 * L.length + 1) := by
  refine runs_while (fun j t => FInv st u p0 (keptP dst wt u L) L j t)
    L.length _ ?_ ?_ st ⟨by simp [hj], by simp [hd0], by funext e; simp, rfl, by simp, by simp⟩
  · intro j hjL t hI
    have htcap : t.cap = st.cap := hI.U.cap
    have hwr : ∀ x, x ∉ flagWR → t.w x = st.w x := hI.U.wreg
    have hwa : ∀ a, a ∉ flagWA → t.wa a = st.wa a ∧ t.wlen a = st.wlen a := hI.U.warr
    have htu : t.w "g_u" = u := by rw [hwr _ (by simp [flagWR])]; exact hu
    have htcnt : t.wa "g_cnt" (u + 1) = p0 + L.length := by
      rw [(hwa "g_cnt" (by simp [flagWA])).1]; exact hcnt
    have htcntL : u + 1 < t.wlen "g_cnt" := by rw [(hwa "g_cnt" (by simp [flagWA])).2]; exact hcntL
    have htord : t.wa "g_ord" (p0 + j) = L.getD j 0 := by
      rw [(hwa "g_ord" (by simp [flagWA])).1]; exact hord j hjL
    have htordL : p0 + j < t.wlen "g_ord" := by
      rw [(hwa "g_ord" (by simp [flagWA])).2]; omega
    set e := L.getD j 0 with he
    have heL : e ∈ L := getD_mem L hjL
    have hem : e < m := hLm e heL
    have hen : dst e < n := hLd e heL
    have htdst : t.wa "dst" e = dst e := by
      rw [(hwa "dst" (by simp [flagWA])).1]; exact hdst e hem
    have htdstL : e < t.wlen "dst" := by rw [(hwa "dst" (by simp [flagWA])).2]; omega
    have htbest : t.wa "g_best" = st.wa "g_best" := (hwa "g_best" (by simp [flagWA])).1
    have htbestL : t.wlen "g_best" = n := by rw [(hwa "g_best" (by simp [flagWA])).2]; exact hbestL
    have htkeptL : e < t.wlen "g_kept" := by rw [hI.kL]; omega
    have htake : L.take (j + 1) = L.take j ++ [e] := take_succ_getD L hjL
    have htj := hI.gj
    have htd := hI.gd
    have htk := hI.kept
    have hU := hI.U
    have hc := hI.c
    have hdle : t.w "g_d" ≤ j := by
      rw [htd]
      have h1 := List.length_filter_le (fun e => decide (keptP dst wt u L e)) (L.take j)
      have h2 := List.length_take_le j L
      omega
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [inGroup_eval htu htj htcntL htcnt (by omega) (by omega)]
      simp [hjL]
    · apply wp_sound
      by_cases hl : dst e = u
      · have hnk : ¬ keptP dst wt u L e := fun h => h.1 hl
        simp [flagBody, inc, wp, htj, htord, htordL, htdst, htdstL, hl, htu, fit, htcap,
          show 1 < st.cap by omega, show p0 + j + 1 < st.cap by omega]
        refine ⟨by simp; ring, ?_, ?_, by simpa using hI.kL, by simpa [flagWR] using hU,
          by simp; omega⟩
        · rw [htake, List.filter_append]; simp [htd, hnk]
        · funext f; simp only [State.charge_wa, State.setW_wa, htk, htake, List.mem_append,
            List.mem_singleton]
          by_cases hfe : f = e
          · rw [hfe]; simp [hnk]
          · simp [hfe]
      · obtain ⟨b, hb⟩ : ∃ b, bst dst wt u L (dst e) = some b :=
          Option.isSome_iff_exists.mp (bst_isSome heL hl)
        have hbst : t.wa "g_best" (dst e) = b := by rw [htbest]; exact (hrep.2 _ hen b hb).2
        by_cases hbe : b = e
        · rw [hbe] at hb hbst
          have hk : keptP dst wt u L e := ⟨hl, hb⟩
          simp [flagBody, inc, wp, htj, htord, htordL, htdst, htdstL, hl, htu, fit, htcap,
            show 1 < st.cap by omega, show 0 < st.cap by omega, show p0 + j + 1 < st.cap by omega,
            hbst, htbestL, hen, htkeptL, show t.w "g_d" + 1 < st.cap by omega]
          refine ⟨by simp; ring, ?_, ?_, by simpa using hI.kL, by simpa [flagWR, flagWA] using hU,
            by simp; omega⟩
          · simp only [State.charge_w, State.setW_w, State.storeW_w, if_true]
            simp [htd, htake, List.filter_append, hk]
          · funext f
            simp only [State.charge_wa, State.setW_wa, State.storeW_wa, htk, htake, List.mem_append,
              List.mem_singleton, true_and]
            by_cases hfe : f = e
            · rw [hfe]; simp [hk]
            · simp [hfe]
        · have hnk : ¬ keptP dst wt u L e := fun h =>
            hbe (Option.some_injective _ (hb.symm.trans h.2))
          simp [flagBody, inc, wp, htj, htord, htordL, htdst, htdstL, hl, htu, fit, htcap,
            show 1 < st.cap by omega, show 0 < st.cap by omega, show p0 + j + 1 < st.cap by omega,
            hbst, htbestL, hen, hbe]
          refine ⟨by simp; ring, ?_, ?_, by simpa using hI.kL, by simpa [flagWR] using hU,
            by simp; omega⟩
          · rw [htake, List.filter_append]; simp [htd, hnk]
          · funext f; simp only [State.charge_wa, State.setW_wa, htk, htake, List.mem_append,
              List.mem_singleton]
            by_cases hfe : f = e
            · rw [hfe]; simp [hnk]
            · simp [hfe]
  · intro t hI
    have htcap : t.cap = st.cap := hI.U.cap
    have htu : t.w "g_u" = u := by rw [hI.U.wreg _ (by simp [flagWR])]; exact hu
    have htcnt : t.wa "g_cnt" (u + 1) = p0 + L.length := by
      rw [(hI.U.warr "g_cnt" (by simp [flagWA])).1]; exact hcnt
    have htcntL : u + 1 < t.wlen "g_cnt" := by
      rw [(hI.U.warr "g_cnt" (by simp [flagWA])).2]; exact hcntL
    refine ⟨?_, ?_, ?_, hI.kL, by simpa using hI.U, by have := hI.c; simp; omega⟩
    · rw [inGroup_eval htu hI.gj htcntL htcnt (by omega) (by omega)]
      simp
    · have := hI.gd; rw [List.take_length] at this; simpa using this
    · have := hI.kept; rw [List.take_length] at this; simpa using this

end Frontier.CHD.L6
