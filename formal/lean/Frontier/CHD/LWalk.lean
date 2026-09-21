import Frontier.CHD.DRep

/-!
# Frontier.CHD.LWalk — a verified RAM walk over DS' entry lists (agent-06; Layer B, NON-GATE)

`lwalk hreg ireg body` walks the linked id list of agent-02's `DRep.LList` (through `ent.nxt`, head word
`0` = nil, `i+1` = entry `i`) starting from the head word in register `hreg`: for each id `i` it sets
`ireg := i`, advances `hreg := ent.nxt[i]` (BEFORE the body, so the body may relink entry `i`), then runs
`body`.  `runs_lwalk` turns a per-entry Hoare spec of `body` (a fold invariant `J` over the processed
prefix) into a spec of the whole walk, with cost `|l| (Cb + 3) + 1`.  Intended for B-L3's F-SPLIT / F-PULL /
F-MERGE (count live entries, copy ids to the selection array, relink).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.LWalk

open Frontier Frontier.RAM Frontier.CHD.DIns

/-- the walk -/
def lwalk (hreg ireg : String) (body : Stmt) : Stmt :=
  .while (.lt (.lit 0) (.var hreg))
    (.seq (.wset ireg (.sub (.var hreg) (.lit 1)))
      (.seq (.wset hreg (.load "ent.nxt" (.var ireg))) body))

theorem LList.cons_inv {st : State ℝ≥0} {h i : ℕ} {l : List ℕ} (hl : LList st h (i :: l)) :
    h = i + 1 ∧ i < st.wlen "ent.nxt" ∧ LList st (st.wa "ent.nxt" i) l := by
  cases hl with
  | cons _ _ h1 h2 => exact ⟨rfl, h1, h2⟩

theorem LList.nil_inv {st : State ℝ≥0} {h : ℕ} (hl : LList st h []) : h = 0 := by
  cases hl; rfl

/-- **The list walk.**  `J p st` : the processed prefix is `p`.  `J` must survive the walker's own register
writes (`hJ`).  The body, run at entry `k` (`ireg = l[k]`, `hreg` already advanced), must re-establish `J` for
the longer prefix, keep `hreg`, the remaining list and the cap, and cost `≤ Cb`. -/
theorem runs_lwalk {hreg ireg : String} {body : Stmt} (hri : hreg ≠ ireg)
    (J : List ℕ → State ℝ≥0 → Prop) (l : List ℕ) (Cb : ℕ)
    (hJ : ∀ p (s t : State ℝ≥0), J p s → (∀ y, y ≠ hreg → y ≠ ireg → t.w y = s.w y) → t.wa = s.wa →
      t.va = s.va → t.wlen = s.wlen → t.vlen = s.vlen → t.v = s.v → t.cap = s.cap → t.procs = s.procs →
      s.cost ≤ t.cost → J p t)
    (hbody : ∀ k (hk : k < l.length) (s : State ℝ≥0), J (l.take k) s → s.w ireg = l[k] →
      LList s (s.w hreg) (l.drop (k + 1)) → 1 < s.cap →
      Runs realOps body s (fun r => J (l.take (k + 1)) r ∧ r.w hreg = s.w hreg ∧
        LList r (r.w hreg) (l.drop (k + 1)) ∧ r.cap = s.cap ∧ r.cost ≤ s.cost + Cb))
    (st : State ℝ≥0) (h0 : J [] st) (hl : LList st (st.w hreg) l) (hcap : 1 < st.cap) :
    Runs realOps (lwalk hreg ireg body) st (fun r => J l r ∧ r.w hreg = 0 ∧ r.cap = st.cap ∧
      r.cost ≤ st.cost + l.length * (Cb + 3) + 1) := by
  refine runs_while (fun k s => J (l.take k) s ∧ LList s (s.w hreg) (l.drop k) ∧ s.cap = st.cap ∧
      s.cost ≤ st.cost + k * (Cb + 3)) l.length _ ?_ ?_ st ⟨by simpa using h0, by simpa using hl, rfl, by simp⟩
  · rintro k hk s ⟨hJs, hLs, hcs, hcost⟩
    have hc1 : 1 < s.cap := by rw [hcs]; exact hcap
    rw [List.drop_eq_getElem_cons hk] at hLs
    obtain ⟨hh, hlt, hrest⟩ := LList.cons_inv hLs
    refine ⟨1, by rw [evalW_lt_of (evalW_lit_of (by omega)) rfl hc1, hh]; simp, one_ne_zero, ?_⟩
    apply runs_seq
    refine runs_wset (a := l[k]) (by simp [evalW_sub', evalW_lit', fit_of_lt hc1, hh]) ?_
    apply runs_seq
    refine runs_wset (a := s.wa "ent.nxt" l[k])
      (evalW_load_of (by simp) (by simpa using hlt)) ?_
    set t := ((((s.charge 1).setW ireg l[k]).charge 1).setW hreg (s.wa "ent.nxt" l[k])).charge 1 with htdef
    have hJt : J (l.take k) t := hJ _ s t hJs (fun y h1 h2 => by simp [htdef, h1, h2]) rfl rfl rfl rfl rfl rfl
      rfl (by simp only [htdef, State.charge_cost, State.setW_cost]; omega)
    have hti : t.w ireg = l[k] := by simp [htdef, hri.symm]
    have hth : t.w hreg = s.wa "ent.nxt" l[k] := by simp [htdef]
    have htL : LList t (t.w hreg) (l.drop (k + 1)) := by
      rw [hth]; exact hrest.of_eq (fun j _ => rfl) le_rfl
    refine (hbody k hk t hJt hti htL (by simpa [htdef] using hc1)).mono ?_
    rintro r ⟨hJr, hrh, hrL, hrc, hrcost⟩
    refine ⟨hJr, hrL, by rw [hrc]; simpa [htdef] using hcs, ?_⟩
    simp only [htdef, State.charge_cost, State.setW_cost] at hrcost
    rw [Nat.succ_mul]
    omega
  · rintro s ⟨hJs, hLs, hcs, hcost⟩
    have hc1 : 1 < s.cap := by rw [hcs]; exact hcap
    rw [List.drop_length] at hLs
    have h0 := LList.nil_inv hLs
    refine ⟨by rw [evalW_lt_of (evalW_lit_of (by omega)) rfl hc1, h0]; simp, ?_, by simp [h0], by simp [hcs], ?_⟩
    · have := hJ _ s (s.charge 1) hJs (fun y _ _ => rfl) rfl rfl rfl rfl rfl rfl rfl (by simp)
      simpa using this
    · simp; omega

end Frontier.CHD.LWalk
