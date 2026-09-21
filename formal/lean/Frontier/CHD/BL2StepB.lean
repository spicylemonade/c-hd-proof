import Frontier.CHD.BL2StepA

/-!
# Frontier.CHD.BL2StepB — B-L2: member bookkeeping blocks of the scan (agent-09, scratch, NON-GATE)
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}

variable {c : FPCtx G s} {T : Finset (Fin G.n)}

theorem memAdd_spec {st : State V} {σ : SSt G s} {v w : Fin G.n}
    (hM : MyRep c T σ st) (hv : st.w "fp.v" = v) (hw : st.w "fp.u" = w) (hvK : v ∉ σ.K)
    (hk : σ.K.length < c.k) (hcap : c.k + 1 < st.cap) :
    Runs ops fpMemAdd st (fun st' =>
      MyRep c T { σ with K := σ.K ++ [v], kpar := Function.update σ.kpar v w } st' ∧
      Unchanged st st' ["fp.K", "fp.inK", "fp.kp"] [] ["fp.kl"] [] ∧ st'.cost = st.cost + 4) := by
  have hklK : st.w "fp.kl" < st.wlen "fp.K" := by rw [hM.kl]; exact lt_of_lt_of_le hk hM.kcap
  have hvK' : (v : ℕ) < st.wlen "fp.inK" := by rw [hM.inK.1]; exact v.isLt
  have hvp : (v : ℕ) < st.wlen "fp.kp" := by rw [hM.kpL]; exact v.isLt
  have hkl1 : σ.K.length + 1 < st.cap := by omega
  obtain ⟨hl, hnd, hset, hsz, hcapH, harr, hpL, hpos, hbL, hb⟩ := hM.heap
  apply wp_sound
  have hklK2 : σ.K.length < st.wlen "fp.K" := by rw [← hM.kl]; exact hklK
  simp [fpMemAdd, wp, hv, hw, hvK', hvp, fit, hM.kl, hkl1, show 1 < st.cap by omega]
  refine ⟨hklK2, ⟨by simpa using hM.gM, by simpa using hM.headL, fun q => by simpa using hM.head q,
    ⟨hl, hnd, hset, by simpa using hsz, by simpa using hcapH, fun i hi => by simpa using harr i hi,
      by simpa using hpL, fun i hi => by simpa using hpos i hi, by simpa using hbL,
      fun x => by simpa using hb x⟩,
    by simp, by simpa using hM.kcap, fun i hi => ?_, ⟨by simpa using hM.inK.1, fun x => ?_⟩,
    ⟨by simpa using hM.val.1, fun x => by simpa using hM.val.2 x⟩,
    ⟨by simpa using hM.fm.1, fun x => by simpa using hM.fm.2 x⟩,
    by simpa using hM.kpL, fun x hx => ?_, by simpa using hM.kreg,
    List.nodup_append.mpr ⟨hM.Knd, List.nodup_singleton v, by
      intro a ha b hb' hab; simp at hb'; subst hb'; subst hab; exact hvK ha⟩,
    fun x hx => by simpa using Or.inr (List.mem_toFinset.mp (hM.HK hx))⟩, ?_⟩
  · -- the member array
    by_cases hi' : i = σ.K.length
    · subst hi'; simp
    · have hi2 : i < σ.K.length := by simp at hi; omega
      simp [hi', List.getElem_append_left hi2]
      simpa using hM.karr i hi2
  · -- the member bitmap
    by_cases hx : x = v
    · subst hx; simp
    · have : (x : ℕ) ≠ v := fun h' => hx (Fin.ext h')
      simp [this, hx, hM.inK.2 x]
  · -- first-discovery parents
    by_cases hxv : x = v
    · subst hxv; simp
    · have : (x : ℕ) ≠ v := fun h' => hxv (Fin.ext h')
      have hxK : x ∈ σ.K := by simpa [hxv] using hx
      simp [this, hxv, hM.kp x hxK]
  · refine ⟨fun a ha => ?_, fun _ _ => ⟨rfl, rfl⟩, fun x hx => ?_, fun _ _ => rfl, rfl, rfl⟩
    · simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at ha
      refine ⟨?_, by simp⟩
      funext j; simp [ha.1, ha.2.1, ha.2.2]
    · simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at hx
      simp [hx]

/-- Marking `v` valid. -/
theorem MyRep.markVal {st : State V} {σ : SSt G s} (hM : MyRep c T σ st) (v : Fin G.n) :
    MyRep c T { σ with val := insert v σ.val } ((st.storeW "fp.val" v 1).charge 1) := by
  obtain ⟨hl, hnd, hset, hsz, hcapH, harr, hpL, hpos, hbL, hb⟩ := hM.heap
  exact ⟨by simpa using hM.gM, by simpa using hM.headL, fun q => by simpa using hM.head q,
    ⟨hl, hnd, hset, by simpa using hsz, by simpa using hcapH, fun i hi => by simpa using harr i hi,
      by simpa using hpL, fun i hi => by simpa using hpos i hi, by simpa using hbL,
      fun x => by simpa using hb x⟩,
    by simpa using hM.kl, by simpa using hM.kcap, fun i hi => by simpa using hM.karr i hi,
    ⟨by simpa using hM.inK.1, fun x => by simpa using hM.inK.2 x⟩, hM.val.update v,
    ⟨by simpa using hM.fm.1, fun x => by simpa using hM.fm.2 x⟩,
    by simpa using hM.kpL, fun x hx => by simpa using hM.kp x hx, by simpa using hM.kreg,
    hM.Knd, hM.HK⟩

/-- Replacing the heap. -/
theorem MyRep.setHeap {st st' : State V} {σ : SSt G s} {H' : Finset (Fin G.n)}
    (hM : MyRep c T σ st) (hH : HeapRep st' c.k H')
    (hu : Unchanged st st' ["fp.H", "fp.hp", "fp.inH"] [] ["fp.hsz"] [])
    (hsub : H' ⊆ σ.K.toFinset) : MyRep c T { σ with H := H' } st' := by
  have A : ∀ a, a ≠ "fp.H" → a ≠ "fp.hp" → a ≠ "fp.inH" →
      st'.wa a = st.wa a ∧ st'.wlen a = st.wlen a := fun a h1 h2 h3 =>
    hu.warr a (by simp [h1, h2, h3])
  have R : ∀ x, x ≠ "fp.hsz" → st'.w x = st.w x := fun x hx => hu.wreg x (by simp [hx])
  have aH := A "gHead" (by decide) (by decide) (by decide)
  have aK := A "fp.K" (by decide) (by decide) (by decide)
  have ainK := A "fp.inK" (by decide) (by decide) (by decide)
  have aval := A "fp.val" (by decide) (by decide) (by decide)
  have afm := A "fp.fm" (by decide) (by decide) (by decide)
  have akp := A "fp.kp" (by decide) (by decide) (by decide)
  exact ⟨by rw [R "gM" (by decide)]; exact hM.gM, by rw [aH.2]; exact hM.headL,
    fun q => by rw [aH.1]; exact hM.head q, hH,
    by rw [R "fp.kl" (by decide)]; exact hM.kl, by rw [aK.2]; exact hM.kcap,
    fun i hi => by rw [aK.1]; exact hM.karr i hi,
    ⟨by rw [ainK.2]; exact hM.inK.1, fun x => by rw [ainK.1]; exact hM.inK.2 x⟩,
    ⟨by rw [aval.2]; exact hM.val.1, fun x => by rw [aval.1]; exact hM.val.2 x⟩,
    ⟨by rw [afm.2]; exact hM.fm.1, fun x => by rw [afm.1]; exact hM.fm.2 x⟩,
    by rw [akp.2]; exact hM.kpL, fun x hx => by rw [akp.1]; exact hM.kp x hx,
    by rw [R "fp.k" (by decide)]; exact hM.kreg, hM.Knd, hsub⟩

theorem okPart_spec {st : State V} {σ : SSt G s} {v : Fin G.n} {okr : String} {b : Prop}
    [Decidable b] (hM : MyRep c T σ st) (hv : st.w "fp.v" = v) (hok : st.w okr = if b then 1 else 0)
    (hvK : v ∈ σ.K) (hk : σ.K.length ≤ c.k) (hcap : c.k + 2 < st.cap) :
    Runs ops (fpOkPart okr) st (fun st' =>
      MyRep c T { σ with val := if b then insert v σ.val else σ.val,
                          H := if b then insert v σ.H else σ.H } st' ∧
      Unchanged st st' ["fp.val", "fp.H", "fp.hp", "fp.inH"] [] ["fp.hsz"] [] ∧
      st.cost + 1 ≤ st'.cost ∧ st'.cost ≤ st.cost + 7) := by
  by_cases hb : b
  · rw [if_pos hb] at hok
    have hvL : (v : ℕ) < st.wlen "fp.val" := by rw [hM.val.1]; exact v.isLt
    refine runs_ite_true (x := 1) (by simp [hok]) one_ne_zero ?_
    have hc1 : 1 < (st.charge 1).cap := by simp; omega
    refine runs_seq (runs_wstore (j := v) (a := 1) (by simp [hv]) (evalW_lit_of hc1)
      (by simpa using hvL) ?_)
    have hM1 := (hM.charge' 1).markVal v
    have hHcard : σ.H.card ≤ c.k := by
      calc σ.H.card ≤ σ.K.toFinset.card := Finset.card_le_card hM.HK
        _ ≤ σ.K.length := List.toFinset_card_le _
        _ ≤ c.k := hk
    refine (heapIns_spec (k := c.k) (H := σ.H) (v := v) hM1.heap (by simpa using hv) ?_
      (by simp; omega)).mono ?_
    · intro hvH
      have hlt : σ.H ⊂ σ.K.toFinset := Finset.ssubset_iff_subset_ne.mpr ⟨hM.HK, fun h =>
        hvH (h ▸ List.mem_toFinset.mpr hvK)⟩
      calc σ.H.card < σ.K.toFinset.card := Finset.card_lt_card hlt
        _ ≤ σ.K.length := List.toFinset_card_le _
        _ ≤ c.k := hk
    · rintro st' ⟨hH', hu', hc1, hc2⟩
      refine ⟨?_, ?_, by simp at hc1 ⊢; omega, by simp at hc2 ⊢; omega⟩
      · simp only [if_pos hb]
        exact MyRep.setHeap (σ := { σ with val := insert v σ.val }) hM1 hH' hu'
          (Finset.insert_subset (List.mem_toFinset.mpr hvK) hM.HK)
      · refine ((Unchanged.charge st 1 _ _ _ _).trans ?_)
        have h1 := unch_storeW (st.charge 1) "fp.val" v 1
        have h2 := Unchanged.trans' (Unchanged.trans' h1 (unch_charge' _ 1)) hu'
        exact h2.mono (by intro a; simp) (by simp) (by simp) (fun _ h => h)
  · rw [if_neg hb] at hok
    refine runs_ite_false (by simp [hok]) (runs_skip ?_)
    simp only [if_neg hb]
    refine ⟨(hM.charge' 1).charge' 1, ?_, by simp, by simp⟩
    exact ((Unchanged.charge st 1 _ _ _ _).trans (Unchanged.charge _ 1 _ _ _ _))

end Frontier.CHD.BL2
