import Frontier.CHD.BL2InvInit

/-!
# Frontier.CHD.BL2InvClear — B-L2: clearing the per-search marks over `K` (agent-09, scratch, NON-GATE)
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}
variable {c : FPCtx G s} {T : Finset (Fin G.n)}

/-- Vertex ids of a vertex list. -/
def sl' (L : List (Fin G.n)) : List ℕ := L.map Fin.val

/-- One clearing step: position `i` of `K`. -/
theorem clearStep_spec {st : State V} {K : List (Fin G.n)} {i : ℕ}
    (harr : LArr st "fp.K" K) (hi : st.w "fp.i" = i) (hiK : i < K.length)
    (hKL : K.length ≤ st.wlen "fp.K") (hLK : st.wlen "fp.inK" = G.n)
    (hLv : st.wlen "fp.val" = G.n) (hLH : st.wlen "fp.inH" = G.n) (hcap : K.length + 1 < st.cap) :
    Runs ops (seq (wset "fp.y" (load "fp.K" (var "fp.i")))
      (seq (wstore "fp.inK" (var "fp.y") (lit 0))
      (seq (wstore "fp.val" (var "fp.y") (lit 0))
      (seq (wstore "fp.inH" (var "fp.y") (lit 0))
           (wset "fp.i" (add (var "fp.i") (lit 1))))))) st
      (fun st' => st'.w "fp.i" = i + 1 ∧
        (∀ a, a ≠ "fp.inK" → a ≠ "fp.val" → a ≠ "fp.inH" → st'.wa a = st.wa a) ∧
        st'.wlen = st.wlen ∧
        (∀ v : ℕ, st'.wa "fp.inK" v = if v = (K[i] : ℕ) then 0 else st.wa "fp.inK" v) ∧
        (∀ v : ℕ, st'.wa "fp.val" v = if v = (K[i] : ℕ) then 0 else st.wa "fp.val" v) ∧
        (∀ v : ℕ, st'.wa "fp.inH" v = if v = (K[i] : ℕ) then 0 else st.wa "fp.inH" v) ∧
        Unchanged st st' ["fp.inK", "fp.val", "fp.inH"] [] ["fp.y", "fp.i"] [] ∧
        st'.cost = st.cost + 5) := by
  have hKi : st.wa "fp.K" i = (K[i] : ℕ) := harr i hiK
  have hiL : i < st.wlen "fp.K" := by omega
  have hy1 : ((K[i] : Fin G.n) : ℕ) < st.wlen "fp.inK" := by rw [hLK]; exact (K[i]).isLt
  have hy2 : ((K[i] : Fin G.n) : ℕ) < st.wlen "fp.val" := by rw [hLv]; exact (K[i]).isLt
  have hy3 : ((K[i] : Fin G.n) : ℕ) < st.wlen "fp.inH" := by rw [hLH]; exact (K[i]).isLt
  have hc0 : 0 < st.cap := by omega
  refine runs_seq (runs_wset (a := K[i]) (by simp [hi, hiL, hKi]) ?_)
  refine runs_seq (runs_wstore (j := K[i]) (a := 0) (by simp) (evalW_lit_of (by simpa using hc0))
    (by simpa using hy1) ?_)
  refine runs_seq (runs_wstore (j := K[i]) (a := 0) (by simp) (evalW_lit_of (by simpa using hc0))
    (by simpa using hy2) ?_)
  refine runs_seq (runs_wstore (j := K[i]) (a := 0) (by simp) (evalW_lit_of (by simpa using hc0))
    (by simpa using hy3) ?_)
  refine runs_wset (a := i + 1) (evalW_add_of (by simp [hi]) (evalW_lit_of (by simp; omega))
    (by simp; omega)) ?_
  refine ⟨by simp, fun a h1 h2 h3 => ?_, ?_, fun v => ?_, fun v => ?_, fun v => ?_, ?_, by simp⟩
  · funext j; simp [h1, h2, h3]
  · funext a; simp
  · by_cases h : v = (K[i] : ℕ) <;> simp [h]
  · by_cases h : v = (K[i] : ℕ) <;> simp [h]
  · by_cases h : v = (K[i] : ℕ) <;> simp [h]
  · refine ⟨fun a ha => ?_, fun _ _ => ⟨rfl, rfl⟩, fun x hx => ?_, fun _ _ => rfl, rfl, rfl⟩
    · simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at ha
      refine ⟨?_, by simp⟩
      funext j; simp [ha.1, ha.2.1, ha.2.2]
    · simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at hx
      simp [hx.1, hx.2]

/-- **Clearing** the per-search marks (after every search): back to the empty search state. -/
theorem clear_spec {st : State V} {σ : SSt G s} {d : Labels G s} {D : Finset (Fin G.m)}
    (hM : MyRep c T σ st) (hval : σ.val ⊆ σ.K.toFinset) (hkK : σ.K.length ≤ c.k)
    (hcap : c.k + 2 < st.cap) :
    Runs ops fpClear st (fun st' => MyRep c T (emptySt d D) st' ∧
      Unchanged st st' ["fp.inK", "fp.val", "fp.inH"] [] ["fp.y", "fp.i", "fp.kl", "fp.hsz"] [] ∧
      st.cost ≤ st'.cost ∧ st'.cost ≤ st.cost + 6 * σ.K.length + 4) := by
  obtain ⟨hl, hnd, hset, hsz, hcapH, harr, hpL, hpos, hbL, hb⟩ := hM.heap
  have hKL : σ.K.length ≤ st.wlen "fp.K" := hkK.trans hM.kcap
  unfold fpClear
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by omega)) ?_)
  generalize hst1 : (st.setW "fp.i" 0).charge 1 = st1
  have hu1 : Unchanged st st1 [] [] ["fp.i"] [] := by
    rw [← hst1]; exact ((unch_setW st "fp.i" 0).cat (unch_charge' _ 1)).mono (by simp) (by simp)
      (by simp) (by simp)
  have hwa1 : st1.wa = st.wa := by rw [← hst1]; rfl
  have hwl1 : st1.wlen = st.wlen := by rw [← hst1]; rfl
  have hcap1 : st1.cap = st.cap := by rw [← hst1]; rfl
  have hc1 : st1.cost = st.cost + 1 := by rw [← hst1]; simp
  have hkl1 : st1.w "fp.kl" = σ.K.length := by rw [← hst1]; simp [hM.kl]
  have hi1 : st1.w "fp.i" = 0 := by rw [← hst1]; simp
  let I : ℕ → State V → Prop := fun m st'' => ∃ i, m = σ.K.length - i ∧ i ≤ σ.K.length ∧
    st''.w "fp.i" = i ∧ st''.w "fp.kl" = σ.K.length ∧
    (∀ a, a ≠ "fp.inK" → a ≠ "fp.val" → a ≠ "fp.inH" → st''.wa a = st.wa a) ∧
    st''.wlen = st.wlen ∧
    (∀ v : ℕ, st''.wa "fp.inK" v = if v ∈ sl' (σ.K.take i) then 0 else st.wa "fp.inK" v) ∧
    (∀ v : ℕ, st''.wa "fp.val" v = if v ∈ sl' (σ.K.take i) then 0 else st.wa "fp.val" v) ∧
    (∀ v : ℕ, st''.wa "fp.inH" v = if v ∈ sl' (σ.K.take i) then 0 else st.wa "fp.inH" v) ∧
    Unchanged st st'' ["fp.inK", "fp.val", "fp.inH"] [] ["fp.y", "fp.i"] [] ∧
    st''.cost = st.cost + 1 + 6 * i
  have hmem : ∀ (L : List (Fin G.n)) (v : Fin G.n), (v : ℕ) ∈ sl' L ↔ v ∈ L := by
    intro L v; simp [sl', Fin.val_inj]
  have htake : ∀ i (h : i < σ.K.length), sl' (σ.K.take (i + 1)) = sl' (σ.K.take i) ++ [(σ.K[i] : ℕ)] := by
    intro i h
    show (σ.K.take (i + 1)).map Fin.val = (σ.K.take i).map Fin.val ++ [(σ.K[i] : ℕ)]
    rw [List.take_add_one, List.map_append, List.getElem?_eq_getElem h]
    rfl
  refine runs_seq (runs_while_nat I _ ?_ σ.K.length st1 ⟨0, by simp, by omega, hi1, hkl1,
    fun a _ _ _ => by rw [hwa1], by rw [hwl1], fun v => by rw [hwa1]; simp [sl'],
    fun v => by rw [hwa1]; simp [sl'], fun v => by rw [hwa1]; simp [sl'],
    hu1.mono (by simp) (by simp) (by simp) (by simp), by simp [hc1]⟩)
  intro m st2 ⟨i, hm, hiK, hi, hkl, hA, hL, hIK, hIV, hIH, hu2, hc2⟩
  have hcap2 : st2.cap = st.cap := hu2.cap
  refine ⟨if i < σ.K.length then 1 else 0, ?_, fun hne => ?_, fun h0 => ?_⟩
  · rw [evalW_lt_of (x := i) (y := σ.K.length) (by simp [hi]) (by simp [hkl]) (by omega)]
  · -- one clearing step
    have hiK' : i < σ.K.length := by by_contra h; simp [h] at hne
    have harr2 : LArr (st2.charge 1) "fp.K" σ.K := fun j hj => by
      simp only [State.charge_wa]; rw [hA "fp.K" (by decide) (by decide) (by decide)]
      exact hM.karr j hj
    have hL2 : (st2.charge 1).wlen = st.wlen := by simp [hL]
    refine (clearStep_spec (st := st2.charge 1) harr2 (by simpa using hi) hiK'
      (by rw [hL2]; exact hKL) (by rw [hL2]; exact hM.inK.1) (by rw [hL2]; exact hM.val.1)
      (by rw [hL2]; exact hbL) (by simp; omega)).mono ?_
    rintro st3 ⟨hi3, hA3, hL3, hK3, hV3, hH3, hu3, hc3⟩
    refine ⟨σ.K.length - (i + 1), by omega, i + 1, rfl, by omega, hi3, ?_, fun a h1 h2 h3 => ?_,
      by rw [hL3]; simp [hL], fun v => ?_, fun v => ?_, fun v => ?_, ?_, by simp at hc3; omega⟩
    · rw [hu3.wreg "fp.kl" (by decide)]; simpa using hkl
    · rw [hA3 a h1 h2 h3]; simp only [State.charge_wa]; exact hA a h1 h2 h3
    · rw [hK3, htake i hiK']; simp only [State.charge_wa, hIK v, List.mem_append, List.mem_singleton]
      by_cases h1 : v = (σ.K[i] : ℕ) <;> by_cases h2 : v ∈ sl' (σ.K.take i) <;> simp [h1, h2]
    · rw [hV3, htake i hiK']; simp only [State.charge_wa, hIV v, List.mem_append, List.mem_singleton]
      by_cases h1 : v = (σ.K[i] : ℕ) <;> by_cases h2 : v ∈ sl' (σ.K.take i) <;> simp [h1, h2]
    · rw [hH3, htake i hiK']; simp only [State.charge_wa, hIH v, List.mem_append, List.mem_singleton]
      by_cases h1 : v = (σ.K[i] : ℕ) <;> by_cases h2 : v ∈ sl' (σ.K.take i) <;> simp [h1, h2]
    · exact (hu2.trans ((Unchanged.charge st2 1 _ _ _ _).trans hu3))
  · -- exit: all of `K` is cleared
    have hieq : i = σ.K.length := by
      by_contra h; simp [show i < σ.K.length by omega] at h0
    subst hieq
    rw [List.take_length] at hIK hIV hIH
    refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by simp; omega)) ?_)
    refine runs_wset (a := 0) (evalW_lit_of (by simp; omega)) ?_
    generalize hst4 : ((((st2.charge 1).setW "fp.kl" 0).charge 1).setW "fp.hsz" 0).charge 1 = st4
    have hwa4 : st4.wa = st2.wa := by rw [← hst4]; rfl
    have hwl4 : st4.wlen = st2.wlen := by rw [← hst4]; rfl
    have hw4 : ∀ x, x ≠ "fp.kl" → x ≠ "fp.hsz" → st4.w x = st2.w x := fun x h1 h2 => by
      rw [← hst4]; simp [h1, h2]
    have htail : Unchanged st2 st4 ["fp.inK", "fp.val", "fp.inH"] [] ["fp.y", "fp.i", "fp.kl", "fp.hsz"] [] := by
      rw [← hst4]
      refine ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun x hx => ?_, fun _ _ => rfl, rfl, rfl⟩
      simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at hx
      simp [hx.2.2.1, hx.2.2.2]
    have hu4 : Unchanged st st4 ["fp.inK", "fp.val", "fp.inH"] [] ["fp.y", "fp.i", "fp.kl", "fp.hsz"] [] :=
      (hu2.mono (fun _ h => h) (fun _ h => h) (by simp) (fun _ h => h)).trans htail
    have hreg : ∀ x, x ∉ ["fp.y", "fp.i", "fp.kl", "fp.hsz"] → st4.w x = st.w x :=
      fun x hx => hu4.wreg x hx
    have hbits : ∀ (arr : String) (S : Finset (Fin G.n)), S ⊆ σ.K.toFinset →
        Bits st arr S → (∀ v : ℕ, st2.wa arr v = if v ∈ sl' σ.K then 0 else st.wa arr v) →
        Bits st4 arr (∅ : Finset (Fin G.n)) := by
      intro arr S hS hB hE
      refine ⟨by rw [hwl4, hL]; exact hB.1, fun v => ?_⟩
      rw [hwa4, hE v]
      by_cases hv : v ∈ σ.K
      · simp [(hmem σ.K v).mpr hv]
      · have : v ∉ S := fun h => hv (List.mem_toFinset.mp (hS h))
        simp [(hmem σ.K v).not.mpr hv, hB.2 v, this]
    refine ⟨⟨by rw [hreg "gM" (by decide)]; exact hM.gM, by rw [hwl4, hL]; exact hM.headL,
      fun q => by rw [hwa4, hA "gHead" (by decide) (by decide) (by decide)]; exact hM.head q,
      ⟨[], List.nodup_nil, by simp [emptySt], by rw [← hst4]; simp, by rw [hwl4, hL]; exact hcapH,
        fun i hi => absurd hi (by simp), by rw [hwl4, hL]; exact hpL, fun i hi => absurd hi (by simp),
        hbits "fp.inH" σ.H hM.HK ⟨hbL, hb⟩ hIH⟩,
      by rw [← hst4]; simp [emptySt], by rw [hwl4, hL]; exact hM.kcap, fun i hi => absurd hi (by simp [emptySt]),
      hbits "fp.inK" σ.K.toFinset subset_rfl hM.inK hIK,
      hbits "fp.val" σ.val hval hM.val hIV,
      ⟨by rw [hwl4, hL]; exact hM.fm.1, fun v => by
        rw [hwa4, hA "fp.fm" (by decide) (by decide) (by decide)]; exact hM.fm.2 v⟩,
      by rw [hwl4, hL]; exact hM.kpL, fun v hv => absurd hv (by simp [emptySt]),
      by rw [hreg "fp.k" (by decide)]; exact hM.kreg, List.nodup_nil, by simp [emptySt]⟩,
      hu4, by rw [← hst4]; simp; omega, by rw [← hst4]; simp; omega⟩

end Frontier.CHD.BL2
