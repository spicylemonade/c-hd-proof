import Frontier.CHD.BL2InvFail

/-!
# Frontier.CHD.BL2InvFail2 — B-L2: the whole failed-search output (agent-09, scratch, NON-GATE)
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}
variable {c : FPCtx G s} {T : Finset (Fin G.n)}

theorem WRep.frame {st st' : State V} {W : Finset (Fin G.n)} {wa va wr vr : List String}
    (h : WRep st W) (hu : Unchanged st st' wa va wr vr) (hwa : Disj wa ["fp.W", "fp.inW"])
    (hwr : Disj wr ["fp.wl", "fp.ob"]) : WRep st' W := by
  obtain ⟨wl, hnd, hset, hwl, harr, hbits, hlen⟩ := h
  have aW := hu.warr "fp.W" (fun h' => hwa _ h' (by simp))
  have aI := hu.warr "fp.inW" (fun h' => hwa _ h' (by simp))
  have rw1 := hu.wreg "fp.wl" (fun h' => hwr _ h' (by simp))
  have rob := hu.wreg "fp.ob" (fun h' => hwr _ h' (by simp))
  exact ⟨wl, hnd, hset, by rw [rw1]; exact hwl, fun i hi => by rw [aW.1, rob]; exact harr i hi,
    ⟨by rw [aI.2]; exact hbits.1, fun v => by rw [aI.1]; exact hbits.2 v⟩,
    by rw [rob, aW.2]; exact hlen⟩

theorem QRep.frame {st st' : State V} {Q : Finset (Fin G.n)} {wa va wr vr : List String}
    (h : QRep st Q) (hu : Unchanged st st' wa va wr vr) (hwa : Disj wa ["fp.Q"])
    (hwr : Disj wr ["fp.ql", "fp.ob"]) : QRep st' Q := by
  obtain ⟨ql, hnd, hset, hql, harr, hlen⟩ := h
  have aQ := hu.warr "fp.Q" (fun h' => hwa _ h' (by simp))
  have rq := hu.wreg "fp.ql" (fun h' => hwr _ h' (by simp))
  have rob := hu.wreg "fp.ob" (fun h' => hwr _ h' (by simp))
  exact ⟨ql, hnd, hset, by rw [rq]; exact hql, fun i hi => by rw [aQ.1, rob]; exact harr i hi,
    by rw [rob, aQ.2]; exact hlen⟩

/-- **Output of a failed search** (FH.21): `W ∪= val`, `Q += x`. -/
theorem failOut_spec {st : State V} {σ : SSt G s} {W Q : Finset (Fin G.n)} {x : Fin G.n}
    (hM : MyRep c T σ st) (hKk : σ.K.length ≤ c.k) (hval : σ.val ⊆ σ.K.toFinset)
    (hW : WRep st W) (hQ : QRep st Q) (hxQ : x ∉ Q) (hx : st.w "fp.x" = x)
    (hcap : st.w "fp.ob" + G.n + 2 < st.cap) :
    Runs ops fpFailOut st (fun st' => WRep st' (W ∪ σ.val) ∧ QRep st' (insert x Q) ∧
      MyRep c T σ st' ∧
      Unchanged st st' ["fp.W", "fp.inW", "fp.Q"] [] ["fp.i", "fp.y", "fp.wl", "fp.ql"] [] ∧
      st.cost ≤ st'.cost ∧ st'.cost ≤ st.cost + 9 * σ.K.length + 6) := by
  unfold fpFailOut
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by omega)) ?_)
  generalize hs1 : (st.setW "fp.i" 0).charge 1 = s1
  have hu1 : Unchanged st s1 [] [] ["fp.i"] [] := by
    rw [← hs1]; exact ((unch_setW st "fp.i" 0).cat (unch_charge' _ 1)).mono (by simp) (by simp)
      (by simp) (by simp)
  have hc1 : s1.cost = st.cost + 1 := by rw [← hs1]; simp
  have hi1 : s1.w "fp.i" = 0 := by rw [← hs1]; simp
  have hcapst : ∀ s : State V, Unchanged st s ["fp.W", "fp.inW"] [] ["fp.i", "fp.y", "fp.wl"] [] →
      s.w "fp.ob" + G.n + 2 < s.cap := fun s hu => by
    rw [hu.wreg "fp.ob" (by decide), hu.cap]; exact hcap
  let J : ℕ → State V → Prop := fun m s' => ∃ i, m = σ.K.length - i ∧ i ≤ σ.K.length ∧
    s'.w "fp.i" = i ∧ WRep s' (W ∪ (σ.val ∩ (σ.K.take i).toFinset)) ∧
    Unchanged st s' ["fp.W", "fp.inW"] [] ["fp.i", "fp.y", "fp.wl"] [] ∧
    st.cost ≤ s'.cost ∧ s'.cost ≤ st.cost + 1 + 9 * i
  have hJ0 : J σ.K.length s1 := ⟨0, by simp, by omega, hi1,
    by simpa using hW.frame hu1 (Disj.nil_left _) (by decide),
    hu1.mono (by simp) (by simp) (by simp) (by simp), by omega, by omega⟩
  refine runs_seq (runs_while_nat J _ ?_ σ.K.length s1 hJ0)
  intro m s' ⟨i, hm, hiK, hi, hW', hu', hc0', hc'⟩
  have hkl' : s'.w "fp.kl" = σ.K.length := by rw [hu'.wreg "fp.kl" (by decide)]; exact hM.kl
  have hcap' := hcapst s' hu'
  refine ⟨if i < σ.K.length then 1 else 0,
    by rw [evalW_lt_of (x := i) (y := σ.K.length) (by simp [hi]) (by simp [hkl']) (by omega)],
    fun hne => ?_, fun h0 => ?_⟩
  · have hiK' : i < σ.K.length := by by_contra h; simp [h] at hne
    have hM' : MyRep c T σ (s'.charge 1) :=
      (hM.frameR hu' (by decide) (by decide)).charge' 1
    refine (failStep_spec hM' hKk (hW'.frame (Unchanged.charge s' 1 [] [] [] []) (Disj.nil_left _)
      (Disj.nil_left _)) (by simpa using hi) hiK' (by simpa using hcap')).mono ?_
    rintro s'' ⟨hW'', hi'', hu'', hc0'', hc''⟩
    refine ⟨σ.K.length - (i + 1), by omega, i + 1, rfl, by omega, hi'', ?_,
      hu'.trans ((Unchanged.charge s' 1 _ _ _ _).trans (hu''.mono (fun _ h => h) (fun _ h => h)
        (by decide) (fun _ h => h))), by simp at hc0''; omega,
      by simp at hc''; omega⟩
    convert hW'' using 1
    rw [List.take_add_one, List.getElem?_eq_getElem hiK']
    ext z
    simp only [Option.toList_some, List.toFinset_append, Finset.mem_union, Finset.mem_inter,
      List.mem_toFinset, List.mem_singleton]
    by_cases hz : z = σ.K[i]
    · subst hz; by_cases hv : σ.K[i] ∈ σ.val <;> simp [hv]
    · by_cases hv : σ.K[i] ∈ σ.val
      · simp [hv, hz]
      · simp [hv, hz]
  · have hieq : i = σ.K.length := by
      by_contra h; simp [show i < σ.K.length by omega] at h0
    subst hieq
    rw [List.take_length] at hW'
    have hWv : W ∪ (σ.val ∩ σ.K.toFinset) = W ∪ σ.val := by
      rw [Finset.inter_eq_left.mpr hval]
    rw [hWv] at hW'
    -- `Q += x`
    obtain ⟨ql, hnd, hset, hql, harr, hlen⟩ := hQ
    have hQn : Q.card < G.n := card_lt_of_not_mem hxQ
    have hqlen : ql.length = Q.card := by rw [← hset, List.toFinset_card_of_nodup hnd]
    have hob : (s'.charge 1).w "fp.ob" = st.w "fp.ob" := by
      simp only [State.charge_w]; exact hu'.wreg "fp.ob" (by decide)
    have hqls : (s'.charge 1).w "fp.ql" = ql.length := by
      simp only [State.charge_w]; rw [hu'.wreg "fp.ql" (by decide)]; exact hql
    have hxs : (s'.charge 1).w "fp.x" = x := by
      simp only [State.charge_w]; rw [hu'.wreg "fp.x" (by decide)]; exact hx
    have hQL : (s'.charge 1).wlen "fp.Q" = st.wlen "fp.Q" := by
      simp only [State.charge_wlen]; exact (hu'.warr "fp.Q" (by decide)).2
    have hQA : (s'.charge 1).wa "fp.Q" = st.wa "fp.Q" := by
      simp only [State.charge_wa]; exact (hu'.warr "fp.Q" (by decide)).1
    have hcaps : (s'.charge 1).cap = st.cap := by simp only [State.charge_cap]; exact hu'.cap
    refine runs_seq (runs_wstore (j := st.w "fp.ob" + ql.length) (a := x)
      (evalW_add_of (by simp [hob]) (by simp [hqls]) (by rw [hcaps]; omega)) (by simp [hxs])
      (by rw [hQL]; omega) ?_)
    refine runs_wset (a := ql.length + 1) (evalW_add_of (by simp [hqls])
      (evalW_lit_of (by simp [hcaps]; omega)) (by simp [hcaps]; omega)) ?_
    generalize hs3 : ((((s'.charge 1).storeW "fp.Q" (st.w "fp.ob" + ql.length) (x : ℕ)).charge 1).setW
      "fp.ql" (ql.length + 1)).charge 1 = s3
    have hu3 : Unchanged s' s3 ["fp.Q"] [] ["fp.ql"] [] := by
      rw [← hs3]
      refine ⟨fun a ha => ?_, fun _ _ => ⟨rfl, rfl⟩, fun y hy => ?_, fun _ _ => rfl, rfl, rfl⟩
      · simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at ha
        refine ⟨?_, by simp⟩; funext j; simp [ha]
      · simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at hy
        simp [hy]
    refine ⟨hW'.frame hu3 (by decide) (by decide), ⟨ql ++ [x], ?_, ?_, ?_, fun j hj => ?_, ?_⟩,
      (hM.frameR hu' (by decide) (by decide)).frameR hu3 (by decide) (by decide), ?_, ?_, ?_⟩
    · exact List.nodup_append.mpr ⟨hnd, List.nodup_singleton x, by
        intro a ha b hb hab; simp at hb; subst hb; subst hab
        exact hxQ (hset ▸ List.mem_toFinset.mpr ha)⟩
    · rw [List.toFinset_append, hset]; ext z; simp [or_comm]
    · rw [← hs3]; simp
    · have hob3 : s3.w "fp.ob" = st.w "fp.ob" := by
        rw [← hs3]; simp; exact hu'.wreg "fp.ob" (by decide)
      rw [hob3]
      by_cases hj' : j = ql.length
      · subst hj'; rw [← hs3]; simp
      · have hj2 : j < ql.length := by simp at hj; omega
        have hne : st.w "fp.ob" + j ≠ st.w "fp.ob" + ql.length := by omega
        rw [← hs3]; simp [hne, hj', List.getElem_append_left hj2, hQA, harr j hj2]
    · have hob3 : s3.w "fp.ob" = st.w "fp.ob" := by
        rw [← hs3]; simp; exact hu'.wreg "fp.ob" (by decide)
      rw [hob3, ← hs3]; simp [hQL]; exact hlen
    · exact ((hu'.cat hu3).mono (by decide) (by simp) (by decide) (by simp))
    · rw [← hs3]; simp; omega
    · rw [← hs3]; simp; omega

end Frontier.CHD.BL2
