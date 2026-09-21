import Frontier.CHD.BL2InvClear

/-!
# Frontier.CHD.BL2InvFail — B-L2: output of a failed search (FH.21: `W += val`, `Q += x`)
(agent-09, scratch, NON-GATE)
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}
variable {c : FPCtx G s} {T : Finset (Fin G.n)}

/-- `W` is listed (without duplicates) at `fp.W[ob ..]` with bitmap `fp.inW`. -/
def WRep (st : State V) (W : Finset (Fin G.n)) : Prop :=
  ∃ wl : List (Fin G.n), wl.Nodup ∧ wl.toFinset = W ∧ st.w "fp.wl" = wl.length ∧
    (∀ i (h : i < wl.length), st.wa "fp.W" (st.w "fp.ob" + i) = (wl[i] : ℕ)) ∧
    Bits st "fp.inW" W ∧ st.w "fp.ob" + G.n ≤ st.wlen "fp.W"

/-- `Q` is listed at `fp.Q[ob ..]`. -/
def QRep (st : State V) (Q : Finset (Fin G.n)) : Prop :=
  ∃ ql : List (Fin G.n), ql.Nodup ∧ ql.toFinset = Q ∧ st.w "fp.ql" = ql.length ∧
    (∀ i (h : i < ql.length), st.wa "fp.Q" (st.w "fp.ob" + i) = (ql[i] : ℕ)) ∧
    st.w "fp.ob" + G.n ≤ st.wlen "fp.Q"

theorem card_lt_of_not_mem {S : Finset (Fin G.n)} {y : Fin G.n} (hy : y ∉ S) : S.card < G.n := by
  have h1 : (insert y S).card ≤ G.n := by
    have := Finset.card_le_univ (insert y S); rwa [Fintype.card_fin] at this
  rw [Finset.card_insert_of_notMem hy] at h1; omega

/-- One step of the `W`-append loop at position `i` of `K`. -/
theorem failStep_spec {st : State V} {σ : SSt G s} {W : Finset (Fin G.n)} {i : ℕ}
    (hM : MyRep c T σ st) (hKk : σ.K.length ≤ c.k) (hW : WRep st W) (hi : st.w "fp.i" = i)
    (hiK : i < σ.K.length) (hcap : st.w "fp.ob" + G.n + 2 < st.cap) :
    Runs ops (seq (wset "fp.y" (load "fp.K" (var "fp.i")))
      (seq (ite (load "fp.val" (var "fp.y"))
              (ite (load "fp.inW" (var "fp.y")) skip
                (seq (wstore "fp.W" (add (var "fp.ob") (var "fp.wl")) (var "fp.y"))
                (seq (wset "fp.wl" (add (var "fp.wl") (lit 1)))
                     (wstore "fp.inW" (var "fp.y") (lit 1)))))
              skip)
           (wset "fp.i" (add (var "fp.i") (lit 1))))) st
      (fun st' => WRep st' (if σ.K[i] ∈ σ.val then insert σ.K[i] W else W) ∧
        st'.w "fp.i" = i + 1 ∧
        Unchanged st st' ["fp.W", "fp.inW"] [] ["fp.y", "fp.wl", "fp.i"] [] ∧
        st.cost ≤ st'.cost ∧ st'.cost ≤ st.cost + 8) := by
  obtain ⟨wl, hnd, hset, hwl, harr, hbits, hlen⟩ := hW
  have hKn : σ.K.length ≤ G.n := by
    have := List.Nodup.length_le_card hM.Knd; simpa using this
  have hKi : st.wa "fp.K" i = ((σ.K[i] : Fin G.n) : ℕ) := hM.karr i hiK
  have hiL : i < st.wlen "fp.K" := by have := hM.kcap; omega
  have hyn := (σ.K[i]).isLt
  have hvL : ((σ.K[i] : Fin G.n) : ℕ) < st.wlen "fp.val" := by rw [hM.val.1]; exact hyn
  have hwL : ((σ.K[i] : Fin G.n) : ℕ) < st.wlen "fp.inW" := by rw [hbits.1]; exact hyn
  have hlenW : wl.length = W.card := by rw [← hset, List.toFinset_card_of_nodup hnd]
  have hc0 : 0 < st.cap := by omega
  -- y := K[i]
  refine runs_seq (runs_wset (a := σ.K[i]) (by simp [hi, hiL, hKi]) ?_)
  generalize hs1 : (st.setW "fp.y" ((σ.K[i] : Fin G.n) : ℕ)).charge 1 = s1
  have hs1w : ∀ x, x ≠ "fp.y" → s1.w x = st.w x := fun x hx => by rw [← hs1]; simp [hx]
  have hs1y : s1.w "fp.y" = σ.K[i] := by rw [← hs1]; simp
  have hs1a : s1.wa = st.wa := by rw [← hs1]; rfl
  have hs1l : s1.wlen = st.wlen := by rw [← hs1]; rfl
  have hs1c : s1.cap = st.cap := by rw [← hs1]; rfl
  have hs1k : s1.cost = st.cost + 1 := by rw [← hs1]; simp
  have hs1u : Unchanged st s1 [] [] ["fp.y"] [] := by
    rw [← hs1]; exact ((unch_setW st "fp.y" _).cat (unch_charge' _ 1)).mono (by simp) (by simp)
      (by simp) (by simp)
  -- the final `i := i + 1` from any state `s` agreeing with `st` on `fp.i`
  have hfin : ∀ (s : State V) (W' : Finset (Fin G.n)), s.w "fp.i" = i → s.cap = st.cap →
      WRep s W' → Unchanged st s ["fp.W", "fp.inW"] [] ["fp.y", "fp.wl"] [] →
      st.cost ≤ s.cost → s.cost ≤ st.cost + 7 →
      Runs ops (wset "fp.i" (add (var "fp.i") (lit 1))) s (fun st' => WRep st' W' ∧
        st'.w "fp.i" = i + 1 ∧
        Unchanged st st' ["fp.W", "fp.inW"] [] ["fp.y", "fp.wl", "fp.i"] [] ∧
        st.cost ≤ st'.cost ∧ st'.cost ≤ st.cost + 8) := by
    intro s W' hsi hsc hWs hus hc1 hc2
    refine runs_wset (a := i + 1) (evalW_add_of (by simp [hsi]) (evalW_lit_of (by rw [hsc]; omega))
      (by rw [hsc]; omega)) ?_
    obtain ⟨wl', hnd', hset', hwl', harr', hbits', hlen'⟩ := hWs
    refine ⟨⟨wl', hnd', hset', by simpa using hwl', fun j hj => by simpa using harr' j hj,
      ⟨by simpa using hbits'.1, fun v => by simpa using hbits'.2 v⟩, by simpa using hlen'⟩,
      by simp, ?_, by simp; omega, by simp; omega⟩
    exact (hus.mono (fun _ h => h) (fun _ h => h) (by simp) (fun _ h => h)).trans
      (((unch_setW s "fp.i" _).cat (unch_charge' _ 1)).mono (by simp) (by simp) (by simp) (by simp))
  have hWst : WRep st W := ⟨wl, hnd, hset, hwl, harr, hbits, hlen⟩
  have hWs1 : WRep s1 W := ⟨wl, hnd, hset, by rw [hs1w _ (by decide)]; exact hwl,
    fun j hj => by rw [hs1a, hs1w _ (by decide)]; exact harr j hj,
    ⟨by rw [hs1l]; exact hbits.1, fun v => by rw [hs1a]; exact hbits.2 v⟩,
    by rw [hs1w _ (by decide), hs1l]; exact hlen⟩
  refine runs_seq ?_
  by_cases hval : σ.K[i] ∈ σ.val
  · have hv1 : s1.wa "fp.val" (σ.K[i]) = 1 := by rw [hs1a, hM.val.2]; simp [hval]
    refine runs_ite_true (x := 1) (by simp [hs1y, hs1l, hvL, hv1]) one_ne_zero ?_
    by_cases hWy : σ.K[i] ∈ W
    · -- already in `W`
      have hw1 : (s1.charge 1).wa "fp.inW" (σ.K[i]) = 1 := by
        simp only [State.charge_wa]; rw [hs1a, hbits.2]; simp [hWy]
      refine runs_ite_true (x := 1) (by simp [hs1y, hs1l, hwL]; simpa using hw1) one_ne_zero
        (runs_skip ?_)
      rw [if_pos hval, Finset.insert_eq_of_mem hWy]
      refine hfin _ W (by simp [hs1w "fp.i" (by decide), hi]) (by simp [hs1c]) ?_ ?_ (by simp; omega)
        (by simp; omega)
      · obtain ⟨wl', hnd', hset', hwl', harr', hbits', hlen'⟩ := hWs1
        exact ⟨wl', hnd', hset', by simpa using hwl', fun j hj => by simpa using harr' j hj,
          ⟨by simpa using hbits'.1, fun v => by simpa using hbits'.2 v⟩, by simpa using hlen'⟩
      · exact (hs1u.trans ((Unchanged.charge s1 1 _ _ _ _).trans ((Unchanged.charge _ 1 _ _ _ _).trans
          (Unchanged.charge _ 1 _ _ _ _)))).mono (by simp) (by simp) (by simp) (by simp)
    · -- append `y` to `W`
      have hw0 : (s1.charge 1).wa "fp.inW" (σ.K[i]) = 0 := by
        simp only [State.charge_wa]; rw [hs1a, hbits.2]; simp [hWy]
      refine runs_ite_false (by simp [hs1y, hs1l, hwL]; simpa using hw0) ?_
      have hWn : W.card < G.n := card_lt_of_not_mem hWy
      have hob : s1.w "fp.ob" = st.w "fp.ob" := hs1w _ (by decide)
      have hwls : s1.w "fp.wl" = wl.length := by rw [hs1w _ (by decide)]; exact hwl
      have hpos : st.w "fp.ob" + wl.length < st.wlen "fp.W" := by omega
      refine runs_seq (runs_wstore (j := st.w "fp.ob" + wl.length) (a := σ.K[i])
        (evalW_add_of (by simp [hob]) (by simp [hwls]) (by simp [hs1c]; omega))
        (by simp [hs1y]) (by simp [hs1l]; exact hpos) ?_)
      refine runs_seq (runs_wset (a := wl.length + 1) (evalW_add_of (by simp [hwls])
        (evalW_lit_of (by simp [hs1c]; omega)) (by simp [hs1c]; omega)) ?_)
      refine runs_wstore (j := σ.K[i]) (a := 1) (by simp [hs1y]) (evalW_lit_of (by simp [hs1c]; omega))
        (by simp [hs1l]; exact hwL) ?_
      rw [if_pos hval]
      refine hfin _ _ (by simp [hs1w "fp.i" (by decide), hi]) (by simp [hs1c]) ?_ ?_ (by simp; omega)
        (by simp; omega)
      · refine ⟨wl ++ [σ.K[i]], List.nodup_append.mpr ⟨hnd, List.nodup_singleton _, ?_⟩, ?_, by simp,
          fun j hj => ?_, ⟨by simp [hs1l]; exact hbits.1, fun v => ?_⟩, by simp [hs1l, hob]; omega⟩
        · intro a ha b hb hab; simp at hb; subst hb; subst hab
          exact hWy (hset ▸ List.mem_toFinset.mpr ha)
        · rw [List.toFinset_append, hset]; ext z; simp [or_comm]
        · by_cases hj' : j = wl.length
          · subst hj'; simp [hob]
          · have hj2 : j < wl.length := by simp at hj; omega
            have hne : st.w "fp.ob" + j ≠ st.w "fp.ob" + wl.length := by omega
            simp [hob, hne, hj', List.getElem_append_left hj2, hs1a, harr j hj2]
        · by_cases hvy : v = σ.K[i]
          · subst hvy; simp
          · have : (v : ℕ) ≠ σ.K[i] := fun h => hvy (Fin.ext h)
            simp [this, hvy, hs1a, hbits.2 v]
      · refine (hs1u.mono (by simp) (by simp) (by simp) (by simp)).trans ?_
        refine ⟨fun a ha => ?_, fun _ _ => ⟨rfl, rfl⟩, fun x hx => ?_, fun _ _ => rfl, rfl, rfl⟩
        · simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at ha
          refine ⟨?_, by simp⟩
          funext j; simp [ha.1, ha.2]
        · simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at hx
          simp [hx.1, hx.2]
  · -- not valid: skip
    have hv0 : s1.wa "fp.val" (σ.K[i]) = 0 := by rw [hs1a, hM.val.2]; simp [hval]
    refine runs_ite_false (by simp [hs1y, hs1l, hvL, hv0]) (runs_skip ?_)
    rw [if_neg hval]
    refine hfin _ W (by simp [hs1w "fp.i" (by decide), hi]) (by simp [hs1c]) ?_ ?_ (by simp; omega)
      (by simp; omega)
    · obtain ⟨wl', hnd', hset', hwl', harr', hbits', hlen'⟩ := hWs1
      exact ⟨wl', hnd', hset', by simpa using hwl', fun j hj => by simpa using harr' j hj,
        ⟨by simpa using hbits'.1, fun v => by simpa using hbits'.2 v⟩, by simpa using hlen'⟩
    · exact (hs1u.trans ((Unchanged.charge s1 1 _ _ _ _).trans (Unchanged.charge _ 1 _ _ _ _))).mono
        (by simp) (by simp) (by simp) (by simp)

end Frontier.CHD.BL2
