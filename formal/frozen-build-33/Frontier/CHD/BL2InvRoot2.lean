import Frontier.CHD.BL2InvRoot

/-!
# Frontier.CHD.BL2InvRoot2 — B-L2: the search branch of a root (agent-09, scratch, NON-GATE)
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}
variable {LI : LabI V ops G s} {X : LabX LI} {TI : TreeI V ops G s} {c : FPCtx G s}
  {slB slX sA : String} {SL : List (Fin G.n)} {d0 : Labels G s}

/-- Post-state facts of the search branch, ready for `root_finish`. -/
def RootPost (LI : LabI V ops G s) (X : LabX LI) (TI : TreeI V ops G s) (c : FPCtx G s)
    (slB slX sA : String) (SL : List (Fin G.n)) (d0 : Labels G s) (ι₀ : IState G s) (g₀ : LI.Gh)
    (st₀ : State V) (j : ℕ) (st5 : State V) : Prop :=
  ∃ ι' n' g', IRep LI TI c slB slX ι' g' st5 ∧ st5.w "fp.j" = j ∧ WalkInv ι'.d ∧
    (∀ v, ι'.d v ≤ d0 v) ∧ FInv c ι' ∧ (∀ q ∈ ι'.Q, q ∈ SL.take (j + 1)) ∧ LI.gext g₀ g' ∧
    (∀ ι'' n'', Invoke c ι' (SL.drop (j + 1)) ι'' n'' → Invoke c ι₀ SL ι'' (n' + n'')) ∧
    Unchanged st₀ st5 (invWA LI TI sA) (invVA LI TI) (invWR LI X TI) (invVR LI X TI) ∧
    st₀.cost ≤ st5.cost ∧ st5.cost + 1 ≤ st₀.cost + TI.Cinit + 4 + KI LI X TI * n'

open Classical in
theorem root_search (hown : OutOK c) (hsort : OutSorted c) (hnd : OutNodup c)
    (hNI : NamesI LI X TI slB slX sA)
    {S : Finset (Fin G.n)} (hpre : CallPre c.B S d0) (hSLS : ∀ x ∈ SL, x ∈ S) (hSLnd : SL.Nodup)
    {ι₀ : IState G s} {g₀ : LI.Gh} {st₀ : State V}
    (hbud : ∀ ι' n', Invoke c ι₀ SL ι' n' →
      st₀.cost + TI.Cinit + 5 + KI LI X TI * n' + KI LI X TI ≤ LI.c0 + st₀.cap)
    (hcapW : c.k + 4 < st₀.cap) (hcapN : st₀.w "fp.ob" + G.n + 2 < st₀.cap)
    (hhext : c.k ≤ c.hext) (hk1 : 1 ≤ c.k)
    {ι : IState G s} {j n : ℕ} {g : LI.Gh} {st1 : State V}
    (hj : j < SL.length) (hR : IRep LI TI c slB slX ι g st1)
    (hwalk : WalkInv ι.d) (hle : ∀ v, ι.d v ≤ d0 v) (hfinv : FInv c ι)
    (hQsub : ∀ q ∈ ι.Q, q ∈ SL.take j) (hhist : LI.gext g₀ g)
    (hcont : ∀ ι'' n', Invoke c ι (SL.drop j) ι'' n' → Invoke c ι₀ SL ι'' (n + n'))
    (hu1 : Unchanged st₀ st1 (invWA LI TI sA) (invVA LI TI) (invWR LI X TI) (invVR LI X TI))
    (hc01 : st₀.cost ≤ st1.cost) (hc1 : st1.cost ≤ st₀.cost + TI.Cinit + 4 + KI LI X TI * n + 3)
    (hx : st1.w "fp.x" = SL[j]) (hjr : st1.w "fp.j" = j) (hxT : SL[j] ∉ ι.tv) :
    Runs ops (seq fpInitSearch (seq (fpSearch LI X slB slX)
      (seq (ite (var "fp.sres") TI.grow fpFailOut) fpClear))) st1
      (RootPost LI X TI c slB slX sA SL d0 ι₀ g₀ st₀ j) := by
  have hcap1 : st1.cap = st₀.cap := hu1.cap
  have hob1 : st1.w "fp.ob" = st₀.w "fp.ob" := hu1.wreg "fp.ob" (fun h => by
    simp only [invWR, List.mem_append] at h
    rcases h with ((h | h) | h) | h
    · exact hNI.srch_inv _ h (by simp [invKeep])
    · simp [invWRegs] at h
    · exact hNI.namesT.gWR_ok _ h (by simp [invRegs])
    · exact hNI.namesT.iWR_ok _ h (by simp [invRegs]))
  have hxS : SL[j] ∈ S := hSLS _ (List.getElem_mem _)
  have hxtop : ι.d SL[j] ≠ ⊤ := ne_top_of_lt (lt_of_le_of_lt (hle _) (hpre.inRange _ hxS))
  have hS0 : SInv c (initSt ι.d ι.D SL[j]) := initSt_inv hwalk hxtop
  have hdrop : SL.drop j = SL[j] :: SL.drop (j + 1) := List.drop_eq_getElem_cons hj
  have hdropS : ∀ y ∈ SL.drop (j + 1), y ∈ S := fun y hy => hSLS y (List.mem_of_mem_drop hy)
  have hxQ : SL[j] ∉ ι.Q := fun h => by
    have h1 := hQsub _ h
    have h2 : SL[j] ∈ SL.drop j := by rw [hdrop]; exact List.mem_cons_self
    exact List.disjoint_take_drop hSLnd le_rfl h1 h2
  have hKIS : KS LI X ≤ KI LI X TI := by simp only [KI]; omega
  -- (1) FH.4: the initial search state
  refine runs_seq ((initSearch_spec (d' := ι.d) (D' := ι.D) hR.my hx hk1
    (by rw [hcap1]; omega)).mono ?_)
  rintro st2 ⟨hM2, hu12, hc2⟩
  have hL2 := hR.lab.frame_inv hNI hu12 (by decide) (by decide) (by omega)
  have hSR2 : SRep LI c ι.tv slB slX (initSt ι.d ι.D SL[j]) g st2 :=
    ⟨hL2, hM2, hR.out.frameR hu12 (by decide)⟩
  have hFR2 : TI.FR st2 ι.trees := FR.frame_inv hNI hR.fr hu12 (by decide) (by decide)
  have hW2 := hR.W.frame hu12 (by decide) (by decide)
  have hQ2 := hR.Q.frame hu12 (by decide) (by decide)
  have hcap2 : st2.cap = st₀.cap := by rw [hu12.cap, hcap1]
  -- (2) FH.5–FH.22: the local search
  have hbudS : ∀ σ'' res' n'', Search c ι.tv (initSt ι.d ι.D SL[j]) σ'' res' n'' →
      st2.cost + 2 + KS LI X * n'' + KS LI X ≤ LI.c0 + st2.cap := by
    intro σ'' res' n'' hs
    obtain ⟨ι₃, N, h₃, hN⟩ := search_extends hown hsort hpre hdropS hwalk hle hxT hxtop hs
    have hb := hbud _ _ (hcont _ _ (hdrop ▸ h₃))
    have e1 : KI LI X TI * (n + N) = KI LI X TI * n + KI LI X TI * N := Nat.mul_add _ _ _
    have e2 : KI LI X TI * N ≥ KI LI X TI * (n'' + 2) := Nat.mul_le_mul_left _ hN
    have e3 : KI LI X TI * (n'' + 2) = KI LI X TI * n'' + 2 * KI LI X TI := by ring
    have e4 : KS LI X * n'' ≤ KI LI X TI * n'' := Nat.mul_le_mul_right _ hKIS
    have e5 : 60 ≤ KI LI X TI := by simp only [KI]; omega
    rw [hcap2]; omega
  refine runs_seq ((search_spec hown hsort hnd hNI.names hNI.namesX hSR2 hS0 hbudS
    (by rw [hcap2]; omega) hhext).mono ?_)
  rintro st3 ⟨σ', res, nS, g', hsrch, hSR3, hI3, hcode3, hhit3, hgg', hu23, hc03, hc3⟩
  have hcap3 : st3.cap = st₀.cap := by rw [hu23.cap, hcap2]
  have hsrchR : ∀ r ∈ invKeep, st3.w r = st2.w r := fun r hr => hu23.wreg r (fun h =>
    hNI.srch_inv r h hr)
  have hx3 : st3.w "fp.x" = SL[j] := by
    rw [hsrchR "fp.x" (by simp [invKeep]), hu12.wreg "fp.x" (by decide)]; exact hx
  have hj3 : st3.w "fp.j" = j := by
    rw [hsrchR "fp.j" (by simp [invKeep]), hu12.wreg "fp.j" (by decide)]; exact hjr
  have hob3 : st3.w "fp.ob" = st₀.w "fp.ob" := by
    rw [hsrchR "fp.ob" (by simp [invKeep]), hu12.wreg "fp.ob" (by decide)]; exact hob1
  have hWA3 : Disj (srchWA LI) ["fp.W", "fp.inW"] := hNI.srch_invA.mono_right (by
    intro z hz; simp at hz ⊢; simp [invArrs]; tauto)
  have hQA3 : Disj (srchWA LI) ["fp.Q"] := hNI.srch_invA.mono_right (by
    intro z hz; simp at hz ⊢; simp [invArrs, hz])
  have hWR3 : Disj (srchWR LI X) ["fp.wl", "fp.ob"] := hNI.srch_inv.mono_right (by
    intro z hz; simp at hz ⊢; simp [invKeep]; tauto)
  have hQR3 : Disj (srchWR LI X) ["fp.ql", "fp.ob"] := hNI.srch_inv.mono_right (by
    intro z hz; simp at hz ⊢; simp [invKeep]; tauto)
  have hW3 := hW2.frame hu23 hWA3 hWR3
  have hQ3 := hQ2.frame hu23 hQA3 hQR3
  have hFR3 : TI.FR st3 ι.trees := TI.FR_frame hFR2 hu23 hNI.namesT.fr_srch hNI.namesT.fr_srchV
    hNI.namesT.fr_srchR hNI.namesT.fr_srchVR
  have hK3 : σ'.K.length ≤ c.k := Search.K_le hsrch (by simp [initSt]; omega)
  have hval3 : σ'.val ⊆ σ'.K.toFinset := fun v hv => List.mem_toFinset.mpr (hI3.valK v hv)
  obtain ⟨-, hle3, -⟩ := Search.inv hown hsort hsrch hS0 (fun w hw => absurd hw (Finset.notMem_empty w))
  have hle' : ∀ v, σ'.d v ≤ d0 v := fun v => (hle3 v).trans (hle v)
  have hKn : σ'.K.length ≤ G.n := by
    have := List.Nodup.length_le_card hSR3.my.Knd; simpa using this
  -- common arithmetic of a root
  have e5 : 60 ≤ KI LI X TI := by simp only [KI]; omega
  have eS : KS LI X * nS ≤ KI LI X TI * nS := Nat.mul_le_mul_right _ hKIS
  have eE : KI LI X TI * (n + (nS + σ'.K.length + 2)) =
      KI LI X TI * n + KI LI X TI * nS + KI LI X TI * σ'.K.length + 2 * KI LI X TI := by ring
  have hcharge3 : Unchanged st3 (st3.charge 1) [] [] [] [] := Unchanged.charge st3 1 _ _ _ _
  refine runs_seq ?_
  by_cases hres : res = .failed
  · -- FH.21: the search FAILED -- W ∪= val, Q += x (Layer A `Invoke.fail`)
    subst hres
    have hsres : st3.w "fp.sres" = 0 := by
      rcases hcode3 with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h (by decide)
      · exact absurd h (by decide)
    refine runs_ite_false (by simp [hsres]) ?_
    refine (failOut_spec (st := st3.charge 1) (hSR3.my.charge' 1) hK3 hval3
      (hW3.frame hcharge3 (Disj.nil_left _) (Disj.nil_left _))
      (hQ3.frame hcharge3 (Disj.nil_left _) (Disj.nil_left _)) hxQ (by simpa using hx3)
      (by simp [hob3, hcap3]; omega)).mono ?_
    rintro st4 ⟨hW4, hQ4, hM4, hu34, hc04, hc4⟩
    have hcap4 : st4.cap = st₀.cap := by rw [hu34.cap]; simp [hcap3]
    refine (clear_spec (d := σ'.d) (D := σ'.D) hM4 hval3 hK3 (by rw [hcap4]; omega)).mono ?_
    rintro st5 ⟨hM5, hu45, hc05, hc5⟩
    have hu35 : Unchanged st3 st5 ([] ++ ["fp.W", "fp.inW", "fp.Q"] ++ ["fp.inK", "fp.val", "fp.inH"])
        ([] ++ [] ++ []) ([] ++ ["fp.i", "fp.y", "fp.wl", "fp.ql"] ++ ["fp.y", "fp.i", "fp.kl", "fp.hsz"])
        ([] ++ [] ++ []) := (hcharge3.cat hu34).cat hu45
    refine ⟨{ ι with d := σ'.d, D := σ'.D, W := ι.W ∪ σ'.val, Q := insert SL[j] ι.Q },
      n + (nS + σ'.K.length + 2), g', ⟨?_, hM5, ?_, ?_, ?_, ?_⟩, ?_, hI3.walk, hle',
      FInv.congr_tr hfinv rfl rfl, ?_, LI.gext_trans hhist hgg', ?_, ?_, ?_, ?_⟩
    · exact hSR3.lab.frame_inv hNI hu35 (by decide) (by decide) (by simp at hc04 hc05; omega)
    · exact hSR3.out.frameR hu35 (by decide)
    · exact FR.frame_inv hNI hFR3 hu35 (by decide) (by decide)
    · exact hW4.frame hu45 (by decide) (by decide)
    · exact hQ4.frame hu45 (by decide) (by decide)
    · rw [hu45.wreg "fp.j" (by decide), hu34.wreg "fp.j" (by decide)]; simpa using hj3
    · intro q hq
      have htk : SL.take (j + 1) = SL.take j ++ [SL[j]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
      rw [htk]
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact List.mem_append_right _ (List.mem_singleton_self _)
      · exact List.mem_append_left _ (hQsub q hq)
    · intro ι'' n'' h''
      have hinv := Invoke.fail ι ι'' SL[j] (SL.drop (j + 1)) σ' nS n'' hxT hsrch h''
      rw [← hdrop] at hinv
      have := hcont _ _ hinv
      rwa [show n + (nS + n'' + σ'.K.length + 2) = n + (nS + σ'.K.length + 2) + n'' by omega]
        at this
    · refine ((hu1.trans ((hu12.cat hu23).mono ?_ ?_ ?_ ?_)).trans (hu35.mono ?_ ?_ ?_ ?_))
      · exact List.append_subset.mpr ⟨List.Subset.trans (by decide) myArrs_sub_invWA,
          srchWA_sub_invWA⟩
      · exact List.append_subset.mpr ⟨fun _ h => absurd h List.not_mem_nil, srchVA_sub_invVA⟩
      · exact List.append_subset.mpr ⟨List.Subset.trans (by decide) myRegs_sub_invWR,
          srchWR_sub_invWR⟩
      · exact List.append_subset.mpr ⟨fun _ h => absurd h List.not_mem_nil, srchVR_sub_invVR⟩
      · exact List.append_subset.mpr ⟨List.append_subset.mpr ⟨fun _ h => absurd h List.not_mem_nil,
          List.Subset.trans (by decide) invArrs_sub_invWA⟩, List.Subset.trans (by decide) myArrs_sub_invWA⟩
      · intro z hz; simp at hz
      · exact List.append_subset.mpr ⟨List.append_subset.mpr ⟨fun _ h => absurd h List.not_mem_nil,
          List.Subset.trans (by decide) invWRegs_sub⟩, fun z hz => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
            rcases hz with rfl | rfl | rfl | rfl
            · exact invWRegs_sub (by simp [invWRegs])
            · exact invWRegs_sub (by simp [invWRegs])
            · exact myRegs_sub_invWR (by simp [myRegs])
            · exact myRegs_sub_invWR (by simp [myRegs])⟩
      · intro z hz; simp at hz
    · simp at hc04 hc05; omega
    · simp at hc4 hc5
      have : 15 * σ'.K.length ≤ KI LI X TI * σ'.K.length := Nat.mul_le_mul_right _ (by omega)
      omega
  · -- FH.12 / FH.23: SUCCESS or CONTACT -- grow the forest (Layer A `Invoke.grow`)
    have hsres : st3.w "fp.sres" ≠ 0 := by
      rcases hcode3 with ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
      · exact absurd h hres
      · rw [h]; decide
      · rw [h]; decide
    refine runs_ite_true (x := st3.w "fp.sres") (by simp) hsres ?_
    have hM3c := hSR3.my.charge' 1
    have hgrow := TI.grow_spec (st := st3.charge 1) (c := c) (ι := ι) (x := SL[j]) (σ' := σ')
      (res := res) (n := nS) hown hsort hxT hres hsrch hS0 hfinv
      (TI.FR_frame hFR3 hcharge3 (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _)
        (Disj.nil_left _)) hM3c.fm hM3c.karr hM3c.kl (hK3.trans hM3c.kcap) hM3c.kpL hM3c.kp
      (by simpa using hx3)
      (fun h => by obtain ⟨a, b, h1, h2, h3⟩ := hhit3 h; exact ⟨a, b, h1, by simpa using h2,
        by simpa using h3⟩)
      (by simpa [SResCode] using hcode3) (by simp [hcap3]; omega)
    refine (hgrow.mono ?_)
    rintro st4 ⟨hFR4, hfm4, hu34, hc04, hc4⟩
    have hgA := hNI.namesT.gWA_ok
    have hgR := hNI.namesT.gWR_ok
    have hgAm : Disj TI.gWA (myRepArrs.erase "fp.fm") := hgA.mono_right (fun z hz => by
      simp only [List.mem_append]; left; left; left; left; left
      exact (by decide : myRepArrs.erase "fp.fm" ⊆ myArrs.erase "fp.fm") hz)
    have hgRm : Disj TI.gWR myRepRegs := hgR.mono_right (fun z hz => by
      simp only [List.mem_append]; left; left; left; left; left
      exact (by decide : myRepRegs ⊆ myRegs) hz)
    have hM4 : MyRep c (ι.tv ∪ σ'.K.toFinset) σ' st4 :=
      MyRep.setFm hM3c hfm4 hu34 hgAm hgRm
    have hcap4 : st4.cap = st₀.cap := by rw [hu34.cap]; simp [hcap3]
    refine (clear_spec (d := σ'.d) (D := σ'.D) hM4 hval3 hK3 (by rw [hcap4]; omega)).mono ?_
    rintro st5 ⟨hM5, hu45, hc05, hc5⟩
    have hu35 : Unchanged st3 st4 ([] ++ TI.gWA) ([] ++ TI.gVA) ([] ++ TI.gWR) ([] ++ TI.gVR) :=
      hcharge3.cat hu34
    -- label layer across the tree layer
    have hLab4 : LabRep LI c slB slX σ'.d g' st4 :=
      hSR3.lab.frame (hu35.mono (by simp) (by simp) (by simp) (by simp))
        (hgA.mono_right (fun z hz => by simp only [List.mem_append]; left; left; right; exact hz))
        (hNI.namesT.gVA_ok.mono_right (fun z hz => by simp only [List.mem_append]; left; left; exact hz))
        (hgA.mono_right (fun z hz => by simp only [List.mem_append]; left; right; exact hz))
        (hNI.namesT.gVA_ok.mono_right (fun z hz => by simp only [List.mem_append]; left; right; exact hz))
        (hgR.mono_right (fun z hz => by simp only [List.mem_append]; left; right; exact hz))
        (hNI.namesT.gVR_ok.mono_right (fun z hz => by simp only [List.mem_append]; left; exact hz))
        (hgA.mono_right (fun z hz => by simp only [List.mem_append]; right; exact hz))
        (hNI.namesT.gVA_ok.mono_right (fun z hz => by simp only [List.mem_append]; right; exact hz))
        (hgR.mono_right (fun z hz => by simp only [List.mem_append]; right; exact hz))
        (hNI.namesT.gVR_ok.mono_right (fun z hz => by simp only [List.mem_append]; right; exact hz))
        (by simp at hc04; omega)
    have hgAW : Disj TI.gWA ["fp.W", "fp.inW"] := hgA.mono_right (fun z hz => by
      simp only [List.mem_append]; left; left; left; left; right
      exact (by decide : (["fp.W", "fp.inW"] : List String) ⊆ invArrs) hz)
    have hgAQ : Disj TI.gWA ["fp.Q"] := hgA.mono_right (fun z hz => by
      simp only [List.mem_append]; left; left; left; left; right
      exact (by decide : (["fp.Q"] : List String) ⊆ invArrs) hz)
    have hgRW : Disj TI.gWR ["fp.wl", "fp.ob"] := hgR.mono_right (fun z hz => by
      simp only [List.mem_append]; left; left; right
      exact (by decide : (["fp.wl", "fp.ob"] : List String) ⊆ invRegs) hz)
    have hgRQ : Disj TI.gWR ["fp.ql", "fp.ob"] := hgR.mono_right (fun z hz => by
      simp only [List.mem_append]; left; left; right
      exact (by decide : (["fp.ql", "fp.ob"] : List String) ⊆ invRegs) hz)
    have hgAO : Disj TI.gWA ["gHd", "gNxt"] := hgA.mono_right (fun z hz => by
      simp only [List.mem_append]; left; left; left; left; left
      exact (by decide : (["gHd", "gNxt"] : List String) ⊆ myArrs.erase "fp.fm") hz)
    refine ⟨{ ι with d := σ'.d, D := σ'.D, tv := ι.tv ∪ σ'.K.toFinset, trees := growForest res ι.trees SL[j] σ' },
      n + (nS + σ'.K.length + 2), g', ⟨?_, hM5, ?_, ?_, ?_, ?_⟩, ?_, hI3.walk, hle',
      growForest_inv hown hsort hxT hres hsrch hS0 hfinv, ?_, LI.gext_trans hhist hgg', ?_, ?_,
      ?_, ?_⟩
    · exact hLab4.frame_inv hNI hu45 (by decide) (by decide) (by omega)
    · exact ((hSR3.out.frameR hu35 (by
        intro z hz; simp only [List.nil_append] at hz; exact hgAO z hz)).frameR hu45 (by decide))
    · exact FR.frame_inv hNI hFR4 hu45 (by decide) (by decide)
    · exact ((hW3.frame hu35 (by intro z hz; simp only [List.nil_append] at hz; exact hgAW z hz)
        (by intro z hz; simp only [List.nil_append] at hz; exact hgRW z hz)).frame hu45 (by decide)
        (by decide))
    · exact ((hQ3.frame hu35 (by intro z hz; simp only [List.nil_append] at hz; exact hgAQ z hz)
        (by intro z hz; simp only [List.nil_append] at hz; exact hgRQ z hz)).frame hu45 (by decide)
        (by decide))
    · have hjg : "fp.j" ∉ TI.gWR := fun h => hgR "fp.j" h (by
        simp only [List.mem_append]; left; left; right; exact (by decide : "fp.j" ∈ invRegs))
      rw [hu45.wreg "fp.j" (by decide), hu35.wreg "fp.j" (by simpa using hjg)]
      simpa using hj3
    · intro q hq
      have htk : SL.take (j + 1) = SL.take j ++ [SL[j]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
      rw [htk]; exact List.mem_append_left _ (hQsub q hq)
    · intro ι'' n'' h''
      have hinv := Invoke.grow ι ι'' SL[j] (SL.drop (j + 1)) σ' res nS n'' hxT hres hsrch h''
      rw [← hdrop] at hinv
      have := hcont _ _ hinv
      rwa [show n + (nS + n'' + σ'.K.length + 2) = n + (nS + σ'.K.length + 2) + n'' by omega]
        at this
    · refine ((hu1.trans ((hu12.cat hu23).mono ?_ ?_ ?_ ?_)).trans ((hu35.cat hu45).mono ?_ ?_ ?_ ?_))
      · exact List.append_subset.mpr ⟨List.Subset.trans (by decide) myArrs_sub_invWA,
          srchWA_sub_invWA⟩
      · exact List.append_subset.mpr ⟨fun _ h => absurd h List.not_mem_nil, srchVA_sub_invVA⟩
      · exact List.append_subset.mpr ⟨List.Subset.trans (by decide) myRegs_sub_invWR,
          srchWR_sub_invWR⟩
      · exact List.append_subset.mpr ⟨fun _ h => absurd h List.not_mem_nil, srchVR_sub_invVR⟩
      · exact List.append_subset.mpr ⟨fun z hz => by
            simp only [List.nil_append] at hz; exact gWA_sub_invWA hz,
          List.Subset.trans (by decide) myArrs_sub_invWA⟩
      · exact List.append_subset.mpr ⟨fun z hz => by
            simp only [List.nil_append] at hz; exact gVA_sub_invVA hz,
          fun _ h => absurd h List.not_mem_nil⟩
      · exact List.append_subset.mpr ⟨fun z hz => by
            simp only [List.nil_append] at hz; exact gWR_sub_invWR hz, fun z hz => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
            rcases hz with rfl | rfl | rfl | rfl
            · exact invWRegs_sub (by simp [invWRegs])
            · exact invWRegs_sub (by simp [invWRegs])
            · exact myRegs_sub_invWR (by simp [myRegs])
            · exact myRegs_sub_invWR (by simp [myRegs])⟩
      · exact List.append_subset.mpr ⟨fun z hz => by
            simp only [List.nil_append] at hz; exact gVR_sub_invVR hz,
          fun _ h => absurd h List.not_mem_nil⟩
    · simp at hc04 hc05; omega
    · simp at hc4 hc5
      have h1 : (TI.Cg + 6) * σ'.K.length ≤ KI LI X TI * σ'.K.length :=
        Nat.mul_le_mul_right _ (by simp only [KI]; omega)
      have h2 : TI.Cg * (σ'.K.length + 1) = TI.Cg * σ'.K.length + TI.Cg := by ring
      have h3 : (TI.Cg + 6) * σ'.K.length = TI.Cg * σ'.K.length + 6 * σ'.K.length := by ring
      have h4 : TI.Cg + 30 ≤ KI LI X TI := by simp only [KI]; omega
      omega

end Frontier.CHD.BL2
