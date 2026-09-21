import Frontier.CHD.BL2InvDefs

/-!
# Frontier.CHD.BL2InvStep — B-L2: one root of the invocation loop (agent-09, scratch, NON-GATE)
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}
variable {LI : LabI V ops G s} {X : LabX LI} {TI : TreeI V ops G s} {c : FPCtx G s}
  {slB slX sA : String} {SL : List (Fin G.n)} {d0 : Labels G s}

/-- Replacing the tree-mark bitmap. -/
theorem MyRep.setFm {T T' : Finset (Fin G.n)} {σ : SSt G s} {st st' : State V}
    {wa va wr vr : List String} (hM : MyRep c T σ st) (hB : Bits st' "fp.fm" T')
    (hu : Unchanged st st' wa va wr vr) (hwa : Disj wa (myRepArrs.erase "fp.fm"))
    (hwr : Disj wr myRepRegs) : MyRep c T' σ st' := by
  have A : ∀ a ∈ myRepArrs.erase "fp.fm", st'.wa a = st.wa a ∧ st'.wlen a = st.wlen a :=
    fun a ha => hu.warr a (fun h' => hwa a h' ha)
  have R : ∀ x ∈ myRepRegs, st'.w x = st.w x := fun x hx => hu.wreg x (fun h' => hwr x h' hx)
  have aH := A "gHead" (by decide)
  have aHp := A "fp.H" (by decide)
  have ahp := A "fp.hp" (by decide)
  have ainH := A "fp.inH" (by decide)
  have aK := A "fp.K" (by decide)
  have ainK := A "fp.inK" (by decide)
  have aval := A "fp.val" (by decide)
  have akp := A "fp.kp" (by decide)
  obtain ⟨hl, hnd, hset, hsz, hcap, harr, hpL, hpos, hbL, hb⟩ := hM.heap
  exact ⟨by rw [R "gM" (by simp [myRepRegs])]; exact hM.gM, by rw [aH.2]; exact hM.headL,
    fun q => by rw [aH.1]; exact hM.head q,
    ⟨hl, hnd, hset, by rw [R "fp.hsz" (by simp [myRepRegs])]; exact hsz, by rw [aHp.2]; exact hcap,
      fun i hi => by rw [aHp.1]; exact harr i hi, by rw [ahp.2]; exact hpL,
      fun i hi => by rw [ahp.1]; exact hpos i hi, by rw [ainH.2]; exact hbL,
      fun v => by rw [ainH.1]; exact hb v⟩,
    by rw [R "fp.kl" (by simp [myRepRegs])]; exact hM.kl, by rw [aK.2]; exact hM.kcap,
    fun i hi => by rw [aK.1]; exact hM.karr i hi,
    ⟨by rw [ainK.2]; exact hM.inK.1, fun v => by rw [ainK.1]; exact hM.inK.2 v⟩,
    ⟨by rw [aval.2]; exact hM.val.1, fun v => by rw [aval.1]; exact hM.val.2 v⟩,
    hB, by rw [akp.2]; exact hM.kpL, fun v hv => by rw [akp.1]; exact hM.kp v hv,
    by rw [R "fp.k" (by simp [myRepRegs])]; exact hM.kreg, hM.Knd, hM.HK⟩

theorem FInv.congr_tr {ι ι' : IState G s} (h : FInv c ι) (ht : ι'.trees = ι.trees)
    (htv : ι'.tv = ι.tv) : FInv c ι' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨ht ▸ h1, ht ▸ h2, fun v => by rw [htv, ht]; exact h3 v, ht ▸ h4⟩

/-- The invocation representation survives a write to an invocation register `r`. -/
theorem IRep.frame_reg (hNI : NamesI LI X TI slB slX sA) {ι : IState G s} {g : LI.Gh}
    {st st' : State V} {r : String} (h : IRep LI TI c slB slX ι g st)
    (hu : Unchanged st st' [] [] [r] []) (hr : r ∈ invRegs) (hrmy : r ∉ myRepRegs)
    (hrW : r ∉ ["fp.wl", "fp.ob"]) (hrQ : r ∉ ["fp.ql", "fp.ob"]) (hc : st.cost ≤ st'.cost) :
    IRep LI TI c slB slX ι g st' := by
  have hB : Disj [r] (LI.slWR slB) :=
    Disj.singleton (hNI.invR_slB r (by simp only [List.mem_append]; left; left; exact hr))
  have hX : Disj [r] (LI.slWR slX) :=
    Disj.singleton (hNI.invR_slX r (by simp only [List.mem_append]; left; left; exact hr))
  have hfr : Disj [r] TI.frWR :=
    Disj.singleton (hNI.namesT.fr_invR r (by simp only [List.mem_append]; left; exact hr))
  exact ⟨h.lab.frame hu (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _)
      hB (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _) hX (Disj.nil_left _) hc,
    h.my.frameR hu (Disj.nil_left _) (Disj.singleton hrmy), h.out.frameR hu (Disj.nil_left _),
    TI.FR_frame h.fr hu (Disj.nil_left _) (Disj.nil_left _) hfr (Disj.nil_left _),
    h.W.frame hu (Disj.nil_left _) (Disj.singleton hrW),
    h.Q.frame hu (Disj.nil_left _) (Disj.singleton hrQ)⟩

theorem invWRegs_sub : invWRegs ⊆ invWR LI X TI := by
  intro x hx; simp only [invWR, List.mem_append]; tauto

/-- The last statement of a root: `j := j + 1`, closing the iteration. -/
theorem root_finish (hNI : NamesI LI X TI slB slX sA) {ι₀ ι' : IState G s} {g₀ g' : LI.Gh}
    {st₀ st₁ : State V} {j n' : ℕ}
    (hR : IRep LI TI c slB slX ι' g' st₁) (hjr : st₁.w "fp.j" = j) (hj : j < SL.length)
    (hwalk : WalkInv ι'.d) (hle : ∀ v, ι'.d v ≤ d0 v) (hfinv : FInv c ι')
    (hQsub : ∀ q ∈ ι'.Q, q ∈ SL.take (j + 1)) (hhist : LI.gext g₀ g')
    (hcont : ∀ ι'' n'', Invoke c ι' (SL.drop (j + 1)) ι'' n'' → Invoke c ι₀ SL ι'' (n' + n''))
    (hu : Unchanged st₀ st₁ (invWA LI TI sA) (invVA LI TI) (invWR LI X TI) (invVR LI X TI))
    (hc0 : st₀.cost ≤ st₁.cost) (hc : st₁.cost + 1 ≤ st₀.cost + TI.Cinit + 4 + KI LI X TI * n')
    (hcapJ : j + 1 < st₁.cap) :
    Runs ops (wset "fp.j" (add (var "fp.j") (lit 1))) st₁ (fun st' => ∃ m', m' < SL.length - j ∧
      ILoopI LI X TI c slB slX sA SL d0 ι₀ g₀ st₀ m' st') := by
  refine runs_wset (a := j + 1) (evalW_add_of (by simp [hjr]) (evalW_lit_of (by omega)) hcapJ) ?_
  have hu1 : Unchanged st₁ ((st₁.setW "fp.j" (j + 1)).charge 1) [] [] ["fp.j"] [] :=
    ((unch_setW st₁ "fp.j" _).cat (unch_charge' _ 1)).mono (by simp) (by simp) (by simp) (by simp)
  refine ⟨SL.length - (j + 1), by omega, ι', j + 1, n', g', rfl,
    ⟨hR.frame_reg hNI hu1 (by simp [invRegs]) (by decide) (by decide) (by decide) (by simp),
      by simp, by omega, hwalk, hle, hfinv, hQsub, hhist, hcont, ⟨?_, by simp; omega,
      by simp; omega⟩⟩⟩
  exact hu.trans (hu1.mono (by simp) (by simp)
    (fun x hx => invWRegs_sub (by simp at hx; subst hx; simp [invWRegs])) (by simp))

/-- Every search outcome of a root extends to an invocation outcome of the remaining roots. -/
theorem search_extends (hown : OutOK c) (hsort : OutSorted c) {S : Finset (Fin G.n)}
    (hpre : CallPre c.B S d0) {ι : IState G s} {x : Fin G.n} {L : List (Fin G.n)}
    (hLS : ∀ y ∈ L, y ∈ S) (hwalk : WalkInv ι.d) (hle : ∀ v, ι.d v ≤ d0 v)
    (hxT : x ∉ ι.tv) (hxtop : ι.d x ≠ ⊤) {σ'' : SSt G s} {res : SearchRes} {n'' : ℕ}
    (hs : Search c ι.tv (initSt ι.d ι.D x) σ'' res n'') :
    ∃ ι₃ N, Invoke c ι (x :: L) ι₃ N ∧ n'' + 2 ≤ N := by
  obtain ⟨hI', hle', -⟩ := Search.inv hown hsort hs (initSt_inv hwalk hxtop)
    (fun w hw => absurd hw (Finset.notMem_empty w))
  have hw'' : WalkInv σ''.d := hI'.walk
  have hle'' : ∀ v, σ''.d v ≤ d0 v := fun v => (hle' v).trans (hle v)
  by_cases hres : res = .failed
  · subst hres
    obtain ⟨ι₃, n₃, h₃⟩ := Invoke.exists_run hown hsort hpre L
      { ι with d := σ''.d, D := σ''.D, W := ι.W ∪ σ''.val, Q := insert x ι.Q } hLS hw'' hle''
    exact ⟨ι₃, n'' + n₃ + σ''.K.length + 2, Invoke.fail ι ι₃ x L σ'' n'' n₃ hxT hs h₃, by omega⟩
  · obtain ⟨ι₃, n₃, h₃⟩ := Invoke.exists_run hown hsort hpre L
      { ι with d := σ''.d, D := σ''.D, tv := ι.tv ∪ σ''.K.toFinset,
               trees := growForest res ι.trees x σ'' } hLS hw'' hle''
    exact ⟨ι₃, n'' + n₃ + σ''.K.length + 2, Invoke.grow ι ι₃ x L σ'' res n'' n₃ hxT hres hs h₃,
      by omega⟩

end Frontier.CHD.BL2
