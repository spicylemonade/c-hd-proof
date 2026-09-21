import Frontier.CHD.RamBody

/-!
# Frontier.CHD.RamBodyA — Layer-A glue for the level body (owner: agent-01)

**NON-GATE** (B-L4, the spine's level body).  The Layer-A facts that the RAM proof of the level
body (`RamBodySpec`) needs about one concrete call `CallD` at level `l + 1`:
* `aloop_init`: the loop invariant `ALoop` at the initial configuration (BM.5–8), as in
  `callD_sim`;
* `callD_mk`: a `BMSSPD (l+1)` outcome from its parts, with its explicit log;
* `callD_ext_loop` / `callD_ext_fp`: every partial outcome (FindPivots outcome, loop outcome)
  extends to a full outcome — the source of the phase budgets;
* `loopD_stop_of`, `loopD_card_le`: the final loop state passes the stop test, `|U'| ≤ |U| + cl`;
* `bodyA_fold_d`: the relaxations never change a complete label.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamBody

open Frontier Frontier.CHD Frontier.CHD.BM Frontier.CHD.RamSpine

variable {G : Graph} {s : Fin G.n}

/-! ## Loop facts -/

section loopfacts

variable {Φ Ω : Type} {p : ℕ} {ops : DOps G s} {T : ℕ} {sub : SubRelD G s Φ Ω} {B : WLab G s}
  {τ : ℕ}

/-- The final state of a loop run passes the stop test. -/
theorem loopD_stop_of {i : ℕ} {cs cs' : CSt G s p} {φ φ' : Φ} {lg : Log G s Ω}
    {J : Finset (Fin G.m)} {cm c : ℕ} (h : LoopD G s ops T sub B τ i cs φ cs' φ' lg J cm c) :
    τ < cs'.U.card ∨ (cs'.g.view cs'.Dc).IsEmpty := by
  induction h with
  | stop i cs φ hs => exact hs
  | step i cs cs' φ φ1 φ' ks Bi g1 Dc1 cp B'i Ui Dci d1' g2 lUi L' piv' lres lg lg' J' cm c
      hcard hne hpull hsubD hlUnd hlU hnd hmem hres hlresnd hlres _ ih => exact ih

/-- The returned set grows by at most the loop's own cost. -/
theorem loopD_card_le {i : ℕ} {cs cs' : CSt G s p} {φ φ' : Φ} {lg : Log G s Ω}
    {J : Finset (Fin G.m)} {cm c : ℕ} (h : LoopD G s ops T sub B τ i cs φ cs' φ' lg J cm c) :
    cs'.U.card ≤ cs.U.card + c := by
  induction h with
  | stop i cs φ hs => omega
  | step i cs cs' φ φ1 φ' ks Bi g1 Dc1 cp B'i Ui Dci d1' g2 lUi L' piv' lres lg lg' J' cm c
      hcard hne hpull hsubD hlUnd hlU hnd hmem hres hlresnd hlres _ ih =>
    have hU : (nextD ops T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).U = cs.U ∪ Ui := rfl
    rw [hU] at ih
    have h1 : (cs.U ∪ Ui).card ≤ cs.U.card + Ui.card := Finset.card_union_le _ _
    have h2 : Ui.card ≤ iterCostD ops T B cs ks.toFinset cp Bi Ui Dc1 Dci d1' g2 lUi L' lres := by
      unfold iterCostD; omega
    omega

end loopfacts

/-! ## Relaxations keep complete labels -/

section relax

variable {T : ℕ} {B : WLab G s} {lo : Option (WLab G s)}

open Classical in
theorem bodyA_relax_d (st : RSt G s) (e : Fin G.m) :
    (relaxInsCc (dlOps G s) T B lo st e).d = if ValidRelax G s st.d B e then
      Function.update st.d (G.dst e) (ext (st.d (G.src e)) e) else st.d := by
  unfold relaxInsCc
  by_cases hv : ValidRelax G s st.d B e
  · rw [if_pos hv, if_pos hv]
    cases lo with
    | none => rfl
    | some b => by_cases hb : b ≤ ext (st.d (G.src e)) e <;> simp [hb]
  · rw [if_neg hv, if_neg hv]

open Classical in
/-- One relaxation keeps walk labels and never changes a complete label. -/
theorem bodyA_relax_complete (st : RSt G s) (hw : WalkInv st.d) (e : Fin G.m) :
    WalkInv (relaxInsCc (dlOps G s) T B lo st e).d ∧
      ∀ u, st.d u = dis (s := s) u → (relaxInsCc (dlOps G s) T B lo st e).d u = st.d u := by
  rw [bodyA_relax_d]
  by_cases hv : ValidRelax G s st.d B e
  · rw [if_pos hv]
    refine ⟨walkInv_update hw, fun u hu => ?_⟩
    by_cases hue : u = G.dst e
    · subst hue
      rw [Function.update_self]
      exact le_antisymm hv.1 (by rw [hu]; exact dis_le_ext hw e)
    · rw [Function.update_of_ne hue]
  · rw [if_neg hv]; exact ⟨hw, fun u _ => rfl⟩

/-- **Relaxations never change a complete label** (along a fold). -/
theorem bodyA_fold_d : ∀ (L : List (Fin G.m)) (st : RSt G s), WalkInv st.d →
    ∀ u, st.d u = dis (s := s) u →
      (L.foldl (relaxInsCc (dlOps G s) T B lo) st).d u = st.d u
  | [], _, _, _, _ => rfl
  | e :: L, st, hw, u, hu => by
    obtain ⟨hw1, hd1⟩ := bodyA_relax_complete (T := T) (B := B) (lo := lo) st hw e
    show (L.foldl (relaxInsCc (dlOps G s) T B lo) (relaxInsCc (dlOps G s) T B lo st e)).d u = st.d u
    rw [bodyA_fold_d L _ hw1 u (by rw [hd1 u hu]; exact hu), hd1 u hu]

end relax

/-! ## The initial loop configuration -/

section init

variable {Φ : Type} {p : ℕ}

/-- The initial concrete loop state of `CallD` (BM.5–8). -/
noncomputable def cs0 (T M : ℕ) (B : WLab G s) (d1 : Labels G s) (P : Fin p → Finset (Fin G.n))
    (piv : Fin p → Fin G.n) (lpiv : List (Fin G.n)) (g0 : DGl G s) : CSt G s p :=
  { d := d1, P := P, piv := piv, U := ∅, B' := initB' B d1 piv,
    g := (initD (dlOps G s) T M B d1 lpiv g0).1, Dc := (initD (dlOps G s) T M B d1 lpiv g0).2.1 }

/-- **The loop invariant at the initial configuration** (as in `callD_sim`). -/
theorem aloop_init {Inv : Φ → Prop} {Mf : ℕ → ℕ} (hM1 : ∀ l, 1 ≤ Mf l) {T l : ℕ}
    {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {P : Fin p → Finset (Fin G.n)}
    {Q W : Finset (Fin G.n)} {φ1 : Φ} {g0 : DGl G s} {piv : Fin p → Fin G.n}
    {lpiv : List (Fin G.n)}
    (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P Q W) (hI1 : Inv φ1)
    (hpiv : ∀ j, piv j ∈ P j ∧ ∀ x ∈ P j, d1 (piv j) ≤ d1 x)
    (hlp : lpiv.toFinset = Finset.univ.image piv)
    (hK : DB.KeyInj g0.L (kof G s)) (hab : ∀ v i a, g0.L v = some (i, a) → B ≤ a) :
    ALoop (dlOps G s) Inv Mf l B S d0 d1 P (initB' B d1 piv) g0.fresh g0.L
      (⟨0, cs0 T (Mf (l + 1)) B d1 P piv lpiv g0, φ1⟩ : LoopCfgD G s Φ p) := by
  obtain ⟨hSnew, hvnew⟩ := new_sim (ops := dlOps G s) (g := g0) (M := Mf (l + 1)) (B := B) (hM1 _) hab
  have hlp' : ∀ y ∈ lpiv, d1 y < B ∧ kof G s (d1 y) = y := by
    intro y hy
    have hy' : y ∈ Finset.univ.image piv := by rw [← hlp]; exact List.mem_toFinset.mpr hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy'
    have hS : piv j ∈ S := (hfp.groups j).2 (hpiv j).1
    have hlt : d1 (piv j) < B := lt_of_le_of_lt (hfp.le _) (hpre.inRange _ hS)
    exact ⟨hlt, kof_of_walk hfp.walk (BM.ne_top_of_lt hlt)⟩
  obtain ⟨hvi, hSi, hKi, -, hCCi, hTi⟩ :=
    insMany_sim (ops := dlOps G s) (T := T) d1 lpiv g0 (newC (Mf (l + 1)) B) hSnew hK hlp'
  have hcs : (cs0 T (Mf (l + 1)) B d1 P piv lpiv g0).lit = initState B d1 P piv := by
    show
      ({ d := d1, D := (insManyC (dlOps G s) T d1 lpiv g0 (newC (Mf (l + 1)) B)).1.view
           (insManyC (dlOps G s) T d1 lpiv g0 (newC (Mf (l + 1)) B)).2.1,
         P := P, piv := piv, U := ∅, B' := initB' B d1 piv } : LState G s p) = _
    rw [hvi, hvnew, hlp]; rfl
  have h0 := linv_init hpre hfp hpiv
  rw [← hcs] at h0
  refine ⟨h0, hI1, hSi, ?_, hKi, hCCi, ?_⟩
  · show (insManyC (dlOps G s) T d1 lpiv g0 (newC (Mf (l + 1)) B)).2.1.M = _
    rw [insManyC_M]; rfl
  · intro y hy
    have hyl := hTi y hy
    right
    refine ⟨d1 y, ?_, hfp.le y⟩
    show (insManyC (dlOps G s) T d1 lpiv g0 (newC (Mf (l + 1)) B)).1.view
      (insManyC (dlOps G s) T d1 lpiv g0 (newC (Mf (l + 1)) B)).2.1 y = some (d1 y)
    rw [hvi, hvnew, insertMany_apply, if_pos (List.mem_toFinset.mpr hyl)]
    rfl

/-- Pivots exist (argmins of the nonempty groups). -/
theorem exists_piv {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s}
    {P : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} (hfp : FPContract B S d0 d1 p P Q W) :
    ∃ (piv : Fin p → Fin G.n) (lpiv : List (Fin G.n)),
      (∀ j, piv j ∈ P j ∧ ∀ x ∈ P j, d1 (piv j) ≤ d1 x) ∧ lpiv.Nodup ∧
        lpiv.toFinset = Finset.univ.image piv := by
  classical
  have hpiv0 : ∀ j, ∃ x, x ∈ P j ∧ ∀ y ∈ P j, d1 x ≤ d1 y := fun j =>
    Finset.exists_min_image (P j) d1 (hfp.groups j).1
  choose piv hpiv using hpiv0
  exact ⟨piv, (Finset.univ.image piv).toList, hpiv, Finset.nodup_toList _,
    Finset.toList_toFinset _⟩

end init

/-! ## A call outcome from its parts -/

section mk

variable {Φ Ω : Type} {FPC : FPRelC G s Φ Ω} {DCb : DCost} {T : ℕ → ℕ} {Mf τ : ℕ → ℕ} {l : ℕ}
  {Blow B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} {φ0 : Φ} {g0 : DGl G s}
  {d1 : Labels G s} {p : ℕ} {P : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {φ1 φ2 : Φ}
  {ω : Ω} {cfp : ℕ} {piv : Fin p → Fin G.n} {lpiv : List (Fin G.n)} {cs : CSt G s p}
  {lgc : Log G s Ω} {J : Finset (Fin G.m)} {cm cl : ℕ}

/-- The call record of a `CallD` outcome. -/
noncomputable def recD (T : ℕ → ℕ) (Mf : ℕ → ℕ) (l : ℕ) (Blow B : WLab G s) (S : Finset (Fin G.n))
    (g0 : DGl G s) (d1 : Labels G s) (p : ℕ) (P : Fin p → Finset (Fin G.n)) (Q W : Finset (Fin G.n))
    (ω : Ω) (cfp : ℕ) (lpiv : List (Fin G.n)) (cs : CSt G s p) (J : Finset (Fin G.m)) (cm cl : ℕ)
    (L : List (Fin G.m)) (B'f : WLab G s) (lT6 : List (Fin G.n)) (W' : Finset (Fin G.n))
    (lW' : List (Fin G.n)) : CallRec G s Ω :=
  { lvl := l + 1, Blow := Blow, B := B, S := S, B' := B'f, U := cs.U ∪ W',
    base := false, p := p, Q := Q, W := W, W' := W', J := J, Wr := L.toFinset,
    fp := some ω, cFP := cfp, cMerge := cm,
    cost := cfp + ((initD (dlOps G s) (T (l + 1)) (Mf (l + 1)) B d1 lpiv g0).2.2 + ∑ j, (P j).card + 2 * p)
      + cl + cm
      + (1 + S.card + W.card + W'.card + ∑ j, (P j).card
        + (finD (dlOps G s) (T (l + 1)) B B'f cs.d cs.g cs.Dc lT6 L lW').2.2.2) }

theorem logCost_cons (x : List ℕ × CallRec G s Ω) (lg : Log G s Ω) :
    Log.cost (x :: lg) = x.2.cost + Log.cost lg := by
  simp [Log.cost]

/-- **A `CallD` outcome from its parts.** -/
theorem callD_mk {L : List (Fin G.m)} {B'f : WLab G s} {lT6 : List (Fin G.n)}
    {W' : Finset (Fin G.n)} {lW' : List (Fin G.n)}
    (hfprel : FPC (l + 1) Blow B S d0 φ0 d1 p P Q W φ1 ω cfp)
    (hpiv : ∀ j, piv j ∈ P j ∧ ∀ x ∈ P j, d1 (piv j) ≤ d1 x)
    (hlpnd : lpiv.Nodup) (hlp : lpiv.toFinset = Finset.univ.image piv)
    (hloop : LoopD G s (dlOps G s) (T (l + 1)) (BMSSPD G s (dlOps G s) FPC DCb T Mf τ l) B
      (τ (l + 1)) 0 (cs0 (T (l + 1)) (Mf (l + 1)) B d1 P piv lpiv g0) φ1 cs φ2 lgc J cm cl)
    (hB'e : (cs.g.view cs.Dc).IsEmpty → B'f = B) (hB'n : ¬ (cs.g.view cs.Dc).IsEmpty → B'f = cs.B')
    (hT6nd : lT6.Nodup) (hT6 : ∀ x, x ∈ lT6 ↔ x ∈ S ∧ B'f ≤ cs.d x ∧ cs.d x < B)
    (hW' : ∀ x, x ∈ W' ↔ (x ∈ W ∧ x ∉ cs.U) ∧ cs.d x < B'f)
    (hL : Enumerates G L W') (hlWnd : lW'.Nodup) (hlW : lW'.toFinset = W') :
    BMSSPD G s (dlOps G s) FPC DCb T Mf τ (l + 1) Blow B S d0 φ0 g0
      (B'f, cs.U ∪ W', (finD (dlOps G s) (T (l + 1)) B B'f cs.d cs.g cs.Dc lT6 L lW').2.2.1,
        (finD (dlOps G s) (T (l + 1)) B B'f cs.d cs.g cs.Dc lT6 L lW').1) φ2
      (finD (dlOps G s) (T (l + 1)) B B'f cs.d cs.g cs.Dc lT6 L lW').2.1
      (([], recD T Mf l Blow B S g0 d1 p P Q W ω cfp lpiv cs J cm cl L B'f lT6 W' lW') :: lgc) :=
  ⟨d1, p, P, Q, W, φ1, ω, cfp, piv, lpiv, cs, lgc, J, cm, cl, L, B'f, lT6, W', lW', hfprel, hpiv,
    hlpnd, hlp, hloop, hB'e, hB'n, hT6nd, hT6, hW', hL, hlWnd, hlW, rfl, rfl, rfl⟩

/-- **Every loop outcome extends to a full call outcome** (canonical finalization). -/
theorem callD_ext_loop
    (hfprel : FPC (l + 1) Blow B S d0 φ0 d1 p P Q W φ1 ω cfp)
    (hpiv : ∀ j, piv j ∈ P j ∧ ∀ x ∈ P j, d1 (piv j) ≤ d1 x)
    (hlpnd : lpiv.Nodup) (hlp : lpiv.toFinset = Finset.univ.image piv)
    (hloop : LoopD G s (dlOps G s) (T (l + 1)) (BMSSPD G s (dlOps G s) FPC DCb T Mf τ l) B
      (τ (l + 1)) 0 (cs0 (T (l + 1)) (Mf (l + 1)) B d1 P piv lpiv g0) φ1 cs φ2 lgc J cm cl) :
    ∃ res gE lg, BMSSPD G s (dlOps G s) FPC DCb T Mf τ (l + 1) Blow B S d0 φ0 g0 res φ2 gE lg ∧
      cfp + (initD (dlOps G s) (T (l + 1)) (Mf (l + 1)) B d1 lpiv g0).2.2 + (∑ j, (P j).card) + 2 * p
        + cl + cm + 1 + S.card + W.card + lgc.cost ≤ Log.cost lg := by
  classical
  set B'f : WLab G s := if (cs.g.view cs.Dc).IsEmpty then B else cs.B' with hB'fdef
  have hB'e : (cs.g.view cs.Dc).IsEmpty → B'f = B := fun he => by rw [hB'fdef, if_pos he]
  have hB'n : ¬ (cs.g.view cs.Dc).IsEmpty → B'f = cs.B' := fun he => by rw [hB'fdef, if_neg he]
  set lT6 := (S.filter fun x => B'f ≤ cs.d x ∧ cs.d x < B).toList with hlT6def
  have hT6nd : lT6.Nodup := Finset.nodup_toList _
  have hT6 : ∀ x, x ∈ lT6 ↔ x ∈ S ∧ B'f ≤ cs.d x ∧ cs.d x < B := by
    intro x; rw [hlT6def, Finset.mem_toList, Finset.mem_filter]
  set W' := W.filter fun x => x ∉ cs.U ∧ cs.d x < B'f with hW'def
  have hW' : ∀ x, x ∈ W' ↔ (x ∈ W ∧ x ∉ cs.U) ∧ cs.d x < B'f := by
    intro x; rw [hW'def, Finset.mem_filter, and_assoc]
  set L := (Finset.univ.filter fun e => G.src e ∈ W').toList with hLdef
  have hL : Enumerates G L W' := ⟨Finset.nodup_toList _, by intro e; simp [hLdef]⟩
  set lW' := W'.toList with hlW'def
  have hlWnd : lW'.Nodup := Finset.nodup_toList _
  have hlW : lW'.toFinset = W' := Finset.toList_toFinset _
  refine ⟨_, _, _, callD_mk hfprel hpiv hlpnd hlp hloop hB'e hB'n hT6nd hT6 hW' hL hlWnd hlW, ?_⟩
  rw [logCost_cons]
  simp only [recD]
  omega

variable (FPC DCb T Mf τ) in
/-- The level-`l` package of Layer-A facts used by `loopD_total` (from the global hypotheses). -/
theorem levelPkg {Inv : Φ → Prop} (hFPC : FPCSound G s FPC Inv) (hFPCt : FPCTotal G s FPC Inv)
    (hτ : ∀ l, 1 ≤ τ l) (hMf : ∀ l, (dlOps G s).mergeM (Mf (l + 1)) (Mf l)) (hM1 : ∀ l, 1 ≤ Mf l)
    (l : ℕ) :
    ∃ (DC : DCost) (subC : SubRelC G s Φ Ω),
      SimSub G s (dlOps G s) τ Inv Mf l (BMSSPD G s (dlOps G s) FPC DCb T Mf τ l) subC ∧
      GoodSub G s τ Inv l subC ∧ DC.M (l + 1) = Mf (l + 1) ∧
      TotalSub G s Inv (BMSSPD G s (dlOps G s) FPC DCb T Mf τ l) := by
  let DC0 : DCost := ⟨Mf, fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, 0, 0⟩
  exact ⟨DC0, BMSSPC G s FPC DC0 τ l,
    bmsspD_sim (DC := DC0) (DCb := DCb) (T := T) hFPC τ hMf hM1 (fun _ => rfl) l,
    bmsspC_log hFPC τ l, rfl, bmsspD_total hFPC hFPCt τ hτ hMf hM1 l⟩

/-- **Every FindPivots outcome, with any pivots, extends to a full call outcome** (loop totality +
canonical finalization). -/
theorem callD_ext_fp {Inv : Φ → Prop} (hFPC : FPCSound G s FPC Inv) (hFPCt : FPCTotal G s FPC Inv)
    (hτ : ∀ l, 1 ≤ τ l) (hMf : ∀ l, (dlOps G s).mergeM (Mf (l + 1)) (Mf l)) (hM1 : ∀ l, 1 ≤ Mf l)
    (hpre : CallPre B S d0) (hI : Inv φ0) (hlow : ∀ x ∈ S, Blow ≤ dis (s := s) x)
    (hK : DB.KeyInj g0.L (kof G s)) (hab : ∀ v i a, g0.L v = some (i, a) → B ≤ a)
    (hfprel : FPC (l + 1) Blow B S d0 φ0 d1 p P Q W φ1 ω cfp)
    (hpiv : ∀ j, piv j ∈ P j ∧ ∀ x ∈ P j, d1 (piv j) ≤ d1 x)
    (hlpnd : lpiv.Nodup) (hlp : lpiv.toFinset = Finset.univ.image piv) :
    ∃ res φ2 gE lg, BMSSPD G s (dlOps G s) FPC DCb T Mf τ (l + 1) Blow B S d0 φ0 g0 res φ2 gE lg ∧
      cfp + (initD (dlOps G s) (T (l + 1)) (Mf (l + 1)) B d1 lpiv g0).2.2 + (∑ j, (P j).card) + 2 * p
        + 1 + S.card + W.card ≤ Log.cost lg := by
  have hlow' : ∀ x ∈ S, Blow ≤ d0 x := fun x hx => (hlow x hx).trans (hpre.walk.sound x)
  obtain ⟨hfp, hI1⟩ := hFPC _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpre hI hlow' hfprel
  obtain ⟨DC, subC, hsimsub, hsubC, hDC, hsubT⟩ := levelPkg FPC DCb T Mf τ hFPC hFPCt hτ hMf hM1 l
  have hA := aloop_init (Inv := Inv) (Mf := Mf) (T := T (l + 1)) (l := l) hM1 hpre hfp hI1 hpiv hlp hK hab
  obtain ⟨cs, φ2, lgc, J, cm, cl, hloop⟩ :=
    loopD_total (T := T (l + 1)) (DC := DC) (g0 := g0) (τl := τ (l + 1)) hpre hfp hMf hsimsub hsubC hDC
      (hτ l) hsubT (τ (l + 1) + 1) 0 (cs0 (T (l + 1)) (Mf (l + 1)) B d1 P piv lpiv g0) φ1
      (by simp [cs0]) hA.linv hA.inv hA.sinv hA.M hA.kinj hA.chg hA.touch
  obtain ⟨res, gE, lg, hrel, hc⟩ := callD_ext_loop (Mf := Mf) hfprel hpiv hlpnd hlp hloop
  exact ⟨res, φ2, gE, lg, hrel, by omega⟩

end mk

/-! ## Completeness of `W'` at the end of the loop -/

section wcomplete

variable {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {p : ℕ}
  {P0 : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)}

/-- **The vertices of `W'` are complete** (as in `BM.final_post`): at the end of the loop, a
vertex of `W` outside `U` with label below `B'f` has its final distance. -/
theorem wp_complete (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W)
    {piv : Fin p → Fin G.n} {σ : LState G s p} (h : LInv G s B S d0 d1 P0 (initB' B d1 piv) σ)
    {B'f : WLab G s} (hB'e : σ.D.IsEmpty → B'f = B) (hB'n : ¬ σ.D.IsEmpty → B'f = σ.B')
    {x : Fin G.n} (hxW : x ∈ W) (hxU : x ∉ σ.U) (hxlt : σ.d x < B'f) : Complete σ.d x := by
  have hB'fge : σ.B' ≤ B'f := by
    by_cases he : σ.D.IsEmpty
    · rw [hB'e he]; exact h.B'_le
    · rw [hB'n he]
  have hE : ∀ v ∈ Aset G s B S d1 P0, dis (s := s) v < B'f → v ∈ σ.U := by
    intro v hvA hvlt
    by_cases he : σ.D.IsEmpty
    · by_contra hvU
      obtain ⟨y, ⟨-, hc⟩, -⟩ := h.certified v hvA hvU
      rcases hc with hk | ⟨j, -, k, hk, -⟩
      · rw [he y] at hk; exact absurd hk (by simp)
      · rw [he _] at hk; exact absurd hk (by simp)
    · rw [hB'n he] at hvlt; exact h.A_below v hvA hvlt
  have hxUK := hfp.region hxW
  by_cases hxA : x ∈ Aset G s B S d1 P0
  · exact absurd (hE x hxA (lt_of_le_of_lt (h.walk.sound x) hxlt)) hxU
  · obtain ⟨-, hvc⟩ := Wc_complete hfp hxUK hxA
    exact complete_of_le hvc (h.mono x) h.walk.sound

end wcomplete

end Frontier.CHD.RamBody
