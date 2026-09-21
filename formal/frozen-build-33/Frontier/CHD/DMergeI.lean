import Frontier.CHD.DLayerInst
import Frontier.CHD.DRekey

/-!
# DMergeI — BM.14: the merge operation of the D layer (B-L3, agent-02, NON-GATE)

`dsMerge` merges the child structure (level `lo`, the deepest active level) into its parent
(level `lo + 1`) on agent-04's representation `DRI`:
1. `mmSetup`: parent base / sizes / group size `M/3` into `mg.*`;
2. `mmKeep`: the keep bit `ltSep D'.Bd (nextSep rest D.Bd)` of `DB.merge` — under the merge
   premises it is `1` when the parent has at least two blocks (its second separator is above the
   child's bound), and otherwise the comparison of the two bounds (`dsl.b*[lo]` vs `dsl.b*[lo+1]`);
3. `mmRekey`: re-key the parent's front block at the child's bound (DRekey) or drop it;
4. `mergeS` (DGlobal.mergeDL): group the child's blocks in place onto the parent's slice;
5. `mmSplice`: the child's live-key list joins the parent's (KeyLists.klSplice).

Main theorem `dsMerge_spec`: `DRI P st H g Ds lo → … → DRI P r H g (update Ds (lo+1) (DB.merge 1
(Ds (lo+1)) (Ds lo)).1) (lo+1)`, cost `≤ 17 · ((DB.merge 1 …).2 + 1)`, the use counters unchanged,
syntactic frame.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.DLI

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.DB Frontier.CHD.DIns
  Frontier.CHD.DList Frontier.CHD.DGlob Frontier.CHD.MLab Frontier.CHD.LabTab Frontier.CHD.BM
open Frontier.RAM.WExpr Frontier.RAM.Stmt

variable {G : Graph} {s : Fin G.n}

/-! ## The text -/

/-- the child's bound (scratch block) -/
def mmX : LReg := ⟨"mm.xl", "mm.xh", "mm.xv", "mm.xe", "mm.xr"⟩
/-- the parent's bound (scratch block) -/
def mmK : LReg := ⟨"mm.kl", "mm.kh", "mm.kv", "mm.ke", "mm.kr"⟩

/-- `mm.c := lvl - 1`; `mg.lv := lvl`; parent base/size, child size, group size `M/3` -/
def mmSetup : Stmt :=
  seq (wset "mm.c" (sub (var "lvl") (lit 1)))
  (seq (wset "mg.lv" (var "lvl"))
  (seq (wset "mg.pb" (load "dsl.base" (var "lvl")))
  (seq (wset "mg.pk" (load "dsl.sz" (var "lvl")))
  (seq (wset "mg.ck" (load "dsl.sz" (var "mm.c")))
       (wset "mg.g" (div (load "dsl.M" (var "lvl")) (lit 3)))))))

/-- the keep bit `mm.k` (child bound `⊤`: drop; parent with `≥ 2` blocks: keep; else `D'.Bd < D.Bd`) -/
def mmKeep : Stmt :=
  ite (eq (load "dsl.bf" (var "mm.c")) (lit 0)) (wset "mm.k" (lit 0))
    (seq (loadA bdA "mm.c" mmX)
      (ite (lt (lit 1) (var "mg.pk")) (wset "mm.k" (lit 1))
        (ite (eq (load "dsl.bf" (var "mg.lv")) (lit 0)) (wset "mm.k" (lit 1))
          (seq (loadA bdA "mg.lv" mmK) (LabRAM.cmp mmX mmK "mm.c1" "mm.c2" "mm.k")))))

/-- re-key the parent's front block at the child's bound, or drop it -/
def mmRekey : Stmt :=
  ite (var "mm.k")
    (seq (wset "rk.pb" (var "mg.pb")) (seq (wset "rk.pk" (var "mg.pk"))
      (seq (rekeyS mmX) (wset "mg.drop" (lit 0)))))
    (wset "mg.drop" (lit 1))

/-- the child's live-key list joins the parent's -/
def mmSplice : Stmt :=
  seq (wset "kl.c" (add (var "n") (var "mm.c")))
  (seq (wset "kl.s" (add (var "n") (var "lvl"))) KL.klSplice)

/-- **BM.14**: merge the child (level `lvl - 1`) into the parent (level `lvl`) -/
def dsMerge : Stmt := seq mmSetup (seq mmKeep (seq mmRekey (seq mergeS mmSplice)))

theorem mmSetup_noalloc : NoAlloc mmSetup := by simp [NoAlloc, mmSetup]
theorem mmKeep_noalloc : NoAlloc mmKeep := by simp [NoAlloc, mmKeep, loadA, LabRAM.cmp, LabRAM.cmpW]
theorem mmRekey_noalloc : NoAlloc mmRekey := by
  simp only [NoAlloc, mmRekey]; exact ⟨⟨trivial, trivial, rekeyS_noalloc mmX, trivial⟩, trivial⟩
theorem mmSplice_noalloc : NoAlloc mmSplice := by simp [NoAlloc, mmSplice, KL.klSplice]
theorem klSplice_noalloc : NoAlloc KL.klSplice := by simp [NoAlloc, KL.klSplice]

theorem dsMerge_noalloc : NoAlloc dsMerge :=
  ⟨mmSetup_noalloc, mmKeep_noalloc, mmRekey_noalloc, mergeS_noalloc, mmSplice_noalloc⟩

/-! ## Small facts -/

theorem nodup_length_le {l : List ℕ} {n : ℕ} (hnd : l.Nodup) (hlt : ∀ x ∈ l, x < n) :
    l.length ≤ n := by
  calc l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ (Finset.range n).card := Finset.card_le_card (fun x hx => by
        simp only [List.mem_toFinset] at hx; simp only [Finset.mem_range]; exact hlt x hx)
    _ = n := Finset.card_range _

/-! ## 1. Set-up -/

theorem mmSetup_spec {ops : VOps ℝ≥0} (P : DPar) (st : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m))
    (g : DGl G s) (Ds : ℕ → DStrM G s) (lo : ℕ) (hD : DRI P st H g Ds lo) (hl : st.w "lvl" = lo + 1)
    (htop : lo + 1 ≤ P.top) :
    Runs ops mmSetup st (fun r => r.w "mm.c" = lo ∧ r.w "mg.lv" = lo + 1 ∧
      r.w "mg.pb" = base st (lo + 1) ∧ r.w "mg.pk" = (Ds (lo + 1)).blocks.length ∧
      r.w "mg.ck" = (Ds lo).blocks.length ∧ r.w "mg.g" = (Ds (lo + 1)).M / 3 ∧
      Unchanged st r [] [] ["mm.c", "mg.lv", "mg.pb", "mg.pk", "mg.ck", "mg.g"] [] ∧
      r.wlen = st.wlen ∧ r.vlen = st.vlen ∧ r.cost = st.cost + 6) := by
  have hc := hD.lens.cap
  have dl := hD.dl
  have hk : 1 ≤ P.top - lo := by omega
  have hbl : lo + 1 < st.wlen "dsl.base" := by have := dl.basel; omega
  have hD1 : DRep st H (vc st) P.bcap (lo + 1) (base st (lo + 1)) (Ds (lo + 1)) := dl.drep 1 hk
  have hD0 : DRep st H (vc st) P.bcap lo (base st lo) (Ds lo) := by
    have := dl.drep 0 (by omega); simpa using this
  have hM : lo + 1 < st.wlen "dsl.M" := by have := hD.lens.M; omega
  have h1c : 1 < st.cap := by omega
  have h3c : 3 < st.cap := by omega
  refine runs_seq (runs_wset (a := lo) (by simp [hl, fit, h1c]) ?_)
  set q1 := (st.setW "mm.c" lo).charge 1 with hq1
  refine runs_seq (runs_wset (a := lo + 1) (by simp [hq1, hl]) ?_)
  set q2 := (q1.setW "mg.lv" (lo + 1)).charge 1 with hq2
  refine runs_seq (runs_wset (a := base st (lo + 1)) (by
    simp [hq2, hq1, hl, hbl]; rfl) ?_)
  set q3 := (q2.setW "mg.pb" (base st (lo + 1))).charge 1 with hq3
  refine runs_seq (runs_wset (a := (Ds (lo + 1)).blocks.length) (by
    simp [hq3, hq2, hq1, hl, hD1.szb, hD1.sz]) ?_)
  set q4 := (q3.setW "mg.pk" (Ds (lo + 1)).blocks.length).charge 1 with hq4
  refine runs_seq (runs_wset (a := (Ds lo).blocks.length) (by
    simp [hq4, hq3, hq2, hq1, hD0.szb, hD0.sz]) ?_)
  set q5 := (q4.setW "mg.ck" (Ds lo).blocks.length).charge 1 with hq5
  refine runs_wset (a := (Ds (lo + 1)).M / 3) (by
    simp [hq5, hq4, hq3, hq2, hq1, hl, hM, fit, h3c, hD.mv (lo + 1) (by omega) htop]) ?_
  refine ⟨by simp [hq5, hq4, hq3, hq2, hq1], by simp [hq5, hq4, hq3, hq2, hq1],
    by simp [hq5, hq4, hq3, hq2, hq1], by simp [hq5, hq4, hq3, hq2, hq1],
    by simp [hq5, hq4, hq3, hq2, hq1], by simp [hq5, hq4, hq3, hq2, hq1], ?_, rfl, rfl,
    by simp [hq5, hq4, hq3, hq2, hq1]⟩
  rw [unch_charge, unch_setW (by simp), hq5, unch_charge, unch_setW (by simp), hq4, unch_charge,
    unch_setW (by simp), hq3, unch_charge, unch_setW (by simp), hq2, unch_charge, unch_setW (by simp),
    hq1, unch_charge, unch_setW (by simp)]
  exact Unchanged.refl _ _ _ _ _

/-! ## 2. The keep bit -/

theorem ltSep_top {α : Type*} [LinearOrder α] [OrderTop α] (s' : WithBot α) :
    ltSep (⊤ : α) s' = false := by
  cases s' with
  | bot => rfl
  | coe x => simp [ltSep, not_top_lt]

theorem ltSep_coe {α : Type*} [LinearOrder α] (a x : α) :
    ltSep a (x : WithBot α) = decide (a < x) := rfl

theorem unch_wset1 (st : State ℝ≥0) (x : String) (a : ℕ) :
    Unchanged st (((st.charge 1).setW x a).charge 1) [] [] [x] [] := by
  rw [unch_charge, unch_setW (by simp), unch_charge]; exact Unchanged.refl _ _ _ _ _

theorem unch_wset0 (st : State ℝ≥0) (x : String) (a : ℕ) :
    Unchanged st ((st.setW x a).charge 1) [] [] [x] [] := by
  rw [unch_charge, unch_setW (by simp)]; exact Unchanged.refl _ _ _ _ _

theorem unch_wset2 (st : State ℝ≥0) (x : String) (a : ℕ) :
    Unchanged st ((((st.charge 1).charge 1).setW x a).charge 1) [] [] [x] [] := by
  rw [unch_charge, unch_setW (by simp), unch_charge, unch_charge]; exact Unchanged.refl _ _ _ _ _

theorem mmX_fresh : LoadAFresh "mm.c" mmX := ⟨by decide, by decide⟩
theorem mmK_fresh : LoadAFresh "mg.lv" mmK := ⟨by decide, by decide⟩
theorem mmXK_cmp : CmpFresh mmX mmK "mm.c1" "mm.c2" := ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem evalW_eqz {q : State ℝ≥0} {arr ix : String} {i : ℕ} (hi : q.w ix = i) (hl : i < q.wlen arr)
    (hcap : 1 < q.cap) :
    evalW q (eq (load arr (var ix)) (lit 0)) = some (if q.wa arr i = 0 then 1 else 0) := by
  have h0 : 0 < q.cap := by omega
  by_cases h : q.wa arr i = 0 <;> simp [evalW, hi, hl, fit, h0, hcap, h]

/-- **the keep bit** of `DB.merge`, under the separator premise of the parent's tail -/
theorem mmKeep_spec (q : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (hH : GoodHist (s := s) H V) (lo : ℕ) (D D' : DStrM G s) (f : Block (Fin G.n) (WLab G s))
    (rest : List (Block (Fin G.n) (WLab G s))) (hDb : D.blocks = f :: rest)
    (hb0 : BdHolds q lo H V D'.Bd) (hb1 : BdHolds q (lo + 1) H V D.Bd)
    (hc : q.w "mm.c" = lo) (hlv : q.w "mg.lv" = lo + 1) (hpk : q.w "mg.pk" = D.blocks.length)
    (hin0 : bdA.InB q lo) (hin1 : bdA.InB q (lo + 1))
    (hf0 : lo < q.wlen "dsl.bf") (hf1 : lo + 1 < q.wlen "dsl.bf") (hcap : 1 < q.cap)
    (hMP2 : ∀ b ∈ D.blocks.tail, ((D'.Bd : WLab G s) : WithBot (WLab G s)) < b.sep) :
    Runs realOps mmKeep q (fun r =>
      r.w "mm.k" = (if ltSep D'.Bd (nextSep rest (D.Bd : WithBot (WLab G s))) then 1 else 0) ∧
      (ltSep D'.Bd (nextSep rest (D.Bd : WithBot (WLab G s))) = true →
        ∃ (x : MLabel G) (p : List (Fin G.m)), Holds r mmX x ∧ Rep (s := s) H V x p ∧
          D'.Bd = ((toW p : WalkOrd G s) : WLab G s)) ∧
      r.cost ≤ q.cost + 30) := by
  have hc0 : 0 < q.cap := by omega
  by_cases h0 : q.wa "dsl.bf" lo = 0
  · -- the child's bound is `⊤`: drop
    have hT : D'.Bd = ⊤ := hb0.1.mp h0
    have hk : ltSep D'.Bd (nextSep rest (D.Bd : WithBot (WLab G s))) = false := by
      rw [hT]; exact ltSep_top _
    refine runs_ite_true (x := 1) (by rw [evalW_eqz hc hf0 hcap, if_pos h0]) one_ne_zero ?_
    refine runs_wset (a := 0) (by simp [evalW, fit, hc0]) ?_
    refine ⟨by simp [hk], by simp [hk], by simp⟩
  · have hT : D'.Bd ≠ ⊤ := fun h => h0 (hb0.1.mpr h)
    obtain ⟨p', hp'⟩ : ∃ p' : List (Fin G.m), D'.Bd = ((toW p' : WalkOrd G s) : WLab G s) := by
      obtain ⟨p', hp'⟩ := WithTop.ne_top_iff_exists.mp hT; exact ⟨p', hp'.symm⟩
    obtain ⟨x, hxA, hxp⟩ := hb0.2 p' hp'
    refine runs_ite_false (by rw [evalW_eqz hc hf0 hcap, if_neg h0]) ?_
    refine runs_seq ((wp_sound _ _ _ (loadA_wp bdA "mm.c" mmX mmX_fresh (q.charge 1) lo
      (by simp [hc]) hin0 x hxA)).mono ?_)
    rintro r1 ⟨hX1, hU1, hc1⟩
    have hpk1 : r1.w "mg.pk" = D.blocks.length := by
      rw [hU1.wreg _ (by simp [mmX, LReg.ws])]; simpa using hpk
    have hlv1 : r1.w "mg.lv" = lo + 1 := by
      rw [hU1.wreg _ (by simp [mmX, LReg.ws])]; simpa using hlv
    have hcap1 : 1 < r1.cap := by rw [hU1.cap]; simpa using hcap
    have hc1' : r1.cost = q.cost + 6 := by simp at hc1; omega
    have hne1 : r1.cap ≠ 0 := by omega
    by_cases hlt : 1 < D.blocks.length
    · -- the parent's second separator is above the child's bound: keep
      have hk : ltSep D'.Bd (nextSep rest (D.Bd : WithBot (WLab G s))) = true := by
        obtain ⟨b, rest', rfl⟩ : ∃ b rest', rest = b :: rest' := by
          cases rest with
          | nil => rw [hDb] at hlt; simp at hlt
          | cons b rest' => exact ⟨b, rest', rfl⟩
        have := hMP2 b (by rw [hDb]; simp)
        simp only [nextSep]; exact (ltSep_iff _ _).mpr this
      refine runs_ite_true (x := 1) (by
        simp [evalW, hpk1, hlt, fit, hcap1]) one_ne_zero ?_
      refine runs_wset (a := 1) (by simp [evalW, fit, hcap1]) ?_
      refine ⟨by simp [hk], fun _ => ⟨x, p', ?_, hxp, hp'⟩, by simp; omega⟩
      exact hX1.of_unchanged (unch_wset1 r1 "mm.k" 1) (by simp [mmX, LReg.ws]) (by simp)
    · have hrest : rest = [] := by
        rw [hDb] at hlt; cases rest with
        | nil => rfl
        | cons b rest' => simp at hlt
      subst hrest
      have hns : nextSep ([] : List (Block (Fin G.n) (WLab G s))) (D.Bd : WithBot (WLab G s)) =
          (D.Bd : WithBot (WLab G s)) := rfl
      rw [hns, ltSep_coe]
      refine runs_ite_false (by simp [evalW, hpk1, hlt, fit, hcap1, hne1]) ?_
      by_cases h1 : r1.wa "dsl.bf" (lo + 1) = 0
      · -- the parent's bound is `⊤`
        have hT1 : D.Bd = ⊤ := hb1.1.mp (by
          rw [(hU1.warr "dsl.bf" (by simp)).1] at h1; simpa using h1)
        have hk : decide (D'.Bd < D.Bd) = true := by rw [hT1]; simpa using lt_top_iff_ne_top.mpr hT
        refine runs_ite_true (x := 1) (by
          rw [evalW_eqz (by simpa using hlv1) (by simpa [(hU1.warr "dsl.bf" (by simp)).2] using hf1)
            (by simpa using hcap1)]; simp [h1]) one_ne_zero ?_
        refine runs_wset (a := 1) (by simp [evalW, fit, hcap1]) ?_
        refine ⟨by simp [hk], fun _ => ⟨x, p', ?_, hxp, hp'⟩, by simp; omega⟩
        exact (hX1.of_unchanged (unch_wset2 r1 "mm.k" 1) (by simp [mmX, LReg.ws]) (by simp))
      · have h1' : q.wa "dsl.bf" (lo + 1) ≠ 0 := by
          rw [(hU1.warr "dsl.bf" (by simp)).1] at h1; simpa using h1
        have hT1 : D.Bd ≠ ⊤ := fun h => h1' (hb1.1.mpr h)
        obtain ⟨p'', hp''⟩ : ∃ p'' : List (Fin G.m), D.Bd = ((toW p'' : WalkOrd G s) : WLab G s) := by
          obtain ⟨p'', hp''⟩ := WithTop.ne_top_iff_exists.mp hT1; exact ⟨p'', hp''.symm⟩
        obtain ⟨y, hyA, hyp⟩ := hb1.2 p'' hp''
        refine runs_ite_false (by
          rw [evalW_eqz (by simpa using hlv1) (by simpa [(hU1.warr "dsl.bf" (by simp)).2] using hf1)
            (by simpa using hcap1)]; simp [h1]) ?_
        have hyA1 : AHolds r1 bdA (lo + 1) y := by
          obtain ⟨y1, y2, y3, y4, y5⟩ := hyA
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · rw [(hU1.varr _ (by simp [bdA])).1]; simpa using y1
          · rw [(hU1.warr _ (by simp [bdA])).1]; simpa using y2
          · rw [(hU1.warr _ (by simp [bdA])).1]; simpa using y3
          · rw [(hU1.warr _ (by simp [bdA])).1]; simpa using y4
          · rw [(hU1.warr _ (by simp [bdA])).1]; simpa using y5
        have hin1' : bdA.InB r1 (lo + 1) := by
          obtain ⟨i1, i2, i3, i4, i5⟩ := hin1
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · rw [(hU1.varr _ (by simp [bdA])).2]; simpa using i1
          · rw [(hU1.warr _ (by simp [bdA])).2]; simpa using i2
          · rw [(hU1.warr _ (by simp [bdA])).2]; simpa using i3
          · rw [(hU1.warr _ (by simp [bdA])).2]; simpa using i4
          · rw [(hU1.warr _ (by simp [bdA])).2]; simpa using i5
        refine runs_seq ((wp_sound _ _ _ (loadA_wp bdA "mg.lv" mmK mmK_fresh ((r1.charge 1).charge 1)
          (lo + 1) (by simpa using hlv1) hin1' y hyA1)).mono ?_)
        rintro r2 ⟨hK2, hU2, hc2⟩
        have hU2' : Unchanged r1 r2 [] [] mmK.ws [mmK.l] :=
          ⟨hU2.warr, hU2.varr, hU2.wreg, hU2.vreg, hU2.cap, hU2.procs⟩
        have hX2 : Holds r2 mmX x := hX1.of_unchanged hU2' (by simp [mmX, mmK, LReg.ws]) (by simp [mmX, mmK])
        have hcap2 : 1 < r2.cap := by rw [hU2.cap]; simpa using hcap1
        refine (wp_sound _ _ _ (cmp_wp (ops := realOps) (fun a b => rfl) "mm.k" mmXK_cmp r2 hcap2)).mono ?_
        rintro r ⟨hk, hU3, -, hc3⟩
        refine ⟨?_, fun _ => ⟨x, p', hX2.of_unchanged hU3 (by simp [mmX, LReg.ws]) (by simp), hxp, hp'⟩, ?_⟩
        · rw [hk, cbit_eq hX2 hK2, hp', hp'']
          have hiff := lt_iff hH hxp hyp
          by_cases hxy : x.lt y
          · rw [if_pos hxy, if_pos (by simpa using WithTop.coe_lt_coe.mpr (hiff.mp hxy))]
          · rw [if_neg hxy, if_neg (by
              intro h; exact hxy (hiff.mpr (WithTop.coe_lt_coe.mp (by simpa using h))))]
        · simp at hc2; omega

/-! ## 3. Re-key or drop the parent's front block -/

/-- the parent after the re-key decision (`keep`: its front block re-separated at `D'.Bd`) -/
def keepD (D D' : DStrM G s) (f : Block (Fin G.n) (WLab G s))
    (rest : List (Block (Fin G.n) (WLab G s))) (keep : Bool) : DStrM G s :=
  { D with blocks := (if keep then ⟨((D'.Bd : WLab G s) : WithBot (WLab G s)), f.ents⟩ else f) :: rest }

theorem mmRekey_spec (q : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (ecap bcap : ℕ) (L : Live (Fin G.n) (WLab G s)) (fresh : ℕ) (Ds : ℕ → DStrM G s) (lo k : ℕ)
    (hk : 1 ≤ k) (hDL : DLRep q H V ecap bcap L fresh Ds lo k) (f : Block (Fin G.n) (WLab G s))
    (rest : List (Block (Fin G.n) (WLab G s))) (hP : (Ds (lo + 1)).blocks = f :: rest)
    (keep : Bool) (hkw : q.w "mm.k" = if keep then 1 else 0)
    (hX : keep = true → ∃ (x : MLabel G) (p : List (Fin G.m)), Holds q mmX x ∧
      Rep (s := s) H V x p ∧ (Ds lo).Bd = ((toW p : WalkOrd G s) : WLab G s))
    (hpb : q.w "mg.pb" = base q (lo + 1)) (hpk : q.w "mg.pk" = (Ds (lo + 1)).blocks.length)
    (hcap : base q (lo + 1) + (Ds (lo + 1)).blocks.length + 1 < q.cap) :
    Runs realOps mmRekey q (fun r =>
      DLRep r H V ecap bcap L fresh
        (Function.update Ds (lo + 1) (keepD (Ds (lo + 1)) (Ds lo) f rest keep)) lo k ∧
      r.w "mg.drop" = (if keep then 0 else 1) ∧ r.cost ≤ q.cost + 12) := by
  have h1c : 1 < q.cap := by omega
  cases keep with
  | false =>
    have hD : keepD (Ds (lo + 1)) (Ds lo) f rest false = Ds (lo + 1) := by
      unfold keepD; rw [if_neg (by simp), ← hP]
    rw [hD, Function.update_eq_self]
    refine runs_ite_false (by simpa [evalW] using hkw) ?_
    refine runs_wset (a := 1) (by simp [evalW, fit, h1c]) ?_
    refine ⟨DLRep.of_unch hDL (unch_wset1 q "mg.drop" 1) (by simp) (by simp) (by decide),
      by simp, by simp⟩
  | true =>
    obtain ⟨x, p, hXq, hxp, hBd⟩ := hX rfl
    refine runs_ite_true (x := 1) (by simpa [evalW] using hkw) one_ne_zero ?_
    refine runs_seq (runs_wset (a := base q (lo + 1)) (by simp [evalW, hpb]) ?_)
    set q1 := ((q.charge 1).setW "rk.pb" (base q (lo + 1))).charge 1 with hq1
    refine runs_seq (runs_wset (a := (Ds (lo + 1)).blocks.length) (by simp [evalW, hq1, hpk]) ?_)
    set q2 := (q1.setW "rk.pk" (Ds (lo + 1)).blocks.length).charge 1 with hq2
    have hU2 : Unchanged q q2 [] [] ["rk.pb", "rk.pk"] [] := by
      rw [hq2, unch_charge, unch_setW (by simp), hq1, unch_charge, unch_setW (by simp), unch_charge]
      exact Unchanged.refl _ _ _ _ _
    have hDL2 : DLRep q2 H V ecap bcap L fresh Ds lo k :=
      DLRep.of_unch hDL hU2 (by simp) (by simp) (by decide)
    have hb2 : ∀ l, base q2 l = base q l := fun l => by simp [base, hq2, hq1]
    have hX2 : Holds q2 mmX x := hXq.of_unchanged hU2 (by decide) (by simp)
    refine runs_seq ((rekeyDL q2 H V ecap bcap L fresh Ds lo k hk hDL2 f rest hP mmX x p hX2 hxp
      (by decide) (by rw [hb2]; simp [hq2, hq1]) (by simp [hq2]) (by rw [hb2]; simpa [hq2, hq1] using hcap)).mono ?_)
    rintro r3 ⟨hDL3, hU3, hc3⟩
    have hc1' : 1 < r3.cap := by rw [hU3.cap]; simpa [hq2, hq1] using h1c
    refine runs_wset (a := 0) (by simp [evalW, fit, show 0 < r3.cap by omega]) ?_
    refine ⟨?_, by simp, by simp [hc3, hq2, hq1]⟩
    have e : keepD (Ds (lo + 1)) (Ds lo) f rest true =
        { Ds (lo + 1) with blocks := ⟨(((toW p : WalkOrd G s) : WLab G s) : WithBot (WLab G s)), f.ents⟩ :: rest } := by
      unfold keepD; rw [if_pos rfl, hBd]
    rw [e]
    exact DLRep.of_unch hDL3 (unch_wset0 r3 "mg.drop" 0) (by simp) (by simp) (by decide)

/-! ## 4. The merge: representation and live-key lists -/

theorem bdA_inB {P : DPar} {st q : State ℝ≥0} (h : DLens (G := G) P st) (hwl : q.wlen = st.wlen)
    (hvl : q.vlen = st.vlen) {j : ℕ} (hj : j ≤ P.top) : bdA.InB q j := by
  have h1 := h.bl; have h2 := h.bh; have h3 := h.bv; have h4 := h.be; have h5 := h.br
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [bdA, hwl, hvl] <;> omega

/-- the merged parent equals the Layer-A `DB.merge 1` result -/
theorem mergedD_keepD (D D' : DStrM G s) (f : Block (Fin G.n) (WLab G s))
    (rest : List (Block (Fin G.n) (WLab G s))) (hD : D.blocks = f :: rest) :
    mergedD (keepD D D' f rest (ltSep D'.Bd (nextSep rest (D.Bd : WithBot (WLab G s))))) D'
      (ltSep D'.Bd (nextSep rest (D.Bd : WithBot (WLab G s)))) (D.M / 3) = (DB.merge 1 D D').1 :=
  mergedD_eq_merge D D' f rest hD

theorem merge_cost_eq (D D' : DStrM G s) (f : Block (Fin G.n) (WLab G s))
    (rest : List (Block (Fin G.n) (WLab G s))) (hD : D.blocks = f :: rest) :
    (DB.merge 1 D D').2 = D'.blocks.length + 1 * ((groupAux (D.M / 3) none D'.blocks).length + 2) + 2 := by
  unfold DB.merge; rw [hD]

theorem dsMerge_main (P : DPar) (st : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (g : DGl G s)
    (Ds : ℕ → DStrM G s) (lo : ℕ) (hD : DRI P st H g Ds lo) (hl : st.w "lvl" = lo + 1)
    (hn : st.w "n" = G.n) (htop : lo + 1 ≤ P.top) (hH : GoodHist (s := s) H (vc st))
    (hMP1 : ∀ e ∈ DB.liveVals g.L (Ds (lo + 1)).blocks, (Ds lo).Bd ≤ e.val)
    (hMP2 : ∀ b ∈ (Ds (lo + 1)).blocks.tail, (((Ds lo).Bd : WLab G s) : WithBot (WLab G s)) < b.sep)
    (hMP0 : (Ds lo).Bd ≤ (Ds (lo + 1)).Bd) :
    Runs realOps dsMerge st (fun r =>
      DLRep r H (vc st) P.ecap P.bcap g.L g.fresh
        (Function.update Ds (lo + 1) (DB.merge 1 (Ds (lo + 1)) (Ds lo)).1) (lo + 1) (P.top - (lo + 1)) ∧
      (∃ K : ℕ → List ℕ, KL.LL (r.wa "lk.n") (r.wa "lk.p") G.n (lo + 1) P.top K ∧
        ∀ j, lo + 1 ≤ j → j ≤ P.top → ∀ v : Fin G.n, (v : ℕ) ∈ K j ↔
          DB.HasKey g.L (Function.update Ds (lo + 1) (DB.merge 1 (Ds (lo + 1)) (Ds lo)).1 j) v) ∧
      r.cost ≤ st.cost + 17 * ((DB.merge 1 (Ds (lo + 1)) (Ds lo)).2 + 1)) := by
  have hc := hD.lens.cap
  have hLn := hD.lens
  have dl := hD.dl
  have hwf1 := hD.wf (lo + 1) (by omega) htop
  have hwf0 := hD.wf lo le_rfl (by omega)
  obtain ⟨f, rest, hDb⟩ : ∃ f rest, (Ds (lo + 1)).blocks = f :: rest := by
    rcases h : (Ds (lo + 1)).blocks with _ | ⟨f, rest⟩
    · exact absurd h hwf1.1
    · exact ⟨f, rest, rfl⟩
  have hk1 : 1 ≤ P.top - lo := by omega
  have hsl := DLRep.stack_le dl
  have hbfc := dl.bfcap
  have hch0 : base st lo = base st (lo + 1) + (Ds (lo + 1)).blocks.length := by
    have := dl.chain 0 hk1; simpa using this
  have hlenD : (Ds (lo + 1)).blocks.length = rest.length + 1 := by rw [hDb]; rfl
  have hstkl := hLn.stkl
  -- entry ids of the child
  have hids : (entIds (Ds lo).blocks).length < P.ecap := by
    have hnd : (entIds (Ds lo).blocks).Nodup := by
      rw [entIds_eq_allEnts]; exact DLRep.ids_lo dl
    have hlt : ∀ x ∈ entIds (Ds lo).blocks, x < g.fresh := by
      intro x hx
      rw [entIds_eq_allEnts] at hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      exact hD.fr lo le_rfl (by omega) e he
    have := nodup_length_le hnd hlt
    have := dl.pool.2.1
    omega
  -- 1. set-up
  refine runs_seq ((mmSetup_spec (ops := realOps) P st H g Ds lo hD hl htop).mono ?_)
  rintro q ⟨hqc, hqlv, hqpb, hqpk, hqck, hqg, hUq, hwlq, hvlq, hcq⟩
  have hDq : DRI P q H g Ds lo := DRI.frame_same hD hUq (by simp) (by simp) (by decide) (by simp)
  have hvcq : vc (G := G) q = vc st := vc_of hUq (by simp)
  have hcapq : q.cap = st.cap := hUq.cap
  -- 2. the keep bit
  refine runs_seq ((Runs.sframe (mmKeep_spec q H (vc st) hH lo (Ds (lo + 1)) (Ds lo) f rest hDb
    (by rw [← hvcq]; exact hDq.bd lo le_rfl (by omega))
    (by rw [← hvcq]; exact hDq.bd (lo + 1) (by omega) htop)
    hqc hqlv hqpk (bdA_inB hLn hwlq hvlq (by omega)) (bdA_inB hLn hwlq hvlq htop)
    (by rw [hwlq]; have := hLn.bf; omega) (by rw [hwlq]; have := hLn.bf; omega)
    (by rw [hcapq]; omega) hMP2) mmKeep_noalloc).mono ?_)
  rintro r2 ⟨⟨hk2, hX2, hc2⟩, hU2, hwl2, hvl2⟩
  set keep := ltSep (Ds lo).Bd (nextSep rest ((Ds (lo + 1)).Bd : WithBot (WLab G s))) with hkeep
  have hsW2 : sWA mmKeep = [] := by simp [sWA, mmKeep, loadA, LabRAM.cmp, LabRAM.cmpW]
  have hsV2 : sVA mmKeep = [] := by simp [sVA, mmKeep, loadA, LabRAM.cmp, LabRAM.cmpW]
  have hr2w : ∀ x ∈ ["mm.c", "mg.lv", "mg.pb", "mg.pk", "mg.ck", "mg.g", "n", "lvl", "ds.fresh",
      "blk.fresh"], r2.w x = q.w x := fun x hx => hU2.wreg x (by
    revert x; simp only [mmKeep, loadA, LabRAM.cmp, LabRAM.cmpW, sWR, mmX, mmK]; decide)
  have hr2a : ∀ a, r2.wa a = q.wa a := fun a => (hU2.warr a (by simp [hsW2])).1
  have hbase2 : ∀ j, base r2 j = base q j := fun j => by simp only [base, hr2a]
  have hDL2 : DLRep r2 H (vc st) P.ecap P.bcap g.L g.fresh Ds lo (P.top - lo) := by
    have := DLRep.of_unch hDq.dl hU2 (by simp [hsW2]) (by simp [hsV2]) (fun a ha h => by
      simp only [drWR, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact absurd (hr2w "ds.fresh" (by simp)) (by
          intro _; revert h; simp only [mmKeep, loadA, LabRAM.cmp, LabRAM.cmpW, sWR, mmX, mmK]; decide)
      · exact absurd (hr2w "blk.fresh" (by simp)) (by
          intro _; revert h; simp only [mmKeep, loadA, LabRAM.cmp, LabRAM.cmpW, sWR, mmX, mmK]; decide))
    rwa [hvcq] at this
  -- 3. re-key or drop
  have hq0 : base q (lo + 1) = base st (lo + 1) := by simp only [base, (hUq.warr _ (by simp)).1]
  refine runs_seq ((Runs.sframe (mmRekey_spec r2 H (vc st) P.ecap P.bcap g.L g.fresh Ds lo (P.top - lo)
    hk1 hDL2 f rest hDb keep hk2 hX2
    (by rw [hr2w _ (by simp), hqpb, hbase2, hq0])
    (by rw [hr2w _ (by simp), hqpk])
    (by rw [hbase2, hq0, show r2.cap = st.cap by rw [hU2.cap, hcapq]]; omega)) mmRekey_noalloc).mono ?_)
  rintro r3 ⟨⟨hDL3, hdr3, hc3⟩, hU3, hwl3, hvl3⟩
  set D1 := keepD (Ds (lo + 1)) (Ds lo) f rest keep with hD1
  set Ds1 := Function.update Ds (lo + 1) D1 with hDs1
  have hr3w : ∀ x ∈ ["mm.c", "mg.lv", "mg.pb", "mg.pk", "mg.ck", "mg.g", "n", "lvl", "ds.fresh",
      "blk.fresh"], r3.w x = r2.w x := fun x hx => hU3.wreg x (by
    revert x; simp only [mmRekey, rekeyS, storeA, sWR]; decide)
  have hr3a : ∀ a, a ∉ ["blk.h", "blk.v", "blk.e", "blk.r", "blk.bot"] → r3.wa a = r2.wa a :=
    fun a ha => (hU3.warr a (by simpa [mmRekey, rekeyS, storeA, sWA, blkA] using ha)).1
  have hbase3 : ∀ j, base r3 j = base st j := fun j => by
    simp only [base]; rw [hr3a _ (by simp), hr2a, (hUq.warr _ (by simp)).1]
  have hstk3 : r3.wa "dsl.stk" = st.wa "dsl.stk" := by
    rw [hr3a _ (by simp), hr2a, (hUq.warr _ (by simp)).1]
  have hwl3' : r3.wlen = st.wlen := by rw [hwl3, hwl2, hwlq]
  have hcap3 : r3.cap = st.cap := by rw [hU3.cap, hU2.cap, hcapq]
  have hDs1lo : Ds1 lo = Ds lo := by rw [hDs1, Function.update_of_ne (by omega)]
  have hDs1hi : Ds1 (lo + 1) = D1 := by rw [hDs1, Function.update_self]
  have hlen1 : (Ds1 (lo + 1)).blocks.length = (Ds (lo + 1)).blocks.length := by
    rw [hDs1hi, hD1, hlenD]; simp [keepD]
  have hne1 : (Ds1 (lo + 1)).blocks ≠ [] := by rw [hDs1hi, hD1]; simp [keepD]
  -- the grouping side conditions
  have hD0 : DRep st H (vc st) P.bcap lo (base st lo) (Ds lo) := by
    have := dl.drep 0 (by omega); simpa using this
  have hbar3 := hDL3.barr
  have hGS : GSide r3 (base r3 (lo + 1) + (Ds1 (lo + 1)).blocks.length + (Ds1 lo).blocks.length - 1)
      (stkId r3 (base r3 (lo + 1) + (Ds1 (lo + 1)).blocks.length) (Ds1 lo).blocks.length)
      (Ds1 lo).blocks := by
    rw [hlen1, hDs1lo, hbase3, ← hch0]
    have hsid : ∀ j, stkId r3 (base st lo) (Ds lo).blocks.length j =
        stkId st (base st lo) (Ds lo).blocks.length j := fun j => by simp only [stkId, hstk3]
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hbar3
    refine ⟨?_, by omega, fun j hj => ?_, fun j hj => ?_, ?_⟩
    · rw [hwl3', hstkl]; omega
    · rw [hsid]; have := hD0.bidb j hj; exact ⟨by omega, by omega, by omega⟩
    · rw [hsid, hcap3]; have := hD0.bidb j hj; omega
    · rw [hcap3]; omega
  -- 4. the in-place grouping
  refine runs_seq ((Runs.sframe (mergeDL (ops := realOps) r3 H (vc st) P.ecap P.bcap g.L g.fresh Ds1 lo
    (P.top - lo) hk1 hDL3 keep ((Ds (lo + 1)).M / 3) hne1 hGS
    (by rw [hr3w _ (by simp), hr2w _ (by simp), hqpb, hbase3])
    (by rw [hr3w _ (by simp), hr2w _ (by simp), hqpk, hlen1])
    (by rw [hr3w _ (by simp), hr2w _ (by simp), hqck, hDs1lo])
    (by rw [hr3w _ (by simp), hr2w _ (by simp), hqg]) hdr3
    (by rw [hr3w _ (by simp), hr2w _ (by simp), hqlv])
    (by rw [hwl3']; have := hLn.sz; omega)) mergeS_noalloc).mono ?_)
  rintro r4 ⟨⟨hDL4, hU4', hc4⟩, hU4, hwl4, hvl4⟩
  have hr4w : ∀ x ∈ ["mm.c", "n", "lvl"], r4.w x = r3.w x := fun x hx => hU4'.wreg x (by
    revert x; simp only [mergeRegs]; decide)
  have hr4a : ∀ a ∈ ["lk.n", "lk.p"], r4.wa a = st.wa a := fun a ha => by
    rw [(hU4'.warr a (by revert a; decide)).1, hr3a a (by revert a; decide), hr2a,
      (hUq.warr a (by simp)).1]
  have hwl4' : r4.wlen = st.wlen := by rw [hwl4, hwl3']
  have hcap4 : r4.cap = st.cap := by rw [hU4.cap, hcap3]
  -- 5. the live-key lists
  obtain ⟨K, hK, hKk⟩ := hD.kl
  have hmc : r4.w "mm.c" = lo := by rw [hr4w _ (by simp), hr3w _ (by simp), hr2w _ (by simp), hqc]
  have hmn : r4.w "n" = G.n := by
    rw [hr4w _ (by simp), hr3w _ (by simp), hr2w _ (by simp), hUq.wreg _ (by simp), hn]
  have hml : r4.w "lvl" = lo + 1 := by
    rw [hr4w _ (by simp), hr3w _ (by simp), hr2w _ (by simp), hUq.wreg _ (by simp), hl]
  refine runs_seq (runs_wset (a := G.n + lo) (by
    simp only [evalW, hmn, hmc, Option.bind_eq_bind, Option.bind_some, fit]
    rw [if_pos (by rw [hcap4]; omega)]) ?_)
  set q5 := (r4.setW "kl.c" (G.n + lo)).charge 1 with hq5
  have h5n : q5.w "n" = G.n := by simp [hq5, hmn]
  have h5l : q5.w "lvl" = lo + 1 := by simp [hq5, hml]
  have h5c : G.n + (lo + 1) < q5.cap := by simp [hq5, hcap4]; omega
  refine runs_seq (runs_wset (a := G.n + (lo + 1)) (by simp [evalW, h5n, h5l, fit, h5c]) ?_)
  set q6 := (q5.setW "kl.s" (G.n + (lo + 1))).charge 1 with hq6
  have hq6a : q6.wa = r4.wa := by simp [hq6, hq5]
  have hK6 : KL.LL (q6.wa "lk.n") (q6.wa "lk.p") G.n lo P.top K := by
    rw [hq6a, hr4a _ (by simp), hr4a _ (by simp)]; exact hK
  have hwl6 : q6.wlen = st.wlen := by simp [hq6, hq5, hwl4']
  refine (Runs.sframe (KL.klSplice_LL (ops := realOps) q6 hK6 (by omega) (by simp [hq6, hq5])
    (by simp [hq6]) (by rw [hwl6]; exact hLn.lkn) (by rw [hwl6]; exact hLn.lkp)
    (by simp [hq6, hq5, hcap4]; omega)) klSplice_noalloc).mono ?_
  rintro r5 ⟨⟨hK5, hU5', -, hc5⟩, hU5, hwl5, hvl5⟩
  -- the merged structure
  have hDm : Function.update Ds1 (lo + 1) (mergedD (Ds1 (lo + 1)) (Ds1 lo) keep ((Ds (lo + 1)).M / 3)) =
      Function.update Ds (lo + 1) (DB.merge 1 (Ds (lo + 1)) (Ds lo)).1 := by
    rw [hDs1hi, hDs1lo, hD1, hkeep, mergedD_keepD _ _ f rest hDb, hDs1, Function.update_idem]
  rw [hDm] at hDL4
  have hsub : P.top - lo - 1 = P.top - (lo + 1) := by omega
  rw [hsub] at hDL4
  obtain ⟨hhas, -, -, -, -⟩ := DB.merge_spec 1 hwf1 hwf0 hMP1 hMP2 hMP0
  have hU46 : Unchanged r4 q6 [] [] ["kl.c", "kl.s"] [] := by
    rw [hq6, unch_charge, unch_setW (by simp), hq5, unch_charge, unch_setW (by simp)]
    exact Unchanged.refl _ _ _ _ _
  refine ⟨DLRep.of_unch (DLRep.of_unch hDL4 hU46 (by simp) (by simp) (by decide)) hU5'
      (by decide) (by simp) (by decide), ⟨_, hK5, fun j h1 h2 v => ?_⟩, ?_⟩
  · by_cases hj : j = lo + 1
    · subst hj
      rw [Function.update_self, Function.update_self, List.mem_append, hKk lo le_rfl (by omega),
        hKk (lo + 1) (by omega) htop, hhas]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
      exact hKk j (by omega) h2 v
  · rw [merge_cost_eq _ _ f rest hDb]
    have e6 : q6.cost = r4.cost + 2 := by simp [hq6, hq5]
    rw [hDs1lo] at hc4
    omega


/-! ## 5. The operation on `DRI` -/

theorem dsMerge_nA : ∀ a ∈ ["vcnt", "dsl.bf", "dsl.bh", "dsl.bv", "dsl.be", "dsl.br", "dsl.M",
    "ent.key"], a ∉ sWA dsMerge := by decide
theorem dsMerge_nV : "dsl.bl" ∉ sVA dsMerge := by decide
theorem dsMerge_nR : ∀ a ∈ ["ds.fresh", "blk.fresh"], a ∉ sWR dsMerge := by decide

/-- **BM.14 on the D layer**: merging the child (level `lo`) into its parent (level `lo + 1`) -/
theorem dsMerge_spec (P : DPar) (st : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (g : DGl G s)
    (Ds : ℕ → DStrM G s) (lo : ℕ) (hD : DRI P st H g Ds lo) (hl : st.w "lvl" = lo + 1)
    (hn : st.w "n" = G.n) (htop : lo + 1 ≤ P.top) (hH : GoodHist (s := s) H (vc st))
    (hMP1 : ∀ e ∈ DB.liveVals g.L (Ds (lo + 1)).blocks, (Ds lo).Bd ≤ e.val)
    (hMP2 : ∀ b ∈ (Ds (lo + 1)).blocks.tail, (((Ds lo).Bd : WLab G s) : WithBot (WLab G s)) < b.sep)
    (hMP0 : (Ds lo).Bd ≤ (Ds (lo + 1)).Bd) :
    Runs realOps dsMerge st (fun r =>
      DRI P r H g (Function.update Ds (lo + 1) (DB.merge 1 (Ds (lo + 1)) (Ds lo)).1) (lo + 1) ∧
      Unchanged st r (sWA dsMerge) (sVA dsMerge) (sWR dsMerge) (sVR dsMerge) ∧ r.wlen = st.wlen ∧
      r.vlen = st.vlen ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + 17 * ((DB.merge 1 (Ds (lo + 1)) (Ds lo)).2 + 1) ∧
      r.w "ds.fresh" + r.w "blk.fresh" = st.w "ds.fresh" + st.w "blk.fresh") := by
  refine (Runs.sframe (Runs.cost_mono (dsMerge_main P st H g Ds lo hD hl hn htop hH hMP1 hMP2 hMP0))
    dsMerge_noalloc).mono ?_
  rintro r ⟨⟨⟨hDL, ⟨K, hK, hKk⟩, hc⟩, hcl⟩, hU, hwl, hvl⟩
  obtain ⟨-, -, hwfm, hMm, hBdm⟩ :=
    DB.merge_spec 1 (hD.wf (lo + 1) (by omega) htop) (hD.wf lo le_rfl (by omega)) hMP1 hMP2 hMP0
  have hwa : ∀ a ∈ ["vcnt", "dsl.bf", "dsl.bh", "dsl.bv", "dsl.be", "dsl.br", "dsl.M", "ent.key"],
      r.wa a = st.wa a := fun a ha => (hU.warr a (dsMerge_nA a ha)).1
  have hvc : vc (G := G) r = vc st := vc_of hU (dsMerge_nA _ (by simp))
  have hDs'j : ∀ j, j ≠ lo + 1 →
      Function.update Ds (lo + 1) (DB.merge 1 (Ds (lo + 1)) (Ds lo)).1 j = Ds j :=
    fun j hj => Function.update_of_ne hj _ _
  have hDs'l : Function.update Ds (lo + 1) (DB.merge 1 (Ds (lo + 1)) (Ds lo)).1 (lo + 1) =
      (DB.merge 1 (Ds (lo + 1)) (Ds lo)).1 := Function.update_self _ _ _
  refine ⟨⟨htop, by rw [hvc]; exact hDL, fun j h1 h2 => ?_, fun j h1 h2 => ?_, ⟨K, hK, hKk⟩,
      fun j h1 h2 => ?_, fun j h1 h2 => ?_, hD.lf, ?_, hD.lens.of_len hwl hvl hU.cap, fun j hj => ?_, ?_,
      fun i hi => ?_, fun j h1 h2 => ?_⟩, hU, hwl, hvl, hcl, hc, ?_⟩
  · -- the bounds
    rw [hvc]
    have hb : BdHolds st j H (vc st)
        (Function.update Ds (lo + 1) (DB.merge 1 (Ds (lo + 1)) (Ds lo)).1 j).Bd := by
      by_cases hj : j = lo + 1
      · subst hj; rw [hDs'l, hBdm]; exact hD.bd (lo + 1) (by omega) htop
      · rw [hDs'j j hj]; exact hD.bd j (by omega) h2
    exact hb.of_eq (by rw [hwa "dsl.bf" (by simp)]) (by rw [(hU.varr _ dsMerge_nV).1])
      (by rw [hwa "dsl.bh" (by simp)]) (by rw [hwa "dsl.bv" (by simp)]) (by rw [hwa "dsl.be" (by simp)])
      (by rw [hwa "dsl.br" (by simp)])
  · -- the parameters
    rw [hwa "dsl.M" (by simp)]
    by_cases hj : j = lo + 1
    · subst hj; rw [hDs'l, hMm]; exact hD.mv (lo + 1) (by omega) htop
    · rw [hDs'j j hj]; exact hD.mv j (by omega) h2
  · by_cases hj : j = lo + 1
    · subst hj; rw [hDs'l]; exact hwfm
    · rw [hDs'j j hj]; exact hD.wf j (by omega) h2
  · by_cases hj : j = lo + 1
    · subst hj; rw [hDs'l]
      intro x hx
      rcases BM.dbMerge_ents 1 (Ds (lo + 1)) (Ds lo) x hx with h | h
      · exact hD.fr (lo + 1) (by omega) htop x h
      · exact hD.fr lo le_rfl (by omega) x h
    · rw [hDs'j j hj]; exact hD.fr j (by omega) h2
  · rw [hU.wreg _ (dsMerge_nR _ (by simp)), hU.wreg _ (dsMerge_nR _ (by simp))]; exact hD.use
  · rw [hDs'j j (by omega)]; exact hD.hib j hj
  · rw [hU.procs]; exact hD.procs
  · rw [hwa "ent.key" (by simp)]; exact hD.keys i hi
  · rw [hU.cap]
    by_cases hj : j = lo + 1
    · subst hj; rw [hDs'l, hMm]; exact hD.mc (lo + 1) (by omega) htop
    · rw [hDs'j j hj]; exact hD.mc j (by omega) h2
  · rw [hU.wreg _ (dsMerge_nR _ (by simp)), hU.wreg _ (dsMerge_nR _ (by simp))]

/-- **`DLayer.merge_spec` for `DRI`**, in the shape of agent-04's `MergeOK` with the stack-top
premise `l ≤ P.top` (`DLayer.LT := P.top`), for any name lists covering the text's footprint and
any `K ≥ 17` -/
theorem dsMerge_ok (P : DPar) {wa va wr vr : List String} (hwa : ∀ a ∈ sWA dsMerge, a ∈ wa)
    (hva : ∀ a ∈ sVA dsMerge, a ∈ va) (hwr : ∀ a ∈ sWR dsMerge, a ∈ wr)
    (hvr : ∀ a ∈ sVR dsMerge, a ∈ vr) {K : ℕ} (hK : 17 ≤ K) :
    ∀ (st : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (g : DGl G s) (Ds : ℕ → DStrM G s)
      (l : ℕ), 1 ≤ l → l ≤ P.top → DRI P st H g Ds (l - 1) → st.w "lvl" = l → st.w "n" = G.n →
      GoodHist (s := s) H (vc st) →
      (∀ e ∈ DB.liveVals g.L (Ds l).blocks, (Ds (l - 1)).Bd ≤ e.val) →
      (∀ b ∈ (Ds l).blocks.tail, (((Ds (l - 1)).Bd : WLab G s) : WithBot (WLab G s)) < b.sep) →
      (Ds (l - 1)).Bd ≤ (Ds l).Bd →
      Runs realOps dsMerge st (fun r =>
        DRI P r H g (Function.update Ds l (DB.merge 1 (Ds l) (Ds (l - 1))).1) l ∧
        Unchanged st r wa va wr vr ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen ∧ st.cost ≤ r.cost ∧
        r.cost ≤ st.cost + K * ((DB.merge 1 (Ds l) (Ds (l - 1))).2 + 1) ∧
        r.w "ds.fresh" + r.w "blk.fresh" = st.w "ds.fresh" + st.w "blk.fresh") := by
  intro st H g Ds l hl1 hlt hD hl hn hH h1 h2 h0
  obtain ⟨lo, rfl⟩ : ∃ lo, l = lo + 1 := ⟨l - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hD h1 h2 h0 ⊢
  refine (dsMerge_spec P st H g Ds lo hD hl hn hlt hH h1 h2 h0).mono ?_
  rintro r ⟨a1, a2, a3, a4, a5, a6, a7⟩
  exact ⟨a1, unch_widen a2 hwa hva hwr hvr, a3, a4, a5,
    le_trans a6 (Nat.add_le_add_left (Nat.mul_le_mul_right _ hK) _), a7⟩

/-- the merge's word arrays / value arrays are the representation's -/
theorem dsMerge_WA_sub : ∀ a ∈ sWA dsMerge, a ∈ drWA := by decide
theorem dsMerge_VA_sub : ∀ a ∈ sVA dsMerge, a ∈ drVA := by decide
/-- the merge's registers avoid the spine's -/
theorem dsMerge_WR_ok : ∀ a ∈ sWR dsMerge, a ∉ RamSpine.spRegs := by decide
theorem dsMerge_VR_ok : ∀ a ∈ sVR dsMerge, a ∉ RamSpine.spVRegs := by decide

/-- **`MergeOK` for agent-04's `mkDL` name lists**: any extra register lists containing the merge's
registers (e.g. `xWR := sWR dsMerge ++ …`, `xVR := sVR dsMerge ++ …`) -/
theorem dsMerge_mergeOK (P : DPar) (xWA xVA xWR xVR : List String)
    (hwr : ∀ a ∈ sWR dsMerge, a ∈ xWR) (hvr : ∀ a ∈ sVR dsMerge, a ∈ xVR) {K : ℕ} (hK : 17 ≤ K) :
    MergeOK (G := G) (s := s) P dsMerge (drWA ++ xWA) (drVA ++ xVA) (wrD ++ xWR) (vrD ++ xVR) K :=
  dsMerge_ok P (fun a ha => List.mem_append_left _ (dsMerge_WA_sub a ha))
    (fun a ha => List.mem_append_left _ (dsMerge_VA_sub a ha))
    (fun a ha => List.mem_append_right _ (hwr a ha)) (fun a ha => List.mem_append_right _ (hvr a ha)) hK

end Frontier.CHD.DLI
