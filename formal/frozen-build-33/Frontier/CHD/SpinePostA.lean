import Frontier.CHD.SpineLoopA
import Frontier.CHD.SpinePost

/-!
# SpinePostA — agent-06's `PostSpecStmt` gives the loop's `PostHalf` (agent-08, B-L4, NON-GATE)

The only difference between the two statements is the budget: `PostHalf` provides it for every
completion `(lUi, L', piv', lres)` with a fixed slack `Sl`, `PostSpecStmt` asks for it in the
`preCost` form with the block-count slack `postS … nb`.  The block count of the merged structure is
at most `2 · NB` (both levels are active, and merging does not increase the block count), so
`postS … (2 · NB) ≤ Sl` suffices.  The use is the same up to the factor `2` of `PostHalf`
(`postCost = restCostA`).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamSpine

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamLevel
  Frontier.CHD.BM Frontier.CHD.RamBaseCase Frontier.CHD.LabTab WExpr Stmt

variable {G : Graph} {s : Fin G.n}

/-! ## Merging does not increase the block count -/

theorem groupAux_length_le (g : ℕ) :
    ∀ (cur : Option (DB.Block (Fin G.n) (WLab G s))) (bs : List (DB.Block (Fin G.n) (WLab G s))),
      (DB.groupAux g cur bs).length ≤ cur.toList.length + bs.length
  | none, [] => by simp [DB.groupAux]
  | some c, [] => by simp [DB.groupAux]
  | none, b :: bs => by
    have ih1 := groupAux_length_le g none bs
    have ih2 := groupAux_length_le g (some b) bs
    simp only [DB.groupAux]
    split_ifs
    · simp only [List.length_cons, Option.toList_none, List.length_nil] at ih1 ⊢; omega
    · simp only [Option.toList_some, List.length_singleton, Option.toList_none, List.length_nil,
        List.length_cons] at ih2 ⊢; omega
  | some c, b :: bs => by
    have ih1 := groupAux_length_le g none bs
    have ih2 := groupAux_length_le g (some ⟨c.sep, c.ents ++ b.ents⟩) bs
    simp only [DB.groupAux]
    split_ifs
    · simp only [List.length_cons, Option.toList_none, List.length_nil, Option.toList_some,
        List.length_singleton] at ih1 ⊢; omega
    · simp only [Option.toList_some, List.length_singleton, List.length_cons] at ih2 ⊢; omega

theorem merge_blocks_le (T : ℕ) (D D' : DStrM G s) :
    ((dlOps G s).merge T D D').1.blocks.length ≤ D.blocks.length + D'.blocks.length := by
  show (DB.merge 1 D D').1.blocks.length ≤ _
  unfold DB.merge
  split
  · simp_all
  · rename_i f rest hD
    have h1 := groupAux_length_le (G := G) (s := s) (D.M / 3) none D'.blocks
    simp only [Option.toList_none, List.length_nil, zero_add] at h1
    rw [hD]
    split_ifs <;> simp only [List.length_append, List.length_cons] <;> omega

/-! ## The adapter -/

section adapter

variable {T : ℕ → ℕ} {Φ Ω : Type}

/-- **agent-06's second half is the loop's `PostHalf`.** -/
theorem postHalf_of_stmt (DL : DLayer G s T) (PI : PhiI Φ) {LF : ℕ} {body : Stmt}
    {τf Mf : ℕ → ℕ} {cmp : Stmt} {C : ℕ} {CW CV : List String} {Inv : Φ → Prop}
    {FPC : FPRelC G s Φ Ω} {DCb : DCost} {l Sl : ℕ}
    (hps : PostSpecStmt DL PI LF body τf Mf cmp C CW CV Ω) (hy : PostHyg DL PI CW)
    (hcmp : ∀ c0, CmpFam DL cmp C CW CV c0) (hsort : WinScan.CSRSorted G s)
    {subC : SubRelC G s Φ Ω}
    (hsimsub : SimSub G s (dlOps G s) τf Inv Mf l (BMSSPD G s (dlOps G s) FPC DCb T Mf τf l) subC)
    (hsubC : GoodSub G s τf Inv l subC)
    (hSl : postS DL.K C G.n G.m (2 * DL.NB) ≤ Sl) (hLT : LF ≤ DL.LT) :
    PostHalf DL PI LF body τf Mf Inv FPC DCb l (postProg DL.merge DL.delB DL.ins DL.empty cmp)
      (postK DL.K C) Sl := by
  classical
  intro B S d0 d1 p P0 Q W B'0 f0 L0 c ks Bi g1 Dc1 cp B'i Ui Dci d1' φ1 g2 lg st0 st τl Ds H c0
    hpre hfp hA hne hpull hsubD hPC hbud hubud
  -- the block count of the merged structure
  have hnb : ((dlOps G s).merge (T (l + 1)) Dc1 Dci).1.blocks.length ≤ 2 * DL.NB := by
    have h1 := DL.nb_le st H g2 _ l hPC.D (l + 1) (by omega)
    have h2 := DL.nb_le st H g2 _ l hPC.D l le_rfl
    simp only [Function.update_self, Function.update_of_ne (show l + 1 ≠ l by omega)] at h1 h2
    have := merge_blocks_le (T (l + 1)) Dc1 Dci
    omega
  have hS := postS_mono DL.K C G.n G.m hnb
  have ecost : ∀ lUi L' lres, postCost (T (l + 1)) B c.cs Bi Ui Dc1 Dci d1' g2 lUi L' lres =
      restCostA (T (l + 1)) B c.cs Bi Ui Dc1 Dci d1' g2 lUi L' lres := fun lUi L' lres => by
    simp only [postCost, preCost, restCostA, postFold, foldA]
  refine (hps c0 hy (hcmp c0) hsort hLT hpre hfp hsimsub hsubC hA hne hpull hsubD hPC ?_ ?_).mono ?_
  · intro lUi L' h1 h2 h3 h4
    obtain ⟨piv', hres⟩ := exists_reselect c.cs.lit Ui (postFold (T (l + 1)) B Bi Dc1 Dci d1' g2 lUi L').d
    have hb := hbud lUi L' piv' (reselected c.cs.lit Ui piv').toList h1 h2 h3 h4 hres
      (Finset.nodup_toList _) (Finset.toList_toFinset _)
    have hle : preCost (T (l + 1)) B Bi Ui Dc1 Dci d1' g2 lUi L' ≤
        restCostA (T (l + 1)) B c.cs Bi Ui Dc1 Dci d1' g2 lUi L'
          (reselected c.cs.lit Ui piv').toList := by
      simp only [preCost, restCostA, postFold, foldA]; omega
    have := Nat.mul_le_mul_left (postK DL.K C) (Nat.add_le_add_right hle 1)
    omega
  · intro lUi L' piv' lres h1 h2 h3 h4 h5 h6 h7
    have hb := hubud lUi L' piv' lres h1 h2 h3 h4 h5 h6 h7
    rw [ecost]; omega
  · rintro r ⟨lUi, L', piv', lres, H', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
      h15⟩
    refine ⟨lUi, L', piv', lres, H', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, ?_, ?_⟩
    · rw [← ecost]; exact h14
    · rw [ecost] at h15; omega

end adapter

end Frontier.CHD.RamSpine
