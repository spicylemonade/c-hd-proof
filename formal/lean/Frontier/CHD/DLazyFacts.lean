import Frontier.CHD.BMLazy

/-!
# Frontier.CHD.DLazyFacts — Layer-A facts of `DLazy` insertions (owner agent-03)

**NON-GATE** (Layer A).  For agent-04's `DLazy` as `dlOps`:
* `insertL_Bd` / `insManyC_Bd`: insertions keep the structure's bound `Bd`;
* `insertL_blocks` / `insManyC_blocks`: insertions never change the number of blocks (no split:
  `insertL` runs `insert` with `M := bigM`, and `fixBlock` then never splits);
* `insManyC_len_le`: every insertion costs `≥ 1` (the conversion's length is paid by its cost);
* `insManyC_take_le`: a prefix costs at most the whole list;
* `insManyC_cost_le`: each insertion costs at most `log₂ #blocks + 4`.
-/

namespace Frontier.CHD.BM

variable {G : Graph} {s : Fin G.n}

open Frontier.CHD.DB in
theorem addTo_length {κ α : Type*} [DecidableEq κ] [LinearOrder α] [Inhabited α] (T0 : ℕ)
    (L : Live κ α) (M : ℕ) (lam : α) (e : Entry κ α) :
    ∀ bs : List (Block κ α), (∀ b ∈ bs, b.ents.length + 1 ≤ 2 * M + 1) →
      (addTo T0 L M lam e bs).1.length = bs.length
  | [], _ => rfl
  | [b], h => by
    have hb := h b (by simp)
    simp only [addTo, Frontier.CHD.DL.fixBlock_small T0 (show (⟨b.sep, e :: b.ents⟩ : Block κ α).ents.length ≤ 2 * M + 1 by
      simp; omega)]
    rfl
  | b :: b' :: bs, h => by
    have hb := h b (by simp)
    simp only [addTo]
    split
    · simp only [List.length_cons]
      rw [addTo_length T0 L M lam e (b' :: bs) (fun x hx => h x (List.mem_cons_of_mem _ hx))]
      simp
    · rw [Frontier.CHD.DL.fixBlock_small T0 (show (⟨b.sep, e :: b.ents⟩ : Block κ α).ents.length ≤ 2 * M + 1 by
        simp; omega)]
      simp

theorem ents_le_allEnts {κ α : Type*} [DecidableEq κ] [LinearOrder α] {bs : List (DB.Block κ α)}
    {b : DB.Block κ α} (hb : b ∈ bs) : b.ents.length ≤ (DB.allEnts bs).length := by
  unfold DB.allEnts
  rw [List.length_flatten, List.map_map]
  exact List.single_le_sum (fun x _ => Nat.zero_le x) _
    (List.mem_map_of_mem (f := (List.length ∘ fun x : DB.Block κ α => x.ents)) hb)

/-- `DLazy` insertions keep the structure's bound. -/
theorem insertL_Bd {L : DB.Live (Fin G.n) (WLab G s)} {fresh : ℕ} {D : DStrM G s} {v : Fin G.n}
    {lam : WLab G s} : (Frontier.CHD.DL.insertL L fresh D v lam).2.2.1.Bd = D.Bd := by
  unfold Frontier.CHD.DL.insertL Frontier.CHD.DB.insert
  split <;> rfl

/-- **A `DLazy` insertion never changes the number of blocks.** -/
theorem insertL_blocks {L : DB.Live (Fin G.n) (WLab G s)} {fresh : ℕ} {D : DStrM G s} {v : Fin G.n}
    {lam : WLab G s} :
    (Frontier.CHD.DL.insertL L fresh D v lam).2.2.1.blocks.length = D.blocks.length := by
  unfold Frontier.CHD.DL.insertL Frontier.CHD.DB.insert
  split
  · rfl
  · dsimp only
    apply addTo_length
    intro b hb
    have := ents_le_allEnts hb
    unfold Frontier.CHD.DL.bigM
    omega

/-- Insertions keep the structure's bound. -/
theorem insManyC_Bd (T0 : ℕ) (f : Fin G.n → WLab G s) :
    ∀ (l : List (Fin G.n)) (g : DGl G s) (D : DStrM G s),
      (insManyC (dlOps G s) T0 f l g D).2.1.Bd = D.Bd
  | [], _, _ => rfl
  | y :: l, g, D => by
    simp only [insManyC]
    rw [insManyC_Bd T0 f l]
    exact insertL_Bd

/-- Insertions keep the number of blocks. -/
theorem insManyC_blocks (T0 : ℕ) (f : Fin G.n → WLab G s) :
    ∀ (l : List (Fin G.n)) (g : DGl G s) (D : DStrM G s),
      (insManyC (dlOps G s) T0 f l g D).2.1.blocks.length = D.blocks.length
  | [], _, _ => rfl
  | y :: l, g, D => by
    simp only [insManyC]
    rw [insManyC_blocks T0 f l]
    exact insertL_blocks

/-- The insertions of a prefix cost at most those of the whole list. -/
theorem insManyC_take_le (T0 : ℕ) (f : Fin G.n → WLab G s) :
    ∀ (l : List (Fin G.n)) (k : ℕ) (g : DGl G s) (D : DStrM G s),
      (insManyC (dlOps G s) T0 f (l.take k) g D).2.2 ≤ (insManyC (dlOps G s) T0 f l g D).2.2
  | [], _, _, _ => by simp
  | _ :: _, 0, _, _ => by simp [insManyC]
  | y :: l, k + 1, g, D => by
    simp only [List.take_succ_cons, insManyC]
    have := insManyC_take_le T0 f l k (insC (dlOps G s) T0 g D y (f y)).1
      (insC (dlOps G s) T0 g D y (f y)).2.1
    omega

/-- Every `DLazy` insertion costs at least `1`: a conversion's length is paid by its cost. -/
theorem insManyC_len_le (T0 : ℕ) (f : Fin G.n → WLab G s) :
    ∀ (l : List (Fin G.n)) (g : DGl G s) (D : DStrM G s),
      l.length ≤ (insManyC (dlOps G s) T0 f l g D).2.2
  | [], _, _ => by simp [insManyC]
  | y :: l, g, D => by
    have ih := insManyC_len_le T0 f l (insC (dlOps G s) T0 g D y (f y)).1
      (insC (dlOps G s) T0 g D y (f y)).2.1
    have h1 : 1 ≤ (insC (dlOps G s) T0 g D y (f y)).2.2 := by
      show 1 ≤ (Frontier.CHD.DL.insertL g.L g.fresh D y (f y)).2.2.2
      unfold Frontier.CHD.DL.insertL
      dsimp only
      split <;> omega
    simp only [insManyC, List.length_cons]
    omega

/-- Each `DLazy` insertion costs at most `log₂ #blocks + 4` (binary search, no split). -/
theorem insManyC_cost_le (T0 : ℕ) (f : Fin G.n → WLab G s) (NB : ℕ) :
    ∀ (l : List (Fin G.n)) (g : DGl G s) (D : DStrM G s), D.blocks.length ≤ NB →
      (insManyC (dlOps G s) T0 f l g D).2.2 ≤ l.length * (Nat.log 2 NB + 4)
  | [], _, _, _ => by simp [insManyC]
  | y :: l, g, D, h0 => by
    have h1 : (insC (dlOps G s) T0 g D y (f y)).2.2 ≤ Nat.log 2 NB + 4 := by
      show (Frontier.CHD.DL.insertL g.L g.fresh D y (f y)).2.2.2 ≤ _
      unfold Frontier.CHD.DL.insertL
      dsimp only
      have := Nat.log_mono_right (b := 2) h0
      split
      · omega
      · unfold Frontier.CHD.DL.bsCost; omega
    have hb : (insC (dlOps G s) T0 g D y (f y)).2.1.blocks.length ≤ NB := by
      rw [show (insC (dlOps G s) T0 g D y (f y)).2.1 = (Frontier.CHD.DL.insertL g.L g.fresh D y (f y)).2.2.1
        from rfl, insertL_blocks]; exact h0
    have ih := insManyC_cost_le T0 f NB l (insC (dlOps G s) T0 g D y (f y)).1
      (insC (dlOps G s) T0 g D y (f y)).2.1 hb
    simp only [insManyC, List.length_cons]
    rw [Nat.succ_mul]
    omega

end Frontier.CHD.BM
