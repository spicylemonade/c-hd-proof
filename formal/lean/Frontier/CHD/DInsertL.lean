import Frontier.CHD.DInsertA
import Frontier.CHD.DLazy

/-!
# DInsertL — `insertNS` is the state part of agent-04's `DL.insertL` (agent-02, NON-GATE)

`DL.insertL` runs DBlocks' `insert` with the parameter `bigM D`, so `fixBlock` never splits and
`addTo` prepends the new entry to the owning block — exactly `prependOwner`.  Hence the RAM
Insert (`DInsertB.insRAM_spec`, stated for `insertNS`) refines `DL.insertL`.
-/

namespace Frontier.CHD.DIns

open Frontier.CHD Frontier.CHD.DB

variable {κ : Type*} [DecidableEq κ] {α : Type*} [LinearOrder α] [Inhabited α]

/-- With a parameter large enough that no block splits, `addTo` is `prependOwner`. -/
theorem addTo_eq_prependOwner (T : ℕ) (L : Live κ α) (M : ℕ) (lam : α) (e : Entry κ α) :
    ∀ bs : List (Block κ α), (∀ c ∈ bs, c.ents.length + 1 ≤ 2 * M + 1) →
      (addTo T L M lam e bs).1 = prependOwner lam e bs
  | [], _ => rfl
  | [b], h => by
    simp only [addTo, prependOwner]
    rw [DL.fixBlock_small T (by simpa using h b (List.mem_singleton_self _))]
  | b :: b' :: bs, h => by
    simp only [addTo, prependOwner]
    split_ifs with hs
    · rw [addTo_eq_prependOwner T L M lam e (b' :: bs) (fun c hc => h c (List.mem_cons_of_mem _ hc))]
    · rw [DL.fixBlock_small T (by simpa using h b List.mem_cons_self)]
      rfl

/-- **Link**: the live map, the fresh counter and the structure produced by `DL.insertL` are
`insertNS`'s. -/
theorem insertL_eq_insertNS (L : Live κ α) (fresh : ℕ) (D : DStr κ α) (v : κ) (lam : α) :
    ((DL.insertL L fresh D v lam).1, (DL.insertL L fresh D v lam).2.1,
      (DL.insertL L fresh D v lam).2.2.1) = insertNS L fresh D v lam := by
  unfold DL.insertL DB.insert insertNS
  by_cases hs : skipIns L v lam = true
  · simp only [hs, if_true]
  · simp only [hs, Bool.false_eq_true, if_false]
    congr 2
    rw [addTo_eq_prependOwner 0 _ (DL.bigM D) lam _ D.blocks (fun c hc => by
      have := DL.length_le_allEnts hc; unfold DL.bigM; omega)]

end Frontier.CHD.DIns
