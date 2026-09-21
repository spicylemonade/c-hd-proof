import Frontier.CHD.FPBind

/-!
# Frontier.CHD.FPWQ — `|W| ≤ k·|Q|` for FindPivots-HD (agent-07's F4; owner agent-03)

**NON-GATE** (Layer A).  `W` is the union of the valid parts of the FAILED searches; each failed search has
fewer than `k` members and its valid part lies among its members; distinct failed roots are distinct
(the root list is duplicate-free), so `|W| ≤ (k-1)·|Q|`.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-- The valid part of a search stays among its members. -/
theorem Scan.val_sub_K {c : FPCtx G s} {T : Finset (Fin G.n)} {u : Fin G.n} {σ σ' : SSt G s}
    {L : List (Fin G.m)} {r : ScanRes} {n : ℕ} (h : Scan c T u σ L σ' r n)
    (hv : ∀ v ∈ σ.val, v ∈ σ.K) : ∀ v ∈ σ'.val, v ∈ σ'.K := by
  classical
  induction h with
  | nil σ => exact hv
  | del σ σ' e L r n _ _ ih => exact ih hv
  | brk σ e L _ _ => exact hv
  | lxdel σ σ' e L r n _ _ _ _ ih => exact ih hv
  | contact σ e L _ _ _ _ => exact hv
  | newFull σ e L _ _ _ _ _ _ =>
    intro v hvv
    unfold addNew at hvv ⊢
    split_ifs at hvv ⊢ with hok
    · rcases Finset.mem_insert.mp hvv with rfl | h1
      · exact List.mem_append_right _ (List.mem_singleton_self _)
      · exact List.mem_append_left _ (hv v h1)
    · exact List.mem_append_left _ (hv v hvv)
  | newCont σ σ' e L r n _ _ _ _ _ _ _ ih =>
    refine ih ?_
    intro v hvv
    unfold addNew at hvv ⊢
    split_ifs at hvv ⊢ with hok
    · rcases Finset.mem_insert.mp hvv with rfl | h1
      · exact List.mem_append_right _ (List.mem_singleton_self _)
      · exact List.mem_append_left _ (hv v h1)
    · exact List.mem_append_left _ (hv v hvv)
  | inK σ σ' e L r n _ _ _ _ hK _ ih =>
    refine ih ?_
    intro v hvv
    unfold improve at hvv ⊢
    split_ifs at hvv ⊢ with hok
    · rcases Finset.mem_insert.mp hvv with rfl | h1
      · exact hK
      · exact hv v h1
    · exact hv v hvv

theorem Search.val_sub_K {c : FPCtx G s} {T : Finset (Fin G.n)} {σ σ' : SSt G s} {res : SearchRes} {n : ℕ}
    (h : Search c T σ σ' res n) (hv : ∀ v ∈ σ.val, v ∈ σ.K) : ∀ v ∈ σ'.val, v ∈ σ'.K := by
  induction h with
  | empty σ _ _ => exact hv
  | capped σ _ => exact hv
  | stepCont σ σ' σ'' u res n n' _ _ _ hscan _ ih => exact ih (Scan.val_sub_K hscan hv)
  | stepContact σ σ' u n _ _ _ hscan => exact Scan.val_sub_K hscan hv
  | stepFull σ σ' u n _ _ _ hscan => exact Scan.val_sub_K hscan hv

/-- A failed search ends with fewer than `k` members. -/
theorem Search.failed_K {c : FPCtx G s} {T : Finset (Fin G.n)} {σ σ' : SSt G s} {res : SearchRes} {n : ℕ}
    (h : Search c T σ σ' res n) (hres : res = .failed) : σ'.K.length < c.k := by
  induction h with
  | empty σ _ hk => exact hk
  | capped σ _ => cases hres
  | stepCont σ σ' σ'' u res n n' _ _ _ _ _ ih => exact ih hres
  | stepContact σ σ' u n _ _ _ _ => cases hres
  | stepFull σ σ' u n _ _ _ _ => cases hres

/-- **`|W|` grows by less than `k` per failed root.** -/
theorem Invoke.W_card {c : FPCtx G s} {ι ι' : IState G s} {L : List (Fin G.n)} {n : ℕ}
    (h : Invoke c ι L ι' n) (hnd : L.Nodup) (hLQ : ∀ x ∈ L, x ∉ ι.Q) :
    ι'.W.card + (c.k - 1) * ι.Q.card ≤ ι.W.card + (c.k - 1) * ι'.Q.card ∧ ι.Q ⊆ ι'.Q := by
  classical
  induction h with
  | nil ι => exact ⟨le_rfl, subset_rfl⟩
  | skip ι ι' x L n _ _ ih =>
    exact ih (List.nodup_cons.mp hnd).2 (fun y hy => hLQ y (List.mem_cons_of_mem _ hy))
  | fail ι ι' x L σ' n n' _ hs _ ih =>
    have hxQ : x ∉ ι.Q := hLQ x List.mem_cons_self
    have hnd' := List.nodup_cons.mp hnd
    obtain ⟨h1, h2⟩ := ih hnd'.2 (by
      intro y hy
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun h => hnd'.1 (h ▸ hy), hLQ y (List.mem_cons_of_mem _ hy)⟩)
    have hK := Search.failed_K hs rfl
    have hvK := Search.val_sub_K hs (by
      intro v hv; simp only [initSt, Finset.mem_singleton] at hv; subst hv; simp [initSt])
    have hval : σ'.val.card ≤ σ'.K.length :=
      (Finset.card_le_card (fun v hv => List.mem_toFinset.mpr (hvK v hv))).trans (List.toFinset_card_le _)
    have hW : (ι.W ∪ σ'.val).card ≤ ι.W.card + σ'.val.card := Finset.card_union_le _ _
    have hQ : (insert x ι.Q).card = ι.Q.card + 1 := Finset.card_insert_of_notMem hxQ
    dsimp only at h1 h2
    refine ⟨?_, (Finset.subset_insert _ _).trans h2⟩
    have e : (c.k - 1) * (insert x ι.Q).card = (c.k - 1) * ι.Q.card + (c.k - 1) := by rw [hQ, Nat.mul_succ]
    omega
  | grow ι ι' x L σ' res n n' _ _ _ _ ih =>
    exact ih (List.nodup_cons.mp hnd).2 (fun y hy => hLQ y (List.mem_cons_of_mem _ hy))

variable {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}

/-- **`|W| ≤ k·|Q|`** for the cost-indexed FindPivots relation (agent-07's F4). -/
theorem fpC_W_card {l : ℕ} {Blow B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s}
    {Din Dout : Finset (Fin G.m)} {p : ℕ} {P : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)}
    {ω : FPData G s} {c : ℕ} (h : fpC G s out k hins hext l Blow B S d0 Din d1 p P Q W Dout ω c) :
    W.card ≤ k * Q.card := by
  obtain ⟨⟨SL, ι', hnd, -, hrun, -, -, rfl, rfl, -, -⟩, -⟩ := h
  have := (Invoke.W_card hrun hnd (fun x _ => Finset.notMem_empty x)).1
  simp only [Finset.card_empty, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at this
  have hk : (pinCtx out k hins hext B (lxOf B S d0)).k = k := rfl
  rw [hk] at this
  calc ι'.W.card ≤ (k - 1) * ι'.Q.card := this
    _ ≤ k * ι'.Q.card := Nat.mul_le_mul_right _ (Nat.sub_le _ _)

end CHD
end Frontier
