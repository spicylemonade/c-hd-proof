import Frontier.CHD.BL2Loop

/-!
# Frontier.CHD.BL2StepA — B-L2: Layer-A bookkeeping lemmas for the scan step (agent-09, scratch, NON-GATE)
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}

/-! ## Effects of `addNew` / `improve` on the fields -/

section Fields
variable (σ : SSt G s) (u : Fin G.n) (e : Fin G.m)
open Classical

theorem addNew_d : (addNew σ u e).d = relaxL σ.d u e := by
  unfold addNew; split_ifs with h
  · rfl
  · simp [relaxL, h]

theorem addNew_K : (addNew σ u e).K = σ.K ++ [G.dst e] := by
  unfold addNew; split_ifs <;> rfl

theorem addNew_D' : (addNew σ u e).D = σ.D := by
  unfold addNew; split_ifs <;> rfl

theorem addNew_kpar : (addNew σ u e).kpar = Function.update σ.kpar (G.dst e) u := by
  unfold addNew; split_ifs <;> rfl

theorem addNew_val : (addNew σ u e).val = if Ok σ.d u e then insert (G.dst e) σ.val else σ.val := by
  unfold addNew; split_ifs <;> rfl

theorem addNew_H : (addNew σ u e).H = if Ok σ.d u e then insert (G.dst e) σ.H else σ.H := by
  unfold addNew; split_ifs <;> rfl

theorem improve_d : (improve σ u e).d = relaxL σ.d u e := by
  unfold improve; split_ifs with h
  · rfl
  · simp [relaxL, h]

theorem improve_K : (improve σ u e).K = σ.K := by
  unfold improve; split_ifs <;> rfl

theorem improve_D' : (improve σ u e).D = σ.D := by
  unfold improve; split_ifs <;> rfl

theorem improve_kpar : (improve σ u e).kpar = σ.kpar := by
  unfold improve; split_ifs <;> rfl

theorem improve_val : (improve σ u e).val = if Ok σ.d u e then insert (G.dst e) σ.val else σ.val := by
  unfold improve; split_ifs <;> rfl

theorem improve_H : (improve σ u e).H = if Ok σ.d u e then insert (G.dst e) σ.H else σ.H := by
  unfold improve; split_ifs <;> rfl

end Fields

/-- `relaxL` never raises a label, so finiteness is kept. -/
theorem relaxL_ne_top {d : Labels G s} {u v : Fin G.n} {e : Fin G.m} (h : d v ≠ ⊤) :
    relaxL d u e v ≠ ⊤ :=
  ne_top_of_le_ne_top h (relaxL_le d u e v)

/-! ## Composing Layer-A scans -/

variable {c : FPCtx G s} {T : Finset (Fin G.n)} {u : Fin G.n}

/-- Extend the continuation by one non-terminal constructor behind deleted edges. -/
theorem cont_extend {σ₀ σ σ₁ : SSt G s} {n k : ℕ} {Ld L'' : List (Fin G.m)} {e : Fin G.m}
    (hcont : ∀ σ' r n', Scan c T u σ (Ld ++ e :: L'') σ' r n' → Scan c T u σ₀ (c.out u) σ' r (n + n'))
    (hLd : ∀ x ∈ Ld, x ∈ σ.D)
    (hk : ∀ σ' r n', Scan c T u σ₁ L'' σ' r n' → Scan c T u σ (e :: L'') σ' r (n' + k)) :
    ∀ σ' r n', Scan c T u σ₁ L'' σ' r n' → Scan c T u σ₀ (c.out u) σ' r (n + k + n') := by
  intro σ' r n' h
  have h1 := (Scan.append_dels Ld (e :: L'') hLd).mpr (hk σ' r n' h)
  have := hcont σ' r _ h1
  rwa [show n + (n' + k) = n + k + n' by omega] at this

/-- A terminal constructor behind deleted edges finishes the scan. -/
theorem cont_stop {σ₀ σ σ' : SSt G s} {n k : ℕ} {r : ScanRes} {Ld L'' : List (Fin G.m)}
    {e : Fin G.m}
    (hcont : ∀ σ' r n', Scan c T u σ (Ld ++ e :: L'') σ' r n' → Scan c T u σ₀ (c.out u) σ' r (n + n'))
    (hLd : ∀ x ∈ Ld, x ∈ σ.D) (hk : Scan c T u σ (e :: L'') σ' r k) :
    Scan c T u σ₀ (c.out u) σ' r (n + k) :=
  hcont σ' r k ((Scan.append_dels Ld (e :: L'') hLd).mpr hk)

/-- An exhausted live list finishes the scan with `cont` at no extra cost. -/
theorem cont_nil {σ₀ σ : SSt G s} {n : ℕ} {Lrem : List (Fin G.m)}
    (hcont : ∀ σ' r n', Scan c T u σ Lrem σ' r n' → Scan c T u σ₀ (c.out u) σ' r (n + n'))
    (hLd : ∀ x ∈ Lrem, x ∈ σ.D) : Scan c T u σ₀ (c.out u) σ .cont n := by
  have h0 : Scan c T u σ [] σ .cont 0 := Scan.nil σ
  have h1 : Scan c T u σ (Lrem ++ []) σ .cont 0 :=
    (Scan.append_dels (c := c) (T := T) (u := u) (σ := σ) (σ' := σ) (r := .cont) (n := 0)
      Lrem [] hLd).mpr h0
  rw [List.append_nil] at h1
  simpa using hcont σ .cont 0 h1

/-- Every element of a list with empty live part is deleted. -/
theorem all_dels_of_filter_nil {D : Finset (Fin G.m)} {L : List (Fin G.m)}
    (h : L.filter (fun e => e ∉ D) = []) : ∀ x ∈ L, x ∈ D := by
  intro x hx
  by_contra hxD
  have : x ∈ L.filter (fun e => e ∉ D) := List.mem_filter.mpr ⟨hx, by simpa using hxD⟩
  rw [h] at this
  exact List.not_mem_nil this

/-! ## From a cursor back to complete out-lists -/

theorem Cursor.toOutRep {st : State V} {D : Finset (Fin G.m)} {Lrem : List (Fin G.m)}
    (h : Cursor st c D u Lrem) : OutRep st c D := by
  obtain ⟨h1, h2, Pre, hPre, hs1, hs2, -⟩ := h
  refine ⟨h1, fun w => ?_⟩
  by_cases hw : w = u
  · subst hw
    have := hs1.append hs2
    rwa [← sl_append, ← List.filter_append, ← hPre] at this
  · exact h2 w hw

end Frontier.CHD.BL2
