import Frontier.CHD.DRekey

/-!
# KeyLists — per-level circular doubly-linked lists of live keys (B-L3, agent-04, NON-GATE)

The `D` layer keeps, for every active level `j`, a circular doubly-linked list (arrays `lk.n`,
`lk.p`, sentinel node `N + j`) of the keys having a live entry in the level-`j` structure.  A
node in no list is a self-loop.  Unlinking a node needs no knowledge of its list, splicing two
lists is `O(1)`, and the emptiness of a level is one sentinel test — this gives the spine's
`O(1)` emptiness test of `view(D_l)`.

This file: the pure list theory over the pointer functions `n p : ℕ → ℕ`.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.KL

/-- consecutive nodes of the list are doubly linked -/
def DL (n p : ℕ → ℕ) : List ℕ → Prop
  | x :: y :: rest => n x = y ∧ p y = x ∧ DL n p (y :: rest)
  | _ => True

/-- a circular doubly-linked list with sentinel `s` and members `ns` (in order) -/
def CL (n p : ℕ → ℕ) (s : ℕ) (ns : List ℕ) : Prop := DL n p (s :: ns ++ [s]) ∧ (s :: ns).Nodup

section pure

variable {n p n' p' : ℕ → ℕ}

@[simp] theorem DL_nil : DL n p [] := trivial
@[simp] theorem DL_single (x : ℕ) : DL n p [x] := trivial
@[simp] theorem DL_cons_cons (x y : ℕ) (rest : List ℕ) :
    DL n p (x :: y :: rest) ↔ n x = y ∧ p y = x ∧ DL n p (y :: rest) := Iff.rfl

theorem DL_tail {x : ℕ} {L : List ℕ} (h : DL n p (x :: L)) : DL n p L := by
  cases L with
  | nil => trivial
  | cons y rest => exact h.2.2

theorem DL_append (x : ℕ) (B : List ℕ) :
    ∀ A : List ℕ, DL n p (A ++ x :: B) ↔ DL n p (A ++ [x]) ∧ DL n p (x :: B)
  | [] => by simp
  | [a] => by simp [and_assoc]
  | a :: a' :: A => by
      have ih := DL_append x B (a' :: A)
      simp only [List.cons_append] at ih ⊢
      rw [DL_cons_cons, DL_cons_cons, ih]
      tauto

/-- frame: `DL` reads `n` on all nodes but the last and `p` on all nodes but the first -/
theorem DL_frame : ∀ {L : List ℕ}, DL n p L → (∀ x ∈ L.dropLast, n' x = n x) →
    (∀ x ∈ L.tail, p' x = p x) → DL n' p' L
  | [], _, _, _ => trivial
  | [_], _, _, _ => trivial
  | x :: y :: rest, h, hn, hp => by
      obtain ⟨h1, h2, h3⟩ := h
      refine ⟨by rw [hn x (by simp)]; exact h1, by rw [hp y (by simp)]; exact h2, ?_⟩
      refine DL_frame h3 (fun z hz => hn z ?_) (fun z hz => hp z ?_)
      · rw [List.dropLast_cons_cons]; exact List.mem_cons_of_mem _ hz
      · simp only [List.tail_cons] at hz ⊢; exact List.mem_cons_of_mem _ hz

theorem DL_frame' {L : List ℕ} (h : DL n p L) (hf : ∀ x ∈ L, n' x = n x ∧ p' x = p x) :
    DL n' p' L :=
  DL_frame h (fun x hx => (hf x (List.dropLast_subset _ hx)).1)
    (fun x hx => (hf x (List.tail_subset _ hx)).2)

theorem CL_frame {s : ℕ} {ns : List ℕ} (h : CL n p s ns)
    (hf : ∀ x ∈ s :: ns, n' x = n x ∧ p' x = p x) : CL n' p' s ns := by
  refine ⟨DL_frame' h.1 (fun x hx => hf x ?_), h.2⟩
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_singleton] at hx ⊢
  tauto

theorem CL_nil_iff {s : ℕ} : CL n p s [] ↔ n s = s ∧ p s = s := by
  simp [CL, DL]

theorem CL_empty_iff {s : ℕ} {ns : List ℕ} (h : CL n p s ns) : n s = s ↔ ns = [] := by
  cases ns with
  | nil => simp only [iff_true]; exact (CL_nil_iff.mp h).1
  | cons y rest =>
    simp only [reduceCtorEq, iff_false]
    obtain ⟨hd, hnd⟩ := h
    have h1 : n s = y := hd.1
    have hsy : s ≠ y := by intro e; subst e; simp at hnd
    rw [h1]; exact fun e => hsy e.symm

/-- the members of a nonempty list start at `n s` and end at `p s` -/
theorem CL_first {s : ℕ} {ns : List ℕ} (h : CL n p s ns) (hne : ns ≠ []) :
    n s = ns.head hne := by
  cases ns with
  | nil => exact absurd rfl hne
  | cons y rest => exact h.1.1

theorem CL_last {s : ℕ} {ns : List ℕ} (h : CL n p s ns) (hne : ns ≠ []) :
    p s = ns.getLast hne := by
  obtain ⟨hd, -⟩ := h
  have e : s :: ns ++ [s] = (s :: ns.dropLast) ++ ns.getLast hne :: [s] := by
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    simp
  rw [e, DL_append] at hd
  exact hd.2.2.1

theorem nd_seg {s v : ℕ} {A B : List ℕ} (h : (s :: (A ++ v :: B)).Nodup) :
    s ∉ A ∧ s ≠ v ∧ s ∉ B ∧ v ∉ A ∧ v ∉ B ∧ (∀ x ∈ A, x ∉ B) ∧ A.Nodup ∧ B.Nodup := by
  rw [List.nodup_cons] at h
  obtain ⟨hs, h⟩ := h
  have hd := List.disjoint_of_nodup_append h
  have hA := h.of_append_left
  have hvB := h.of_append_right
  rw [List.nodup_cons] at hvB
  simp only [List.mem_append, List.mem_cons, not_or] at hs
  exact ⟨hs.1, hs.2.1, hs.2.2, fun hv => hd hv List.mem_cons_self, hvB.1,
    fun x hx hxB => hd hx (List.mem_cons_of_mem _ hxB), hA, hvB.2⟩

theorem upd_ne {f : ℕ → ℕ} {a b x : ℕ} (h : x ≠ a) : Function.update f a b x = f x :=
  Function.update_of_ne h _ _

/-- unlinking a member `v` -/
theorem CL_unlink {s v : ℕ} {ns : List ℕ} (h : CL n p s ns) (hv : v ∈ ns) :
    CL (Function.update (Function.update n (p v) (n v)) v v)
      (Function.update (Function.update p (n v) (p v)) v v) s (ns.erase v) ∧
    p v ∈ s :: ns ∧ n v ∈ s :: ns ∧ p v ≠ v ∧ n v ≠ v := by
  obtain ⟨hd, hnd⟩ := h
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hv
  obtain ⟨hsA, hsv, hsB, hvA, hvB, hAB, hAn, hBn⟩ := nd_seg hnd
  obtain ⟨A0, a, hA⟩ : ∃ A0 a, s :: A = A0 ++ [a] :=
    ⟨(s :: A).dropLast, (s :: A).getLast (List.cons_ne_nil _ _),
      (List.dropLast_append_getLast _).symm⟩
  obtain ⟨b, B0, hB⟩ : ∃ b B0, B ++ [s] = b :: B0 := by
    cases B with
    | nil => exact ⟨s, [], rfl⟩
    | cons b B' => exact ⟨b, B' ++ [s], rfl⟩
  have e1 : s :: (A ++ v :: B) ++ [s] = (s :: A) ++ v :: (B ++ [s]) := by simp
  rw [e1, DL_append] at hd
  obtain ⟨hdA, hdB⟩ := hd
  rw [hA, List.append_assoc, List.singleton_append, DL_append] at hdA
  obtain ⟨hdA0, hna, hpv, -⟩ := hdA
  rw [hB] at hdB
  obtain ⟨hnv, hpb, hdB0⟩ := hdB
  -- facts about the neighbours
  have hsAnd : (s :: A).Nodup :=
    ((List.sublist_append_left A (v :: B)).cons_cons s).nodup hnd
  have hBsnd : (B ++ [s]).Nodup :=
    (List.perm_append_singleton s B).nodup_iff.mpr
      (List.nodup_cons.mpr ⟨hsB, hBn⟩)
  have haA : a ∈ s :: A := by rw [hA]; simp
  have hbB : b ∈ B ++ [s] := by rw [hB]; simp
  have hav : a ≠ v := by
    intro e; subst e
    simp only [List.mem_cons] at haA
    rcases haA with h' | h'
    · exact hsv h'.symm
    · exact hvA h'
  have hbv : b ≠ v := by
    intro e; subst e
    simp only [List.mem_append, List.mem_singleton] at hbB
    rcases hbB with h' | h'
    · exact hvB h'
    · exact hsv h'.symm
  have haA0 : a ∉ A0 := by
    rw [hA] at hsAnd
    exact fun h' => List.disjoint_of_nodup_append hsAnd h' (List.mem_singleton_self a)
  have hbB0 : b ∉ B0 := by
    rw [hB] at hBsnd
    exact (List.nodup_cons.mp hBsnd).1
  rw [hpv, hnv]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, hav, hbv⟩
  · rw [List.erase_append_right _ hvA, List.erase_cons_head]
    have e2 : s :: (A ++ B) ++ [s] = A0 ++ a :: b :: B0 := by
      rw [show s :: (A ++ B) ++ [s] = (s :: A) ++ (B ++ [s]) by simp, hA, hB]; simp
    rw [e2, DL_append]
    refine ⟨DL_frame hdA0 (fun x hx => ?_) (fun x hx => ?_), ?_, ?_, ?_⟩
    · rw [List.dropLast_concat] at hx
      have hxa : x ≠ a := fun e => haA0 (e ▸ hx)
      have hxv : x ≠ v := by
        intro e; subst e
        have : x ∈ s :: A := by rw [hA]; exact List.mem_append_left _ hx
        simp only [List.mem_cons] at this
        rcases this with h' | h'
        · exact hsv h'.symm
        · exact hvA h'
      rw [upd_ne hxv, upd_ne hxa]
    · have hxA : x ∈ A := by
        have : (A0 ++ [a]).tail = A := by rw [← hA]; rfl
        rw [this] at hx; exact hx
      have hxv : x ≠ v := fun e => hvA (e ▸ hxA)
      have hxb : x ≠ b := by
        intro e; subst e
        simp only [List.mem_append, List.mem_singleton] at hbB
        rcases hbB with h' | h'
        · exact hAB x hxA h'
        · exact hsA (h' ▸ hxA)
      rw [upd_ne hxv, upd_ne hxb]
    · rw [upd_ne hav]; simp
    · rw [upd_ne hbv]; simp
    · refine DL_frame hdB0 (fun x hx => ?_) (fun x hx => ?_)
      · have hxB : x ∈ B := by
          have : (b :: B0).dropLast = B := by rw [← hB]; simp
          rw [this] at hx; exact hx
        have hxv : x ≠ v := fun e => hvB (e ▸ hxB)
        have hxa : x ≠ a := by
          intro e; subst e
          simp only [List.mem_cons] at haA
          rcases haA with h' | h'
          · exact hsB (h' ▸ hxB)
          · exact hAB x h' hxB
        rw [upd_ne hxv, upd_ne hxa]
      · have hxb : x ≠ b := fun e => hbB0 (e ▸ hx)
        have hxv : x ≠ v := by
          intro e; subst e
          have : x ∈ B ++ [s] := by rw [hB]; exact List.mem_cons_of_mem _ hx
          simp only [List.mem_append, List.mem_singleton] at this
          rcases this with h' | h'
          · exact hvB h'
          · exact hsv h'.symm
        rw [upd_ne hxv, upd_ne hxb]
  · have : List.Sublist (s :: (A ++ B)) (s :: (A ++ v :: B)) :=
      ((List.sublist_cons_self v B).append_left A).cons_cons s
    rw [List.erase_append_right _ hvA, List.erase_cons_head]
    exact this.nodup hnd
  · simp only [List.mem_cons] at haA
    simp only [List.mem_cons, List.mem_append]
    tauto
  · simp only [List.mem_append, List.mem_singleton] at hbB
    simp only [List.mem_cons, List.mem_append]
    tauto

/-- linking a new node `v` right after the sentinel -/
theorem CL_link {s v : ℕ} {ns : List ℕ} (h : CL n p s ns) (hv : v ∉ s :: ns) :
    CL (Function.update (Function.update n v (n s)) s v)
      (Function.update (Function.update p v s) (n s) v) s (v :: ns) ∧ n s ∈ s :: ns := by
  obtain ⟨hd, hnd⟩ := h
  obtain ⟨t, R, hR⟩ : ∃ t R, ns ++ [s] = t :: R := by
    cases ns with
    | nil => exact ⟨s, [], rfl⟩
    | cons t ns' => exact ⟨t, ns' ++ [s], rfl⟩
  have hd' : DL n p (s :: t :: R) := by rw [← hR]; simpa using hd
  obtain ⟨hns, hpt, hdR⟩ := hd'
  simp only [List.mem_cons, not_or] at hv
  obtain ⟨hvs, hvns⟩ := hv
  have hsns := (List.nodup_cons.mp hnd).1
  have hnsnd := (List.nodup_cons.mp hnd).2
  have hRnd : (t :: R).Nodup := by
    rw [← hR]
    exact (List.perm_append_singleton s ns).nodup_iff.mpr hnd
  have htmem : t ∈ ns ++ [s] := by rw [hR]; simp
  have hvt : v ≠ t := by
    intro e; subst e
    simp only [List.mem_append, List.mem_singleton] at htmem
    rcases htmem with h' | h'
    · exact hvns h'
    · exact hvs h'
  rw [hns]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have e : s :: (v :: ns) ++ [s] = s :: v :: t :: R := by rw [List.cons_append, List.cons_append, hR]
    rw [e]
    refine ⟨by simp, ?_, ?_, ?_, ?_⟩
    · rw [upd_ne hvt]; simp
    · rw [upd_ne hvs]; simp
    · simp
    · refine DL_frame hdR (fun x hx => ?_) (fun x hx => ?_)
      · have hx' : x ∈ ns := by
          have : (t :: R).dropLast = ns := by rw [← hR]; simp
          rw [this] at hx; exact hx
        have hxs : x ≠ s := fun e => hsns (e ▸ hx')
        have hxv : x ≠ v := fun e => hvns (e ▸ hx')
        rw [upd_ne hxs, upd_ne hxv]
      · have hxt : x ≠ t := fun e => (List.nodup_cons.mp hRnd).1 (e ▸ hx)
        have hxv : x ≠ v := by
          intro e; subst e
          have : x ∈ ns ++ [s] := by rw [hR]; exact List.mem_cons_of_mem _ hx
          simp only [List.mem_append, List.mem_singleton] at this
          rcases this with h' | h'
          · exact hvns h'
          · exact hvs h'
        rw [upd_ne hxt, upd_ne hxv]
  · simp only [List.nodup_cons, List.mem_cons, not_or]
    exact ⟨⟨fun e => hvs e.symm, hsns⟩, hvns, hnsnd⟩
  · rw [← hns]; rw [hns]
    simp only [List.mem_append, List.mem_singleton] at htmem
    simp only [List.mem_cons]
    tauto

/-- splicing the (nonempty) list of sentinel `c` in front of the list of sentinel `s` -/
theorem CL_splice {c s : ℕ} {nc ns : List ℕ} (hc : CL n p c nc) (hs : CL n p s ns) (hne : nc ≠ [])
    (hdisj : ∀ x ∈ c :: nc, x ∉ s :: ns) :
    CL (Function.update (Function.update (Function.update n s (n c)) (p c) (n s)) c c)
      (Function.update (Function.update (Function.update p (n c) s) (n s) (p c)) c c) s (nc ++ ns) ∧
    n c ∈ nc ∧ p c ∈ nc ∧ n s ∈ s :: ns := by
  have hf := CL_first hc hne
  have hl := CL_last hc hne
  obtain ⟨hdc, hndc⟩ := hc
  obtain ⟨hds, hnds⟩ := hs
  obtain ⟨f, nc1, hnc1⟩ : ∃ f nc1, nc = f :: nc1 := by
    cases nc with
    | nil => exact absurd rfl hne
    | cons f nc1 => exact ⟨f, nc1, rfl⟩
  obtain ⟨nc0, l, hnc0⟩ : ∃ nc0 l, nc = nc0 ++ [l] :=
    ⟨nc.dropLast, nc.getLast hne, (List.dropLast_append_getLast hne).symm⟩
  have hfv : n c = f := by rw [hf]; subst hnc1; rfl
  have hlv : p c = l := by rw [hl]; simp [hnc0]
  obtain ⟨t, R, hR⟩ : ∃ t R, ns ++ [s] = t :: R := by
    cases ns with
    | nil => exact ⟨s, [], rfl⟩
    | cons t ns' => exact ⟨t, ns' ++ [s], rfl⟩
  have hds' : DL n p (s :: t :: R) := by rw [← hR]; simpa using hds
  obtain ⟨hnsv, -, hdR⟩ := hds'
  -- the inner path of the child list
  have hdnc : DL n p nc := by
    have e : c :: nc ++ [c] = (c :: nc0) ++ l :: [c] := by rw [hnc0]; simp
    rw [e, DL_append] at hdc
    have : DL n p (c :: nc0 ++ [l]) := hdc.1
    rw [List.cons_append, ← hnc0] at this
    exact DL_tail this
  -- disjointness facts
  have hcnc := (List.nodup_cons.mp hndc).1
  have hncnd := (List.nodup_cons.mp hndc).2
  have hsns := (List.nodup_cons.mp hnds).1
  have hnsnd := (List.nodup_cons.mp hnds).2
  have hfmem : f ∈ nc := by rw [hnc1]; simp
  have hlmem : l ∈ nc := by rw [hnc0]; simp
  have htmem : t ∈ s :: ns := by
    have : t ∈ ns ++ [s] := by rw [hR]; simp
    simp only [List.mem_append, List.mem_singleton] at this
    simp only [List.mem_cons]; tauto
  have hD : ∀ x ∈ nc, ∀ y ∈ s :: ns, x ≠ y := fun x hx y hy e =>
    hdisj x (List.mem_cons_of_mem _ hx) (e ▸ hy)
  have hcS : ∀ y ∈ s :: ns, c ≠ y := fun y hy e => hdisj c List.mem_cons_self (e ▸ hy)
  have hsc : s ≠ c := fun e => hcS s List.mem_cons_self e.symm
  have hsl : s ≠ l := fun e => hD l hlmem s List.mem_cons_self e.symm
  have hfc : f ≠ c := fun e => hcnc (e ▸ hfmem)
  have hft : f ≠ t := hD f hfmem t htmem
  have hlc : l ≠ c := fun e => hcnc (e ▸ hlmem)
  have htc : t ≠ c := fun e => hcS t htmem e.symm
  have hRnd : (t :: R).Nodup := by
    rw [← hR]; exact (List.perm_append_singleton s ns).nodup_iff.mpr hnds
  rw [hfv, hlv, hnsv]
  refine ⟨⟨?_, ?_⟩, hfmem, hlmem, htmem⟩
  · have e : s :: (nc ++ ns) ++ [s] = (s :: nc) ++ t :: R := by
      rw [List.cons_append, List.append_assoc, hR]; rfl
    rw [e, DL_append]
    refine ⟨?_, ?_⟩
    · have e2 : s :: nc ++ [t] = s :: f :: (nc1 ++ [t]) := by rw [hnc1]; rfl
      rw [e2]
      refine ⟨by rw [upd_ne hsc, upd_ne hsl]; simp, by rw [upd_ne hfc, upd_ne hft]; simp, ?_⟩
      have e3 : f :: (nc1 ++ [t]) = nc0 ++ l :: [t] := by
        rw [← List.cons_append, ← hnc1, hnc0]; simp
      rw [e3, DL_append]
      refine ⟨?_, by rw [upd_ne hlc]; simp, by rw [upd_ne htc]; simp, trivial⟩
      rw [← hnc0]
      refine DL_frame hdnc (fun x hx => ?_) (fun x hx => ?_)
      · have hxnc : x ∈ nc := List.dropLast_subset _ hx
        have hxc : x ≠ c := fun e => hcnc (e ▸ hxnc)
        have hxl : x ≠ l := by
          intro e; subst e
          rw [hnc0, List.dropLast_concat] at hx
          have := hncnd; rw [hnc0] at this
          exact List.disjoint_of_nodup_append this hx (List.mem_singleton_self x)
        have hxs : x ≠ s := hD x hxnc s List.mem_cons_self
        rw [upd_ne hxc, upd_ne hxl, upd_ne hxs]
      · have hxnc : x ∈ nc := List.tail_subset _ hx
        have hxc : x ≠ c := fun e => hcnc (e ▸ hxnc)
        have hxf : x ≠ f := by
          intro e; subst e
          rw [hnc1] at hx hncnd
          exact (List.nodup_cons.mp hncnd).1 hx
        have hxt : x ≠ t := hD x hxnc t htmem
        rw [upd_ne hxc, upd_ne hxt, upd_ne hxf]
    · refine DL_frame hdR (fun x hx => ?_) (fun x hx => ?_)
      · have hx' : x ∈ ns := by
          have : (t :: R).dropLast = ns := by rw [← hR]; simp
          rw [this] at hx; exact hx
        have hxS : x ∈ s :: ns := List.mem_cons_of_mem _ hx'
        have hxc : x ≠ c := fun e => hcS x hxS e.symm
        have hxl : x ≠ l := fun e => hD l hlmem x hxS e.symm
        have hxs : x ≠ s := fun e => hsns (e ▸ hx')
        rw [upd_ne hxc, upd_ne hxl, upd_ne hxs]
      · have hxS : x ∈ s :: ns := by
          have : x ∈ ns ++ [s] := by rw [hR]; exact List.mem_cons_of_mem _ hx
          simp only [List.mem_append, List.mem_singleton] at this
          simp only [List.mem_cons]; tauto
        have hxc : x ≠ c := fun e => hcS x hxS e.symm
        have hxt : x ≠ t := fun e => (List.nodup_cons.mp hRnd).1 (e ▸ hx)
        have hxf : x ≠ f := fun e => hD f hfmem x hxS e.symm
        rw [upd_ne hxc, upd_ne hxt, upd_ne hxf]
  · refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · simp only [List.mem_append, not_or]
      exact ⟨fun h' => hD s h' s List.mem_cons_self rfl, hsns⟩
    · exact hncnd.append hnsnd (fun x hx hy => hD x hx x (List.mem_cons_of_mem _ hy) rfl)

end pure

/-! ## The family of lists of the active levels -/

/-- the live-key lists of the active levels `lo..top` (sentinel of level `j` = `N + j`) -/
structure LL (n p : ℕ → ℕ) (N lo top : ℕ) (K : ℕ → List ℕ) : Prop where
  cl : ∀ j, lo ≤ j → j ≤ top → CL n p (N + j) (K j)
  lt : ∀ j, lo ≤ j → j ≤ top → ∀ x ∈ K j, x < N
  disj : ∀ i j, lo ≤ i → i ≤ top → lo ≤ j → j ≤ top → i ≠ j → ∀ x ∈ K i, x ∉ K j
  self : ∀ v, v < N → (∀ j, lo ≤ j → j ≤ top → v ∉ K j) → n v = v ∧ p v = v

section family

variable {n p : ℕ → ℕ} {N lo top : ℕ} {K : ℕ → List ℕ}

theorem LL.congr {K' : ℕ → List ℕ} (h : LL n p N lo top K)
    (hK : ∀ j, lo ≤ j → j ≤ top → K' j = K j) : LL n p N lo top K' := by
  refine ⟨fun j h1 h2 => by rw [hK j h1 h2]; exact h.cl j h1 h2,
    fun j h1 h2 x hx => h.lt j h1 h2 x (by rw [← hK j h1 h2]; exact hx),
    fun i j hi1 hi2 hj1 hj2 hij x hx hx' => h.disj i j hi1 hi2 hj1 hj2 hij x
      (by rw [← hK i hi1 hi2]; exact hx) (by rw [← hK j hj1 hj2]; exact hx'),
    fun v hv hf => h.self v hv (fun j h1 h2 hv' => hf j h1 h2 (by rw [hK j h1 h2]; exact hv'))⟩

/-- the cycles (sentinel + members) of two different active levels are disjoint -/
theorem LL.cyc_disj (h : LL n p N lo top K) {i j : ℕ} (hi1 : lo ≤ i) (hi2 : i ≤ top)
    (hj1 : lo ≤ j) (hj2 : j ≤ top) (hij : i ≠ j) : ∀ x ∈ (N + i) :: K i, x ∉ (N + j) :: K j := by
  intro x hx hx'
  simp only [List.mem_cons] at hx hx'
  rcases hx with rfl | hx <;> rcases hx' with h' | h'
  · omega
  · have := h.lt j hj1 hj2 _ h'; omega
  · have := h.lt i hi1 hi2 _ hx; omega
  · exact h.disj i j hi1 hi2 hj1 hj2 hij x hx h'

theorem LL.cyc_lt (h : LL n p N lo top K) {j : ℕ} (hj1 : lo ≤ j) (hj2 : j ≤ top) :
    ∀ x ∈ (N + j) :: K j, x < N + top + 1 := by
  intro x hx
  simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · omega
  · have := h.lt j hj1 hj2 x hx; omega

/-- the neighbours of a node are nodes -/
theorem LL.nbr (h : LL n p N lo top K) {v : ℕ} (hv : v < N) :
    p v < N + top + 1 ∧ n v < N + top + 1 := by
  by_cases hin : ∃ j, lo ≤ j ∧ j ≤ top ∧ v ∈ K j
  · obtain ⟨j, hj1, hj2, hvj⟩ := hin
    obtain ⟨-, hpm, hnm, -, -⟩ := CL_unlink (h.cl j hj1 hj2) hvj
    exact ⟨h.cyc_lt hj1 hj2 _ hpm, h.cyc_lt hj1 hj2 _ hnm⟩
  · have hf : ∀ j, lo ≤ j → j ≤ top → v ∉ K j := fun j h1 h2 hv' => hin ⟨j, h1, h2, hv'⟩
    obtain ⟨e1, e2⟩ := h.self v hv hf
    rw [e1, e2]; omega

theorem LL.empty_iff (h : LL n p N lo top K) {j : ℕ} (hj1 : lo ≤ j) (hj2 : j ≤ top) :
    n (N + j) = N + j ↔ K j = [] := CL_empty_iff (h.cl j hj1 hj2)

/-- **unlink** a node (a member of some list, or a self-loop) -/
theorem LL.unlink (h : LL n p N lo top K) {v : ℕ} (hv : v < N) :
    LL (Function.update (Function.update n (p v) (n v)) v v)
      (Function.update (Function.update p (n v) (p v)) v v) N lo top (fun j => (K j).erase v) := by
  by_cases hin : ∃ j, lo ≤ j ∧ j ≤ top ∧ v ∈ K j
  · obtain ⟨j, hj1, hj2, hvj⟩ := hin
    obtain ⟨hCL, hpm, hnm, hpv, hnv⟩ := CL_unlink (h.cl j hj1 hj2) hvj
    have hvc : v ∈ (N + j) :: K j := List.mem_cons_of_mem _ hvj
    refine ⟨fun i hi1 hi2 => ?_, fun i hi1 hi2 x hx => h.lt i hi1 hi2 x (List.mem_of_mem_erase hx),
      fun i i' hi1 hi2 hi1' hi2' hii x hx hx' => h.disj i i' hi1 hi2 hi1' hi2' hii x
        (List.mem_of_mem_erase hx) (List.mem_of_mem_erase hx'), fun w hw hf => ?_⟩
    · by_cases hij : i = j
      · subst hij; exact hCL
      · have hvi : v ∉ K i := fun h' => h.disj j i hj1 hj2 hi1 hi2 (Ne.symm hij) v hvj h'
        show CL _ _ (N + i) ((K i).erase v)
        rw [List.erase_of_not_mem hvi]
        refine CL_frame (h.cl i hi1 hi2) (fun x hx => ?_)
        have hxc := h.cyc_disj hi1 hi2 hj1 hj2 hij x hx
        have hxpv : x ≠ p v := fun e => hxc (e ▸ hpm)
        have hxnv : x ≠ n v := fun e => hxc (e ▸ hnm)
        have hxv : x ≠ v := fun e => hxc (e ▸ hvc)
        exact ⟨by rw [upd_ne hxv, upd_ne hxpv], by rw [upd_ne hxv, upd_ne hxnv]⟩
    · by_cases hwv : w = v
      · subst hwv; simp
      · have hf' : ∀ i, lo ≤ i → i ≤ top → w ∉ K i := fun i hi1 hi2 hw' =>
          hf i hi1 hi2 ((List.mem_erase_of_ne hwv).mpr hw')
        obtain ⟨e1, e2⟩ := h.self w hw hf'
        have hwc : w ∉ (N + j) :: K j := by
          simp only [List.mem_cons, not_or]; exact ⟨by omega, hf' j hj1 hj2⟩
        exact ⟨by rw [upd_ne hwv, upd_ne (show w ≠ p v from fun e => hwc (e ▸ hpm))]; exact e1,
          by rw [upd_ne hwv, upd_ne (show w ≠ n v from fun e => hwc (e ▸ hnm))]; exact e2⟩
  · have hf : ∀ j, lo ≤ j → j ≤ top → v ∉ K j := fun j h1 h2 hv' => hin ⟨j, h1, h2, hv'⟩
    obtain ⟨e1, e2⟩ := h.self v hv hf
    have hn : Function.update (Function.update n (p v) (n v)) v v = n := by
      rw [e1, e2]; funext x; by_cases hx : x = v
      · subst hx; simp [e1]
      · simp [Function.update_apply, hx]
    have hp : Function.update (Function.update p (n v) (p v)) v v = p := by
      rw [e1, e2]; funext x; by_cases hx : x = v
      · subst hx; simp [e2]
      · simp [Function.update_apply, hx]
    rw [hn, hp]
    exact h.congr (fun j h1 h2 => List.erase_of_not_mem (hf j h1 h2))

/-- **link** a free node at the front of the list of level `j` -/
theorem LL.link (h : LL n p N lo top K) {v j : ℕ} (hv : v < N)
    (hfree : ∀ i, lo ≤ i → i ≤ top → v ∉ K i) (hj1 : lo ≤ j) (hj2 : j ≤ top) :
    LL (Function.update (Function.update n v (n (N + j))) (N + j) v)
      (Function.update (Function.update p v (N + j)) (n (N + j)) v) N lo top
      (Function.update K j (v :: K j)) := by
  have hvc : v ∉ (N + j) :: K j := by
    simp only [List.mem_cons, not_or]; exact ⟨by omega, hfree j hj1 hj2⟩
  obtain ⟨hCL, htm⟩ := CL_link (h.cl j hj1 hj2) hvc
  refine ⟨fun i hi1 hi2 => ?_, fun i hi1 hi2 x hx => ?_, fun i i' hi1 hi2 hi1' hi2' hii x hx hx' => ?_,
    fun w hw hf => ?_⟩
  · by_cases hij : i = j
    · subst hij; simpa using hCL
    · rw [Function.update_of_ne hij]
      refine CL_frame (h.cl i hi1 hi2) (fun x hx => ?_)
      have hxc := h.cyc_disj hi1 hi2 hj1 hj2 hij x hx
      have hxs : x ≠ N + j := fun e => hxc (e ▸ List.mem_cons_self)
      have hxt : x ≠ n (N + j) := fun e => hxc (e ▸ htm)
      have hxv : x ≠ v := by
        intro e; subst e
        simp only [List.mem_cons] at hx
        rcases hx with h' | h'
        · omega
        · exact hfree i hi1 hi2 h'
      exact ⟨by rw [upd_ne hxs, upd_ne hxv], by rw [upd_ne hxt, upd_ne hxv]⟩
  · by_cases hij : i = j
    · subst hij
      simp only [Function.update_self, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hv
      · exact h.lt i hi1 hi2 x hx
    · rw [Function.update_of_ne hij] at hx; exact h.lt i hi1 hi2 x hx
  · by_cases hij : i = j
    · subst hij
      rw [Function.update_of_ne (Ne.symm hii)] at hx'
      simp only [Function.update_self, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hfree i' hi1' hi2' hx'
      · exact h.disj i i' hi1 hi2 hi1' hi2' hii x hx hx'
    · rw [Function.update_of_ne hij] at hx
      by_cases hij' : i' = j
      · subst hij'
        simp only [Function.update_self, List.mem_cons] at hx'
        rcases hx' with rfl | hx'
        · exact hfree i hi1 hi2 hx
        · exact h.disj i i' hi1 hi2 hi1' hi2' hii x hx hx'
      · rw [Function.update_of_ne hij'] at hx'
        exact h.disj i i' hi1 hi2 hi1' hi2' hii x hx hx'
  · have hwv : w ≠ v := by
      intro e; subst e; exact hf j hj1 hj2 (by simp)
    have hf' : ∀ i, lo ≤ i → i ≤ top → w ∉ K i := by
      intro i hi1 hi2 hw'
      by_cases hij : i = j
      · subst hij; exact hf i hi1 hi2 (by simp [hw'])
      · exact hf i hi1 hi2 (by rw [Function.update_of_ne hij]; exact hw')
    obtain ⟨e1, e2⟩ := h.self w hw hf'
    have hwc : w ∉ (N + j) :: K j := by
      simp only [List.mem_cons, not_or]; exact ⟨by omega, hf' j hj1 hj2⟩
    exact ⟨by rw [upd_ne (show w ≠ N + j by omega), upd_ne hwv]; exact e1,
      by rw [upd_ne (show w ≠ n (N + j) from fun e => hwc (e ▸ htm)), upd_ne hwv]; exact e2⟩

/-- **splice** the (nonempty) list of level `lo` into level `lo + 1` (level `lo` retires) -/
theorem LL.splice (h : LL n p N lo top K) (hlt : lo < top) (hne : K lo ≠ []) :
    LL (Function.update (Function.update (Function.update n (N + (lo + 1)) (n (N + lo)))
          (p (N + lo)) (n (N + (lo + 1)))) (N + lo) (N + lo))
      (Function.update (Function.update (Function.update p (n (N + lo)) (N + (lo + 1)))
          (n (N + (lo + 1))) (p (N + lo))) (N + lo) (N + lo))
      N (lo + 1) top (Function.update K (lo + 1) (K lo ++ K (lo + 1))) := by
  have hd := h.cyc_disj (i := lo) (j := lo + 1) le_rfl hlt.le (by omega) hlt (by omega)
  obtain ⟨hCL, hfm, hlm, htm⟩ := CL_splice (h.cl lo le_rfl hlt.le) (h.cl (lo + 1) (by omega) hlt) hne hd
  have hfc : n (N + lo) ∈ (N + lo) :: K lo := List.mem_cons_of_mem _ hfm
  have hlc : p (N + lo) ∈ (N + lo) :: K lo := List.mem_cons_of_mem _ hlm
  refine ⟨fun i hi1 hi2 => ?_, fun i hi1 hi2 x hx => ?_, fun i i' hi1 hi2 hi1' hi2' hii x hx hx' => ?_,
    fun w hw hf => ?_⟩
  · by_cases hij : i = lo + 1
    · subst hij; simpa using hCL
    · rw [Function.update_of_ne hij]
      have hlo : i ≠ lo := by omega
      refine CL_frame (h.cl i (by omega) hi2) (fun x hx => ?_)
      have hx0 := h.cyc_disj (by omega) hi2 le_rfl hlt.le hlo x hx
      have hx1 := h.cyc_disj (by omega) hi2 (by omega) hlt hij x hx
      have a1 : x ≠ N + lo := fun e => hx0 (e ▸ List.mem_cons_self)
      have a2 : x ≠ p (N + lo) := fun e => hx0 (e ▸ hlc)
      have a3 : x ≠ N + (lo + 1) := fun e => hx1 (e ▸ List.mem_cons_self)
      have a4 : x ≠ n (N + lo) := fun e => hx0 (e ▸ hfc)
      have a5 : x ≠ n (N + (lo + 1)) := fun e => hx1 (e ▸ htm)
      exact ⟨by rw [upd_ne a1, upd_ne a2, upd_ne a3], by rw [upd_ne a1, upd_ne a5, upd_ne a4]⟩
  · by_cases hij : i = lo + 1
    · subst hij
      simp only [Function.update_self, List.mem_append] at hx
      rcases hx with hx | hx
      · exact h.lt lo le_rfl hlt.le x hx
      · exact h.lt (lo + 1) (by omega) hi2 x hx
    · rw [Function.update_of_ne hij] at hx; exact h.lt i (by omega) hi2 x hx
  · have key : ∀ a b, lo + 1 ≤ a → a ≤ top → lo + 1 ≤ b → b ≤ top → a ≠ b → a = lo + 1 →
        ∀ y ∈ K lo ++ K (lo + 1), y ∉ K b := by
      intro a b ha1 ha2 hb1 hb2 hab hal y hy hy'
      subst hal
      simp only [List.mem_append] at hy
      rcases hy with hy | hy
      · exact h.disj lo b le_rfl hlt.le (by omega) hb2 (by omega) y hy hy'
      · exact h.disj (lo + 1) b (by omega) ha2 (by omega) hb2 hab y hy hy'
    by_cases hij : i = lo + 1
    · subst hij
      rw [Function.update_of_ne (Ne.symm hii)] at hx'
      simp only [Function.update_self] at hx
      exact key _ i' hi1 hi2 hi1' hi2' hii rfl x hx hx'
    · rw [Function.update_of_ne hij] at hx
      by_cases hij' : i' = lo + 1
      · subst hij'
        simp only [Function.update_self] at hx'
        exact key _ i hi1' hi2' hi1 hi2 (Ne.symm hii) rfl x hx' hx
      · rw [Function.update_of_ne hij'] at hx'
        exact h.disj i i' (by omega) hi2 (by omega) hi2' hii x hx hx'
  · have hf' : ∀ i, lo ≤ i → i ≤ top → w ∉ K i := by
      intro i hi1 hi2 hw'
      by_cases hil : i = lo
      · subst hil
        exact hf (i + 1) le_rfl hlt (by simp [List.mem_append, hw'])
      · by_cases hij : i = lo + 1
        · subst hij; exact hf (lo + 1) le_rfl hi2 (by simp [List.mem_append, hw'])
        · exact hf i (by omega) hi2 (by rw [Function.update_of_ne hij]; exact hw')
    obtain ⟨e1, e2⟩ := h.self w hw hf'
    have hw0 : w ∉ (N + lo) :: K lo := by
      simp only [List.mem_cons, not_or]; exact ⟨by omega, hf' lo le_rfl hlt.le⟩
    have hw1 : w ∉ (N + (lo + 1)) :: K (lo + 1) := by
      simp only [List.mem_cons, not_or]; exact ⟨by omega, hf' (lo + 1) (by omega) hlt⟩
    exact ⟨by rw [upd_ne (show w ≠ N + lo by omega), upd_ne (show w ≠ p (N + lo) from fun e => hw0 (e ▸ hlc)),
        upd_ne (show w ≠ N + (lo + 1) by omega)]; exact e1,
      by rw [upd_ne (show w ≠ N + lo by omega), upd_ne (show w ≠ n (N + (lo + 1)) from fun e => hw1 (e ▸ htm)),
        upd_ne (show w ≠ n (N + lo) from fun e => hw0 (e ▸ hfc))]; exact e2⟩

/-- splicing an empty list: level `lo` just retires -/
theorem LL.splice_nil (h : LL n p N lo top K) (hlt : lo < top) (hnil : K lo = []) :
    LL n p N (lo + 1) top (Function.update K (lo + 1) (K lo ++ K (lo + 1))) := by
  refine ⟨fun i hi1 hi2 => ?_, fun i hi1 hi2 x hx => ?_, fun i i' hi1 hi2 hi1' hi2' hii x hx hx' => ?_,
    fun w hw hf => ?_⟩
  · by_cases hij : i = lo + 1
    · subst hij; simpa [hnil] using h.cl (lo + 1) (by omega) hi2
    · rw [Function.update_of_ne hij]; exact h.cl i (by omega) hi2
  · by_cases hij : i = lo + 1
    · subst hij; simp only [Function.update_self, hnil, List.nil_append] at hx
      exact h.lt _ (by omega) hi2 x hx
    · rw [Function.update_of_ne hij] at hx; exact h.lt i (by omega) hi2 x hx
  · have e : ∀ j, lo + 1 ≤ j → Function.update K (lo + 1) (K lo ++ K (lo + 1)) j = K j := by
      intro j _; by_cases hj : j = lo + 1
      · subst hj; simp [hnil]
      · exact Function.update_of_ne hj _ _
    rw [e i hi1] at hx; rw [e i' hi1'] at hx'
    exact h.disj i i' (by omega) hi2 (by omega) hi2' hii x hx hx'
  · refine h.self w hw (fun j hj1 hj2 hw' => ?_)
    by_cases hjl : j = lo
    · subst hjl; rw [hnil] at hw'; simp at hw'
    · by_cases hj : j = lo + 1
      · subst hj; exact hf (lo + 1) le_rfl hj2 (by simp [hw'])
      · exact hf j (by omega) hj2 (by rw [Function.update_of_ne hj]; exact hw')

/-- **init** the (empty) list of a new level `lo - 1` -/
theorem LL.init (h : LL n p N lo top K) (hlo : 1 ≤ lo) :
    LL (Function.update n (N + (lo - 1)) (N + (lo - 1))) (Function.update p (N + (lo - 1)) (N + (lo - 1)))
      N (lo - 1) top (Function.update K (lo - 1) []) := by
  refine ⟨fun i hi1 hi2 => ?_, fun i hi1 hi2 x hx => ?_, fun i i' hi1 hi2 hi1' hi2' hii x hx hx' => ?_,
    fun w hw hf => ?_⟩
  · by_cases hij : i = lo - 1
    · subst hij; rw [Function.update_self, CL_nil_iff]; simp
    · rw [Function.update_of_ne hij]
      refine CL_frame (h.cl i (by omega) hi2) (fun x hx => ?_)
      have hx' : x ≠ N + (lo - 1) := by
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · omega
        · have := h.lt i (by omega) hi2 x hx; omega
      exact ⟨upd_ne hx', upd_ne hx'⟩
  · by_cases hij : i = lo - 1
    · subst hij; simp at hx
    · rw [Function.update_of_ne hij] at hx; exact h.lt i (by omega) hi2 x hx
  · by_cases hij : i = lo - 1
    · subst hij; simp at hx
    · by_cases hij' : i' = lo - 1
      · subst hij'; simp at hx'
      · rw [Function.update_of_ne hij] at hx; rw [Function.update_of_ne hij'] at hx'
        exact h.disj i i' (by omega) hi2 (by omega) hi2' hii x hx hx'
  · have hf' : ∀ j, lo ≤ j → j ≤ top → w ∉ K j := fun j hj1 hj2 hw' =>
      hf j (by omega) hj2 (by rw [Function.update_of_ne (show j ≠ lo - 1 by omega)]; exact hw')
    obtain ⟨e1, e2⟩ := h.self w hw hf'
    exact ⟨by rw [upd_ne (show w ≠ N + (lo - 1) by omega)]; exact e1,
      by rw [upd_ne (show w ≠ N + (lo - 1) by omega)]; exact e2⟩

end family


/-! ## RAM fragments -/

section ram

open Frontier.RAM Frontier.RAM.LabRAM Frontier.RAM.WExpr Frontier.RAM.Stmt

/-- `lk.n[kl.s] := kl.s; lk.p[kl.s] := kl.s` -/
def klInit : Stmt := seq (wstore "lk.n" (var "kl.s") (var "kl.s")) (wstore "lk.p" (var "kl.s") (var "kl.s"))

/-- link node `kl.v` right after sentinel `kl.s` -/
def klLink : Stmt :=
  seq (wset "kl.t" (load "lk.n" (var "kl.s")))
  (seq (wstore "lk.n" (var "kl.v") (var "kl.t"))
  (seq (wstore "lk.p" (var "kl.v") (var "kl.s"))
  (seq (wstore "lk.p" (var "kl.t") (var "kl.v"))
       (wstore "lk.n" (var "kl.s") (var "kl.v")))))

/-- unlink node `kl.v` (a self-loop stays a self-loop) -/
def klUnlink : Stmt :=
  seq (wset "kl.a" (load "lk.p" (var "kl.v")))
  (seq (wset "kl.b" (load "lk.n" (var "kl.v")))
  (seq (wstore "lk.n" (var "kl.a") (var "kl.b"))
  (seq (wstore "lk.p" (var "kl.b") (var "kl.a"))
  (seq (wstore "lk.n" (var "kl.v") (var "kl.v"))
       (wstore "lk.p" (var "kl.v") (var "kl.v"))))))

/-- splice the list of sentinel `kl.c` right after sentinel `kl.s`, then reset `kl.c` -/
def klSplice : Stmt :=
  seq (wset "kl.f" (load "lk.n" (var "kl.c")))
  (ite (eq (var "kl.f") (var "kl.c")) skip
    (seq (wset "kl.l" (load "lk.p" (var "kl.c")))
    (seq (wset "kl.t" (load "lk.n" (var "kl.s")))
    (seq (wstore "lk.n" (var "kl.s") (var "kl.f"))
    (seq (wstore "lk.p" (var "kl.f") (var "kl.s"))
    (seq (wstore "lk.n" (var "kl.l") (var "kl.t"))
    (seq (wstore "lk.p" (var "kl.t") (var "kl.l"))
    (seq (wstore "lk.n" (var "kl.c") (var "kl.c"))
         (wstore "lk.p" (var "kl.c") (var "kl.c"))))))))))

/-- `sp.em := [lk.n[kl.s] = kl.s]` (1 iff the list of sentinel `kl.s` is empty) -/
def klTest : Stmt := wset "sp.em" (eq (load "lk.n" (var "kl.s")) (var "kl.s"))

/-- the register names of the list fragments -/
def klRegs : List String := ["kl.v", "kl.s", "kl.c", "kl.a", "kl.b", "kl.t", "kl.f", "kl.l"]

variable {ops : VOps ℝ≥0}

theorem unch_lk {st r : State ℝ≥0} {wr : List String}
    (hwa : ∀ a, a ≠ "lk.n" → a ≠ "lk.p" → r.wa a = st.wa a) (hva : r.va = st.va)
    (hw : ∀ x, x ∉ wr → r.w x = st.w x) (hv : r.v = st.v) (hwl : r.wlen = st.wlen)
    (hvl : r.vlen = st.vlen) (hcap : r.cap = st.cap) (hpr : r.procs = st.procs) :
    Unchanged st r ["lk.n", "lk.p"] [] wr [] :=
  ⟨fun a ha => ⟨hwa a (by intro e; subst e; simp at ha) (by intro e; subst e; simp at ha),
      by rw [hwl]⟩, fun a _ => ⟨by rw [hva], by rw [hvl]⟩, hw, fun x _ => by rw [hv], hcap, hpr⟩

theorem klUnlink_spec (st : State ℝ≥0) (v : ℕ) (hv : st.w "kl.v" = v)
    (h1 : v < st.wlen "lk.n") (h2 : v < st.wlen "lk.p")
    (h3 : st.wa "lk.p" v < st.wlen "lk.n") (h4 : st.wa "lk.n" v < st.wlen "lk.p") :
    Runs ops klUnlink st (fun r =>
      r.wa "lk.n" = Function.update (Function.update (st.wa "lk.n") (st.wa "lk.p" v) (st.wa "lk.n" v)) v v ∧
      r.wa "lk.p" = Function.update (Function.update (st.wa "lk.p") (st.wa "lk.n" v) (st.wa "lk.p" v)) v v ∧
      Unchanged st r ["lk.n", "lk.p"] [] ["kl.a", "kl.b"] [] ∧ r.wlen = st.wlen ∧
      r.cost = st.cost + 6) := by
  apply wp_sound
  simp [klUnlink, wp, evalW, hv, h1, h2, h3, h4, State.setW, State.charge, State.storeW]
  refine ⟨by funext j; simp [Function.update_apply], by funext j; simp [Function.update_apply], ?_⟩
  refine unch_lk (fun a h1 h2 => ?_) rfl (fun x hx => ?_) rfl rfl rfl rfl rfl
  · funext j; simp [h1, h2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp [hx.1, hx.2]

theorem klLink_spec (st : State ℝ≥0) (v sn : ℕ) (hv : st.w "kl.v" = v) (hs : st.w "kl.s" = sn)
    (h1 : v < st.wlen "lk.n") (h2 : v < st.wlen "lk.p")
    (h3 : sn < st.wlen "lk.n") (h4 : st.wa "lk.n" sn < st.wlen "lk.p") :
    Runs ops klLink st (fun r =>
      r.wa "lk.n" = Function.update (Function.update (st.wa "lk.n") v (st.wa "lk.n" sn)) sn v ∧
      r.wa "lk.p" = Function.update (Function.update (st.wa "lk.p") v sn) (st.wa "lk.n" sn) v ∧
      Unchanged st r ["lk.n", "lk.p"] [] ["kl.t"] [] ∧ r.wlen = st.wlen ∧
      r.cost = st.cost + 5) := by
  apply wp_sound
  simp [klLink, wp, evalW, hv, hs, h1, h2, h3, h4, State.setW, State.charge, State.storeW]
  refine ⟨by funext j; simp [Function.update_apply], by funext j; simp [Function.update_apply], ?_⟩
  refine unch_lk (fun a h1 h2 => ?_) rfl (fun x hx => ?_) rfl rfl rfl rfl rfl
  · funext j; simp [h1, h2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simp [hx]

theorem klInit_spec (st : State ℝ≥0) (sn : ℕ) (hs : st.w "kl.s" = sn)
    (h1 : sn < st.wlen "lk.n") (h2 : sn < st.wlen "lk.p") :
    Runs ops klInit st (fun r =>
      r.wa "lk.n" = Function.update (st.wa "lk.n") sn sn ∧
      r.wa "lk.p" = Function.update (st.wa "lk.p") sn sn ∧
      Unchanged st r ["lk.n", "lk.p"] [] [] [] ∧ r.wlen = st.wlen ∧ r.cost = st.cost + 2) := by
  apply wp_sound
  simp [klInit, wp, evalW, hs, h1, h2, State.charge, State.storeW]
  refine ⟨by funext j; simp [Function.update_apply], by funext j; simp [Function.update_apply], ?_⟩
  refine unch_lk (fun a h1 h2 => ?_) rfl (fun x _ => rfl) rfl rfl rfl rfl rfl
  funext j; simp [h1, h2]

theorem klTest_spec (st : State ℝ≥0) (sn : ℕ) (hs : st.w "kl.s" = sn) (h1 : sn < st.wlen "lk.n")
    (hcap : 1 < st.cap) :
    Runs ops klTest st (fun r => (r.w "sp.em" = if st.wa "lk.n" sn = sn then 1 else 0) ∧
      Unchanged st r [] [] ["sp.em"] [] ∧ r.wlen = st.wlen ∧ r.cost = st.cost + 1) := by
  apply wp_sound
  have hc0 : 0 < st.cap := by omega
  by_cases he : st.wa "lk.n" sn = sn
  · simp [klTest, wp, evalW, hs, h1, he, fit, hcap, State.setW, State.charge]
    exact ⟨fun a _ => ⟨rfl, rfl⟩, fun a _ => ⟨rfl, rfl⟩, fun x hx => by simp at hx; simp [hx],
      fun _ _ => rfl, rfl, rfl⟩
  · simp [klTest, wp, evalW, hs, h1, he, fit, hc0, State.setW, State.charge]
    exact ⟨fun a _ => ⟨rfl, rfl⟩, fun a _ => ⟨rfl, rfl⟩, fun x hx => by simp at hx; simp [hx],
      fun _ _ => rfl, rfl, rfl⟩

theorem klSplice_spec (st : State ℝ≥0) (cn sn : ℕ) (hc : st.w "kl.c" = cn) (hs : st.w "kl.s" = sn)
    (h1 : cn < st.wlen "lk.n") (h2 : cn < st.wlen "lk.p") (h3 : sn < st.wlen "lk.n")
    (h4 : st.wa "lk.n" cn < st.wlen "lk.p") (h5 : st.wa "lk.p" cn < st.wlen "lk.n")
    (h6 : st.wa "lk.n" sn < st.wlen "lk.p") (hcap : 1 < st.cap) :
    Runs ops klSplice st (fun r =>
      (st.wa "lk.n" cn = cn → r.wa "lk.n" = st.wa "lk.n" ∧ r.wa "lk.p" = st.wa "lk.p") ∧
      (st.wa "lk.n" cn ≠ cn →
        r.wa "lk.n" = Function.update (Function.update (Function.update (st.wa "lk.n") sn
          (st.wa "lk.n" cn)) (st.wa "lk.p" cn) (st.wa "lk.n" sn)) cn cn ∧
        r.wa "lk.p" = Function.update (Function.update (Function.update (st.wa "lk.p")
          (st.wa "lk.n" cn) sn) (st.wa "lk.n" sn) (st.wa "lk.p" cn)) cn cn) ∧
      Unchanged st r ["lk.n", "lk.p"] [] ["kl.f", "kl.l", "kl.t"] [] ∧ r.wlen = st.wlen ∧
      r.cost ≤ st.cost + 10) := by
  apply wp_sound
  have hc0 : 0 < st.cap := by omega
  by_cases he : st.wa "lk.n" cn = cn
  · simp [klSplice, wp, evalW, hc, h1, he, fit, hcap, State.setW, State.charge]
    refine unch_lk (fun a _ _ => rfl) rfl (fun x hx => ?_) rfl rfl rfl rfl rfl
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp [hx.1]
  · simp [klSplice, wp, evalW, hc, hs, h1, h2, h3, h4, h5, h6, he, fit, hc0, State.setW,
      State.charge, State.storeW]
    refine ⟨⟨by funext j; simp [Function.update_apply], by funext j; simp [Function.update_apply]⟩, ?_⟩
    refine unch_lk (fun a h1 h2 => ?_) rfl (fun x hx => ?_) rfl rfl rfl rfl rfl
    · funext j; simp [h1, h2]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp [hx.1, hx.2.1, hx.2.2]

/-! ### The fragments on the family invariant -/

theorem LL.next_mem {n p : ℕ → ℕ} {N lo top : ℕ} {K : ℕ → List ℕ} (h : LL n p N lo top K) {j : ℕ}
    (hj1 : lo ≤ j) (hj2 : j ≤ top) : n (N + j) ∈ (N + j) :: K j ∧ p (N + j) ∈ (N + j) :: K j := by
  have hc := h.cl j hj1 hj2
  by_cases hK : K j = []
  · rw [hK] at hc ⊢; obtain ⟨e1, e2⟩ := CL_nil_iff.mp hc; simp [e1, e2]
  · exact ⟨by rw [CL_first hc hK]; exact List.mem_cons_of_mem _ (List.head_mem hK),
      by rw [CL_last hc hK]; exact List.mem_cons_of_mem _ (List.getLast_mem hK)⟩

theorem klUnlink_LL (st : State ℝ≥0) {N lo top v : ℕ} {K : ℕ → List ℕ}
    (hL : LL (st.wa "lk.n") (st.wa "lk.p") N lo top K) (hv : st.w "kl.v" = v) (hvN : v < N)
    (hl1 : N + top < st.wlen "lk.n") (hl2 : N + top < st.wlen "lk.p") :
    Runs ops klUnlink st (fun r => LL (r.wa "lk.n") (r.wa "lk.p") N lo top (fun j => (K j).erase v) ∧
      Unchanged st r ["lk.n", "lk.p"] [] ["kl.a", "kl.b"] [] ∧ r.wlen = st.wlen ∧
      r.cost = st.cost + 6) := by
  obtain ⟨hp, hn⟩ := hL.nbr hvN
  refine (klUnlink_spec st v hv (by omega) (by omega) (by omega) (by omega)).mono ?_
  rintro r ⟨e1, e2, hU, hwl, hc⟩
  exact ⟨by rw [e1, e2]; exact hL.unlink hvN, hU, hwl, hc⟩

theorem klLink_LL (st : State ℝ≥0) {N lo top v j : ℕ} {K : ℕ → List ℕ}
    (hL : LL (st.wa "lk.n") (st.wa "lk.p") N lo top K) (hv : st.w "kl.v" = v) (hvN : v < N)
    (hfree : ∀ i, lo ≤ i → i ≤ top → v ∉ K i) (hs : st.w "kl.s" = N + j) (hj1 : lo ≤ j)
    (hj2 : j ≤ top) (hl1 : N + top < st.wlen "lk.n") (hl2 : N + top < st.wlen "lk.p") :
    Runs ops klLink st (fun r => LL (r.wa "lk.n") (r.wa "lk.p") N lo top
        (Function.update K j (v :: K j)) ∧
      Unchanged st r ["lk.n", "lk.p"] [] ["kl.t"] [] ∧ r.wlen = st.wlen ∧ r.cost = st.cost + 5) := by
  have hnm := (hL.next_mem hj1 hj2).1
  have hnlt := hL.cyc_lt hj1 hj2 _ hnm
  refine (klLink_spec st v (N + j) hv hs (by omega) (by omega) (by omega) (by omega)).mono ?_
  rintro r ⟨e1, e2, hU, hwl, hc⟩
  exact ⟨by rw [e1, e2]; exact hL.link hvN hfree hj1 hj2, hU, hwl, hc⟩

theorem klSplice_LL (st : State ℝ≥0) {N lo top : ℕ} {K : ℕ → List ℕ}
    (hL : LL (st.wa "lk.n") (st.wa "lk.p") N lo top K) (hlt : lo < top)
    (hc : st.w "kl.c" = N + lo) (hs : st.w "kl.s" = N + (lo + 1))
    (hl1 : N + top < st.wlen "lk.n") (hl2 : N + top < st.wlen "lk.p") (hcap : 1 < st.cap) :
    Runs ops klSplice st (fun r => LL (r.wa "lk.n") (r.wa "lk.p") N (lo + 1) top
        (Function.update K (lo + 1) (K lo ++ K (lo + 1))) ∧
      Unchanged st r ["lk.n", "lk.p"] [] ["kl.f", "kl.l", "kl.t"] [] ∧ r.wlen = st.wlen ∧
      r.cost ≤ st.cost + 10) := by
  obtain ⟨hn0, hp0⟩ := hL.next_mem (j := lo) le_rfl hlt.le
  obtain ⟨hn1, -⟩ := hL.next_mem (j := lo + 1) (by omega) hlt
  have a1 := hL.cyc_lt le_rfl hlt.le _ hn0
  have a2 := hL.cyc_lt le_rfl hlt.le _ hp0
  have a3 := hL.cyc_lt (by omega) hlt _ hn1
  refine (klSplice_spec st (N + lo) (N + (lo + 1)) hc hs (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hcap).mono ?_
  rintro r ⟨hE, hNE, hU, hwl, hcost⟩
  refine ⟨?_, hU, hwl, hcost⟩
  by_cases hK : K lo = []
  · have he : st.wa "lk.n" (N + lo) = N + lo := (hL.empty_iff le_rfl hlt.le).mpr hK
    obtain ⟨e1, e2⟩ := hE he
    rw [e1, e2]; exact hL.splice_nil hlt hK
  · have he : st.wa "lk.n" (N + lo) ≠ N + lo := fun h' => hK ((hL.empty_iff le_rfl hlt.le).mp h')
    obtain ⟨e1, e2⟩ := hNE he
    rw [e1, e2]; exact hL.splice hlt hK

theorem klInit_LL (st : State ℝ≥0) {N lo top : ℕ} {K : ℕ → List ℕ}
    (hL : LL (st.wa "lk.n") (st.wa "lk.p") N lo top K) (hlo : 1 ≤ lo)
    (hs : st.w "kl.s" = N + (lo - 1)) (hlt : lo ≤ top)
    (hl1 : N + top < st.wlen "lk.n") (hl2 : N + top < st.wlen "lk.p") :
    Runs ops klInit st (fun r => LL (r.wa "lk.n") (r.wa "lk.p") N (lo - 1) top
        (Function.update K (lo - 1) []) ∧
      Unchanged st r ["lk.n", "lk.p"] [] [] [] ∧ r.wlen = st.wlen ∧ r.cost = st.cost + 2) := by
  refine (klInit_spec st (N + (lo - 1)) hs (by omega) (by omega)).mono ?_
  rintro r ⟨e1, e2, hU, hwl, hc⟩
  exact ⟨by rw [e1, e2]; exact hL.init hlo, hU, hwl, hc⟩

theorem klTest_LL (st : State ℝ≥0) {N lo top j : ℕ} {K : ℕ → List ℕ}
    (hL : LL (st.wa "lk.n") (st.wa "lk.p") N lo top K) (hs : st.w "kl.s" = N + j) (hj1 : lo ≤ j)
    (hj2 : j ≤ top) (hl1 : N + top < st.wlen "lk.n") (hcap : 1 < st.cap) :
    Runs ops klTest st (fun r => (r.w "sp.em" = if K j = [] then 1 else 0) ∧
      Unchanged st r [] [] ["sp.em"] [] ∧ r.wlen = st.wlen ∧ r.cost = st.cost + 1) := by
  refine (klTest_spec st (N + j) hs (by omega) hcap).mono ?_
  rintro r ⟨e1, hU, hwl, hc⟩
  refine ⟨?_, hU, hwl, hc⟩
  rw [e1]
  by_cases hK : K j = []
  · rw [if_pos ((hL.empty_iff hj1 hj2).mpr hK), if_pos hK]
  · rw [if_neg (fun h' => hK ((hL.empty_iff hj1 hj2).mp h')), if_neg hK]

/-! ### Allocation (prologue): every node a self-loop -/

def klFillBody : Stmt :=
  seq (wstore "lk.n" (var "kl.j") (var "kl.j"))
  (seq (wstore "lk.p" (var "kl.j") (var "kl.j")) (wset "kl.j" (add (var "kl.j") (lit 1))))

def klFillLoop : Stmt := .while (lt (var "kl.j") (var "kl.len")) klFillBody

/-- allocate `lk.n`, `lk.p` of length `kl.len` and make every node a self-loop -/
def klAlloc : Stmt :=
  seq (walloc "lk.n" (var "kl.len")) (seq (walloc "lk.p" (var "kl.len"))
    (seq (wset "kl.j" (lit 0)) klFillLoop))

structure FInv (st0 q : State ℝ≥0) (M k : ℕ) : Prop where
  jr : q.w "kl.j" = k
  kle : k ≤ M
  done : ∀ i < k, q.wa "lk.n" i = i ∧ q.wa "lk.p" i = i
  ln : q.wlen "lk.n" = M
  lp : q.wlen "lk.p" = M
  unch : Unchanged st0 q ["lk.n", "lk.p"] [] ["kl.j"] []

theorem fill_loop (st0 : State ℝ≥0) (M : ℕ) (hM : st0.w "kl.len" = M) (hcap : M + 1 < st0.cap) :
    ∀ (n k : ℕ) (q : State ℝ≥0), M - k = n → FInv st0 q M k →
      Runs ops klFillLoop q (fun r => FInv st0 r M M ∧ r.cost = q.cost + 4 * n + 1)
  | 0, k, q, hn, hI => by
      have hk : k = M := by have := hI.kle; omega
      subst hk
      have hc : q.cap = st0.cap := hI.unch.cap
      have hw : q.w "kl.len" = k := by rw [hI.unch.wreg _ (by simp)]; exact hM
      refine Frontier.CHD.DList.runs_while_exit (by simp [hI.jr, hw, fit, show 0 < q.cap by omega]) ?_
      exact ⟨⟨by simp [hI.jr], le_rfl, fun i hi => by simpa using hI.done i hi, by simp [hI.ln],
        by simp [hI.lp], (unch_charge 1).mpr hI.unch⟩, by simp⟩
  | n + 1, k, q, hn, hI => by
      have hk : k < M := by omega
      have hc : q.cap = st0.cap := hI.unch.cap
      have hw : q.w "kl.len" = M := by rw [hI.unch.wreg _ (by simp)]; exact hM
      refine Frontier.CHD.DList.runs_while_step (x := 1) (by simp [hI.jr, hw, fit, hk, show 1 < q.cap by omega])
        one_ne_zero ?_
      apply wp_sound
      have h1 : k < q.wlen "lk.n" := by rw [hI.ln]; exact hk
      have h2 : k < q.wlen "lk.p" := by rw [hI.lp]; exact hk
      have h3 : k + 1 < q.cap := by omega
      have h0 : 1 < q.cap := by omega
      simp [klFillBody, wp, hI.jr, fit, h1, h2, h3, h0]
      refine (fill_loop st0 M hM hcap n (k + 1) _ (by omega) ?_).mono ?_
      · refine ⟨by simp, by omega, ?_, by simp [hI.ln], by simp [hI.lp], ?_⟩
        · intro i hi
          by_cases hik : i = k
          · subst hik; simp
          · simp only [State.charge_wa, State.setW_wa, State.storeW_wa]
            simp [hik, hI.done i (by omega)]
        · rw [unch_charge, unch_setW (by simp), unch_charge, unch_storeW (by simp), unch_charge,
            unch_storeW (by simp), unch_charge]
          exact hI.unch
      · rintro r ⟨h1, h2⟩
        exact ⟨h1, by simp at h2; omega⟩

theorem klAlloc_spec (st : State ℝ≥0) (M : ℕ) (hM : st.w "kl.len" = M) (hcap : M + 1 < st.cap) :
    Runs ops klAlloc st (fun r => (∀ i < M, r.wa "lk.n" i = i ∧ r.wa "lk.p" i = i) ∧
      r.wlen "lk.n" = M ∧ r.wlen "lk.p" = M ∧ Unchanged st r ["lk.n", "lk.p"] [] ["kl.j"] [] ∧
      r.cost = st.cost + 6 * M + 4) := by
  have hc1 : 0 < st.cap := by omega
  refine runs_seq (runs_walloc (k := M) (by simp [hM]) ?_)
  refine runs_seq (runs_walloc (k := M) (by simp [hM]) ?_)
  refine runs_seq (runs_wset (a := 0) (by simp [fit, hc1]) ?_)
  set q := ((((st.allocW "lk.n" M).charge (M + 1)).allocW "lk.p" M).charge (M + 1)).setW "kl.j" 0
    |>.charge 1 with hq
  have hI : FInv st q M 0 := by
    refine ⟨by simp [hq], Nat.zero_le _, fun i hi => absurd hi (Nat.not_lt_zero _),
      by simp [hq, State.allocW], by simp [hq, State.allocW], ?_⟩
    refine ⟨fun a ha => ?_, fun a _ => ⟨by simp [hq, State.allocW], by simp [hq, State.allocW]⟩,
      fun x hx => ?_, fun x _ => by simp [hq, State.allocW], by simp [hq, State.allocW],
      by simp [hq, State.allocW]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
      exact ⟨by funext j; simp [hq, State.allocW, ha.1, ha.2],
        by simp [hq, State.allocW, ha.1, ha.2]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp [hq, State.allocW, hx]
  refine (fill_loop st M hM hcap M 0 q (by omega) hI).mono ?_
  rintro r ⟨hF, hc⟩
  refine ⟨hF.done, hF.ln, hF.lp, hF.unch, ?_⟩
  rw [hc]; simp [hq, State.allocW]; ring

/-- the family invariant right after allocation: one (empty) level `top` -/
theorem LL_alloc {n p : ℕ → ℕ} {N top : ℕ} (h : ∀ i < N + top + 1, n i = i ∧ p i = i) :
    LL n p N top top (fun _ => []) := by
  refine ⟨fun j h1 h2 => ?_, fun _ _ _ x hx => absurd hx (List.not_mem_nil),
    fun _ _ _ _ _ _ _ x hx => absurd hx (List.not_mem_nil), fun v hv _ => h v (by omega)⟩
  have hj : j = top := le_antisymm h2 h1
  subst hj
  exact CL_nil_iff.mpr (h (N + j) (by omega))

end ram

end Frontier.CHD.KL
