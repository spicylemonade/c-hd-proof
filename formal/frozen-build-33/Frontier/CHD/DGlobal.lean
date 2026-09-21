import Frontier.CHD.DList

/-!
# DGlobal — the D layer of all active BMSSP levels (B-L3 integration, agent-04, NON-GATE)

Shared stack (A1): the top-level structure (level `hi`) has base `0`; the structure of level
`l < hi` sits directly on top of level `l+1`: `base l = base (l+1) + sz (l+1)`.  Bases are kept in
the word array `dsl.base`.  `DLRep` bundles, for the active levels `lo..hi`:
* agent-02's per-level `DRep` (stack slice + block records);
* one `RecsOK` family over the records of all active levels (distinct record ids, pairwise
  disjoint entry ids): the frame condition that makes per-level operations local;
* the global live map (`LiveRep`), entry pool (`PoolRep`), block arrays (`BlkArrs`).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.DGlob

open Frontier Frontier.RAM Frontier.CHD Frontier.CHD.DB Frontier.CHD.DIns Frontier.CHD.DList
open Frontier.RAM.WExpr Frontier.RAM.Stmt

variable {G : Graph} {s : Fin G.n}

/-- the base of level `l` -/
def base (st : State ℝ≥0) (l : ℕ) : ℕ := st.wa "dsl.base" l

/-- the block records of `n` consecutive levels starting at `l` -/
def recsFrom (st : State ℝ≥0) (Ds : ℕ → DStr (Fin G.n) (WLab G s)) : ℕ → ℕ →
    List (ℕ × Block (Fin G.n) (WLab G s))
  | _, 0 => []
  | l, n + 1 => recsOf st (base st l) (Ds l).blocks ++ recsFrom st Ds (l + 1) n

/-- **the D layer** at active levels `lo..lo+k` (`lo + k` = top level) -/
structure DLRep (st : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (ecap bcap : ℕ) (L : Live (Fin G.n) (WLab G s)) (fresh : ℕ)
    (Ds : ℕ → DStr (Fin G.n) (WLab G s)) (lo k : ℕ) : Prop where
  live : LiveRep st H V L
  pool : PoolRep st fresh ecap
  barr : BlkArrs st bcap
  basel : lo + k < st.wlen "dsl.base"
  base0 : base st (lo + k) = 0
  chain : ∀ j < k, base st (lo + j) = base st (lo + j + 1) + (Ds (lo + j + 1)).blocks.length
  drep : ∀ j ≤ k, DRep st H V bcap (lo + j) (base st (lo + j)) (Ds (lo + j))
  recs : RecsOK st H V (recsFrom st Ds lo (k + 1))
  /-- all used block ids are below the block counter `blk.fresh`, itself at most the capacity -/
  bfresh : ∀ p ∈ recsFrom st Ds lo (k + 1), p.1 < st.w "blk.fresh"
  bfcap : st.w "blk.fresh" ≤ bcap

/-! ## Statements without allocation keep all array lengths -/

/-- no allocation and no procedure call -/
def NoAlloc : Stmt → Prop
  | .walloc _ _ => False
  | .valloc _ _ => False
  | .call _ => False
  | .seq a b => NoAlloc a ∧ NoAlloc b
  | .ite _ a b => NoAlloc a ∧ NoAlloc b
  | .while _ b => NoAlloc b
  | _ => True

/-- the array lengths of a state -/
def Lens {V : Type} (st : State V) : (String → ℕ) × (String → ℕ) := (st.wlen, st.vlen)

theorem exec_noalloc_len {V : Type} (ops : VOps V) :
    ∀ (f : ℕ) (c : Stmt) (st r : State V), NoAlloc c → exec ops f c st = some r → Lens r = Lens st := by
  intro f
  induction f with
  | zero => intro c st r _ h; simp [exec] at h
  | succ f ih =>
    intro c st r hc h
    cases c with
    | skip => simp [exec] at h; subst h; rfl
    | wset x e =>
      cases he : evalW st e with
      | none => simp [exec, he] at h
      | some a => simp [exec, he] at h; subst h; rfl
    | vset x e =>
      cases he : evalV ops st e with
      | none => simp [exec, he] at h
      | some a => simp [exec, he] at h; subst h; rfl
    | vle x a b =>
      cases h1 : evalV ops st a with
      | none => simp [exec, h1] at h
      | some p =>
        cases h2 : evalV ops st b with
        | none => simp [exec, h1, h2] at h
        | some q =>
          cases h3 : fit st.cap (if ops.le p q then 1 else 0) with
          | none => simp [exec, h1, h2, h3] at h
          | some bit => simp [exec, h1, h2, h3] at h; subst h; rfl
    | wstore arr i e =>
      cases h1 : evalW st i with
      | none => simp [exec, h1] at h
      | some j =>
        cases h2 : evalW st e with
        | none => simp [exec, h1, h2] at h
        | some a =>
          by_cases hj : j < st.wlen arr
          · simp [exec, h1, h2, hj] at h; subst h; rfl
          · simp [exec, h1, h2, hj] at h
    | vstore arr i e =>
      cases h1 : evalW st i with
      | none => simp [exec, h1] at h
      | some j =>
        cases h2 : evalV ops st e with
        | none => simp [exec, h1, h2] at h
        | some a =>
          by_cases hj : j < st.vlen arr
          · simp [exec, h1, h2, hj] at h; subst h; rfl
          · simp [exec, h1, h2, hj] at h
    | walloc arr e => exact absurd hc (by simp [NoAlloc])
    | valloc arr e => exact absurd hc (by simp [NoAlloc])
    | call p => exact absurd hc (by simp [NoAlloc])
    | seq a b =>
      rw [exec_seq, Option.bind_eq_some_iff] at h
      obtain ⟨s', h1, h2⟩ := h
      exact (ih b s' r hc.2 h2).trans (ih a st s' hc.1 h1)
    | ite c a b =>
      rw [exec_ite, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h2⟩ := h
      split_ifs at h2
      · exact (ih a _ r hc.1 h2).trans rfl
      · exact (ih b _ r hc.2 h2).trans rfl
    | «while» c b =>
      rw [exec_while, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h2⟩ := h
      split_ifs at h2
      · rw [Option.bind_eq_some_iff] at h2
        obtain ⟨s', h3, h4⟩ := h2
        exact (ih _ s' r hc h4).trans ((ih b _ s' hc h3).trans rfl)
      · simp at h2; subst h2; rfl

/-- `Runs` of an allocation-free statement also keeps all lengths -/
theorem Runs.keep_len {ops : VOps ℝ≥0} {c : Stmt} {st : State ℝ≥0} {Q : State ℝ≥0 → Prop}
    (h : Runs ops c st Q) (hc : NoAlloc c) :
    Runs ops c st (fun r => Q r ∧ (∀ a, r.wlen a = st.wlen a) ∧ (∀ a, r.vlen a = st.vlen a)) := by
  obtain ⟨f, r, h1, h2⟩ := h
  have := exec_noalloc_len ops f c st r hc h1
  simp only [Lens, Prod.mk.injEq] at this
  exact ⟨f, r, h1, h2, fun a => congrFun this.1 a, fun a => congrFun this.2 a⟩

theorem mergeS_noalloc : NoAlloc mergeS := by
  simp [NoAlloc, mergeS, mgInit, mgLoop, mgBody, emitS, concatS, mgFlush, mgSetShift, mgShift,
    shiftLoop, shiftBody, mgSetSz]

/-! ## Helpers -/

theorem RecsOK.sublist {q : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {r₁ r₂ : List (ℕ × Block (Fin G.n) (WLab G s))} (h : RecsOK q H V r₂) (hs : r₁.Sublist r₂) :
    RecsOK q H V r₁ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨(hs.map _).nodup h1, fun p hp => h2 p (hs.subset hp), ?_⟩
  have : (entIds (r₁.map Prod.snd)).Sublist (entIds (r₂.map Prod.snd)) := by
    unfold entIds; exact (hs.map _).flatMap _
  exact this.nodup h3

/-- the arrays the live map and the pool depend on -/
def poolArrs : List String := ["live", "ent.key", "ent.h", "ent.v", "ent.e", "ent.r"]

theorem liveRep_of_arrays {q r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {L : Live (Fin G.n) (WLab G s)} (h : LiveRep q H V L) (hA : ∀ a ∈ poolArrs, r.wa a = q.wa a)
    (hV : r.va "ent.len" = q.va "ent.len") (hlen : r.wlen "live" = q.wlen "live") :
    LiveRep r H V L := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [hlen]; exact h1, fun v => ⟨by rw [hA _ (by simp [poolArrs])]; exact (h2 v).1, ?_⟩⟩
  intro i a hv
  exact ((h2 v).2 i a hv).of_eq (by rw [hA _ (by simp [poolArrs])])
    (by rw [show entA.l = "ent.len" from rfl, hV]) (by rw [hA _ (by simp [poolArrs, entA])])
    (by rw [hA _ (by simp [poolArrs, entA])]) (by rw [hA _ (by simp [poolArrs, entA])])
    (by rw [hA _ (by simp [poolArrs, entA])])

theorem poolRep_of {q r : State ℝ≥0} {fresh ecap : ℕ} (h : PoolRep q fresh ecap)
    (hf : r.w "ds.fresh" = q.w "ds.fresh") (hl : ∀ a, r.wlen a = q.wlen a)
    (hvl : ∀ a, r.vlen a = q.vlen a) : PoolRep r fresh ecap := by
  obtain ⟨h1, h2, a1, a2, a3, a4, a5, a6, a7⟩ := h
  refine ⟨hf.trans h1, h2, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | (rw [hl]; assumption) | (rw [hvl]; assumption)

theorem blkArrs_of {q r : State ℝ≥0} {bcap : ℕ} (h : BlkArrs q bcap) (hl : ∀ a, r.wlen a = q.wlen a)
    (hvl : ∀ a, r.vlen a = q.vlen a) : BlkArrs r bcap := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | (rw [hl]; assumption) | (rw [hvl]; assumption)

/-- a structure survives when its stack slice, its size cell and its records survive -/
theorem DRep.of_frame {q r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap lv bse : ℕ} {D : DStr (Fin G.n) (WLab G s)} (h : DRep q H V bcap lv bse D)
    (hstk : ∀ x, bse ≤ x → x < bse + D.blocks.length → r.wa "dsl.stk" x = q.wa "dsl.stk" x)
    (hsz : r.wa "dsl.sz" lv = q.wa "dsl.sz" lv) (hl : ∀ a, r.wlen a = q.wlen a)
    (hrec : ∀ i (hi : i < D.blocks.length), BlkRep r H V (stkId q bse D.blocks.length i) D.blocks[i]) :
    DRep r H V bcap lv bse D := by
  have hs : ∀ i, i < D.blocks.length → stkId r bse D.blocks.length i = stkId q bse D.blocks.length i := by
    intro i hi; unfold stkId; exact hstk _ (by omega) (by omega)
  refine ⟨by rw [hsz]; exact h.sz, by rw [hl]; exact h.szb, by rw [hl]; exact h.stkb,
    fun i hi => by rw [hs i hi]; exact hrec i hi, fun i j hi hj hij => ?_, fun i hi => ?_⟩
  · rw [hs i hi, hs j hj] at hij; exact h.inj i j hi hj hij
  · rw [hs i hi]; exact h.bidb i hi

theorem mem_recsOf' {st : State ℝ≥0} {bse : ℕ} {P : List (Block (Fin G.n) (WLab G s))} {i : ℕ}
    (hi : i < P.length) : (stkId st bse P.length i, P[i]) ∈ recsOf st bse P :=
  mem_recsOf st bse P i hi

theorem mem_recsFrom (st : State ℝ≥0) (Ds : ℕ → DStr (Fin G.n) (WLab G s)) :
    ∀ (n l0 l i : ℕ), l0 ≤ l → l < l0 + n → (hi : i < (Ds l).blocks.length) →
      (stkId st (base st l) (Ds l).blocks.length i, (Ds l).blocks[i]) ∈ recsFrom st Ds l0 n
  | 0, l0, l, i, h1, h2, _ => by omega
  | n + 1, l0, l, i, h1, h2, hi => by
      simp only [recsFrom]
      by_cases hl : l = l0
      · subst hl; exact List.mem_append_left _ (mem_recsOf st _ _ i hi)
      · exact List.mem_append_right _ (mem_recsFrom st Ds n (l0 + 1) l i (by omega) (by omega) hi)

theorem recsFrom_congr (st r : State ℝ≥0) (Ds Ds' : ℕ → DStr (Fin G.n) (WLab G s)) :
    ∀ (n l0 : ℕ), (∀ l, l0 ≤ l → l < l0 + n → Ds' l = Ds l ∧ base r l = base st l ∧
        ∀ x, base st l ≤ x → x < base st l + (Ds l).blocks.length → r.wa "dsl.stk" x = st.wa "dsl.stk" x) →
      recsFrom r Ds' l0 n = recsFrom st Ds l0 n
  | 0, _, _ => rfl
  | n + 1, l0, h => by
      simp only [recsFrom]
      obtain ⟨h1, h2, h3⟩ := h l0 le_rfl (by omega)
      rw [recsFrom_congr st r Ds Ds' n (l0 + 1) (fun l hl1 hl2 => h l (by omega) (by omega)), h1, h2]
      congr 1
      unfold recsOf
      congr 1
      apply List.map_congr_left
      intro i hi
      simp only [List.mem_range] at hi
      unfold stkId
      exact h3 _ (by omega) (by omega)

/-- bases are antitone in the level -/
theorem base_antitone {st : State ℝ≥0} {Ds : ℕ → DStr (Fin G.n) (WLab G s)} {lo k : ℕ}
    (hch : ∀ j < k, base st (lo + j) = base st (lo + j + 1) + (Ds (lo + j + 1)).blocks.length) :
    ∀ i j, i ≤ j → j ≤ k → base st (lo + j) ≤ base st (lo + i)
  | i, j, hij, hjk => by
      induction j with
      | zero => have : i = 0 := by omega
                subst this; exact le_rfl
      | succ j ih =>
        rcases Nat.lt_or_ge i (j + 1) with h | h
        · have := hch j (by omega)
          have := ih (by omega) (by omega)
          rw [show lo + (j + 1) = lo + j + 1 by omega]
          omega
        · have : i = j + 1 := by omega
          subst this; exact le_rfl

/-! ## Merge at the level of the whole D layer -/

/-- **Merge of the deepest active structure (level `lo`) into its parent (level `lo+1`)**, after
the caller has re-keyed the parent's front block (so `Ds (lo+1)` is the re-keyed parent). -/
theorem mergeDL {ops : VOps ℝ≥0} (st0 : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m))
    (V : Fin G.n → ℕ) (ecap bcap : ℕ) (L : Live (Fin G.n) (WLab G s)) (fresh : ℕ)
    (Ds : ℕ → DStr (Fin G.n) (WLab G s)) (lo k : ℕ) (hk : 1 ≤ k)
    (hDL : DLRep st0 H V ecap bcap L fresh Ds lo k) (keep : Bool) (g : ℕ)
    (hne : (Ds (lo + 1)).blocks ≠ [])
    (hS : GSide st0 (base st0 (lo + 1) + (Ds (lo + 1)).blocks.length + (Ds lo).blocks.length - 1)
      (stkId st0 (base st0 (lo + 1) + (Ds (lo + 1)).blocks.length) (Ds lo).blocks.length) (Ds lo).blocks)
    (hpb : st0.w "mg.pb" = base st0 (lo + 1)) (hpk : st0.w "mg.pk" = (Ds (lo + 1)).blocks.length)
    (hck : st0.w "mg.ck" = (Ds lo).blocks.length) (hg : st0.w "mg.g" = g)
    (hdr : st0.w "mg.drop" = (if keep then 0 else 1)) (hlv : st0.w "mg.lv" = lo + 1)
    (hszl : lo + 1 < st0.wlen "dsl.sz") :
    Runs ops mergeS st0 (fun r =>
      DLRep r H V ecap bcap L fresh (Function.update Ds (lo + 1) (mergedD (Ds (lo + 1)) (Ds lo) keep g))
        (lo + 1) (k - 1) ∧
      Unchanged st0 r ["dsl.stk", "blk.hd", "blk.tl", "blk.cnt", "ent.nxt", "dsl.sz"] []
        (mergeRegs ++ ["mg.w"]) [] ∧
      r.cost ≤ st0.cost + 17 * (Ds lo).blocks.length + 3 * (groupAux g none (Ds lo).blocks).length + 20) := by
  set pb := base st0 (lo + 1) with hpbd
  set P := (Ds (lo + 1)).blocks with hP
  have hchild : base st0 lo = pb + P.length := by
    have := hDL.chain 0 (by omega); simpa using this
  have hPd : DRep st0 H V bcap (lo + 1) pb (Ds (lo + 1)) := hDL.drep 1 (by omega)
  have hCd : DRep st0 H V bcap lo (pb + P.length) (Ds lo) := by
    rw [← hchild]; have := hDL.drep 0 (by omega); simpa using this
  set ext := recsFrom st0 Ds (lo + 2) (k - 1) with hext
  have hR : RecsOK st0 H V (recsOf st0 (pb + P.length) (Ds lo).blocks ++ (recsOf st0 pb P ++ ext)) := by
    have h := hDL.recs
    have e : recsFrom st0 Ds lo (k + 1) = recsOf st0 (pb + P.length) (Ds lo).blocks ++
        (recsOf st0 pb P ++ ext) := by
      rw [show k + 1 = (k - 1) + 1 + 1 by omega]
      simp only [recsFrom]
      rw [hchild, hext, show lo + 1 + 1 = lo + 2 by omega]
    rwa [e] at h
  refine (Runs.keep_len (mergeS_spec (ops := ops) st0 H V bcap (lo + 1) lo pb (Ds (lo + 1)) (Ds lo) keep g
    hne hPd hCd ext hR hS hpb hpk hck hg hdr hlv hszl) mergeS_noalloc).mono ?_
  rintro r ⟨⟨hD, hU, hc, ⟨ids, hRr, hrecs, hidsC⟩, hbelow, hszo⟩, hwl, hvl⟩
  have hwr : ∀ x, x ∉ mergeRegs ++ ["mg.w"] → r.w x = st0.w x := hU.wreg
  have hbase : ∀ l, base r l = base st0 l := by
    intro l; unfold base; rw [(hU.warr "dsl.base" (by simp)).1]
  have hanti := base_antitone hDL.chain
  have hbf : r.w "blk.fresh" = st0.w "blk.fresh" := hwr _ (by simp [mergeRegs])
  have hsubR : (recsFrom r (Function.update Ds (lo + 1) (mergedD (Ds (lo + 1)) (Ds lo) keep g)) (lo + 1)
      (k - 1 + 1)).Sublist (ids.zip (groupAux g none (Ds lo).blocks) ++ (recsOf st0 pb P ++ ext)) := by
    have hkk : k = (k - 1) + 1 := by omega
    have e1 : recsFrom r (Function.update Ds (lo + 1) (mergedD (Ds (lo + 1)) (Ds lo) keep g)) (lo + 1) k =
        recsOf r pb (mergedD (Ds (lo + 1)) (Ds lo) keep g).blocks ++
          recsFrom r (Function.update Ds (lo + 1) (mergedD (Ds (lo + 1)) (Ds lo) keep g)) (lo + 2) (k - 1) := by
      conv_lhs => rw [hkk]
      simp only [recsFrom, Function.update_self, hbase]
      rfl
    have e2 : recsFrom r (Function.update Ds (lo + 1) (mergedD (Ds (lo + 1)) (Ds lo) keep g)) (lo + 2) (k - 1) =
        ext := by
      rw [hext]
      apply recsFrom_congr
      intro l hl1 hl2
      refine ⟨by simp [Function.update_apply, show l ≠ lo + 1 by omega], hbase l, fun x hx1 hx2 => hbelow x ?_⟩
      have h1 := hDL.chain (l - lo - 1) (by omega)
      have h2 := hanti 1 (l - lo - 1) (by omega) (by omega)
      rw [show lo + (l - lo - 1) + 1 = l by omega] at h1
      omega
    rw [show k - 1 + 1 = k by omega]
    rw [e1, e2, hrecs]
    rw [List.append_assoc]
    exact List.Sublist.append_left (List.Sublist.append_right (List.drop_sublist _ _) _) _

  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hU, hc⟩
  · exact liveRep_of_arrays hDL.live (fun a ha => (hU.warr a (by
      simp only [poolArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with h | h | h | h | h | h <;> subst h <;> simp)).1) (hU.varr _ (by simp)).1 (hwl _)
  · exact poolRep_of hDL.pool (hwr _ (by simp [mergeRegs])) hwl hvl
  · exact blkArrs_of hDL.barr hwl hvl
  · rw [hwl]; have := hDL.basel; omega
  · rw [hbase, show lo + 1 + (k - 1) = lo + k by omega]; exact hDL.base0
  · intro j hj
    rw [hbase, hbase]
    simp only [Function.update_apply, show lo + 1 + j + 1 ≠ lo + 1 by omega, if_false]
    have := hDL.chain (j + 1) (by omega)
    rw [show lo + (j + 1) = lo + 1 + j by omega] at this
    exact this
  · intro j hj
    rw [hbase]
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simpa using hD
    · simp only [Function.update_apply, show lo + 1 + j ≠ lo + 1 by omega, if_false]
      have hd := hDL.drep (j + 1) (by omega)
      rw [show lo + (j + 1) = lo + 1 + j by omega] at hd
      have hlow : base st0 (lo + 1 + j) + (Ds (lo + 1 + j)).blocks.length ≤ pb := by
        have h1 := hDL.chain j (by omega)
        have h2 := hanti 1 j (by omega) (by omega)
        rw [show lo + j + 1 = lo + 1 + j by omega] at h1
        omega
      refine DRep.of_frame hd (fun x hx1 hx2 => hbelow x (by omega))
        (hszo _ (by omega)) hwl (fun i hi => ?_)
      exact hRr.2.1 _ (List.mem_append_right _ (List.mem_append_right _
        (mem_recsFrom st0 Ds (k - 1) (lo + 2) (lo + 1 + j) i (by omega) (by omega) hi)))
  · rw [show k - 1 + 1 = k by omega] at hsubR ⊢
    exact RecsOK.sublist hRr hsubR
  · intro p hp
    rw [hbf]
    have hp' := hsubR.subset hp
    rcases List.mem_append.mp hp' with hp' | hp'
    · obtain ⟨x, y⟩ := p
      have hx := (List.of_mem_zip hp').1
      obtain ⟨j, hj, hxj⟩ := hidsC x hx
      have hmem := mem_recsFrom st0 Ds (k + 1) lo lo j le_rfl (by omega) hj
      have := hDL.bfresh _ hmem
      simp only at this ⊢
      rw [hxj, ← hchild]; exact this
    · have e : recsFrom st0 Ds lo (k + 1) = recsOf st0 (pb + P.length) (Ds lo).blocks ++
          (recsOf st0 pb P ++ ext) := by
        rw [show k + 1 = (k - 1) + 1 + 1 by omega]
        simp only [recsFrom]
        rw [hchild, hext, show lo + 1 + 1 = lo + 2 by omega]
      exact hDL.bfresh p (by rw [e]; exact List.mem_append_right _ hp')
  · rw [hbf]; exact hDL.bfcap

/-! ## New structure (child of the deepest active level) -/

def newChildS : Stmt :=
  seq (wset "nw.b" (add (load "dsl.base" (var "nw.pl")) (load "dsl.sz" (var "nw.pl"))))
  (seq (wstore "dsl.base" (var "nw.lv") (var "nw.b"))
  (seq (wset "nw.id" (var "blk.fresh"))
  (seq (wset "blk.fresh" (add (var "blk.fresh") (lit 1)))
  (seq (wstore "blk.hd" (var "nw.id") (lit 0))
  (seq (wstore "blk.tl" (var "nw.id") (lit 0))
  (seq (wstore "blk.cnt" (var "nw.id") (lit 0))
  (seq (wstore "blk.bot" (var "nw.id") (lit 1))
  (seq (wstore "dsl.stk" (var "nw.b") (var "nw.id"))
       (wstore "dsl.sz" (var "nw.lv") (lit 1))))))))))

/-- block records only depend on their own fields, the separator label arrays and the pool -/
theorem blkRep_of_point {q r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bid : ℕ} {b : Block (Fin G.n) (WLab G s)} (h : BlkRep q H V bid b)
    (hF : ∀ a ∈ ["blk.hd", "blk.tl", "blk.cnt", "blk.bot"], r.wa a bid = q.wa a bid)
    (hA : ∀ a ∈ ["blk.h", "blk.v", "blk.e", "blk.r", "ent.nxt", "ent.key", "ent.h", "ent.v", "ent.e",
      "ent.r"], r.wa a = q.wa a)
    (hV1 : r.va "ent.len" = q.va "ent.len") (hV2 : r.va "blk.len" = q.va "blk.len")
    (hlen : r.wlen "ent.nxt" = q.wlen "ent.nxt") : BlkRep r H V bid b := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1.of_eq (hF _ (by simp)) (by rw [show blkA.l = "blk.len" from rfl, hV2])
    (by rw [hA _ (by simp [blkA])]) (by rw [hA _ (by simp [blkA])])
    (by rw [hA _ (by simp [blkA])]) (by rw [hA _ (by simp [blkA])]), ?_,
    fun x hx => (h3 x hx).of_eq (by rw [hA _ (by simp)])
      (by rw [show entA.l = "ent.len" from rfl, hV1]) (by rw [hA _ (by simp [entA])])
      (by rw [hA _ (by simp [entA])]) (by rw [hA _ (by simp [entA])])
      (by rw [hA _ (by simp [entA])]), by rw [hF _ (by simp)]; exact h4,
    by rw [hF _ (by simp)]; exact h5⟩
  rw [hF _ (by simp)]
  exact h2.of_eq (fun j _ => by rw [hA _ (by simp)]) (le_of_eq hlen.symm)

/-- **New structure `⟨M, Bd, [⟨⊥, []⟩]⟩` at level `lo - 1`**, on top of the deepest active level `lo`. -/
theorem newDL {ops : VOps ℝ≥0} (st0 : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m))
    (V : Fin G.n → ℕ) (ecap bcap : ℕ) (L : Live (Fin G.n) (WLab G s)) (fresh : ℕ)
    (Ds : ℕ → DStr (Fin G.n) (WLab G s)) (lo k : ℕ) (M : ℕ) (Bd : WLab G s) (hlo : 1 ≤ lo)
    (hDL : DLRep st0 H V ecap bcap L fresh Ds lo k)
    (hpl : st0.w "nw.pl" = lo) (hlv : st0.w "nw.lv" = lo - 1)
    (hstk : base st0 lo + (Ds lo).blocks.length < st0.wlen "dsl.stk")
    (hbf : st0.w "blk.fresh" < bcap) (hszl : lo - 1 < st0.wlen "dsl.sz")
    (hcap : base st0 lo + (Ds lo).blocks.length + bcap + 2 < st0.cap) :
    Runs ops newChildS st0 (fun r =>
      DLRep r H V ecap bcap L fresh (Function.update Ds (lo - 1) ⟨M, Bd, [⟨⊥, []⟩]⟩) (lo - 1) (k + 1) ∧
      r.cost = st0.cost + 10) := by
  set b := base st0 lo + (Ds lo).blocks.length with hb
  set nb := st0.w "blk.fresh" with hnb
  have hbl := hDL.basel
  have hszlo : lo < st0.wlen "dsl.sz" := (hDL.drep 0 (by omega)).szb
  have hbase_lo : st0.wa "dsl.base" lo = base st0 lo := rfl
  have hsz_lo : st0.wa "dsl.sz" lo = (Ds lo).blocks.length := by
    have := (hDL.drep 0 (by omega)).sz; simpa using this
  have hc0 : 0 < st0.cap := by omega
  have hc1 : 1 < st0.cap := by omega
  have hbarr := hDL.barr
  obtain ⟨ba1, ba2, ba3, ba4, -, -, -, -, -⟩ := hbarr
  apply wp_sound
  simp [newChildS, wp, hpl, hlv, fit, hc0, hc1, show lo < st0.wlen "dsl.base" by omega, hbase_lo,
    hszlo, hsz_lo, show b < st0.cap by omega, show lo - 1 < st0.wlen "dsl.base" by omega,
    show nb + 1 < st0.cap by omega, show nb < st0.wlen "blk.hd" by omega,
    show nb < st0.wlen "blk.tl" by omega, show nb < st0.wlen "blk.cnt" by omega,
    show nb < st0.wlen "blk.bot" by omega, hstk, hszl, hb.symm, hnb.symm]
  set R := ((((((((((((((((((((st0).setW "nw.b" b).charge 1).storeW "dsl.base" (lo - 1) b).charge 1).setW "nw.id" nb).charge 1).setW "blk.fresh" (nb + 1)).charge 1).storeW "blk.hd" nb 0).charge 1).storeW "blk.tl" nb 0).charge 1).storeW "blk.cnt" nb 0).charge 1).storeW "blk.bot" nb 1).charge 1).storeW "dsl.stk" b nb).charge 1).storeW "dsl.sz" (lo - 1) 1).charge 1 with hR
  have hRl : ∀ a, R.wlen a = st0.wlen a := by intro a; simp [hR]
  have hRvl : ∀ a, R.vlen a = st0.vlen a := by intro a; simp [hR]
  have hRva : R.va = st0.va := by simp [hR]
  have hRwa : ∀ a, a ∉ ["dsl.base", "blk.hd", "blk.tl", "blk.cnt", "blk.bot", "dsl.stk", "dsl.sz"] →
      R.wa a = st0.wa a := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ha
    funext j; simp [hR, h1, h2, h3, h4, h5, h6, h7]
  have hRbase : ∀ l, l ≠ lo - 1 → base R l = base st0 l := by intro l hl; simp [base, hR, hl]
  have hRbase' : base R (lo - 1) = b := by simp [base, hR]
  have hRsz : ∀ l, l ≠ lo - 1 → R.wa "dsl.sz" l = st0.wa "dsl.sz" l := by intro l hl; simp [hR, hl]
  have hRstk : ∀ x, x ≠ b → R.wa "dsl.stk" x = st0.wa "dsl.stk" x := by intro x hx; simp [hR, hx]
  have hRfld : ∀ a ∈ ["blk.hd", "blk.tl", "blk.cnt", "blk.bot"], ∀ x, x ≠ nb → R.wa a x = st0.wa a x := by
    intro a ha x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> simp [hR, hx]
  have hdisj : ∀ a ∈ ["blk.h", "blk.v", "blk.e", "blk.r", "ent.nxt", "ent.key", "ent.h", "ent.v",
      "ent.e", "ent.r"], a ∉ ["dsl.base", "blk.hd", "blk.tl", "blk.cnt", "blk.bot", "dsl.stk", "dsl.sz"] := by
    decide
  -- old records keep their representation
  have hold : ∀ p ∈ recsFrom st0 Ds lo (k + 1), BlkRep R H V p.1 p.2 := by
    intro p hp
    have hne : p.1 ≠ nb := by have := hDL.bfresh p hp; omega
    exact blkRep_of_point (hDL.recs.2.1 p hp) (fun a ha => hRfld a ha _ hne)
      (fun a ha => hRwa a (hdisj a ha)) (by rw [hRva]) (by rw [hRva]) (hRl _)
  have hanti := base_antitone hDL.chain
  -- every old slice lies below `b`
  have hslice : ∀ j ≤ k, base st0 (lo + j) + (Ds (lo + j)).blocks.length ≤ b := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hjp
    · simp [hb]
    · have h1 := hDL.chain (j - 1) (by omega)
      rw [show lo + (j - 1) + 1 = lo + j by omega] at h1
      have h2 := hanti 0 (j - 1) (by omega) (by omega)
      simp only [add_zero] at h2
      omega
  have hcongr : recsFrom R (Function.update Ds (lo - 1) ⟨M, Bd, [⟨⊥, []⟩]⟩) lo (k + 1) =
      recsFrom st0 Ds lo (k + 1) := by
    apply recsFrom_congr
    intro l hl1 hl2
    refine ⟨by simp [Function.update_apply, show l ≠ lo - 1 by omega], hRbase l (by omega),
      fun x hx1 hx2 => hRstk x ?_⟩
    have := hslice (l - lo) (by omega)
    rw [show lo + (l - lo) = l by omega] at this
    omega
  have hnewB : BlkRep R H V nb (⟨⊥, []⟩ : Block (Fin G.n) (WLab G s)) := by
    refine ⟨⟨by simp [hR], Or.inl rfl⟩, ?_, by simp, by simp [hR], by simp [hR, tlWord]⟩
    have : R.wa "blk.hd" nb = 0 := by simp [hR]
    simp only [List.map_nil]; rw [this]; exact LList.nil
  have hkk : lo - 1 + (k + 1) = lo + k := by omega
  have hrecsR : recsFrom R (Function.update Ds (lo - 1) ⟨M, Bd, [⟨⊥, []⟩]⟩) (lo - 1) (k + 1 + 1) =
      (nb, (⟨⊥, []⟩ : Block (Fin G.n) (WLab G s))) :: recsFrom st0 Ds lo (k + 1) := by
    have e : recsFrom R (Function.update Ds (lo - 1) ⟨M, Bd, [⟨⊥, []⟩]⟩) (lo - 1) (k + 1 + 1) =
        recsOf R (base R (lo - 1)) ((Function.update Ds (lo - 1) ⟨M, Bd, [⟨⊥, []⟩]⟩) (lo - 1)).blocks ++
          recsFrom R (Function.update Ds (lo - 1) ⟨M, Bd, [⟨⊥, []⟩]⟩) (lo - 1 + 1) (k + 1) := rfl
    rw [e, show lo - 1 + 1 = lo by omega, hcongr, hRbase', Function.update_self]
    simp [recsOf, stkId, hR]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact liveRep_of_arrays hDL.live (fun a ha => hRwa a (by revert a; decide)) (by rw [hRva]) (hRl _)
  · exact poolRep_of hDL.pool (by simp [hR]) hRl hRvl
  · exact blkArrs_of hDL.barr hRl hRvl
  · rw [hRl, hkk]; exact hDL.basel
  · rw [hkk, hRbase _ (by omega)]; exact hDL.base0
  · intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hjp
    · simp only [add_zero, Function.update_apply, show lo - 1 + 1 ≠ lo - 1 by omega, if_false]
      rw [hRbase', show lo - 1 + 1 = lo by omega, hRbase _ (by omega)]
    · simp only [Function.update_apply, show lo - 1 + j + 1 ≠ lo - 1 by omega, if_false]
      rw [hRbase _ (by omega), hRbase _ (by omega)]
      have := hDL.chain (j - 1) (by omega)
      rw [show lo + (j - 1) = lo - 1 + j by omega, show lo - 1 + j + 1 = lo + (j - 1) + 1 by omega] at *
      exact this
  · intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hjp
    · simp only [add_zero, Function.update_self]
      rw [hRbase']
      refine ⟨by simp [hR], by rw [hRl]; exact hszl, by rw [hRl]; simp; omega, fun i hi => ?_,
        fun i j hi hj _ => by simp at hi hj; omega, fun i hi => ?_⟩
      · simp at hi; subst hi
        show BlkRep R H V (stkId R b 1 0) (⟨⊥, []⟩ : Block (Fin G.n) (WLab G s))
        have : stkId R b 1 0 = nb := by simp [stkId, hR]
        rw [this]; exact hnewB
      · simp at hi; subst hi; simp [stkId, hR]; exact hbf
    · simp only [Function.update_apply, show lo - 1 + j ≠ lo - 1 by omega, if_false]
      rw [hRbase _ (by omega)]
      have hd := hDL.drep (j - 1) (by omega)
      rw [show lo + (j - 1) = lo - 1 + j by omega] at hd
      have hsl := hslice (j - 1) (by omega)
      rw [show lo + (j - 1) = lo - 1 + j by omega] at hsl
      refine DRep.of_frame hd (fun x hx1 hx2 => hRstk x (by omega)) (hRsz _ (by omega)) hRl
        (fun i hi => hold (stkId st0 (base st0 (lo - 1 + j)) (Ds (lo - 1 + j)).blocks.length i,
          (Ds (lo - 1 + j)).blocks[i]) (mem_recsFrom st0 Ds (k + 1) lo (lo - 1 + j) i (by omega) (by omega) hi))
  · rw [hrecsR]
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨fun h => ?_, hDL.recs.1⟩
      obtain ⟨p, hp, hp1⟩ := List.mem_map.mp h
      have := hDL.bfresh p hp
      omega
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hnewB
      · exact hold p hp
    · simp only [List.map_cons, entIds_cons, List.map_nil, List.nil_append]
      exact hDL.recs.2.2
  · rw [hrecsR]
    intro p hp
    have hf : R.w "blk.fresh" = nb + 1 := by simp [hR]
    rw [hf]
    rcases List.mem_cons.mp hp with rfl | hp
    · simp
    · have := hDL.bfresh p hp; omega
  · have hf : R.w "blk.fresh" = nb + 1 := by simp [hR]
    rw [hf]; omega

/-! ## Delete: clear the live pointers of the keys in a row -/

def delBody (arr : String) : Stmt :=
  seq (wset "dd.v" (load arr (add (var "dd.off") (var "dd.j"))))
  (seq (wstore "live" (var "dd.v") (lit 0)) (wset "dd.j" (add (var "dd.j") (lit 1))))

def delLoop (arr : String) : Stmt := .while (lt (var "dd.j") (var "dd.len")) (delBody arr)

def delS (arr : String) : Stmt := seq (wset "dd.j" (lit 0)) (delLoop arr)

/-- invariant of the delete loop after `j` keys -/
structure DInv (st0 q : State ℝ≥0) (arr : String) (ks : List (Fin G.n)) (j : ℕ) : Prop where
  jr : q.w "dd.j" = j
  jle : j ≤ ks.length
  live : ∀ v : Fin G.n, q.wa "live" v = if v ∈ ks.take j then 0 else st0.wa "live" v
  livelen : q.wlen "live" = st0.wlen "live"
  unch : Unchanged st0 q ["live"] [] ["dd.j", "dd.v"] []

theorem del_loop {ops : VOps ℝ≥0} (st0 : State ℝ≥0) (arr : String) (ks : List (Fin G.n)) (off : ℕ)
    (hsp : Spells st0 arr off (ks.map (·.val))) (hoff : st0.w "dd.off" = off)
    (hlen : st0.w "dd.len" = ks.length) (harr : off + ks.length ≤ st0.wlen arr)
    (hlive : G.n ≤ st0.wlen "live") (hcap : off + ks.length + 1 < st0.cap) (harrne : arr ≠ "live") :
    ∀ (n j : ℕ) (q : State ℝ≥0), ks.length - j = n → DInv st0 q arr ks j →
      Runs ops (delLoop arr) q (fun r => DInv st0 r arr ks ks.length ∧ r.cost ≤ q.cost + 4 * n + 1)
  | 0, j, q, hn, hI => by
      have hj : j = ks.length := by have := hI.jle; omega
      subst hj
      have hc1 : 1 < q.cap := by rw [hI.unch.cap]; omega
      have hlq : q.w "dd.len" = ks.length := by rw [hI.unch.wreg _ (by simp)]; exact hlen
      refine runs_while_exit (by simp [hI.jr, hlq, fit, hc1, show q.cap ≠ 0 by omega]) ?_
      exact ⟨⟨by simp [hI.jr], le_rfl, fun v => by simp [hI.live v], by simp [hI.livelen],
        (unch_charge 1).mpr hI.unch⟩, by simp⟩
  | n + 1, j, q, hn, hI => by
      have hj : j < ks.length := by omega
      have hcq : q.cap = st0.cap := hI.unch.cap
      have hc1 : 1 < q.cap := by omega
      have hlq : q.w "dd.len" = ks.length := by rw [hI.unch.wreg _ (by simp)]; exact hlen
      have hoq : q.w "dd.off" = off := by rw [hI.unch.wreg _ (by simp)]; exact hoff
      have harrq : q.wa arr = st0.wa arr := (hI.unch.warr arr (by simpa using harrne)).1
      have harrl : q.wlen arr = st0.wlen arr := (hI.unch.warr arr (by simpa using harrne)).2
      have hkj : q.wa arr (off + j) = (ks[j]).val := by
        rw [harrq]; have := hsp j (by simpa using hj); simpa using this
      have hv : (ks[j]).val < q.wlen "live" := by rw [hI.livelen]; have := (ks[j]).isLt; omega
      refine runs_while_step (x := 1) (by simp [hI.jr, hlq, fit, hc1, hj]) one_ne_zero ?_
      apply wp_sound
      simp [delBody, wp, hoq, hI.jr, fit, show off + j < q.cap by omega, show off + j < q.wlen arr by omega,
        hkj, hv, hc1, show j + 1 < q.cap by omega, show 0 < q.cap by omega]
      refine (del_loop st0 arr ks off hsp hoff hlen harr hlive hcap harrne n (j + 1) _ (by omega) ?_).mono ?_
      · refine ⟨by simp, by omega, fun v => ?_, by simp [hI.livelen], ?_⟩
        · rw [List.take_succ_eq_append_getElem hj]
          by_cases hvk : v = ks[j]
          · subst hvk
            simp only [State.charge_wa, State.setW_wa, State.storeW_wa, true_and, if_true]
            rw [if_pos (List.mem_append_right _ (List.mem_singleton_self _))]
          · have hne : (v : ℕ) ≠ (ks[j]).val := fun h => hvk (Fin.ext h)
            simp only [State.charge_wa, State.setW_wa, State.storeW_wa, true_and]
            rw [if_neg hne, hI.live v]
            simp only [List.mem_append, List.mem_singleton, hvk, or_false]
        · rw [unch_charge, unch_setW (by simp), unch_charge, unch_storeW (by simp), unch_charge,
            unch_setW (by simp), unch_charge]
          exact hI.unch
      · rintro r ⟨h1, h2⟩
        exact ⟨h1, by simp at h2; omega⟩

/-- **Delete** of the keys `ks` spelled by `arr[dd.off, dd.off + dd.len)`: the D layer now
represents the live map `clearKeys L ks` (`= (DB.deleteKeys L ks).1`); cost `≤ 4|ks| + 3`. -/
theorem delDL {ops : VOps ℝ≥0} (st0 : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m))
    (V : Fin G.n → ℕ) (ecap bcap : ℕ) (L : Live (Fin G.n) (WLab G s)) (fresh : ℕ)
    (Ds : ℕ → DStr (Fin G.n) (WLab G s)) (lo k : ℕ) (hDL : DLRep st0 H V ecap bcap L fresh Ds lo k)
    (arr : String) (ks : List (Fin G.n)) (off : ℕ) (hsp : Spells st0 arr off (ks.map (·.val)))
    (hoff : st0.w "dd.off" = off) (hlen : st0.w "dd.len" = ks.length)
    (harr : off + ks.length ≤ st0.wlen arr) (hcap : off + ks.length + 1 < st0.cap)
    (harrne : arr ≠ "live") :
    Runs ops (delS arr) st0 (fun r => DLRep r H V ecap bcap (clearKeys L ks) fresh Ds lo k ∧
      Unchanged st0 r ["live"] [] ["dd.j", "dd.v"] [] ∧ r.cost ≤ st0.cost + 4 * ks.length + 3) := by
  have hc0 : 0 < st0.cap := by omega
  apply wp_sound
  rw [delS, LabRAM.wp_seq, LabRAM.wp_wset_of (a := 0) (by simp [fit, hc0])]
  set q := (st0.setW "dd.j" 0).charge 1 with hq
  have hI0 : DInv st0 q arr ks 0 := ⟨by simp [hq], Nat.zero_le _, fun v => by simp [hq], by simp [hq],
    by rw [hq, unch_charge, unch_setW (by simp)]; exact Unchanged.refl _ _ _ _ _⟩
  show Runs ops (delLoop arr) q _
  refine (del_loop (ops := ops) st0 arr ks off hsp hoff hlen harr hDL.live.1 hcap harrne ks.length 0 q
    (by simp) hI0).mono ?_
  rintro r ⟨hI, hc⟩
  have hU := hI.unch
  have hwa : ∀ a, a ≠ "live" → r.wa a = st0.wa a := fun a ha => (hU.warr a (by simpa using ha)).1
  have hwl : ∀ a, r.wlen a = st0.wlen a := by
    intro a; by_cases ha : a = "live"
    · subst ha; exact hI.livelen
    · exact (hU.warr a (by simpa using ha)).2
  have hvl : ∀ a, r.vlen a = st0.vlen a := fun a => (hU.varr a (by simp)).2
  have hva : ∀ a, r.va a = st0.va a := fun a => (hU.varr a (by simp)).1
  have hbase : ∀ l, base r l = base st0 l := by intro l; unfold base; rw [hwa _ (by simp)]
  have hrf : recsFrom r Ds lo (k + 1) = recsFrom st0 Ds lo (k + 1) := by
    apply recsFrom_congr
    intro l _ _
    exact ⟨rfl, hbase l, fun x _ _ => by rw [hwa _ (by simp)]⟩
  have hkeep : ∀ a ∈ bArrs, r.wa a = st0.wa a := by
    intro a ha; apply hwa; intro h; subst h; simp [bArrs] at ha
  refine ⟨⟨?_, poolRep_of hDL.pool (hU.wreg _ (by simp)) hwl hvl, blkArrs_of hDL.barr hwl hvl,
    by rw [hwl]; exact hDL.basel, by rw [hbase]; exact hDL.base0,
    fun j hj => by rw [hbase, hbase]; exact hDL.chain j hj, fun j hj => ?_, ?_, ?_,
    by rw [hU.wreg _ (by simp)]; exact hDL.bfcap⟩, hU, by
      have hqc : q.cost = st0.cost + 1 := by simp [hq]
      omega⟩
  · -- the live map
    refine ⟨by rw [hwl]; exact hDL.live.1, fun v => ⟨?_, ?_⟩⟩
    · rw [hI.live v, List.take_length, (hDL.live.2 v).1]
      simp only [clearKeys]
      split_ifs <;> simp [liveWord]
    · intro i a hv
      have hv' : L v = some (i, a) := by
        simp only [clearKeys] at hv
        split_ifs at hv
        exact hv
      exact ((hDL.live.2 v).2 i a hv').of_eq (by rw [hwa _ (by simp)])
          (by rw [show entA.l = "ent.len" from rfl, hva]) (by rw [hwa _ (by simp [entA])])
          (by rw [hwa _ (by simp [entA])]) (by rw [hwa _ (by simp [entA])])
          (by rw [hwa _ (by simp [entA])])
  · rw [hbase]
    exact DRep.of_frame (hDL.drep j hj) (fun x _ _ => by rw [hwa _ (by simp)])
      (by rw [hwa _ (by simp)]) hwl (fun i hi => blkRep_of_arrays
        ((hDL.drep j hj).blk i hi) hkeep (hva _) (hva _) (hwl _))
  · rw [hrf]; exact recsOK_of_arrays hDL.recs hkeep (hva _) (hva _) (hwl _)
  · rw [hrf, hU.wreg _ (by simp)]; exact hDL.bfresh

/-! ## Allocation of the D layer and the top-level structure -/

/-- one-time allocation of all D arrays: `live` (size `n`), the entry pool (`ad.ec`), the block
records (`ad.bc`), the stack (`ad.sc`), the level tables (`ad.lc`); counters `ds.fresh`, `blk.fresh` -/
def allocD : Stmt :=
  seq (walloc "live" (var "n"))
  (seq (walloc "ent.key" (var "ad.ec")) (seq (walloc "ent.nxt" (var "ad.ec"))
  (seq (walloc "ent.h" (var "ad.ec")) (seq (walloc "ent.v" (var "ad.ec"))
  (seq (walloc "ent.e" (var "ad.ec")) (seq (walloc "ent.r" (var "ad.ec"))
  (seq (valloc "ent.len" (var "ad.ec"))
  (seq (walloc "blk.hd" (var "ad.bc")) (seq (walloc "blk.tl" (var "ad.bc"))
  (seq (walloc "blk.cnt" (var "ad.bc")) (seq (walloc "blk.bot" (var "ad.bc"))
  (seq (walloc "blk.h" (var "ad.bc")) (seq (walloc "blk.v" (var "ad.bc"))
  (seq (walloc "blk.e" (var "ad.bc")) (seq (walloc "blk.r" (var "ad.bc"))
  (seq (valloc "blk.len" (var "ad.bc"))
  (seq (walloc "dsl.stk" (var "ad.sc")) (seq (walloc "dsl.sz" (var "ad.lc"))
  (seq (walloc "dsl.base" (var "ad.lc"))
  (seq (wset "ds.fresh" (lit 0)) (wset "blk.fresh" (lit 0))))))))))))))))))))))

/-- the empty D layer -/
structure EmptyD (st : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (ecap bcap scap lcap : ℕ) : Prop where
  live : LiveRep st H V (fun _ => none : Live (Fin G.n) (WLab G s))
  pool : PoolRep st 0 ecap
  barr : BlkArrs st bcap
  stkl : scap ≤ st.wlen "dsl.stk"
  szl : lcap ≤ st.wlen "dsl.sz"
  basel : lcap ≤ st.wlen "dsl.base"
  bf : st.w "blk.fresh" = 0

theorem allocD_spec {ops : VOps ℝ≥0} (st0 : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m))
    (V : Fin G.n → ℕ) (ecap bcap scap lcap : ℕ) (hn : st0.w "n" = G.n) (hec : st0.w "ad.ec" = ecap)
    (hbc : st0.w "ad.bc" = bcap) (hsc : st0.w "ad.sc" = scap) (hlc : st0.w "ad.lc" = lcap)
    (hpos : 0 < ecap) (hcap : 1 < st0.cap) :
    Runs ops allocD st0 (fun r => EmptyD (s := s) r H V ecap bcap scap lcap ∧
      r.cost = st0.cost + (G.n + 7 * ecap + 9 * bcap + scap + 2 * lcap) + 22) := by
  apply wp_sound
  simp [allocD, wp, hn, hec, hbc, hsc, hlc, fit, hcap, show 0 < st0.cap by omega]
  refine ⟨⟨⟨by simp, fun v => ⟨by simp [liveWord], fun i a h => by simp at h⟩⟩,
    ⟨by simp, hpos, by simp [EntArrs, entA]⟩, by simp [BlkArrs, blkA], by simp, by simp, by simp, by simp⟩,
    by ring⟩

/-- the top-level structure at level `nw.lv`, base `0` -/
def newTopS : Stmt :=
  seq (wstore "dsl.base" (var "nw.lv") (lit 0))
  (seq (wset "nw.id" (var "blk.fresh"))
  (seq (wset "blk.fresh" (add (var "blk.fresh") (lit 1)))
  (seq (wstore "blk.hd" (var "nw.id") (lit 0))
  (seq (wstore "blk.tl" (var "nw.id") (lit 0))
  (seq (wstore "blk.cnt" (var "nw.id") (lit 0))
  (seq (wstore "blk.bot" (var "nw.id") (lit 1))
  (seq (wstore "dsl.stk" (lit 0) (var "nw.id"))
       (wstore "dsl.sz" (var "nw.lv") (lit 1)))))))))

/-- **the top-level structure** `⟨M, Bd, [⟨⊥, []⟩]⟩` at level `hi` of an empty D layer -/
theorem newTopDL {ops : VOps ℝ≥0} (st0 : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m))
    (V : Fin G.n → ℕ) (ecap bcap scap lcap : ℕ) (Ds : ℕ → DStr (Fin G.n) (WLab G s)) (hi M : ℕ)
    (Bd : WLab G s) (hE : EmptyD (s := s) st0 H V ecap bcap scap lcap) (hlv : st0.w "nw.lv" = hi)
    (hhi : hi < lcap) (hsc : 1 ≤ scap) (hbc : 1 ≤ bcap) (hcap : 2 < st0.cap) :
    Runs ops newTopS st0 (fun r =>
      DLRep r H V ecap bcap (fun _ => none) 0 (Function.update Ds hi ⟨M, Bd, [⟨⊥, []⟩]⟩) hi 0 ∧
      r.cost = st0.cost + 9) := by
  obtain ⟨hlive, hpool, hbarr, hstkl, hszl, hbasel, hbf⟩ := hE
  have ba1 := hbarr.1
  have ba2 := hbarr.2.1
  have ba3 := hbarr.2.2.1
  have ba4 := hbarr.2.2.2.1
  have hc0 : 0 < st0.cap := by omega
  have hc1 : 1 < st0.cap := by omega
  apply wp_sound
  simp [newTopS, wp, hlv, hbf, fit, hc0, hc1, show hi < st0.wlen "dsl.base" by omega,
    show 0 < st0.wlen "blk.hd" by omega, show 0 < st0.wlen "blk.tl" by omega,
    show 0 < st0.wlen "blk.cnt" by omega, show 0 < st0.wlen "blk.bot" by omega,
    show 0 < st0.wlen "dsl.stk" by omega, show hi < st0.wlen "dsl.sz" by omega]
  set R := ((((((((((((((((((st0).storeW "dsl.base" hi 0).charge 1).setW "nw.id" 0).charge 1).setW "blk.fresh" 1).charge 1).storeW "blk.hd" 0 0).charge 1).storeW "blk.tl" 0 0).charge 1).storeW "blk.cnt" 0 0).charge 1).storeW "blk.bot" 0 1).charge 1).storeW "dsl.stk" 0 0).charge 1).storeW "dsl.sz" hi 1).charge 1 with hR
  have hRl : ∀ a, R.wlen a = st0.wlen a := by intro a; simp [hR]
  have hRvl : ∀ a, R.vlen a = st0.vlen a := by intro a; simp [hR]
  have hRva : R.va = st0.va := by simp [hR]
  have hRwa : ∀ a, a ∉ ["dsl.base", "blk.hd", "blk.tl", "blk.cnt", "blk.bot", "dsl.stk", "dsl.sz"] →
      R.wa a = st0.wa a := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ha
    funext j; simp [hR, h1, h2, h3, h4, h5, h6, h7]
  have hnewB : BlkRep R H V 0 (⟨⊥, []⟩ : Block (Fin G.n) (WLab G s)) := by
    refine ⟨⟨by simp [hR], Or.inl rfl⟩, ?_, by simp, by simp [hR], by simp [hR, tlWord]⟩
    have : R.wa "blk.hd" 0 = 0 := by simp [hR]
    simp only [List.map_nil]; rw [this]; exact LList.nil
  have hbase : base R hi = 0 := by simp [base, hR]
  have hrecs : recsFrom R (Function.update Ds hi ⟨M, Bd, [⟨⊥, []⟩]⟩) hi (0 + 1) =
      [(0, (⟨⊥, []⟩ : Block (Fin G.n) (WLab G s)))] := by
    simp only [recsFrom, Function.update_self, List.append_nil]
    rw [hbase]
    simp [recsOf, stkId, hR]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun j hj => absurd hj (Nat.not_lt_zero _), ?_, ?_, ?_, ?_⟩
  · exact liveRep_of_arrays hlive (fun a ha => hRwa a (by revert a; decide)) (by rw [hRva]) (hRl _)
  · exact poolRep_of hpool (by simp [hR]) hRl hRvl
  · exact blkArrs_of hbarr hRl hRvl
  · rw [hRl]; omega
  · simpa using hbase
  · intro j hj
    have : j = 0 := by omega
    subst this
    simp only [add_zero, Function.update_self]
    rw [hbase]
    refine ⟨by simp [hR], by rw [hRl]; omega, by rw [hRl]; simp; omega, fun i hi => ?_,
      fun i j hi hj _ => by simp at hi hj; omega, fun i hi => ?_⟩
    · simp at hi; subst hi
      show BlkRep R H V (stkId R 0 1 0) (⟨⊥, []⟩ : Block (Fin G.n) (WLab G s))
      have : stkId R 0 1 0 = 0 := by simp [stkId, hR]
      rw [this]; exact hnewB
    · simp at hi; subst hi; simp [stkId, hR]; omega
  · rw [hrecs]
    refine ⟨by simp, fun p hp => ?_, by simp [entIds]⟩
    simp at hp; subst hp; exact hnewB
  · rw [hrecs]; intro p hp; simp at hp; subst hp; simp [hR]
  · simp [hR]; omega

end Frontier.CHD.DGlob
