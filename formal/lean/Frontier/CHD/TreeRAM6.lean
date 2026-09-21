import Frontier.CHD.TreeRAM5
import Frontier.CHD.WFrame

/-!
# Frontier.CHD.TreeRAM6 — (T2) `mergeTree` at RAM level (owner agent-03)

**NON-GATE** (Layer B).  On a contact `(u, v)` of the search `K` (root `x`, first-discovery parents `kpar`),
`mergeProg` appends `P ++ K.filter (∉ P)` (`P = kpath kpar x |K| u`) to the tree `t = tr.tid[v]` of the contact
head, re-rooting `P` at the contact edge — agent-05's `mergeTree`: path walk (`pwLoop`), rest pass (`rpLoop`),
tail/length update, path clear (`pcLoop`).  `mergeProg_spec`: `ForestRep` of the merged forest
`trees.map (if v ∈ T.ord then mergeRec T … else T)`, the syntactic frame (`WFr`), cost `≤ 33|K| + 40`.
-/

namespace Frontier.CHD.PartitionRAM

open Frontier Frontier.RAM Frontier.CHD.Partition

variable {V : Type} {ops : VOps V}

/-- The merged tree (agent-05's `mergeTree`, over `Fin N`). -/
def mergeRec {N : ℕ} (Tr : TreeRec (Fin N)) (K : List (Fin N)) (kpar : Fin N → Fin N) (x u v : Fin N) :
    TreeRec (Fin N) :=
  { root := Tr.root,
    ord := Tr.ord ++ kpath kpar x K.length u ++ K.filter (fun y => y ∉ kpath kpar x K.length u),
    par := reroot (kpath kpar x K.length u) v (fun w => if w ∈ K then kpar w else Tr.par w) }

/-- Locate the tree of the contact head; start the path walk at `u` with fuel `|K|`. -/
def mergePre : Stmt :=
  .seq (.wset "tr.t" (.load "tr.tid" (.var "fp.cv"))) <|
  .seq (.wset "tr.pv" (.load "tr.tl" (.var "tr.t"))) <|
  .seq (.wset "tr.u" (.var "fp.cv")) <|
  .seq (.wset "tr.c" (.var "fp.cu")) <|
  .seq (.wset "tr.f" (.var "fp.kl"))
       (.wset "tr.x" (.lit 1))

/-- New tail and length of the tree; restart at `u` for the path clear. -/
def mergeMid : Stmt :=
  .seq (.wstore "tr.tl" (.var "tr.t") (.var "tr.pv")) <|
  .seq (.wset "tr.a" (.load "tr.ln" (.var "tr.t"))) <|
  .seq (.wstore "tr.ln" (.var "tr.t") (.add (.var "tr.a") (.var "fp.kl"))) <|
  .seq (.wset "tr.c" (.var "fp.cu")) <|
  .seq (.wset "tr.f" (.var "fp.kl"))
       (.wset "tr.x" (.lit 1))

/-- (T2) Merge the contact search into the tree of `fp.cv`. -/
def mergeProg : Stmt :=
  .seq mergePre <| .seq pwLoop <| .seq (.wset "tr.j" (.lit 0)) <| .seq rpLoop <| .seq mergeMid pcLoop

theorem mergePre_spec {st : State V} {t ot : ℕ} (hvl : st.w "fp.cv" < st.wlen "tr.tid")
    (htid : st.wa "tr.tid" (st.w "fp.cv") = t) (htl' : t < st.wlen "tr.tl") (htl : st.wa "tr.tl" t = ot)
    (hcap : 1 < st.cap) :
    Runs ops mergePre st (fun s => s.wa = st.wa ∧ s.wlen = st.wlen ∧ s.cap = st.cap ∧ s.cost = st.cost + 6 ∧
      s.w "tr.t" = t ∧ s.w "tr.pv" = ot ∧ s.w "tr.u" = st.w "fp.cv" ∧ s.w "tr.c" = st.w "fp.cu" ∧
      s.w "tr.f" = st.w "fp.kl" ∧ s.w "tr.x" = 1 ∧ ∀ y, y ∉ trRegs → s.w y = st.w y) := by
  have hfit1 : fit st.cap 1 = some 1 := fit_of_lt hcap
  apply runs_seq
  refine runs_wset (a := t) (by simp [hvl, htid]) ?_
  apply runs_seq
  refine runs_wset (a := ot) (by simp [htl', htl]) ?_
  apply runs_seq
  refine runs_wset (a := st.w "fp.cv") (by simp) ?_
  apply runs_seq
  refine runs_wset (a := st.w "fp.cu") (by simp) ?_
  apply runs_seq
  refine runs_wset (a := st.w "fp.kl") (by simp) ?_
  refine runs_wset (a := 1) (by simp [hfit1]) ?_
  refine ⟨rfl, rfl, rfl, by simp only [State.charge_cost, State.setW_cost] <;> omega, by simp, by simp,
    by simp, by simp, by simp, by simp, fun y hy => ?_⟩
  have h1 : y ≠ "tr.t" := fun h => hy (by simp [trRegs, h])
  have h2 : y ≠ "tr.pv" := fun h => hy (by simp [trRegs, h])
  have h3 : y ≠ "tr.u" := fun h => hy (by simp [trRegs, h])
  have h4 : y ≠ "tr.c" := fun h => hy (by simp [trRegs, h])
  have h5 : y ≠ "tr.f" := fun h => hy (by simp [trRegs, h])
  have h6 : y ≠ "tr.x" := fun h => hy (by simp [trRegs, h])
  simp [h1, h2, h3, h4, h5, h6]

theorem mergeMid_spec {st : State V} {t pv l k : ℕ} (ht : st.w "tr.t" = t) (hpv : st.w "tr.pv" = pv)
    (htl : t < st.wlen "tr.tl") (hln : t < st.wlen "tr.ln") (hl : st.wa "tr.ln" t = l)
    (hk : st.w "fp.kl" = k) (hlk : l + k < st.cap) (hcap : 1 < st.cap) :
    Runs ops mergeMid st (fun s => s.wlen = st.wlen ∧ s.cap = st.cap ∧ s.cost = st.cost + 6 ∧
      (∀ a i, a ≠ "tr.tl" → a ≠ "tr.ln" → s.wa a i = st.wa a i) ∧
      (∀ i, s.wa "tr.tl" i = if i = t then pv else st.wa "tr.tl" i) ∧
      (∀ i, s.wa "tr.ln" i = if i = t then l + k else st.wa "tr.ln" i) ∧
      s.w "tr.c" = st.w "fp.cu" ∧ s.w "tr.f" = k ∧ s.w "tr.x" = 1 ∧
      ∀ y, y ∉ trRegs → s.w y = st.w y) := by
  have hfit1 : fit st.cap 1 = some 1 := fit_of_lt hcap
  have hfitlk : fit st.cap (l + k) = some (l + k) := fit_of_lt hlk
  apply runs_seq
  refine runs_wstore (j := t) (a := pv) (by simp [ht]) (by simp [hpv]) htl ?_
  apply runs_seq
  refine runs_wset (a := l) (by simp [ht, hln, hl]) ?_
  apply runs_seq
  refine runs_wstore (j := t) (a := l + k) (by simp [ht]) (by simp [hk, hfitlk]) (by simpa using hln) ?_
  apply runs_seq
  refine runs_wset (a := st.w "fp.cu") (by simp) ?_
  apply runs_seq
  refine runs_wset (a := k) (by simp [hk]) ?_
  refine runs_wset (a := 1) (by simp [hfit1]) ?_
  refine ⟨rfl, rfl, by simp only [State.charge_cost, State.setW_cost, State.storeW_cost] <;> omega,
    fun a i h1 h2 => by simp [h1, h2], fun i => by simp, fun i => by simp, by simp, by simp, by simp,
    fun y hy => ?_⟩
  have h1 : y ≠ "tr.a" := fun h => hy (by simp [trRegs, h])
  have h4 : y ≠ "tr.c" := fun h => hy (by simp [trRegs, h])
  have h5 : y ≠ "tr.f" := fun h => hy (by simp [trRegs, h])
  have h6 : y ≠ "tr.x" := fun h => hy (by simp [trRegs, h])
  simp [h1, h4, h5, h6]

/-- The path walk's final state is a chain state of the rest pass (nothing off the path yet). -/
theorem CF.of_PWI {st0 st : State V} {N : ℕ} {kpar : Fin N → Fin N} {x v : Fin N} {P : List (Fin N)}
    {ot t c : ℕ} (h : PWI st0 kpar x v P ot t c 0 P st) (ht : st0.w "tr.t" = t) :
    CF st0 kpar v P ot t P st :=
  ⟨h.inP, h.tid, h.fm, h.par, fun _ hw hwP => absurd hw hwP, h.par', h.ll, h.nx, h.pv,
    by rw [h.reg _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ht, h.arr,
    fun y hy => h.reg y (fun e => hy (by simp [trRegs, e])) (fun e => hy (by simp [trRegs, e]))
      (fun e => hy (by simp [trRegs, e])) (fun e => hy (by simp [trRegs, e])) (fun e => hy (by simp [trRegs, e])),
    h.wlen, h.cap⟩

theorem restL_zero {N : ℕ} (P K : List (Fin N)) : restL P K 0 = P := by simp [restL]

theorem lastOr_of_ne_nil {α : Type*} {L : List α} (h : L ≠ []) (d : α) : lastOr L d = L.getLast h := by
  unfold lastOr; rw [List.getLast?_eq_getLast h]; rfl

theorem mem_map_val {N : ℕ} {L : List (Fin N)} {w : Fin N} : w.val ∈ L.map Fin.val ↔ w ∈ L :=
  ⟨fun h => by obtain ⟨a, ha, hav⟩ := List.mem_map.mp h; rw [← Fin.ext hav]; exact ha,
   fun h => List.mem_map_of_mem h⟩

/-- Joining a chain with a chain starting at its last node. -/
theorem LL.join {st : State V} {arr : String} {A B : List ℕ} (hA : LL st arr A) (hne : A ≠ [])
    (hB : LL st arr (A.getLast hne :: B)) : LL st arr (A ++ B) := by
  cases B with
  | nil => simpa using hA
  | cons b B' =>
    obtain ⟨h1, h2⟩ := hB
    exact LL.append hA h2 hne (List.cons_ne_nil b B') h1

/-- The facts after a merge, relative to the start state. -/
structure MF (st0 : State V) {N : ℕ} (kpar : Fin N → Fin N) (v : Fin N) (P L : List (Fin N)) (ot t k : ℕ)
    (st : State V) : Prop where
  tid : ∀ i, st.wa "tr.tid" i = if i ∈ L.map Fin.val then t else st0.wa "tr.tid" i
  fm : ∀ i, st.wa "fp.fm" i = if i ∈ L.map Fin.val then 1 else st0.wa "fp.fm" i
  parP : ∀ w ∈ P, st.wa "fp.par" w.val = (reroot P v id w).val
  parR : ∀ w ∈ L, w ∉ P → st.wa "fp.par" w.val = (kpar w).val
  par' : ∀ i, i ∉ L.map Fin.val → st.wa "fp.par" i = st0.wa "fp.par" i
  ll : LL st "tr.nx" (ot :: L.map Fin.val)
  nx : ∀ i, i ∉ (ot :: L.map Fin.val).dropLast → st.wa "tr.nx" i = st0.wa "tr.nx" i
  tl : ∀ i, st.wa "tr.tl" i = if i = t then lastOr (L.map Fin.val) ot else st0.wa "tr.tl" i
  ln : ∀ i, st.wa "tr.ln" i = if i = t then st0.wa "tr.ln" t + k else st0.wa "tr.ln" i
  inP : ∀ i, st.wa "tr.inP" i = if i ∈ P.map Fin.val then 0 else st0.wa "tr.inP" i

/-- **The run of `mergeProg`**: path walk, rest pass, tail/length update, path clear. -/
theorem mergeProg_run {st0 : State V} {N : ℕ} {trees : List (TreeRec (Fin N))} {K : List (Fin N)}
    {kpar : Fin N → Fin N} {x u v : Fin N} {t : ℕ}
    (hF : ForestRep st0 N trees) (ht : t < trees.length) (hvt : v ∈ trees[t].ord) (hKnd : K.Nodup)
    (hKtv : ∀ w ∈ K, ∀ T ∈ trees, w ∉ T.ord)
    (hPK : ∀ w ∈ kpath kpar x K.length u, w ∈ K) (hPnd : (kpath kpar x K.length u).Nodup)
    (hK : ∀ i (h : i < K.length), st0.wa "fp.K" i = (K[i]).val) (hkl : st0.w "fp.kl" = K.length)
    (hKl : K.length ≤ st0.wlen "fp.K")
    (hkp : ∀ w ∈ K, st0.wa "fp.kp" w.val = (kpar w).val) (hkpl : N ≤ st0.wlen "fp.kp")
    (hx : st0.w "fp.x" = x.val) (hcu : st0.w "fp.cu" = u.val) (hcv : st0.w "fp.cv" = v.val)
    (hcap : N + 2 < st0.cap) :
    Runs ops mergeProg st0 (fun st' => MF st0 kpar v (kpath kpar x K.length u)
      (restL (kpath kpar x K.length u) K K.length) (st0.wa "tr.tl" t) t K.length st' ∧
      st'.cost ≤ st0.cost + 33 * K.length + 40) := by
  obtain ⟨lfm, ltid, lnx, lpar, linP, lhd, ltl, lln⟩ := hF.lens
  obtain ⟨P, hP⟩ : ∃ P, P = kpath kpar x K.length u := ⟨_, rfl⟩
  rw [← hP] at hPK hPnd ⊢
  have huP : u ∈ P := by rw [hP, kpath_step]; split_ifs <;> simp
  have huK : u ∈ K := hPK u huP
  have hlt : trees.length < N := trees_len_lt hF.ne_mem hF.disj hF.nodup (hKtv u huK)
  have htN : t < N := lt_trans ht hlt
  have hTt : trees[t] ∈ trees := List.getElem_mem ht
  -- the old tail `o` of tree `t`
  have hne := hF.ne t ht
  have htl0 : (trees[t].ord.getLast hne).val = st0.wa "tr.tl" t := by
    have h := hF.tl t ht
    rw [List.getLast?_eq_getLast hne] at h
    exact Option.some.inj h
  obtain ⟨o, ho⟩ : ∃ o, o = trees[t].ord.getLast hne := ⟨_, rfl⟩
  rw [← ho] at htl0
  have hoT : o ∈ trees[t].ord := by rw [ho]; exact List.getLast_mem hne
  rw [← htl0]
  have hoK : o.val ∉ K.map Fin.val := by
    intro h
    obtain ⟨w, hw, hwo⟩ := List.mem_map.mp h
    exact hKtv w hw trees[t] hTt (by rw [Fin.ext hwo]; exact hoT)
  have hoP : o.val ∉ P.map Fin.val := fun h => by
    obtain ⟨w, hw, hwo⟩ := List.mem_map.mp h
    exact hoK (List.mem_map.mpr ⟨w, hPK w hw, hwo⟩)
  have hTK : (trees[t].ord ++ K).Nodup := List.nodup_append.mpr ⟨hF.nodup _ hTt, hKnd,
    fun a ha b hb hab => hKtv b hb trees[t] hTt (by rw [← hab]; exact ha)⟩
  have hlnN : trees[t].ord.length + K.length ≤ N := by
    have := hTK.length_le_card; simpa using this
  -- prefix
  apply runs_seq
  refine Runs.mono (mergePre_spec (ops := ops) (st := st0) (t := t) (ot := o.val)
    (by rw [hcv]; have := v.2; omega) (by rw [hcv]; exact hF.tid t ht v hvt) (by omega) htl0.symm
    (by omega)) ?_
  rintro s6 ⟨h6wa, h6len, h6cap, h6cost, h6t, h6pv, h6u, h6c, h6f, h6x, h6reg⟩
  have h6fx : s6.w "fp.x" = x.val := by rw [h6reg _ (by decide)]; exact hx
  have h6kl : s6.w "fp.kl" = K.length := by rw [h6reg _ (by decide)]; exact hkl
  -- path walk
  have hPW0 : PWI s6 kpar x v P o.val t (s6.cost + 14 * (K.length + 1)) (K.length + 1) [] s6 :=
    ⟨List.nil_prefix, Or.inr ⟨Nat.succ_pos _, h6x, u, K.length, by rw [h6c, hcu], by rw [h6f, hkl], rfl,
      (List.nil_append _).trans hP.symm⟩, fun i => by simp, fun i => by simp, fun i => by simp,
      fun w hw => absurd hw List.not_mem_nil, fun _ _ => rfl, trivial, fun _ _ => rfl, h6pv, h6u.trans hcv,
      fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, rfl, rfl, le_refl _⟩
  apply runs_seq
  refine Runs.mono (pwLoop_spec (ops := ops) (st0 := s6) (K := K) hPnd hPK hoP
    (fun w hw => by rw [h6wa]; exact hkp w hw) h6fx h6t
    (by rw [h6len]; exact ⟨linP, ltid, lfm, lpar, lnx, hkpl⟩) (by rw [h6len]; have := o.2; omega)
    (by rw [h6cap]; exact hcap) (K.length + 1) s6 ⟨[], hPW0⟩) ?_
  intro s7 hP7
  have hC7 : CF s6 kpar v P o.val t P s7 := CF.of_PWI hP7 h6t
  -- rest pass
  apply runs_seq
  refine runs_wset (a := 0) (by simp [fit_of_lt (show 0 < s7.cap by rw [hP7.cap, h6cap]; omega)]) ?_
  apply runs_seq
  have hR0 : RPJ s6 kpar v P K o.val t (((s7.setW "tr.j" 0).charge 1).cost + 13 * K.length) K.length
      ((s7.setW "tr.j" 0).charge 1) := by
    refine ⟨le_refl _, by simp, ?_, le_refl _⟩
    rw [Nat.sub_self, restL_zero]
    exact hC7.frame rfl (fun y _ _ h3 => by simp [h3]) rfl rfl
  refine Runs.mono (rpLoop_spec (ops := ops) (st0 := s6) (by intro i h; rw [h6wa]; exact hK i h) h6kl
    (by rw [h6len]; exact hKl) hKnd hPnd hoK hPK (fun w => by rw [h6wa]; exact hF.inP w)
    (fun w hw => by rw [h6wa]; exact hkp w hw)
    (by rw [h6len]; exact ⟨linP, ltid, lfm, lpar, lnx, hkpl⟩) (by rw [h6len]; have := o.2; omega)
    (by rw [h6cap]; exact hcap) K.length _ hR0) ?_
  rintro s9 ⟨-, -, hC9, hcost9⟩
  rw [Nat.sub_zero] at hC9
  obtain ⟨L, hL⟩ : ∃ L, L = restL P K K.length := ⟨_, rfl⟩
  rw [← hL] at hC9 ⊢
  have h9arr : ∀ a i, a ≠ "tr.inP" → a ≠ "tr.tid" → a ≠ "fp.fm" → a ≠ "fp.par" → a ≠ "tr.nx" →
      s9.wa a i = st0.wa a i := fun a i h1 h2 h3 h4 h5 => by rw [hC9.arr a i h1 h2 h3 h4 h5, h6wa]
  have h9reg : ∀ y, y ∉ trRegs → s9.w y = st0.w y := fun y hy => by rw [hC9.reg y hy, h6reg y hy]
  have h9len : s9.wlen = st0.wlen := by rw [hC9.wlen, h6len]
  have h9cap : s9.cap = st0.cap := by rw [hC9.cap, h6cap]
  -- tail and length
  apply runs_seq
  refine Runs.mono (mergeMid_spec (ops := ops) (st := s9) (t := t) (pv := lastOr (L.map Fin.val) o.val)
    (l := st0.wa "tr.ln" t) (k := K.length) hC9.tt hC9.pv (by rw [h9len]; omega) (by rw [h9len]; omega)
    (h9arr "tr.ln" t (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [h9reg "fp.kl" (by decide)]; exact hkl) (by rw [h9cap, hF.ln t ht]; omega)
    (by rw [h9cap]; omega)) ?_
  rintro s15 ⟨h15len, h15cap, h15cost, h15arr, h15tl, h15ln, h15c, h15f, h15x, h15reg⟩
  -- path clear
  have hPC0 : PCI s15 kpar x P (s15.cost + 6 * (K.length + 1)) (K.length + 1) [] s15 :=
    ⟨List.nil_prefix, Or.inr ⟨Nat.succ_pos _, h15x, u, K.length,
      by rw [h15c, h9reg "fp.cu" (by decide)]; exact hcu, h15f, rfl, (List.nil_append _).trans hP.symm⟩,
      fun i => by simp, fun _ _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl, le_refl _⟩
  refine Runs.mono (pcLoop_spec (ops := ops) (st0 := s15) (K := K) hPnd hPK
    (fun w hw => by
      rw [h15arr "fp.kp" w.val (by decide) (by decide),
        h9arr "fp.kp" w.val (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hkp w hw)
    (by rw [h15reg "fp.x" (by decide), h9reg "fp.x" (by decide)]; exact hx)
    (by rw [h15len, h9len]; exact ⟨linP, hkpl⟩) (by rw [h15cap, h9cap]; exact hcap) (K.length + 1) s15
    ⟨[], hPC0⟩) ?_
  intro s16 hPC
  have hA : ∀ a i, a ≠ "tr.inP" → a ≠ "tr.tl" → a ≠ "tr.ln" → s16.wa a i = s9.wa a i :=
    fun a i h1 h2 h3 => by rw [hPC.arr a i h1, h15arr a i h2 h3]
  refine ⟨⟨fun i => ?_, fun i => ?_, fun w hw => ?_, fun w hw hwP => ?_, fun i hi => ?_, ?_, fun i hi => ?_,
    fun i => ?_, fun i => ?_, fun i => ?_⟩, ?_⟩
  · rw [hA "tr.tid" i (by decide) (by decide) (by decide), hC9.tid, h6wa]
  · rw [hA "fp.fm" i (by decide) (by decide) (by decide), hC9.fm, h6wa]
  · rw [hA "fp.par" w.val (by decide) (by decide) (by decide)]; exact hC9.parP w hw
  · rw [hA "fp.par" w.val (by decide) (by decide) (by decide)]; exact hC9.parR w hw hwP
  · rw [hA "fp.par" i (by decide) (by decide) (by decide), hC9.par' i hi, h6wa]
  · exact LL.frame hC9.ll (fun j _ => hA "tr.nx" j (by decide) (by decide) (by decide))
  · rw [hA "tr.nx" i (by decide) (by decide) (by decide), hC9.nx i hi, h6wa]
  · rw [hPC.arr "tr.tl" i (by decide), h15tl i,
      h9arr "tr.tl" i (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rw [hPC.arr "tr.ln" i (by decide), h15ln i,
      h9arr "tr.ln" i (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rw [hPC.inP i, h15arr "tr.inP" i (by decide) (by decide), hC9.inP i, h6wa]
    split_ifs <;> rfl
  · have c7 := hP7.cost
    have c16 := hPC.cost
    simp only [State.charge_cost, State.setW_cost] at hcost9
    omega

/-- **(T2) `mergeProg` refines `growForest .contact`** (agent-05's `mergeTree` into the tree of `v`). -/
theorem mergeProg_spec {st0 : State V} {N : ℕ} {trees : List (TreeRec (Fin N))} {K : List (Fin N)}
    {kpar : Fin N → Fin N} {x u v : Fin N}
    (hF : ForestRep st0 N trees) (hvT : ∃ T ∈ trees, v ∈ T.ord) (hKnd : K.Nodup)
    (hKtv : ∀ w ∈ K, ∀ T ∈ trees, w ∉ T.ord)
    (hPK : ∀ w ∈ kpath kpar x K.length u, w ∈ K) (hPnd : (kpath kpar x K.length u).Nodup)
    (hK : ∀ i (h : i < K.length), st0.wa "fp.K" i = (K[i]).val) (hkl : st0.w "fp.kl" = K.length)
    (hKl : K.length ≤ st0.wlen "fp.K")
    (hkp : ∀ w ∈ K, st0.wa "fp.kp" w.val = (kpar w).val) (hkpl : N ≤ st0.wlen "fp.kp")
    (hx : st0.w "fp.x" = x.val) (hcu : st0.w "fp.cu" = u.val) (hcv : st0.w "fp.cv" = v.val)
    (hcap : N + 2 < st0.cap) :
    Runs ops mergeProg st0 (fun st' =>
      ForestRep st' N (trees.map (fun T => if v ∈ T.ord then mergeRec T K kpar x u v else T)) ∧
      WFr st0 st' (wregsOf mergeProg) (warrsOf mergeProg) ∧ st'.cost ≤ st0.cost + 33 * K.length + 40) := by
  obtain ⟨T0, hT0, hvT0⟩ := hvT
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hT0
  have hWS : WS mergeProg := by
    simp [WS, mergeProg, mergePre, mergeMid, pwLoop, pwBody, pwRec, pwIte, rpLoop, rpBody, rpApp, pcLoop,
      pcBody]
  refine Runs.mono (Runs.wframe hWS (mergeProg_run (ops := ops) hF ht hvT0 hKnd hKtv hPK hPnd hK hkl hKl hkp
    hkpl hx hcu hcv hcap)) ?_
  rintro st' ⟨⟨hM, hcost⟩, hW⟩
  refine ⟨?_, hW, hcost⟩
  have hnt : "tr.nt" ∉ wregsOf mergeProg := by decide
  have hhd : "tr.hd" ∉ warrsOf mergeProg := by decide
  obtain ⟨P, hP⟩ : ∃ P, P = kpath kpar x K.length u := ⟨_, rfl⟩
  rw [← hP] at hPK hPnd hM
  obtain ⟨L, hL⟩ : ∃ L, L = restL P K K.length := ⟨_, rfl⟩
  rw [← hL] at hM
  have hmord : ∀ T : TreeRec (Fin N), (mergeRec T K kpar x u v).ord = T.ord ++ L := by
    intro T
    rw [hL, hP]
    simp only [mergeRec, restL, List.take_length, List.append_assoc]
  have hmpar : ∀ T : TreeRec (Fin N),
      (mergeRec T K kpar x u v).par = reroot P v (fun w => if w ∈ K then kpar w else T.par w) := by
    intro T; rw [hP]; rfl
  have hLdef : L = P ++ K.filter (fun w => w ∉ P) := by rw [hL]; simp [restL]
  have hLK : ∀ w ∈ L, w ∈ K := by
    intro w hw
    rw [hLdef, List.mem_append, List.mem_filter] at hw
    rcases hw with h | ⟨h, -⟩
    · exact hPK w h
    · exact h
  have hKL : ∀ w ∈ K, w ∈ L := by
    intro w hw
    rw [hLdef, List.mem_append, List.mem_filter]
    by_cases h : w ∈ P
    · exact Or.inl h
    · exact Or.inr ⟨hw, by simpa using h⟩
  have hLnd : L.Nodup := by rw [hL]; exact restL_nodup hPnd hKnd _
  have huP : u ∈ P := by rw [hP, kpath_step]; split_ifs <;> simp
  have hLne : L ≠ [] := by rw [hLdef]; exact List.append_ne_nil_of_left_ne_nil (List.ne_nil_of_mem huP) _
  have hLlen : L.length = K.length :=
    ((List.perm_ext_iff_of_nodup hLnd hKnd).mpr (fun w => ⟨hLK w, hKL w⟩)).length_eq
  have hfmem : ∀ T ∈ trees, ∀ w ∈ T.ord, w ∉ L := fun T hT w hw hwL => hKtv w (hLK w hwL) T hT hw
  have hidx : ∀ t1 (h1 : t1 < trees.length) t2 (h2 : t2 < trees.length) (w : Fin N),
      w ∈ trees[t1].ord → w ∈ trees[t2].ord → t1 = t2 := by
    intro t1 h1 t2 h2 w hw1 hw2
    have e1 := hF.tid t1 h1 w hw1
    have e2 := hF.tid t2 h2 w hw2
    omega
  have hvt_iff : ∀ t' (h : t' < trees.length), v ∈ trees[t'].ord ↔ t' = t := fun t' h =>
    ⟨fun hv => hidx t' h t ht v hv hvT0, fun e => by subst e; exact hvT0⟩
  have hne := hF.ne t ht
  have htl0 : (trees[t].ord.getLast hne).val = st0.wa "tr.tl" t := by
    have h := hF.tl t ht
    rw [List.getLast?_eq_getLast hne] at h
    exact Option.some.inj h
  have mem_f : ∀ T ∈ trees, ∀ w,
      w ∈ (if v ∈ T.ord then mergeRec T K kpar x u v else T).ord ↔ w ∈ T.ord ∨ (v ∈ T.ord ∧ w ∈ L) := by
    intro T _ w
    by_cases hv : v ∈ T.ord
    · rw [if_pos hv, hmord, List.mem_append]; simp [hv]
    · rw [if_neg hv]; simp [hv]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- nt
    rw [List.length_map, hW.w "tr.nt" hnt]; exact hF.nt
  · -- ne
    intro t' h'
    have h'' : t' < trees.length := by simpa using h'
    simp only [List.getElem_map]
    split_ifs with hv
    · rw [hmord]; exact List.append_ne_nil_of_left_ne_nil (hF.ne t' h'') _
    · exact hF.ne t' h''
  · -- root
    intro t' h'
    have h'' : t' < trees.length := by simpa using h'
    simp only [List.getElem_map]
    split_ifs with hv
    · rw [hmord, List.head?_append_of_ne_nil _ (hF.ne t' h'')]; exact hF.root t' h''
    · exact hF.root t' h''
  · -- hd
    intro t' h'
    have h'' : t' < trees.length := by simpa using h'
    rw [hW.arr "tr.hd" hhd]
    simp only [List.getElem_map]
    split_ifs with hv
    · rw [hmord, List.head?_append_of_ne_nil _ (hF.ne t' h'')]; exact hF.hd t' h''
    · exact hF.hd t' h''
  · -- tl
    intro t' h'
    have h'' : t' < trees.length := by simpa using h'
    simp only [List.getElem_map]
    rw [hM.tl t']
    by_cases hv : v ∈ trees[t'].ord
    · have htt := (hvt_iff t' h'').mp hv
      rw [if_pos hv, if_pos htt, hmord, List.getLast?_append_of_ne_nil _ hLne, List.getLast?_eq_getLast hLne,
        lastOr_of_ne_nil (L := L.map Fin.val) (by simpa using hLne), List.getLast_map]
      try rfl
    · have htt : t' ≠ t := fun h => hv ((hvt_iff t' h'').mpr h)
      rw [if_neg hv, if_neg htt]; exact hF.tl t' h''
  · -- ln
    intro t' h'
    have h'' : t' < trees.length := by simpa using h'
    simp only [List.getElem_map]
    rw [hM.ln t']
    by_cases hv : v ∈ trees[t'].ord
    · have htt := (hvt_iff t' h'').mp hv
      rw [if_pos hv, if_pos htt, hmord, List.length_append, hLlen, ← htt, hF.ln t' h'']
    · have htt : t' ≠ t := fun h => hv ((hvt_iff t' h'').mpr h)
      rw [if_neg hv, if_neg htt]; exact hF.ln t' h''
  · -- ll
    intro t' h'
    have h'' : t' < trees.length := by simpa using h'
    have hTt' : trees[t'] ∈ trees := List.getElem_mem h''
    simp only [List.getElem_map]
    by_cases hv : v ∈ trees[t'].ord
    · have htt := (hvt_iff t' h'').mp hv
      rw [if_pos hv, hmord, List.map_append]
      have hA : trees[t'].ord.map Fin.val ≠ [] := by simpa using hF.ne t' h''
      have hlast : (trees[t'].ord.map Fin.val).getLast hA = st0.wa "tr.tl" t := by
        have e := hF.tl t' h''
        rw [List.getLast?_eq_getLast (hF.ne t' h'')] at e
        rw [List.getLast_map, Option.some.inj e, htt]
      have hndA : (trees[t'].ord.map Fin.val).Nodup := (hF.nodup _ hTt').map Fin.val_injective
      refine LL.join (LL.frame (hF.ll t' h'') (fun j hj => hM.nx j (fun hj' => ?_))) hA
        (by rw [hlast]; exact hM.ll)
      have hjA := List.dropLast_subset _ hj
      rcases List.mem_cons.mp (List.dropLast_subset _ hj') with h1 | h1
      · rw [h1, ← hlast] at hj; exact getLast_not_mem_dropLast hndA hA hj
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hjA
        exact hfmem _ hTt' w hw (mem_map_val.mp h1)
    · have htt : t' ≠ t := fun h => hv ((hvt_iff t' h'').mpr h)
      rw [if_neg hv]
      refine LL.frame (hF.ll t' h'') (fun j hj => hM.nx j (fun hj' => ?_))
      have hjA := List.dropLast_subset _ hj
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hjA
      rcases List.mem_cons.mp (List.dropLast_subset _ hj') with h1 | h1
      · rw [← htl0] at h1
        exact htt (hidx t' h'' t ht w hw (by rw [Fin.ext h1]; exact List.getLast_mem hne))
      · exact hfmem _ hTt' w hw (mem_map_val.mp h1)
  · -- tid
    intro t' h' w hw
    have h'' : t' < trees.length := by simpa using h'
    simp only [List.getElem_map] at hw
    rw [hM.tid]
    by_cases hv : v ∈ trees[t'].ord
    · have htt := (hvt_iff t' h'').mp hv
      rw [if_pos hv, hmord, List.mem_append] at hw
      by_cases hwL : w ∈ L
      · rw [if_pos (mem_map_val.mpr hwL), htt]
      · rw [if_neg (fun h => hwL (mem_map_val.mp h))]
        rcases hw with hw | hw
        · exact hF.tid t' h'' w hw
        · exact absurd hw hwL
    · rw [if_neg hv] at hw
      rw [if_neg (fun h => hfmem _ (List.getElem_mem h'') w hw (mem_map_val.mp h))]
      exact hF.tid t' h'' w hw
  · -- par
    intro t' h' w hw
    have h'' : t' < trees.length := by simpa using h'
    have hTt' : trees[t'] ∈ trees := List.getElem_mem h''
    simp only [List.getElem_map] at hw ⊢
    by_cases hv : v ∈ trees[t'].ord
    · rw [if_pos hv] at hw ⊢
      rw [hmord, List.tail_append_of_ne_nil (hF.ne t' h''), List.mem_append] at hw
      rw [hmpar]
      rcases hw with hw | hw
      · have hwT := List.mem_of_mem_tail hw
        have hwL := hfmem _ hTt' w hwT
        have hwP : w ∉ P := fun h => hwL (hKL w (hPK w h))
        have hwK : w ∉ K := fun h => hwL (hKL w h)
        rw [hM.par' _ (fun h => hwL (mem_map_val.mp h)), reroot_not_mem hwP, if_neg hwK]
        exact hF.par t' h'' w hw
      · by_cases hwP : w ∈ P
        · rw [hM.parP w hwP]; exact congrArg Fin.val (reroot_base P v id _ w hwP hPnd)
        · rw [hM.parR w hw hwP, reroot_not_mem hwP, if_pos (hLK w hw)]
    · rw [if_neg hv] at hw ⊢
      have hwT := List.mem_of_mem_tail hw
      have hwL := hfmem _ hTt' w hwT
      rw [hM.par' _ (fun h => hwL (mem_map_val.mp h))]
      exact hF.par t' h'' w hw
  · -- fm
    intro w
    rw [hM.fm, hF.fm w]
    have hiff : (∃ T ∈ trees.map (fun T => if v ∈ T.ord then mergeRec T K kpar x u v else T), w ∈ T.ord) ↔
        w ∈ L ∨ ∃ T ∈ trees, w ∈ T.ord := by
      constructor
      · rintro ⟨T', hT', hw⟩
        obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hT'
        rcases (mem_f T hT w).mp hw with h | ⟨-, h⟩
        · exact Or.inr ⟨T, hT, h⟩
        · exact Or.inl h
      · rintro (h | ⟨T, hT, h⟩)
        · exact ⟨_, List.mem_map_of_mem (List.getElem_mem ht),
            (mem_f _ (List.getElem_mem ht) w).mpr (Or.inr ⟨hvT0, h⟩)⟩
        · exact ⟨_, List.mem_map_of_mem hT, (mem_f T hT w).mpr (Or.inl h)⟩
    by_cases hwL : w ∈ L
    · rw [if_pos (mem_map_val.mpr hwL), if_pos (hiff.mpr (Or.inl hwL))]
    · rw [if_neg (fun h => hwL (mem_map_val.mp h))]
      by_cases hwT : ∃ T ∈ trees, w ∈ T.ord
      · rw [if_pos hwT, if_pos (hiff.mpr (Or.inr hwT))]
      · rw [if_neg hwT, if_neg (fun h => (hiff.mp h).elim hwL hwT)]
  · -- inP
    intro w
    rw [hM.inP]
    split_ifs
    · rfl
    · exact hF.inP w
  · -- disj
    rw [List.pairwise_map]
    refine hF.disj.imp_of_mem (fun {a b} ha hb hab => ?_)
    intro w hwa hwb
    rcases (mem_f a ha w).mp hwa with h1 | ⟨hva, h1⟩ <;> rcases (mem_f b hb w).mp hwb with h2 | ⟨hvb, h2⟩
    · exact hab w h1 h2
    · exact hfmem a ha w h1 h2
    · exact hfmem b hb w h2 h1
    · exact hab v hva hvb
  · -- nodup
    intro T' hT'
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hT'
    split_ifs with hv
    · rw [hmord]
      exact List.nodup_append.mpr ⟨hF.nodup T hT, hLnd, fun a ha b hb hab => hfmem T hT a ha (by rw [hab]; exact hb)⟩
    · exact hF.nodup T hT
  · -- lens
    rw [hW.wlen]; exact hF.lens

end Frontier.CHD.PartitionRAM
