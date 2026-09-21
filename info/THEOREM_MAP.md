# THEOREM_MAP: C-HD Gate-C result, paper-to-Lean map (CONSOLIDATED by agent-07, cross-check by agent-09). NON-GATE draft.

Consolidated 2026-09-20 23:02 UTC from the owners' parts listed below (provenance sha256 per part).
- Frozen tree: integration build #33.
- Source manifest: /research/agents/agent-10/work/integration/sources_33.sha256 (292 files); sha256 of the manifest file = b43018fbfedfed6cc6bf71af3ea2f26480e0d1d41eec9fecc7fddd0e4129a2c3.
- The reviewer #1 fresh copy (repro/final1/proj) is byte-identical to the manifest (checked 22:58).
- Paper: PAPER_CHD v2.0 (agent-03, cbdf6c9e).

Final theorems (module Frontier.CHD.Final):
- `Frontier.CHD.Final.chd_gateC : Frontier.GateC`;
- `Frontier.CHD.Final.chd_CHDTarget : Frontier.GateCTarget.CHDTarget Frontier.GateCCalc.F`;
- `Frontier.CHD.Final.chd_exact_within`.
Axioms: [propext, Classical.choice, Quot.sound]. The algorithm `Frontier.CHD.Final.chdProgram` depends on no axioms.

Every backticked Lean name in this file is checked mechanically against the frozen tree by agent-07/work/repro/theorem_map_check.py; the result is in the last section.

## 1. Target, gate, preprocessing (L6), core wrapper, parameters, spine top level, final assembly (owner agent-10; source /research/agents/agent-10/work/final_stage/drafts/THEOREM_MAP_agent10.md, sha256 b9d9374d7290)

### THEOREM MAP, agent-10's part (DRAFT, updated 23:08; frozen tree = build #33). Paper = PAPER_CHD v1.7.

#### Target and gate
| claim | Lean |
|---|---|
| Frozen target: ∃ program, Exact ∧ RunsWithin C·Tdisp F | `Frontier.GateCTarget.CHDTarget GateCCalc.F` (GateC.lean) |
| Target ⇒ Gate C | `GateCTarget.chdTarget_F_imp_gateC`, `mu_window`, `tendsto_Tchd_mu` |
| Named witness program | `L6.chdProg e ps core`; `L6.chdProg_exact_within` |

#### §2 Preprocessing (P1–P5) and the output
| paper | Lean (Layer B, RAM) | Lean (Layer A / math) |
|---|---|---|
| dispatcher: BF fallback for n < 2^16 or m > n F(n) | `Dispatch.dispatch_runs`, `Dispatch.chdTarget_of_body` | `Dispatch.bf_bodySpec` |
| P1–P4: keep set, counting sort, dedup, degree chunking, CSR, per-range sort | `L6.l6_runs` (L6/Run.lean) with its passes: keepProg, csort, dedup, passA, passB, sortPass | `CHD.KReduction` (Preprocess.lean): dist_eq, dist_rep, dist_top |
| reduced graph facts | `L6.kred`, `L6.csrAt`, `L6.graphAt`, `L6.outL_sorted`, `L6.outL_simple`, `L6.off_n_le_cn`, `L6.sl_n_le`, `L6.delta_le_dd` | |
| P5: output mapping, and the m = 0 case | `L6.outLoop_runs`, `L6.solves_of_oinv`, `L6.trivialOut_runs` | |
| body assembly | `L6.body_spec` (bound (2Kc+1500)·Tchd), `L6.chdTarget_of_core` | `L6.Tchd_cn_le`, `L6.nm_log_le` |

#### Core wrapper and parameters
| paper | Lean |
|---|---|
| parameters t = max(16, t*), k = ⌈√t⌉, L = ⌊lg n/t⌋+1, computed from (cn, cm) | `L6.paramsProg_runs` (Params.lean) |
| per-level tables τ_l = t³2^{lt}, M_l | `L6.levelTab_runs`, `L6.levelTab_cap` |
| label-table init | `LabRAM.initLab_wp` (agent-02) inside `L6.corePre_runs` |
| core = prefix ; (gM = 0 ? skip : spine) ; restore | `L6.coreTop`, `L6.coreSpec_of_spine` |
| exactness at the top | `L6.complete_of_topRun` (bmsspDL_top), `L6.coreOut_of_labAt` |
| master cost, Layer A | `L6.masterSpec_of_good` (agent-06: master_cost_D, masterSpec_of_goodP) |
| word-size budget | `L6.Tchd_le_sq`, `CostSkeleton.Tchd_le_Tnat`, `CostSkeleton.Tnat_le_Tchd` |

#### Spine top level
| paper | Lean |
|---|---|
| spine = prologue ; call BMSSP(LF, ⊤, {s}) | `L6.spineOf`, `L6.spineSpec_of_parts` |
| prologue: sizes, allocation, heap, FP/D init, B/Blow slots, S row | `L6.spinePro`, `L6.proSpec_spinePro`, `L6.partA_runs`, `L6.blowProg_runs`, `L6.frameProg_runs`, `L6.fpHook` |
| the top call refines BMSSPD at level LF | `L6.callSpec_of_ramSpine` (from agent-08's `RamSpine.CallSpec`) |
| level induction | `L6.callSpec_of_levels`, `L6.chdTarget_of_levels`, `L6.chdProg_of_levels` |
| cost parameters of the run (§6) | `L6.SbF` (3k·M_{l+1}), `L6.KhF` (heap bound), `L6.chdDC`, `L6.chdP`; `L6.goodP_chdP : GoodP chdP 1 1 1000` via `L6.log_KhF_le` |
| base case at level 0 | `L6.callSpec_base` (agent-03's `RamSpine.callSpec_zero` with the rfl bridge `baseProg_closed`; slack `L6.baseReq`, `L6.baseBud_le`) |
| final assembly | `L6.chdTarget_of_step` (Assembly.lean): CHDTarget F from the D layer + level step + decidable facts; the final `Frontier.CHD.Final.chd_gateC` instantiates it |
| space | `L6.chdProg_space` (space ≤ cost for the named witness) |
| D-layer capacity / word size | `L6.kmN`, `L6.kmaster_eq`, `L6.kmN_le`, `L6.ucap_cover`, `L6.hucap_of`, `L6.cbig_of_cap` (L6/DCap.lean); `L6.chdM_two_cap`, `L6.tau_M_cap` (L6/TauCap.lean) |
| expansion size of sub-call frontiers (BM.11-12) | `L6.hSbA_chd` (L6/SbA.lean; same fact as agent-01's `RamBody.sbA_fpC`) |
| level step wired to the instance | `L6.hs_of_parts` (L6/StepInst.lean; from agent-01's `callSpec_succ`) |
| final budget slack | `L6.SlfC`, `L6.finCst_le_SlfC`, `L6.postS_le_SlfC`, `L6.SlfC_le` (degree 8) (L6/SlackF.lean) |
| final composition, generic in the D layer | `L6.chdProg_of_DLayer`, `L6.hbig160` (L6/FinalGen.lean) |
| THE THEOREM | `Frontier.CHD.Final.chd_gateC : Frontier.GateC`, `Final.chd_CHDTarget`, `Final.chd_exact_within`, the program `Final.chdProgram` (axiom-free); the name facts `Final.n_*` are decided by `decide +kernel` at a closed dummy instance (Final.lean) |
| tooling | `RAM.exec_frame` / `Runs.frame` (SynFrame), `AllocList.allocWs_runs` |

## 2. Level body BM.1-31 (one call at level l+1), level step (owner agent-01; source /research/agents/agent-01/work/PAPER_TO_CODE_agent01.md, sha256 cea4b0b149c0)

### Paper-to-code: agent-01 components, the level body of BMSSP-HD (NON-GATE, for THEOREM_MAP.md)

All files are installed in /research/lean/Frontier/CHD. Main theorems use std axioms only ([propext, Classical.choice, Quot.sound]); none contains sorry, admit or native_decide. The sha256 prefixes are as of 22:50 UTC.

| Paper item (§3.2 BM.1–31, one call at level l+1) | Lean theorem (file:line) | File (sha, lines) |
|---|---|---|
| BM.1–2 call entry and dispatch (level > 0 → recursive body, else base case) | `bmsspProc base rec := ite (var "lvl") rec base`; `callIn_enter`, `unch_enter_charge` (RamBodySpec:366/361) | RamBodySpec (a2631e7c, 428) |
| BM.3–4 FindPivots-HD at level l+1 | interface `FPB` (RamBody) and `FPCSound/FPCTotal` for the Layer-A contract; instance agent-09's `L6.hFP_of` | RamBody (1cb248ce, 207) |
| BM.5 new D structure `newC M_{l+1} B` | `dNewI_of` (RamBodyI:113), from `DLayer.new_spec` | RamBodyI (068ded53, 426) |
| BM.5–6 argmin pivots per group (label order `cmpTT`) | `pivProg_spec` (RamInit:370) with `cmpI_tt` (RamBodyI:393); Layer A `exists_piv` / `aloop_init` (RamBodyA:117) | RamInit (0698d8bc, 517), RamBodyA (f6ea46d5, 324) |
| BM.6 insert the pivots, `d v < B` | `pivIns_spec` (RamPiv:114) with `dInsI_of` (RamBodyI:76), using insManyC_* cost lemmas | RamPiv (b8590016, 273) |
| BM.7–8 `B'_0`, `U := ∅` | agent-02's `b8Prog_spec` and `rowReset "U.len"`, composed in `pro_spec` | RamBodyPro (6670cd2b, 771) |
| prologue BM.3–8 composed (FindPivots → copyGrp → pivots → inserts → B'_0 → U reset) | `pro_spec` (RamBodyPro:242, CPS form), with frames from RamBodyF (`static_frame`, `clear_frame`, `SetRow.toList/ofList`, `ptrOK_congr`) | RamBodyPro, RamBodyF (19f05cd2, 208) |
| BM.9–23 main loop | interface `LoopSpecB` (RamBody); instance agent-08's `L6.hLoop_of_parts`; Layer-A budget `callD_ext_loop` (RamBodyA:221), `loopD_card_le` | RamBody, RamBodyA |
| BM.11–12 expansion size, `\|expand\| ≤ 3k·M_{l+1}` (premise hSbA) | `sbA_fpC` (RamBodyL:23), from `expand_card_le`, `fpC_spec`, `fpC_sound`, `pull_sim` | RamBodyL (6fca2fe3, 51) |
| BM.24–31 finalization | interface `FinB` / `FinOut` (RamBodySpec); instance agent-03's `fin_spec` (RamBodyFin), turned into FinB by `finB_of_finSpec` (RamBodyFinB:57), `FinB.mono` (:95), `finB_uniform` (:110) | RamBodyFinB (b2e1e786, 119) |
| BM.25 T6 test `B'f ≤ d x < B` | `testI_T6` (RamBodyI:341), `t6Prog_spec` (RamT6:43) | RamT6 (be124748, 256) |
| BM.26 W' test `x ∉ U ∧ d x < B'f` | `testI_Wp` (RamBodyI:357), `wpProg_spec` (RamWp:107); Layer A `wp_complete` (RamBodyA:299), `bodyA_fold_d` (RamBodyA:93) | RamWp (3ef776b5, 431) |
| BM.29 delete W' from D | `dsDelW` and `dsDelW_spec` (DDelW:155); `delWBU_mkDL` (DDelW:167) = fin_spec's `hDel` on every mkDL D layer | DDelW (48e82177, 186) |
| one call BM.1–31: RAM run refines `BMLazy.CallD`, cost `≤ K·lg.cost` with ONE K, use `≤ 2·lg.cost` | `body_spec` (RamBodySpec:185), via `callD_mk` (RamBodyA:201) and `levelPkg` (RamBodyA:253) | RamBodySpec |
| level step `CallSpec l → CallSpec (l+1)` | `callSpec_succ` (RamBodySpec:387): `hK : Kf + Cf + Ko + Kfin + Cfin + 2·DL.K + 60 ≤ K`, `hSl : Cst + 2 ≤ Sl` | RamBodySpec |
| hFin of `L6.hs_of_parts` / `FinalGen.chdProg_of_DLayer` | `L6.hFin_of_parts` (L6/FinInst:29) | L6/FinInst (d8188292, 52) |

Constants of the level step (the kernel #eval is in agents/agent-01/work/lean/A01/tests/ConstCheck.lean):
- Kf = 524 and Cf = 351 (FindPivots, agent-09).
- Kfin = 3·K_D + 300 and Cfin = 100 (finalization, agent-03).
- Cst = finCst H K_D NB = K_D·n·(log₂ NB + 4) + (n+1)·((m+1)·CED K_D NB + 101).
- With K_D = 23037: Ko = 92469, K = 208989; hbig then needs a word exponent e ≥ 139.

## 3. Spine / B-L4 (recursion contract, loop, post-half, use threading) (owner agent-08; source /research/agents/agent-08/work/SPINE_MAP.md, sha256 7bd1610b482f)

### The BMSSP spine in Lean: theorem map (agent-08, B-L4, NON-GATE)

Status 2026-09-20 22:10 UTC. Every theorem below is kernel-checked, `#print axioms` = [propext, Classical.choice,
Quot.sound], no `sorry`. The hashes are sha256 prefixes of the installed files in `/research/lean/Frontier/CHD`.

#### What the spine proves

The recursive BMSSP procedure `P_bmssp` of the named RAM program refines agent-01's concrete Layer-A relation
`BMSSPD` (CallD above level 0, BaseDH at level 0). The contract is `CallSpec … l` (SpineLoop):

- the entry is `CallIn` (level, Static, label table, the D layer's DR, B-L2's PhiR, the S row, slots, Clear);
- the post is some Layer-A outcome `BMSSPD … l … res φ' g' lg`, together with:
  - `CallOut` (the returned U row, slot B', pointer invariant PtrOK, frames Above / stArr / ptrFr, Clear);
  - RAM cost `st.cost ≤ r.cost ≤ st.cost + K * lg.cost`, with ONE constant K at every level;
  - D-layer use `DL.use r ≤ DL.use st + 2 * lg.cost` (the use budget has factor 2 and no additive slack, since
    ucap is allocated memory and must stay O(Tchd));
- this holds for every outcome, given the budget premises `st.cost + K*lg.cost + Sl ≤ c0 + st.cap` and
  `DL.use st + 2*lg.cost ≤ DL.ucap`.

The level induction is `callSpec_all` (SpineLevels; agent-10 uses the equivalent `L6.LevelRoute`):
- the base case `CallSpec 0` is agent-03's `callSpec_zero`;
- the step `CallSpec l → CallSpec (l+1)` is agent-01's `callSpec_succ`;
- the step's only loop input is the spine's `LoopSpecB` (below).

#### Files and main theorems

| file (sha) | theorem / def | role |
|---|---|---|
| RamSpine 4586e26a | `expand_spec`, `LtI` | BM.11–12 expansion scan over the level group table. `LtI` is the expansion-test interface; agent-02 extended it with LV. |
| SpineLink f8290ece | `expand_link`, `scanW_sum` | The machine's expanded row equals Layer-A `BM.expand`, and the scan work equals Σ over pulled groups. |
| SpineLoop d4588e1e | `DLayer`, `PhiI`, `Static`, `Above`, `Clear`, `PtrOK`, `CallIn`/`CallOut`/`CallSpec`, `LoopRep`, `ALoop`, `mainLoop`, `loopTest` | Interfaces. DLayer is agent-04's D layer (ops pull/merge/delB/ins/new/empty with cost and use posts, NB, LT, use/ucap). PhiI is B-L2's state. |
| SpineIter 45e3e057 | `loadBi_spec`, `copyChild_spec`, `LFrame` (with `stArr`), `PostCall` | The hand-off between the first and second half of an iteration. |
| SpineA 5057c177 | `iterD_total`, `iterD_step` | Layer-A totality and one-step invariants of the loop. |
| SpineFirst 040b1245 | `preCall_spec`, `firstHalf_spec`, `iterW_of_sub`, `LoopRep.charge`, `loopTest_eval` | BM.10–13: pull (GoodHist, use room), expansion, child entry, the recursive call through the level IH, lvlUp. Cost ≤ (DL.K+CL+71)·(1+cp+\|ks\|+Σ) + K·lg; use ≤ (cp+1) + 2·lg. |
| SpineRule 4eca80c3 | `loopTight` | Budgeted while-rule at factor K: the body pays its own test, so there is no K+1 growth per level. |
| SpineLoopW 73e668b4 | `IterRelW`, `IterRelU`, `loopDW_of_relLoop`, `loopDU_of_relLoop` | Weighted iterations (own work at Ko, sub-calls at K). `IterRelU` pairs each configuration with the use spent so far (weights 2, 2). The bridges to `LoopD` carry both resources. |
| SpineLoopA b47f59d1 | `PostHalf`, `loop2_spec`, `LoopRep.of_frame` | The main loop BM.9–24. `mainLoop DL.empty (seq (firstHalf DL.pull ltBi) postI)` realizes one `LoopD` run with RAM cost ≤ Ko·(cc+cm) + K·lg.cost and use ≤ 2·(cc+cm+lg.cost). The second half is the interface `PostHalf`. |
| SpinePostA b78e1b18 | `postHalf_of_stmt`, `merge_blocks_le` | agent-06's `PostSpecStmt` (proved as `postSpec`, SpinePostProof) gives `PostHalf`. The block count after merge is ≤ 2·NB. |
| SpineLoopB 799b4256 | `LoopSpecB2`, `loopSpecB_of_loop2`, `loopSpecB_of_postSpec`, `postI`, `postProg_eq` | `loop2_spec` plus `postSpec` give agent-01's `RamBody.LoopSpecB`, the loop hypothesis of `callSpec_succ`. |
| SpineLoopInst 632e6dbf | `L6.hLoop_of_parts`, `L6.iterText` | Exactly the `hLoop` input of `L6.hs_of_parts`, for all instances and all levels l < LF. See below for what it discharges. |
| SpineLevels 2f1b1077 | `bmsspProc`, `spinePs`, `runs_call_base`, `runs_call_rec`, `callSpec_all` | Procedure dispatch (`ite lvl rec base`) and the level induction. |
| SpineRegFrame a7fbb6b3 | `exec_wreg_frame`, `Runs.wreg_frame_list` | Syntactic register frame across calls: a register assigned nowhere in the program or the procedure table keeps its value. |
| RamBaseCase 5ee0f66a | base-case machine pieces | Used by agent-03's `callSpec_zero`. |

`L6.hLoop_of_parts` discharges inside:
- Layer A via `levelPkg` (agent-01): fpC_sound / fpC_total / chdTau_pos / chdM_pos;
- CSRSorted via `csrSorted_of_outL` (agent-02);
- the second half via `postHalf_cmpTT` (agent-06);
- the expansion test via `ltBi_ltI` (agent-02).

#### Hypotheses that remain for the final instance (all per instance)

From `hLoop_of_parts`, discharged by agent-10 in `Final.lean`:
- closed D texts: `(DLf …).pull/merge/delB/ins = pullS/mergeS/delBS/insS`;
- names, all decidable: `PostHyg`, `ltW ∉ dWR / pWR`, `dWA ∉ pWA`, `dWR ∉ pWR`;
- slack: `postS K 27 n m (2·NB) ≤ Slf cn cm`, which is polynomial since NB = O(ucap);
- `LF ≤ DL.LT`, with LT := LF+1;
- constants: `Ko ≥ 4·K_D + 322`.

The recursion text must use `iterB := iterText pullS mergeS delBS insS`.

#### Design decisions recorded (for the write-up)

1. **One constant K at every level.** The loop charges its own work at Ko and the sub-calls at the IH's K (`IterRelW`), and loopTight has no `+1` factor. Otherwise the constant would grow per level and the cost bound would fail.
2. **Look-ahead budgets.** Every budget premise is "for every Layer-A outcome", discharged by continuation totality (`iterW_of_sub`, `iterD_total`, `RelLoop.total`). This is why RAM runs never need to know which outcome occurs.
3. **Use counter (D-layer memory).** This is a second resource with factor 2 at the CallSpec boundary. Each D operation posts `use ≤ use + (c+1)` with c ≥ 1 its logged cost, so `c+1 ≤ 2c`. The loop tracks the use spent so far in its abstract state (`IterRelU`), so loopTight itself is unchanged.
4. **Frames.** `LFrame` (rows and slots above the level, `stArr`) and `Above` protect the parent's data across child calls. The static arrays gSt/gHead/cp.tau/cp.M/gKeep/gRep are framed semantically through the loop (`LFrame.stArr`), and syntactically only at the top (SynFrame).

## 4. FindPivots-HD RAM (B-L2), FH.1-FH.26, prologue allocation (owner agent-09; source /research/agents/agent-09/work/THEOREM_MAP_BL2.md, sha256 4005be2ca5f6)

### THEOREM MAP — B-L2: FindPivots-HD at RAM level (owner agent-09)

Status on 2026-09-20 at 22:00 UTC: complete on the B-L2 side (plus the D-layer prologue hook dPro and the level-step input hFP_of). Everything is built in /research/lean. There is no sorry, and `#print axioms` gives
[propext, Classical.choice, Quot.sound], except where noted.

#### Layer B refinement chain (paper CHD_SEC_FINDPIVOTS FH.1–FH.25 ↔ Lean)

Legend: the paper step, then the Lean theorem (file, sha256 prefix), then the Layer-A relation it refines.

| Paper step | Lean theorem | Refines (Layer A, agent-05 `FindPivots.lean`) |
|---|---|---|
| FH.5–FH.11: scan of one out-list, with permanent deletion of edges below L_X, candidates, heap insertion and contact detection | `BL2.scan_spec` (BL2ScanSpec 260115ac, over BL2Scan/Loop/StepA–G) | `Scan c T u σ (c.out u) σ' r n` |
| FH.13–FH.14: unsorted-array ExtractMin | `BL2.extract_spec` (BL2Extract 4d46bf6c) | extraction step of `Search` |
| FH.5–FH.22: one local search (extract, then scan, until stop) | `BL2.search_spec` (BL2SearchSpec f2fb8918) | `Search c T σ₀ σ' res n` |
| FH.12 / FH.23: forest growth (new tree / contact merge) | interface `BL2.TreeI` (BL2Tree c9b92c7c), instantiated by agent-03's `PartitionRAM.treeImpl` | `growForest res trees x σ'` |
| FH.2–FH.25: invocation loop over the roots | `BL2.invoke_spec` (BL2InvLoop ecc9d811, over BL2Inv*) | `Invoke c ι₀ SL ι' n` |
| FH.1: L_X := d_B[S] = B ⊓ inf_{x∈S} d[x] | `BL2.lx_spec` (BL2LX 2624cb95) | `lxOf B S d0` |
| FH.1–FH.25 | `BL2.fpFind_spec` (BL2Find cfdcfbb6) | `FindPivotsC` (pinned L_X) |
| export of W to the level row, plus clearing inW | `BL2.export_spec` (BL2Export 7eeaaf36) | — (RowRep for BM.26) |
| complete call = FH.1 ; invocation ; FP-TAIL (agent-03) ; export | `BL2.fpCall_spec` (BL2Call 00ba28b3) | full `fpC` (groups `forestGroups`, data ω) |
| between-calls state | `BL2.FPClean`, `FPClean.congr` (BL2Call); `FPCleanNH` / `phiR` / `FPCleanNH.frame` (BL2Phi 484c06c5) | — (persistent state representation) |
| level-l call (slot B[l], S row l, fp.sb/fp.sn) | `BL2Inst.fpAt_spec` (BL2At a13f5ec7) | `fpC (outL G) k hins hext` |
| black box of agent-01's level body | `BL2Inst.fpB_inst` / `fpB_raw` (BL2FPB 83cec087 / BL2AtRaw b58801f4) | `RamBody.FPB` |
| spine persistent state | `BL2Inst.phiI` (BL2FPB) | `RamSpine.PhiI` |
| prologue (one-time allocation, initial live lists) | `BL2.outRep_init`, `BL2.fpAlloc_spec` (BL2Alloc 5d04f9b1), `BL2.fpAlloc_phiR` (BL2Pro 9bd0c100), `BL2Inst.fpHook` (BL2Hook aba3c140; agent-10's `L6.fpHook` is the version in use); `BL2Side.phWR_base` (BL2Side 6bbd2b2e) | `L6.HookSpec` |

#### Concrete instantiation and program text

- The name hygiene of every interface is DISCHARGED for the concrete layers by kernel evaluation. The layers are `labI c0` (agent-02), `labX c0` (agent-06's cmpTT, packaged in BL2Inst) and `treeImpl` (agent-03). The lemmas are `namesL_inst`, `names_inst`, `namesX_inst`, `namesT_inst`, `namesI_inst` and `namesD_inst` (BL2Inst), plus `namesTail_inst` and `namesCall_inst` (BL2CallInst).
- Two unsatisfiable NamesI fields were found this way and fixed (`srch_inv`, `inv_tab`).
- `fpFindC` and `fpCallC` (BL2Comp, BL2CallInst) are closed and computable, and are rfl-equal to the interface forms.
- **`fpAtRaw` (BL2AtRaw)** is the literal Stmt of the level call, generated from `repr fpAt`. `#print axioms fpAtRaw` gives "does not depend on any axioms". The bridge is `fpAt_eq_raw := rfl`.
- `fpAlloc` gives "does not depend on any axioms".

#### Costs (uniform constants)

- CFC = 342 and KC = 524, with `CFC_labI` and `KC_labI` proved.
- FPB constants: Kf = 524, Cf = 351.
- The Layer-A cost index pays for everything:
  - |S| ≤ cost, via `Invoke.tv_len_le`;
  - |W| ≤ cost, via `Invoke.W_card_le` (BL2Call);
  - the tail cost, via agent-03's `tail_le_invoke`.
- Requirements: 2 ≤ k ≤ hext. This is compatible with GoodP's hext ≤ ce·(k+1); the planned choice is hext = kF.

#### Remaining obligations owned by others

- `hDLA`/`hDLV`/`hDLR`: the D-layer names must avoid FP's write sets, which are listed in fp_writesets.txt. This is decidable for agent-04's DLayer instance.
- The level body (agent-01) uses FPB. The final assembly (agent-10) uses PIf := phiI and fpPro := fpAlloc.

#### Level-step input and the D-layer prologue hook (added 22:00 UTC)

| Obligation | Lean theorem (file, sha256 prefix) | Use |
|---|---|---|
| `hFP` of agent-10's `L6.hs_of_parts` | `L6.hFP_of` (BL2Step f567d799) | FPB at level `l+1` with `fp = fpAtRaw`, Kf = 524, Cf = 351. The remaining inputs are three decidable DLf name facts; the only candidate overlap is `sl.i`, which agent-04's save/restore wrapper removes |
| D-layer allocation hook `hD` | `DPro.dProSpec` / `dProSpec_full` (DPro 63889150); `DPro.dProSpecC` (DProInst fa0e51c5, Cw = 12·kmN) | `HookSpec e ps dProC (∃ Ds, DRI (dParC cn cm) r H0 DGl.init Ds (LF+1)) ∧ use ≤ 2` |
| `hPd` (PhiR survives dPro) | `DPro.hPd_dPro` (DProInst) | decided |
| `hucapF` | `DPro.dParC_ucap` (DProInst) | `12·kmN·Tnat + 2 ≤ ucap`, by `le_rfl` |
| call-free syntactic frame with allocations | `RAM.exec_cframe`, `RAM.Runs.cframe` (DPro) | general tool |

**dPro details.**
- Text: `dSizes Cw ; allocD ; newTopS ; KL.klAlloc ; dLvl`. It has no calls and no axioms.
- Parameters: `ucap = Cw·Tnat + 2`, `ecap = bcap = ucap + 2`, `top = LF + 1`, `psel = 1`.
- Cost ≤ `(23 Cw + 300)(Tnat + 1)`.
- Word size: `64 Cw + 128 ≤ 4^(e-1)`, which holds for e ≥ 32 when Cw = 12·kmN (`hCw_C`). Every word-size fact comes from `CoreIn.cap` (`dPro_cap`).
- `DAlloc` records all the raw facts. `dri_of_alloc` builds agent-04's DRI (a132ce48) from them, and it is the only lemma that changes if the DRI fields change.

**Literal twin.** A full-program trial (`chdProg 100 (chdPs skip skip fpAtRaw [selBody entLess 1]) (coreTop (spineOf (spinePro BL2.fpAlloc dProC)))`) gave:
- 765 KB and 8291 lines;
- compiles in about 30 s;
- the `rfl` bridge checks;
- no axioms.

#### Assumptions and honest scope of B-L2 (for LIMITATIONS)

**Word-size facts.** Every word-size fact that B-L2 uses sits in B-L2's persistent state and is established once, from CoreIn.cap = (cn+cm+2)^{e+1}. The facts are:
- `(2·LF+5)·n + 4·LF + 2k + 8 < cap`, the PhiR cap conjunct;
- `2n+2 < cap`, in the prologue.

Nothing is derived from the reduced graph's size alone, so tiny reduced graphs are covered.

**Cost.** B-L2's RAM cost is `≤ 524·c + 351` per call, where c is the Layer-A cost index of agent-05's fpC relation. The Layer-A index charges:
- the heap costs hins/hext per insertion/extraction (hext ≥ k is required, and the planned choice is hext = kF);
- scanC per scanned or deleted edge;
- |K|+2 per root.

The tail and the W export are paid by the same index (|S|, |W|, #tree vertices ≤ c).

**Model features used.**
- Plain word and value statements only, with no allocation inside the per-call program. This is checked by `fpAt_noalloc` (decided).
- No procedure calls.
- The one-time allocation `fpAlloc` runs in the prologue: 34n + 2k + 41 steps.

**Frames.**
- The declared write set of the per-call program is an over-approximation. It lists gHead, the scan's read footprint.
- The exact fact that gHead, gSt, cp.tau, cp.M, gKeep and gRep are never STORED to is kernel-checked syntactically (`fpAt_static`, `exec_wa_frame`).

**Not in B-L2.**
- The label layer (B-LAB, agent-02) and the table compare (agent-06) are used through their verified specs.
- The tree layer and FP-TAIL are agent-03's.
- The D layer is independent of B-L2. The only coupling is name disjointness, which agent-04 must decide.

**dPro scope (D-layer prologue allocation, agent-09).**
- One-time allocation. The use capacity is ucap = 12·kmN·Tnat + 2, and kmN ≈ 1.02·10^10. So the entry pool and block arrays hold ≈ 1.2·10^11·Tnat cells.
- This is O(Tnat) = O(Tchd) (Tnat ≤ 33·Tchd). The constant factor is honest but astronomically large. The asymptotic claim is unaffected.
- No reallocation: every DS' operation keeps all array lengths.
- Word size: `64·Cw + 128 ≤ 4^(e-1)` (e ≥ 32 suffices). All capacity facts come from `CoreIn.cap = (cn+cm+2)^(e+1)`.
- `sel.w` holds 6·ecap + 60 scratch cells for agent-05's BFPRT select, which runs as procedure 1.

## 5. DS' / B-L3 data structure (ops, representation, instance DLf) (owner agent-04; source /research/agents/agent-04/work/PAPER_TO_CODE_agent04.md, sha256 f81a26869f1e)

### Paper-to-code: the DS' data structure (B-L3), agent-04 (NON-GATE)

Status 2026-09-20 22:23 UTC.
- Every name below exists at the given line of the installed file `/research/lean/Frontier/CHD/<File>.lean`. The sha is the sha256 prefix.
- `#print axioms` is [propext, Classical.choice, Quot.sound] for all theorems, and there is no sorry.
- Owners: agent-04 unless noted.

#### Where the spine uses DS'

The interface is `RamSpine.DLayer G s T` (SpineLoop.lean l.185–289). Each op spec refines the matching `BM.dlOps` step:
- the Layer-A op is DLazy / DBlocks through `BMLazy.dlOps` (BMLazy l.2875);
- the RAM cost is ≤ K·(Layer-A cost + 1);
- `use` grows by at most the Layer-A cost + 1;
- the frame is exact.

The instance is `DLayerF.DLf T cn cm` (DLayerF l.188). Final.lean uses it as `Final.DLfC H src cn cm := DLI.DLf (G := H) (s := src) Tz cn cm`.

| paper line | Layer A | Layer B (RAM text / spec) | cost (RAM steps) |
|---|---|---|---|
| BM.3–5 new D at call entry | `BM.newC M Bd` | `DLI.dsNew` (DLayerInst l.596) / `dsNew_spec` (l.786) → `DLayer.new_spec`. Inside: `DGlobal.newTopDL` (l.731) and `KeyLists.klInit_LL` (l.882). | = 22; use +1 |
| BM.6/7, BM.23, BM.25, BM.27–28 Insert (keep-min, rule EA) | `BM.insC` = `DLazy.insertL` (l.1008) / `insertL_spec` (l.1016). **No split** (paper v1.6 R-1). | `DLI.dsIns` (l.1108) / `dsIns_spec` (l.1509). Steps: skip test via the global live map, binary search on the separator stack, prepend. Specs: `DInsertB.insRAM_spec` (l.492, agent-02), `DInsDL.insertDL` (l.68), then the key-list moves `KeyLists.klUnlink_LL` (l.833) and `klLink_LL` (l.844). | ≤ 40·(c + 1), with c = 2 (skip) or bsCost(#blocks) + 3 = ⌊log₂ #blocks⌋ + 4 (DLazy l.1004–1012) |
| BM.9 / BM.24a IsEmpty | `DS.IsEmpty (g.view D)`, `DLI.isEmpty_iff` (l.415): IsEmpty ↔ no live key | `DLI.dsEmpty` (l.413) / `dsEmpty_spec` (l.420) → `DLayer.empty_spec`. Uses `KeyLists.klTest_LL` (l.893) and `LL.empty_iff` (l.444). | ≤ 2 |
| BM.10 Pull | `BM.pullC` = `DLazy.pullL 1` (l.518) / `pullL_spec` (l.554): lazy front prep `DLazy.prep` (l.226), then select | `DLI.pullD` (DLayerF l.33) / `pullD_ok` (l.54). pullD saves and restores sp.go/sp.t/sl.i and runs agent-05's `PullWrap.pullW` (l.57) / `pullOK_of` (l.503). The core is `DPull.pullS_spec` (l.4355): prep splits, collection, BFPRT select (SelectRAM), cut. The pulled keys go to the child S row, the separator to slot B_i[l], and the pulled keys are unlinked. | ≤ (Kpw + 6)·(c + 1) |
| BM.14 Merge (group splice, keep bit) | `DB.merge 1` (DBlocks l.1106) / `merge_spec` (l.1117); `DLazy.mergeM_amortized` (l.1442); `DB.lazy_merge_eq_literal` (l.1443) | `DMergeI.dsMerge` (l.69) / `dsMerge_spec` (l.546) / `dsMerge_ok` (l.612), agent-02. Inside: `DRekey.rekeyDL` (l.175), `DList.mergeS_spec` (l.1453) + `mergedD_eq_merge` (l.1749) (grouping, flush, shift on the shared stack), `DGlobal.mergeDL` (l.253), `KeyLists.klSplice_LL` (l.857). | ≤ 17·(c + 1) |
| BM.15 FIX-STALE Delete U_i | `BM.delC g lU` = `DB.deleteKeys` / `deleteKeys_spec` (DBlocks l.908) | `DLI.dsDelB` (l.916) / `dsDelB_spec` (l.1044): `DGlobal.delDL` (l.615) + `DLI.unlinkRow_spec` (l.879) | ≤ 13·\|U_i\| + 9 |
| BM.29 Delete W' | `deleteSet W'` | `DDelW.dsDelW` (l.26) / `dsDelW_spec` (l.155) / `delWBU_mkDL` (l.167), agent-01: dsDelB on the Wp row | ≤ 13·\|W'\| + 9 |
| DS' representation (§3.4) | `DStr`, `WF` (DBlocks l.142), `HasKey`, `view` | agent-02 (DRep): `EntRep` l.42, `BlkRep` l.68, `DRep` l.89, `LiveRep` l.106, `PoolRep` l.112, `SepRep` l.55. Mine: `DGlobal.DLRep` l.34 (one shared block stack for the active levels lo..lo+k, each child on top of its parent) and `DLI.DRI` (DLayerInst l.88), with the frame `DRI.frame` l.261. | — |
| block bound NB | `DRI.nb_le` (l.1526) | NB = ucap | — |
| one-time allocation | — | `DPro.dPro`, `DProInst.dProSpecC` / `dParC_ucap` (agent-09). Uses `DGlobal.allocD_spec` (l.706) and `KeyLists.klAlloc_spec` (l.963). | O(Tnat) |
| the instance | `BMLazy.dlOps` (l.2875) | `DLayerF.DLf` (l.188) := `DLayerInst.mkDL` (l.1612) (DPro.dParC cn cm) … `dsMerge` `pullD`. Names: `DLf_names` (l.180), by decide. | K_D = Kpw + 6 = 23037 |

Constants of the instance:
- K = 23037 (Final.lean `hKD`);
- NB = ucap = (dParC cn cm).ucap = dUcap (12·kmN) cn cm = nbF cn cm = 12·kmN·Tnat + 2 (Final.lean `hNB` is rfl);
- LT = LF + 1;
- use = ds.fresh + blk.fresh ≤ ucap.

#### Paper item for §3.4 (suggested text for v1.7; the code already does this)

**IsEmpty in O(1).** The paper reads IsEmpty at BM.9, BM.24a and BC.3 and says stale entries are invisible to it (agent-02 C4), but does not say how the test is O(1).

The implementation: each level keeps a circular doubly-linked list of its live keys (sentinel n + l).
- Insert unlinks the key from whatever list holds it. This may be an ancestor's (rule EA); unlinking needs no level. Insert then links the key into level l's list.
- Delete unlinks the key.
- Pull unlinks the pulled keys.
- Merge splices the child's list into the parent's in O(1).
- IsEmpty(level l) is then one comparison: `next[sentinel] = sentinel`.

Per-level counters do NOT work. An Insert can supersede a live entry of any ancestor level. After a Merge the superseded entry's recorded level is stale, and relabelling the child's entries would cost Θ(|D'|), which breaks Merge's O(1 + |D'|/M') bound. The lists avoid this: every op on them is O(1) and none needs the level.

Formal: `KeyLists.LL` (l.396) with membership `v ∈ K l ↔ DB.HasKey g.L (Ds l) v` (field `DRI.kl`). The ops cost O(1) each. The spine never pays more than the Layer-A cost + 1 per op.

#### Other D facts a reviewer may ask about

- **Register hygiene of the pull.** agent-05's core pull uses sp.go, sp.t and sl.i as scratch. pullD saves them in dp.go/dp.t/dp.si and restores them.
  - Result: the D-layer write lists `dWR = wrD ++ xWR` avoid every spine, scan, body and B-L2 list (agent-02 re-checked at 22:19).
  - The raw `PullWrap.pwWR` still contains sp.t and must never be used as a D list.
- **Merge precondition.** The spine supplies dlOps.merge_spec's three separator facts: the parent's live values are ≥ the child's bound, the parent's non-front separators lie above the child's bound, and Bd' ≤ Bd.
  - These show the dropped front block holds no live key, so the in-place RAM merge equals `DB.merge 1`.
- **Capacity.** use = ds.fresh + blk.fresh counts allocated entries and blocks. Each op grows it by at most its Layer-A cost + 1.
  - The spine threads it at factor 2 (CallSpec: `use r ≤ use st + 2·lg.cost`, no slack).
  - Hence ucap = O(Tchd), allocated once by dPro, with no reallocation.

## 6. FindPivots-HD Layer A, select/filters, DLazy pull refinement (owner agent-05; source /research/agents/agent-05/work/PAPER_TO_CODE_agent05.md, sha256 a386145b923e)

### Paper-to-code: agent-05 components (NON-GATE; for THEOREM_MAP.md)

All files are installed in /research/lean/Frontier/CHD/. `#print axioms` on each main theorem gives [propext, Classical.choice, Quot.sound]. None contains sorry, admit or native_decide.

| Paper item | Lean theorem | File (sha256 prefix, lines) |
|---|---|---|
| FindPivots-HD pinned relation (Layer A) | `findPivotsCL_spec`, `FPContract` | FindPivots.lean (6c28dde5, 2891) |
| FindPivots binding to BM (Layer A) | `fpC_sound`, `fpC_total`, `fpC_spec`, `fpC_foreign`, `fpC_tv_card`, `fpC_interval`, `fpC_cost_del`, `fpC_tedge` | FPBind.lean (bc1ddd40, 186) |
| Deleted-edge disjointness (O3) | `loopC_chain`, `bmsspC_chain`, `counters_del_disj` | FPDel.lean (d460004a, 221) |
| Merge total (O23) | `counters_merge_total` | MergeTotal.lean (649833ff, 260) |
| Linear-time selection in the RAM (BFPRT, generic comparator) | `sel_spec`: rank-k element, cost ≤ (400·Cl+2100)·n+100 | SelectRAM.lean (a43a81ac, 2383) |
| Selection filters (partition by pivot) | `filt_spec` (< / >), `filtGe_spec` (≥) | SelectRAM.lean |
| Comparator on pool-entry labels | `entLess_spec` (a LessSpec instance, via B-LAB cmp/cbit_eq/lt_iff) | EntLess.lean (33ae6ab5, 130) |
| DLazy prep step (median split of the front block) | `splitStep_spec` | DPull.lean (4aa9ef86, 4546) |
| DLazy prep (split while SplitG) | `prep_loop`, `prepTop_spec` | DPull.lean |
| DB.pull collection over prepList | `col_round`, `col_loop` (by `prepList.induct`) | DPull.lean |
| DB.pull finishes (exhausted / cut at rank M) | `pullAll_spec`, `pullCut_spec` | DPull.lean |
| DLazy.pullL 1 (complete Pull) | `pullS_spec`: PullRes (DRep/RecsOK/LiveRep of the result, keys in S row lv−1, separator in slot 4lv+3, frames), cost ≤ 23011·(c+1), blk.fresh bound | DPull.lean |
| DLayer pull (spine interface) | `pullW_spec`, `pullOK_of`, `pullOK_inst` (DLI.PullOK on dnames_of lists, K ≥ 23031) | PullWrap.lean (c7aa18de, 557) |

Model notes:
- The pull calls the selection procedure through `call pSel`, with `procs[1] = selBody entLess 1`. Each call is charged by `enter` (cost +1, space +1).
- All other code is straight-line RAM. There are no allocations; the prologue (dPro) allocates sel.w with 6·ecap+60 cells.
- Space: the model keeps space ≤ cost.
- Registers written by the pull are pwWR. They avoid RamSpine.spRegs (`pwWR_ok`, by decide), after the rename to `dsp.go` and the save/restore of `sl.i`.
  - pwWR still contains `sp.t`, the split step's scratch register. It is not in spRegs, but it is PostHyg.gdel's register.
  - So the D layer never uses the raw pwWR. In the final program the pull is agent-04's `DLI.pullD`, which saves and restores sp.go, sp.t and sl.i around `pullW 1`. Its register list is `pdWR = pwWR.filter (∉ spSaved) ++ [dp.go, dp.t, dp.si]`, and `pullD_ok` is in DLayerF.lean.
- Final instance: `Final.DLfC H src cn cm = DLI.DLf Tz cn cm = mkDL (dParC cn cm) … pullD (pullD_ok …)`. Its pull text is `DLI.pullD`, and its K = Kpw + 6 = 23037.
- Space: the pull allocates nothing. The DS' arrays, including sel.w, are preallocated by dProC at Θ(Tnat) cells (see the 22:54 honesty item). The whole program's formal space bound is space ≤ cost.

## 7. B-LAB labels, B-L3 insert/merge, B-L4 scans/RelW/PtrScan (owner agent-02; source /research/agents/agent-02/work/PAPER_TO_CODE_agent02.md, sha256 966eebf916e0)

### Paper-to-code rows for agent-02's components (for THEOREM_MAP.md; agent-02, 2026-09-20 22:40 UTC)

All files are installed in /research/lean/Frontier/CHD. Every file listed builds, has no sorry, and its
axioms are [propext, Classical.choice, Quot.sound] or fewer. The shas are the first 8 hex digits of
sha256 at 22:40.

#### B-LAB: the label layer (κ order, table, RAM label fragments)
| Paper item | Lean (Layer B) | sha |
|---|---|---|
| κ realized by O(1) machine labels (5-tuples, versions) | MLabel.lean: `MLabel`, `Rep`, `lt_iff`/`eq_iff` (x.lt y ↔ toW p < toW q under GoodHist), `GoodHist` | 5a652f89 |
| label table d[·] + history of walks | LabTab.lean: `Tab`, `Represents`, `tabOf`, `mlt_iff_fields` | 9941442a |
| RAM label fragments: cmp, candLab, loadLab/storeLab, relaxFP (FH.relax), relaxBM (BM.20/27 relax), ltB/headLtB, candB, initLab, loadA/storeA | LabRAM.lean: `cmp_wp`, `cbit_eq`, `candLab_wp`, `loadLab_wp`, `storeLab_wp`, `relaxFP_spec`, `relaxBM_spec`, `ltB_wp`, `ltB_bit`, `headLtB_wp`, `candB_spec`, `initLab_wp`, `loadA_wp`, `storeA_wp`, `LabAt`, `WHolds` | 0c55c31e |
| label-layer interface for FindPivots-HD (agent-09's FPIface) | LabI.lean (`labI`), LabIC.lean (program fields are closed Stmts) | c5844802 / cb3192df |
| BM.25/BM.26 vertex tests | LabTests.lean: `tstT6`, `tstWp`, `RamInit.TestI` instances | 7dc4738f |
| table–table compare for pivot/group selection | CmpTTI.lean: `cmpTT_cmpI` (RamInit.CmpI, C = 27) | e8c04689 |
| BM.12 expansion test [d(px) < B_i] | LtBiTest.lean: `ltBi_spec`; LtBiI.lean: `ltBi_ltI` (= the hLt of firstHalf_spec/loop2_spec; CL = 22, LW = ltW, LV = [sp.yl]) | c369ef18 / 8e5e4422 |
| BM.8 B'_0 and spine label steps | SpineLab.lean: `b8Prog_spec` and the slot/label steps | 8b6c1e40 |

#### B-L3: DS' RAM representation, Insert, Merge (with agent-04's DLazy/DList/DGlobal)
| Paper item | Lean (Layer B) | sha |
|---|---|---|
| DS' layout: entry pool, block records, separator stack, live map | DRep.lean: `EntRep`, `LList`, `SepRep`, `BlkRep`, `DRep`, `LiveRep`, `PoolRep`, frames | 1c2508b2 |
| history growth / table-only steps keep D | DRepExt.lean | 55382c29 |
| binary search over the separator stack | BSearch.lean (pluggable probe) | f088ec91 |
| §3.4 Insert = binary search + prepend (never splits) | DInsertA/L/B.lean: `insRAM`, `insRAM_spec` (refines DLazy.insertL via `insertNS`), cost 24 (skip) / 70 + 35(⌈lg⌉+1) | df937867 / 94742fd8 / 3999c88e |
| **BM.14 Merge** (keep bit ltSep D'.Bd (nextSep rest D.Bd); rekey/drop front; group child blocks in place; splice live-key lists) | DMergeI.lean: `dsMerge` (closed Stmt), `dsMerge_spec` (DRI lo → DRI (lo+1) with update Ds (lo+1) (DB.merge 1 …).1; cost ≤ 17(merge cost + 1); use unchanged), `dsMerge_ok` / `dsMerge_mergeOK` (= agent-04's MergeOK with l ≤ P.top) | d486f91e |

#### B-L4: scans, relaxations and pointers (with agent-08's spine)
| Paper item | Lean (Layer B) | sha |
|---|---|---|
| per-edge relax + insert into lazy D (BM.20/27) | RelaxIns.lean: `relaxInsRAM_spec` refines BMLazy.relaxInsCc; `insC_dl_cost` | ddfb9cc4 |
| BM.19–21 window scan, one vertex (inner loop, stops at the first cand ⪰ B) | WinScanB.lean: `winInner_spec` | ebc018b2 |
| BM.19–21 / 27–28 scan over a row; pointer invariant PtrAt (H0') | WinScanC.lean: `scanLoop_spec`, `winScan_spec`, `window_char`, `ptr_advance`, `CSRSorted`, `PtrAt` | 70095179 |
| BM.27–28 W' relaxations (whole range) | WinScanD.lean: `wScan_spec`, `fold_full`, `fullSlots_enum` | 356866ff |
| the scans over the ABSTRACT D layer (use/ucap threaded) | WinScanE.lean: `winScanD_spec` (L' Nodup ∧ e ∈ L' ↔ src ∈ U_i ∧ B_i ≤ cand < B), `wScanD_spec`, `ScanStop.eq_stopOf` | 1fecd002 |
| DLayer → scan interface | WinScanF.lean: `DInsI.ofDLayer` | 0b083aec |
| BM.27–28 for the level body | RelW.lean: `relW_spec` (Enumerates W' fold; completeness premise, §4.4 A-1) | a331b0d6 |
| base case pointer set (BC.7 then ptr = first cand ⪰ B) | PtrScan.lean: `ptrSet_spec` (cost ≤ 25 deg + 30) | dc8b28ed |
| sorted CSR from CoreIn | CSRSortedOf.lean: `csrSorted_of_outL` | 2a50c674 |
| allocation-free ⇒ lengths kept | ExecLen.lean: `exec_len`, `Runs.len` | 39436052 |

#### Interface statement fixes by agent-02 (spine-owned files; the proofs are the owners')
- RamSpine `LtI` gains the value list LV and `run`'s premise `px < n` (G2-16). SpineFirst/SpineLoopA threading: RamSpine 4586e26a, SpineFirst 1d2b9170, SpineLoopA c84033fc (21:25). Later edits are by agent-08.
- DLayer.merge_spec's level bound `l ≤ LT`. I found it (20:48); agent-06 installed it in SpineLoop d4588e1e.

## 8. Layer A (BMSSP relation, costs, base case) and Layer B rows of agent-03 (owner agent-03; source /research/agents/agent-03/work/PAPER_TO_CODE_agent03.md, sha256 133e4e8501d5)

### PAPER_TO_CODE — agent-03's components (PAPER_CHD v1.7 → Lean), for final/THEOREM_MAP.md

This map is NON-GATE. The sha values are the first 8 hex digits of sha256 of the installed files under /research/lean/Frontier/,
as of 2026-09-20 ~22:50 UTC. Every file listed is installed, depends only on std axioms, and contains no sorry.

#### Layer A: the time analysis, PAPER_CHD §5
| Paper item | Lean name(s) | File@sha |
|---|---|---|
| §5.1 handled ranges; §5.2 pivot bound with foreign leaves | level_pivot_mass_le, beta_sum_le, sum_card_le_of_unique | Density.lean@e3d7b35f |
| §5.3 home charging (contact-through-leaf) | cross_of_home_ne, split_of_home_ne, card_children_meeting_le | Homes.lean@88bba589 |
| §5.2 foreign-leaf counters of FindPivots-HD (N3) | counters_foreign_level, counters_full_p, counters_partial_Fo | CHD/FPForeign.lean@1e38306f |
| §5.3 re-selection charging (N4) | pieces_bich_sum, groups_colors_le, forall2_colors_le | CHD/Reselect.lean@4a069d52 |
| cross/between counters (T5 inputs) | bich_le_crbe, mkOf_full_le | CHD/CrBe.lean@7bc25b06 |
| §5.4 per-call costs T0–T7, summed over the loop | loopC_cost, callC_cost, sum_card_le_of_disjoint | CHD/LoopCost.lean@3a816b56 |
| log / record costs of a traced run | callC_reccost, bmsspC_reccost, childSumAt_eq_sum | CHD/CostLog.lean@669a2db2 |
| FindPivots W/Q sizes | fpC_W_card, Invoke.W_card, Search.failed_K | CHD/FPWQ.lean@5cbfe6c5 |
| recursive FP log, the forest of calls | bmsspC_recall, recForest_of_run, loopC_recall | CHD/RecFPLog.lean@23628c5c |
| (G4) Q-witness (reviewer O22), in-degree free | qwit_of_prov, wit_exists, bmsspC_qwit, bmsspC_prov, tracedCounters_wit | CHD/QWit.lean@52d6e1cf, QWitProv.lean@319676a8, QWitValid.lean@3e8a6b3e |
| traced counters: cr/be/del (Valid fields) | tracedCounters_cr_cross, tracedCounters_be_total, tracedCounters_del_disj | CHD/CostLe.lean@703ccf53 |
| OBJECTION 4 fix (FindPivots charge ≤ with hext) | fpA_le_of_hext | CHD/CostLe2.lean@5fbaaefe |
| (O12) trace sizes: own placements, ucap | ownSum_le, ownB_le_wB, wB_sum_le, ucap_le | CHD/TraceSize.lean@7077d064, TraceSizeD.lean@548b5739, SizeParams.lean@01b842af |
| size facts of calls (\|U\| ≤ ucap, base ↔ lvl 0) | bmsspC_sizes, loopC_sizes, baseLoopC_U | CHD/SizeFacts.lean@ca39bbfc |
| §3.3 FH.26 MakePivots equivariance under Fin.val | makePivots_map, mpStep_map, parentFirst_map | CHD/PartitionMap.lean@125c2113 |
| base loop pays out-degrees (pointer pass, clear) | baseLoopC_deg_le, Enumerates.length_eq | CHD/BaseCostDeg.lean@5cb5bd3b |
| DLazy insert keeps Bd and #blocks; cost ≤ log₂ NB + 4 | insertL_Bd, insertL_blocks, insManyC_Bd, insManyC_blocks, insManyC_cost_le, insManyC_len_le, insManyC_take_le | CHD/DLazyFacts.lean@cd97eac8 |

#### Layer B: RAM refinement (CostModel v2)
| Paper item | Lean name(s) | File@sha |
|---|---|---|
| FH.26 PT program (pieces, groups into GrpOut) | ptProg_spec, GrpOut.congr (+ PartitionRAM..4 steps) | CHD/PartitionRAM5.lean@7bfd0e1c (+ PartitionRAM@8bbb9c30, 2@4792709d, 3@966b7df1, 4@41fcd74a) |
| mark loop | markLoop_spec | CHD/MarkLoop.lean@3a4ac402 |
| syntactic frame for word-only statements | exec_WS, Runs.wframe, WFr.unchanged | CHD/WFrame.lean@001b0795 |
| §3.3 tree layer T1–T4 (new tree, grow, merge, compact, FP-TAIL) | ntLoop_spec, rpLoop_spec, pcLoop_spec, mergeProg_spec, growProg_spec, compact_forestAt, fpTail_spec, allocFP_spec | CHD/TreeRAM.lean@0091405f … TreeRAM10.lean@1c509791 |
| FindPivots-HD composite = fpFind ; fpTail refines FindPivotsC + GrpOut | fpInvTail_spec, fpFull_spec, namesFull_inst, fpC_of_findPivotsC, forestGroups_facts, tail_le_invoke | CHD/FPComposite@d9b76edf, FPFull@6c954eb2, FPFullInst@c0f031bc, FPBridge@1af89c91, FPBridge2@1011ac3c, FPTailCost@3c788181 |
| BM.5–6 / base conversion: insert a slot segment | insSeg_spec | CHD/InsSeg.lean@b4c8b847 |
| base conversion over the heap slots (Layer A) | baseConv_spec, HRL.slots | CHD/BaseConv.lean@de889079 |
| BaseDH from BaseC + slot enumeration | baseDH_of_baseC | CHD/BaseDHGlue.lean@6e4f6cee |
| level-0 conversion on the D layer | convDL_spec | CHD/BaseConvDL.lean@fb6d21be |
| base pointer pass (PtrOK for returned U) | ptrLoop_spec | CHD/PtrLoop.lean@220f5275 |
| **base case = CallSpec 0**: heap base + ptr pass + conversion + clear; closed text | callSpec_zero, baseProg_spec, baseProgC, baseBody_closed, baseProg_closed, baseC_fin, baseC_heap_lt | CHD/BaseCall0.lean@49c164f7 |
| allocation-free ⇒ lengths kept; slot facts | exec_noAl, Runs.noAl, SlotHolds.of_idx, SlotLens.of_len | CHD/BaseUtil.lean@d9a45ac7 |
| **BM.24a–31 finalization**: B'f, T6, W', relaxations out of W', delete W', clears → FinOut / FinB | fin_spec, fin_spec_stmt (= agent-01's FinSpecStmt), fin_B, bpf_spec, t6_spec, wp_spec, clears_spec, copyBtoBp_spec | CHD/RamBodyFin.lean@68e3511c, RamBodyFinDefs.lean@439728a8 |
| index frames of the heap base case (F1–F3) | appended conjuncts of extractBody_spec, baseLoop_spec, setBp_spec, baseBody_spec | CHD/RamBaseCase.lean (agent-08's file; agent-03 patch 5ee0f66a, later edits by its owner) |

#### How the paper statements map onto the formal route (my part)
- §5.4's base-call accounting is BaseDH's log cost: S·(1+bins) + c + 1 + conversion. The RAM cost of the base case is at most
  K·lg.cost for K ≥ 2·DL.K + 82 (callSpec_zero), and the D-layer use is at most 2·lg.cost.
- §5.4's T6/W' terms (1 + |S| + |W| + |W'| + finD cost) are CallD's record terms. The finalization's RAM cost is at most
  Kfin·(those terms) + 3|U| + 100, with Kfin = 3·DL.K + 300 (FinOut.cost2). The 3|U| is charged to the loop cost cl by agent-01's
  body_spec.

## 9. Reviewer #1 final route summary and discrepancy log (D1-D9, all resolved) (owner agent-07; source /research/agents/agent-07/work/PAPER_TO_CODE_map_route.md, sha256 faa0eaea7748)

### agent-07: route summary (frozen tree #33) and the paper-to-code discrepancy log

#### Final route, top-down (every node installed, std axioms, and replayed by reviewer #1)
| level | Lean |
|---|---|
| Gate C | `Frontier.CHD.Final.chd_gateC : Frontier.GateC`, via `GateCTarget.chdTarget_F_imp_gateC` |
| frozen target | `Frontier.CHD.Final.chd_CHDTarget : GateCTarget.CHDTarget GateCCalc.F` |
| the named program | `Frontier.CHD.Final.chdProgram := chdProg 160 psC coreC` (axiom-free); `Frontier.CHD.Final.chd_exact_within` |
| generic final composition | `L6.chdProg_of_DLayer` (FinalGen) |
| top theorem from D layer + level step | `L6.chdTarget_of_step` (Assembly) → `L6.chdTarget_of_levels` (LevelRoute) |
| level induction | `L6.callSpec_of_levels`: base `L6.callSpec_base` (agent-03's `RamSpine.callSpec_zero`); step `L6.hs_of_parts` → `RamBody.callSpec_succ` → `RamBody.body_spec` |
| level-step inputs | `L6.hFP_of` (FindPivots), `L6.hLoop_of_parts` (loop; `SpineLoopA.loop2_spec` + `RamSpine.postSpec`), `L6.hFin_of_parts` (finalization; `RamBodyFin.fin_spec_stmt`) |
| D layer | `DLI.DLf` (DLayerF) := `DLI.mkDL` with ops dsNew/dsIns/dsDelB/dsEmpty (DLayerInst), `DLI.dsMerge` (DMergeI), `DLI.pullD` (DLayerF; wraps `PullWrap.pullW`); allocation `DPro.dProC` with `DPro.dProSpecC` |
| exactness | `L6.complete_of_topRun` (`BM.bmsspDL_top`), `L6.coreOut_of_labAt` |
| master cost (Layer A) | `L6.masterSpec_of_good`, `TraceFits.chdDL_tele_top`, `CostFinal.total_le_Tchd` |
| dispatcher / L6 / output | `Dispatch.dispatch_runs`, `Dispatch.bf_bodySpec`, `L6.l6_runs`, `L6.body_spec`, `L6.outLoop_runs` |

#### Paper-to-code discrepancy log (reviewer #1); ALL RESOLVED in the paper
- D1: base case BST → IHeap + level-0 DS' conversion. Resolved in PAPER_CHD v1.5.
- D2: split charging → separator stack + Ψ potential. Resolved in v1.5.
- D3: header version. Resolved in v1.5.
- D4: "binary-heap Dijkstra for small N" → Bellman–Ford fallback (`Dispatch.bf_bodySpec`). Resolved in v1.5.
- D5: gM ≤ 1.5m → proven gM ≤ 2m (`L6.sl_n_le`). Resolved in v1.5.
- D6: L := min{l : Λ_l ≥ N} → fixed LF(cn, cm) (`L6.tau_top_gt`). Resolved in v1.5.
- D7: Insert eager split → never splits (`DLazy.insertL`). Resolved in v1.6 (agent-02's R-1).
- D8: prepaid base conversion. Resolved in v1.6.
- D9: stale G7 tree/split lines. Resolved in v1.6.
- Final paper candidate: PAPER_CHD v2.0 (cbdf6c9e).
  - Its §1 Theorem 1 / Corollary 2 are exactly `chd_exact_within`/`chd_CHDTarget`/`chd_gateC`, checked 23:01.
  - F is `Nat.sqrt (Nat.sqrt (Nat.log 2 n ^ 3))` = ⌊⌊log₂ n⌋^{3/4}⌋.
  - Tdisp (GateC.lean:27-28) and the profile μ = n·⌊ln(n+2)^{3/4}⌋ (GateCCalc.μ) match.
  - Theorem 3 (the full window) is marked NOT formalized.


## 10. Mechanical verification (agent-07, 23:02 UTC)

Command: python3 repro/theorem_map_check.py repro/final1/proj/Frontier THEOREM_MAP.md. The tree is the frozen #33 copy, byte-identical to sources_33.sha256.

```
identifiers checked: 626, declared: 607, missing: 19
MISSING THEOREM_MAP.md hDel
MISSING THEOREM_MAP.md hSl
MISSING THEOREM_MAP.md L6.LevelRoute
MISSING THEOREM_MAP.md hLoop
MISSING THEOREM_MAP.md Final.lean
MISSING THEOREM_MAP.md iterB
MISSING THEOREM_MAP.md FindPivots.lean
MISSING THEOREM_MAP.md repr
MISSING THEOREM_MAP.md hDLA
MISSING THEOREM_MAP.md hDLV
MISSING THEOREM_MAP.md hDLR
MISSING THEOREM_MAP.md hFP
MISSING THEOREM_MAP.md hPd
MISSING THEOREM_MAP.md hucapF
MISSING THEOREM_MAP.md le_rfl
MISSING THEOREM_MAP.md hNB
MISSING THEOREM_MAP.md next
MISSING THEOREM_MAP.md prepList.induct
MISSING THEOREM_MAP.md Nat.sqrt
file:line citations off by > 3 lines or wrong file: 0
```
The 19 unmatched tokens are not Frontier theorem names:
- hypothesis names: hDel, hSl, hLoop, hDLA, hDLV, hDLR, hFP, hPd, hucapF, hNB;
- variables: iterB, next;
- file or module names: L6.LevelRoute, Final.lean, FindPivots.lean;
- Lean core or auto-generated names: repr, le_rfl, Nat.sqrt, prepList.induct.
Every cited Frontier theorem/def exists in the frozen tree, and every file:line citation is within 3 lines.

### 10.1 Cross-check by agent-09 (23:39): hash citations
- 51 of 53 file-hash citations match frozen #33.
- The 2 others are DATED HISTORY in part 7 (agent-02's "Interface statement fixes" paragraph, l.~419): the 21:25 hashes of SpineFirst / SpineLoopA. SPINE_MAP (part 3) already has the frozen values (agent-08, 23:40).
  The frozen #33 values are SpineFirst 040b1245 and SpineLoopA b47f59d1.
- Part 4 (B-L2) matches: 20/20 hashes OK.

### 10.2 Closure membership (agent-07, 23:56)
Every backticked name was checked against the module list of the Frontier.CHD.Final closure: 266 modules, taken from my kernel replay repro/final_final1/replay.txt.
Six cited names are declared ONLY outside the Final closure. They are installed, compiled alternatives or duplicates that the final route does NOT use:
| cited (not on the route) | file | what the final route uses instead |
|---|---|---|
| `L6.hFin_of_parts` | L6/FinInst | `RamBodyFinB.finB_uniform` + `RamBodyFin.fin_spec_stmt`, directly in Final.lean:132-133 |
| `RamBody.sbA_fpC` / `sbA_fpC` | RamBodyL | `L6.hSbA_chd` (L6/SbA; used at StepInst:103) |
| `Runs.wreg_frame_list`, `exec_wreg_frame` | SpineRegFrame | the syntactic frame `RAM.exec_frame` / `Runs.frame` (SynFrame) |
| `BL2Side.phWR_base` | BL2Side | the name facts `Final.n_*`, decided by `decide +kernel` in Final.lean |
All other cited theorems are in the closure of the accepted theorem, as far as their names occur in it.
