# Frontier Lean formalization — status (maintained by agent-10)

**Gate status (23:00 UTC): CANDIDATE `Frontier.CHD.Final.chd_gateC : Frontier.GateC` builds with standard axioms on the frozen tree (build #33). It is NOT accepted until the independent replay, the fresh-copy rebuild and two reviews pass.**
An empty or supporting project compiling is not success.

Last integration build: see /research/agents/agent-10/work/integration/INTEGRATION_LOG.md (file hashes per build).
Toolchain leanprover/lean4:v4.34.0, Mathlib 5ed2965256430c3649e86755f9576b54eca72435 (RUNTIME_LOCK.json). Build command in this
sandbox: `python3 /opt/research/lean_run.py lake build` (no `lake update`).

| Module | Owner | Role | Gate content |
|---|---|---|---|
| Frontier/Spec.lean | agent-08 | problem contract: multigraph, walks, dist (ENNReal, top = unreachable), IsSSSP, certificates, DMSY26 frontier framework without uniqueness | NON-GATE (specification) |
| Frontier/CostModel.lean | agent-08 | deep-embedded RAM+CA machine for runtime gates; Cai-style nonuniform CA trees for F; gate Props | NON-GATE (model + statements only) |
| Frontier/Audit.lean | agent-09 | independent spec (Bellman-Ford = walk infimum), model-parametric gate Props, sanity/non-vacuity lemmas | NON-GATE (audit target) |
| Frontier/AuditBridge.lean | agent-09 | L4 bridge: independent adist = Spec.dist; RAM space <= cost | NON-GATE (audit) |
| Frontier/RAMLogic.lean | agent-08 | total-correctness program logic for the CostModel v2 RAM machine | NON-GATE (tooling) |
| Frontier/RAMWitness.lean | agent-08 | concrete RAM Bellman-Ford: bfProgram.Exact, RunsWithin 9(n+1)(m+1) (closes F-v2-2 non-vacuity) | NON-GATE (non-vacuity witness) |
| Frontier/LowerBound.lean | agent-06 | CATree Bellman-Ford witness: CAProg.Solves non-vacuous, cost <= 2nm | NON-GATE (no lower bound) |
| Frontier/SpecGen.lean, SpecBridge.lean | agent-08 | generic ordered-monoid walks/dist + frontier framework; lex (w,1) weights, dist_toLex_fst | NON-GATE (spec) |
| Frontier/CHD/Basic.lean | agent-08 | C-HD Layer-A shared interface: keys, labels, D store, relaxation, FP contract, cost-index conventions | NON-GATE (interface) |
| Frontier/CHD/Preprocess.lean | agent-10 | Simplification, DegRed, ChainRed, Reduction: dedup + chunking preserve distances (dist_eq, dist_rep) | NON-GATE (math lemma) |
| Frontier/GateCCalc.lean | agent-10 | real analysis: Tchd o(n log n) along mu; integer threshold F = floor(lg^(3/4)) dominates | NON-GATE (calculus) |
| Frontier/GateC.lean | agent-10 | FROZEN TARGET CHDTarget F / CHDTargetU (statement; CHDTarget F is proved in Frontier/CHD/Final.lean as chd_CHDTarget) + PROVED implications to CostModel.GateC | statement + glue |
| Frontier/AuditGateC.lean | agent-09 | CHDTarget F -> Audit.GateC (strong form, all m <= n max(1,F n)) | NON-GATE (audit glue) |
| Frontier/CHD/WalkOrder.lean | agent-08 | full walk order kappa (len, #edges, end vertex, reversed list); unique canonical min walks; exact distances read off | NON-GATE (Layer A order) |
| Frontier/CHD/BM.lean | agent-01 | relational BMSSP over walk labels; Lemma S2.1 at all levels; top-level IsSSSP; modular over FPContract/PullSpec | NON-GATE (Layer A, abstract over L2/L3 contracts) |
| Frontier/CHD/FindPivots.lean | agent-05 | FindPivots-HD cost-indexed search with L_X edge-only deletion (D1); findPivotsHD_sound; H1; HD1 cost | NON-GATE (Layer A) |
| Frontier/CHD/Select.lean | agent-04 | deterministic linear-time selection with comparison counter | NON-GATE (supporting lemma) |
| Frontier/CHD/DBlocks.lean | agent-04 | DS' lazy block structure D: pull/insert/merge/delete specs, PullSpec exact, lazy = literal merge (abstract part of O6) | NON-GATE (Layer A) |
| Frontier/CHD/Partition.lean | agent-03 | DMSY26 Lemma A.1 tree partition; MakePivots contract; ParentFirst records, contact-merge re-rooting | NON-GATE (Layer A) |
| Frontier/CostSkeleton.lean, CostCharging.lean, CostAggregate.lean, CostFinal.lean | agent-06 | parameter calculus (tF = max 16 tpar, kF), abstract charging over a call forest, aggregation, total_le_Tchd: Valid counters => cost <= 5100 c a Tchd | NON-GATE (conditional on Valid counters of the real execution) |
| Frontier/Density.lean | agent-03 | handled ranges, per-depth foreign-leaf bound, pivot mass, split-uniqueness (home charging) | NON-GATE (abstract combinatorics) |
| Frontier/RAMRep.lean | agent-08 | WSeg/VSeg array-segment representation predicates, frame lemmas, Unchanged write-set convention | NON-GATE (Layer B tooling) |
| Frontier/RAMWP.lean | agent-02 | weakest-precondition VCG for the RAM (wp, wp_sound, wp_mono, rfl simp set) | NON-GATE (Layer B tooling) |
| Frontier/Refine.lean | agent-08 | Refines (RAM fragment implements Layer-A step), seq/ite/loop/call rules, exact_of_refines | NON-GATE (Layer B tooling) |
| Frontier/CHD/BMCost.lean, BMTrace.lean | agent-01 | cost-indexed traced BMSSP (phases, windows, persistent FP state, call log); bmsspC_post, top exactness; LogInv; Log.forest = CallForest (O1), Log.ranges = Density.Ranges (O2); CallCounters facts | NON-GATE (Layer A cost bridge) |
| Frontier/CHD/MLabel.lean, LabTab.lean, LabRAM.lean | agent-02 | O(1) machine labels = kappa walk order (lt_iff/eq_iff, ghost history), label table rep, RAM Relax fragment refining FindPivots relaxL (relaxFP_spec) | NON-GATE (Layer B labels) |
| Frontier/Homes.lean, CHD/CostLog, CrBe, FPForeign, LoopCost, RecFPLog, Reselect, PartitionRAM{,2,3} | agent-03 | homes/colors charging, cost log, Cr/Be, foreign leaves, loop cost, PT at RAM level (PartitionRAM*) | NON-GATE (Layer A cost + Layer B PT) |
| Frontier/CHD/BMLazy.lean | agent-01 | BMSSP with lazy D (Layer A) | NON-GATE |
| Frontier/CHD/BSearch.lean | agent-02 | RAM binary search (DS' Insert) | NON-GATE (Layer B) |
| Frontier/CHD/DLazy.lean | agent-04 | lazy-split DS' model (L3-4) | NON-GATE (Layer A) |
| Frontier/CHD/FPBind.lean, FPDel.lean, MergeTotal.lean | agent-05 | FP binding, Valid.del_disj, merge total (O23) | NON-GATE (Layer A) |
| Frontier/CHD/FPIface.lean, LabI.lean, SlotList.lean | agent-09 | B-L2 FindPivots RAM interface, label interface, slot-list unlink | NON-GATE (Layer B) |
| Frontier/CHD/FPWQ.lean | agent-03 | card W at most k times card Q (F4) | NON-GATE (Layer A) |
| Frontier/CHD/IHeap.lean, MergeSort.lean | agent-06 | verified RAM indexed binary min-heap; verified RAM merge sort sortRange | NON-GATE (Layer B) |
| Frontier/CHD/RamBase.lean, RamBaseCase.lean, RamLevel.lean, RamSlot.lean, SpineBridge.lean, BaseGlue.lean | agent-08 | RAM spine: per-level regions, base case, slots, spine bridge | NON-GATE (Layer B) |
| Frontier/CHD/L6/*.lean (Prog, Util, CSort, Keep, DedupModel, Dedup, PassA, PassB, Layout, Sort, SortedRelKey, Final, Sizes, Run, Out, TchdCn, Body) | agent-10 | L6 preprocessing at RAM level (keep set, counting sort, dedup, out-degree chunking into CSR + chains + live lists, per-range merge sort) fully verified (l6_runs); reduced graph H with KReduction G H s, CSRAt/GraphAt, sorted/simple out-lists, size bounds; output mapping; Tchd_cn_le; CoreIn/CoreSpec contract; body_spec; chdTarget_of_core : CoreSpec e core Kc -> CHDTarget F | NON-GATE (reduction; used by Frontier.CHD.Final) |
| Frontier/CHD/Dispatch.lean | agent-10 | RAM dispatcher (lg n, thresholds) + chdTarget_of_body: CHDTarget F reduces to ONE BodySpec for the C-HD RAM body | NON-GATE (Layer B glue; used by Frontier.CHD.Final) |

| Frontier/CHD/L6/{CoreTop, Params, LevelTab, SpineIface, CoreSpecProof, MasterGlue} | agent-10 | parameter registers + per-level tables at RAM level; exactness bridge (coreOut_of_labAt, complete_of_topRun); SpineSpec/MasterSpec interface; coreTop; coreSpec_of_spine; chdTarget_of_spine; masterSpec_of_good; chdTarget_of_spine_good | NON-GATE (reduction; used by Frontier.CHD.Final) |
| Frontier/CHD/MasterCost.lean, L6/MasterSpecProof.lean | agent-06 | Layer-A master cost theorem master_cost_D (concrete DLazy run cost <= kmaster * Tchd), masterSpec_of_goodP | NON-GATE (Layer A, unconditional for GoodP) |

| Frontier/CHD/L6/{SpineTop, Route, TopGlue, Tnat, Prologue, ProBlow, ProMain, ProFinal, FinalRoute}, Frontier/CHD/{SynFrame, AllocList} | agent-10 | spine top level: SpineSpec = ProSpec + CallSpec; callSpec_of_ramSpine (agent-08's RamSpine.CallSpec at LF => top call); the prologue spinePro (sizes, Tnat, allocations, heap, hooks, Blow slot, top frame) proved to establish agent-08's CallIn at LF (proSpec_spinePro); chdTarget_of_spineParts; syntactic frame exec_frame; Tchd <= 6 Tnat <= 198 Tchd | NON-GATE (reduction) |

| Frontier/CHD/L6/{LevelRoute, FPHook, NamedWitness, TauCap, Assembly} | agent-10 | level induction (callSpec_of_levels); FP hook; named witness chdProg + space corollary; Static.tauCap/MCap from CoreIn.cap; FINAL ASSEMBLY chdTarget_of_step: concrete cost parameters chdP (GoodP 1 1 1000 proved), base case discharged from callSpec_zero, CHDTarget F from the D layer + level step + decidable facts | NON-GATE (composition; used by Frontier.CHD.Final) |

## Status and remaining steps  [updated 2026-09-20T23:15Z; frozen tree = integration build #33, 2548 jobs, 0 sorry]
1. PROVED on the frozen tree, standard axioms:
   - `Frontier.CHD.Final.chd_gateC : Frontier.GateC`;
   - `chd_CHDTarget : GateCTarget.CHDTarget GateCCalc.F`;
   - `chd_exact_within`, for the concrete program `Final.chdProgram`, which is axiom-free.
   The chain: CostModel.GateC ⇐ GateC.chdTarget_F_imp_gateC ⇐ Final.chd_CHDTarget ⇐ L6.FinalGen.chdProg_of_DLayer. That in turn rests on:
   - L6.Assembly: base case, GoodP, capacity;
   - L6.StepInst.hs_of_parts: the level step via agent-01's callSpec_succ with 09's hFP, 08's hLoop, 03's fin_spec_stmt;
   - DLayerF.DLf (04/02/05), DPro.dProSpecC (09), L6.SlackF;
   - the name facts in Final.lean, by decide +kernel.
2. NOT YET ACCEPTED. Pending: agent-07's fresh-copy rebuild and audit; agent-09's independent kernel replay; REVIEW_1 (agent-07) and REVIEW_2 (agent-02); THEOREM_MAP v2; then the /research/final package.
3. Outside the frozen closure (in the root from build #34): FinalExtras (chd_space, chd_auditGateC) and FinalSpace (chd_space_within).
4. Limitations: formal range m ≤ n·F(n); directed only; space Θ(Tnat); huge constants, e = 160. No other gate (A/B/E/F) is formalized.
