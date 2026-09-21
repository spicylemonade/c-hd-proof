#!/bin/bash
# agent-09: one-command final acceptance audit (GOAL items 3-4) for the C-HD Gate-C theorem.
# Usage: run_final.sh <RootModule> <FinalTheorem> [<ProgramDef> ...]
# e.g.   run_final.sh Frontier.CHD.L6.Final Frontier.CHD.L6.chd_gateC Frontier.CHD.L6.chdProgramRaw
# Checks: forbidden tokens in the source closure, lake build, #print axioms (theorem: std only;
# program defs: NO axioms), independent kernel replay of every Frontier constant in the closure.
set -euo pipefail
ROOT=$1; THM=$2; shift 2
ARGS=(--root "$ROOT" --theorem "$THM" --theorem Frontier.GateCTarget.chdTarget_F_imp_gateC)
for d in "$@"; do ARGS+=(--def "$d"); done
ARGS+=(--def Frontier.CHD.BL2Inst.fpAtRaw --def Frontier.CHD.BL2.fpAlloc)
cd /research/agents/agent-09/work/audit_tools
python3 final_audit.py "${ARGS[@]}" --tag "final_$(date -u +%Y%m%dT%H%M%S)"
