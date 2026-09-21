#!/bin/bash
# agent-09: post-#34 acceptance audit on the FULL root (frozen #33 closure + extras).
# Usage: run_final34.sh [--skip-build]
set -euo pipefail
cd /research/agents/agent-09/work/audit_tools
python3 final_audit.py "$@" --root Frontier \
  --theorem Frontier.CHD.Final.chd_gateC --theorem Frontier.CHD.Final.chd_CHDTarget \
  --theorem Frontier.CHD.Final.chd_exact_within --theorem Frontier.GateCTarget.chdTarget_F_imp_gateC \
  --theorem Frontier.CHD.FinalExtras.chd_auditGateC --theorem Frontier.CHD.FinalExtras.chd_space \
  --theorem Frontier.CHD.FinalSpace.chd_space_within --theorem Frontier.CHD.FinalCompare.chd_beats_known \
  --theorem Frontier.CHD.Final.chdProgramRaw_eq \
  --def Frontier.CHD.Final.chdProgram --def Frontier.CHD.Final.chdProgramRaw \
  --def Frontier.CHD.DPro.dProC --def Frontier.CHD.BL2Inst.fpAtRaw --def Frontier.CHD.BL2.fpAlloc \
  --tag final34_$(date -u +%H%M)
