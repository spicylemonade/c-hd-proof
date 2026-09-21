#!/usr/bin/env python3
"""agent-07 independent reproduction of the /research/lean Frontier project (reviewer #1). Theory-audit tool only.

Copies ONLY source files (lakefile, toolchain, manifest, Frontier.lean, Frontier/**/*.lean) into a fresh directory, links the
pinned dependency packages read-only (no .lake/build copied, so every Frontier module is re-elaborated), builds with the sandbox
runner, scans the import closure for forbidden tokens (comments/strings stripped), and probes `#print axioms` for given theorems.
Usage: python3 my_repro.py TAG [Module.Name:theorem ...]
Writes repro/TAG/{build.log, scan.txt, axioms.txt, summary.json}. Never writes into /research/lean.
"""
import hashlib, json, os, re, shutil, subprocess, sys, time
from pathlib import Path

SRC = Path('/research/lean')
OUT = Path('/research/agents/agent-07/work/repro')
# HARD: unsound or oracle-like features (must be absent). INFO: sound but worth listing (kernel-checked decide, opaque defs).
FORBIDDEN = [r'\bsorry\b', r'\badmit\b', r'\bnative_decide\b', r'^\s*axiom\b', r'\bunsafe\b', r'\bimplemented_by\b',
             r'@\[extern', r'\bofReduceBool\b', r'\bofReduceNat\b', r'\bcsimp\b', r'\bsorryAx\b',
             r'#eval\b', r'\brun_cmd\b', r'\bLean\.Elab\b', r'\bset_option\s+debug\.skipKernelTC', r'\bpartial\s+def\b']
INFO = [r'\bdecide\s*:=\s*true', r'\bdecide\s*\+kernel', r'\bkernel\s*:=\s*true', r'\bopaque\b']

def _blank(m):                                                 # keep newlines so reported line numbers stay correct
    return re.sub(r'[^\n]', ' ', m.group(0))

def strip(text):
    text = re.sub(r'/-.*?-/', _blank, text, flags=re.S)          # block comments (incl. doc comments)
    text = re.sub(r'--[^\n]*', _blank, text)                     # line comments
    text = re.sub(r'"(?:\\.|[^"\\])*"', _blank, text)            # string literals
    return text

def main():
    tag = sys.argv[1]
    probes = sys.argv[2:]
    d = OUT / tag; proj = d / 'proj'
    if d.exists(): shutil.rmtree(d)
    proj.mkdir(parents=True)
    for f in ['lakefile.toml', 'lean-toolchain', 'lake-manifest.json', 'Frontier.lean']:
        shutil.copy2(SRC / f, proj / f)
    files = sorted((SRC / 'Frontier').rglob('*.lean'))
    hashes = {}
    for f in files:
        rel = f.relative_to(SRC); t = proj / rel; t.parent.mkdir(parents=True, exist_ok=True); shutil.copy2(f, t)
        hashes[str(rel)] = hashlib.sha256(f.read_bytes()).hexdigest()
    (proj / '.lake').mkdir()
    os.symlink(SRC / '.lake' / 'packages', proj / '.lake' / 'packages')
    t0 = time.time()
    r = subprocess.run(['python3', '/opt/research/lean_run.py', 'lake', 'build', '-d', str(proj)], capture_output=True, text=True)
    (d / 'build.log').write_text(r.stdout + '\n' + r.stderr)
    build_ok = r.returncode == 0
    # forbidden-token scan over all Frontier sources (conservative: whole tree, not only the import closure)
    hits, infos = [], []
    for f in files:
        txt = strip(f.read_text())
        for pats, out in ((FORBIDDEN, hits), (INFO, infos)):
            for pat in pats:
                for mm in re.finditer(pat, txt, flags=re.M):
                    line = txt[:mm.start()].count('\n') + 1
                    out.append(f'{f.relative_to(SRC)}:{line}: {pat}')
    (d / 'scan.txt').write_text('HARD:\n' + '\n'.join(hits) + '\nINFO:\n' + '\n'.join(infos) + '\n')
    ax = []
    for p in probes:
        mod, thm = p.split(':', 1)
        probe = proj / f'Probe_{abs(hash(p)) % 10**8}.lean'
        probe.write_text(f'import {mod}\n#print axioms {thm}\n')
        rr = subprocess.run(['python3', '/opt/research/lean_run.py', 'lake', 'env', '-d', str(proj), 'lean', str(probe)],
                            capture_output=True, text=True)
        ax.append(f'== {p}\n{rr.stdout.strip()}\n{rr.stderr.strip()}')
    (d / 'axioms.txt').write_text('\n'.join(ax) + '\n')
    summary = dict(tag=tag, build_ok=build_ok, seconds=round(time.time() - t0, 1), files=len(files), forbidden_hits=len(hits), info_hits=len(infos),
                   probes=probes, hashes=hashes)
    (d / 'summary.json').write_text(json.dumps(summary, indent=1))
    print(json.dumps({k: v for k, v in summary.items() if k != 'hashes'}, indent=1))
    print('\n'.join(hits[:30]))
    print('\n'.join(ax))

if __name__ == '__main__':
    main()
