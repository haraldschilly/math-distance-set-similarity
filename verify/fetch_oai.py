"""Copy the external Lean sources needed to discharge the paper's hypotheses into verify/.

Usage: python3 verify/fetch_oai.py /path/to/openai-math-checkout /path/to/math-mattila-sjolin-checkout

* verify/ms-src: the Mattila–Sjölin formalization (github.com/haraldschilly/math-mattila-sjolin),
  all of `MattilaSjolin.lean` and `MattilaSjolin/`.
* verify/oai-src: the transitive OAI import closure of OpenAI's two solution modules (Falconer,
  dyadic) together with the OAI modules imported by the Mattila–Sjölin sources. The closure depends
  on Mathlib only.

Both checkouts must be at the pinned commits.
"""
import os, re, shutil, subprocess, sys

OAI_PINNED_COMMIT = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
MS_PINNED_COMMIT = "435cd62612b2259bca142d93d728d1e402a3ad16"
SOLUTION_MODULES = [
    "OAI.MeasureTheory.DyadicAvoidance.Main",                      # dyadic_affine_avoidance
    "OAI.MeasureTheory.Falconer.Campaign123PlanarFurstenbergProof",  # falconer_distance_conjecture
]
IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+(?:all\s+)?([\w.«»]+)", re.M)

if len(sys.argv) != 3:
    sys.exit(__doc__)
math, ms = (os.path.abspath(a) for a in sys.argv[1:3])
for repo, pinned, name in [(math, OAI_PINNED_COMMIT, "openai/math"),
                           (ms, MS_PINNED_COMMIT, "math-mattila-sjolin")]:
    head = subprocess.run(["git", "-C", repo, "rev-parse", "HEAD"],
                          capture_output=True, text=True).stdout.strip()
    if head != pinned:
        sys.exit(f"{name} checkout is at {head or '?'}, expected {pinned}")
here = os.path.dirname(os.path.abspath(__file__))

# Mattila–Sjölin sources
ms_dst = os.path.join(here, "ms-src")
shutil.rmtree(ms_dst, ignore_errors=True)
ms_files = ["MattilaSjolin.lean"] + sorted(
    os.path.relpath(os.path.join(d, f), ms)
    for d, _, fs in os.walk(os.path.join(ms, "MattilaSjolin")) for f in fs if f.endswith(".lean"))
ms_oai = set()
for rel in ms_files:
    os.makedirs(os.path.dirname(os.path.join(ms_dst, rel)), exist_ok=True)
    shutil.copy2(os.path.join(ms, rel), os.path.join(ms_dst, rel))
    for imp in IMPORT_RE.findall(open(os.path.join(ms, rel), encoding="utf-8").read()):
        if imp.startswith("OAI"):
            ms_oai.add(imp)
shutil.copy2(os.path.join(ms, "LICENSE"), os.path.join(ms_dst, "LICENSE"))

# OAI closure
src = os.path.join(math, "lean")
dst = os.path.join(here, "oai-src")

def path(root, mod):
    return os.path.join(root, *mod.split(".")) + ".lean"

seen, stack, external = set(), SOLUTION_MODULES + sorted(ms_oai), set()
while stack:
    mod = stack.pop()
    if mod in seen:
        continue
    seen.add(mod)
    text = open(path(src, mod), encoding="utf-8").read()
    for imp in IMPORT_RE.findall(text):
        (stack.append if imp.startswith("OAI") else external.add)(imp)
bad = {m.split(".")[0] for m in external} - {"Mathlib", "Lean", "Init", "Std"}
if bad:
    sys.exit(f"unexpected external dependencies: {sorted(bad)}")

shutil.rmtree(dst, ignore_errors=True)
for mod in sorted(seen):
    os.makedirs(os.path.dirname(path(dst, mod)), exist_ok=True)
    shutil.copy2(path(src, mod), path(dst, mod))
shutil.copy2(os.path.join(src, "LICENSE"), os.path.join(dst, "LICENSE"))
print(f"copied {len(ms_files)} Mattila–Sjölin files to {ms_dst}")
print(f"copied {len(seen)} OAI modules to {dst}")
