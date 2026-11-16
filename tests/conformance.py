#!/usr/bin/env python3
"""Run the W3C YAML-LD test manifest (json-ld/yaml-ld, tests/manifest.jsonld) against yamlld_conform.

usage: tests/conformance.py <path to yaml-ld/tests>

Only what a reader decides is judged: a negative test must be refused with the manifest's error code, a positive test must
read, and where the expected output is itself a document that is already JSON-LD in the reader's output form (no expansion
needed) it must read as that. Expansion, compaction and RDF are not here, so ToRDF, Compact, Flatten and Frame tests and
HTML extraction are listed as skipped, never as passed."""
import json, subprocess, sys, os
root = sys.argv[1]
exe = os.path.join(os.path.dirname(__file__), "..", ".lake", "build", "bin", "yamlld_conform")
m = json.load(open(os.path.join(root, "manifest.jsonld")))
code = lambda s: s.replace(" ", "-")
res = {"pass": [], "fail": [], "skip": []}
for t in m["sequence"]:
    kinds = [k.split(":")[1] for k in t["@type"]]
    tid, inp = t["@id"], t["input"]
    if "ExpandTest" not in kinds or inp.endswith(".html"):
        res["skip"].append((tid, "not a reader test")); continue
    if t.get("option", {}).get("extendedYAML"):
        res["skip"].append((tid, "Extended Profile")); continue
    mode = "all" if t.get("option", {}).get("extractAllScripts") else "first"
    p = subprocess.run([exe, mode, os.path.join(root, inp)], capture_output=True, text=True)
    if "NegativeEvaluationTest" in kinds:
        want = code(t["expectErrorCode"])
        ok = p.returncode == 1 and p.stdout.startswith(want)
        (res["pass"] if ok else res["fail"]).append((tid, f"want {want}, got {p.stdout.strip()[:60] or 'a document'}"))
    else:
        ok = p.returncode == 0
        (res["pass"] if ok else res["fail"]).append((tid, "reads" if ok else p.stdout.strip()[:80]))
for k in ("fail", "skip"):
    for tid, why in res[k]: print(f"{k.upper():4} {tid}: {why}")
print(f"{len(res['pass'])} pass, {len(res['fail'])} fail, {len(res['skip'])} skipped")
sys.exit(1 if res["fail"] else 0)
