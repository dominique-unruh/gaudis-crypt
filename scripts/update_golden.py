#!/usr/bin/env python3
"""Fill in / refresh the expected text of `#guard_msgs` golden tests.

    scripts/update_golden.py GaudisCrypt/Logic/ECAutoTest.lean [...]

Runs `lake env lean --json FILE`; for every `#guard_msgs in` whose docstring does not match what
Lean printed, the docstring is replaced by the printed text (Lean's mismatch message carries it).
Review the diff before committing: a changed expectation is a changed tactic behaviour.
"""
import json, subprocess, sys, re

HEADER = "Docstring on `#guard_msgs` does not match generated message:"

def run(path):
    # (plain text, not a diff against the old docstring)
    out = subprocess.run(["lake", "env", "lean", "-D", "guard_msgs.diff=false", "--json", path],
                         capture_output=True, text=True).stdout
    msgs = []
    for line in out.splitlines():
        try:
            msgs.append(json.loads(line))
        except json.JSONDecodeError:
            pass
    return msgs

def update(path):
    msgs = run(path)
    fixes = {}  # 1-based line of `#guard_msgs` -> expected text
    for m in msgs:
        data = m.get("data", "")
        if HEADER in data:
            text = data.split(HEADER, 1)[1].strip("\n")
            fixes[m["pos"]["line"]] = text
    if not fixes:
        others = [m for m in msgs if m.get("severity") == "error"]
        print(f"{path}: up to date" + (f" ({len(others)} other errors)" if others else ""))
        return
    lines = open(path).read().split("\n")
    for ln in sorted(fixes, reverse=True):
        i = ln - 1                      # index of the `#guard_msgs` line
        assert lines[i].lstrip().startswith("#guard_msgs"), (path, ln, lines[i])
        # drop an existing docstring right above
        j = i
        if j > 0 and lines[j - 1].rstrip().endswith("-/"):
            k = j - 1
            while k >= 0 and not lines[k].lstrip().startswith("/--"):
                k -= 1
            assert k >= 0
            del lines[k:j]
            i = k
        doc = ["/--"] + fixes[ln].split("\n") + ["-/"]
        lines[i:i] = doc
    open(path, "w").write("\n".join(lines))
    print(f"{path}: {len(fixes)} expectation(s) updated")

if __name__ == "__main__":
    for p in sys.argv[1:]:
        update(p)
