#!/usr/bin/env python3
"""EasyCrypt-fidelity report for the SHA-3 port (refactor plan, phase 0).

Reads `notes/SHA3/Mapping.md` (EC declaration -> Lean declaration) and the Lean files it names,
and reports, per file, how close the EC lemmas' Lean counterparts are to their EC form:

* statements: how many EC lemmas are judgments (equiv/hoare/phoare/Pr/islossless), and how many
  of those are written in the surface syntax (`equiv[ ]`, `hoare[ ]`, `phoare[ ]`, `Pr[ ]`)
  rather than as raw `prhlProc`/`Procedure.Pr` terms;
* statement overhead: hypotheses EC does not have (`Module.ECModule`, lens parameters,
  footprint inequalities);
* proofs: how many judgment proofs are pure tactic scripts, versus proofs with term-mode rule
  applications, denotational reasoning, or footprint bookkeeping;
* auxiliary theorems: Lean theorems with no EC counterpart;
* exceptions: EC rows marked `exc`.

The classification is syntactic (regular expressions over the source), so the numbers are a
trend indicator, not a proof of anything.

Usage:
    scripts/ec_fidelity.py                 # per-file table and totals
    scripts/ec_fidelity.py --json          # machine-readable
    scripts/ec_fidelity.py --list raw      # list EC lemmas in a category, one per line
      categories: raw (judgment statement not in surface syntax), term, den, fp, overhead,
                  unmatched (mapped Lean name not found), aux (auxiliary theorems)
"""

import argparse
import json
import os
import re
import sys
from collections import Counter, defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MAPPING = os.path.join(ROOT, "notes", "SHA3", "Mapping.md")

LEMMA_KINDS = {"lemma", "local lemma", "equiv", "local equiv"}

JUDGMENT = re.compile(
    r"\b(prhlProc|prhlStmt|hoareProc|hoareStmt|phoareProc|phoareStmt|Procedure\.Pr|IsLossless)\b"
    r"|equiv\[|hoare\[|phoare\[|Pr\[|islossless")
RAW_JUDGMENT = re.compile(
    r"\b(prhlProc|prhlStmt|hoareProc|hoareStmt|phoareProc|phoareStmt|Procedure\.Pr)\b"
    r"|\.IsLossless\b")
OVERHEAD = re.compile(
    r"Module\.ECModule|ECModule\b|:\s*Lens\b|FinitelySupported|\.footprint\s*≤|FVP\.fvP\s+\S+\s*≤")
DENOTATIONAL = re.compile(
    r"ProgramDenotation|SubProbability|\.expected\b|\bprhl2\b|Stmt\.ewp|procedureDenotation"
    r"|Procedure\.ewp|lintegral|MeasureTheory")
TERM_RULE = re.compile(
    r"\b(refine|exact|apply)\s+\(?@?(prhl|hoare|phoare|Procedure\.Pr_|ProgramDenotation)\w*")
FOOTPRINT = re.compile(
    r"\b(fp_\w+|FVP\.\w+|Footprint\.\w+|inFootprint\w*|le_compl\w*|Lens\.disjoint_of_\w+)\b")

DECL_START = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma)\s+(\S+)")
DEF_START = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(def|abbrev)\s+(\S+)")
STATEMENT_REF = re.compile(r"([\w.']+\.statement)\b")
REUSE = re.compile(r"^:=\s*\(?([\w.']+)[\w.'\s()_]*\)?\s*$")


def parse_mapping(path):
    """[(lean_file, namespace, [rows])], a row = dict(line, kind, ec, lean, status)."""
    sections = []
    cur = None
    for line in open(path, encoding="utf-8"):
        m = re.match(r"^Lean: `([^`]+)`(?:, namespace `([^`]+)`)?", line)
        if m:
            cur = {"file": m.group(1), "ns": m.group(2) or "", "rows": []}
            sections.append(cur)
            continue
        if cur is None or not re.match(r"^\| \d+ \|", line):
            continue
        cols = [c.strip() for c in line.rstrip("\n").split("|")[1:-1]]
        if len(cols) < 6:
            continue
        names = re.findall(r"`([^`]+)`", cols[4])
        cur["rows"].append({
            "line": int(cols[0]), "kind": cols[1], "ec": cols[2].strip("`"),
            "lean": names[0] if names else "", "lean_col": cols[4], "status": cols[5]})
    return sections


def parse_lean(path):
    """({relative full name: (statement, proof)} for the theorems, theorem order,
    {name: text} for the definitions) of a Lean file."""
    lines = open(path, encoding="utf-8").read().split("\n")
    stack = []  # (kind, name)
    decls = {}
    order = []
    defs = {}
    i = 0
    while i < len(lines):
        line = lines[i]
        m_ns = re.match(r"^namespace\s+(\S+)", line)
        m_sec = re.match(r"^section(?:\s+(\S+))?\s*$", line)
        m_end = re.match(r"^end(?:\s+(\S+))?\s*$", line)
        if m_ns:
            stack.append(("ns", m_ns.group(1)))
        elif m_sec:
            stack.append(("sec", m_sec.group(1) or ""))
        elif m_end:
            if stack:
                stack.pop()
        md = DEF_START.match(line)
        if md:
            j = i + 1
            while j < len(lines) and (lines[j] == "" or lines[j][0] in " \t)"):
                j += 1
            name = md.group(2).replace("«", "").replace("»", "")
            defs[name] = "\n".join(lines[i:j])
            i = j
            continue
        m = DECL_START.match(line)
        if m:
            j = i + 1
            while j < len(lines) and (lines[j] == "" or lines[j][0] in " \t)"):
                j += 1
            text = "\n".join(lines[i:j])
            k = text.find(":= by")
            if k < 0:
                k = text.find(":=")
            stmt, proof = (text[:k], text[k:]) if k >= 0 else (text, "")
            ns = ".".join(n for kind, n in stack if kind == "ns")
            name = m.group(2).replace("«", "").replace("»", "")
            full = f"{ns}.{name}" if ns else name
            decls[full] = (stmt, proof)
            order.append(full)
            i = j
            continue
        i += 1
    return decls, order, defs


def lookup(decls, ns, name):
    if not name:
        return None
    cands = [f"{ns}.{name}" if ns else name, name]
    for c in cands:
        if c in decls:
            return c
    hits = [d for d in decls if d == name or d.endswith("." + name)]
    return hits[0] if len(hits) == 1 else (min(hits, key=len) if hits else None)


def analyse():
    report = []
    for sec in parse_mapping(MAPPING):
        path = os.path.join(ROOT, sec["file"])
        if not os.path.exists(path):
            continue
        decls, order, defs = parse_lean(path)
        used = set()
        c = Counter()
        items = defaultdict(list)
        for row in sec["rows"]:
            if row["kind"] not in LEMMA_KINDS:
                continue
            c["ec_lemmas"] += 1
            tag = f"{sec['file']}: {row['ec']} (EC line {row['line']})"
            if "omitted" in row["status"]:
                c["omitted"] += 1
                continue
            if "exc" in row["status"]:
                c["exc"] += 1
            full = lookup(decls, sec["ns"], row["lean"])
            if full is None:
                c["unmatched"] += 1
                items["unmatched"].append(f"{tag} -> {row['lean']}")
                continue
            used.add(full)
            stmt, proof = decls[full]
            for ref in STATEMENT_REF.findall(stmt):
                hits = [t for n, t in defs.items()
                        if n == ref or n.endswith("." + ref) or ref.endswith("." + n)]
                if hits:
                    stmt = stmt + "\n" + hits[0]
            if OVERHEAD.search(stmt):
                c["overhead"] += 1
                items["overhead"].append(f"{tag} -> {full}")
            if not JUDGMENT.search(stmt):
                c["pure"] += 1
                continue
            c["judgment"] += 1
            if RAW_JUDGMENT.search(stmt):
                items["raw"].append(f"{tag} -> {full}")
            else:
                c["surface"] += 1
            flags = []
            mr = REUSE.match(proof.strip())
            if mr and lookup(decls, "", mr.group(1)) is not None:
                c["reuse"] += 1
                c["clean"] += 1
                continue
            if TERM_RULE.search(proof) or not proof.lstrip(":= ").startswith("by"):
                flags.append("term")
            if DENOTATIONAL.search(proof):
                flags.append("den")
            if FOOTPRINT.search(proof):
                flags.append("fp")
            for f in flags:
                c[f] += 1
                items[f].append(f"{tag} -> {full}")
            if not flags:
                c["clean"] += 1
        for d in order:
            if d not in used:
                c["aux"] += 1
                items["aux"].append(f"{sec['file']}: {d}")
        report.append({"file": sec["file"], "counts": dict(c), "items": dict(items)})
    return report


COLUMNS = [("ec_lemmas", "EC"), ("judgment", "judg"), ("surface", "surf"), ("clean", "clean"),
           ("reuse", "reuse"),
           ("term", "term"), ("den", "den"), ("fp", "fp"), ("overhead", "ovh"), ("exc", "exc"),
           ("unmatched", "unm"), ("aux", "aux")]


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--list", metavar="CATEGORY")
    args = ap.parse_args()
    report = analyse()
    if args.json:
        json.dump(report, sys.stdout, indent=1)
        return
    if args.list:
        for r in report:
            for it in r["items"].get(args.list, []):
                print(it)
        return
    w = max(len(os.path.basename(r["file"])) for r in report)
    print(f"{'file':{w}s} " + " ".join(f"{h:>5s}" for _, h in COLUMNS))
    tot = Counter()
    for r in report:
        c = r["counts"]
        tot.update(c)
        print(f"{os.path.basename(r['file']):{w}s} " +
              " ".join(f"{c.get(k, 0):5d}" for k, _ in COLUMNS))
    print(f"{'TOTAL':{w}s} " + " ".join(f"{tot.get(k, 0):5d}" for k, _ in COLUMNS))
    print()
    print("EC: EC lemmas/equivs; judg: of those, judgment statements; surf: judgments in surface "
          "syntax;\nclean: judgment proofs with no term/den/fp flag; reuse: of those, a reference "
          "to another\nsection's identical proof (EC repeats it); term: term-mode rule "
          "application;\nden: denotational reasoning; fp: footprint bookkeeping; ovh: statement "
          "has hypotheses EC lacks;\nexc: EC row marked exc; unm: mapped Lean name not found; "
          "aux: Lean theorems with no EC row.")


if __name__ == "__main__":
    main()
