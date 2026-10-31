#!/usr/bin/env python3
r"""Inventory this manuscript's active environments, retaining original source lines.

This is deliberately a source-specific extractor, not a general TeX interpreter.
It handles percent comments, comment environments, iffalses, and balanced \junk
arguments used by STOC2027.tex. It does not expand arbitrary macros.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parent / "STOC2027.tex"
raw = SOURCE.read_text()

def blank(s):
    return "".join("\n" if c == "\n" else " " for c in s)

active = re.sub(r"(?<!\\)%[^\n]*", lambda m: blank(m[0]), raw)
active = re.sub(r"\\begin\{comment\}.*?\\end\{comment\}", lambda m: blank(m[0]), active, flags=re.S)
active = re.sub(r"\\iffalse\b.*?\\fi\b", lambda m: blank(m[0]), active, flags=re.S)
while match := re.search(r"\\junk\s*\{", active):
    end, depth = match.end(), 1
    while depth:
        if end >= len(active):
            raise ValueError("Unbalanced junk argument")
        if active[end] in "{}" and active[end - 1] != "\\":
            depth += 1 if active[end] == "{" else -1
        end += 1
    active = active[:match.start()] + blank(active[match.start():end]) + active[end:]

def line(pos):
    return raw.count("\n", 0, pos) + 1

def refs(s, kind):
    pattern = r"\\(?:ref|[Cc]ref|eqref)\{([^}]+)\}" if kind == "refs" else r"\\cite(?:\[[^]]*\])*\{([^}]+)\}"
    return sorted({key.strip() for m in re.finditer(pattern, s) for key in m[1].split(",")})

records = []
envs = "definition|theorem|lemma|proposition|corollary|claim|fact|observation|condition|assumption|restatable|remark"
pattern = re.compile(r"\\begin\{(" + envs + r")\}(.*?)\\end\{\1\}", re.S)
for m in pattern.finditer(active):
    text = "\n".join(x.rstrip() for x in m[0].splitlines() if x.strip())
    labels = re.findall(r"\\label\{([^}]+)\}", m[0])
    # Attach an immediately following proof; distant appendix proofs are inventoried below.
    tail = active[m.end():]
    proof = re.match(r"\s*\\begin\{proof\}(?:\[([^\n]*)\])?(.*?)\\end\{proof\}", tail, re.S)
    belongs = proof and (not proof[1] or set(refs(proof[1], "refs")) & set(labels))
    evidence = m[0] + (proof[0] if belongs else "")
    records.append(dict(kind=m[1], labels=labels, start_line=line(m.start()), end_line=line(m.end()),
                        statement=text, references=refs(evidence, "refs"), citations=refs(evidence, "cites")))

proofs = []
for m in re.finditer(r"\\begin\{proof\}(?:\[([^\n]*)\])?(.*?)\\end\{proof\}", active, re.S):
    proofs.append(dict(start_line=line(m.start()), end_line=line(m.end()), title=m[1],
                       references=refs(m[0], "refs"), citations=refs(m[0], "cites")))

algorithms = []
for m in re.finditer(r"\\begin\{algorithm\}.*?\\end\{algorithm\}", active, re.S):
    algorithms.append(dict(start_line=line(m.start()), end_line=line(m.end()),
                           labels=re.findall(r"\\label\{([^}]+)\}", m[0]), text=m[0]))

labels = [dict(label=m[1], line=line(m.start())) for m in re.finditer(r"\\label\{([^}]+)\}", active)]
data = dict(source="../STOC2027.tex", sha256=hashlib.sha256(raw.encode()).hexdigest(),
            statements=records, proofs=proofs, algorithms=algorithms, labels=labels)
(ROOT / "source_inventory.json").write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")
out = ["% Verbatim active mathematical statements from ../STOC2027.tex.",
       "% Source SHA-256: " + data["sha256"],
       "% Reference appendix only; not a standalone LaTeX document.",
       "% Commented, iffalsed, and junk-wrapped statements are excluded.", ""]
for record in records:
    out += [f"% STOC2027.tex:{record['start_line']}-{record['end_line']}", record["statement"], ""]
(ROOT / "SourceStatements.tex").write_text("\n".join(out))
print(f"{len(records)} active statements, {len(algorithms)} algorithms, {len(proofs)} proofs, {len(labels)} labels")
print("SHA-256: " + data["sha256"])
