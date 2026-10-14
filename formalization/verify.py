#!/usr/bin/env python3
"""Build the Lean development and audit its axioms.

Run from this directory after `lake exe cache get`. The script
1. scans the sources for forbidden tokens,
2. checks that the root file `LearningGuided.lean` imports every module of the library,
3. runs `lake build` (warnings are errors and Mathlib's standard linters are on, see
   lakefile.toml),
4. runs `AxiomAudit.lean`, which checks that every declaration defined in the library depends
   only on `propext`, `Classical.choice` and `Quot.sound`, and lists every theorem whose
   docstring cites a paper statement by TeX label,
5. checks that every cited label exists in the manuscript sources in `../paper`.
It writes the results to lean-verification.json.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
LIB = "LearningGuided"
FORBIDDEN = [
    r"\bsorry\b",
    r"\badmit\b",
    r"\baxiom\b",
    r"\bnative_decide\b",
    r"\bimplemented_by\b",
    r"\bunsafe\b",
    r"@\[extern",
    r"maxHeartbeats\s+0\b",
]


def strip_comments(text: str) -> str:
    """Remove Lean comments and keep every newline, so line numbers are preserved.

    Block comments `/- ... -/` (including `/--` and `/-!`) nest. Line comments run from `--`
    to the end of the line. String literals are copied unchanged.
    """
    out: list[str] = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth > 0:
            if text.startswith("/-", i):
                depth, i = depth + 1, i + 2
            elif text.startswith("-/", i):
                depth, i = depth - 1, i + 2
            else:
                if text[i] == "\n":
                    out.append("\n")
                i += 1
        elif text.startswith("/-", i):
            depth, i = 1, i + 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i : j + 1])
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def sources() -> list[Path]:
    return sorted((ROOT / LIB).rglob("*.lean")) + [ROOT / f"{LIB}.lean"]


def scan() -> list[str]:
    hits = []
    for path in sources() + [ROOT / "AxiomAudit.lean"]:
        text = path.read_text(encoding="utf-8")
        raw = text.splitlines()
        code = strip_comments(text).splitlines()
        for lineno, line in enumerate(code, 1):
            for pattern in FORBIDDEN:
                if re.search(pattern, line):
                    hits.append(f"{path.relative_to(ROOT)}:{lineno}: {raw[lineno - 1].strip()}")
    return hits


def missing_imports() -> list[str]:
    root = (ROOT / f"{LIB}.lean").read_text(encoding="utf-8")
    imported = set(re.findall(r"^import (\S+)$", root, re.M))
    modules = {
        ".".join(p.relative_to(ROOT).with_suffix("").parts) for p in (ROOT / LIB).rglob("*.lean")
    }
    return sorted(modules - imported)


def tex_labels() -> set[str]:
    text = "\n".join(p.read_text(encoding="utf-8") for p in (ROOT.parent / "paper").glob("*.tex"))
    return set(re.findall(r"\\label\{([^}]+)\}", text))


def run(cmd: list[str]) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)


def audit(output: str) -> tuple[dict[str, list[str]], int | None, int | None]:
    labelled: dict[str, list[str]] = {}
    for name, labels in re.findall(r"^AUDIT (\S+) (\S+)$", output, re.M):
        labelled[name] = labels.split(",")
    m = re.search(r"GLOBAL (\d+) declarations checked, (\d+) with nonstandard axioms", output)
    return labelled, (int(m.group(1)) if m else None), (int(m.group(2)) if m else None)


def main() -> int:
    hits = scan()
    unimported = missing_imports()
    build = run(["lake", "build"])
    audit_run = run(["lake", "env", "lean", "AxiomAudit.lean"])
    labelled, checked, nonstandard = audit(audit_run.stdout)
    known = tex_labels()
    unknown = sorted({lab for labs in labelled.values() for lab in labs} - known)
    cited = sorted({lab for labs in labelled.values() for lab in labs} & known)
    ok = (
        not hits
        and not unimported
        and build.returncode == 0
        and audit_run.returncode == 0
        and checked is not None
        and checked > 0
        and nonstandard == 0
        and labelled
        and not unknown
    )
    report = {
        "status": "passed" if ok else "failed",
        "forbidden_tokens": hits,
        "modules_missing_from_root": unimported,
        "build_returncode": build.returncode,
        "declarations_checked": checked,
        "declarations_with_nonstandard_axioms": nonstandard,
        "theorems_citing_paper_labels": len(labelled),
        "distinct_paper_labels_cited": len(cited),
        "unknown_labels": unknown,
        "labelled_theorems": labelled,
    }
    (ROOT / "lean-verification.json").write_text(json.dumps(report, indent=2) + "\n")
    summary_keys = (
        "status",
        "declarations_checked",
        "declarations_with_nonstandard_axioms",
        "theorems_citing_paper_labels",
        "distinct_paper_labels_cited",
        "unknown_labels",
        "modules_missing_from_root",
        "forbidden_tokens",
    )
    print(json.dumps({k: report[k] for k in summary_keys}, indent=2))
    if build.returncode != 0:
        print(build.stdout[-4000:], file=sys.stderr)
    if audit_run.returncode != 0:
        print(audit_run.stdout[-4000:], audit_run.stderr[-4000:], file=sys.stderr)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
