"""Structural checks of the manuscript sources and of the last LaTeX build.

Run `paper/build.sh` first. The script checks that every reference and citation resolves,
that labels are unique, that the build log has no overfull or underfull boxes and no LaTeX
warnings, that the author block names only Samuel Mausberg, that the AI disclosure appears
once, and that the sources contain no em dashes. It is a build check, not a proof check.
"""

from __future__ import annotations

import json
import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DISCLOSURE = r"\section*{AI disclosure}"


def main() -> int:
    sources = sorted((ROOT / "paper").glob("*.tex"))
    text = "\n".join(p.read_text(encoding="utf-8") for p in sources)
    labels = re.findall(r"\\label\{([^}]+)\}", text)
    refs = re.findall(r"\\(?:eqref|ref|pageref)\{([^}]+)\}", text)
    keys = re.findall(r"\\bibitem(?:\[[^]]*\])?\{([^}]+)\}", text)
    cites = re.findall(r"\\cite(?:\[[^]]*\])?\{([^}]+)\}", text)
    cited = {k.strip() for item in cites for k in item.split(",")}
    authors = re.findall(r"\\author\{([^}]+)\}", text)
    log_path = ROOT / "paper/build.log"
    if not log_path.exists():
        print("missing paper/build.log; run paper/build.sh first", file=sys.stderr)
        return 1
    log = log_path.read_text(encoding="utf-8", errors="replace")
    result = {
        "tex_files": len(sources),
        "labels": len(set(labels)),
        "unresolved_references": sorted(set(refs) - set(labels)),
        "unresolved_citations": sorted(cited - set(keys)),
        "uncited_bibliography_keys": sorted(set(keys) - cited),
        "duplicate_labels": [k for k, c in Counter(labels).items() if c > 1],
        "overfull_boxes": len(re.findall(r"Overfull \\hbox", log)),
        "underfull_boxes": len(re.findall(r"Underfull \\hbox", log)),
        "latex_warnings": len(re.findall(r"(?:LaTeX|Package [^\n]+) Warning:", log)),
        "authors": authors,
        "ai_disclosure_sections": text.count(DISCLOSURE),
        "em_dashes": text.count("\u2014") + text.count("---"),
    }
    failures = [
        key
        for key in (
            "unresolved_references",
            "unresolved_citations",
            "uncited_bibliography_keys",
            "duplicate_labels",
            "overfull_boxes",
            "underfull_boxes",
            "latex_warnings",
            "em_dashes",
        )
        if result[key]
    ]
    if authors != ["Samuel Mausberg"]:
        failures.append("authors")
    if result["ai_disclosure_sections"] != 1:
        failures.append("ai_disclosure_sections")
    result["status"] = "failed" if failures else "passed"
    result["failures"] = failures
    print(json.dumps(result, indent=2))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
