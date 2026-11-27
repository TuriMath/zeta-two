#!/usr/bin/env python3
"""A theorem repo counts as verified only if its gate is the template's gate, byte for byte.

Run from a checkout of theorem-template (its scripts are the reference):

    python3 scripts/template_match.py TuriMath/irrational-sqrt-two TuriMath/sum-of-first-n ...
    python3 scripts/template_match.py --all        # every non-template, non-index repo in the org

Compares the default branch's gate files with this checkout by sha256. Exit 1 if any differ or are missing.
Needs the `gh` CLI. (A repo cannot check itself: a doctored gate would also doctor the check.)
"""
import base64
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FILES = ["scripts/gate.py", "scripts/gate.sh", ".github/workflows/gate.yml", "lean-toolchain", "lakefile.lean"]
NOT_THEOREM_REPOS = {"theorem-template", "theorems", "mathlab", "turimath.github.io", ".github"}


def gh(*args) -> str | None:
    r = subprocess.run(["gh", *args], capture_output=True, text=True, timeout=60)
    return r.stdout if r.returncode == 0 else None


def remote_sha(repo: str, path: str) -> str | None:
    out = gh("api", f"repos/{repo}/contents/{path}")
    if out is None:
        return None
    return hashlib.sha256(base64.b64decode(json.loads(out)["content"])).hexdigest()


def check(repo: str) -> bool:
    bad = []
    for f in FILES:
        want = hashlib.sha256((ROOT / f).read_bytes()).hexdigest()
        got = remote_sha(repo, f)
        if got != want:
            bad.append(f"{f} ({'missing' if got is None else 'differs'})")
    print(f"{'✓' if not bad else '✗'} {repo}" + (": " + ", ".join(bad) if bad else ""))
    return not bad


def main() -> int:
    args = sys.argv[1:]
    if args == ["--all"]:
        out = gh("repo", "list", "TuriMath", "--no-archived", "--limit", "200", "--json", "name")
        args = [f"TuriMath/{r['name']}" for r in json.loads(out or "[]") if r["name"] not in NOT_THEOREM_REPOS]
    if not args:
        print(__doc__)
        return 2
    results = [check(r) for r in args]
    return 0 if all(results) else 1


if __name__ == "__main__":
    sys.exit(main())
