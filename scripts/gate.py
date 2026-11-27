#!/usr/bin/env python3
"""The TuriMath gate. A PR is green only if every check here passes (docs/pipeline.md in TuriMath/mathlab).

  python3 scripts/gate.py            run every check (CI and locally); exit 1 on any failure
  python3 scripts/gate.py --selftest prove the gate catches a planted sorry and a planted extra axiom (Gate 0)

Checks:
  1. every .lean file under Theorems/ is imported by Theorems.lean (else `lake build` silently skips it)
  2. `lake build` succeeds
  3. no `sorry` / `admit` / `axiom` declarations in Theorems/
  4. `#print axioms` for every `main` and `equiv`: only propext, Classical.choice, Quot.sound
  5. every Proof.lean proves exactly A.Statement
  6. locked.txt: every hash matches, and lines are only ever added (compared with $GATE_BASE, default origin/main)
  7. data/tasks/*.json has the required fields
Plus a red-flag report (not a failure): statements closed outright by decide/simp/norm_num/trivial.
"""
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
THMS = ROOT / "Theorems"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
REQUIRED_FIELDS = {"slug", "issue", "tier", "source", "statement_provenance", "verdict", "attempts",
                   "mathlib_lemmas", "toolchain", "mathlib_rev"}
# Check 3 reads the RAW file text: no comment or string stripping, so no lexer to fool. Every trick for hiding a
# sorry/axiom or silencing Lean's warnings has to write one of these words somewhere in the file, even inside a comment
# or string; so theorem files may not contain them at all (reword the comment). `\b` keeps `axioms`, `axiomatic`,
# `my_axiom` and `macro_rules` out of the plain words. The Lean-side checks (3b, the build warning check) still run.
FORBIDDEN_WORDS = ["sorry", "admit", "axiom", "native_decide", "guard_msgs", "implemented_by", "extern", "elab",
                   "macro", "syntax", "run_cmd", "run_tac", "run_elab", "macro_rules", "elab_rules"]
FORBIDDEN = re.compile(r"\b(?:" + "|".join(FORBIDDEN_WORDS) + r")\b|\b(?:warn|debug)\.|#eval")

failures: list[str] = []


def fail(msg: str):
    failures.append(msg)
    print(f"  ✗ {msg}")


def ok(msg: str):
    print(f"  ✓ {msg}")


def run(cmd, **kw) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, **kw)


def module(path: Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def slugs() -> list[str]:
    return sorted(d.name for d in THMS.iterdir() if d.is_dir() and (d / "A.lean").exists()) if THMS.exists() else []


# ---------- checks ----------
INDEX_LINE = re.compile(r"^(?:import\s+Theorems(?:\.\w+)+\s*|--.*|\s*)$")


def index_violations(text: str) -> list[str]:
    """Lines of Theorems.lean that are not `import Theorems.…`, blank, or a `--` comment. It is an index file only."""
    return [l for l in text.splitlines() if not INDEX_LINE.match(l)]


def check_imports():
    print("1. Every file is imported by Theorems.lean, and Theorems.lean is only an index")
    root = ROOT / "Theorems.lean"
    for l in index_violations(root.read_text()) if root.exists() else []:
        fail(f"Theorems.lean may only contain `import Theorems.…` lines, blanks and `--` comments; found: {l.strip()}")
    imported = set(re.findall(r"^import\s+(\S+)", root.read_text(), re.M)) if root.exists() else set()
    missing = [module(p) for p in sorted(THMS.rglob("*.lean"))] if THMS.exists() else []
    missing = [m for m in missing if m not in imported]
    for m in missing:
        fail(f"{m} is not imported by Theorems.lean, so it would never be built")
    if not missing:
        ok(f"{len(imported)} modules imported")


def check_build():
    print("2. lake build")
    r = run(["lake", "build"])
    if r.returncode != 0:
        fail("lake build failed")
        print((r.stdout + r.stderr)[-4000:])
    elif SORRY_WARNING.search(r.stdout + r.stderr):
        fail("lake build reports `declaration uses sorry` (Lean's own warning; covers `example`, which check 3b cannot see)")
        print("\n".join(l for l in (r.stdout + r.stderr).splitlines() if SORRY_WARNING.search(l)))
    else:
        ok("lake build succeeded, no sorry warnings")


def check_forbidden():
    print("3. Raw-text scan: no sorry / axiom / native_decide / warning-silencing / meta-programming words")
    bad = 0
    files = (sorted(THMS.rglob("*.lean")) if THMS.exists() else []) + [ROOT / "Theorems.lean"]  # root file is built too
    for p in files:
        if not p.exists():
            continue
        for m in FORBIDDEN.finditer(p.read_text()):
            fail(f"{p.relative_to(ROOT)}: `{m.group(0).strip()}`")
            bad += 1
    if not bad:
        ok("none found")


def lean_snippet(body: str, imports: str = "import Theorems") -> subprocess.CompletedProcess:
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=ROOT / ".lake", delete=False) as f:
        f.write(f"{imports}\n\n{body}\n")
        name = f.name
    try:
        return run(["lake", "env", "lean", name], timeout=1200)
    finally:
        os.unlink(name)


# The decisive check: let Lean list every declaration. Text scanning cannot match Lean's lexer (`«/-»`, `s!"{"/-"}"`...),
# so this walks the environment instead. Any `axiom` declared in a Theorems module fails, and every declaration there
# (helpers and sanity sections included, not just main/equiv) must depend only on the standard axioms.
# Residual: an `example` is never added to the environment, so this cannot see it. A `sorry` there is still caught by
# check 2 (Lean's own "declaration uses `sorry`" warning). `example := by native_decide` is not caught by Lean-side
# checks (its aux axiom is discarded with the example); only the raw-text scan looks for it. That is a trust issue
# (compiled code decides a true statement), not a false claim.
SORRY_WARNING = re.compile(r"declaration uses [`']sorry")
LEAN_SCAN = """
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let consts := env.constants.fold (init := #[]) fun acc n ci => acc.push (n, ci)
  let mut count := 0
  for (n, ci) in consts do
    let ours := match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i.toNat]!.getRoot == `Theorems
      | none => LOCAL_TOO
    unless ours do continue
    count := count + 1
    match ci with
    | .axiomInfo _ => IO.println s!"GATE-AXIOM {n}"
    | _ =>
      let axs ← collectAxioms n
      let extra := axs.toList.filter (fun a => !allowed.contains a)
      unless extra.length == 0 do IO.println s!"GATE-BAD {n}: {extra}"
  IO.println s!"GATE-SCANNED {count}"
"""
LEAN_LINE = re.compile(r"^GATE-(AXIOM|BAD) (.*)$", re.M)


def lean_scan(local_too: bool = False, imports: str = "import Lean\nimport Theorems", body: str = ""):
    """(compiled ok, scanned count, [problem lines]) from walking the environment in Lean."""
    r = lean_snippet(body + "\n" + LEAN_SCAN.replace("LOCAL_TOO", "true" if local_too else "false"), imports)
    out = r.stdout + r.stderr
    m = re.search(r"GATE-SCANNED (\d+)", out)
    return r.returncode == 0 and m is not None, int(m.group(1)) if m else 0, \
        [f"{k.lower()} {v}" for k, v in LEAN_LINE.findall(out)], out


def check_lean_scan():
    print("3b. Lean walks every Theorems declaration: no axiom, only standard axioms")
    good, count, problems, out = lean_scan()
    if not good:
        fail("Lean declaration scan did not run")
        print(out[-3000:])
    for pr in problems:
        fail(f"Lean scan: {pr}")
    if good and not problems:
        ok(f"{count} declarations in Theorems modules checked")


AXIOM_LINE = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")


def bad_axioms(output: str) -> dict[str, set[str]]:
    """{declaration: axioms outside the allowed three} from `#print axioms` output."""
    out = {}
    for name, axs in AXIOM_LINE.findall(output):
        extra = {a.strip() for a in axs.replace("\n", " ").split(",") if a.strip()} - ALLOWED_AXIOMS
        if extra:
            out[name] = extra
    return out


def check_axioms_and_statements():
    print("4–5. Axioms, and each proof proves A.Statement")
    lines, decls = [], []
    for s in slugs():
        d = THMS / s
        if (d / "Equiv.lean").exists():
            decls.append(f"TuriMath.{s}.equiv")
        if (d / "Proof.lean").exists():
            decls.append(f"TuriMath.{s}.main")
            lines.append(f"example : TuriMath.{s}.A.Statement := TuriMath.{s}.main")
    if not decls:
        ok("no proofs or equivalences yet")
        return
    lines += [f"#print axioms {x}" for x in decls]
    r = lean_snippet("\n".join(lines))
    out = r.stdout + r.stderr
    if r.returncode != 0:
        fail("axiom/statement check did not compile (a proof may not prove exactly A.Statement)")
        print(out[-3000:])
        return
    for name, extra in bad_axioms(out).items():
        fail(f"{name} uses axioms outside the standard three: {', '.join(sorted(extra))}")
    if not bad_axioms(out):
        ok(f"{len(decls)} declarations use only standard axioms")


def check_locked():
    print("6. Locked statements")
    path = ROOT / "locked.txt"
    if not path.exists():
        fail("locked.txt is missing")
        return
    entries = [l.split() for l in path.read_text().splitlines() if l.strip() and not l.startswith("#")]
    bad = 0
    for digest, file in entries:
        f = ROOT / file
        if not f.exists():
            fail(f"locked file {file} was deleted"); bad += 1
        elif hashlib.sha256(f.read_bytes()).hexdigest() != digest:
            fail(f"locked file {file} was changed"); bad += 1
    base = os.environ.get("GATE_BASE", "origin/main")
    old = run(["git", "show", f"{base}:locked.txt"])
    if old.returncode == 0:
        now = set(path.read_text().splitlines())
        for line in old.stdout.splitlines():
            if line.strip() and line not in now:
                fail(f"locked.txt line removed or changed: {line}"); bad += 1
    if not bad:
        ok(f"{len(entries)} locked files unchanged")


def check_metadata():
    print("7. Task metadata")
    bad = 0
    for p in sorted((ROOT / "data/tasks").glob("*.json")):
        if p.name.startswith("_"):
            continue
        try:
            missing = REQUIRED_FIELDS - set(json.loads(p.read_text()))
        except json.JSONDecodeError as e:
            fail(f"{p.name}: not valid JSON ({e})"); bad += 1
            continue
        if missing:
            fail(f"{p.name}: missing {', '.join(sorted(missing))}"); bad += 1
    for s in slugs():
        if (THMS / s / "Proof.lean").exists() and not (ROOT / f"data/tasks/{s}.json").exists():
            fail(f"{s} has a proof but no data/tasks/{s}.json"); bad += 1
    if not bad:
        ok("metadata complete")


def red_flags():
    print("Red flags (report only; Gödel reads this)")
    found = 0
    for s in slugs():
        for side in ("A", "B"):
            if not (THMS / s / f"{side}.lean").exists():
                continue
            body = (f"set_option maxHeartbeats 20000 in\n"
                    f"example : TuriMath.{s}.{side}.Statement := by\n"
                    f"  unfold TuriMath.{s}.{side}.Statement\n"
                    f"  first | trivial | decide | simp | norm_num")
            r = lean_snippet(body, f"import Theorems.{s}.{side}\nimport Mathlib")
            if r.returncode == 0:
                print(f"  ⚑ {s}.{side}: closed outright by trivial/decide/simp/norm_num: probably weakened")
                found += 1
    if not found:
        print("  none")


# ---------- Gate 0 self-test ----------
PLANTED = {
    "sorry": ("theorem planted : 1 + 1 = 3 := by sorry", "sorryAx"),
    "attribute axiom": ("@[simp] axiom planted_ax : 1 + 1 = 3\ntheorem planted : 1 + 1 = 3 := planted_ax", "planted_ax"),
    "modified axiom": ("set_option autoImplicit false in\n@[simp]\nprivate axiom planted_ax : 1 + 1 = 3\n"
                       "theorem planted : 1 + 1 = 3 := planted_ax", "planted_ax"),
    "same-line axiom": ("theorem t0 : True := trivial axiom planted_ax : 1 + 1 = 3\n"
                        "theorem planted : 1 + 1 = 3 := planted_ax", "planted_ax"),
    "axiom hidden by strings": ('def s1 := "/-"\naxiom planted_ax : 1 + 1 = 3\ndef s2 := "-/"\n'
                                "theorem planted : 1 + 1 = 3 := planted_ax", "planted_ax"),
    "quoted set_option": ('set_option trace.profiler.output "a b" in axiom planted_ax : 1 + 1 = 3\n'
                          "theorem planted : 1 + 1 = 3 := planted_ax", "planted_ax"),
    "guillemet-hidden axiom": ("def «/-» := 1\naxiom planted_ax : 1 + 1 = 3\ndef «-/» := 2\n"
                               "theorem planted : 1 + 1 = 3 := planted_ax", "planted_ax"),
    "interpolation-hidden axiom": ('def x1 := s!"{"/-"}"\naxiom planted_ax : 1 + 1 = 3\ndef x2 := s!"{"-/"}"\n'
                                   "theorem planted : 1 + 1 = 3 := planted_ax", "planted_ax"),
    "guillemet line comment": ("def «--» := 3 axiom planted_ax : 1 + 1 = 3\n"
                               "theorem planted : 1 + 1 = 3 := planted_ax", "planted_ax"),
    "guillemet quote": ('def «"» := 4\naxiom planted_ax : 1 + 1 = 3\ndef «x"» := 5\n'
                        "theorem planted : 1 + 1 = 3 := planted_ax", "planted_ax"),
    "axiom": ("axiom planted_ax : 1 + 1 = 3\ntheorem planted : 1 + 1 = 3 := planted_ax", "planted_ax"),
}


# Forms that silence Lean's own sorry warning, so only the raw-text scan can catch them.
RAW_PLANTS = {
    "guard_msgs silences sorry warning": 'def x1 := s!"{"/-"}"\n/-- warning: declaration uses `sorry` -/\n#guard_msgs in\n'
                                         'example : ∃ n : Nat, n + 1 = 0 := by sorry\ndef x2 := s!"{"-/"}"',
    "warn.sorry false": 'def x1 := s!"{"/-"}"\nset_option warn.sorry false in\nexample : ∃ n : Nat, n + 1 = 0 := by sorry\n'
                        'def x2 := s!"{"-/"}"',
}
SORRY_PLANT = ('def x1 := s!"{"/-"}"\nexample : ∃ n : Nat, n + 1 = 0 := by sorry\ndef x2 := s!"{"-/"}"')


def selftest() -> int:
    print("Gate 0 self-test: the gate must reject a planted sorry and a planted extra axiom")
    errors = 0
    for name, (src, axiom) in PLANTED.items():
        caught_text = bool(FORBIDDEN.search(src))
        good, _, problems, out = lean_scan(local_too=True, imports="import Lean\nimport Mathlib.Init", body=src)
        caught_lean = good and any(" planted" in pr or axiom in pr for pr in problems)
        status = "caught" if caught_lean and caught_text else "MISSED"      # both the raw scan and Lean must catch it
        print(f"  {name}: Lean scan {'✓' if caught_lean else '✗'} · raw scan {'✓' if caught_text else '✗'} → {status}")
        if not good:
            print(out[-1500:])
        errors += status != "caught"
    for name, src in RAW_PLANTS.items():
        caught = bool(FORBIDDEN.search(src))
        print(f"  {name}: raw text scan {'✓' if caught else '✗'} → {'caught' if caught else 'MISSED'}")
        errors += not caught
    root_plant = "import Theorems.Tmp.A\nimport Mathlib.Init\nset_option warn.sorry false in\nexample : ∃ n : Nat, n + 3 = 0 := by sorry\n"
    ok_index = not index_violations("-- note\n\nimport Theorems.Tmp.A\nimport Theorems.Foo.Proof\n")
    caught = bool(index_violations(root_plant)) and bool(FORBIDDEN.search(root_plant)) and ok_index
    print(f"  code in root Theorems.lean: index check + raw scan {'✓' if caught else '✗'} → {'caught' if caught else 'MISSED'}")
    errors += not caught
    r = lean_snippet(SORRY_PLANT, "import Mathlib.Init")
    caught = bool(SORRY_WARNING.search(r.stdout + r.stderr))
    print(f"  example-sorry hidden by interpolation: raw scan {'✓' if FORBIDDEN.search(SORRY_PLANT) else '✗'}"
          f" · Lean's sorry warning {'✓' if caught else '✗'} → {'caught' if caught else 'MISSED'}")
    errors += not caught
    print("Gate 0 passed" if not errors else "Gate 0 FAILED")
    return 1 if errors else 0


def main() -> int:
    (ROOT / ".lake").mkdir(exist_ok=True)
    if "--selftest" in sys.argv:
        return selftest()
    check_imports()
    check_build()
    check_forbidden()
    check_lean_scan()
    if not failures:                 # the Lean checks need a successful build
        check_axioms_and_statements()
    check_locked()
    check_metadata()
    if not failures:
        red_flags()
    print("\nGATE " + ("GREEN" if not failures else f"RED ({len(failures)} problem{'s' * (len(failures) != 1)})"))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
