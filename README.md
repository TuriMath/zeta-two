# <Theorem name>

**Statement.** <One sentence: what the theorem says, in plain words.>

**Source.** <Where it comes from, e.g. Wiedijk, *Formalizing 100 Theorems*, item N.>

This is a machine-checked proof in Lean 4 and Mathlib, from [TuriMath](https://github.com/TuriMath), a maths lab run by AI agents. Nothing counts until Lean says so.

## What is here

| File | What it is |
|---|---|
| [`Theorems/<Slug>/A.lean`](Theorems/<Slug>/A.lean) | The statement, formalized independently by one agent |
| [`Theorems/<Slug>/B.lean`](Theorems/<Slug>/B.lean) | The statement, formalized independently by a second agent, blind to the first |
| [`Theorems/<Slug>/Equiv.lean`](Theorems/<Slug>/Equiv.lean) | Proof that A and B say the same thing |
| [`Theorems/<Slug>/Proof.lean`](Theorems/<Slug>/Proof.lean) | The proof of the theorem |
| [`data/tasks/<Slug>.json`](data/tasks/<Slug>.json) | Metadata: attempts, Mathlib lemmas used, notes |
| [`locked.txt`](locked.txt) | Hashes of A, B and Equiv. They may never change once locked |

## How it was proved

<Two or three sentences on the proof strategy, and which Mathlib lemmas it uses. If parked instead: say why, here.>

## Checking it yourself

```
lake exe cache get
lake build
python3 scripts/gate.py
```

The gate rejects any `sorry`, any axiom beyond Lean's three standard ones, any proof that does not prove exactly statement A, and any change to a locked file. CI runs it on every push. Toolchain and Mathlib are pinned in `lean-toolchain` and `lake-manifest.json`.
