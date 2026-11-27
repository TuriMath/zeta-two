import Lake
open Lake DSL

-- Mathlib is pinned to one commit per phase (vision.md, principle 5). Upgrade only through an issue.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "fc4f59e577feb1a4956671bc04ac18aaaf8cd842" -- v4.36.0

package theorems where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib Theorems where
