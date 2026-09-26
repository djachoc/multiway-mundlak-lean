/-
PORTED FILE — NOTICE REQUIRED BY THE APACHE LICENSE, VERSION 2.0, SECTION 4.

Upstream repository : CausalSmith (the `Causalean` library)
Upstream path       : Causalean/Mathlib/Probability/SteinMethod/Bounds.lean
Upstream toolchain  : leanprover/lean4:v4.33.0
Upstream licence    : Apache License, Version 2.0
                      http://www.apache.org/licenses/LICENSE-2.0
Upstream copyright  : Copyright (c) 2026 Jiyuan Tan. All rights reserved. The upstream
                      copyright block and author line are kept verbatim immediately below.

MODIFICATIONS: this file has been modified in this package to
build against leanprover/lean4:v4.34.0 and its matching Mathlib. The changes made here,
relative to the upstream v4.33.0 file, are:
  * this notice was prepended;
  * every `import` line naming a sibling module of this chain was re-rooted from
    `Causalean.Mathlib.Probability.SteinMethod.…` to `Multiway.SteinCLT.…`, the upstream
    file names `Bounds_Part1.lean` / `Bounds_Part2.lean` becoming `BoundsPart1.lean` /
    `BoundsPart2.lean` so that the module names carry no underscore;
No mathematical content, no declaration name, no namespace (the upstream namespace
`Causalean.Mathlib.Probability.SteinMethod` is kept exactly as written), no docstring and no
attribution of the upstream file was removed or altered.

Lean's new module system (`module`, `public import`, `@[expose] public section`) is kept
exactly as upstream wrote it: v4.34.0 accepts these files unchanged in that respect, so no
`module` or `public` marker was stripped.

Every repair is marked in place with a `-- PORT v4.34.0:` comment saying what changed.
-/
/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Multiway.SteinCLT.BoundsPart2
/-!
Quantitative error bounds from Stein's method, including the two parts of the core bound construction. Use these results to turn a Stein identity into an explicit distributional approximation error.
-/
