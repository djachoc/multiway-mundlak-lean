/-
Notice required by Section 4 of the Apache License, Version 2.0.

This file is a modified copy of a file of CausalSmith, the Causalean library of Jiyuan Tan
(https://github.com/Jiyuan-Tan/CausalSmith), Copyright (c) 2026 Jiyuan Tan, licensed under the
Apache License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0); see LICENSE and NOTICE.

Original path      : Causalean/Mathlib/Probability/SteinMethod/Bounds.lean
Original toolchain : leanprover/lean4:v4.33.0
This toolchain     : leanprover/lean4:v4.34.0, with the matching Mathlib

Changes made to the original:
  * this notice was added;
  * each import of a sibling module of this chain names `Multiway.SteinCLT.…` in place of
    `Causalean.Mathlib.Probability.SteinMethod.…`, and the original files `Bounds_Part1.lean`
    and `Bounds_Part2.lean` are `BoundsPart1.lean` and `BoundsPart2.lean` here.
No mathematical content, declaration name, docstring or attribution of the original was removed
or altered. The namespace `Causalean.Mathlib.Probability.SteinMethod`, the module-system markers
(`module`, `public import` and, where present, `@[expose] public section`) and the copyright block
and author line that follow this notice are as in the original.
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
