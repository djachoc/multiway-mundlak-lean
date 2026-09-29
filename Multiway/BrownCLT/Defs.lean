/-
Notice required by Section 4 of the Apache License, Version 2.0.

This file is a modified copy of a file of Stat-Lean, the Lean 4 formalization of statistical
theory (https://github.com/StatLean/Stat-Lean), Copyright 2024 Junwei Lu, licensed under the
Apache License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0); see LICENSE and NOTICE.

Original path      : StatLean/TimeSeries/ForMathlib/Probability/MartingaleCLT/Defs.lean
Original toolchain : leanprover/lean4:v4.29.1
This toolchain     : leanprover/lean4:v4.34.0, with the matching Mathlib

Changes made to the original:
  * this notice was added;
  * the module and field docstrings were shortened.
No mathematical content or attribution of the original was removed.
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Moments.Variance

/-!
# Martingale-difference arrays

The triangular-array martingale-difference structure of the martingale central limit theorem of
Brown (1971). Each row `n` has a filtration `𝓕_{n,0} ≤ ⋯ ≤ 𝓕_{n,k_n}` and differences `X_{n,i}`
that are `𝓕_{n,i+1}`-measurable, square-integrable, and have vanishing
conditional mean given `𝓕_{n,i}`. The conditional variance process is
`V_n = Σ_{i<k_n} E[X_{n,i}² | 𝓕_{n,i}]`. Filtrations are plain monotone families
`Fin (k n + 1) → MeasurableSpace Ω`.

## References

* B. M. Brown, *Martingale central limit theorems*, Ann. Math. Statist. **42** (1971), 59–66.
* P. Hall and C. C. Heyde, *Martingale Limit Theory and Its Application*, Academic Press,
  1980, Theorem 3.2 and Corollary 3.1.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A martingale-difference triangular array. Row `n` has `k n` differences adapted to the row
filtration `F n : Fin (k n + 1) → MeasurableSpace Ω`. -/
structure IsMDSArray (k : ℕ → ℕ) (X : (n : ℕ) → Fin (k n) → Ω → ℝ)
    (F : (n : ℕ) → Fin (k n + 1) → MeasurableSpace Ω) (μ : Measure Ω) : Prop where
  /-- The row filtration is a family of sub-σ-algebras. -/
  le_ambient : ∀ n i, F n i ≤ ‹MeasurableSpace Ω›
  /-- The row filtration is monotone. -/
  mono : ∀ n, Monotone (F n)
  /-- `X_{n,i}` is `𝓕_{n,i+1}`-measurable. -/
  adapted : ∀ n (i : Fin (k n)), Measurable[F n i.succ] (X n i)
  /-- The differences are square-integrable. -/
  memLp : ∀ n (i : Fin (k n)), MemLp (X n i) 2 μ
  /-- The martingale-difference property `E[X_{n,i} | 𝓕_{n,i}] = 0`. -/
  condexp_zero : ∀ n (i : Fin (k n)), μ[X n i | F n i.castSucc] =ᵐ[μ] 0

/-- The conditional variance process of a row, `V_n = Σ_{i<k_n} E[X_{n,i}² | 𝓕_{n,i}]`. -/
noncomputable def mdsCondVariance (k : ℕ → ℕ) (X : (n : ℕ) → Fin (k n) → Ω → ℝ)
    (F : (n : ℕ) → Fin (k n + 1) → MeasurableSpace Ω) (μ : Measure Ω) (n : ℕ)
    (ω : Ω) : ℝ :=
  ∑ i, μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω

/-- The row sums `S_n = Σ_{i<k_n} X_{n,i}`. -/
def mdsRowSum (k : ℕ → ℕ) (X : (n : ℕ) → Fin (k n) → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i, X n i ω

end StatLean.TimeSeries
