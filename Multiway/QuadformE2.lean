import Multiway.Sqrt
import Multiway.InclusionExclusion
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.FieldSimp

/-!
# Variance of a quadratic form under interaction dependence

This file formalizes Lemma SM.C.6 of the paper (variance of a quadratic form under interaction
dependence): for symmetric `W`,
`Var(ζ'Wζ | 𝒟) ≤ 2 tr(W Ω' W Ω') + C(M) G_max c_max ‖W‖_F²`.

The conditional expectation is an abstract linear functional `E : (Ω → ℝ) →ₗ[ℝ] ℝ`, standing
for `E[· | 𝒟]` along a fixed design realization, and `W` is a constant matrix. The fourth
joint cumulant is defined by the moment formula for mean-zero variables, so multilinearity and
vanishing under a split into independent groups are immediate. The moment identities used by
the proof enter as hypotheses (`hOmdef`, `hsupp`, `hbdd`); they are derived from a product-law
model of Regime 2 in `Multiway.QuadformE2Indep`. The bulk of the file is the site counting.

## Main results

* `varQuad_eq`: `Var(ζ'Wζ) = 2 tr(WΩ'WΩ') + 𝒦`.
* `var_quadForm_le`, `var_quadForm_le_sites`: the bound with the cumulant expansion as a
  hypothesis.
* `var_quadForm_le_levels`: the bound from the level decomposition.

The names `Linked` and `quadForm` here are distinct from `Multiway.Linked` and
`Multiway.Quadform.quadForm`.
-/

namespace Multiway
namespace QuadformE2

open Finset

/-! ## 1. `cum₄` by definition, and its algebra -/

section Cumulants

variable {Ω : Type*}

/-- The fourth joint cumulant of four mean-zero variables, defined by the moment formula
`E[abcd] - E[ab]E[cd] - E[ac]E[bd] - E[ad]E[bc]`. -/
def cum4 (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (a b c d : Ω → ℝ) : ℝ :=
  E (a * b * c * d) - E (a * b) * E (c * d) - E (a * c) * E (b * d) - E (a * d) * E (b * c)

/-- Additivity in the first argument. -/
theorem cum4_add_one (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (x y b c d : Ω → ℝ) :
    cum4 E (x + y) b c d = cum4 E x b c d + cum4 E y b c d := by
  simp only [cum4, add_mul, map_add]; ring

/-- Additivity in the second argument. -/
theorem cum4_add_two (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (a x y c d : Ω → ℝ) :
    cum4 E a (x + y) c d = cum4 E a x c d + cum4 E a y c d := by
  simp only [cum4, add_mul, mul_add, map_add]; ring

/-- Additivity in the third argument. -/
theorem cum4_add_three (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (a b x y d : Ω → ℝ) :
    cum4 E a b (x + y) d = cum4 E a b x d + cum4 E a b y d := by
  simp only [cum4, add_mul, mul_add, map_add]; ring

/-- Additivity in the fourth argument. -/
theorem cum4_add_four (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (a b c x y : Ω → ℝ) :
    cum4 E a b c (x + y) = cum4 E a b c x + cum4 E a b c y := by
  simp only [cum4, add_mul, mul_add, map_add]; ring

/-- The cumulant vanishes when its first argument does. -/
theorem cum4_zero_one (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (b c d : Ω → ℝ) : cum4 E 0 b c d = 0 := by
  simp [cum4]

/-- Multilinearity in the first slot: a finite sum may be expanded inside a cumulant. -/
theorem cum4_sum_one {ι : Type*} (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (s : Finset ι) (f : ι → Ω → ℝ)
    (b c d : Ω → ℝ) : cum4 E (∑ i ∈ s, f i) b c d = ∑ i ∈ s, cum4 E (f i) b c d := by
  classical
  induction s using Finset.induction with
  | empty => simp [cum4_zero_one]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, cum4_add_one, ih]

/-- The same expansion in the second slot. -/
theorem cum4_sum_two {ι : Type*} (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (s : Finset ι) (f : ι → Ω → ℝ)
    (a c d : Ω → ℝ) : cum4 E a (∑ i ∈ s, f i) c d = ∑ i ∈ s, cum4 E a (f i) c d := by
  classical
  induction s using Finset.induction with
  | empty => simp [cum4]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, cum4_add_two, ih]

/-- The same expansion in the third slot. -/
theorem cum4_sum_three {ι : Type*} (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (s : Finset ι) (f : ι → Ω → ℝ)
    (a b d : Ω → ℝ) : cum4 E a b (∑ i ∈ s, f i) d = ∑ i ∈ s, cum4 E a b (f i) d := by
  classical
  induction s using Finset.induction with
  | empty => simp [cum4]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, cum4_add_three, ih]

/-- The same expansion in the fourth slot. -/
theorem cum4_sum_four {ι : Type*} (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (s : Finset ι) (f : ι → Ω → ℝ)
    (a b c : Ω → ℝ) : cum4 E a b c (∑ i ∈ s, f i) = ∑ i ∈ s, cum4 E a b c (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [cum4]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, cum4_add_four, ih]

/-- `cum₄` is symmetric in its first two arguments. -/
theorem cum4_swap_one_two (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (a b c d : Ω → ℝ) :
    cum4 E a b c d = cum4 E b a c d := by
  have h2 : a * b = b * a := mul_comm a b
  simp only [cum4, h2]; ring

/-- `cum₄` is symmetric in its middle two arguments. -/
theorem cum4_swap_two_three (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (a b c d : Ω → ℝ) :
    cum4 E a b c d = cum4 E a c b d := by
  have h1 : a * b * c * d = a * c * b * d := by ring
  have h2 : b * c = c * b := mul_comm b c
  simp only [cum4, h1, h2]; ring

/-- `cum₄` is symmetric in its last two arguments. -/
theorem cum4_swap_three_four (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (a b c d : Ω → ℝ) :
    cum4 E a b c d = cum4 E a b d c := by
  have h1 : a * b * c * d = a * b * d * c := by ring
  have h2 : c * d = d * c := mul_comm c d
  simp only [cum4, h1, h2]; ring

/-- A cumulant vanishes when every moment term of the moment formula containing the first
argument vanishes. -/
theorem cum4_eq_zero_of_moments_vanish (E : (Ω → ℝ) →ₗ[ℝ] ℝ) {a b c d : Ω → ℝ}
    (h4 : E (a * b * c * d) = 0) (hab : E (a * b) = 0) (hac : E (a * c) = 0)
    (had : E (a * d) = 0) : cum4 E a b c d = 0 := by
  simp [cum4, h4, hab, hac, had]

/-- A joint cumulant of mean-zero variables vanishes when its arguments split into two
independent pairs `{a,b} ⊥ {c,d}`. -/
theorem cum4_eq_zero_of_indep_pair (E : (Ω → ℝ) →ₗ[ℝ] ℝ) {a b c d : Ω → ℝ}
    (h4 : E (a * b * c * d) = E (a * b) * E (c * d))
    (hac : E (a * c) = E a * E c) (had : E (a * d) = E a * E d)
    (hbc : E (b * c) = E b * E c) (hbd : E (b * d) = E b * E d)
    (ha : E a = 0) (hb : E b = 0) : cum4 E a b c d = 0 := by
  simp [cum4, h4, hac, had, hbc, hbd, ha, hb]

/-- The same, in the singleton-versus-triple case `{a} ⊥ {b,c,d}`: every term of the
moment formula carries `E[a] = 0`. -/
theorem cum4_eq_zero_of_indep_single (E : (Ω → ℝ) →ₗ[ℝ] ℝ) {a b c d : Ω → ℝ}
    (h4 : E (a * (b * c * d)) = E a * E (b * c * d))
    (hab : E (a * b) = E a * E b) (hac : E (a * c) = E a * E c)
    (had : E (a * d) = E a * E d) (ha : E a = 0) : cum4 E a b c d = 0 := by
  have hassoc : a * b * c * d = a * (b * c * d) := by ring
  simp [cum4, hassoc, h4, hab, hac, had, ha]

end Cumulants

/-! ## 2. The weighted double count -/

section DoubleCount

/-- A weighted double sum supported on a relation `A`, with summands bounded by `K`, is at
most `Λ K ∑ w²` when `Λ` bounds the number of partners of any `p` in either direction. -/
theorem abs_sum_pairs_le {α : Type*} [Fintype α] (w : α → ℝ) (A : α → α → Prop)
    [DecidableRel A] (g : α → α → ℝ) {K Λ : ℝ} (hK : 0 ≤ K)
    (hsupp : ∀ p q, ¬ A p q → g p q = 0) (hbdd : ∀ p q, |g p q| ≤ K)
    (hrow : ∀ p, ((Finset.univ.filter fun q => A p q).card : ℝ) ≤ Λ)
    (hcol : ∀ q, ((Finset.univ.filter fun p => A p q).card : ℝ) ≤ Λ) :
    |∑ p, ∑ q, w p * w q * g p q| ≤ K * Λ * ∑ p, (w p) ^ 2 := by
  have hnn : ∀ x : α, (0:ℝ) ≤ K / 2 * (w x) ^ 2 := fun x =>
    mul_nonneg (by linarith) (sq_nonneg _)
  -- the pointwise bound
  have hbound : ∀ p q, |w p * w q * g p q|
      ≤ (if A p q then K / 2 * (w p) ^ 2 + K / 2 * (w q) ^ 2 else 0) := by
    intro p q
    by_cases h : A p q
    · have hAM : |w p| * |w q| ≤ ((w p) ^ 2 + (w q) ^ 2) / 2 := by
        nlinarith [sq_nonneg (|w p| - |w q|), sq_abs (w p), sq_abs (w q),
          abs_nonneg (w p), abs_nonneg (w q)]
      have : |w p * w q * g p q| ≤ K / 2 * (w p) ^ 2 + K / 2 * (w q) ^ 2 := by
        calc |w p * w q * g p q| = |w p| * |w q| * |g p q| := by rw [abs_mul, abs_mul]
          _ ≤ ((w p) ^ 2 + (w q) ^ 2) / 2 * K :=
              mul_le_mul hAM (hbdd p q) (abs_nonneg _) (by positivity)
          _ = K / 2 * (w p) ^ 2 + K / 2 * (w q) ^ 2 := by ring
      simpa [h] using this
    · simp [h, hsupp p q h]
  -- triangle inequality, then split into row and column sums
  have htri : |∑ p, ∑ q, w p * w q * g p q| ≤ ∑ p, ∑ q, |w p * w q * g p q| :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun p _ => Finset.abs_sum_le_sum_abs _ _)
  have hsplit : ∑ p, ∑ q, |w p * w q * g p q|
      ≤ (∑ p, ∑ q, (if A p q then K / 2 * (w p) ^ 2 else 0))
        + ∑ p, ∑ q, (if A p q then K / 2 * (w q) ^ 2 else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q _ => (hbound p q).trans ?_
    by_cases h : A p q <;> simp [h]
  -- the row sum
  have hR1 : (∑ p, ∑ q, (if A p q then K / 2 * (w p) ^ 2 else 0))
      ≤ K / 2 * Λ * ∑ p, (w p) ^ 2 := by
    have hfib : ∀ p : α, (∑ q, (if A p q then K / 2 * (w p) ^ 2 else 0))
        = ((Finset.univ.filter fun q => A p q).card : ℝ) * (K / 2 * (w p) ^ 2) := by
      intro p
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    simp only [hfib]
    calc ∑ p, ((Finset.univ.filter fun q => A p q).card : ℝ) * (K / 2 * (w p) ^ 2)
        ≤ ∑ p, Λ * (K / 2 * (w p) ^ 2) :=
          Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_right (hrow p) (hnn p)
      _ = K / 2 * Λ * ∑ p, (w p) ^ 2 := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]; ring
  -- the column sum
  have hR2 : (∑ p, ∑ q, (if A p q then K / 2 * (w q) ^ 2 else 0))
      ≤ K / 2 * Λ * ∑ p, (w p) ^ 2 := by
    rw [Finset.sum_comm]
    have hfib : ∀ q : α, (∑ p, (if A p q then K / 2 * (w q) ^ 2 else 0))
        = ((Finset.univ.filter fun p => A p q).card : ℝ) * (K / 2 * (w q) ^ 2) := by
      intro q
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    simp only [hfib]
    calc ∑ q, ((Finset.univ.filter fun p => A p q).card : ℝ) * (K / 2 * (w q) ^ 2)
        ≤ ∑ q, Λ * (K / 2 * (w q) ^ 2) :=
          Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_right (hcol q) (hnn q)
      _ = K / 2 * Λ * ∑ p, (w p) ^ 2 := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]; ring
  linarith

end DoubleCount

/-! ## 3. The variance identity -/

section Identity

variable {Ω O : Type*} [Fintype O] [DecidableEq O]

omit [Fintype O] [DecidableEq O] in
/-- An entry of a symmetric matrix is unchanged by transposing its indices. -/
theorem entry_symm {W : Matrix O O ℝ} (hW : W.IsSymm) (i j : O) : W i j = W j i := by
  conv_lhs => rw [← hW]
  rfl

/-- The quadratic form `ζ'Wζ`, as a random variable. -/
def quadForm (W : Matrix O O ℝ) (z : O → Ω → ℝ) : Ω → ℝ :=
  ∑ o : O, ∑ o' : O, W o o' • (z o * z o')

omit [DecidableEq O] in
@[simp] theorem quadForm_apply (W : Matrix O O ℝ) (z : O → Ω → ℝ) (ω : Ω) :
    quadForm W z ω = ∑ o : O, ∑ o' : O, W o o' * (z o ω * z o' ω) := by
  simp [quadForm, Finset.sum_apply]

omit [DecidableEq O] in
/-- The square of the quadratic form, expanded into a fourfold sum. -/
theorem quadForm_sq (W : Matrix O O ℝ) (z : O → Ω → ℝ) :
    quadForm W z ^ 2 = ∑ o₁ : O, ∑ o₂ : O, ∑ o₃ : O, ∑ o₄ : O,
      (W o₁ o₂ * W o₃ o₄) • (z o₁ * z o₂ * z o₃ * z o₄) := by
  have key : ∀ o₁ o₃ : O,
      (∑ o₂ : O, W o₁ o₂ • (z o₁ * z o₂)) * (∑ o₄ : O, W o₃ o₄ • (z o₃ * z o₄))
        = ∑ o₂ : O, ∑ o₄ : O, (W o₁ o₂ * W o₃ o₄) • (z o₁ * z o₂ * z o₃ * z o₄) := by
    intro o₁ o₃
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun o₂ _ => Finset.sum_congr rfl fun o₄ _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1
    ring
  rw [sq, quadForm, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun o₁ _ => ?_
  simp only [key]
  exact Finset.sum_comm

omit [DecidableEq O] in
/-- `E[ζ'Wζ]`. -/
theorem expect_quadForm (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (W : Matrix O O ℝ) (z : O → Ω → ℝ) :
    E (quadForm W z) = ∑ o₁ : O, ∑ o₂ : O, W o₁ o₂ * E (z o₁ * z o₂) := by
  simp [quadForm, map_sum, map_smul]

omit [DecidableEq O] in
/-- `E[(ζ'Wζ)²]`. -/
theorem expect_quadForm_sq (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (W : Matrix O O ℝ) (z : O → Ω → ℝ) :
    E (quadForm W z ^ 2) = ∑ o₁ : O, ∑ o₂ : O, ∑ o₃ : O, ∑ o₄ : O,
      W o₁ o₂ * W o₃ o₄ * E (z o₁ * z o₂ * z o₃ * z o₄) := by
  rw [quadForm_sq]
  simp [map_sum, map_smul]

/-- `𝒦 := ∑ W_{o₁o₂}W_{o₃o₄} cum₄(ζ_{o₁},ζ_{o₂},ζ_{o₃},ζ_{o₄})`. -/
def kappaSum (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (W : Matrix O O ℝ) (z : O → Ω → ℝ) : ℝ :=
  ∑ o₁ : O, ∑ o₂ : O, ∑ o₃ : O, ∑ o₄ : O,
    W o₁ o₂ * W o₃ o₄ * cum4 E (z o₁) (z o₂) (z o₃) (z o₄)

/-- `Var(ζ'Wζ | 𝒟)`. -/
def varQuad (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (W : Matrix O O ℝ) (z : O → Ω → ℝ) : ℝ :=
  E (quadForm W z ^ 2) - (E (quadForm W z)) ^ 2

omit [DecidableEq O] in
/-- `tr(WΩ'WΩ')` written out as a fourfold sum. -/
theorem trace_expand (W Om : Matrix O O ℝ) :
    (W * Om * W * Om).trace
      = ∑ a : O, ∑ b : O, ∑ c : O, ∑ d : O, W a b * Om b c * W c d * Om d a := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  calc ∑ d : O, ∑ c : O, ∑ b : O, W a b * Om b c * W c d * Om d a
      = ∑ c : O, ∑ d : O, ∑ b : O, W a b * Om b c * W c d * Om d a := Finset.sum_comm
    _ = ∑ c : O, ∑ b : O, ∑ d : O, W a b * Om b c * W c d * Om d a :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ b : O, ∑ c : O, ∑ d : O, W a b * Om b c * W c d * Om d a := Finset.sum_comm

omit [DecidableEq O] in
/-- `Var(ζ'Wζ) = 2 tr(WΩ'WΩ') + 𝒦`, for symmetric `W` and `Ω'`. -/
theorem varQuad_eq (E : (Ω → ℝ) →ₗ[ℝ] ℝ) {W Om : Matrix O O ℝ} (hW : W.IsSymm)
    (hOm : Om.IsSymm) (z : O → Ω → ℝ) (hOmdef : ∀ o o', Om o o' = E (z o * z o')) :
    varQuad E W z = 2 * (W * Om * W * Om).trace + kappaSum E W z := by
  have hmom : ∀ o₁ o₂ o₃ o₄ : O, W o₁ o₂ * W o₃ o₄ * E (z o₁ * z o₂ * z o₃ * z o₄)
      = W o₁ o₂ * W o₃ o₄ * (Om o₁ o₂ * Om o₃ o₄)
        + W o₁ o₂ * W o₃ o₄ * (Om o₁ o₃ * Om o₂ o₄)
        + W o₁ o₂ * W o₃ o₄ * (Om o₁ o₄ * Om o₂ o₃)
        + W o₁ o₂ * W o₃ o₄ * cum4 E (z o₁) (z o₂) (z o₃) (z o₄) := by
    intro o₁ o₂ o₃ o₄
    simp only [cum4, hOmdef]
    ring
  -- the three moment terms
  have h1 : (∑ o₁ : O, ∑ o₂ : O, ∑ o₃ : O, ∑ o₄ : O,
      W o₁ o₂ * W o₃ o₄ * (Om o₁ o₂ * Om o₃ o₄))
      = (∑ o₁ : O, ∑ o₂ : O, W o₁ o₂ * Om o₁ o₂) * ∑ o₁ : O, ∑ o₂ : O, W o₁ o₂ * Om o₁ o₂ := by
    have inner : ∀ o₁ o₂ : O, (∑ o₃ : O, ∑ o₄ : O, W o₁ o₂ * W o₃ o₄ * (Om o₁ o₂ * Om o₃ o₄))
        = (W o₁ o₂ * Om o₁ o₂) * ∑ o₃ : O, ∑ o₄ : O, W o₃ o₄ * Om o₃ o₄ := by
      intro o₁ o₂
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun o₃ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun o₄ _ => ?_
      ring
    simp only [inner, ← Finset.sum_mul]
  have h2 : (W * Om * W * Om).trace
      = ∑ o₁ : O, ∑ o₂ : O, ∑ o₃ : O, ∑ o₄ : O, W o₁ o₂ * W o₃ o₄ * (Om o₁ o₃ * Om o₂ o₄) := by
    calc (W * Om * W * Om).trace
        = ∑ a : O, ∑ b : O, ∑ c : O, ∑ d : O, W a b * Om b c * W c d * Om d a :=
          trace_expand W Om
      _ = ∑ a : O, ∑ b : O, ∑ d : O, ∑ c : O, W a b * Om b c * W c d * Om d a :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ o₁ : O, ∑ o₂ : O, ∑ o₃ : O, ∑ o₄ : O,
            W o₁ o₂ * W o₃ o₄ * (Om o₁ o₃ * Om o₂ o₄) := by
          refine Finset.sum_congr rfl fun o₁ _ => Finset.sum_congr rfl fun o₂ _ =>
            Finset.sum_congr rfl fun o₃ _ => Finset.sum_congr rfl fun o₄ _ => ?_
          rw [entry_symm hW o₄ o₃, entry_symm hOm o₃ o₁]
          ring
  have h3 : (W * Om * W * Om).trace
      = ∑ o₁ : O, ∑ o₂ : O, ∑ o₃ : O, ∑ o₄ : O, W o₁ o₂ * W o₃ o₄ * (Om o₁ o₄ * Om o₂ o₃) := by
    rw [trace_expand]
    refine Finset.sum_congr rfl fun o₁ _ => Finset.sum_congr rfl fun o₂ _ =>
      Finset.sum_congr rfl fun o₃ _ => Finset.sum_congr rfl fun o₄ _ => ?_
    rw [entry_symm hOm o₄ o₁]
    ring
  rw [varQuad, expect_quadForm_sq, expect_quadForm]
  simp only [hmom]
  simp only [← hOmdef]
  simp only [Finset.sum_add_distrib]
  rw [h1, ← h2, ← h3, kappaSum, sq]
  ring

end Identity

/-! ## 4. The site combinatorics

A *site* is a pair `(k, j)` with `k` a fixed-effect dimension and `j` a category of it; argument
`i`, carrying level `e i` and observation `o i`, occupies the site `(k, idx k (o i))` for each
`k ∈ e i`. -/

section Counting

variable {O D L : Type*}

/-- The four arguments `(o₁,o₂,o₃,o₄)` of a cumulant, as a map `Fin 4 → O`. -/
def quad (a b c d : O) : Fin 4 → O :=
  fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d

@[simp] theorem quad_zero (a b c d : O) : quad a b c d 0 = a := by simp [quad]
@[simp] theorem quad_one (a b c d : O) : quad a b c d 1 = b := by simp [quad]
@[simp] theorem quad_two (a b c d : O) : quad a b c d 2 = c := by simp [quad]
@[simp] theorem quad_three (a b c d : O) : quad a b c d 3 = d := by simp [quad]

/-- Every occupied site is occupied by at least two arguments. -/
def Admissible (idx : D → O → L) (e : Fin 4 → Finset D) (o : Fin 4 → O) : Prop :=
  ∀ i : Fin 4, ∀ k ∈ e i, ∃ i' : Fin 4, i' ≠ i ∧ k ∈ e i' ∧ idx k (o i') = idx k (o i)

instance [DecidableEq D] [DecidableEq L] (idx : D → O → L) (e : Fin 4 → Finset D)
    (o : Fin 4 → O) : Decidable (Admissible idx e o) := by
  unfold Admissible; infer_instance

/-- Arguments `i` and `i'` occupy a common site. -/
def SharesSite (idx : D → O → L) (e : Fin 4 → Finset D) (o : Fin 4 → O) (i i' : Fin 4) : Prop :=
  ∃ k ∈ e i, k ∈ e i' ∧ idx k (o i) = idx k (o i')

instance [DecidableEq D] [DecidableEq L] (idx : D → O → L) (e : Fin 4 → Finset D)
    (o : Fin 4 → O) (i i' : Fin 4) : Decidable (SharesSite idx e o i i') := by
  unfold SharesSite; infer_instance

theorem sharesSite_symm {idx : D → O → L} {e : Fin 4 → Finset D} {o : Fin 4 → O} {i i' : Fin 4}
    (h : SharesSite idx e o i i') : SharesSite idx e o i' i := by
  obtain ⟨k, hk, hk', heq⟩ := h
  exact ⟨k, hk', hk, heq.symm⟩

/-- Some member of `{o₃,o₄}` occupies a site occupied by `o₁` or `o₂`. -/
def Linked (idx : D → O → L) (e : Fin 4 → Finset D) (o : Fin 4 → O) : Prop :=
  SharesSite idx e o 2 0 ∨ SharesSite idx e o 2 1
    ∨ SharesSite idx e o 3 0 ∨ SharesSite idx e o 3 1

instance [DecidableEq D] [DecidableEq L] (idx : D → O → L) (e : Fin 4 → Finset D)
    (o : Fin 4 → O) : Decidable (Linked idx e o) := by
  unfold Linked; infer_instance

/-- The determination step: if two quadruples agree off `i₀` and are both admissible, the
remaining argument is determined at every coordinate `k ∈ e i₀`. Proved by counting: two
admissible values would need four distinct partners among the other three arguments. -/
theorem sameOn_of_admissible {idx : D → O → L} {e : Fin 4 → Finset D} {o o' : Fin 4 → O}
    {i₀ : Fin 4} (hagree : ∀ i, i ≠ i₀ → o i = o' i)
    (h : Admissible idx e o) (h' : Admissible idx e o') :
    SameOn idx (e i₀) (o i₀) (o' i₀) := by
  intro k hk
  by_contra hne
  obtain ⟨i₁, hi₁ne, hi₁e, hi₁⟩ := h i₀ k hk
  obtain ⟨i₂, hi₂ne, hi₂e, hi₂⟩ := h' i₀ k hk
  -- `i₂` carries the value `t' := idx k (o' i₀)` under `o` as well
  have hi₂' : idx k (o i₂) = idx k (o' i₀) := by rw [hagree i₂ hi₂ne]; exact hi₂
  -- a second index carrying `t := idx k (o i₀)`
  obtain ⟨i₃, hi₃ne, hi₃e, hi₃⟩ := h' i₁ k hi₁e
  have hi₁' : idx k (o' i₁) = idx k (o i₀) := by rw [← hagree i₁ hi₁ne]; exact hi₁
  have hi₃i₀ : i₃ ≠ i₀ := by
    intro hh
    apply hne
    rw [← hi₁', ← hi₃, hh]
  have hi₃v : idx k (o i₃) = idx k (o i₀) := by
    rw [hagree i₃ hi₃i₀, hi₃, hi₁']
  -- a second index carrying `t'`
  obtain ⟨i₄, hi₄ne, hi₄e, hi₄⟩ := h i₂ k hi₂e
  have hi₄i₀ : i₄ ≠ i₀ := by
    intro hh
    apply hne
    rw [← hi₂', ← hi₄, hh]
  have hi₄v : idx k (o i₄) = idx k (o' i₀) := by rw [hi₄, hi₂']
  -- the four indices are distinct and avoid `i₀`
  have hne12 : i₁ ≠ i₂ := by intro hh; apply hne; rw [← hi₁, hh, hi₂']
  have hne14 : i₁ ≠ i₄ := by intro hh; apply hne; rw [← hi₁, hh, hi₄v]
  have hne32 : i₃ ≠ i₂ := by intro hh; apply hne; rw [← hi₃v, hh, hi₂']
  have hne34 : i₃ ≠ i₄ := by intro hh; apply hne; rw [← hi₃v, hh, hi₄v]
  have hne13 : i₁ ≠ i₃ := fun hh => hi₃ne hh.symm
  have hne24 : i₂ ≠ i₄ := fun hh => hi₄ne hh.symm
  have hsub : ({i₁, i₃, i₂, i₄} : Finset (Fin 4)) ⊆ Finset.univ.erase i₀ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      simp [Finset.mem_erase, hi₁ne, hi₃i₀, hi₂ne, hi₄i₀]
  have hcard4 : ({i₁, i₃, i₂, i₄} : Finset (Fin 4)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hne13, hne12, hne14]),
      Finset.card_insert_of_notMem (by simp [hne32, hne34]),
      Finset.card_insert_of_notMem (by simp [hne24]), Finset.card_singleton]
  have hcard3 : (Finset.univ.erase i₀).card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  have := Finset.card_le_card hsub
  omega

/-! ### The determination step through the multiset `V_k` -/

section Vk

variable [DecidableEq D] [DecidableEq L]

/-- The multiset `V_k` of values at coordinate `k` carried by the three arguments other
than `i₀` that occupy `k`. -/
def valuesAt (idx : D → O → L) (e : Fin 4 → Finset D) (o : Fin 4 → O) (i₀ : Fin 4) (k : D) :
    Multiset L :=
  ((Finset.univ.erase i₀).filter fun i => k ∈ e i).val.map fun i => idx k (o i)

/-- The values at `k` of every argument that occupies `k`. -/
def occValuesAt (idx : D → O → L) (e : Fin 4 → Finset D) (o : Fin 4 → O) (k : D) : Multiset L :=
  (Finset.univ.filter fun i => k ∈ e i).val.map fun i => idx k (o i)

omit [DecidableEq L] in
/-- `|V_k| ≤ 3`. -/
theorem card_valuesAt_le (idx : D → O → L) (e : Fin 4 → Finset D) (o : Fin 4 → O) (i₀ : Fin 4)
    (k : D) : Multiset.card (valuesAt idx e o i₀ k) ≤ 3 := by
  rw [valuesAt, Multiset.card_map]
  have hdef : Multiset.card ((Finset.univ.erase i₀).filter fun i => k ∈ e i).val
      = ((Finset.univ.erase i₀).filter fun i => k ∈ e i).card := rfl
  have h1 : ((Finset.univ.erase i₀).filter fun i => k ∈ e i).card
      ≤ (Finset.univ.erase i₀ : Finset (Fin 4)).card := Finset.card_filter_le _ _
  have h2 : (Finset.univ.erase i₀ : Finset (Fin 4)).card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  omega

omit [DecidableEq L] in
/-- `t_{i₀k} ::ₘ V_k` is the full occupancy multiset at `k`, when `i₀` occupies `k`. -/
theorem cons_valuesAt {idx : D → O → L} {e : Fin 4 → Finset D} {o : Fin 4 → O} {i₀ : Fin 4}
    {k : D} (hk : k ∈ e i₀) :
    idx k (o i₀) ::ₘ valuesAt idx e o i₀ k = occValuesAt idx e o k := by
  have hmem : i₀ ∈ (Finset.univ.filter fun i => k ∈ e i) := by simp [hk]
  have hval : ((Finset.univ.erase i₀).filter fun i => k ∈ e i).val
      = (Finset.univ.filter fun i => k ∈ e i).val.erase i₀ := by
    rw [Finset.filter_erase, Finset.erase_val]
  rw [valuesAt, occValuesAt, hval]
  conv_rhs => rw [← Multiset.cons_erase (Finset.mem_val.mpr hmem)]
  rw [Multiset.map_cons]

/-- Admissibility says that each value present at `k` occurs at least twice in the
occupancy multiset. -/
theorem two_le_count_of_admissible {idx : D → O → L} {e : Fin 4 → Finset D} {o : Fin 4 → O}
    (h : Admissible idx e o) (k : D) {v : L} (hv : v ∈ occValuesAt idx e o k) :
    2 ≤ Multiset.count v (occValuesAt idx e o k) := by
  rw [occValuesAt, Multiset.mem_map] at hv
  obtain ⟨i, hi, hiv⟩ := hv
  have hik : k ∈ e i := by
    have := Finset.mem_val.mp hi
    simpa using this
  obtain ⟨i', hne, hi'k, hi'v⟩ := h i k hik
  have hfi : idx k (o i) = v := hiv
  have hfi' : idx k (o i') = v := by rw [hi'v]; exact hiv
  rw [Multiset.le_count_iff_replicate_le, occValuesAt]
  have hsub : ({i, i'} : Finset (Fin 4)) ⊆ (Finset.univ.filter fun j => k ∈ e j) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [hik, hi'k]
  have hle := Multiset.map_le_map (f := fun j => idx k (o j)) (Finset.val_le_iff.mpr hsub)
  have hins : ({i, i'} : Finset (Fin 4)).val = i ::ₘ {i'} := by
    rw [Finset.insert_val_of_notMem (by simpa using hne.symm)]
    rfl
  rw [hins] at hle
  simpa [Multiset.replicate_succ, hfi, hfi'] using hle

/-- On a multiset with at most three elements, at most one value `t` is such that `t` and
the multiset together contain every value at least twice. The bound is necessary: on
`{a,a,b,b}` both `a` and `b` qualify. -/
theorem eq_of_two_le_count {V : Multiset L} (hV : Multiset.card V ≤ 3) {t t' : L}
    (ht : ∀ j ∈ t ::ₘ V, 2 ≤ Multiset.count j (t ::ₘ V))
    (ht' : ∀ j ∈ t' ::ₘ V, 2 ≤ Multiset.count j (t' ::ₘ V)) : t = t' := by
  by_contra hne
  have h1 : 1 ≤ Multiset.count t V := by
    have := ht t (Multiset.mem_cons_self _ _)
    rw [Multiset.count_cons_self] at this
    omega
  have h2 : 1 ≤ Multiset.count t' V := by
    have := ht' t' (Multiset.mem_cons_self _ _)
    rw [Multiset.count_cons_self] at this
    omega
  have ht'V : t' ∈ V := Multiset.count_pos.mp (by omega)
  have htV : t ∈ V := Multiset.count_pos.mp (by omega)
  have h3 : 2 ≤ Multiset.count t' V := by
    have := ht t' (Multiset.mem_cons_of_mem ht'V)
    rwa [Multiset.count_cons_of_ne (Ne.symm hne)] at this
  have h4 : 2 ≤ Multiset.count t V := by
    have := ht' t (Multiset.mem_cons_of_mem htV)
    rwa [Multiset.count_cons_of_ne hne] at this
  have hsub : Multiset.replicate (Multiset.count t V) t
      + Multiset.replicate (Multiset.count t' V) t' ≤ V := by
    rw [Multiset.le_iff_count]
    intro a
    rw [Multiset.count_add, Multiset.count_replicate, Multiset.count_replicate]
    rcases eq_or_ne a t with rfl | hat
    · have hts : t' ≠ a := fun hh => hne hh.symm
      simp [hts]
    · rcases eq_or_ne a t' with rfl | hat'
      · simp [hne]
      · simp [Ne.symm hat, Ne.symm hat']
  have hcard := Multiset.card_le_card hsub
  rw [Multiset.card_add, Multiset.card_replicate, Multiset.card_replicate] at hcard
  omega

/-- If `V_k` is empty, no value is admissible. -/
theorem not_admissible_of_valuesAt_empty {V : Multiset L} (hV : V = 0) (t : L) :
    ¬ (∀ j ∈ t ::ₘ V, 2 ≤ Multiset.count j (t ::ₘ V)) := by
  subst hV
  intro hcon
  have := hcon t (Multiset.mem_cons_self _ _)
  simp at this

/-- If `V_k` contains two distinct values each occurring exactly once, no value is
admissible. -/
theorem not_admissible_of_two_singletons {V : Multiset L} {a b : L} (hab : a ≠ b)
    (ha : Multiset.count a V = 1) (hb : Multiset.count b V = 1) (t : L) :
    ¬ (∀ j ∈ t ::ₘ V, 2 ≤ Multiset.count j (t ::ₘ V)) := by
  intro hcon
  rcases eq_or_ne t a with rfl | hta
  · have hbV : b ∈ V := Multiset.count_pos.mp (by omega)
    have := hcon b (Multiset.mem_cons_of_mem hbV)
    rw [Multiset.count_cons_of_ne (Ne.symm hab)] at this
    omega
  · have haV : a ∈ V := Multiset.count_pos.mp (by omega)
    have := hcon a (Multiset.mem_cons_of_mem haV)
    rw [Multiset.count_cons_of_ne (Ne.symm hta)] at this
    omega

/-- The determination step, via `V_k`: the two candidate values `t_{i₀k}` and `t'_{i₀k}`
share the same `V_k`, and `eq_of_two_le_count` forces them equal. -/
theorem sameOn_of_admissible_vk {idx : D → O → L} {e : Fin 4 → Finset D} {o o' : Fin 4 → O}
    {i₀ : Fin 4} (hagree : ∀ i, i ≠ i₀ → o i = o' i)
    (h : Admissible idx e o) (h' : Admissible idx e o') :
    SameOn idx (e i₀) (o i₀) (o' i₀) := by
  intro k hk
  have hV : valuesAt idx e o i₀ k = valuesAt idx e o' i₀ k := by
    rw [valuesAt, valuesAt]
    refine Multiset.map_congr rfl ?_
    intro i hi
    have hine : i ≠ i₀ := by
      have := Finset.mem_val.mp hi
      exact (Finset.mem_erase.mp (Finset.mem_filter.mp this).1).1
    rw [hagree i hine]
  refine eq_of_two_le_count (card_valuesAt_le idx e o i₀ k) ?_ ?_
  · intro j hj
    rw [cons_valuesAt hk] at hj ⊢
    exact two_le_count_of_admissible h k hj
  · intro j hj
    rw [hV, cons_valuesAt hk] at hj ⊢
    exact two_le_count_of_admissible h' k hj

end Vk

/-! ### Invariance under permuting the four arguments -/

/-- `Admissible` is a condition on the quadruple, so it survives any relabelling of the four
arguments that moves the levels with them. -/
theorem admissible_comp {idx : D → O → L} {e : Fin 4 → Finset D} {o : Fin 4 → O}
    (σ : Equiv.Perm (Fin 4)) (h : Admissible idx e o) :
    Admissible idx (e ∘ σ) (o ∘ σ) := by
  intro i k hk
  obtain ⟨j, hjne, hje, hj⟩ := h (σ i) k hk
  refine ⟨σ.symm j, ?_, ?_, ?_⟩
  · intro hh
    exact hjne (by rw [← hh]; simp)
  · simpa using hje
  · simpa using hj

theorem admissible_comp_iff {idx : D → O → L} {e : Fin 4 → Finset D} {o : Fin 4 → O}
    (σ : Equiv.Perm (Fin 4)) : Admissible idx (e ∘ σ) (o ∘ σ) ↔ Admissible idx e o := by
  refine ⟨fun h => ?_, admissible_comp σ⟩
  have h2 := admissible_comp σ.symm h
  have he : (e ∘ (σ : Fin 4 → Fin 4)) ∘ (σ.symm : Fin 4 → Fin 4) = e := by funext i; simp
  have ho : (o ∘ (σ : Fin 4 → Fin 4)) ∘ (σ.symm : Fin 4 → Fin 4) = o := by funext i; simp
  rwa [he, ho] at h2

/-- The permutation exchanging the pair `(o₁,o₂)` with the pair `(o₃,o₄)`. -/
def pairSwapFun : Fin 4 → Fin 4 :=
  fun i => if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 0 else 1

/-- The pair swap as a permutation of the four arguments. -/
def pairSwap : Equiv.Perm (Fin 4) where
  toFun := pairSwapFun
  invFun := pairSwapFun
  left_inv := by decide
  right_inv := by decide

@[simp] theorem pairSwap_apply (i : Fin 4) : pairSwap i = pairSwapFun i := rfl

@[simp] theorem pairSwap_zero : (pairSwap : Fin 4 → Fin 4) 0 = 2 := by decide
@[simp] theorem pairSwap_one : (pairSwap : Fin 4 → Fin 4) 1 = 3 := by decide
@[simp] theorem pairSwap_two : (pairSwap : Fin 4 → Fin 4) 2 = 0 := by decide
@[simp] theorem pairSwap_three : (pairSwap : Fin 4 → Fin 4) 3 = 1 := by decide

theorem quad_comp_pairSwap (a b c d : O) :
    (quad a b c d) ∘ (pairSwap : Fin 4 → Fin 4) = quad c d a b := by
  funext i
  fin_cases i <;> simp [pairSwap, pairSwapFun, quad]

/-- `Linked` is invariant under exchanging the two pairs, because `SharesSite` is
symmetric. -/
theorem linked_pairSwap {idx : D → O → L} {e : Fin 4 → Finset D} {o : Fin 4 → O} :
    Linked idx (e ∘ (pairSwap : Fin 4 → Fin 4)) (o ∘ (pairSwap : Fin 4 → Fin 4))
      ↔ Linked idx e o := by
  have hS : ∀ i i' : Fin 4,
      SharesSite idx (e ∘ (pairSwap : Fin 4 → Fin 4)) (o ∘ (pairSwap : Fin 4 → Fin 4)) i i'
        ↔ SharesSite idx e o (pairSwap i) (pairSwap i') := fun _ _ => Iff.rfl
  unfold Linked
  rw [hS 2 0, hS 2 1, hS 3 0, hS 3 1]
  simp only [pairSwap_zero, pairSwap_one, pairSwap_two, pairSwap_three]
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl (sharesSite_symm h)
    · exact Or.inr (Or.inr (Or.inl (sharesSite_symm h)))
    · exact Or.inr (Or.inl (sharesSite_symm h))
    · exact Or.inr (Or.inr (Or.inr (sharesSite_symm h)))
  · rintro (h | h | h | h)
    · exact Or.inl (sharesSite_symm h)
    · exact Or.inr (Or.inr (Or.inl (sharesSite_symm h)))
    · exact Or.inr (Or.inl (sharesSite_symm h))
    · exact Or.inr (Or.inr (Or.inr (sharesSite_symm h)))

/-! ### The count -/

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

/-- The observations sharing a site with `o₁` or with `o₂`. -/
def touchSet (idx : D → O → L) (e : Fin 4 → Finset D) (o₁ o₂ : O) : Finset O :=
  (e 0).biUnion (fun k => cellOf idx ({k} : Finset D) o₁)
    ∪ (e 1).biUnion (fun k => cellOf idx ({k} : Finset D) o₂)

omit [DecidableEq D] in
theorem card_touchSet_le (idx : D → O → L) (e : Fin 4 → Finset D) (o₁ o₂ : O) {Gmax : ℕ}
    (hG : ∀ (k : D) (o : O), (cellOf idx ({k} : Finset D) o).card ≤ Gmax) :
    (touchSet idx e o₁ o₂).card ≤ ((e 0).card + (e 1).card) * Gmax := by
  have b1 : ((e 0).biUnion (fun k => cellOf idx ({k} : Finset D) o₁)).card
      ≤ (e 0).card * Gmax := by
    refine (Finset.card_biUnion_le).trans ?_
    calc ∑ k ∈ e 0, (cellOf idx ({k} : Finset D) o₁).card
        ≤ ∑ _k ∈ e 0, Gmax := Finset.sum_le_sum fun k _ => hG k o₁
      _ = (e 0).card * Gmax := by rw [Finset.sum_const, smul_eq_mul]
  have b2 : ((e 1).biUnion (fun k => cellOf idx ({k} : Finset D) o₂)).card
      ≤ (e 1).card * Gmax := by
    refine (Finset.card_biUnion_le).trans ?_
    calc ∑ k ∈ e 1, (cellOf idx ({k} : Finset D) o₂).card
        ≤ ∑ _k ∈ e 1, Gmax := Finset.sum_le_sum fun k _ => hG k o₂
      _ = (e 1).card * Gmax := by rw [Finset.sum_const, smul_eq_mul]
  refine (Finset.card_union_le _ _).trans ?_
  calc ((e 0).biUnion (fun k => cellOf idx ({k} : Finset D) o₁)).card
        + ((e 1).biUnion (fun k => cellOf idx ({k} : Finset D) o₂)).card
      ≤ (e 0).card * Gmax + (e 1).card * Gmax := by omega
    _ = ((e 0).card + (e 1).card) * Gmax := by ring

/-- The quadruples that can contribute, for a given assignment and a given first pair. -/
def admissiblePairs (idx : D → O → L) (e : Fin 4 → Finset D) (o₁ o₂ : O) : Finset (O × O) :=
  Finset.univ.filter fun p =>
    Admissible idx e (quad o₁ o₂ p.1 p.2) ∧ Linked idx e (quad o₁ o₂ p.1 p.2)

/-- The number of pairs `(o₃,o₄)` that can contribute for a given `(o₁,o₂)` is at most
`2((|e₁|+|e₂|)G_max)c_max`, hence at most `4MG_max c_max`. -/
theorem card_admissiblePairs_le (idx : D → O → L) (e : Fin 4 → Finset D) (o₁ o₂ : O)
    {Gmax cmax : ℕ} (he : ∀ i, 2 ≤ (e i).card)
    (hG : ∀ (k : D) (o : O), (cellOf idx ({k} : Finset D) o).card ≤ Gmax)
    (hc : ∀ (A : Finset D) (o : O), 2 ≤ A.card → (cellOf idx A o).card ≤ cmax) :
    (admissiblePairs idx e o₁ o₂).card ≤ 2 * (((e 0).card + (e 1).card) * Gmax) * cmax := by
  classical
  set T := touchSet idx e o₁ o₂ with hTdef
  -- every contributing pair has a member in `T`
  have hmemT : ∀ p ∈ admissiblePairs idx e o₁ o₂, p.1 ∈ T ∨ p.2 ∈ T := by
    intro p hp
    have hL : Linked idx e (quad o₁ o₂ p.1 p.2) := (Finset.mem_filter.mp hp).2.2
    -- expand the four cases of `Linked`
    rcases hL with ⟨k, hk2, hk0, heq⟩ | ⟨k, hk2, hk1, heq⟩ | ⟨k, hk3, hk0, heq⟩
      | ⟨k, hk3, hk1, heq⟩
    · refine Or.inl ?_
      rw [hTdef, touchSet]
      refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨k, hk0, ?_⟩)
      simp only [mem_cellOf, SameOn, Finset.mem_singleton]
      rintro j rfl
      simpa using heq
    · refine Or.inl ?_
      rw [hTdef, touchSet]
      refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, hk1, ?_⟩)
      simp only [mem_cellOf, SameOn, Finset.mem_singleton]
      rintro j rfl
      simpa using heq
    · refine Or.inr ?_
      rw [hTdef, touchSet]
      refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨k, hk0, ?_⟩)
      simp only [mem_cellOf, SameOn, Finset.mem_singleton]
      rintro j rfl
      simpa using heq
    · refine Or.inr ?_
      rw [hTdef, touchSet]
      refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, hk1, ?_⟩)
      simp only [mem_cellOf, SameOn, Finset.mem_singleton]
      rintro j rfl
      simpa using heq
  -- the fibre over a fixed third argument lies in a single `e 3`-cell
  have hfib3 : ∀ a : O,
      ((admissiblePairs idx e o₁ o₂).filter fun p => p.1 = a).card ≤ cmax := by
    intro a
    rcases Finset.eq_empty_or_nonempty ((admissiblePairs idx e o₁ o₂).filter fun p => p.1 = a)
      with hemp | ⟨p₀, hp₀⟩
    · simp [hemp]
    · have hp0a : p₀.1 = a := (Finset.mem_filter.mp hp₀).2
      have hAdm0 : Admissible idx e (quad o₁ o₂ a p₀.2) := by
        have := (Finset.mem_filter.mp (Finset.mem_filter.mp hp₀).1).2.1
        rwa [hp0a] at this
      refine le_trans (Finset.card_le_card_of_injOn (fun p => p.2) ?_ ?_) (hc (e 3) p₀.2 (he 3))
      · intro p hp
        have hpa : p.1 = a := (Finset.mem_filter.mp hp).2
        have hAdm : Admissible idx e (quad o₁ o₂ a p.2) := by
          have := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
          rwa [hpa] at this
        have hagree : ∀ i : Fin 4, i ≠ 3 → quad o₁ o₂ a p.2 i = quad o₁ o₂ a p₀.2 i := by
          intro i hi
          fin_cases i <;> simp_all
        have hsame := sameOn_of_admissible_vk (i₀ := 3) hagree hAdm hAdm0
        rw [quad_three, quad_three] at hsame
        simpa using hsame
      · intro p hp q hq hpq
        rw [Finset.mem_coe, Finset.mem_filter] at hp hq
        exact Prod.ext (hp.2.trans hq.2.symm) hpq
  -- and the fibre over a fixed fourth argument lies in a single `e 2`-cell
  have hfib2 : ∀ b : O,
      ((admissiblePairs idx e o₁ o₂).filter fun p => p.2 = b).card ≤ cmax := by
    intro b
    rcases Finset.eq_empty_or_nonempty ((admissiblePairs idx e o₁ o₂).filter fun p => p.2 = b)
      with hemp | ⟨p₀, hp₀⟩
    · simp [hemp]
    · have hp0b : p₀.2 = b := (Finset.mem_filter.mp hp₀).2
      have hAdm0 : Admissible idx e (quad o₁ o₂ p₀.1 b) := by
        have := (Finset.mem_filter.mp (Finset.mem_filter.mp hp₀).1).2.1
        rwa [hp0b] at this
      refine le_trans (Finset.card_le_card_of_injOn (fun p => p.1) ?_ ?_) (hc (e 2) p₀.1 (he 2))
      · intro p hp
        have hpb : p.2 = b := (Finset.mem_filter.mp hp).2
        have hAdm : Admissible idx e (quad o₁ o₂ p.1 b) := by
          have := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
          rwa [hpb] at this
        have hagree : ∀ i : Fin 4, i ≠ 2 → quad o₁ o₂ p.1 b i = quad o₁ o₂ p₀.1 b i := by
          intro i hi
          fin_cases i <;> simp_all
        have hsame := sameOn_of_admissible_vk (i₀ := 2) hagree hAdm hAdm0
        rw [quad_two, quad_two] at hsame
        simpa using hsame
      · intro p hp q hq hpq
        rw [Finset.mem_coe, Finset.mem_filter] at hp hq
        exact Prod.ext hpq (hp.2.trans hq.2.symm)
  -- at most `#T` choices for the linked observation, at most `c_max` for the other
  have hcount1 : ((admissiblePairs idx e o₁ o₂).filter fun p => p.1 ∈ T).card
      ≤ T.card * cmax := by
    have hfw := Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
      (s := (admissiblePairs idx e o₁ o₂).filter fun p => p.1 ∈ T) (t := T)
      (fun p hp => (Finset.mem_filter.mp hp).2)
    rw [hfw]
    calc ∑ a ∈ T, (((admissiblePairs idx e o₁ o₂).filter fun p => p.1 ∈ T).filter
          fun p => p.1 = a).card
        ≤ ∑ _a ∈ T, cmax := by
          refine Finset.sum_le_sum fun a _ => le_trans (Finset.card_le_card ?_) (hfib3 a)
          intro x hx
          simp only [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1.1, hx.2⟩
      _ = T.card * cmax := by rw [Finset.sum_const, smul_eq_mul]
  have hcount2 : ((admissiblePairs idx e o₁ o₂).filter fun p => p.2 ∈ T).card
      ≤ T.card * cmax := by
    have hfw := Finset.card_eq_sum_card_fiberwise (f := Prod.snd)
      (s := (admissiblePairs idx e o₁ o₂).filter fun p => p.2 ∈ T) (t := T)
      (fun p hp => (Finset.mem_filter.mp hp).2)
    rw [hfw]
    calc ∑ b ∈ T, (((admissiblePairs idx e o₁ o₂).filter fun p => p.2 ∈ T).filter
          fun p => p.2 = b).card
        ≤ ∑ _b ∈ T, cmax := by
          refine Finset.sum_le_sum fun b _ => le_trans (Finset.card_le_card ?_) (hfib2 b)
          intro x hx
          simp only [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1.1, hx.2⟩
      _ = T.card * cmax := by rw [Finset.sum_const, smul_eq_mul]
  have hunion : admissiblePairs idx e o₁ o₂
      ⊆ ((admissiblePairs idx e o₁ o₂).filter fun p => p.1 ∈ T)
        ∪ ((admissiblePairs idx e o₁ o₂).filter fun p => p.2 ∈ T) := by
    intro p hp
    rcases hmemT p hp with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, h⟩)
  have hTcard : T.card ≤ ((e 0).card + (e 1).card) * Gmax := by
    rw [hTdef]; exact card_touchSet_le idx e o₁ o₂ hG
  calc (admissiblePairs idx e o₁ o₂).card
      ≤ (((admissiblePairs idx e o₁ o₂).filter fun p => p.1 ∈ T)
          ∪ ((admissiblePairs idx e o₁ o₂).filter fun p => p.2 ∈ T)).card :=
        Finset.card_le_card hunion
    _ ≤ ((admissiblePairs idx e o₁ o₂).filter fun p => p.1 ∈ T).card
          + ((admissiblePairs idx e o₁ o₂).filter fun p => p.2 ∈ T).card :=
        Finset.card_union_le _ _
    _ ≤ T.card * cmax + T.card * cmax := by omega
    _ = 2 * T.card * cmax := by ring
    _ ≤ 2 * (((e 0).card + (e 1).card) * Gmax) * cmax :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hTcard)

/-- The admissibility relation of a fixed assignment, between the pairs `(o₁,o₂)` and
`(o₃,o₄)`: the conjunction of `Admissible` and `Linked`. -/
def admRel (idx : D → O → L) (e : Fin 4 → Finset D) (p q : O × O) : Prop :=
  Admissible idx e (quad p.1 p.2 q.1 q.2) ∧ Linked idx e (quad p.1 p.2 q.1 q.2)

instance (idx : D → O → L) (e : Fin 4 → Finset D) : DecidableRel (admRel idx e) := by
  unfold admRel; infer_instance

omit [DecidableEq O] in
theorem filter_admRel_row (idx : D → O → L) (e : Fin 4 → Finset D) (p : O × O) :
    (Finset.univ.filter fun q => admRel idx e p q) = admissiblePairs idx e p.1 p.2 := by
  ext q
  constructor
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2⟩
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2⟩

omit [DecidableEq O] in
/-- The column count equals a row count: exchanging the two pairs is the permutation
`pairSwap`, which preserves `Admissible` and `Linked`. -/
theorem filter_admRel_col (idx : D → O → L) (e : Fin 4 → Finset D) (q : O × O) :
    (Finset.univ.filter fun p => admRel idx e p q)
      = admissiblePairs idx (e ∘ (pairSwap : Fin 4 → Fin 4)) q.1 q.2 := by
  ext p
  have key : admRel idx (e ∘ (pairSwap : Fin 4 → Fin 4)) q p ↔ admRel idx e p q := by
    unfold admRel
    rw [(quad_comp_pairSwap p.1 p.2 q.1 q.2).symm, admissible_comp_iff, linked_pairSwap]
  constructor
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, key.mpr ((Finset.mem_filter.mp h).2)⟩
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, key.mp ((Finset.mem_filter.mp h).2)⟩

end Counting

/-! ## 5. The lemma -/

section Assembly

variable {Ω O : Type*} [Fintype O] [DecidableEq O]

/-- Two levels of at most `M` dimensions each give at most `2M` sites. -/
theorem pairCount_bound {a b G c M : ℕ} (ha : a ≤ M) (hb : b ≤ M) :
    2 * ((a + b) * G) * c ≤ 4 * M * G * c := by
  have h : a + b ≤ 2 * M := by omega
  calc 2 * ((a + b) * G) * c = (a + b) * (2 * G) * c := by ring
    _ ≤ 2 * M * (2 * G) * c :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h)
    _ = 4 * M * G * c := by ring

omit [DecidableEq O] in
/-- **Lemma SM.C.6**, with the admissibility relation abstract.

`hdecomp` expands each cumulant as a sum over a family `cc` indexed by `s`; `hsupp` says that
the cumulant of an assignment vanishes off its admissible quadruples, and `hbdd` bounds each
such cumulant by `K`. -/
theorem var_quadForm_le {Γ : Type*} (E : (Ω → ℝ) →ₗ[ℝ] ℝ) {W Om : Matrix O O ℝ}
    (hW : W.IsSymm) (hOm : Om.IsSymm) (z : O → Ω → ℝ)
    (hOmdef : ∀ o o', Om o o' = E (z o * z o'))
    (s : Finset Γ) (cc : Γ → O → O → O → O → ℝ)
    (hdecomp : ∀ o₁ o₂ o₃ o₄ : O,
      cum4 E (z o₁) (z o₂) (z o₃) (z o₄) = ∑ g ∈ s, cc g o₁ o₂ o₃ o₄)
    (Adm : Γ → (O × O) → (O × O) → Prop) [∀ g, DecidableRel (Adm g)]
    {K Λ : ℝ} (hK : 0 ≤ K)
    (hsupp : ∀ g ∈ s, ∀ p q : O × O, ¬ Adm g p q → cc g p.1 p.2 q.1 q.2 = 0)
    (hbdd : ∀ g ∈ s, ∀ p q : O × O, |cc g p.1 p.2 q.1 q.2| ≤ K)
    (hrow : ∀ g ∈ s, ∀ p : O × O,
      ((Finset.univ.filter fun q => Adm g p q).card : ℝ) ≤ Λ)
    (hcol : ∀ g ∈ s, ∀ q : O × O,
      ((Finset.univ.filter fun p => Adm g p q).card : ℝ) ≤ Λ) :
    varQuad E W z ≤ 2 * (W * Om * W * Om).trace + s.card * K * Λ * frobSq W := by
  have hfrob : (∑ p : O × O, (W p.1 p.2) ^ 2) = frobSq W := by
    rw [frobSq, Fintype.sum_prod_type]
  have hpair : kappaSum E W z
      = ∑ g ∈ s, ∑ p : O × O, ∑ q : O × O,
          W p.1 p.2 * W q.1 q.2 * cc g p.1 p.2 q.1 q.2 := by
    have h0 : kappaSum E W z
        = ∑ p : O × O, ∑ q : O × O,
            W p.1 p.2 * W q.1 q.2 * ∑ g ∈ s, cc g p.1 p.2 q.1 q.2 := by
      rw [kappaSum]
      simp only [Fintype.sum_prod_type, hdecomp]
    rw [h0]
    simp only [Finset.mul_sum]
    calc ∑ p : O × O, ∑ q : O × O, ∑ g ∈ s, W p.1 p.2 * W q.1 q.2 * cc g p.1 p.2 q.1 q.2
        = ∑ p : O × O, ∑ g ∈ s, ∑ q : O × O,
            W p.1 p.2 * W q.1 q.2 * cc g p.1 p.2 q.1 q.2 :=
          Finset.sum_congr rfl fun p _ => Finset.sum_comm
      _ = ∑ g ∈ s, ∑ p : O × O, ∑ q : O × O,
            W p.1 p.2 * W q.1 q.2 * cc g p.1 p.2 q.1 q.2 := Finset.sum_comm
  have hbound : |kappaSum E W z| ≤ s.card * K * Λ * frobSq W := by
    rw [hpair]
    calc |∑ g ∈ s, ∑ p : O × O, ∑ q : O × O, W p.1 p.2 * W q.1 q.2 * cc g p.1 p.2 q.1 q.2|
        ≤ ∑ g ∈ s, |∑ p : O × O, ∑ q : O × O,
            W p.1 p.2 * W q.1 q.2 * cc g p.1 p.2 q.1 q.2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _g ∈ s, K * Λ * ∑ p : O × O, (W p.1 p.2) ^ 2 := by
          refine Finset.sum_le_sum fun g hg => ?_
          exact abs_sum_pairs_le (α := O × O) (w := fun p => W p.1 p.2) (A := Adm g)
            (g := fun p q => cc g p.1 p.2 q.1 q.2) (K := K) (Λ := Λ) hK (hsupp g hg)
            (hbdd g hg) (hrow g hg) (hcol g hg)
      _ = s.card * K * Λ * frobSq W := by
          rw [Finset.sum_const, nsmul_eq_mul, hfrob]; ring
  have := (abs_le.mp hbound).2
  rw [varQuad_eq E hW hOm z hOmdef]
  linarith

/-- **Lemma SM.C.6**, with the site admissibility relation and constant
`s.card * K * (4 M G_max c_max)`. -/
theorem var_quadForm_le_sites {Γ D L : Type*} [DecidableEq D] [DecidableEq L] [Fintype D]
    (E : (Ω → ℝ) →ₗ[ℝ] ℝ) {W Om : Matrix O O ℝ} (hW : W.IsSymm) (hOm : Om.IsSymm)
    (z : O → Ω → ℝ) (hOmdef : ∀ o o', Om o o' = E (z o * z o'))
    (s : Finset Γ) (cc : Γ → O → O → O → O → ℝ)
    (hdecomp : ∀ o₁ o₂ o₃ o₄ : O,
      cum4 E (z o₁) (z o₂) (z o₃) (z o₄) = ∑ g ∈ s, cc g o₁ o₂ o₃ o₄)
    (idx : D → O → L) (e : Γ → Fin 4 → Finset D) {Gmax cmax : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (he : ∀ g ∈ s, ∀ i, 2 ≤ (e g i).card)
    (hG : ∀ (k : D) (o : O), (cellOf idx ({k} : Finset D) o).card ≤ Gmax)
    (hc : ∀ (A : Finset D) (o : O), 2 ≤ A.card → (cellOf idx A o).card ≤ cmax)
    (hsupp : ∀ g ∈ s, ∀ o₁ o₂ o₃ o₄ : O,
      ¬ (Admissible idx (e g) (quad o₁ o₂ o₃ o₄) ∧ Linked idx (e g) (quad o₁ o₂ o₃ o₄)) →
        cc g o₁ o₂ o₃ o₄ = 0)
    (hbdd : ∀ g ∈ s, ∀ o₁ o₂ o₃ o₄ : O, |cc g o₁ o₂ o₃ o₄| ≤ K) :
    varQuad E W z ≤ 2 * (W * Om * W * Om).trace
      + s.card * K * (4 * Fintype.card D * Gmax * cmax : ℕ) * frobSq W := by
  have hcardle : ∀ (g : Γ) (i : Fin 4), (e g i).card ≤ Fintype.card D := fun g i => by
    simpa using Finset.card_le_univ (e g i)
  have hrow : ∀ g ∈ s, ∀ p : O × O,
      ((Finset.univ.filter fun q => admRel idx (e g) p q).card : ℝ)
        ≤ (4 * Fintype.card D * Gmax * cmax : ℕ) := by
    intro g hg p
    rw [filter_admRel_row]
    have h1 := card_admissiblePairs_le idx (e g) p.1 p.2 (he g hg) hG hc
    have h2 := pairCount_bound (hcardle g 0) (hcardle g 1) (G := Gmax) (c := cmax)
    exact_mod_cast h1.trans h2
  have hcol : ∀ g ∈ s, ∀ q : O × O,
      ((Finset.univ.filter fun p => admRel idx (e g) p q).card : ℝ)
        ≤ (4 * Fintype.card D * Gmax * cmax : ℕ) := by
    intro g hg q
    rw [filter_admRel_col]
    have hes : ∀ i, 2 ≤ ((e g ∘ (pairSwap : Fin 4 → Fin 4)) i).card := fun i => he g hg _
    have h1 := card_admissiblePairs_le idx (e g ∘ (pairSwap : Fin 4 → Fin 4)) q.1 q.2 hes hG hc
    have h2 := pairCount_bound
      (a := ((e g ∘ (pairSwap : Fin 4 → Fin 4)) 0).card)
      (b := ((e g ∘ (pairSwap : Fin 4 → Fin 4)) 1).card)
      (hcardle g ((pairSwap : Fin 4 → Fin 4) 0)) (hcardle g ((pairSwap : Fin 4 → Fin 4) 1))
      (G := Gmax) (c := cmax)
    exact_mod_cast h1.trans h2
  exact var_quadForm_le E hW hOm z hOmdef s cc hdecomp (fun g => admRel idx (e g)) hK
    (fun g hg p q h => hsupp g hg p.1 p.2 q.1 q.2 h)
    (fun g hg p q => hbdd g hg p.1 p.2 q.1 q.2) hrow hcol

end Assembly

/-! ## 6. A witness

The hypotheses of `var_quadForm_le_sites` hold on a model with one observation, two
fixed-effect dimensions and a Rademacher variable under the uniform law on `Bool`. -/

section Witness

/-- The expectation under the uniform law on `Bool`, as a linear functional. -/
noncomputable def witE : (Bool → ℝ) →ₗ[ℝ] ℝ where
  toFun f := (f true + f false) / 2
  map_add' f g := by simp; ring
  map_smul' c f := by simp; ring

@[simp] theorem witE_apply (f : Bool → ℝ) : witE f = (f true + f false) / 2 := rfl

/-- A Rademacher variable, indexed by the single observation. -/
def witZ : Fin 1 → Bool → ℝ := fun _ b => if b then (1 : ℝ) else -1

@[simp] theorem witZ_true (o : Fin 1) : witZ o true = 1 := rfl
@[simp] theorem witZ_false (o : Fin 1) : witZ o false = -1 := rfl

theorem quadformE2_witness :
    varQuad witE (1 : Matrix (Fin 1) (Fin 1) ℝ) witZ
      ≤ 2 * ((1 : Matrix (Fin 1) (Fin 1) ℝ) * 1 * 1 * 1).trace
        + (({()} : Finset Unit).card : ℝ) * 2
          * (4 * Fintype.card (Fin 2) * 1 * 1 : ℕ)
          * frobSq (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  have hadm : ∀ (o : Fin 4 → Fin 1),
      Admissible (fun (_ : Fin 2) (_ : Fin 1) => ()) (fun _ => Finset.univ) o := by
    intro o i k _
    refine ⟨if i = 0 then 1 else 0, ?_, Finset.mem_univ _, rfl⟩
    by_cases h : i = 0
    · subst h; decide
    · have hz : (if i = 0 then (1 : Fin 4) else 0) = 0 := by simp [h]
      rw [hz]
      exact fun hh => h hh.symm
  have hlink : ∀ (o : Fin 4 → Fin 1),
      Linked (fun (_ : Fin 2) (_ : Fin 1) => ()) (fun _ => Finset.univ) o :=
    fun o => Or.inl ⟨0, Finset.mem_univ _, Finset.mem_univ _, rfl⟩
  refine var_quadForm_le_sites (Γ := Unit) (D := Fin 2) (L := Unit) witE
    Matrix.isSymm_one Matrix.isSymm_one witZ ?_ {()}
    (fun _ _ _ _ _ => -2) ?_ (fun _ _ => ()) (fun _ _ => Finset.univ)
    (by norm_num) ?_ ?_ ?_ ?_ ?_
  · intro o o'
    have ho : o = 0 := Subsingleton.elim _ _
    have ho' : o' = 0 := Subsingleton.elim _ _
    subst ho; subst ho'
    simp
  · intro o₁ o₂ o₃ o₄
    simp only [cum4, Finset.sum_singleton, witE_apply, Pi.mul_apply, witZ_true, witZ_false]
    norm_num
  · intro g _ i
    simp
  · intro k o
    exact le_trans (Finset.card_le_univ _) (by simp)
  · intro A o _
    exact le_trans (Finset.card_le_univ _) (by simp)
  · intro g _ o₁ o₂ o₃ o₄ h
    exact absurd ⟨hadm _, hlink _⟩ h
  · intro g _ o₁ o₂ o₃ o₄
    norm_num

end Witness

/-! ## 7. The `(2^M)⁴` aggregation

From the level decomposition `ζ_o = ∑_γ ξ^γ_o`, multilinearity expands each cumulant into a sum
over `Lv⁴` assignments, of which there are at most `(2^M)⁴`. -/

section Aggregation

variable {Ω O : Type*}

/-- The index set of assignments `(γ₁,γ₂,γ₃,γ₄)`. -/
def levelQuadruples {Γ₀ : Type*} (Lv : Finset Γ₀) : Finset (Γ₀ × Γ₀ × Γ₀ × Γ₀) :=
  Lv ×ˢ Lv ×ˢ Lv ×ˢ Lv

theorem mem_levelQuadruples {Γ₀ : Type*} {Lv : Finset Γ₀} {g : Γ₀ × Γ₀ × Γ₀ × Γ₀} :
    g ∈ levelQuadruples Lv ↔
      g.1 ∈ Lv ∧ g.2.1 ∈ Lv ∧ g.2.2.1 ∈ Lv ∧ g.2.2.2 ∈ Lv := by
  simp [levelQuadruples, Finset.mem_product]

/-- The number of assignments is `|Lv|⁴`. -/
theorem card_levelQuadruples {Γ₀ : Type*} (Lv : Finset Γ₀) :
    (levelQuadruples Lv).card = Lv.card ^ 4 := by
  simp only [levelQuadruples, Finset.card_product]
  ring

/-- If `|Lv| ≤ 2^M`, there are at most `(2^M)⁴` assignments. -/
theorem card_levelQuadruples_le {Γ₀ : Type*} (Lv : Finset Γ₀) {M : ℕ} (h : Lv.card ≤ 2 ^ M) :
    (levelQuadruples Lv).card ≤ (2 ^ M) ^ 4 := by
  rw [card_levelQuadruples]
  exact Nat.pow_le_pow_left h 4

/-- The cumulant of a single assignment, `cum(ξ^{γ₁}_{o₁},…,ξ^{γ₄}_{o₄})`. -/
def assignCum (E : (Ω → ℝ) →ₗ[ℝ] ℝ) {Γ₀ : Type*} (xi : Γ₀ → O → Ω → ℝ)
    (g : Γ₀ × Γ₀ × Γ₀ × Γ₀) (o₁ o₂ o₃ o₄ : O) : ℝ :=
  cum4 E (xi g.1 o₁) (xi g.2.1 o₂) (xi g.2.2.1 o₃) (xi g.2.2.2 o₄)

/-- The multilinear expansion of `cum₄(ζ_{o₁},…,ζ_{o₄})` over `Lv⁴`, from the level
decomposition `hz`. -/
theorem cum4_levelExpansion (E : (Ω → ℝ) →ₗ[ℝ] ℝ) {Γ₀ : Type*} (Lv : Finset Γ₀)
    (xi : Γ₀ → O → Ω → ℝ) (z : O → Ω → ℝ) (hz : ∀ o, z o = ∑ γ ∈ Lv, xi γ o)
    (o₁ o₂ o₃ o₄ : O) :
    cum4 E (z o₁) (z o₂) (z o₃) (z o₄)
      = ∑ g ∈ levelQuadruples Lv, assignCum E xi g o₁ o₂ o₃ o₄ := by
  rw [hz o₁, hz o₂, hz o₃, hz o₄, cum4_sum_one]
  simp only [cum4_sum_two]
  simp only [cum4_sum_three]
  simp only [cum4_sum_four]
  rw [levelQuadruples]
  simp only [Finset.sum_product, assignCum]

/-- The level sets `(e₁,e₂,e₃,e₄)` of the four arguments under a given assignment. -/
def assignLevels {Γ₀ D : Type*} (lev : Γ₀ → Finset D) (g : Γ₀ × Γ₀ × Γ₀ × Γ₀) :
    Fin 4 → Finset D :=
  fun i => lev (quad g.1 g.2.1 g.2.2.1 g.2.2.2 i)

/-- With no fixed-effect dimension, the condition `2 ≤ |e_γ|` forces `Lv` to be empty. -/
theorem levels_eq_empty_of_isEmpty {Γ₀ D : Type*} [IsEmpty D] {Lv : Finset Γ₀}
    {lev : Γ₀ → Finset D} (he : ∀ γ ∈ Lv, 2 ≤ (lev γ).card) : Lv = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr fun γ hγ => ?_
  have h := he γ hγ
  rw [Finset.eq_empty_of_isEmpty (lev γ)] at h
  simp at h

variable [Fintype O] [DecidableEq O]

/-- **Lemma SM.C.6**, from the level decomposition `hz : ζ_o = ∑_γ ξ^γ_o`, with constant
`(2^M)⁴ · K · 4M G_max c_max`.

`hLv` and `he` say the levels are subsets of `{1,…,M}` of size at least two, together with the
symbol `ε`; `hG` and `hc` bound the category and cell sizes by `G_max` and `c_max`; `hsupp` and
`hbdd` are the vanishing and boundedness of the assignment cumulants (supplied in
`Multiway.QuadformE2Indep`). -/
theorem var_quadForm_le_levels {Γ₀ D L : Type*} [DecidableEq D] [DecidableEq L] [Fintype D]
    (E : (Ω → ℝ) →ₗ[ℝ] ℝ) {W Om : Matrix O O ℝ} (hW : W.IsSymm) (hOm : Om.IsSymm)
    (z : O → Ω → ℝ) (hOmdef : ∀ o o', Om o o' = E (z o * z o'))
    (Lv : Finset Γ₀) (xi : Γ₀ → O → Ω → ℝ) (hz : ∀ o, z o = ∑ γ ∈ Lv, xi γ o)
    (lev : Γ₀ → Finset D) (idx : D → O → L) {Gmax cmax : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (hLv : Lv.card ≤ 2 ^ Fintype.card D)
    (he : ∀ γ ∈ Lv, 2 ≤ (lev γ).card)
    (hG : ∀ (k : D) (o : O), (cellOf idx ({k} : Finset D) o).card ≤ Gmax)
    (hc : ∀ (A : Finset D) (o : O), 2 ≤ A.card → (cellOf idx A o).card ≤ cmax)
    (hsupp : ∀ g ∈ levelQuadruples Lv, ∀ o₁ o₂ o₃ o₄ : O,
      ¬ (Admissible idx (assignLevels lev g) (quad o₁ o₂ o₃ o₄)
          ∧ Linked idx (assignLevels lev g) (quad o₁ o₂ o₃ o₄)) →
        assignCum E xi g o₁ o₂ o₃ o₄ = 0)
    (hbdd : ∀ g ∈ levelQuadruples Lv, ∀ o₁ o₂ o₃ o₄ : O,
      |assignCum E xi g o₁ o₂ o₃ o₄| ≤ K) :
    varQuad E W z ≤ 2 * (W * Om * W * Om).trace
      + ((2 ^ Fintype.card D) ^ 4 : ℕ) * K
          * (4 * Fintype.card D * Gmax * cmax : ℕ) * frobSq W := by
  have he' : ∀ g ∈ levelQuadruples Lv, ∀ i, 2 ≤ (assignLevels lev g i).card := by
    intro g hg i
    rw [mem_levelQuadruples] at hg
    fin_cases i
    · simp only [assignLevels]; exact he _ hg.1
    · simp only [assignLevels]; exact he _ hg.2.1
    · simp only [assignLevels]; exact he _ hg.2.2.1
    · simp only [assignLevels]; exact he _ hg.2.2.2
  have hmain := var_quadForm_le_sites (Γ := Γ₀ × Γ₀ × Γ₀ × Γ₀) E hW hOm z hOmdef
    (levelQuadruples Lv) (assignCum E xi) (cum4_levelExpansion E Lv xi z hz)
    idx (assignLevels lev) hK he' hG hc hsupp hbdd
  refine hmain.trans ?_
  have hfrob : 0 ≤ frobSq W := by
    rw [frobSq]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hLam : (0:ℝ) ≤ ((4 * Fintype.card D * Gmax * cmax : ℕ) : ℝ) := Nat.cast_nonneg _
  have hpos : (0:ℝ) ≤ K * ((4 * Fintype.card D * Gmax * cmax : ℕ) : ℝ) * frobSq W :=
    mul_nonneg (mul_nonneg hK hLam) hfrob
  have hcard : (((levelQuadruples Lv).card : ℕ) : ℝ) ≤ (((2 ^ Fintype.card D) ^ 4 : ℕ) : ℝ) := by
    exact_mod_cast card_levelQuadruples_le Lv hLv
  have hstep :
      ((levelQuadruples Lv).card : ℝ) * K * ((4 * Fintype.card D * Gmax * cmax : ℕ) : ℝ)
            * frobSq W
        ≤ (((2 ^ Fintype.card D) ^ 4 : ℕ) : ℝ) * K
            * ((4 * Fintype.card D * Gmax * cmax : ℕ) : ℝ) * frobSq W := by
    calc ((levelQuadruples Lv).card : ℝ) * K
            * ((4 * Fintype.card D * Gmax * cmax : ℕ) : ℝ) * frobSq W
        = ((levelQuadruples Lv).card : ℝ)
            * (K * ((4 * Fintype.card D * Gmax * cmax : ℕ) : ℝ) * frobSq W) := by ring
      _ ≤ (((2 ^ Fintype.card D) ^ 4 : ℕ) : ℝ)
            * (K * ((4 * Fintype.card D * Gmax * cmax : ℕ) : ℝ) * frobSq W) :=
          mul_le_mul_of_nonneg_right hcard hpos
      _ = (((2 ^ Fintype.card D) ^ 4 : ℕ) : ℝ) * K
            * ((4 * Fintype.card D * Gmax * cmax : ℕ) : ℝ) * frobSq W := by ring
  linarith

end Aggregation

/-! ## 8. Conditional expectation on a finite space

Mathlib's `condExp` is linear only almost everywhere, so it does not give a linear functional
at a fixed point. On a finite sample space with `𝒟` generated by a partition, `E[· ∣ 𝒟](ω₀)` is
a linear functional on all of `Ω → ℝ`; `condAvg` is this object. -/

section CondExp

/-- `E[· ∣ 𝒟](ω₀)` on a finite sample space, where `A` is the atom containing `ω₀`: the
`p`-weighted average over `A`. -/
noncomputable def condAvg {Ω : Type*} (p : Ω → ℝ) (A : Finset Ω) : (Ω → ℝ) →ₗ[ℝ] ℝ where
  toFun f := (∑ ω ∈ A, p ω * f ω) / (∑ ω ∈ A, p ω)
  map_add' f g := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' c f := by
    have h : ∀ ω, p ω * (c • f) ω = c * (p ω * f ω) := by
      intro ω
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    simp only [h, ← Finset.mul_sum, RingHom.id_apply, smul_eq_mul]
    ring

@[simp] theorem condAvg_apply {Ω : Type*} (p : Ω → ℝ) (A : Finset Ω) (f : Ω → ℝ) :
    condAvg p A f = (∑ ω ∈ A, p ω * f ω) / (∑ ω ∈ A, p ω) := rfl

/-- The defining property of a conditional expectation on the atom:
`∫_A f = P(A)·E[f∣𝒟]`. -/
theorem condAvg_defining {Ω : Type*} (p : Ω → ℝ) (A : Finset Ω)
    (hA : (∑ ω ∈ A, p ω) ≠ 0) (f : Ω → ℝ) :
    (∑ ω ∈ A, p ω) * condAvg p A f = ∑ ω ∈ A, p ω * f ω := by
  rw [condAvg_apply, mul_div_cancel₀ _ hA]

/-- `E[1 ∣ 𝒟] = 1`. -/
theorem condAvg_one {Ω : Type*} (p : Ω → ℝ) (A : Finset Ω)
    (hA : (∑ ω ∈ A, p ω) ≠ 0) : condAvg p A 1 = 1 := by
  rw [condAvg_apply]
  simp [div_self hA]

/-- The functional `witE` is `condAvg` at the trivial σ-algebra under the uniform law. -/
theorem witE_eq_condAvg : witE = condAvg (fun _ : Bool => (1:ℝ)/2) Finset.univ := by
  ext f
  simp
  ring

end CondExp

/-! ## 9. A witness at a nontrivial conditional expectation

The hypotheses of `var_quadForm_le_levels` hold on a model with one observation, `M = 2`,
`Ω = Bool × Bool` under the uniform law and `𝒟 = σ(first coordinate)` realized at
`ω₁ = true`. The variable has conditional mean zero but unconditional mean `3/2`, and its fourth
cumulant is `-2`. -/

section WitnessCond

/-- The conditioning atom: `𝒟 = σ(first coordinate)`, realized at `ω₁ = true`. -/
def witAtom : Finset (Bool × Bool) := {(true, true), (true, false)}

/-- `E[· ∣ 𝒟]` along that realization, under the uniform law on `Bool × Bool`. -/
noncomputable def witE₂ : ((Bool × Bool) → ℝ) →ₗ[ℝ] ℝ :=
  condAvg (fun _ => (1:ℝ)/4) witAtom

@[simp] theorem witE₂_apply (f : (Bool × Bool) → ℝ) :
    witE₂ f = (f (true, true) + f (true, false)) / 2 := by
  rw [witE₂, condAvg_apply, witAtom,
    Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- A variable that is Rademacher **on the atom** and constant `3` off it. -/
def witZ₂ : Fin 1 → (Bool × Bool) → ℝ :=
  fun _ ω => if ω.1 then (if ω.2 then (1:ℝ) else -1) else 3

/-- On the realized atom the variable has conditional mean zero. -/
theorem witZ₂_condMean : witE₂ (witZ₂ 0) = 0 := by
  simp [witZ₂]

/-- The unconditional mean of the variable is `3/2`. -/
theorem witZ₂_uncondMean :
    condAvg (fun _ : Bool × Bool => (1:ℝ)/4) Finset.univ (witZ₂ 0) = 3/2 := by
  simp [witZ₂, Fintype.sum_prod_type]
  norm_num

/-- The fourth cumulant of the variable is `-2`. -/
theorem witness_cum4 : cum4 witE₂ (witZ₂ 0) (witZ₂ 0) (witZ₂ 0) (witZ₂ 0) = -2 := by
  simp only [cum4, witE₂_apply, Pi.mul_apply, witZ₂]
  norm_num

theorem quadformE2_witness_levels :
    varQuad witE₂ (1 : Matrix (Fin 1) (Fin 1) ℝ) witZ₂
      ≤ 2 * ((1 : Matrix (Fin 1) (Fin 1) ℝ) * 1 * 1 * 1).trace
        + ((2 ^ Fintype.card (Fin 2)) ^ 4 : ℕ) * 2
          * (4 * Fintype.card (Fin 2) * 1 * 1 : ℕ)
          * frobSq (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  have hadm : ∀ (o : Fin 4 → Fin 1),
      Admissible (fun (_ : Fin 2) (_ : Fin 1) => ()) (fun _ => Finset.univ) o := by
    intro o i k _
    refine ⟨if i = 0 then 1 else 0, ?_, Finset.mem_univ _, rfl⟩
    by_cases h : i = 0
    · subst h; decide
    · have hz : (if i = 0 then (1 : Fin 4) else 0) = 0 := by simp [h]
      rw [hz]
      exact fun hh => h hh.symm
  have hlink : ∀ (o : Fin 4 → Fin 1),
      Linked (fun (_ : Fin 2) (_ : Fin 1) => ()) (fun _ => Finset.univ) o :=
    fun o => Or.inl ⟨0, Finset.mem_univ _, Finset.mem_univ _, rfl⟩
  refine var_quadForm_le_levels (Γ₀ := Unit) (D := Fin 2) (L := Unit)
    (K := 2) (Gmax := 1) (cmax := 1) witE₂ Matrix.isSymm_one Matrix.isSymm_one witZ₂ ?_
    {()} (fun _ => witZ₂) ?_ (fun _ => Finset.univ) (fun _ _ => ()) (by norm_num) ?_ ?_ ?_ ?_
    ?_ ?_
  · intro o o'
    have ho : o = 0 := Subsingleton.elim _ _
    have ho' : o' = 0 := Subsingleton.elim _ _
    subst ho; subst ho'
    simp [witZ₂]
  · intro o
    simp
  · simp
  · intro γ _
    simp
  · intro k o
    exact le_trans (Finset.card_le_univ _) (by simp)
  · intro A o _
    exact le_trans (Finset.card_le_univ _) (by simp)
  · intro g _ o₁ o₂ o₃ o₄ h
    exact absurd ⟨hadm _, hlink _⟩ h
  · intro g _ o₁ o₂ o₃ o₄
    simp only [assignCum, cum4, witE₂_apply, Pi.mul_apply, witZ₂]
    norm_num

end WitnessCond

end QuadformE2
end Multiway
