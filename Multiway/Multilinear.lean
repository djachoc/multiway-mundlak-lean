import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Fourth moments of bounded multilinear forms

This file formalizes Lemma SM.C.4 of the paper (fourth moments of bounded multilinear forms):
if `{ξ^{(k)}_i : k ≤ j, i ∈ I_k}` are independent, centred and bounded by `B` almost surely,
and `Z := ∑_s a_s ∏_k ξ^{(k)}_{s_k}` with nonrandom coefficients, then
`E[Z⁴] ≤ (3B⁴)^j (∑_s a_s²)²`. The proof adds one independent summand at a time, using
`E[(S + T)⁴] = E[S⁴] + 6 E[S²] E[T²] + E[T⁴]` for independent centred `S`, `T`. The random
coefficients that arise in the induction on `j` are handled by independence.

## Main results

* `integral_pow_four_sum_le`: `E[(∑ᵢYᵢ)⁴] ≤ 3(∑ᵢvᵢ)²` for independent centred `Yᵢ` with
  `E[Yᵢ²] ≤ vᵢ` and `E[Yᵢ⁴] ≤ 3vᵢ²`.
* `integral_pow_four_linear_le`: the case `j = 1`.
* `integral_pow_four_random_le`: `E[(∑ᵢ Zᵢξᵢ)⁴] ≤ 3B⁴ E[(∑ᵢ Zᵢ²)²]` for background-measurable
  coefficients `Zᵢ`.
* `integral_sq_sum_sq_le`: `E[(∑ᵢZᵢ²)²] ≤ (∑ᵢ(E[Zᵢ⁴])^{1/2})²`.
* `integral_pow_four_multilinear_le`: Lemma SM.C.4 for every `j`.
-/

namespace Multiway
namespace Multilinear

open MeasureTheory ProbabilityTheory

-- `m₀` is declared before `mΩ`, so that an unannotated `Measurable` refers to the ambient
-- σ-algebra.
variable {Ω : Type*} {m₀ mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Bounded measurable functions -/

/-- A measurable function bounded almost everywhere by a constant is integrable against a
finite measure. -/
lemma integrable_of_abs_le [IsFiniteMeasure μ] {f : Ω → ℝ} {C : ℝ}
    (hf : Measurable f) (hC : ∀ᵐ ω ∂μ, |f ω| ≤ C) : Integrable f μ := by
  refine (integrable_const C).mono' hf.aestronglyMeasurable ?_
  filter_upwards [hC] with ω hω
  simpa [Real.norm_eq_abs] using hω

/-- A constant that bounds `|f|` almost everywhere is nonnegative, provided the measure is not
the zero measure. -/
lemma nonneg_of_abs_le [IsProbabilityMeasure μ] {f : Ω → ℝ} {C : ℝ}
    (hC : ∀ᵐ ω ∂μ, |f ω| ≤ C) : 0 ≤ C := by
  obtain ⟨ω, hω⟩ := hC.exists
  exact (abs_nonneg _).trans hω

/-- `E[f^n] ≤ C^n` for an even exponent, from `|f| ≤ C` almost surely. -/
lemma integral_pow_le_of_abs_le [IsProbabilityMeasure μ] {f : Ω → ℝ} {C : ℝ} {n : ℕ}
    (hn : Even n) (hf : Measurable f) (hC : ∀ᵐ ω ∂μ, |f ω| ≤ C) :
    ∫ ω, f ω ^ n ∂μ ≤ C ^ n := by
  have hpt : ∀ᵐ ω ∂μ, f ω ^ n ≤ C ^ n := by
    filter_upwards [hC] with ω hω
    calc f ω ^ n = |f ω| ^ n := (hn.pow_abs _).symm
      _ ≤ C ^ n := pow_le_pow_left₀ (abs_nonneg _) hω n
  have hint : Integrable (fun ω => f ω ^ n) μ := by
    refine integrable_of_abs_le (hf.pow_const n) (C := C ^ n) ?_
    filter_upwards [hC] with ω hω
    calc |f ω ^ n| = |f ω| ^ n := by rw [abs_pow]
      _ ≤ C ^ n := pow_le_pow_left₀ (abs_nonneg _) hω n
  calc ∫ ω, f ω ^ n ∂μ ≤ ∫ _ω, C ^ n ∂μ := integral_mono_ae hint (integrable_const _) hpt
    _ = C ^ n := by simp

/-! ### Monomials in two independent factors -/

/-- `S^p T^q` is integrable when both factors are measurable and almost surely bounded. -/
lemma integrable_monomial [IsProbabilityMeasure μ] {S T : Ω → ℝ} {cS cT : ℝ}
    (hSm : Measurable S) (hTm : Measurable T)
    (hSb : ∀ᵐ ω ∂μ, |S ω| ≤ cS) (hTb : ∀ᵐ ω ∂μ, |T ω| ≤ cT) (p q : ℕ) :
    Integrable (fun ω => S ω ^ p * T ω ^ q) μ := by
  have hcS : 0 ≤ cS := nonneg_of_abs_le hSb
  refine integrable_of_abs_le ((hSm.pow_const p).mul (hTm.pow_const q))
    (C := cS ^ p * cT ^ q) ?_
  filter_upwards [hSb, hTb] with ω h1 h2
  rw [abs_mul, abs_pow, abs_pow]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h1 p)
    (pow_le_pow_left₀ (abs_nonneg _) h2 q) (pow_nonneg (abs_nonneg _) q) (pow_nonneg hcS p)

/-- `E[S^p T^q] = E[S^p] E[T^q]` when `S` and `T` are independent. -/
lemma integral_monomial_eq [IsProbabilityMeasure μ] {S T : Ω → ℝ}
    (hind : IndepFun S T μ) (hSm : Measurable S) (hTm : Measurable T) (p q : ℕ) :
    ∫ ω, S ω ^ p * T ω ^ q ∂μ = (∫ ω, S ω ^ p ∂μ) * ∫ ω, T ω ^ q ∂μ := by
  have hI : IndepFun (fun ω => S ω ^ p) (fun ω => T ω ^ q) μ :=
    hind.comp (measurable_id.pow_const p) (measurable_id.pow_const q)
  exact hI.integral_fun_mul_eq_mul_integral (hSm.pow_const p).aestronglyMeasurable
    (hTm.pow_const q).aestronglyMeasurable

/-! ### The two induction steps -/

/-- If `S` and `T` are independent and centred, then `E[(S + T)²] = E[S²] + E[T²]`. -/
lemma integral_sq_add_le [IsProbabilityMeasure μ] {S T : Ω → ℝ} {cS cT vS vT : ℝ}
    (hind : IndepFun S T μ) (hSm : Measurable S) (hTm : Measurable T)
    (hSb : ∀ᵐ ω ∂μ, |S ω| ≤ cS) (hTb : ∀ᵐ ω ∂μ, |T ω| ≤ cT)
    (hT1 : ∫ ω, T ω ∂μ = 0)
    (hS2 : ∫ ω, S ω ^ 2 ∂μ ≤ vS) (hT2 : ∫ ω, T ω ^ 2 ∂μ ≤ vT) :
    ∫ ω, (S ω + T ω) ^ 2 ∂μ ≤ vS + vT := by
  have hint : ∀ p q : ℕ, Integrable (fun ω => S ω ^ p * T ω ^ q) μ :=
    fun p q => integrable_monomial hSm hTm hSb hTb p q
  have hfact := integral_monomial_eq hind hSm hTm
  have hpow0 : ∀ f : Ω → ℝ, ∫ ω, f ω ^ 0 ∂μ = 1 := by intro f; simp
  have hT1' : ∫ ω, T ω ^ 1 ∂μ = 0 := by simpa using hT1
  have hexp : ∫ ω, (S ω + T ω) ^ 2 ∂μ
      = ∫ ω, (S ω ^ 2 * T ω ^ 0 + (2 * (S ω ^ 1 * T ω ^ 1) + S ω ^ 0 * T ω ^ 2)) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with ω
    ring
  have i1 := hint 2 0
  have i2 := (hint 1 1).const_mul 2
  have i3 := hint 0 2
  rw [hexp, integral_add i1 (i2.fun_add i3), integral_add i2 i3, integral_const_mul,
    hfact 2 0, hfact 1 1, hfact 0 2, hT1', hpow0 S, hpow0 T]
  simp only [mul_zero, mul_one, one_mul, zero_add]
  linarith

/-- The fourth-moment step. Expanding `(S + T)⁴` and factorizing by independence,
`E[(S+T)⁴] = E[S⁴] + 4E[S³]E[T] + 6E[S²]E[T²] + 4E[S]E[T³] + E[T⁴]`; the odd cross terms
vanish, and the rest is bounded by `3vS² + 6 vS vT + 3vT² = 3(vS + vT)²`. -/
lemma integral_pow_four_add_le [IsProbabilityMeasure μ] {S T : Ω → ℝ} {cS cT vS vT : ℝ}
    (hind : IndepFun S T μ) (hSm : Measurable S) (hTm : Measurable T)
    (hSb : ∀ᵐ ω ∂μ, |S ω| ≤ cS) (hTb : ∀ᵐ ω ∂μ, |T ω| ≤ cT)
    (hS1 : ∫ ω, S ω ∂μ = 0) (hT1 : ∫ ω, T ω ∂μ = 0)
    (hS2 : ∫ ω, S ω ^ 2 ∂μ ≤ vS) (hT2 : ∫ ω, T ω ^ 2 ∂μ ≤ vT)
    (hS4 : ∫ ω, S ω ^ 4 ∂μ ≤ 3 * vS ^ 2) (hT4 : ∫ ω, T ω ^ 4 ∂μ ≤ 3 * vT ^ 2) :
    ∫ ω, (S ω + T ω) ^ 4 ∂μ ≤ 3 * (vS + vT) ^ 2 := by
  have hint : ∀ p q : ℕ, Integrable (fun ω => S ω ^ p * T ω ^ q) μ :=
    fun p q => integrable_monomial hSm hTm hSb hTb p q
  have hfact := integral_monomial_eq hind hSm hTm
  have hpow0 : ∀ f : Ω → ℝ, ∫ ω, f ω ^ 0 ∂μ = 1 := by intro f; simp
  have hS1' : ∫ ω, S ω ^ 1 ∂μ = 0 := by simpa using hS1
  have hT1' : ∫ ω, T ω ^ 1 ∂μ = 0 := by simpa using hT1
  have h2S : (0 : ℝ) ≤ ∫ ω, S ω ^ 2 ∂μ := integral_nonneg fun ω => by positivity
  have h2T : (0 : ℝ) ≤ ∫ ω, T ω ^ 2 ∂μ := integral_nonneg fun ω => by positivity
  have hvS : (0 : ℝ) ≤ vS := h2S.trans hS2
  have hmul : (∫ ω, S ω ^ 2 ∂μ) * (∫ ω, T ω ^ 2 ∂μ) ≤ vS * vT :=
    mul_le_mul hS2 hT2 h2T hvS
  have hexp : ∫ ω, (S ω + T ω) ^ 4 ∂μ
      = ∫ ω, (S ω ^ 4 * T ω ^ 0 + (4 * (S ω ^ 3 * T ω ^ 1)
          + (6 * (S ω ^ 2 * T ω ^ 2) + (4 * (S ω ^ 1 * T ω ^ 3) + S ω ^ 0 * T ω ^ 4)))) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with ω
    ring
  have i1 := hint 4 0
  have i2 := (hint 3 1).const_mul 4
  have i3 := (hint 2 2).const_mul 6
  have i4 := (hint 1 3).const_mul 4
  have i5 := hint 0 4
  rw [hexp, integral_add i1 (i2.fun_add (i3.fun_add (i4.fun_add i5))),
    integral_add i2 (i3.fun_add (i4.fun_add i5)),
    integral_add i3 (i4.fun_add i5), integral_add i4 i5,
    integral_const_mul, integral_const_mul, integral_const_mul,
    hfact 4 0, hfact 3 1, hfact 2 2, hfact 1 3, hfact 0 4, hS1', hT1', hpow0 S, hpow0 T]
  simp only [mul_zero, zero_mul, mul_one, one_mul, zero_add]
  nlinarith [hS4, hT4, hmul]

/-! ### Fourth moments of a sum of independent centred variables -/

section Engine

variable {ι : Type*} {Y : ι → Ω → ℝ} {c v : ι → ℝ}

/-- If `|Yᵢ| ≤ cᵢ` almost surely for every `i`, then `|∑_{i ∈ F} Yᵢ| ≤ ∑_{i ∈ F} cᵢ` almost
surely. -/
lemma abs_sum_le_of_abs_le (hbdd : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ c i) (F : Finset ι) :
    ∀ᵐ ω ∂μ, |∑ i ∈ F, Y i ω| ≤ ∑ i ∈ F, c i := by
  classical
  induction F using Finset.induction_on with
  | empty => filter_upwards with ω; simp
  | @insert a F ha ih =>
    filter_upwards [hbdd a, ih] with ω h1 h2
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- A finite sum of centred summands is centred. -/
lemma integral_sum_eq_zero [IsProbabilityMeasure μ]
    (hmeasY : ∀ i, Measurable (Y i)) (hbdd : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ c i)
    (hmean : ∀ i, ∫ ω, Y i ω ∂μ = 0) (F : Finset ι) :
    ∫ ω, (∑ i ∈ F, Y i ω) ∂μ = 0 := by
  rw [integral_finsetSum _ fun i _ => integrable_of_abs_le (hmeasY i) (hbdd i)]
  simp [hmean]

/-- Independence of a partial sum from a summand outside it. -/
lemma indepFun_sum_of_notMem (hindep : iIndepFun Y μ) (hmeasY : ∀ i, Measurable (Y i))
    {F : Finset ι} {a : ι} (ha : a ∉ F) :
    IndepFun (fun ω => ∑ i ∈ F, Y i ω) (Y a) μ := by
  have h := hindep.indepFun_finsetSum_of_notMem hmeasY ha
  have e : (∑ j ∈ F, Y j) = fun ω => ∑ i ∈ F, Y i ω := by funext ω; simp
  rwa [e] at h

/-- Second moments of a sum of independent centred variables: `E[(∑ᵢYᵢ)²] ≤ ∑ᵢvᵢ`. -/
lemma integral_sq_sum_le [IsProbabilityMeasure μ] (hindep : iIndepFun Y μ)
    (hmeasY : ∀ i, Measurable (Y i)) (hbdd : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ c i)
    (hmean : ∀ i, ∫ ω, Y i ω ∂μ = 0) (hsq : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ ≤ v i)
    (F : Finset ι) :
    ∫ ω, (∑ i ∈ F, Y i ω) ^ 2 ∂μ ≤ ∑ i ∈ F, v i := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a F ha ih =>
    have hrw : ∫ ω, (∑ i ∈ insert a F, Y i ω) ^ 2 ∂μ
        = ∫ ω, ((∑ i ∈ F, Y i ω) + Y a ω) ^ 2 ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards with ω
      rw [Finset.sum_insert ha]
      ring
    rw [hrw, Finset.sum_insert ha, add_comm (v a) _]
    exact integral_sq_add_le (indepFun_sum_of_notMem hindep hmeasY ha)
      (Finset.measurable_sum F fun i _ => hmeasY i) (hmeasY a)
      (abs_sum_le_of_abs_le hbdd F) (hbdd a) (hmean a) ih (hsq a)

/-- **Fourth moments of a sum of independent, centred random variables.** If the `Yᵢ` are
independent with `E[Yᵢ] = 0`, `E[Yᵢ²] ≤ vᵢ` and `E[Yᵢ⁴] ≤ 3vᵢ²`, then
`E[(∑ᵢYᵢ)⁴] ≤ 3(∑ᵢvᵢ)²`. -/
theorem integral_pow_four_sum_le [IsProbabilityMeasure μ] (hindep : iIndepFun Y μ)
    (hmeasY : ∀ i, Measurable (Y i)) (hbdd : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ c i)
    (hmean : ∀ i, ∫ ω, Y i ω ∂μ = 0) (hsq : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ ≤ v i)
    (hfour : ∀ i, ∫ ω, Y i ω ^ 4 ∂μ ≤ 3 * v i ^ 2) (F : Finset ι) :
    ∫ ω, (∑ i ∈ F, Y i ω) ^ 4 ∂μ ≤ 3 * (∑ i ∈ F, v i) ^ 2 := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a F ha ih =>
    have hrw : ∫ ω, (∑ i ∈ insert a F, Y i ω) ^ 4 ∂μ
        = ∫ ω, ((∑ i ∈ F, Y i ω) + Y a ω) ^ 4 ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards with ω
      rw [Finset.sum_insert ha]
      ring
    rw [hrw, Finset.sum_insert ha, add_comm (v a) _]
    exact integral_pow_four_add_le (indepFun_sum_of_notMem hindep hmeasY ha)
      (Finset.measurable_sum F fun i _ => hmeasY i) (hmeasY a)
      (abs_sum_le_of_abs_le hbdd F) (hbdd a)
      (integral_sum_eq_zero hmeasY hbdd hmean F) (hmean a)
      (integral_sq_sum_le hindep hmeasY hbdd hmean hsq F) (hsq a)
      ih (hfour a)

end Engine

/-! ### The case `j = 1` -/

section LevelOne

variable {ι : Type*} {ξ : ι → Ω → ℝ} {a : ι → ℝ} {B : ℝ}

/-- **Lemma SM.C.4**, the case `j = 1`: for independent centred `ξᵢ` with `|ξᵢ| ≤ B` almost
surely and nonrandom coefficients `aᵢ`, `E[(∑ᵢ aᵢξᵢ)⁴] ≤ 3B⁴(∑ᵢ aᵢ²)²`. The index type is
arbitrary and the index set `F` may be empty; `0 ≤ B` is not assumed. -/
theorem integral_pow_four_linear_le [IsProbabilityMeasure μ] (hindep : iIndepFun ξ μ)
    (hmeas : ∀ i, Measurable (ξ i)) (hmean : ∀ i, ∫ ω, ξ i ω ∂μ = 0)
    (hbdd : ∀ i, ∀ᵐ ω ∂μ, |ξ i ω| ≤ B) (F : Finset ι) :
    ∫ ω, (∑ i ∈ F, a i * ξ i ω) ^ 4 ∂μ ≤ 3 * B ^ 4 * (∑ i ∈ F, a i ^ 2) ^ 2 := by
  -- the summands and the variance proxies `vᵢ = aᵢ²B²`
  set Y : ι → Ω → ℝ := fun i ω => a i * ξ i ω with hY
  have hmeasY : ∀ i, Measurable (Y i) := fun i => (hmeas i).const_mul (a i)
  have hindepY : iIndepFun Y μ :=
    hindep.comp (fun i x => a i * x) fun i => measurable_id.const_mul (a i)
  have hbddY : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ |a i| * B := by
    intro i
    filter_upwards [hbdd i] with ω hω
    rw [hY, abs_mul]
    exact mul_le_mul_of_nonneg_left hω (abs_nonneg _)
  have hmeanY : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i
    rw [hY]
    simp [integral_const_mul, hmean i]
  have hsqY : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ ≤ a i ^ 2 * B ^ 2 := by
    intro i
    have hxi : ∫ ω, ξ i ω ^ 2 ∂μ ≤ B ^ 2 :=
      integral_pow_le_of_abs_le (by decide) (hmeas i) (hbdd i)
    have he : ∫ ω, Y i ω ^ 2 ∂μ = a i ^ 2 * ∫ ω, ξ i ω ^ 2 ∂μ := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards with ω
      rw [hY]
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hxi (sq_nonneg _)
  have hfourY : ∀ i, ∫ ω, Y i ω ^ 4 ∂μ ≤ 3 * (a i ^ 2 * B ^ 2) ^ 2 := by
    intro i
    have hxi : ∫ ω, ξ i ω ^ 4 ∂μ ≤ B ^ 4 :=
      integral_pow_le_of_abs_le (by decide) (hmeas i) (hbdd i)
    have he : ∫ ω, Y i ω ^ 4 ∂μ = a i ^ 4 * ∫ ω, ξ i ω ^ 4 ∂μ := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards with ω
      rw [hY]
      ring
    have h4 : (0 : ℝ) ≤ a i ^ 4 := by positivity
    have hB4 : (0 : ℝ) ≤ B ^ 4 := by positivity
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hxi h4]
  have hmain := integral_pow_four_sum_le hindepY hmeasY hbddY hmeanY hsqY hfourY F
  have hsum : ∑ i ∈ F, a i ^ 2 * B ^ 2 = (∑ i ∈ F, a i ^ 2) * B ^ 2 := by
    rw [← Finset.sum_mul]
  rw [hsum] at hmain
  calc ∫ ω, (∑ i ∈ F, a i * ξ i ω) ^ 4 ∂μ ≤ 3 * ((∑ i ∈ F, a i ^ 2) * B ^ 2) ^ 2 := hmain
    _ = 3 * B ^ 4 * (∑ i ∈ F, a i ^ 2) ^ 2 := by ring

end LevelOne

/-! ### Random coefficients

The `j = 1` bound extends to coefficients `Zᵢ` measurable with respect to a background
σ-algebra `m₀`, provided each `ξ_a` is independent of `m₀` together with the summands already
used (`hind`). Every cross term factorizes by independence, and those that must vanish do so
because `E[ξ_a] = 0` or because `E[(∑ᵢZᵢξᵢ)·W] = 0` for background `W`. The coefficients are
assumed almost surely bounded (`hZb`), which ensures integrability. -/

section RandomCoefficients

variable {ι : Type*} {ξ Z : ι → Ω → ℝ} {B : ℝ}

/-! #### Almost-sure boundedness -/

/-- `f` is bounded almost everywhere by some constant. -/
def AEBdd (μ : Measure Ω) (f : Ω → ℝ) : Prop := ∃ C, ∀ᵐ ω ∂μ, |f ω| ≤ C

lemma AEBdd.integrable [IsProbabilityMeasure μ] {f : Ω → ℝ} (hb : AEBdd μ f)
    (hf : Measurable f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := hb
  exact integrable_of_abs_le hf hC

lemma AEBdd.const (c : ℝ) : AEBdd μ fun _ => c :=
  ⟨|c|, Filter.Eventually.of_forall fun _ => le_rfl⟩

lemma AEBdd.add {f g : Ω → ℝ} (hf : AEBdd μ f) (hg : AEBdd μ g) :
    AEBdd μ fun ω => f ω + g ω := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨C + D, ?_⟩
  filter_upwards [hC, hD] with ω h1 h2
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

lemma AEBdd.mul {f g : Ω → ℝ} (hf : AEBdd μ f) (hg : AEBdd μ g) :
    AEBdd μ fun ω => f ω * g ω := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨|C| * |D|, ?_⟩
  filter_upwards [hC, hD] with ω h1 h2
  rw [abs_mul]
  exact mul_le_mul (h1.trans (le_abs_self C)) (h2.trans (le_abs_self D)) (abs_nonneg _)
    (abs_nonneg _)

lemma AEBdd.pow {f : Ω → ℝ} (hf : AEBdd μ f) (n : ℕ) : AEBdd μ fun ω => f ω ^ n := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨|C| ^ n, ?_⟩
  filter_upwards [hC] with ω h
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (h.trans (le_abs_self C)) n

lemma AEBdd.sum {κ : Type*} {f : κ → Ω → ℝ} (hf : ∀ i, AEBdd μ (f i)) (F : Finset κ) :
    AEBdd μ fun ω => ∑ i ∈ F, f i ω := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a F ha ih =>
    obtain ⟨C, hC⟩ := (hf a).add ih
    refine ⟨C, ?_⟩
    filter_upwards [hC] with ω h
    rwa [Finset.sum_insert ha]

/-- A finite product of almost surely bounded functions is almost surely bounded. -/
lemma AEBdd.prod {κ : Type*} {f : κ → Ω → ℝ} (hf : ∀ i, AEBdd μ (f i)) (F : Finset κ) :
    AEBdd μ fun ω => ∏ i ∈ F, f i ω := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | @insert a F ha ih =>
    obtain ⟨C, hC⟩ := (hf a).mul ih
    refine ⟨C, ?_⟩
    filter_upwards [hC] with ω h
    rwa [Finset.prod_insert ha]

/-! #### The σ-algebra of what has already been used -/

-- kept semireducible
set_option warn.classDefReducibility false in
/-- The σ-algebra generated by the background `m₀` together with the variables `ξ i`, `i ∈ F`,
already summed over. -/
def restSigma (mb : MeasurableSpace Ω) (ξ : ι → Ω → ℝ) (F : Finset ι) : MeasurableSpace Ω :=
  mb ⊔ ⨆ i ∈ F, MeasurableSpace.comap (ξ i) inferInstance

lemma measurable_restSigma_background {F : Finset ι} {f : Ω → ℝ}
    (hf : Measurable[m₀] f) : Measurable[restSigma m₀ ξ F] f :=
  hf.mono le_sup_left le_rfl

lemma measurable_restSigma_xi {F : Finset ι} {i : ι} (hi : i ∈ F) :
    Measurable[restSigma m₀ ξ F] (ξ i) := by
  have h1 : MeasurableSpace.comap (ξ i) inferInstance
      ≤ ⨆ j ∈ F, MeasurableSpace.comap (ξ j) inferInstance :=
    le_iSup₂ (f := fun (j : ι) (_ : j ∈ F) => MeasurableSpace.comap (ξ j) inferInstance) i hi
  have h2 : MeasurableSpace.comap (ξ i) inferInstance ≤ restSigma m₀ ξ F :=
    h1.trans le_sup_right
  exact (comap_measurable (ξ i)).mono h2 le_rfl

/-- The hypothesis `hind` follows from joint independence: if a family of σ-algebras indexed by
`Option ι` is independent (the background at `none`, the variables at `some i`), then every
`ξ a` is independent of the background together with the `ξ i`, `i ∈ F`, for `a ∉ F`. -/
lemma indep_restSigma_of_iIndep {s : Option ι → MeasurableSpace Ω}
    (hle : ∀ p, s p ≤ mΩ) (hs : iIndep s μ)
    (hξs : ∀ i, MeasurableSpace.comap (ξ i) inferInstance ≤ s (some i))
    (F : Finset ι) (a : ι) (ha : a ∉ F) :
    Indep (MeasurableSpace.comap (ξ a) inferInstance) (restSigma (s none) ξ F) μ := by
  have hdisj : Disjoint ({some a} : Set (Option ι)) ({none} ∪ some '' (F : Set ι)) := by
    rw [Set.disjoint_singleton_left]
    rintro (h | ⟨i, hi, h⟩)
    · exact Option.some_ne_none a (Set.mem_singleton_iff.mp h)
    · exact ha (Finset.mem_coe.mp (Option.some_injective ι h ▸ hi))
  have h := indep_iSup_of_disjoint hle hs hdisj
  have hleft : MeasurableSpace.comap (ξ a) inferInstance
      ≤ ⨆ p ∈ ({some a} : Set (Option ι)), s p := by
    refine le_trans (hξs a) ?_
    exact le_iSup₂ (f := fun (p : Option ι) (_ : p ∈ ({some a} : Set (Option ι))) => s p)
      (some a) rfl
  have hright : restSigma (s none) ξ F
      ≤ ⨆ p ∈ ({none} ∪ some '' (F : Set ι)), s p := by
    refine sup_le ?_ (iSup₂_le fun i hi => ?_)
    · exact le_iSup₂ (f := fun (p : Option ι)
        (_ : p ∈ ({none} ∪ some '' (F : Set ι))) => s p) none (Or.inl rfl)
    · refine le_trans (hξs i) ?_
      exact le_iSup₂ (f := fun (p : Option ι)
        (_ : p ∈ ({none} ∪ some '' (F : Set ι))) => s p) (some i) (Or.inr ⟨i, hi, rfl⟩)
  have hcut := indep_of_indep_of_le_right h hright
  exact indep_of_indep_of_le_left hcut hleft

/-- The hypothesis `hind` from joint independence over a site type into which the summation
index embeds via `e`, with background the block `T` of sites disjoint from the image of `e`. -/
lemma indep_restSigma_of_sites {S : Type*} {m : S → MeasurableSpace Ω} {e : ι → S} {T : Set S}
    (hle : ∀ p, m p ≤ mΩ) (hm : iIndep m μ)
    (he : Function.Injective e) (heT : ∀ i, e i ∉ T)
    (hξ : ∀ i, MeasurableSpace.comap (ξ i) inferInstance ≤ m (e i))
    (G : Finset ι) (b : ι) (hb : b ∉ G) :
    Indep (MeasurableSpace.comap (ξ b) inferInstance)
      (restSigma (⨆ p ∈ T, m p) ξ G) μ := by
  have hdisj : Disjoint ({e b} : Set S) (T ∪ e '' (G : Set ι)) := by
    rw [Set.disjoint_singleton_left]
    rintro (h | ⟨i, hi, h⟩)
    · exact heT b h
    · exact hb (Finset.mem_coe.mp (he h ▸ hi))
  have h := indep_iSup_of_disjoint hle hm hdisj
  have hleft : MeasurableSpace.comap (ξ b) inferInstance ≤ ⨆ p ∈ ({e b} : Set S), m p :=
    (hξ b).trans (le_iSup₂ (f := fun (p : S) (_ : p ∈ ({e b} : Set S)) => m p) (e b) rfl)
  have hright : restSigma (⨆ p ∈ T, m p) ξ G ≤ ⨆ p ∈ (T ∪ e '' (G : Set ι)), m p := by
    refine sup_le (iSup₂_le fun p hp => ?_) (iSup₂_le fun i hi => ?_)
    · exact le_iSup₂ (f := fun (p : S) (_ : p ∈ (T ∪ e '' (G : Set ι))) => m p) p (Or.inl hp)
    · exact (hξ i).trans (le_iSup₂ (f := fun (p : S) (_ : p ∈ (T ∪ e '' (G : Set ι))) => m p)
        (e i) (Or.inr ⟨i, hi, rfl⟩))
  have hcut := indep_of_indep_of_le_right h hright
  exact indep_of_indep_of_le_left hcut hleft

/-- Independence of `ξ a` from the σ-algebra of what has been used transfers to any function
measurable with respect to it. -/
lemma indepFun_of_restSigma {F : Finset ι} {a : ι}
    (h : Indep (MeasurableSpace.comap (ξ a) inferInstance) (restSigma m₀ ξ F) μ)
    {g : Ω → ℝ} (hg : Measurable[restSigma m₀ ξ F] g) : IndepFun g (ξ a) μ :=
  indep_of_indep_of_le_left h.symm hg.comap_le

/-! #### Three kinds of cross term -/

/-- A cross term with a lone `E[ξ_a]` vanishes. -/
lemma integral_mul_eq_zero_of_mean [IsProbabilityMeasure μ]
    {F : Finset ι} {a : ι}
    (h : Indep (MeasurableSpace.comap (ξ a) inferInstance) (restSigma m₀ ξ F) μ)
    (hξm : Measurable (ξ a)) (hξ1 : ∫ ω, ξ a ω ∂μ = 0)
    {g : Ω → ℝ} (hgm : Measurable g) (hgr : Measurable[restSigma m₀ ξ F] g) :
    ∫ ω, g ω * ξ a ω ∂μ = 0 := by
  have h2 := integral_monomial_eq (indepFun_of_restSigma h hgr) hgm hξm 1 1
  simp only [pow_one] at h2
  rw [h2, hξ1, mul_zero]

/-- A cross term with a lone `E[g]` vanishes. -/
lemma integral_mul_pow_eq_zero_of_coeff [IsProbabilityMeasure μ]
    {F : Finset ι} {a : ι} {n : ℕ}
    (h : Indep (MeasurableSpace.comap (ξ a) inferInstance) (restSigma m₀ ξ F) μ)
    (hξm : Measurable (ξ a))
    {g : Ω → ℝ} (hgm : Measurable g) (hgr : Measurable[restSigma m₀ ξ F] g)
    (hg : ∫ ω, g ω ∂μ = 0) :
    ∫ ω, g ω * ξ a ω ^ n ∂μ = 0 := by
  have h2 := integral_monomial_eq (indepFun_of_restSigma h hgr) hgm hξm 1 n
  simp only [pow_one] at h2
  rw [h2, hg, zero_mul]

/-- An even power of `ξ_a` against a nonnegative coefficient: `E[g ξ_a^n] ≤ B^n E[g]`. -/
lemma integral_mul_pow_le [IsProbabilityMeasure μ]
    {F : Finset ι} {a : ι} {n : ℕ}
    (h : Indep (MeasurableSpace.comap (ξ a) inferInstance) (restSigma m₀ ξ F) μ)
    (hn : Even n) (hξm : Measurable (ξ a)) (hξb : ∀ᵐ ω ∂μ, |ξ a ω| ≤ B)
    {g : Ω → ℝ} (hgm : Measurable g) (hgr : Measurable[restSigma m₀ ξ F] g)
    (hg0 : 0 ≤ ∫ ω, g ω ∂μ) :
    ∫ ω, g ω * ξ a ω ^ n ∂μ ≤ B ^ n * ∫ ω, g ω ∂μ := by
  have h2 := integral_monomial_eq (indepFun_of_restSigma h hgr) hgm hξm 1 n
  simp only [pow_one] at h2
  rw [h2]
  calc (∫ ω, g ω ∂μ) * ∫ ω, ξ a ω ^ n ∂μ ≤ (∫ ω, g ω ∂μ) * B ^ n :=
        mul_le_mul_of_nonneg_left (integral_pow_le_of_abs_le hn hξm hξb) hg0
    _ = B ^ n * ∫ ω, g ω ∂μ := by ring

/-! #### The three inductions -/

/-- `E[(∑ᵢ Zᵢξᵢ)·W] = 0` for background `W`. -/
lemma integral_sum_mul_background_eq_zero [IsProbabilityMeasure μ]
    (hm₀ : m₀ ≤ mΩ) (hZm : ∀ i, Measurable[m₀] (Z i)) (hZb : ∀ i, AEBdd μ (Z i))
    (hξm : ∀ i, Measurable (ξ i)) (hξb : ∀ i, ∀ᵐ ω ∂μ, |ξ i ω| ≤ B)
    (hξ1 : ∀ i, ∫ ω, ξ i ω ∂μ = 0)
    (hind : ∀ (G : Finset ι) (b : ι), b ∉ G →
      Indep (MeasurableSpace.comap (ξ b) inferInstance) (restSigma m₀ ξ G) μ)
    {W : Ω → ℝ} (hWm : Measurable[m₀] W) (hWb : AEBdd μ W) (F : Finset ι) :
    ∫ ω, (∑ i ∈ F, Z i ω * ξ i ω) * W ω ∂μ = 0 := by
  have hW : Measurable W := hWm.mono hm₀ le_rfl
  have hZ : ∀ i, Measurable (Z i) := fun i => (hZm i).mono hm₀ le_rfl
  have hξB : ∀ i, AEBdd μ (ξ i) := fun i => ⟨B, hξb i⟩
  have hint : ∀ i ∈ F, Integrable (fun ω => Z i ω * W ω * ξ i ω) μ := fun i _ =>
    (((hZb i).mul hWb).mul (hξB i)).integrable (((hZ i).mul hW).mul (hξm i))
  have hterm : ∀ i : ι, ∫ ω, Z i ω * W ω * ξ i ω ∂μ = 0 := by
    intro i
    refine integral_mul_eq_zero_of_mean (F := (∅ : Finset ι)) (hind ∅ i (by simp)) (hξm i)
      (hξ1 i) ((hZ i).mul hW) ?_
    exact measurable_restSigma_background ((hZm i).mul hWm)
  have hrw : ∫ ω, (∑ i ∈ F, Z i ω * ξ i ω) * W ω ∂μ
      = ∫ ω, ∑ i ∈ F, Z i ω * W ω * ξ i ω ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with ω
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hrw, integral_finsetSum F hint]
  simp [hterm]

/-- `E[(∑ᵢ Zᵢξᵢ)²·W] ≤ B² E[(∑ᵢ Zᵢ²)·W]` for nonnegative background `W`. -/
lemma integral_sq_sum_mul_background_le [IsProbabilityMeasure μ]
    (hm₀ : m₀ ≤ mΩ) (hZm : ∀ i, Measurable[m₀] (Z i)) (hZb : ∀ i, AEBdd μ (Z i))
    (hξm : ∀ i, Measurable (ξ i)) (hξb : ∀ i, ∀ᵐ ω ∂μ, |ξ i ω| ≤ B)
    (hξ1 : ∀ i, ∫ ω, ξ i ω ∂μ = 0)
    (hind : ∀ (G : Finset ι) (b : ι), b ∉ G →
      Indep (MeasurableSpace.comap (ξ b) inferInstance) (restSigma m₀ ξ G) μ)
    {W : Ω → ℝ} (hWm : Measurable[m₀] W) (hWb : AEBdd μ W) (hW0 : ∀ᵐ ω ∂μ, 0 ≤ W ω)
    (F : Finset ι) :
    ∫ ω, (∑ i ∈ F, Z i ω * ξ i ω) ^ 2 * W ω ∂μ
      ≤ B ^ 2 * ∫ ω, (∑ i ∈ F, Z i ω ^ 2) * W ω ∂μ := by
  classical
  have hW : Measurable W := hWm.mono hm₀ le_rfl
  have hZ : ∀ i, Measurable (Z i) := fun i => (hZm i).mono hm₀ le_rfl
  have hξB : ∀ i, AEBdd μ (ξ i) := fun i => ⟨B, hξb i⟩
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a F ha ih =>
    have hSm : Measurable fun ω => ∑ i ∈ F, Z i ω * ξ i ω :=
      Finset.measurable_sum F fun i _ => (hZ i).mul (hξm i)
    have hSr : Measurable[restSigma m₀ ξ F] fun ω => ∑ i ∈ F, Z i ω * ξ i ω :=
      Finset.measurable_sum F fun i hi =>
        (measurable_restSigma_background (hZm i)).mul (measurable_restSigma_xi hi)
    have hSb : AEBdd μ fun ω => ∑ i ∈ F, Z i ω * ξ i ω :=
      AEBdd.sum (fun i => (hZb i).mul (hξB i)) F
    have hQm : Measurable fun ω => ∑ i ∈ F, Z i ω ^ 2 :=
      Finset.measurable_sum F fun i _ => (hZ i).pow_const 2
    have hQb : AEBdd μ fun ω => ∑ i ∈ F, Z i ω ^ 2 :=
      AEBdd.sum (fun i => (hZb i).pow 2) F
    -- the three pieces of the expansion
    have hcross : ∫ ω, (∑ i ∈ F, Z i ω * ξ i ω) * Z a ω * W ω * ξ a ω ∂μ = 0 :=
      integral_mul_eq_zero_of_mean (hind F a ha) (hξm a) (hξ1 a)
        ((hSm.mul (hZ a)).mul hW)
        ((hSr.mul (measurable_restSigma_background (hZm a))).mul
          (measurable_restSigma_background hWm))
    have hdiag0 : 0 ≤ ∫ ω, Z a ω ^ 2 * W ω ∂μ := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [hW0] with ω h
      exact mul_nonneg (sq_nonneg _) h
    have hdiag : ∫ ω, Z a ω ^ 2 * W ω * ξ a ω ^ 2 ∂μ ≤ B ^ 2 * ∫ ω, Z a ω ^ 2 * W ω ∂μ :=
      integral_mul_pow_le (hind F a ha) (by decide) (hξm a) (hξb a)
        (((hZ a).pow_const 2).mul hW)
        ((measurable_restSigma_background (hZm a)).pow_const 2 |>.mul
          (measurable_restSigma_background hWm)) hdiag0
    -- integrability of the five functions in the expansion
    have i1 : Integrable (fun ω => (∑ i ∈ F, Z i ω * ξ i ω) ^ 2 * W ω) μ :=
      ((hSb.pow 2).mul hWb).integrable ((hSm.pow_const 2).mul hW)
    have i2 : Integrable
        (fun ω => 2 * ((∑ i ∈ F, Z i ω * ξ i ω) * Z a ω * W ω * ξ a ω)) μ :=
      ((((hSb.mul (hZb a)).mul hWb).mul (hξB a)).integrable
        (((hSm.mul (hZ a)).mul hW).mul (hξm a))).const_mul 2
    have i3 : Integrable (fun ω => Z a ω ^ 2 * W ω * ξ a ω ^ 2) μ :=
      ((((hZb a).pow 2).mul hWb).mul ((hξB a).pow 2)).integrable
        ((((hZ a).pow_const 2).mul hW).mul ((hξm a).pow_const 2))
    have i4 : Integrable (fun ω => (∑ i ∈ F, Z i ω ^ 2) * W ω) μ :=
      (hQb.mul hWb).integrable (hQm.mul hW)
    have i5 : Integrable (fun ω => Z a ω ^ 2 * W ω) μ :=
      (((hZb a).pow 2).mul hWb).integrable (((hZ a).pow_const 2).mul hW)
    have hexp : ∫ ω, (∑ i ∈ insert a F, Z i ω * ξ i ω) ^ 2 * W ω ∂μ
        = ∫ ω, ((∑ i ∈ F, Z i ω * ξ i ω) ^ 2 * W ω
            + (2 * ((∑ i ∈ F, Z i ω * ξ i ω) * Z a ω * W ω * ξ a ω)
              + Z a ω ^ 2 * W ω * ξ a ω ^ 2)) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards with ω
      rw [Finset.sum_insert ha]
      ring
    have hrhs : ∫ ω, (∑ i ∈ insert a F, Z i ω ^ 2) * W ω ∂μ
        = ∫ ω, ((∑ i ∈ F, Z i ω ^ 2) * W ω + Z a ω ^ 2 * W ω) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards with ω
      rw [Finset.sum_insert ha]
      ring
    rw [hexp, integral_add i1 (i2.fun_add i3), integral_add i2 i3, integral_const_mul,
      hrhs, integral_add i4 i5, hcross]
    have := ih
    nlinarith [this, hdiag]

/-- **Fourth moments with random coefficients.** If the `Zᵢ` are measurable with respect to a
background σ-algebra `m₀` and bounded, and each `ξ_a` is independent of `m₀` together with the
`ξᵢ` already used, then `E[(∑ᵢ Zᵢξᵢ)⁴] ≤ 3B⁴ E[(∑ᵢ Zᵢ²)²]`. -/
theorem integral_pow_four_random_le [IsProbabilityMeasure μ]
    (hm₀ : m₀ ≤ mΩ) (hZm : ∀ i, Measurable[m₀] (Z i)) (hZb : ∀ i, AEBdd μ (Z i))
    (hξm : ∀ i, Measurable (ξ i)) (hξb : ∀ i, ∀ᵐ ω ∂μ, |ξ i ω| ≤ B)
    (hξ1 : ∀ i, ∫ ω, ξ i ω ∂μ = 0)
    (hind : ∀ (G : Finset ι) (b : ι), b ∉ G →
      Indep (MeasurableSpace.comap (ξ b) inferInstance) (restSigma m₀ ξ G) μ)
    (F : Finset ι) :
    ∫ ω, (∑ i ∈ F, Z i ω * ξ i ω) ^ 4 ∂μ
      ≤ 3 * B ^ 4 * ∫ ω, (∑ i ∈ F, Z i ω ^ 2) ^ 2 ∂μ := by
  classical
  have hZ : ∀ i, Measurable (Z i) := fun i => (hZm i).mono hm₀ le_rfl
  have hξB : ∀ i, AEBdd μ (ξ i) := fun i => ⟨B, hξb i⟩
  have hB2 : (0 : ℝ) ≤ B ^ 2 := by positivity
  have hB4 : (0 : ℝ) ≤ B ^ 4 := by positivity
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a F ha ih =>
    have hSm : Measurable fun ω => ∑ i ∈ F, Z i ω * ξ i ω :=
      Finset.measurable_sum F fun i _ => (hZ i).mul (hξm i)
    have hSr : Measurable[restSigma m₀ ξ F] fun ω => ∑ i ∈ F, Z i ω * ξ i ω :=
      Finset.measurable_sum F fun i hi =>
        (measurable_restSigma_background (hZm i)).mul (measurable_restSigma_xi hi)
    have hSb : AEBdd μ fun ω => ∑ i ∈ F, Z i ω * ξ i ω :=
      AEBdd.sum (fun i => (hZb i).mul (hξB i)) F
    have hQm : Measurable fun ω => ∑ i ∈ F, Z i ω ^ 2 :=
      Finset.measurable_sum F fun i _ => (hZ i).pow_const 2
    have hQb : AEBdd μ fun ω => ∑ i ∈ F, Z i ω ^ 2 :=
      AEBdd.sum (fun i => (hZb i).pow 2) F
    have hZar : Measurable[restSigma m₀ ξ F] (Z a) := measurable_restSigma_background (hZm a)
    -- term 2: a lone `E[ξ_a]`
    have ht2 : ∫ ω, (∑ i ∈ F, Z i ω * ξ i ω) ^ 3 * Z a ω * ξ a ω ∂μ = 0 :=
      integral_mul_eq_zero_of_mean (hind F a ha) (hξm a) (hξ1 a) ((hSm.pow_const 3).mul (hZ a))
        ((hSr.pow_const 3).mul hZar)
    -- term 4: a lone `E[(∑ Zξ)·Z_a³]`, which vanishes
    have ht4coeff : ∫ ω, (∑ i ∈ F, Z i ω * ξ i ω) * Z a ω ^ 3 ∂μ = 0 :=
      integral_sum_mul_background_eq_zero hm₀ hZm hZb hξm hξb hξ1 hind
        ((hZm a).pow_const 3) ((hZb a).pow 3) F
    have ht4 : ∫ ω, (∑ i ∈ F, Z i ω * ξ i ω) * Z a ω ^ 3 * ξ a ω ^ 3 ∂μ = 0 :=
      integral_mul_pow_eq_zero_of_coeff (hind F a ha) (hξm a) (hSm.mul ((hZ a).pow_const 3))
        (hSr.mul (hZar.pow_const 3)) ht4coeff
    -- term 3: an even power of `ξ_a`, then the second-moment lemma
    have ht3inner0 : 0 ≤ ∫ ω, (∑ i ∈ F, Z i ω * ξ i ω) ^ 2 * Z a ω ^ 2 ∂μ :=
      integral_nonneg fun ω => by positivity
    have ht3 : ∫ ω, (∑ i ∈ F, Z i ω * ξ i ω) ^ 2 * Z a ω ^ 2 * ξ a ω ^ 2 ∂μ
        ≤ B ^ 2 * ∫ ω, (∑ i ∈ F, Z i ω * ξ i ω) ^ 2 * Z a ω ^ 2 ∂μ :=
      integral_mul_pow_le (hind F a ha) (by decide) (hξm a) (hξb a)
        ((hSm.pow_const 2).mul ((hZ a).pow_const 2)) ((hSr.pow_const 2).mul (hZar.pow_const 2))
        ht3inner0
    have ht3inner : ∫ ω, (∑ i ∈ F, Z i ω * ξ i ω) ^ 2 * Z a ω ^ 2 ∂μ
        ≤ B ^ 2 * ∫ ω, (∑ i ∈ F, Z i ω ^ 2) * Z a ω ^ 2 ∂μ :=
      integral_sq_sum_mul_background_le hm₀ hZm hZb hξm hξb hξ1 hind ((hZm a).pow_const 2)
        ((hZb a).pow 2) (by filter_upwards with ω; positivity) F
    -- term 5
    have ht5inner0 : 0 ≤ ∫ ω, Z a ω ^ 4 ∂μ := integral_nonneg fun ω => by positivity
    have ht5 : ∫ ω, Z a ω ^ 4 * ξ a ω ^ 4 ∂μ ≤ B ^ 4 * ∫ ω, Z a ω ^ 4 ∂μ :=
      integral_mul_pow_le (hind F a ha) (by decide) (hξm a) (hξb a) ((hZ a).pow_const 4)
        (hZar.pow_const 4) ht5inner0
    -- integrability
    have i1 : Integrable (fun ω => (∑ i ∈ F, Z i ω * ξ i ω) ^ 4) μ :=
      (hSb.pow 4).integrable (hSm.pow_const 4)
    have i2 : Integrable
        (fun ω => 4 * ((∑ i ∈ F, Z i ω * ξ i ω) ^ 3 * Z a ω * ξ a ω)) μ :=
      ((((hSb.pow 3).mul (hZb a)).mul (hξB a)).integrable
        (((hSm.pow_const 3).mul (hZ a)).mul (hξm a))).const_mul 4
    have i3 : Integrable
        (fun ω => 6 * ((∑ i ∈ F, Z i ω * ξ i ω) ^ 2 * Z a ω ^ 2 * ξ a ω ^ 2)) μ :=
      (((((hSb.pow 2).mul ((hZb a).pow 2)).mul ((hξB a).pow 2))).integrable
        (((hSm.pow_const 2).mul ((hZ a).pow_const 2)).mul ((hξm a).pow_const 2))).const_mul 6
    have i4 : Integrable
        (fun ω => 4 * ((∑ i ∈ F, Z i ω * ξ i ω) * Z a ω ^ 3 * ξ a ω ^ 3)) μ :=
      ((((hSb.mul ((hZb a).pow 3)).mul ((hξB a).pow 3))).integrable
        ((hSm.mul ((hZ a).pow_const 3)).mul ((hξm a).pow_const 3))).const_mul 4
    have i5 : Integrable (fun ω => Z a ω ^ 4 * ξ a ω ^ 4) μ :=
      (((hZb a).pow 4).mul ((hξB a).pow 4)).integrable
        (((hZ a).pow_const 4).mul ((hξm a).pow_const 4))
    have j1 : Integrable (fun ω => (∑ i ∈ F, Z i ω ^ 2) ^ 2) μ :=
      (hQb.pow 2).integrable (hQm.pow_const 2)
    have j2 : Integrable (fun ω => 2 * ((∑ i ∈ F, Z i ω ^ 2) * Z a ω ^ 2)) μ :=
      ((hQb.mul ((hZb a).pow 2)).integrable (hQm.mul ((hZ a).pow_const 2))).const_mul 2
    have j3 : Integrable (fun ω => Z a ω ^ 4) μ :=
      ((hZb a).pow 4).integrable ((hZ a).pow_const 4)
    have hexp : ∫ ω, (∑ i ∈ insert a F, Z i ω * ξ i ω) ^ 4 ∂μ
        = ∫ ω, ((∑ i ∈ F, Z i ω * ξ i ω) ^ 4
            + (4 * ((∑ i ∈ F, Z i ω * ξ i ω) ^ 3 * Z a ω * ξ a ω)
              + (6 * ((∑ i ∈ F, Z i ω * ξ i ω) ^ 2 * Z a ω ^ 2 * ξ a ω ^ 2)
                + (4 * ((∑ i ∈ F, Z i ω * ξ i ω) * Z a ω ^ 3 * ξ a ω ^ 3)
                  + Z a ω ^ 4 * ξ a ω ^ 4)))) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards with ω
      rw [Finset.sum_insert ha]
      ring
    have hrhs : ∫ ω, (∑ i ∈ insert a F, Z i ω ^ 2) ^ 2 ∂μ
        = ∫ ω, ((∑ i ∈ F, Z i ω ^ 2) ^ 2
            + (2 * ((∑ i ∈ F, Z i ω ^ 2) * Z a ω ^ 2) + Z a ω ^ 4)) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards with ω
      rw [Finset.sum_insert ha]
      ring
    rw [hexp, integral_add i1 (i2.fun_add (i3.fun_add (i4.fun_add i5))),
      integral_add i2 (i3.fun_add (i4.fun_add i5)), integral_add i3 (i4.fun_add i5),
      integral_add i4 i5, integral_const_mul, integral_const_mul, integral_const_mul,
      hrhs, integral_add j1 (j2.fun_add j3), integral_add j2 j3, integral_const_mul,
      ht2, ht4]
    nlinarith [ih, ht3, ht3inner, ht5, ht5inner0, hB2, hB4,
      mul_le_mul_of_nonneg_left ht3inner hB2]

end RandomCoefficients

/-! ### Cauchy–Schwarz

`E[(∑ᵢZᵢ²)²] ≤ (∑ᵢ(E[Zᵢ⁴])^{1/2})²`, proved from the discriminant of the nonnegative quadratic
`t ↦ E[(tf - g)²]`. -/

section CauchySchwarz

variable {ι : Type*}

/-- A quadratic `A t² - 2Dt + C` that is nonnegative everywhere has nonpositive discriminant,
hence `D ≤ √A √C`. -/
lemma le_sqrt_mul_sqrt_of_quadratic_nonneg {A C D : ℝ} (hA : 0 ≤ A)
    (h : ∀ t : ℝ, 0 ≤ A * (t * t) + (-2 * D) * t + C) :
    D ≤ Real.sqrt A * Real.sqrt C := by
  have hdisc := discrim_le_zero h
  have hsq : D ^ 2 ≤ A * C := by
    simp only [discrim] at hdisc
    nlinarith [hdisc]
  calc D ≤ |D| := le_abs_self D
    _ = Real.sqrt (D ^ 2) := (Real.sqrt_sq_eq_abs D).symm
    _ ≤ Real.sqrt (A * C) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt A * Real.sqrt C := Real.sqrt_mul hA C

/-- The Cauchy–Schwarz inequality `E[fg] ≤ (E[f²])^{1/2}(E[g²])^{1/2}` for two almost surely
bounded measurable functions, with no sign condition on `f` or `g`. -/
lemma integral_mul_le_sqrt_mul_sqrt [IsProbabilityMeasure μ] {f g : Ω → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (hfb : AEBdd μ f) (hgb : AEBdd μ g) :
    ∫ ω, f ω * g ω ∂μ
      ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂μ) * Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
  have if2 : Integrable (fun ω => f ω ^ 2) μ := (hfb.pow 2).integrable (hfm.pow_const 2)
  have ig2 : Integrable (fun ω => g ω ^ 2) μ := (hgb.pow 2).integrable (hgm.pow_const 2)
  have ifg : Integrable (fun ω => f ω * g ω) μ := (hfb.mul hgb).integrable (hfm.mul hgm)
  refine le_sqrt_mul_sqrt_of_quadratic_nonneg (integral_nonneg fun ω => by positivity) ?_
  intro t
  have hnn : 0 ≤ ∫ ω, (t * f ω - g ω) ^ 2 ∂μ := integral_nonneg fun ω => by positivity
  have hexp : ∫ ω, (t * f ω - g ω) ^ 2 ∂μ
      = (∫ ω, f ω ^ 2 ∂μ) * (t * t) + (-2 * ∫ ω, f ω * g ω ∂μ) * t + ∫ ω, g ω ^ 2 ∂μ := by
    have he : ∫ ω, (t * f ω - g ω) ^ 2 ∂μ
        = ∫ ω, ((t * t) * f ω ^ 2 + ((-2 * t) * (f ω * g ω) + g ω ^ 2)) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards with ω
      ring
    rw [he, integral_add (if2.const_mul _) ((ifg.const_mul _).fun_add ig2),
      integral_add (ifg.const_mul _) ig2, integral_const_mul, integral_const_mul]
    ring
  rw [hexp] at hnn
  exact hnn

/-- `E[(∑ᵢZᵢ²)²] ≤ (∑ᵢ(E[Zᵢ⁴])^{1/2})²` for almost surely bounded measurable `Zᵢ` over a finite
index set. No independence is assumed. -/
lemma integral_sq_sum_sq_le [IsProbabilityMeasure μ] {Z : ι → Ω → ℝ}
    (hZm : ∀ i, Measurable (Z i)) (hZb : ∀ i, AEBdd μ (Z i)) (F : Finset ι) :
    ∫ ω, (∑ i ∈ F, Z i ω ^ 2) ^ 2 ∂μ
      ≤ (∑ i ∈ F, Real.sqrt (∫ ω, Z i ω ^ 4 ∂μ)) ^ 2 := by
  have hint : ∀ i i' : ι, Integrable (fun ω => Z i ω ^ 2 * Z i' ω ^ 2) μ := fun i i' =>
    (((hZb i).pow 2).mul ((hZb i').pow 2)).integrable
      (((hZm i).pow_const 2).mul ((hZm i').pow_const 2))
  have hexp : ∫ ω, (∑ i ∈ F, Z i ω ^ 2) ^ 2 ∂μ
      = ∑ i ∈ F, ∑ i' ∈ F, ∫ ω, Z i ω ^ 2 * Z i' ω ^ 2 ∂μ := by
    have h1 : ∫ ω, (∑ i ∈ F, Z i ω ^ 2) ^ 2 ∂μ
        = ∫ ω, ∑ i ∈ F, ∑ i' ∈ F, Z i ω ^ 2 * Z i' ω ^ 2 ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards with ω
      rw [pow_two, Finset.sum_mul_sum]
    rw [h1, integral_finsetSum F fun i _ => integrable_finsetSum F fun i' _ => hint i i']
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum F fun i' _ => hint i i'
  have hbd : ∀ i i' : ι, ∫ ω, Z i ω ^ 2 * Z i' ω ^ 2 ∂μ
      ≤ Real.sqrt (∫ ω, Z i ω ^ 4 ∂μ) * Real.sqrt (∫ ω, Z i' ω ^ 4 ∂μ) := by
    have h4 : ∀ l : ι, ∫ ω, (Z l ω ^ 2) ^ 2 ∂μ = ∫ ω, Z l ω ^ 4 ∂μ := by
      intro l
      refine integral_congr_ae ?_
      filter_upwards with ω
      ring
    intro i i'
    have h := integral_mul_le_sqrt_mul_sqrt (μ := μ) ((hZm i).pow_const 2)
      ((hZm i').pow_const 2) ((hZb i).pow 2) ((hZb i').pow 2)
    rwa [h4 i, h4 i'] at h
  have hrhs : (∑ i ∈ F, Real.sqrt (∫ ω, Z i ω ^ 4 ∂μ)) ^ 2
      = ∑ i ∈ F, ∑ i' ∈ F,
          Real.sqrt (∫ ω, Z i ω ^ 4 ∂μ) * Real.sqrt (∫ ω, Z i' ω ^ 4 ∂μ) := by
    rw [pow_two, Finset.sum_mul_sum]
  rw [hexp, hrhs]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun i' _ => hbd i i'

end CauchySchwarz

/-! ### Assembly across levels

The levels are `Fin j`, the index sets are `I : Fin j → Type*`, the multi-index range is
`Fintype.piFinset F` for `F : ∀ k, Finset (I k)`, and joint independence is stated on the site
type `Σ k, I k`. The form is
`Z = fun ω => ∑ s ∈ Fintype.piFinset F, a s * ∏ k, ξ k (s k) ω`.
-/

section Levels

/-- Splitting a sum over multi-indices `s ∈ I_0 × ⋯ × I_j` into the first coordinate and the
rest: `∑_s f(s) = ∑_{i ∈ I_0} ∑_t f(i ∷ t)`. -/
lemma sum_piFinset_succ {j : ℕ} {I : Fin (j + 1) → Type*} {M : Type*} [AddCommMonoid M]
    (F : ∀ k, Finset (I k)) (f : (∀ k, I k) → M) :
    ∑ s ∈ Fintype.piFinset F, f s
      = ∑ i ∈ F 0, ∑ t ∈ Fintype.piFinset (fun k : Fin j => F k.succ), f (Fin.cons i t) := by
  rw [← Finset.sum_product' (F 0) (Fintype.piFinset fun k : Fin j => F k.succ)
    fun (i : I 0) (t : ∀ k : Fin j, I k.succ) => f (Fin.cons i t)]
  refine Finset.sum_nbij' (fun s => (s 0, Fin.tail s)) (fun p => Fin.cons p.1 p.2)
    ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rw [Fintype.mem_piFinset] at hs
    exact Finset.mem_product.mpr ⟨hs 0, Fintype.mem_piFinset.mpr fun k => hs k.succ⟩
  · intro p hp
    rw [Finset.mem_product] at hp
    refine Fintype.mem_piFinset.mpr fun k => ?_
    refine Fin.cases ?_ (fun k' => ?_) k
    · rw [Fin.cons_zero]
      exact hp.1
    · rw [Fin.cons_succ]
      exact Fintype.mem_piFinset.mp hp.2 k'
  · intro s _
    exact Fin.cons_self_tail s
  · intro p _
    simp [Fin.tail_cons]
  · intro s _
    rw [Fin.cons_self_tail]

/-- **Lemma SM.C.4.** `E[Z⁴] ≤ (3B⁴)^j (∑_s a_s²)²` for every `j`.

The proof is by induction on `j`. Write `Z = ∑_{i ∈ I_0} ξ^{(0)}_i Zᵢ` with
`Zᵢ = ∑_t a_{i ∷ t} ∏_{k ≥ 1} ξ^{(k)}_{t_k}`, apply `integral_pow_four_random_le` with the
σ-algebra generated by the higher levels as background, then `integral_sq_sum_sq_le` and the
induction hypothesis. The coefficients `Zᵢ` are bounded because the `ξ^{(k)}` are. -/
theorem integral_pow_four_multilinear_le [IsProbabilityMeasure μ] {B : ℝ} :
    ∀ (j : ℕ) (I : Fin j → Type*) (ξ : ∀ k : Fin j, I k → Ω → ℝ)
      (a : (∀ k, I k) → ℝ) (F : ∀ k, Finset (I k)),
      iIndepFun (fun p : Σ k : Fin j, I k => ξ p.1 p.2) μ →
      (∀ (k : Fin j) (i : I k), Measurable (ξ k i)) →
      (∀ (k : Fin j) (i : I k), ∫ ω, ξ k i ω ∂μ = 0) →
      (∀ (k : Fin j) (i : I k), ∀ᵐ ω ∂μ, |ξ k i ω| ≤ B) →
      ∫ ω, (∑ s ∈ Fintype.piFinset F, a s * ∏ k, ξ k (s k) ω) ^ 4 ∂μ
        ≤ (3 * B ^ 4) ^ j * (∑ s ∈ Fintype.piFinset F, a s ^ 2) ^ 2 := by
  intro j
  induction j with
  | zero =>
    intro I ξ a F _ _ _ _
    have hsingle : Fintype.piFinset F = {(default : ∀ k : Fin 0, I k)} :=
      Finset.eq_singleton_iff_unique_mem.mpr
        ⟨Fintype.mem_piFinset.mpr fun k => k.elim0, fun s _ => Subsingleton.elim _ _⟩
    rw [hsingle]
    have hleft : ∫ ω, (∑ s ∈ ({(default : ∀ k : Fin 0, I k)} : Finset (∀ k : Fin 0, I k)),
          a s * ∏ k : Fin 0, ξ k (s k) ω) ^ 4 ∂μ
        = a (default : ∀ k : Fin 0, I k) ^ 4 := by simp
    rw [hleft, Finset.sum_singleton, pow_zero, one_mul]
    exact le_of_eq (by ring)
  | succ j ih =>
    intro I ξ a F hindep hmeas hmean hbdd
    classical
    -- `Zᵢ` and `∑_{s : s_0 = i} a_s²`
    obtain ⟨Zc, hZc⟩ : ∃ Z : I 0 → Ω → ℝ, Z = fun i ω =>
        ∑ t ∈ Fintype.piFinset (fun k : Fin j => F k.succ),
          a (Fin.cons i t) * ∏ k : Fin j, ξ k.succ (t k) ω := ⟨_, rfl⟩
    obtain ⟨Tc, hTc⟩ : ∃ T : I 0 → ℝ, T = fun i =>
        ∑ t ∈ Fintype.piFinset (fun k : Fin j => F k.succ), a (Fin.cons i t) ^ 2 := ⟨_, rfl⟩
    -- the background σ-algebra: everything at a level above `0`
    obtain ⟨m₁, hm₁⟩ : ∃ m : MeasurableSpace Ω, m =
        ⨆ p ∈ {p : Σ k : Fin (j + 1), I k | p.1 ≠ 0},
          MeasurableSpace.comap (ξ p.1 p.2) inferInstance := ⟨_, rfl⟩
    have hcomap : ∀ (k : Fin j) (i : I k.succ),
        MeasurableSpace.comap (ξ k.succ i) inferInstance ≤ m₁ := by
      intro k i
      rw [hm₁]
      exact le_iSup₂ (f := fun (p : Σ k : Fin (j + 1), I k)
        (_ : p ∈ {p : Σ k : Fin (j + 1), I k | p.1 ≠ 0}) =>
          MeasurableSpace.comap (ξ p.1 p.2) inferInstance)
        (⟨k.succ, i⟩ : Σ k : Fin (j + 1), I k) (Fin.succ_ne_zero k)
    have hm₁le : m₁ ≤ mΩ := by
      rw [hm₁]
      exact iSup₂_le fun p _ => (hmeas p.1 p.2).comap_le
    have hZmeas : ∀ i : I 0, Measurable[m₁] (Zc i) := by
      intro i
      simp only [hZc]
      refine Finset.measurable_sum _ fun t _ => Measurable.mul measurable_const ?_
      exact Finset.measurable_prod _ fun k _ =>
        (comap_measurable (ξ k.succ (t k))).mono (hcomap k (t k)) le_rfl
    have hxiB : ∀ (k : Fin j) (i : I k.succ), AEBdd μ (ξ k.succ i) :=
      fun k i => ⟨B, hbdd k.succ i⟩
    have hZbdd : ∀ i : I 0, AEBdd μ (Zc i) := by
      intro i
      simp only [hZc]
      refine AEBdd.sum (fun t => ?_) _
      have hp : AEBdd μ fun ω => ∏ k ∈ (Finset.univ : Finset (Fin j)), ξ k.succ (t k) ω :=
        AEBdd.prod (f := fun k : Fin j => ξ k.succ (t k)) (fun k => hxiB k (t k)) Finset.univ
      exact (AEBdd.const (a (Fin.cons i t))).mul hp
    have hind : ∀ (G : Finset (I 0)) (b : I 0), b ∉ G →
        Indep (MeasurableSpace.comap (ξ 0 b) inferInstance) (restSigma m₁ (ξ 0) G) μ := by
      intro G b hb
      rw [hm₁]
      refine indep_restSigma_of_sites
        (m := fun p : Σ k : Fin (j + 1), I k =>
          MeasurableSpace.comap (ξ p.1 p.2) inferInstance)
        (e := fun i : I 0 => (⟨0, i⟩ : Σ k : Fin (j + 1), I k))
        (T := {p : Σ k : Fin (j + 1), I k | p.1 ≠ 0})
        (fun p => (hmeas p.1 p.2).comap_le) hindep ?_ ?_ (fun i => le_rfl) G b hb
      · exact fun i i' h => eq_of_heq (Sigma.mk.inj_iff.mp h).2
      · intro i
        simp
    -- the induction hypothesis, one level down, for each level-`0` index
    have hIH : ∀ i : I 0, ∫ ω, Zc i ω ^ 4 ∂μ ≤ (3 * B ^ 4) ^ j * Tc i ^ 2 := by
      have hg : Function.Injective (fun p : Σ k : Fin j, I k.succ =>
          (⟨p.1.succ, p.2⟩ : Σ k : Fin (j + 1), I k)) := by
        rintro ⟨k, x⟩ ⟨k', x'⟩ h
        obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
        obtain rfl : k = k' := Fin.succ_injective _ h1
        obtain rfl : x = x' := eq_of_heq h2
        rfl
      have hindep' : iIndepFun (fun p : Σ k : Fin j, I k.succ => ξ p.1.succ p.2) μ :=
        hindep.precomp hg
      intro i
      have h := ih (fun k : Fin j => I k.succ) (fun k i => ξ k.succ i)
        (fun t => a (Fin.cons i t)) (fun k => F k.succ) hindep'
        (fun k i => hmeas k.succ i) (fun k i => hmean k.succ i) (fun k i => hbdd k.succ i)
      simp only [hZc, hTc]
      exact h
    -- Cauchy–Schwarz, then the induction hypothesis, on `E[(∑ᵢZᵢ²)²]`
    have hTc0 : ∀ i : I 0, 0 ≤ Tc i := by
      intro i
      simp only [hTc]
      exact Finset.sum_nonneg fun t _ => sq_nonneg _
    have hD0 : (0 : ℝ) ≤ (3 * B ^ 4) ^ j := pow_nonneg (by positivity) j
    have hN : ∀ i : I 0, Real.sqrt (∫ ω, Zc i ω ^ 4 ∂μ)
        ≤ Real.sqrt ((3 * B ^ 4) ^ j) * Tc i := by
      intro i
      calc Real.sqrt (∫ ω, Zc i ω ^ 4 ∂μ)
          ≤ Real.sqrt ((3 * B ^ 4) ^ j * Tc i ^ 2) := Real.sqrt_le_sqrt (hIH i)
        _ = Real.sqrt ((3 * B ^ 4) ^ j) * Real.sqrt (Tc i ^ 2) := Real.sqrt_mul hD0 _
        _ = Real.sqrt ((3 * B ^ 4) ^ j) * Tc i := by rw [Real.sqrt_sq (hTc0 i)]
    have hCS : ∫ ω, (∑ i ∈ F 0, Zc i ω ^ 2) ^ 2 ∂μ
        ≤ (3 * B ^ 4) ^ j * (∑ i ∈ F 0, Tc i) ^ 2 := by
      have h1 := integral_sq_sum_sq_le (Z := Zc) (fun i => (hZmeas i).mono hm₁le le_rfl)
        hZbdd (F 0)
      have h2 : (∑ i ∈ F 0, Real.sqrt (∫ ω, Zc i ω ^ 4 ∂μ)) ^ 2
          ≤ (Real.sqrt ((3 * B ^ 4) ^ j) * ∑ i ∈ F 0, Tc i) ^ 2 := by
        refine pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _) ?_ 2
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun i _ => hN i
      have h3 : (Real.sqrt ((3 * B ^ 4) ^ j) * ∑ i ∈ F 0, Tc i) ^ 2
          = (3 * B ^ 4) ^ j * (∑ i ∈ F 0, Tc i) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hD0]
      exact h1.trans (h2.trans (le_of_eq h3))
    -- `Z = ∑_{i ∈ I_0} ξ^{(0)}_i Zᵢ`, and the matching split of `∑_s a_s²`
    have hrw : ∀ ω, (∑ s ∈ Fintype.piFinset F, a s * ∏ k, ξ k (s k) ω)
        = ∑ i ∈ F 0, Zc i ω * ξ 0 i ω := by
      intro ω
      rw [sum_piFinset_succ F fun s => a s * ∏ k, ξ k (s k) ω]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hZc, Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      ring
    have hrwsum : (∑ s ∈ Fintype.piFinset F, a s ^ 2) = ∑ i ∈ F 0, Tc i := by
      rw [sum_piFinset_succ F fun s => a s ^ 2]
      simp only [hTc]
    have hgoal : ∫ ω, (∑ s ∈ Fintype.piFinset F, a s * ∏ k, ξ k (s k) ω) ^ 4 ∂μ
        = ∫ ω, (∑ i ∈ F 0, Zc i ω * ξ 0 i ω) ^ 4 ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards with ω
      rw [hrw ω]
    have hrand := integral_pow_four_random_le (m₀ := m₁) (Z := Zc) (ξ := ξ 0) (B := B)
      hm₁le hZmeas hZbdd (fun i => hmeas 0 i) (fun i => hbdd 0 i) (fun i => hmean 0 i)
      hind (F 0)
    rw [hgoal, hrwsum]
    calc ∫ ω, (∑ i ∈ F 0, Zc i ω * ξ 0 i ω) ^ 4 ∂μ
        ≤ 3 * B ^ 4 * ∫ ω, (∑ i ∈ F 0, Zc i ω ^ 2) ^ 2 ∂μ := hrand
      _ ≤ 3 * B ^ 4 * ((3 * B ^ 4) ^ j * (∑ i ∈ F 0, Tc i) ^ 2) :=
          mul_le_mul_of_nonneg_left hCS (by positivity)
      _ = (3 * B ^ 4) ^ (j + 1) * (∑ i ∈ F 0, Tc i) ^ 2 := by ring

end Levels

/-! ### Boundary values -/

section Boundary

variable {ι : Type*} {ξ : ι → Ω → ℝ} {a : ι → ℝ} {B : ℝ}

/-- If `F = ∅`, both sides of the case `j = 1` are `0`. -/
theorem boundary_empty_index [IsProbabilityMeasure μ] :
    ∫ ω, (∑ i ∈ (∅ : Finset ι), a i * ξ i ω) ^ 4 ∂μ = 0
      ∧ 3 * B ^ 4 * (∑ i ∈ (∅ : Finset ι), a i ^ 2) ^ 2 = 0 := by
  constructor <;> simp

/-- If `B = 0`, every `ξ i` is zero almost surely and both sides are `0`. -/
theorem boundary_bound_zero [IsProbabilityMeasure μ]
    (hbdd : ∀ i, ∀ᵐ ω ∂μ, |ξ i ω| ≤ 0) (F : Finset ι) :
    ∫ ω, (∑ i ∈ F, a i * ξ i ω) ^ 4 ∂μ = 0
      ∧ 3 * (0 : ℝ) ^ 4 * (∑ i ∈ F, a i ^ 2) ^ 2 = 0 := by
  refine ⟨?_, by ring⟩
  have hbdd' : ∀ i, ∀ᵐ ω ∂μ, |a i * ξ i ω| ≤ 0 := by
    intro i
    filter_upwards [hbdd i] with ω hω
    rw [abs_mul]
    have : |ξ i ω| = 0 := le_antisymm hω (abs_nonneg _)
    simp [this]
  have hsum := abs_sum_le_of_abs_le (c := fun _ => (0 : ℝ)) hbdd' F
  have hzero : ∀ᵐ ω ∂μ, (∑ i ∈ F, a i * ξ i ω) ^ 4 = 0 := by
    filter_upwards [hsum] with ω hω
    rw [Finset.sum_const_zero] at hω
    rw [abs_nonpos_iff.mp hω]
    simp
  rw [integral_congr_ae hzero]
  simp

/-- If `j = 0`, the empty product is `1`, `Z = a` is nonrandom, and the bound reads
`a⁴ ≤ (a²)²`, an equality for every `B`. -/
theorem boundary_level_zero (a : ℝ) : a ^ 4 ≤ (a ^ 2) ^ 2 := le_of_eq (by ring)

end Boundary

/-! ### Examples

The model is `n` independent fair signs, with `B = 1` and `E[ξᵢ²] = 1`.

* `witness`: `integral_pow_four_linear_le` at a two-element index set.
* `witness_random`: `integral_pow_four_random_le` with a random coefficient.
* `witness_two_levels`: `integral_pow_four_multilinear_le` at `j = 2` with two indices per
  level, where the left-hand side is `64` and the right-hand side is `144`. -/

section Witness

open scoped ENNReal

/-- A fair coin, as a measure on `Bool`. -/
noncomputable def coin : Measure Bool :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure coin := by
  constructor
  simp only [coin, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [show (1 : ℝ≥0∞) + 1 = 2 by norm_num,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

lemma integral_coin (f : Bool → ℝ) : ∫ b, f b ∂coin = (f true + f false) / 2 := by
  rw [coin, integral_smul_measure,
    integral_add_measure (Integrable.of_finite) (Integrable.of_finite),
    integral_dirac, integral_dirac]
  rw [ENNReal.toReal_inv]
  simp only [smul_eq_mul]
  norm_num
  ring

/-- `n` independent fair coins. -/
noncomputable def coins (n : ℕ) : Measure (Fin n → Bool) := Measure.pi fun _ => coin

instance (n : ℕ) : IsProbabilityMeasure (coins n) := by
  unfold coins
  infer_instance

/-- A fair sign, `±1` with equal probability, read off coordinate `i` of `n` coins. -/
noncomputable def sign2 {n : ℕ} (i : Fin n) (ω : Fin n → Bool) : ℝ := if ω i then 1 else -1

lemma measurable_sign2 {n : ℕ} (i : Fin n) : Measurable (sign2 i) := measurable_of_finite _

lemma integral_coins_eval {n : ℕ} (g : Bool → ℝ) (i : Fin n) :
    ∫ ω, g (ω i) ∂coins n = ∫ b, g b ∂coin := by
  have hmap : Measure.map (fun ω : Fin n → Bool => ω i) (coins n) = coin :=
    (measurePreserving_eval (fun _ => coin) i).map_eq
  rw [← hmap, integral_map (measurable_pi_apply i).aemeasurable
    ((measurable_of_finite g).aestronglyMeasurable)]

lemma iIndepFun_sign2 (n : ℕ) : iIndepFun (fun i : Fin n => sign2 i) (coins n) :=
  iIndepFun_pi (X := fun (_ : Fin n) (b : Bool) => if b then (1 : ℝ) else -1)
    fun _ => (measurable_of_finite _).aemeasurable

lemma integral_sign2 {n : ℕ} (i : Fin n) : ∫ ω, sign2 i ω ∂coins n = 0 := by
  have := integral_coins_eval (fun b => if b then (1 : ℝ) else -1) i
  rw [show (fun ω : Fin n → Bool => sign2 i ω) = fun ω => (if ω i then (1 : ℝ) else -1) from rfl,
    this, integral_coin]
  norm_num

lemma abs_sign2_le {n : ℕ} (i : Fin n) : ∀ᵐ ω ∂coins n, |sign2 i ω| ≤ 1 := by
  filter_upwards with ω
  unfold sign2
  by_cases h : ω i <;> simp [h]

/-- The second moment of a fair sign is `1`. -/
theorem witness_nondegenerate {n : ℕ} (i : Fin n) : ∫ ω, sign2 i ω ^ 2 ∂coins n = 1 := by
  have := integral_coins_eval (fun b => (if b then (1 : ℝ) else -1) ^ 2) i
  rw [show (fun ω : Fin n → Bool => sign2 i ω ^ 2)
      = fun ω => (if ω i then (1 : ℝ) else -1) ^ 2 from rfl,
    this, integral_coin]
  norm_num

/-- Every product of distinct fair signs has mean zero. -/
lemma integral_prod_sign2_eq_zero {n m : ℕ} [NeZero m] {g : Fin m → Fin n}
    (hg : Function.Injective g) :
    ∫ ω, ∏ i : Fin m, sign2 (g i) ω ∂coins n = 0 := by
  rw [((iIndepFun_sign2 n).precomp hg).integral_fun_prod_eq_prod_integral
    fun i => (measurable_sign2 (g i)).aestronglyMeasurable]
  exact Finset.prod_eq_zero (Finset.mem_univ (0 : Fin m)) (integral_sign2 (g 0))

/-- `integral_pow_four_linear_le` at two independent fair signs, with `B = 1` and coefficients
`aᵢ = 1`. -/
theorem witness :
    ∫ ω, (∑ i ∈ (Finset.univ : Finset (Fin 2)), (1 : ℝ) * sign2 i ω) ^ 4 ∂coins 2
      ≤ 3 * (1 : ℝ) ^ 4 * (∑ _i ∈ (Finset.univ : Finset (Fin 2)), (1 : ℝ) ^ 2) ^ 2 := by
  refine integral_pow_four_linear_le (a := fun _ => (1 : ℝ)) (B := 1) (iIndepFun_sign2 2)
    (fun i => measurable_sign2 i) (fun i => integral_sign2 i) (fun i => abs_sign2_le i)
    Finset.univ

/-- The index set of the example is nonempty. -/
theorem witness_index_nonempty : (Finset.univ : Finset (Fin 2)).Nonempty := ⟨0, by simp⟩

/-- `integral_pow_four_random_le` with the first fair sign as the coefficient, the second as the
summand, and the σ-algebra generated by the first as background. -/
theorem witness_random :
    ∫ ω, (∑ _i ∈ (Finset.univ : Finset (Fin 1)),
        sign2 (0 : Fin 2) ω * sign2 (1 : Fin 2) ω) ^ 4 ∂coins 2
      ≤ 3 * (1 : ℝ) ^ 4
        * ∫ ω, (∑ _i ∈ (Finset.univ : Finset (Fin 1)),
            sign2 (0 : Fin 2) ω ^ 2) ^ 2 ∂coins 2 := by
  refine integral_pow_four_random_le
    (m₀ := MeasurableSpace.comap (sign2 (0 : Fin 2)) inferInstance)
    (Z := fun _ => sign2 (0 : Fin 2)) (ξ := fun _ => sign2 (1 : Fin 2)) (B := 1)
    (measurable_sign2 (0 : Fin 2)).comap_le (fun _ => comap_measurable _)
    (fun _ => ⟨1, abs_sign2_le (0 : Fin 2)⟩) (fun _ => measurable_sign2 (1 : Fin 2))
    (fun _ => abs_sign2_le (1 : Fin 2)) (fun _ => integral_sign2 (1 : Fin 2)) ?_ Finset.univ
  intro G b hb
  have hG : G = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun x hx => hb ?_
    rwa [Subsingleton.elim x b] at hx
  subst hG
  have hrs : restSigma (MeasurableSpace.comap (sign2 (0 : Fin 2)) inferInstance)
      (fun _ : Fin 1 => sign2 (1 : Fin 2)) (∅ : Finset (Fin 1))
      = MeasurableSpace.comap (sign2 (0 : Fin 2)) inferInstance := by
    simp [restSigma]
  rw [hrs]
  exact (iIndepFun_sign2 2).indepFun (show (1 : Fin 2) ≠ 0 by decide)

/-- The site of index `i` at level `k` in the two-level example: `2k + i`. -/
def site4 (k i : Fin 2) : Fin 4 := ⟨2 * k.val + i.val, by omega⟩

lemma site4_injective : Function.Injective fun p : Σ _ : Fin 2, Fin 2 => site4 p.1 p.2 := by
  decide

/-- `integral_pow_four_multilinear_le` at `j = 2` over four independent fair signs, with
`I_0 = I_1 = Fin 2`, `B = 1` and `a ≡ 1`, so `Z = (σ₀ + σ₁)(σ₂ + σ₃)`. -/
theorem witness_two_levels :
    ∫ ω, (∑ s ∈ Fintype.piFinset (fun _ : Fin 2 => (Finset.univ : Finset (Fin 2))),
        (1 : ℝ) * ∏ k : Fin 2, sign2 (site4 k (s k)) ω) ^ 4 ∂coins 4
      ≤ (3 * (1 : ℝ) ^ 4) ^ 2
        * (∑ _s ∈ Fintype.piFinset (fun _ : Fin 2 => (Finset.univ : Finset (Fin 2))),
            (1 : ℝ) ^ 2) ^ 2 :=
  integral_pow_four_multilinear_le (B := 1) 2 (fun _ => Fin 2)
    (fun k i => sign2 (site4 k i)) (fun _ => (1 : ℝ)) (fun _ => Finset.univ)
    ((iIndepFun_sign2 4).precomp site4_injective)
    (fun k i => measurable_sign2 (site4 k i)) (fun k i => integral_sign2 (site4 k i))
    (fun k i => abs_sign2_le (site4 k i))

/-- In the two-level example `E[Z⁴] = 64`. Since `σ² = 1`,
`Z⁴ = 64(1 + σ₀σ₁ + σ₂σ₃ + σ₀σ₁σ₂σ₃)`, and each product of distinct signs has mean zero. -/
theorem witness_two_levels_nondegenerate :
    ∫ ω, (∑ s ∈ Fintype.piFinset (fun _ : Fin 2 => (Finset.univ : Finset (Fin 2))),
        (1 : ℝ) * ∏ k : Fin 2, sign2 (site4 k (s k)) ω) ^ 4 ∂coins 4 = 64 := by
  -- the multi-index sum is the product of the two level sums
  have hZ : ∀ ω : Fin 4 → Bool,
      (∑ s ∈ Fintype.piFinset (fun _ : Fin 2 => (Finset.univ : Finset (Fin 2))),
          (1 : ℝ) * ∏ k : Fin 2, sign2 (site4 k (s k)) ω)
        = (sign2 (0 : Fin 4) ω + sign2 (1 : Fin 4) ω)
          * (sign2 (2 : Fin 4) ω + sign2 (3 : Fin 4) ω) := by
    intro ω
    simp only [one_mul]
    rw [Finset.sum_prod_piFinset (Finset.univ : Finset (Fin 2))
      fun (k j : Fin 2) => sign2 (site4 k j) ω]
    simp [Fin.prod_univ_two, Fin.sum_univ_two, site4]
  -- the fourth power, expanded with `σ² = 1`
  have hpt : ∀ ω : Fin 4 → Bool,
      (∑ s ∈ Fintype.piFinset (fun _ : Fin 2 => (Finset.univ : Finset (Fin 2))),
          (1 : ℝ) * ∏ k : Fin 2, sign2 (site4 k (s k)) ω) ^ 4
        = 64 * (1 + sign2 (0 : Fin 4) ω * sign2 (1 : Fin 4) ω
            + sign2 (2 : Fin 4) ω * sign2 (3 : Fin 4) ω
            + sign2 (0 : Fin 4) ω * sign2 (1 : Fin 4) ω
              * (sign2 (2 : Fin 4) ω * sign2 (3 : Fin 4) ω)) := by
    intro ω
    rw [hZ ω]
    unfold sign2
    cases h0 : ω 0 <;> cases h1 : ω 1 <;> cases h2 : ω 2 <;> cases h3 : ω 3 <;> norm_num
  -- the three products of distinct signs have mean zero
  have hpair : ∀ g : Fin 2 → Fin 4, Function.Injective g →
      ∫ ω, sign2 (g 0) ω * sign2 (g 1) ω ∂coins 4 = 0 := by
    intro g hg
    have h := integral_prod_sign2_eq_zero (n := 4) (m := 2) hg
    rwa [show (fun ω : Fin 4 → Bool => ∏ i : Fin 2, sign2 (g i) ω)
        = fun ω => sign2 (g 0) ω * sign2 (g 1) ω from funext fun ω => by
      rw [Fin.prod_univ_two]] at h
  have h01 : ∫ ω, sign2 (0 : Fin 4) ω * sign2 (1 : Fin 4) ω ∂coins 4 = 0 :=
    hpair ![0, 1] (by decide)
  have h23 : ∫ ω, sign2 (2 : Fin 4) ω * sign2 (3 : Fin 4) ω ∂coins 4 = 0 :=
    hpair ![2, 3] (by decide)
  have h0123 : ∫ ω, sign2 (0 : Fin 4) ω * sign2 (1 : Fin 4) ω
      * (sign2 (2 : Fin 4) ω * sign2 (3 : Fin 4) ω) ∂coins 4 = 0 := by
    have h := integral_prod_sign2_eq_zero (n := 4) (m := 4)
      (g := (id : Fin 4 → Fin 4)) Function.injective_id
    rwa [show (fun ω : Fin 4 → Bool => ∏ i : Fin 4, sign2 (id i) ω)
        = fun ω => sign2 (0 : Fin 4) ω * sign2 (1 : Fin 4) ω
          * (sign2 (2 : Fin 4) ω * sign2 (3 : Fin 4) ω) from funext fun ω => by
      rw [Fin.prod_univ_four]
      simp only [id_eq]
      ring] at h
  -- integrate term by term
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_add (Integrable.of_finite.fun_add Integrable.of_finite) Integrable.of_finite,
    integral_add Integrable.of_finite Integrable.of_finite,
    integral_add Integrable.of_finite Integrable.of_finite, h01, h23, h0123]
  simp

end Witness

end Multilinear
end Multiway
