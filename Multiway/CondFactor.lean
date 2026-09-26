import Mathlib.Algebra.BigOperators.Pi
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Conditional

/-!
# Conditional independence factorizes `condExp`

For a family `X` conditionally independent given `𝒟` and bounded measurable complex `g i`,
`P[∏ i ∈ S, g i (X i ·) | 𝒟] =ᵐ[P] ∏ i ∈ S, P[g i (X i ·) | 𝒟]`. Consequently the conditional
characteristic function of a conditionally independent sum is the product of the conditional
characteristic functions. This is used in the proof of Theorem 4 of the paper. The proof lifts
`ProbabilityTheory.iCondIndepFun_iff_condExp_inter_preimage_eq_mul` from indicators to bounded
measurable functions, one slot at a time.

## Main results

* `condExp_prod_eq_prod_condExp`, `condExp_prod_eq_prod_condExp_real`: the factorization.
* `condCharFun_sum_eq_prod_condCharFun`: the conditional characteristic function of a sum.
* `condCharFun_sum_eq_prod_condCharFun_witness`: a model on which the hypotheses hold.

The ambient σ-algebra `mΩ` is an implicit variable and measures are written `@Measure Ω mΩ`, so
that they refer to the ambient σ-algebra rather than to `𝒟`.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace Multiway

namespace CondFactor

-- `𝒟` is declared before `mΩ`, so that `mΩ` is the default `MeasurableSpace Ω` instance.
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}

/-! ## Auxiliary lemmas -/

/-- A measurable function bounded almost everywhere is integrable, on a finite measure. -/
theorem integrable_of_ae_bound {F : Type*} [NormedAddCommGroup F] {P : @Measure Ω mΩ}
    [IsFiniteMeasure P] {u : Ω → F} (hu : AEStronglyMeasurable u P) {C : ℝ}
    (hub : ∀ᵐ ω ∂P, ‖u ω‖ ≤ C) : Integrable u P :=
  (integrable_const C).mono' hu hub

/-- A finite product of almost-everywhere bounded functions is almost everywhere bounded. -/
theorem exists_ae_bound_prod {K : Type*} [NormedField K] {ι : Type*} (P : @Measure Ω mΩ)
    {u : ι → Ω → K} (S : Finset ι) (h : ∀ i ∈ S, ∃ C, ∀ᵐ ω ∂P, ‖u i ω‖ ≤ C) :
    ∃ C, ∀ᵐ ω ∂P, ‖∏ i ∈ S, u i ω‖ ≤ C := by
  classical
  revert h
  induction S using Finset.induction_on with
  | empty => exact fun _ => ⟨1, Eventually.of_forall fun ω => by simp⟩
  | insert a S ha ih =>
    intro h
    obtain ⟨Ca, hCa⟩ := h a (Finset.mem_insert_self a S)
    obtain ⟨C, hC⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine ⟨max Ca 0 * max C 0, ?_⟩
    filter_upwards [hCa, hC] with ω h1 h2
    rw [Finset.prod_insert ha, norm_mul]
    exact mul_le_mul (le_max_of_le_left h1) (le_max_of_le_left h2) (norm_nonneg _)
      (le_max_right _ _)

/-- A conditional expectation inherits an almost-everywhere norm bound from its integrand
(conditional Jensen, `MeasureTheory.norm_condExp_le`). -/
theorem ae_norm_condExp_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (h𝒟 : 𝒟 ≤ mΩ) (P : @Measure Ω mΩ) [IsFiniteMeasure P] {u : Ω → F}
    (hu : Integrable u P) {C : ℝ} (hub : ∀ᵐ ω ∂P, ‖u ω‖ ≤ C) :
    ∀ᵐ ω ∂P, ‖condExp 𝒟 P u ω‖ ≤ C := by
  have h1 := norm_condExp_le (m := 𝒟) (μ := P) u
  have h2 : condExp 𝒟 P (fun ω => ‖u ω‖) ≤ᵐ[P] condExp 𝒟 P (fun _ => C) :=
    condExp_mono hu.norm (integrable_const C) hub
  rw [condExp_const h𝒟] at h2
  filter_upwards [h1, h2] with ω hω1 hω2
  exact hω1.trans hω2

/-- An indicator of a preimage, evaluated, is the indicator of the set evaluated at the image. -/
theorem indicator_preimage_apply {β F : Type*} [Zero F] (s : Set β) (Y : Ω → β) (c : F) (ω : Ω) :
    Set.indicator (Y ⁻¹' s) (fun _ => c) ω = Set.indicator s (fun _ => c) (Y ω) := by
  by_cases h : Y ω ∈ s <;> simp [Set.mem_preimage, h]

/-- The real-to-complex coercion commutes with a finite product. -/
theorem ofReal_prod {ι : Type*} (S : Finset ι) (v : ι → ℝ) :
    ((∏ i ∈ S, v i : ℝ) : ℂ) = ∏ i ∈ S, ((v i : ℝ) : ℂ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul, ih]

/-- Conditional expectation commutes with the real-to-complex coercion
(`ContinuousLinearMap.comp_condExp_comm` at `Complex.ofRealCLM`). -/
theorem condExp_ofReal (P : @Measure Ω mΩ) {u : Ω → ℝ}
    (hu : Integrable u P) :
    condExp 𝒟 P (fun ω => ((u ω : ℝ) : ℂ)) =ᵐ[P] fun ω => ((condExp 𝒟 P u ω : ℝ) : ℂ) := by
  have h := (Complex.ofRealCLM.comp_condExp_comm (m := 𝒟) hu).symm
  simpa [Function.comp_def] using h

/-- The complex conditional expectation of an indicator is the coercion of the real one. -/
theorem condExp_indicator_ofReal (P : @Measure Ω mΩ)
    [IsProbabilityMeasure P] {A : Set Ω} (hA : MeasurableSet A) :
    condExp 𝒟 P (Set.indicator A fun _ => (1 : ℂ))
      =ᵐ[P] fun ω => ((condExp 𝒟 P (Set.indicator A fun _ => (1 : ℝ)) ω : ℝ) : ℂ) := by
  have hbd : ∀ ω, ‖Set.indicator A (fun _ => (1 : ℝ)) ω‖ ≤ 1 := by
    intro ω; by_cases h : ω ∈ A <;> simp [h]
  have hint : Integrable (Set.indicator A fun _ => (1 : ℝ)) P :=
    integrable_of_ae_bound (measurable_const.indicator hA).aestronglyMeasurable
      (Eventually.of_forall hbd)
  have hEq : (Set.indicator A fun _ => (1 : ℂ))
      = fun ω => ((Set.indicator A (fun _ => (1 : ℝ)) ω : ℝ) : ℂ) := by
    funext ω; by_cases h : ω ∈ A <;> simp [h]
  rw [hEq]
  exact condExp_ofReal 𝒟 P hint

/-! ## The functional lift, at the level of ordinary integrals

The one-slot lift below reduces, through the defining property of `condExp`, to a statement about
ordinary Bochner integrals proved by linearity and dominated convergence. -/

/-- If `∫ 1_s(Y) · W = 0` for every measurable `s`, then `∫ f(Y) · W = 0` for every bounded
measurable `f`. The proof passes through simple functions (`SimpleFunc.induction`) and then
bounded measurable functions (`SimpleFunc.approxOn` and dominated convergence). -/
theorem integral_comp_mul_eq_zero {β : Type*} [MeasurableSpace β] (P : @Measure Ω mΩ)
    [IsProbabilityMeasure P] {Y : Ω → β} (hY : Measurable Y) {W : Ω → ℂ} (hW : Measurable W)
    {CW : ℝ} (hWb : ∀ᵐ ω ∂P, ‖W ω‖ ≤ CW)
    (hzero : ∀ s : Set β, MeasurableSet s →
      ∫ ω, Set.indicator s (fun _ => (1 : ℂ)) (Y ω) * W ω ∂P = 0)
    {f : β → ℂ} (hf : Measurable f) {Cf : ℝ} (hfb : ∀ x, ‖f x‖ ≤ Cf) :
    ∫ ω, f (Y ω) * W ω ∂P = 0 := by
  classical
  have hWb' : ∀ᵐ ω ∂P, ‖W ω‖ ≤ max CW 0 := hWb.mono fun _ h => le_max_of_le_left h
  -- integrability of `u ∘ Y · W` for every bounded measurable `u`
  have hint : ∀ u : β → ℂ, Measurable u → ∀ C : ℝ, (∀ x, ‖u x‖ ≤ C) →
      Integrable (fun ω => u (Y ω) * W ω) P := by
    intro u hu C hC
    refine integrable_of_ae_bound ((hu.comp hY).mul hW).aestronglyMeasurable
      (C := max C 0 * max CW 0) ?_
    filter_upwards [hWb'] with ω hω
    rw [norm_mul]
    exact mul_le_mul (le_max_of_le_left (hC _)) hω (norm_nonneg _) (le_max_right _ _)
  -- step one: simple functions
  have hsimple : ∀ φ : SimpleFunc β ℂ, ∫ ω, φ (Y ω) * W ω ∂P = 0 := by
    intro φ
    induction φ using SimpleFunc.induction with
    | @const c s hs =>
      have hpt : ∀ ω, (SimpleFunc.piecewise s hs (SimpleFunc.const β c)
          (SimpleFunc.const β 0)) (Y ω) * W ω
          = c * (Set.indicator s (fun _ => (1 : ℂ)) (Y ω) * W ω) := by
        intro ω
        by_cases h : Y ω ∈ s <;>
          simp [SimpleFunc.piecewise_apply, h]
      simp_rw [hpt]
      rw [integral_const_mul, hzero s hs, mul_zero]
    | @add φ ψ _ hφ hψ =>
      obtain ⟨Cφ, hCφ⟩ := (φ.map fun z : ℂ => ‖z‖).exists_forall_le
      obtain ⟨Cψ, hCψ⟩ := (ψ.map fun z : ℂ => ‖z‖).exists_forall_le
      have hIφ := hint φ φ.measurable Cφ (by simpa using hCφ)
      have hIψ := hint ψ ψ.measurable Cψ (by simpa using hCψ)
      have hpt : ∀ ω, (φ + ψ) (Y ω) * W ω = φ (Y ω) * W ω + ψ (Y ω) * W ω := by
        intro ω; simp [add_mul]
      simp_rw [hpt]
      rw [integral_add hIφ hIψ, hφ, hψ, add_zero]
  -- step two: a uniformly bounded simple approximation of `f`
  have happrox : ∃ φ : ℕ → SimpleFunc β ℂ,
      (∀ x, Tendsto (fun n => φ n x) atTop (𝓝 (f x))) ∧ ∀ n x, ‖φ n x‖ ≤ Cf + Cf := by
    refine ⟨fun n => SimpleFunc.approxOn f hf Set.univ 0 (Set.mem_univ 0) n, fun x => ?_,
      fun n x => ?_⟩
    · exact SimpleFunc.tendsto_approxOn hf (Set.mem_univ (0 : ℂ)) (by simp)
    · exact (SimpleFunc.norm_approxOn_zero_le hf (Set.mem_univ (0 : ℂ)) x n).trans
        (add_le_add (hfb x) (hfb x))
  obtain ⟨φ, hφlim, hφbd⟩ := happrox
  have hbound : ∀ n, ∀ᵐ ω ∂P, ‖φ n (Y ω) * W ω‖ ≤ (Cf + Cf) * max CW 0 := by
    intro n
    filter_upwards [hWb'] with ω hω
    have hCf0 : (0 : ℝ) ≤ Cf := (norm_nonneg _).trans (hfb (Y ω))
    rw [norm_mul]
    exact mul_le_mul (hφbd n (Y ω)) hω (norm_nonneg _) (by linarith)
  have hdct := tendsto_integral_of_dominated_convergence
    (F := fun n ω => φ n (Y ω) * W ω) (f := fun ω => f (Y ω) * W ω)
    (fun _ => (Cf + Cf) * max CW 0)
    (fun n => (((φ n).measurable.comp hY).mul hW).aestronglyMeasurable)
    (integrable_const _) hbound
    (Eventually.of_forall fun ω => (hφlim (Y ω)).mul tendsto_const_nhds)
  have hz : ∀ n, ∫ ω, φ n (Y ω) * W ω ∂P = 0 := fun n => hsimple (φ n)
  simp only [hz] at hdct
  exact (tendsto_nhds_unique tendsto_const_nhds hdct).symm

/-! ## The one-slot lift: from indicators to bounded measurable functions -/

/-- Let `G` be bounded measurable, let `H` be bounded and `𝒟`-measurable, and
suppose that for every measurable `s`,

`P[1_s(Y) · G | 𝒟] =ᵐ P[1_s(Y) | 𝒟] · H`.

Then the same identity holds with `1_s` replaced by any bounded measurable `f : β → ℂ`. -/
theorem condExp_mul_of_indicator (h𝒟 : 𝒟 ≤ mΩ) (P : @Measure Ω mΩ)
    [IsProbabilityMeasure P] {β : Type*} [MeasurableSpace β] {Y : Ω → β} (hY : Measurable Y)
    {G : Ω → ℂ} (hG : Measurable G) (hGb : ∃ C, ∀ᵐ ω ∂P, ‖G ω‖ ≤ C)
    {H : Ω → ℂ} (hH : StronglyMeasurable[𝒟] H) (hHb : ∃ C, ∀ᵐ ω ∂P, ‖H ω‖ ≤ C)
    (hkey : ∀ s : Set β, MeasurableSet s →
      condExp 𝒟 P (fun ω => Set.indicator s (fun _ => (1 : ℂ)) (Y ω) * G ω)
        =ᵐ[P] fun ω =>
          condExp 𝒟 P (fun ω => Set.indicator s (fun _ => (1 : ℂ)) (Y ω)) ω * H ω)
    {f : β → ℂ} (hf : Measurable f) {Cf : ℝ} (hfb : ∀ x, ‖f x‖ ≤ Cf) :
    condExp 𝒟 P (fun ω => f (Y ω) * G ω)
      =ᵐ[P] fun ω => condExp 𝒟 P (fun ω => f (Y ω)) ω * H ω := by
  classical
  obtain ⟨CG, hCG⟩ := hGb
  obtain ⟨CH, hCH⟩ := hHb
  have hHmeas : Measurable H := (hH.mono h𝒟).measurable
  -- integrability of `u ∘ Y · V` for `u` bounded on `β` and `V` bounded on `Ω`
  have hint : ∀ V : Ω → ℂ, Measurable V → (∃ C, ∀ᵐ ω ∂P, ‖V ω‖ ≤ C) →
      ∀ u : β → ℂ, Measurable u → (∃ C, ∀ x, ‖u x‖ ≤ C) →
      Integrable (fun ω => u (Y ω) * V ω) P := by
    rintro V hV ⟨CV, hCV⟩ u hu ⟨Cu, hCu⟩
    refine integrable_of_ae_bound ((hu.comp hY).mul hV).aestronglyMeasurable
      (C := max Cu 0 * max CV 0) ?_
    filter_upwards [hCV] with ω hω
    rw [norm_mul]
    exact mul_le_mul (le_max_of_le_left (hCu _)) (le_max_of_le_left hω) (norm_nonneg _)
      (le_max_right _ _)
  have hcomp : ∀ u : β → ℂ, Measurable u → (∃ C, ∀ x, ‖u x‖ ≤ C) →
      Integrable (fun ω => u (Y ω)) P := by
    rintro u hu ⟨Cu, hCu⟩
    exact integrable_of_ae_bound (hu.comp hY).aestronglyMeasurable
      (Eventually.of_forall fun ω => hCu (Y ω))
  -- the pull-out property, with `H` the `𝒟`-measurable factor
  have hpull : ∀ u : β → ℂ, Measurable u → (∃ C, ∀ x, ‖u x‖ ≤ C) →
      condExp 𝒟 P (fun ω => u (Y ω) * H ω)
        =ᵐ[P] fun ω => condExp 𝒟 P (fun ω => u (Y ω)) ω * H ω := by
    intro u hu hub
    have h2 := hint H hHmeas ⟨CH, hCH⟩ u hu hub
    have h3 := condExp_bilin_of_aestronglyMeasurable_right (ContinuousLinearMap.mul ℝ ℂ)
      (m := 𝒟) (μ := P) hH.aestronglyMeasurable
      (f := fun ω => u (Y ω)) (by simpa using h2) (hcomp u hu hub)
    simpa using h3
  -- testing `P[u(Y) | 𝒟] · H` against a `𝒟`-measurable set
  have hI : ∀ u : β → ℂ, Measurable u → (∃ C, ∀ x, ‖u x‖ ≤ C) →
      ∀ A : Set Ω, MeasurableSet[𝒟] A →
      ∫ ω in A, condExp 𝒟 P (fun ω => u (Y ω)) ω * H ω ∂P = ∫ ω in A, u (Y ω) * H ω ∂P := by
    intro u hu hub A hA
    have h2 := hint H hHmeas ⟨CH, hCH⟩ u hu hub
    calc ∫ ω in A, condExp 𝒟 P (fun ω => u (Y ω)) ω * H ω ∂P
        = ∫ ω in A, condExp 𝒟 P (fun ω => u (Y ω) * H ω) ω ∂P := by
          refine setIntegral_congr_ae (h𝒟 A hA) ?_
          filter_upwards [hpull u hu hub] with ω hω _
          exact hω.symm
      _ = ∫ ω in A, u (Y ω) * H ω ∂P := setIntegral_condExp h𝒟 h2 hA
  -- the hypothesis, read as an equality of set integrals
  have hindbd : ∀ s : Set β, ∃ C, ∀ x, ‖Set.indicator s (fun _ => (1 : ℂ)) x‖ ≤ C := by
    intro s
    exact ⟨1, fun x => by by_cases h : x ∈ s <;> simp [h]⟩
  have hGH : ∀ A : Set Ω, MeasurableSet[𝒟] A → ∀ s : Set β, MeasurableSet s →
      ∫ ω in A, Set.indicator s (fun _ => (1 : ℂ)) (Y ω) * G ω ∂P
        = ∫ ω in A, Set.indicator s (fun _ => (1 : ℂ)) (Y ω) * H ω ∂P := by
    intro A hA s hs
    have hu : Measurable (Set.indicator s fun _ => (1 : ℂ)) := measurable_const.indicator hs
    have h1 := hint G hG ⟨CG, hCG⟩ _ hu (hindbd s)
    calc ∫ ω in A, Set.indicator s (fun _ => (1 : ℂ)) (Y ω) * G ω ∂P
        = ∫ ω in A, condExp 𝒟 P
            (fun ω => Set.indicator s (fun _ => (1 : ℂ)) (Y ω) * G ω) ω ∂P :=
          (setIntegral_condExp h𝒟 h1 hA).symm
      _ = ∫ ω in A,
            condExp 𝒟 P (fun ω => Set.indicator s (fun _ => (1 : ℂ)) (Y ω)) ω * H ω ∂P := by
          refine setIntegral_congr_ae (h𝒟 A hA) ?_
          filter_upwards [hkey s hs] with ω hω _
          exact hω
      _ = ∫ ω in A, Set.indicator s (fun _ => (1 : ℂ)) (Y ω) * H ω ∂P := hI _ hu (hindbd s) A hA
  -- the same conclusion for a general bounded measurable `f`, via `integral_comp_mul_eq_zero`
  have hfin : ∀ A : Set Ω, MeasurableSet[𝒟] A →
      ∫ ω in A, f (Y ω) * G ω ∂P = ∫ ω in A, f (Y ω) * H ω ∂P := by
    intro A hA
    have hAm : MeasurableSet A := h𝒟 A hA
    have hWmeas : Measurable (fun ω => Set.indicator A (fun _ => (1 : ℂ)) ω * (G ω - H ω)) :=
      (measurable_const.indicator hAm).mul (hG.sub hHmeas)
    have hWbd : ∀ᵐ ω ∂P,
        ‖Set.indicator A (fun _ => (1 : ℂ)) ω * (G ω - H ω)‖ ≤ max CG 0 + max CH 0 := by
      filter_upwards [hCG, hCH] with ω h1 h2
      have hi : ‖Set.indicator A (fun _ => (1 : ℂ)) ω‖ ≤ 1 := by
        by_cases h : ω ∈ A <;> simp [h]
      calc ‖Set.indicator A (fun _ => (1 : ℂ)) ω * (G ω - H ω)‖
          = ‖Set.indicator A (fun _ => (1 : ℂ)) ω‖ * ‖G ω - H ω‖ := norm_mul _ _
        _ ≤ 1 * (‖G ω‖ + ‖H ω‖) :=
            mul_le_mul hi (norm_sub_le _ _) (norm_nonneg _) zero_le_one
        _ ≤ max CG 0 + max CH 0 := by
            rw [one_mul]
            exact add_le_add (le_max_of_le_left h1) (le_max_of_le_left h2)
    have hrepr : ∀ u : β → ℂ, Measurable u → (∃ C, ∀ x, ‖u x‖ ≤ C) →
        ∫ ω, u (Y ω) * (Set.indicator A (fun _ => (1 : ℂ)) ω * (G ω - H ω)) ∂P
          = ∫ ω in A, u (Y ω) * G ω ∂P - ∫ ω in A, u (Y ω) * H ω ∂P := by
      intro u hu hub
      have hEq : (fun ω => u (Y ω) * (Set.indicator A (fun _ => (1 : ℂ)) ω * (G ω - H ω)))
          = fun ω => Set.indicator A (fun ω => u (Y ω) * G ω - u (Y ω) * H ω) ω := by
        funext ω
        by_cases h : ω ∈ A <;> simp [h, mul_sub]
      rw [hEq, integral_indicator hAm]
      exact integral_sub (hint G hG ⟨CG, hCG⟩ u hu hub).restrict
        (hint H hHmeas ⟨CH, hCH⟩ u hu hub).restrict
    have h0 : ∫ ω, f (Y ω) * (Set.indicator A (fun _ => (1 : ℂ)) ω * (G ω - H ω)) ∂P = 0 := by
      refine integral_comp_mul_eq_zero P hY hWmeas hWbd ?_ hf hfb
      intro s hs
      rw [hrepr _ (measurable_const.indicator hs) (hindbd s), hGH A hA s hs, sub_self]
    have hrf := hrepr f hf ⟨Cf, hfb⟩
    rw [h0] at hrf
    exact sub_eq_zero.1 hrf.symm
  -- the defining property of the conditional expectation
  have hgint : Integrable (fun ω => condExp 𝒟 P (fun ω => f (Y ω)) ω * H ω) P :=
    (integrable_condExp (m := 𝒟) (μ := P) (f := fun ω => f (Y ω) * H ω)).congr
      (hpull f hf ⟨Cf, hfb⟩)
  refine (ae_eq_condExp_of_forall_setIntegral_eq h𝒟 (hint G hG ⟨CG, hCG⟩ f hf ⟨Cf, hfb⟩)
    (fun A _ _ => hgint.integrableOn) (fun A hA _ => ?_)
    (StronglyMeasurable.aestronglyMeasurable
      (StronglyMeasurable.mul
        (stronglyMeasurable_condExp (m := 𝒟) (μ := P) (f := fun ω => f (Y ω))) hH))).symm
  rw [hI f hf ⟨Cf, hfb⟩ A hA]
  exact (hfin A hA).symm

/-! ## The two-dimensional induction -/

/-- Suppose the slots in `T` hold bounded measurable functions and the slots in the disjoint set
`S` hold indicators. Then the conditional expectation of the whole product factorizes. The proof is
by induction on `T`, applying the inductive hypothesis with `S` replaced by `insert a S`. -/
theorem condExp_prod_mul_prod_indicator [StandardBorelSpace Ω] {ι : Type*} {β : ι → Type*}
    [mβ : ∀ i, MeasurableSpace (β i)] (h𝒟 : 𝒟 ≤ mΩ)
    (P : @Measure Ω mΩ) [IsProbabilityMeasure P] {X : ∀ i, Ω → β i} (hX : ∀ i, Measurable (X i))
    (hCI : iCondIndepFun 𝒟 h𝒟 X P) {g : ∀ i, β i → ℂ} (hg : ∀ i, Measurable (g i))
    (hgb : ∀ i, ∃ C, ∀ x, ‖g i x‖ ≤ C) (T : Finset ι) :
    ∀ S : Finset ι, Disjoint T S → ∀ sets : ∀ i, Set (β i), (∀ i, MeasurableSet (sets i)) →
      condExp 𝒟 P (fun ω => (∏ i ∈ T, g i (X i ω)) *
          ∏ i ∈ S, Set.indicator (sets i) (fun _ => (1 : ℂ)) (X i ω))
        =ᵐ[P] fun ω => (∏ i ∈ T, condExp 𝒟 P (fun ω => g i (X i ω)) ω) *
          ∏ i ∈ S, condExp 𝒟 P (fun ω =>
            Set.indicator (sets i) (fun _ => (1 : ℂ)) (X i ω)) ω := by
  classical
  -- the two kinds of slot, as measurable and bounded functions of `ω`
  have hgX : ∀ i, Measurable fun ω => g i (X i ω) := fun i => (hg i).comp (hX i)
  have hindX : ∀ (sets : ∀ i, Set (β i)), (∀ i, MeasurableSet (sets i)) → ∀ i,
      Measurable fun ω => Set.indicator (sets i) (fun _ => (1 : ℂ)) (X i ω) :=
    fun sets hsets i => (measurable_const.indicator (hsets i)).comp (hX i)
  have hgXint : ∀ i, Integrable (fun ω => g i (X i ω)) P := by
    intro i
    obtain ⟨C, hC⟩ := hgb i
    exact integrable_of_ae_bound (hgX i).aestronglyMeasurable
      (Eventually.of_forall fun ω => hC _)
  -- almost-everywhere bounds on the conditional expectations that make up `H`
  have hgCbd : ∀ i, ∃ C, ∀ᵐ ω ∂P, ‖condExp 𝒟 P (fun ω => g i (X i ω)) ω‖ ≤ C := by
    intro i
    obtain ⟨C, hC⟩ := hgb i
    exact ⟨C, ae_norm_condExp_le 𝒟 h𝒟 P (hgXint i) (Eventually.of_forall fun ω => hC _)⟩
  have hiCbd : ∀ (sets : ∀ i, Set (β i)), (∀ i, MeasurableSet (sets i)) → ∀ i,
      ∃ C, ∀ᵐ ω ∂P,
        ‖condExp 𝒟 P (fun ω => Set.indicator (sets i) (fun _ => (1 : ℂ)) (X i ω)) ω‖ ≤ C := by
    intro sets hsets i
    have hb : ∀ ω, ‖Set.indicator (sets i) (fun _ => (1 : ℂ)) (X i ω)‖ ≤ 1 := by
      intro ω; by_cases h : X i ω ∈ sets i <;> simp [h]
    refine ⟨1, ae_norm_condExp_le 𝒟 h𝒟 P ?_ (Eventually.of_forall hb)⟩
    exact integrable_of_ae_bound (hindX sets hsets i).aestronglyMeasurable
      (Eventually.of_forall hb)
  induction T using Finset.induction_on with
  | empty =>
    intro S _ sets hsets
    simp only [Finset.prod_empty, one_mul]
    -- the product of indicators is the indicator of the intersection
    have hcap : MeasurableSet (⋂ i ∈ S, X i ⁻¹' sets i) :=
      S.measurableSet_biInter fun i _ => (hX i) (hsets i)
    have hprodC : (fun ω => ∏ i ∈ S, Set.indicator (sets i) (fun _ => (1 : ℂ)) (X i ω))
        = Set.indicator (⋂ i ∈ S, X i ⁻¹' sets i) fun _ => (1 : ℂ) := by
      funext ω
      have h1 : ∀ i, Set.indicator (sets i) (fun _ => (1 : ℂ)) (X i ω)
          = Set.indicator (X i ⁻¹' sets i) (fun _ => (1 : ℂ)) ω :=
        fun i => (indicator_preimage_apply (sets i) (X i) (1 : ℂ) ω).symm
      have hpow : ((fun _ : Ω => (1 : ℂ)) ^ S.card) = fun _ : Ω => (1 : ℂ) := by
        funext x; simp
      simp only [h1]
      rw [prod_indicator_const_apply, hpow]
    have hsingle : ∀ i, (fun ω => Set.indicator (sets i) (fun _ => (1 : ℂ)) (X i ω))
        = Set.indicator (X i ⁻¹' sets i) fun _ => (1 : ℂ) := by
      intro i
      funext ω
      exact (indicator_preimage_apply (sets i) (X i) (1 : ℂ) ω).symm
    have hML := (iCondIndepFun_iff_condExp_inter_preimage_eq_mul mβ X hX).1 hCI S
      (sets := sets) fun i _ => hsets i
    have hstep1 : condExp 𝒟 P
        (fun ω => ∏ i ∈ S, Set.indicator (sets i) (fun _ => (1 : ℂ)) (X i ω))
        =ᵐ[P] fun ω => ((condExp 𝒟 P
          (Set.indicator (⋂ i ∈ S, X i ⁻¹' sets i) fun _ => (1 : ℝ)) ω : ℝ) : ℂ) := by
      rw [hprodC]
      exact condExp_indicator_ofReal 𝒟 P hcap
    have hstep2 : ∀ i ∈ S,
        condExp 𝒟 P (fun ω => Set.indicator (sets i) (fun _ => (1 : ℂ)) (X i ω))
          =ᵐ[P] fun ω => ((condExp 𝒟 P
            (Set.indicator (X i ⁻¹' sets i) fun _ => (1 : ℝ)) ω : ℝ) : ℂ) := by
      intro i _
      rw [hsingle i]
      exact condExp_indicator_ofReal 𝒟 P ((hX i) (hsets i))
    have hall : ∀ᵐ ω ∂P, ∀ i ∈ S,
        condExp 𝒟 P (fun ω => Set.indicator (sets i) (fun _ => (1 : ℂ)) (X i ω)) ω
          = ((condExp 𝒟 P (Set.indicator (X i ⁻¹' sets i) fun _ => (1 : ℝ)) ω : ℝ) : ℂ) :=
      (eventually_all_finset S).2 hstep2
    filter_upwards [hstep1, hML, hall] with ω h1 h2 h3
    rw [h1, h2, Finset.prod_apply, ofReal_prod]
    exact Finset.prod_congr rfl fun i hi => (h3 i hi).symm
  | insert a T ha ih =>
    intro S hdisj sets hsets
    obtain ⟨Ca, hCa⟩ := hgb a
    have haS : a ∉ S := (Finset.disjoint_insert_left.1 hdisj).1
    have hdisjT : Disjoint T (insert a S) :=
      Finset.disjoint_insert_right.2 ⟨ha, (Finset.disjoint_insert_left.1 hdisj).2⟩
    -- split the `a`-slot off, on both sides
    have hgoalL : (fun ω => (∏ i ∈ insert a T, g i (X i ω)) *
          ∏ i ∈ S, Set.indicator (sets i) (fun _ => (1 : ℂ)) (X i ω))
        = fun ω => g a (X a ω) * ((∏ i ∈ T, g i (X i ω)) *
          ∏ i ∈ S, Set.indicator (sets i) (fun _ => (1 : ℂ)) (X i ω)) := by
      funext ω; rw [Finset.prod_insert ha, mul_assoc]
    have hgoalR : (fun ω => (∏ i ∈ insert a T, condExp 𝒟 P (fun ω => g i (X i ω)) ω) *
          ∏ i ∈ S, condExp 𝒟 P
            (fun ω => Set.indicator (sets i) (fun _ => (1 : ℂ)) (X i ω)) ω)
        = fun ω => condExp 𝒟 P (fun ω => g a (X a ω)) ω *
          ((∏ i ∈ T, condExp 𝒟 P (fun ω => g i (X i ω)) ω) *
          ∏ i ∈ S, condExp 𝒟 P
            (fun ω => Set.indicator (sets i) (fun _ => (1 : ℂ)) (X i ω)) ω) := by
      funext ω; rw [Finset.prod_insert ha, mul_assoc]
    rw [hgoalL, hgoalR]
    -- `G`: the slots other than `a`
    have hGmeas : Measurable fun ω => (∏ i ∈ T, g i (X i ω)) *
        ∏ i ∈ S, Set.indicator (sets i) (fun _ => (1 : ℂ)) (X i ω) :=
      (Finset.measurable_prod T fun i _ => hgX i).mul
        (Finset.measurable_prod S fun i _ => hindX sets hsets i)
    have hGbd : ∃ C, ∀ᵐ ω ∂P, ‖(∏ i ∈ T, g i (X i ω)) *
        ∏ i ∈ S, Set.indicator (sets i) (fun _ => (1 : ℂ)) (X i ω)‖ ≤ C := by
      obtain ⟨C1, hC1⟩ := exists_ae_bound_prod (K := ℂ) P (u := fun i ω => g i (X i ω)) T
        fun i _ => (hgb i).imp fun _ h => Eventually.of_forall fun ω => h _
      obtain ⟨C2, hC2⟩ := exists_ae_bound_prod (K := ℂ) P
        (u := fun i ω => Set.indicator (sets i) (fun _ => (1 : ℂ)) (X i ω)) S
        fun i _ => ⟨1, Eventually.of_forall fun ω => by
          by_cases h : X i ω ∈ sets i <;> simp [h]⟩
      refine ⟨max C1 0 * max C2 0, ?_⟩
      filter_upwards [hC1, hC2] with ω h1 h2
      rw [norm_mul]
      exact mul_le_mul (le_max_of_le_left h1) (le_max_of_le_left h2) (norm_nonneg _)
        (le_max_right _ _)
    -- `H`: the corresponding product of conditional expectations
    have hHsm : StronglyMeasurable[𝒟] fun ω =>
        (∏ i ∈ T, condExp 𝒟 P (fun ω => g i (X i ω)) ω) *
        ∏ i ∈ S, condExp 𝒟 P
          (fun ω => Set.indicator (sets i) (fun _ => (1 : ℂ)) (X i ω)) ω :=
      (Finset.stronglyMeasurable_fun_prod T fun i _ => stronglyMeasurable_condExp).mul
        (Finset.stronglyMeasurable_fun_prod S fun i _ => stronglyMeasurable_condExp)
    have hHbd : ∃ C, ∀ᵐ ω ∂P, ‖(∏ i ∈ T, condExp 𝒟 P (fun ω => g i (X i ω)) ω) *
        ∏ i ∈ S, condExp 𝒟 P
          (fun ω => Set.indicator (sets i) (fun _ => (1 : ℂ)) (X i ω)) ω‖ ≤ C := by
      obtain ⟨C1, hC1⟩ := exists_ae_bound_prod (K := ℂ) P
        (u := fun i ω => condExp 𝒟 P (fun ω => g i (X i ω)) ω) T fun i _ => hgCbd i
      obtain ⟨C2, hC2⟩ := exists_ae_bound_prod (K := ℂ) P
        (u := fun i ω => condExp 𝒟 P
          (fun ω => Set.indicator (sets i) (fun _ => (1 : ℂ)) (X i ω)) ω) S
        fun i _ => hiCbd sets hsets i
      refine ⟨max C1 0 * max C2 0, ?_⟩
      filter_upwards [hC1, hC2] with ω h1 h2
      rw [norm_mul]
      exact mul_le_mul (le_max_of_le_left h1) (le_max_of_le_left h2) (norm_nonneg _)
        (le_max_right _ _)
    -- the hypothesis of the one-slot lift, supplied by the inductive hypothesis at `insert a S`
    refine condExp_mul_of_indicator 𝒟 h𝒟 P (hX a) hGmeas hGbd hHsm hHbd ?_ (hg a) hCa
    intro s hs
    have hsets' : ∀ i, MeasurableSet (Function.update sets a s i) := by
      intro i
      by_cases h : i = a
      · subst h; rw [Function.update_self]; exact hs
      · rw [Function.update_of_ne h]; exact hsets i
    have hIH := ih (insert a S) hdisjT (Function.update sets a s) hsets'
    have hupdL : ∀ ω : Ω, ∏ i ∈ insert a S,
        Set.indicator (Function.update sets a s i) (fun _ => (1 : ℂ)) (X i ω)
        = Set.indicator s (fun _ => (1 : ℂ)) (X a ω) *
          ∏ i ∈ S, Set.indicator (sets i) (fun _ => (1 : ℂ)) (X i ω) := by
      intro ω
      rw [Finset.prod_insert haS, Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [Function.update_of_ne (by rintro rfl; exact haS hi)]
    have hupdR : ∀ ω : Ω, ∏ i ∈ insert a S, condExp 𝒟 P (fun ω =>
        Set.indicator (Function.update sets a s i) (fun _ => (1 : ℂ)) (X i ω)) ω
        = condExp 𝒟 P (fun ω => Set.indicator s (fun _ => (1 : ℂ)) (X a ω)) ω *
          ∏ i ∈ S, condExp 𝒟 P
            (fun ω => Set.indicator (sets i) (fun _ => (1 : ℂ)) (X i ω)) ω := by
      intro ω
      rw [Finset.prod_insert haS, Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [Function.update_of_ne (by rintro rfl; exact haS hi)]
    have hL : (fun ω => (∏ i ∈ T, g i (X i ω)) * ∏ i ∈ insert a S,
          Set.indicator (Function.update sets a s i) (fun _ => (1 : ℂ)) (X i ω))
        = fun ω => Set.indicator s (fun _ => (1 : ℂ)) (X a ω) *
          ((∏ i ∈ T, g i (X i ω)) *
          ∏ i ∈ S, Set.indicator (sets i) (fun _ => (1 : ℂ)) (X i ω)) := by
      funext ω; rw [hupdL ω]; ring
    have hR : (fun ω => (∏ i ∈ T, condExp 𝒟 P (fun ω => g i (X i ω)) ω) *
          ∏ i ∈ insert a S, condExp 𝒟 P (fun ω =>
            Set.indicator (Function.update sets a s i) (fun _ => (1 : ℂ)) (X i ω)) ω)
        = fun ω => condExp 𝒟 P (fun ω => Set.indicator s (fun _ => (1 : ℂ)) (X a ω)) ω *
          ((∏ i ∈ T, condExp 𝒟 P (fun ω => g i (X i ω)) ω) *
          ∏ i ∈ S, condExp 𝒟 P
            (fun ω => Set.indicator (sets i) (fun _ => (1 : ℂ)) (X i ω)) ω) := by
      funext ω; rw [hupdR ω]; ring
    rw [hL, hR] at hIH
    exact hIH

/-! ## The factorization -/

/-- If `X` is conditionally independent given `𝒟` and each `g i` is bounded, measurable and
complex valued, then

`P[∏ i ∈ S, g i (X i ·) | 𝒟] =ᵐ[P] fun ω => ∏ i ∈ S, P[g i (X i ·) | 𝒟] ω`. -/
theorem condExp_prod_eq_prod_condExp [StandardBorelSpace Ω] {ι : Type*} {β : ι → Type*}
    [mβ : ∀ i, MeasurableSpace (β i)] (h𝒟 : 𝒟 ≤ mΩ)
    (P : @Measure Ω mΩ) [IsProbabilityMeasure P] {X : ∀ i, Ω → β i} (hX : ∀ i, Measurable (X i))
    (hCI : iCondIndepFun 𝒟 h𝒟 X P) {g : ∀ i, β i → ℂ} (hg : ∀ i, Measurable (g i))
    (hgb : ∀ i, ∃ C, ∀ x, ‖g i x‖ ≤ C) (S : Finset ι) :
    condExp 𝒟 P (fun ω => ∏ i ∈ S, g i (X i ω))
      =ᵐ[P] fun ω => ∏ i ∈ S, condExp 𝒟 P (fun ω => g i (X i ω)) ω := by
  have h := condExp_prod_mul_prod_indicator 𝒟 h𝒟 P hX hCI hg hgb S ∅ (by simp)
    (fun _ => Set.univ) fun _ => MeasurableSet.univ
  simpa using h

/-- The factorization for bounded real `g i`, obtained from the complex statement by
coercion. -/
theorem condExp_prod_eq_prod_condExp_real [StandardBorelSpace Ω] {ι : Type*} {β : ι → Type*}
    [mβ : ∀ i, MeasurableSpace (β i)] (h𝒟 : 𝒟 ≤ mΩ)
    (P : @Measure Ω mΩ) [IsProbabilityMeasure P] {X : ∀ i, Ω → β i} (hX : ∀ i, Measurable (X i))
    (hCI : iCondIndepFun 𝒟 h𝒟 X P) {g : ∀ i, β i → ℝ} (hg : ∀ i, Measurable (g i))
    (hgb : ∀ i, ∃ C, ∀ x, ‖g i x‖ ≤ C) (S : Finset ι) :
    condExp 𝒟 P (fun ω => ∏ i ∈ S, g i (X i ω))
      =ᵐ[P] fun ω => ∏ i ∈ S, condExp 𝒟 P (fun ω => g i (X i ω)) ω := by
  classical
  have hgX : ∀ i, Measurable fun ω => g i (X i ω) := fun i => (hg i).comp (hX i)
  have hgXint : ∀ i, Integrable (fun ω => g i (X i ω)) P := by
    intro i
    obtain ⟨C, hC⟩ := hgb i
    exact integrable_of_ae_bound (hgX i).aestronglyMeasurable
      (Eventually.of_forall fun ω => hC _)
  have hprodint : Integrable (fun ω => ∏ i ∈ S, g i (X i ω)) P := by
    obtain ⟨C, hC⟩ := exists_ae_bound_prod (K := ℝ) P (u := fun i ω => g i (X i ω)) S
      fun i _ => (hgb i).imp fun _ h => Eventually.of_forall fun ω => h _
    exact integrable_of_ae_bound
      (Finset.measurable_prod S fun i _ => hgX i).aestronglyMeasurable hC
  -- the complex statement, for the coerced family
  have hC := condExp_prod_eq_prod_condExp 𝒟 h𝒟 P hX hCI
    (g := fun i x => ((g i x : ℝ) : ℂ)) (fun i => Complex.measurable_ofReal.comp (hg i))
    (fun i => (hgb i).imp fun C h x => by simpa using h x) S
  -- both sides of the complex statement, rewritten as coercions of the real ones
  have hL : condExp 𝒟 P (fun ω => ∏ i ∈ S, ((g i (X i ω) : ℝ) : ℂ))
      =ᵐ[P] fun ω => ((condExp 𝒟 P (fun ω => ∏ i ∈ S, g i (X i ω)) ω : ℝ) : ℂ) := by
    have hfun : (fun ω => ∏ i ∈ S, ((g i (X i ω) : ℝ) : ℂ))
        = fun ω => ((∏ i ∈ S, g i (X i ω) : ℝ) : ℂ) := by
      funext ω; exact (ofReal_prod S fun i => g i (X i ω)).symm
    rw [hfun]
    exact condExp_ofReal 𝒟 P hprodint
  have hR : ∀ i ∈ S, condExp 𝒟 P (fun ω => ((g i (X i ω) : ℝ) : ℂ))
      =ᵐ[P] fun ω => ((condExp 𝒟 P (fun ω => g i (X i ω)) ω : ℝ) : ℂ) :=
    fun i _ => condExp_ofReal 𝒟 P (hgXint i)
  have hall : ∀ᵐ ω ∂P, ∀ i ∈ S, condExp 𝒟 P (fun ω => ((g i (X i ω) : ℝ) : ℂ)) ω
      = ((condExp 𝒟 P (fun ω => g i (X i ω)) ω : ℝ) : ℂ) := (eventually_all_finset S).2 hR
  filter_upwards [hC, hL, hall] with ω h1 h2 h3
  have h4 : ((condExp 𝒟 P (fun ω => ∏ i ∈ S, g i (X i ω)) ω : ℝ) : ℂ)
      = ((∏ i ∈ S, condExp 𝒟 P (fun ω => g i (X i ω)) ω : ℝ) : ℂ) := by
    rw [← h2, h1, ofReal_prod]
    exact Finset.prod_congr rfl fun i hi => h3 i hi
  exact_mod_cast h4

/-! ## The conditional characteristic function of a conditionally independent sum -/

/-- The conditional characteristic function of a conditionally independent sum is the product of
the conditional characteristic functions,
`E[exp(i t ∑_{i ∈ S} X i) ∣ 𝒟] = ∏_{i ∈ S} E[exp(i t X i) ∣ 𝒟]`. -/
theorem condCharFun_sum_eq_prod_condCharFun [StandardBorelSpace Ω] {ι : Type*}
    (h𝒟 : 𝒟 ≤ mΩ) (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    {X : ι → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hCI : iCondIndepFun 𝒟 h𝒟 X P) (S : Finset ι) (t : ℝ) :
    condExp 𝒟 P (fun ω => Complex.exp (((t * ∑ i ∈ S, X i ω : ℝ) : ℂ) * Complex.I))
      =ᵐ[P] fun ω => ∏ i ∈ S,
        condExp 𝒟 P (fun ω => Complex.exp (((t * X i ω : ℝ) : ℂ) * Complex.I)) ω := by
  have hexp : (fun ω => Complex.exp (((t * ∑ i ∈ S, X i ω : ℝ) : ℂ) * Complex.I))
      = fun ω => ∏ i ∈ S, Complex.exp (((t * X i ω : ℝ) : ℂ) * Complex.I) := by
    funext ω
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [hexp]
  exact condExp_prod_eq_prod_condExp 𝒟 h𝒟 P hX hCI
    (g := fun _ x => Complex.exp (((t * x : ℝ) : ℂ) * Complex.I))
    (fun i => by fun_prop)
    (fun i => ⟨1, fun x => le_of_eq (Complex.norm_exp_ofReal_mul_I _)⟩) S

/-! ## Examples

Two models satisfying all hypotheses of `condCharFun_sum_eq_prod_condCharFun`, to which the
theorem is applied. -/

/-- Every family is conditionally independent given the ambient σ-algebra. -/
theorem iCondIndepFun_self [StandardBorelSpace Ω] {ι : Type*} {β : ι → Type*}
    [mβ : ∀ i, MeasurableSpace (β i)] (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    {X : ∀ i, Ω → β i} (hX : ∀ i, Measurable (X i)) :
    iCondIndepFun mΩ le_rfl X P := by
  classical
  have hid : ∀ A : Set Ω, MeasurableSet A →
      condExp mΩ P (Set.indicator A fun _ => (1 : ℝ)) = Set.indicator A fun _ => (1 : ℝ) := by
    intro A hA
    have hbd : ∀ ω, ‖Set.indicator A (fun _ => (1 : ℝ)) ω‖ ≤ 1 := by
      intro ω; by_cases h : ω ∈ A <;> simp [h]
    exact condExp_of_stronglyMeasurable le_rfl
      (measurable_const.indicator hA).stronglyMeasurable
      (integrable_of_ae_bound (measurable_const.indicator hA).aestronglyMeasurable
        (Eventually.of_forall hbd))
  refine (iCondIndepFun_iff_condExp_inter_preimage_eq_mul mβ X hX).2 ?_
  intro S sets hsets
  refine Eventually.of_forall fun ω => ?_
  rw [hid _ (S.measurableSet_biInter fun i hi => (hX i) (hsets i hi)), Finset.prod_apply]
  have hpt : ∀ i ∈ S, condExp mΩ P
      (Set.indicator (X i ⁻¹' sets i) fun _ => (1 : ℝ)) ω
      = Set.indicator (X i ⁻¹' sets i) (fun _ => (1 : ℝ)) ω := by
    intro i hi
    rw [hid _ ((hX i) (hsets i hi))]
  have hpow : ((fun _ : Ω => (1 : ℝ)) ^ S.card) = fun _ : Ω => (1 : ℝ) := by
    funext x; simp
  rw [Finset.prod_congr rfl hpt, prod_indicator_const_apply, hpow]

/-- Under a point mass, every family is conditionally independent given the trivial
σ-algebra. -/
theorem iCondIndepFun_bot_dirac [StandardBorelSpace Ω] [MeasurableSingletonClass Ω] {ι : Type*}
    {β : ι → Type*} [mβ : ∀ i, MeasurableSpace (β i)] (ω₀ : Ω) {X : ∀ i, Ω → β i}
    (hX : ∀ i, Measurable (X i)) :
    iCondIndepFun ⊥ bot_le X (@Measure.dirac Ω mΩ ω₀) := by
  classical
  refine (iCondIndepFun_iff_condExp_inter_preimage_eq_mul mβ X hX).2 ?_
  intro S sets _
  refine Eventually.of_forall fun ω => ?_
  have hpow : ((fun _ : Ω => (1 : ℝ)) ^ S.card) = fun _ : Ω => (1 : ℝ) := by
    funext x; simp
  simp only [condExp_bot, Finset.prod_apply, integral_dirac]
  rw [prod_indicator_const_apply, hpow]

/-- Under a standard Gaussian on `ℝ` with `X i ω = ω / (i + 1)` and `𝒟` the ambient σ-algebra,
every hypothesis of `condCharFun_sum_eq_prod_condCharFun` holds, and the theorem applies. -/
theorem condCharFun_sum_eq_prod_condCharFun_witness (S : Finset ℕ) (t : ℝ) :
    condExp (inferInstance : MeasurableSpace ℝ) (gaussianReal 0 1)
        (fun ω => Complex.exp (((t * ∑ i ∈ S, ω / (i + 1) : ℝ) : ℂ) * Complex.I))
      =ᵐ[gaussianReal 0 1] fun ω => ∏ i ∈ S,
        condExp (inferInstance : MeasurableSpace ℝ) (gaussianReal 0 1)
          (fun ω => Complex.exp (((t * (ω / (i + 1)) : ℝ) : ℂ) * Complex.I)) ω :=
  condCharFun_sum_eq_prod_condCharFun _ le_rfl (gaussianReal 0 1)
    (X := fun (i : ℕ) (ω : ℝ) => ω / (i + 1)) (fun i => by fun_prop)
    (iCondIndepFun_self (gaussianReal 0 1) fun i => by fun_prop) S t

/-- The same with `𝒟 = ⊥` under a point mass, so that `𝒟` is a proper sub-σ-algebra. -/
theorem condCharFun_sum_eq_prod_condCharFun_witness_bot (ω₀ : ℝ) (S : Finset ℕ) (t : ℝ) :
    condExp ⊥ (Measure.dirac ω₀)
        (fun ω : ℝ => Complex.exp (((t * ∑ i ∈ S, ω / (i + 1) : ℝ) : ℂ) * Complex.I))
      =ᵐ[Measure.dirac ω₀] fun ω => ∏ i ∈ S,
        condExp ⊥ (Measure.dirac ω₀)
          (fun ω : ℝ => Complex.exp (((t * (ω / (i + 1)) : ℝ) : ℂ) * Complex.I)) ω :=
  condCharFun_sum_eq_prod_condCharFun ⊥ bot_le (Measure.dirac ω₀)
    (X := fun (i : ℕ) (ω : ℝ) => ω / (i + 1)) (fun i => by fun_prop)
    (iCondIndepFun_bot_dirac ω₀ fun i => by fun_prop) S t

end CondFactor

end Multiway
