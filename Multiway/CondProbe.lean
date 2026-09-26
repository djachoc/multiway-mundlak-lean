import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Removing the conditioning in a conditional central limit theorem

This file isolates the last step of the proof of Theorem 4(a) of the paper, the passage from
almost-sure convergence of a conditional characteristic function `φ_n(t) = E[exp(i t'Y_n) ∣ 𝒟]`
to unconditional convergence in distribution. The argument uses the subsequence principle,
dominated convergence (`|φ_n(t)| ≤ 1`), the tower property and Lévy's continuity theorem.
The conditional limit is supplied as the hypothesis `hstep4`, and the limit `ψ` of the
conditional characteristic functions may be random.

## Main results

* `condCharFun`, `integral_condCharFun`: the conditional characteristic function and its mean.
* `step5_of_forall_subseq`, `step5_tendsto_charFun`: convergence of the unconditional
  characteristic functions, from almost-sure or in-probability convergence of the design.
* `step5_tendstoInDistribution`: the unconditional convergence in distribution.
* `probe_condGaussian`, `probe_condGaussian_witness`: a conditionally Gaussian example with a
  random variance converging in probability, and a model satisfying all its hypotheses.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace ENNReal NNReal

namespace Multiway

namespace CondProbe

-- `mΩ` is implicit and measures are written `@Measure Ω mΩ`, so that instance synthesis does
-- not pick up the sub-σ-algebra `𝒟` as the ambient measurable space.
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

/-! ## The conditional characteristic function -/

/-- The conditional characteristic function `φ(t) = E[exp(i⟪Y, t⟫) ∣ 𝒟]`, a conditional
expectation of a bounded `ℂ`-valued random variable. -/
noncomputable def condCharFun (𝒟 : MeasurableSpace Ω) (P : @Measure Ω mΩ) (Y : Ω → E) (t : E) :
    Ω → ℂ :=
  condExp 𝒟 P fun ω => Complex.exp (⟪Y ω, t⟫ * Complex.I)

omit [MeasurableSpace E] in
/-- `φ_n(t)` is `𝒟`-measurable, hence measurable, being a conditional expectation. -/
theorem stronglyMeasurable_condCharFun (𝒟 : MeasurableSpace Ω) (h𝒟 : 𝒟 ≤ mΩ)
    (P : @Measure Ω mΩ) (Y : Ω → E) (t : E) :
    StronglyMeasurable[mΩ] (condCharFun 𝒟 P Y t) :=
  (stronglyMeasurable_condExp (m := 𝒟)).mono h𝒟

omit [MeasurableSpace E] in
/-- `|φ_n(t)| ≤ 1`, by the conditional Jensen inequality. -/
theorem norm_condCharFun_le_one (𝒟 : MeasurableSpace Ω) (h𝒟 : 𝒟 ≤ mΩ) (P : @Measure Ω mΩ)
    [IsFiniteMeasure P] (Y : Ω → E) (t : E) :
    ∀ᵐ ω ∂P, ‖condCharFun 𝒟 P Y t ω‖ ≤ 1 := by
  have h1 := norm_condExp_le (m := 𝒟) (μ := P)
    (fun ω => Complex.exp ((⟪Y ω, t⟫ : ℝ) * Complex.I))
  have h2 : (fun ω : Ω => ‖Complex.exp ((⟪Y ω, t⟫ : ℝ) * Complex.I)‖) = fun _ : Ω => (1 : ℝ) := by
    funext ω
    exact Complex.norm_exp_ofReal_mul_I _
  rw [h2, condExp_const h𝒟] at h1
  exact h1

/-- `E[φ_n(t)] = E[exp(i⟪Y_n, t⟫)]`, by the tower property. -/
theorem integral_condCharFun (𝒟 : MeasurableSpace Ω) (h𝒟 : 𝒟 ≤ mΩ) (P : @Measure Ω mΩ)
    [IsProbabilityMeasure P] [BorelSpace E] [SecondCountableTopology E]
    {Y : Ω → E} (hY : AEMeasurable Y P) (t : E) :
    ∫ ω, condCharFun 𝒟 P Y t ω ∂P = charFun (@Measure.map Ω E mΩ _ Y P) t := by
  have hcont : Continuous fun x : E => Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) := by fun_prop
  rw [charFun_apply, integral_map hY hcont.aestronglyMeasurable]
  exact integral_condExp h𝒟

/-! ## Removing the conditioning -/

/-- For each `t`: if every subsequence of `φ_n(t)` has a further subsequence converging
almost surely to `ψ`, then the unconditional characteristic functions converge to `∫ψ`. The
limit `ψ` may be random. -/
theorem step5_of_forall_subseq
    (𝒟 : MeasurableSpace Ω) (h𝒟 : 𝒟 ≤ mΩ) (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    [BorelSpace E] [SecondCountableTopology E]
    {Y : ℕ → Ω → E} (hY : ∀ n, AEMeasurable (Y n) P) {t : E} {ψ : Ω → ℂ}
    (hsub : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ ms : ℕ → ℕ,
      ∀ᵐ ω ∂P, Tendsto (fun i => condCharFun 𝒟 P (Y (ns (ms i))) t ω) atTop (𝓝 (ψ ω))) :
    Tendsto (fun n => charFun (@Measure.map Ω E mΩ _ (Y n) P) t) atTop
      (𝓝 (∫ ω, ψ ω ∂P)) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, hae⟩ := hsub ns hns
  refine ⟨ms, ?_⟩
  have hrw : (fun i => charFun (@Measure.map Ω E mΩ _ (Y (ns (ms i))) P) t)
      = fun i => ∫ ω, condCharFun 𝒟 P (Y (ns (ms i))) t ω ∂P := by
    funext i
    exact (integral_condCharFun 𝒟 h𝒟 P (hY _) t).symm
  rw [hrw]
  exact tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun i => (stronglyMeasurable_condCharFun 𝒟 h𝒟 P _ t).aestronglyMeasurable)
    (integrable_const _)
    (fun i => norm_condCharFun_le_one 𝒟 h𝒟 P _ t) hae

/-- The design `d` converges in probability, as a single sequence into a pseudo-emetric space;
`hstep4` states that along any subsequence on which `d` converges almost surely, the
conditional characteristic function converges almost surely. Then the unconditional
characteristic functions converge. -/
theorem step5_tendsto_charFun
    (𝒟 : MeasurableSpace Ω) (h𝒟 : 𝒟 ≤ mΩ) (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    [BorelSpace E] [SecondCountableTopology E]
    {F : Type*} [PseudoEMetricSpace F] {d : ℕ → Ω → F} {L : Ω → F}
    (hdes : TendstoInMeasure P d atTop L)
    {Y : ℕ → Ω → E} (hY : ∀ n, AEMeasurable (Y n) P) {t : E} {ψ : Ω → ℂ}
    (hstep4 : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      (∀ᵐ ω ∂P, Tendsto (fun i => d (ns i) ω) atTop (𝓝 (L ω))) →
      ∀ᵐ ω ∂P, Tendsto (fun i => condCharFun 𝒟 P (Y (ns i)) t ω) atTop (𝓝 (ψ ω))) :
    Tendsto (fun n => charFun (@Measure.map Ω E mΩ _ (Y n) P) t) atTop
      (𝓝 (∫ ω, ψ ω ∂P)) := by
  refine step5_of_forall_subseq 𝒟 h𝒟 P hY fun ns hns => ?_
  obtain ⟨ms, hms, hae⟩ := (hdes.comp hns).exists_seq_tendsto_ae
  exact ⟨ms, hstep4 (fun i => ns (ms i)) (hns.comp hms.tendsto_atTop) hae⟩

/-- Unconditional convergence in distribution, by Lévy's continuity theorem. -/
theorem step5_tendstoInDistribution
    [FiniteDimensional ℝ E] [BorelSpace E]
    (𝒟 : MeasurableSpace Ω) (h𝒟 : 𝒟 ≤ mΩ) (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    {F : Type*} [PseudoEMetricSpace F] {d : ℕ → Ω → F} {L : Ω → F}
    (hdes : TendstoInMeasure P d atTop L)
    {Y : ℕ → Ω → E} (hY : ∀ n, AEMeasurable (Y n) P)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : @Measure Ω' mΩ'} [IsProbabilityMeasure P']
    {Z : Ω' → E} (hZ : AEMeasurable Z P')
    (hstep4 : ∀ t : E, ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      (∀ᵐ ω ∂P, Tendsto (fun i => d (ns i) ω) atTop (𝓝 (L ω))) →
      ∀ᵐ ω ∂P, Tendsto (fun i => condCharFun 𝒟 P (Y (ns i)) t ω) atTop
        (𝓝 (charFun (P'.map Z) t))) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ) Y atTop Z (fun _ => P) P' := by
  have : ∀ n : ℕ, IsProbabilityMeasure ((fun _ : ℕ => P) n) := fun _ => by assumption
  refine TendstoInDistribution.of_tendsto_charFun (fun n => hY n) hZ fun t => ?_
  have h := step5_tendsto_charFun 𝒟 h𝒟 P hdes hY (t := t)
    (ψ := fun _ => charFun (P'.map Z) t) (hstep4 t)
  simpa using h

/-! ## A conditionally Gaussian example -/

/-- A scalar sequence `Y_n` whose conditional characteristic function given `𝒟` is that of
`N(0, s_n)`, where the `𝒟`-measurable variance `s_n` converges in probability to a constant `v`,
converges unconditionally in distribution to `N(0, v)`. -/
theorem probe_condGaussian
    (𝒟 : MeasurableSpace Ω) (h𝒟 : 𝒟 ≤ mΩ) (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    {s : ℕ → Ω → ℝ≥0} {v : ℝ≥0} (hs : TendstoInMeasure P s atTop fun _ => v)
    {Y : ℕ → Ω → ℝ} (hY : ∀ n, AEMeasurable (Y n) P)
    (hcond : ∀ (n : ℕ) (t : ℝ),
      condCharFun 𝒟 P (Y n) t =ᵐ[P] fun ω => charFun (gaussianReal 0 (s n ω)) t)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : @Measure Ω' mΩ'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : AEMeasurable Z P') (hZlaw : P'.map Z = gaussianReal 0 v) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ) Y atTop Z (fun _ => P) P' := by
  refine step5_tendstoInDistribution 𝒟 h𝒟 P hs hY hZ ?_
  intro t ns hns hae
  have hall : ∀ᵐ ω ∂P, ∀ i : ℕ,
      condCharFun 𝒟 P (Y (ns i)) t ω = charFun (gaussianReal 0 (s (ns i) ω)) t :=
    ae_all_iff.2 fun i => hcond (ns i) t
  have hc : Continuous fun u : ℝ≥0 => charFun (gaussianReal 0 u) t := by
    simp only [charFun_gaussianReal]
    fun_prop
  filter_upwards [hae, hall] with ω hω heq
  have : Tendsto (fun i => charFun (gaussianReal 0 (s (ns i) ω)) t) atTop
      (𝓝 (charFun (gaussianReal 0 v) t)) := (hc.tendsto v).comp hω
  rw [hZlaw]
  exact this.congr fun i => (heq i).symm

/-- The hypotheses of `probe_condGaussian` hold for the degenerate design `𝒟 = ⊥`, with
`Ω = ℝ` under `N(0,v)`, `Y_n = Z = id` and `s_n ≡ v`. -/
theorem probe_condGaussian_witness (v : ℝ≥0) :
    TendstoInDistribution (m := fun _ : ℕ => (inferInstance : MeasurableSpace ℝ))
      (fun _ : ℕ => (id : ℝ → ℝ)) atTop (id : ℝ → ℝ)
      (fun _ => gaussianReal 0 v) (gaussianReal 0 v) := by
  have hs : TendstoInMeasure (gaussianReal 0 v) (fun (_ : ℕ) (_ : ℝ) => v) atTop fun _ => v := by
    intro ε hε
    have hset : {_x : ℝ | ε ≤ edist v v} = (∅ : Set ℝ) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, edist_self,
        nonpos_iff_eq_zero]
      exact hε.ne'
    simp only [hset, measure_empty]
    exact tendsto_const_nhds
  refine probe_condGaussian ⊥ bot_le (gaussianReal 0 v) hs (fun _ => aemeasurable_id)
    (fun _ t => ?_) aemeasurable_id Measure.map_id
  have hbot : condCharFun ⊥ (gaussianReal 0 v) (id : ℝ → ℝ) t
      = fun _ => charFun (gaussianReal 0 v) t := by
    rw [condCharFun, condExp_bot]
    rfl
  rw [hbot]

end CondProbe

end Multiway
