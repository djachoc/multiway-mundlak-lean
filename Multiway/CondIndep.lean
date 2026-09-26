import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Conditional independence factorizes a conditional expectation of a product

If `X` and `Y` are conditionally independent given a sub-σ-field `𝒟`, then
`μ[X·Y | 𝒟] =ᵐ[μ] μ[X|𝒟]·μ[Y|𝒟]`, with no boundedness hypothesis. The proof goes through
`ProbabilityTheory.condIndepFun_iff_map_prod_eq_prod_map_map`, which identifies the joint
conditional law with the product of the conditional marginals. The two-variable statement is
then applied to a conditionally independent family grouped as three slots against one, which
covers the fourth-order moments of Lemma SM.C.5 and Proposition SM.D.1.

## Main results

* `condExp_mul_of_condIndepFun`: the factorization of a conditional expectation of a product.
* `condIndepFun_triple`, `condExp_mul_triple`: three slots against one, conditionally.
* `indepFun_triple`, `integral_mul_triple`: the unconditional versions.
* `integrable_of_pow_four_bound`: integrability of products of at most four factors from
  integrable fourth powers.
* `iCondIndepFun_of_indep`: independence of a family and of `𝒟` gives conditional independence.
-/

namespace Multiway
namespace CondIndep

open MeasureTheory ProbabilityTheory

/-! ## 1. Conditional independence under the regular conditional law

The side condition `[CountableOrCountablyGenerated Ω (β × β')]` of
`condIndepFun_iff_map_prod_eq_prod_map_map` holds for any standard Borel target. -/

section Swap

variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- If `X` and `Y` are conditionally independent given `𝒟`, then for `μ`-almost every `ω` they
are independent under the regular conditional law `condExpKernel μ 𝒟 ω`. -/
theorem ae_indepFun_condExpKernel [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {h𝒟 : 𝒟 ≤ mΩ} {β β' : Type*} [MeasurableSpace β] [MeasurableSpace β']
    [MeasurableSpace.CountableOrCountablyGenerated Ω (β × β')]
    {X : Ω → β} {Y : Ω → β'} (hX : Measurable X) (hY : Measurable Y)
    (hind : CondIndepFun 𝒟 h𝒟 X Y μ) :
    ∀ᵐ ω ∂μ, IndepFun X Y (condExpKernel μ 𝒟 ω) := by
  have h := (condIndepFun_iff_map_prod_eq_prod_map_map hX hY).1 hind
  filter_upwards [ae_of_ae_trim h𝒟 h] with ω hω
  rw [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable,
    ← Kernel.map_apply _ (hX.prodMk hY) ω, ← Kernel.map_apply _ hX ω,
    ← Kernel.map_apply _ hY ω, ← Kernel.prod_apply]
  exact hω

/-- Under conditional independence given `𝒟`, the conditional expectation of a product is the
product of the conditional expectations: `μ[X·Y | 𝒟] =ᵐ[μ] μ[X|𝒟]·μ[Y|𝒟]`. -/
theorem condExp_mul_of_condIndepFun [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {h𝒟 : 𝒟 ≤ mΩ} {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hind : CondIndepFun 𝒟 h𝒟 X Y μ)
    (hXi : Integrable X μ) (hYi : Integrable Y μ)
    (hXY : Integrable (fun ω => X ω * Y ω) μ) :
    μ[fun ω => X ω * Y ω | 𝒟] =ᵐ[μ] fun ω => μ[X | 𝒟] ω * μ[Y | 𝒟] ω := by
  filter_upwards [ae_indepFun_condExpKernel 𝒟 hX hY hind,
    condExp_ae_eq_integral_condExpKernel h𝒟 hXY,
    condExp_ae_eq_integral_condExpKernel h𝒟 hXi,
    condExp_ae_eq_integral_condExpKernel h𝒟 hYi] with ω h1 h2 h3 h4
  rw [h2, h3, h4]
  exact h1.integral_fun_mul_eq_mul_integral hX.aestronglyMeasurable hY.aestronglyMeasurable

/-- If `μ[X|𝒟] = 0`, the conditional expectation of `X·Y` vanishes. -/
theorem condExp_mul_eq_zero_of_condIndepFun [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {h𝒟 : 𝒟 ≤ mΩ} {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hind : CondIndepFun 𝒟 h𝒟 X Y μ)
    (hXi : Integrable X μ) (hYi : Integrable Y μ)
    (hXY : Integrable (fun ω => X ω * Y ω) μ)
    (hzero : μ[Y | 𝒟] =ᵐ[μ] 0) :
    μ[fun ω => X ω * Y ω | 𝒟] =ᵐ[μ] 0 := by
  filter_upwards [condExp_mul_of_condIndepFun 𝒟 hX hY hind hXi hYi hXY, hzero] with ω h1 h2
  rw [h1, h2]
  simp

end Swap

/-! ## 2. Grouping three slots against one

The index `l` differs from each of `i`, `j`, `k`; these three may coincide. -/

section Triple

variable {O : Type*} [DecidableEq O] {γ : Type*} [MeasurableSpace γ]
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- For a conditionally independent family `Z`, the triple `(Z_i, Z_j, Z_k)` is conditionally
independent of `Z_l` whenever `l` differs from each of `i, j, k`. -/
theorem condIndepFun_triple [StandardBorelSpace Ω] [IsFiniteMeasure μ] {h𝒟 : 𝒟 ≤ mΩ}
    {Z : O → Ω → γ} (hZ : ∀ o, Measurable (Z o)) (hindep : iCondIndepFun 𝒟 h𝒟 Z μ)
    {i j k l : O} (hi : i ≠ l) (hj : j ≠ l) (hk : k ≠ l) :
    CondIndepFun 𝒟 h𝒟 (fun ω => (Z i ω, Z j ω, Z k ω)) (Z l) μ := by
  have hdisj : Disjoint ({i, j, k} : Finset O) ({l} : Finset O) := by
    rw [Finset.disjoint_singleton_right]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hi, Ne.symm hj, Ne.symm hk⟩
  have hmi : i ∈ ({i, j, k} : Finset O) := by simp
  have hmj : j ∈ ({i, j, k} : Finset O) := by simp
  have hmk : k ∈ ({i, j, k} : Finset O) := by simp
  have hml : l ∈ ({l} : Finset O) := by simp
  have hφ : Measurable
      (fun v : ↥({i, j, k} : Finset O) → γ => (v ⟨i, hmi⟩, v ⟨j, hmj⟩, v ⟨k, hmk⟩)) := by
    fun_prop
  have hψ : Measurable (fun v : ↥({l} : Finset O) → γ => v ⟨l, hml⟩) := by fun_prop
  exact (hindep.condIndepFun_finset ({i, j, k} : Finset O) ({l} : Finset O) hdisj hZ).comp hφ hψ

/-- `μ[G(Z_i,Z_j,Z_k)·H(Z_l) | 𝒟] =ᵐ[μ] μ[G(Z_i,Z_j,Z_k) | 𝒟]·μ[H(Z_l) | 𝒟]` for a conditionally
independent family and `l ∉ {i, j, k}`. -/
theorem condExp_mul_triple [StandardBorelSpace Ω] [IsFiniteMeasure μ] {h𝒟 : 𝒟 ≤ mΩ}
    {Z : O → Ω → γ} (hZ : ∀ o, Measurable (Z o)) (hindep : iCondIndepFun 𝒟 h𝒟 Z μ)
    {i j k l : O} (hi : i ≠ l) (hj : j ≠ l) (hk : k ≠ l)
    {G : γ × γ × γ → ℝ} {H : γ → ℝ} (hG : Measurable G) (hH : Measurable H)
    (hGi : Integrable (fun ω => G (Z i ω, Z j ω, Z k ω)) μ)
    (hHi : Integrable (fun ω => H (Z l ω)) μ)
    (hGH : Integrable (fun ω => G (Z i ω, Z j ω, Z k ω) * H (Z l ω)) μ) :
    μ[fun ω => G (Z i ω, Z j ω, Z k ω) * H (Z l ω) | 𝒟]
      =ᵐ[μ] fun ω => μ[fun ω => G (Z i ω, Z j ω, Z k ω) | 𝒟] ω * μ[fun ω => H (Z l ω) | 𝒟] ω :=
  condExp_mul_of_condIndepFun 𝒟
    (hG.comp ((hZ i).prodMk ((hZ j).prodMk (hZ k))))
    (hH.comp (hZ l)) ((condIndepFun_triple 𝒟 hZ hindep hi hj hk).comp hG hH) hGi hHi hGH

/-- If the lone slot has conditional mean zero, so does the product of all four slots. -/
theorem condExp_mul_triple_eq_zero [StandardBorelSpace Ω] [IsFiniteMeasure μ] {h𝒟 : 𝒟 ≤ mΩ}
    {Z : O → Ω → γ} (hZ : ∀ o, Measurable (Z o)) (hindep : iCondIndepFun 𝒟 h𝒟 Z μ)
    {i j k l : O} (hi : i ≠ l) (hj : j ≠ l) (hk : k ≠ l)
    {G : γ × γ × γ → ℝ} {H : γ → ℝ} (hG : Measurable G) (hH : Measurable H)
    (hGi : Integrable (fun ω => G (Z i ω, Z j ω, Z k ω)) μ)
    (hHi : Integrable (fun ω => H (Z l ω)) μ)
    (hGH : Integrable (fun ω => G (Z i ω, Z j ω, Z k ω) * H (Z l ω)) μ)
    (hzero : μ[fun ω => H (Z l ω) | 𝒟] =ᵐ[μ] 0) :
    μ[fun ω => G (Z i ω, Z j ω, Z k ω) * H (Z l ω) | 𝒟] =ᵐ[μ] 0 := by
  filter_upwards [condExp_mul_triple 𝒟 hZ hindep hi hj hk hG hH hGi hHi hGH, hzero]
    with ω h1 h2
  rw [h1, h2]
  simp

end Triple

/-! ## 3. The unconditional version

The same grouping for an independent family under an ordinary measure. -/

section TripleIndep

variable {O : Type*} [DecidableEq O] {γ : Type*} [MeasurableSpace γ]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- For an independent family, the triple `(Z_i, Z_j, Z_k)` is independent of `Z_l`. -/
theorem indepFun_triple {Z : O → Ω → γ} (hZ : ∀ o, Measurable (Z o)) (hindep : iIndepFun Z μ)
    {i j k l : O} (hi : i ≠ l) (hj : j ≠ l) (hk : k ≠ l) :
    IndepFun (fun ω => (Z i ω, Z j ω, Z k ω)) (Z l) μ := by
  have hdisj : Disjoint ({i, j, k} : Finset O) ({l} : Finset O) := by
    rw [Finset.disjoint_singleton_right]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hi, Ne.symm hj, Ne.symm hk⟩
  have hmi : i ∈ ({i, j, k} : Finset O) := by simp
  have hmj : j ∈ ({i, j, k} : Finset O) := by simp
  have hmk : k ∈ ({i, j, k} : Finset O) := by simp
  have hml : l ∈ ({l} : Finset O) := by simp
  have hφ : Measurable
      (fun v : ↥({i, j, k} : Finset O) → γ => (v ⟨i, hmi⟩, v ⟨j, hmj⟩, v ⟨k, hmk⟩)) := by
    fun_prop
  have hψ : Measurable (fun v : ↥({l} : Finset O) → γ => v ⟨l, hml⟩) := by fun_prop
  exact (hindep.indepFun_finset ({i, j, k} : Finset O) ({l} : Finset O) hdisj hZ).comp hφ hψ

/-- `∫ G(Z_i,Z_j,Z_k)·H(Z_l) dμ = (∫ G(Z_i,Z_j,Z_k) dμ)(∫ H(Z_l) dμ)` for an independent family and
`l ∉ {i, j, k}`. No integrability hypothesis is required. -/
theorem integral_mul_triple {Z : O → Ω → γ} (hZ : ∀ o, Measurable (Z o)) (hindep : iIndepFun Z μ)
    {i j k l : O} (hi : i ≠ l) (hj : j ≠ l) (hk : k ≠ l)
    {G : γ × γ × γ → ℝ} {H : γ → ℝ} (hG : Measurable G) (hH : Measurable H) :
    ∫ ω, G (Z i ω, Z j ω, Z k ω) * H (Z l ω) ∂μ
      = (∫ ω, G (Z i ω, Z j ω, Z k ω) ∂μ) * ∫ ω, H (Z l ω) ∂μ :=
  (indepFun_triple hZ hindep hi hj hk).comp hG hH |>.integral_fun_mul_eq_mul_integral
    (hG.comp ((hZ i).prodMk ((hZ j).prodMk (hZ k)))).aestronglyMeasurable
    ((hH.comp (hZ l)).aestronglyMeasurable)

end TripleIndep

/-! ## 4. Integrability from fourth moments -/

section Integrability

/-- `|abcd| ≤ (a⁴+b⁴+c⁴+d⁴)/4`. -/
theorem abs_mul_four_le (a b c d : ℝ) :
    |a * b * (c * d)| ≤ (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) / 4 := by
  have hr : a * b * (c * d) = (a * b) * (c * d) := by ring
  rw [hr, abs_mul]
  have h1 : |a * b| * |c * d| ≤ (|a * b| ^ 2 + |c * d| ^ 2) / 2 := by
    nlinarith [sq_nonneg (|a * b| - |c * d|)]
  have h2 : |a * b| ^ 2 = a ^ 2 * b ^ 2 := by rw [sq_abs]; ring
  have h3 : |c * d| ^ 2 = c ^ 2 * d ^ 2 := by rw [sq_abs]; ring
  have h4 : a ^ 2 * b ^ 2 ≤ (a ^ 4 + b ^ 4) / 2 := by nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]
  have h5 : c ^ 2 * d ^ 2 ≤ (c ^ 4 + d ^ 4) / 2 := by nlinarith [sq_nonneg (c ^ 2 - d ^ 2)]
  rw [h2, h3] at h1
  linarith [h1, h4, h5]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A function pointwise equal to a product of four factors, each with an integrable fourth
power, is integrable. Fewer factors are handled by padding with the constant `1`. -/
theorem integrable_of_pow_four_bound {f a b c d : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hfe : ∀ ω, f ω = a ω * b ω * (c ω * d ω))
    (ha : Integrable (fun ω => a ω ^ 4) μ) (hb : Integrable (fun ω => b ω ^ 4) μ)
    (hc : Integrable (fun ω => c ω ^ 4) μ) (hd : Integrable (fun ω => d ω ^ 4) μ) :
    Integrable f μ := by
  refine Integrable.mono' (g := fun ω => (a ω ^ 4 + b ω ^ 4 + c ω ^ 4 + d ω ^ 4) / 4)
    (((ha.add hb).add hc).add hd |>.div_const 4) hf (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, hfe ω]
  exact abs_mul_four_le (a ω) (b ω) (c ω) (d ω)

/-- The constant `1` has an integrable fourth power on a finite measure. -/
theorem integrable_one_pow_four [IsFiniteMeasure μ] :
    Integrable (fun _ : Ω => (1 : ℝ) ^ 4) μ := integrable_const _

end Integrability

/-! ## 5. Conditionally independent families with a non-trivial `𝒟`

A family independent of a sub-σ-field `𝒟` and independent in itself is conditionally
independent given `𝒟`. -/

section Bridge

variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Independence of a family, together with independence of the family from `𝒟`, gives
conditional independence given `𝒟`. The proof reduces to
`iIndepFun_iff_measure_inter_preimage_eq_mul` via `MeasureTheory.condExp_indep_eq`. -/
theorem iCondIndepFun_of_indep [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    {h𝒟 : 𝒟 ≤ mΩ} {ι : Type*} {β : ι → Type*} [mβ : ∀ i, MeasurableSpace (β i)]
    {Z : ∀ i, Ω → β i} (hZ : ∀ i, Measurable (Z i)) (hindep : iIndepFun Z μ)
    (hD : Indep (⨆ i, MeasurableSpace.comap (Z i) (mβ i)) 𝒟 μ) :
    iCondIndepFun 𝒟 h𝒟 Z μ := by
  classical
  refine (iCondIndepFun_iff_condExp_inter_preimage_eq_mul mβ Z hZ).2 ?_
  intro S sets hsets
  have hmS : MeasurableSet[mΩ] (⋂ i ∈ S, Z i ⁻¹' sets i) :=
    MeasurableSet.biInter S.countable_toSet fun i hi => (hZ i) (hsets i hi)
  set m₁ : MeasurableSpace Ω := ⨆ i, MeasurableSpace.comap (Z i) (mβ i) with hm₁
  have hle : ∀ i, MeasurableSpace.comap (Z i) (mβ i) ≤ m₁ :=
    fun i => le_iSup (fun i => MeasurableSpace.comap (Z i) (mβ i)) i
  have hm1le : m₁ ≤ mΩ := iSup_le fun i => (hZ i).comap_le
  have hpre : ∀ i ∈ S, MeasurableSet[MeasurableSpace.comap (Z i) (mβ i)] (Z i ⁻¹' sets i) :=
    fun i hi => ⟨sets i, hsets i hi, rfl⟩
  have hmemS : MeasurableSet[m₁] (⋂ i ∈ S, Z i ⁻¹' sets i) :=
    MeasurableSet.biInter S.countable_toSet fun i hi => hle i _ (hpre i hi)
  have hbig : μ⟦⋂ i ∈ S, Z i ⁻¹' sets i | 𝒟⟧
      =ᵐ[μ] fun _ => (μ (⋂ i ∈ S, Z i ⁻¹' sets i)).toReal := by
    refine (condExp_indep_eq hm1le h𝒟 (stronglyMeasurable_const.indicator hmemS) hD).trans ?_
    refine Filter.Eventually.of_forall fun _ => ?_
    rw [integral_indicator_const _ hmS]
    simp [measureReal_def]
  have hsing : ∀ᵐ ω ∂μ, ∀ i ∈ S,
      (μ⟦Z i ⁻¹' sets i | 𝒟⟧) ω = (μ (Z i ⁻¹' sets i)).toReal := by
    refine (Filter.eventually_all_finset S).2 fun i hi => ?_
    refine (condExp_indep_eq (hZ i).comap_le h𝒟
      (stronglyMeasurable_const.indicator (hpre i hi))
      (indep_of_indep_of_le_left hD (hle i))).trans ?_
    refine Filter.Eventually.of_forall fun _ => ?_
    rw [integral_indicator_const _ (show MeasurableSet[mΩ] (Z i ⁻¹' sets i) from
      (hZ i) (hsets i hi))]
    simp [measureReal_def]
  have hmul : μ (⋂ i ∈ S, Z i ⁻¹' sets i) = ∏ i ∈ S, μ (Z i ⁻¹' sets i) :=
    (iIndepFun_iff_measure_inter_preimage_eq_mul).1 hindep S hsets
  filter_upwards [hbig, hsing] with ω h1 h2
  rw [h1, Finset.prod_apply, hmul, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl fun i hi => (h2 i hi).symm

end Bridge

end CondIndep
end Multiway
