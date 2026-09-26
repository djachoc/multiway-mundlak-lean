/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Multiway.JansonCLT
import Mathlib.Probability.Moments.Variance

/-!
# Examples for Janson's Theorem 1 and Theorem 2

This file applies the two main theorems of `Multiway/JansonCLT.lean` (Janson (1988)) to explicit
non-degenerate sequences. Both examples take `m = 4`, a skewed summand law with nonzero third
semiinvariant and a nondegenerate limit variance.

## Main results

* `Janson.Theorem1Witness`: Theorem 1 applied to `X_n = Z / (n+1) + G`, with `Z` the skewed law
  `1/4 δ_4 + 3/4 δ_0` and `G ~ N (0, 1)` independent of it.
* `Janson.Theorem2Witness`: Theorem 2 applied to `N_n = 2 n + 2` i.i.d. copies of the skewed law,
  with the dependency graph pairing `2 q` and `2 q + 1`, maximal degree `M_n = 1` and
  `sigma_n ^ 2 = 6 n + 6`.
-/

open Finset MeasureTheory ProbabilityTheory Filter Topology
open Causalean.Mathlib.Probability.SteinMethod

namespace Janson

/-! ### The bridge between `Cumulant.cumulant _ 2` and Mathlib's `variance` -/

lemma variance_eq_cumulant_two {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    variance X μ = Cumulant.cumulant X 2 μ := by
  rw [Cumulant.cumulant_two, variance_eq_sub hX]
  rfl

/-! ### Theorem 1 on a skewed law plus independent Gaussian noise -/

namespace Theorem1Witness

open Cumulant Cumulant.SkewWitness

/-- Coordinate `0` has the skewed law `1/4 δ_4 + 3/4 δ_0` and coordinate `1` has law
`N (0, 1)`. -/
noncomputable def mixFactor (i : Fin 2) : Measure ℝ :=
  if i = 0 then skewLaw else gaussianReal 0 1

instance instMixFactor (i : Fin 2) : IsProbabilityMeasure (mixFactor i) := by
  unfold mixFactor
  split <;> infer_instance

/-- The product of the two coordinate laws. -/
noncomputable def mixLaw : Measure (Fin 2 → ℝ) := Measure.pi mixFactor

instance instMixLawProb : IsProbabilityMeasure mixLaw := by
  unfold mixLaw
  infer_instance

def mcoord (i : Fin 2) (ω : Fin 2 → ℝ) : ℝ := ω i

theorem measurable_mcoord (i : Fin 2) : Measurable (mcoord i) := measurable_pi_apply i

theorem map_mcoord (i : Fin 2) : mixLaw.map (mcoord i) = mixFactor i :=
  (MeasureTheory.measurePreserving_eval mixFactor i).map_eq

theorem mcoord_cumulant (i : Fin 2) (j : ℕ) :
    cumulant (mcoord i) j mixLaw = cumulant id j (mixFactor i) := by
  rw [← map_mcoord i, cumulant_map mixLaw (measurable_mcoord i).aemeasurable id measurable_id]
  rfl

theorem mcoord_indep : IndepFun (mcoord 0) (mcoord 1) mixLaw :=
  (iIndepFun_pi (μ := mixFactor) (X := fun _ => (id : ℝ → ℝ))
    (fun _ => aemeasurable_id)).indepFun (by decide)

theorem integrable_mixFactor_pow (i : Fin 2) (r : ℕ) :
    Integrable (fun x : ℝ => x ^ r) (mixFactor i) := by
  unfold mixFactor
  split
  · exact integrable_skew (measurable_id.pow_const r)
  · exact integrable_pow_gaussianReal 0 1 r

theorem mcoord_integrable (i : Fin 2) (r : ℕ) :
    Integrable (fun ω => mcoord i ω ^ r) mixLaw := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ r) (mixLaw.map (mcoord i)) := by
    rw [map_mcoord i]
    exact (measurable_id.pow_const r).aestronglyMeasurable
  have hint : Integrable (fun x : ℝ => x ^ r) (mixLaw.map (mcoord i)) := by
    rw [map_mcoord i]
    exact integrable_mixFactor_pow i r
  exact (integrable_map_measure hmeas (measurable_mcoord i).aemeasurable).mp hint

theorem mcoord_integrable_abs (i : Fin 2) (r : ℕ) :
    Integrable (fun ω => |mcoord i ω| ^ r) mixLaw := by
  simpa [abs_pow] using (mcoord_integrable i r).abs

theorem mcoord_zero_bdd : ∀ᵐ ω ∂mixLaw, |mcoord 0 ω| ≤ 4 := by
  have h := SkewWitness.skew_bounded
  have hm : mixFactor 0 = skewLaw := by simp [mixFactor]
  rw [← hm, ← map_mcoord 0, ae_map_iff (measurable_mcoord 0).aemeasurable
    (measurableSet_le measurable_id.abs measurable_const)] at h
  exact h

/-- The sequence `X_n = Z / (n+1) + G`. -/
noncomputable def wX (n : ℕ) : (Fin 2 → ℝ) → ℝ :=
  fun ω => (1 / ((n : ℝ) + 1)) * mcoord 0 ω + mcoord 1 ω

theorem measurable_wX (n : ℕ) : Measurable (wX n) :=
  ((measurable_mcoord 0).const_mul _).add (measurable_mcoord 1)

theorem wX_bdd (n : ℕ) : ∀ᵐ ω ∂mixLaw, |wX n ω| ≤ 4 + |mcoord 1 ω| := by
  filter_upwards [mcoord_zero_bdd] with ω hω
  have hc : |1 / ((n : ℝ) + 1)| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  calc |wX n ω| ≤ |(1 / ((n : ℝ) + 1)) * mcoord 0 ω| + |mcoord 1 ω| :=
        abs_add_le _ _
    _ ≤ 4 + |mcoord 1 ω| := by
        have hq : |(1 / ((n : ℝ) + 1)) * mcoord 0 ω| ≤ 4 := by
          rw [abs_mul]
          calc |1 / ((n : ℝ) + 1)| * |mcoord 0 ω| ≤ 1 * 4 :=
                mul_le_mul hc hω (abs_nonneg _) zero_le_one
            _ = 4 := one_mul 4
        linarith

theorem integrable_pow_wX (n : ℕ) (p : ℕ) : Integrable (fun ω => wX n ω ^ p) mixLaw := by
  have hdom : Integrable (fun ω => (4 + |mcoord 1 ω|) ^ p) mixLaw := by
    have he : ∀ ω, (4 + |mcoord 1 ω|) ^ p
        = ∑ k ∈ Finset.range (p + 1),
            (4 : ℝ) ^ k * |mcoord 1 ω| ^ (p - k) * (p.choose k : ℝ) :=
      fun ω => add_pow 4 _ p
    simp only [he]
    refine integrable_finset_sum _ fun k _ => ?_
    exact ((mcoord_integrable_abs 1 (p - k)).const_mul ((4 : ℝ) ^ k)).mul_const _
  refine Integrable.mono' hdom ((measurable_wX n).pow_const p).aestronglyMeasurable ?_
  filter_upwards [wX_bdd n] with ω hω
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) hω p

/-- The law of `Z / (n+1) + G`, bundled. -/
noncomputable def wPM (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨mixLaw.map (wX n), by
    constructor
    rw [Measure.map_apply (measurable_wX n) MeasurableSet.univ, Set.preimage_univ,
      measure_univ]⟩

lemma wPM_toMeasure (n : ℕ) : (wPM n : Measure ℝ) = mixLaw.map (wX n) := rfl

theorem wPM_integrable (n p : ℕ) : Integrable (fun x : ℝ => x ^ p) (wPM n : Measure ℝ) := by
  rw [wPM_toMeasure,
    integrable_map_measure (measurable_id'.pow_const p).aestronglyMeasurable
      (measurable_wX n).aemeasurable]
  simpa only [Function.comp_def] using integrable_pow_wX n p

/-- By `(2.2)` and `(2.3)`, the semiinvariants of the sequence are
`kappa_j (X_n) = (n+1)^(-j) kappa_j (Z) + kappa_j (G)`. -/
theorem wPM_cumulant (n : ℕ) {j : ℕ} (hj : 0 < j) :
    cumulant id j (wPM n : Measure ℝ)
      = (1 / ((n : ℝ) + 1)) ^ j * cumulant id j skewLaw + cumulant id j (gaussianReal 0 1) := by
  have h0 : mixFactor 0 = skewLaw := by simp [mixFactor]
  have h1 : mixFactor 1 = gaussianReal 0 1 := by simp [mixFactor]
  rw [wPM_toMeasure, cumulant_map mixLaw (measurable_wX n).aemeasurable id measurable_id]
  have hfun : (fun ω => id (wX n ω))
      = fun ω => (1 / ((n : ℝ) + 1)) * mcoord 0 ω + mcoord 1 ω := rfl
  rw [hfun]
  have hindep : IndepFun (fun ω => (1 / ((n : ℝ) + 1)) * mcoord 0 ω) (mcoord 1) mixLaw :=
    mcoord_indep.comp (measurable_id.const_mul _) (measurable_id (α := ℝ))
  have hXi : ∀ r ≤ j, Integrable (fun ω => ((1 / ((n : ℝ) + 1)) * mcoord 0 ω) ^ r) mixLaw := by
    intro r _
    have he : (fun ω => ((1 / ((n : ℝ) + 1)) * mcoord 0 ω) ^ r)
        = fun ω => (1 / ((n : ℝ) + 1)) ^ r * (mcoord 0 ω ^ r) := by
      funext ω
      rw [mul_pow]
    rw [he]
    exact (mcoord_integrable 0 r).const_mul _
  have hYi : ∀ r ≤ j, Integrable (fun ω => mcoord 1 ω ^ r) mixLaw :=
    fun r _ => mcoord_integrable 1 r
  rw [cumulant_add_of_indepFun ((measurable_mcoord 0).const_mul _) (measurable_mcoord 1)
      hindep hj hXi hYi,
    cumulant_const_smul (mcoord 0) _ j mixLaw, mcoord_cumulant, mcoord_cumulant, h0, h1]

/-- `kappa_3 (X_n) = 6 / (n+1)^3`, which is nonzero at every `n`. -/
theorem wPM_cumulant_three (n : ℕ) :
    cumulant id 3 (wPM n : Measure ℝ) = 6 / ((n : ℝ) + 1) ^ 3 := by
  rw [wPM_cumulant n (by norm_num), skew_cumulant_three,
    cumulant_gaussianReal 0 1 3 (by norm_num)]
  simp only [gaussCumulants]
  norm_num
  ring

theorem wPM_cumulant_three_ne_zero (n : ℕ) : cumulant id 3 (wPM n : Measure ℝ) ≠ 0 := by
  rw [wPM_cumulant_three]
  positivity

theorem tendsto_inv_pow (j : ℕ) (hj : 0 < j) (C : ℝ) :
    Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ j * C) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 := (h1.pow j).mul_const C
  rw [zero_pow (by omega : j ≠ 0), zero_mul] at h2
  exact h2

theorem wPM_h1 : Tendsto (fun n => cumulant id 1 (wPM n : Measure ℝ)) atTop (𝓝 0) := by
  have he : ∀ n : ℕ, cumulant id 1 (wPM n : Measure ℝ) = (1 / ((n : ℝ) + 1)) ^ 1 * 1 := by
    intro n
    rw [wPM_cumulant n (by norm_num), skew_cumulant_one, cumulant_gaussianReal 0 1 1 le_rfl]
    simp [gaussCumulants]
  simp only [he]
  exact tendsto_inv_pow 1 (by norm_num) 1

theorem wPM_h2 : Tendsto (fun n => cumulant id 2 (wPM n : Measure ℝ)) atTop (𝓝 1) := by
  have he : ∀ n : ℕ, cumulant id 2 (wPM n : Measure ℝ) = (1 / ((n : ℝ) + 1)) ^ 2 * 3 + 1 := by
    intro n
    rw [wPM_cumulant n (by norm_num), skew_cumulant_two, cumulant_gaussianReal 0 1 2 (by norm_num)]
    simp [gaussCumulants]
  simp only [he]
  have h := (tendsto_inv_pow 2 (by norm_num) 3).add (tendsto_const_nhds (x := (1 : ℝ)))
  rw [zero_add] at h
  exact h

theorem wPM_h3 : ∀ j, 4 ≤ j → Tendsto (fun n => cumulant id j (wPM n : Measure ℝ)) atTop (𝓝 0) := by
  intro j hj
  have he : ∀ n : ℕ, cumulant id j (wPM n : Measure ℝ)
      = (1 / ((n : ℝ) + 1)) ^ j * cumulant id j skewLaw := by
    intro n
    rw [wPM_cumulant n (by omega), cumulant_gaussianReal 0 1 j (by omega)]
    simp only [gaussCumulants]
    rw [if_neg (by omega : ¬ j = 1), if_neg (by omega : ¬ j = 2), add_zero]
  simp only [he]
  exact tendsto_inv_pow j (by omega) _

/-- Janson's Theorem 1 applied at `m = 4` to a sequence whose third semiinvariant is nonzero at
every `n`, with limit variance `sigma ^ 2 = 1`. -/
theorem theorem1_witness : Tendsto wPM atTop (𝓝 (gaussPM 0 1)) :=
  tendsto_gaussPM wPM_integrable (m := 4) wPM_h1 wPM_h2 wPM_h3

/-- For the same sequence, the third moment of `X_n` converges to that of `N (0, 1)`. -/
theorem theorem1_moment_witness :
    Tendsto (fun n => ∫ x, x ^ 3 ∂(wPM n : Measure ℝ)) atTop
      (𝓝 (∫ x, x ^ 3 ∂(gaussPM 0 1 : Measure ℝ))) :=
  tendsto_integral_pow_gaussPM wPM_integrable (m := 4) wPM_h1 wPM_h2 wPM_h3 3

end Theorem1Witness

/-! ### Theorem 2 on a paired i.i.d. array -/

namespace Theorem2Witness

open Cumulant Cumulant.SkewWitness

/-- `2 n + 2` i.i.d. copies of the skewed law. -/
noncomputable def arrLaw (n : ℕ) : Measure (Fin (2 * n + 2) → ℝ) :=
  Measure.pi fun _ => skewLaw

instance instArrLawProb (n : ℕ) : IsProbabilityMeasure (arrLaw n) := by
  unfold arrLaw
  infer_instance

def acoord (n : ℕ) (i : Fin (2 * n + 2)) (ω : Fin (2 * n + 2) → ℝ) : ℝ := ω i

theorem measurable_acoord (n : ℕ) (i : Fin (2 * n + 2)) : Measurable (acoord n i) :=
  measurable_pi_apply i

theorem map_acoord (n : ℕ) (i : Fin (2 * n + 2)) : (arrLaw n).map (acoord n i) = skewLaw :=
  (MeasureTheory.measurePreserving_eval (fun _ : Fin (2 * n + 2) => skewLaw) i).map_eq

theorem acoord_iIndep (n : ℕ) : iIndepFun (acoord n) (arrLaw n) :=
  iIndepFun_pi (μ := fun _ : Fin (2 * n + 2) => skewLaw) (X := fun _ => (id : ℝ → ℝ))
    (fun _ => aemeasurable_id)

theorem acoord_cumulant (n : ℕ) (i : Fin (2 * n + 2)) (j : ℕ) :
    cumulant (acoord n i) j (arrLaw n) = cumulant id j skewLaw := by
  rw [← map_acoord n i,
    cumulant_map (arrLaw n) (measurable_acoord n i).aemeasurable id measurable_id]
  rfl

theorem acoord_integrable (n : ℕ) (i : Fin (2 * n + 2)) (r : ℕ) :
    Integrable (fun ω => acoord n i ω ^ r) (arrLaw n) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ r) ((arrLaw n).map (acoord n i)) := by
    rw [map_acoord n i]
    exact (measurable_id.pow_const r).aestronglyMeasurable
  have hint : Integrable (fun x : ℝ => x ^ r) ((arrLaw n).map (acoord n i)) := by
    rw [map_acoord n i]
    exact integrable_skew (measurable_id.pow_const r)
  exact (integrable_map_measure hmeas (measurable_acoord n i).aemeasurable).mp hint

theorem acoord_bdd (n : ℕ) (i : Fin (2 * n + 2)) :
    ∀ᵐ ω ∂(arrLaw n), |acoord n i ω| ≤ 4 := by
  have h := SkewWitness.skew_bounded
  rw [← map_acoord n i, ae_map_iff (measurable_acoord n i).aemeasurable
    (measurableSet_le measurable_id.abs measurable_const)] at h
  exact h

/-- The dependency relation: `i` and `k` are adjacent if and only if they belong to the same pair
`{2 q, 2 q + 1}`. Adding edges preserves the separation property, so this is a dependency graph,
with maximal degree `M_n = 1`. -/
def aG (n : ℕ) (i k : Fin (2 * n + 2)) : Prop := (i : ℕ) / 2 = (k : ℕ) / 2

instance instDecidableAG (n : ℕ) : DecidableRel (aG n) :=
  fun i k => inferInstanceAs (Decidable ((i : ℕ) / 2 = (k : ℕ) / 2))

/-- The dependency graph. -/
noncomputable def aDep (n : ℕ) : DepGraph (acoord n) (arrLaw n) where
  G := aG n
  decG := inferInstance
  refl := fun _ => rfl
  symm := fun _ _ h => h.symm
  meas := measurable_acoord n
  indep := by
    intro A B hsep
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro a ha hb
      exact hsep a ha a hb rfl
    exact (acoord_iIndep n).indepFun_finset A B hdisj (measurable_acoord n)

theorem aDep_G_eq (n : ℕ) : (aDep n).G = aG n := rfl

/-- The graph has an edge. -/
theorem aDep_edge (n : ℕ) :
    (aDep n).G ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  rw [aDep_G_eq]
  show (0 : ℕ) / 2 = (1 : ℕ) / 2
  norm_num

/-- The graph has a non-edge. -/
theorem aDep_nonedge (n : ℕ) (hn : 1 ≤ n) :
    ¬ (aDep n).G ⟨0, by omega⟩ ⟨2, by omega⟩ := by
  rw [aDep_G_eq]
  show ¬ ((0 : ℕ) / 2 = (2 : ℕ) / 2)
  norm_num

/-- Janson's maximal degree is `M_n = 1`. -/
theorem aDep_degree (n : ℕ) (i : Fin (2 * n + 2)) :
    #(((aDep n).nbhd i).erase i) ≤ 1 := by
  classical
  have hsub : (aDep n).nbhd i ⊆
      ({⟨2 * ((i : ℕ) / 2), by have := i.isLt; omega⟩,
        ⟨2 * ((i : ℕ) / 2) + 1, by have := i.isLt; omega⟩} : Finset (Fin (2 * n + 2))) := by
    intro k hk
    rw [DepGraph.mem_nbhd_iff, aDep_G_eq] at hk
    have hk' : (i : ℕ) / 2 = (k : ℕ) / 2 := hk
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    omega
  have hcard : #((aDep n).nbhd i) ≤ 2 :=
    le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_insert_le _ _) (by simp))
  rw [Finset.card_erase_of_mem ((aDep n).self_mem_nbhd i)]
  omega

/-- The maximal degree `M_n = 1` is attained: vertex `1` is a neighbour of vertex `0`. -/
theorem aDep_degree_pos (n : ℕ) :
    1 ≤ #(((aDep n).nbhd ⟨0, by omega⟩).erase ⟨0, by omega⟩) := by
  classical
  refine Finset.card_pos.mpr ⟨⟨1, by omega⟩, ?_⟩
  rw [Finset.mem_erase, DepGraph.mem_nbhd_iff, aDep_G_eq]
  refine ⟨fun h => ?_, ?_⟩
  · have := congrArg Fin.val h
    simp at this
  · show (0 : ℕ) / 2 = (1 : ℕ) / 2
    norm_num

theorem aDep_degree_attained (n : ℕ) :
    #(((aDep n).nbhd ⟨0, by omega⟩).erase ⟨0, by omega⟩) = 1 :=
  le_antisymm (aDep_degree n _) (aDep_degree_pos n)

/-! #### The variance -/

theorem memLp_acoord (n : ℕ) (i : Fin (2 * n + 2)) : MemLp (acoord n i) 2 (arrLaw n) :=
  (memLp_two_iff_integrable_sq (measurable_acoord n i).aestronglyMeasurable).2
    (acoord_integrable n i 2)

theorem memLp_aSum (n : ℕ) : MemLp (fun ω => ∑ i, acoord n i ω) 2 (arrLaw n) := by
  have he : (fun ω => ∑ i, acoord n i ω) = ∑ i, acoord n i := by
    funext ω
    rw [Finset.sum_apply]
  rw [he]
  exact memLp_finsetSum' _ (fun i _ => memLp_acoord n i)

/-- `sigma_n ^ 2 = var (S_n) = 3 (2 n + 2) = 6 n + 6`. -/
theorem aSum_cumulant_two (n : ℕ) :
    cumulant (fun ω => ∑ i, acoord n i ω) 2 (arrLaw n) = 6 * (n : ℝ) + 6 := by
  have he : (fun ω => ∑ i, acoord n i ω) = ∑ i, acoord n i := by
    funext ω
    rw [Finset.sum_apply]
  rw [← variance_eq_cumulant_two (memLp_aSum n), he]
  rw [IndepFun.variance_sum (fun i _ => memLp_acoord n i)
    (fun i _ k _ hik => (acoord_iIndep n).indepFun hik)]
  have hterm : ∀ i : Fin (2 * n + 2), variance (acoord n i) (arrLaw n) = 3 := by
    intro i
    rw [variance_eq_cumulant_two (memLp_acoord n i), acoord_cumulant, skew_cumulant_two]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- The standard deviation. -/
noncomputable def aSigma (n : ℕ) : ℝ := Real.sqrt (6 * (n : ℝ) + 6)

theorem aSigma_pos (n : ℕ) : 0 < aSigma n := by
  rw [aSigma]
  apply Real.sqrt_pos.mpr
  positivity

theorem aSigma_sq (n : ℕ) : aSigma n ^ 2 = 6 * (n : ℝ) + 6 := by
  rw [aSigma, Real.sq_sqrt (by positivity)]

/-! #### The rate condition -/

theorem aRate (j : ℕ) (hj : 4 ≤ j) :
    Tendsto (fun n : ℕ => (Fintype.card (Fin (2 * n + 2)) : ℝ)
      * (((1 : ℕ) : ℝ) + 1) ^ (j - 1) * ((4 : ℝ) / aSigma n) ^ j) atTop (𝓝 0) := by
  have hub : Tendsto (fun n : ℕ => (2 : ℝ) ^ (j - 1) * 15 * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using h.const_mul ((2 : ℝ) ^ (j - 1) * 15)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub ?_ ?_
  · filter_upwards with n
    have h0 : (0 : ℝ) ≤ (4 : ℝ) / aSigma n :=
      le_of_lt (div_pos (by norm_num) (aSigma_pos n))
    have h1 : (0 : ℝ) ≤ ((4 : ℝ) / aSigma n) ^ j := pow_nonneg h0 j
    have h2 : (0 : ℝ) ≤ (Fintype.card (Fin (2 * n + 2)) : ℝ) := Nat.cast_nonneg _
    have h3 : (0 : ℝ) ≤ (((1 : ℕ) : ℝ) + 1) ^ (j - 1) := by positivity
    exact mul_nonneg (mul_nonneg h2 h3) h1
  · filter_upwards [eventually_ge_atTop 3] with n hn
    have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hs2 : aSigma n ^ 2 = 6 * (n : ℝ) + 6 := aSigma_sq n
    have hspos : 0 < aSigma n := aSigma_pos n
    set u : ℝ := (4 : ℝ) / aSigma n with hu
    have hu0 : 0 ≤ u := by positivity
    have husq : u ^ 2 = 16 / (6 * (n : ℝ) + 6) := by
      rw [hu, div_pow, hs2]
      norm_num
    have hs4 : (4 : ℝ) ≤ aSigma n := by
      by_contra hcon
      push_neg at hcon
      have hlt : aSigma n ^ 2 < 16 := by nlinarith [hspos]
      rw [hs2] at hlt
      linarith
    have hu1 : u ≤ 1 := by
      rw [hu, div_le_one hspos]
      linarith
    have hpow : u ^ j ≤ u ^ 4 := pow_le_pow_of_le_one hu0 hu1 hj
    have hu4 : u ^ 4 = 256 / (6 * (n : ℝ) + 6) ^ 2 := by
      have : u ^ 4 = (u ^ 2) ^ 2 := by ring
      rw [this, husq, div_pow]
      norm_num
    have hcard : (Fintype.card (Fin (2 * n + 2)) : ℝ) = 2 * (n : ℝ) + 2 := by
      rw [Fintype.card_fin]
      push_cast
      ring
    rw [hcard]
    have hbase : (((1 : ℕ) : ℝ) + 1) = 2 := by norm_num
    rw [hbase]
    have hnp : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hkey : (2 * (n : ℝ) + 2) * u ^ 4 ≤ 15 * (1 / ((n : ℝ) + 1)) := by
      rw [hu4]
      have he : (2 * (n : ℝ) + 2) * (256 / (6 * (n : ℝ) + 6) ^ 2)
          = 128 / (9 * ((n : ℝ) + 1)) := by
        field_simp
        ring
      have he2 : 15 * (1 / ((n : ℝ) + 1)) = 15 / ((n : ℝ) + 1) := by ring
      rw [he, he2, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hnp]
    calc (2 * (n : ℝ) + 2) * 2 ^ (j - 1) * u ^ j
        = 2 ^ (j - 1) * ((2 * (n : ℝ) + 2) * u ^ j) := by ring
      _ ≤ 2 ^ (j - 1) * ((2 * (n : ℝ) + 2) * u ^ 4) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ 2 ^ (j - 1) * (15 * (1 / ((n : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = 2 ^ (j - 1) * 15 * (1 / ((n : ℝ) + 1)) := by ring

/-- Janson's Theorem 2 applied at `m = 4` to `N_n = 2 n + 2` summands with a dependency graph that
is neither empty nor complete, `M_n = 1`, `A_n = 4` and `sigma_n ^ 2 = 6 n + 6`. -/
theorem theorem2_witness :
    Tendsto (fun n => stdSumPM (aDep n) (aSigma n)
      (-(∫ ω, ∑ i, acoord n i ω ∂(arrLaw n)) / aSigma n)) atTop (𝓝 (gaussPM 0 1)) :=
  tendsto_gaussPM_of_depGraph aDep (M := fun _ => 1) aDep_degree (A := fun _ => 4)
    (fun _ => by norm_num) acoord_bdd (σ := aSigma) aSigma_pos
    (fun n => by rw [aSigma_sq, aSum_cumulant_two]) (m := 4) (by norm_num) aRate

end Theorem2Witness

/-! ### The rate arithmetic of `(1.5)` -/

namespace RateWitness

/-- `Janson.tendsto_rate_of_janson15` applied at `m = 4` and `j = 5`, with `N_n = 2 n + 2`,
`Md_n = 2` and `u_n = 1 / (n+1) ^ 2`, so that `N_n / Md_n = n + 1` grows. -/
theorem rate_witness :
    Tendsto (fun n : ℕ => (2 * (n : ℝ) + 2) * (2 : ℝ) ^ (5 - 1)
      * ((1 : ℝ) / ((n : ℝ) + 1) ^ 2) ^ 5) atTop (𝓝 0) := by
  refine tendsto_rate_of_janson15 (N := fun n => 2 * (n : ℝ) + 2) (Md := fun _ => 2)
    (u := fun n => 1 / ((n : ℝ) + 1) ^ 2) (m := 4) (by norm_num)
    (fun _ => by norm_num)
    (fun n => by have h := Nat.cast_nonneg (α := ℝ) n; linarith)
    (fun n => by positivity) ?_ (by norm_num)
  have hlim : Tendsto (fun n : ℕ => (2 : ℝ) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 : ℝ)
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hlim
  · have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) ≤ ((2 * (n : ℝ) + 2) / 2) ^ ((4 : ℕ) : ℝ)⁻¹ := by
      refine Real.rpow_nonneg ?_ _
      have h := Nat.cast_nonneg (α := ℝ) n
      linarith
    have h3 : (0 : ℝ) ≤ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by positivity
    exact mul_nonneg h2 h3
  · have hb : ((2 * (n : ℝ) + 2) / 2) = (n : ℝ) + 1 := by ring
    rw [hb]
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have h := Nat.cast_nonneg (α := ℝ) n
      linarith
    have hrp : ((n : ℝ) + 1) ^ (((4 : ℕ) : ℝ))⁻¹ ≤ (n : ℝ) + 1 := by
      have h := Real.rpow_le_rpow_of_exponent_le h1
        (show (((4 : ℕ) : ℝ))⁻¹ ≤ (1 : ℝ) by norm_num)
      simpa using h
    calc ((n : ℝ) + 1) ^ (((4 : ℕ) : ℝ))⁻¹ * (2 * (1 / ((n : ℝ) + 1) ^ 2))
        ≤ ((n : ℝ) + 1) * (2 * (1 / ((n : ℝ) + 1) ^ 2)) :=
          mul_le_mul_of_nonneg_right hrp (by positivity)
      _ = 2 * (1 / ((n : ℝ) + 1)) := by
          have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
          field_simp

end RateWitness

end Janson
