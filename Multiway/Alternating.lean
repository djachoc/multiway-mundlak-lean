import Multiway.Compute
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Convergence of the alternating projection scheme

This file proves the convergence clause of Proposition SM.E.1(c) (computation of the joint
within transformation): the iterates `Γ_k` of the sweep `Q_M ⋯ Q_1` converge to `Q_[Δ]Γ_0`,
where `𝒮 = ∑_m 𝒮_m`. In finite dimensions the sweep is a strict contraction on `𝒮`, so the
convergence is geometric; this is the finite-dimensional case of Halperin (1962).

The subspaces `𝒮_m` are `P m`, the projectors `P_m`, `Q_m` are `(P m).starProjection` and
`(P m)ᗮ.starProjection`, and `Γ_k` is `sweepIter P l k` for a list `l` containing every `m`.

## Main results

* `norm_sweepList_lt`: a sweep strictly shrinks every nonzero vector of `𝒮`.
* `exists_contraction`: a sweep is a contraction on `𝒮` with a uniform constant `c < 1`.
* `tendsto_sweepIter`: `Γ_k → Q_[Δ]Γ_0`.
-/

namespace Multiway

namespace Alternating

open Submodule Filter Topology

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {D : Type*}

/-! ## Step 1: a sweep is non-expansive -/

/-- Each `Q_m` is norm non-increasing, hence so is `Q_M ⋯ Q_1`. -/
theorem norm_sweepList_le (P : D → Submodule ℝ E) (l : List D) (x : E) :
    ‖sweepList P l x‖ ≤ ‖x‖ := by
  induction l generalizing x with
  | nil => simp
  | cons m t ih =>
      rw [sweepList_cons]
      exact le_trans (ih _) ((P m)ᗮ.norm_starProjection_apply_le x)

/-! ## Step 2: a vector whose norm a sweep preserves is annihilated by every `P_m` -/

/-- By Pythagoras `‖x‖² = ‖P_m x‖² + ‖Q_m x‖²`, so `‖Q_m x‖ = ‖x‖` forces `P_m x = 0`. -/
theorem starProjection_eq_zero_of_norm_orthogonal (K : Submodule ℝ E) {x : E}
    (h : ‖Kᗮ.starProjection x‖ = ‖x‖) : K.starProjection x = 0 := by
  have hp : ‖x‖ ^ 2 = ‖K.starProjection x‖ ^ 2 + ‖Kᗮ.starProjection x‖ ^ 2 :=
    K.norm_sq_eq_add_norm_sq_starProjection x
  rw [h] at hp
  have h0 : ‖K.starProjection x‖ = 0 := by nlinarith [norm_nonneg (K.starProjection x)]
  exact norm_eq_zero.mp h0

/-- If a sweep preserves the norm of `x`, then every `P_m` with `m` in the list annihilates
`x`. -/
theorem starProjection_eq_zero_of_norm_sweepList_eq (P : D → Submodule ℝ E) :
    ∀ (l : List D) (x : E), ‖sweepList P l x‖ = ‖x‖ → ∀ m ∈ l, (P m).starProjection x = 0 := by
  intro l
  induction l with
  | nil => intro x _ m hm; simp at hm
  | cons a t ih =>
      intro x hx m hm
      rw [sweepList_cons] at hx
      have h1 : ‖sweepList P t ((P a)ᗮ.starProjection x)‖ ≤ ‖(P a)ᗮ.starProjection x‖ :=
        norm_sweepList_le P t _
      have h2 : ‖(P a)ᗮ.starProjection x‖ ≤ ‖x‖ := (P a)ᗮ.norm_starProjection_apply_le x
      have hqa : ‖(P a)ᗮ.starProjection x‖ = ‖x‖ := by linarith
      have hPa : (P a).starProjection x = 0 := starProjection_eq_zero_of_norm_orthogonal (P a) hqa
      have hfix : (P a)ᗮ.starProjection x = x := by
        rw [Submodule.starProjection_orthogonal_val, hPa, sub_zero]
      rw [hfix] at hx
      rcases List.mem_cons.mp hm with hma | hmt
      · rw [hma]; exact hPa
      · exact ih x hx m hmt

variable {S : Submodule ℝ E} {P : D → Submodule ℝ E}

/-- `𝒮` is invariant under a sweep: `Q_m x = x - P_m x` and `𝒮_m ⊆ 𝒮`. -/
theorem sweepList_mem (hPS : ∀ m, P m ≤ S) (l : List D) {x : E} (hx : x ∈ S) :
    sweepList P l x ∈ S := by
  induction l generalizing x with
  | nil => simpa using hx
  | cons m t ih =>
      rw [sweepList_cons]
      refine ih ?_
      rw [Submodule.starProjection_orthogonal_val]
      exact Submodule.sub_mem _ hx (hPS m ((P m).starProjection_apply_mem x))

/-- A sweep strictly shrinks every nonzero vector of `𝒮`: otherwise `x` would be orthogonal to
every `𝒮_m`, hence to `𝒮 = ∑_m 𝒮_m`, hence to itself. -/
theorem norm_sweepList_lt (hS : S = ⨆ m, P m) {l : List D} (hfull : ∀ m : D, m ∈ l) {x : E}
    (hx : x ∈ S) (hne : x ≠ 0) : ‖sweepList P l x‖ < ‖x‖ := by
  rcases (norm_sweepList_le P l x).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have hperp : ∀ m, x ∈ (P m)ᗮ := fun m =>
      (Submodule.starProjection_apply_eq_zero_iff (P m)).mp
        (starProjection_eq_zero_of_norm_sweepList_eq P l x heq m (hfull m))
    have hle : S ≤ (ℝ ∙ x)ᗮ := by
      rw [hS]
      refine iSup_le fun m => ?_
      intro y hy
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
        (Submodule.inner_left_of_mem_orthogonal hy (hperp m))
    have hxx : ⟪x, x⟫ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle hx)
    exact hne (inner_self_eq_zero.mp hxx)

/-! ## Step 3: a uniform contraction constant

Compactness of the unit ball of `𝒮`, which uses finite-dimensionality, turns the pointwise
strict inequality into a uniform bound. -/

/-- The sweep is a strict contraction on `𝒮`: `y ↦ ‖(Q_M⋯Q_1)y‖` attains its maximum `c` on the
compact set `{x ∈ 𝒮 : ‖x‖ ≤ 1}`, and `c < 1` by `norm_sweepList_lt`. Homogeneity extends the
bound to all of `𝒮`. -/
theorem exists_contraction (hS : S = ⨆ m, P m) (l : List D) (hfull : ∀ m : D, m ∈ l) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ x ∈ S, ‖sweepList P l x‖ ≤ c * ‖x‖ := by
  have hKc : IsCompact (Metric.closedBall (0 : E) 1 ∩ (S : Set E)) :=
    (isCompact_closedBall (0 : E) 1).inter_right S.closed_of_finiteDimensional
  have hKne : (Metric.closedBall (0 : E) 1 ∩ (S : Set E)).Nonempty :=
    ⟨0, by simp, S.zero_mem⟩
  have hcont : ContinuousOn (fun y : E => ‖sweepList P l y‖)
      (Metric.closedBall (0 : E) 1 ∩ (S : Set E)) :=
    (((sweepList P l).continuous_of_finiteDimensional).norm).continuousOn
  obtain ⟨y₀, hy₀mem, hy₀max⟩ := hKc.exists_isMaxOn hKne hcont
  have hy₀S : y₀ ∈ S := hy₀mem.2
  have hy₀ball : ‖y₀‖ ≤ 1 := by simpa using hy₀mem.1
  refine ⟨‖sweepList P l y₀‖, norm_nonneg _, ?_, ?_⟩
  · rcases eq_or_ne y₀ 0 with h0 | h0
    · rw [h0, map_zero, norm_zero]; norm_num
    · exact lt_of_lt_of_le (norm_sweepList_lt hS hfull hy₀S h0) hy₀ball
  · intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hunit : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖⁻¹),
          inv_mul_cancel₀ (ne_of_gt hxpos)]
      have hmemK : (‖x‖⁻¹ : ℝ) • x ∈ Metric.closedBall (0 : E) 1 ∩ (S : Set E) := by
        refine ⟨?_, S.smul_mem _ hx⟩
        simp [Metric.mem_closedBall, dist_zero_right, hunit]
      have hmax := isMaxOn_iff.mp hy₀max _ hmemK
      have hscaled : ‖x‖⁻¹ * ‖sweepList P l x‖ ≤ ‖sweepList P l y₀‖ := by
        rw [map_smul, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖⁻¹)] at hmax
        exact hmax
      have hmul := mul_le_mul_of_nonneg_left hscaled (le_of_lt hxpos)
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hxpos), one_mul] at hmul
      linarith [hmul, mul_comm ‖x‖ ‖sweepList P l y₀‖]

/-! ## Step 4: geometric convergence -/

/-- `‖Γ_k x‖ ≤ cᵏ‖x‖` for `x ∈ 𝒮`. -/
theorem norm_sweepIter_le (hPS : ∀ m, P m ≤ S) {l : List D} {c : ℝ} (hc0 : 0 ≤ c)
    (hcon : ∀ x ∈ S, ‖sweepList P l x‖ ≤ c * ‖x‖) (k : ℕ) {x : E} (hx : x ∈ S) :
    ‖sweepIter P l k x‖ ≤ c ^ k * ‖x‖ := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      rw [sweepIter_succ]
      calc ‖sweepIter P l k (sweepList P l x)‖ ≤ c ^ k * ‖sweepList P l x‖ :=
            ih (sweepList_mem hPS l hx)
        _ ≤ c ^ k * (c * ‖x‖) := mul_le_mul_of_nonneg_left (hcon x hx) (pow_nonneg hc0 k)
        _ = c ^ (k + 1) * ‖x‖ := by ring

/-- `Q_[Δ]Γ_0` is a fixed point of the sweep, since `𝒮^⊥ ⊆ 𝒮_m^⊥` for every `m`. -/
theorem sweepList_of_mem_orthogonal (hPS : ∀ m, P m ≤ S) (l : List D) {x : E} (hx : x ∈ Sᗮ) :
    sweepList P l x = x := by
  induction l with
  | nil => rfl
  | cons m t ih =>
      have hxm : (P m)ᗮ.starProjection x = x :=
        Submodule.starProjection_eq_self_iff.mpr (Submodule.orthogonal_le (hPS m) hx)
      rw [sweepList_cons, hxm]
      exact ih

/-- A vector of `𝒮^⊥` is fixed by every iterate of the sweep. -/
theorem sweepIter_of_mem_orthogonal (hPS : ∀ m, P m ≤ S) (l : List D) (k : ℕ) {x : E}
    (hx : x ∈ Sᗮ) : sweepIter P l k x = x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [sweepIter_succ, sweepList_of_mem_orthogonal hPS l hx, ih]

/-- `Γ_k` is additive in its argument, so it respects the decomposition
`Γ_0 = P_[Δ]Γ_0 + Q_[Δ]Γ_0`. -/
theorem sweepIter_add (P : D → Submodule ℝ E) (l : List D) (k : ℕ) (x y : E) :
    sweepIter P l k (x + y) = sweepIter P l k x + sweepIter P l k y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih => rw [sweepIter_succ, sweepIter_succ, sweepIter_succ, map_add, ih]

/-- **Proposition SM.E.1(c), convergence.** If `𝒮 = ∑_m 𝒮_m` and the sweep runs over every
dimension, then `Γ_k → Q_[Δ]Γ_0` columnwise, geometrically fast. -/
theorem tendsto_sweepIter (hS : S = ⨆ m, P m) {l : List D} (hfull : ∀ m : D, m ∈ l) (x : E) :
    Tendsto (fun k => sweepIter P l k x) atTop (𝓝 (Sᗮ.starProjection x)) := by
  have hPS : ∀ m, P m ≤ S := fun m => by rw [hS]; exact le_iSup P m
  obtain ⟨c, hc0, hc1, hcon⟩ := exists_contraction hS l hfull
  have hdecomp : ∀ k, sweepIter P l k x
      = sweepIter P l k (S.starProjection x) + Sᗮ.starProjection x := by
    intro k
    conv_lhs => rw [← S.starProjection_add_starProjection_orthogonal x]
    rw [sweepIter_add, sweepIter_of_mem_orthogonal hPS l k (Sᗮ.starProjection_apply_mem x)]
  have hbound : ∀ k, ‖sweepIter P l k x - Sᗮ.starProjection x‖
      ≤ c ^ k * ‖S.starProjection x‖ := by
    intro k
    rw [hdecomp k, add_sub_cancel_right]
    exact norm_sweepIter_le hPS hc0 hcon k (S.starProjection_apply_mem x)
  have hlim : Tendsto (fun k : ℕ => c ^ k * ‖S.starProjection x‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const ‖S.starProjection x‖
  exact tendsto_sub_nhds_zero_iff.mp (squeeze_zero_norm hbound hlim)

/-- The error `Γ_k - Q_[Δ]Γ_0` of the alternating scheme tends to `0`; by `sweep_iterate_sub` it
equals `P_[Δ]Γ_k`. -/
theorem tendsto_sweepIter_sub (hS : S = ⨆ m, P m) {l : List D} (hfull : ∀ m : D, m ∈ l)
    (x : E) :
    Tendsto (fun k => sweepIter P l k x - Sᗮ.starProjection x) atTop (𝓝 0) :=
  tendsto_sub_nhds_zero_iff.mpr (tendsto_sweepIter hS hfull x)

end Alternating

end Multiway
