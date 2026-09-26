import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# The incremental projector

This file formalizes Lemma SM.B.1 of the paper (incremental projector). For a finite-dimensional
real inner product space `E` and submodules `T, U` with `T ⊔ U = S`, the difference
`A_m = P_[Δ] - P_{-m}` is the orthogonal projector onto `Q_{-m} 𝒮_m`, it has the same range as
`B_m = Q_{-m} P_m`, and both annihilate `Q_[Δ]`.

## Notation

* `S`, `T`, `U` are the spans `𝒮`, `𝒮_{-m}`, `𝒮_m`; `P_[Δ]`, `P_{-m}`, `P_m` are their
  `starProjection`s, and `Q_[Δ]`, `Q_{-m}` are those of `Sᗮ`, `Tᗮ`.
* `incrementalProjector S T` is `A_m` and `incrementalMundlak T U` is `B_m`.
* `U.map Tᗮ.starProjection` is `col(Q_{-m} Δ_m)`.

## Main results

* `incrementalProjector_eq_starProjection`: `A_m` is the projector onto `col(Q_{-m} Δ_m)`.
* `range_incrementalMundlak_eq`, `finrank_range_incrementalMundlak`: equal ranges and ranks.
* `incremental_projector`: Lemma SM.B.1, all four clauses.
-/

namespace Multiway

open Submodule LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- `A_m := P_[Δ] - P_{-m}`, the difference of the orthogonal projectors onto `S` and onto
`T`. -/
noncomputable def incrementalProjector (S T : Submodule ℝ E) : E →ₗ[ℝ] E :=
  (S.starProjection : E →ₗ[ℝ] E) - (T.starProjection : E →ₗ[ℝ] E)

/-- `B_m := Q_{-m} P_m`, the projector onto `U` followed by the projector onto `Tᗮ`. -/
noncomputable def incrementalMundlak (T U : Submodule ℝ E) : E →ₗ[ℝ] E :=
  ((Tᗮ).starProjection : E →ₗ[ℝ] E).comp ((U.starProjection : E →ₗ[ℝ] E))

@[simp]
theorem incrementalProjector_apply (S T : Submodule ℝ E) (x : E) :
    incrementalProjector S T x = S.starProjection x - T.starProjection x := rfl

@[simp]
theorem incrementalMundlak_apply (T U : Submodule ℝ E) (x : E) :
    incrementalMundlak T U x = (Tᗮ).starProjection (U.starProjection x) := rfl

section Symmetric

variable {S T : Submodule ℝ E}

/-- If `T ≤ S`, then `A_m` is a symmetric idempotent. -/
theorem incrementalProjector_isSymmetricProjection (hTS : T ≤ S) :
    (incrementalProjector S T).IsSymmetricProjection := by
  have hrange : LinearMap.range (T.starProjection : E →ₗ[ℝ] E)
      ≤ LinearMap.range (S.starProjection : E →ₗ[ℝ] E) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨T.starProjection x,
      starProjection_eq_self_iff.mpr (hTS (T.starProjection_apply_mem x))⟩
  exact LinearMap.IsSymmetricProjection.sub_of_range_le_range
    (isSymmetricProjection_starProjection T) (isSymmetricProjection_starProjection S) hrange

/-- The range of `A_m` is `S ⊓ Tᗮ`. -/
theorem range_incrementalProjector (hTS : T ≤ S) :
    LinearMap.range (incrementalProjector S T) = S ⊓ Tᗮ := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · exact Submodule.sub_mem _ (S.starProjection_apply_mem x)
        (hTS (T.starProjection_apply_mem x))
    · refine (Submodule.starProjection_apply_eq_zero_iff T).mp ?_
      have h₁ : T.starProjection (S.starProjection x) = T.starProjection x :=
        DFunLike.congr_fun (starProjection_comp_starProjection_of_le hTS) x
      simp only [incrementalProjector_apply, map_sub, h₁]
      rw [starProjection_eq_self_iff.mpr (T.starProjection_apply_mem x), sub_self]
  · intro y hy
    obtain ⟨hyS, hyT⟩ := Submodule.mem_inf.mp hy
    refine ⟨y, ?_⟩
    rw [incrementalProjector_apply, starProjection_eq_self_iff.mpr hyS,
      (Submodule.starProjection_apply_eq_zero_iff T).mpr hyT, sub_zero]

/-- `A_m` is the orthogonal projector onto `S ⊓ Tᗮ`. -/
theorem incrementalProjector_eq_starProjection_inf (hTS : T ≤ S) :
    incrementalProjector S T = ((S ⊓ Tᗮ).starProjection : E →ₗ[ℝ] E) :=
  LinearMap.IsSymmetricProjection.ext (incrementalProjector_isSymmetricProjection hTS)
    (isSymmetricProjection_starProjection _)
    (by rw [range_incrementalProjector hTS, range_starProjection])

end Symmetric

section Range

variable {S T U : Submodule ℝ E}

/-- `S ⊓ Tᗮ = Q_{-m} S = Q_{-m} U` when `T ⊔ U = S`. -/
theorem inf_orthogonal_eq_map_starProjection_orthogonal (hS : T ⊔ U = S) :
    S ⊓ Tᗮ = U.map ((Tᗮ).starProjection : E →ₗ[ℝ] E) := by
  have hTS : T ≤ S := hS ▸ le_sup_left
  have hUS : U ≤ S := hS ▸ le_sup_right
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨hyS, hyT⟩ := Submodule.mem_inf.mp hy
    obtain ⟨t, ht, u, hu, rfl⟩ := Submodule.mem_sup.mp (hS ▸ hyS : y ∈ T ⊔ U)
    refine ⟨u, hu, ?_⟩
    have hself : (Tᗮ).starProjection (t + u) = t + u :=
      starProjection_eq_self_iff.mpr hyT
    have ht0 : (Tᗮ).starProjection t = 0 := starProjection_orthogonal_apply_eq_zero ht
    have : (Tᗮ).starProjection u = t + u := by rw [← hself, map_add, ht0, zero_add]
    simpa only [ContinuousLinearMap.coe_coe] using this
  · rintro _ ⟨u, hu, rfl⟩
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · show (Tᗮ).starProjection u ∈ S
      rw [starProjection_orthogonal_val]
      exact Submodule.sub_mem _ (hUS hu) (hTS (T.starProjection_apply_mem u))
    · show (Tᗮ).starProjection u ∈ Tᗮ
      exact (Tᗮ).starProjection_apply_mem u

/-- `A_m` is the orthogonal projector onto `col(Q_{-m} Δ_m)`. -/
theorem incrementalProjector_eq_starProjection (hS : T ⊔ U = S) :
    incrementalProjector S T
      = ((U.map ((Tᗮ).starProjection : E →ₗ[ℝ] E)).starProjection : E →ₗ[ℝ] E) :=
  have hTS : T ≤ S := hS ▸ le_sup_left
  LinearMap.IsSymmetricProjection.ext (incrementalProjector_isSymmetricProjection hTS)
    (isSymmetricProjection_starProjection _)
    (by rw [range_incrementalProjector hTS, range_starProjection,
      inf_orthogonal_eq_map_starProjection_orthogonal hS])

/-- `col(B_m) = Q_{-m} 𝒮_m`. -/
theorem range_incrementalMundlak (T U : Submodule ℝ E) :
    LinearMap.range (incrementalMundlak T U) = U.map ((Tᗮ).starProjection : E →ₗ[ℝ] E) := by
  rw [incrementalMundlak, LinearMap.range_comp, range_starProjection]

/-- `col(B_m) = col(A_m)`. -/
theorem range_incrementalMundlak_eq (hS : T ⊔ U = S) :
    LinearMap.range (incrementalMundlak T U) = LinearMap.range (incrementalProjector S T) := by
  have hTS : T ≤ S := hS ▸ le_sup_left
  rw [range_incrementalMundlak, range_incrementalProjector hTS,
    inf_orthogonal_eq_map_starProjection_orthogonal hS]

/-- `rank(A_m) = rank(B_m)`. -/
theorem finrank_range_incrementalMundlak (hS : T ⊔ U = S) :
    Module.finrank ℝ (LinearMap.range (incrementalProjector S T))
      = Module.finrank ℝ (LinearMap.range (incrementalMundlak T U)) := by
  rw [range_incrementalMundlak_eq hS]

end Range

section Annihilate

variable {S T U : Submodule ℝ E}

/-- `A_m Q_[Δ] = 0`. -/
theorem incrementalProjector_comp_orthogonal (hTS : T ≤ S) :
    (incrementalProjector S T).comp ((Sᗮ).starProjection : E →ₗ[ℝ] E) = 0 := by
  ext x
  have hmem : (Sᗮ).starProjection x ∈ Sᗮ := (Sᗮ).starProjection_apply_mem x
  have hS0 : S.starProjection ((Sᗮ).starProjection x) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff S).mpr hmem
  have hT0 : T.starProjection ((Sᗮ).starProjection x) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff T).mpr (Submodule.orthogonal_le hTS hmem)
  rw [LinearMap.comp_apply, LinearMap.zero_apply, ContinuousLinearMap.coe_coe,
    incrementalProjector_apply, hS0, hT0, sub_zero]

/-- `B_m Q_[Δ] = 0`. -/
theorem incrementalMundlak_comp_orthogonal (hUS : U ≤ S) :
    (incrementalMundlak T U).comp ((Sᗮ).starProjection : E →ₗ[ℝ] E) = 0 := by
  ext x
  have hU0 : U.starProjection ((Sᗮ).starProjection x) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff U).mpr
      (Submodule.orthogonal_le hUS ((Sᗮ).starProjection_apply_mem x))
  rw [LinearMap.comp_apply, LinearMap.zero_apply, ContinuousLinearMap.coe_coe,
    incrementalMundlak_apply, hU0, map_zero]

end Annihilate

/-- **Lemma SM.B.1.** Let `T ⊔ U = S` (hypothesis `hS`). Then

1. `A_m` is the orthogonal projector onto `col(Q_{-m}Δ_m) = U.map Q_{-m}`;
2. `col(B_m) = col(A_m)`;
3. `rank(A_m) = rank(B_m)`;
4. `A_m Q_[Δ] = 0` and `B_m Q_[Δ] = 0`. -/
theorem incremental_projector {S T U : Submodule ℝ E} (hS : T ⊔ U = S) :
    incrementalProjector S T
        = ((U.map ((Tᗮ).starProjection : E →ₗ[ℝ] E)).starProjection : E →ₗ[ℝ] E)
      ∧ LinearMap.range (incrementalMundlak T U) = LinearMap.range (incrementalProjector S T)
      ∧ Module.finrank ℝ (LinearMap.range (incrementalProjector S T))
          = Module.finrank ℝ (LinearMap.range (incrementalMundlak T U))
      ∧ (incrementalProjector S T).comp ((Sᗮ).starProjection : E →ₗ[ℝ] E) = 0
      ∧ (incrementalMundlak T U).comp ((Sᗮ).starProjection : E →ₗ[ℝ] E) = 0 :=
  ⟨incrementalProjector_eq_starProjection hS, range_incrementalMundlak_eq hS,
    finrank_range_incrementalMundlak hS,
    incrementalProjector_comp_orthogonal (hS ▸ le_sup_left),
    incrementalMundlak_comp_orthogonal (hS ▸ le_sup_right)⟩

end Multiway
