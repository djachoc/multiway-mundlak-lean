import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Sums of orthogonal projectors onto an orthogonal family

General facts about orthogonal projectors in a finite-dimensional real inner product space,
used to decompose `P_[Δ]` into projectors onto mutually orthogonal pieces (for instance
`P_0 + ∑_m R_m` in Proposition 1).

## Main results

* `starProjection_comp_eq_zero_iff`: `P_U P_V = 0` if and only if `U ⟂ V`.
* `sum_starProjection_of_isOrtho`: for a finite pairwise-orthogonal family, the sum of the
  projectors is the projector onto the supremum.
* `starProjection_add_of_isOrtho`: the two-subspace case `P_U + P_V = P_{U ⊔ V}`.
-/

namespace Multiway

open Submodule

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*}

/-! ### Orthogonality and the vanishing composite -/

/-- `P_UP_V = 0` exactly when `U` and `V` are orthogonal. Mathlib has the forward direction;
the converse turns a projector identity such as `R_mR_ℓ = 0` into an orthogonality statement. -/
theorem starProjection_comp_eq_zero_iff (U V : Submodule ℝ E) :
    (∀ x : E, U.starProjection (V.starProjection x) = 0) ↔ U ⟂ V := by
  constructor
  · intro h
    rw [Submodule.isOrtho_iff_inner_eq]
    intro u hu v hv
    have hv' : V.starProjection v = v := starProjection_eq_self_iff.mpr hv
    have : U.starProjection v = 0 := by rw [← hv']; exact h v
    have hperp : v ∈ Uᗮ := (Submodule.starProjection_apply_eq_zero_iff U).mp this
    exact (Submodule.mem_orthogonal U v).mp hperp u hu
  · intro h x
    have := Submodule.IsOrtho.starProjection_comp_starProjection h
    exact congrArg (fun T : E →L[ℝ] E => T x) this

/-! ### The sum of the projectors of an orthogonal family -/

section Family

variable [Fintype ι] {V : ι → Submodule ℝ E}

omit [FiniteDimensional ℝ E] [Fintype ι] in
/-- A pairwise-orthogonal family of submodules is an `OrthogonalFamily`, which is the shape
Mathlib's results about such families take. -/
theorem orthogonalFamily_of_isOrtho (h : ∀ i j, i ≠ j → V i ⟂ V j) :
    OrthogonalFamily ℝ (fun i => (V i : Type _)) fun i => (V i).subtypeₗᵢ := by
  intro i j hij v w
  exact (Submodule.isOrtho_iff_inner_eq.mp (h i j hij)) v v.2 w w.2

/-- For a finite pairwise-orthogonal family, the sum of the orthogonal projectors is the
orthogonal projector onto the supremum. -/
theorem sum_starProjection_of_isOrtho (h : ∀ i j, i ≠ j → V i ⟂ V j) (x : E) :
    ∑ i, (V i).starProjection x = (⨆ i, V i).starProjection x := by
  classical
  have hle : ∀ i, V i ≤ (⨆ j, V j) := fun i => le_iSup V i
  -- split `x` into its component in `⨆ V` and its component in `(⨆ V)ᗮ`
  have hsplit : (⨆ j, V j).starProjection x + (⨆ j, V j)ᗮ.starProjection x = x :=
    (⨆ j, V j).starProjection_add_starProjection_orthogonal x
  -- every projector of the family kills the second component
  have hzero : ∀ i, (V i).starProjection ((⨆ j, V j)ᗮ.starProjection x) = 0 := by
    intro i
    refine (Submodule.starProjection_apply_eq_zero_iff (V i)).mpr ?_
    exact (Submodule.orthogonal_le (hle i)) ((⨆ j, V j)ᗮ.starProjection_apply_mem x)
  -- and reproduces the first, by Mathlib's `sum_projection_of_mem_iSup`
  have hsum : ∑ i, (V i).starProjection ((⨆ j, V j).starProjection x)
      = (⨆ j, V j).starProjection x :=
    (orthogonalFamily_of_isOrtho h).sum_projection_of_mem_iSup _
      ((⨆ j, V j).starProjection_apply_mem x)
  calc ∑ i, (V i).starProjection x
      = ∑ i, (V i).starProjection
          ((⨆ j, V j).starProjection x + (⨆ j, V j)ᗮ.starProjection x) := by rw [hsplit]
    _ = ∑ i, ((V i).starProjection ((⨆ j, V j).starProjection x)
          + (V i).starProjection ((⨆ j, V j)ᗮ.starProjection x)) :=
        Finset.sum_congr rfl fun i _ => by rw [map_add]
    _ = ∑ i, (V i).starProjection ((⨆ j, V j).starProjection x) := by
        simp only [hzero, add_zero]
    _ = (⨆ j, V j).starProjection x := hsum

/-- The same, as an identity of continuous linear maps. -/
theorem sum_starProjection_of_isOrtho' (h : ∀ i j, i ≠ j → V i ⟂ V j) :
    ∑ i, ((V i).starProjection : E →L[ℝ] E) = ((⨆ i, V i).starProjection : E →L[ℝ] E) := by
  ext x
  simpa using sum_starProjection_of_isOrtho h x

end Family

/-! ### The two-subspace case -/

/-- `P_U + P_V = P_{U ⊔ V}` for orthogonal `U` and `V`. -/
theorem starProjection_add_of_isOrtho {U V : Submodule ℝ E} (h : U ⟂ V) (x : E) :
    U.starProjection x + V.starProjection x = (U ⊔ V).starProjection x := by
  classical
  refine (Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_).symm
  · exact Submodule.add_mem_sup (U.starProjection_apply_mem x) (V.starProjection_apply_mem x)
  · rw [← Submodule.inf_orthogonal]
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · have h₁ : x - U.starProjection x ∈ Uᗮ := Submodule.sub_starProjection_mem_orthogonal x
      have h₂ : V.starProjection x ∈ Uᗮ :=
        (Submodule.mem_orthogonal U _).mpr fun u hu =>
          real_inner_comm (V.starProjection x) u ▸
            (Submodule.isOrtho_iff_inner_eq.mp h) u hu _ (V.starProjection_apply_mem x)
      have : x - (U.starProjection x + V.starProjection x)
          = (x - U.starProjection x) - V.starProjection x := by abel
      rw [this]
      exact Submodule.sub_mem _ h₁ h₂
    · have h₁ : x - V.starProjection x ∈ Vᗮ := Submodule.sub_starProjection_mem_orthogonal x
      have h₂ : U.starProjection x ∈ Vᗮ :=
        (Submodule.mem_orthogonal V _).mpr fun v hv =>
          real_inner_comm (U.starProjection x) v ▸
            (Submodule.isOrtho_iff_inner_eq.mp h) _ (U.starProjection_apply_mem x) v hv
      have : x - (U.starProjection x + V.starProjection x)
          = (x - V.starProjection x) - U.starProjection x := by abel
      rw [this]
      exact Submodule.sub_mem _ h₁ h₂

end Multiway
