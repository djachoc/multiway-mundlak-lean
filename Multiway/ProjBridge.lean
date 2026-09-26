import Multiway.Proportional
import Multiway.DimensionWise
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Marginal projector matrices as orthogonal projectors

This file shows that the matrix `proj f`, defined by its entries
`(P_m)_{o,o'} = 𝟙{i_m(o) = i_m(o')} / T^{(m)}_{i_m(o)}`, acts on `EuclideanSpace ℝ O` as the
orthogonal projector onto `𝒮_m = col(Δ_m)`. As an application it proves the final statement of
Theorem 2: under a connected support and `rank(Q_[Δ]) ≥ K`, dimension-wise Mundlak augmentation
is uniformly fixed-effects equivalent if and only if the cell frequencies are proportional.

## Main results

* `mem_fibreSpace_iff`: `col(Δ_m)` is the space of vectors constant within every category.
* `starProjection_fibreSpace`: `proj f` is the orthogonal projector onto `col(Δ_m)`.
* `starProjection_constSpace`: `grandMeanProj O` is the orthogonal projector onto `span(ι_n)`.
* `uniformlyFEEquivalent_iff_proportional`: the two-way characterization of Theorem 2.
-/

open Finset Matrix
open scoped RealInnerProductSpace

namespace Multiway

/-! ## Matrices as operators on `EuclideanSpace ℝ O` -/

section Bridge

variable {O : Type*} [Fintype O] [DecidableEq O] {L : Type*} [DecidableEq L]

omit [Fintype O] [DecidableEq O] in
/-- A `Finset` sum of vectors of `EuclideanSpace ℝ O` is evaluated coordinatewise. -/
theorem euclideanSum_apply {ι : Type*} (s : Finset ι) (F : ι → EuclideanSpace ℝ O) (o : O) :
    (∑ i ∈ s, F i) o = ∑ i ∈ s, (F i) o :=
  map_sum (PiLp.projₗ (𝕜 := ℝ) 2 (β := fun _ : O => ℝ) o) F s

omit [DecidableEq O] in
/-- The inner product of `EuclideanSpace ℝ O` as a coordinate sum. -/
theorem inner_euclidean (x y : EuclideanSpace ℝ O) : ⟪x, y⟫ = ∑ o : O, x o * y o := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun o _ => mul_comm _ _

/-- The indicator vector of the fibre `{o : i_m(o) = a}`, that is, the column of `Δ_m` for
category `a`. -/
noncomputable def fibreIndicator (f : O → L) (a : L) : EuclideanSpace ℝ O :=
  WithLp.toLp 2 fun o => if f o = a then (1 : ℝ) else 0

omit [Fintype O] [DecidableEq O] in
@[simp] theorem fibreIndicator_apply (f : O → L) (a : L) (o : O) :
    fibreIndicator f a o = if f o = a then (1 : ℝ) else 0 := rfl

/-- `𝒮_m = col(Δ_m)` as a subspace of `EuclideanSpace ℝ O`, the span of the indicator
vectors of the fibres of the index map. -/
noncomputable def fibreSpace (f : O → L) : Submodule ℝ (EuclideanSpace ℝ O) :=
  Submodule.span ℝ (Set.range (fibreIndicator f))

/-- The matrix `proj f` as an operator on `EuclideanSpace ℝ O`. -/
noncomputable def projEuc (f : O → L) : EuclideanSpace ℝ O →ₗ[ℝ] EuclideanSpace ℝ O :=
  Matrix.toEuclideanLin (proj f)

/-- `projEuc f` acts by `Matrix.mulVec`. -/
theorem projEuc_apply (f : O → L) (x : EuclideanSpace ℝ O) :
    projEuc f x = WithLp.toLp 2 (proj f *ᵥ WithLp.ofLp x) := rfl

/-- The `o`-th coordinate of `P_m x` is the mean of `x` over the `m`-category of `o`. -/
theorem projEuc_coord (f : O → L) (x : EuclideanSpace ℝ O) (o : O) :
    projEuc f x o
      = (margCount f (f o) : ℝ)⁻¹ * ∑ o' ∈ Finset.univ.filter fun o' => f o' = f o, x o' :=
  mulVec_proj_apply f (WithLp.ofLp x) o

/-- Two matrices agreeing as operators on `EuclideanSpace ℝ O` are equal. -/
theorem eq_of_toEuclideanLin_eq {A B : Matrix O O ℝ}
    (h : ∀ x : EuclideanSpace ℝ O,
      WithLp.toLp 2 (A *ᵥ WithLp.ofLp x) = WithLp.toLp 2 (B *ᵥ WithLp.ofLp x)) :
    A = B :=
  Matrix.toEuclideanLin.injective (LinearMap.ext h)

/-! ## `fibreSpace` is the space of vectors constant within every category -/

/-- `P_m` fixes every vector that is constant within each category. -/
theorem projEuc_eq_self_of_const (f : O → L) {x : EuclideanSpace ℝ O}
    (h : ∀ o o' : O, f o = f o' → x o = x o') : projEuc f x = x := by
  ext o
  rw [projEuc_coord]
  have hs : ∑ o' ∈ Finset.univ.filter fun o' => f o' = f o, x o'
      = (margCount f (f o) : ℝ) * x o := by
    rw [Finset.sum_congr rfl (fun o' ho' => ?_), Finset.sum_const, nsmul_eq_mul,
      margCount_eq_card]
    · rw [Finset.mem_filter] at ho'
      exact h o' o ho'.2
  rw [hs, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact Nat.cast_ne_zero.mpr (margCount_pos f o).ne'

/-- `col(P_m) ⊆ col(Δ_m)`. -/
theorem projEuc_mem_fibreSpace (f : O → L) (x : EuclideanSpace ℝ O) :
    projEuc f x ∈ fibreSpace f := by
  have key : projEuc f x
      = ∑ o : O, ((margCount f (f o) : ℝ)⁻¹ * x o) • fibreIndicator f (f o) := by
    ext o''
    rw [projEuc_coord, euclideanSum_apply]
    have hstep : ∀ o ∈ Finset.univ,
        (((margCount f (f o) : ℝ)⁻¹ * x o) • fibreIndicator f (f o)) o''
          = if f o = f o'' then (margCount f (f o'') : ℝ)⁻¹ * x o else 0 := by
      intro o _
      rw [PiLp.smul_apply, fibreIndicator_apply, smul_eq_mul]
      by_cases h : f o'' = f o
      · simp [h]
      · have h' : ¬ f o = f o'' := fun hh => h hh.symm
        simp [h, h']
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter, Finset.mul_sum]
  rw [key]
  exact Submodule.sum_mem _ fun o _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨f o, rfl⟩)

/-- A vector constant within every category lies in `col(Δ_m)`, since it is fixed by `P_m`
and the range of `P_m` lies in `col(Δ_m)`. -/
theorem mem_fibreSpace_of_const (f : O → L) {x : EuclideanSpace ℝ O}
    (h : ∀ o o' : O, f o = f o' → x o = x o') : x ∈ fibreSpace f := by
  rw [← projEuc_eq_self_of_const f h]
  exact projEuc_mem_fibreSpace f x

omit [Fintype O] [DecidableEq O] in
/-- Conversely, every vector of `col(Δ_m)` is constant within every category, since the
generators are and the property is preserved by sums and scalar multiples. -/
theorem const_of_mem_fibreSpace {f : O → L} {x : EuclideanSpace ℝ O} (hx : x ∈ fibreSpace f) :
    ∀ o o' : O, f o = f o' → x o = x o' := by
  induction hx using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨a, rfl⟩ := hv
      intro o o' hff
      simp [hff]
  | zero => intro o o' _; simp
  | add u v _ _ hu hv => intro o o' hff; simp [hu o o' hff, hv o o' hff]
  | smul c v _ hv => intro o o' hff; simp [hv o o' hff]

/-- `col(Δ_m)` is the set of vectors constant within every category. -/
theorem mem_fibreSpace_iff (f : O → L) (x : EuclideanSpace ℝ O) :
    x ∈ fibreSpace f ↔ ∀ o o' : O, f o = f o' → x o = x o' :=
  ⟨const_of_mem_fibreSpace, mem_fibreSpace_of_const f⟩

/-! ## `proj f` is the orthogonal projector onto `col(Δ_m)` -/

/-- `P_m` is symmetric: `⟪P_m x, y⟫ = ⟪x, P_m y⟫`. -/
theorem inner_projEuc_left_eq_right (f : O → L) (x y : EuclideanSpace ℝ O) :
    ⟪projEuc f x, y⟫ = ⟪x, projEuc f y⟫ := by
  have hco : ∀ (z : EuclideanSpace ℝ O) (o : O),
      projEuc f z o = ∑ o' : O, proj f o o' * z o' := fun _ _ => rfl
  simp only [inner_euclidean, hco, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => ?_
  have hs : proj f o' o = proj f o o' := by
    have h := congrFun (congrFun (transpose_proj f) o) o'
    simpa [Matrix.transpose_apply] using h
  rw [hs]
  ring

/-- The matrix `proj f` is the orthogonal projector onto `𝒮_m = col(Δ_m)`. Indeed
`P_m x ∈ col(Δ_m)`, and `x - P_m x ⟂ col(Δ_m)` because `P_m` is symmetric and fixes `col(Δ_m)`. -/
theorem starProjection_fibreSpace (f : O → L) (x : EuclideanSpace ℝ O) :
    (fibreSpace f).starProjection x = projEuc f x := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (projEuc_mem_fibreSpace f x) ?_
  intro w hw
  rw [inner_sub_left, inner_projEuc_left_eq_right,
    projEuc_eq_self_of_const f (const_of_mem_fibreSpace hw), sub_self]

/-- `starProjection_fibreSpace` in `mulVec` form: `(𝒮_f).starProjection x = proj f *ᵥ x`. -/
theorem starProjection_fibreSpace_mulVec (f : O → L) (x : EuclideanSpace ℝ O) :
    (fibreSpace f).starProjection x = WithLp.toLp 2 (proj f *ᵥ WithLp.ofLp x) :=
  starProjection_fibreSpace f x

/-- `starProjection_fibreSpace` as an identity of linear maps. -/
theorem starProjection_fibreSpace_eq (f : O → L) :
    ((fibreSpace f).starProjection : EuclideanSpace ℝ O →ₗ[ℝ] EuclideanSpace ℝ O)
      = projEuc f :=
  LinearMap.ext (starProjection_fibreSpace f)

/-- A product of two marginal projectors, as a matrix product. -/
theorem starProjection_fibreSpace_comp (f g : O → L) (x : EuclideanSpace ℝ O) :
    (fibreSpace f).starProjection ((fibreSpace g).starProjection x)
      = WithLp.toLp 2 ((proj f * proj g) *ᵥ WithLp.ofLp x) := by
  rw [starProjection_fibreSpace_mulVec, starProjection_fibreSpace_mulVec,
    ← Matrix.mulVec_mulVec]

/-! ## The constant space, and `grandMeanProj` -/

/-- The constant vector `ι_n`. -/
noncomputable def constVec (O : Type*) : EuclideanSpace ℝ O :=
  WithLp.toLp 2 fun _ => (1 : ℝ)

omit [Fintype O] [DecidableEq O] in
@[simp] theorem constVec_apply (o : O) : constVec O o = (1 : ℝ) := rfl

/-- `span(ι_n)`. -/
noncomputable def constSpace (O : Type*) : Submodule ℝ (EuclideanSpace ℝ O) :=
  ℝ ∙ constVec O

omit [Fintype O] [DecidableEq O] in
/-- `span(ι_n)` is the fibre space of the one-category dimension. -/
theorem fibreSpace_unit : fibreSpace (fun _ : O => (() : Unit)) = constSpace O := by
  have hgen : fibreIndicator (fun _ : O => (() : Unit)) default = constVec O := by
    ext o
    simp
  rw [fibreSpace, Set.range_unique, hgen]
  rfl

/-- `span(ι_n) ⊆ 𝒮_m`. -/
theorem constSpace_le_fibreSpace (f : O → L) : constSpace O ≤ fibreSpace f := by
  rw [constSpace, Submodule.span_singleton_le_iff_mem]
  exact mem_fibreSpace_of_const f fun _ _ _ => rfl

/-- The matrix `grandMeanProj O`, with entries `(P_0)_{o,o'} = 1/n`, is the orthogonal
projector `P_0` onto `span(ι_n)`. -/
theorem starProjection_constSpace (x : EuclideanSpace ℝ O) :
    (constSpace O).starProjection x = WithLp.toLp 2 (grandMeanProj O *ᵥ WithLp.ofLp x) := by
  have h : constSpace O = fibreSpace (fun _ : O => (() : Unit)) := fibreSpace_unit.symm
  simp only [h]
  rw [starProjection_fibreSpace_mulVec, proj_const]

/-- The matrix identity `P_m P_ℓ = P_0` is equivalent to the corresponding identity of
orthogonal projectors. -/
theorem starProjection_comp_eq_const_iff (f g : O → L) :
    (∀ x : EuclideanSpace ℝ O,
        (fibreSpace f).starProjection ((fibreSpace g).starProjection x)
          = (constSpace O).starProjection x)
      ↔ proj f * proj g = grandMeanProj O := by
  constructor
  · intro h
    refine eq_of_toEuclideanLin_eq fun x => ?_
    rw [← starProjection_fibreSpace_comp, h, starProjection_constSpace]
  · intro h x
    rw [starProjection_fibreSpace_comp, h, starProjection_constSpace]

end Bridge

/-! ## Two-way characterization of uniform equivalence -/

section Uniform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Dimension-wise Mundlak augmentation is uniformly fixed-effects equivalent, that is, the
spanning condition `G_X = 0` holds at every identified `X`. -/
def UniformlyFEEquivalent {D : Type*} (C₀ : Submodule ℝ E) (P : D → Submodule ℝ E)
    (F : Type*) [AddCommGroup F] [Module ℝ F] : Prop :=
  ∀ X : F →ₗ[ℝ] E, Identified (⨆ ℓ, P ℓ) X →
    (LinearMap.range X).map (((⨆ ℓ, P ℓ).starProjection : E →ₗ[ℝ] E))
      ≤ dwControls C₀ P (LinearMap.range X)

end Uniform

section TwoWay

variable {O : Type*} [Fintype O] [DecidableEq O] {L : Type*} [DecidableEq L]

/-- The two-dimensional family of fibre spaces, `M = 2`. -/
noncomputable def twoFib (f g : O → L) : Fin 2 → Submodule ℝ (EuclideanSpace ℝ O) :=
  fun i => if i = 0 then fibreSpace f else fibreSpace g

omit [Fintype O] [DecidableEq O] in
@[simp] theorem twoFib_zero (f g : O → L) : twoFib f g 0 = fibreSpace f := rfl

omit [Fintype O] [DecidableEq O] in
@[simp] theorem twoFib_one (f g : O → L) : twoFib f g 1 = fibreSpace g := rfl

omit [Fintype O] [DecidableEq O] in
theorem iSup_twoFib (f g : O → L) :
    (⨆ ℓ, twoFib f g ℓ) = fibreSpace f ⊔ fibreSpace g := by
  refine le_antisymm (iSup_le fun ℓ => ?_)
    (sup_le (le_iSup (twoFib f g) 0) (le_iSup (twoFib f g) 1))
  rcases (by decide : ∀ ℓ : Fin 2, ℓ = 0 ∨ ℓ = 1) ℓ with h | h
  · rw [h, twoFib_zero]; exact le_sup_left
  · rw [h, twoFib_one]; exact le_sup_right

omit [Fintype O] [DecidableEq O] in
/-- At `M = 2`, the sum of the fibre spaces of the dimensions other than `0` is the fibre
space of `g`. -/
theorem iSup_ne_twoFib (f g : O → L) :
    (⨆ ℓ, ⨆ (_ : ℓ ≠ (0 : Fin 2)), twoFib f g ℓ) = fibreSpace g := by
  refine le_antisymm (iSup_le fun ℓ => iSup_le fun hℓ => ?_) ?_
  · rcases (by decide : ∀ ℓ : Fin 2, ℓ = 0 ∨ ℓ = 1) ℓ with h | h
    · exact absurd h hℓ
    · rw [h, twoFib_one]
  · exact le_trans (le_of_eq (twoFib_one f g).symm)
      (le_iSup₂ (f := fun ℓ (_ : ℓ ≠ (0 : Fin 2)) => twoFib f g ℓ) (1 : Fin 2) (by decide))

theorem constSpace_le_twoFib (f g : O → L) (m : Fin 2) :
    constSpace O ≤ twoFib f g m := by
  rcases (by decide : ∀ ℓ : Fin 2, ℓ = 0 ∨ ℓ = 1) m with h | h
  · rw [h, twoFib_zero]; exact constSpace_le_fibreSpace f
  · rw [h, twoFib_one]; exact constSpace_le_fibreSpace g

/-- `P_m P_ℓ = P_0` for `m ≠ ℓ`, from the two matrix identities. -/
theorem twoFib_pair (f g : O → L) (h1 : proj f * proj g = grandMeanProj O)
    (h2 : proj g * proj f = grandMeanProj O) :
    ∀ m ℓ : Fin 2, m ≠ ℓ → ∀ x : EuclideanSpace ℝ O,
      (twoFib f g m).starProjection ((twoFib f g ℓ).starProjection x)
        = (constSpace O).starProjection x := by
  intro m ℓ hmℓ
  rcases (by decide : ∀ ℓ : Fin 2, ℓ = 0 ∨ ℓ = 1) m with hm | hm <;>
    rcases (by decide : ∀ ℓ : Fin 2, ℓ = 0 ∨ ℓ = 1) ℓ with hl | hl
  · exact absurd (hm.trans hl.symm) hmℓ
  · subst hm; subst hl
    simp only [twoFib_zero, twoFib_one]
    exact (starProjection_comp_eq_const_iff f g).mpr h1
  · subst hm; subst hl
    simp only [twoFib_zero, twoFib_one]
    exact (starProjection_comp_eq_const_iff g f).mpr h2
  · exact absurd (hm.trans hl.symm) hmℓ

/-- **Theorem 2** (final statement). Under a connected support and `rank(Q_[Δ]) ≥ K`,
dimension-wise Mundlak augmentation is uniformly fixed-effects equivalent if and only if the
cell frequencies are proportional over realized categories. -/
theorem uniformlyFEEquivalent_iff_proportional (f g : O → L) (hconn : SupportConnected f g)
    (F : Type*) [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F] [Nontrivial F]
    (hrank : Module.finrank ℝ F
      ≤ Module.finrank ℝ
          ((fibreSpace f ⊔ fibreSpace g)ᗮ : Submodule ℝ (EuclideanSpace ℝ O))) :
    UniformlyFEEquivalent (constSpace O) (twoFib f g) F ↔
      ∀ i ∈ Set.range f, ∀ t ∈ Set.range g,
        (pairCount f g i t : ℝ)
          = (margCount f i : ℝ) * (margCount g t : ℝ) / (Fintype.card O : ℝ) := by
  constructor
  · -- non-commuting projectors rule out equivalence (Proposition 1(iii))
    intro huniform
    refine (commute_iff_proportional f g hconn).mp ?_
    have hcomm := commute_of_uniform_spanning (m := (0 : Fin 2)) (P := twoFib f g)
      (C₀ := constSpace O) (F := F) ⟨1, by decide⟩ (constSpace_le_twoFib f g)
      (by rw [iSup_twoFib]; exact hrank) huniform
    rw [iSup_ne_twoFib, twoFib_zero] at hcomm
    refine eq_of_toEuclideanLin_eq fun x => ?_
    have hx := DFunLike.congr_fun hcomm x
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe] at hx
    rw [← starProjection_fibreSpace_comp, ← starProjection_fibreSpace_comp]
    exact hx
  · -- proportionality gives `P_1P_2 = P_0` (Proposition 1(ii))
    intro hprop X _
    have h1 : proj f * proj g = grandMeanProj O :=
      (proj_mul_proj_eq_grandMeanProj_iff f g).mpr hprop
    have h2 : proj g * proj f = grandMeanProj O := by
      have hgm : (grandMeanProj O)ᵀ = grandMeanProj O := by ext o o'; rfl
      have h := congrArg Matrix.transpose h1
      rwa [Matrix.transpose_mul, transpose_proj, transpose_proj, hgm] at h
    exact spanning_of_pairwise (constSpace_le_twoFib f g) (twoFib_pair f g h1 h2)

end TwoWay

end Multiway

