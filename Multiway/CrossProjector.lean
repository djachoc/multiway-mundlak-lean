import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Card

/-!
# Entries of the cross-projector product

This file formalizes Lemma SM.B.3 of the paper (entries of the cross-projector product):
`(P_m P_ℓ)_{o,o'} = n^{(mℓ)}_{i_m(o), i_ℓ(o')} / (T^{(m)}_{i_m(o)} T^{(ℓ)}_{i_ℓ(o')})`.
The identity holds for arbitrary index maps, including `m = ℓ`.

## Notation

* `O` is the finite set of observations and `L` the type of category labels.
* `f g : O → L` are the index maps `i_m`, `i_ℓ`.
* `margCount f i` is the marginal count `T^{(m)}_i`.
* `pairCount f g i j` is the pairwise cell count `n^{(mℓ)}_{ij}`.
* `proj f` is the marginal projector `P_m`, given by its entries
  `(P_m)_{o,o'} = 𝟙{i_m(o) = i_m(o')} / T^{(m)}_{i_m(o)}`.
-/

open Finset Matrix

namespace Multiway

section CrossProjector

variable {O : Type*} [Fintype O] {L : Type*} [DecidableEq L]

/-- `T^{(m)}_a := #{o ∈ 𝒪 : i_m(o) = a}`, the marginal count of category `a` in the
dimension whose index map is `f`. -/
def margCount (f : O → L) (a : L) : ℕ :=
  (Finset.univ.filter fun o => f o = a).card

lemma margCount_eq_card (f : O → L) (a : L) :
    margCount f a = (Finset.univ.filter fun o => f o = a).card := rfl

/-- `n^{(mℓ)}_{ab} := #{o ∈ 𝒪 : i_m(o) = a, i_ℓ(o) = b}`, the pairwise cell count of the
dimensions whose index maps are `f` and `g`. -/
def pairCount (f g : O → L) (a b : L) : ℕ :=
  (Finset.univ.filter fun o => f o = a ∧ g o = b).card

lemma pairCount_eq_card (f g : O → L) (a b : L) :
    pairCount f g a b = (Finset.univ.filter fun o => f o = a ∧ g o = b).card := rfl

/-- The marginal projector `P_m`, given by its entries
`(P_m)_{o,o'} = 𝟙{i_m(o) = i_m(o')} / T^{(m)}_{i_m(o)}`. -/
noncomputable def proj (f : O → L) : Matrix O O ℝ :=
  Matrix.of fun o o' => if f o = f o' then (margCount f (f o) : ℝ)⁻¹ else 0

@[simp]
lemma proj_apply (f : O → L) (o o' : O) :
    proj f o o' = if f o = f o' then (margCount f (f o) : ℝ)⁻¹ else 0 := rfl

/-- The category of an observation is nonempty, so every marginal count that appears in a
denominator is positive. -/
lemma margCount_pos (f : O → L) (o : O) : 0 < margCount f (f o) :=
  Finset.card_pos.mpr ⟨o, by simp⟩

/-- `(P_ℓ z)_{o} = (T^{(ℓ)}_{i_ℓ(o)})⁻¹ ∑_{o' : i_ℓ(o') = i_ℓ(o)} z_{o'}`: applying `P_ℓ`
averages `z` over the `ℓ`-category of `o`. -/
theorem mulVec_proj_apply (f : O → L) (z : O → ℝ) (o : O) :
    (proj f *ᵥ z) o
      = (margCount f (f o) : ℝ)⁻¹ * ∑ o' ∈ Finset.univ.filter fun o' => f o' = f o, z o' := by
  rw [Matrix.mulVec_apply_eq_sum, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun o' _ => ?_
  by_cases h : f o' = f o
  · simp [h]
  · have h' : f o ≠ f o' := fun hh => h hh.symm
    simp [h, h']

/-- An intermediate observation `o''` contributes to `(P_m P_ℓ)_{o,o'}` exactly when it lies
in the `m`-category of `o` and in the `ℓ`-category of `o'`, and it then contributes
`(T^{(m)}_{i_m(o)})⁻¹ (T^{(ℓ)}_{i_ℓ(o')})⁻¹`. -/
lemma proj_mul_proj_summand (f g : O → L) (o o' o'' : O) :
    proj f o o'' * proj g o'' o'
      = if f o'' = f o ∧ g o'' = g o' then
          (margCount f (f o) : ℝ)⁻¹ * (margCount g (g o') : ℝ)⁻¹ else 0 := by
  by_cases h1 : f o'' = f o
  · by_cases h2 : g o'' = g o'
    · simp [h1, h2]
    · simp [h2]
  · have h1' : f o ≠ f o'' := fun hh => h1 hh.symm
    have hn : ¬(f o'' = f o ∧ g o'' = g o') := fun h => h1 h.1
    simp [h1', hn]

/-- **Lemma SM.B.3.** For observations `o` and `o'`,
`(P_m P_ℓ)_{o,o'} = n^{(mℓ)}_{i_m(o), i_ℓ(o')} / (T^{(m)}_{i_m(o)} T^{(ℓ)}_{i_ℓ(o')})`. -/
theorem entries_crossProjector_mul (f g : O → L) (o o' : O) :
    (proj f * proj g) o o'
      = (pairCount f g (f o) (g o') : ℝ)
          / ((margCount f (f o) : ℝ) * (margCount g (g o') : ℝ)) := by
  rw [Matrix.mul_apply]
  simp only [proj_mul_proj_summand]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, pairCount_eq_card,
    div_eq_mul_inv, mul_inv]

end CrossProjector

end Multiway
