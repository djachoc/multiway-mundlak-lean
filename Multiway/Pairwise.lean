import Multiway.CrossProjector

/-!
# Pairwise proportional-frequency characterization

This file formalizes Proposition 2 of the paper (pairwise proportional-frequency
characterization): for two index maps `f g : O → L`, the product of the marginal projectors
equals the grand-mean projector if and only if the pairwise counts are proportional to the
product of the marginal counts. The proof compares the two sides entry by entry using
`Multiway.entries_crossProjector_mul` (Lemma SM.B.3).

## Notation

* `proj f`, `proj g` are the marginal projectors `P_m`, `P_ℓ`;
* `margCount f i` is `T^{(m)}_i` and `pairCount f g i j` is `n^{(mℓ)}_{ij}`;
* `grandMeanProj O` is `P_0`, every entry of which equals `1/n`, with `n = Fintype.card O`.

## Main results

* `proj_mul_proj_eq_grandMeanProj_iff`: the characterization over realized categories.
* `proj_mul_proj_eq_grandMeanProj_iff_of_surjective`: the same over all labels, for
  surjective index maps.
-/

open Finset Matrix

namespace Multiway

section Pairwise

variable {O : Type*} [Fintype O] {L : Type*} [DecidableEq L]

/-- The grand-mean projector `P_0`, every entry of which equals `1/n`. -/
noncomputable def grandMeanProj (O : Type*) [Fintype O] : Matrix O O ℝ :=
  Matrix.of fun _ _ => (Fintype.card O : ℝ)⁻¹

@[simp]
lemma grandMeanProj_apply (o o' : O) :
    grandMeanProj O o o' = (Fintype.card O : ℝ)⁻¹ := rfl

/-- `P_0` is the marginal projector of a dimension with a single category. -/
lemma proj_const (c : L) : proj (fun _ : O => c) = grandMeanProj O := by
  ext o o'
  simp [margCount, Finset.card_univ]

/-- For a pair of observations `(o, o')`, the entry identity `(P_m P_ℓ)_{o,o'} = 1/n` is
equivalent to the proportionality of the counts at the categories `(i_m(o), i_ℓ(o'))`. -/
lemma entry_eq_inv_card_iff (f g : O → L) (o o' : O) :
    (proj f * proj g) o o' = (Fintype.card O : ℝ)⁻¹ ↔
      (pairCount f g (f o) (g o') : ℝ)
        = (margCount f (f o) : ℝ) * (margCount g (g o') : ℝ) / (Fintype.card O : ℝ) := by
  have hT : (margCount f (f o) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (margCount_pos f o).ne'
  have hC : (margCount g (g o') : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (margCount_pos g o').ne'
  have hN : (Fintype.card O : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_pos_iff.mpr ⟨o⟩).ne'
  rw [entries_crossProjector_mul, inv_eq_one_div, div_eq_div_iff (mul_ne_zero hT hC) hN,
    eq_div_iff hN, one_mul]

/-- **Proposition 2.** `P_m P_ℓ = P_0` if and only if `n^{(mℓ)}_{ij} = T^{(m)}_i T^{(ℓ)}_j / n`
for every pair of realized categories `(i, j)`. -/
theorem proj_mul_proj_eq_grandMeanProj_iff (f g : O → L) :
    proj f * proj g = grandMeanProj O ↔
      ∀ i ∈ Set.range f, ∀ j ∈ Set.range g,
        (pairCount f g i j : ℝ)
          = (margCount f i : ℝ) * (margCount g j : ℝ) / (Fintype.card O : ℝ) := by
  constructor
  · -- the entry at `(o, o')` is the count condition at `(i_m(o), i_ℓ(o'))`
    intro h i hi j hj
    obtain ⟨o, rfl⟩ := hi
    obtain ⟨o', rfl⟩ := hj
    exact (entry_eq_inv_card_iff f g o o').mp (by rw [h, grandMeanProj_apply])
  · -- conversely, the categories of any two observations are realized
    intro h
    ext o o'
    exact (entry_eq_inv_card_iff f g o o').mpr
      (h _ (Set.mem_range_self o) _ (Set.mem_range_self o'))

/-- **Proposition 2** for surjective index maps, with the count condition quantified over all
pairs of labels. -/
theorem proj_mul_proj_eq_grandMeanProj_iff_of_surjective {f g : O → L}
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    proj f * proj g = grandMeanProj O ↔
      ∀ i j : L, (pairCount f g i j : ℝ)
        = (margCount f i : ℝ) * (margCount g j : ℝ) / (Fintype.card O : ℝ) := by
  rw [proj_mul_proj_eq_grandMeanProj_iff]
  constructor
  · intro h i j
    exact h i (Set.mem_range.mpr (hf i)) j (Set.mem_range.mpr (hg j))
  · intro h i _ j _
    exact h i j

end Pairwise

end Multiway
