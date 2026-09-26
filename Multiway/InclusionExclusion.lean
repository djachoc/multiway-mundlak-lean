import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Inclusion–exclusion identity for the multiway meat

This file formalizes Lemma SM.B.7 of the paper (Inclusion–exclusion identity for the multiway
meat). For `v ∈ ℝⁿ`,
`∑_{∅ ≠ A ⊆ {1,…,J}} (-1)^{|A|+1} ∑_{g ∈ 𝒢_A} (∑_{o ∈ g} x̃_o v_o)(∑_{o ∈ g} x̃_o v_o)'`
equals `∑_{o,o' ∈ 𝒪} 𝟙{o ∼ o'} x̃_o x̃_{o'}' v_o v_{o'}`. It is a finite-sample combinatorial
identity.

## Notation

* `c : D → O → L` assigns each observation its cluster in each dimension; `dims` is the set of
  maintained dimensions.
* `cells c A` is the partition `𝒢_A`, with cells `cellOf c A o`.
* `SameOn c A o o'` is `o ∼_A o'`; `Linked c dims o o'` is `o ∼ o'`.
* `sharedDims c dims o o'` is `J(o,o')`.

## Main results

* `sum_cells_mul`, `weight_eq`: the two steps of the proof.
* `multiway_meat_inclusion_exclusion`: the identity in matrix form.
-/

namespace Multiway

open Finset

variable {O K D L : Type*}

section Defs

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

/-- `o ∼_A o'`: the two observations lie in the same cluster in every dimension of `A`. -/
def SameOn (c : D → O → L) (A : Finset D) (o o' : O) : Prop := ∀ j ∈ A, c j o = c j o'

instance (c : D → O → L) (A : Finset D) (o o' : O) : Decidable (SameOn c A o o') :=
  inferInstanceAs (Decidable (∀ j ∈ A, c j o = c j o'))

/-- The cell of `o` in the partition `𝒢_A`. -/
def cellOf (c : D → O → L) (A : Finset D) (o : O) : Finset O :=
  Finset.univ.filter (fun o' => SameOn c A o' o)

/-- `𝒢_A`, the partition of `𝒪` obtained by intersecting the clusters of the dimensions
in `A`. -/
def cells (c : D → O → L) (A : Finset D) : Finset (Finset O) :=
  Finset.univ.image (cellOf c A)

/-- `J(o,o')`, the set of maintained dimensions in which `o` and `o'` share a cluster. -/
def sharedDims (c : D → O → L) (dims : Finset D) (o o' : O) : Finset D :=
  dims.filter (fun j => c j o = c j o')

/-- `o ∼ o'`: the two observations share at least one maintained cluster. -/
def Linked (c : D → O → L) (dims : Finset D) (o o' : O) : Prop :=
  ∃ j ∈ dims, c j o = c j o'

instance (c : D → O → L) (dims : Finset D) (o o' : O) : Decidable (Linked c dims o o') :=
  inferInstanceAs (Decidable (∃ j ∈ dims, c j o = c j o'))

end Defs

section Basic

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
variable {c : D → O → L} {A : Finset D}

@[simp] lemma mem_cellOf {o o' : O} : o' ∈ cellOf c A o ↔ SameOn c A o' o := by
  simp [cellOf]

lemma sameOn_refl (o : O) : SameOn c A o o := fun _ _ => rfl

lemma sameOn_symm {o o' : O} (h : SameOn c A o o') : SameOn c A o' o :=
  fun j hj => (h j hj).symm

lemma sameOn_trans {o o' o'' : O} (h : SameOn c A o o') (h' : SameOn c A o' o'') :
    SameOn c A o o'' := fun j hj => (h j hj).trans (h' j hj)

/-- Two observations have the same cell if and only if they are `∼_A`-equivalent. -/
lemma cellOf_eq_iff {o o' : O} : cellOf c A o = cellOf c A o' ↔ SameOn c A o o' := by
  constructor
  · intro h
    have : o ∈ cellOf c A o' := by rw [← h]; simp [sameOn_refl]
    simpa using this
  · intro h
    ext o''
    simp only [mem_cellOf]
    exact ⟨fun h'' => sameOn_trans h'' h, fun h'' => sameOn_trans h'' (sameOn_symm h)⟩

/-- The fibre of the cell map over a cell is that cell. -/
lemma filter_cellOf_eq {g : Finset O} (hg : g ∈ cells c A) :
    Finset.univ.filter (fun o => cellOf c A o = g) = g := by
  obtain ⟨o₀, -, rfl⟩ := Finset.mem_image.1 hg
  ext o
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_cellOf, cellOf_eq_iff]

end Basic

section Grouping

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
variable {c : D → O → L} {A : Finset D}

/-- Forming the cell scores over `𝒢_A` and multiplying is the same as summing over the
`∼_A`-linked pairs. -/
lemma sum_cells_mul (f h : O → ℝ) :
    ∑ g ∈ cells c A, (∑ o ∈ g, f o) * (∑ o' ∈ g, h o')
      = ∑ o : O, ∑ o' : O, if SameOn c A o o' then f o * h o' else 0 := by
  classical
  have hmaps : ∀ o ∈ (Finset.univ : Finset O), cellOf c A o ∈ cells c A :=
    fun o _ => Finset.mem_image_of_mem _ (Finset.mem_univ o)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
        (fun o => ∑ o' : O, if SameOn c A o o' then f o * h o' else 0)]
  refine Finset.sum_congr rfl ?_
  intro g hg
  rw [filter_cellOf_eq hg, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro o ho
  rw [Finset.mul_sum, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  obtain ⟨o₀, -, rfl⟩ := Finset.mem_image.1 hg
  have ho' : SameOn c A o o₀ := by simpa using ho
  ext o'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_cellOf]
  constructor
  · intro hh; exact sameOn_trans ho' (sameOn_symm hh)
  · intro hh; exact sameOn_trans (sameOn_symm hh) ho'

end Grouping

section Weight

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
variable {c : D → O → L} {dims : Finset D}

/-- `o ∼_A o'` if and only if `A ⊆ J(o,o')`, for `A` a set of maintained dimensions. -/
lemma sameOn_iff_subset {A : Finset D} (hA : A ⊆ dims) {o o' : O} :
    SameOn c A o o' ↔ A ⊆ sharedDims c dims o o' := by
  constructor
  · intro h j hj; exact Finset.mem_filter.2 ⟨hA hj, h j hj⟩
  · intro h j hj; exact (Finset.mem_filter.1 (h hj)).2

/-- The alternating weight of a pair collapses to the linkage indicator:
`∑_{∅ ≠ A ⊆ J(o,o')} (-1)^{|A|+1} = 1 - ∑_{A ⊆ J(o,o')} (-1)^{|A|} = 𝟙{o ∼ o'}`,
using `∑_{A ⊆ E} (-1)^{|A|} = (1-1)^{|E|} = 0` for `E ≠ ∅`. -/
lemma weight_eq (o o' : O) :
    ∑ A ∈ dims.powerset.filter (fun A => A.Nonempty),
        (-1 : ℝ) ^ (A.card + 1) * (if SameOn c A o o' then (1 : ℝ) else 0)
      = if Linked c dims o o' then (1 : ℝ) else 0 := by
  classical
  set E : Finset D := sharedDims c dims o o' with hEdef
  have hEsub : E ⊆ dims := Finset.filter_subset _ _
  -- only the subsets of `E` contribute, and on them the indicator is `1`
  have hstep :
      ∑ A ∈ dims.powerset.filter (fun A => A.Nonempty),
          (-1 : ℝ) ^ (A.card + 1) * (if SameOn c A o o' then (1 : ℝ) else 0)
        = ∑ A ∈ E.powerset.filter (fun A => A.Nonempty), (-1 : ℝ) ^ (A.card + 1) := by
    rw [Finset.sum_filter, Finset.sum_filter,
        ← Finset.sum_subset (Finset.powerset_mono.2 hEsub)]
    · refine Finset.sum_congr rfl ?_
      intro A hA
      have hAE : A ⊆ E := Finset.mem_powerset.1 hA
      have hAd : A ⊆ dims := hAE.trans hEsub
      by_cases hne : A.Nonempty
      · simp [hne, (sameOn_iff_subset (c := c) (dims := dims) hAd).2 hAE]
      · simp [hne]
    · intro A hA hA'
      have hAd : A ⊆ dims := Finset.mem_powerset.1 hA
      have hnot : ¬ A ⊆ E := fun hc => hA' (Finset.mem_powerset.2 hc)
      by_cases hne : A.Nonempty
      · have hno : ¬ SameOn c A o o' :=
          fun hc => hnot ((sameOn_iff_subset (c := c) (dims := dims) hAd).1 hc)
        simp [hne, hno]
      · simp [hne]
  rw [hstep]
  -- `∑_{∅ ≠ A ⊆ E} (-1)^{|A|+1} = 1 - ∑_{A ⊆ E} (-1)^{|A|}`
  have hfil : E.powerset.filter (fun A => A.Nonempty) = E.powerset.erase ∅ := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.nonempty_iff_ne_empty]
    tauto
  have hsucc : ∀ A : Finset D, (-1 : ℝ) ^ (A.card + 1) = -((-1 : ℝ) ^ A.card) := by
    intro A; rw [pow_succ]; ring
  have hall : ∑ A ∈ E.powerset, (-1 : ℝ) ^ (A.card + 1)
      = -∑ A ∈ E.powerset, (-1 : ℝ) ^ A.card := by
    rw [Finset.sum_congr rfl (fun A _ => hsucc A)]
    simp
  have herase : ∑ A ∈ E.powerset.erase ∅, (-1 : ℝ) ^ (A.card + 1)
      = (∑ A ∈ E.powerset, (-1 : ℝ) ^ (A.card + 1)) - (-1 : ℝ) ^ ((∅ : Finset D).card + 1) := by
    rw [eq_sub_iff_add_eq]
    exact Finset.sum_erase_add _ _ (Finset.empty_mem_powerset E)
  -- Mathlib states `∑_{A ⊆ E} (-1)^{|A|}` over `ℤ`; cast it to `ℝ`.
  have hpow : ∑ A ∈ E.powerset, (-1 : ℝ) ^ A.card = if E = ∅ then (1 : ℝ) else 0 := by
    have hZ : ∑ A ∈ E.powerset, (-1 : ℤ) ^ A.card = if E = ∅ then (1 : ℤ) else 0 :=
      Finset.sum_powerset_neg_one_pow_card
    have := congrArg (fun z : ℤ => (z : ℝ)) hZ
    push_cast at this
    simpa using this
  rw [hfil, herase, hall, hpow]
  simp only [Finset.card_empty, zero_add, pow_one]
  by_cases hlink : Linked c dims o o'
  · have hEne : E ≠ ∅ := by
      obtain ⟨j, hj, hcj⟩ := hlink
      exact Finset.nonempty_iff_ne_empty.1 ⟨j, Finset.mem_filter.2 ⟨hj, hcj⟩⟩
    simp [hlink, hEne]
  · have hEe : E = ∅ := by
      by_contra hne
      obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hne
      exact hlink ⟨j, (Finset.mem_filter.1 hj).1, (Finset.mem_filter.1 hj).2⟩
    simp [hlink, hEe]

end Weight

section Main

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

/-- **Lemma SM.B.7, entrywise.** For each pair of coefficient indices `(a,b)`, the
inclusion–exclusion sum over the nonempty subsets of the maintained dimensions equals the sum of
`x̃_o x̃_{o'}' v_o v_{o'}` over the pairs of observations that share a maintained cluster. -/
theorem multiway_meat_inclusion_exclusion_entry
    (c : D → O → L) (dims : Finset D) (x : O → K → ℝ) (v : O → ℝ) (a b : K) :
    ∑ A ∈ dims.powerset.filter (fun A => A.Nonempty),
        (-1 : ℝ) ^ (A.card + 1) *
          ∑ g ∈ cells c A, (∑ o ∈ g, x o a * v o) * (∑ o' ∈ g, x o' b * v o')
      = ∑ o : O, ∑ o' : O,
          (if Linked c dims o o' then x o a * x o' b * (v o * v o') else 0) := by
  classical
  -- each `A`-term becomes a double sum over the `∼_A`-linked pairs
  have h1 : ∀ A : Finset D,
      ∑ g ∈ cells c A, (∑ o ∈ g, x o a * v o) * (∑ o' ∈ g, x o' b * v o')
        = ∑ o : O, ∑ o' : O,
            if SameOn c A o o' then (x o a * v o) * (x o' b * v o') else 0 :=
    fun A => sum_cells_mul (c := c) (A := A) (fun o => x o a * v o) (fun o' => x o' b * v o')
  simp only [h1]
  -- push the alternating sign inside both sums
  have h2 : ∀ A : Finset D,
      (-1 : ℝ) ^ (A.card + 1) *
          (∑ o : O, ∑ o' : O,
            if SameOn c A o o' then (x o a * v o) * (x o' b * v o') else 0)
        = ∑ o : O, ∑ o' : O,
            (-1 : ℝ) ^ (A.card + 1) *
              (if SameOn c A o o' then (x o a * v o) * (x o' b * v o') else 0) := by
    intro A
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun o _ => Finset.mul_sum _ _ _)
  simp only [h2]
  -- exchange the order of summation and collect each pair's weight
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro o _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro o' _
  have hfac : ∀ A : Finset D,
      (-1 : ℝ) ^ (A.card + 1) *
          (if SameOn c A o o' then (x o a * v o) * (x o' b * v o') else 0)
        = ((x o a * v o) * (x o' b * v o')) *
            ((-1 : ℝ) ^ (A.card + 1) * (if SameOn c A o o' then (1 : ℝ) else 0)) := by
    intro A
    by_cases h : SameOn c A o o' <;> simp [h] <;> ring
  rw [Finset.sum_congr rfl (fun A _ => hfac A), ← Finset.mul_sum,
      weight_eq (c := c) (dims := dims) o o']
  by_cases hl : Linked c dims o o' <;> simp [hl] <;> ring

/-- **Lemma SM.B.7.** The inclusion–exclusion identity in matrix form, with
`Matrix.vecMulVec u w` the outer product `u w'`. -/
theorem multiway_meat_inclusion_exclusion [Fintype K]
    (c : D → O → L) (dims : Finset D) (x : O → K → ℝ) (v : O → ℝ) :
    ∑ A ∈ dims.powerset.filter (fun A => A.Nonempty),
        (-1 : ℝ) ^ (A.card + 1) •
          ∑ g ∈ cells c A,
            Matrix.vecMulVec (fun k => ∑ o ∈ g, x o k * v o) (fun k => ∑ o ∈ g, x o k * v o)
      = ∑ o : O, ∑ o' : O,
          (if Linked c dims o o' then
              (v o * v o') • Matrix.vecMulVec (x o) (x o') else 0) := by
  classical
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
    Matrix.zero_apply, apply_ite (fun M : Matrix K K ℝ => M a b)]
  rw [multiway_meat_inclusion_exclusion_entry c dims x v a b]
  refine Finset.sum_congr rfl (fun o _ => Finset.sum_congr rfl (fun o' _ => ?_))
  by_cases h : Linked c dims o o' <;> simp [h] <;> ring

end Main

end Multiway
