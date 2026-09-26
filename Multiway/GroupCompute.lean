import Multiway.InclusionExclusion
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Grouped computation of the moment system

This file formalizes Proposition SM.E.2 of the paper (Grouped computation of the moment
system): the superset aggregates `T_F(·)` over pairs of observations sharing the dimensions `F`
reduce to sums over the level-`F` cells (part (a)), the exact-pattern aggregates follow by
Möbius inversion on the Boolean lattice (part (b)), and the residual-maker quantities reduce to
cell sums and Frobenius norms (part (c)). The proofs use finite combinatorics and matrix algebra.

## Notation

* `O` is the set of observations, `dims` the fixed-effect dimensions, `c : D → O → L` the
  category map; `cells c F` are the level-`F` cells `𝒯_F`.
* `sharedDims c dims o o'` is `E(o,o')`; `superAgg c F w` is `T_F(w)` and `exactAgg` sums
  over `P_F = {(o,o') : o ≠ o', E(o,o') = F}`.
* `cellCross Ξ s t` is `ι_s'Ξ ι_t`; `shMat`, `shOff` are `Sh_e`, `Sh^off_e`.
* `R` is an abstract symmetric idempotent matrix with `RΔ_m = 0`; `Multiway.ResidualBridge`
  supplies these properties for the residual maker `residualMatrix`.
-/

namespace Multiway

open Finset

variable {O D L ι : Type*}

/-! ### The aggregates of the proposition -/

section Defs

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

/-- `T_F(w) = ∑_{o ≠ o' : F ⊆ E(o,o')} w_{oo'}`, the superset aggregate at level `F`.
`T_F(v)` is the case `w o o' = v_o v_{o'}`, `T_F(Ξ)` the case `w = Ξ`, and `C_F` the case
`w = 1`. -/
def superAgg (c : D → O → L) (F : Finset D) (w : O → O → ℝ) : ℝ :=
  ∑ o : O, ∑ o' : O, if o ≠ o' ∧ SameOn c F o o' then w o o' else 0

/-- `∑_{(o,o') ∈ P_F} w_{oo'}`, the aggregate over the ordered pairs whose shared set is
exactly `F`. `|P_F|` is the case `w = 1`. -/
def exactAgg (c : D → O → L) (dims F : Finset D) (w : O → O → ℝ) : ℝ :=
  ∑ o : O, ∑ o' : O, if o ≠ o' ∧ sharedDims c dims o o' = F then w o o' else 0

end Defs

/-! ### The cells of level `F` partition `𝒪` -/

section Partition

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

/-- The cells of level `F` partition `𝒪`. -/
theorem sum_over_cells (c : D → O → L) (F : Finset D) (f : O → ℝ) :
    ∑ t ∈ cells c F, ∑ o ∈ t, f o = ∑ o : O, f o := by
  classical
  have hmaps : ∀ o ∈ (univ : Finset O), cellOf c F o ∈ cells c F :=
    fun o _ => Finset.mem_image_of_mem _ (Finset.mem_univ o)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps f]
  exact Finset.sum_congr rfl fun g hg => by rw [filter_cellOf_eq hg]

/-- `F ⊆ E(o,o')` if and only if `o` and `o'` lie in the same level-`F` cell. Hence the double sum
over a cell, summed over the cells, is the double sum over the `∼_F`-linked pairs. -/
theorem sum_cells_pair (c : D → O → L) (F : Finset D) (w : O → O → ℝ) :
    ∑ t ∈ cells c F, ∑ o ∈ t, ∑ o' ∈ t, w o o'
      = ∑ o : O, ∑ o' : O, if SameOn c F o o' then w o o' else 0 := by
  classical
  have hmaps : ∀ o ∈ (univ : Finset O), cellOf c F o ∈ cells c F :=
    fun o _ => Finset.mem_image_of_mem _ (Finset.mem_univ o)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
        (fun o => ∑ o' : O, if SameOn c F o o' then w o o' else 0)]
  refine Finset.sum_congr rfl ?_
  intro g hg
  rw [filter_cellOf_eq hg]
  refine Finset.sum_congr rfl ?_
  intro o ho
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  obtain ⟨o₀, -, rfl⟩ := Finset.mem_image.1 hg
  have ho' : SameOn c F o o₀ := by simpa using ho
  ext o'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_cellOf]
  constructor
  · intro hh; exact sameOn_trans ho' (sameOn_symm hh)
  · intro hh; exact sameOn_trans (sameOn_symm hh) ho'

/-- For any `Ξ`, `T_F(Ξ) = ∑_{t ∈ 𝒯_F} ι_{F,t}'Ξ ι_{F,t} - tr(Ξ)`. -/
theorem superAgg_eq_cells (c : D → O → L) (F : Finset D) (w : O → O → ℝ) :
    superAgg c F w = (∑ t ∈ cells c F, ∑ o ∈ t, ∑ o' ∈ t, w o o') - ∑ o : O, w o o := by
  classical
  rw [sum_cells_pair, superAgg]
  have key : ∀ o : O, (∑ o' : O, if SameOn c F o o' then w o o' else 0)
      = (∑ o' : O, if o ≠ o' ∧ SameOn c F o o' then w o o' else 0) + w o o := by
    intro o
    have h1 : ∀ o' : O, (if SameOn c F o o' then w o o' else 0)
        = (if o ≠ o' ∧ SameOn c F o o' then w o o' else 0)
          + (if o' = o then w o o' else 0) := by
      intro o'
      by_cases h : o' = o
      · subst h; simp [sameOn_refl]
      · have h2 : o ≠ o' := fun hc => h hc.symm
        simp [h, h2]
    rw [Finset.sum_congr rfl (fun o' _ => h1 o'), Finset.sum_add_distrib]
    simp
  rw [Finset.sum_congr rfl (fun o _ => key o), Finset.sum_add_distrib]
  ring

end Partition

/-! ### Part (a): the grouped form of the superset aggregates -/

section PartA

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

/-- **Proposition SM.E.2(a), first identity.**
`T_F(v) = ∑_{t ∈ 𝒯_F}(u_{F,t}² - q_{F,t})`. -/
theorem superAgg_vec (c : D → O → L) (F : Finset D) (v : O → ℝ) :
    superAgg c F (fun o o' => v o * v o')
      = ∑ t ∈ cells c F, ((∑ o ∈ t, v o) ^ 2 - ∑ o ∈ t, v o ^ 2) := by
  classical
  rw [superAgg_eq_cells]
  have h1 : ∀ t : Finset O, (∑ o ∈ t, ∑ o' ∈ t, v o * v o') = (∑ o ∈ t, v o) ^ 2 := by
    intro t; rw [sq, Finset.sum_mul_sum]
  have h2 : (∑ o : O, v o * v o) = ∑ t ∈ cells c F, ∑ o ∈ t, v o ^ 2 := by
    rw [sum_over_cells]
    exact Finset.sum_congr rfl fun o _ => (sq (v o)).symm
  rw [h2, Finset.sum_congr rfl (fun t _ => h1 t), ← Finset.sum_sub_distrib]

/-- **Proposition SM.E.2(a), second identity.**
`C_F = ∑_{t ∈ 𝒯_F}(n_{F,t}² - n_{F,t})`. -/
theorem superAgg_one (c : D → O → L) (F : Finset D) :
    superAgg c F (fun _ _ => 1)
      = ∑ t ∈ cells c F, ((t.card : ℝ) ^ 2 - (t.card : ℝ)) := by
  classical
  rw [superAgg_eq_cells]
  have h1 : ∀ t : Finset O, (∑ _o ∈ t, ∑ _o' ∈ t, (1 : ℝ)) = (t.card : ℝ) ^ 2 := by
    intro t; simp [sq]
  have h2 : (∑ _o : O, (1 : ℝ)) = ∑ t ∈ cells c F, (t.card : ℝ) := by
    rw [← sum_over_cells c F (fun _ => (1 : ℝ))]
    simp
  rw [h2, Finset.sum_congr rfl (fun t _ => h1 t), ← Finset.sum_sub_distrib]

/-- `C_F = #{(o,o') : o ≠ o', F ⊆ E(o,o')}` is the aggregate at `w = 1`. -/
theorem superAgg_one_eq_card (c : D → O → L) (dims F : Finset D) (hF : F ⊆ dims) :
    superAgg c F (fun _ _ => 1)
      = ((univ.filter fun p : O × O =>
            p.1 ≠ p.2 ∧ F ⊆ sharedDims c dims p.1 p.2).card : ℝ) := by
  classical
  rw [← Finset.sum_boole, Fintype.sum_prod_type, superAgg]
  refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => ?_
  by_cases h : SameOn c F o o'
  · simp [h, (sameOn_iff_subset (c := c) (dims := dims) hF).1 h]
  · have h2 : ¬ F ⊆ sharedDims c dims o o' :=
      fun hc => h ((sameOn_iff_subset (c := c) (dims := dims) hF).2 hc)
    simp [h, h2]

/-- `|P_F|` is the exact aggregate at `w = 1`. -/
theorem exactAgg_one_eq_card (c : D → O → L) (dims F : Finset D) :
    exactAgg c dims F (fun _ _ => 1)
      = ((univ.filter fun p : O × O =>
            p.1 ≠ p.2 ∧ sharedDims c dims p.1 p.2 = F).card : ℝ) := by
  classical
  rw [← Finset.sum_boole, Fintype.sum_prod_type, exactAgg]

end PartA

/-! ### Part (b): Möbius inversion on the Boolean lattice -/

section PartB

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

/-- On the Boolean lattice, `∑_{F ⊆ G ⊆ E}(-1)^{|G|-|F|}` is `1` when
`E = F` and `0` otherwise. -/
theorem alternating_interval (F E : Finset D) :
    ∑ G ∈ E.powerset.filter (fun G => F ⊆ G), (-1 : ℝ) ^ (G.card - F.card)
      = if E = F then 1 else 0 := by
  classical
  by_cases hFE : F ⊆ E
  · have hbij : ∑ G ∈ E.powerset.filter (fun G => F ⊆ G), (-1 : ℝ) ^ (G.card - F.card)
        = ∑ H ∈ (E \ F).powerset, (-1 : ℝ) ^ H.card := by
      refine Finset.sum_nbij' (fun G => G \ F) (fun H => F ∪ H) ?_ ?_ ?_ ?_ ?_
      · intro G hG
        have hGE : G ⊆ E := Finset.mem_powerset.1 (Finset.mem_filter.1 hG).1
        exact Finset.mem_powerset.2 (Finset.sdiff_subset_sdiff hGE le_rfl)
      · intro H hH
        have hHE : H ⊆ E \ F := Finset.mem_powerset.1 hH
        exact Finset.mem_filter.2
          ⟨Finset.mem_powerset.2 (Finset.union_subset hFE (hHE.trans Finset.sdiff_subset)),
            Finset.subset_union_left⟩
      · intro G hG
        exact Finset.union_sdiff_of_subset (Finset.mem_filter.1 hG).2
      · intro H hH
        have hHE : H ⊆ E \ F := Finset.mem_powerset.1 hH
        have hdisj : Disjoint F H :=
          Finset.disjoint_right.2 fun a ha => (Finset.mem_sdiff.1 (hHE ha)).2
        exact Finset.union_sdiff_cancel_left hdisj
      · intro G hG
        rw [Finset.card_sdiff, Finset.inter_eq_left.2 (Finset.mem_filter.1 hG).2]
    rw [hbij]
    have hZ : ∑ H ∈ (E \ F).powerset, (-1 : ℤ) ^ H.card = if E \ F = ∅ then (1 : ℤ) else 0 :=
      Finset.sum_powerset_neg_one_pow_card
    have hR : ∑ H ∈ (E \ F).powerset, (-1 : ℝ) ^ H.card
        = if E \ F = ∅ then (1 : ℝ) else 0 := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hZ
      push_cast at this
      simpa using this
    rw [hR]
    have hiff : E \ F = ∅ ↔ E = F :=
      ⟨fun h => Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.1 h) hFE,
        fun h => by subst h; simp⟩
    by_cases h : E = F
    · simp [h]
    · have hnsub : ¬ E ⊆ F := fun hc => h (Finset.Subset.antisymm hc hFE)
      simp [h, hiff]
  · have hempty : E.powerset.filter (fun G => F ⊆ G) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 ?_
      intro G hG hFG
      exact hFE (hFG.trans (Finset.mem_powerset.1 hG))
    have hne : E ≠ F := fun h => hFE (h ▸ Finset.Subset.refl F)
    simp [hempty, hne]

/-- **Proposition SM.E.2(b).** `∑_{(o,o') ∈ P_F} w_{oo'} = ∑_{G ⊇ F}(-1)^{|G|-|F|}T_G(w)`
for an arbitrary weight `w`, by Möbius inversion. If `F ⊄ dims` both sides are `0`. -/
theorem exactAgg_eq_mobius (c : D → O → L) (dims F : Finset D) (w : O → O → ℝ) :
    exactAgg c dims F w
      = ∑ G ∈ dims.powerset.filter (fun G => F ⊆ G),
          (-1 : ℝ) ^ (G.card - F.card) * superAgg c G w := by
  classical
  simp only [superAgg, Finset.mul_sum]
  rw [Finset.sum_comm, exactAgg]
  refine Finset.sum_congr rfl ?_
  intro o _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro o' _
  by_cases hne : o ≠ o'
  · set E : Finset D := sharedDims c dims o o' with hEdef
    have hEsub : E ⊆ dims := Finset.filter_subset _ _
    have hrestrict :
        ∑ G ∈ dims.powerset.filter (fun G => F ⊆ G),
            (-1 : ℝ) ^ (G.card - F.card) *
              (if o ≠ o' ∧ SameOn c G o o' then w o o' else 0)
          = w o o' * ∑ G ∈ E.powerset.filter (fun G => F ⊆ G),
              (-1 : ℝ) ^ (G.card - F.card) := by
      rw [Finset.mul_sum, Finset.sum_filter, Finset.sum_filter,
        ← Finset.sum_subset (Finset.powerset_mono.2 hEsub)]
      · refine Finset.sum_congr rfl ?_
        intro G hG
        have hGE : G ⊆ E := Finset.mem_powerset.1 hG
        have hGd : G ⊆ dims := hGE.trans hEsub
        have hsame : SameOn c G o o' :=
          (sameOn_iff_subset (c := c) (dims := dims) hGd).2 hGE
        by_cases hFG : F ⊆ G
        · simp [hFG, hne, hsame, mul_comm]
        · simp [hFG]
      · intro G hG hG'
        have hGd : G ⊆ dims := Finset.mem_powerset.1 hG
        have hnot : ¬ G ⊆ E := fun hc => hG' (Finset.mem_powerset.2 hc)
        have hno : ¬ SameOn c G o o' :=
          fun hc => hnot ((sameOn_iff_subset (c := c) (dims := dims) hGd).1 hc)
        by_cases hFG : F ⊆ G <;> simp [hFG, hno]
    rw [hrestrict, alternating_interval]
    by_cases hEF : E = F
    · simp [hne, hEF]
    · simp [hne, hEF]
  · simp [hne]

end PartB

/-! ### Part (c): the residual maker, the sharing matrices and the two Frobenius norms -/

section PartC

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

/-- `ι_s'Ξ ι_t`, the cross term of two cells. -/
def cellCross (Ξ : Matrix O O ℝ) (s t : Finset O) : ℝ := ∑ o ∈ s, ∑ o' ∈ t, Ξ o o'

/-- `ι_{F,t}'Ξ ι_{F,t}`. -/
def cellQuad (Ξ : Matrix O O ℝ) (t : Finset O) : ℝ := cellCross Ξ t t

/-- The sharing matrix `Sh_e`, with `(Sh_e)_{oo'} = 𝟙{o ⊙ e = o' ⊙ e}`. -/
def shMat (c : D → O → L) (e : Finset D) : Matrix O O ℝ :=
  Matrix.of fun o o' => if SameOn c e o o' then 1 else 0

/-- `Sh^off_e = Sh_e - I_n`. -/
def shOff (c : D → O → L) (e : Finset D) : Matrix O O ℝ := shMat c e - 1

/-- `‖RΔ_e‖_F²`, the columns of `Δ_e` being the indicators of the cells of level `e`. -/
def frobSqRDelta (c : D → O → L) (R : Matrix O O ℝ) (e : Finset D) : ℝ :=
  ∑ o : O, ∑ t ∈ cells c e, (∑ o' ∈ t, R o o') ^ 2

/-- `‖Δ_e'RΔ_F‖_F²`, whose `(s,t)` entry is `ι_{e,s}'R ι_{F,t}`. -/
def frobSqCross (c : D → O → L) (R : Matrix O O ℝ) (e F : Finset D) : ℝ :=
  ∑ s ∈ cells c e, ∑ t ∈ cells c F, cellCross R s t ^ 2

/-- `Δ_FΔ_F' = Sh_F` entrywise, since exactly one cell of level `F` contains a given
observation. -/
theorem shMat_apply_eq_sum_cells (c : D → O → L) (e : Finset D) (o o' : O) :
    shMat c e o o'
      = ∑ t ∈ cells c e,
          (if o ∈ t then (1 : ℝ) else 0) * (if o' ∈ t then (1 : ℝ) else 0) := by
  classical
  have hmem : cellOf c e o ∈ cells c e := Finset.mem_image_of_mem _ (Finset.mem_univ o)
  rw [Finset.sum_eq_single (cellOf c e o)]
  · have h1 : (if o ∈ cellOf c e o then (1 : ℝ) else 0) = 1 := by
      simp [sameOn_refl]
    have h2 : (if o' ∈ cellOf c e o then (1 : ℝ) else 0)
        = if SameOn c e o o' then (1 : ℝ) else 0 := by
      by_cases h : SameOn c e o o'
      · simp [h, sameOn_symm h]
      · have h' : ¬ SameOn c e o' o := fun hc => h (sameOn_symm hc)
        simp [h, h']
    rw [h1, h2, shMat]
    simp
  · intro t ht hne
    have hot : o ∉ t := by
      intro hmemt
      obtain ⟨o₀, -, rfl⟩ := Finset.mem_image.1 ht
      exact hne (cellOf_eq_iff.2 (by simpa using hmemt)).symm
    simp [hot]
  · intro h; exact absurd hmem h

/-- The indicator form of a sum over a cell. -/
theorem sum_indicator (s : Finset O) (f : O → ℝ) :
    (∑ a : O, if a ∈ s then f a else 0) = ∑ a ∈ s, f a := by
  classical
  rw [← Finset.sum_filter, Finset.filter_univ_mem]

/-- `tr(A Sh_F) = ∑_{t ∈ 𝒯_F} ι_{F,t}'A ι_{F,t}`, the partition identity applied to
the diagonal of a product. -/
theorem trace_mul_shMat (c : D → O → L) (F : Finset D) (A : Matrix O O ℝ) :
    (A * shMat c F).trace = ∑ t ∈ cells c F, cellQuad A t := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, shMat, Matrix.of_apply,
    mul_ite, mul_one, mul_zero, cellQuad, cellCross]
  rw [sum_cells_pair c F (fun o o' => A o o')]
  refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => ?_
  by_cases h : SameOn c F o' o
  · simp [h, sameOn_symm h]
  · have h' : ¬ SameOn c F o o' := fun hc => h (sameOn_symm hc)
    simp [h, h']

/-- `R Sh_e R = (RΔ_e)(RΔ_e)'`, entrywise, by the symmetry of `R`. -/
theorem mul_shMat_mul_apply (c : D → O → L) (e : Finset D) {R : Matrix O O ℝ}
    (hsymm : R.IsSymm) (o o' : O) :
    (R * shMat c e * R) o o'
      = ∑ s ∈ cells c e, (∑ a ∈ s, R o a) * (∑ b ∈ s, R o' b) := by
  classical
  have hL : (R * shMat c e * R) o o'
      = ∑ b : O, ∑ a : O, ∑ s ∈ cells c e,
          (if a ∈ s then R o a else 0) * (if b ∈ s then R o' b else 0) := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [shMat_apply_eq_sum_cells, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hb : R b o' = R o' b := hsymm.apply o' b
    by_cases ha : a ∈ s <;> by_cases hbs : b ∈ s <;> simp [ha, hbs, hb]
  have hR : ∀ s : Finset O, (∑ a ∈ s, R o a) * (∑ b ∈ s, R o' b)
      = ∑ b : O, ∑ a : O,
          (if a ∈ s then R o a else 0) * (if b ∈ s then R o' b else 0) := by
    intro s
    rw [← sum_indicator s (fun a => R o a), ← sum_indicator s (fun b => R o' b),
      Finset.sum_mul_sum, Finset.sum_comm]
  rw [hL]
  have h1 : ∀ b : O,
      (∑ a : O, ∑ s ∈ cells c e,
          (if a ∈ s then R o a else 0) * (if b ∈ s then R o' b else 0))
        = ∑ s ∈ cells c e, ∑ a : O,
          (if a ∈ s then R o a else 0) * (if b ∈ s then R o' b else 0) :=
    fun _ => Finset.sum_comm
  rw [Finset.sum_congr rfl (fun b _ => h1 b), Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => (hR s).symm

/-- `R Sh^off_e R = (RΔ_e)(RΔ_e)' - R`, entrywise, by the idempotence of `R`. -/
theorem mul_shOff_mul_apply (c : D → O → L) (e : Finset D) {R : Matrix O O ℝ}
    (hsymm : R.IsSymm) (hidem : R * R = R) (o o' : O) :
    (R * shOff c e * R) o o'
      = (∑ s ∈ cells c e, (∑ a ∈ s, R o a) * (∑ b ∈ s, R o' b)) - R o o' := by
  have hmat : R * shOff c e * R = R * shMat c e * R - R := by
    rw [shOff, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hidem]
  rw [hmat, Matrix.sub_apply, mul_shMat_mul_apply c e hsymm o o']

omit [Fintype O] [DecidableEq O] in
/-- `ι_s'R ι_t = ι_t'R ι_s` for symmetric `R`. -/
theorem cellCross_comm {R : Matrix O O ℝ} (hsymm : R.IsSymm) (s t : Finset O) :
    cellCross R s t = cellCross R t s := by
  have h1 : (∑ o ∈ s, ∑ o' ∈ t, R o o') = ∑ o' ∈ t, ∑ o ∈ s, R o o' := Finset.sum_comm
  rw [cellCross, cellCross, h1]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hsymm.apply x y

/-- `ι_{F,t}'(R Sh_e R)ι_{F,t} = ∑_{s ∈ 𝒯_e}(ι_{F,t}'R ι_{e,s})²`. -/
theorem cellQuad_mul_shMat_mul (c : D → O → L) (e : Finset D) {R : Matrix O O ℝ}
    (hsymm : R.IsSymm) (t : Finset O) :
    cellQuad (R * shMat c e * R) t = ∑ s ∈ cells c e, cellCross R t s ^ 2 := by
  classical
  simp only [cellQuad, cellCross, mul_shMat_mul_apply c e hsymm]
  have h1 : ∀ o : O,
      (∑ o' ∈ t, ∑ s ∈ cells c e, (∑ a ∈ s, R o a) * (∑ b ∈ s, R o' b))
        = ∑ s ∈ cells c e, ∑ o' ∈ t, (∑ a ∈ s, R o a) * (∑ b ∈ s, R o' b) :=
    fun _ => Finset.sum_comm
  rw [Finset.sum_congr rfl (fun o _ => h1 o), Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [sq, Finset.sum_mul_sum]

/-- **Proposition SM.E.2(c), first display.**
`T_F(R) = ∑_{t ∈ 𝒯_F} ι_{F,t}'R ι_{F,t} - tr(R)`. -/
theorem superAgg_residual (c : D → O → L) (F : Finset D) (R : Matrix O O ℝ) :
    superAgg c F (fun o o' => R o o') = (∑ t ∈ cells c F, cellQuad R t) - R.trace := by
  rw [superAgg_eq_cells]
  simp [cellQuad, cellCross, Matrix.trace, Matrix.diag_apply]

omit [DecidableEq D] in
/-- **Proposition SM.E.2(c), third claim.** `‖RΔ_e‖_F² = ∑_{t ∈ 𝒯_e} ι_{e,t}'R ι_{e,t}`
for idempotent `R`. -/
theorem frobSqRDelta_eq_sum_cellQuad (c : D → O → L) (e : Finset D) {R : Matrix O O ℝ}
    (hsymm : R.IsSymm) (hidem : R * R = R) :
    frobSqRDelta c R e = ∑ t ∈ cells c e, cellQuad R t := by
  classical
  rw [frobSqRDelta, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : ∀ o : O, (∑ a ∈ t, R o a) ^ 2 = ∑ a ∈ t, ∑ b ∈ t, R o a * R o b := by
    intro o; rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl (fun o _ => h1 o), Finset.sum_comm, cellQuad, cellCross]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hmul : ∑ o : O, R o a * R o b = (R * R) a b := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun o _ => by rw [hsymm.apply a o]
  rw [hmul, hidem]

/-- **Proposition SM.E.2(c), fourth claim.** `‖Δ_e'RΔ_F‖_F² = tr(R Sh_e R Sh_F)`. -/
theorem frobSqCross_eq_trace (c : D → O → L) (e F : Finset D) {R : Matrix O O ℝ}
    (hsymm : R.IsSymm) :
    frobSqCross c R e F = (R * shMat c e * R * shMat c F).trace := by
  classical
  rw [trace_mul_shMat, frobSqCross, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [cellQuad_mul_shMat_mul c e hsymm]
  exact Finset.sum_congr rfl fun s _ => by rw [cellCross_comm hsymm s t]

/-- **Proposition SM.E.2(c), second display.**
`T_F(R Sh^off_e R) = ‖Δ_e'RΔ_F‖_F² - ∑_{t ∈ 𝒯_F} ι_{F,t}'R ι_{F,t} - ‖RΔ_e‖_F² + tr(R)`. -/
theorem superAgg_residual_interaction (c : D → O → L) (e F : Finset D) {R : Matrix O O ℝ}
    (hsymm : R.IsSymm) (hidem : R * R = R) :
    superAgg c F (fun o o' => (R * shOff c e * R) o o')
      = frobSqCross c R e F - (∑ t ∈ cells c F, cellQuad R t)
        - frobSqRDelta c R e + R.trace := by
  classical
  rw [superAgg_eq_cells]
  -- the cell blocks, `Ξ = (RΔ_e)(RΔ_e)' - R`
  have hcell : ∀ t : Finset O,
      (∑ o ∈ t, ∑ o' ∈ t, (R * shOff c e * R) o o')
        = cellQuad (R * shMat c e * R) t - cellQuad R t := by
    intro t
    simp only [mul_shOff_mul_apply c e hsymm hidem, cellQuad, cellCross,
      mul_shMat_mul_apply c e hsymm]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun o _ => Finset.sum_sub_distrib _ _
  have hblocks : (∑ t ∈ cells c F, ∑ o ∈ t, ∑ o' ∈ t, (R * shOff c e * R) o o')
      = frobSqCross c R e F - ∑ t ∈ cells c F, cellQuad R t := by
    rw [Finset.sum_congr rfl (fun t _ => hcell t), Finset.sum_sub_distrib]
    congr 1
    rw [frobSqCross, Finset.sum_comm]
    exact Finset.sum_congr rfl fun t _ =>
      (cellQuad_mul_shMat_mul c e hsymm t).trans
        (Finset.sum_congr rfl fun s _ => by rw [cellCross_comm hsymm t s])
  -- the diagonal, `tr(Ξ) = ‖RΔ_e‖_F² - tr(R)`
  have hdiag : (∑ o : O, (R * shOff c e * R) o o) = frobSqRDelta c R e - R.trace := by
    have h1 : ∀ o : O, (R * shOff c e * R) o o
        = (∑ s ∈ cells c e, (∑ a ∈ s, R o a) ^ 2) - R o o := by
      intro o
      rw [mul_shOff_mul_apply c e hsymm hidem]
      congr 1
      exact Finset.sum_congr rfl fun s _ => (sq _).symm
    rw [Finset.sum_congr rfl (fun o _ => h1 o), Finset.sum_sub_distrib]
    simp only [frobSqRDelta, Matrix.trace, Matrix.diag_apply]
  rw [hblocks, hdiag]
  ring

/-- **Proposition SM.E.2(c), last claim.** If `F = {m}` and `RΔ_m = 0`, then
`T_F(R) = -tr(R)`. -/
theorem superAgg_residual_singleton (c : D → O → L) (m : D) {R : Matrix O O ℝ}
    (hRD : ∀ t ∈ cells c ({m} : Finset D), ∀ o : O, ∑ o' ∈ t, R o o' = 0) :
    superAgg c ({m} : Finset D) (fun o o' => R o o') = -R.trace := by
  rw [superAgg_residual]
  have hzero : ∑ t ∈ cells c ({m} : Finset D), cellQuad R t = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    rw [cellQuad, cellCross]
    exact Finset.sum_eq_zero fun o _ => hRD t ht o
  rw [hzero, zero_sub]

omit [Fintype O] [DecidableEq O] in
/-- **Proposition SM.E.2(c), second claim.** If `R = Q - X̃ A X̃'`, then
`ι_{F,t}'R ι_{F,t} = ι_{F,t}'Q ι_{F,t} - (X̃'ι_{F,t})'A(X̃'ι_{F,t})`,
applied with `A = (X̃'X̃)⁻¹`. -/
theorem cellQuad_sub_of_eq_mul {K : Type*} [Fintype K] {R Q Lam : Matrix O O ℝ}
    (Xt : Matrix O K ℝ) (A : Matrix K K ℝ) (hR : R = Q - Lam)
    (hLam : Lam = Xt * A * Xt.transpose) (t : Finset O) :
    cellQuad R t
      = cellQuad Q t
        - ∑ a : K, ∑ b : K, (∑ o ∈ t, Xt o a) * A a b * (∑ o' ∈ t, Xt o' b) := by
  classical
  have hpull : ∀ (T : Finset O) (g : O → K → K → ℝ),
      (∑ o ∈ T, ∑ a : K, ∑ b : K, g o a b) = ∑ a : K, ∑ b : K, ∑ o ∈ T, g o a b := by
    intro T g
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  have hLamCell : cellQuad Lam t
      = ∑ a : K, ∑ b : K, (∑ o ∈ t, Xt o a) * A a b * (∑ o' ∈ t, Xt o' b) := by
    have hentry : ∀ o o' : O, Lam o o'
        = ∑ a : K, ∑ b : K, Xt o a * A a b * Xt o' b := by
      intro o o'
      have h0 : Lam o o' = ∑ b : K, ∑ a : K, Xt o a * A a b * Xt o' b := by
        rw [hLam, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Matrix.mul_apply, Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by rw [Matrix.transpose_apply]
      rw [h0, Finset.sum_comm]
    have hprod : ∀ a b : K, (∑ o ∈ t, Xt o a) * A a b * (∑ o' ∈ t, Xt o' b)
        = ∑ o ∈ t, ∑ o' ∈ t, Xt o a * A a b * Xt o' b := by
      intro a b
      rw [Finset.sum_mul, Finset.sum_mul_sum]
    simp only [cellQuad, cellCross, hentry]
    rw [Finset.sum_congr rfl
        (fun o (_ : o ∈ t) => hpull t (fun o' a b => Xt o a * A a b * Xt o' b)),
      hpull t (fun o a b => ∑ o' ∈ t, Xt o a * A a b * Xt o' b)]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => (hprod a b).symm
  have hsub : cellQuad R t = cellQuad Q t - cellQuad Lam t := by
    simp only [hR, cellQuad, cellCross, Matrix.sub_apply]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun o _ => Finset.sum_sub_distrib _ _
  rw [hsub, hLamCell]

end PartC

end Multiway
