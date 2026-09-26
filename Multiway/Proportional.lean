import Multiway.Pairwise
import Mathlib.Logic.Relation

/-!
# Two-way characterization under proportional cell frequencies

This file formalizes Theorem 2 of the paper (Two-way characterization under proportional cell
frequencies) for two index maps `f g : O → L`. On a connected bipartite support graph, the
marginal projectors commute if and only if `n_{it} = T_i C_t / n` for every realized pair of
categories; proportionality forces a complete support; and when `n_{it} ∈ {0,1}`,
proportionality holds if and only if every cell count equals one. The statement that
dimension-wise Mundlak augmentation is uniformly fixed-effects equivalent if and only if the cell
frequencies are proportional is `ProjBridge.uniformlyFEEquivalent_iff_proportional`.

## Main results

* `commute_iff_proportional`: `P_1P_2 = P_2P_1 ↔ n_{it} = T_iC_t/n` on a connected support.
* `pairCount_pos_of_proportional`: proportionality implies `n_{it} > 0`.
* `proportional_iff_pairCount_eq_one`: the `{0,1}` clause.
* The `_of_surjective` variants quantify over all of `L × L` when every category is realized.
-/

open Finset Matrix

namespace Multiway

section Proportional

variable {O : Type*} [Fintype O] {L : Type*} [DecidableEq L]

/-! ### The bipartite support graph -/

/-- Adjacency in the bipartite support graph: the categories of the first dimension on one
side (`Sum.inl`) and those of the second on the other (`Sum.inr`), with an edge between `i`
and `t` whenever `n_{it} > 0`. The graph is undirected, so both orientations are edges. -/
def supportAdj (f g : O → L) : L ⊕ L → L ⊕ L → Prop
  | Sum.inl i, Sum.inr t => 0 < pairCount f g i t
  | Sum.inr t, Sum.inl i => 0 < pairCount f g i t
  | Sum.inl _, Sum.inl _ => False
  | Sum.inr _, Sum.inr _ => False

@[simp] lemma supportAdj_inl_inr (f g : O → L) (i t : L) :
    supportAdj f g (Sum.inl i) (Sum.inr t) ↔ 0 < pairCount f g i t := Iff.rfl

@[simp] lemma supportAdj_inr_inl (f g : O → L) (i t : L) :
    supportAdj f g (Sum.inr t) (Sum.inl i) ↔ 0 < pairCount f g i t := Iff.rfl

@[simp] lemma supportAdj_inl_inl (f g : O → L) (i j : L) :
    ¬ supportAdj f g (Sum.inl i) (Sum.inl j) := id

@[simp] lemma supportAdj_inr_inr (f g : O → L) (s t : L) :
    ¬ supportAdj f g (Sum.inr s) (Sum.inr t) := id

/-- The vertices of the bipartite support graph, `𝒩_1 ⊔ 𝒩_2`: the realized categories. -/
def IsSupportVertex (f g : O → L) : L ⊕ L → Prop
  | Sum.inl i => i ∈ Set.range f
  | Sum.inr t => t ∈ Set.range g

/-- The bipartite support graph is connected: every vertex can be reached from every other one
through a sequence of edges. -/
def SupportConnected (f g : O → L) : Prop :=
  ∀ u v : L ⊕ L, IsSupportVertex f g u → IsSupportVertex f g v →
    Relation.ReflTransGen (supportAdj f g) u v

/-- `Realizes f g u o`: the observation `o` carries the category the vertex `u` stands for.
Every observation realizes exactly one vertex on each side, and the two vertices it realizes
are adjacent. -/
def Realizes (f g : O → L) : L ⊕ L → O → Prop
  | Sum.inl i, o => f o = i
  | Sum.inr t, o => g o = t

/-- An edge of the support graph is an occupied cell, which holds an observation carrying both
endpoints' categories. -/
lemma exists_realizes_of_supportAdj (f g : O → L) {u v : L ⊕ L} (h : supportAdj f g u v) :
    ∃ o : O, Realizes f g u o ∧ Realizes f g v o := by
  cases u with
  | inl i =>
      cases v with
      | inl j => exact absurd h (supportAdj_inl_inl f g i j)
      | inr t =>
          obtain ⟨o, ho⟩ := Finset.card_pos.mp h
          rw [Finset.mem_filter] at ho
          exact ⟨o, ho.2.1, ho.2.2⟩
  | inr s =>
      cases v with
      | inl i =>
          obtain ⟨o, ho⟩ := Finset.card_pos.mp h
          rw [Finset.mem_filter] at ho
          exact ⟨o, ho.2.2, ho.2.1⟩
      | inr t => exact absurd h (supportAdj_inr_inr f g s t)

omit [Fintype O] [DecidableEq L] in
/-- Two observations realizing the *same* vertex agree under any function that is constant
within every row category and within every column category. -/
lemma eq_of_realizes (f g : O → L) {z : O → ℝ}
    (hf : ∀ o o', f o = f o' → z o = z o') (hg : ∀ o o', g o = g o' → z o = z o')
    {u : L ⊕ L} {o o' : O} (ho : Realizes f g u o) (ho' : Realizes f g u o') :
    z o = z o' := by
  cases u with
  | inl i =>
      have h1 : f o = i := ho
      have h2 : f o' = i := ho'
      exact hf o o' (h1.trans h2.symm)
  | inr t =>
      have h1 : g o = t := ho
      have h2 : g o' = t := ho'
      exact hg o o' (h1.trans h2.symm)

/-- A function constant within every row category and within every column category takes the
same value at two observations realizing the two ends of a walk. -/
lemma eq_of_supportWalk (f g : O → L) {z : O → ℝ}
    (hf : ∀ o o', f o = f o' → z o = z o') (hg : ∀ o o', g o = g o' → z o = z o')
    {u v : L ⊕ L} (h : Relation.ReflTransGen (supportAdj f g) u v)
    {o : O} (ho : Realizes f g u o) :
    ∀ o' : O, Realizes f g v o' → z o = z o' := by
  induction h with
  | refl => exact fun o' ho' => eq_of_realizes f g hf hg ho ho'
  | tail _ hbc ih =>
      intro o' ho'
      obtain ⟨p, hp1, hp2⟩ := exists_realizes_of_supportAdj f g hbc
      exact (ih p hp1).trans (eq_of_realizes f g hf hg hp2 ho')

/-- A function constant within every row category and within every column category is constant
on a connected support, that is, `𝒮_1 ∩ 𝒮_2 = span(ι_n)`. -/
lemma eq_of_supportConnected (f g : O → L) (hconn : SupportConnected f g) {z : O → ℝ}
    (hf : ∀ o o', f o = f o' → z o = z o') (hg : ∀ o o', g o = g o' → z o = z o')
    (o o' : O) : z o = z o' :=
  eq_of_supportWalk f g hf hg
    (hconn (Sum.inl (f o)) (Sum.inl (f o')) ⟨o, rfl⟩ ⟨o', rfl⟩) rfl o' rfl

/-! ### Elementary facts about the marginal projectors and the counts -/

/-- The pairwise cell count is symmetric in the two dimensions. -/
lemma pairCount_comm (f g : O → L) (a b : L) : pairCount g f b a = pairCount f g a b := by
  rw [pairCount_eq_card, pairCount_eq_card]
  congr 1
  ext o
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-- `P_m` is symmetric. -/
lemma transpose_proj (f : O → L) : (proj f)ᵀ = proj f := by
  ext o o'
  simp only [Matrix.transpose_apply, proj_apply]
  by_cases h : f o = f o'
  · simp [h]
  · have h' : ¬ f o' = f o := fun hh => h hh.symm
    simp [h, h']

/-- `P_mι_n = ι_n`: every row of a marginal projector sums to one. -/
lemma sum_proj_row (f : O → L) (o : O) : ∑ o' : O, proj f o o' = 1 := by
  have hrw : ∀ o' : O, proj f o o'
      = if f o' = f o then (margCount f (f o) : ℝ)⁻¹ else 0 := by
    intro o'
    simp only [proj_apply]
    by_cases h : f o = f o'
    · simp [h]
    · have h' : ¬ f o' = f o := fun hh => h hh.symm
      simp [h, h']
  have hT : (margCount f (f o) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (margCount_pos f o).ne'
  simp only [hrw]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← margCount_eq_card,
    mul_inv_cancel₀ hT]

/-- The row margin is the sum of the cells along its row: `T_i = ∑_t n_{it}`. -/
lemma margCount_eq_sum_pairCount (f g : O → L) (i : L) :
    margCount f i = ∑ t ∈ Finset.univ.image g, pairCount f g i t := by
  classical
  rw [margCount_eq_card,
    Finset.card_eq_sum_card_fiberwise (f := g) (t := Finset.univ.image g)
      (fun o _ => by simp)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [pairCount_eq_card]
  congr 1
  ext o
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The sample size is the sum of the margins: `n = ∑_i T_i`. -/
lemma card_eq_sum_margCount (f : O → L) :
    Fintype.card O = ∑ i ∈ Finset.univ.image f, margCount f i := by
  classical
  rw [← Finset.card_univ, Finset.card_eq_sum_card_image f Finset.univ]
  exact Finset.sum_congr rfl fun i _ => (margCount_eq_card f i).symm

/-- A realized category is a category of the index map's image, and conversely. -/
lemma mem_univ_image_of_mem_range (f : O → L) {i : L} (h : i ∈ Set.range f) :
    i ∈ Finset.univ.image f := by
  obtain ⟨o, rfl⟩ := h
  exact Finset.mem_image_of_mem f (Finset.mem_univ o)

lemma mem_range_of_mem_univ_image (f : O → L) {i : L} (h : i ∈ Finset.univ.image f) :
    i ∈ Set.range f := by
  obtain ⟨o, -, rfl⟩ := Finset.mem_image.mp h
  exact ⟨o, rfl⟩

/-! ### The direction that needs connectedness -/

/-- The entry `(P_1P_2)_{o,o'}` depends on `o` only through `i_1(o)` and on `o'` only through
`i_2(o')` (Lemma SM.B.3). -/
lemma proj_mul_proj_apply_congr (f g : O → L) {o₁ o₂ o₃ o₄ : O}
    (h₁ : f o₁ = f o₂) (h₂ : g o₃ = g o₄) :
    (proj f * proj g) o₁ o₃ = (proj f * proj g) o₂ o₄ := by
  rw [entries_crossProjector_mul, entries_crossProjector_mul, h₁, h₂]

/-- `(P_2P_1)_{o,o'} = (P_1P_2)_{o',o}`. -/
lemma proj_mul_proj_apply_swap (f g : O → L) (o o' : O) :
    (proj g * proj f) o o' = (proj f * proj g) o' o := by
  rw [entries_crossProjector_mul, entries_crossProjector_mul,
    pairCount_comm f g (f o') (g o), mul_comm ((margCount g (g o) : ℝ))]

/-- Every row of `P_1P_2` sums to one, since `P_2ι_n = ι_n` and `P_1ι_n = ι_n`. -/
lemma sum_proj_mul_proj_row (f g : O → L) (o : O) :
    ∑ o' : O, (proj f * proj g) o o' = 1 := by
  have hmul : ∀ o' : O, (proj f * proj g) o o'
      = ∑ o'' : O, proj f o o'' * proj g o'' o' := fun _ => Matrix.mul_apply
  simp only [hmul]
  rw [Finset.sum_comm]
  have hinner : ∀ o'' : O, ∑ o' : O, proj f o o'' * proj g o'' o' = proj f o o'' := by
    intro o''
    rw [← Finset.mul_sum, sum_proj_row, mul_one]
  simp only [hinner]
  exact sum_proj_row f o

/-- Commuting marginal projectors on a connected two-way support multiply to `P_0`. Each column
of `P_1P_2` is constant within row and column categories, hence constant by connectedness, and
sums to one by symmetry and the unit row sums. -/
theorem proj_mul_proj_eq_grandMeanProj_of_commute (f g : O → L) (hconn : SupportConnected f g)
    (hcomm : proj f * proj g = proj g * proj f) :
    proj f * proj g = grandMeanProj O := by
  -- commutation is the symmetry of `P_1P_2`
  have hsymm : ∀ o o' : O, (proj f * proj g) o o' = (proj f * proj g) o' o := by
    intro o o'
    have h := proj_mul_proj_apply_swap f g o o'
    rw [← hcomm] at h
    exact h
  -- every column of `P_1P_2` lies in `𝒮_1 ∩ 𝒮_2`, and is therefore constant
  have hcol : ∀ o₀ o o' : O, (proj f * proj g) o o₀ = (proj f * proj g) o' o₀ := by
    intro o₀
    refine eq_of_supportConnected f g hconn
      (z := fun o => (proj f * proj g) o o₀) ?_ ?_
    · exact fun a b hab => proj_mul_proj_apply_congr f g hab rfl
    · intro a b hab
      rw [hsymm a o₀, hsymm b o₀]
      exact proj_mul_proj_apply_congr f g rfl hab
  ext o o'
  rw [grandMeanProj_apply]
  have hn : (Fintype.card O : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_pos_iff.mpr ⟨o⟩).ne'
  -- the column through `o'` sums to one, by symmetry and the unit row sums
  have hsum : ∑ a : O, (proj f * proj g) a o' = 1 := by
    have hswap : ∀ a : O, (proj f * proj g) a o' = (proj f * proj g) o' a :=
      fun a => hsymm a o'
    simp only [hswap]
    exact sum_proj_mul_proj_row f g o'
  -- and it is constant, so each of its `n` entries is `1/n`
  have hconst : ∑ a : O, (proj f * proj g) a o'
      = (Fintype.card O : ℝ) * (proj f * proj g) o o' := by
    have hc : ∀ a : O, (proj f * proj g) a o' = (proj f * proj g) o o' :=
      fun a => hcol o' a o
    simp only [hc]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hconst] at hsum
  calc (proj f * proj g) o o'
      = (Fintype.card O : ℝ)⁻¹ * ((Fintype.card O : ℝ) * (proj f * proj g) o o') := by
        rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
    _ = (Fintype.card O : ℝ)⁻¹ * 1 := by rw [hsum]
    _ = (Fintype.card O : ℝ)⁻¹ := mul_one _

/-! ### The direction that does not -/

/-- If `n_{it} = T_iC_t/n` for every realized pair, then `P_1P_2 = P_0`. Connectedness is not
needed. -/
theorem proj_mul_proj_eq_grandMeanProj_of_proportional (f g : O → L)
    (hprop : ∀ i ∈ Set.range f, ∀ t ∈ Set.range g,
      (pairCount f g i t : ℝ)
        = (margCount f i : ℝ) * (margCount g t : ℝ) / (Fintype.card O : ℝ)) :
    proj f * proj g = grandMeanProj O :=
  (proj_mul_proj_eq_grandMeanProj_iff f g).mpr hprop

/-! ### The characterization -/

/-- **Theorem 2**, first claim. On a connected two-way support, `P_1P_2 = P_2P_1` if and only
if `n_{it} = T_iC_t/n` for every realized pair of categories. -/
theorem commute_iff_proportional (f g : O → L) (hconn : SupportConnected f g) :
    proj f * proj g = proj g * proj f ↔
      ∀ i ∈ Set.range f, ∀ t ∈ Set.range g,
        (pairCount f g i t : ℝ)
          = (margCount f i : ℝ) * (margCount g t : ℝ) / (Fintype.card O : ℝ) := by
  constructor
  · intro hcomm
    exact (proj_mul_proj_eq_grandMeanProj_iff f g).mp
      (proj_mul_proj_eq_grandMeanProj_of_commute f g hconn hcomm)
  · intro hprop
    have h1 : proj f * proj g = grandMeanProj O :=
      proj_mul_proj_eq_grandMeanProj_of_proportional f g hprop
    have hgm : (grandMeanProj O)ᵀ = grandMeanProj O := by
      ext o o'
      rfl
    have h2 : proj g * proj f = grandMeanProj O := by
      have h := congrArg Matrix.transpose h1
      rwa [Matrix.transpose_mul, transpose_proj, transpose_proj, hgm] at h
    rw [h1, h2]

/-- **Theorem 2**, first claim, when every category is realized. -/
theorem commute_iff_proportional_of_surjective {f g : O → L} (hconn : SupportConnected f g)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    proj f * proj g = proj g * proj f ↔
      ∀ i t : L, (pairCount f g i t : ℝ)
        = (margCount f i : ℝ) * (margCount g t : ℝ) / (Fintype.card O : ℝ) := by
  rw [commute_iff_proportional f g hconn]
  constructor
  · exact fun h i t => h i (Set.mem_range.mpr (hf i)) t (Set.mem_range.mpr (hg t))
  · exact fun h i _ t _ => h i t

/-! ### Proportionality forces a complete support -/

/-- **Theorem 2**, second claim. Proportionality implies `n_{it} > 0` for every realized pair,
so the support is complete. Connectedness is not needed. -/
theorem pairCount_pos_of_proportional (f g : O → L)
    (hprop : ∀ i ∈ Set.range f, ∀ t ∈ Set.range g,
      (pairCount f g i t : ℝ)
        = (margCount f i : ℝ) * (margCount g t : ℝ) / (Fintype.card O : ℝ)) :
    ∀ i ∈ Set.range f, ∀ t ∈ Set.range g, 0 < pairCount f g i t := by
  rintro i ⟨o, rfl⟩ t ⟨o', rfl⟩
  have hT : (0 : ℝ) < (margCount f (f o) : ℝ) := by exact_mod_cast margCount_pos f o
  have hC : (0 : ℝ) < (margCount g (g o') : ℝ) := by exact_mod_cast margCount_pos g o'
  have hn : (0 : ℝ) < (Fintype.card O : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨o⟩
  have hpos : (0 : ℝ) < (pairCount f g (f o) (g o') : ℝ) := by
    rw [hprop (f o) ⟨o, rfl⟩ (g o') ⟨o', rfl⟩]
    exact div_pos (mul_pos hT hC) hn
  exact_mod_cast hpos

/-- **Theorem 2**, second claim, when every category is realized. -/
theorem pairCount_pos_of_proportional_of_surjective {f g : O → L}
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hprop : ∀ i t : L, (pairCount f g i t : ℝ)
      = (margCount f i : ℝ) * (margCount g t : ℝ) / (Fintype.card O : ℝ)) :
    ∀ i t : L, 0 < pairCount f g i t := by
  intro i t
  exact pairCount_pos_of_proportional f g (fun i' _ t' _ => hprop i' t')
    i (Set.mem_range.mpr (hf i)) t (Set.mem_range.mpr (hg t))

/-! ### The `{0,1}` clause -/

/-- **Theorem 2**, last claim. If `n_{it} ∈ {0,1}` for every cell, proportionality holds if and
only if `n_{it} = 1` for every realized pair. Connectedness is not needed. -/
theorem proportional_iff_pairCount_eq_one (f g : O → L)
    (h01 : ∀ i ∈ Set.range f, ∀ t ∈ Set.range g, pairCount f g i t ≤ 1) :
    (∀ i ∈ Set.range f, ∀ t ∈ Set.range g,
        (pairCount f g i t : ℝ)
          = (margCount f i : ℝ) * (margCount g t : ℝ) / (Fintype.card O : ℝ)) ↔
      ∀ i ∈ Set.range f, ∀ t ∈ Set.range g, pairCount f g i t = 1 := by
  classical
  constructor
  · intro hprop i hi t ht
    exact le_antisymm (h01 i hi t ht) (pairCount_pos_of_proportional f g hprop i hi t ht)
  · intro hone i hi t ht
    -- `T_i = N_2` for every realized row category
    have hTi : ∀ i' ∈ Finset.univ.image f,
        margCount f i' = (Finset.univ.image g).card := by
      intro i' hi'
      have hrow : ∀ t' ∈ Finset.univ.image g, pairCount f g i' t' = 1 := fun t' ht' =>
        hone i' (mem_range_of_mem_univ_image f hi') t' (mem_range_of_mem_univ_image g ht')
      rw [margCount_eq_sum_pairCount f g i', Finset.sum_congr rfl hrow]
      simp
    -- `C_t = N_1` for every realized column category
    have hCt : ∀ t' ∈ Finset.univ.image g,
        margCount g t' = (Finset.univ.image f).card := by
      intro t' ht'
      have hcolumn : ∀ i' ∈ Finset.univ.image f, pairCount g f t' i' = 1 := by
        intro i' hi'
        rw [pairCount_comm f g i' t']
        exact hone i' (mem_range_of_mem_univ_image f hi') t'
          (mem_range_of_mem_univ_image g ht')
      rw [margCount_eq_sum_pairCount g f t', Finset.sum_congr rfl hcolumn]
      simp
    -- `n = N_1N_2`
    have hcard : Fintype.card O = (Finset.univ.image f).card * (Finset.univ.image g).card := by
      rw [card_eq_sum_margCount f, Finset.sum_congr rfl hTi, Finset.sum_const, smul_eq_mul]
    have hiF := mem_univ_image_of_mem_range f hi
    have htG := mem_univ_image_of_mem_range g ht
    have hN₁ : (0 : ℝ) < ((Finset.univ.image f).card : ℝ) := by
      have : 0 < (Finset.univ.image f).card := Finset.card_pos.mpr ⟨i, hiF⟩
      exact_mod_cast this
    have hN₂ : (0 : ℝ) < ((Finset.univ.image g).card : ℝ) := by
      have : 0 < (Finset.univ.image g).card := Finset.card_pos.mpr ⟨t, htG⟩
      exact_mod_cast this
    have hne : ((Finset.univ.image f).card : ℝ) * ((Finset.univ.image g).card : ℝ) ≠ 0 :=
      ne_of_gt (mul_pos hN₁ hN₂)
    rw [hone i hi t ht, hTi i hiF, hCt t htG, hcard]
    push_cast
    rw [eq_div_iff hne, one_mul, mul_comm]

/-- **Theorem 2**, last claim, when every category is realized. -/
theorem proportional_iff_pairCount_eq_one_of_surjective {f g : O → L}
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h01 : ∀ i t : L, pairCount f g i t ≤ 1) :
    (∀ i t : L, (pairCount f g i t : ℝ)
        = (margCount f i : ℝ) * (margCount g t : ℝ) / (Fintype.card O : ℝ)) ↔
      ∀ i t : L, pairCount f g i t = 1 := by
  have h := proportional_iff_pairCount_eq_one f g (fun i' _ t' _ => h01 i' t')
  constructor
  · intro hprop i t
    exact h.mp (fun i' _ t' _ => hprop i' t') i (Set.mem_range.mpr (hf i)) t
      (Set.mem_range.mpr (hg t))
  · intro hone i t
    exact h.mpr (fun i' _ t' _ => hone i' t') i (Set.mem_range.mpr (hf i)) t
      (Set.mem_range.mpr (hg t))

end Proportional

end Multiway
