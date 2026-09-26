import Multiway.InclusionExclusion
import Multiway.GroupCompute
import Multiway.Sqrt
import Multiway.CondFactor
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Structure of the sharing graph, and the exponent arithmetic of the variance floor

This file formalizes Lemma SM.B.11 of the paper (structure of the sharing graph and of the score
variance), all five clauses, and Proposition SM.D.3 (sufficient conditions under a variance
floor), all three parts. The two results share the maximal degree `D_n` (`maxDegree`) and the
sequence `δ_n := nD_n³/λ_min(Ω_n)²` (`deltaSeq`).

## Main results

* `condCov_eq_zero_of_not_linked`, `condExp_meat_eq_scoreVar`: clause (a), `Ω_{oo'} = 0` for
  `o ≁ o'` and `𝔼[𝓜̃_n ∣ 𝒟] = Ω_n`.
* `card_linkedPairs_le`, `card_linkedQuads_le`: clauses (b) and (c).
* `eigenvalues_le_of_graphSupported`, `eigenvalues_conj_le_of_graphSupported`: clause (d).
* `sharing_e`, `sharing_e_lambdaMin_of_graphSupported`: clause (e).
* `threeseq_a_of_design`, `threeseq_b_tendsto`, `regime3_of_clusterShock`,
  `condOmega_eq_clusterOmega`, `smul_one_le_condOmega`: Proposition SM.D.3 (a)–(c).

## Notation

* `c : D → O → L` assigns clusters; `Multiway.Linked c dims o o'` is `o ∼ o'`.
* `Xt : Matrix O K ℝ` is `X̃`, and `Xtᵀ * Om * Xt` is `Ω_n = X̃'ΩX̃`.
* `clusterOmega c dims sc ve` is `∑_j σ²_{c,j}Sh^{(j)} + diag(Var(ε_o ∣ 𝒟))`.
-/

namespace Multiway.Sharing

open Finset

variable {O D L : Type*}

/-! ### The sharing graph and its maximal degree `D_n` -/

section Graph

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
variable (c : D → O → L) (dims : Finset D)

/-- `{o' : o' ∼ o}`, the closed neighbourhood of `o` in the sharing graph. -/
def closedNbhd (o : O) : Finset O :=
  Finset.univ.filter (fun o' => Linked c dims o o')

/-- `{o' ≠ o : o' ∼ o}`, the open neighbourhood of `o`. -/
def openNbhd (o : O) : Finset O :=
  Finset.univ.filter (fun o' => o' ≠ o ∧ Linked c dims o o')

/-- `D_n := max{1, max_{o∈𝒪} #{o' ≠ o : o' ∼ o}}`, the maximal degree of the sharing graph,
with `D_n = 1` for an edgeless graph. -/
def maxDegree : ℕ :=
  max 1 (Finset.univ.sup fun o : O => (openNbhd c dims o).card)

omit [DecidableEq D] in
/-- `D_n ≥ 1`. -/
lemma one_le_maxDegree : 1 ≤ maxDegree c dims := le_max_left _ _

variable {c dims}

omit [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L] in
/-- `o ∼ o'` is symmetric. -/
lemma linked_symm {o o' : O} (h : Linked c dims o o') : Linked c dims o' o := by
  obtain ⟨j, hj, hcj⟩ := h
  exact ⟨j, hj, hcj.symm⟩

omit [DecidableEq O] [DecidableEq D] in
@[simp] lemma mem_closedNbhd {o o' : O} : o' ∈ closedNbhd c dims o ↔ Linked c dims o o' := by
  simp [closedNbhd]

omit [DecidableEq D] in
@[simp] lemma mem_openNbhd {o o' : O} :
    o' ∈ openNbhd c dims o ↔ o' ≠ o ∧ Linked c dims o o' := by
  simp [openNbhd]

variable (c dims)

omit [DecidableEq D] in
/-- Every open neighbourhood has at most `D_n` elements. -/
lemma card_openNbhd_le (o : O) : (openNbhd c dims o).card ≤ maxDegree c dims :=
  le_trans (Finset.le_sup (f := fun o : O => (openNbhd c dims o).card) (Finset.mem_univ o))
    (le_max_right _ _)

omit [DecidableEq D] in
/-- Each `o` has at most `D_n` neighbours, plus itself. -/
lemma card_closedNbhd_le (o : O) : (closedNbhd c dims o).card ≤ maxDegree c dims + 1 := by
  have hsub : closedNbhd c dims o ⊆ insert o (openNbhd c dims o) := by
    intro o' ho'
    rw [mem_closedNbhd] at ho'
    by_cases h : o' = o
    · subst h; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (mem_openNbhd.2 ⟨h, ho'⟩)
  calc (closedNbhd c dims o).card ≤ (insert o (openNbhd c dims o)).card :=
        Finset.card_le_card hsub
    _ ≤ (openNbhd c dims o).card + 1 := Finset.card_insert_le _ _
    _ ≤ maxDegree c dims + 1 := Nat.add_le_add_right (card_openNbhd_le c dims o) 1

omit [DecidableEq O] [DecidableEq D] in
/-- Counting a closed neighbourhood as a sum of indicators. -/
lemma sum_ite_closedNbhd (r : O) (k : ℕ) :
    (∑ o' : O, if Linked c dims r o' then k else 0) = (closedNbhd c dims r).card * k := by
  rw [← Finset.sum_filter]
  simp [closedNbhd]

end Graph

/-! ### Clause (b): the number of linked ordered pairs -/

section ClauseB

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
variable (c : D → O → L) (dims : Finset D)

/-- `{(o,o') ∈ 𝒪² : o ∼ o'}`. -/
def linkedPairs : Finset (O × O) :=
  Finset.univ.filter (fun p => Linked c dims p.1 p.2)

omit [DecidableEq D] in
/-- **Lemma SM.B.11(b).** `#{(o,o') ∈ 𝒪² : o ∼ o'} ≤ n(D_n+1)`. -/
theorem card_linkedPairs_le :
    (linkedPairs c dims).card ≤ Fintype.card O * (maxDegree c dims + 1) := by
  have hcard : (linkedPairs c dims).card = ∑ o : O, (closedNbhd c dims o).card := by
    rw [linkedPairs, Finset.card_filter, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun o _ => by rw [closedNbhd, Finset.card_filter]
  rw [hcard]
  calc ∑ o : O, (closedNbhd c dims o).card ≤ ∑ _o : O, (maxDegree c dims + 1) :=
        Finset.sum_le_sum fun o _ => card_closedNbhd_le c dims o
    _ = Fintype.card O * (maxDegree c dims + 1) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

end ClauseB

/-! ### Clause (c): the quadruple set `𝓛_n` -/

section ClauseC

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
variable (c : D → O → L) (dims : Finset D)

/-- The rooted three-chains: a vertex `q.1`, two of its neighbours `q.2.1` and `q.2.2.1`, and a
neighbour `q.2.2.2` of the latter. -/
def chainQuads : Finset (O × O × O × O) :=
  Finset.univ.filter (fun q =>
    Linked c dims q.1 q.2.1 ∧ Linked c dims q.1 q.2.2.1 ∧ Linked c dims q.2.2.1 q.2.2.2)

/-- `𝓛_n`: the quadruples `(o₁,o₂,o₃,o₄)` with `o₁ ∼ o₂`, `o₃ ∼ o₄`, and `o_a ∼ o_b` for some
`a ∈ {1,2}` and `b ∈ {3,4}`. -/
def linkedQuads : Finset (O × O × O × O) :=
  Finset.univ.filter (fun q =>
    Linked c dims q.1 q.2.1 ∧ Linked c dims q.2.2.1 q.2.2.2 ∧
      (Linked c dims q.1 q.2.2.1 ∨ Linked c dims q.1 q.2.2.2 ∨
        Linked c dims q.2.1 q.2.2.1 ∨ Linked c dims q.2.1 q.2.2.2))

omit [DecidableEq D] in
/-- There are at most `n(D_n+1)³` rooted three-chains. -/
theorem card_chainQuads_le :
    (chainQuads c dims).card ≤ Fintype.card O * (maxDegree c dims + 1) ^ 3 := by
  have hd : ∀ o : O, (closedNbhd c dims o).card ≤ maxDegree c dims + 1 :=
    card_closedNbhd_le c dims
  set d := maxDegree c dims + 1 with hdef
  -- the innermost neighbour choice
  have h1 : ∀ r a b : O,
      (∑ x : O, if Linked c dims r a ∧ Linked c dims r b ∧ Linked c dims b x then (1 : ℕ) else 0)
        ≤ (if Linked c dims r a ∧ Linked c dims r b then d else 0) := by
    intro a b x
    by_cases hab : Linked c dims a b ∧ Linked c dims a x
    · rw [ite_eq_left hab]
      have : ∀ y : O,
          (if Linked c dims a b ∧ Linked c dims a x ∧ Linked c dims x y then (1 : ℕ) else 0)
            = (if Linked c dims x y then (1 : ℕ) else 0) := by
        intro y
        by_cases hy : Linked c dims x y <;> simp [hab.1, hab.2, hy]
      rw [Finset.sum_congr rfl (fun y _ => this y), sum_ite_closedNbhd c dims x 1, mul_one]
      exact hd x
    · rw [ite_eq_right hab]
      refine le_of_eq (Finset.sum_eq_zero fun y _ => ite_eq_right ?_)
      intro hy
      exact hab ⟨hy.1, hy.2.1⟩
  -- the second neighbour choice
  have h2 : ∀ r a : O,
      (∑ b : O, if Linked c dims r a ∧ Linked c dims r b then d else 0)
        ≤ (if Linked c dims r a then d * d else 0) := by
    intro r a
    by_cases ha : Linked c dims r a
    · rw [ite_eq_left ha]
      have : ∀ b : O, (if Linked c dims r a ∧ Linked c dims r b then d else 0)
          = (if Linked c dims r b then d else 0) := by
        intro b; by_cases hb : Linked c dims r b <;> simp [ha, hb]
      rw [Finset.sum_congr rfl (fun b _ => this b), sum_ite_closedNbhd c dims r d]
      exact Nat.mul_le_mul_right d (hd r)
    · rw [ite_eq_right ha]
      refine le_of_eq (Finset.sum_eq_zero fun b _ => ite_eq_right ?_)
      intro hb; exact ha hb.1
  -- the root, and the first neighbour choice
  have h3 : ∀ r : O,
      (∑ a : O, ∑ b : O, ∑ x : O,
        if Linked c dims r a ∧ Linked c dims r b ∧ Linked c dims b x then (1 : ℕ) else 0)
        ≤ d * d * d := by
    intro r
    calc (∑ a : O, ∑ b : O, ∑ x : O,
            if Linked c dims r a ∧ Linked c dims r b ∧ Linked c dims b x then (1 : ℕ) else 0)
        ≤ ∑ a : O, ∑ b : O, (if Linked c dims r a ∧ Linked c dims r b then d else 0) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => h1 r a b
      _ ≤ ∑ a : O, (if Linked c dims r a then d * d else 0) :=
          Finset.sum_le_sum fun a _ => h2 r a
      _ = (closedNbhd c dims r).card * (d * d) := sum_ite_closedNbhd c dims r (d * d)
      _ ≤ d * (d * d) := Nat.mul_le_mul_right (d * d) (hd r)
      _ = d * d * d := by ring
  rw [chainQuads, Finset.card_filter]
  simp only [Fintype.sum_prod_type]
  calc (∑ r : O, ∑ a : O, ∑ b : O, ∑ x : O,
          if Linked c dims r a ∧ Linked c dims r b ∧ Linked c dims b x then (1 : ℕ) else 0)
      ≤ ∑ _r : O, d * d * d := Finset.sum_le_sum fun r _ => h3 r
    _ = Fintype.card O * d ^ 3 := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        ring

omit [DecidableEq D] in
/-- **Lemma SM.B.11(c).** `|𝓛_n| ≤ 4n(D_n+1)³`, by a union bound over the four choices of
`(a,b) ∈ {1,2}×{3,4}`, each a permutation of `chainQuads`. -/
theorem card_linkedQuads_le :
    (linkedQuads c dims).card ≤ 4 * (Fintype.card O * (maxDegree c dims + 1) ^ 3) := by
  classical
  set M := Fintype.card O * (maxDegree c dims + 1) ^ 3 with hM
  have hbase : (chainQuads c dims).card ≤ M := card_chainQuads_le c dims
  -- a rooted chain read along a coordinate permutation is still a rooted chain
  have hinj : ∀ (f : O × O × O × O → O × O × O × O) (S : Finset (O × O × O × O)),
      Function.Injective f → (∀ q ∈ S, f q ∈ chainQuads c dims) → S.card ≤ M := by
    intro f S hf hmem
    exact le_trans (Finset.card_le_card_of_injOn f hmem hf.injOn) hbase
  have hinj14 : Function.Injective
      (fun q : O × O × O × O => (q.1, q.2.1, q.2.2.2, q.2.2.1)) := by
    rintro ⟨a, b, x, y⟩ ⟨a', b', x', y'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    subst h1; subst h2; subst h3; subst h4; rfl
  have hinj23 : Function.Injective
      (fun q : O × O × O × O => (q.2.1, q.1, q.2.2.1, q.2.2.2)) := by
    rintro ⟨a, b, x, y⟩ ⟨a', b', x', y'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    subst h1; subst h2; subst h3; subst h4; rfl
  have hinj24 : Function.Injective
      (fun q : O × O × O × O => (q.2.1, q.1, q.2.2.2, q.2.2.1)) := by
    rintro ⟨a, b, x, y⟩ ⟨a', b', x', y'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    subst h1; subst h2; subst h3; subst h4; rfl
  -- the four blocks
  have h13 : (Finset.univ.filter (fun q : O × O × O × O =>
      (Linked c dims q.1 q.2.1 ∧ Linked c dims q.2.2.1 q.2.2.2) ∧
        Linked c dims q.1 q.2.2.1)).card ≤ M := by
    refine hinj id _ Function.injective_id ?_
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    simp only [chainQuads, Finset.mem_filter, Finset.mem_univ, true_and, id]
    exact ⟨hq.1.1, hq.2, hq.1.2⟩
  have h14 : (Finset.univ.filter (fun q : O × O × O × O =>
      (Linked c dims q.1 q.2.1 ∧ Linked c dims q.2.2.1 q.2.2.2) ∧
        Linked c dims q.1 q.2.2.2)).card ≤ M := by
    refine hinj _ _ hinj14 ?_
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    simp only [chainQuads, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hq.1.1, hq.2, linked_symm hq.1.2⟩
  have h23 : (Finset.univ.filter (fun q : O × O × O × O =>
      (Linked c dims q.1 q.2.1 ∧ Linked c dims q.2.2.1 q.2.2.2) ∧
        Linked c dims q.2.1 q.2.2.1)).card ≤ M := by
    refine hinj _ _ hinj23 ?_
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    simp only [chainQuads, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨linked_symm hq.1.1, hq.2, hq.1.2⟩
  have h24 : (Finset.univ.filter (fun q : O × O × O × O =>
      (Linked c dims q.1 q.2.1 ∧ Linked c dims q.2.2.1 q.2.2.2) ∧
        Linked c dims q.2.1 q.2.2.2)).card ≤ M := by
    refine hinj _ _ hinj24 ?_
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    simp only [chainQuads, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨linked_symm hq.1.1, hq.2, linked_symm hq.1.2⟩
  -- the union bound
  have hcover : linkedQuads c dims ⊆
      ((Finset.univ.filter (fun q : O × O × O × O =>
        (Linked c dims q.1 q.2.1 ∧ Linked c dims q.2.2.1 q.2.2.2) ∧
          Linked c dims q.1 q.2.2.1)) ∪
       (Finset.univ.filter (fun q : O × O × O × O =>
        (Linked c dims q.1 q.2.1 ∧ Linked c dims q.2.2.1 q.2.2.2) ∧
          Linked c dims q.1 q.2.2.2))) ∪
      ((Finset.univ.filter (fun q : O × O × O × O =>
        (Linked c dims q.1 q.2.1 ∧ Linked c dims q.2.2.1 q.2.2.2) ∧
          Linked c dims q.2.1 q.2.2.1)) ∪
       (Finset.univ.filter (fun q : O × O × O × O =>
        (Linked c dims q.1 q.2.1 ∧ Linked c dims q.2.2.1 q.2.2.2) ∧
          Linked c dims q.2.1 q.2.2.2))) := by
    intro q hq
    simp only [linkedQuads, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    obtain ⟨h12, h34, hd⟩ := hq
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hd with h | h | h | h
    · exact Or.inl (Or.inl ⟨⟨h12, h34⟩, h⟩)
    · exact Or.inl (Or.inr ⟨⟨h12, h34⟩, h⟩)
    · exact Or.inr (Or.inl ⟨⟨h12, h34⟩, h⟩)
    · exact Or.inr (Or.inr ⟨⟨h12, h34⟩, h⟩)
  calc (linkedQuads c dims).card ≤ _ := Finset.card_le_card hcover
    _ ≤ _ + _ := Finset.card_union_le _ _
    _ ≤ (M + M) + (M + M) := by
        refine Nat.add_le_add ?_ ?_
        · exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add h13 h14)
        · exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add h23 h24)
    _ = 4 * M := by ring

end ClauseC

/-! ### Sums over linked pairs

A kernel vanishing off the sharing graph may be summed over linked pairs alone. The vanishing
hypothesis is discharged for conditional covariances by `condCov_eq_zero_of_not_linked`. -/

section Support

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
variable (c : D → O → L) (dims : Finset D)

omit [DecidableEq O] [DecidableEq D] in
/-- A real kernel vanishing off the sharing graph may be summed over linked pairs alone. -/
theorem sum_eq_sum_over_linkedPairs (Om w : O → O → ℝ)
    (hz : ∀ o o', ¬ Linked c dims o o' → Om o o' = 0) :
    ∑ o : O, ∑ o' : O, w o o' * Om o o'
      = ∑ p ∈ linkedPairs c dims, w p.1 p.2 * Om p.1 p.2 := by
  rw [linkedPairs, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => ?_
  by_cases h : Linked c dims o o'
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, hz o o' h, mul_zero]

end Support

/-! ### Clause (d), first bound: Gershgorin on a graph-supported matrix -/

section ClauseD

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
variable (c : D → O → L) (dims : Finset D)

omit [DecidableEq D] in
/-- **Lemma SM.B.11(d), first bound**, for an arbitrary eigenvalue of `A` as an operator on
`O → ℝ`: if `|A_{oo'}| ≤ κ` and `A` vanishes off the sharing graph, every eigenvalue is at most
`κ(D_n+1)`. The proof is Gershgorin's circle theorem (`eigenvalue_mem_ball`); symmetry of `A` is
not needed. -/
theorem eigenvalue_le_of_graphSupported (A : Matrix O O ℝ) (κ : ℝ)
    (hb : ∀ o o', |A o o'| ≤ κ)
    (hz : ∀ o o', ¬ Linked c dims o o' → A o o' = 0)
    {μ : ℝ} (hμ : Module.End.HasEigenvalue (Matrix.toLin' A) μ) :
    μ ≤ κ * ((maxDegree c dims : ℝ) + 1) := by
  classical
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hμ
  rw [Metric.mem_closedBall, Real.dist_eq] at hk
  have hκ : 0 ≤ κ := le_trans (abs_nonneg _) (hb k k)
  -- only the linked entries of row `k` survive
  have hsplit : ∑ j ∈ Finset.univ.erase k, ‖A k j‖
      = ∑ j ∈ (Finset.univ.erase k).filter (fun j => Linked c dims k j), ‖A k j‖ := by
    refine (Finset.sum_filter_of_ne ?_).symm
    intro j _ hne
    by_contra hcon
    exact hne (by rw [hz k j hcon, norm_zero])
  have hcard : ((Finset.univ.erase k).filter (fun j => Linked c dims k j)).card
      ≤ maxDegree c dims := by
    refine le_trans (Finset.card_le_card ?_) (card_openNbhd_le c dims k)
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hj
    exact mem_openNbhd.2 ⟨hj.1, hj.2⟩
  have hrow : ∑ j ∈ Finset.univ.erase k, ‖A k j‖ ≤ κ * (maxDegree c dims : ℝ) := by
    rw [hsplit]
    calc ∑ j ∈ (Finset.univ.erase k).filter (fun j => Linked c dims k j), ‖A k j‖
        ≤ ∑ _j ∈ (Finset.univ.erase k).filter (fun j => Linked c dims k j), κ :=
          Finset.sum_le_sum fun j _ => by rw [Real.norm_eq_abs]; exact hb k j
      _ = (((Finset.univ.erase k).filter (fun j => Linked c dims k j)).card : ℝ) * κ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (maxDegree c dims : ℝ) * κ := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hκ
      _ = κ * (maxDegree c dims : ℝ) := mul_comm _ _
  have hdiag : A k k ≤ κ := le_trans (le_abs_self _) (hb k k)
  have habs := abs_le.mp hk
  nlinarith [habs.2, hrow, hdiag]

omit [DecidableEq D] in
/-- **Lemma SM.B.11(d), first bound**: every eigenvalue of the symmetric matrix `A` is at most
`κ(D_n+1)`. -/
theorem eigenvalues_le_of_graphSupported {A : Matrix O O ℝ} (hA : A.IsHermitian) (κ : ℝ)
    (hb : ∀ o o', |A o o'| ≤ κ)
    (hz : ∀ o o', ¬ Linked c dims o o' → A o o' = 0) (i : O) :
    hA.eigenvalues i ≤ κ * ((maxDegree c dims : ℝ) + 1) := by
  refine eigenvalue_le_of_graphSupported c dims A κ hb hz ?_
  refine Module.End.hasEigenvalue_of_hasEigenvector
    (x := (⇑(hA.eigenvectorBasis i) : O → ℝ)) ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact hA.mulVec_eigenvectorBasis i
  · exact Multiway.eigenvectorBasis_ne_zero hA i

end ClauseD

/-! ### The smallest eigenvalue `λ_min` -/

section LambdaMin

open Matrix

variable {K : Type*} [Fintype K] [DecidableEq K] [Nonempty K]

/-- `λ_min(A)`, the smallest eigenvalue of a symmetric matrix, as a `Finset.inf'` over a
nonempty finite index type, so that the minimum is attained. -/
noncomputable def lambdaMin {A : Matrix K K ℝ} (hA : A.IsHermitian) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty hA.eigenvalues

/-- `lambdaMin` unfolded. -/
theorem lambdaMin_def {A : Matrix K K ℝ} (hA : A.IsHermitian) :
    lambdaMin hA = Finset.univ.inf' Finset.univ_nonempty hA.eigenvalues := rfl

/-- `λ_min(A) ≤ λ_i(A)` at every index. -/
theorem lambdaMin_le {A : Matrix K K ℝ} (hA : A.IsHermitian) (i : K) :
    lambdaMin hA ≤ hA.eigenvalues i := by
  rw [lambdaMin_def, Finset.inf'_le_iff]
  exact ⟨i, Finset.mem_univ i, le_rfl⟩

/-- The minimum is attained at some index. -/
theorem exists_eigenvalues_eq_lambdaMin {A : Matrix K K ℝ} (hA : A.IsHermitian) :
    ∃ i : K, hA.eigenvalues i = lambdaMin hA := by
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_inf' (H := (Finset.univ_nonempty : (Finset.univ : Finset K).Nonempty))
      hA.eigenvalues
  exact ⟨i, by rw [lambdaMin_def]; exact hi.symm⟩

/-- `Ω_n ≻ 0` gives `λ_min(Ω_n) > 0`. -/
theorem lambdaMin_pos {A : Matrix K K ℝ} (hA : A.PosDef) : 0 < lambdaMin hA.1 := by
  rw [lambdaMin_def, Finset.lt_inf'_iff]
  exact fun i _ => hA.eigenvalues_pos i

end LambdaMin

/-! ### Clause (e): the arithmetic of `δ_n` -/

section ClauseE

/-- `δ_n := nD_n³/λ_min(Ω_n)²`, the accumulation ratio. -/
noncomputable def deltaSeq (nR Dn lmin : ℝ) : ℝ := nR * Dn ^ 3 / lmin ^ 2

/-- **Lemma SM.B.11(e)**, as arithmetic on real numbers: given the second bound of clause (d)
as the hypothesis `hd` and `D_n ≥ 1`, `D_n²/λ_min(Ω_n) ≤ 2B²C^{1/2}δ_n`. See
`sharing_e_of_graphSupported` for the version with `hd` discharged. -/
theorem sharing_e {B Csqrt nR Dn lmin : ℝ} (hB : 0 < B) (hC : 0 < Csqrt)
    (hD : 1 ≤ Dn) (hlmin : 0 < lmin)
    (hd : lmin ≤ B ^ 2 * Csqrt * nR * (Dn + 1)) :
    Dn ^ 2 / lmin ≤ 2 * B ^ 2 * Csqrt * deltaSeq nR Dn lmin := by
  have hDpos : (0 : ℝ) < Dn := lt_of_lt_of_le zero_lt_one hD
  have hfac : 0 < B ^ 2 * Csqrt * (Dn + 1) := by positivity
  have hn : 0 < nR := by
    rcases le_or_gt nR 0 with h | h
    · exfalso
      have : B ^ 2 * Csqrt * nR * (Dn + 1) ≤ 0 := by nlinarith
      linarith
    · exact h
  -- `D_n ≥ 1` turns `D_n + 1` into `2D_n`
  have hd2 : lmin ≤ 2 * B ^ 2 * Csqrt * nR * Dn := by nlinarith [hd, hD, hn.le]
  have hmul := mul_le_mul_of_nonneg_right hd2 (by positivity : (0 : ℝ) ≤ Dn ^ 2 * lmin)
  have key : Dn ^ 2 / lmin ≤ (2 * B ^ 2 * Csqrt * nR * Dn ^ 3) / lmin ^ 2 := by
    rw [div_le_div_iff₀ hlmin (by positivity)]
    nlinarith [hmul]
  calc Dn ^ 2 / lmin ≤ (2 * B ^ 2 * Csqrt * nR * Dn ^ 3) / lmin ^ 2 := key
    _ = 2 * B ^ 2 * Csqrt * deltaSeq nR Dn lmin := by
        rw [deltaSeq]; ring

end ClauseE

/-! ### Proposition SM.D.3(b): exponent arithmetic on the variance floor -/

section ThreeSeq

open Filter

/-- **Proposition SM.D.3(b), first step.** From `Ḡ_n/2 ≤ D_n` and `δ_n ≤ K Ḡ_n³/n`,
`(n/D_n)^εδ_n ≤ 2^ε K Ḡ_n^{3-ε}/n^{1-ε}`. -/
theorem threeseq_b_transfer {ε K nR G Dn δ : ℝ}
    (hε : 0 ≤ ε) (hn : 0 < nR) (hG : 0 < G) (hD : 0 < Dn)
    (hGD : G / 2 ≤ Dn) (hδ0 : 0 ≤ δ) (hδ : δ ≤ K * G ^ (3 : ℕ) / nR) :
    (nR / Dn) ^ ε * δ ≤ 2 ^ ε * K * (G ^ (3 - ε) / nR ^ (1 - ε)) := by
  have hstep : (nR / Dn) ^ ε ≤ (2 * nR / G) ^ ε := by
    refine Real.rpow_le_rpow (by positivity) ?_ hε
    rw [div_le_div_iff₀ hD hG]
    nlinarith [hn.le, hG.le]
  have hpos : (0 : ℝ) ≤ (2 * nR / G) ^ ε := Real.rpow_nonneg (by positivity) ε
  have hkey : (2 * nR / G) ^ ε = 2 ^ ε * nR ^ ε / G ^ ε := by
    rw [Real.div_rpow (by positivity) hG.le, Real.mul_rpow (by norm_num) hn.le]
  have hG3 : G ^ (3 : ℕ) = G ^ (3 : ℝ) := by
    rw [← Real.rpow_natCast G 3]; norm_num
  have hGsub : G ^ (3 - ε) = G ^ (3 : ℝ) / G ^ ε := Real.rpow_sub hG 3 ε
  have hnsub : nR ^ (1 - ε) = nR ^ (1 : ℝ) / nR ^ ε := Real.rpow_sub hn 1 ε
  have hGe : (0 : ℝ) < G ^ ε := Real.rpow_pos_of_pos hG ε
  have hne : (0 : ℝ) < nR ^ ε := Real.rpow_pos_of_pos hn ε
  calc (nR / Dn) ^ ε * δ ≤ (2 * nR / G) ^ ε * δ := mul_le_mul_of_nonneg_right hstep hδ0
    _ ≤ (2 * nR / G) ^ ε * (K * G ^ (3 : ℕ) / nR) := mul_le_mul_of_nonneg_left hδ hpos
    _ = 2 ^ ε * K * (G ^ (3 - ε) / nR ^ (1 - ε)) := by
        rw [hkey, hGsub, hnsub, hG3, Real.rpow_one]
        field_simp

/-- **Proposition SM.D.3(b), second step.** If `Ḡ_n ≤ Cn^{1/3-η}`, then
`Ḡ_n^{3-ε}/n^{1-ε} ≤ C^{3-ε}n^{-3η+ε(2/3+η)}`. -/
theorem threeseq_b_exponent {ε η C nR G : ℝ} (hC : 0 ≤ C) (hε3 : ε ≤ 3)
    (hn : 0 < nR) (hG : 0 < G) (hGn : G ≤ C * nR ^ (1 / 3 - η)) :
    G ^ (3 - ε) / nR ^ (1 - ε) ≤ C ^ (3 - ε) * nR ^ (-(3 * η) + ε * (2 / 3 + η)) := by
  have hexp : (0 : ℝ) ≤ 3 - ε := by linarith
  have hpow : G ^ (3 - ε) ≤ (C * nR ^ (1 / 3 - η)) ^ (3 - ε) :=
    Real.rpow_le_rpow hG.le hGn hexp
  have hsplit : (C * nR ^ (1 / 3 - η)) ^ (3 - ε)
      = C ^ (3 - ε) * nR ^ ((1 / 3 - η) * (3 - ε)) := by
    rw [Real.mul_rpow hC (Real.rpow_nonneg hn.le _), ← Real.rpow_mul hn.le]
  have hdiv : nR ^ ((1 / 3 - η) * (3 - ε)) / nR ^ (1 - ε)
      = nR ^ (-(3 * η) + ε * (2 / 3 + η)) := by
    rw [← Real.rpow_sub hn]
    congr 1
    ring
  have hnpos : (0 : ℝ) < nR ^ (1 - ε) := Real.rpow_pos_of_pos hn _
  calc G ^ (3 - ε) / nR ^ (1 - ε)
      ≤ (C * nR ^ (1 / 3 - η)) ^ (3 - ε) / nR ^ (1 - ε) :=
        div_le_div_of_nonneg_right hpow hnpos.le
    _ = C ^ (3 - ε) * (nR ^ ((1 / 3 - η) * (3 - ε)) / nR ^ (1 - ε)) := by
        rw [hsplit]; ring
    _ = C ^ (3 - ε) * nR ^ (-(3 * η) + ε * (2 / 3 + η)) := by rw [hdiv]

/-- The same bound with the constant `C³`, which requires `1 ≤ C`. -/
theorem threeseq_b_exponent_le_cube {ε η C nR G : ℝ} (hC : 1 ≤ C) (hε : 0 ≤ ε) (hε3 : ε ≤ 3)
    (hn : 0 < nR) (hG : 0 < G) (hGn : G ≤ C * nR ^ (1 / 3 - η)) :
    G ^ (3 - ε) / nR ^ (1 - ε) ≤ C ^ (3 : ℕ) * nR ^ (-(3 * η) + ε * (2 / 3 + η)) := by
  have h := threeseq_b_exponent (by linarith : (0 : ℝ) ≤ C) hε3 hn hG hGn
  have hcube : C ^ (3 - ε) ≤ C ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast C 3]
    exact Real.rpow_le_rpow_of_exponent_le hC (by push_cast; linarith)
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_right hcube (Real.rpow_nonneg hn.le _)

/-- **Proposition SM.D.3(b), the limit.** `n^{-3η+ε(2/3+η)} → 0` for `ε < 3η/(2/3+η)`. -/
theorem threeseq_b_tendsto {ε η : ℝ} (hη : 0 < η)
    (hlt : ε < 3 * η / (2 / 3 + η)) :
    Tendsto (fun x : ℝ => x ^ (-(3 * η) + ε * (2 / 3 + η))) atTop (nhds 0) := by
  have hpos : (0 : ℝ) < 2 / 3 + η := by linarith
  have h1 : ε * (2 / 3 + η) < 3 * η := by
    rw [lt_div_iff₀ hpos] at hlt
    exact hlt
  have hneg : (0 : ℝ) < -(-(3 * η) + ε * (2 / 3 + η)) := by linarith
  simpa using tendsto_rpow_neg_atTop hneg

/-- **Proposition SM.D.3(b)**, the two steps combined: `(n/D_n)^εδ_n` is bounded by a constant
times a negative power of `n`. -/
theorem threeseq_b {ε η C K nR G Dn δ : ℝ}
    (hε : 0 ≤ ε) (hε3 : ε ≤ 3) (hK : 0 ≤ K) (hC : 1 ≤ C)
    (hn : 0 < nR) (hG : 0 < G) (hD : 0 < Dn) (hGD : G / 2 ≤ Dn)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ K * G ^ (3 : ℕ) / nR)
    (hGn : G ≤ C * nR ^ (1 / 3 - η)) :
    (nR / Dn) ^ ε * δ
      ≤ 2 ^ ε * K * (C ^ (3 : ℕ) * nR ^ (-(3 * η) + ε * (2 / 3 + η))) := by
  refine (threeseq_b_transfer hε hn hG hD hGD hδ0 hδ).trans ?_
  refine mul_le_mul_of_nonneg_left
    (threeseq_b_exponent_le_cube hC hε hε3 hn hG hGn) ?_
  positivity

end ThreeSeq

/-! ### Clause (d), second bound: the rectangular Loewner conjugation

The bound `λ_max(Ω_n) ≤ C^{1/2}(D_n+1)nB²` is proved in the Loewner order: `Ω ⪯ C^{1/2}(D_n+1)I`
is conjugated by `X̃` with `Multiway.mul_mul_transpose_le` and combined with `X̃'X̃ ⪯ nB²I`. -/

section ClauseD2

open scoped MatrixOrder
open Matrix

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
variable (c : D → O → L) (dims : Finset D)
variable {K : Type*} [Fintype K] [DecidableEq K]


omit [DecidableEq D] in
/-- A weight `(x r)²` summed over the closed neighbourhood of `r` is at most `(D_n+1)(x r)²`. -/
theorem sum_ite_linked_sq_le (x : O → ℝ) (r : O) :
    (∑ _o' : O, (if Linked c dims r _o' then (x r) ^ 2 else 0))
      ≤ ((maxDegree c dims : ℝ) + 1) * (x r) ^ 2 := by
  have e : (∑ _o' : O, (if Linked c dims r _o' then (x r) ^ 2 else 0))
      = ((closedNbhd c dims r).card : ℝ) * (x r) ^ 2 := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rfl
  rw [e]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  exact_mod_cast card_closedNbhd_le c dims r

omit [DecidableEq D] in
/-- **Lemma SM.B.11(d), first bound, in Loewner form**: a symmetric kernel bounded in absolute
value by `κ ≥ 0` and vanishing off the sharing graph satisfies `A ⪯ κ(D_n+1)I`. The proof bounds
`|x_o A_{oo'} x_{o'}| ≤ κ(x_o² + x_{o'}²)/2` and sums over linked pairs. -/
theorem le_smul_one_of_graphSupported {A : Matrix O O ℝ} (hA : A.IsHermitian) {κ : ℝ}
    (hκ : 0 ≤ κ) (hb : ∀ o o', |A o o'| ≤ κ)
    (hz : ∀ o o', ¬ Linked c dims o o' → A o o' = 0) :
    A ≤ (κ * ((maxDegree c dims : ℝ) + 1)) • (1 : Matrix O O ℝ) := by
  have hHerm : ((κ * ((maxDegree c dims : ℝ) + 1)) • (1 : Matrix O O ℝ) - A).IsHermitian := by
    have h1 : ((κ * ((maxDegree c dims : ℝ) + 1)) • (1 : Matrix O O ℝ)).IsHermitian := by
      simp [Matrix.IsHermitian]
    exact h1.sub hA
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm fun x => ?_
  -- the quadratic form of `A`, pair by pair
  have hlhs : x ⬝ᵥ (A *ᵥ x) = ∑ o : O, ∑ o' : O, x o * (A o o' * x o') := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  have hterm : ∀ o o' : O, x o * (A o o' * x o')
      ≤ (if Linked c dims o o' then κ / 2 * ((x o) ^ 2 + (x o') ^ 2) else 0) := by
    intro o o'
    by_cases h : Linked c dims o o'
    · rw [ite_eq_left h]
      have h1 : x o * (A o o' * x o') ≤ |x o * (A o o' * x o')| := le_abs_self _
      have h2 : |x o * (A o o' * x o')| = |x o| * (|A o o'| * |x o'|) := by
        rw [abs_mul, abs_mul]
      have h3 : |x o| * (|A o o'| * |x o'|) ≤ |x o| * (κ * |x o'|) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hb o o') (abs_nonneg _)) (abs_nonneg _)
      have h4 : |x o| * (κ * |x o'|) ≤ κ / 2 * ((x o) ^ 2 + (x o') ^ 2) := by
        rw [← sq_abs (x o), ← sq_abs (x o')]
        nlinarith [mul_nonneg hκ (sq_nonneg (|x o| - |x o'|))]
      linarith
    · rw [ite_eq_right h, hz o o' h]
      simp
  -- the two halves of the symmetric split, each counted by the closed neighbourhoods
  have hsplit : ∀ o o' : O,
      (if Linked c dims o o' then κ / 2 * ((x o) ^ 2 + (x o') ^ 2) else 0)
        = κ / 2 * ((if Linked c dims o o' then (x o) ^ 2 else 0)
            + (if Linked c dims o o' then (x o') ^ 2 else 0)) := by
    intro o o'
    by_cases h : Linked c dims o o' <;> simp [h]
  have hS1 : (∑ o : O, ∑ _o' : O, (if Linked c dims o _o' then (x o) ^ 2 else 0))
      ≤ ((maxDegree c dims : ℝ) + 1) * ∑ o : O, (x o) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun o _ => sum_ite_linked_sq_le c dims x o
  have hS2 : (∑ o : O, ∑ o' : O, (if Linked c dims o o' then (x o') ^ 2 else 0))
      ≤ ((maxDegree c dims : ℝ) + 1) * ∑ o : O, (x o) ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    have e : (∑ o : O, (if Linked c dims o r then (x r) ^ 2 else 0))
        = ∑ _o : O, (if Linked c dims r _o then (x r) ^ 2 else 0) := by
      refine Finset.sum_congr rfl fun o _ => ?_
      by_cases h : Linked c dims r o
      · rw [ite_eq_left h, ite_eq_left (linked_symm h)]
      · rw [ite_eq_right h, ite_eq_right (fun hc => h (linked_symm hc))]
    rw [e]
    exact sum_ite_linked_sq_le c dims x r
  have hcomb : (∑ o : O, ∑ o' : O, κ / 2 * ((if Linked c dims o o' then (x o) ^ 2 else 0)
        + (if Linked c dims o o' then (x o') ^ 2 else 0)))
      = κ / 2 * (∑ o : O, ∑ o' : O, (if Linked c dims o o' then (x o) ^ 2 else 0))
        + κ / 2 * (∑ o : O, ∑ o' : O, (if Linked c dims o o' then (x o') ^ 2 else 0)) := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hxx : x ⬝ᵥ x = ∑ o : O, (x o) ^ 2 := by
    simp [dotProduct, sq]
  have hquad : x ⬝ᵥ (A *ᵥ x)
      ≤ κ * ((maxDegree c dims : ℝ) + 1) * (x ⬝ᵥ x) := by
    rw [hlhs, hxx]
    calc (∑ o : O, ∑ o' : O, x o * (A o o' * x o'))
        ≤ ∑ o : O, ∑ o' : O,
            (if Linked c dims o o' then κ / 2 * ((x o) ^ 2 + (x o') ^ 2) else 0) :=
          Finset.sum_le_sum fun o _ => Finset.sum_le_sum fun o' _ => hterm o o'
      _ = ∑ o : O, ∑ o' : O, κ / 2 * ((if Linked c dims o o' then (x o) ^ 2 else 0)
            + (if Linked c dims o o' then (x o') ^ 2 else 0)) :=
          Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => hsplit o o'
      _ = κ / 2 * (∑ o : O, ∑ o' : O, (if Linked c dims o o' then (x o) ^ 2 else 0))
            + κ / 2 * (∑ o : O, ∑ o' : O, (if Linked c dims o o' then (x o') ^ 2 else 0)) :=
          hcomb
      _ ≤ κ * ((maxDegree c dims : ℝ) + 1) * ∑ o : O, (x o) ^ 2 := by
          have hκ2 : (0 : ℝ) ≤ κ / 2 := by linarith
          nlinarith [mul_le_mul_of_nonneg_left hS1 hκ2, mul_le_mul_of_nonneg_left hS2 hκ2]
  have he : star x ⬝ᵥ (((κ * ((maxDegree c dims : ℝ) + 1)) • (1 : Matrix O O ℝ) - A) *ᵥ x)
      = κ * ((maxDegree c dims : ℝ) + 1) * (x ⬝ᵥ x) - x ⬝ᵥ (A *ᵥ x) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul, star_trivial]
  rw [he]
  linarith


omit [DecidableEq O] in
/-- If every regressor vector has squared length at most `B²`, then `X̃'X̃ ⪯ nB²I`, by
Cauchy–Schwarz observation by observation. -/
theorem transpose_mul_self_le_smul_one {Xt : Matrix O K ℝ} {B2 : ℝ}
    (hB : ∀ o : O, ∑ k : K, (Xt o k) ^ 2 ≤ B2) :
    Xtᵀ * Xt ≤ ((Fintype.card O : ℝ) * B2) • (1 : Matrix K K ℝ) := by
  have hXh : Xtᴴ = Xtᵀ := Matrix.conjTranspose_eq_transpose_of_trivial Xt
  have hHerm : (((Fintype.card O : ℝ) * B2) • (1 : Matrix K K ℝ) - Xtᵀ * Xt).IsHermitian := by
    have h1 : ((((Fintype.card O : ℝ) * B2)) • (1 : Matrix K K ℝ)).IsHermitian := by
      simp [Matrix.IsHermitian]
    have h2 : (Xtᵀ * Xt).IsHermitian := by
      rw [← hXh]
      exact Matrix.isHermitian_conjTranspose_mul_self Xt
    exact h1.sub h2
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm fun v => ?_
  have hvv : v ⬝ᵥ v = ∑ k : K, (v k) ^ 2 := by simp [dotProduct, sq]
  have hvv0 : (0 : ℝ) ≤ v ⬝ᵥ v := by
    rw [hvv]; exact Finset.sum_nonneg fun k _ => sq_nonneg _
  have hterm : ∀ o : O, (Xt *ᵥ v) o * (Xt *ᵥ v) o ≤ B2 * (v ⬝ᵥ v) := by
    intro o
    have hcs : ((Xt *ᵥ v) o) ^ 2 ≤ (∑ k : K, (Xt o k) ^ 2) * (∑ k : K, (v k) ^ 2) := by
      have hmv : (Xt *ᵥ v) o = ∑ k : K, Xt o k * v k := rfl
      rw [hmv]
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hmono : (∑ k : K, (Xt o k) ^ 2) * (∑ k : K, (v k) ^ 2) ≤ B2 * (∑ k : K, (v k) ^ 2) :=
      mul_le_mul_of_nonneg_right (hB o) (by rw [← hvv]; exact hvv0)
    rw [hvv, ← sq]
    linarith
  have hq : v ⬝ᵥ ((Xtᵀ * Xt) *ᵥ v) ≤ ((Fintype.card O : ℝ) * B2) * (v ⬝ᵥ v) := by
    rw [dotProduct_transpose_mul_self_rect]
    calc (Xt *ᵥ v) ⬝ᵥ (Xt *ᵥ v) = ∑ o : O, (Xt *ᵥ v) o * (Xt *ᵥ v) o := rfl
      _ ≤ ∑ _o : O, B2 * (v ⬝ᵥ v) := Finset.sum_le_sum fun o _ => hterm o
      _ = ((Fintype.card O : ℝ) * B2) * (v ⬝ᵥ v) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have he : star v ⬝ᵥ ((((Fintype.card O : ℝ) * B2) • (1 : Matrix K K ℝ) - Xtᵀ * Xt) *ᵥ v)
      = ((Fintype.card O : ℝ) * B2) * (v ⬝ᵥ v) - v ⬝ᵥ ((Xtᵀ * Xt) *ᵥ v) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul, star_trivial]
  rw [he]
  linarith

omit [DecidableEq D] in
/-- **Lemma SM.B.11(d), second bound, in Loewner form**: `Ω_n = X̃'ΩX̃ ⪯ B²C^{1/2}n(D_n+1)I`. -/
theorem conj_le_smul_one_of_graphSupported {Om : Matrix O O ℝ} (hOm : Om.IsHermitian)
    {κ : ℝ} (hκ : 0 ≤ κ) (hb : ∀ o o', |Om o o'| ≤ κ)
    (hz : ∀ o o', ¬ Linked c dims o o' → Om o o' = 0)
    {Xt : Matrix O K ℝ} {B2 : ℝ} (hB : ∀ o : O, ∑ k : K, (Xt o k) ^ 2 ≤ B2) :
    Xtᵀ * Om * Xt
      ≤ (κ * ((maxDegree c dims : ℝ) + 1) * ((Fintype.card O : ℝ) * B2))
          • (1 : Matrix K K ℝ) := by
  have h1 : Om ≤ (κ * ((maxDegree c dims : ℝ) + 1)) • (1 : Matrix O O ℝ) :=
    le_smul_one_of_graphSupported c dims hOm hκ hb hz
  have h2 := Multiway.mul_mul_transpose_le h1 Xtᵀ
  rw [Matrix.transpose_transpose] at h2
  have e : Xtᵀ * ((κ * ((maxDegree c dims : ℝ) + 1)) • (1 : Matrix O O ℝ)) * Xt
      = (κ * ((maxDegree c dims : ℝ) + 1)) • (Xtᵀ * Xt) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  rw [e] at h2
  have hκd : (0 : ℝ) ≤ κ * ((maxDegree c dims : ℝ) + 1) := by positivity
  have h3 := loewner_smul_le_smul (n := K) hκd (transpose_mul_self_le_smul_one hB)
  have e2 : (κ * ((maxDegree c dims : ℝ) + 1)) • (((Fintype.card O : ℝ) * B2)
        • (1 : Matrix K K ℝ))
      = (κ * ((maxDegree c dims : ℝ) + 1) * ((Fintype.card O : ℝ) * B2))
          • (1 : Matrix K K ℝ) := by
    rw [smul_smul]
  rw [e2] at h3
  exact le_trans h2 h3

omit [DecidableEq D] in
/-- **Lemma SM.B.11(d), second bound**: every eigenvalue of `Ω_n` is at most
`B²C^{1/2}n(D_n+1)`. The symmetry of `Ω_n` is supplied as `hOn`. -/
theorem eigenvalues_conj_le_of_graphSupported {Om : Matrix O O ℝ} (hOm : Om.IsHermitian)
    {κ : ℝ} (hκ : 0 ≤ κ) (hb : ∀ o o', |Om o o'| ≤ κ)
    (hz : ∀ o o', ¬ Linked c dims o o' → Om o o' = 0)
    {Xt : Matrix O K ℝ} {B2 : ℝ} (hB : ∀ o : O, ∑ k : K, (Xt o k) ^ 2 ≤ B2)
    (hOn : (Xtᵀ * Om * Xt).IsHermitian) (i : K) :
    hOn.eigenvalues i
      ≤ κ * ((maxDegree c dims : ℝ) + 1) * ((Fintype.card O : ℝ) * B2) :=
  Multiway.eigenvalues_le_of_le_smul_one hOn
    (conj_le_smul_one_of_graphSupported c dims hOm hκ hb hz hB) i

omit [DecidableEq D] in
/-- **Lemma SM.B.11(e)** for an actual `Ω` and `X̃`, at every eigenvalue of `Ω_n = X̃'ΩX̃`, with
the second bound of clause (d) discharged. -/
theorem sharing_e_of_graphSupported {Om : Matrix O O ℝ} (hOm : Om.IsHermitian)
    {κ : ℝ} (hκ : 0 < κ) (hb : ∀ o o', |Om o o'| ≤ κ)
    (hz : ∀ o o', ¬ Linked c dims o o' → Om o o' = 0)
    {Xt : Matrix O K ℝ} {B : ℝ} (hBpos : 0 < B)
    (hB : ∀ o : O, ∑ k : K, (Xt o k) ^ 2 ≤ B ^ 2)
    (hOn : (Xtᵀ * Om * Xt).IsHermitian) (i : K) (hpos : 0 < hOn.eigenvalues i) :
    (maxDegree c dims : ℝ) ^ 2 / hOn.eigenvalues i
      ≤ 2 * B ^ 2 * κ *
          deltaSeq (Fintype.card O : ℝ) (maxDegree c dims : ℝ) (hOn.eigenvalues i) := by
  refine sharing_e hBpos hκ ?_ hpos ?_
  · exact_mod_cast one_le_maxDegree c dims
  · have h := eigenvalues_conj_le_of_graphSupported c dims hOm hκ.le hb hz hB hOn i
    have e : κ * ((maxDegree c dims : ℝ) + 1) * ((Fintype.card O : ℝ) * B ^ 2)
        = B ^ 2 * κ * (Fintype.card O : ℝ) * ((maxDegree c dims : ℝ) + 1) := by ring
    rwa [e] at h

omit [DecidableEq D] in
/-- `λ_min(Ω_n) ≤ λ_max(Ω_n) ≤ B²C^{1/2}n(D_n+1)`. -/
theorem lambdaMin_conj_le_of_graphSupported [Nonempty K] {Om : Matrix O O ℝ}
    (hOm : Om.IsHermitian) {κ : ℝ} (hκ : 0 ≤ κ) (hb : ∀ o o', |Om o o'| ≤ κ)
    (hz : ∀ o o', ¬ Linked c dims o o' → Om o o' = 0)
    {Xt : Matrix O K ℝ} {B2 : ℝ} (hB : ∀ o : O, ∑ k : K, (Xt o k) ^ 2 ≤ B2)
    (hOn : (Xtᵀ * Om * Xt).IsHermitian) :
    lambdaMin hOn ≤ κ * ((maxDegree c dims : ℝ) + 1) * ((Fintype.card O : ℝ) * B2) := by
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq_lambdaMin hOn
  rw [← hi]
  exact eigenvalues_conj_le_of_graphSupported c dims hOm hκ hb hz hB hOn i

omit [DecidableEq D] in
/-- **Lemma SM.B.11(e).** If `Ω_n ≻ 0`, then `D_n²/λ_min(Ω_n) ≤ 2B²C^{1/2}δ_n`. -/
theorem sharing_e_lambdaMin_of_graphSupported [Nonempty K] {Om : Matrix O O ℝ}
    (hOm : Om.IsHermitian) {κ : ℝ} (hκ : 0 < κ) (hb : ∀ o o', |Om o o'| ≤ κ)
    (hz : ∀ o o', ¬ Linked c dims o o' → Om o o' = 0)
    {Xt : Matrix O K ℝ} {B : ℝ} (hBpos : 0 < B)
    (hB : ∀ o : O, ∑ k : K, (Xt o k) ^ 2 ≤ B ^ 2)
    (hpd : (Xtᵀ * Om * Xt).PosDef) :
    (maxDegree c dims : ℝ) ^ 2 / lambdaMin hpd.1
      ≤ 2 * B ^ 2 * κ *
          deltaSeq (Fintype.card O : ℝ) (maxDegree c dims : ℝ) (lambdaMin hpd.1) := by
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq_lambdaMin hpd.1
  rw [← hi]
  exact sharing_e_of_graphSupported c dims hOm hκ hb hz hBpos hB hpd.1 i
    (hpd.eigenvalues_pos i)

end ClauseD2

/-! ### Proposition SM.D.3(a): the variance floor through `X̃`, and `D_n ≤ JḠ_n` -/

section ThreeSeqA

open scoped MatrixOrder
open Matrix

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
variable (c : D → O → L) (dims : Finset D)
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- `Ω ⪰ σ²I` implies `Ω_n = X̃'ΩX̃ ⪰ σ²X̃'X̃`. -/
theorem smul_transpose_mul_self_le_conj {Om : Matrix O O ℝ} {s2 : ℝ}
    (hfloor : s2 • (1 : Matrix O O ℝ) ≤ Om) (Xt : Matrix O K ℝ) :
    s2 • (Xtᵀ * Xt) ≤ Xtᵀ * Om * Xt := by
  have h := Multiway.mul_mul_transpose_le hfloor Xtᵀ
  rw [Matrix.transpose_transpose] at h
  have e : Xtᵀ * (s2 • (1 : Matrix O O ℝ)) * Xt = s2 • (Xtᵀ * Xt) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  rwa [e] at h

/-- **Proposition SM.D.3(a), first step**: `Ω_n = X̃'ΩX̃ ⪰ σ²X̃'X̃ ≻ 0`, given `X̃'X̃ ≻ 0` as
`hX`. -/
theorem posDef_conj_of_floor {Om : Matrix O O ℝ} {s2 : ℝ} (hs2 : 0 < s2)
    (hfloor : s2 • (1 : Matrix O O ℝ) ≤ Om) {Xt : Matrix O K ℝ}
    (hX : (Xtᵀ * Xt).PosDef) : (Xtᵀ * Om * Xt).PosDef :=
  Multiway.posDef_of_le (hX.smul hs2) (smul_transpose_mul_self_le_conj hfloor Xt)

/-- `Ḡ_n := max_{j≤J} max_{g∈𝒢_{\{j\}}} |g|`, the largest cluster of the maintained structure. -/
def maxCluster : ℕ :=
  dims.sup fun j => Finset.univ.sup fun o : O => (cellOf c {j} o).card

variable {c dims}

omit [DecidableEq O] [DecidableEq D] in
/-- Every maintained cluster has at most `Ḡ_n` elements. -/
theorem card_cellOf_le_maxCluster {j : D} (hj : j ∈ dims) (o : O) :
    (cellOf c {j} o).card ≤ maxCluster c dims :=
  le_trans (Finset.le_sup (f := fun o : O => (cellOf c {j} o).card) (Finset.mem_univ o))
    (Finset.le_sup (f := fun j => Finset.univ.sup fun o : O => (cellOf c {j} o).card) hj)

/-- The open neighbourhood of any `o` is covered by the `J` punctured clusters containing it, so
it has at most `J(Ḡ_n - 1)` elements. -/
theorem card_openNbhd_le_maxCluster (o : O) :
    (openNbhd c dims o).card ≤ dims.card * (maxCluster c dims - 1) := by
  classical
  have hsub : openNbhd c dims o ⊆ dims.biUnion (fun j => (cellOf c {j} o).erase o) := by
    intro o' ho'
    obtain ⟨hne, hlink⟩ := mem_openNbhd.1 ho'
    obtain ⟨j, hj, hc⟩ := hlink
    refine Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_erase.mpr ⟨hne, ?_⟩⟩
    refine mem_cellOf.mpr fun k hk => ?_
    rw [Finset.mem_singleton] at hk
    subst hk
    exact hc.symm
  calc (openNbhd c dims o).card
      ≤ (dims.biUnion (fun j => (cellOf c {j} o).erase o)).card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ dims, ((cellOf c {j} o).erase o).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ dims, (maxCluster c dims - 1) := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [Finset.card_erase_of_mem (mem_cellOf.mpr (sameOn_refl o))]
        exact Nat.sub_le_sub_right (card_cellOf_le_maxCluster hj o) 1
    _ = dims.card * (maxCluster c dims - 1) := by rw [Finset.sum_const, smul_eq_mul]

variable (c dims)

/-- `D_n ≤ max{1, J(Ḡ_n - 1)}`. -/
theorem maxDegree_le_max_one_mul :
    maxDegree c dims ≤ max 1 (dims.card * (maxCluster c dims - 1)) :=
  max_le_max (le_refl 1) (Finset.sup_le fun o _ => card_openNbhd_le_maxCluster o)

/-- `D_n ≤ max{1, J(Ḡ_n - 1)} ≤ JḠ_n`, for `J ≥ 1` (`hdims`) and a nonempty observation set. -/
theorem maxDegree_le_card_mul_maxCluster [Nonempty O] (hdims : dims.Nonempty) :
    maxDegree c dims ≤ dims.card * maxCluster c dims := by
  refine le_trans (maxDegree_le_max_one_mul c dims) (max_le ?_ ?_)
  · obtain ⟨j, hj⟩ := hdims
    obtain ⟨o⟩ := ‹Nonempty O›
    have hG : 1 ≤ maxCluster c dims :=
      le_trans (Finset.card_pos.mpr ⟨o, mem_cellOf.mpr (sameOn_refl o)⟩)
        (card_cellOf_le_maxCluster hj o)
    have hJ : 1 ≤ dims.card := Finset.card_pos.mpr ⟨j, hj⟩
    calc (1 : ℕ) = 1 * 1 := by ring
      _ ≤ dims.card * maxCluster c dims := Nat.mul_le_mul hJ hG
  · exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

/-- From `D_n ≤ JḠ_n` and a lower bound `λ_min(Ω_n) ≥ σ²nλ`, `δ_n ≤ KḠ_n³/n` with the explicit
constant `K = J³/(σ⁴λ²)`. -/
theorem deltaSeq_le_of_cluster_bound {nR Dn G J s2 lam lmin : ℝ} (hnR : 0 < nR) (hJ : 0 ≤ J)
    (hG : 0 ≤ G) (hs2 : 0 < s2) (hlam : 0 < lam) (hD0 : 0 ≤ Dn) (hD : Dn ≤ J * G)
    (hl : s2 * nR * lam ≤ lmin) :
    deltaSeq nR Dn lmin ≤ J ^ 3 / (s2 ^ 2 * lam ^ 2) * (G ^ 3 / nR) := by
  have hlpos : (0 : ℝ) < s2 * nR * lam := by positivity
  have hlminpos : (0 : ℝ) < lmin := lt_of_lt_of_le hlpos hl
  have h1 : Dn ^ 3 ≤ (J * G) ^ 3 := pow_le_pow_left₀ hD0 hD 3
  have h2 : (s2 * nR * lam) ^ 2 ≤ lmin ^ 2 := pow_le_pow_left₀ hlpos.le hl 2
  rw [deltaSeq, div_le_iff₀ (by positivity : (0 : ℝ) < lmin ^ 2)]
  have hR : J ^ 3 / (s2 ^ 2 * lam ^ 2) * (G ^ 3 / nR) * (s2 * nR * lam) ^ 2
      ≤ J ^ 3 / (s2 ^ 2 * lam ^ 2) * (G ^ 3 / nR) * lmin ^ 2 :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  refine le_trans ?_ hR
  have hcalc : J ^ 3 / (s2 ^ 2 * lam ^ 2) * (G ^ 3 / nR) * (s2 * nR * lam) ^ 2
      = nR * (J * G) ^ 3 := by
    field_simp
  rw [hcalc]
  exact mul_le_mul_of_nonneg_left h1 hnR.le

end ThreeSeqA

/-! ### Proposition SM.D.3(a): the eigenvalue bound

The bound `λ_min(Ω_n) ≥ σ²n(λ_min(H) - ε)` on the event `{‖n⁻¹X̃'X̃ - H‖ ≤ ε}` is proved in the
Loewner order: `‖A - H‖ ≤ ε` implies `(λ_min(H) - ε)I ⪯ A`. -/

section ThreeSeqAEigen

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix

variable {K : Type*} [Fintype K] [DecidableEq K]

omit [Fintype K] [DecidableEq K] in
/-- `M'M` is symmetric, for a rectangular `M`. -/
theorem isHermitian_transpose_mul_self {m : Type*} [Fintype m] (M : Matrix m K ℝ) :
    (Mᵀ * M).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [star_trivial, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun o _ => mul_comm _ _

/-- A symmetric `M` with `‖M‖ ≤ ε` satisfies `-εI ⪯ M`. -/
theorem neg_smul_one_le_of_norm_le {M : Matrix K K ℝ} (hM : M.IsHermitian) {ε : ℝ}
    (hε : ‖M‖ ≤ ε) : (-ε) • (1 : Matrix K K ℝ) ≤ M := by
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.sub hM ?_
    simp [Matrix.IsHermitian]
  · intro x
    have h1 : star x ⬝ᵥ ((M - (-ε) • (1 : Matrix K K ℝ)) *ᵥ x)
        = x ⬝ᵥ (M *ᵥ x) + ε * (x ⬝ᵥ x) := by
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_smul, smul_eq_mul, star_trivial]
      ring
    have h2 : -(x ⬝ᵥ (M *ᵥ x)) ≤ ‖M‖ * ‖(EuclideanSpace.equiv K ℝ).symm x‖ ^ 2 := by
      have h := Multiway.dot_mulVec_le (-M) x
      rwa [Matrix.neg_mulVec, dotProduct_neg, norm_neg] at h
    have h3 : ‖M‖ * ‖(EuclideanSpace.equiv K ℝ).symm x‖ ^ 2
        ≤ ε * ‖(EuclideanSpace.equiv K ℝ).symm x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hε (sq_nonneg _)
    rw [h1, Multiway.dot_self_eq]
    linarith

/-- If `λ_0 I ⪯ H` and `‖A - H‖ ≤ ε`, then `(λ_0 - ε)I ⪯ A`. -/
theorem smul_one_le_of_norm_sub_le {A H : Matrix K K ℝ} (hA : A.IsHermitian) (hH : H.IsHermitian)
    {lam0 ε : ℝ} (hHf : lam0 • (1 : Matrix K K ℝ) ≤ H) (hclose : ‖A - H‖ ≤ ε) :
    (lam0 - ε) • (1 : Matrix K K ℝ) ≤ A := by
  have h1 : (-ε) • (1 : Matrix K K ℝ) ≤ A - H := neg_smul_one_le_of_norm_le (hA.sub hH) hclose
  rw [Matrix.le_iff] at hHf h1 ⊢
  have e : A - (lam0 - ε) • (1 : Matrix K K ℝ)
      = (H - lam0 • (1 : Matrix K K ℝ)) + ((A - H) - (-ε) • (1 : Matrix K K ℝ)) := by
    module
  rw [e]
  exact hHf.add h1

/-- A lower Loewner bound `bI ⪯ H` gives `b ≤ λ_i(H)` at every eigenvalue. -/
theorem le_eigenvalues_of_smul_one_le {H : Matrix K K ℝ} (hH : H.IsHermitian) {b : ℝ}
    (h : b • (1 : Matrix K K ℝ) ≤ H) (i : K) : b ≤ hH.eigenvalues i := by
  set v : K → ℝ := ⇑(hH.eigenvectorBasis i) with hvdef
  have hvne : v ≠ 0 := by rw [hvdef]; exact Multiway.eigenvectorBasis_ne_zero hH i
  have hvv : 0 < v ⬝ᵥ v := by simpa using Matrix.dotProduct_star_self_pos_iff.mpr hvne
  have hmul : H *ᵥ v = hH.eigenvalues i • v := hH.mulVec_eigenvectorBasis i
  have h1 := Multiway.le_dotProduct_mulVec_of_smul_one_le h v
  rw [hmul, dotProduct_smul, smul_eq_mul] at h1
  nlinarith

variable [Fintype O] [DecidableEq O]

/-- From the variance floor `Ω ⪰ σ²I_n` and `λI_K ⪯ n⁻¹X̃'X̃`, `Ω_n = X̃'ΩX̃ ⪰ σ²nλ I_K`. -/
theorem smul_one_le_conj_of_design {Om : Matrix O O ℝ} {s2 : ℝ} (hs2 : 0 ≤ s2)
    (hfloor : s2 • (1 : Matrix O O ℝ) ≤ Om) {Xt : Matrix O K ℝ} {nR lam : ℝ} (hnR : 0 < nR)
    (hgram : lam • (1 : Matrix K K ℝ) ≤ (nR⁻¹ : ℝ) • (Xtᵀ * Xt)) :
    (s2 * (nR * lam)) • (1 : Matrix K K ℝ) ≤ Xtᵀ * Om * Xt := by
  have h1 : (nR * lam) • (1 : Matrix K K ℝ) ≤ Xtᵀ * Xt := by
    have h := Multiway.loewner_smul_le_smul (a := nR) hnR.le hgram
    rw [smul_smul, smul_smul, mul_inv_cancel₀ hnR.ne', one_smul] at h
    exact h
  have h2 := Multiway.loewner_smul_le_smul (a := s2) hs2 h1
  rw [smul_smul] at h2
  exact le_trans h2 (smul_transpose_mul_self_le_conj hfloor Xt)

/-- `λ_i(Ω_n) ≥ σ²n(λ_0 - ε)` at every eigenvalue, given `λ_0 I ⪯ H` (`hHf`) and
`‖n⁻¹X̃'X̃ - H‖ ≤ ε` (`hclose`). -/
theorem eigenvalues_conj_ge_of_design {Om : Matrix O O ℝ} {s2 : ℝ} (hs2 : 0 ≤ s2)
    (hfloor : s2 • (1 : Matrix O O ℝ) ≤ Om) {Xt : Matrix O K ℝ} {H : Matrix K K ℝ}
    {nR lam0 ε : ℝ} (hnR : 0 < nR) (hH : H.IsHermitian)
    (hHf : lam0 • (1 : Matrix K K ℝ) ≤ H)
    (hclose : ‖(nR⁻¹ : ℝ) • (Xtᵀ * Xt) - H‖ ≤ ε)
    (hHerm : (Xtᵀ * Om * Xt).IsHermitian) (i : K) :
    s2 * nR * (lam0 - ε) ≤ hHerm.eigenvalues i := by
  have hA : ((nR⁻¹ : ℝ) • (Xtᵀ * Xt)).IsHermitian :=
    (isHermitian_transpose_mul_self Xt).smul (IsSelfAdjoint.all _)
  have h1 : (lam0 - ε) • (1 : Matrix K K ℝ) ≤ (nR⁻¹ : ℝ) • (Xtᵀ * Xt) :=
    smul_one_le_of_norm_sub_le hA hH hHf hclose
  have h2 := smul_one_le_conj_of_design hs2 hfloor hnR h1
  have h3 := le_eigenvalues_of_smul_one_le hHerm h2 i
  calc s2 * nR * (lam0 - ε) = s2 * (nR * (lam0 - ε)) := by ring
    _ ≤ hHerm.eigenvalues i := h3

end ThreeSeqAEigen

/-! ### Proposition SM.D.3(a): the accumulation condition

`threeseq_a_accum` gives `δ_n ⟶ᵖ 0` (and `δ_nd_{[Δ]} ⟶ᵖ 0`) through a nonnegative multiplier,
and `threeseq_a_bigO` gives `δ_n = O_p(Ḡ_n³/n)` with an explicit constant. -/

section ThreeSeqAProb

open Filter MeasureTheory
open scoped Topology ENNReal MatrixOrder Matrix.Norms.L2Operator
open Matrix

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- If `|Z_n| ≤ b_n` on `E_n`, `b_n → 0` and `P(E_nᶜ) → 0`, then `Z_n ⟶ᵖ 0`. -/
theorem tendstoInProb_zero_of_le_on_event {Z : ℕ → Ω → ℝ} {b : ℕ → ℝ} {E : ℕ → Set Ω}
    (hle : ∀ n, ∀ ω ∈ E n, |Z n ω| ≤ b n) (hb : Tendsto b atTop (𝓝 0))
    (hE : Tendsto (fun n => P (E n)ᶜ) atTop (𝓝 0)) :
    TendstoInMeasure P Z atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hsmall : ∀ᶠ n in atTop, b n < ε := Filter.Tendsto.eventually_lt_const hε hb
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hE
    (Filter.Eventually.of_forall fun _n => zero_le) ?_
  filter_upwards [hsmall] with n hn
  refine measure_mono fun ω hω => ?_
  simp only [Set.mem_compl_iff]
  intro hEn
  have h1 : |Z n ω| ≤ b n := hle n ω hEn
  have h2 : ε ≤ dist (Z n ω) 0 := hω
  rw [Real.dist_eq, sub_zero] at h2
  linarith

/-- A sequence converging to zero in probability eventually puts almost all mass on any event
its smallness implies. -/
theorem event_compl_tendsto_zero_of_tendstoInProb {W : ℕ → Ω → ℝ} {E : ℕ → Set Ω} {ε : ℝ}
    (hε : 0 < ε) (hW : TendstoInMeasure P W atTop (fun _ => (0 : ℝ)))
    (hgood : ∀ n ω, |W n ω| < ε → ω ∈ E n) :
    Tendsto (fun n => P (E n)ᶜ) atTop (𝓝 0) := by
  rw [tendstoInMeasure_iff_dist] at hW
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hW ε hε)
    (fun n => zero_le) (fun n => measure_mono fun ω hω => ?_)
  simp only [Set.mem_ofPred_eq]
  by_contra hcon
  rw [not_le] at hcon
  rw [Real.dist_eq, sub_zero] at hcon
  exact hω (hgood n ω hcon)

/-- `δ_n = O_p(Ḡ_n³/n)` with an explicit constant: `P(δ_n > J³/(σ⁴λ²)·Ḡ_n³/n) → 0`. -/
theorem threeseq_a_bigO {nR Dn G : ℕ → ℝ} {J s2 lam : ℝ} {lmin : ℕ → Ω → ℝ}
    (hnR : ∀ n, 0 < nR n) (hJ : 0 ≤ J) (hG : ∀ n, 0 ≤ G n) (hs2 : 0 < s2) (hlam : 0 < lam)
    (hD0 : ∀ n, 0 ≤ Dn n) (hD : ∀ n, Dn n ≤ J * G n)
    (hE : Tendsto (fun n => P {ω | s2 * nR n * lam ≤ lmin n ω}ᶜ) atTop (𝓝 0)) :
    Tendsto (fun n => P {ω | J ^ 3 / (s2 ^ 2 * lam ^ 2) * (G n ^ 3 / nR n)
        < deltaSeq (nR n) (Dn n) (lmin n ω)}) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hE
    (fun n => zero_le) (fun n => measure_mono fun ω hω => ?_)
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
  intro hgood
  exact absurd (deltaSeq_le_of_cluster_bound (hnR n) hJ (hG n) hs2 hlam (hD0 n) (hD n) hgood)
    (not_le.2 hω)

/-- **Proposition SM.D.3(a), conclusion.** `mlt_n δ_n ⟶ᵖ 0` whenever `mlt_n Ḡ_n³/n → 0`, for a
nonnegative multiplier `mlt`; `mlt ≡ 1` and `mlt = d_{[Δ]}` give both parts of the accumulation
condition. -/
theorem threeseq_a_accum {nR Dn G mlt : ℕ → ℝ} {J s2 lam : ℝ} {lmin : ℕ → Ω → ℝ}
    (hnR : ∀ n, 0 < nR n) (hJ : 0 ≤ J) (hG : ∀ n, 0 ≤ G n) (hs2 : 0 < s2) (hlam : 0 < lam)
    (hD0 : ∀ n, 0 ≤ Dn n) (hD : ∀ n, Dn n ≤ J * G n) (hm : ∀ n, 0 ≤ mlt n)
    (hE : Tendsto (fun n => P {ω | s2 * nR n * lam ≤ lmin n ω}ᶜ) atTop (𝓝 0))
    (hb : Tendsto (fun n => mlt n * (G n ^ 3 / nR n)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => mlt n * deltaSeq (nR n) (Dn n) (lmin n ω)) atTop
      (fun _ => (0 : ℝ)) := by
  refine tendstoInProb_zero_of_le_on_event
    (b := fun n => J ^ 3 / (s2 ^ 2 * lam ^ 2) * (mlt n * (G n ^ 3 / nR n)))
    (E := fun n => {ω | s2 * nR n * lam ≤ lmin n ω}) (fun n ω hω => ?_) ?_ hE
  · have h := deltaSeq_le_of_cluster_bound (hnR n) hJ (hG n) hs2 hlam (hD0 n) (hD n) hω
    have hd0 : 0 ≤ deltaSeq (nR n) (Dn n) (lmin n ω) := by
      rw [deltaSeq]
      exact div_nonneg (mul_nonneg (hnR n).le (pow_nonneg (hD0 n) 3)) (sq_nonneg _)
    rw [abs_of_nonneg (mul_nonneg (hm n) hd0)]
    calc mlt n * deltaSeq (nR n) (Dn n) (lmin n ω)
        ≤ mlt n * (J ^ 3 / (s2 ^ 2 * lam ^ 2) * (G n ^ 3 / nR n)) :=
          mul_le_mul_of_nonneg_left h (hm n)
      _ = J ^ 3 / (s2 ^ 2 * lam ^ 2) * (mlt n * (G n ^ 3 / nR n)) := by ring
  · simpa using hb.const_mul (J ^ 3 / (s2 ^ 2 * lam ^ 2))

/-- `δ_n ⟶ᵖ 0` whenever `Ḡ_n³/n → 0`. -/
theorem threeseq_a_accum_i {nR Dn G : ℕ → ℝ} {J s2 lam : ℝ} {lmin : ℕ → Ω → ℝ}
    (hnR : ∀ n, 0 < nR n) (hJ : 0 ≤ J) (hG : ∀ n, 0 ≤ G n) (hs2 : 0 < s2) (hlam : 0 < lam)
    (hD0 : ∀ n, 0 ≤ Dn n) (hD : ∀ n, Dn n ≤ J * G n)
    (hE : Tendsto (fun n => P {ω | s2 * nR n * lam ≤ lmin n ω}ᶜ) atTop (𝓝 0))
    (hb : Tendsto (fun n => G n ^ 3 / nR n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => deltaSeq (nR n) (Dn n) (lmin n ω)) atTop
      (fun _ => (0 : ℝ)) := by
  have h := threeseq_a_accum (mlt := fun _ => 1) hnR hJ hG hs2 hlam hD0 hD
    (fun _ => zero_le_one) hE (by simpa using hb)
  simpa using h

/-- Over a sequence of designs with `n⁻¹X̃_n'X̃_n ⟶ᵖ H_n` (in the l2 operator norm), the
eigenvalue bound of `eigenvalues_conj_ge_of_design` holds with probability tending to one, at any
eigenvalue index `idx`. -/
theorem event_floor_of_design {Oseq Kseq : ℕ → Type*} [∀ n, Fintype (Oseq n)]
    [∀ n, DecidableEq (Oseq n)] [∀ n, Fintype (Kseq n)] [∀ n, DecidableEq (Kseq n)]
    {Xt : ∀ n, Ω → Matrix (Oseq n) (Kseq n) ℝ} {Om : ∀ n, Ω → Matrix (Oseq n) (Oseq n) ℝ}
    {H : ∀ n, Matrix (Kseq n) (Kseq n) ℝ} {nR : ℕ → ℝ} {s2 lam0 ε : ℝ}
    (hε : 0 < ε) (hs2 : 0 ≤ s2) (hnR : ∀ n, 0 < nR n)
    (hH : ∀ n, (H n).IsHermitian)
    (hHf : ∀ n, lam0 • (1 : Matrix (Kseq n) (Kseq n) ℝ) ≤ H n)
    (hOm : ∀ n ω, s2 • (1 : Matrix (Oseq n) (Oseq n) ℝ) ≤ Om n ω)
    (hHerm : ∀ n ω, ((Xt n ω)ᵀ * Om n ω * Xt n ω).IsHermitian)
    (idx : ∀ n, Ω → Kseq n)
    (hd2 : TendstoInMeasure P
      (fun n ω => ‖(nR n)⁻¹ • ((Xt n ω)ᵀ * Xt n ω) - H n‖) atTop (fun _ => (0 : ℝ))) :
    Tendsto (fun n => P {ω | s2 * nR n * (lam0 - ε)
        ≤ (hHerm n ω).eigenvalues (idx n ω)}ᶜ) atTop (𝓝 0) := by
  refine event_compl_tendsto_zero_of_tendstoInProb hε hd2 fun n ω hW => ?_
  simp only [Set.mem_ofPred_eq]
  have hclose : ‖(nR n)⁻¹ • ((Xt n ω)ᵀ * Xt n ω) - H n‖ ≤ ε :=
    le_of_lt (lt_of_le_of_lt (le_abs_self _) hW)
  exact eigenvalues_conj_ge_of_design hs2 (hOm n ω) (hnR n) (hH n) (hHf n) hclose
    (hHerm n ω) (idx n ω)

/-- **Proposition SM.D.3(a)** over a sequence of designs: the design conditions and the variance
floor `Ω ⪰ σ²I_n` give `δ_n ⟶ᵖ 0` at `mlt ≡ 1` and `δ_nd_{[Δ]} ⟶ᵖ 0` at `mlt = d_{[Δ]}`,
whenever the corresponding `Ḡ_n³/n → 0` or `Ḡ_n³d_{[Δ]}/n → 0` holds. Here `0 < λ_0 - ε`. -/
theorem threeseq_a_of_design {Oseq Kseq : ℕ → Type*} [∀ n, Fintype (Oseq n)]
    [∀ n, DecidableEq (Oseq n)] [∀ n, Fintype (Kseq n)] [∀ n, DecidableEq (Kseq n)]
    {Xt : ∀ n, Ω → Matrix (Oseq n) (Kseq n) ℝ} {Om : ∀ n, Ω → Matrix (Oseq n) (Oseq n) ℝ}
    {H : ∀ n, Matrix (Kseq n) (Kseq n) ℝ} {nR Dn G mlt : ℕ → ℝ} {J s2 lam0 ε : ℝ}
    (hε : 0 < ε) (hs2 : 0 < s2) (hlam : 0 < lam0 - ε) (hnR : ∀ n, 0 < nR n)
    (hJ : 0 ≤ J) (hG : ∀ n, 0 ≤ G n) (hD0 : ∀ n, 0 ≤ Dn n) (hD : ∀ n, Dn n ≤ J * G n)
    (hm : ∀ n, 0 ≤ mlt n)
    (hH : ∀ n, (H n).IsHermitian)
    (hHf : ∀ n, lam0 • (1 : Matrix (Kseq n) (Kseq n) ℝ) ≤ H n)
    (hOm : ∀ n ω, s2 • (1 : Matrix (Oseq n) (Oseq n) ℝ) ≤ Om n ω)
    (hHerm : ∀ n ω, ((Xt n ω)ᵀ * Om n ω * Xt n ω).IsHermitian)
    (idx : ∀ n, Ω → Kseq n)
    (hd2 : TendstoInMeasure P
      (fun n ω => ‖(nR n)⁻¹ • ((Xt n ω)ᵀ * Xt n ω) - H n‖) atTop (fun _ => (0 : ℝ)))
    (hb : Tendsto (fun n => mlt n * (G n ^ 3 / nR n)) atTop (𝓝 0)) :
    TendstoInMeasure P
      (fun n ω => mlt n * deltaSeq (nR n) (Dn n) ((hHerm n ω).eigenvalues (idx n ω)))
      atTop (fun _ => (0 : ℝ)) :=
  threeseq_a_accum hnR hJ hG hs2 hlam hD0 hD hm
    (event_floor_of_design hε hs2.le hnR hH hHf hOm hHerm idx hd2) hb

end ThreeSeqAProb

/-! ### Proposition SM.D.3(c): the cluster-shock model, deterministically

The shock index sets of two non-adjacent observation sets are disjoint, `ν` restricted to a set
depends only on those shocks, and the covariance matrix `clusterOmega` satisfies `Ω ⪰ σ²I_n`. -/

section ClusterShock

open scoped MatrixOrder
open Matrix

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

omit [Fintype O] [DecidableEq O] in
/-- A finite sum of positive semidefinite matrices is positive semidefinite. -/
theorem posSemidef_sum {γ : Type*} (s : Finset γ) (f : γ → Matrix O O ℝ)
    (h : ∀ i ∈ s, (f i).PosSemidef) : (∑ i ∈ s, f i).PosSemidef :=
  Finset.sum_induction f Matrix.PosSemidef (fun _ _ ha hb => ha.add hb)
    Matrix.PosSemidef.zero h

/-- **Proposition SM.D.3(c)(iv).** Each sharing matrix `Sh_e` is positive semidefinite, by the
Gram factorization `Sh_e = Δ_eΔ_e'` (`shMat_apply_eq_sum_cells`). -/
theorem shMat_posSemidef (c : D → O → L) (e : Finset D) : (Multiway.shMat c e).PosSemidef := by
  classical
  have h : Multiway.shMat c e
      = (Matrix.of fun (t : {t : Finset O // t ∈ cells c e}) (o : O) =>
            if o ∈ (t : Finset O) then (1 : ℝ) else 0)ᴴ
        * Matrix.of fun (t : {t : Finset O // t ∈ cells c e}) (o : O) =>
            if o ∈ (t : Finset O) then (1 : ℝ) else 0 := by
    ext o o'
    rw [Matrix.mul_apply, Multiway.shMat_apply_eq_sum_cells,
      ← Finset.sum_coe_sort (cells c e)
        (fun t => (if o ∈ t then (1 : ℝ) else 0) * (if o' ∈ t then (1 : ℝ) else 0))]
    exact Finset.sum_congr rfl fun t _ => by simp [Matrix.conjTranspose_apply]
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- **Proposition SM.D.3(c)(iii)**: `Ω = ∑_j σ²_{c,j}Sh^{(j)} + diag(Var(ε_o ∣ 𝒟))`. That this is
the conditional covariance matrix is `condOmega_eq_clusterOmega`. -/
def clusterOmega (c : D → O → L) (dims : Finset D) (sc : D → ℝ) (ve : O → ℝ) :
    Matrix O O ℝ :=
  (∑ j ∈ dims, sc j • Multiway.shMat c {j}) + Matrix.diagonal ve

omit [Fintype O] [DecidableEq D] in
/-- The entries of `clusterOmega`. -/
theorem clusterOmega_apply (c : D → O → L) (dims : Finset D) (sc : D → ℝ) (ve : O → ℝ)
    (o o' : O) :
    clusterOmega c dims sc ve o o'
      = (∑ j ∈ dims, if SameOn c {j} o o' then sc j else 0) + (if o = o' then ve o else 0) := by
  simp only [clusterOmega, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
    Multiway.shMat, Matrix.of_apply, smul_eq_mul, Matrix.diagonal_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : SameOn c {j} o o' <;> simp [h]

/-- **Proposition SM.D.3(c)**: `Ω ⪰ σ²I_n`. -/
theorem smul_one_le_clusterOmega {c : D → O → L} {dims : Finset D} {sc : D → ℝ} {ve : O → ℝ}
    {s2 : ℝ} (hsc : ∀ j ∈ dims, 0 ≤ sc j) (hve : ∀ o, s2 ≤ ve o) :
    s2 • (1 : Matrix O O ℝ) ≤ clusterOmega c dims sc ve := by
  rw [Matrix.le_iff]
  have e2 : Matrix.diagonal ve - s2 • (1 : Matrix O O ℝ)
      = Matrix.diagonal (fun o => ve o - s2) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  have e : clusterOmega c dims sc ve - s2 • (1 : Matrix O O ℝ)
      = (∑ j ∈ dims, sc j • Multiway.shMat c {j})
        + Matrix.diagonal (fun o => ve o - s2) := by
    rw [clusterOmega, add_sub_assoc, e2]
  rw [e]
  refine Matrix.PosSemidef.add ?_ ?_
  · exact posSemidef_sum _ _ fun j hj => (shMat_posSemidef c {j}).smul (hsc j hj)
  · exact Matrix.posSemidef_diagonal_iff.mpr fun o => by linarith [hve o]

/-- The same conclusion for an abstract `Ω` with the decomposition given entrywise. -/
theorem smul_one_le_of_clusterDecomposition {c : D → O → L} {dims : Finset D} {sc : D → ℝ}
    {ve : O → ℝ} {s2 : ℝ} {Om : Matrix O O ℝ}
    (hOm : ∀ o o', Om o o'
      = (∑ j ∈ dims, if SameOn c {j} o o' then sc j else 0) + (if o = o' then ve o else 0))
    (hsc : ∀ j ∈ dims, 0 ≤ sc j) (hve : ∀ o, s2 ≤ ve o) :
    s2 • (1 : Matrix O O ℝ) ≤ Om := by
  have e : Om = clusterOmega c dims sc ve := by
    ext o o'
    rw [hOm o o', clusterOmega_apply]
  rw [e]
  exact smul_one_le_clusterOmega hsc hve

omit [Fintype O] [DecidableEq D] in
/-- In the cluster-shock model, `Ω_{oo'} = 0` whenever `o ≁ o'`. The hypothesis
`dims.Nonempty` (`J ≥ 1`) is needed: at `J = 0` nothing is linked, not even `o` to itself. -/
theorem clusterOmega_eq_zero_of_not_linked {c : D → O → L} {dims : Finset D}
    (hdims : dims.Nonempty) {sc : D → ℝ} {ve : O → ℝ} {o o' : O}
    (h : ¬ Linked c dims o o') : clusterOmega c dims sc ve o o' = 0 := by
  rw [clusterOmega_apply]
  have hne : o ≠ o' := by
    rintro rfl
    obtain ⟨j, hj⟩ := hdims
    exact h ⟨j, hj, rfl⟩
  rw [ite_eq_right hne, add_zero]
  refine Finset.sum_eq_zero fun j hj => ?_
  refine ite_eq_right fun hs => ?_
  exact h ⟨j, hj, hs j (Finset.mem_singleton_self j)⟩

/-- The indices of the cluster shocks the observations in `S` depend on:
`{(j, g^{(j)}(o)) : j ≤ J, o ∈ S}`. -/
def shockIdx (c : D → O → L) (dims : Finset D) (S : Finset O) : Finset (D × L) :=
  dims.biUnion fun j => S.image fun o => (j, c j o)

omit [Fintype O] [DecidableEq O] in
/-- If `S₁` and `S₂` are non-adjacent in the sharing graph, the cluster shocks they depend on
are indexed by disjoint sets. -/
theorem shockIdx_disjoint {c : D → O → L} {dims : Finset D} {S₁ S₂ : Finset O}
    (hsep : ∀ o ∈ S₁, ∀ o' ∈ S₂, ¬ Linked c dims o o') :
    Disjoint (shockIdx c dims S₁) (shockIdx c dims S₂) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  rintro ⟨j, l⟩ h1 h2
  simp only [shockIdx, Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq] at h1 h2
  obtain ⟨j1, hj1, o1, ho1, hje1, hl1⟩ := h1
  obtain ⟨j2, hj2, o2, ho2, hje2, hl2⟩ := h2
  rw [hje1] at hl1
  rw [hje2] at hl2
  refine hsep o1 ho1 o2 ho2 ⟨j, ?_, ?_⟩
  · rw [← hje1]; exact hj1
  · rw [hl1, hl2]

/-- `ν_o = ∑_j c^{(j)}_{g^{(j)}(o)} + ε_o`, the cluster-shock representation. -/
def nuVal (c : D → O → L) (dims : Finset D) (cs : D × L → ℝ) (ep : O → ℝ) (o : O) : ℝ :=
  (∑ j ∈ dims, cs (j, c j o)) + ep o

omit [Fintype O] [DecidableEq O] in
/-- `ν_o` for `o ∈ S` depends only on the shocks indexed by `shockIdx S` and on `ε_o`. -/
theorem nuVal_congr {c : D → O → L} {dims : Finset D} {cs cs' : D × L → ℝ} {ep ep' : O → ℝ}
    {S : Finset O} (hcs : ∀ p ∈ shockIdx c dims S, cs p = cs' p) (hep : ∀ o ∈ S, ep o = ep' o)
    {o : O} (ho : o ∈ S) : nuVal c dims cs ep o = nuVal c dims cs' ep' o := by
  classical
  unfold nuVal
  rw [hep o ho]
  congr 1
  refine Finset.sum_congr rfl fun j hj => hcs _ ?_
  simp only [shockIdx, Finset.mem_biUnion]
  exact ⟨j, hj, Finset.mem_image_of_mem _ ho⟩

omit [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L] in
/-- If `|c^{(j)}_g| ≤ a_j` for all `g` and `|ε_o| ≤ b` for all `o`, then `|ν_o| ≤ ∑_j a_j + b`. -/
theorem abs_nuVal_le {c : D → O → L} {dims : Finset D} {cs : D × L → ℝ} {ep : O → ℝ}
    {a : D → ℝ} {b : ℝ} (ha : ∀ j ∈ dims, ∀ g : L, |cs (j, g)| ≤ a j) (hb : ∀ o, |ep o| ≤ b)
    (o : O) :
    |nuVal c dims cs ep o| ≤ (∑ j ∈ dims, a j) + b := by
  rw [nuVal]
  refine (abs_add_le _ _).trans (add_le_add ?_ (hb o))
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro j hj
  exact ha j hj (c j o)

omit [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L] in
/-- With bounded shocks, `ν_o⁴ ≤ C_ν⁴` pointwise. The conditional fourth-moment bound from the
shocks' conditional fourth moments is `ClusterJanson.condExp_nuRV_pow_four_le` in
`Multiway/ClusterShockB.lean`. -/
theorem nuVal_pow_four_le {c : D → O → L} {dims : Finset D} {cs : D × L → ℝ} {ep : O → ℝ}
    {a : D → ℝ} {b : ℝ} (ha : ∀ j ∈ dims, ∀ g : L, |cs (j, g)| ≤ a j) (hb : ∀ o, |ep o| ≤ b)
    (o : O) :
    nuVal c dims cs ep o ^ 4 ≤ ((∑ j ∈ dims, a j) + b) ^ 4 :=
  calc nuVal c dims cs ep o ^ 4 ≤ |nuVal c dims cs ep o ^ 4| := le_abs_self _
    _ = |nuVal c dims cs ep o| ^ 4 := abs_pow _ _
    _ ≤ ((∑ j ∈ dims, a j) + b) ^ 4 :=
        pow_le_pow_left₀ (abs_nonneg _) (abs_nuVal_le ha hb o) 4

end ClusterShock

/-! ### Non-vacuity witnesses

Each witness applies the theorem it witnesses to a concrete model. The first graph model has two
observations, one maintained dimension, and a single cluster containing both, so every pair is
linked. -/

section Witness

/-- Two observations. -/
abbrev WitO := Fin 2

/-- One maintained dimension. -/
abbrev WitD := Fin 1

/-- One cluster label: everything shares. -/
def witC : WitD → WitO → Fin 1 := fun _ _ => 0

/-- The maintained dimension is kept. -/
def witDims : Finset WitD := Finset.univ

lemma witLinked (o o' : WitO) : Linked witC witDims o o' :=
  ⟨0, Finset.mem_univ 0, rfl⟩

/-- Every pair is linked in the graph model. -/
lemma witness_graph_nonempty : (linkedPairs witC witDims).Nonempty :=
  ⟨(0, 0), by simp [linkedPairs, witLinked]⟩

/-- Witness for `eigenvalues_le_of_graphSupported`: the identity on two observations, `κ = 1`. -/
theorem witness_eigenvalues_le (i : WitO) :
    (Matrix.isHermitian_one (n := WitO) (α := ℝ)).eigenvalues i
      ≤ (1 : ℝ) * ((maxDegree witC witDims : ℝ) + 1) := by
  refine eigenvalues_le_of_graphSupported witC witDims Matrix.isHermitian_one 1 ?_ ?_ i
  · intro o o'
    by_cases h : o = o' <;> simp [Matrix.one_apply, h]
  · intro o o' h
    exact absurd (witLinked o o') h

/-- Witness for `sharing_e`, at `B = Csqrt = nR = Dn = lmin = 1`. -/
theorem witness_sharing_e :
    (1 : ℝ) ^ 2 / 1 ≤ 2 * (1 : ℝ) ^ 2 * 1 * deltaSeq 1 1 1 := by
  refine sharing_e (B := 1) (Csqrt := 1) (nR := 1) (Dn := 1) (lmin := 1)
    one_pos one_pos le_rfl one_pos ?_
  norm_num

/-- Witness for `threeseq_b`, at `ε = 1/2`, `η = 1`, `C = K = 1`, `n = G = Dn = 1`, `δ = 1`. -/
theorem witness_threeseq_b :
    ((1 : ℝ) / 1) ^ ((1 : ℝ) / 2) * 1
      ≤ 2 ^ ((1 : ℝ) / 2) * 1 *
        ((1 : ℝ) ^ (3 : ℕ) * (1 : ℝ) ^ (-(3 * (1 : ℝ)) + (1 / 2) * (2 / 3 + 1))) := by
  refine threeseq_b (ε := 1 / 2) (η := 1) (C := 1) (K := 1) (nR := 1) (G := 1) (Dn := 1)
    (δ := 1) (by norm_num) (by norm_num) (by norm_num) le_rfl one_pos one_pos one_pos
    (by norm_num) (by norm_num) ?_ ?_
  · norm_num
  · rw [Real.one_rpow]; norm_num

/-- Witness for `deltaSeq_le_of_cluster_bound`, at `n = 4`, `D_n = 2`, `J = Ḡ_n = 2`,
`σ² = λ = 1` and `λ_min(Ω_n) = 4`, where the inequality `2 ≤ 16` is strict. -/
theorem witness_deltaSeq_le_of_cluster_bound :
    deltaSeq 4 2 4 ≤ (2 : ℝ) ^ 3 / ((1 : ℝ) ^ 2 * (1 : ℝ) ^ 2) * ((2 : ℝ) ^ 3 / 4) :=
  deltaSeq_le_of_cluster_bound (nR := 4) (Dn := 2) (G := 2) (J := 2) (s2 := 1) (lam := 1)
    (lmin := 4) (by norm_num) (by norm_num) (by norm_num) one_pos one_pos (by norm_num)
    (by norm_num) (by norm_num)

/-- Witness for `threeseq_b_tendsto`, at `ε = 1/2`, `η = 1`. -/
theorem witness_threeseq_b_tendsto :
    Filter.Tendsto
      (fun x : ℝ => x ^ (-(3 * (1 : ℝ)) + (1 / 2) * (2 / 3 + 1))) Filter.atTop (nhds 0) := by
  refine threeseq_b_tendsto (ε := 1 / 2) (η := 1) one_pos ?_
  norm_num

end Witness

/-! ### Witnesses for clause (d)'s second bound and for Proposition SM.D.3

A second model, `witC2`, puts each observation in its own cluster, so that it has a non-adjacent
pair. -/

section Witness2

open scoped MatrixOrder
open Matrix

/-- The second model: one maintained dimension, each observation in its own cluster, so that
`o ∼ o'` exactly when `o = o'`. -/
def witC2 : WitD → WitO → WitO := fun _ o => o

/-- The second model has a non-adjacent pair. -/
lemma witNotLinked : ¬ Linked witC2 witDims (0 : WitO) 1 := by
  rintro ⟨j, -, h⟩
  simp [witC2] at h

/-- Witness for `le_smul_one_of_graphSupported`: the identity on two observations, `κ = 1`. -/
theorem witness_le_smul_one :
    (1 : Matrix WitO WitO ℝ)
      ≤ ((1 : ℝ) * ((maxDegree witC witDims : ℝ) + 1)) • (1 : Matrix WitO WitO ℝ) := by
  refine le_smul_one_of_graphSupported witC witDims Matrix.isHermitian_one zero_le_one ?_ ?_
  · intro o o'
    by_cases h : o = o' <;> simp [Matrix.one_apply, h]
  · intro o o' h
    exact absurd (witLinked o o') h

/-- Witness for `transpose_mul_self_le_smul_one`, at `X̃ = I₂` and `B² = 1`. -/
theorem witness_transpose_mul_self_le :
    (1 : Matrix WitO WitO ℝ)ᵀ * (1 : Matrix WitO WitO ℝ)
      ≤ ((Fintype.card WitO : ℝ) * 1) • (1 : Matrix WitO WitO ℝ) := by
  refine transpose_mul_self_le_smul_one (K := WitO) (Xt := 1) (B2 := 1) ?_
  intro o
  have e : ∀ k : WitO, ((1 : Matrix WitO WitO ℝ) o k) ^ 2 = if o = k then (1 : ℝ) else 0 := by
    intro k
    by_cases h : o = k <;> simp [Matrix.one_apply, h]
  rw [Finset.sum_congr rfl (fun k _ => e k), Finset.sum_ite_eq]
  simp

/-- Witness for `conj_le_smul_one_of_graphSupported`, at `Ω = I₂`, `X̃ = I₂`, `κ = B² = 1`. -/
theorem witness_conj_le_smul_one :
    (1 : Matrix WitO WitO ℝ)ᵀ * (1 : Matrix WitO WitO ℝ) * (1 : Matrix WitO WitO ℝ)
      ≤ ((1 : ℝ) * ((maxDegree witC witDims : ℝ) + 1) * ((Fintype.card WitO : ℝ) * 1))
          • (1 : Matrix WitO WitO ℝ) := by
  refine conj_le_smul_one_of_graphSupported witC witDims Matrix.isHermitian_one zero_le_one
    ?_ ?_ ?_
  · intro o o'
    by_cases h : o = o' <;> simp [Matrix.one_apply, h]
  · intro o o' h
    exact absurd (witLinked o o') h
  · intro o
    have e : ∀ k : WitO, ((1 : Matrix WitO WitO ℝ) o k) ^ 2 = if o = k then (1 : ℝ) else 0 := by
      intro k
      by_cases h : o = k <;> simp [Matrix.one_apply, h]
    rw [Finset.sum_congr rfl (fun k _ => e k), Finset.sum_ite_eq]
    simp

/-- The symmetry of `Ω_n` in the witness model. -/
theorem witOnHerm :
    ((1 : Matrix WitO WitO ℝ)ᵀ * (1 : Matrix WitO WitO ℝ)
      * (1 : Matrix WitO WitO ℝ)).IsHermitian := by
  simp

/-- Witness for `eigenvalues_conj_le_of_graphSupported`. -/
theorem witness_eigenvalues_conj_le (i : WitO) :
    witOnHerm.eigenvalues i
      ≤ (1 : ℝ) * ((maxDegree witC witDims : ℝ) + 1) * ((Fintype.card WitO : ℝ) * 1) := by
  refine eigenvalues_conj_le_of_graphSupported witC witDims Matrix.isHermitian_one zero_le_one
    ?_ ?_ ?_ witOnHerm i
  · intro o o'
    by_cases h : o = o' <;> simp [Matrix.one_apply, h]
  · intro o o' h
    exact absurd (witLinked o o') h
  · intro o
    have e : ∀ k : WitO, ((1 : Matrix WitO WitO ℝ) o k) ^ 2 = if o = k then (1 : ℝ) else 0 := by
      intro k
      by_cases h : o = k <;> simp [Matrix.one_apply, h]
    rw [Finset.sum_congr rfl (fun k _ => e k), Finset.sum_ite_eq]
    simp

/-- Witness for `posDef_conj_of_floor`, at `Ω = X̃ = I₂` and `σ² = 1`. -/
theorem witness_posDef_conj_of_floor :
    ((1 : Matrix WitO WitO ℝ)ᵀ * (1 : Matrix WitO WitO ℝ)
      * (1 : Matrix WitO WitO ℝ)).PosDef := by
  refine posDef_conj_of_floor (s2 := 1) one_pos ?_ ?_
  · simp
  · simpa using (Matrix.PosDef.one : (1 : Matrix WitO WitO ℝ).PosDef)

/-- Witness for `sharing_e_of_graphSupported`. -/
theorem witness_sharing_e_of_graphSupported (i : WitO) :
    (maxDegree witC witDims : ℝ) ^ 2 / witOnHerm.eigenvalues i
      ≤ 2 * (1 : ℝ) ^ 2 * 1 *
          deltaSeq (Fintype.card WitO : ℝ) (maxDegree witC witDims : ℝ)
            (witOnHerm.eigenvalues i) := by
  refine sharing_e_of_graphSupported witC witDims Matrix.isHermitian_one one_pos ?_ ?_
    one_pos ?_ witOnHerm i (witness_posDef_conj_of_floor.eigenvalues_pos i)
  · intro o o'
    by_cases h : o = o' <;> simp [Matrix.one_apply, h]
  · intro o o' h
    exact absurd (witLinked o o') h
  · intro o
    have e : ∀ k : WitO, ((1 : Matrix WitO WitO ℝ) o k) ^ 2 = if o = k then (1 : ℝ) else 0 := by
      intro k
      by_cases h : o = k <;> simp [Matrix.one_apply, h]
    rw [Finset.sum_congr rfl (fun k _ => e k), Finset.sum_ite_eq]
    simp

/-- Witness for `sharing_e_lambdaMin_of_graphSupported`. Here the spectrum of `Ω_n` is
constant; `witness_lambdaMin_lt_eigenvalues` covers a non-constant spectrum. -/
theorem witness_sharing_e_lambdaMin :
    (maxDegree witC witDims : ℝ) ^ 2 / lambdaMin witness_posDef_conj_of_floor.1
      ≤ 2 * (1 : ℝ) ^ 2 * 1 *
          deltaSeq (Fintype.card WitO : ℝ) (maxDegree witC witDims : ℝ)
            (lambdaMin witness_posDef_conj_of_floor.1) := by
  refine sharing_e_lambdaMin_of_graphSupported witC witDims Matrix.isHermitian_one one_pos
    ?_ ?_ one_pos ?_ witness_posDef_conj_of_floor
  · intro o o'
    by_cases h : o = o' <;> simp [Matrix.one_apply, h]
  · intro o o' h
    exact absurd (witLinked o o') h
  · intro o
    have e : ∀ k : WitO, ((1 : Matrix WitO WitO ℝ) o k) ^ 2 = if o = k then (1 : ℝ) else 0 := by
      intro k
      by_cases h : o = k <;> simp [Matrix.one_apply, h]
    rw [Finset.sum_congr rfl (fun k _ => e k), Finset.sum_ite_eq]
    simp

/-- The model `Ω = diag(1, 4)`, with a non-constant spectrum. -/
def witOmSpread : Matrix WitO WitO ℝ := Matrix.diagonal ![1, 4]

lemma witOmSpreadHerm : witOmSpread.IsHermitian := Matrix.isHermitian_diagonal _

lemma witOmSpread_eq : witOmSpread = Matrix.diagonal ![(1 : ℝ), 4] := rfl

/-- On `diag(1, 4)`, `λ_min(Ω)` is strictly below some eigenvalue. The proof uses
`tr Ω = 5` and `det Ω = 4` rather than computing the eigenvalues. -/
theorem witness_lambdaMin_lt_eigenvalues :
    ∃ i : WitO, lambdaMin witOmSpreadHerm < witOmSpreadHerm.eigenvalues i := by
  by_contra hcon
  have hcon' : ∀ i : WitO, witOmSpreadHerm.eigenvalues i ≤ lambdaMin witOmSpreadHerm :=
    fun i => not_lt.mp (fun h => hcon ⟨i, h⟩)
  have h0 : witOmSpreadHerm.eigenvalues 0 = lambdaMin witOmSpreadHerm :=
    le_antisymm (hcon' 0) (lambdaMin_le _ 0)
  have h1 : witOmSpreadHerm.eigenvalues 1 = lambdaMin witOmSpreadHerm :=
    le_antisymm (hcon' 1) (lambdaMin_le _ 1)
  have htr := witOmSpreadHerm.trace_eq_sum_eigenvalues
  have hdet := witOmSpreadHerm.det_eq_prod_eigenvalues
  have htr2 : witOmSpread.trace = 5 := by
    rw [witOmSpread_eq, Matrix.trace_diagonal]
    norm_num [Fin.sum_univ_two]
  have hdet2 : witOmSpread.det = 4 := by
    rw [witOmSpread_eq, Matrix.det_diagonal]
    norm_num [Fin.prod_univ_two]
  rw [htr2] at htr
  rw [hdet2] at hdet
  simp only [Fin.sum_univ_two, Fin.prod_univ_two, RCLike.ofReal_real_eq_id, id_eq] at htr hdet
  rw [h0, h1] at htr hdet
  nlinarith [htr, hdet]

/-- Witness for `maxDegree_le_card_mul_maxCluster`, with `D_n = 1`, `J = 1` and `Ḡ_n = 2`. -/
theorem witness_maxDegree_le_card_mul_maxCluster :
    maxDegree witC witDims ≤ witDims.card * maxCluster witC witDims :=
  maxDegree_le_card_mul_maxCluster witC witDims ⟨0, Finset.mem_univ 0⟩

/-- Witness for `shMat_posSemidef`. -/
theorem witness_shMat_posSemidef : (Multiway.shMat witC witDims).PosSemidef :=
  shMat_posSemidef witC witDims

/-- Witness for `smul_one_le_clusterOmega`, at `σ²_{c,1} = Var(ε_o ∣ 𝒟) = σ² = 1`. -/
theorem witness_clusterOmega_floor :
    (1 : ℝ) • (1 : Matrix WitO WitO ℝ)
      ≤ clusterOmega witC witDims (fun _ => 1) (fun _ => 1) :=
  smul_one_le_clusterOmega (fun _ _ => zero_le_one) (fun _ => le_refl 1)

/-- Witness for `smul_one_le_of_clusterDecomposition`. -/
theorem witness_clusterDecomposition_floor :
    (1 : ℝ) • (1 : Matrix WitO WitO ℝ)
      ≤ clusterOmega witC witDims (fun _ => 1) (fun _ => 1) :=
  smul_one_le_of_clusterDecomposition (c := witC) (dims := witDims)
    (fun o o' => clusterOmega_apply witC witDims (fun _ => 1) (fun _ => 1) o o')
    (fun _ _ => zero_le_one) (fun _ => le_refl 1)

/-- Witness for `clusterOmega_eq_zero_of_not_linked`, in the second model, where `0 ≁ 1`. -/
theorem witness_clusterOmega_eq_zero :
    clusterOmega witC2 witDims (fun _ => 1) (fun _ => 1) (0 : WitO) 1 = 0 :=
  clusterOmega_eq_zero_of_not_linked ⟨0, Finset.mem_univ 0⟩ witNotLinked

/-- Witness for `shockIdx_disjoint`, at `S₁ = {0}`, `S₂ = {1}` in the second model. -/
theorem witness_shockIdx_disjoint :
    Disjoint (shockIdx witC2 witDims {(0 : WitO)}) (shockIdx witC2 witDims {(1 : WitO)}) := by
  refine shockIdx_disjoint ?_
  intro o ho o' ho'
  rw [Finset.mem_singleton] at ho ho'
  subst ho
  subst ho'
  exact witNotLinked

/-- A shock configuration. -/
def witCs : WitD × WitO → ℝ := fun _ => 1

/-- The same configuration, changed at the cluster `1` of dimension `0`, which `ν_0` does not
see. -/
def witCs' : WitD × WitO → ℝ := fun p => if p.2 = 1 then 2 else 1

/-- Witness for `nuVal_congr`: the two configurations differ, yet agree on `shockIdx {0}`, so
`ν_0` is unchanged. -/
theorem witness_nuVal_congr :
    nuVal witC2 witDims witCs (fun _ => 0) (0 : WitO)
      = nuVal witC2 witDims witCs' (fun _ => 0) (0 : WitO) := by
  refine nuVal_congr (S := {(0 : WitO)}) ?_ (fun _ _ => rfl) (Finset.mem_singleton_self _)
  intro p hp
  simp only [shockIdx, Finset.mem_biUnion, Finset.mem_image, Finset.mem_singleton] at hp
  obtain ⟨j, -, o, ho, hp⟩ := hp
  subst ho
  subst hp
  simp [witCs, witCs', witC2]

/-- The two configurations are different. -/
theorem witCs_ne_witCs' : witCs ≠ witCs' := by
  intro h
  have := congrFun h ((0 : WitD), (1 : WitO))
  simp [witCs, witCs'] at this

end Witness2

/-! ### The Regime 3 assumption

Regime 3: conditionally on `𝒟`, for any two disjoint sets `S₁, S₂ ⊆ 𝒪` with `o ≁ o'` for every
`o ∈ S₁` and `o' ∈ S₂`, the families `{ν_o}_{o∈S₁}` and `{ν_{o'}}_{o'∈S₂}` are independent. It is
expressed with `ProbabilityTheory.CondIndep` between the σ-algebras the two blocks generate. -/

section Regime3

open MeasureTheory ProbabilityTheory MeasurableSpace

/-- The Regime 3 assumption. `ν` is the disturbance, `𝒟` the design σ-algebra with
`h𝒟 : 𝒟 ≤ mΩ`, and `P` the probability measure. For disjoint, separated blocks `S₁` and `S₂`,
the σ-algebras they generate are conditionally independent given `𝒟`. -/
def Regime3 {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] (h𝒟 : 𝒟 ≤ mΩ) (c : D → O → L) (dims : Finset D)
    (ν : O → Ω → ℝ) (P : Measure Ω) [IsFiniteMeasure P] : Prop :=
  ∀ S₁ S₂ : Finset O, Disjoint S₁ S₂ →
    (∀ o ∈ S₁, ∀ o' ∈ S₂, ¬ Linked c dims o o') →
    CondIndep 𝒟 (⨆ o ∈ (S₁ : Set O), MeasurableSpace.comap (ν o) inferInstance)
      (⨆ o ∈ (S₂ : Set O), MeasurableSpace.comap (ν o) inferInstance) h𝒟 P

/-- Mutual conditional independence of the `ν_o` gives Regime 3, by `condIndep_iSup_of_disjoint`.
The separation hypothesis is not used, so this reading is strictly stronger than Regime 3. -/
theorem regime3_of_iCondIndepFun {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] (h𝒟 : 𝒟 ≤ mΩ) (c : D → O → L) (dims : Finset D)
    {ν : O → Ω → ℝ} {P : Measure Ω} [IsFiniteMeasure P]
    (hν : ∀ o, Measurable (ν o)) (hind : iCondIndepFun 𝒟 h𝒟 ν P) :
    Regime3 𝒟 h𝒟 c dims ν P := by
  intro S₁ S₂ hdisj _
  exact condIndep_iSup_of_disjoint (fun o => (hν o).comap_le)
    ((iCondIndepFun_iff_iCondIndep 𝒟 h𝒟 _ ν P).1 hind) (Finset.disjoint_coe.2 hdisj)

/-- Under Regime 3, `ν_o` and `ν_{o'}` are conditionally independent given `𝒟` for distinct,
non-linked `o` and `o'`. -/
theorem condIndepFun_of_regime3 [DecidableEq O] {Ω : Type*} {𝒟 : MeasurableSpace Ω}
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {h𝒟 : 𝒟 ≤ mΩ} {c : D → O → L}
    {dims : Finset D} {ν : O → Ω → ℝ} {P : Measure Ω} [IsFiniteMeasure P]
    (hreg : Regime3 𝒟 h𝒟 c dims ν P) {o o' : O} (hne : o ≠ o')
    (hsep : ¬ Linked c dims o o') :
    CondIndepFun 𝒟 h𝒟 (ν o) (ν o') P := by
  have h := hreg {o} {o'} (by simpa using hne) (by
    intro a ha b hb
    rw [Finset.mem_singleton] at ha hb
    subst ha
    subst hb
    exact hsep)
  rw [Finset.coe_singleton, Finset.coe_singleton, _root_.iSup_singleton,
    _root_.iSup_singleton] at h
  exact (condIndepFun_iff_condIndep 𝒟 h𝒟 (ν o) (ν o') P).2 h

end Regime3

/-! ### Clause (a) of Lemma SM.B.11

The conditional product rule is proved pointwise: `condIndepFun_iff_map_prod_eq_prod_map_map`
gives, for almost every `ω`, ordinary independence under `condExpKernel P 𝒟 ω`, where
`IndepFun.integral_mul_eq_mul_integral` applies. -/

section ClauseA

open MeasureTheory ProbabilityTheory MeasurableSpace
open Matrix

variable {Ω : Type*} {𝒟 mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {h𝒟 : 𝒟 ≤ mΩ}
  {P : Measure Ω} [IsFiniteMeasure P]

/-- The conditional product rule: for conditionally independent real random variables,
`𝔼[XY ∣ 𝒟] = 𝔼[X ∣ 𝒟]𝔼[Y ∣ 𝒟]`. The integrability hypotheses are needed only to read the
conditional expectations as integrals against `condExpKernel`. -/
theorem condExp_mul_of_condIndepFun {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hXi : Integrable X P) (hYi : Integrable Y P) (hXYi : Integrable (X * Y) P)
    (hind : CondIndepFun 𝒟 h𝒟 X Y P) :
    P[X * Y | 𝒟] =ᵐ[P] P[X | 𝒟] * P[Y | 𝒟] := by
  have hker : ∀ᵐ ω ∂P, IndepFun X Y ((condExpKernel P 𝒟) ω) := by
    refine ae_of_ae_trim h𝒟 ?_
    filter_upwards [(condIndepFun_iff_map_prod_eq_prod_map_map hX hY).1 hind] with ω hω
    rw [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]
    rwa [Kernel.map_apply _ (hX.prodMk hY), Kernel.prod_apply, Kernel.map_apply _ hX,
      Kernel.map_apply _ hY] at hω
  filter_upwards [hker, condExp_ae_eq_integral_condExpKernel h𝒟 hXYi,
    condExp_ae_eq_integral_condExpKernel h𝒟 hXi,
    condExp_ae_eq_integral_condExpKernel h𝒟 hYi] with ω hω h1 h2 h3
  rw [h1, Pi.mul_apply, h2, h3]
  exact hω.integral_mul_eq_mul_integral hX.aestronglyMeasurable hY.aestronglyMeasurable

/-- An independent family is conditionally independent given the trivial σ-algebra. -/
theorem iCondIndepFun_bot_of_iIndepFun {ι : Type*} {β : ι → Type*}
    [mβ : ∀ i, MeasurableSpace (β i)] {Z : ∀ i, Ω → β i} [IsProbabilityMeasure P]
    (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P) :
    iCondIndepFun ⊥ bot_le Z P := by
  classical
  refine (iCondIndepFun_iff_condExp_inter_preimage_eq_mul mβ Z hZ).2 ?_
  intro S sets hsets
  refine Filter.Eventually.of_forall fun ω => ?_
  have hmS : MeasurableSet (⋂ i ∈ S, Z i ⁻¹' sets i) :=
    MeasurableSet.biInter S.countable_toSet fun i hi => (hZ i) (hsets i hi)
  have hR : ∀ i ∈ S, ∫ x, (Z i ⁻¹' sets i).indicator (fun _ => (1 : ℝ)) x ∂P
      = (P (Z i ⁻¹' sets i)).toReal := by
    intro i hi
    rw [integral_indicator_const _ ((hZ i) (hsets i hi))]
    simp [measureReal_def]
  rw [condExp_bot, Finset.prod_apply]
  simp only [condExp_bot]
  rw [integral_indicator_const _ hmS, Finset.prod_congr rfl hR]
  simp only [smul_eq_mul, mul_one, measureReal_def]
  rw [(iIndepFun_iff_measure_inter_preimage_eq_mul).1 hind S hsets, ENNReal.toReal_prod]

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
variable {c : D → O → L} {dims : Finset D} {ν : O → Ω → ℝ}

omit [Fintype O] [DecidableEq D] [DecidableEq L] in
/-- **Lemma SM.B.11(a), first part.** Under Regime 3 (`hreg`), conditional mean zero (`hexog`)
and square integrability (`hL2`), `Ω_{oo'} = 𝔼[ν_oν_{o'} ∣ 𝒟] = 0` for `o ≁ o'`. Here `hdims`
is `J ≥ 1`. -/
theorem condCov_eq_zero_of_not_linked (hdims : dims.Nonempty) (hreg : Regime3 𝒟 h𝒟 c dims ν P)
    (hmeas : ∀ o, Measurable (ν o)) (hL2 : ∀ o, MemLp (ν o) 2 P)
    (hexog : ∀ o, P[ν o | 𝒟] =ᵐ[P] 0) {o o' : O} (hsep : ¬ Linked c dims o o') :
    P[ν o * ν o' | 𝒟] =ᵐ[P] 0 := by
  have hne : o ≠ o' := by
    rintro rfl
    exact hsep ⟨hdims.choose, hdims.choose_spec, rfl⟩
  have h := condExp_mul_of_condIndepFun (hmeas o) (hmeas o')
    ((hL2 o).integrable one_le_two) ((hL2 o').integrable one_le_two)
    ((hL2 o).integrable_mul (hL2 o')) (condIndepFun_of_regime3 hreg hne hsep)
  filter_upwards [h, hexog o] with ω hω h0
  simp [hω, h0]

omit [DecidableEq O] [DecidableEq D] [DecidableEq L] in
/-- `(X̃'ΩX̃)_{kl} = ∑_{o,o'} x̃_{ok}x̃_{o'l}Ω_{oo'}`. -/
theorem conj_apply_eq_double_sum {κ : Type*} [Fintype κ] (Xt : Matrix O κ ℝ)
    (Om : Matrix O O ℝ) (k l : κ) :
    (Xtᵀ * Om * Xt) k l = ∑ o : O, ∑ o' : O, Xt o k * Xt o' l * Om o o' := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => by ring

omit [StandardBorelSpace Ω] [IsFiniteMeasure P] [DecidableEq O] [DecidableEq D] in
/-- **Lemma SM.B.11(a), second part.** `𝔼[𝓜̃_n ∣ 𝒟] = Ω_n`, entrywise, where
`𝓜̃_n := ∑_{o∼o'} x̃_ox̃_{o'}'ν_oν_{o'}` and `Ω_{oo'} = 𝔼[ν_oν_{o'} ∣ 𝒟]`. The sum extends from
linked pairs to all pairs because the other entries vanish (`hzero`), and `x̃` is
`𝒟`-measurable (`hxt`). -/
theorem condExp_meat_eq_scoreVar (hle : 𝒟 ≤ mΩ) {κ : Type*} {xt : O → κ → Ω → ℝ} {B : ℝ}
    (hxt : ∀ o k, StronglyMeasurable[𝒟] (xt o k)) (hB : ∀ o k ω, |xt o k ω| ≤ B)
    (hint : ∀ o o', Integrable (ν o * ν o') P)
    (hzero : ∀ o o', ¬ Linked c dims o o' → P[ν o * ν o' | 𝒟] =ᵐ[P] 0) (k l : κ) :
    P[fun ω => ∑ p ∈ linkedPairs c dims,
          xt p.1 k ω * xt p.2 l ω * (ν p.1 ω * ν p.2 ω) | 𝒟]
      =ᵐ[P] fun ω => ∑ o : O, ∑ o' : O, xt o k ω * xt o' l ω * (P[ν o * ν o' | 𝒟]) ω := by
  classical
  have hwm : ∀ p : O × O, StronglyMeasurable[𝒟] (xt p.1 k * xt p.2 l) :=
    fun p => (hxt p.1 k).mul (hxt p.2 l)
  have hwg : ∀ p : O × O, Integrable ((xt p.1 k * xt p.2 l) * (ν p.1 * ν p.2)) P := by
    intro p
    have hbd : ∀ᵐ ω ∂P, ‖(xt p.1 k * xt p.2 l) ω‖ ≤ B * B := by
      refine Filter.Eventually.of_forall fun ω => ?_
      have h0 : (0 : ℝ) ≤ B := le_trans (abs_nonneg _) (hB p.1 k ω)
      calc ‖(xt p.1 k * xt p.2 l) ω‖ = |xt p.1 k ω| * |xt p.2 l ω| := by
            rw [Real.norm_eq_abs]; exact abs_mul _ _
        _ ≤ B * B := mul_le_mul (hB _ _ _) (hB _ _ _) (abs_nonneg _) h0
    exact (hint p.1 p.2).bdd_mul ((hwm p).mono hle).aestronglyMeasurable hbd
  have key : (fun ω => ∑ p ∈ linkedPairs c dims,
        xt p.1 k ω * xt p.2 l ω * (ν p.1 ω * ν p.2 ω))
      = ∑ p ∈ linkedPairs c dims, ((xt p.1 k * xt p.2 l) * (ν p.1 * ν p.2)) := by
    funext ω; rw [Finset.sum_apply]; rfl
  rw [key]
  have step1 := condExp_finsetSum (μ := P) (s := linkedPairs c dims)
    (f := fun p => (xt p.1 k * xt p.2 l) * (ν p.1 * ν p.2)) (fun p _ => hwg p) 𝒟
  have step2 : ∀ᵐ ω ∂P, ∀ p : O × O,
      (P[(xt p.1 k * xt p.2 l) * (ν p.1 * ν p.2) | 𝒟]) ω
        = xt p.1 k ω * xt p.2 l ω * (P[ν p.1 * ν p.2 | 𝒟]) ω := by
    rw [ae_all_iff]
    intro p
    filter_upwards [condExp_mul_of_stronglyMeasurable_left (hwm p) (hwg p) (hint p.1 p.2)]
      with ω hω
    rw [hω]; rfl
  have hz : ∀ᵐ ω ∂P, ∀ o o' : O, ¬ Linked c dims o o' → (P[ν o * ν o' | 𝒟]) ω = 0 := by
    rw [ae_all_iff]; intro o; rw [ae_all_iff]; intro o'
    by_cases h : Linked c dims o o'
    · exact Filter.Eventually.of_forall fun ω hcon => absurd h hcon
    · filter_upwards [hzero o o' h] with ω hω _; exact hω
  filter_upwards [step1, step2, hz] with ω h1 h2 h3
  rw [h1, Finset.sum_apply]
  rw [Finset.sum_congr rfl (fun p _ => h2 p)]
  exact (sum_eq_sum_over_linkedPairs c dims (fun o o' => (P[ν o * ν o' | 𝒟]) ω)
    (fun o o' => xt o k ω * xt o' l ω) (fun o o' h => h3 o o' h)).symm

end ClauseA

/-! ### Proposition SM.D.3(c)(ii): the cluster-shock model satisfies Regime 3 -/

section ClusterShockRegime3

open MeasureTheory ProbabilityTheory MeasurableSpace

variable [DecidableEq D] [DecidableEq L]

/-- The shocks that the block `S` depends on, as indices in one family: `Sum.inl (j,g)` is the
cluster shock `c^{(j)}_g`, and `Sum.inr o` is `ε_o`. -/
def shockSet (c : D → O → L) (dims : Finset D) (S : Finset O) : Set ((D × L) ⊕ O) :=
  Sum.inl '' (shockIdx c dims S : Set (D × L)) ∪ Sum.inr '' (S : Set O)

theorem mem_shockSet_inl {c : D → O → L} {dims : Finset D} {S : Finset O} {j : D} (hj : j ∈ dims)
    {o : O} (ho : o ∈ S) : Sum.inl (j, c j o) ∈ shockSet c dims S := by
  refine Set.mem_union_left _ ⟨(j, c j o), ?_, rfl⟩
  simp only [Finset.mem_coe, shockIdx, Finset.mem_biUnion]
  exact ⟨j, hj, Finset.mem_image_of_mem _ ho⟩

theorem mem_shockSet_inr {c : D → O → L} {dims : Finset D} {S : Finset O} {o : O} (ho : o ∈ S) :
    Sum.inr o ∈ shockSet c dims S :=
  Set.mem_union_right _ ⟨o, ho, rfl⟩

/-- Two blocks that are disjoint and separated depend on disjoint sets of shocks. -/
theorem shockSet_disjoint {c : D → O → L} {dims : Finset D} {S₁ S₂ : Finset O}
    (hdisj : Disjoint S₁ S₂) (hsep : ∀ o ∈ S₁, ∀ o' ∈ S₂, ¬ Linked c dims o o') :
    Disjoint (shockSet c dims S₁) (shockSet c dims S₂) := by
  classical
  have hidx := shockIdx_disjoint hsep
  refine Set.disjoint_left.mpr ?_
  rintro (p | o) h1 h2
  · simp only [shockSet, Set.mem_union, Set.mem_image, Finset.mem_coe] at h1 h2
    obtain ⟨q, hq, hqe⟩ | ⟨q, -, hq⟩ := h1
    · obtain ⟨r, hr, hre⟩ | ⟨r, -, hr⟩ := h2
      · cases hqe
        cases hre
        exact (Finset.disjoint_left.1 hidx hq) hr
      · simp at hr
    · simp at hq
  · simp only [shockSet, Set.mem_union, Set.mem_image, Finset.mem_coe] at h1 h2
    obtain ⟨q, -, hq⟩ | ⟨q, hq, hqe⟩ := h1
    · simp at hq
    · obtain ⟨r, -, hr⟩ | ⟨r, hr, hre⟩ := h2
      · simp at hr
      · cases hqe
        cases hre
        exact (Finset.disjoint_left.1 hdisj hq) hr

variable {Ω : Type*}

/-- `ν_o = ∑_j c^{(j)}_{g^{(j)}(o)} + ε_o` as a random variable, defined through `nuVal`. -/
def nuRV (c : D → O → L) (dims : Finset D) (Z : ((D × L) ⊕ O) → Ω → ℝ) (o : O) : Ω → ℝ :=
  fun ω => nuVal c dims (fun p => Z (Sum.inl p) ω) (fun o => Z (Sum.inr o) ω) o

omit [DecidableEq D] [DecidableEq L] in
/-- The formula for `ν_o`, pointwise. -/
theorem nuRV_apply (c : D → O → L) (dims : Finset D) (Z : ((D × L) ⊕ O) → Ω → ℝ) (o : O)
    (ω : Ω) :
    nuRV c dims Z o ω = (∑ j ∈ dims, Z (Sum.inl (j, c j o)) ω) + Z (Sum.inr o) ω := rfl

/-- `ν_o` is measurable with respect to the σ-algebra generated by the shocks of any block
containing `o`. No measurability of `Z` is needed. -/
theorem comap_nuRV_le [MeasurableSpace Ω] {c : D → O → L} {dims : Finset D}
    {Z : ((D × L) ⊕ O) → Ω → ℝ} {S : Finset O} {o : O} (ho : o ∈ S) :
    MeasurableSpace.comap (nuRV c dims Z o) inferInstance
      ≤ ⨆ s ∈ shockSet c dims S, MeasurableSpace.comap (Z s) inferInstance := by
  have hmem : ∀ s ∈ shockSet c dims S,
      Measurable[⨆ s ∈ shockSet c dims S, MeasurableSpace.comap (Z s) inferInstance] (Z s) := by
    intro s hs
    refine (comap_measurable (Z s)).mono ?_ le_rfl
    exact le_iSup₂ (f := fun (s : (D × L) ⊕ O) (_ : s ∈ shockSet c dims S) =>
      MeasurableSpace.comap (Z s) inferInstance) s hs
  have hmeas : Measurable[⨆ s ∈ shockSet c dims S, MeasurableSpace.comap (Z s) inferInstance]
      (nuRV c dims Z o) := by
    refine Measurable.add ?_ (hmem _ (mem_shockSet_inr ho))
    exact Finset.measurable_sum dims fun j hj => hmem _ (mem_shockSet_inl hj ho)
  exact hmeas.comap_le

/-- **Proposition SM.D.3(c)(ii).** The cluster-shock model satisfies the Regime 3 assumption,
given that the shocks are mutually independent conditionally on `𝒟` (`hind`). -/
theorem regime3_of_clusterShock (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] (h𝒟 : 𝒟 ≤ mΩ) (c : D → O → L) (dims : Finset D)
    {Z : ((D × L) ⊕ O) → Ω → ℝ} {P : Measure Ω} [IsFiniteMeasure P]
    (hZ : ∀ s, Measurable (Z s)) (hind : iCondIndepFun 𝒟 h𝒟 Z P) :
    Regime3 𝒟 h𝒟 c dims (nuRV c dims Z) P := by
  intro S₁ S₂ hdisj hsep
  have hZi : iCondIndep 𝒟 h𝒟 (fun s => MeasurableSpace.comap (Z s) inferInstance) P :=
    (iCondIndepFun_iff_iCondIndep 𝒟 h𝒟 _ Z P).1 hind
  have h := condIndep_iSup_of_disjoint (fun s => (hZ s).comap_le) hZi
    (shockSet_disjoint hdisj hsep)
  refine condIndep_of_condIndep_of_le_left (condIndep_of_condIndep_of_le_right h ?_) ?_
  · exact iSup₂_le fun o ho => comap_nuRV_le (Finset.mem_coe.1 ho)
  · exact iSup₂_le fun o ho => comap_nuRV_le (Finset.mem_coe.1 ho)

omit [DecidableEq D] [DecidableEq L] in
/-- **Proposition SM.D.3(c)(i).** If every component has conditional mean zero (`hz`), then
`𝔼[ν_o ∣ 𝒟] = 0`, by linearity of `condExp`. -/
theorem condExp_nuRV_eq_zero (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (c : D → O → L)
    (dims : Finset D) {Z : ((D × L) ⊕ O) → Ω → ℝ} {P : Measure Ω}
    (hint : ∀ s, Integrable (Z s) P) (hz : ∀ s, P[Z s | 𝒟] =ᵐ[P] 0) (o : O) :
    P[nuRV c dims Z o | 𝒟] =ᵐ[P] 0 := by
  have hfun : nuRV c dims Z o = (∑ j ∈ dims, Z (Sum.inl (j, c j o))) + Z (Sum.inr o) := by
    funext ω
    rw [nuRV_apply, Pi.add_apply, Finset.sum_apply]
  have hsum : Integrable (∑ j ∈ dims, Z (Sum.inl (j, c j o))) P :=
    integrable_finsetSum' _ fun j _ => hint _
  have hall : ∀ᵐ ω ∂P, ∀ j ∈ dims, (P[Z (Sum.inl (j, c j o)) | 𝒟]) ω = 0 :=
    (Finset.eventually_all dims).2 fun j _ => hz (Sum.inl (j, c j o))
  rw [hfun]
  filter_upwards [condExp_add hsum (hint _) 𝒟,
    condExp_finsetSum (μ := P) (s := dims) (f := fun j => Z (Sum.inl (j, c j o)))
      (fun j _ => hint _) 𝒟, hall, hz (Sum.inr o)] with ω h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, Finset.sum_apply,
    Finset.sum_congr rfl (fun j hj => h3 j hj), Finset.sum_const_zero, h4]
  simp

end ClusterShockRegime3

/-! ### Proposition SM.D.3(c): the covariance identification

The conditional covariance matrix of the cluster-shock model is `clusterOmega`. The product
`ν_oν_{o'}` expands over pairs of shocks; pairs of distinct shocks have zero conditional mean
(`condExp_shock_mul_eq_zero`), and the surviving terms give `Sh^{(j)}` and the diagonal. -/

section ClusterShockOmega

open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped MatrixOrder
open Matrix

variable [DecidableEq D] [DecidableEq L]
variable {Ω : Type*} {𝒟 mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {h𝒟 : 𝒟 ≤ mΩ}
  {P : Measure Ω} [IsFiniteMeasure P]

/-- For distinct members of a conditionally independent, conditionally centred family,
`𝔼[Z_sZ_t ∣ 𝒟] = 0`. -/
theorem condExp_shock_mul_eq_zero {ι : Type*} {Z : ι → Ω → ℝ}
    (hZ : ∀ s, Measurable (Z s)) (hL2 : ∀ s, MemLp (Z s) 2 P)
    (hind : iCondIndepFun 𝒟 h𝒟 Z P) (hmean : ∀ s, P[Z s | 𝒟] =ᵐ[P] 0)
    {s t : ι} (hst : s ≠ t) :
    P[Z s * Z t | 𝒟] =ᵐ[P] 0 := by
  have h := condExp_mul_of_condIndepFun (hZ s) (hZ t) ((hL2 s).integrable one_le_two)
    ((hL2 t).integrable one_le_two) ((hL2 s).integrable_mul (hL2 t)) (hind.condIndepFun hst)
  filter_upwards [h, hmean s] with ω hω h0
  simp [hω, h0]

/-- **Proposition SM.D.3(c)**, the covariance identification entrywise:
`𝔼[ν_oν_{o'} ∣ 𝒟] = ∑_{j : c^{(j)}(o)=c^{(j)}(o')} 𝔼[(c^{(j)}_{g^{(j)}(o)})² ∣ 𝒟] + 𝟙{o=o'}𝔼[ε_o² ∣ 𝒟]`. -/
theorem condExp_nuRV_mul_nuRV [DecidableEq O] {c : D → O → L} {dims : Finset D}
    {Z : ((D × L) ⊕ O) → Ω → ℝ}
    (hZ : ∀ s, Measurable (Z s)) (hL2 : ∀ s, MemLp (Z s) 2 P)
    (hind : iCondIndepFun 𝒟 h𝒟 Z P) (hmean : ∀ s, P[Z s | 𝒟] =ᵐ[P] 0)
    (o o' : O) :
    P[nuRV c dims Z o * nuRV c dims Z o' | 𝒟]
      =ᵐ[P] fun ω =>
        (∑ j ∈ dims, if c j o = c j o'
            then (P[Z (Sum.inl (j, c j o)) * Z (Sum.inl (j, c j o)) | 𝒟]) ω else 0)
          + (if o = o' then (P[Z (Sum.inr o) * Z (Sum.inr o) | 𝒟]) ω else 0) := by
  classical
  have hint2 : ∀ s t : (D × L) ⊕ O, Integrable (Z s * Z t) P :=
    fun s t => (hL2 s).integrable_mul (hL2 t)
  -- expand the product into four blocks
  have hexp : nuRV c dims Z o * nuRV c dims Z o'
      = (∑ j ∈ dims, ∑ j' ∈ dims, Z (Sum.inl (j, c j o)) * Z (Sum.inl (j', c j' o')))
        + ((∑ j ∈ dims, Z (Sum.inl (j, c j o)) * Z (Sum.inr o'))
          + ((∑ j' ∈ dims, Z (Sum.inr o) * Z (Sum.inl (j', c j' o')))
            + Z (Sum.inr o) * Z (Sum.inr o'))) := by
    funext ω
    simp only [Pi.mul_apply, Pi.add_apply, Finset.sum_apply, nuRV_apply]
    rw [← Finset.sum_mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have hIrow : ∀ j : D,
      Integrable (∑ j' ∈ dims, Z (Sum.inl (j, c j o)) * Z (Sum.inl (j', c j' o'))) P :=
    fun j => integrable_finsetSum' _ fun j' _ => hint2 _ _
  have hI1 : Integrable (∑ j ∈ dims, ∑ j' ∈ dims,
      Z (Sum.inl (j, c j o)) * Z (Sum.inl (j', c j' o'))) P :=
    integrable_finsetSum' _ fun j _ => hIrow j
  have hI2 : Integrable (∑ j ∈ dims, Z (Sum.inl (j, c j o)) * Z (Sum.inr o')) P :=
    integrable_finsetSum' _ fun j _ => hint2 _ _
  have hI3 : Integrable (∑ j' ∈ dims, Z (Sum.inr o) * Z (Sum.inl (j', c j' o'))) P :=
    integrable_finsetSum' _ fun j' _ => hint2 _ _
  have hI4 : Integrable (Z (Sum.inr o) * Z (Sum.inr o')) P := hint2 _ _
  -- block 1: the cluster-shock double sum collapses to its diagonal
  have hA : P[∑ j ∈ dims, ∑ j' ∈ dims,
        Z (Sum.inl (j, c j o)) * Z (Sum.inl (j', c j' o')) | 𝒟]
      =ᵐ[P] fun ω => ∑ j ∈ dims, if c j o = c j o'
          then (P[Z (Sum.inl (j, c j o)) * Z (Sum.inl (j, c j o)) | 𝒟]) ω else 0 := by
    have hrow : ∀ᵐ ω ∂P, ∀ j ∈ dims,
        (P[∑ j' ∈ dims, Z (Sum.inl (j, c j o)) * Z (Sum.inl (j', c j' o')) | 𝒟]) ω
          = if c j o = c j o'
              then (P[Z (Sum.inl (j, c j o)) * Z (Sum.inl (j, c j o)) | 𝒟]) ω else 0 := by
      refine (Finset.eventually_all (I := dims)).2 fun j hj => ?_
      have hterm : ∀ᵐ ω ∂P, ∀ j' ∈ dims,
          (P[Z (Sum.inl (j, c j o)) * Z (Sum.inl (j', c j' o')) | 𝒟]) ω
            = if j' = j then (if c j o = c j o'
                then (P[Z (Sum.inl (j, c j o)) * Z (Sum.inl (j, c j o)) | 𝒟]) ω else 0)
              else 0 := by
        refine (Finset.eventually_all (I := dims)).2 fun j' _ => ?_
        by_cases hmatch : (Sum.inl (j, c j o) : (D × L) ⊕ O) = Sum.inl (j', c j' o')
        · have hje : j = j' ∧ c j o = c j' o' := by simpa using hmatch
          obtain ⟨rfl, he⟩ := hje
          refine Filter.Eventually.of_forall fun ω => ?_
          rw [ite_eq_left rfl, ite_eq_left he, ← he]
        · filter_upwards [condExp_shock_mul_eq_zero hZ hL2 hind hmean hmatch] with ω hω
          rw [hω]
          by_cases hjj : j' = j
          · subst hjj
            have hc : ¬ c j' o = c j' o' := fun h => hmatch (by rw [h])
            rw [ite_eq_left rfl, ite_eq_right hc]
            rfl
          · rw [ite_eq_right hjj]
            rfl
      filter_upwards [hterm, condExp_finsetSum (μ := P) (s := dims)
        (f := fun j' => Z (Sum.inl (j, c j o)) * Z (Sum.inl (j', c j' o')))
        (fun j' _ => hint2 _ _) 𝒟] with ω h1 h2
      rw [h2, Finset.sum_apply, Finset.sum_congr rfl (fun j' hj' => h1 j' hj'),
        Finset.sum_eq_single_of_mem j hj (fun j' _ hne => ite_eq_right hne), ite_eq_left rfl]
    filter_upwards [hrow, condExp_finsetSum (μ := P) (s := dims)
      (f := fun j => ∑ j' ∈ dims, Z (Sum.inl (j, c j o)) * Z (Sum.inl (j', c j' o')))
      (fun j _ => hIrow j) 𝒟] with ω h1 h2
    rw [h2, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j hj => h1 j hj
  -- blocks 2 and 3: cluster shock times idiosyncratic term
  have hB : P[∑ j ∈ dims, Z (Sum.inl (j, c j o)) * Z (Sum.inr o') | 𝒟] =ᵐ[P] 0 := by
    have hz : ∀ᵐ ω ∂P, ∀ j ∈ dims,
        (P[Z (Sum.inl (j, c j o)) * Z (Sum.inr o') | 𝒟]) ω = 0 := by
      refine (Finset.eventually_all (I := dims)).2 fun j _ => ?_
      filter_upwards [condExp_shock_mul_eq_zero hZ hL2 hind hmean
        (s := (Sum.inl (j, c j o) : (D × L) ⊕ O)) (t := Sum.inr o') (by simp)] with ω hω
      exact hω
    filter_upwards [hz, condExp_finsetSum (μ := P) (s := dims)
      (f := fun j => Z (Sum.inl (j, c j o)) * Z (Sum.inr o'))
      (fun j _ => hint2 _ _) 𝒟] with ω h1 h2
    rw [h2, Finset.sum_apply, Finset.sum_congr rfl (fun j hj => h1 j hj)]
    simp
  have hC : P[∑ j' ∈ dims, Z (Sum.inr o) * Z (Sum.inl (j', c j' o')) | 𝒟] =ᵐ[P] 0 := by
    have hz : ∀ᵐ ω ∂P, ∀ j' ∈ dims,
        (P[Z (Sum.inr o) * Z (Sum.inl (j', c j' o')) | 𝒟]) ω = 0 := by
      refine (Finset.eventually_all (I := dims)).2 fun j' _ => ?_
      filter_upwards [condExp_shock_mul_eq_zero hZ hL2 hind hmean
        (s := (Sum.inr o : (D × L) ⊕ O)) (t := Sum.inl (j', c j' o')) (by simp)] with ω hω
      exact hω
    filter_upwards [hz, condExp_finsetSum (μ := P) (s := dims)
      (f := fun j' => Z (Sum.inr o) * Z (Sum.inl (j', c j' o')))
      (fun j' _ => hint2 _ _) 𝒟] with ω h1 h2
    rw [h2, Finset.sum_apply, Finset.sum_congr rfl (fun j' hj' => h1 j' hj')]
    simp
  -- block 4: the idiosyncratic diagonal
  have hD : P[Z (Sum.inr o) * Z (Sum.inr o') | 𝒟]
      =ᵐ[P] fun ω => if o = o' then (P[Z (Sum.inr o) * Z (Sum.inr o) | 𝒟]) ω else 0 := by
    by_cases hoo : o = o'
    · subst hoo
      exact Filter.Eventually.of_forall fun ω => by simp
    · filter_upwards [condExp_shock_mul_eq_zero hZ hL2 hind hmean
        (s := (Sum.inr o : (D × L) ⊕ O)) (t := Sum.inr o') (by simpa using hoo)] with ω hω
      rw [hω, ite_eq_right hoo]
      rfl
  rw [hexp]
  filter_upwards [condExp_add hI1 (hI2.add (hI3.add hI4)) 𝒟,
    condExp_add hI2 (hI3.add hI4) 𝒟, condExp_add hI3 hI4 𝒟, hA, hB, hC, hD]
    with ω e1 e2 e3 eA eB eC eD
  rw [e1, Pi.add_apply, eA, e2, Pi.add_apply, eB, e3, Pi.add_apply, eC, eD]
  simp

/-- **Proposition SM.D.3(c)**, the covariance identification as a matrix: almost surely, the
conditional covariance matrix of the cluster-shock model is
`Ω = ∑_j σ²_{c,j}Sh^{(j)} + diag(Var(ε_o ∣ 𝒟))`, given `Var(c^{(j)}_g ∣ 𝒟) = σ²_{c,j}` (`hsc`). -/
theorem condOmega_eq_clusterOmega [Fintype O] [DecidableEq O] {c : D → O → L} {dims : Finset D}
    {Z : ((D × L) ⊕ O) → Ω → ℝ} {sc : D → ℝ}
    (hZ : ∀ s, Measurable (Z s)) (hL2 : ∀ s, MemLp (Z s) 2 P)
    (hind : iCondIndepFun 𝒟 h𝒟 Z P) (hmean : ∀ s, P[Z s | 𝒟] =ᵐ[P] 0)
    (hsc : ∀ j ∈ dims, ∀ g : L,
      P[Z (Sum.inl (j, g)) * Z (Sum.inl (j, g)) | 𝒟] =ᵐ[P] fun _ => sc j) :
    ∀ᵐ ω ∂P, (Matrix.of fun o o' => (P[nuRV c dims Z o * nuRV c dims Z o' | 𝒟]) ω)
      = clusterOmega c dims sc (fun o => (P[Z (Sum.inr o) * Z (Sum.inr o) | 𝒟]) ω) := by
  classical
  have hall : ∀ᵐ ω ∂P, ∀ o : O, ∀ o' : O,
      (P[nuRV c dims Z o * nuRV c dims Z o' | 𝒟]) ω
        = (∑ j ∈ dims, if c j o = c j o'
            then (P[Z (Sum.inl (j, c j o)) * Z (Sum.inl (j, c j o)) | 𝒟]) ω else 0)
          + (if o = o' then (P[Z (Sum.inr o) * Z (Sum.inr o) | 𝒟]) ω else 0) := by
    rw [ae_all_iff]
    intro o
    rw [ae_all_iff]
    intro o'
    exact condExp_nuRV_mul_nuRV hZ hL2 hind hmean o o'
  have hvar : ∀ᵐ ω ∂P, ∀ o : O, ∀ j ∈ dims,
      (P[Z (Sum.inl (j, c j o)) * Z (Sum.inl (j, c j o)) | 𝒟]) ω = sc j := by
    rw [ae_all_iff]
    intro o
    exact (Finset.eventually_all (I := dims)).2 fun j hj => hsc j hj (c j o)
  filter_upwards [hall, hvar] with ω h1 h2
  ext o o'
  rw [Matrix.of_apply, h1 o o', clusterOmega_apply]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  by_cases hs : SameOn c {j} o o'
  · rw [ite_eq_left (hs j (Finset.mem_singleton_self j)), ite_eq_left hs, h2 o j hj]
  · have hc : ¬ c j o = c j o' := by
      intro h
      exact hs fun k hk => by rw [Finset.mem_singleton] at hk; subst hk; exact h
    rw [ite_eq_right hc, ite_eq_right hs]

omit [DecidableEq D] [DecidableEq L] [StandardBorelSpace Ω] [IsFiniteMeasure P] in
/-- `σ²_{c,j} ≥ 0` follows from `hsc`, for a nonzero measure. -/
theorem sc_nonneg_of_condExp_sq [Nonempty O] {c : D → O → L} {dims : Finset D}
    {Z : ((D × L) ⊕ O) → Ω → ℝ} {sc : D → ℝ} (hP : P ≠ 0)
    (hsc : ∀ j ∈ dims, ∀ g : L,
      P[Z (Sum.inl (j, g)) * Z (Sum.inl (j, g)) | 𝒟] =ᵐ[P] fun _ => sc j)
    {j : D} (hj : j ∈ dims) : 0 ≤ sc j := by
  obtain ⟨o⟩ := ‹Nonempty O›
  have hne : (MeasureTheory.ae P).NeBot := MeasureTheory.ae_neBot.2 hP
  have hnn : (0 : Ω → ℝ) ≤ᵐ[P] P[Z (Sum.inl (j, c j o)) * Z (Sum.inl (j, c j o)) | 𝒟] :=
    condExp_nonneg (Filter.Eventually.of_forall fun ω => mul_self_nonneg _)
  have hcomb : ∀ᵐ _ω ∂P, (0 : ℝ) ≤ sc j := by
    filter_upwards [hnn, hsc j hj (c j o)] with ω h1 h2
    rw [h2] at h1
    exact h1
  exact Filter.eventually_const.mp hcomb

/-- **Proposition SM.D.3(c)**: the conditional covariance matrix satisfies `Ω ⪰ σ²I_n`, given
`𝔼[ε_o² ∣ 𝒟] ≥ σ²` (`hve`). -/
theorem smul_one_le_condOmega [Fintype O] [DecidableEq O] [Nonempty O] {c : D → O → L}
    {dims : Finset D} {Z : ((D × L) ⊕ O) → Ω → ℝ} {sc : D → ℝ} {s2 : ℝ} (hP : P ≠ 0)
    (hZ : ∀ s, Measurable (Z s)) (hL2 : ∀ s, MemLp (Z s) 2 P)
    (hind : iCondIndepFun 𝒟 h𝒟 Z P) (hmean : ∀ s, P[Z s | 𝒟] =ᵐ[P] 0)
    (hsc : ∀ j ∈ dims, ∀ g : L,
      P[Z (Sum.inl (j, g)) * Z (Sum.inl (j, g)) | 𝒟] =ᵐ[P] fun _ => sc j)
    (hve : ∀ o : O, ∀ᵐ ω ∂P, s2 ≤ (P[Z (Sum.inr o) * Z (Sum.inr o) | 𝒟]) ω) :
    ∀ᵐ ω ∂P, s2 • (1 : Matrix O O ℝ)
      ≤ (Matrix.of fun o o' => (P[nuRV c dims Z o * nuRV c dims Z o' | 𝒟]) ω) := by
  have hsc0 : ∀ j ∈ dims, 0 ≤ sc j := fun j hj =>
    sc_nonneg_of_condExp_sq (c := c) hP hsc hj
  have hveall : ∀ᵐ ω ∂P, ∀ o : O, s2 ≤ (P[Z (Sum.inr o) * Z (Sum.inr o) | 𝒟]) ω := by
    rw [ae_all_iff]
    exact hve
  filter_upwards [condOmega_eq_clusterOmega hZ hL2 hind hmean hsc, hveall] with ω h1 h2
  rw [h1]
  exact smul_one_le_clusterOmega hsc0 h2

/-- In the cluster-shock model, `𝔼[ν_oν_{o'} ∣ 𝒟] = 0` whenever `o ≁ o'`, for `J ≥ 1`. -/
theorem condOmega_eq_zero_of_not_linked [Fintype O] [DecidableEq O] {c : D → O → L}
    {dims : Finset D} (hdims : dims.Nonempty) {Z : ((D × L) ⊕ O) → Ω → ℝ} {sc : D → ℝ}
    (hZ : ∀ s, Measurable (Z s)) (hL2 : ∀ s, MemLp (Z s) 2 P)
    (hind : iCondIndepFun 𝒟 h𝒟 Z P) (hmean : ∀ s, P[Z s | 𝒟] =ᵐ[P] 0)
    (hsc : ∀ j ∈ dims, ∀ g : L,
      P[Z (Sum.inl (j, g)) * Z (Sum.inl (j, g)) | 𝒟] =ᵐ[P] fun _ => sc j) :
    ∀ᵐ ω ∂P, ∀ o o' : O, ¬ Linked c dims o o' →
      (P[nuRV c dims Z o * nuRV c dims Z o' | 𝒟]) ω = 0 := by
  filter_upwards [condOmega_eq_clusterOmega hZ hL2 hind hmean hsc] with ω h1 o o' hsep
  have h2 : (Matrix.of fun o o' => (P[nuRV c dims Z o * nuRV c dims Z o' | 𝒟]) ω) o o'
      = clusterOmega c dims sc (fun o => (P[Z (Sum.inr o) * Z (Sum.inr o) | 𝒟]) ω) o o' := by
    rw [h1]
  rw [Matrix.of_apply] at h2
  rw [h2]
  exact clusterOmega_eq_zero_of_not_linked hdims hsep

end ClusterShockOmega

/-! ### Witnesses for Regime 3

These use the second model `witC2`, which has a non-adjacent pair, and the point-mass model
`Multiway.CondFactor.iCondIndepFun_bot_dirac`. -/

section Witness3

open MeasureTheory ProbabilityTheory MeasurableSpace

/-- The witness shock family on `ℝ`: every shock is the identity. -/
def witZ : ((WitD × WitO) ⊕ WitO) → ℝ → ℝ := fun _ ω => ω

/-- In the witness model, `ν_o = 2ω`. -/
theorem witZ_nuRV_apply (ω : ℝ) (o : WitO) : nuRV witC2 witDims witZ o ω = ω + ω := by
  rw [nuRV_apply]
  simp [witZ, witDims]

/-- Witness for `regime3_of_clusterShock`. -/
theorem witness_regime3_clusterShock (ω₀ : ℝ) :
    Regime3 (⊥ : MeasurableSpace ℝ) bot_le witC2 witDims
      (nuRV witC2 witDims witZ) (Measure.dirac ω₀) :=
  regime3_of_clusterShock ⊥ bot_le witC2 witDims (fun _ => measurable_id)
    (Multiway.CondFactor.iCondIndepFun_bot_dirac ω₀ fun _ => measurable_id)

/-- `Regime3` applied at the non-adjacent pair `0 ≁ 1` of `witC2`, through
`condIndepFun_of_regime3`. -/
theorem witness_regime3_separated (ω₀ : ℝ) :
    CondIndepFun (⊥ : MeasurableSpace ℝ) bot_le
      (nuRV witC2 witDims witZ (0 : WitO)) (nuRV witC2 witDims witZ (1 : WitO))
      (Measure.dirac ω₀) :=
  condIndepFun_of_regime3 (witness_regime3_clusterShock ω₀) (by decide) witNotLinked

end Witness3

/-! ### Witnesses for clause (a) on a Gaussian model

Two observations under a product of two standard Gaussians, with `ν_o` the `o`-th coordinate and
`witC2` giving each observation its own cluster. The diagonal entry `𝔼[ν_0ν_0 ∣ 𝒟] = 1` is
nonzero. -/

section WitnessGaussian

open MeasureTheory ProbabilityTheory MeasurableSpace

/-- The sample space: one standard Gaussian coordinate per observation. -/
abbrev WitGΩ := WitO → ℝ

/-- A product of two standard Gaussians. -/
noncomputable def witGP : Measure WitGΩ := Measure.pi fun _ : WitO => gaussianReal 0 1

instance : IsProbabilityMeasure witGP := by
  unfold witGP; infer_instance

/-- `ν_o` is the `o`-th coordinate. -/
def witGNu : WitO → WitGΩ → ℝ := fun o ω => ω o

theorem witGNu_measurable (o : WitO) : Measurable (witGNu o) := measurable_pi_apply o

/-- Each coordinate is standard Gaussian. -/
theorem witGP_map_eval (o : WitO) : witGP.map (fun ω : WitGΩ => ω o) = gaussianReal 0 1 :=
  (MeasureTheory.measurePreserving_eval (fun _ : WitO => gaussianReal 0 1) o).map_eq

theorem witGNu_memLp (o : WitO) : MemLp (witGNu o) 2 witGP := by
  have h : MemLp (id : ℝ → ℝ) 2 (witGP.map (fun ω : WitGΩ => ω o)) := by
    rw [witGP_map_eval o]; exact memLp_id_gaussianReal' 2 (by simp)
  exact (memLp_map_measure_iff aestronglyMeasurable_id
    (measurable_pi_apply o).aemeasurable).1 h

theorem witGNu_integral (o : WitO) : ∫ ω, witGNu o ω ∂witGP = 0 := by
  have h := integral_map (μ := witGP) (φ := fun ω : WitGΩ => ω o) (f := fun y : ℝ => y)
    (measurable_pi_apply o).aemeasurable aestronglyMeasurable_id
  rw [witGP_map_eval o] at h
  rw [show (∫ ω, witGNu o ω ∂witGP) = ∫ ω : WitGΩ, ω o ∂witGP from rfl, ← h,
    integral_id_gaussianReal]

/-- The second moment of a standard Gaussian is `1`. -/
theorem integral_sq_gaussianReal_one : ∫ x : ℝ, x * x ∂(gaussianReal 0 1) = 1 := by
  have hL : MemLp (fun x : ℝ => x) 2 (gaussianReal 0 1) := memLp_id_gaussianReal' 2 (by simp)
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_sub hL] at hv
  simp only [integral_id_gaussianReal] at hv
  simp only [pow_two] at hv ⊢
  simpa using hv

theorem witGNu_sq_integral (o : WitO) : ∫ ω, witGNu o ω * witGNu o ω ∂witGP = 1 := by
  have h := integral_map (μ := witGP) (φ := fun ω : WitGΩ => ω o) (f := fun y : ℝ => y * y)
    (measurable_pi_apply o).aemeasurable (by fun_prop)
  rw [witGP_map_eval o] at h
  rw [show (∫ ω, witGNu o ω * witGNu o ω ∂witGP) = ∫ ω : WitGΩ, (ω o) * (ω o) ∂witGP from rfl,
    ← h, integral_sq_gaussianReal_one]

/-- Conditional mean zero in the Gaussian model. -/
theorem witG_exog (o : WitO) : witGP[witGNu o | (⊥ : MeasurableSpace WitGΩ)] =ᵐ[witGP] 0 := by
  rw [condExp_bot]
  simp [witGNu_integral o]
  rfl

/-- The Regime 3 assumption in the Gaussian model, from independence of the coordinates. -/
theorem witG_regime3 :
    Regime3 (⊥ : MeasurableSpace WitGΩ) bot_le witC2 witDims witGNu witGP :=
  regime3_of_iCondIndepFun ⊥ bot_le witC2 witDims witGNu_measurable
    (iCondIndepFun_bot_of_iIndepFun witGNu_measurable
      (iIndepFun_pi (X := fun _ : WitO => (id : ℝ → ℝ)) fun _ => aemeasurable_id))

theorem witG_integrable (o o' : WitO) : Integrable (witGNu o * witGNu o') witGP :=
  (witGNu_memLp o).integrable_mul (witGNu_memLp o')

/-- Witness for `condCov_eq_zero_of_not_linked`, at the non-adjacent pair `0 ≁ 1`. -/
theorem witness_condCov_eq_zero :
    witGP[witGNu 0 * witGNu 1 | (⊥ : MeasurableSpace WitGΩ)] =ᵐ[witGP] 0 :=
  condCov_eq_zero_of_not_linked Finset.univ_nonempty witG_regime3 witGNu_measurable
    witGNu_memLp witG_exog witNotLinked

theorem witG_zero (o o' : WitO) (h : ¬ Linked witC2 witDims o o') :
    witGP[witGNu o * witGNu o' | (⊥ : MeasurableSpace WitGΩ)] =ᵐ[witGP] 0 :=
  condCov_eq_zero_of_not_linked Finset.univ_nonempty witG_regime3 witGNu_measurable
    witGNu_memLp witG_exog h

/-- A non-constant within-regressor array for the witness. -/
noncomputable def witGXt : WitO → Fin 1 → WitGΩ → ℝ :=
  fun o _ _ => if o = (0 : WitO) then 2 else 3

/-- Witness for `condExp_meat_eq_scoreVar`. In `witC2` the linked pairs are the two diagonal
ones, so the left-hand side is `4𝔼[ν_0ν_0] + 9𝔼[ν_1ν_1] = 13`. -/
theorem witness_condExp_meat_eq_scoreVar :
    witGP[fun ω => ∑ p ∈ linkedPairs witC2 witDims,
        witGXt p.1 0 ω * witGXt p.2 0 ω * (witGNu p.1 ω * witGNu p.2 ω)
        | (⊥ : MeasurableSpace WitGΩ)]
      =ᵐ[witGP] fun ω => ∑ o : WitO, ∑ o' : WitO, witGXt o 0 ω * witGXt o' 0 ω *
        (witGP[witGNu o * witGNu o' | (⊥ : MeasurableSpace WitGΩ)]) ω :=
  condExp_meat_eq_scoreVar bot_le (xt := witGXt) (B := 3)
    (fun _ _ => stronglyMeasurable_const)
    (fun o _ _ => by unfold witGXt; split <;> norm_num)
    witG_integrable witG_zero 0 0

/-- `Ω_{00} = 𝔼[ν_0ν_0 ∣ 𝒟] = 1` in the Gaussian model. -/
theorem witness_condOmega_diag_eq_one :
    witGP[witGNu 0 * witGNu 0 | (⊥ : MeasurableSpace WitGΩ)] =ᵐ[witGP] fun _ => 1 := by
  rw [condExp_bot]
  have h : ∫ x, witGNu 0 x * witGNu 0 x ∂witGP = 1 := witGNu_sq_integral 0
  simp only [Pi.mul_apply]
  rw [h]

/-- A shock family in which the cluster shock of `o` and its idiosyncratic term are both
coordinate `o`. -/
def witGZ : ((WitD × WitO) ⊕ WitO) → WitGΩ → ℝ :=
  fun s => witGNu (Sum.elim (fun p => p.2) id s)

/-- Witness for `condExp_nuRV_eq_zero`. -/
theorem witness_condExp_nuRV_eq_zero (o : WitO) :
    witGP[nuRV witC2 witDims witGZ o | (⊥ : MeasurableSpace WitGΩ)] =ᵐ[witGP] 0 :=
  condExp_nuRV_eq_zero (Z := witGZ) (P := witGP) ⊥ witC2 witDims
    (fun _s => (witGNu_memLp _).integrable one_le_two)
    (fun _s => witG_exog _) o

end WitnessGaussian

/-! ### Witnesses for the covariance identification

These use one independent standard Gaussian coordinate per shock (`witSZ`). -/

section WitnessShocks

open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped MatrixOrder
open Matrix

/-- The sample space: one standard Gaussian coordinate per shock. -/
abbrev WitSΩ := ((WitD × WitO) ⊕ WitO) → ℝ

/-- A product of standard Gaussians. -/
noncomputable def witSP : Measure WitSΩ := Measure.pi fun _ => gaussianReal 0 1

instance : IsProbabilityMeasure witSP := by
  unfold witSP; infer_instance

/-- Shock `s` is coordinate `s`. -/
def witSZ : ((WitD × WitO) ⊕ WitO) → WitSΩ → ℝ := fun s ω => ω s

theorem witSZ_measurable (s : (WitD × WitO) ⊕ WitO) : Measurable (witSZ s) :=
  measurable_pi_apply s

theorem witSP_map_eval (s : (WitD × WitO) ⊕ WitO) :
    witSP.map (fun ω : WitSΩ => ω s) = gaussianReal 0 1 :=
  (MeasureTheory.measurePreserving_eval (fun _ : (WitD × WitO) ⊕ WitO => gaussianReal 0 1) s).map_eq

theorem witSZ_memLp (s : (WitD × WitO) ⊕ WitO) : MemLp (witSZ s) 2 witSP := by
  have h : MemLp (id : ℝ → ℝ) 2 (witSP.map (fun ω : WitSΩ => ω s)) := by
    rw [witSP_map_eval s]; exact memLp_id_gaussianReal' 2 (by simp)
  exact (memLp_map_measure_iff aestronglyMeasurable_id
    (measurable_pi_apply s).aemeasurable).1 h

theorem witSZ_integral (s : (WitD × WitO) ⊕ WitO) : ∫ ω, witSZ s ω ∂witSP = 0 := by
  have h := integral_map (μ := witSP) (φ := fun ω : WitSΩ => ω s) (f := fun y : ℝ => y)
    (measurable_pi_apply s).aemeasurable aestronglyMeasurable_id
  rw [witSP_map_eval s] at h
  rw [show (∫ ω, witSZ s ω ∂witSP) = ∫ ω : WitSΩ, ω s ∂witSP from rfl, ← h,
    integral_id_gaussianReal]

theorem witSZ_sq_integral (s : (WitD × WitO) ⊕ WitO) :
    ∫ ω, witSZ s ω * witSZ s ω ∂witSP = 1 := by
  have h := integral_map (μ := witSP) (φ := fun ω : WitSΩ => ω s) (f := fun y : ℝ => y * y)
    (measurable_pi_apply s).aemeasurable (by fun_prop)
  rw [witSP_map_eval s] at h
  rw [show (∫ ω, witSZ s ω * witSZ s ω ∂witSP) = ∫ ω : WitSΩ, (ω s) * (ω s) ∂witSP from rfl,
    ← h, integral_sq_gaussianReal_one]

/-- Every shock has conditional mean zero. -/
theorem witS_exog (s : (WitD × WitO) ⊕ WitO) :
    witSP[witSZ s | (⊥ : MeasurableSpace WitSΩ)] =ᵐ[witSP] 0 := by
  rw [condExp_bot]
  simp [witSZ_integral s]
  rfl

/-- The shocks are mutually independent conditionally on `𝒟 = ⊥`. -/
theorem witS_indep : iCondIndepFun (⊥ : MeasurableSpace WitSΩ) bot_le witSZ witSP :=
  iCondIndepFun_bot_of_iIndepFun witSZ_measurable
    (iIndepFun_pi (X := fun _ : (WitD × WitO) ⊕ WitO => (id : ℝ → ℝ))
      fun _ => aemeasurable_id)

/-- Every shock has conditional second moment `1`. -/
theorem witS_sq (s : (WitD × WitO) ⊕ WitO) :
    witSP[witSZ s * witSZ s | (⊥ : MeasurableSpace WitSΩ)] =ᵐ[witSP] fun _ => 1 := by
  rw [condExp_bot]
  have h : ∫ x, witSZ s x * witSZ s x ∂witSP = 1 := witSZ_sq_integral s
  simp only [Pi.mul_apply]
  rw [h]

theorem witS_sc : ∀ j ∈ witDims, ∀ g : WitO,
    witSP[witSZ (Sum.inl (j, g)) * witSZ (Sum.inl (j, g)) | (⊥ : MeasurableSpace WitSΩ)]
      =ᵐ[witSP] fun _ => (1 : ℝ) :=
  fun j _ g => witS_sq (Sum.inl (j, g))

/-- Witness for `condOmega_eq_clusterOmega`. -/
theorem witness_condOmega_eq_clusterOmega :
    ∀ᵐ ω ∂witSP, (Matrix.of fun o o' =>
        (witSP[nuRV witC2 witDims witSZ o * nuRV witC2 witDims witSZ o'
          | (⊥ : MeasurableSpace WitSΩ)]) ω)
      = clusterOmega witC2 witDims (fun _ => 1)
          (fun o => (witSP[witSZ (Sum.inr o) * witSZ (Sum.inr o)
            | (⊥ : MeasurableSpace WitSΩ)]) ω) :=
  condOmega_eq_clusterOmega witSZ_measurable witSZ_memLp witS_indep witS_exog witS_sc

/-- The diagonal entry of the conditional covariance matrix is `2`. -/
theorem witness_condOmega_diag_eq_two :
    witSP[nuRV witC2 witDims witSZ 0 * nuRV witC2 witDims witSZ 0
        | (⊥ : MeasurableSpace WitSΩ)] =ᵐ[witSP] fun _ => (2 : ℝ) := by
  filter_upwards [condExp_nuRV_mul_nuRV (c := witC2) (dims := witDims) (Z := witSZ)
      witSZ_measurable witSZ_memLp witS_indep witS_exog (0 : WitO) (0 : WitO),
    witS_sq (Sum.inl ((0 : WitD), (0 : WitO))), witS_sq (Sum.inr (0 : WitO))]
    with ω h1 h2 h3
  rw [h1]
  have hsum : (∑ j ∈ witDims, if witC2 j 0 = witC2 j 0
      then (witSP[witSZ (Sum.inl (j, witC2 j 0)) * witSZ (Sum.inl (j, witC2 j 0))
        | (⊥ : MeasurableSpace WitSΩ)]) ω else 0) = 1 := by
    rw [show witDims = ({0} : Finset WitD) from by decide, Finset.sum_singleton,
      ite_eq_left rfl]
    exact h2
  rw [hsum, ite_eq_left rfl, h3]
  norm_num

/-- `𝔼[ε_o² ∣ 𝒟] ≥ 1` in the witness model. -/
theorem witS_ve (o : WitO) :
    ∀ᵐ ω ∂witSP, (1 : ℝ) ≤ (witSP[witSZ (Sum.inr o) * witSZ (Sum.inr o)
      | (⊥ : MeasurableSpace WitSΩ)]) ω := by
  filter_upwards [witS_sq (Sum.inr o)] with ω hω
  rw [hω]

/-- Witness for `smul_one_le_condOmega`, at `σ² = 1`. -/
theorem witness_smul_one_le_condOmega :
    ∀ᵐ ω ∂witSP, (1 : ℝ) • (1 : Matrix WitO WitO ℝ)
      ≤ (Matrix.of fun o o' => (witSP[nuRV witC2 witDims witSZ o * nuRV witC2 witDims witSZ o'
          | (⊥ : MeasurableSpace WitSΩ)]) ω) :=
  smul_one_le_condOmega (IsProbabilityMeasure.ne_zero witSP) witSZ_measurable witSZ_memLp
    witS_indep witS_exog witS_sc witS_ve

end WitnessShocks

/-! ### Witnesses for Proposition SM.D.3(a) -/

section WitnessThreeSeqA

open Filter MeasureTheory
open scoped Topology MatrixOrder Matrix.Norms.L2Operator
open Matrix

/-- The one-observation, one-regressor design with every matrix the identity. -/
theorem witDesign_herm : (((1 : Matrix (Fin 1) (Fin 1) ℝ))ᵀ * (1 : Matrix (Fin 1) (Fin 1) ℝ)
    * (1 : Matrix (Fin 1) (Fin 1) ℝ)).IsHermitian := by
  simp [Matrix.IsHermitian]

/-- Witness for `eigenvalues_conj_ge_of_design`, at `σ² = 1`, `n = 1`, `λ_0 = 1`, `ε = 1/2`,
giving the lower bound `1/2`. -/
theorem witness_eigenvalues_conj_ge_of_design (i : Fin 1) :
    (1 : ℝ) / 2 ≤ witDesign_herm.eigenvalues i := by
  have h := eigenvalues_conj_ge_of_design (O := Fin 1) (K := Fin 1)
    (Om := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (s2 := 1) (Xt := (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (H := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (nR := 1) (lam0 := 1) (ε := 1 / 2)
    zero_le_one (by simp) one_pos
    (by simp [Matrix.IsHermitian]) (by simp)
    (by norm_num) witDesign_herm i
  linarith

/-- A design sequence on `ℝ` under a point mass at `0`: `λ_min(Ω_n) = n+1` at the atom and `1`
off it. -/
noncomputable def witLmin (n : ℕ) (ω : ℝ) : ℝ := if ω = 0 then (n : ℝ) + 1 else 1

theorem witLmin_good (n : ℕ) : {ω : ℝ | (1 : ℝ) * ((n : ℝ) + 1) * 1 ≤ witLmin n ω}ᶜ
    ⊆ ({(0 : ℝ)} : Set ℝ)ᶜ := by
  intro ω hω h0
  rw [Set.mem_singleton_iff] at h0
  exact hω (by simp [witLmin, h0])

/-- Witness for `threeseq_a_accum_i`. Off the atom `δ_n = n+1` diverges, so the convergence in
probability is not pointwise. -/
theorem witness_threeseq_a_accum_i :
    TendstoInMeasure (Measure.dirac (0 : ℝ))
      (fun (n : ℕ) (ω : ℝ) => deltaSeq ((n : ℝ) + 1) 1 (witLmin n ω)) atTop
      (fun _ => (0 : ℝ)) := by
  refine threeseq_a_accum_i (J := 1) (s2 := 1) (lam := 1) (G := fun _ => 1)
    (nR := fun n => (n : ℝ) + 1) (Dn := fun _ => 1) (lmin := witLmin)
    (fun n => by positivity) zero_le_one (fun _ => zero_le_one) one_pos one_pos
    (fun _ => zero_le_one) (fun _ => by norm_num) ?_ ?_
  · have hnull : ∀ n : ℕ,
        (Measure.dirac (0 : ℝ)) {ω : ℝ | (1 : ℝ) * ((n : ℝ) + 1) * 1 ≤ witLmin n ω}ᶜ = 0 := by
      intro n
      refine measure_mono_null (witLmin_good n) ?_
      rw [Measure.dirac_apply' _ (measurableSet_singleton (0 : ℝ)).compl]
      simp
    simp only [hnull]
    exact tendsto_const_nhds
  · simp only [one_pow]
    exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- Off the atom, `δ_5 = 6`. -/
theorem witness_deltaSeq_off_event : deltaSeq ((5 : ℕ) + 1) 1 (witLmin 5 1) = 6 := by
  rw [deltaSeq, witLmin]
  norm_num

end WitnessThreeSeqA

end Multiway.Sharing
