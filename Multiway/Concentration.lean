import Mathlib.Basic.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Concentration of the conditional variance

This file formalizes Lemma SM.C.3 of the paper (concentration of the conditional variance).
For components `γ ∈ Γ` with coefficient arrays `V^{(γ)}` and products `π^γ_s` of an orthonormal
system `{ψ_r}` evaluated at independent latent variables, the entries
`X_{γγ'} = ∑_i A^γ_i A^{γ'}_i` satisfy (a) `𝔼[X_{γγ}] = tot(γ)` and `𝔼[X_{γγ'}] = 0` for
`γ ≠ γ'`, and (b) `Var(∑_{γ,γ'} λ_γ λ_{γ'} X_{γγ'}) ≤ C(M, B_0, |Γ|) max_γ cut(γ) max_γ tot(γ)`
when `∑_γ λ_γ² ≤ 1`. Here `tot(γ) = ‖V^{(γ)}‖_F²` and `cut(γ)` is the largest Frobenius norm of
a contraction `V^{(γ)} ⊠_A V^{(γ)}` over proper nonempty `A`. Arrays enter through their
matricizations, which are ordinary rectangular matrices: `V ⊠_A V` is `Fᵀ * F`.

## Main results

* `concentration_clause_a`, `concentration_clause_a_tuples`: clause (a).
* `concentration_clause_b_singleton_uniform`: clause (b) when every level has two dimensions.
* `concentration_clause_b_general_closed_uniform`: clause (b) at general level size, with a
  constant depending only on `M`, `B_0` and `|Γ|`.
-/

namespace Multiway

open Matrix Finset

variable {α β δ : Type*} [Fintype α] [Fintype β] [Fintype δ]

/-! ### The Frobenius norm of a rectangular matricization -/

/-- `‖F‖_F²` for a rectangular matrix; this is `tot(γ)` when `F` is a matricization of
`V^{(γ)}`. -/
def rectFrobSq (F : Matrix α β ℝ) : ℝ := ∑ i, ∑ j, F i j ^ 2

/-- `‖F‖_F` for a rectangular matrix. -/
noncomputable def rectFrobNorm (F : Matrix α β ℝ) : ℝ := Real.sqrt (rectFrobSq F)

theorem rectFrobSq_nonneg (F : Matrix α β ℝ) : 0 ≤ rectFrobSq F :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem rectFrobNorm_nonneg (F : Matrix α β ℝ) : 0 ≤ rectFrobNorm F := Real.sqrt_nonneg _

theorem rectFrobNorm_sq (F : Matrix α β ℝ) : rectFrobNorm F ^ 2 = rectFrobSq F :=
  Real.sq_sqrt (rectFrobSq_nonneg F)

/-- `‖F‖_F ≤ c` squares to `‖F‖_F² ≤ c²`. -/
theorem rectFrobSq_le_sq_of_rectFrobNorm_le (F : Matrix α β ℝ) {c : ℝ}
    (hF : rectFrobNorm F ≤ c) : rectFrobSq F ≤ c ^ 2 := by
  rw [← rectFrobNorm_sq F, sq, sq]
  exact mul_self_le_mul_self (rectFrobNorm_nonneg F) hF

/-- `‖Fᵀ‖_F² = ‖F‖_F²`. -/
theorem rectFrobSq_transpose (F : Matrix α β ℝ) : rectFrobSq Fᵀ = rectFrobSq F := by
  simp only [rectFrobSq, Matrix.transpose_apply]
  exact Finset.sum_comm

/-- `‖F‖_F² = tr(F'F)`. -/
theorem rectFrobSq_eq_trace (F : Matrix α β ℝ) : rectFrobSq F = (Fᵀ * F).trace := by
  simp only [rectFrobSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply, pow_two]
  exact Finset.sum_comm

/-- The squared Frobenius norm is invariant under reindexing rows and columns, so `tot(γ)`
does not depend on the matricization. -/
theorem rectFrobSq_reindex {α' β' : Type*} [Fintype α'] [Fintype β'] (F : Matrix α β ℝ)
    (G : Matrix α' β' ℝ) (e : α × β ≃ α' × β')
    (h : ∀ p : α × β, F p.1 p.2 = G (e p).1 (e p).2) :
    rectFrobSq F = rectFrobSq G := by
  have hF : rectFrobSq F = ∑ p : α × β, F p.1 p.2 ^ 2 := by
    rw [rectFrobSq, Fintype.sum_prod_type]
  have hG : rectFrobSq G = ∑ q : α' × β', G q.1 q.2 ^ 2 := by
    rw [rectFrobSq, Fintype.sum_prod_type]
  rw [hF, hG]
  exact Fintype.sum_equiv e _ _ fun p => by rw [h p]

/-! ### Cauchy--Schwarz in the Frobenius inner product -/

/-- The squared Cauchy--Schwarz inequality for the Frobenius inner product `tr(S'T)`. -/
theorem sq_trace_transpose_mul_le (S T : Matrix α β ℝ) :
    ((Sᵀ * T).trace) ^ 2 ≤ rectFrobSq S * rectFrobSq T := by
  have htr : (Sᵀ * T).trace = ∑ p : α × β, S p.1 p.2 * T p.1 p.2 := by
    rw [Fintype.sum_prod_type]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_comm
  have hS : rectFrobSq S = ∑ p : α × β, S p.1 p.2 ^ 2 := by
    rw [rectFrobSq, Fintype.sum_prod_type]
  have hT : rectFrobSq T = ∑ p : α × β, T p.1 p.2 ^ 2 := by
    rw [rectFrobSq, Fintype.sum_prod_type]
  rw [htr, hS, hT]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _

/-- **Cauchy--Schwarz in the Frobenius inner product**, `|tr(S'T)| ≤ ‖S‖_F ‖T‖_F`. -/
theorem abs_trace_transpose_mul_le (S T : Matrix α β ℝ) :
    |(Sᵀ * T).trace| ≤ rectFrobNorm S * rectFrobNorm T := by
  calc |(Sᵀ * T).trace| = Real.sqrt (((Sᵀ * T).trace) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (rectFrobSq S * rectFrobSq T) :=
        Real.sqrt_le_sqrt (sq_trace_transpose_mul_le S T)
    _ = rectFrobNorm S * rectFrobNorm T := by
        rw [rectFrobNorm, rectFrobNorm, Real.sqrt_mul (rectFrobSq_nonneg S)]

/-! ### Symmetry of the contraction norm -/

/-- `‖F F'‖_F² = ‖F' F‖_F²`, by cyclicity of the trace. -/
theorem rectFrobSq_mul_transpose_comm (F : Matrix α β ℝ) :
    rectFrobSq (F * Fᵀ) = rectFrobSq (Fᵀ * F) := by
  rw [rectFrobSq_eq_trace, rectFrobSq_eq_trace]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [show F * Fᵀ * (F * Fᵀ) = F * (Fᵀ * F * Fᵀ) by simp [Matrix.mul_assoc],
    Matrix.trace_mul_comm,
    show Fᵀ * F * Fᵀ * F = Fᵀ * F * (Fᵀ * F) by simp [Matrix.mul_assoc]]

/-- `‖V ⊠_A V‖_F = ‖V ⊠_{e ∖ A} V‖_F`, i.e. `‖F F'‖_F = ‖F' F‖_F`. -/
theorem rectFrobNorm_mul_transpose_comm (F : Matrix α β ℝ) :
    rectFrobNorm (F * Fᵀ) = rectFrobNorm (Fᵀ * F) := by
  rw [rectFrobNorm, rectFrobNorm, rectFrobSq_mul_transpose_comm]

/-! ### `‖V ⊠_A V‖_F ≤ ‖V‖_F²`, hence `cut(γ) ≤ tot(γ)` -/

theorem rectFrobSq_transpose_mul_self_le (F : Matrix α β ℝ) :
    rectFrobSq (Fᵀ * F) ≤ rectFrobSq F ^ 2 := by
  have hcol : ∀ j : β, (0:ℝ) ≤ ∑ k : α, F k j ^ 2 :=
    fun j => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hstep : ∀ i : β, ∀ j : β,
      ((Fᵀ * F) i j) ^ 2 ≤ (∑ k : α, F k i ^ 2) * (∑ k : α, F k j ^ 2) := by
    intro i j
    have : (Fᵀ * F) i j = ∑ k : α, F k i * F k j := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
    rw [this]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hsum : rectFrobSq (Fᵀ * F)
      ≤ ∑ i : β, ∑ j : β, (∑ k : α, F k i ^ 2) * (∑ k : α, F k j ^ 2) := by
    rw [rectFrobSq]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hstep i j
  have hfact : ∑ i : β, ∑ j : β, (∑ k : α, F k i ^ 2) * (∑ k : α, F k j ^ 2)
      = (∑ i : β, ∑ k : α, F k i ^ 2) * (∑ j : β, ∑ k : α, F k j ^ 2) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
  have hcomm : ∑ i : β, ∑ k : α, F k i ^ 2 = rectFrobSq F := by
    rw [rectFrobSq]
    exact Finset.sum_comm
  rw [hfact, hcomm] at hsum
  calc rectFrobSq (Fᵀ * F) ≤ rectFrobSq F * rectFrobSq F := hsum
    _ = rectFrobSq F ^ 2 := by ring

/-- `‖V ⊠_A V‖_F ≤ ‖V‖_F² = tot(γ)`; over proper nonempty `A` this gives
`cut(γ) ≤ tot(γ)`. -/
theorem rectFrobNorm_transpose_mul_self_le (F : Matrix α β ℝ) :
    rectFrobNorm (Fᵀ * F) ≤ rectFrobSq F := by
  rw [rectFrobNorm]
  calc Real.sqrt (rectFrobSq (Fᵀ * F)) ≤ Real.sqrt (rectFrobSq F ^ 2) :=
        Real.sqrt_le_sqrt (rectFrobSq_transpose_mul_self_le F)
    _ = rectFrobSq F := Real.sqrt_sq (rectFrobSq_nonneg F)

/-- The same bound for the other orientation of the contraction, `V ⊠_{e ∖ A} V`. -/
theorem rectFrobNorm_mul_transpose_self_le (F : Matrix α β ℝ) :
    rectFrobNorm (F * Fᵀ) ≤ rectFrobSq F := by
  rw [rectFrobNorm_mul_transpose_comm]
  exact rectFrobNorm_transpose_mul_self_le F

/-! ### Diagonal entries of a Gram matrix -/

/-- The sum of the squared diagonal entries of a square matrix is at most its squared
Frobenius norm. -/
theorem sum_sq_diag_le_rectFrobSq (S : Matrix α α ℝ) :
    ∑ i, (S i i) ^ 2 ≤ rectFrobSq S := by
  rw [rectFrobSq]
  refine Finset.sum_le_sum fun i _ => ?_
  exact Finset.single_le_sum (f := fun j => S i j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

/-! ### The trace bound for a cross-Gram matrix -/

/-- With `H = (F^γ_A)' F^{γ'}_A`, whose factors share a row index set,
`‖H‖_F² = tr(F^γ_A (F^γ_A)' F^{γ'}_A (F^{γ'}_A)')
  ≤ ‖V^{(γ)} ⊠_A V^{(γ)}‖_F ‖V^{(γ')} ⊠_A V^{(γ')}‖_F`. -/
theorem rectFrobSq_transpose_mul_le (F : Matrix α β ℝ) (G : Matrix α δ ℝ) :
    rectFrobSq (Fᵀ * G) ≤ rectFrobNorm (F * Fᵀ) * rectFrobNorm (G * Gᵀ) := by
  have hid : rectFrobSq (Fᵀ * G) = ((F * Fᵀ)ᵀ * (G * Gᵀ)).trace := by
    rw [rectFrobSq_eq_trace]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [show Gᵀ * F * (Fᵀ * G) = Gᵀ * (F * Fᵀ * G) by simp [Matrix.mul_assoc],
      Matrix.trace_mul_comm,
      show F * Fᵀ * G * Gᵀ = F * Fᵀ * (G * Gᵀ) by simp [Matrix.mul_assoc]]
  rw [hid]
  exact (le_abs_self _).trans (abs_trace_transpose_mul_le (F * Fᵀ) (G * Gᵀ))

/-! ### Cauchy--Schwarz along an involution that respects a fibration -/

/-- Cauchy--Schwarz along an involution `τ` of `P` that preserves `d : P → Q`, applied fibre
by fibre: `∑_a |∑_{d x = a} H x · H (τ x)| ≤ ∑_x (H x)²`. -/
theorem sum_fiber_abs_involution_le {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q]
    [DecidableEq Q] (H : P → ℝ) (τ : P → P) (d : P → Q)
    (hτ : Function.Involutive τ) (hd : ∀ x, d (τ x) = d x) :
    ∑ a : Q, |∑ x ∈ Finset.univ.filter (fun x => d x = a), H x * H (τ x)|
      ≤ ∑ x : P, (H x) ^ 2 := by
  have hfibre : ∀ a : Q,
      |∑ x ∈ Finset.univ.filter (fun x => d x = a), H x * H (τ x)|
        ≤ ∑ x ∈ Finset.univ.filter (fun x => d x = a), (H x) ^ 2 := by
    intro a
    set s : Finset P := Finset.univ.filter (fun x => d x = a) with hs
    -- `τ` maps the fibre `s` to itself, because it preserves `d`.
    have hmem : ∀ x : P, x ∈ s ↔ τ x ∈ s := by
      intro x
      simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and, hd]
    -- the fibre sum of `(H ∘ τ)²` is the fibre sum of `H²`
    have hperm : ∑ x ∈ s, (H (τ x)) ^ 2 = ∑ x ∈ s, (H x) ^ 2 :=
      Finset.sum_equiv (hτ.toPerm τ) (fun i => hmem i) (fun _ _ => rfl)
    have hnn : (0:ℝ) ≤ ∑ x ∈ s, (H x) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc |∑ x ∈ s, H x * H (τ x)|
        ≤ ∑ x ∈ s, |H x * H (τ x)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x ∈ s, |H x| * |H (τ x)| := by
          exact Finset.sum_congr rfl fun x _ => abs_mul _ _
      _ ≤ Real.sqrt (∑ x ∈ s, |H x| ^ 2) * Real.sqrt (∑ x ∈ s, |H (τ x)| ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt s _ _
      _ = Real.sqrt (∑ x ∈ s, (H x) ^ 2) * Real.sqrt (∑ x ∈ s, (H x) ^ 2) := by
          rw [show (∑ x ∈ s, |H x| ^ 2) = ∑ x ∈ s, (H x) ^ 2 from
                Finset.sum_congr rfl fun x _ => sq_abs _,
            show (∑ x ∈ s, |H (τ x)| ^ 2) = ∑ x ∈ s, (H x) ^ 2 from
                (Finset.sum_congr rfl fun x _ => sq_abs _).trans hperm]
      _ = ∑ x ∈ s, (H x) ^ 2 := Real.mul_self_sqrt hnn
  calc ∑ a : Q, |∑ x ∈ Finset.univ.filter (fun x => d x = a), H x * H (τ x)|
      ≤ ∑ a : Q, ∑ x ∈ Finset.univ.filter (fun x => d x = a), (H x) ^ 2 :=
        Finset.sum_le_sum fun a _ => hfibre a
    _ = ∑ x : P, (H x) ^ 2 := Finset.sum_fiberwise Finset.univ d _

/-! ### Two index-set facts -/

/-- A singleton `{k}` with `k ∈ e` is a proper subset of `e` when `|e| ≥ 2`. -/
theorem singleton_ssubset_of_two_le_card {K : Type*} [DecidableEq K] {e : Finset K} {k : K}
    (hk : k ∈ e) (hcard : 2 ≤ e.card) : ({k} : Finset K) ⊂ e := by
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨Finset.singleton_subset_iff.2 hk, ?_⟩
  intro h
  rw [← h, Finset.card_singleton] at hcard
  omega

/-- If `g ↦ (e g, r g)` is injective in the sense of `hinj`, `g ≠ g'`, `e g = e g'`, and
`r g k = r g' k` at some `k ∈ e g`, then `r g l ≠ r g' l` for some `l ∈ e g` other than `k`. -/
theorem exists_multiIndex_ne_of_injective {K Γ : Type*} [DecidableEq K]
    {e : Γ → Finset K} {r : Γ → K → ℕ}
    (hinj : ∀ g g' : Γ, e g = e g' → (∀ k ∈ e g, r g k = r g' k) → g = g')
    {g g' : Γ} (hne : g ≠ g') (hlevel : e g = e g') {k : K} (hk : k ∈ e g)
    (hstar : r g k = r g' k) :
    ∃ l ∈ (e g).erase k, r g l ≠ r g' l := by
  by_contra hcon
  refine hne (hinj g g' hlevel ?_)
  intro l hl
  by_cases hlk : l = k
  · subst hlk; exact hstar
  · by_contra hne2
    exact hcon ⟨l, Finset.mem_erase.2 ⟨hlk, hl⟩, hne2⟩

/-! ## Clause (a)

`𝔼[X_{γγ}] = tot(γ)` and `𝔼[X_{γγ'}] = 0` for `γ ≠ γ'`.

The product `π^γ_s = ∏_{k ∈ f_γ} ψ_{r_k(γ)}(U^{(k)}_{s_k})` is written as a product over the
sites `(k, s_k)` of the sub-tuple `s`: `sites γ s : Finset V` is its site set and
`rIdx γ : V → R` reads the multi-index at a site. The basis is indexed by an arbitrary type `R`
with a subset `Rpos` of mean-zero indices (`R = ℕ`, `Rpos = {r | r ≠ 0}` is the usual case), and
only orthonormality, not completeness, is assumed. In clause (a) the bound `|ψ_r| ≤ B_0` is used
only for integrability. -/

section ClauseA

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {R : Type*} [DecidableEq R] {U : V → Ω → ℝ} {ψ : R → ℝ → ℝ} {Rpos : Set R} {B₀ : ℝ}

/-- An orthonormal system `{ψ_r}` evaluated at independent latent variables:
`𝔼[ψ_r(U_v)] = 0` for `r ∈ Rpos`, `𝔼[ψ_r(U_v)ψ_{r'}(U_v)] = 𝟙{r = r'}` and `|ψ_r| ≤ B_0`. -/
structure IsBasisSystem (μ : Measure Ω) (U : V → Ω → ℝ) (ψ : R → ℝ → ℝ) (Rpos : Set R)
    (B₀ : ℝ) : Prop where
  /-- The latent variables are measurable. -/
  measurable_latent : ∀ v, Measurable (U v)
  /-- The basis functions are measurable. -/
  measurable_psi : ∀ r, Measurable (ψ r)
  /-- The latent variables are independent. -/
  indep : iIndepFun U μ
  /-- `|ψ_r| ≤ B_0`. -/
  bound : ∀ r x, |ψ r x| ≤ B₀
  /-- `𝔼[ψ_r(U_v)] = 0` for `r ∈ Rpos`. -/
  integral_eq_zero : ∀ (v : V) {r : R}, r ∈ Rpos → ∫ ω, ψ r (U v ω) ∂μ = 0
  /-- `𝔼[ψ_r(U_v)ψ_{r'}(U_v)] = 𝟙{r = r'}`. -/
  integral_mul : ∀ (v : V) (r r' : R),
    ∫ ω, ψ r (U v ω) * ψ r' (U v ω) ∂μ = if r = r' then 1 else 0

omit [Fintype V] [DecidableEq V] in
/-- The measure of a basis system is a probability measure, since `iIndepFun` forces it. -/
theorem IsBasisSystem.isProbabilityMeasure (h : IsBasisSystem μ U ψ Rpos B₀) :
    IsProbabilityMeasure μ := h.indep.isProbabilityMeasure

/-- `𝔼[∏_{v ∈ E} ψ_{r v}(U_v) · ∏_{v ∈ E'} ψ_{r' v}(U_v)] = 𝟙{E = E' and r = r' on E}`.
Both products are extended by `1` to all of `V`, so that independence applies to the partition
of `V` into singletons. -/
theorem integral_prod_mul_prod (h : IsBasisSystem μ U ψ Rpos B₀)
    {E E' : Finset V} {r r' : V → R} (hr : ∀ v ∈ E, r v ∈ Rpos) (hr' : ∀ v ∈ E', r' v ∈ Rpos) :
    ∫ ω, (∏ v ∈ E, ψ (r v) (U v ω)) * (∏ v ∈ E', ψ (r' v) (U v ω)) ∂μ
      = if E = E' ∧ ∀ v ∈ E, r v = r' v then 1 else 0 := by
  classical
  have hP : IsProbabilityMeasure μ := h.isProbabilityMeasure
  set f : V → ℝ → ℝ := fun v x =>
    (if v ∈ E then ψ (r v) x else 1) * (if v ∈ E' then ψ (r' v) x else 1) with hfdef
  have hmeas : ∀ v, Measurable (f v) := by
    intro v
    apply Measurable.mul
    · by_cases hv : v ∈ E <;> simp [hv, h.measurable_psi]
    · by_cases hv : v ∈ E' <;> simp [hv, h.measurable_psi]
  have hpoint : ∀ ω, (∏ v ∈ E, ψ (r v) (U v ω)) * (∏ v ∈ E', ψ (r' v) (U v ω))
      = ∏ v : V, f v (U v ω) := by
    intro ω
    rw [hfdef]
    simp only [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq]
  have hint : ∫ ω, ∏ v : V, f v (U v ω) ∂μ = ∏ v : V, ∫ ω, f v (U v ω) ∂μ :=
    h.indep.integral_fun_prod_comp (fun v => (h.measurable_latent v).aemeasurable)
      (fun v => (hmeas v).aestronglyMeasurable)
  have hfac : ∀ v : V, ∫ ω, f v (U v ω) ∂μ
      = (if v ∈ E then (if v ∈ E' then (if r v = r' v then (1:ℝ) else 0) else 0)
         else (if v ∈ E' then 0 else 1)) := by
    intro v
    by_cases hv : v ∈ E <;> by_cases hv' : v ∈ E'
    · simp only [hfdef, hv, hv', ite_true]
      exact h.integral_mul v (r v) (r' v)
    · simp only [hfdef, hv, hv', ite_true, ite_false, mul_one]
      exact h.integral_eq_zero v (hr v hv)
    · simp only [hfdef, hv, hv', ite_true, ite_false, one_mul]
      exact h.integral_eq_zero v (hr' v hv')
    · simp [hfdef, hv, hv']
  simp only [hpoint] at *
  rw [hint]
  simp only [hfac]
  split_ifs with hc
  · refine Finset.prod_eq_one fun v _ => ?_
    obtain ⟨hEE, hrr⟩ := hc
    by_cases hv : v ∈ E
    · have hv' : v ∈ E' := hEE ▸ hv
      simp [hv, hv', hrr v hv]
    · have hv' : v ∉ E' := fun hx => hv (hEE ▸ hx)
      simp [hv, hv']
  · have hex : ∃ v : V, (if v ∈ E then (if v ∈ E' then (if r v = r' v then (1:ℝ) else 0) else 0)
         else (if v ∈ E' then 0 else 1)) = 0 := by
      by_cases hEE : E = E'
      · have hnr : ¬ ∀ v ∈ E, r v = r' v := fun hx => hc ⟨hEE, hx⟩
        rw [not_forall] at hnr
        obtain ⟨v, hv⟩ := hnr
        rw [not_imp] at hv
        obtain ⟨hv1, hv2⟩ := hv
        have hv' : v ∈ E' := hEE ▸ hv1
        exact ⟨v, by simp [hv1, hv', hv2]⟩
      · rw [Finset.ext_iff, not_forall] at hEE
        obtain ⟨v, hv⟩ := hEE
        refine ⟨v, ?_⟩
        by_cases hv1 : v ∈ E
        · have hv2 : v ∉ E' := fun hx => hv (iff_of_true hv1 hx)
          simp [hv1, hv2]
        · have hv2 : v ∈ E' := by
            by_contra hx
            exact hv (iff_of_false hv1 hx)
          simp [hv1, hv2]
    obtain ⟨v, hv⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ v) hv

section Components

variable {Γ : Type*} {S : Γ → Type*} [∀ γ, Fintype (S γ)]
  {I : Type*} [Fintype I] {τ : Type*} [DecidableEq τ]

/-- `π^γ_s := ∏_{k ∈ f_γ} ψ_{r_k(γ)}(U^{(k)}_{s_k})`, written as a product over the sites the
sub-tuple `s` carries. -/
noncomputable def basisProd (U : V → Ω → ℝ) (ψ : R → ℝ → ℝ)
    (sites : ∀ γ, S γ → Finset V) (rIdx : Γ → V → R) (γ : Γ) (s : S γ) : Ω → ℝ :=
  fun ω => ∏ w ∈ sites γ s, ψ (rIdx γ w) (U w ω)

/-- `A^γ_i := ∑_s v^{(γ)}_{(s,i)} π^γ_s`. -/
noncomputable def blockSum (U : V → Ω → ℝ) (ψ : R → ℝ → ℝ)
    (sites : ∀ γ, S γ → Finset V) (rIdx : Γ → V → R) (arr : ∀ γ, S γ → I → ℝ)
    (γ : Γ) (i : I) : Ω → ℝ :=
  fun ω => ∑ s : S γ, arr γ s i * basisProd U ψ sites rIdx γ s ω

/-- `X_{γγ'} := ∑_i A^γ_i A^{γ'}_i` when `k^⋆_γ = k^⋆_{γ'}` and
`r_{k^⋆}(γ) = r_{k^⋆}(γ')`, and `0` otherwise. The side condition is carried by `tag`, the pair
`(k^⋆_γ, r_{k^⋆_γ}(γ))`. -/
noncomputable def cvarEntry (U : V → Ω → ℝ) (ψ : R → ℝ → ℝ)
    (sites : ∀ γ, S γ → Finset V) (rIdx : Γ → V → R) (arr : ∀ γ, S γ → I → ℝ)
    (tag : Γ → τ) (γ γ' : Γ) : Ω → ℝ :=
  fun ω => if tag γ = tag γ' then
    ∑ i : I, blockSum U ψ sites rIdx arr γ i ω * blockSum U ψ sites rIdx arr γ' i ω else 0

variable {sites : ∀ γ, S γ → Finset V} {rIdx : Γ → V → R} {arr : ∀ γ, S γ → I → ℝ}
  {tag : Γ → τ}

omit [Fintype V] [DecidableEq V] [∀ γ, Fintype (S γ)] in
theorem measurable_basisProd (h : IsBasisSystem μ U ψ Rpos B₀) (γ : Γ) (s : S γ) :
    Measurable (basisProd U ψ sites rIdx γ s) :=
  Finset.measurable_prod _ fun w _ => (h.measurable_psi _).comp (h.measurable_latent w)

omit [DecidableEq V] [∀ γ, Fintype (S γ)] in
/-- `|π^γ_s| ≤ max(B_0,1)^{|f_γ|}`. -/
theorem abs_basisProd_le_card (h : IsBasisSystem μ U ψ Rpos B₀) (γ : Γ) (s : S γ) (ω : Ω) :
    |basisProd U ψ sites rIdx γ s ω| ≤ max B₀ 1 ^ (sites γ s).card := by
  calc |basisProd U ψ sites rIdx γ s ω|
      = ∏ w ∈ sites γ s, |ψ (rIdx γ w) (U w ω)| := Finset.abs_prod _ _
    _ ≤ ∏ _w ∈ sites γ s, max B₀ 1 :=
        Finset.prod_le_prod₀ (fun w _ => abs_nonneg _)
          (fun w _ => le_trans (h.bound _ _) (le_max_left _ _))
    _ = max B₀ 1 ^ (sites γ s).card := by rw [Finset.prod_const]

omit [DecidableEq V] [∀ γ, Fintype (S γ)] in
/-- `|π^γ_s| ≤ max(B_0,1)^M` when every site set has at most `M` elements. -/
theorem abs_basisProd_le_ofCard (h : IsBasisSystem μ U ψ Rpos B₀) {M : ℕ}
    (hlev : ∀ (g : Γ) (x : S g), (sites g x).card ≤ M) (γ : Γ) (s : S γ) (ω : Ω) :
    |basisProd U ψ sites rIdx γ s ω| ≤ max B₀ 1 ^ M :=
  le_trans (abs_basisProd_le_card h γ s ω) (pow_le_pow_right₀ (le_max_right _ _) (hlev γ s))

omit [DecidableEq V] [∀ γ, Fintype (S γ)] in
/-- `|π^γ_s| ≤ max(B_0,1)^{|V|}`. -/
theorem abs_basisProd_le (h : IsBasisSystem μ U ψ Rpos B₀) (γ : Γ) (s : S γ) (ω : Ω) :
    |basisProd U ψ sites rIdx γ s ω| ≤ max B₀ 1 ^ Fintype.card V :=
  abs_basisProd_le_ofCard h (fun _ _ => Finset.card_le_univ _) γ s ω

omit [DecidableEq V] [∀ γ, Fintype (S γ)] in
/-- A product of two `π`'s is bounded, hence integrable. -/
theorem integrable_basisProd_mul (h : IsBasisSystem μ U ψ Rpos B₀)
    (γ γ' : Γ) (s : S γ) (s' : S γ') :
    Integrable (fun ω => basisProd U ψ sites rIdx γ s ω *
      basisProd U ψ sites rIdx γ' s' ω) μ := by
  have hP : IsProbabilityMeasure μ := h.isProbabilityMeasure
  refine Integrable.mono' (g := fun _ => (max B₀ 1 ^ Fintype.card V) ^ 2)
    (integrable_const _)
    (((measurable_basisProd h γ s).mul (measurable_basisProd h γ' s')).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul, sq]
  have hpow : (0:ℝ) ≤ max B₀ 1 ^ Fintype.card V := by positivity
  exact mul_le_mul (abs_basisProd_le h γ s ω) (abs_basisProd_le h γ' s' ω) (abs_nonneg _) hpow

omit [∀ γ, Fintype (S γ)] in
/-- **Orthonormality of the `π`'s**: `𝔼[π^γ_sπ^{γ'}_{s'}]` is `1` if the site sets agree and
the multi-indices agree on them, and `0` otherwise. -/
theorem integral_basisProd_mul (h : IsBasisSystem μ U ψ Rpos B₀)
    (hpos : ∀ (γ : Γ) (s : S γ), ∀ w ∈ sites γ s, rIdx γ w ∈ Rpos)
    (γ γ' : Γ) (s : S γ) (s' : S γ') :
    ∫ ω, basisProd U ψ sites rIdx γ s ω * basisProd U ψ sites rIdx γ' s' ω ∂μ
      = if sites γ s = sites γ' s' ∧ ∀ w ∈ sites γ s, rIdx γ w = rIdx γ' w then 1 else 0 :=
  integral_prod_mul_prod h (hpos γ s) (hpos γ' s')

omit [Fintype I] in
/-- `𝔼[A^γ_iA^{γ'}_i]` expanded over the pairs `(s,s')`. -/
theorem integral_blockSum_mul (h : IsBasisSystem μ U ψ Rpos B₀)
    (hpos : ∀ (γ : Γ) (s : S γ), ∀ w ∈ sites γ s, rIdx γ w ∈ Rpos)
    (γ γ' : Γ) (i : I) :
    ∫ ω, blockSum U ψ sites rIdx arr γ i ω * blockSum U ψ sites rIdx arr γ' i ω ∂μ
      = ∑ s : S γ, ∑ s' : S γ', (arr γ s i * arr γ' s' i) *
          (if sites γ s = sites γ' s' ∧ ∀ w ∈ sites γ s, rIdx γ w = rIdx γ' w then 1 else 0) := by
  classical
  have hexp : ∀ ω, blockSum U ψ sites rIdx arr γ i ω * blockSum U ψ sites rIdx arr γ' i ω
      = ∑ s : S γ, ∑ s' : S γ', (arr γ s i * arr γ' s' i) *
          (basisProd U ψ sites rIdx γ s ω * basisProd U ψ sites rIdx γ' s' ω) := by
    intro ω
    simp only [blockSum, Fintype.sum_mul_sum]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => by ring
  simp only [hexp]
  rw [integral_finsetSum _ fun s _ =>
    integrable_finsetSum _ fun s' _ => ((integrable_basisProd_mul h γ γ' s s').const_mul _)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_finsetSum _ fun s' _ => ((integrable_basisProd_mul h γ γ' s s').const_mul _)]
  exact Finset.sum_congr rfl fun s' _ => by
    rw [integral_const_mul, integral_basisProd_mul h hpos]

/-- **Clause (a), diagonal**: `𝔼[X_{γγ}] = tot(γ)`. -/
theorem integral_cvarEntry_self (h : IsBasisSystem μ U ψ Rpos B₀)
    (hpos : ∀ (γ : Γ) (s : S γ), ∀ w ∈ sites γ s, rIdx γ w ∈ Rpos)
    (hinj : ∀ (γ : Γ) (s s' : S γ), sites γ s = sites γ s' → s = s')
    (γ : Γ) :
    ∫ ω, cvarEntry U ψ sites rIdx arr tag γ γ ω ∂μ = rectFrobSq (arr γ) := by
  classical
  have hP : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have hif : ∀ ω, cvarEntry U ψ sites rIdx arr tag γ γ ω
      = ∑ i : I, blockSum U ψ sites rIdx arr γ i ω * blockSum U ψ sites rIdx arr γ i ω := by
    intro ω; simp [cvarEntry]
  simp only [hif]
  have hintbl : ∀ i : I, Integrable (fun ω => blockSum U ψ sites rIdx arr γ i ω *
      blockSum U ψ sites rIdx arr γ i ω) μ := by
    intro i
    have hexp : (fun ω => blockSum U ψ sites rIdx arr γ i ω * blockSum U ψ sites rIdx arr γ i ω)
        = fun ω => ∑ s : S γ, ∑ s' : S γ, (arr γ s i * arr γ s' i) *
            (basisProd U ψ sites rIdx γ s ω * basisProd U ψ sites rIdx γ s' ω) := by
      funext ω
      simp only [blockSum, Fintype.sum_mul_sum]
      exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => by ring
    rw [hexp]
    exact integrable_finsetSum _ fun s _ =>
      integrable_finsetSum _ fun s' _ => ((integrable_basisProd_mul h γ γ s s').const_mul _)
  rw [integral_finsetSum _ fun i _ => hintbl i]
  have hrow : ∀ i : I, ∫ ω, blockSum U ψ sites rIdx arr γ i ω *
      blockSum U ψ sites rIdx arr γ i ω ∂μ = ∑ s : S γ, arr γ s i ^ 2 := by
    intro i
    rw [integral_blockSum_mul h hpos]
    refine Finset.sum_congr rfl fun s _ => ?_
    refine (Finset.sum_eq_single s ?_ ?_).trans ?_
    · intro b _ hb
      have hns : ¬ sites γ s = sites γ b := fun hsite => hb (hinj γ b s hsite.symm)
      simp [hns]
    · intro hb; exact absurd (Finset.mem_univ s) hb
    · simp [sq]
  simp only [hrow, rectFrobSq]
  exact Finset.sum_comm

/-- **Clause (a), off the diagonal**: `𝔼[X_{γγ'}] = 0` for `γ ≠ γ'`. -/
theorem integral_cvarEntry_ne (h : IsBasisSystem μ U ψ Rpos B₀)
    (hpos : ∀ (γ : Γ) (s : S γ), ∀ w ∈ sites γ s, rIdx γ w ∈ Rpos)
    (hsep : ∀ (γ γ' : Γ) (s : S γ) (s' : S γ'), tag γ = tag γ' → sites γ s = sites γ' s' →
      (∀ w ∈ sites γ s, rIdx γ w = rIdx γ' w) → γ = γ')
    {γ γ' : Γ} (hne : γ ≠ γ') :
    ∫ ω, cvarEntry U ψ sites rIdx arr tag γ γ' ω ∂μ = 0 := by
  classical
  have hP : IsProbabilityMeasure μ := h.isProbabilityMeasure
  by_cases htag : tag γ = tag γ'
  · have hif : ∀ ω, cvarEntry U ψ sites rIdx arr tag γ γ' ω
        = ∑ i : I, blockSum U ψ sites rIdx arr γ i ω * blockSum U ψ sites rIdx arr γ' i ω := by
      intro ω; simp [cvarEntry, htag]
    simp only [hif]
    have hintbl : ∀ i : I, Integrable (fun ω => blockSum U ψ sites rIdx arr γ i ω *
        blockSum U ψ sites rIdx arr γ' i ω) μ := by
      intro i
      have hexp : (fun ω => blockSum U ψ sites rIdx arr γ i ω *
          blockSum U ψ sites rIdx arr γ' i ω)
          = fun ω => ∑ s : S γ, ∑ s' : S γ', (arr γ s i * arr γ' s' i) *
              (basisProd U ψ sites rIdx γ s ω * basisProd U ψ sites rIdx γ' s' ω) := by
        funext ω
        simp only [blockSum, Fintype.sum_mul_sum]
        exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => by ring
      rw [hexp]
      exact integrable_finsetSum _ fun s _ =>
        integrable_finsetSum _ fun s' _ => ((integrable_basisProd_mul h γ γ' s s').const_mul _)
    rw [integral_finsetSum _ fun i _ => hintbl i]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_blockSum_mul h hpos]
    refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun s' _ => ?_
    have hno : ¬ (sites γ s = sites γ' s' ∧ ∀ w ∈ sites γ s, rIdx γ w = rIdx γ' w) := by
      rintro ⟨h1, h2⟩
      exact hne (hsep γ γ' s s' htag h1 h2)
    simp [hno]
  · simp [cvarEntry, htag]

/-- **Lemma SM.C.3(a).** `𝔼[X_{γγ}] = tot(γ)` and `𝔼[X_{γγ'}] = 0` for `γ ≠ γ'`.

`hpos` says every index read at a site of a sub-tuple is a mean-zero index; `hinj` says a
sub-tuple is determined by its site set; `hsep` says that equal site sets, equal multi-indices on
them and equal tags force `γ = γ'`. -/
theorem concentration_clause_a (h : IsBasisSystem μ U ψ Rpos B₀)
    (hpos : ∀ (γ : Γ) (s : S γ), ∀ w ∈ sites γ s, rIdx γ w ∈ Rpos)
    (hinj : ∀ (γ : Γ) (s s' : S γ), sites γ s = sites γ s' → s = s')
    (hsep : ∀ (γ γ' : Γ) (s : S γ) (s' : S γ'), tag γ = tag γ' → sites γ s = sites γ' s' →
      (∀ w ∈ sites γ s, rIdx γ w = rIdx γ' w) → γ = γ') :
    (∀ γ : Γ, ∫ ω, cvarEntry U ψ sites rIdx arr tag γ γ ω ∂μ = rectFrobSq (arr γ)) ∧
      (∀ γ γ' : Γ, γ ≠ γ' → ∫ ω, cvarEntry U ψ sites rIdx arr tag γ γ' ω ∂μ = 0) :=
  ⟨fun γ => integral_cvarEntry_self h hpos hinj γ,
    fun _ _ hne => integral_cvarEntry_ne h hpos hsep hne⟩

end Components

/-! ### Clause (a) in the tuple model

A sub-tuple `t ∈ 𝒯_{f_γ}` is encoded by its site set `{(k, t_k) : k ∈ f_γ}` inside
`V = Σ k, 𝒩_k`, whose image under `Sigma.fst` is `f_γ`. Then `hinj` holds by `Subtype.ext`, and
`hsep` follows from the injectivity of `γ ↦ (e_γ, 𝐫(γ))`. -/

section TupleModel

variable {K : Type*} [DecidableEq K] {N : K → Type*}

/-- The sites `⟨k, i⟩`, one latent variable `U^{(k)}_i` per category `i` of each dimension
`k`. -/
abbrev Site (K : Type*) (N : K → Type*) := Σ k : K, N k

variable {Γ : Type*} {S : Γ → Type*}

omit [DecidableEq K] in
/-- When a sub-tuple is its site set, the site set determines it. -/
theorem sites_injective_of_subtype {V : Type*} {P : Γ → Finset V → Prop} (γ : Γ)
    (s s' : {E : Finset V // P γ E}) (h : (s : Finset V) = (s' : Finset V)) : s = s' :=
  Subtype.ext h

/-- `hsep` in the tuple model. If `γ ↦ (e_γ, 𝐫(γ))` is injective, with
`e_γ = insert k^⋆_γ f_γ`, and each site set projects onto `f_γ`, then equal site sets, equal
multi-indices on them and equal tags force `γ = γ'`. -/
theorem sep_of_multiIndex_injective {f : Γ → Finset K} {kstar : Γ → K} {rmul : Γ → K → ℕ}
    {sites : ∀ γ, S γ → Finset (Site K N)}
    (hlevel : ∀ (γ : Γ) (s : S γ), (sites γ s).image Sigma.fst = f γ)
    (hlevelinj : ∀ γ γ' : Γ, insert (kstar γ) (f γ) = insert (kstar γ') (f γ') →
      (∀ k ∈ insert (kstar γ) (f γ), rmul γ k = rmul γ' k) → γ = γ')
    (γ γ' : Γ) (s : S γ) (s' : S γ')
    (htag : (kstar γ, rmul γ (kstar γ)) = (kstar γ', rmul γ' (kstar γ')))
    (hsite : sites γ s = sites γ' s')
    (hr : ∀ w ∈ sites γ s, rmul γ w.1 = rmul γ' w.1) : γ = γ' := by
  obtain ⟨hk, hrk⟩ := Prod.mk.injEq .. ▸ htag
  have hf : f γ = f γ' := by rw [← hlevel γ s, ← hlevel γ' s', hsite]
  have hagree : ∀ k ∈ f γ, rmul γ k = rmul γ' k := by
    intro k hk'
    rw [← hlevel γ s, Finset.mem_image] at hk'
    obtain ⟨w, hw, rfl⟩ := hk'
    exact hr w hw
  refine hlevelinj γ γ' (by rw [hk, hf]) ?_
  intro k hkmem
  rcases Finset.mem_insert.1 hkmem with rfl | hkf
  · exact hk ▸ hrk
  · exact hagree k hkf

end TupleModel

section TupleClauseA

variable {K : Type*} [Fintype K] [DecidableEq K] {N : K → Type*}
  [∀ k, Fintype (N k)] [∀ k, DecidableEq (N k)]
variable {Γ : Type*} (f : Γ → Finset K)

/-- A sub-tuple `t ∈ 𝒯_{f_γ}` of the component `γ`, encoded by its site set: a finite set of
sites meeting exactly the dimensions of `f_γ`. -/
abbrev SubTuple (γ : Γ) := {E : Finset (Site K N) // E.image Sigma.fst = f γ}

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Lemma SM.C.3(a) in the tuple model.** `hlevelinj` is the injectivity of
`γ ↦ (e_γ, 𝐫(γ))` with `e_γ = insert k^⋆_γ f_γ`, and `hpos` asks `r_k(γ)` to be a mean-zero index
for `k ∈ f_γ`. The index `i` runs over all sites, with `arr γ` extended by zero outside
`𝒩_{k^⋆_γ}`. -/
theorem concentration_clause_a_tuples
    {kstar : Γ → K} {rmul : Γ → K → ℕ}
    {U : Site K N → Ω → ℝ} {ψ : ℕ → ℝ → ℝ} {B₀ : ℝ}
    {arr : ∀ γ, SubTuple f γ → Site K N → ℝ}
    (h : IsBasisSystem μ U ψ {r : ℕ | r ≠ 0} B₀)
    (hpos : ∀ (γ : Γ) (k : K), k ∈ f γ → rmul γ k ≠ 0)
    (hlevelinj : ∀ γ γ' : Γ, insert (kstar γ) (f γ) = insert (kstar γ') (f γ') →
      (∀ k ∈ insert (kstar γ) (f γ), rmul γ k = rmul γ' k) → γ = γ') :
    (∀ γ : Γ, ∫ ω, cvarEntry (S := SubTuple f) U ψ (fun _ s => s.1)
        (fun γ w => rmul γ w.1) arr (fun γ => (kstar γ, rmul γ (kstar γ))) γ γ ω ∂μ
      = rectFrobSq (arr γ)) ∧
    (∀ γ γ' : Γ, γ ≠ γ' →
      ∫ ω, cvarEntry (S := SubTuple f) U ψ (fun _ s => s.1)
        (fun γ w => rmul γ w.1) arr (fun γ => (kstar γ, rmul γ (kstar γ))) γ γ' ω ∂μ = 0) := by
  refine concentration_clause_a h ?_ ?_ ?_
  · intro γ s w hw
    have hk : w.1 ∈ f γ := by
      rw [← s.2]
      exact Finset.mem_image_of_mem Sigma.fst hw
    exact hpos γ w.1 hk
  · intro γ s s' hsite
    exact sites_injective_of_subtype (P := fun γ E => E.image Sigma.fst = f γ) γ s s' hsite
  · intro γ γ' s s' htag hsite hr
    exact sep_of_multiIndex_injective (f := f) (kstar := kstar) (rmul := rmul)
      (sites := fun _ s => s.1) (fun γ s => s.2) hlevelinj
      γ γ' s s' htag hsite hr

end TupleClauseA

/-! ### A model for clause (a)

Two independent fair signs, the orthonormal system `{1, sign}` indexed by `Fin 2`, and two
components on distinct sites with equal tags and nonzero coefficient arrays. -/

section Witness

open scoped ENNReal

namespace ClauseAWitness

/-- A fair sign, `½δ_1 + ½δ_{-1}` on `ℝ`. -/
noncomputable def signLaw : Measure ℝ :=
  (1/2 : ℝ≥0∞) • Measure.dirac (1:ℝ) + (1/2 : ℝ≥0∞) • Measure.dirac (-1:ℝ)

instance : IsProbabilityMeasure signLaw := by
  constructor
  simp [signLaw]
  exact ENNReal.inv_two_add_inv_two

/-- The witness probability space: two independent fair signs. -/
noncomputable def wμ : Measure (Fin 2 → ℝ) := Measure.pi fun _ => signLaw

instance : IsProbabilityMeasure wμ := by
  unfold wμ; infer_instance

/-- The two latent variables: the coordinates. -/
def wU (v : Fin 2) (ω : Fin 2 → ℝ) : ℝ := ω v

/-- The orthonormal system: the constant and the sign `if 0 ≤ x then 1 else -1`, which is
bounded by `1` on all of `ℝ`. -/
noncomputable def wψ (r : Fin 2) (x : ℝ) : ℝ := if r = 0 then 1 else if 0 ≤ x then 1 else -1

theorem measurable_wψ (r : Fin 2) : Measurable (wψ r) := by
  by_cases hr : r = 0
  · have hfun : wψ r = fun _ : ℝ => (1:ℝ) := by funext x; simp [wψ, hr]
    rw [hfun]
    exact measurable_const
  · have hfun : wψ r = fun x : ℝ => if 0 ≤ x then (1:ℝ) else -1 := by funext x; simp [wψ, hr]
    rw [hfun]
    exact Measurable.ite (measurableSet_le measurable_const measurable_id)
      measurable_const measurable_const

/-- `𝔼[f(U_v)] = (f(1) + f(-1))/2`: the coordinate push-forward of `wμ` is `signLaw`. -/
theorem wintegral {f : ℝ → ℝ} (hf : Measurable f) (v : Fin 2) :
    ∫ ω, f (wU v ω) ∂wμ = (f 1 + f (-1)) / 2 := by
  have hmap : wμ.map (fun ω : Fin 2 → ℝ => ω v) = signLaw :=
    (MeasureTheory.measurePreserving_eval (fun _ => signLaw) v).map_eq
  have h1 : ∫ ω, f (wU v ω) ∂wμ = ∫ x, f x ∂signLaw := by
    rw [← hmap, integral_map (measurable_pi_apply v).aemeasurable hf.aestronglyMeasurable]
    rfl
  have hi1 : Integrable f ((1/2 : ℝ≥0∞) • Measure.dirac (1:ℝ)) :=
    (integrable_dirac' hf.stronglyMeasurable (by simp)).smul_measure (by simp)
  have hi2 : Integrable f ((1/2 : ℝ≥0∞) • Measure.dirac (-1:ℝ)) :=
    (integrable_dirac' hf.stronglyMeasurable (by simp)).smul_measure (by simp)
  rw [h1, signLaw, integral_add_measure hi1 hi2, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  simp
  ring

/-- The basis system of the model. -/
theorem wIsBasisSystem : IsBasisSystem wμ wU wψ ({1} : Set (Fin 2)) 1 where
  measurable_latent v := measurable_pi_apply v
  measurable_psi := measurable_wψ
  indep := iIndepFun_pi (μ := fun _ : Fin 2 => signLaw) (X := fun _ => (id : ℝ → ℝ))
    (fun _ => aemeasurable_id)
  bound r x := by
    simp only [wψ]
    split_ifs <;> simp
  integral_eq_zero v {r} hr := by
    have hr1 : r = 1 := hr
    subst hr1
    have h : ∫ ω, wψ 1 (wU v ω) ∂wμ = (wψ 1 1 + wψ 1 (-1)) / 2 := wintegral (measurable_wψ 1) v
    rw [h]
    norm_num [wψ]
  integral_mul v r r' := by
    have h : ∫ ω, wψ r (wU v ω) * wψ r' (wU v ω) ∂wμ
        = (wψ r 1 * wψ r' 1 + wψ r (-1) * wψ r' (-1)) / 2 :=
      wintegral (f := fun x => wψ r x * wψ r' x) ((measurable_wψ r).mul (measurable_wψ r')) v
    rw [h]
    fin_cases r <;> fin_cases r' <;> norm_num [wψ]

/-- Two components on the two distinct sites, each with a single sub-tuple. -/
def wsites : ∀ _γ : Fin 2, Unit → Finset (Fin 2) := fun γ _ => {γ}

/-- Both components read the same mean-zero basis index. -/
def wrIdx : Fin 2 → Fin 2 → Fin 2 := fun _ _ => 1

/-- Equal tags, so `cvarEntry` is not identically zero off the diagonal. -/
def wtag : Fin 2 → Unit := fun _ => ()

/-- A nonzero coefficient array. -/
def warr : ∀ _γ : Fin 2, Unit → Unit → ℝ := fun _ _ _ => 1

theorem wHpos : ∀ (γ : Fin 2) (s : Unit), ∀ w ∈ wsites γ s, wrIdx γ w ∈ ({1} : Set (Fin 2)) :=
  fun _ _ _ _ => rfl

theorem wHinj : ∀ (γ : Fin 2) (s s' : Unit), wsites γ s = wsites γ s' → s = s' :=
  fun _ _ _ _ => rfl

theorem wHsep : ∀ (γ γ' : Fin 2) (s s' : Unit), wtag γ = wtag γ' → wsites γ s = wsites γ' s' →
    (∀ w ∈ wsites γ s, wrIdx γ w = wrIdx γ' w) → γ = γ' := by
  intro γ γ' s s' _ hsite _
  exact Finset.singleton_inj.mp hsite

/-- All hypotheses of `concentration_clause_a` hold on this model; the diagonal expectations
equal `1`. -/
theorem concentration_clause_a_witness :
    (∀ γ : Fin 2, ∫ ω, cvarEntry wU wψ wsites wrIdx warr wtag γ γ ω ∂wμ = 1) ∧
      (∀ γ γ' : Fin 2, γ ≠ γ' → ∫ ω, cvarEntry wU wψ wsites wrIdx warr wtag γ γ' ω ∂wμ = 0) := by
  have h := concentration_clause_a (μ := wμ) (U := wU) (ψ := wψ) (Rpos := ({1} : Set (Fin 2)))
    (B₀ := 1) (S := fun _ => Unit) (I := Unit) (sites := wsites) (rIdx := wrIdx) (arr := warr)
    (tag := wtag) wIsBasisSystem wHpos wHinj wHsep
  refine ⟨fun γ => ?_, h.2⟩
  rw [h.1 γ]
  simp [rectFrobSq, warr]

end ClauseAWitness

end Witness

end ClauseA

/-! ## Clause (b)

For `∑_γ λ_γ² ≤ 1`,
`Var(∑_{γ,γ'} λ_γ λ_{γ'} X_{γγ'}) ≤ C(M, B_0, |Γ|) (max_γ cut(γ)) (max_γ tot(γ))`.

Each entry splits as `X_{γγ'} = 𝔼[X_{γγ'}] + Ξᵐ_{γγ'} + Ξᵘ_{γγ'}` into its mean, the matched part
and the unmatched part. `concentration_clause_b` reduces the lemma to a bound on `Var(Ξᵐ)` and a
bound on `𝔼[(Ξᵘ)²]`; the later theorems prove both, with explicit constants. -/

section ClauseB

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {R : Type*} [DecidableEq R] {U : V → Ω → ℝ} {ψ : R → ℝ → ℝ} {Rpos : Set R} {B₀ : ℝ}

/-! ### Variance tools -/

/-- The variance of a constant is zero. -/
theorem variance_const_fun [IsProbabilityMeasure μ] (c : ℝ) :
    variance (fun _ : Ω => c) μ = 0 := by
  rw [variance_eq_integral aemeasurable_const]
  simp

/-- `∫ f² ≤ C` from a pointwise bound on `f²`. -/
theorem integral_sq_le_of_bound [IsProbabilityMeasure μ] {f : Ω → ℝ} {C : ℝ}
    (hf : MemLp f 2 μ) (hb : ∀ ω, (f ω) ^ 2 ≤ C) : ∫ ω, (f ω) ^ 2 ∂μ ≤ C := by
  refine le_trans (integral_mono hf.integrable_sq (integrable_const _) hb) ?_
  simp

theorem abs_covariance_le_of_variance_le [IsFiniteMeasure μ] {X Y : Ω → ℝ} {κ : ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hXv : variance X μ ≤ κ) (hYv : variance Y μ ≤ κ) :
    |cov[X, Y; μ]| ≤ κ := by
  have hadd : variance (X + Y) μ = variance X μ + 2 * cov[X, Y; μ] + variance Y μ :=
    variance_add hX hY
  have hsub : variance (X - Y) μ = variance X μ - 2 * cov[X, Y; μ] + variance Y μ :=
    variance_sub hX hY
  have h1 : (0:ℝ) ≤ variance (X + Y) μ := variance_nonneg _ _
  have h2 : (0:ℝ) ≤ variance (X - Y) μ := variance_nonneg _ _
  rw [abs_le]
  constructor <;> linarith [hadd, hsub, h1, h2]

/-! ### The site-indexed counting bound -/

theorem sum_shared_le_sum_site_sq {S V : Type*} [Fintype S] [Fintype V] [DecidableEq V]
    (E : S → Finset V) (c : S → ℝ) (hc : ∀ s, 0 ≤ c s) :
    ∑ s : S, ∑ u : S, (if Disjoint (E s) (E u) then 0 else c s * c u)
      ≤ ∑ w : V, (∑ s ∈ Finset.univ.filter (fun s => w ∈ E s), c s) ^ 2 := by
  classical
  have hnn : ∀ (w : V) (s u : S), (0:ℝ) ≤ (if w ∈ E s ∧ w ∈ E u then c s * c u else 0) := by
    intro w s u
    split_ifs
    · exact mul_nonneg (hc s) (hc u)
    · exact le_rfl
  have hstep : ∀ s u : S, (if Disjoint (E s) (E u) then 0 else c s * c u)
      ≤ ∑ w : V, (if w ∈ E s ∧ w ∈ E u then c s * c u else 0) := by
    intro s u
    split_ifs with hdisj
    · exact Finset.sum_nonneg fun w _ => hnn w s u
    · obtain ⟨w0, hw1, hw2⟩ := Finset.not_disjoint_iff.1 hdisj
      calc c s * c u = (if w0 ∈ E s ∧ w0 ∈ E u then c s * c u else 0) := by simp [hw1, hw2]
        _ ≤ ∑ w : V, (if w ∈ E s ∧ w ∈ E u then c s * c u else 0) :=
            Finset.single_le_sum (fun w _ => hnn w s u) (Finset.mem_univ w0)
  have hper : ∀ w : V, ∑ s : S, ∑ u : S, (if w ∈ E s ∧ w ∈ E u then c s * c u else 0)
      = (∑ s ∈ Finset.univ.filter (fun s => w ∈ E s), c s) ^ 2 := by
    intro w
    have hF : ∀ s : S, ∑ u : S, (if w ∈ E s ∧ w ∈ E u then c s * c u else 0)
        = (if w ∈ E s then c s * ∑ u ∈ Finset.univ.filter (fun u => w ∈ E u), c u else 0) := by
      intro s
      by_cases hs : w ∈ E s
      · simp only [hs, true_and, ite_true]
        rw [Finset.mul_sum, Finset.sum_filter]
      · simp [hs]
    rw [Finset.sum_congr rfl fun s _ => hF s, ← Finset.sum_filter, sq, Finset.sum_mul]
  calc ∑ s : S, ∑ u : S, (if Disjoint (E s) (E u) then 0 else c s * c u)
      ≤ ∑ s : S, ∑ u : S, ∑ w : V, (if w ∈ E s ∧ w ∈ E u then c s * c u else 0) :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun u _ => hstep s u
    _ = ∑ w : V, ∑ s : S, ∑ u : S, (if w ∈ E s ∧ w ∈ E u then c s * c u else 0) := by
        have hswap : ∀ s : S,
            ∑ u : S, ∑ w : V, (if w ∈ E s ∧ w ∈ E u then c s * c u else 0)
              = ∑ w : V, ∑ u : S, (if w ∈ E s ∧ w ∈ E u then c s * c u else 0) :=
          fun _ => Finset.sum_comm
        rw [Finset.sum_congr rfl fun s _ => hswap s]
        exact Finset.sum_comm
    _ = ∑ w : V, (∑ s ∈ Finset.univ.filter (fun s => w ∈ E s), c s) ^ 2 :=
        Finset.sum_congr rfl fun w _ => hper w

/-! ### The variance of a weighted sum whose covariances are supported on overlapping sites -/

theorem variance_sum_le_of_disjoint_support {S V : Type*} [Fintype S] [Fintype V] [DecidableEq V]
    [IsFiniteMeasure μ] (E : S → Finset V) {W : S → Ω → ℝ} {c : S → ℝ} {κ : ℝ}
    (hc : ∀ s, 0 ≤ c s) (hκ : 0 ≤ κ)
    (hmem : ∀ s, MemLp (W s) 2 μ)
    (hbdd : ∀ s u, |cov[W s, W u; μ]| ≤ κ)
    (hzero : ∀ s u, Disjoint (E s) (E u) → cov[W s, W u; μ] = 0) :
    variance (fun ω => ∑ s, c s * W s ω) μ
      ≤ κ * ∑ w : V, (∑ s ∈ Finset.univ.filter (fun s => w ∈ E s), c s) ^ 2 := by
  classical
  rw [variance_fun_sum (fun s => (hmem s).const_mul _)]
  have hterm : ∀ s u : S, cov[fun ω => c s * W s ω, fun ω => c u * W u ω; μ]
      ≤ κ * (if Disjoint (E s) (E u) then 0 else c s * c u) := by
    intro s u
    rw [covariance_const_mul_left, covariance_const_mul_right]
    split_ifs with hdisj
    · rw [hzero s u hdisj]; simp
    · calc c s * (c u * cov[W s, W u; μ]) ≤ |c s * (c u * cov[W s, W u; μ])| := le_abs_self _
        _ = c s * c u * |cov[W s, W u; μ]| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (hc s), abs_of_nonneg (hc u)]; ring
        _ ≤ c s * c u * κ := mul_le_mul_of_nonneg_left (hbdd s u) (mul_nonneg (hc s) (hc u))
        _ = κ * (c s * c u) := by ring
  calc ∑ s : S, ∑ u : S, cov[fun ω => c s * W s ω, fun ω => c u * W u ω; μ]
      ≤ ∑ s : S, ∑ u : S, κ * (if Disjoint (E s) (E u) then 0 else c s * c u) :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun u _ => hterm s u
    _ = κ * ∑ s : S, ∑ u : S, (if Disjoint (E s) (E u) then 0 else c s * c u) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => (Finset.mul_sum _ _ _).symm
    _ ≤ κ * ∑ w : V, (∑ s ∈ Finset.univ.filter (fun s => w ∈ E s), c s) ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_shared_le_sum_site_sq E c hc) hκ


/-- A weighted sum of random variables whose variances are all at most `κ` has variance at
most `(∑|c|)²κ`. -/
theorem variance_weighted_sum_le {P : Type*} [Fintype P] [IsFiniteMeasure μ]
    {Z : P → Ω → ℝ} {c : P → ℝ} {κ : ℝ}
    (hmem : ∀ p, MemLp (Z p) 2 μ) (hvar : ∀ p, variance (Z p) μ ≤ κ) :
    variance (fun ω => ∑ p, c p * Z p ω) μ ≤ (∑ p, |c p|) ^ 2 * κ := by
  classical
  have hmem' : ∀ p, MemLp (fun ω => c p * Z p ω) 2 μ := fun p => (hmem p).const_mul _
  rw [variance_fun_sum hmem']
  have hcov : ∀ p q : P, cov[fun ω => c p * Z p ω, fun ω => c q * Z q ω; μ]
      ≤ |c p| * |c q| * κ := by
    intro p q
    rw [covariance_const_mul_left, covariance_const_mul_right]
    have h := abs_covariance_le_of_variance_le (hmem p) (hmem q) (hvar p) (hvar q)
    have hκ : (0:ℝ) ≤ κ := le_trans (variance_nonneg (Z p) μ) (hvar p)
    calc c p * (c q * cov[Z p, Z q; μ]) ≤ |c p * (c q * cov[Z p, Z q; μ])| := le_abs_self _
      _ = |c p| * |c q| * |cov[Z p, Z q; μ]| := by rw [abs_mul, abs_mul]; ring
      _ ≤ |c p| * |c q| * κ :=
          mul_le_mul_of_nonneg_left h (by positivity)
  calc ∑ p, ∑ q, cov[fun ω => c p * Z p ω, fun ω => c q * Z q ω; μ]
      ≤ ∑ p : P, ∑ q : P, |c p| * |c q| * κ :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hcov p q
    _ = (∑ p, |c p|) ^ 2 * κ := by
        rw [sq, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]

/-- `Var(A+B) ≤ 2 Var(A) + 2 𝔼[B²]`: the split of `X` into its matched and unmatched parts. -/
theorem variance_add_le_two_mul [IsProbabilityMeasure μ] {A B : Ω → ℝ}
    (hA : MemLp A 2 μ) (hB : MemLp B 2 μ) :
    variance (fun ω => A ω + B ω) μ ≤ 2 * variance A μ + 2 * ∫ ω, (B ω) ^ 2 ∂μ := by
  have hadd : variance (fun ω => A ω + B ω) μ
      = variance A μ + 2 * cov[A, B; μ] + variance B μ := variance_fun_add hA hB
  have hsub : variance (A - B) μ = variance A μ - 2 * cov[A, B; μ] + variance B μ :=
    variance_sub hA hB
  have h2 : (0:ℝ) ≤ variance (A - B) μ := variance_nonneg _ _
  have hBsq : variance B μ ≤ ∫ ω, (B ω) ^ 2 ∂μ := by
    have := variance_le_expectation_sq (μ := μ) (X := B) hB.aestronglyMeasurable
    simpa using this
  linarith


/-! ### Factorization over site sets, and the fourth moments of `π^γ_s` -/

/-- `𝔼[∏_{v ∈ E} g_v(U_v)] = ∏_{v ∈ E} 𝔼[g_v(U_v)]`. -/
theorem integral_prod_eq_prod_integral (h : IsBasisSystem μ U ψ Rpos B₀)
    {E : Finset V} {g : V → ℝ → ℝ} (hg : ∀ v, Measurable (g v)) :
    ∫ ω, ∏ v ∈ E, g v (U v ω) ∂μ = ∏ v ∈ E, ∫ ω, g v (U v ω) ∂μ := by
  classical
  have hP : IsProbabilityMeasure μ := h.isProbabilityMeasure
  set G : V → ℝ → ℝ := fun v x => if v ∈ E then g v x else 1 with hGdef
  have hmG : ∀ v, Measurable (G v) := by
    intro v
    by_cases hv : v ∈ E <;> simp [hGdef, hv, hg]
  have hpoint : ∀ ω, (∏ v ∈ E, g v (U v ω)) = ∏ v : V, G v (U v ω) := by
    intro ω
    rw [hGdef]
    simp only [Finset.prod_ite_mem_eq]
  have hint : ∫ ω, ∏ v : V, G v (U v ω) ∂μ = ∏ v : V, ∫ ω, G v (U v ω) ∂μ :=
    h.indep.integral_fun_prod_comp (fun v => (h.measurable_latent v).aemeasurable)
      (fun v => (hmG v).aestronglyMeasurable)
  have hfac : ∀ v : V, ∫ ω, G v (U v ω) ∂μ = if v ∈ E then ∫ ω, g v (U v ω) ∂μ else 1 := by
    intro v
    by_cases hv : v ∈ E <;> simp [hGdef, hv]
  simp only [hpoint]
  rw [hint]
  simp only [hfac, Finset.prod_ite_mem_eq]

section Components

variable {Γ : Type*} {S : Γ → Type*} [∀ γ, Fintype (S γ)] {I : Type*} [Fintype I]
variable {sites : ∀ γ, S γ → Finset V} {rIdx : Γ → V → R} {arr : ∀ γ, S γ → I → ℝ}

omit [∀ γ, Fintype (S γ)] in
/-- `𝔼[(π^γ_s)²] = 1`. -/
theorem integral_basisProd_sq (h : IsBasisSystem μ U ψ Rpos B₀) (γ : Γ) (s : S γ) :
    ∫ ω, basisProd U ψ sites rIdx γ s ω ^ 2 ∂μ = 1 := by
  have hpt : (fun ω => basisProd U ψ sites rIdx γ s ω ^ 2)
      = fun ω => ∏ w ∈ sites γ s, ψ (rIdx γ w) (U w ω) ^ 2 := by
    funext ω
    simp only [basisProd]
    rw [← Finset.prod_pow]
  rw [hpt, integral_prod_eq_prod_integral (g := fun w x => ψ (rIdx γ w) x ^ 2) h
    (fun w => ((h.measurable_psi (rIdx γ w)).pow_const 2))]
  refine Finset.prod_eq_one fun w _ => ?_
  have := h.integral_mul w (rIdx γ w) (rIdx γ w)
  simpa [pow_two] using this

omit [DecidableEq V] [∀ γ, Fintype (S γ)] in
/-- `𝔼[(π^γ_s)²(π^{γ'}_{s'})²] = 1` when the two site sets are disjoint. -/
theorem integral_basisProd_sq_mul_sq_of_disjoint (h : IsBasisSystem μ U ψ Rpos B₀)
    {γ γ' : Γ} {s : S γ} {s' : S γ'} (hdisj : Disjoint (sites γ s) (sites γ' s')) :
    ∫ ω, basisProd U ψ sites rIdx γ s ω ^ 2 * basisProd U ψ sites rIdx γ' s' ω ^ 2 ∂μ = 1 := by
  classical
  set g : V → ℝ → ℝ := fun w x => if w ∈ sites γ s then ψ (rIdx γ w) x ^ 2
    else ψ (rIdx γ' w) x ^ 2 with hgdef
  have hmg : ∀ w, Measurable (g w) := by
    intro w
    by_cases hw : w ∈ sites γ s <;>
      simp [hgdef, hw, (h.measurable_psi _).pow_const 2]
  have hpt : ∀ ω, basisProd U ψ sites rIdx γ s ω ^ 2 * basisProd U ψ sites rIdx γ' s' ω ^ 2
      = ∏ w ∈ sites γ s ∪ sites γ' s', g w (U w ω) := by
    intro ω
    rw [Finset.prod_union hdisj]
    simp only [basisProd, ← Finset.prod_pow]
    congr 1
    · exact Finset.prod_congr rfl fun w hw => by simp [hgdef, hw]
    · refine Finset.prod_congr rfl fun w hw => ?_
      have hw' : w ∉ sites γ s := Finset.disjoint_right.1 hdisj hw
      simp [hgdef, hw']
  simp only [hpt]
  rw [integral_prod_eq_prod_integral h hmg]
  refine Finset.prod_eq_one fun w hw => ?_
  by_cases hw1 : w ∈ sites γ s
  · have := h.integral_mul w (rIdx γ w) (rIdx γ w)
    simpa [hgdef, hw1, pow_two] using this
  · have := h.integral_mul w (rIdx γ' w) (rIdx γ' w)
    simpa [hgdef, hw1, pow_two] using this

omit [DecidableEq V] [∀ γ, Fintype (S γ)] in
/-- `(π^γ_s)²` is bounded, hence in `L²`. -/
theorem memLp_basisProd_sq (h : IsBasisSystem μ U ψ Rpos B₀) (γ : Γ) (s : S γ) :
    MemLp (fun ω => basisProd U ψ sites rIdx γ s ω ^ 2) 2 μ := by
  have hP : IsProbabilityMeasure μ := h.isProbabilityMeasure
  refine MemLp.of_bound
    (((measurable_basisProd h γ s).pow_const 2).aestronglyMeasurable)
    ((max B₀ 1 ^ Fintype.card V) ^ 2) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_pow, sq, sq]
  have hb := abs_basisProd_le (sites := sites) (rIdx := rIdx) h γ s ω
  exact mul_le_mul hb hb (abs_nonneg _) (by positivity)

omit [DecidableEq V] [∀ γ, Fintype (S γ)] in
/-- `Var[(π^γ_s)²] ≤ max(B₀,1)^{4M}` when every site set has at most `M` elements. -/
theorem variance_basisProd_sq_le_ofCard (h : IsBasisSystem μ U ψ Rpos B₀) {M : ℕ}
    (hlev : ∀ (g : Γ) (x : S g), (sites g x).card ≤ M) (γ : Γ) (s : S γ) :
    variance (fun ω => basisProd U ψ sites rIdx γ s ω ^ 2) μ
      ≤ ((max B₀ 1 ^ M) ^ 2) ^ 2 := by
  have hP : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have hmem := memLp_basisProd_sq (sites := sites) (rIdx := rIdx) h γ s
  refine le_trans (variance_le_expectation_sq hmem.aestronglyMeasurable) ?_
  have hint : Integrable (fun ω => (basisProd U ψ sites rIdx γ s ω ^ 2) ^ 2) μ :=
    hmem.integrable_sq
  have hbnd : ∀ ω, (basisProd U ψ sites rIdx γ s ω ^ 2) ^ 2
      ≤ ((max B₀ 1 ^ M) ^ 2) ^ 2 := by
    intro ω
    have hb := abs_basisProd_le_ofCard (sites := sites) (rIdx := rIdx) h hlev γ s ω
    have h1 : basisProd U ψ sites rIdx γ s ω ^ 2 ≤ (max B₀ 1 ^ M) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    have h0 : (0:ℝ) ≤ basisProd U ψ sites rIdx γ s ω ^ 2 := sq_nonneg _
    exact pow_le_pow_left₀ h0 h1 2
  have hrw : μ[(fun ω => basisProd U ψ sites rIdx γ s ω ^ 2) ^ 2]
      = ∫ ω, (basisProd U ψ sites rIdx γ s ω ^ 2) ^ 2 ∂μ := by
    simp only [Pi.pow_apply]
  rw [hrw]
  calc ∫ ω, (basisProd U ψ sites rIdx γ s ω ^ 2) ^ 2 ∂μ
      ≤ ∫ _ω, ((max B₀ 1 ^ M) ^ 2) ^ 2 ∂μ :=
        integral_mono hint (integrable_const _) hbnd
    _ = ((max B₀ 1 ^ M) ^ 2) ^ 2 := by simp


omit [DecidableEq V] [∀ γ, Fintype (S γ)] in
/-- `Var[(π^γ_s)²] ≤ max(B₀,1)^{4|V|}`. -/
theorem variance_basisProd_sq_le (h : IsBasisSystem μ U ψ Rpos B₀) (γ : Γ) (s : S γ) :
    variance (fun ω => basisProd U ψ sites rIdx γ s ω ^ 2) μ
      ≤ ((max B₀ 1 ^ Fintype.card V) ^ 2) ^ 2 := by
  apply variance_basisProd_sq_le_ofCard (M := Fintype.card V) <;>
    first
      | assumption
      | exact fun _ _ => Finset.card_le_univ _
      | exact fun _ => Finset.card_le_univ _
omit [∀ γ, Fintype (S γ)] in
/-- The covariance of two squared basis products vanishes when their site sets are disjoint. -/
theorem covariance_basisProd_sq_eq_zero_of_disjoint (h : IsBasisSystem μ U ψ Rpos B₀)
    {γ γ' : Γ} {s : S γ} {s' : S γ'} (hdisj : Disjoint (sites γ s) (sites γ' s')) :
    cov[fun ω => basisProd U ψ sites rIdx γ s ω ^ 2,
        fun ω => basisProd U ψ sites rIdx γ' s' ω ^ 2; μ] = 0 := by
  have hP : IsProbabilityMeasure μ := h.isProbabilityMeasure
  rw [covariance_eq_sub (memLp_basisProd_sq (sites := sites) (rIdx := rIdx) h γ s)
    (memLp_basisProd_sq (sites := sites) (rIdx := rIdx) h γ' s')]
  have h1 : μ[(fun ω => basisProd U ψ sites rIdx γ s ω ^ 2) *
      (fun ω => basisProd U ψ sites rIdx γ' s' ω ^ 2)] = 1 :=
    integral_basisProd_sq_mul_sq_of_disjoint h hdisj
  rw [h1, integral_basisProd_sq (sites := sites) (rIdx := rIdx) h γ s,
    integral_basisProd_sq (sites := sites) (rIdx := rIdx) h γ' s']
  ring

end Components

/-! ### The matched part `Ξᵐ_{γγ} = ∑_s G_{ss}((π^γ_s)² − 1)` -/

section MatchedPart

variable {Γ : Type*} {S : Γ → Type*} [∀ γ, Fintype (S γ)] {I : Type*} [Fintype I]
variable {sites : ∀ γ, S γ → Finset V} {rIdx : Γ → V → R} {arr : ∀ γ, S γ → I → ℝ}

/-- `G_{ss} = ∑_i (v^γ_{(s,i)})²`, the diagonal of the Gram matrix. -/
noncomputable def gramDiag (arr : ∀ γ, S γ → I → ℝ) (γ : Γ) (s : S γ) : ℝ :=
  ∑ i : I, arr γ s i ^ 2

omit [∀ γ, Fintype (S γ)] in
theorem gramDiag_nonneg (arr : ∀ γ, S γ → I → ℝ) (γ : Γ) (s : S γ) :
    0 ≤ gramDiag arr γ s :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `∑_s G_{ss} = tot(γ)`. -/
theorem sum_gramDiag (arr : ∀ γ, S γ → I → ℝ) (γ : Γ) :
    ∑ s : S γ, gramDiag arr γ s = rectFrobSq (arr γ) := rfl

/-- `Ξᵐ_{γγ} = ∑_s G_{ss}((π^γ_s)² − 1)`, the centered matched part of `X_{γγ}`. -/
noncomputable def matchedPart (U : V → Ω → ℝ) (ψ : R → ℝ → ℝ)
    (sites : ∀ γ, S γ → Finset V) (rIdx : Γ → V → R) (arr : ∀ γ, S γ → I → ℝ)
    (γ : Γ) : Ω → ℝ :=
  fun ω => ∑ s : S γ, gramDiag arr γ s * (basisProd U ψ sites rIdx γ s ω ^ 2 - 1)

/-- The variance of the matched part, bounded by the squared site-fibre sums of `G_{ss}`, when
every site set has at most `M` elements. -/
theorem variance_matchedPart_le_ofCard (h : IsBasisSystem μ U ψ Rpos B₀) {M : ℕ}
    (hlev : ∀ (g : Γ) (x : S g), (sites g x).card ≤ M) (γ : Γ) :
    variance (matchedPart U ψ sites rIdx arr γ) μ
      ≤ ((max B₀ 1 ^ M) ^ 2) ^ 2 *
        ∑ w : V, (∑ s ∈ Finset.univ.filter (fun s => w ∈ sites γ s), gramDiag arr γ s) ^ 2 := by
  classical
  have hP : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have hpt : matchedPart U ψ sites rIdx arr γ
      = fun ω => (∑ s : S γ, gramDiag arr γ s * basisProd U ψ sites rIdx γ s ω ^ 2)
          - ∑ s : S γ, gramDiag arr γ s := by
    funext ω
    simp only [matchedPart, mul_sub, mul_one]
    rw [Finset.sum_sub_distrib]
  rw [hpt]
  have hmeas : Measurable
      (fun ω => ∑ s : S γ, gramDiag arr γ s * basisProd U ψ sites rIdx γ s ω ^ 2) :=
    Finset.measurable_sum _ fun s _ => ((measurable_basisProd h γ s).pow_const 2).const_mul _
  rw [variance_sub_const hmeas.aestronglyMeasurable]
  refine variance_sum_le_of_disjoint_support (sites γ) (gramDiag_nonneg arr γ) (by positivity)
    (fun s => memLp_basisProd_sq (sites := sites) (rIdx := rIdx) h γ s) (fun s u => ?_)
    (fun s u hdisj => covariance_basisProd_sq_eq_zero_of_disjoint h hdisj)
  exact abs_covariance_le_of_variance_le
    (memLp_basisProd_sq (sites := sites) (rIdx := rIdx) h γ s)
    (memLp_basisProd_sq (sites := sites) (rIdx := rIdx) h γ u)
    (variance_basisProd_sq_le_ofCard (sites := sites) (rIdx := rIdx) h hlev γ s)
    (variance_basisProd_sq_le_ofCard (sites := sites) (rIdx := rIdx) h hlev γ u)


/-- The variance of the matched part, bounded by the squared site-fibre sums of `G_{ss}`. -/
theorem variance_matchedPart_le (h : IsBasisSystem μ U ψ Rpos B₀) (γ : Γ) :
    variance (matchedPart U ψ sites rIdx arr γ) μ
      ≤ ((max B₀ 1 ^ Fintype.card V) ^ 2) ^ 2 *
        ∑ w : V, (∑ s ∈ Finset.univ.filter (fun s => w ∈ sites γ s), gramDiag arr γ s) ^ 2 := by
  apply variance_matchedPart_le_ofCard (M := Fintype.card V) <;>
    first
      | assumption
      | exact fun _ _ => Finset.card_le_univ _
      | exact fun _ => Finset.card_le_univ _
/-- If the diagonal of `F Fᵀ` is `Sg`, then `∑_j Sg_j² ≤ ‖F Fᵀ‖_F²`. -/
theorem sum_sq_of_diag_le {N C : Type*} [Fintype N] [Fintype C]
    (F : Matrix N C ℝ) (Sg : N → ℝ) (hdiag : ∀ j, (F * Fᵀ) j j = Sg j) :
    ∑ j : N, (Sg j) ^ 2 ≤ rectFrobNorm (F * Fᵀ) ^ 2 := by
  rw [rectFrobNorm_sq]
  calc ∑ j : N, (Sg j) ^ 2 = ∑ j : N, ((F * Fᵀ) j j) ^ 2 :=
        Finset.sum_congr rfl fun j _ => by rw [hdiag j]
    _ ≤ rectFrobSq (F * Fᵀ) := sum_sq_diag_le_rectFrobSq _

end MatchedPart

/-! ### The matched part over the sites `Σ k, 𝒩_k` -/

section StepTwo

variable {K : Type*} [Fintype K] [DecidableEq K] {N : K → Type*}
  [∀ k, Fintype (N k)] [∀ k, DecidableEq (N k)]
variable {Γ : Type*} {S : Γ → Type*} [∀ γ, Fintype (S γ)] {I : Type*} [Fintype I]

/-- The variance of the matched part over the sites `Σ k, 𝒩_k`, given a bound on each
coordinate's fibre sum, when every site set has at most `M` elements. -/
theorem variance_matchedPart_le_bnd_ofCard
    {U : Site K N → Ω → ℝ} {ψ : R → ℝ → ℝ} {Rpos : Set R} {B₀ : ℝ}
    {sites : ∀ γ, S γ → Finset (Site K N)} {rIdx : Γ → Site K N → R}
    {arr : ∀ γ, S γ → I → ℝ} {M : ℕ}
    (h : IsBasisSystem μ U ψ Rpos B₀)
    (hlev : ∀ (g : Γ) (x : S g), (sites g x).card ≤ M) (γ : Γ) {bnd : ℝ}
    (hstep2 : ∀ k : K, ∑ j : N k,
        (∑ s ∈ Finset.univ.filter (fun s => (⟨k, j⟩ : Site K N) ∈ sites γ s),
          gramDiag arr γ s) ^ 2 ≤ bnd) :
    variance (matchedPart U ψ sites rIdx arr γ) μ
      ≤ ((max B₀ 1 ^ M) ^ 2) ^ 2 * ((Fintype.card K : ℝ) * bnd) := by
  classical
  refine le_trans (variance_matchedPart_le_ofCard h hlev γ) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hsplit : ∑ w : Site K N,
      (∑ s ∈ Finset.univ.filter (fun s => w ∈ sites γ s), gramDiag arr γ s) ^ 2
      = ∑ k : K, ∑ j : N k,
        (∑ s ∈ Finset.univ.filter (fun s => (⟨k, j⟩ : Site K N) ∈ sites γ s),
          gramDiag arr γ s) ^ 2 := Fintype.sum_sigma _
  rw [hsplit]
  calc ∑ k : K, ∑ j : N k,
        (∑ s ∈ Finset.univ.filter (fun s => (⟨k, j⟩ : Site K N) ∈ sites γ s),
          gramDiag arr γ s) ^ 2
      ≤ ∑ _k : K, bnd := Finset.sum_le_sum fun k _ => hstep2 k
    _ = (Fintype.card K : ℝ) * bnd := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]


/-- The variance of the matched part over the sites `Σ k, 𝒩_k`, given a bound on each
coordinate's fibre sum. -/
theorem variance_matchedPart_le_bnd
    {U : Site K N → Ω → ℝ} {ψ : R → ℝ → ℝ} {Rpos : Set R} {B₀ : ℝ}
    {sites : ∀ γ, S γ → Finset (Site K N)} {rIdx : Γ → Site K N → R}
    {arr : ∀ γ, S γ → I → ℝ}
    (h : IsBasisSystem μ U ψ Rpos B₀) (γ : Γ) {bnd : ℝ}
    (hstep2 : ∀ k : K, ∑ j : N k,
        (∑ s ∈ Finset.univ.filter (fun s => (⟨k, j⟩ : Site K N) ∈ sites γ s),
          gramDiag arr γ s) ^ 2 ≤ bnd) :
    variance (matchedPart U ψ sites rIdx arr γ) μ
      ≤ ((max B₀ 1 ^ Fintype.card (Site K N)) ^ 2) ^ 2 * ((Fintype.card K : ℝ) * bnd) := by
  apply variance_matchedPart_le_bnd_ofCard (M := Fintype.card (Site K N)) <;>
    first
      | assumption
      | exact fun _ _ => Finset.card_le_univ _
      | exact fun _ => Finset.card_le_univ _
/-- The matched-part bound in the `cut(γ)²` form, given the fibre-sum bound `hstep2`, when
every site set has at most `M` elements. -/
theorem variance_matchedPart_le_cut_ofCard
    {U : Site K N → Ω → ℝ} {ψ : R → ℝ → ℝ} {Rpos : Set R} {B₀ : ℝ}
    {sites : ∀ γ, S γ → Finset (Site K N)} {rIdx : Γ → Site K N → R}
    {arr : ∀ γ, S γ → I → ℝ} {M : ℕ}
    (h : IsBasisSystem μ U ψ Rpos B₀)
    (hlev : ∀ (g : Γ) (x : S g), (sites g x).card ≤ M) (γ : Γ) {cutγ : ℝ}
    (hstep2 : ∀ k : K, ∑ j : N k,
        (∑ s ∈ Finset.univ.filter (fun s => (⟨k, j⟩ : Site K N) ∈ sites γ s),
          gramDiag arr γ s) ^ 2 ≤ cutγ ^ 2) :
    variance (matchedPart U ψ sites rIdx arr γ) μ
      ≤ ((max B₀ 1 ^ M) ^ 2) ^ 2 * ((Fintype.card K : ℝ) * cutγ ^ 2) :=
  variance_matchedPart_le_bnd_ofCard h hlev γ hstep2

/-- The matched-part bound in the `cut(γ)²` form, given the fibre-sum bound `hstep2`. -/
theorem variance_matchedPart_le_cut
    {U : Site K N → Ω → ℝ} {ψ : R → ℝ → ℝ} {Rpos : Set R} {B₀ : ℝ}
    {sites : ∀ γ, S γ → Finset (Site K N)} {rIdx : Γ → Site K N → R}
    {arr : ∀ γ, S γ → I → ℝ}
    (h : IsBasisSystem μ U ψ Rpos B₀) (γ : Γ) {cutγ : ℝ}
    (hstep2 : ∀ k : K, ∑ j : N k,
        (∑ s ∈ Finset.univ.filter (fun s => (⟨k, j⟩ : Site K N) ∈ sites γ s),
          gramDiag arr γ s) ^ 2 ≤ cutγ ^ 2) :
    variance (matchedPart U ψ sites rIdx arr γ) μ
      ≤ ((max B₀ 1 ^ Fintype.card (Site K N)) ^ 2) ^ 2 * ((Fintype.card K : ℝ) * cutγ ^ 2) := by
  apply variance_matchedPart_le_cut_ofCard (M := Fintype.card (Site K N)) <;>
    first
      | assumption
      | exact fun _ _ => Finset.card_le_univ _
      | exact fun _ => Finset.card_le_univ _

end StepTwo

/-! ### The decomposition `X_{γγ'} = 𝔼[X_{γγ'}] + Ξᵐ_{γγ'} + Ξᵘ_{γγ'}`

`Ξᵘ` is defined directly as the sum over the unmatched pairs. -/

section Decomposition

variable {Γ : Type*} {S : Γ → Type*} [∀ γ, Fintype (S γ)] {I : Type*} [Fintype I]
  {τ : Type*} [DecidableEq τ]
variable {sites : ∀ γ, S γ → Finset V} {rIdx : Γ → V → R} {arr : ∀ γ, S γ → I → ℝ}
  {tag : Γ → τ}

/-- `G_{ss'} = ∑_i v^γ_{(s,i)}v^{γ'}_{(s',i)}`, the Gram matrix. -/
noncomputable def gramEntry (arr : ∀ γ, S γ → I → ℝ) (γ γ' : Γ) (s : S γ) (s' : S γ') : ℝ :=
  ∑ i : I, arr γ s i * arr γ' s' i

/-- A pair `(s,s')` is matched when `𝔼[π^γ_sπ^{γ'}_{s'}] ≠ 0`. -/
def IsMatched (sites : ∀ γ, S γ → Finset V) (rIdx : Γ → V → R) (γ γ' : Γ)
    (s : S γ) (s' : S γ') : Prop :=
  sites γ s = sites γ' s' ∧ ∀ w ∈ sites γ s, rIdx γ w = rIdx γ' w

instance decidableIsMatched (sites : ∀ γ, S γ → Finset V) (rIdx : Γ → V → R) (γ γ' : Γ)
    (s : S γ) (s' : S γ') : Decidable (IsMatched sites rIdx γ γ' s s') := by
  unfold IsMatched
  infer_instance

/-- `Ξᵘ_{γγ'} = ∑_{(s,s') unmatched} G_{ss'}π^γ_sπ^{γ'}_{s'}`. -/
noncomputable def unmatchedPart (U : V → Ω → ℝ) (ψ : R → ℝ → ℝ)
    (sites : ∀ γ, S γ → Finset V) (rIdx : Γ → V → R) (arr : ∀ γ, S γ → I → ℝ)
    (tag : Γ → τ) (γ γ' : Γ) : Ω → ℝ :=
  fun ω => if tag γ = tag γ' then
    ∑ s : S γ, ∑ s' : S γ',
      (if IsMatched sites rIdx γ γ' s s' then 0
        else gramEntry arr γ γ' s s' *
          (basisProd U ψ sites rIdx γ s ω * basisProd U ψ sites rIdx γ' s' ω))
    else 0

omit [MeasurableSpace Ω] [Fintype V] [DecidableEq V] [DecidableEq R] [DecidableEq τ] in
/-- Interchanging the order of summation, `X_{γγ'} = ∑_{s,s'}G_{ss'}π^γ_sπ^{γ'}_{s'}`. -/
theorem sum_blockSum_mul (γ γ' : Γ) (ω : Ω) :
    ∑ i : I, blockSum U ψ sites rIdx arr γ i ω * blockSum U ψ sites rIdx arr γ' i ω
      = ∑ s : S γ, ∑ s' : S γ', gramEntry arr γ γ' s s' *
          (basisProd U ψ sites rIdx γ s ω * basisProd U ψ sites rIdx γ' s' ω) := by
  have hexp : ∀ i : I, blockSum U ψ sites rIdx arr γ i ω *
      blockSum U ψ sites rIdx arr γ' i ω
      = ∑ s : S γ, ∑ s' : S γ', (arr γ s i * arr γ' s' i) *
          (basisProd U ψ sites rIdx γ s ω * basisProd U ψ sites rIdx γ' s' ω) := by
    intro i
    simp only [blockSum, Fintype.sum_mul_sum]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => by ring
  simp only [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [gramEntry, Finset.sum_mul]

omit [MeasurableSpace Ω] in
/-- **The decomposition on the diagonal**: `X_{γγ} = tot(γ) + Ξᵐ_{γγ} + Ξᵘ_{γγ}`. -/
theorem cvarEntry_self_eq (hinj : ∀ (γ : Γ) (s s' : S γ), sites γ s = sites γ s' → s = s')
    (γ : Γ) (ω : Ω) :
    cvarEntry U ψ sites rIdx arr tag γ γ ω
      = rectFrobSq (arr γ) + matchedPart U ψ sites rIdx arr γ ω
        + unmatchedPart U ψ sites rIdx arr tag γ γ ω := by
  have hmatch : ∀ s s' : S γ, IsMatched sites rIdx γ γ s s' ↔ s' = s := by
    intro s s'
    constructor
    · rintro ⟨h1, -⟩; exact (hinj γ s s' h1).symm
    · rintro rfl; exact ⟨rfl, fun _ _ => rfl⟩
  have hc : cvarEntry U ψ sites rIdx arr tag γ γ ω
      = ∑ i : I, blockSum U ψ sites rIdx arr γ i ω * blockSum U ψ sites rIdx arr γ i ω := by
    simp [cvarEntry]
  have hu : unmatchedPart U ψ sites rIdx arr tag γ γ ω
      = ∑ s : S γ, ∑ s' : S γ, (if IsMatched sites rIdx γ γ s s' then 0
          else gramEntry arr γ γ s s' *
            (basisProd U ψ sites rIdx γ s ω * basisProd U ψ sites rIdx γ s' ω)) := by
    simp [unmatchedPart]
  rw [hc, hu, sum_blockSum_mul]
  have hkey : ∀ s : S γ, ∑ s' : S γ, gramEntry arr γ γ s s' *
        (basisProd U ψ sites rIdx γ s ω * basisProd U ψ sites rIdx γ s' ω)
      = gramDiag arr γ s * basisProd U ψ sites rIdx γ s ω ^ 2
        + ∑ s' : S γ, (if IsMatched sites rIdx γ γ s s' then 0
            else gramEntry arr γ γ s s' *
              (basisProd U ψ sites rIdx γ s ω * basisProd U ψ sites rIdx γ s' ω)) := by
    intro s
    have hid : ∀ s' : S γ, gramEntry arr γ γ s s' *
        (basisProd U ψ sites rIdx γ s ω * basisProd U ψ sites rIdx γ s' ω)
        = (if IsMatched sites rIdx γ γ s s' then gramEntry arr γ γ s s' *
              (basisProd U ψ sites rIdx γ s ω * basisProd U ψ sites rIdx γ s' ω) else 0)
          + (if IsMatched sites rIdx γ γ s s' then 0
              else gramEntry arr γ γ s s' *
                (basisProd U ψ sites rIdx γ s ω * basisProd U ψ sites rIdx γ s' ω)) := by
      intro s'; split_ifs <;> ring
    rw [Finset.sum_congr rfl fun s' _ => hid s', Finset.sum_add_distrib]
    congr 1
    refine (Finset.sum_eq_single s ?_ ?_).trans ?_
    · intro b _ hb
      have hnm : ¬ IsMatched sites rIdx γ γ s b := fun hm => hb ((hmatch s b).1 hm)
      simp [hnm]
    · intro hb; exact absurd (Finset.mem_univ s) hb
    · have hm : IsMatched sites rIdx γ γ s s := (hmatch s s).2 rfl
      have hgd : gramEntry arr γ γ s s = gramDiag arr γ s :=
        Finset.sum_congr rfl fun i _ => (pow_two (arr γ s i)).symm
      rw [hgd]
      split_ifs
      · ring
  rw [Finset.sum_congr rfl fun s _ => hkey s, Finset.sum_add_distrib, matchedPart]
  have hms : ∑ s : S γ, gramDiag arr γ s * (basisProd U ψ sites rIdx γ s ω ^ 2 - 1)
      = (∑ s : S γ, gramDiag arr γ s * basisProd U ψ sites rIdx γ s ω ^ 2)
        - ∑ s : S γ, gramDiag arr γ s := by
    simp only [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib]
  rw [hms, ← sum_gramDiag arr γ]
  ring

omit [MeasurableSpace Ω] in
/-- **The decomposition off the diagonal**: for `γ ≠ γ'` there are no matched pairs, so
`X_{γγ'} = Ξᵘ_{γγ'}`. -/
theorem cvarEntry_eq_unmatchedPart_of_ne
    (hsep : ∀ (γ γ' : Γ) (s : S γ) (s' : S γ'), tag γ = tag γ' → sites γ s = sites γ' s' →
      (∀ w ∈ sites γ s, rIdx γ w = rIdx γ' w) → γ = γ')
    {γ γ' : Γ} (hne : γ ≠ γ') (ω : Ω) :
    cvarEntry U ψ sites rIdx arr tag γ γ' ω
      = unmatchedPart U ψ sites rIdx arr tag γ γ' ω := by
  by_cases htag : tag γ = tag γ'
  · have hc : cvarEntry U ψ sites rIdx arr tag γ γ' ω
        = ∑ i : I, blockSum U ψ sites rIdx arr γ i ω * blockSum U ψ sites rIdx arr γ' i ω := by
      simp [cvarEntry, htag]
    have hu : unmatchedPart U ψ sites rIdx arr tag γ γ' ω
        = ∑ s : S γ, ∑ s' : S γ', (if IsMatched sites rIdx γ γ' s s' then 0
            else gramEntry arr γ γ' s s' *
              (basisProd U ψ sites rIdx γ s ω * basisProd U ψ sites rIdx γ' s' ω)) := by
      simp [unmatchedPart, htag]
    rw [hc, hu, sum_blockSum_mul]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    have hnm : ¬ IsMatched sites rIdx γ γ' s s' := by
      rintro ⟨h1, h2⟩
      exact hne (hsep γ γ' s s' htag h1 h2)
    simp [hnm]
  · simp [cvarEntry, unmatchedPart, htag]

end Decomposition

/-! ### Clause (b), assembled -/

section Assembly

variable {Γ : Type*} {S : Γ → Type*} [∀ γ, Fintype (S γ)] {I : Type*} [Fintype I]
  {τ : Type*} [DecidableEq τ]
variable {sites : ∀ γ, S γ → Finset V} {rIdx : Γ → V → R} {arr : ∀ γ, S γ → I → ℝ}
  {tag : Γ → τ}

/-- A bounded measurable real function on a finite measure space is in `L²`. -/
theorem memLp_two_of_bound [IsFiniteMeasure μ] {f : Ω → ℝ} {C : ℝ}
    (hf : Measurable f) (hb : ∀ ω, |f ω| ≤ C) : MemLp f 2 μ :=
  MemLp.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hb ω)

omit [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq τ] in
theorem measurable_blockSum (h : IsBasisSystem μ U ψ Rpos B₀) (γ : Γ) (i : I) :
    Measurable (blockSum U ψ sites rIdx arr γ i) :=
  Finset.measurable_sum _ fun s _ => (measurable_basisProd h γ s).const_mul _

omit [Fintype V] [DecidableEq V] in
theorem measurable_cvarEntry (h : IsBasisSystem μ U ψ Rpos B₀) (γ γ' : Γ) :
    Measurable (cvarEntry U ψ sites rIdx arr tag γ γ') := by
  unfold cvarEntry
  refine Measurable.ite (MeasurableSet.const _) ?_ measurable_const
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_blockSum h γ i).mul (measurable_blockSum h γ' i)

omit [DecidableEq V] [∀ γ, Fintype (S γ)] [DecidableEq τ] in
/-- `|π^γ_sπ^{γ'}_{s'}| ≤ max(B₀,1)^{2|V|}`, hence the product is in `L²`. -/
theorem memLp_basisProd_mul (h : IsBasisSystem μ U ψ Rpos B₀) (γ γ' : Γ) (s : S γ) (s' : S γ') :
    MemLp (fun ω => basisProd U ψ sites rIdx γ s ω * basisProd U ψ sites rIdx γ' s' ω) 2 μ := by
  have hP : IsProbabilityMeasure μ := h.isProbabilityMeasure
  refine memLp_two_of_bound
    ((measurable_basisProd h γ s).mul (measurable_basisProd h γ' s'))
    (C := (max B₀ 1 ^ Fintype.card V) * (max B₀ 1 ^ Fintype.card V)) fun ω => ?_
  rw [abs_mul]
  exact mul_le_mul (abs_basisProd_le h γ s ω) (abs_basisProd_le h γ' s' ω) (abs_nonneg _)
    (by positivity)

omit [DecidableEq V] in
theorem memLp_matchedPart (h : IsBasisSystem μ U ψ Rpos B₀) (γ : Γ) :
    MemLp (matchedPart U ψ sites rIdx arr γ) 2 μ := by
  have hP : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have : matchedPart U ψ sites rIdx arr γ
      = fun ω => ∑ s ∈ (Finset.univ : Finset (S γ)),
          gramDiag arr γ s * (basisProd U ψ sites rIdx γ s ω ^ 2 - 1) := rfl
  rw [this]
  refine memLp_finsetSum _ fun s _ => ?_
  exact ((memLp_basisProd_sq (sites := sites) (rIdx := rIdx) h γ s).sub
    (memLp_const 1)).const_mul _

theorem memLp_unmatchedPart (h : IsBasisSystem μ U ψ Rpos B₀) (γ γ' : Γ) :
    MemLp (unmatchedPart U ψ sites rIdx arr tag γ γ') 2 μ := by
  have hP : IsProbabilityMeasure μ := h.isProbabilityMeasure
  by_cases htag : tag γ = tag γ'
  · have hf : unmatchedPart U ψ sites rIdx arr tag γ γ'
        = fun ω => ∑ s ∈ (Finset.univ : Finset (S γ)),
            ∑ s' ∈ (Finset.univ : Finset (S γ')),
              (if IsMatched sites rIdx γ γ' s s' then 0
                else gramEntry arr γ γ' s s' *
                  (basisProd U ψ sites rIdx γ s ω * basisProd U ψ sites rIdx γ' s' ω)) := by
      funext ω; simp [unmatchedPart, htag]
    rw [hf]
    refine memLp_finsetSum _ fun s _ => memLp_finsetSum _ fun s' _ => ?_
    by_cases hm : IsMatched sites rIdx γ γ' s s'
    · have : (fun ω => if IsMatched sites rIdx γ γ' s s' then (0:ℝ)
          else gramEntry arr γ γ' s s' *
            (basisProd U ψ sites rIdx γ s ω * basisProd U ψ sites rIdx γ' s' ω))
          = fun _ => (0:ℝ) := by funext ω; simp [hm]
      rw [this]; exact memLp_const 0
    · have : (fun ω => if IsMatched sites rIdx γ γ' s s' then (0:ℝ)
          else gramEntry arr γ γ' s s' *
            (basisProd U ψ sites rIdx γ s ω * basisProd U ψ sites rIdx γ' s' ω))
          = fun ω => gramEntry arr γ γ' s s' *
              (basisProd U ψ sites rIdx γ s ω * basisProd U ψ sites rIdx γ' s' ω) := by
        funext ω; simp [hm]
      rw [this]
      exact (memLp_basisProd_mul h γ γ' s s').const_mul _
  · have hf : unmatchedPart U ψ sites rIdx arr tag γ γ' = fun _ => (0:ℝ) := by
      funext ω; simp [unmatchedPart, htag]
    rw [hf]; exact memLp_const 0

omit [DecidableEq V] [Fintype I] [DecidableEq τ] in
/-- `|A^γ_i| ≤ ∑_s |v^γ_{(s,i)}| max(B₀,1)^{|V|}`. -/
theorem abs_blockSum_le (h : IsBasisSystem μ U ψ Rpos B₀) (γ : Γ) (i : I) (ω : Ω) :
    |blockSum U ψ sites rIdx arr γ i ω|
      ≤ ∑ s : S γ, |arr γ s i| * (max B₀ 1 ^ Fintype.card V) := by
  simp only [blockSum]
  calc |∑ s : S γ, arr γ s i * basisProd U ψ sites rIdx γ s ω|
      ≤ ∑ s : S γ, |arr γ s i * basisProd U ψ sites rIdx γ s ω| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s : S γ, |arr γ s i| * (max B₀ 1 ^ Fintype.card V) := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_basisProd_le h γ s ω) (abs_nonneg _)

omit [DecidableEq V] in
/-- `X_{γγ'}` is bounded, uniformly in `ω`. -/
theorem abs_cvarEntry_le (h : IsBasisSystem μ U ψ Rpos B₀) (γ γ' : Γ) (ω : Ω) :
    |cvarEntry U ψ sites rIdx arr tag γ γ' ω|
      ≤ ∑ i : I, (∑ s : S γ, |arr γ s i| * (max B₀ 1 ^ Fintype.card V)) *
          (∑ s' : S γ', |arr γ' s' i| * (max B₀ 1 ^ Fintype.card V)) := by
  have hpow : (0:ℝ) ≤ max B₀ 1 ^ Fintype.card V := by positivity
  have hrow : ∀ (g : Γ) (t : S g → I → ℝ) (i : I),
      (0:ℝ) ≤ ∑ s : S g, |t s i| * (max B₀ 1 ^ Fintype.card V) :=
    fun g t i => Finset.sum_nonneg fun s _ => mul_nonneg (abs_nonneg _) hpow
  simp only [cvarEntry]
  split_ifs with htag
  · calc |∑ i : I, blockSum U ψ sites rIdx arr γ i ω * blockSum U ψ sites rIdx arr γ' i ω|
        ≤ ∑ i : I, |blockSum U ψ sites rIdx arr γ i ω * blockSum U ψ sites rIdx arr γ' i ω| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : I, (∑ s : S γ, |arr γ s i| * (max B₀ 1 ^ Fintype.card V)) *
            (∑ s' : S γ', |arr γ' s' i| * (max B₀ 1 ^ Fintype.card V)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_mul (abs_blockSum_le h γ i ω) (abs_blockSum_le h γ' i ω)
            (abs_nonneg _) (hrow γ (arr γ) i)
  · rw [abs_zero]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hrow γ (arr γ) i) (hrow γ' (arr γ') i)

omit [DecidableEq V] in
/-- `X_{γγ'}` is in `L²`. -/
theorem memLp_cvarEntry (h : IsBasisSystem μ U ψ Rpos B₀) (γ γ' : Γ) :
    MemLp (cvarEntry U ψ sites rIdx arr tag γ γ') 2 μ := by
  have hP : IsProbabilityMeasure μ := h.isProbabilityMeasure
  exact memLp_two_of_bound (measurable_cvarEntry h γ γ') (abs_cvarEntry_le h γ γ')

/-- The variance bound for a diagonal entry. -/
theorem variance_cvarEntry_self_le (h : IsBasisSystem μ U ψ Rpos B₀)
    (hinj : ∀ (γ : Γ) (s s' : S γ), sites γ s = sites γ s' → s = s') (γ : Γ) {a b : ℝ}
    (hmatch : variance (matchedPart U ψ sites rIdx arr γ) μ ≤ a)
    (hunm : ∫ ω, (unmatchedPart U ψ sites rIdx arr tag γ γ ω) ^ 2 ∂μ ≤ b) :
    variance (cvarEntry U ψ sites rIdx arr tag γ γ) μ ≤ 2 * a + 2 * b := by
  have hP : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have hfun : cvarEntry U ψ sites rIdx arr tag γ γ
      = fun ω => rectFrobSq (arr γ) + (matchedPart U ψ sites rIdx arr γ ω
        + unmatchedPart U ψ sites rIdx arr tag γ γ ω) := by
    funext ω
    rw [cvarEntry_self_eq hinj γ ω]
    ring
  have hmemXi : MemLp (fun ω => matchedPart U ψ sites rIdx arr γ ω
      + unmatchedPart U ψ sites rIdx arr tag γ γ ω) 2 μ :=
    (memLp_matchedPart h γ).add (memLp_unmatchedPart h γ γ)
  rw [hfun, variance_const_add (X := fun ω => matchedPart U ψ sites rIdx arr γ ω
      + unmatchedPart U ψ sites rIdx arr tag γ γ ω) hmemXi.aestronglyMeasurable
      (rectFrobSq (arr γ))]
  refine le_trans (variance_add_le_two_mul (memLp_matchedPart h γ)
    (memLp_unmatchedPart h γ γ)) ?_
  linarith [hmatch, hunm]

/-- The variance bound for an off-diagonal entry. -/
theorem variance_cvarEntry_ne_le (h : IsBasisSystem μ U ψ Rpos B₀)
    (hsep : ∀ (γ γ' : Γ) (s : S γ) (s' : S γ'), tag γ = tag γ' → sites γ s = sites γ' s' →
      (∀ w ∈ sites γ s, rIdx γ w = rIdx γ' w) → γ = γ')
    {γ γ' : Γ} (hne : γ ≠ γ') {b : ℝ}
    (hunm : ∫ ω, (unmatchedPart U ψ sites rIdx arr tag γ γ' ω) ^ 2 ∂μ ≤ b) :
    variance (cvarEntry U ψ sites rIdx arr tag γ γ') μ ≤ b := by
  have hP : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have hfun : cvarEntry U ψ sites rIdx arr tag γ γ'
      = unmatchedPart U ψ sites rIdx arr tag γ γ' := by
    funext ω; exact cvarEntry_eq_unmatchedPart_of_ne hsep hne ω
  rw [hfun]
  refine le_trans (variance_le_expectation_sq
    (memLp_unmatchedPart h γ γ').aestronglyMeasurable) ?_
  have hrw : μ[(unmatchedPart U ψ sites rIdx arr tag γ γ') ^ 2]
      = ∫ ω, (unmatchedPart U ψ sites rIdx arr tag γ γ' ω) ^ 2 ∂μ := by
    simp only [Pi.pow_apply]
  rw [hrw]
  exact hunm

/-- **Lemma SM.C.3(b)**, reduced to the two parts: if `Var(Ξᵐ_{γγ}) ≤ a` and
`𝔼[(Ξᵘ_{γγ'})²] ≤ b` for all `γ, γ'`, the variance is at most `|Γ|²(2a + 2b)`. -/
theorem concentration_clause_b [Fintype Γ] [DecidableEq Γ]
    (h : IsBasisSystem μ U ψ Rpos B₀)
    (hinj : ∀ (γ : Γ) (s s' : S γ), sites γ s = sites γ s' → s = s')
    (hsep : ∀ (γ γ' : Γ) (s : S γ) (s' : S γ'), tag γ = tag γ' → sites γ s = sites γ' s' →
      (∀ w ∈ sites γ s, rIdx γ w = rIdx γ' w) → γ = γ')
    {lam : Γ → ℝ} (hlam : ∑ γ, lam γ ^ 2 ≤ 1) {a b : ℝ}
    (hmatch : ∀ γ : Γ, variance (matchedPart U ψ sites rIdx arr γ) μ ≤ a)
    (hunm : ∀ γ γ' : Γ, ∫ ω, (unmatchedPart U ψ sites rIdx arr tag γ γ' ω) ^ 2 ∂μ ≤ b) :
    variance (fun ω => ∑ γ : Γ, ∑ γ' : Γ,
        lam γ * lam γ' * cvarEntry U ψ sites rIdx arr tag γ γ' ω) μ
      ≤ (Fintype.card Γ : ℝ) ^ 2 * (2 * a + 2 * b) := by
  classical
  have hP : IsProbabilityMeasure μ := h.isProbabilityMeasure
  rcases isEmpty_or_nonempty Γ with hE | hN
  · have hzero : (fun ω => ∑ γ : Γ, ∑ γ' : Γ,
        lam γ * lam γ' * cvarEntry U ψ sites rIdx arr tag γ γ' ω) = fun _ => (0:ℝ) := by
      funext ω; simp
    rw [hzero]
    rw [variance_const_fun]
    simp
  · obtain ⟨γ0⟩ := hN
    have ha : (0:ℝ) ≤ a := le_trans (variance_nonneg _ _) (hmatch γ0)
    have hb : (0:ℝ) ≤ b :=
      le_trans (integral_nonneg fun ω => sq_nonneg _) (hunm γ0 γ0)
    -- the per-pair bound
    have hpair : ∀ γ γ' : Γ,
        variance (cvarEntry U ψ sites rIdx arr tag γ γ') μ ≤ 2 * a + 2 * b := by
      intro γ γ'
      by_cases hg : γ = γ'
      · subst hg
        exact variance_cvarEntry_self_le h hinj γ (hmatch γ) (hunm γ γ)
      · exact le_trans (variance_cvarEntry_ne_le h hsep hg (hunm γ γ')) (by linarith)
    -- flatten the double sum
    have hflat : (fun ω => ∑ γ : Γ, ∑ γ' : Γ,
          lam γ * lam γ' * cvarEntry U ψ sites rIdx arr tag γ γ' ω)
        = fun ω => ∑ p : Γ × Γ, (lam p.1 * lam p.2) *
            cvarEntry U ψ sites rIdx arr tag p.1 p.2 ω := by
      funext ω; rw [Fintype.sum_prod_type]
    rw [hflat]
    refine le_trans (variance_weighted_sum_le
      (fun p : Γ × Γ => memLp_cvarEntry h p.1 p.2) (fun p => hpair p.1 p.2)) ?_
    have hT : ∑ p : Γ × Γ, |lam p.1 * lam p.2| = (∑ γ : Γ, |lam γ|) ^ 2 := by
      rw [Fintype.sum_prod_type, sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun γ' _ => abs_mul _ _
    have hT2 : (∑ γ : Γ, |lam γ|) ^ 2 ≤ (Fintype.card Γ : ℝ) := by
      refine le_trans sq_sum_le_card_mul_sum_sq ?_
      rw [Finset.card_univ]
      have habs : ∑ γ : Γ, |lam γ| ^ 2 = ∑ γ : Γ, lam γ ^ 2 :=
        Finset.sum_congr rfl fun γ _ => sq_abs _
      rw [habs]
      calc (Fintype.card Γ : ℝ) * ∑ γ : Γ, lam γ ^ 2
          ≤ (Fintype.card Γ : ℝ) * 1 := mul_le_mul_of_nonneg_left hlam (by positivity)
        _ = (Fintype.card Γ : ℝ) := by ring
    rw [hT]
    refine mul_le_mul_of_nonneg_right ?_ (by linarith)
    exact pow_le_pow_left₀ (sq_nonneg _) hT2 2

/-- **Lemma SM.C.3(b)** in the form `C (max_γ cut(γ)) (max_γ tot(γ))` with
`C = 4|Γ|²Cst`, given per-part bounds `hmatch` and `hunm` with constant `Cst`. -/
theorem concentration_clause_b_cut_tot [Fintype Γ] [DecidableEq Γ]
    (h : IsBasisSystem μ U ψ Rpos B₀)
    (hinj : ∀ (γ : Γ) (s s' : S γ), sites γ s = sites γ s' → s = s')
    (hsep : ∀ (γ γ' : Γ) (s : S γ) (s' : S γ'), tag γ = tag γ' → sites γ s = sites γ' s' →
      (∀ w ∈ sites γ s, rIdx γ w = rIdx γ' w) → γ = γ')
    {lam : Γ → ℝ} (hlam : ∑ γ, lam γ ^ 2 ≤ 1) {Cst cutmax totmax : ℝ}
    (hmatch : ∀ γ : Γ, variance (matchedPart U ψ sites rIdx arr γ) μ
        ≤ Cst * (cutmax * totmax))
    (hunm : ∀ γ γ' : Γ, ∫ ω, (unmatchedPart U ψ sites rIdx arr tag γ γ' ω) ^ 2 ∂μ
        ≤ Cst * (cutmax * totmax)) :
    variance (fun ω => ∑ γ : Γ, ∑ γ' : Γ,
        lam γ * lam γ' * cvarEntry U ψ sites rIdx arr tag γ γ' ω) μ
      ≤ 4 * (Fintype.card Γ : ℝ) ^ 2 * Cst * (cutmax * totmax) := by
  refine le_trans (concentration_clause_b h hinj hsep hlam hmatch hunm) (le_of_eq ?_)
  ring

end Assembly

/-! ### The unmatched part when every site set is a singleton

When `|e_γ| = 2`, each sub-tuple carries exactly one site (hypothesis `hst`). A quadruple
`(s,s',u,u')` with nonzero coefficient and nonzero moment is then either the diagonal one
`(u,u') = (s,s')` or the transposed one `(u,u') = (s',s)`, and both are bounded by Cauchy--Schwarz
and the trace bound. -/

section SingletonSites

/-! #### The four-fold moment `𝔼[π^γ_sπ^{γ'}_{s'}π^γ_uπ^{γ'}_{u'}]` -/

/-- The four-fold moment `𝔼[∏_{j<4} ψ_{r_j}(U_{w_j})]` at sites `w : Fin 4 → V`. -/
noncomputable def quadMoment (μ : Measure Ω) (U : V → Ω → ℝ) (ψ : R → ℝ → ℝ)
    (w : Fin 4 → V) (r : Fin 4 → R) : ℝ :=
  ∫ ω, ∏ j : Fin 4, ψ (r j) (U (w j) ω) ∂μ

/-- The four-fold moment factorizes over the distinct sites among `w 0, …, w 3`. -/
theorem quadMoment_eq_prod (h : IsBasisSystem μ U ψ Rpos B₀) (w : Fin 4 → V) (r : Fin 4 → R) :
    quadMoment μ U ψ w r
      = ∏ v : V, ∫ ω, ∏ j ∈ Finset.univ.filter (fun j => w j = v), ψ (r j) (U v ω) ∂μ := by
  classical
  have hP : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have hmeas : ∀ v : V, Measurable (fun x : ℝ =>
      ∏ j ∈ Finset.univ.filter (fun j => w j = v), ψ (r j) x) := fun v =>
    Finset.measurable_prod _ fun j _ => h.measurable_psi (r j)
  have hpt : ∀ ω, ∏ j : Fin 4, ψ (r j) (U (w j) ω)
      = ∏ v : V, ∏ j ∈ Finset.univ.filter (fun j => w j = v), ψ (r j) (U v ω) := by
    intro ω
    rw [← Finset.prod_fiberwise (Finset.univ : Finset (Fin 4)) w
      (fun j => ψ (r j) (U (w j) ω))]
    refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun j hj => ?_
    rw [(Finset.mem_filter.1 hj).2]
  rw [quadMoment]
  simp only [hpt]
  exact h.indep.integral_fun_prod_comp (fun v => (h.measurable_latent v).aemeasurable)
    (fun v => (hmeas v).aestronglyMeasurable)

/-- The four-fold moment vanishes if some site carries exactly one of the four factors. -/
theorem quadMoment_eq_zero_of_isolated (h : IsBasisSystem μ U ψ Rpos B₀)
    {w : Fin 4 → V} {r : Fin 4 → R} {j : Fin 4}
    (hiso : ∀ j', j' ≠ j → w j' ≠ w j) (hr : r j ∈ Rpos) :
    quadMoment μ U ψ w r = 0 := by
  classical
  rw [quadMoment_eq_prod h]
  refine Finset.prod_eq_zero (Finset.mem_univ (w j)) ?_
  have hfil : (Finset.univ.filter (fun j' => w j' = w j)) = {j} := by
    ext j'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hj => by by_contra hne; exact hiso j' hne hj, by rintro rfl; rfl⟩
  simp only [hfil, Finset.prod_singleton]
  exact h.integral_eq_zero (w j) hr

/-- The four-fold moment vanishes if exactly two slots `j ≠ k` share a site and their indices
differ. -/
theorem quadMoment_eq_zero_of_pair (h : IsBasisSystem μ U ψ Rpos B₀)
    {w : Fin 4 → V} {r : Fin 4 → R} {j k : Fin 4} (hjk : j ≠ k) (hw : w k = w j)
    (hiso : ∀ l, l ≠ j → l ≠ k → w l ≠ w j) (hr : r j ≠ r k) :
    quadMoment μ U ψ w r = 0 := by
  classical
  rw [quadMoment_eq_prod h]
  refine Finset.prod_eq_zero (Finset.mem_univ (w j)) ?_
  have hfil : (Finset.univ.filter (fun l => w l = w j)) = {j, k} := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hl
      by_contra hcon
      rw [not_or] at hcon
      exact hiso l hcon.1 hcon.2 hl
    · rintro (rfl | rfl)
      · rfl
      · exact hw
  simp only [hfil, Finset.prod_pair hjk]
  rw [h.integral_mul (w j) (r j) (r k)]
  simp [hr]

omit [Fintype V] [DecidableEq V] in
/-- `|quadMoment| ≤ max(B_0,1)^4`. -/
theorem abs_quadMoment_le (h : IsBasisSystem μ U ψ Rpos B₀) (w : Fin 4 → V) (r : Fin 4 → R) :
    |quadMoment μ U ψ w r| ≤ max B₀ 1 ^ 4 := by
  have hP : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have hb : ∀ ω, |∏ j : Fin 4, ψ (r j) (U (w j) ω)| ≤ max B₀ 1 ^ 4 := by
    intro ω
    rw [Finset.abs_prod]
    calc ∏ j : Fin 4, |ψ (r j) (U (w j) ω)| ≤ ∏ _j : Fin 4, max B₀ 1 :=
          Finset.prod_le_prod₀ (fun j _ => abs_nonneg _)
            (fun j _ => le_trans (h.bound _ _) (le_max_left _ _))
      _ = max B₀ 1 ^ 4 := by simp
  have hm := MeasureTheory.norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun ω => ∏ j : Fin 4, ψ (r j) (U (w j) ω)) (C := max B₀ 1 ^ 4)
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hb ω)
  simpa [quadMoment, Real.norm_eq_abs] using hm

omit [Fintype V] [DecidableEq V] in
theorem integrable_quadProd (h : IsBasisSystem μ U ψ Rpos B₀) (w : Fin 4 → V) (r : Fin 4 → R) :
    Integrable (fun ω => ∏ j : Fin 4, ψ (r j) (U (w j) ω)) μ := by
  have hP : IsProbabilityMeasure μ := h.isProbabilityMeasure
  refine Integrable.mono' (g := fun _ => max B₀ 1 ^ 4) (integrable_const _)
    ((Finset.measurable_prod _ fun j _ =>
      (h.measurable_psi (r j)).comp (h.measurable_latent (w j))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, Finset.abs_prod]
  calc ∏ j : Fin 4, |ψ (r j) (U (w j) ω)| ≤ ∏ _j : Fin 4, max B₀ 1 :=
        Finset.prod_le_prod₀ (fun j _ => abs_nonneg _)
          (fun j _ => le_trans (h.bound _ _) (le_max_left _ _))
    _ = max B₀ 1 ^ 4 := by simp

/-- The contrapositive of `quadMoment_eq_zero_of_isolated`: a surviving quadruple has no
singleton site. -/
theorem exists_eq_of_quadMoment_ne_zero (h : IsBasisSystem μ U ψ Rpos B₀)
    {w : Fin 4 → V} {r : Fin 4 → R} (hr : ∀ j, r j ∈ Rpos)
    (hne : quadMoment μ U ψ w r ≠ 0) (j : Fin 4) : ∃ j', j' ≠ j ∧ w j' = w j := by
  by_contra hcon
  exact hne (quadMoment_eq_zero_of_isolated h (j := j)
    (fun j' hj' hEq => hcon ⟨j', hj', hEq⟩) (hr j))

/-- **Surviving quadruples for singleton site sets.** `w 0, w 1, w 2, w 3` are the sites of
`s, s', u, u'`; `hum` says `(s,s')` is unmatched and `hdiag` excludes the diagonal quadruple. A
quadruple with nonzero moment is then the transposed one, `w 3 = w 0` and `w 2 = w 1`. -/
theorem quad_pattern_of_ne_zero (h : IsBasisSystem μ U ψ Rpos B₀)
    {w : Fin 4 → V} {r : Fin 4 → R} (hr : ∀ j, r j ∈ Rpos)
    (hne : quadMoment μ U ψ w r ≠ 0)
    (hum : w 0 = w 1 → r 0 ≠ r 1)
    (hdiag : w 2 = w 0 → w 3 = w 1 → False) :
    w 3 = w 0 ∧ w 2 = w 1 := by
  have hfin : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  have D0 : w 1 = w 0 ∨ w 2 = w 0 ∨ w 3 = w 0 := by
    obtain ⟨j', hj1, hj2⟩ := exists_eq_of_quadMoment_ne_zero h hr hne 0
    rcases hfin j' with rfl | rfl | rfl | rfl
    · exact absurd rfl hj1
    · exact Or.inl hj2
    · exact Or.inr (Or.inl hj2)
    · exact Or.inr (Or.inr hj2)
  have D1 : w 0 = w 1 ∨ w 2 = w 1 ∨ w 3 = w 1 := by
    obtain ⟨j', hj1, hj2⟩ := exists_eq_of_quadMoment_ne_zero h hr hne 1
    rcases hfin j' with rfl | rfl | rfl | rfl
    · exact Or.inl hj2
    · exact absurd rfl hj1
    · exact Or.inr (Or.inl hj2)
    · exact Or.inr (Or.inr hj2)
  have D2 : w 0 = w 2 ∨ w 1 = w 2 ∨ w 3 = w 2 := by
    obtain ⟨j', hj1, hj2⟩ := exists_eq_of_quadMoment_ne_zero h hr hne 2
    rcases hfin j' with rfl | rfl | rfl | rfl
    · exact Or.inl hj2
    · exact Or.inr (Or.inl hj2)
    · exact absurd rfl hj1
    · exact Or.inr (Or.inr hj2)
  have D3 : w 0 = w 3 ∨ w 1 = w 3 ∨ w 2 = w 3 := by
    obtain ⟨j', hj1, hj2⟩ := exists_eq_of_quadMoment_ne_zero h hr hne 3
    rcases hfin j' with rfl | rfl | rfl | rfl
    · exact Or.inl hj2
    · exact Or.inr (Or.inl hj2)
    · exact Or.inr (Or.inr hj2)
    · exact absurd rfl hj1
  -- the diagonal configuration is excluded by hypothesis, so `w 2 = w 0` is impossible
  have hA : w 2 ≠ w 0 := by
    intro hc
    refine hdiag hc ?_
    rcases D3 with h30 | h31 | h32
    · have h3 : w 3 = w 0 := h30.symm
      rcases D1 with e | e | e
      · rw [h3, ← e]
      · rw [h3, ← e, hc]
      · rw [h3, ← e, h3]
    · exact h31.symm
    · have h3 : w 3 = w 0 := by rw [← h32, hc]
      rcases D1 with e | e | e
      · rw [h3, ← e]
      · rw [h3, ← e, hc]
      · rw [h3, ← e, h3]
  -- the pattern-(A) configuration is excluded by orthonormality, so `w 3 = w 0`
  have hB : w 3 = w 0 := by
    by_contra hc
    have h10 : w 1 = w 0 := by
      rcases D0 with e | e | e
      · exact e
      · exact absurd e hA
      · exact absurd e hc
    have hiso : ∀ l : Fin 4, l ≠ 0 → l ≠ 1 → w l ≠ w 0 := by
      intro l hl0 hl1
      rcases hfin l with rfl | rfl | rfl | rfl
      · exact absurd rfl hl0
      · exact absurd rfl hl1
      · exact hA
      · exact hc
    have hrr : r 0 = r 1 := by
      by_contra hrne
      exact hne (quadMoment_eq_zero_of_pair h (by decide : (0 : Fin 4) ≠ 1) h10 hiso hrne)
    exact hum h10.symm hrr
  refine ⟨hB, ?_⟩
  rcases D2 with e | e | e
  · exact absurd e.symm hA
  · exact e.symm
  · exact absurd (by rw [← e, hB] : w 2 = w 0) hA

/-! #### The second moment as a sum over quadruples -/

/-- The square of a double sum, expanded over quadruples. -/
theorem sq_double_sum {A B : Type*} [Fintype A] [Fintype B] (g : A → B → ℝ) :
    (∑ s : A, ∑ s' : B, g s s') ^ 2 = ∑ s : A, ∑ s' : B, ∑ u : A, ∑ u' : B, g s s' * g u u' := by
  rw [sq, Fintype.sum_mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Fintype.sum_mul_sum]
  exact Finset.sum_comm

omit [Fintype V] [DecidableEq V] [DecidableEq R] in
/-- The second moment of a double sum of products, expanded over quadruples. -/
theorem integral_sq_double_sum {A B : Type*} [Fintype A] [Fintype B] (c : A → B → ℝ)
    (f : A → Ω → ℝ) (g : B → Ω → ℝ)
    (hint : ∀ (a : A) (b : B) (a' : A) (b' : B),
      Integrable (fun ω => f a ω * g b ω * (f a' ω * g b' ω)) μ) :
    ∫ ω, (∑ a : A, ∑ b : B, c a b * (f a ω * g b ω)) ^ 2 ∂μ
      = ∑ a : A, ∑ b : B, ∑ a' : A, ∑ b' : B,
          c a b * c a' b' * ∫ ω, f a ω * g b ω * (f a' ω * g b' ω) ∂μ := by
  classical
  have hpt : ∀ ω, (∑ a : A, ∑ b : B, c a b * (f a ω * g b ω)) ^ 2
      = ∑ a : A, ∑ b : B, ∑ a' : A, ∑ b' : B,
          c a b * c a' b' * (f a ω * g b ω * (f a' ω * g b' ω)) := by
    intro ω
    rw [sq_double_sum (fun a b => c a b * (f a ω * g b ω))]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => by ring
  have hint' : ∀ (a : A) (b : B) (a' : A) (b' : B),
      Integrable (fun ω => c a b * c a' b' * (f a ω * g b ω * (f a' ω * g b' ω))) μ :=
    fun a b a' b' => (hint a b a' b').const_mul _
  simp only [hpt]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      integrable_finsetSum _ fun a' _ => integrable_finsetSum _ fun b' _ => hint' a b a' b']
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => integrable_finsetSum _ fun a' _ =>
      integrable_finsetSum _ fun b' _ => hint' a b a' b']
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_finsetSum _ fun a' _ => integrable_finsetSum _ fun b' _ => hint' a b a' b']
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [integral_finsetSum _ fun b' _ => hint' a b a' b']
  exact Finset.sum_congr rfl fun b' _ => integral_const_mul _ _

/-! #### Cauchy--Schwarz over quadruples -/

/-- Cauchy--Schwarz over a set `T` of quadruples each determined by either of its two pairs:
`|∑_{q ∈ T} c_{q_1} c_{q_2} Q_q| ≤ M₀ ∑ c²` when `|Q| ≤ M₀`. -/
theorem abs_sum_quad_pairs_le {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] (c : A → B → ℝ) (Q : A → B → A → B → ℝ) {M₀ : ℝ} (hM : 0 ≤ M₀)
    (hQ : ∀ s s' u u', |Q s s' u u'| ≤ M₀)
    (T : Finset ((A × B) × (A × B)))
    (h1 : ∀ q ∈ T, ∀ q' ∈ T, q.1 = q'.1 → q = q')
    (h2 : ∀ q ∈ T, ∀ q' ∈ T, q.2 = q'.2 → q = q') :
    |∑ q ∈ T, c q.1.1 q.1.2 * c q.2.1 q.2.2 * Q q.1.1 q.1.2 q.2.1 q.2.2|
      ≤ M₀ * ∑ s : A, ∑ s' : B, (c s s') ^ 2 := by
  classical
  set Stot : ℝ := ∑ s : A, ∑ s' : B, (c s s') ^ 2 with hStot
  have hStot' : Stot = ∑ x : A × B, (c x.1 x.2) ^ 2 := by
    rw [hStot, Fintype.sum_prod_type]
  have hSnn : (0:ℝ) ≤ Stot := by
    rw [hStot]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hproj : ∀ (g : ((A × B) × (A × B)) → A × B),
      (∀ q ∈ T, ∀ q' ∈ T, g q = g q' → q = q') → ∑ q ∈ T, (c (g q).1 (g q).2) ^ 2 ≤ Stot := by
    intro g hg
    have himg : ∑ x ∈ T.image g, (c x.1 x.2) ^ 2 = ∑ q ∈ T, (c (g q).1 (g q).2) ^ 2 :=
      Finset.sum_image fun q hq q' hq' hEq => hg q hq q' hq' hEq
    rw [← himg, hStot']
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun x _ _ => sq_nonneg _
  have hA : ∑ q ∈ T, (c q.1.1 q.1.2) ^ 2 ≤ Stot := hproj (fun q => q.1) h1
  have hB : ∑ q ∈ T, (c q.2.1 q.2.2) ^ 2 ≤ Stot := hproj (fun q => q.2) h2
  calc |∑ q ∈ T, c q.1.1 q.1.2 * c q.2.1 q.2.2 * Q q.1.1 q.1.2 q.2.1 q.2.2|
      ≤ ∑ q ∈ T, |c q.1.1 q.1.2 * c q.2.1 q.2.2 * Q q.1.1 q.1.2 q.2.1 q.2.2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ T, M₀ * (|c q.1.1 q.1.2| * |c q.2.1 q.2.2|) := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [abs_mul, abs_mul]
        have hcc : (0:ℝ) ≤ |c q.1.1 q.1.2| * |c q.2.1 q.2.2| :=
          mul_nonneg (abs_nonneg _) (abs_nonneg _)
        calc |c q.1.1 q.1.2| * |c q.2.1 q.2.2| * |Q q.1.1 q.1.2 q.2.1 q.2.2|
            ≤ |c q.1.1 q.1.2| * |c q.2.1 q.2.2| * M₀ :=
              mul_le_mul_of_nonneg_left (hQ q.1.1 q.1.2 q.2.1 q.2.2) hcc
          _ = M₀ * (|c q.1.1 q.1.2| * |c q.2.1 q.2.2|) := by ring
    _ = M₀ * ∑ q ∈ T, |c q.1.1 q.1.2| * |c q.2.1 q.2.2| := by rw [Finset.mul_sum]
    _ ≤ M₀ * Stot := by
        refine mul_le_mul_of_nonneg_left ?_ hM
        calc ∑ q ∈ T, |c q.1.1 q.1.2| * |c q.2.1 q.2.2|
            ≤ Real.sqrt (∑ q ∈ T, |c q.1.1 q.1.2| ^ 2) *
                Real.sqrt (∑ q ∈ T, |c q.2.1 q.2.2| ^ 2) :=
              Real.sum_mul_le_sqrt_mul_sqrt T _ _
          _ = Real.sqrt (∑ q ∈ T, (c q.1.1 q.1.2) ^ 2) *
                Real.sqrt (∑ q ∈ T, (c q.2.1 q.2.2) ^ 2) := by
              rw [show (∑ q ∈ T, |c q.1.1 q.1.2| ^ 2) = ∑ q ∈ T, (c q.1.1 q.1.2) ^ 2 from
                    Finset.sum_congr rfl fun q _ => sq_abs _,
                show (∑ q ∈ T, |c q.2.1 q.2.2| ^ 2) = ∑ q ∈ T, (c q.2.1 q.2.2) ^ 2 from
                    Finset.sum_congr rfl fun q _ => sq_abs _]
          _ ≤ Real.sqrt Stot * Real.sqrt Stot :=
              mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB)
                (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
          _ = Stot := Real.mul_self_sqrt hSnn

/-- The quadruple sum split at the diagonal, with one further configuration `p` determined
by either of its two pairs. -/
theorem abs_sum_quad_le {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (c : A → B → ℝ) (Q : A → B → A → B → ℝ) {M₀ : ℝ} (hM : 0 ≤ M₀)
    (hQ : ∀ s s' u u', |Q s s' u u'| ≤ M₀)
    (p : A → B → A → B → Prop)
    (hsupp : ∀ s s' u u', ¬ (u = s ∧ u' = s') →
      c s s' * c u u' * Q s s' u u' ≠ 0 → p s s' u u')
    (hfwd : ∀ s s' u u' v v', p s s' u u' → p s s' v v' → u = v ∧ u' = v')
    (hbwd : ∀ s s' t t' u u', p s s' u u' → p t t' u u' → s = t ∧ s' = t') :
    |∑ s : A, ∑ s' : B, ∑ u : A, ∑ u' : B, c s s' * c u u' * Q s s' u u'|
      ≤ 2 * M₀ * ∑ s : A, ∑ s' : B, (c s s') ^ 2 := by
  classical
  set F : ((A × B) × (A × B)) → ℝ :=
    fun q => c q.1.1 q.1.2 * c q.2.1 q.2.2 * Q q.1.1 q.1.2 q.2.1 q.2.2 with hF
  have hflat : ∑ s : A, ∑ s' : B, ∑ u : A, ∑ u' : B, c s s' * c u u' * Q s s' u u'
      = ∑ q : (A × B) × (A × B), F q := by
    rw [hF]
    simp only [Fintype.sum_prod_type]
  set D : Finset ((A × B) × (A × B)) := Finset.univ.filter (fun q => q.2 = q.1) with hD
  set T : Finset ((A × B) × (A × B)) :=
    Finset.univ.filter (fun q => q.2 ≠ q.1 ∧ p q.1.1 q.1.2 q.2.1 q.2.2) with hT
  have hsplit : ∑ q : (A × B) × (A × B), F q
      = (∑ q ∈ D, F q) + ∑ q ∈ Finset.univ.filter (fun q => ¬ (q.2 = q.1)), F q :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ (fun q => q.2 = q.1) F).symm
  have hoff : ∑ q ∈ T, F q = ∑ q ∈ Finset.univ.filter (fun q => ¬ (q.2 = q.1)), F q := by
    refine Finset.sum_subset ?_ ?_
    · intro q hq
      rw [hT, Finset.mem_filter] at hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hq.2.1
    · intro q hq hqT
      rw [Finset.mem_filter] at hq
      by_contra hne
      refine hqT ?_
      rw [hT, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hq.2, ?_⟩
      refine hsupp q.1.1 q.1.2 q.2.1 q.2.2 ?_ hne
      rintro ⟨h1, h2⟩
      exact hq.2 (Prod.ext h1 h2)
  have hDbound : |∑ q ∈ D, F q| ≤ M₀ * ∑ s : A, ∑ s' : B, (c s s') ^ 2 := by
    refine abs_sum_quad_pairs_le c Q hM hQ D ?_ ?_
    · intro q hq q' hq' hEq
      rw [hD, Finset.mem_filter] at hq hq'
      exact Prod.ext hEq (by rw [hq.2, hEq, hq'.2])
    · intro q hq q' hq' hEq
      rw [hD, Finset.mem_filter] at hq hq'
      have hq11 : q.1 = q'.1 := by rw [← hq.2, hEq, hq'.2]
      exact Prod.ext hq11 (by rw [hq.2, hq11, hq'.2])
  have hTbound : |∑ q ∈ T, F q| ≤ M₀ * ∑ s : A, ∑ s' : B, (c s s') ^ 2 := by
    refine abs_sum_quad_pairs_le c Q hM hQ T ?_ ?_
    · intro q hq q' hq' hEq
      rw [hT, Finset.mem_filter] at hq hq'
      have hp := hq.2.2
      have hp' := hq'.2.2
      rw [← hEq] at hp'
      obtain ⟨e1, e2⟩ := hfwd _ _ _ _ _ _ hp hp'
      exact Prod.ext hEq (Prod.ext e1 e2)
    · intro q hq q' hq' hEq
      rw [hT, Finset.mem_filter] at hq hq'
      have hp := hq.2.2
      have hp' := hq'.2.2
      rw [← hEq] at hp'
      obtain ⟨e1, e2⟩ := hbwd _ _ _ _ _ _ hp hp'
      exact Prod.ext (Prod.ext e1 e2) hEq
  rw [hflat, hsplit, ← hoff]
  calc |(∑ q ∈ D, F q) + ∑ q ∈ T, F q| ≤ |∑ q ∈ D, F q| + |∑ q ∈ T, F q| := abs_add_le _ _
    _ ≤ M₀ * ∑ s : A, ∑ s' : B, (c s s') ^ 2 + M₀ * ∑ s : A, ∑ s' : B, (c s s') ^ 2 :=
        add_le_add hDbound hTbound
    _ = 2 * M₀ * ∑ s : A, ∑ s' : B, (c s s') ^ 2 := by ring

/-! #### The two part bounds for singleton site sets -/

section Discharge

variable {Γ : Type*} {S : Γ → Type*} [∀ γ, Fintype (S γ)] {I : Type*} [Fintype I]
  {τ : Type*} [DecidableEq τ]
variable {sites : ∀ γ, S γ → Finset V} {rIdx : Γ → V → R} {arr : ∀ γ, S γ → I → ℝ}
  {tag : Γ → τ}

/-- `G_{ss'}` restricted to the unmatched pairs, which is the coefficient array `Ξᵘ` carries. -/
noncomputable def unmCoef (sites : ∀ γ, S γ → Finset V) (rIdx : Γ → V → R)
    (arr : ∀ γ, S γ → I → ℝ) (γ γ' : Γ) (s : S γ) (s' : S γ') : ℝ :=
  if IsMatched sites rIdx γ γ' s s' then 0 else gramEntry arr γ γ' s s'

omit [MeasurableSpace Ω] in
theorem unmatchedPart_eq_sum_unmCoef (γ γ' : Γ) (htag : tag γ = tag γ') (ω : Ω) :
    unmatchedPart U ψ sites rIdx arr tag γ γ' ω
      = ∑ s : S γ, ∑ s' : S γ', unmCoef sites rIdx arr γ γ' s s' *
          (basisProd U ψ sites rIdx γ s ω * basisProd U ψ sites rIdx γ' s' ω) := by
  classical
  simp only [unmatchedPart, unmCoef, htag, ite_true]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => by
    split_ifs <;> ring

omit [MeasurableSpace Ω] [Fintype V] [DecidableEq V] [DecidableEq R] [∀ γ, Fintype (S γ)] in
/-- At `|f_γ| = 1` the product `π^γ_s` is a single basis function of a single latent variable. -/
theorem basisProd_of_singleton {st : ∀ γ, S γ → V}
    (hst : ∀ (γ : Γ) (s : S γ), sites γ s = {st γ s}) (γ : Γ) (s : S γ) (ω : Ω) :
    basisProd U ψ sites rIdx γ s ω = ψ (rIdx γ (st γ s)) (U (st γ s) ω) := by
  simp [basisProd, hst γ s]

omit [Fintype V] [DecidableEq V] [DecidableEq R] [∀ γ, Fintype (S γ)] [Fintype I]
  [DecidableEq τ] in
theorem integral_basisProd_four_eq_quadMoment {st : ∀ γ, S γ → V}
    (hst : ∀ (γ : Γ) (s : S γ), sites γ s = {st γ s}) (γ γ' : Γ)
    (s u : S γ) (s' u' : S γ') :
    ∫ ω, basisProd U ψ sites rIdx γ s ω * basisProd U ψ sites rIdx γ' s' ω *
        (basisProd U ψ sites rIdx γ u ω * basisProd U ψ sites rIdx γ' u' ω) ∂μ
      = quadMoment μ U ψ ![st γ s, st γ' s', st γ u, st γ' u']
          ![rIdx γ (st γ s), rIdx γ' (st γ' s'), rIdx γ (st γ u), rIdx γ' (st γ' u')] := by
  rw [quadMoment]
  congr 1
  funext ω
  simp only [basisProd_of_singleton hst, Fin.prod_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num
  ring

omit [MeasurableSpace Ω] [DecidableEq τ] in
/-- `∑_{s,s'}(Ξᵘ's coefficient)² ≤ ‖G‖_F²`, since the unmatched restriction only deletes terms. -/
theorem sum_sq_unmCoef_le (γ γ' : Γ) :
    ∑ s : S γ, ∑ s' : S γ', (unmCoef sites rIdx arr γ γ' s s') ^ 2
      ≤ rectFrobSq (Matrix.of (arr γ) * (Matrix.of (arr γ'))ᵀ) := by
  classical
  rw [rectFrobSq]
  refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun s' _ => ?_
  have hEq : (Matrix.of (arr γ) * (Matrix.of (arr γ'))ᵀ) s s'
      = gramEntry arr γ γ' s s' := by
    simp [Matrix.mul_apply, Matrix.transpose_apply, gramEntry]
  rw [hEq, unmCoef]
  split_ifs
  · simpa using sq_nonneg (gramEntry arr γ γ' s s')
  · exact le_rfl

omit [MeasurableSpace Ω] [DecidableEq R] [DecidableEq τ] in
/-- `‖G_{γγ'}‖_F² ≤ ‖V^{(γ)} ⊠_{k^⋆} V^{(γ)}‖_F ‖V^{(γ')} ⊠_{k^⋆} V^{(γ')}‖_F`, where
`arr γ` is the transpose of `F^γ_{{k^⋆}}`. -/
theorem rectFrobSq_gram_le (γ γ' : Γ) :
    rectFrobSq (Matrix.of (arr γ) * (Matrix.of (arr γ'))ᵀ)
      ≤ rectFrobNorm (Matrix.of (arr γ) * (Matrix.of (arr γ))ᵀ) *
        rectFrobNorm (Matrix.of (arr γ') * (Matrix.of (arr γ'))ᵀ) := by
  rw [rectFrobNorm_mul_transpose_comm (Matrix.of (arr γ)),
    rectFrobNorm_mul_transpose_comm (Matrix.of (arr γ'))]
  simpa using rectFrobSq_transpose_mul_le (Matrix.of (arr γ))ᵀ (Matrix.of (arr γ'))ᵀ

/-- `𝔼[(Ξᵘ_{γγ'})²] ≤ 2max(B_0,1)^4‖G_{γγ'}‖_F²` when every site set is a singleton. -/
theorem integral_sq_unmatchedPart_le_of_singleton
    (h : IsBasisSystem μ U ψ Rpos B₀)
    {st : ∀ γ, S γ → V} (hst : ∀ (γ : Γ) (s : S γ), sites γ s = {st γ s})
    (hpos : ∀ (γ : Γ) (s : S γ), ∀ w ∈ sites γ s, rIdx γ w ∈ Rpos)
    (hinj : ∀ (γ : Γ) (s s' : S γ), sites γ s = sites γ s' → s = s')
    (γ γ' : Γ) :
    ∫ ω, (unmatchedPart U ψ sites rIdx arr tag γ γ' ω) ^ 2 ∂μ
      ≤ 2 * max B₀ 1 ^ 4 *
        rectFrobSq (Matrix.of (arr γ) * (Matrix.of (arr γ'))ᵀ) := by
  classical
  have hP : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have hM : (0:ℝ) ≤ max B₀ 1 ^ 4 := by positivity
  have hfrob : (0:ℝ) ≤ rectFrobSq (Matrix.of (arr γ) * (Matrix.of (arr γ'))ᵀ) :=
    rectFrobSq_nonneg _
  have hpos' : ∀ (g : Γ) (x : S g), rIdx g (st g x) ∈ Rpos := fun g x =>
    hpos g x (st g x) (by rw [hst g x]; exact Finset.mem_singleton_self _)
  by_cases htag : tag γ = tag γ'
  · have hstinj : ∀ (g : Γ) (x y : S g), st g x = st g y → x = y := by
      intro g x y hxy
      exact hinj g x y (by rw [hst g x, hst g y, hxy])
    have hfin : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
    set c : S γ → S γ' → ℝ := fun s s' => unmCoef sites rIdx arr γ γ' s s' with hc
    set Qf : S γ → S γ' → S γ → S γ' → ℝ := fun s s' u u' =>
      quadMoment μ U ψ ![st γ s, st γ' s', st γ u, st γ' u']
        ![rIdx γ (st γ s), rIdx γ' (st γ' s'), rIdx γ (st γ u), rIdx γ' (st γ' u')] with hQf
    have hint : ∀ (a : S γ) (b : S γ') (a' : S γ) (b' : S γ'),
        Integrable (fun ω => basisProd U ψ sites rIdx γ a ω * basisProd U ψ sites rIdx γ' b ω *
          (basisProd U ψ sites rIdx γ a' ω * basisProd U ψ sites rIdx γ' b' ω)) μ := by
      intro a b a' b'
      refine (integrable_quadProd h ![st γ a, st γ' b, st γ a', st γ' b']
        ![rIdx γ (st γ a), rIdx γ' (st γ' b), rIdx γ (st γ a'), rIdx γ' (st γ' b')]).congr ?_
      filter_upwards with ω
      simp only [basisProd_of_singleton hst, Fin.prod_univ_four, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      norm_num
      ring
    have hexpand : ∫ ω, (unmatchedPart U ψ sites rIdx arr tag γ γ' ω) ^ 2 ∂μ
        = ∑ s : S γ, ∑ s' : S γ', ∑ u : S γ, ∑ u' : S γ', c s s' * c u u' * Qf s s' u u' := by
      have hfun : (fun ω => (unmatchedPart U ψ sites rIdx arr tag γ γ' ω) ^ 2)
          = fun ω => (∑ s : S γ, ∑ s' : S γ', c s s' *
              (basisProd U ψ sites rIdx γ s ω * basisProd U ψ sites rIdx γ' s' ω)) ^ 2 := by
        funext ω
        rw [unmatchedPart_eq_sum_unmCoef γ γ' htag ω]
      rw [hfun, integral_sq_double_sum c _ _ hint]
      exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ =>
        Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => by
          rw [integral_basisProd_four_eq_quadMoment hst γ γ' s u s' u']
    rw [hexpand]
    refine le_trans (le_abs_self _) (le_trans (abs_sum_quad_le c Qf hM ?_
      (fun s s' u u' => st γ' u' = st γ s ∧ st γ u = st γ' s') ?_ ?_ ?_) ?_)
    · intro s s' u u'
      exact abs_quadMoment_le h _ _
    · intro s s' u u' hnd hprod
      have hc1 : c s s' ≠ 0 := by
        intro h0; rw [h0] at hprod; simp at hprod
      have hQ0 : Qf s s' u u' ≠ 0 := by
        intro h0; rw [h0] at hprod; simp at hprod
      have hnm : ¬ IsMatched sites rIdx γ γ' s s' := by
        intro hm; exact hc1 (by simp [hc, unmCoef, hm])
      have hr : ∀ j : Fin 4,
          (![rIdx γ (st γ s), rIdx γ' (st γ' s'), rIdx γ (st γ u),
              rIdx γ' (st γ' u')] : Fin 4 → R) j ∈ Rpos := by
        intro j
        rcases hfin j with rfl | rfl | rfl | rfl
        · simpa using hpos' γ s
        · simpa using hpos' γ' s'
        · simpa using hpos' γ u
        · simpa using hpos' γ' u'
      have hum : (![st γ s, st γ' s', st γ u, st γ' u'] : Fin 4 → V) 0
            = (![st γ s, st γ' s', st γ u, st γ' u'] : Fin 4 → V) 1 →
          (![rIdx γ (st γ s), rIdx γ' (st γ' s'), rIdx γ (st γ u),
              rIdx γ' (st γ' u')] : Fin 4 → R) 0
            ≠ (![rIdx γ (st γ s), rIdx γ' (st γ' s'), rIdx γ (st γ u),
              rIdx γ' (st γ' u')] : Fin 4 → R) 1 := by
        intro he
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at he ⊢
        intro hrr
        refine hnm ⟨by rw [hst γ s, hst γ' s', he], ?_⟩
        intro w hw
        rw [hst γ s, Finset.mem_singleton] at hw
        subst hw
        rw [hrr, he]
      have hdg : (![st γ s, st γ' s', st γ u, st γ' u'] : Fin 4 → V) 2
            = (![st γ s, st γ' s', st γ u, st γ' u'] : Fin 4 → V) 0 →
          (![st γ s, st γ' s', st γ u, st γ' u'] : Fin 4 → V) 3
            = (![st γ s, st γ' s', st γ u, st γ' u'] : Fin 4 → V) 1 → False := by
        intro e1 e2
        norm_num at e1 e2
        exact hnd ⟨hstinj γ u s e1, hstinj γ' u' s' e2⟩
      have hpat := quad_pattern_of_ne_zero h hr hQ0 hum hdg
      simpa using hpat
    · rintro s s' u u' v v' ⟨p1, p2⟩ ⟨q1, q2⟩
      exact ⟨hstinj γ u v (by rw [p2, q2]), hstinj γ' u' v' (by rw [p1, q1])⟩
    · rintro s s' t t' u u' ⟨p1, p2⟩ ⟨q1, q2⟩
      exact ⟨hstinj γ s t (by rw [← p1, q1]), hstinj γ' s' t' (by rw [← p2, q2])⟩
    · exact mul_le_mul_of_nonneg_left (sum_sq_unmCoef_le γ γ') (by positivity)
  · have h0 : unmatchedPart U ψ sites rIdx arr tag γ γ' = fun _ => (0:ℝ) := by
      funext ω; simp [unmatchedPart, htag]
    rw [h0]
    simpa using mul_nonneg (by positivity : (0:ℝ) ≤ 2 * max B₀ 1 ^ 4) hfrob

/-- A sum over a subsingleton `Finset` squares termwise. -/
theorem sq_sum_of_subsingleton {A : Type*} (F : Finset A) (g : A → ℝ)
    (hF : ∀ a ∈ F, ∀ b ∈ F, a = b) : (∑ a ∈ F, g a) ^ 2 = ∑ a ∈ F, (g a) ^ 2 := by
  classical
  rcases Finset.eq_empty_or_nonempty F with he | ⟨a, ha⟩
  · rw [he]; simp
  · have hs : F = {a} := Finset.eq_singleton_iff_unique_mem.2 ⟨ha, fun x hx => hF x hx a ha⟩
    rw [hs]; simp

/-- The matched-part bound when every site set is a singleton: the fibre sums are the
diagonal Gram entries `G_{ss}`, so `sum_sq_diag_le_rectFrobSq` applies directly. -/
theorem variance_matchedPart_le_of_singleton_ofCard (h : IsBasisSystem μ U ψ Rpos B₀)
    {M : ℕ} (hlev : ∀ (g : Γ) (x : S g), (sites g x).card ≤ M)
    {st : ∀ γ, S γ → V} (hst : ∀ (γ : Γ) (s : S γ), sites γ s = {st γ s})
    (hinj : ∀ (γ : Γ) (s s' : S γ), sites γ s = sites γ s' → s = s') (γ : Γ) :
    variance (matchedPart U ψ sites rIdx arr γ) μ
      ≤ ((max B₀ 1 ^ M) ^ 2) ^ 2 *
        rectFrobSq (Matrix.of (arr γ) * (Matrix.of (arr γ))ᵀ) := by
  classical
  refine le_trans (variance_matchedPart_le_ofCard h hlev γ) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hsub : ∀ w : V, ∀ s ∈ Finset.univ.filter (fun s => w ∈ sites γ s),
      ∀ t ∈ Finset.univ.filter (fun s => w ∈ sites γ s), s = t := by
    intro w s hs t ht
    rw [Finset.mem_filter, hst γ s, Finset.mem_singleton] at hs
    rw [Finset.mem_filter, hst γ t, Finset.mem_singleton] at ht
    exact hinj γ s t (by rw [hst γ s, hst γ t, ← hs.2, ht.2])
  have hfib : ∀ w : V,
      (∑ s ∈ Finset.univ.filter (fun s => w ∈ sites γ s), gramDiag arr γ s) ^ 2
        = ∑ s ∈ Finset.univ.filter (fun s => w ∈ sites γ s), (gramDiag arr γ s) ^ 2 :=
    fun w => sq_sum_of_subsingleton _ _ (hsub w)
  have hswap : ∑ w : V, ∑ s ∈ Finset.univ.filter (fun s => w ∈ sites γ s),
      (gramDiag arr γ s) ^ 2 = ∑ s : S γ, (gramDiag arr γ s) ^ 2 := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [hst γ s]
  have hdiag : ∀ s : S γ, gramDiag arr γ s
      = (Matrix.of (arr γ) * (Matrix.of (arr γ))ᵀ) s s := by
    intro s
    simp [Matrix.mul_apply, Matrix.transpose_apply, gramDiag, sq]
  calc ∑ w : V, (∑ s ∈ Finset.univ.filter (fun s => w ∈ sites γ s), gramDiag arr γ s) ^ 2
      = ∑ s : S γ, (gramDiag arr γ s) ^ 2 := by rw [Finset.sum_congr rfl fun w _ => hfib w, hswap]
    _ = ∑ s : S γ, ((Matrix.of (arr γ) * (Matrix.of (arr γ))ᵀ) s s) ^ 2 :=
        Finset.sum_congr rfl fun s _ => by rw [hdiag s]
    _ ≤ rectFrobSq (Matrix.of (arr γ) * (Matrix.of (arr γ))ᵀ) := sum_sq_diag_le_rectFrobSq _


/-- The matched-part bound when every site set is a singleton, with constant in terms of
`|V|`. -/
theorem variance_matchedPart_le_of_singleton (h : IsBasisSystem μ U ψ Rpos B₀)
    {st : ∀ γ, S γ → V} (hst : ∀ (γ : Γ) (s : S γ), sites γ s = {st γ s})
    (hinj : ∀ (γ : Γ) (s s' : S γ), sites γ s = sites γ s' → s = s') (γ : Γ) :
    variance (matchedPart U ψ sites rIdx arr γ) μ
      ≤ ((max B₀ 1 ^ Fintype.card V) ^ 2) ^ 2 *
        rectFrobSq (Matrix.of (arr γ) * (Matrix.of (arr γ))ᵀ) := by
  apply variance_matchedPart_le_of_singleton_ofCard (M := Fintype.card V) <;>
    first
      | assumption
      | exact fun _ _ => Finset.card_le_univ _
      | exact fun _ => Finset.card_le_univ _
/-- **Lemma SM.C.3(b) when `|e_γ| = 2`.** `hst` says every site set is a singleton, and
`hcut`, `htot` bound `cut(γ)` and `tot(γ)`. The constant is explicit. -/
theorem concentration_clause_b_singleton_ofCard [Fintype Γ] [DecidableEq Γ]
    (h : IsBasisSystem μ U ψ Rpos B₀) {M : ℕ}
    (hlev : ∀ (g : Γ) (x : S g), (sites g x).card ≤ M)
    {st : ∀ γ, S γ → V} (hst : ∀ (γ : Γ) (s : S γ), sites γ s = {st γ s})
    (hpos : ∀ (γ : Γ) (s : S γ), ∀ w ∈ sites γ s, rIdx γ w ∈ Rpos)
    (hinj : ∀ (γ : Γ) (s s' : S γ), sites γ s = sites γ s' → s = s')
    (hsep : ∀ (γ γ' : Γ) (s : S γ) (s' : S γ'), tag γ = tag γ' → sites γ s = sites γ' s' →
      (∀ w ∈ sites γ s, rIdx γ w = rIdx γ' w) → γ = γ')
    {lam : Γ → ℝ} (hlam : ∑ γ, lam γ ^ 2 ≤ 1) {cutmax totmax : ℝ}
    (hcut : ∀ γ : Γ, rectFrobNorm (Matrix.of (arr γ) * (Matrix.of (arr γ))ᵀ) ≤ cutmax)
    (htot : ∀ γ : Γ, rectFrobSq (arr γ) ≤ totmax) :
    variance (fun ω => ∑ γ : Γ, ∑ γ' : Γ,
        lam γ * lam γ' * cvarEntry U ψ sites rIdx arr tag γ γ' ω) μ
      ≤ 4 * (Fintype.card Γ : ℝ) ^ 2 *
          (max B₀ 1 ^ (4 * M) + 2 * max B₀ 1 ^ 4) * (cutmax * totmax) := by
  classical
  have hpow4 : (0:ℝ) ≤ max B₀ 1 ^ 4 := by positivity
  have hpowV : (0:ℝ) ≤ max B₀ 1 ^ (4 * M) := by positivity
  have hnn : ∀ _g : Γ, (0:ℝ) ≤ cutmax * totmax := by
    intro g
    have h1 : (0:ℝ) ≤ cutmax := le_trans (rectFrobNorm_nonneg _) (hcut g)
    have h2 : (0:ℝ) ≤ totmax := le_trans (rectFrobSq_nonneg _) (htot g)
    exact mul_nonneg h1 h2
  have hbase : ∀ g g' : Γ,
      rectFrobSq (Matrix.of (arr g) * (Matrix.of (arr g'))ᵀ) ≤ cutmax * totmax := by
    intro g g'
    refine le_trans (rectFrobSq_gram_le g g') ?_
    exact mul_le_mul (hcut g)
      (le_trans (rectFrobNorm_mul_transpose_self_le _) (htot g'))
      (rectFrobNorm_nonneg _) (le_trans (rectFrobNorm_nonneg _) (hcut g))
  refine concentration_clause_b_cut_tot h hinj hsep hlam ?_ ?_
  · intro γ
    refine le_trans (variance_matchedPart_le_of_singleton_ofCard h hlev hst hinj γ) ?_
    have hconst : ((max B₀ 1 ^ M) ^ 2) ^ 2
        = max B₀ 1 ^ (4 * M) := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    rw [hconst]
    calc max B₀ 1 ^ (4 * M) *
          rectFrobSq (Matrix.of (arr γ) * (Matrix.of (arr γ))ᵀ)
        ≤ max B₀ 1 ^ (4 * M) * (cutmax * totmax) :=
          mul_le_mul_of_nonneg_left (hbase γ γ) hpowV
      _ ≤ (max B₀ 1 ^ (4 * M) + 2 * max B₀ 1 ^ 4) * (cutmax * totmax) := by
          refine mul_le_mul_of_nonneg_right ?_ (hnn γ)
          linarith
  · intro γ γ'
    refine le_trans (integral_sq_unmatchedPart_le_of_singleton h hst hpos hinj γ γ') ?_
    calc 2 * max B₀ 1 ^ 4 * rectFrobSq (Matrix.of (arr γ) * (Matrix.of (arr γ'))ᵀ)
        ≤ 2 * max B₀ 1 ^ 4 * (cutmax * totmax) :=
          mul_le_mul_of_nonneg_left (hbase γ γ') (by positivity)
      _ ≤ (max B₀ 1 ^ (4 * M) + 2 * max B₀ 1 ^ 4) * (cutmax * totmax) := by
          refine mul_le_mul_of_nonneg_right ?_ (hnn γ)
          linarith

/-- **Lemma SM.C.3(b) when `|e_γ| = 2`**, with constant in terms of `|V|`; see
`concentration_clause_b_singleton_uniform`. -/
theorem concentration_clause_b_singleton [Fintype Γ] [DecidableEq Γ]
    (h : IsBasisSystem μ U ψ Rpos B₀)
    {st : ∀ γ, S γ → V} (hst : ∀ (γ : Γ) (s : S γ), sites γ s = {st γ s})
    (hpos : ∀ (γ : Γ) (s : S γ), ∀ w ∈ sites γ s, rIdx γ w ∈ Rpos)
    (hinj : ∀ (γ : Γ) (s s' : S γ), sites γ s = sites γ s' → s = s')
    (hsep : ∀ (γ γ' : Γ) (s : S γ) (s' : S γ'), tag γ = tag γ' → sites γ s = sites γ' s' →
      (∀ w ∈ sites γ s, rIdx γ w = rIdx γ' w) → γ = γ')
    {lam : Γ → ℝ} (hlam : ∑ γ, lam γ ^ 2 ≤ 1) {cutmax totmax : ℝ}
    (hcut : ∀ γ : Γ, rectFrobNorm (Matrix.of (arr γ) * (Matrix.of (arr γ))ᵀ) ≤ cutmax)
    (htot : ∀ γ : Γ, rectFrobSq (arr γ) ≤ totmax) :
    variance (fun ω => ∑ γ : Γ, ∑ γ' : Γ,
        lam γ * lam γ' * cvarEntry U ψ sites rIdx arr tag γ γ' ω) μ
      ≤ 4 * (Fintype.card Γ : ℝ) ^ 2 *
          (max B₀ 1 ^ (4 * Fintype.card V) + 2 * max B₀ 1 ^ 4) * (cutmax * totmax) := by
  apply concentration_clause_b_singleton_ofCard (M := Fintype.card V) <;>
    first
      | assumption
      | exact fun _ _ => Finset.card_le_univ _
      | exact fun _ => Finset.card_le_univ _

set_option linter.unusedSectionVars false in
/-- **Lemma SM.C.3(b) when `|e_γ| = 2`**, with constant `12|Γ|²max(B_0,1)^4`. -/
theorem concentration_clause_b_singleton_uniform [Fintype Γ] [DecidableEq Γ]
    (h : IsBasisSystem μ U ψ Rpos B₀)
    {st : ∀ γ, S γ → V} (hst : ∀ (γ : Γ) (s : S γ), sites γ s = {st γ s})
    (hpos : ∀ (γ : Γ) (s : S γ), ∀ w ∈ sites γ s, rIdx γ w ∈ Rpos)
    (hinj : ∀ (γ : Γ) (s s' : S γ), sites γ s = sites γ s' → s = s')
    (hsep : ∀ (γ γ' : Γ) (s : S γ) (s' : S γ'), tag γ = tag γ' → sites γ s = sites γ' s' →
      (∀ w ∈ sites γ s, rIdx γ w = rIdx γ' w) → γ = γ')
    {lam : Γ → ℝ} (hlam : ∑ γ, lam γ ^ 2 ≤ 1) {cutmax totmax : ℝ}
    (hcut : ∀ γ : Γ, rectFrobNorm (Matrix.of (arr γ) * (Matrix.of (arr γ))ᵀ) ≤ cutmax)
    (htot : ∀ γ : Γ, rectFrobSq (arr γ) ≤ totmax) :
    variance (fun ω => ∑ γ : Γ, ∑ γ' : Γ,
        lam γ * lam γ' * cvarEntry U ψ sites rIdx arr tag γ γ' ω) μ
      ≤ 4 * (Fintype.card Γ : ℝ) ^ 2 *
          (max B₀ 1 ^ 4 + 2 * max B₀ 1 ^ 4) * (cutmax * totmax) := by
  have h1 := concentration_clause_b_singleton_ofCard (M := 1) h
    (fun g x => by rw [hst g x]; simp) hst hpos hinj hsep hlam hcut htot
  simpa only [Nat.mul_one] using h1

end Discharge

end SingletonSites

/-! ### The unmatched part at general level size

Sub-tuples carry coordinates: `lev γ` is `f_γ`, `pt γ s k` is the site of `s` at coordinate `k`,
`hsite` says `sites γ s = (lev γ).image (pt γ s)`, and `hptc` says a site determines its
coordinate. At a common coordinate `k`, a quadruple `(s,s',u,u')` with nonzero moment carries one
of the patterns (A) `s_k = s'_k`, `u_k = u'_k`; (B) `s_k = u_k`, `s'_k = u'_k`;
(C) `s_k = u'_k`, `s'_k = u_k`; (D) all four equal. With `ℬ` the set of pattern-(A) coordinates
and `A_𝒫 = ℬ ∪ {k^⋆}`, Class 1 is `ℬ = ∅`, Class 3 is `A_𝒫 = e_γ = e_{γ'}`, and Class 2 is the
remaining case. -/

section GeneralSites

/-! #### The four-fold moment for site sets -/

/-- The four-fold moment `𝔼[π^γ_sπ^{γ'}_{s'}π^γ_uπ^{γ'}_{u'}]` when each slot carries a site
set; `quadMoment` is the case of singleton sets. -/
noncomputable def multiMoment (μ : Measure Ω) (U : V → Ω → ℝ) (ψ : R → ℝ → ℝ)
    (E : Fin 4 → Finset V) (r : Fin 4 → V → R) : ℝ :=
  ∫ ω, ∏ j : Fin 4, ∏ w ∈ E j, ψ (r j w) (U w ω) ∂μ

/-- The four-fold moment factorizes over sites. -/
theorem multiMoment_eq_prod (h : IsBasisSystem μ U ψ Rpos B₀) (E : Fin 4 → Finset V)
    (r : Fin 4 → V → R) :
    multiMoment μ U ψ E r
      = ∏ v : V, ∫ ω, ∏ j ∈ Finset.univ.filter (fun j => v ∈ E j), ψ (r j v) (U v ω) ∂μ := by
  classical
  have hP : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have hmeas : ∀ v : V, Measurable (fun x : ℝ =>
      ∏ j ∈ Finset.univ.filter (fun j => v ∈ E j), ψ (r j v) x) := fun v =>
    Finset.measurable_prod _ fun j _ => h.measurable_psi (r j v)
  have hpt : ∀ ω, ∏ j : Fin 4, ∏ w ∈ E j, ψ (r j w) (U w ω)
      = ∏ v : V, ∏ j ∈ Finset.univ.filter (fun j => v ∈ E j), ψ (r j v) (U v ω) := by
    intro ω
    exact Finset.prod_comm' (s := (Finset.univ : Finset (Fin 4))) (t := E)
      (t' := (Finset.univ : Finset V))
      (s' := fun v => Finset.univ.filter (fun j => v ∈ E j)) (by intro j v; simp)
  rw [multiMoment]
  simp only [hpt]
  exact h.indep.integral_fun_prod_comp (fun v => (h.measurable_latent v).aemeasurable)
    (fun v => (hmeas v).aestronglyMeasurable)

/-- The four-fold moment vanishes at a site met by exactly one slot. -/
theorem multiMoment_eq_zero_of_isolated (h : IsBasisSystem μ U ψ Rpos B₀)
    {E : Fin 4 → Finset V} {r : Fin 4 → V → R} {v : V} {j : Fin 4}
    (hv : v ∈ E j) (hiso : ∀ j', j' ≠ j → v ∉ E j') (hr : r j v ∈ Rpos) :
    multiMoment μ U ψ E r = 0 := by
  classical
  rw [multiMoment_eq_prod h]
  refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
  have hfil : (Finset.univ.filter (fun j' => v ∈ E j')) = {j} := by
    ext j'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hj => by by_contra hne; exact hiso j' hne hj, by rintro rfl; exact hv⟩
  simp only [hfil, Finset.prod_singleton]
  exact h.integral_eq_zero v hr

/-- The four-fold moment vanishes at a site met by exactly two slots whose indices differ. -/
theorem multiMoment_eq_zero_of_pair (h : IsBasisSystem μ U ψ Rpos B₀)
    {E : Fin 4 → Finset V} {r : Fin 4 → V → R} {v : V} {j k : Fin 4} (hjk : j ≠ k)
    (hvj : v ∈ E j) (hvk : v ∈ E k) (hiso : ∀ l, l ≠ j → l ≠ k → v ∉ E l)
    (hne : r j v ≠ r k v) :
    multiMoment μ U ψ E r = 0 := by
  classical
  rw [multiMoment_eq_prod h]
  refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
  have hfil : (Finset.univ.filter (fun l => v ∈ E l)) = {j, k} := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hl
      by_contra hcon
      rw [not_or] at hcon
      exact hiso l hcon.1 hcon.2 hl
    · rintro (rfl | rfl)
      · exact hvj
      · exact hvk
  simp only [hfil, Finset.prod_pair hjk]
  rw [h.integral_mul v (r j v) (r k v)]
  simp [hne]

omit [DecidableEq V] in
/-- `|multiMoment| ≤ max(B_0,1)^{4M}` when each site set has at most `M` elements. -/
theorem abs_multiMoment_le_ofCard (h : IsBasisSystem μ U ψ Rpos B₀) {M : ℕ}
    (E : Fin 4 → Finset V) (hE : ∀ j, (E j).card ≤ M) (r : Fin 4 → V → R) :
    |multiMoment μ U ψ E r| ≤ max B₀ 1 ^ (4 * M) := by
  have hP : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have h1 : (1:ℝ) ≤ max B₀ 1 := le_max_right _ _
  have hb : ∀ ω, |∏ j : Fin 4, ∏ w ∈ E j, ψ (r j w) (U w ω)|
      ≤ max B₀ 1 ^ (4 * M) := by
    intro ω
    rw [Finset.abs_prod]
    calc ∏ j : Fin 4, |∏ w ∈ E j, ψ (r j w) (U w ω)|
        ≤ ∏ _j : Fin 4, max B₀ 1 ^ M := by
          refine Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) fun j _ => ?_
          rw [Finset.abs_prod]
          calc ∏ w ∈ E j, |ψ (r j w) (U w ω)| ≤ ∏ _w ∈ E j, max B₀ 1 :=
                Finset.prod_le_prod₀ (fun w _ => abs_nonneg _)
                  (fun w _ => le_trans (h.bound _ _) (le_max_left _ _))
            _ = max B₀ 1 ^ (E j).card := by rw [Finset.prod_const]
            _ ≤ max B₀ 1 ^ M :=
                pow_le_pow_right₀ h1 (hE j)
      _ = max B₀ 1 ^ (4 * M) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul,
            Nat.mul_comm (M) 4]
  have hm := MeasureTheory.norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun ω => ∏ j : Fin 4, ∏ w ∈ E j, ψ (r j w) (U w ω))
    (C := max B₀ 1 ^ (4 * M))
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hb ω)
  simpa [multiMoment, Real.norm_eq_abs] using hm


omit [DecidableEq V] in
/-- `|multiMoment| ≤ max(B_0,1)^{4|V|}`. -/
theorem abs_multiMoment_le (h : IsBasisSystem μ U ψ Rpos B₀) (E : Fin 4 → Finset V)
    (r : Fin 4 → V → R) :
    |multiMoment μ U ψ E r| ≤ max B₀ 1 ^ (4 * Fintype.card V) := by
  apply abs_multiMoment_le_ofCard (M := Fintype.card V) <;>
    first
      | assumption
      | exact fun _ _ => Finset.card_le_univ _
      | exact fun _ => Finset.card_le_univ _
omit [Fintype V] in
/-- If four elements carry none of the patterns (A), (B), (C), then one of them occurs exactly
once. -/
theorem exists_isolated_of_not_pattern {x y z w : V}
    (hA : ¬(x = y ∧ z = w)) (hB : ¬(x = z ∧ y = w)) (hC : ¬(x = w ∧ y = z)) :
    (x ≠ y ∧ x ≠ z ∧ x ≠ w) ∨ (y ≠ x ∧ y ≠ z ∧ y ≠ w) ∨
      (z ≠ x ∧ z ≠ y ∧ z ≠ w) ∨ (w ≠ x ∧ w ≠ y ∧ w ≠ z) := by
  classical
  by_cases h1 : x = y
  · have hzw : z ≠ w := fun hcc => hA ⟨h1, hcc⟩
    by_cases h2 : z = x
    · exact Or.inr (Or.inr (Or.inr ⟨fun hcc => hzw (h2.trans hcc.symm),
        fun hcc => hzw (h2.trans (h1.trans hcc.symm)), Ne.symm hzw⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨h2, fun hcc => h2 (hcc.trans h1.symm), hzw⟩))
  · by_cases h2 : z = x
    · by_cases h3 : w = x
      · exact Or.inr (Or.inl ⟨Ne.symm h1, fun hcc => h1 (hcc.trans h2).symm,
          fun hcc => h1 (hcc.trans h3).symm⟩)
      · have hyw : y ≠ w := fun hcc => hB ⟨h2.symm, hcc⟩
        exact Or.inr (Or.inr (Or.inr ⟨h3, Ne.symm hyw, fun hcc => h3 (hcc.trans h2)⟩))
    · by_cases h3 : w = x
      · have hyz : y ≠ z := fun hcc => hC ⟨h3.symm, hcc⟩
        exact Or.inr (Or.inr (Or.inl ⟨h2, Ne.symm hyz, fun hcc => h2 (hcc.trans h3)⟩))
      · exact Or.inl ⟨h1, Ne.symm h2, Ne.symm h3⟩

section GeneralDischarge

variable {Γ : Type*} {S : Γ → Type*} [∀ γ, Fintype (S γ)] {I : Type*} [Fintype I]
  {τ : Type*} [DecidableEq τ]
variable {sites : ∀ γ, S γ → Finset V} {rIdx : Γ → V → R} {arr : ∀ γ, S γ → I → ℝ}
  {tag : Γ → τ}
variable {K : Type*} [Fintype K] [DecidableEq K] {lev : Γ → Finset K}
  {pt : ∀ γ, S γ → K → V}

/-- The site sets of the four slots `s, s', u, u'`. -/
def quadSites (sites : ∀ γ, S γ → Finset V) (γ γ' : Γ) (s : S γ) (s' : S γ') (u : S γ)
    (u' : S γ') (j : Fin 4) : Finset V :=
  if j = 0 then sites γ s else if j = 1 then sites γ' s' else
    if j = 2 then sites γ u else sites γ' u'

/-- The basis indices of the four slots: the `γ`-side ones read `𝐫(γ)`, the `γ'`-side ones
read `𝐫(γ')`. -/
def quadIdx (rIdx : Γ → V → R) (γ γ' : Γ) (j : Fin 4) : V → R :=
  if j = 0 then rIdx γ else if j = 1 then rIdx γ' else
    if j = 2 then rIdx γ else rIdx γ'

omit [Fintype V] [DecidableEq V] [(γ : Γ) → Fintype (S γ)] in
@[simp] theorem quadSites_zero (sites : ∀ γ, S γ → Finset V) (γ γ' : Γ) (s : S γ) (s' : S γ')
    (u : S γ) (u' : S γ') : quadSites sites γ γ' s s' u u' 0 = sites γ s := by simp [quadSites]

omit [Fintype V] [DecidableEq V] [(γ : Γ) → Fintype (S γ)] in
@[simp] theorem quadSites_one (sites : ∀ γ, S γ → Finset V) (γ γ' : Γ) (s : S γ) (s' : S γ')
    (u : S γ) (u' : S γ') : quadSites sites γ γ' s s' u u' 1 = sites γ' s' := by simp [quadSites]

omit [Fintype V] [DecidableEq V] [(γ : Γ) → Fintype (S γ)] in
@[simp] theorem quadSites_two (sites : ∀ γ, S γ → Finset V) (γ γ' : Γ) (s : S γ) (s' : S γ')
    (u : S γ) (u' : S γ') : quadSites sites γ γ' s s' u u' 2 = sites γ u := by simp [quadSites]

omit [Fintype V] [DecidableEq V] [(γ : Γ) → Fintype (S γ)] in
@[simp] theorem quadSites_three (sites : ∀ γ, S γ → Finset V) (γ γ' : Γ) (s : S γ) (s' : S γ')
    (u : S γ) (u' : S γ') : quadSites sites γ γ' s s' u u' 3 = sites γ' u' := by simp [quadSites]

set_option linter.unusedSectionVars false in
/-- Each site set has at most `|K|` elements, since it is the image of the level under
`pt`. -/
theorem card_sites_le_card_K (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (g : Γ) (x : S g) : (sites g x).card ≤ Fintype.card K := by
  rw [hsite g x]
  exact le_trans Finset.card_image_le (Finset.card_le_univ _)

set_option linter.unusedSectionVars false in
/-- The level bound, transported to the four slot site sets. -/
theorem card_quadSites_le {M : ℕ} (hlev : ∀ (g : Γ) (x : S g), (sites g x).card ≤ M)
    (γ γ' : Γ) (s : S γ) (s' : S γ') (u : S γ) (u' : S γ') (j : Fin 4) :
    (quadSites sites γ γ' s s' u u' j).card ≤ M := by
  unfold quadSites
  split_ifs
  · exact hlev γ s
  · exact hlev γ' s'
  · exact hlev γ u
  · exact hlev γ' u'

omit [Fintype V] [DecidableEq V] [DecidableEq R] in
@[simp] theorem quadIdx_zero (rIdx : Γ → V → R) (γ γ' : Γ) :
    quadIdx rIdx γ γ' 0 = rIdx γ := by simp [quadIdx]

omit [Fintype V] [DecidableEq V] [DecidableEq R] in
@[simp] theorem quadIdx_one (rIdx : Γ → V → R) (γ γ' : Γ) :
    quadIdx rIdx γ γ' 1 = rIdx γ' := by simp [quadIdx]

omit [Fintype V] [DecidableEq V] [DecidableEq R] in
@[simp] theorem quadIdx_two (rIdx : Γ → V → R) (γ γ' : Γ) :
    quadIdx rIdx γ γ' 2 = rIdx γ := by simp [quadIdx]

omit [Fintype V] [DecidableEq V] [DecidableEq R] in
@[simp] theorem quadIdx_three (rIdx : Γ → V → R) (γ γ' : Γ) :
    quadIdx rIdx γ γ' 3 = rIdx γ' := by simp [quadIdx]

omit [Fintype V] [DecidableEq V] [DecidableEq R] [(γ : Γ) → Fintype (S γ)] in
/-- The four-fold expectation of `π`'s equals `multiMoment` at the four site sets. -/
theorem integral_basisProd_four_eq_multiMoment (γ γ' : Γ) (s : S γ) (s' : S γ') (u : S γ)
    (u' : S γ') :
    ∫ ω, basisProd U ψ sites rIdx γ s ω * basisProd U ψ sites rIdx γ' s' ω *
        (basisProd U ψ sites rIdx γ u ω * basisProd U ψ sites rIdx γ' u' ω) ∂μ
      = multiMoment μ U ψ (quadSites sites γ γ' s s' u u') (quadIdx rIdx γ γ') := by
  rw [multiMoment]
  congr 1
  funext ω
  rw [Fin.prod_univ_four]
  simp only [quadSites_zero, quadSites_one, quadSites_two, quadSites_three, quadIdx_zero,
    quadIdx_one, quadIdx_two, quadIdx_three, basisProd]
  ring

omit [DecidableEq V] [(γ : Γ) → Fintype (S γ)] in
/-- A product of four `π`'s is bounded, hence integrable. -/
theorem integrable_basisProd_four (h : IsBasisSystem μ U ψ Rpos B₀) (γ γ' : Γ) (a a' : S γ)
    (b b' : S γ') :
    Integrable (fun ω => basisProd U ψ sites rIdx γ a ω * basisProd U ψ sites rIdx γ' b ω *
      (basisProd U ψ sites rIdx γ a' ω * basisProd U ψ sites rIdx γ' b' ω)) μ := by
  have hP : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have hCnn : (0:ℝ) ≤ max B₀ 1 ^ Fintype.card V := by positivity
  refine Integrable.mono'
    (g := fun _ => (max B₀ 1 ^ Fintype.card V) * (max B₀ 1 ^ Fintype.card V) *
      ((max B₀ 1 ^ Fintype.card V) * (max B₀ 1 ^ Fintype.card V)))
    (integrable_const _)
    ((((measurable_basisProd h γ a).mul (measurable_basisProd h γ' b)).mul
      ((measurable_basisProd h γ a').mul (measurable_basisProd h γ' b'))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
  exact mul_le_mul
    (mul_le_mul (abs_basisProd_le h γ a ω) (abs_basisProd_le h γ' b ω) (abs_nonneg _) hCnn)
    (mul_le_mul (abs_basisProd_le h γ a' ω) (abs_basisProd_le h γ' b' ω) (abs_nonneg _) hCnn)
    (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg hCnn hCnn)

/-! #### Coordinates and patterns -/

/-- The pattern a quadruple carries at coordinate `k`, read exclusively: `0`, `1`, `2` are
(A), (B), (C) without (D), and `3` covers (D) and the configurations with vanishing moment. -/
def patAt (pt : ∀ γ, S γ → K → V) (γ γ' : Γ) (s : S γ) (s' : S γ') (u : S γ) (u' : S γ')
    (k : K) : Fin 4 :=
  if pt γ s k = pt γ' s' k ∧ pt γ u k = pt γ' u' k ∧ pt γ s k ≠ pt γ u k then 0
  else if pt γ s k = pt γ u k ∧ pt γ' s' k = pt γ' u' k ∧ pt γ s k ≠ pt γ' s' k then 1
  else if pt γ s k = pt γ' u' k ∧ pt γ' s' k = pt γ u k ∧ pt γ s k ≠ pt γ' s' k then 2
  else 3

omit [Fintype V] [(γ : Γ) → Fintype (S γ)] [Fintype K] [DecidableEq K] in
theorem eq_of_patAt_eq_zero {γ γ' : Γ} {s : S γ} {s' : S γ'} {u : S γ} {u' : S γ'} {k : K}
    (hp : patAt pt γ γ' s s' u u' k = 0) :
    pt γ s k = pt γ' s' k ∧ pt γ u k = pt γ' u' k ∧ pt γ s k ≠ pt γ u k := by
  unfold patAt at hp
  split_ifs at hp with hc1 hc2 hc3
  · exact hc1
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)

omit [Fintype V] [(γ : Γ) → Fintype (S γ)] [Fintype K] [DecidableEq K] in
theorem eq_of_patAt_eq_one {γ γ' : Γ} {s : S γ} {s' : S γ'} {u : S γ} {u' : S γ'} {k : K}
    (hp : patAt pt γ γ' s s' u u' k = 1) :
    pt γ s k = pt γ u k ∧ pt γ' s' k = pt γ' u' k := by
  unfold patAt at hp
  split_ifs at hp with hc1 hc2 hc3
  · exact absurd hp (by decide)
  · exact ⟨hc2.1, hc2.2.1⟩
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)

omit [Fintype V] [(γ : Γ) → Fintype (S γ)] [Fintype K] [DecidableEq K] in
theorem eq_of_patAt_eq_two {γ γ' : Γ} {s : S γ} {s' : S γ'} {u : S γ} {u' : S γ'} {k : K}
    (hp : patAt pt γ γ' s s' u u' k = 2) :
    pt γ s k = pt γ' u' k ∧ pt γ' s' k = pt γ u k := by
  unfold patAt at hp
  split_ifs at hp with hc1 hc2 hc3
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)
  · exact ⟨hc3.1, hc3.2.1⟩
  · exact absurd hp (by decide)

omit [Fintype V] [(γ : Γ) → Fintype (S γ)] [Fintype K] [DecidableEq K] in
/-- A surviving coordinate carrying none of the exclusive patterns (A), (B), (C) has all four
indices equal. -/
theorem all_eq_of_patAt_eq_three {γ γ' : Γ} {s : S γ} {s' : S γ'} {u : S γ} {u' : S γ'} {k : K}
    (hp : patAt pt γ γ' s s' u u' k = 3)
    (hsurv : (pt γ s k = pt γ' s' k ∧ pt γ u k = pt γ' u' k) ∨
      (pt γ s k = pt γ u k ∧ pt γ' s' k = pt γ' u' k) ∨
      (pt γ s k = pt γ' u' k ∧ pt γ' s' k = pt γ u k)) :
    pt γ s k = pt γ' s' k ∧ pt γ s k = pt γ u k ∧ pt γ s k = pt γ' u' k := by
  unfold patAt at hp
  split_ifs at hp with hc1 hc2 hc3
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)
  · rcases hsurv with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have hxz : pt γ s k = pt γ u k := by
        by_contra hcc
        exact hc1 ⟨e1, e2, hcc⟩
      exact ⟨e1, hxz, hxz.trans e2⟩
    · have hxy : pt γ s k = pt γ' s' k := by
        by_contra hcc
        exact hc2 ⟨e1, e2, hcc⟩
      exact ⟨hxy, e1, hxy.trans e2⟩
    · have hxy : pt γ s k = pt γ' s' k := by
        by_contra hcc
        exact hc3 ⟨e1, e2, hcc⟩
      exact ⟨hxy, hxy.trans e2, e1⟩

omit [Fintype V] [(γ : Γ) → Fintype (S γ)] [Fintype K] [DecidableEq K] in
/-- A site of coordinate `k` lies in a sub-tuple's site set exactly when `k` is in its level
and the sub-tuple occupies that site there. -/
theorem mem_sites_iff (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' → k = k')
    (g g' : Γ) (x : S g) (y : S g') (k : K) :
    pt g x k ∈ sites g' y ↔ (k ∈ lev g' ∧ pt g' y k = pt g x k) := by
  rw [hsite g' y, Finset.mem_image]
  constructor
  · rintro ⟨k', hk', hEq⟩
    have hkk : k' = k := hptc g' g y x k' k hEq
    subst hkk
    exact ⟨hk', hEq⟩
  · rintro ⟨hk, hEq⟩
    exact ⟨k, hk, hEq⟩

omit [Fintype V] [(γ : Γ) → Fintype (S γ)] [Fintype K] [DecidableEq K] in
theorem mem_sites_self (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (g : Γ) (x : S g) {k : K} (hk : k ∈ lev g) : pt g x k ∈ sites g x := by
  rw [hsite g x]
  exact Finset.mem_image_of_mem _ hk

omit [Fintype V] [(γ : Γ) → Fintype (S γ)] [Fintype K] [DecidableEq K] in
/-- The four slots' membership at one coordinate, in one statement. -/
theorem quadSites_mem (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' → k = k')
    {γ γ' : Γ} (s : S γ) (s' : S γ') (u : S γ) (u' : S γ') {g : Γ} (x : S g) (k : K) :
    (pt g x k ∈ quadSites sites γ γ' s s' u u' 0 ↔ k ∈ lev γ ∧ pt γ s k = pt g x k) ∧
    (pt g x k ∈ quadSites sites γ γ' s s' u u' 1 ↔ k ∈ lev γ' ∧ pt γ' s' k = pt g x k) ∧
    (pt g x k ∈ quadSites sites γ γ' s s' u u' 2 ↔ k ∈ lev γ ∧ pt γ u k = pt g x k) ∧
    (pt g x k ∈ quadSites sites γ γ' s s' u u' 3 ↔ k ∈ lev γ' ∧ pt γ' u' k = pt g x k) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [quadSites_zero, quadSites_one, quadSites_two, quadSites_three] <;>
    exact mem_sites_iff hsite hptc _ _ _ _ _

/-! #### The classification in coordinates -/

omit [(γ : Γ) → Fintype (S γ)] [Fintype K] [DecidableEq K] in
/-- On `f_γ ∖ f_{γ'}`, a nonzero moment forces `s_k = u_k`. -/
theorem eq_of_notMem_lev_right (h : IsBasisSystem μ U ψ Rpos B₀)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' → k = k')
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    {γ γ' : Γ} {s : S γ} {s' : S γ'} {u : S γ} {u' : S γ'}
    (hne : multiMoment μ U ψ (quadSites sites γ γ' s s' u u') (quadIdx rIdx γ γ') ≠ 0)
    {k : K} (hk : k ∈ lev γ) (hk' : k ∉ lev γ') : pt γ s k = pt γ u k := by
  by_contra hcon
  obtain ⟨m0, m1, m2, m3⟩ := quadSites_mem (lev := lev) hsite hptc s s' u u' s k
  have hfin : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  refine hne (multiMoment_eq_zero_of_isolated h (v := pt γ s k) (j := 0)
    (m0.2 ⟨hk, rfl⟩) ?_ ?_)
  · intro j' hj'
    rcases hfin j' with rfl | rfl | rfl | rfl
    · exact absurd rfl hj'
    · rw [m1]; rintro ⟨hcc, -⟩; exact hk' hcc
    · rw [m2]; rintro ⟨-, hcc⟩; exact hcon hcc.symm
    · rw [m3]; rintro ⟨hcc, -⟩; exact hk' hcc
  · rw [quadIdx_zero]
    exact hpos γ s _ (mem_sites_self (lev := lev) hsite γ s hk)

omit [(γ : Γ) → Fintype (S γ)] [Fintype K] [DecidableEq K] in
/-- On `f_{γ'} ∖ f_γ`, a nonzero moment forces `s'_k = u'_k`. -/
theorem eq_of_notMem_lev_left (h : IsBasisSystem μ U ψ Rpos B₀)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' → k = k')
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    {γ γ' : Γ} {s : S γ} {s' : S γ'} {u : S γ} {u' : S γ'}
    (hne : multiMoment μ U ψ (quadSites sites γ γ' s s' u u') (quadIdx rIdx γ γ') ≠ 0)
    {k : K} (hk' : k ∈ lev γ') (hk : k ∉ lev γ) : pt γ' s' k = pt γ' u' k := by
  by_contra hcon
  obtain ⟨m0, m1, m2, m3⟩ := quadSites_mem (lev := lev) hsite hptc s s' u u' s' k
  have hfin : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  refine hne (multiMoment_eq_zero_of_isolated h (v := pt γ' s' k) (j := 1)
    (m1.2 ⟨hk', rfl⟩) ?_ ?_)
  · intro j' hj'
    rcases hfin j' with rfl | rfl | rfl | rfl
    · rw [m0]; rintro ⟨hcc, -⟩; exact hk hcc
    · exact absurd rfl hj'
    · rw [m2]; rintro ⟨hcc, -⟩; exact hk hcc
    · rw [m3]; rintro ⟨-, hcc⟩; exact hcon hcc.symm
  · rw [quadIdx_one]
    exact hpos γ' s' _ (mem_sites_self (lev := lev) hsite γ' s' hk')

omit [(γ : Γ) → Fintype (S γ)] [Fintype K] [DecidableEq K] in
/-- On `f_γ ∩ f_{γ'}`, a nonzero moment forces one of the patterns (A), (B), (C). -/
theorem pattern_of_mem_inter (h : IsBasisSystem μ U ψ Rpos B₀)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' → k = k')
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    {γ γ' : Γ} {s : S γ} {s' : S γ'} {u : S γ} {u' : S γ'}
    (hne : multiMoment μ U ψ (quadSites sites γ γ' s s' u u') (quadIdx rIdx γ γ') ≠ 0)
    {k : K} (hk : k ∈ lev γ) (hk' : k ∈ lev γ') :
    (pt γ s k = pt γ' s' k ∧ pt γ u k = pt γ' u' k) ∨
      (pt γ s k = pt γ u k ∧ pt γ' s' k = pt γ' u' k) ∨
      (pt γ s k = pt γ' u' k ∧ pt γ' s' k = pt γ u k) := by
  by_contra hcon
  rw [not_or, not_or] at hcon
  obtain ⟨hA, hB, hC⟩ := hcon
  have hfin : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  rcases exists_isolated_of_not_pattern hA hB hC with
    ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
  · obtain ⟨m0, m1, m2, m3⟩ := quadSites_mem (lev := lev) hsite hptc s s' u u' s k
    refine hne (multiMoment_eq_zero_of_isolated h (v := pt γ s k) (j := 0)
      (m0.2 ⟨hk, rfl⟩) ?_ ?_)
    · intro j' hj'
      rcases hfin j' with rfl | rfl | rfl | rfl
      · exact absurd rfl hj'
      · rw [m1]; rintro ⟨-, hcc⟩; exact e1 hcc.symm
      · rw [m2]; rintro ⟨-, hcc⟩; exact e2 hcc.symm
      · rw [m3]; rintro ⟨-, hcc⟩; exact e3 hcc.symm
    · rw [quadIdx_zero]
      exact hpos γ s _ (mem_sites_self (lev := lev) hsite γ s hk)
  · obtain ⟨m0, m1, m2, m3⟩ := quadSites_mem (lev := lev) hsite hptc s s' u u' s' k
    refine hne (multiMoment_eq_zero_of_isolated h (v := pt γ' s' k) (j := 1)
      (m1.2 ⟨hk', rfl⟩) ?_ ?_)
    · intro j' hj'
      rcases hfin j' with rfl | rfl | rfl | rfl
      · rw [m0]; rintro ⟨-, hcc⟩; exact e1 hcc.symm
      · exact absurd rfl hj'
      · rw [m2]; rintro ⟨-, hcc⟩; exact e2 hcc.symm
      · rw [m3]; rintro ⟨-, hcc⟩; exact e3 hcc.symm
    · rw [quadIdx_one]
      exact hpos γ' s' _ (mem_sites_self (lev := lev) hsite γ' s' hk')
  · obtain ⟨m0, m1, m2, m3⟩ := quadSites_mem (lev := lev) hsite hptc s s' u u' u k
    refine hne (multiMoment_eq_zero_of_isolated h (v := pt γ u k) (j := 2)
      (m2.2 ⟨hk, rfl⟩) ?_ ?_)
    · intro j' hj'
      rcases hfin j' with rfl | rfl | rfl | rfl
      · rw [m0]; rintro ⟨-, hcc⟩; exact e1 hcc.symm
      · rw [m1]; rintro ⟨-, hcc⟩; exact e2 hcc.symm
      · exact absurd rfl hj'
      · rw [m3]; rintro ⟨-, hcc⟩; exact e3 hcc.symm
    · rw [quadIdx_two]
      exact hpos γ u _ (mem_sites_self (lev := lev) hsite γ u hk)
  · obtain ⟨m0, m1, m2, m3⟩ := quadSites_mem (lev := lev) hsite hptc s s' u u' u' k
    refine hne (multiMoment_eq_zero_of_isolated h (v := pt γ' u' k) (j := 3)
      (m3.2 ⟨hk', rfl⟩) ?_ ?_)
    · intro j' hj'
      rcases hfin j' with rfl | rfl | rfl | rfl
      · rw [m0]; rintro ⟨-, hcc⟩; exact e1 hcc.symm
      · rw [m1]; rintro ⟨-, hcc⟩; exact e2 hcc.symm
      · rw [m2]; rintro ⟨-, hcc⟩; exact e3 hcc.symm
      · exact absurd rfl hj'
    · rw [quadIdx_three]
      exact hpos γ' u' _ (mem_sites_self (lev := lev) hsite γ' u' hk')

/-! #### The three classes -/

/-- The pattern-(A) set `ℬ` of the configuration a quadruple carries. -/
def patAset (lev : Γ → Finset K) (pt : ∀ γ, S γ → K → V) (γ γ' : Γ) (s : S γ) (s' : S γ')
    (u : S γ) (u' : S γ') : Finset K :=
  (lev γ ∩ lev γ').filter (fun k => patAt pt γ γ' s s' u u' k = 0)

omit [Fintype V] [(γ : Γ) → Fintype (S γ)] [Fintype K] in
/-- On a Class-1 configuration no common coordinate carries pattern (A). -/
theorem patAt_ne_zero_of_patAset_empty {γ γ' : Γ} {s : S γ} {s' : S γ'} {u : S γ} {u' : S γ'}
    (hB : patAset lev pt γ γ' s s' u u' = ∅) {k : K} (hk : k ∈ lev γ) (hk' : k ∈ lev γ') :
    patAt pt γ γ' s s' u u' k ≠ 0 := by
  intro h0
  rw [patAset, Finset.filter_eq_empty_iff] at hB
  exact hB (Finset.mem_inter.2 ⟨hk, hk'⟩) h0

/-- **Class 2**: the pattern-(A) set `ℬ` is nonempty and `A_𝒫 = ℬ ∪ {k^⋆}` is a proper
subset of a level. -/
def IsClassTwo (lev : Γ → Finset K) (pt : ∀ γ, S γ → K → V) (γ γ' : Γ) (s : S γ) (s' : S γ')
    (u : S γ) (u' : S γ') : Prop :=
  (patAset lev pt γ γ' s s' u u').Nonempty ∧
    ¬ (lev γ = lev γ' ∧ patAset lev pt γ γ' s s' u u' = lev γ)

instance decidableIsClassTwo (lev : Γ → Finset K) (pt : ∀ γ, S γ → K → V) (γ γ' : Γ)
    (s : S γ) (s' : S γ') (u : S γ) (u' : S γ') :
    Decidable (IsClassTwo lev pt γ γ' s s' u u') := by
  unfold IsClassTwo
  infer_instance

/-- The Class-2 part of the quadruple sum for `𝔼[(Ξᵘ_{γγ'})²]`. -/
noncomputable def classTwoSum (μ : Measure Ω) (U : V → Ω → ℝ) (ψ : R → ℝ → ℝ)
    (sites : ∀ γ, S γ → Finset V) (rIdx : Γ → V → R) (arr : ∀ γ, S γ → I → ℝ)
    (lev : Γ → Finset K) (pt : ∀ γ, S γ → K → V) (γ γ' : Γ) : ℝ :=
  ∑ s : S γ, ∑ s' : S γ', ∑ u : S γ, ∑ u' : S γ',
    if IsClassTwo lev pt γ γ' s s' u u' then
      unmCoef sites rIdx arr γ γ' s s' * unmCoef sites rIdx arr γ γ' u u' *
        multiMoment μ U ψ (quadSites sites γ γ' s s' u u') (quadIdx rIdx γ γ')
    else 0

omit [(γ : Γ) → Fintype (S γ)] [Fintype K] in
/-- **Class 3.** If every coordinate of `f_γ = f_{γ'}` carries pattern (A) and the moment is
nonzero, then `(s,s')` is matched, so its coefficient in `Ξᵘ` vanishes. -/
theorem isMatched_of_patAset_eq (h : IsBasisSystem μ U ψ Rpos B₀)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' → k = k')
    {γ γ' : Γ} {s : S γ} {s' : S γ'} {u : S γ} {u' : S γ'}
    (hne : multiMoment μ U ψ (quadSites sites γ γ' s s' u u') (quadIdx rIdx γ γ') ≠ 0)
    (hlev : lev γ = lev γ') (hB : patAset lev pt γ γ' s s' u u' = lev γ) :
    IsMatched sites rIdx γ γ' s s' := by
  classical
  have hall : ∀ k ∈ lev γ, patAt pt γ γ' s s' u u' k = 0 := by
    intro k hk
    have hmem : k ∈ patAset lev pt γ γ' s s' u u' := by rw [hB]; exact hk
    exact (Finset.mem_filter.1 hmem).2
  constructor
  · rw [hsite γ s, hsite γ' s', ← hlev]
    refine Finset.image_congr ?_
    intro k hk
    exact (eq_of_patAt_eq_zero (pt := pt) (hall k (Finset.mem_coe.1 hk))).1
  · intro w hw
    rw [hsite γ s, Finset.mem_image] at hw
    obtain ⟨k, hk, rfl⟩ := hw
    obtain ⟨p1, p2, p3⟩ := eq_of_patAt_eq_zero (pt := pt) (hall k hk)
    obtain ⟨m0, m1, m2, m3⟩ := quadSites_mem (lev := lev) hsite hptc s s' u u' s k
    have hfin : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
    by_contra hcon
    refine hne (multiMoment_eq_zero_of_pair h (j := 0) (k := 1) (by decide)
      (m0.2 ⟨hk, rfl⟩) (m1.2 ⟨hlev ▸ hk, p1.symm⟩) ?_ ?_)
    · intro l hl0 hl1
      rcases hfin l with rfl | rfl | rfl | rfl
      · exact absurd rfl hl0
      · exact absurd rfl hl1
      · rw [m2]; rintro ⟨-, hcc⟩; exact p3 hcc.symm
      · rw [m3]; rintro ⟨-, hcc⟩; exact p3 (p2.trans hcc).symm
    · rw [quadIdx_zero, quadIdx_one]
      exact hcon

omit [(γ : Γ) → Fintype (S γ)] [Fintype K] in
/-- On a Class-1 configuration, `u` is determined by `(s,s')` coordinatewise. -/
theorem pt_u_eq_of_classOne (h : IsBasisSystem μ U ψ Rpos B₀)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' → k = k')
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    {γ γ' : Γ} {s : S γ} {s' : S γ'} {u : S γ} {u' : S γ'}
    (hne : multiMoment μ U ψ (quadSites sites γ γ' s s' u u') (quadIdx rIdx γ γ') ≠ 0)
    (hB : patAset lev pt γ γ' s s' u u' = ∅) {k : K} (hk : k ∈ lev γ) :
    pt γ u k = if patAt pt γ γ' s s' u u' k = 2 ∧ k ∈ lev γ' then pt γ' s' k else pt γ s k := by
  classical
  have hfin : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  by_cases hk' : k ∈ lev γ'
  · have hne0 : patAt pt γ γ' s s' u u' k ≠ 0 :=
      patAt_ne_zero_of_patAset_empty hB hk hk'
    rcases hfin (patAt pt γ γ' s s' u u' k) with hp | hp | hp | hp
    · exact absurd hp hne0
    · rw [hp, ite_eq_right (fun hcon => absurd hcon.1 (by decide))]
      exact (eq_of_patAt_eq_one (pt := pt) hp).1.symm
    · rw [hp, ite_eq_left ⟨rfl, hk'⟩]
      exact (eq_of_patAt_eq_two (pt := pt) hp).2.symm
    · rw [hp, ite_eq_right (fun hcon => absurd hcon.1 (by decide))]
      exact (all_eq_of_patAt_eq_three (pt := pt) hp
        (pattern_of_mem_inter h hsite hptc hpos hne hk hk')).2.1.symm
  · rw [ite_eq_right (fun hcon => hk' hcon.2)]
    exact (eq_of_notMem_lev_right h hsite hptc hpos hne hk hk').symm

omit [(γ : Γ) → Fintype (S γ)] [Fintype K] in
/-- The same for `u'`. -/
theorem pt_u'_eq_of_classOne (h : IsBasisSystem μ U ψ Rpos B₀)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' → k = k')
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    {γ γ' : Γ} {s : S γ} {s' : S γ'} {u : S γ} {u' : S γ'}
    (hne : multiMoment μ U ψ (quadSites sites γ γ' s s' u u') (quadIdx rIdx γ γ') ≠ 0)
    (hB : patAset lev pt γ γ' s s' u u' = ∅) {k : K} (hk' : k ∈ lev γ') :
    pt γ' u' k = if patAt pt γ γ' s s' u u' k = 2 ∧ k ∈ lev γ then pt γ s k else pt γ' s' k := by
  classical
  have hfin : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  by_cases hk : k ∈ lev γ
  · have hne0 : patAt pt γ γ' s s' u u' k ≠ 0 :=
      patAt_ne_zero_of_patAset_empty hB hk hk'
    rcases hfin (patAt pt γ γ' s s' u u' k) with hp | hp | hp | hp
    · exact absurd hp hne0
    · rw [hp, ite_eq_right (fun hcon => absurd hcon.1 (by decide))]
      exact (eq_of_patAt_eq_one (pt := pt) hp).2.symm
    · rw [hp, ite_eq_left ⟨rfl, hk⟩]
      exact (eq_of_patAt_eq_two (pt := pt) hp).1.symm
    · rw [hp, ite_eq_right (fun hcon => absurd hcon.1 (by decide))]
      have hD := all_eq_of_patAt_eq_three (pt := pt) hp
        (pattern_of_mem_inter h hsite hptc hpos hne hk hk')
      exact hD.2.2.symm.trans hD.1
  · rw [ite_eq_right (fun hcon => hk hcon.2)]
    exact (eq_of_notMem_lev_left h hsite hptc hpos hne hk' hk).symm

omit [(γ : Γ) → Fintype (S γ)] [Fintype K] in
/-- On a Class-1 configuration, `s` is determined by `(u,u')` coordinatewise. -/
theorem pt_s_eq_of_classOne (h : IsBasisSystem μ U ψ Rpos B₀)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' → k = k')
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    {γ γ' : Γ} {s : S γ} {s' : S γ'} {u : S γ} {u' : S γ'}
    (hne : multiMoment μ U ψ (quadSites sites γ γ' s s' u u') (quadIdx rIdx γ γ') ≠ 0)
    (hB : patAset lev pt γ γ' s s' u u' = ∅) {k : K} (hk : k ∈ lev γ) :
    pt γ s k = if patAt pt γ γ' s s' u u' k = 2 ∧ k ∈ lev γ' then pt γ' u' k else pt γ u k := by
  classical
  have hfin : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  by_cases hk' : k ∈ lev γ'
  · have hne0 : patAt pt γ γ' s s' u u' k ≠ 0 :=
      patAt_ne_zero_of_patAset_empty hB hk hk'
    rcases hfin (patAt pt γ γ' s s' u u' k) with hp | hp | hp | hp
    · exact absurd hp hne0
    · rw [hp, ite_eq_right (fun hcon => absurd hcon.1 (by decide))]
      exact (eq_of_patAt_eq_one (pt := pt) hp).1
    · rw [hp, ite_eq_left ⟨rfl, hk'⟩]
      exact (eq_of_patAt_eq_two (pt := pt) hp).1
    · rw [hp, ite_eq_right (fun hcon => absurd hcon.1 (by decide))]
      exact (all_eq_of_patAt_eq_three (pt := pt) hp
        (pattern_of_mem_inter h hsite hptc hpos hne hk hk')).2.1
  · rw [ite_eq_right (fun hcon => hk' hcon.2)]
    exact eq_of_notMem_lev_right h hsite hptc hpos hne hk hk'

omit [(γ : Γ) → Fintype (S γ)] [Fintype K] in
/-- The same for `s'`. -/
theorem pt_s'_eq_of_classOne (h : IsBasisSystem μ U ψ Rpos B₀)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' → k = k')
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    {γ γ' : Γ} {s : S γ} {s' : S γ'} {u : S γ} {u' : S γ'}
    (hne : multiMoment μ U ψ (quadSites sites γ γ' s s' u u') (quadIdx rIdx γ γ') ≠ 0)
    (hB : patAset lev pt γ γ' s s' u u' = ∅) {k : K} (hk' : k ∈ lev γ') :
    pt γ' s' k = if patAt pt γ γ' s s' u u' k = 2 ∧ k ∈ lev γ then pt γ u k else pt γ' u' k := by
  classical
  have hfin : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  by_cases hk : k ∈ lev γ
  · have hne0 : patAt pt γ γ' s s' u u' k ≠ 0 :=
      patAt_ne_zero_of_patAset_empty hB hk hk'
    rcases hfin (patAt pt γ γ' s s' u u' k) with hp | hp | hp | hp
    · exact absurd hp hne0
    · rw [hp, ite_eq_right (fun hcon => absurd hcon.1 (by decide))]
      exact (eq_of_patAt_eq_one (pt := pt) hp).2
    · rw [hp, ite_eq_left ⟨rfl, hk⟩]
      exact (eq_of_patAt_eq_two (pt := pt) hp).2
    · rw [hp, ite_eq_right (fun hcon => absurd hcon.1 (by decide))]
      have hD := all_eq_of_patAt_eq_three (pt := pt) hp
        (pattern_of_mem_inter h hsite hptc hpos hne hk hk')
      exact hD.1.symm.trans hD.2.2
  · rw [ite_eq_right (fun hcon => hk hcon.2)]
    exact eq_of_notMem_lev_left h hsite hptc hpos hne hk' hk

/-! #### The unmatched part with the Class-2 bound as a hypothesis -/

/-- `𝔼[(Ξᵘ_{γγ'})²] ≤ 4^{|K|}max(B_0,1)^{4M}‖G_{γγ'}‖_F² + b₂`, given the bound `b₂` on the
Class-2 part. -/
theorem integral_sq_unmatchedPart_le_of_classTwo_ofCard (h : IsBasisSystem μ U ψ Rpos B₀)
    {M : ℕ}
    (hlev : ∀ (g : Γ) (x : S g), (sites g x).card ≤ M)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' → k = k')
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y → x = y)
    (γ γ' : Γ) {b₂ : ℝ}
    (hcls2 : |classTwoSum μ U ψ sites rIdx arr lev pt γ γ'| ≤ b₂) :
    ∫ ω, (unmatchedPart U ψ sites rIdx arr tag γ γ' ω) ^ 2 ∂μ
      ≤ (4:ℝ) ^ Fintype.card K * max B₀ 1 ^ (4 * M) *
          rectFrobSq (Matrix.of (arr γ) * (Matrix.of (arr γ'))ᵀ) + b₂ := by
  classical
  have hP : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have hb₂ : (0:ℝ) ≤ b₂ := le_trans (abs_nonneg _) hcls2
  have hM : (0:ℝ) ≤ max B₀ 1 ^ (4 * M) := by positivity
  have hfrob : (0:ℝ) ≤ rectFrobSq (Matrix.of (arr γ) * (Matrix.of (arr γ'))ᵀ) :=
    rectFrobSq_nonneg _
  have hRHS : (0:ℝ) ≤ (4:ℝ) ^ Fintype.card K * max B₀ 1 ^ (4 * M) *
      rectFrobSq (Matrix.of (arr γ) * (Matrix.of (arr γ'))ᵀ) := by positivity
  by_cases htag : tag γ = tag γ'
  · -- expand the square over quadruples
    set c : S γ → S γ' → ℝ := fun x y => unmCoef sites rIdx arr γ γ' x y with hcdef
    set Qf : S γ → S γ' → S γ → S γ' → ℝ := fun x y z w =>
      multiMoment μ U ψ (quadSites sites γ γ' x y z w) (quadIdx rIdx γ γ') with hQfdef
    have hexpand : ∫ ω, (unmatchedPart U ψ sites rIdx arr tag γ γ' ω) ^ 2 ∂μ
        = ∑ s : S γ, ∑ s' : S γ', ∑ u : S γ, ∑ u' : S γ', c s s' * c u u' * Qf s s' u u' := by
      have hfun : (fun ω => (unmatchedPart U ψ sites rIdx arr tag γ γ' ω) ^ 2)
          = fun ω => (∑ s : S γ, ∑ s' : S γ', c s s' *
              (basisProd U ψ sites rIdx γ s ω * basisProd U ψ sites rIdx γ' s' ω)) ^ 2 := by
        funext ω
        rw [unmatchedPart_eq_sum_unmCoef γ γ' htag ω]
      rw [hfun, integral_sq_double_sum c _ _
        (fun a b a' b' => integrable_basisProd_four h γ γ' a a' b b')]
      exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ =>
        Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => by
          rw [integral_basisProd_four_eq_multiMoment]
    rw [hexpand]
    -- flatten the quadruple sum
    set F : ((S γ × S γ') × (S γ × S γ')) → ℝ :=
      fun q => c q.1.1 q.1.2 * c q.2.1 q.2.2 * Qf q.1.1 q.1.2 q.2.1 q.2.2 with hFdef
    have hflat : ∑ s : S γ, ∑ s' : S γ', ∑ u : S γ, ∑ u' : S γ', c s s' * c u u' * Qf s s' u u'
        = ∑ q : (S γ × S γ') × (S γ × S γ'), F q := by
      rw [hFdef]
      simp only [Fintype.sum_prod_type]
    rw [hflat]
    -- split off the Class-2 part, pointwise rather than by filtering
    set A1 : Finset ((S γ × S γ') × (S γ × S γ')) :=
      Finset.univ.filter
        (fun q => ¬ IsClassTwo lev pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2 ∧ F q ≠ 0) with hA1def
    have hC2eq : ∑ q : (S γ × S γ') × (S γ × S γ'),
        (if IsClassTwo lev pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2 then F q else 0)
          = classTwoSum μ U ψ sites rIdx arr lev pt γ γ' := by
      rw [classTwoSum]
      simp only [Fintype.sum_prod_type, hFdef, hcdef, hQfdef]
    have hQne : ∀ q : (S γ × S γ') × (S γ × S γ'), F q ≠ 0 →
        Qf q.1.1 q.1.2 q.2.1 q.2.2 ≠ 0 := by
      intro q hq h0
      exact hq (by rw [hFdef]; simp [h0])
    -- every surviving quadruple outside Class 2 is Class 1
    have hBempty : ∀ q ∈ A1, patAset lev pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2 = ∅ := by
      intro q hq
      rw [hA1def, Finset.mem_filter] at hq
      obtain ⟨-, hnc, hFne⟩ := hq
      by_contra hBne
      refine hFne ?_
      have hNE : (patAset lev pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2).Nonempty :=
        Finset.nonempty_of_ne_empty hBne
      have hcls3 : lev γ = lev γ' ∧ patAset lev pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2 = lev γ := by
        by_contra hc3
        exact hnc ⟨hNE, hc3⟩
      have hmatch := isMatched_of_patAset_eq h hsite hptc (hQne q hFne) hcls3.1 hcls3.2
      rw [hFdef]
      simp [hcdef, unmCoef, hmatch]
    have hA1eq : ∑ q : (S γ × S γ') × (S γ × S γ'),
        (if IsClassTwo lev pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2 then 0 else F q)
          = ∑ q ∈ A1, F q := by
      rw [hA1def, Finset.sum_filter]
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hcl : IsClassTwo lev pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2
      · simp [hcl]
      · by_cases hz : F q = 0 <;> simp [hcl, hz]
    have hsplit : ∑ q : (S γ × S γ') × (S γ × S γ'), F q
        = classTwoSum μ U ψ sites rIdx arr lev pt γ γ' + ∑ q ∈ A1, F q := by
      have hptsplit : ∀ q : (S γ × S γ') × (S γ × S γ'),
          F q = (if IsClassTwo lev pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2 then F q else 0)
              + (if IsClassTwo lev pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2 then 0 else F q) := by
        intro q
        split_ifs <;> ring
      rw [Finset.sum_congr rfl fun q _ => hptsplit q, Finset.sum_add_distrib, hC2eq, hA1eq]
    -- the Class-1 part, one configuration at a time
    set PM : ((S γ × S γ') × (S γ × S γ')) → (K → Fin 4) :=
      fun q => patAt pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2 with hPMdef
    have hper : ∀ cfg : K → Fin 4, |∑ q ∈ A1.filter (fun q => PM q = cfg), F q|
        ≤ max B₀ 1 ^ (4 * M) *
          rectFrobSq (Matrix.of (arr γ) * (Matrix.of (arr γ'))ᵀ) := by
      intro cfg
      have hdet : ∀ q ∈ A1.filter (fun q => PM q = cfg), ∀ q' ∈ A1.filter (fun q => PM q = cfg),
          (q.1 = q'.1 → q.2 = q'.2) ∧ (q.2 = q'.2 → q.1 = q'.1) := by
        intro q hq q' hq'
        rw [Finset.mem_filter] at hq hq'
        obtain ⟨hqA, hqP⟩ := hq
        obtain ⟨hq'A, hq'P⟩ := hq'
        have hQ1 : Qf q.1.1 q.1.2 q.2.1 q.2.2 ≠ 0 := by
          refine hQne q ?_
          rw [hA1def, Finset.mem_filter] at hqA
          exact hqA.2.2
        have hQ2 : Qf q'.1.1 q'.1.2 q'.2.1 q'.2.2 ≠ 0 := by
          refine hQne q' ?_
          rw [hA1def, Finset.mem_filter] at hq'A
          exact hq'A.2.2
        have hB1 := hBempty q hqA
        have hB2 := hBempty q' hq'A
        have hp1 : ∀ k, patAt pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2 k = cfg k := fun k =>
          congrFun hqP k
        have hp2 : ∀ k, patAt pt γ γ' q'.1.1 q'.1.2 q'.2.1 q'.2.2 k = cfg k := fun k =>
          congrFun hq'P k
        constructor
        · intro hEq
          have hu : q.2.1 = q'.2.1 := by
            refine hinj γ _ _ ?_
            rw [hsite γ q.2.1, hsite γ q'.2.1]
            refine Finset.image_congr ?_
            intro k hk
            have hk' : k ∈ lev γ := Finset.mem_coe.1 hk
            rw [pt_u_eq_of_classOne h hsite hptc hpos hQ1 hB1 hk',
              pt_u_eq_of_classOne h hsite hptc hpos hQ2 hB2 hk', hp1 k, hp2 k, hEq]
          have hu' : q.2.2 = q'.2.2 := by
            refine hinj γ' _ _ ?_
            rw [hsite γ' q.2.2, hsite γ' q'.2.2]
            refine Finset.image_congr ?_
            intro k hk
            have hk' : k ∈ lev γ' := Finset.mem_coe.1 hk
            rw [pt_u'_eq_of_classOne h hsite hptc hpos hQ1 hB1 hk',
              pt_u'_eq_of_classOne h hsite hptc hpos hQ2 hB2 hk', hp1 k, hp2 k, hEq]
          exact Prod.ext hu hu'
        · intro hEq
          have hs : q.1.1 = q'.1.1 := by
            refine hinj γ _ _ ?_
            rw [hsite γ q.1.1, hsite γ q'.1.1]
            refine Finset.image_congr ?_
            intro k hk
            have hk' : k ∈ lev γ := Finset.mem_coe.1 hk
            rw [pt_s_eq_of_classOne h hsite hptc hpos hQ1 hB1 hk',
              pt_s_eq_of_classOne h hsite hptc hpos hQ2 hB2 hk', hp1 k, hp2 k, hEq]
          have hs' : q.1.2 = q'.1.2 := by
            refine hinj γ' _ _ ?_
            rw [hsite γ' q.1.2, hsite γ' q'.1.2]
            refine Finset.image_congr ?_
            intro k hk
            have hk' : k ∈ lev γ' := Finset.mem_coe.1 hk
            rw [pt_s'_eq_of_classOne h hsite hptc hpos hQ1 hB1 hk',
              pt_s'_eq_of_classOne h hsite hptc hpos hQ2 hB2 hk', hp1 k, hp2 k, hEq]
          exact Prod.ext hs hs'
      refine le_trans (abs_sum_quad_pairs_le c Qf hM (fun x y z w => abs_multiMoment_le_ofCard h _ (card_quadSites_le hlev γ γ' x y z w) _)
        (A1.filter (fun q => PM q = cfg)) ?_ ?_) ?_
      · intro q hq q' hq' hEq
        exact Prod.ext hEq ((hdet q hq q' hq').1 hEq)
      · intro q hq q' hq' hEq
        exact Prod.ext ((hdet q hq q' hq').2 hEq) hEq
      · exact mul_le_mul_of_nonneg_left (sum_sq_unmCoef_le (sites := sites) (rIdx := rIdx) γ γ')
          hM
    have hfib : ∑ q ∈ A1, F q = ∑ cfg : K → Fin 4, ∑ q ∈ A1.filter (fun q => PM q = cfg), F q :=
      (Finset.sum_fiberwise A1 PM F).symm
    have hA1bound : |∑ q ∈ A1, F q| ≤ (4:ℝ) ^ Fintype.card K *
        max B₀ 1 ^ (4 * M) *
        rectFrobSq (Matrix.of (arr γ) * (Matrix.of (arr γ'))ᵀ) := by
      rw [hfib]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum fun cfg _ => hper cfg) ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun, Fintype.card_fin]
      push_cast
      exact le_of_eq (by ring)
    calc ∑ q : (S γ × S γ') × (S γ × S γ'), F q
        ≤ |∑ q : (S γ × S γ') × (S γ × S γ'), F q| := le_abs_self _
      _ ≤ |classTwoSum μ U ψ sites rIdx arr lev pt γ γ'| + |∑ q ∈ A1, F q| := by
          rw [hsplit]; exact abs_add_le _ _
      _ ≤ b₂ + (4:ℝ) ^ Fintype.card K * max B₀ 1 ^ (4 * M) *
            rectFrobSq (Matrix.of (arr γ) * (Matrix.of (arr γ'))ᵀ) :=
          add_le_add hcls2 hA1bound
      _ = (4:ℝ) ^ Fintype.card K * max B₀ 1 ^ (4 * M) *
            rectFrobSq (Matrix.of (arr γ) * (Matrix.of (arr γ'))ᵀ) + b₂ := by ring
  · have h0 : unmatchedPart U ψ sites rIdx arr tag γ γ' = fun _ => (0:ℝ) := by
      funext ω
      simp [unmatchedPart, htag]
    rw [h0]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero]
    linarith


/-- `𝔼[(Ξᵘ_{γγ'})²] ≤ 4^{|K|}max(B_0,1)^{4|V|}‖G_{γγ'}‖_F² + b₂`, given the bound `b₂` on the
Class-2 part. -/
theorem integral_sq_unmatchedPart_le_of_classTwo (h : IsBasisSystem μ U ψ Rpos B₀)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' → k = k')
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y → x = y)
    (γ γ' : Γ) {b₂ : ℝ}
    (hcls2 : |classTwoSum μ U ψ sites rIdx arr lev pt γ γ'| ≤ b₂) :
    ∫ ω, (unmatchedPart U ψ sites rIdx arr tag γ γ' ω) ^ 2 ∂μ
      ≤ (4:ℝ) ^ Fintype.card K * max B₀ 1 ^ (4 * Fintype.card V) *
          rectFrobSq (Matrix.of (arr γ) * (Matrix.of (arr γ'))ᵀ) + b₂ := by
  apply integral_sq_unmatchedPart_le_of_classTwo_ofCard (M := Fintype.card V) <;>
    first
      | assumption
      | exact fun _ _ => Finset.card_le_univ _
      | exact fun _ => Finset.card_le_univ _
omit [Fintype K] in
/-- Class 2 is empty when every level has at most one coordinate: a nonempty
`ℬ ⊆ f_γ ∩ f_{γ'}` is then `f_γ = f_{γ'}`. -/
theorem classTwoSum_eq_zero_of_card_le_one (hcard : ∀ g : Γ, (lev g).card ≤ 1) (γ γ' : Γ) :
    classTwoSum μ U ψ sites rIdx arr lev pt γ γ' = 0 := by
  classical
  refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun s' _ =>
    Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun u' _ => ?_
  have hnot : ¬ IsClassTwo lev pt γ γ' s s' u u' := by
    rintro ⟨hNE, hnc⟩
    have hsub : patAset lev pt γ γ' s s' u u' ⊆ lev γ ∩ lev γ' := Finset.filter_subset _ _
    have hcardB : 1 ≤ (patAset lev pt γ γ' s s' u u').card := Finset.card_pos.2 hNE
    have hEqγ : patAset lev pt γ γ' s s' u u' = lev γ :=
      Finset.eq_of_subset_of_card_le (hsub.trans Finset.inter_subset_left)
        (le_trans (hcard γ) hcardB)
    have hEqγ' : patAset lev pt γ γ' s s' u u' = lev γ' :=
      Finset.eq_of_subset_of_card_le (hsub.trans Finset.inter_subset_right)
        (le_trans (hcard γ') hcardB)
    exact hnc ⟨hEqγ.symm.trans hEqγ', hEqγ⟩
  rw [ite_eq_right hnot]

/-- Lemma SM.C.3(b) at general level size, with the matched-part bound `hstep2` and the
Class-2 bound `hcls2` as hypotheses, sharing a constant `Cst ≥ 0`. -/
theorem concentration_clause_b_general_of_classTwo_ofCard [Fintype Γ] [DecidableEq Γ]
    (h : IsBasisSystem μ U ψ Rpos B₀) {M : ℕ}
    (hlev : ∀ (g : Γ) (x : S g), (sites g x).card ≤ M)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' → k = k')
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y → x = y)
    (hsep : ∀ (g g' : Γ) (x : S g) (y : S g'), tag g = tag g' → sites g x = sites g' y →
      (∀ w ∈ sites g x, rIdx g w = rIdx g' w) → g = g')
    {lam : Γ → ℝ} (hlam : ∑ γ, lam γ ^ 2 ≤ 1) {Cst cutmax totmax : ℝ} (hCst : 0 ≤ Cst)
    (hcut : ∀ γ : Γ, rectFrobNorm (Matrix.of (arr γ) * (Matrix.of (arr γ))ᵀ) ≤ cutmax)
    (htot : ∀ γ : Γ, rectFrobSq (arr γ) ≤ totmax)
    (hstep2 : ∀ γ : Γ, variance (matchedPart U ψ sites rIdx arr γ) μ ≤ Cst * (cutmax * totmax))
    (hcls2 : ∀ γ γ' : Γ,
      |classTwoSum μ U ψ sites rIdx arr lev pt γ γ'| ≤ Cst * (cutmax * totmax)) :
    variance (fun ω => ∑ γ : Γ, ∑ γ' : Γ,
        lam γ * lam γ' * cvarEntry U ψ sites rIdx arr tag γ γ' ω) μ
      ≤ 4 * (Fintype.card Γ : ℝ) ^ 2 *
          (2 * Cst + (4:ℝ) ^ Fintype.card K * max B₀ 1 ^ (4 * M)) *
          (cutmax * totmax) := by
  classical
  have hM : (0:ℝ) ≤ (4:ℝ) ^ Fintype.card K * max B₀ 1 ^ (4 * M) := by positivity
  have hnn : ∀ _g : Γ, (0:ℝ) ≤ cutmax * totmax := by
    intro g
    have h1 : (0:ℝ) ≤ cutmax := le_trans (rectFrobNorm_nonneg _) (hcut g)
    have h2 : (0:ℝ) ≤ totmax := le_trans (rectFrobSq_nonneg _) (htot g)
    exact mul_nonneg h1 h2
  have hbase : ∀ g g' : Γ,
      rectFrobSq (Matrix.of (arr g) * (Matrix.of (arr g'))ᵀ) ≤ cutmax * totmax := by
    intro g g'
    refine le_trans (rectFrobSq_gram_le g g') ?_
    exact mul_le_mul (hcut g)
      (le_trans (rectFrobNorm_mul_transpose_self_le _) (htot g'))
      (rectFrobNorm_nonneg _) (le_trans (rectFrobNorm_nonneg _) (hcut g))
  refine concentration_clause_b_cut_tot h hinj hsep hlam ?_ ?_
  · intro γ
    refine le_trans (hstep2 γ) (mul_le_mul_of_nonneg_right ?_ (hnn γ))
    linarith
  · intro γ γ'
    refine le_trans (integral_sq_unmatchedPart_le_of_classTwo_ofCard h hlev hsite hptc hpos hinj γ γ'
      (hcls2 γ γ')) ?_
    calc (4:ℝ) ^ Fintype.card K * max B₀ 1 ^ (4 * M) *
          rectFrobSq (Matrix.of (arr γ) * (Matrix.of (arr γ'))ᵀ) + Cst * (cutmax * totmax)
        ≤ (4:ℝ) ^ Fintype.card K * max B₀ 1 ^ (4 * M) * (cutmax * totmax)
            + Cst * (cutmax * totmax) := by
          have hstep := mul_le_mul_of_nonneg_left (hbase γ γ') hM
          linarith
      _ = ((4:ℝ) ^ Fintype.card K * max B₀ 1 ^ (4 * M) + Cst) *
            (cutmax * totmax) := by ring
      _ ≤ (2 * Cst + (4:ℝ) ^ Fintype.card K * max B₀ 1 ^ (4 * M)) *
            (cutmax * totmax) :=
          mul_le_mul_of_nonneg_right (by linarith) (hnn γ)


/-- Lemma SM.C.3(b) at general level size with `hstep2` and `hcls2` as hypotheses, with
constant in terms of `|V|`. -/
theorem concentration_clause_b_general_of_classTwo [Fintype Γ] [DecidableEq Γ]
    (h : IsBasisSystem μ U ψ Rpos B₀)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' → k = k')
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y → x = y)
    (hsep : ∀ (g g' : Γ) (x : S g) (y : S g'), tag g = tag g' → sites g x = sites g' y →
      (∀ w ∈ sites g x, rIdx g w = rIdx g' w) → g = g')
    {lam : Γ → ℝ} (hlam : ∑ γ, lam γ ^ 2 ≤ 1) {Cst cutmax totmax : ℝ} (hCst : 0 ≤ Cst)
    (hcut : ∀ γ : Γ, rectFrobNorm (Matrix.of (arr γ) * (Matrix.of (arr γ))ᵀ) ≤ cutmax)
    (htot : ∀ γ : Γ, rectFrobSq (arr γ) ≤ totmax)
    (hstep2 : ∀ γ : Γ, variance (matchedPart U ψ sites rIdx arr γ) μ ≤ Cst * (cutmax * totmax))
    (hcls2 : ∀ γ γ' : Γ,
      |classTwoSum μ U ψ sites rIdx arr lev pt γ γ'| ≤ Cst * (cutmax * totmax)) :
    variance (fun ω => ∑ γ : Γ, ∑ γ' : Γ,
        lam γ * lam γ' * cvarEntry U ψ sites rIdx arr tag γ γ' ω) μ
      ≤ 4 * (Fintype.card Γ : ℝ) ^ 2 *
          (2 * Cst + (4:ℝ) ^ Fintype.card K * max B₀ 1 ^ (4 * Fintype.card V)) *
          (cutmax * totmax) := by
  apply concentration_clause_b_general_of_classTwo_ofCard (M := Fintype.card V) <;>
    first
      | assumption
      | exact fun _ _ => Finset.card_le_univ _
      | exact fun _ => Finset.card_le_univ _

set_option linter.unusedSectionVars false in
/-- The same with `max(B_0,1)^{4|K|}` in place of `max(B_0,1)^{4|V|}`; the level bound follows
from `hsite`. -/
theorem concentration_clause_b_general_of_classTwo_uniform [Fintype Γ] [DecidableEq Γ]
    (h : IsBasisSystem μ U ψ Rpos B₀)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' → k = k')
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y → x = y)
    (hsep : ∀ (g g' : Γ) (x : S g) (y : S g'), tag g = tag g' → sites g x = sites g' y →
      (∀ w ∈ sites g x, rIdx g w = rIdx g' w) → g = g')
    {lam : Γ → ℝ} (hlam : ∑ γ, lam γ ^ 2 ≤ 1) {Cst cutmax totmax : ℝ} (hCst : 0 ≤ Cst)
    (hcut : ∀ γ : Γ, rectFrobNorm (Matrix.of (arr γ) * (Matrix.of (arr γ))ᵀ) ≤ cutmax)
    (htot : ∀ γ : Γ, rectFrobSq (arr γ) ≤ totmax)
    (hstep2 : ∀ γ : Γ, variance (matchedPart U ψ sites rIdx arr γ) μ ≤ Cst * (cutmax * totmax))
    (hcls2 : ∀ γ γ' : Γ,
      |classTwoSum μ U ψ sites rIdx arr lev pt γ γ'| ≤ Cst * (cutmax * totmax)) :
    variance (fun ω => ∑ γ : Γ, ∑ γ' : Γ,
        lam γ * lam γ' * cvarEntry U ψ sites rIdx arr tag γ γ' ω) μ
      ≤ 4 * (Fintype.card Γ : ℝ) ^ 2 *
          (2 * Cst + (4:ℝ) ^ Fintype.card K * max B₀ 1 ^ (4 * Fintype.card K)) *
          (cutmax * totmax) :=
  concentration_clause_b_general_of_classTwo_ofCard h (card_sites_le_card_K hsite)
    hsite hptc hpos hinj hsep hlam hCst hcut htot hstep2 hcls2

/-! ### The key encoding of a sub-tuple at a contraction set `Bs` -/

/-- The **row key** of a sub-tuple at the contraction set `Bs`: its coordinates inside `Bs`. -/
def bKey (pt : ∀ γ, S γ → K → V) (Bs : Finset K) (g : Γ) (x : S g) : K → Option V :=
  fun k => if k ∈ Bs then some (pt g x k) else none

/-- The **column key**: the sub-tuple's coordinates in `lev g \ Bs`. -/
def cKey (lev : Γ → Finset K) (pt : ∀ γ, S γ → K → V) (Bs : Finset K) (g : Γ) (x : S g) :
    K → Option V :=
  fun k => if k ∈ lev g \ Bs then some (pt g x k) else none

omit [Fintype V] [DecidableEq V] [(γ : Γ) → Fintype (S γ)] [Fintype K] in
theorem bKey_apply_of_mem {Bs : Finset K} {g : Γ} (x : S g) {k : K} (hk : k ∈ Bs) :
    bKey pt Bs g x k = some (pt g x k) := by simp [bKey, hk]

omit [Fintype V] [DecidableEq V] [(γ : Γ) → Fintype (S γ)] [Fintype K] in
theorem cKey_apply_of_mem {Bs : Finset K} {g : Γ} (x : S g) {k : K} (hk : k ∈ lev g)
    (hk' : k ∉ Bs) : cKey lev pt Bs g x k = some (pt g x k) := by
  simp [cKey, Finset.mem_sdiff, hk, hk']

omit [Fintype V] [DecidableEq V] [(γ : Γ) → Fintype (S γ)] [Fintype K] in
theorem cKey_apply_of_notMem {Bs : Finset K} {g : Γ} (x : S g) {k : K} (hk : k ∉ lev g \ Bs) :
    cKey lev pt Bs g x k = none := by simp [cKey, hk]

omit [Fintype V] [DecidableEq V] [(γ : Γ) → Fintype (S γ)] [Fintype K] in
/-- The two keys together pin every coordinate inside the level. -/
theorem pt_eq_of_keys {Bs : Finset K} {g : Γ} {x y : S g}
    (hb : bKey pt Bs g x = bKey pt Bs g y) (hc : cKey lev pt Bs g x = cKey lev pt Bs g y)
    {k : K} (hk : k ∈ lev g) : pt g x k = pt g y k := by
  by_cases hkB : k ∈ Bs
  · have := congrFun hb k
    rw [bKey_apply_of_mem x hkB, bKey_apply_of_mem y hkB] at this
    exact Option.some.inj this
  · have := congrFun hc k
    rw [cKey_apply_of_mem (lev := lev) x hk hkB, cKey_apply_of_mem (lev := lev) y hk hkB] at this
    exact Option.some.inj this

omit [Fintype V] [(γ : Γ) → Fintype (S γ)] [Fintype K] in
/-- The key pair determines the sub-tuple. -/
theorem eq_of_keys (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y → x = y)
    {Bs : Finset K} {g : Γ} {x y : S g}
    (hb : bKey pt Bs g x = bKey pt Bs g y) (hc : cKey lev pt Bs g x = cKey lev pt Bs g y) :
    x = y := by
  refine hinj g x y ?_
  rw [hsite g x, hsite g y]
  exact Finset.image_congr fun k hk => pt_eq_of_keys hb hc (Finset.mem_coe.1 hk)

/-! ### The `A_𝒫`-matricization `F^γ_{Bs ∪ {k^⋆}}` -/

/-- **The matricization of `V^{(g)}` at the coordinate set `Bs ∪ {k^⋆}`**: rows indexed by a
`Bs`-key together with the `k^⋆`-index `i`, columns by a `lev g \ Bs`-key. The fibres of the key
pair are subsingletons, so each entry is a single array value or zero. -/
noncomputable def levMat (lev : Γ → Finset K) (pt : ∀ γ, S γ → K → V) (Bs : Finset K) (g : Γ)
    (a : S g → I → ℝ) : ((K → Option V) × I) → (K → Option V) → ℝ :=
  fun p v => ∑ x : S g, if bKey pt Bs g x = p.1 ∧ cKey lev pt Bs g x = v then a x p.2 else 0

omit [Fintype V] [Fintype I] in
theorem levMat_apply (Bs : Finset K) (g : Γ) (a : S g → I → ℝ) (r v : K → Option V) (i : I) :
    levMat lev pt Bs g a (r, i) v
      = ∑ x ∈ Finset.univ.filter
          (fun x => bKey pt Bs g x = r ∧ cKey lev pt Bs g x = v), a x i := by
  classical
  rw [levMat, Finset.sum_filter]

omit [Fintype V] in
/-- Every fibre of the key pair is a subsingleton. -/
theorem subsingleton_key_fiber (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y → x = y)
    {Bs : Finset K} {g : Γ} {a v : K → Option V} :
    ∀ x ∈ Finset.univ.filter (fun x : S g => bKey pt Bs g x = a ∧ cKey lev pt Bs g x = v),
      ∀ y ∈ Finset.univ.filter (fun x : S g => bKey pt Bs g x = a ∧ cKey lev pt Bs g x = v),
      x = y := by
  classical
  intro x hx y hy
  rw [Finset.mem_filter] at hx hy
  exact eq_of_keys (sites := sites) hsite hinj (hx.2.1.trans hy.2.1.symm)
    (hx.2.2.trans hy.2.2.symm)

omit [Fintype I] in
/-- Summing a fibrewise sum over both keys is summing over the sub-tuples. -/
theorem sum_over_keys {g : Γ} {Bs : Finset K} (f : S g -> Real) :
    (Finset.univ.sum fun a : K -> Option V => Finset.univ.sum fun v : K -> Option V =>
      (Finset.univ.filter
        (fun x => bKey pt Bs g x = a /\ cKey lev pt Bs g x = v)).sum f)
      = Finset.univ.sum f := by
  classical
  have hfib := Finset.sum_fiberwise (Finset.univ : Finset (S g))
    (fun x => (bKey pt Bs g x, cKey lev pt Bs g x)) f
  rw [<- hfib, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun v _ => ?_
  congr 1
  ext x
  simp [Prod.ext_iff]

/-- The matricization carries each array entry once, so its squared Frobenius norm is
`tot(g)`. -/
theorem rectFrobSq_levMat (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y -> x = y)
    (Bs : Finset K) (g : Γ) (a : S g -> I -> Real) :
    rectFrobSq (levMat lev pt Bs g a) = rectFrobSq a := by
  classical
  have h1 : ∀ (r v : K -> Option V) (i : I),
      (levMat lev pt Bs g a (r, i) v) ^ 2
        = (Finset.univ.filter
            (fun x => bKey pt Bs g x = r /\ cKey lev pt Bs g x = v)).sum
              (fun x => (a x i) ^ 2) := by
    intro r v i
    rw [levMat_apply]
    exact sq_sum_of_subsingleton _ _ (subsingleton_key_fiber (sites := sites) hsite hinj)
  have hL : rectFrobSq (levMat lev pt Bs g a)
      = Finset.univ.sum fun i : I => Finset.univ.sum fun r : K -> Option V =>
          Finset.univ.sum fun v : K -> Option V =>
            (Finset.univ.filter
              (fun x => bKey pt Bs g x = r /\ cKey lev pt Bs g x = v)).sum
                (fun x => (a x i) ^ 2) := by
    simp only [rectFrobSq]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => ?_
    exact Finset.sum_congr rfl fun v _ => h1 r v i
  rw [hL]
  have h2 : ∀ i : I,
      (Finset.univ.sum fun r : K -> Option V => Finset.univ.sum fun v : K -> Option V =>
        (Finset.univ.filter
          (fun x => bKey pt Bs g x = r /\ cKey lev pt Bs g x = v)).sum
            (fun x => (a x i) ^ 2))
        = Finset.univ.sum fun x : S g => (a x i) ^ 2 :=
    fun i => sum_over_keys (lev := lev) (pt := pt) (Bs := Bs) _
  rw [Finset.sum_congr rfl fun i _ => h2 i]
  simp only [rectFrobSq]
  exact Finset.sum_comm

/-! ### The contraction `H_{v,v'} = sum_a G_{(v,a),(v',a)}` -/

/-- The contraction `H_{v,v'} = ∑_aG_{(v,a),(v',a)}` of a coefficient array `c`. -/
noncomputable def contrEntry (lev : Γ -> Finset K) (pt : ∀ γ, S γ -> K -> V)
    (Bs : Finset K) (γ γ' : Γ) (c : S γ -> S γ' -> Real) (v v' : K -> Option V) : Real :=
  Finset.univ.sum fun s : S γ => Finset.univ.sum fun s' : S γ' =>
    if cKey lev pt Bs γ s = v /\ cKey lev pt Bs γ' s' = v' /\
       bKey pt Bs γ s = bKey pt Bs γ' s' then c s s' else 0

/-- The contraction of the Gram array is the product of the two matricizations,
`H = (F^γ_{A_𝒫})'F^{γ'}_{A_𝒫}`. -/
theorem contrEntry_gram (Bs : Finset K) (γ γ' : Γ) (a₁ : S γ -> I -> Real)
    (a₂ : S γ' -> I -> Real) (v v' : K -> Option V) :
    ((Matrix.of (levMat lev pt Bs γ a₁))ᵀ * (Matrix.of (levMat lev pt Bs γ' a₂))) v v'
      = contrEntry lev pt Bs γ γ'
          (fun s s' => Finset.univ.sum fun i : I => a₁ s i * a₂ s' i) v v' := by
  classical
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  have key : ∀ p : (K -> Option V) × I,
      levMat lev pt Bs γ a₁ p v * levMat lev pt Bs γ' a₂ p v'
        = Finset.univ.sum fun s : S γ => Finset.univ.sum fun s' : S γ' =>
            (if bKey pt Bs γ s = p.1 /\ cKey lev pt Bs γ s = v then a₁ s p.2 else 0) *
            (if bKey pt Bs γ' s' = p.1 /\ cKey lev pt Bs γ' s' = v' then a₂ s' p.2
              else 0) := by
    intro p
    exact Finset.sum_mul_sum _ _ _ _
  rw [Finset.sum_congr rfl fun p _ => key p, Finset.sum_comm]
  simp only [contrEntry]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [Fintype.sum_prod_type]
  by_cases hv : cKey lev pt Bs γ s = v
  · by_cases hv' : cKey lev pt Bs γ' s' = v'
    · simp only [hv, hv', and_true, true_and]
      rw [Finset.sum_eq_single (bKey pt Bs γ s)]
      · by_cases hb : bKey pt Bs γ s = bKey pt Bs γ' s'
        · simp only [if_pos hb]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [hb]
        · simp only [if_neg hb]
          refine Finset.sum_eq_zero fun i _ => ?_
          have hb' : ¬ (bKey pt Bs γ' s' = bKey pt Bs γ s) := fun hc => hb hc.symm
          simp [hb']
      · intro a _ hne
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [if_neg (fun hc => hne hc.symm)]
        ring
      · intro hcon
        exact absurd (Finset.mem_univ _) hcon
    · simp [hv']
  · simp [hv]

theorem sum2_add {C : Type*} [Fintype C] (F G : C -> C -> Real) :
    (Finset.univ.sum fun v : C => Finset.univ.sum fun v' : C => (F v v' + G v v'))
      = (Finset.univ.sum fun v : C => Finset.univ.sum fun v' : C => F v v')
        + (Finset.univ.sum fun v : C => Finset.univ.sum fun v' : C => G v v') := by
  rw [<- Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ => Finset.sum_add_distrib

theorem sum2_const_mul {C : Type*} [Fintype C] (a : Real) (F : C -> C -> Real) :
    (Finset.univ.sum fun v : C => Finset.univ.sum fun v' : C => a * F v v')
      = a * (Finset.univ.sum fun v : C => Finset.univ.sum fun v' : C => F v v') := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => (Finset.mul_sum _ _ _).symm

/-! ### Masking rows of a matricization -/

/-- Masking rows by a `{0,1}` weight does not increase the Frobenius norm of the Gram
matrix: with `A` the masked Gram and `A'` its complement,
`∑_{v,v'}A_{vv'}A'_{vv'} = ∑_{p,q}(∑_vN_{pv}N_{qv})² ≥ 0`, so `‖A‖_F² ≤ ‖A+A'‖_F²`. -/
theorem rectFrobSq_gram_filter_le {P C : Type*} [Fintype P] [DecidableEq P] [Fintype C]
    (N : P -> C -> Real) (Msk : Finset P) :
    rectFrobSq (fun v v' : C => Msk.sum fun p => N p v * N p v')
      <= rectFrobSq (fun v v' : C => Finset.univ.sum fun p => N p v * N p v') := by
  classical
  set A : C -> C -> Real := fun v v' => Msk.sum fun p => N p v * N p v' with hA
  set A' : C -> C -> Real := fun v v' => (Finset.univ \ Msk).sum fun p => N p v * N p v' with hA'
  have hsum : ∀ v v' : C, (Finset.univ.sum fun p => N p v * N p v') = A v v' + A' v v' := by
    intro v v'
    rw [hA, hA']
    exact (Finset.sum_sdiff (Finset.subset_univ Msk)).symm.trans (by ring)
  have hcross : ∀ s t : Finset P,
      (Finset.univ.sum fun v : C => Finset.univ.sum fun v' : C =>
          (s.sum fun p => N p v * N p v') * (t.sum fun q => N q v * N q v'))
        = s.sum fun p => t.sum fun q => (Finset.univ.sum fun v : C => N p v * N q v) ^ 2 := by
    intro s t
    have hpt : ∀ (p q : P),
        (Finset.univ.sum fun v : C => Finset.univ.sum fun v' : C =>
            (N p v * N p v') * (N q v * N q v'))
          = (Finset.univ.sum fun v : C => N p v * N q v) ^ 2 := by
      intro p q
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun v' _ => by ring
    calc (Finset.univ.sum fun v : C => Finset.univ.sum fun v' : C =>
            (s.sum fun p => N p v * N p v') * (t.sum fun q => N q v * N q v'))
        = Finset.univ.sum fun v : C => Finset.univ.sum fun v' : C =>
            s.sum fun p => t.sum fun q => (N p v * N p v') * (N q v * N q v') := by
          refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun v' _ => ?_
          exact Finset.sum_mul_sum s t (fun p => N p v * N p v') (fun q => N q v * N q v')
      _ = Finset.univ.sum fun v : C => s.sum fun p => Finset.univ.sum fun v' : C =>
            t.sum fun q => (N p v * N p v') * (N q v * N q v') :=
          Finset.sum_congr rfl fun v _ => Finset.sum_comm
      _ = s.sum fun p => Finset.univ.sum fun v : C => Finset.univ.sum fun v' : C =>
            t.sum fun q => (N p v * N p v') * (N q v * N q v') := Finset.sum_comm
      _ = s.sum fun p => Finset.univ.sum fun v : C => t.sum fun q =>
            Finset.univ.sum fun v' : C => (N p v * N p v') * (N q v * N q v') :=
          Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun v _ => Finset.sum_comm
      _ = s.sum fun p => t.sum fun q => Finset.univ.sum fun v : C => Finset.univ.sum fun v' : C =>
            (N p v * N p v') * (N q v * N q v') :=
          Finset.sum_congr rfl fun p _ => Finset.sum_comm
      _ = s.sum fun p => t.sum fun q => (Finset.univ.sum fun v : C => N p v * N q v) ^ 2 :=
          Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => hpt p q
  have hnn : (0:Real) <= Finset.univ.sum fun v : C => Finset.univ.sum fun v' : C =>
      A v v' * A' v v' := by
    rw [hA, hA', hcross]
    exact Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => sq_nonneg _
  have hAA : (0:Real) <= Finset.univ.sum fun v : C => Finset.univ.sum fun v' : C =>
      A' v v' * A' v v' := by
    refine Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun v' _ => ?_
    exact mul_self_nonneg _
  have hsplit : ∀ F G : C -> C -> Real,
      (Finset.univ.sum fun v : C => Finset.univ.sum fun v' : C => (F v v' + G v v'))
        = (Finset.univ.sum fun v : C => Finset.univ.sum fun v' : C => F v v')
          + (Finset.univ.sum fun v : C => Finset.univ.sum fun v' : C => G v v') := by
    intro F G
    rw [<- Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => Finset.sum_add_distrib
  have hdouble : ∀ F : C -> C -> Real,
      2 * (Finset.univ.sum fun v : C => Finset.univ.sum fun v' : C => F v v')
        = Finset.univ.sum fun v : C => Finset.univ.sum fun v' : C => 2 * F v v' := by
    intro F
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => Finset.mul_sum _ _ _
  simp only [rectFrobSq]
  have hexp : (Finset.univ.sum fun v : C => Finset.univ.sum fun v' : C =>
        (Finset.univ.sum fun p => N p v * N p v') ^ 2)
      = Finset.univ.sum fun v : C => Finset.univ.sum fun v' : C =>
          ((A v v') ^ 2 + (2 * (A v v' * A' v v') + A' v v' * A' v v')) := by
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun v' _ => ?_
    rw [hsum v v']
    ring
  rw [hexp, hsplit (fun v v' => (A v v') ^ 2)
      (fun v v' => 2 * (A v v' * A' v v') + A' v v' * A' v v'),
    hsplit (fun v v' => 2 * (A v v' * A' v v')) (fun v v' => A' v v' * A' v v'),
    <- hdouble (fun v v' => A v v' * A' v v')]
  linarith

/-! ### The trace bound for the Class-2 contraction -/

omit [Fintype V] [Fintype I] in
/-- A weight that depends on the sub-tuple only through its two keys comes out of the
matricization as a weight on the row and the column. -/
theorem levMat_weight (Bs : Finset K) (g : Γ) (a : S g -> I -> Real)
    (w : (K -> Option V) -> (K -> Option V) -> Real) (p : (K -> Option V) × I)
    (v : K -> Option V) :
    levMat lev pt Bs g
        (fun x i => w (bKey pt Bs g x) (cKey lev pt Bs g x) * a x i) p v
      = w p.1 v * levMat lev pt Bs g a p v := by
  classical
  simp only [levMat]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hc : bKey pt Bs g x = p.1 /\ cKey lev pt Bs g x = v
  · rw [if_pos hc, if_pos hc, hc.1, hc.2]
  · rw [if_neg hc, if_neg hc, mul_zero]

/-- `‖H‖_F² ≤ ‖V^{(γ)}⊠_{A_𝒫}V^{(γ)}‖_F‖V^{(γ')}⊠_{A_𝒫}V^{(γ')}‖_F` at
`A_𝒫 = Bs ∪ {k^⋆}`, with `{0,1}` masks on the row and column keys. -/
theorem rectFrobSq_contrEntry_masked_le (Bs : Finset K) (γ γ' : Γ)
    (mrow mcol : (K -> Option V) -> Real)
    (hmrow : ∀ r, mrow r = 0 \/ mrow r = 1) (hmcol : ∀ v, mcol v = 0 \/ mcol v = 1) :
    rectFrobSq (contrEntry lev pt Bs γ γ'
        (fun s s' => mrow (bKey pt Bs γ s) * mcol (cKey lev pt Bs γ s) *
          gramEntry arr γ γ' s s'))
      <= rectFrobNorm (Matrix.of (levMat lev pt Bs γ (arr γ)) *
            (Matrix.of (levMat lev pt Bs γ (arr γ)))ᵀ) *
        rectFrobNorm (Matrix.of (levMat lev pt Bs γ' (arr γ')) *
            (Matrix.of (levMat lev pt Bs γ' (arr γ')))ᵀ) := by
  classical
  set F := levMat lev pt Bs γ (arr γ) with hF
  set G := levMat lev pt Bs γ' (arr γ') with hG
  set Fm := levMat lev pt Bs γ
    (fun x i => mrow (bKey pt Bs γ x) * mcol (cKey lev pt Bs γ x) * arr γ x i) with hFm
  have hFmw : ∀ (p : (K -> Option V) × I) (v : K -> Option V),
      Fm p v = mrow p.1 * mcol v * F p v := by
    intro p v
    rw [hFm, hF]
    exact levMat_weight (lev := lev) (pt := pt) Bs γ (arr γ)
      (fun r v => mrow r * mcol v) p v
  have hid : contrEntry lev pt Bs γ γ'
      (fun s s' => mrow (bKey pt Bs γ s) * mcol (cKey lev pt Bs γ s) * gramEntry arr γ γ' s s')
      = fun v v' => ((Matrix.of Fm)ᵀ * (Matrix.of G)) v v' := by
    funext v v'
    rw [contrEntry_gram]
    refine congrArg (fun c => contrEntry lev pt Bs γ γ' c v v') ?_
    funext s s'
    rw [gramEntry, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hid]
  refine le_trans (rectFrobSq_transpose_mul_le (Matrix.of Fm) (Matrix.of G)) ?_
  refine mul_le_mul_of_nonneg_right ?_ (rectFrobNorm_nonneg _)
  -- the row mask is what the Gram-mask lemma absorbs; the column mask is entrywise
  have hgram : ∀ v v' : K -> Option V,
      ((Matrix.of Fm)ᵀ * (Matrix.of Fm)) v v'
        = mcol v * mcol v' *
          (Finset.univ.filter (fun p : (K -> Option V) × I => mrow p.1 = 1)).sum
            (fun p => F p v * F p v') := by
    intro v v'
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hFmw p v, hFmw p v']
    rcases hmrow p.1 with h0 | h1
    · rw [h0]
      norm_num
    · rw [h1, if_pos (rfl : (1:Real) = 1)]
      ring
  have hstep : rectFrobSq ((Matrix.of Fm)ᵀ * (Matrix.of Fm))
      <= rectFrobSq ((Matrix.of F)ᵀ * (Matrix.of F)) := by
    refine le_trans ?_ (rectFrobSq_gram_filter_le (C := K -> Option V) F
      (Finset.univ.filter (fun p : (K -> Option V) × I => mrow p.1 = 1)) |>.trans (le_of_eq ?_))
    · simp only [rectFrobSq]
      refine Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun v' _ => ?_
      rw [hgram v v']
      have hb : |mcol v * mcol v'| <= 1 := by
        rcases hmcol v with h | h <;> rcases hmcol v' with h' | h' <;> simp [h, h']
      have := abs_nonneg ((Finset.univ.filter
        (fun p : (K -> Option V) × I => mrow p.1 = 1)).sum (fun p => F p v * F p v'))
      calc (mcol v * mcol v' * (Finset.univ.filter
              (fun p : (K -> Option V) × I => mrow p.1 = 1)).sum (fun p => F p v * F p v')) ^ 2
          = (mcol v * mcol v') ^ 2 * ((Finset.univ.filter
              (fun p : (K -> Option V) × I => mrow p.1 = 1)).sum
                (fun p => F p v * F p v')) ^ 2 := by ring
        _ <= 1 * ((Finset.univ.filter
              (fun p : (K -> Option V) × I => mrow p.1 = 1)).sum
                (fun p => F p v * F p v')) ^ 2 := by
              refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
              rw [<- sq_abs]
              nlinarith [abs_nonneg (mcol v * mcol v')]
        _ = ((Finset.univ.filter
              (fun p : (K -> Option V) × I => mrow p.1 = 1)).sum
                (fun p => F p v * F p v')) ^ 2 := by ring
    · simp only [rectFrobSq]
      refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun v' _ => ?_
      congr 1
  rw [rectFrobNorm_mul_transpose_comm (Matrix.of Fm), rectFrobNorm_mul_transpose_comm
    (Matrix.of F), rectFrobNorm, rectFrobNorm]
  exact Real.sqrt_le_sqrt hstep

/-! ### The matched pairs inside a Class-2 configuration -/

/-- The multi-indices of `γ` and `γ'` agree at every site the key records. -/
def keyIdxOK (rIdx : Γ -> V -> R) (γ γ' : Γ) (c : K -> Option V) : Prop :=
  ∀ (k : K) (w : V), c k = some w -> rIdx γ w = rIdx γ' w

open Classical in
/-- The `{0,1}` weight that `keyIdxOK` carries. -/
noncomputable def keyMask (rIdx : Γ -> V -> R) (γ γ' : Γ) (c : K -> Option V) : Real :=
  if keyIdxOK rIdx γ γ' c then 1 else 0

omit [Fintype V] [DecidableEq V] [DecidableEq R] [(γ : Γ) -> Fintype (S γ)] [Fintype I] [Fintype K] [DecidableEq K] in
theorem keyMask_one {rIdx : Γ -> V -> R} {γ γ' : Γ} {c : K -> Option V}
    (h : keyIdxOK rIdx γ γ' c) : keyMask rIdx γ γ' c = 1 := by
  classical
  unfold keyMask
  rw [if_pos h]

omit [Fintype V] [DecidableEq V] [DecidableEq R] [(γ : Γ) -> Fintype (S γ)] [Fintype I] [Fintype K] [DecidableEq K] in
theorem keyMask_zero {rIdx : Γ -> V -> R} {γ γ' : Γ} {c : K -> Option V}
    (h : ¬ keyIdxOK rIdx γ γ' c) : keyMask rIdx γ γ' c = 0 := by
  classical
  unfold keyMask
  rw [if_neg h]

omit [Fintype V] [DecidableEq V] [DecidableEq R] [(γ : Γ) -> Fintype (S γ)] [Fintype I] [Fintype K] [DecidableEq K] in
theorem keyMask_eq (rIdx : Γ -> V -> R) (γ γ' : Γ) (c : K -> Option V) :
    keyMask rIdx γ γ' c = 0 \/ keyMask rIdx γ γ' c = 1 := by
  classical
  unfold keyMask
  split_ifs <;> simp

omit [Fintype V] [DecidableEq V] [DecidableEq R] [(γ : Γ) -> Fintype (S γ)] [Fintype I] [Fintype K] in
theorem keyIdxOK_bKey_iff {Bs : Finset K} {γ γ' : Γ} (s : S γ) :
    keyIdxOK rIdx γ γ' (bKey pt Bs γ s)
      <-> ∀ k ∈ Bs, rIdx γ (pt γ s k) = rIdx γ' (pt γ s k) := by
  constructor
  · intro h k hk
    exact h k (pt γ s k) (bKey_apply_of_mem s hk)
  · intro h k w hw
    by_cases hk : k ∈ Bs
    · rw [bKey_apply_of_mem s hk] at hw
      cases Option.some.inj hw
      exact h k hk
    · rw [bKey, if_neg hk] at hw
      exact absurd hw (by simp)

omit [Fintype V] [DecidableEq V] [DecidableEq R] [(γ : Γ) -> Fintype (S γ)] [Fintype I] [Fintype K] in
theorem keyIdxOK_cKey_iff {Bs : Finset K} {γ γ' : Γ} (s : S γ) :
    keyIdxOK rIdx γ γ' (cKey lev pt Bs γ s)
      <-> ∀ k ∈ lev γ \ Bs, rIdx γ (pt γ s k) = rIdx γ' (pt γ s k) := by
  constructor
  · intro h k hk
    rw [Finset.mem_sdiff] at hk
    exact h k (pt γ s k) (cKey_apply_of_mem (lev := lev) s hk.1 hk.2)
  · intro h k w hw
    by_cases hk : k ∈ lev γ \ Bs
    · rw [cKey, if_pos hk] at hw
      cases Option.some.inj hw
      exact h k hk
    · rw [cKey, if_neg hk] at hw
      exact absurd hw (by simp)

omit [Fintype V] [(γ : Γ) -> Fintype (S γ)] [Fintype I] [Fintype K] in
/-- Within one configuration, the matched pairs are cut out by a row mask, a column mask and
the diagonal `v = v'`. -/
theorem isMatched_iff_keys (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' -> k = k')
    {Bs : Finset K} {γ γ' : Γ} (hBs : Bs ⊆ lev γ) (hBs' : Bs ⊆ lev γ') {s : S γ} {s' : S γ'}
    (hb : bKey pt Bs γ s = bKey pt Bs γ' s') :
    IsMatched sites rIdx γ γ' s s'
      <-> (cKey lev pt Bs γ s = cKey lev pt Bs γ' s'
            /\ keyIdxOK rIdx γ γ' (bKey pt Bs γ s) /\ keyIdxOK rIdx γ γ' (cKey lev pt Bs γ s)) := by
  classical
  have hbpt : ∀ k ∈ Bs, pt γ s k = pt γ' s' k := by
    intro k hk
    have := congrFun hb k
    rw [bKey_apply_of_mem s hk, bKey_apply_of_mem s' hk] at this
    exact Option.some.inj this
  constructor
  · rintro ⟨hst, hr⟩
    have hlev : lev γ = lev γ' /\ ∀ k ∈ lev γ, pt γ s k = pt γ' s' k := by
      rw [hsite γ s, hsite γ' s'] at hst
      have hfwd : ∀ k ∈ lev γ, k ∈ lev γ' /\ pt γ' s' k = pt γ s k := by
        intro k hk
        have hmem : pt γ s k ∈ (lev γ').image (pt γ' s') := by
          rw [<- hst]; exact Finset.mem_image_of_mem _ hk
        obtain ⟨k', hk', heq⟩ := Finset.mem_image.1 hmem
        cases hptc γ' γ s' s k' k heq
        exact ⟨hk', heq⟩
      have hbwd : ∀ k ∈ lev γ', k ∈ lev γ := by
        intro k hk
        have hmem : pt γ' s' k ∈ (lev γ).image (pt γ s) := by
          rw [hst]; exact Finset.mem_image_of_mem _ hk
        obtain ⟨k', hk', heq⟩ := Finset.mem_image.1 hmem
        cases hptc γ γ' s s' k' k heq
        exact hk'
      refine ⟨Finset.ext fun k => ⟨fun hk => (hfwd k hk).1, fun hk => hbwd k hk⟩, ?_⟩
      intro k hk
      exact ((hfwd k hk).2).symm
    have hridx : ∀ k ∈ lev γ, rIdx γ (pt γ s k) = rIdx γ' (pt γ s k) := by
      intro k hk
      exact hr _ (by rw [hsite γ s]; exact Finset.mem_image_of_mem _ hk)
    refine ⟨?_, ?_, ?_⟩
    · funext k
      by_cases hk : k ∈ lev γ \ Bs
      · rw [Finset.mem_sdiff] at hk
        rw [cKey_apply_of_mem (lev := lev) s hk.1 hk.2,
          cKey_apply_of_mem (lev := lev) s' (hlev.1 ▸ hk.1) hk.2, hlev.2 k hk.1]
      · rw [cKey_apply_of_notMem (lev := lev) s hk, cKey_apply_of_notMem (lev := lev) s' ?_]
        rw [Finset.mem_sdiff] at hk ⊢
        rw [<- hlev.1]
        exact hk
    · exact (keyIdxOK_bKey_iff (rIdx := rIdx) s).2
        (fun k hk => hridx k (hBs hk))
    · exact (keyIdxOK_cKey_iff (rIdx := rIdx) s).2
        (fun k hk => hridx k (Finset.mem_sdiff.1 hk).1)
  · rintro ⟨hc, hbok, hcok⟩
    have hlevEq : lev γ \ Bs = lev γ' \ Bs := by
      ext k
      constructor
      · intro hk
        by_contra hk'
        have h1 := congrFun hc k
        rw [cKey, if_pos hk, cKey, if_neg hk'] at h1
        exact absurd h1 (by simp)
      · intro hk'
        by_contra hk
        have h1 := congrFun hc k
        rw [cKey, if_neg hk, cKey, if_pos hk'] at h1
        exact absurd h1 (by simp)
    have hlev : lev γ = lev γ' := by
      ext k
      by_cases hk : k ∈ Bs
      · exact ⟨fun _ => hBs' hk, fun _ => hBs hk⟩
      · constructor
        · intro hkl
          have : k ∈ lev γ \ Bs := Finset.mem_sdiff.2 ⟨hkl, hk⟩
          rw [hlevEq] at this
          exact (Finset.mem_sdiff.1 this).1
        · intro hkl
          have : k ∈ lev γ' \ Bs := Finset.mem_sdiff.2 ⟨hkl, hk⟩
          rw [<- hlevEq] at this
          exact (Finset.mem_sdiff.1 this).1
    have hptEq : ∀ k ∈ lev γ, pt γ s k = pt γ' s' k := by
      intro k hk
      by_cases hkB : k ∈ Bs
      · exact hbpt k hkB
      · have hks : k ∈ lev γ \ Bs := Finset.mem_sdiff.2 ⟨hk, hkB⟩
        have h1 := congrFun hc k
        rw [cKey_apply_of_mem (lev := lev) s hk hkB,
          cKey_apply_of_mem (lev := lev) s' (hlev ▸ hk) hkB] at h1
        exact Option.some.inj h1
    constructor
    · rw [hsite γ s, hsite γ' s', <- hlev]
      exact Finset.image_congr fun k hk => hptEq k (Finset.mem_coe.1 hk)
    · intro w hw
      rw [hsite γ s, Finset.mem_image] at hw
      obtain ⟨k, hk, rfl⟩ := hw
      by_cases hkB : k ∈ Bs
      · exact (keyIdxOK_bKey_iff (rIdx := rIdx) s).1 hbok k hkB
      · exact (keyIdxOK_cKey_iff (rIdx := rIdx) s).1 hcok k (Finset.mem_sdiff.2 ⟨hk, hkB⟩)

/-! ### The contraction of the unmatched coefficient array -/

omit [Fintype V] [Fintype I] in
theorem contrEntry_sub (Bs : Finset K) (γ γ' : Γ) (c₁ c₂ : S γ -> S γ' -> Real)
    (v v' : K -> Option V) :
    contrEntry lev pt Bs γ γ' (fun s s' => c₁ s s' - c₂ s s') v v'
      = contrEntry lev pt Bs γ γ' c₁ v v' - contrEntry lev pt Bs γ γ' c₂ v v' := by
  classical
  simp only [contrEntry]
  rw [<- Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [<- Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s' _ => ?_
  split_ifs <;> ring

/-- The contraction of the unmatched coefficient array obeys the trace bound up to a factor
of four: the matched part is itself a masked contraction, and `(a-b)² ≤ 2a²+2b²`. -/
theorem rectFrobSq_contrEntry_unm_le
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' -> k = k')
    {Bs : Finset K} {γ γ' : Γ} (hBs : Bs ⊆ lev γ) (hBs' : Bs ⊆ lev γ') :
    rectFrobSq (contrEntry lev pt Bs γ γ'
        (fun s s' => keyMask rIdx γ γ' (bKey pt Bs γ s) * unmCoef sites rIdx arr γ γ' s s'))
      <= 4 * (rectFrobNorm (Matrix.of (levMat lev pt Bs γ (arr γ)) *
              (Matrix.of (levMat lev pt Bs γ (arr γ)))ᵀ) *
            rectFrobNorm (Matrix.of (levMat lev pt Bs γ' (arr γ')) *
              (Matrix.of (levMat lev pt Bs γ' (arr γ')))ᵀ)) := by
  classical
  set mb : (K -> Option V) -> Real := keyMask rIdx γ γ' with hmbdef
  set cG : S γ -> S γ' -> Real :=
    fun s s' => mb (bKey pt Bs γ s) * (1:Real) * gramEntry arr γ γ' s s' with hcG
  set cM : S γ -> S γ' -> Real :=
    fun s s' => mb (bKey pt Bs γ s) * mb (cKey lev pt Bs γ s) * gramEntry arr γ γ' s s' with hcM
  set cM' : S γ -> S γ' -> Real :=
    fun s s' => mb (bKey pt Bs γ s) *
      (if IsMatched sites rIdx γ γ' s s' then gramEntry arr γ γ' s s' else 0) with hcM'
  -- the unmatched coefficient is the Gram one minus the matched one
  have hdecomp : (fun s s' => mb (bKey pt Bs γ s) * unmCoef sites rIdx arr γ γ' s s')
      = fun s s' => cG s s' - cM' s s' := by
    funext s s'
    simp only [hcG, hcM', unmCoef]
    by_cases hm : IsMatched sites rIdx γ γ' s s'
    · simp [hm]
    · simp [hm]
  -- the matched part is a masked contraction, cut down to the diagonal `v = v'`
  have hMdiag : ∀ v v' : K -> Option V,
      (contrEntry lev pt Bs γ γ' cM' v v') ^ 2 <= (contrEntry lev pt Bs γ γ' cM v v') ^ 2 := by
    intro v v'
    by_cases hvv : v = v'
    · subst hvv
      have : contrEntry lev pt Bs γ γ' cM' v v = contrEntry lev pt Bs γ γ' cM v v := by
        simp only [contrEntry]
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
        by_cases hc : cKey lev pt Bs γ s = v ∧ cKey lev pt Bs γ' s' = v ∧
            bKey pt Bs γ s = bKey pt Bs γ' s'
        · rw [if_pos hc, if_pos hc]
          simp only [hcM', hcM, hmbdef]
          have hiff := isMatched_iff_keys (sites := sites) (rIdx := rIdx) hsite hptc hBs hBs' hc.2.2
          have hck : cKey lev pt Bs γ s = cKey lev pt Bs γ' s' := by rw [hc.1, hc.2.1]
          by_cases hb : keyIdxOK rIdx γ γ' (bKey pt Bs γ s)
          · by_cases hcc : keyIdxOK rIdx γ γ' (cKey lev pt Bs γ s)
            · rw [if_pos (hiff.2 ⟨hck, hb, hcc⟩), keyMask_one hb, keyMask_one hcc]
              ring
            · rw [if_neg (fun hm => hcc (hiff.1 hm).2.2), keyMask_zero hcc]
              ring
          · rw [if_neg (fun hm => hb (hiff.1 hm).2.1), keyMask_zero hb]
            ring
        · rw [if_neg hc, if_neg hc]
      rw [this]
    · have hz : contrEntry lev pt Bs γ γ' cM' v v' = 0 := by
        simp only [contrEntry]
        refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun s' _ => ?_
        by_cases hc : cKey lev pt Bs γ s = v ∧ cKey lev pt Bs γ' s' = v' ∧
            bKey pt Bs γ s = bKey pt Bs γ' s'
        · rw [if_pos hc]
          simp only [hcM']
          have hiff := isMatched_iff_keys (sites := sites) (rIdx := rIdx) hsite hptc hBs hBs' hc.2.2
          rw [if_neg (fun hm => hvv (by rw [<- hc.1, (hiff.1 hm).1, hc.2.1]))]
          ring
        · rw [if_neg hc]
      rw [hz]
      simpa using sq_nonneg (contrEntry lev pt Bs γ γ' cM v v')
  -- the trace bound for both masked contractions
  have hGb := rectFrobSq_contrEntry_masked_le (arr := arr) (lev := lev) (pt := pt) Bs γ γ'
    mb (fun _ => 1) (fun r => keyMask_eq rIdx γ γ' r) (fun _ => Or.inr rfl)
  have hMb := rectFrobSq_contrEntry_masked_le (arr := arr) (lev := lev) (pt := pt) Bs γ γ'
    mb mb (fun r => keyMask_eq rIdx γ γ' r) (fun r => keyMask_eq rIdx γ γ' r)
  have hMsq : rectFrobSq (contrEntry lev pt Bs γ γ' cM')
      <= rectFrobSq (contrEntry lev pt Bs γ γ' cM) := by
    simp only [rectFrobSq]
    exact Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun v' _ => hMdiag v v'
  rw [hdecomp]
  have hterm : ∀ v v' : K -> Option V,
      (contrEntry lev pt Bs γ γ' (fun s s' => cG s s' - cM' s s') v v') ^ 2
        <= 2 * (contrEntry lev pt Bs γ γ' cG v v') ^ 2
          + 2 * (contrEntry lev pt Bs γ γ' cM' v v') ^ 2 := by
    intro v v'
    rw [contrEntry_sub]
    nlinarith [sq_nonneg (contrEntry lev pt Bs γ γ' cG v v'
      + contrEntry lev pt Bs γ γ' cM' v v')]
  have hsplit : rectFrobSq (contrEntry lev pt Bs γ γ' (fun s s' => cG s s' - cM' s s'))
      <= 2 * rectFrobSq (contrEntry lev pt Bs γ γ' cG)
        + 2 * rectFrobSq (contrEntry lev pt Bs γ γ' cM') := by
    have h1 : rectFrobSq (contrEntry lev pt Bs γ γ' (fun s s' => cG s s' - cM' s s'))
        <= Finset.univ.sum fun v : K -> Option V => Finset.univ.sum fun v' : K -> Option V =>
            (2 * (contrEntry lev pt Bs γ γ' cG v v') ^ 2
              + 2 * (contrEntry lev pt Bs γ γ' cM' v v') ^ 2) := by
      simp only [rectFrobSq]
      exact Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun v' _ => hterm v v'
    have h2 : (Finset.univ.sum fun v : K -> Option V => Finset.univ.sum fun v' : K -> Option V =>
          (2 * (contrEntry lev pt Bs γ γ' cG v v') ^ 2
            + 2 * (contrEntry lev pt Bs γ γ' cM' v v') ^ 2))
        = 2 * rectFrobSq (contrEntry lev pt Bs γ γ' cG)
          + 2 * rectFrobSq (contrEntry lev pt Bs γ γ' cM') := by
      simp only [rectFrobSq]
      rw [sum2_add (fun v v' => 2 * (contrEntry lev pt Bs γ γ' cG v v') ^ 2)
          (fun v v' => 2 * (contrEntry lev pt Bs γ γ' cM' v v') ^ 2),
        sum2_const_mul 2 (fun v v' => (contrEntry lev pt Bs γ γ' cG v v') ^ 2),
        sum2_const_mul 2 (fun v v' => (contrEntry lev pt Bs γ γ' cM' v v') ^ 2)]
    linarith
  have hnn1 : (0:Real) <= rectFrobNorm (Matrix.of (levMat lev pt Bs γ (arr γ)) *
      (Matrix.of (levMat lev pt Bs γ (arr γ)))ᵀ) := rectFrobNorm_nonneg _
  have hnn2 : (0:Real) <= rectFrobNorm (Matrix.of (levMat lev pt Bs γ' (arr γ')) *
      (Matrix.of (levMat lev pt Bs γ' (arr γ')))ᵀ) := rectFrobNorm_nonneg _
  linarith [hsplit, hMsq, hGb, hMb]

/-! ### Cauchy--Schwarz for Class 2 -/

open Classical in
omit [Fintype I] in
/-- The quadruple sum over one configuration, when the column keys of `(u,u')` are a fixed
function of those of `(s,s')`, is `∑_{(v,v')}H_{v,v'}H_{τ(v,v')}` weighted by the coefficient. -/
theorem sum_quad_eq_contr (Bs : Finset K) (γ γ' : Γ) (c : S γ -> S γ' -> Real)
    (σ : (K -> Option V) -> (K -> Option V) -> (K -> Option V) × (K -> Option V))
    (Θ : (K -> Option V) -> (K -> Option V) -> Real) :
    (Finset.univ.sum fun q : (S γ × S γ') × (S γ × S γ') =>
        (if bKey pt Bs γ q.1.1 = bKey pt Bs γ' q.1.2 ∧
            bKey pt Bs γ q.2.1 = bKey pt Bs γ' q.2.2 ∧
            (cKey lev pt Bs γ q.2.1, cKey lev pt Bs γ' q.2.2)
              = σ (cKey lev pt Bs γ q.1.1) (cKey lev pt Bs γ' q.1.2)
          then Θ (cKey lev pt Bs γ q.1.1) (cKey lev pt Bs γ' q.1.2) *
            (c q.1.1 q.1.2 * c q.2.1 q.2.2) else 0))
      = Finset.univ.sum fun x : K -> Option V => Finset.univ.sum fun y : K -> Option V =>
          Θ x y * (contrEntry lev pt Bs γ γ' c x y *
            contrEntry lev pt Bs γ γ' c (σ x y).1 (σ x y).2) := by
  classical
  have hHpair : ∀ x y : K -> Option V, contrEntry lev pt Bs γ γ' c x y
      = Finset.univ.sum fun p : S γ × S γ' =>
          (if cKey lev pt Bs γ p.1 = x ∧ cKey lev pt Bs γ' p.2 = y ∧
              bKey pt Bs γ p.1 = bKey pt Bs γ' p.2 then c p.1 p.2 else 0) := by
    intro x y
    rw [contrEntry, Fintype.sum_prod_type]
  have hprod : ∀ x y : K -> Option V,
      Θ x y * (contrEntry lev pt Bs γ γ' c x y *
          contrEntry lev pt Bs γ γ' c (σ x y).1 (σ x y).2)
        = Finset.univ.sum fun q : (S γ × S γ') × (S γ × S γ') =>
            (if (cKey lev pt Bs γ q.1.1 = x ∧ cKey lev pt Bs γ' q.1.2 = y ∧
                  bKey pt Bs γ q.1.1 = bKey pt Bs γ' q.1.2) ∧
                (cKey lev pt Bs γ q.2.1 = (σ x y).1 ∧ cKey lev pt Bs γ' q.2.2 = (σ x y).2 ∧
                  bKey pt Bs γ q.2.1 = bKey pt Bs γ' q.2.2)
              then Θ x y * (c q.1.1 q.1.2 * c q.2.1 q.2.2) else 0) := by
    intro x y
    have hfac : contrEntry lev pt Bs γ γ' c x y *
          contrEntry lev pt Bs γ γ' c (σ x y).1 (σ x y).2
        = Finset.univ.sum fun p1 : S γ × S γ' => Finset.univ.sum fun p2 : S γ × S γ' =>
            (if cKey lev pt Bs γ p1.1 = x ∧ cKey lev pt Bs γ' p1.2 = y ∧
                bKey pt Bs γ p1.1 = bKey pt Bs γ' p1.2 then c p1.1 p1.2 else 0) *
            (if cKey lev pt Bs γ p2.1 = (σ x y).1 ∧ cKey lev pt Bs γ' p2.2 = (σ x y).2 ∧
                bKey pt Bs γ p2.1 = bKey pt Bs γ' p2.2 then c p2.1 p2.2 else 0) := by
      rw [hHpair x y, hHpair (σ x y).1 (σ x y).2]
      exact Finset.sum_mul_sum _ _ _ _
    rw [hfac, Finset.mul_sum]
    conv_rhs => rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p1 _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p2 _ => ?_
    by_cases hC : (cKey lev pt Bs γ p1.1 = x ∧ cKey lev pt Bs γ' p1.2 = y ∧
          bKey pt Bs γ p1.1 = bKey pt Bs γ' p1.2) ∧
        (cKey lev pt Bs γ p2.1 = (σ x y).1 ∧ cKey lev pt Bs γ' p2.2 = (σ x y).2 ∧
          bKey pt Bs γ p2.1 = bKey pt Bs γ' p2.2)
    · rw [if_pos hC, if_pos hC.1, if_pos hC.2]
    · rw [if_neg hC]
      by_cases h1 : cKey lev pt Bs γ p1.1 = x ∧ cKey lev pt Bs γ' p1.2 = y ∧
          bKey pt Bs γ p1.1 = bKey pt Bs γ' p1.2
      · have h2 : ¬ (cKey lev pt Bs γ p2.1 = (σ x y).1 ∧ cKey lev pt Bs γ' p2.2 = (σ x y).2 ∧
              bKey pt Bs γ p2.1 = bKey pt Bs γ' p2.2) := fun hc => hC ⟨h1, hc⟩
        rw [if_neg h2]
        ring
      · rw [if_neg h1]
        ring
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hprod x y]
  rw [show (Finset.univ.sum fun x : K -> Option V => Finset.univ.sum fun y : K -> Option V =>
        Finset.univ.sum fun q : (S γ × S γ') × (S γ × S γ') => _)
      = (Finset.univ.sum fun x : K -> Option V =>
          Finset.univ.sum fun q : (S γ × S γ') × (S γ × S γ') =>
            Finset.univ.sum fun y : K -> Option V => _) from
    Finset.sum_congr rfl fun x _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_eq_single (cKey lev pt Bs γ q.1.1)]
  · rw [Finset.sum_eq_single (cKey lev pt Bs γ' q.1.2)]
    · by_cases hb1 : bKey pt Bs γ q.1.1 = bKey pt Bs γ' q.1.2
      · by_cases hb2 : bKey pt Bs γ q.2.1 = bKey pt Bs γ' q.2.2
        · by_cases hs : (cKey lev pt Bs γ q.2.1, cKey lev pt Bs γ' q.2.2)
              = σ (cKey lev pt Bs γ q.1.1) (cKey lev pt Bs γ' q.1.2)
          · have hA : cKey lev pt Bs γ q.2.1
                = (σ (cKey lev pt Bs γ q.1.1) (cKey lev pt Bs γ' q.1.2)).1 := congrArg Prod.fst hs
            have hB : cKey lev pt Bs γ' q.2.2
                = (σ (cKey lev pt Bs γ q.1.1) (cKey lev pt Bs γ' q.1.2)).2 := congrArg Prod.snd hs
            rw [if_pos ⟨hb1, hb2, hs⟩, if_pos ⟨⟨rfl, rfl, hb1⟩, hA, hB, hb2⟩]
          · rw [if_neg (fun hc => hs (by rw [hc.2.2])), if_neg ?_]
            rintro ⟨-, h2, h3, -⟩
            exact hs (Prod.ext h2 h3)
        · rw [if_neg (fun hc => hb2 hc.2.1), if_neg (fun hc => hb2 hc.2.2.2)]
      · rw [if_neg (fun hc => hb1 hc.1), if_neg (fun hc => hb1 hc.1.2.2)]
    · intro y _ hne
      rw [if_neg]
      rintro ⟨⟨-, h2, -⟩, -⟩
      exact hne h2.symm
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  · intro x _ hne
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [if_neg]
    rintro ⟨⟨h1, -, -⟩, -⟩
    exact hne h1.symm
  · intro hcon
    exact absurd (Finset.mem_univ _) hcon

open Classical in
omit [Fintype I] in
/-- Cauchy--Schwarz for one configuration: if `(v,v') ↦ τ(v,v')` is injective and the
coefficient is bounded by `M₀`, the sum is at most `M₀‖H‖_F²`. -/
theorem abs_sum_quad_contrEntry_le (Bs : Finset K) (γ γ' : Γ) (c : S γ -> S γ' -> Real)
    (σ : (K -> Option V) -> (K -> Option V) -> (K -> Option V) × (K -> Option V))
    (Θ : (K -> Option V) -> (K -> Option V) -> Real) {M₀ : Real} (hM : 0 <= M₀)
    (hΘ : ∀ x y, |Θ x y| <= M₀)
    (hσ : Function.Injective
      (fun p : (K -> Option V) × (K -> Option V) => σ p.1 p.2)) :
    |Finset.univ.sum fun q : (S γ × S γ') × (S γ × S γ') =>
        (if bKey pt Bs γ q.1.1 = bKey pt Bs γ' q.1.2 ∧
            bKey pt Bs γ q.2.1 = bKey pt Bs γ' q.2.2 ∧
            (cKey lev pt Bs γ q.2.1, cKey lev pt Bs γ' q.2.2)
              = σ (cKey lev pt Bs γ q.1.1) (cKey lev pt Bs γ' q.1.2)
          then Θ (cKey lev pt Bs γ q.1.1) (cKey lev pt Bs γ' q.1.2) *
            (c q.1.1 q.1.2 * c q.2.1 q.2.2) else 0)|
      <= M₀ * rectFrobSq (contrEntry lev pt Bs γ γ' c) := by
  classical
  set H : (K -> Option V) -> (K -> Option V) -> Real := contrEntry lev pt Bs γ γ' c with hHdef
  set sg : (K -> Option V) × (K -> Option V) -> (K -> Option V) × (K -> Option V) :=
    fun p => σ p.1 p.2 with hsg
  have hbij : Function.Bijective sg := Finite.injective_iff_bijective.mp hσ
  have hsqSum : (Finset.univ.sum fun j : (K -> Option V) × (K -> Option V) =>
        (H (sg j).1 (sg j).2) ^ 2)
      = Finset.univ.sum fun j : (K -> Option V) × (K -> Option V) => (H j.1 j.2) ^ 2 :=
    Fintype.sum_bijective sg hbij _ _ fun _ => rfl
  have hfrob : rectFrobSq H
      = Finset.univ.sum fun j : (K -> Option V) × (K -> Option V) => (H j.1 j.2) ^ 2 := by
    simp only [rectFrobSq]
    rw [Fintype.sum_prod_type]
  have hnn : (0:Real) <= Finset.univ.sum fun j : (K -> Option V) × (K -> Option V) =>
      (H j.1 j.2) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [sum_quad_eq_contr (lev := lev) (pt := pt) Bs γ γ' c σ Θ, <- hHdef,
    show (Finset.univ.sum fun x : K -> Option V => Finset.univ.sum fun y : K -> Option V =>
        Θ x y * (H x y * H (σ x y).1 (σ x y).2))
      = Finset.univ.sum (fun j : (K -> Option V) × (K -> Option V) =>
          Θ j.1 j.2 * (H j.1 j.2 * H (σ j.1 j.2).1 (σ j.1 j.2).2))
      from (Fintype.sum_prod_type (fun j : (K -> Option V) × (K -> Option V) =>
          Θ j.1 j.2 * (H j.1 j.2 * H (σ j.1 j.2).1 (σ j.1 j.2).2))).symm]
  calc |Finset.univ.sum fun j : (K -> Option V) × (K -> Option V) =>
          Θ j.1 j.2 * (H j.1 j.2 * H (σ j.1 j.2).1 (σ j.1 j.2).2)|
      <= Finset.univ.sum fun j : (K -> Option V) × (K -> Option V) =>
          |Θ j.1 j.2 * (H j.1 j.2 * H (σ j.1 j.2).1 (σ j.1 j.2).2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.univ.sum fun j : (K -> Option V) × (K -> Option V) =>
          M₀ * (|H j.1 j.2| * |H (sg j).1 (sg j).2|) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right (hΘ _ _)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = M₀ * Finset.univ.sum fun j : (K -> Option V) × (K -> Option V) =>
          |H j.1 j.2| * |H (sg j).1 (sg j).2| := by rw [Finset.mul_sum]
    _ <= M₀ * rectFrobSq H := by
        refine mul_le_mul_of_nonneg_left ?_ hM
        rw [hfrob]
        calc Finset.univ.sum (fun j : (K -> Option V) × (K -> Option V) =>
              |H j.1 j.2| * |H (sg j).1 (sg j).2|)
            <= Real.sqrt (Finset.univ.sum fun j : (K -> Option V) × (K -> Option V) =>
                  |H j.1 j.2| ^ 2) *
                Real.sqrt (Finset.univ.sum fun j : (K -> Option V) × (K -> Option V) =>
                  |H (sg j).1 (sg j).2| ^ 2) :=
              Real.sum_mul_le_sqrt_mul_sqrt _ _ _
          _ = Real.sqrt (Finset.univ.sum fun j : (K -> Option V) × (K -> Option V) =>
                  (H j.1 j.2) ^ 2) *
              Real.sqrt (Finset.univ.sum fun j : (K -> Option V) × (K -> Option V) =>
                  (H j.1 j.2) ^ 2) := by
              rw [show (Finset.univ.sum fun j : (K -> Option V) × (K -> Option V) =>
                    |H j.1 j.2| ^ 2)
                  = Finset.univ.sum fun j : (K -> Option V) × (K -> Option V) => (H j.1 j.2) ^ 2
                from Finset.sum_congr rfl fun j _ => sq_abs _,
                show (Finset.univ.sum fun j : (K -> Option V) × (K -> Option V) =>
                    |H (sg j).1 (sg j).2| ^ 2)
                  = Finset.univ.sum fun j : (K -> Option V) × (K -> Option V) => (H j.1 j.2) ^ 2
                from (Finset.sum_congr rfl fun j _ => sq_abs _).trans hsqSum]
          _ = Finset.univ.sum fun j : (K -> Option V) × (K -> Option V) => (H j.1 j.2) ^ 2 :=
              Real.mul_self_sqrt hnn

/-! ### Splitting the pattern-(A) sites off the moment -/

/-- The sites a key records. -/
def keySites (c : K -> Option V) : Finset V :=
  Finset.univ.filter (fun w => ∃ k : K, c k = some w)

omit [(γ : Γ) -> Fintype (S γ)] [Fintype I] in
theorem keySites_cKey (Bs : Finset K) (g : Γ) (x : S g) :
    keySites (cKey lev pt Bs g x) = (lev g \ Bs).image (pt g x) := by
  classical
  ext w
  simp only [keySites, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨k, hk⟩
    by_cases hkm : k ∈ lev g \ Bs
    · rw [cKey, if_pos hkm] at hk
      exact ⟨k, hkm, Option.some.inj hk⟩
    · rw [cKey, if_neg hkm] at hk
      exact absurd hk (by simp)
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, cKey_apply_of_mem (lev := lev) x (Finset.mem_sdiff.1 hk).1
      (Finset.mem_sdiff.1 hk).2⟩

/-- The four reduced slot site sets, read off four keys. -/
def keyQuadSites (x y z w : K -> Option V) (j : Fin 4) : Finset V :=
  if j = 0 then keySites x else if j = 1 then keySites y else
    if j = 2 then keySites z else keySites w

omit [(γ : Γ) -> Fintype (S γ)] [Fintype I] in
@[simp] theorem keyQuadSites_zero (x y z w : K -> Option V) :
    keyQuadSites x y z w 0 = keySites x := by simp [keyQuadSites]

omit [(γ : Γ) -> Fintype (S γ)] [Fintype I] in
@[simp] theorem keyQuadSites_one (x y z w : K -> Option V) :
    keyQuadSites x y z w 1 = keySites y := by simp [keyQuadSites]

omit [(γ : Γ) -> Fintype (S γ)] [Fintype I] in
@[simp] theorem keyQuadSites_two (x y z w : K -> Option V) :
    keyQuadSites x y z w 2 = keySites z := by simp [keyQuadSites]

omit [(γ : Γ) -> Fintype (S γ)] [Fintype I] in
@[simp] theorem keyQuadSites_three (x y z w : K -> Option V) :
    keyQuadSites x y z w 3 = keySites w := by simp [keyQuadSites]

set_option linter.unusedSectionVars false in
/-- A key records at most one site per coordinate, so it names at most `|K|` sites. -/
theorem card_keySites_le (c : K -> Option V) : (keySites c).card <= Fintype.card K := by
  classical
  have h1 : ((keySites c).image (fun w => (some w : Option V))).card = (keySites c).card :=
    Finset.card_image_of_injective _ (fun a b hab => Option.some.inj hab)
  have h2 : (keySites c).image (fun w => (some w : Option V)) ⊆ Finset.univ.image c := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    have hk : ∃ k : K, c k = some w := by simpa [keySites] using hw
    obtain ⟨k, hk⟩ := hk
    exact Finset.mem_image.2 ⟨k, Finset.mem_univ k, hk⟩
  calc (keySites c).card = ((keySites c).image (fun w => (some w : Option V))).card := h1.symm
    _ <= (Finset.univ.image c).card := Finset.card_le_card h2
    _ <= (Finset.univ : Finset K).card := Finset.card_image_le
    _ = Fintype.card K := Finset.card_univ

set_option linter.unusedSectionVars false in
/-- The key bound, transported to the four reduced slot site sets. -/
theorem card_keyQuadSites_le {M : ℕ} (hkey : ∀ c : K -> Option V, (keySites c).card <= M)
    (x y z w : K -> Option V) (j : Fin 4) : (keyQuadSites x y z w j).card <= M := by
  unfold keyQuadSites
  split_ifs
  · exact hkey x
  · exact hkey y
  · exact hkey z
  · exact hkey w

/-- The pattern-(A) sites contribute only the factors `𝔼[ψ_{r_k(γ)}ψ_{r_k(γ')}]`: the site
`s_k = s'_k` carries slots `0, 1`, the site `u_k = u'_k` carries slots `2, 3`, and the remaining
sites give the reduced four-slot moment. -/
theorem multiMoment_split (h : IsBasisSystem μ U ψ Rpos B₀)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' -> k = k')
    {Bs : Finset K} {γ γ' : Γ} (hBs : Bs ⊆ lev γ) (hBs' : Bs ⊆ lev γ')
    {s u : S γ} {s' u' : S γ'}
    (hA1 : ∀ k ∈ Bs, pt γ s k = pt γ' s' k)
    (hA2 : ∀ k ∈ Bs, pt γ u k = pt γ' u' k)
    (hA3 : ∀ k ∈ Bs, pt γ s k ≠ pt γ u k) :
    multiMoment μ U ψ (quadSites sites γ γ' s s' u u') (quadIdx rIdx γ γ')
      = (Bs.prod fun k => (if rIdx γ (pt γ s k) = rIdx γ' (pt γ s k) then (1:Real) else 0)) *
        (Bs.prod fun k => (if rIdx γ (pt γ u k) = rIdx γ' (pt γ u k) then (1:Real) else 0)) *
        multiMoment μ U ψ (keyQuadSites (cKey lev pt Bs γ s) (cKey lev pt Bs γ' s')
          (cKey lev pt Bs γ u) (cKey lev pt Bs γ' u')) (quadIdx rIdx γ γ') := by
  classical
  have hP : IsProbabilityMeasure μ := h.isProbabilityMeasure
  set Bst : Finset V := Bs.image (pt γ s) ∪ Bs.image (pt γ u) with hBstdef
  rw [multiMoment_eq_prod h, multiMoment_eq_prod h]
  -- membership in the four slot sets, coordinate by coordinate
  have hmem : ∀ (g : Γ) (x : S g) (k : K), pt g x k ∈ sites g x ↔ k ∈ lev g := by
    intro g x k
    rw [hsite g x, Finset.mem_image]
    constructor
    · rintro ⟨k', hk', heq⟩
      cases hptc g g x x k' k heq
      exact hk'
    · intro hk
      exact ⟨k, hk, rfl⟩
  have hmem' : ∀ (g g' : Γ) (x : S g) (y : S g') (k : K),
      pt g x k ∈ sites g' y ↔ (k ∈ lev g' ∧ pt g' y k = pt g x k) := by
    intro g g' x y k
    rw [hsite g' y, Finset.mem_image]
    constructor
    · rintro ⟨k', hk', heq⟩
      cases hptc g' g y x k' k heq
      exact ⟨hk', heq⟩
    · rintro ⟨hk, heq⟩
      exact ⟨k, hk, heq⟩
  -- the reduced site sets are the originals minus the pattern-(A) sites
  have hgen : ∀ (g : Γ) (x : S g), (∀ k ∈ Bs, pt g x k ∈ Bst) ->
      (lev g \ Bs).image (pt g x) = sites g x \ Bst := by
    intro g x hin
    ext w
    simp only [Finset.mem_image, Finset.mem_sdiff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨(hmem g x k).2 hk.1, ?_⟩
      rw [hBstdef, Finset.mem_union, Finset.mem_image, Finset.mem_image]
      rintro (⟨k', hk', heq⟩ | ⟨k', hk', heq⟩)
      · cases hptc γ g s x k' k heq
        exact hk.2 hk'
      · cases hptc γ g u x k' k heq
        exact hk.2 hk'
    · rintro ⟨hw, hnb⟩
      rw [hsite g x, Finset.mem_image] at hw
      obtain ⟨k, hk, rfl⟩ := hw
      exact ⟨k, ⟨hk, fun hkB => hnb (hin k hkB)⟩, rfl⟩
  have hE : ∀ j : Fin 4,
      keyQuadSites (cKey lev pt Bs γ s) (cKey lev pt Bs γ' s')
          (cKey lev pt Bs γ u) (cKey lev pt Bs γ' u') j
        = quadSites sites γ γ' s s' u u' j \ Bst := by
    have hfin : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
    intro j
    rcases hfin j with rfl | rfl | rfl | rfl
    · rw [keyQuadSites_zero, quadSites_zero, keySites_cKey]
      exact hgen γ s fun k hk => by
        rw [hBstdef, Finset.mem_union]
        exact Or.inl (Finset.mem_image_of_mem _ hk)
    · rw [keyQuadSites_one, quadSites_one, keySites_cKey]
      exact hgen γ' s' fun k hk => by
        rw [hBstdef, Finset.mem_union, <- hA1 k hk]
        exact Or.inl (Finset.mem_image_of_mem _ hk)
    · rw [keyQuadSites_two, quadSites_two, keySites_cKey]
      exact hgen γ u fun k hk => by
        rw [hBstdef, Finset.mem_union]
        exact Or.inr (Finset.mem_image_of_mem _ hk)
    · rw [keyQuadSites_three, quadSites_three, keySites_cKey]
      exact hgen γ' u' fun k hk => by
        rw [hBstdef, Finset.mem_union, <- hA2 k hk]
        exact Or.inr (Finset.mem_image_of_mem _ hk)
  -- the local factor at a site, in the two shapes it takes
  set L : V -> Real := fun v => ∫ ω, (Finset.univ.filter
      (fun j => v ∈ quadSites sites γ γ' s s' u u' j)).prod
        (fun j => ψ (quadIdx rIdx γ γ' j v) (U v ω)) ∂μ with hLdef
  set L' : V -> Real := fun v => ∫ ω, (Finset.univ.filter
      (fun j => v ∈ keyQuadSites (cKey lev pt Bs γ s) (cKey lev pt Bs γ' s')
        (cKey lev pt Bs γ u) (cKey lev pt Bs γ' u') j)).prod
        (fun j => ψ (quadIdx rIdx γ γ' j v) (U v ω)) ∂μ with hL'def
  have hout : ∀ v : V, v ∉ Bst -> L' v = L v := by
    intro v hv
    have hf : (Finset.univ.filter
        (fun j => v ∈ keyQuadSites (cKey lev pt Bs γ s) (cKey lev pt Bs γ' s')
          (cKey lev pt Bs γ u) (cKey lev pt Bs γ' u') j))
        = Finset.univ.filter (fun j => v ∈ quadSites sites γ γ' s s' u u' j) := by
      apply Finset.filter_congr
      intro j _
      rw [hE j, Finset.mem_sdiff]
      simp [hv]
    simp only [hLdef, hL'def, hf]
  have hin1 : ∀ v : V, v ∈ Bst -> L' v = 1 := by
    intro v hv
    have hempty : (Finset.univ.filter
        (fun j => v ∈ keyQuadSites (cKey lev pt Bs γ s) (cKey lev pt Bs γ' s')
          (cKey lev pt Bs γ u) (cKey lev pt Bs γ' u') j)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro j _
      rw [hE j, Finset.mem_sdiff]
      tauto
    simp [hL'def, hempty]
  -- the pattern-(A) sites of `s` carry slots 0 and 1 only
  have hLs : ∀ k ∈ Bs, L (pt γ s k)
      = (if rIdx γ (pt γ s k) = rIdx γ' (pt γ s k) then (1:Real) else 0) := by
    intro k hk
    have h0 : pt γ s k ∈ sites γ s := (hmem γ s k).2 (hBs hk)
    have h1 : pt γ s k ∈ sites γ' s' :=
      (hmem' γ γ' s s' k).2 ⟨hBs' hk, (hA1 k hk).symm⟩
    have h2 : pt γ s k ∉ sites γ u := fun hcon =>
      hA3 k hk ((hmem' γ γ s u k).1 hcon).2.symm
    have h3 : pt γ s k ∉ sites γ' u' := fun hcon =>
      hA3 k hk ((hA2 k hk).trans ((hmem' γ γ' s u' k).1 hcon).2).symm
    have hf : (Finset.univ.filter
        (fun j => pt γ s k ∈ quadSites sites γ γ' s s' u u' j)) = {0, 1} := by
      have hfin : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
      ext j
      rcases hfin j with rfl | rfl | rfl | rfl <;>
        simp [Finset.mem_filter, h0, h1, h2, h3]
    simp only [hLdef, hf, Finset.prod_pair (show (0:Fin 4) ≠ 1 by decide), quadIdx_zero,
      quadIdx_one]
    exact h.integral_mul _ _ _
  have hLu : ∀ k ∈ Bs, L (pt γ u k)
      = (if rIdx γ (pt γ u k) = rIdx γ' (pt γ u k) then (1:Real) else 0) := by
    intro k hk
    have h0 : pt γ u k ∉ sites γ s := fun hcon =>
      hA3 k hk ((hmem' γ γ u s k).1 hcon).2
    have h1 : pt γ u k ∉ sites γ' s' := fun hcon =>
      hA3 k hk ((hA1 k hk).trans ((hmem' γ γ' u s' k).1 hcon).2)
    have h2 : pt γ u k ∈ sites γ u := (hmem γ u k).2 (hBs hk)
    have h3 : pt γ u k ∈ sites γ' u' :=
      (hmem' γ γ' u u' k).2 ⟨hBs' hk, (hA2 k hk).symm⟩
    have hf : (Finset.univ.filter
        (fun j => pt γ u k ∈ quadSites sites γ γ' s s' u u' j)) = {2, 3} := by
      have hfin : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
      ext j
      rcases hfin j with rfl | rfl | rfl | rfl <;>
        simp [Finset.mem_filter, h0, h1, h2, h3]
    simp only [hLdef, hf, Finset.prod_pair (show (2:Fin 4) ≠ 3 by decide), quadIdx_two,
      quadIdx_three]
    exact h.integral_mul _ _ _
  -- the two pattern-(A) site families are disjoint, and each is injective on `Bs`
  have hinjs : ∀ k ∈ (Bs : Finset K), ∀ k' ∈ (Bs : Finset K),
      pt γ s k = pt γ s k' -> k = k' := fun k _ k' _ hEq => hptc γ γ s s k k' hEq
  have hinju : ∀ k ∈ (Bs : Finset K), ∀ k' ∈ (Bs : Finset K),
      pt γ u k = pt γ u k' -> k = k' := fun k _ k' _ hEq => hptc γ γ u u k k' hEq
  have hdisj : Disjoint (Bs.image (pt γ s)) (Bs.image (pt γ u)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨k', hk', heq⟩ := Finset.mem_image.1 hb
    cases hptc γ γ u s k' k heq
    exact hA3 k hk heq.symm
  -- assemble
  have hprodBst : Bst.prod L
      = (Bs.prod fun k => (if rIdx γ (pt γ s k) = rIdx γ' (pt γ s k) then (1:Real) else 0)) *
        (Bs.prod fun k => (if rIdx γ (pt γ u k) = rIdx γ' (pt γ u k) then (1:Real) else 0)) := by
    rw [hBstdef, Finset.prod_union hdisj, Finset.prod_image hinjs, Finset.prod_image hinju]
    exact congrArg₂ (· * ·) (Finset.prod_congr rfl hLs) (Finset.prod_congr rfl hLu)
  have hsplitL : (Finset.univ.prod L) = ((Finset.univ \ Bst).prod L) * Bst.prod L :=
    (Finset.prod_sdiff (Finset.subset_univ Bst)).symm
  have hsplitL' : (Finset.univ.prod L') = ((Finset.univ \ Bst).prod L') * Bst.prod L' :=
    (Finset.prod_sdiff (Finset.subset_univ Bst)).symm
  have hL'out : ((Finset.univ \ Bst).prod L') = ((Finset.univ \ Bst).prod L) :=
    Finset.prod_congr rfl fun v hv => hout v (Finset.mem_sdiff.1 hv).2
  have hL'in : Bst.prod L' = 1 := Finset.prod_eq_one fun v hv => hin1 v hv
  rw [show (Finset.univ.prod fun v : V => ∫ ω, (Finset.univ.filter
        (fun j => v ∈ quadSites sites γ γ' s s' u u' j)).prod
          (fun j => ψ (quadIdx rIdx γ γ' j v) (U v ω)) ∂μ) = Finset.univ.prod L from rfl,
    show (Finset.univ.prod fun v : V => ∫ ω, (Finset.univ.filter
        (fun j => v ∈ keyQuadSites (cKey lev pt Bs γ s) (cKey lev pt Bs γ' s')
          (cKey lev pt Bs γ u) (cKey lev pt Bs γ' u') j)).prod
          (fun j => ψ (quadIdx rIdx γ γ' j v) (U v ω)) ∂μ) = Finset.univ.prod L' from rfl,
    hsplitL, hsplitL', hL'out, hL'in, hprodBst]
  ring

/-! ### The involution on column keys -/

/-- The involution `τ` on column keys: it swaps the two arguments at the pattern-(C)
coordinates. -/
def sigKey (D : Finset K) (x y : K -> Option V) : (K -> Option V) × (K -> Option V) :=
  (fun k => if k ∈ D then y k else x k, fun k => if k ∈ D then x k else y k)

omit [Fintype V] [DecidableEq V] [(γ : Γ) -> Fintype (S γ)] [Fintype I] [Fintype K] in
theorem sigKey_involutive (D : Finset K) :
    Function.Involutive
      (fun p : (K -> Option V) × (K -> Option V) => sigKey D p.1 p.2) := by
  intro p
  obtain ⟨x, y⟩ := p
  simp only [sigKey, Prod.mk.injEq]
  constructor <;> funext k <;> by_cases hk : k ∈ D <;> simp [hk]

omit [Fintype V] [DecidableEq V] [(γ : Γ) -> Fintype (S γ)] [Fintype I] [Fintype K] in
theorem sigKey_injective (D : Finset K) :
    Function.Injective
      (fun p : (K -> Option V) × (K -> Option V) => sigKey D p.1 p.2) :=
  (sigKey_involutive (V := V) D).injective

/-- Forgetting the coordinates of `ℬ` from a `ℬ \ J`-key. -/
def keyDrop (Bee : Finset K) (c : K -> Option V) : K -> Option V :=
  fun k => if k ∈ Bee then none else c k

omit [Fintype V] [DecidableEq V] [(γ : Γ) -> Fintype (S γ)] [Fintype I] [Fintype K] in
theorem keyDrop_cKey {Bee J : Finset K} (hJ : J ⊆ Bee) (g : Γ) (x : S g) :
    keyDrop Bee (cKey lev pt (Bee \ J) g x) = cKey lev pt Bee g x := by
  funext k
  by_cases hk : k ∈ Bee
  · rw [keyDrop, if_pos hk, cKey, if_neg (by simp [Finset.mem_sdiff, hk])]
  · rw [keyDrop, if_neg hk, cKey, cKey]
    have h1 : (k ∈ lev g \ (Bee \ J)) ↔ (k ∈ lev g \ Bee) := by
      simp only [Finset.mem_sdiff]
      exact ⟨fun h => ⟨h.1, hk⟩, fun h => ⟨h.1, fun hc => hk hc.1⟩⟩
    exact if_congr h1 rfl rfl

open Classical in
/-- `𝟙{r_k(γ) = r_k(γ')}` at the coordinates of `J`, read off a column key. -/
noncomputable def keyMaskOn (J : Finset K) (rIdx : Γ -> V -> R) (γ γ' : Γ)
    (c : K -> Option V) : Real :=
  if ∀ k ∈ J, ∀ w : V, c k = some w -> rIdx γ w = rIdx γ' w then 1 else 0

set_option linter.unusedSectionVars false in
theorem abs_keyMaskOn_le (J : Finset K) (rIdx : Γ -> V -> R) (γ γ' : Γ)
    (c : K -> Option V) : |keyMaskOn J rIdx γ γ' c| <= 1 := by
  classical
  unfold keyMaskOn
  split_ifs <;> simp

/-! ### The pattern-(C) coordinates carry `s_k ≠ s'_k` -/

omit [Fintype V] [(γ : Γ) -> Fintype (S γ)] [Fintype K] [DecidableEq K] in
theorem ne_of_patAt_eq_two {γ γ' : Γ} {s : S γ} {s' : S γ'} {u : S γ} {u' : S γ'} {k : K}
    (hp : patAt pt γ γ' s s' u u' k = 2) : pt γ s k ≠ pt γ' s' k := by
  unfold patAt at hp
  split_ifs at hp with hc1 hc2 hc3
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)
  · exact hc3.2.2
  · exact absurd hp (by decide)

omit [Fintype V] [(γ : Γ) -> Fintype (S γ)] [Fintype K] [DecidableEq K] in
theorem patAt_eq_zero_of {γ γ' : Γ} {s : S γ} {s' : S γ'} {u : S γ} {u' : S γ'} {k : K}
    (h1 : pt γ s k = pt γ' s' k) (h2 : pt γ u k = pt γ' u' k) (h3 : pt γ s k ≠ pt γ u k) :
    patAt pt γ γ' s s' u u' k = 0 := by
  unfold patAt
  rw [if_pos ⟨h1, h2, h3⟩]

/-! ### The coordinatewise rule when `ℬ` is nonempty -/

omit [(γ : Γ) -> Fintype (S γ)] [Fintype K] in
/-- `pt_u_eq_of_classOne` with `ℬ = ∅` replaced by `patAt ≠ 0` at the coordinate. -/
theorem pt_u_eq_of_patAt (h : IsBasisSystem μ U ψ Rpos B₀)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' -> k = k')
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    {γ γ' : Γ} {s : S γ} {s' : S γ'} {u : S γ} {u' : S γ'}
    (hne : multiMoment μ U ψ (quadSites sites γ γ' s s' u u') (quadIdx rIdx γ γ') ≠ 0)
    {k : K} (hk : k ∈ lev γ) (hB0 : k ∈ lev γ' -> patAt pt γ γ' s s' u u' k ≠ 0) :
    pt γ u k = if patAt pt γ γ' s s' u u' k = 2 ∧ k ∈ lev γ' then pt γ' s' k else pt γ s k := by
  classical
  have hfin : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  by_cases hk' : k ∈ lev γ'
  · have hne0 : patAt pt γ γ' s s' u u' k ≠ 0 := hB0 hk'
    rcases hfin (patAt pt γ γ' s s' u u' k) with hp | hp | hp | hp
    · exact absurd hp hne0
    · rw [hp, ite_eq_right (fun hcon => absurd hcon.1 (by decide))]
      exact (eq_of_patAt_eq_one (pt := pt) hp).1.symm
    · rw [hp, ite_eq_left ⟨rfl, hk'⟩]
      exact (eq_of_patAt_eq_two (pt := pt) hp).2.symm
    · rw [hp, ite_eq_right (fun hcon => absurd hcon.1 (by decide))]
      exact (all_eq_of_patAt_eq_three (pt := pt) hp
        (pattern_of_mem_inter h hsite hptc hpos hne hk hk')).2.1.symm
  · rw [ite_eq_right (fun hcon => hk' hcon.2)]
    exact (eq_of_notMem_lev_right h hsite hptc hpos hne hk hk').symm

omit [(γ : Γ) -> Fintype (S γ)] [Fintype K] in
/-- The same on the `γ'` side. -/
theorem pt_u'_eq_of_patAt (h : IsBasisSystem μ U ψ Rpos B₀)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' -> k = k')
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    {γ γ' : Γ} {s : S γ} {s' : S γ'} {u : S γ} {u' : S γ'}
    (hne : multiMoment μ U ψ (quadSites sites γ γ' s s' u u') (quadIdx rIdx γ γ') ≠ 0)
    {k : K} (hk' : k ∈ lev γ') (hB0 : k ∈ lev γ -> patAt pt γ γ' s s' u u' k ≠ 0) :
    pt γ' u' k = if patAt pt γ γ' s s' u u' k = 2 ∧ k ∈ lev γ then pt γ s k else pt γ' s' k := by
  classical
  have hfin : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  by_cases hk : k ∈ lev γ
  · have hne0 : patAt pt γ γ' s s' u u' k ≠ 0 := hB0 hk
    rcases hfin (patAt pt γ γ' s s' u u' k) with hp | hp | hp | hp
    · exact absurd hp hne0
    · rw [hp, ite_eq_right (fun hcon => absurd hcon.1 (by decide))]
      exact (eq_of_patAt_eq_one (pt := pt) hp).2.symm
    · rw [hp, ite_eq_left ⟨rfl, hk⟩]
      exact (eq_of_patAt_eq_two (pt := pt) hp).1.symm
    · rw [hp, ite_eq_right (fun hcon => absurd hcon.1 (by decide))]
      have hD := all_eq_of_patAt_eq_three (pt := pt) hp
        (pattern_of_mem_inter h hsite hptc hpos hne hk hk')
      exact hD.2.2.symm.trans hD.1
  · rw [ite_eq_right (fun hcon => hk hcon.2)]
    exact (eq_of_notMem_lev_left h hsite hptc hpos hne hk' hk).symm

/-! ### The Class-2 configuration, its quadruple set and its surrogate summand -/

/-- The configuration a quadruple carries, as the pair (pattern-(A) set, pattern-(C) set). -/
def clsFib (lev : Γ -> Finset K) (pt : ∀ γ, S γ -> K -> V) (γ γ' : Γ) (s : S γ) (s' : S γ')
    (u : S γ) (u' : S γ') : Finset K × Finset K :=
  (patAset lev pt γ γ' s s' u u',
    ((lev γ ∩ lev γ') \ patAset lev pt γ γ' s s' u u').filter
      (fun k => patAt pt γ γ' s s' u u' k = 2))

/-- The quadruples of one configuration, with the pattern-(A) coordinates of `J` relaxed
from `s_k ≠ u_k` to `s_k = u_k`. -/
def clsGood (lev : Γ -> Finset K) (pt : ∀ γ, S γ -> K -> V) (Bee J D : Finset K) (γ γ' : Γ)
    (s : S γ) (s' : S γ') (u : S γ) (u' : S γ') : Prop :=
  (∀ k ∈ Bee, pt γ s k = pt γ' s' k) ∧ (∀ k ∈ Bee, pt γ u k = pt γ' u' k)
  ∧ (∀ k ∈ lev γ \ (Bee \ J), pt γ u k = if k ∈ D then pt γ' s' k else pt γ s k)
  ∧ (∀ k ∈ lev γ' \ (Bee \ J), pt γ' u' k = if k ∈ D then pt γ s k else pt γ' s' k)
  ∧ (∀ k ∈ D, pt γ s k ≠ pt γ' s' k)

instance decidableClsGood (lev : Γ -> Finset K) (pt : ∀ γ, S γ -> K -> V)
    (Bee J D : Finset K) (γ γ' : Γ) (s : S γ) (s' : S γ') (u : S γ) (u' : S γ') :
    Decidable (clsGood lev pt Bee J D γ γ' s s' u u') := by
  unfold clsGood
  infer_instance

/-- The summand with the pattern-(A) sites of `ℬ` split off, as produced by
`multiMoment_split`. -/
noncomputable def clsF (μ : Measure Ω) (U : V -> Ω -> Real) (ψ : R -> Real -> Real)
    (sites : ∀ γ, S γ -> Finset V) (rIdx : Γ -> V -> R) (arr : ∀ γ, S γ -> I -> Real)
    (lev : Γ -> Finset K) (pt : ∀ γ, S γ -> K -> V) (Bee : Finset K) (γ γ' : Γ)
    (s : S γ) (s' : S γ') (u : S γ) (u' : S γ') : Real :=
  keyMask rIdx γ γ' (bKey pt Bee γ s) * keyMask rIdx γ γ' (bKey pt Bee γ u) *
    (unmCoef sites rIdx arr γ γ' s s' * unmCoef sites rIdx arr γ γ' u u') *
    multiMoment μ U ψ (keyQuadSites (cKey lev pt Bee γ s) (cKey lev pt Bee γ' s')
      (cKey lev pt Bee γ u) (cKey lev pt Bee γ' u')) (quadIdx rIdx γ γ')

open Classical in
/-- On a quadruple of the configuration `(ℬ, 𝒟_C)` the summand `G_{ss'}G_{uu'}m` equals
`clsF`; off it the summand vanishes. -/
theorem clsFib_term_eq (h : IsBasisSystem μ U ψ Rpos B₀)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' -> k = k')
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    {γ γ' : Γ} {Bee D : Finset K} (hBee : Bee ⊆ lev γ ∩ lev γ')
    (hD : D ⊆ (lev γ ∩ lev γ') \ Bee)
    (s : S γ) (s' : S γ') (u : S γ) (u' : S γ') :
    (if clsFib lev pt γ γ' s s' u u' = (Bee, D) then
        unmCoef sites rIdx arr γ γ' s s' * unmCoef sites rIdx arr γ γ' u u' *
          multiMoment μ U ψ (quadSites sites γ γ' s s' u u') (quadIdx rIdx γ γ') else 0)
      = (if clsGood lev pt Bee ∅ D γ γ' s s' u u' ∧ (∀ k ∈ Bee, pt γ s k ≠ pt γ u k) then
          clsF μ U ψ sites rIdx arr lev pt Bee γ γ' s s' u u' else 0) := by
  classical
  have hBeeγ : Bee ⊆ lev γ := fun k hk => (Finset.mem_inter.1 (hBee hk)).1
  have hBeeγ' : Bee ⊆ lev γ' := fun k hk => (Finset.mem_inter.1 (hBee hk)).2
  have hsd : Bee \ (∅ : Finset K) = Bee := Finset.sdiff_empty
  have hmaskS : ∀ x : S γ,
      (Bee.prod fun k => (if rIdx γ (pt γ x k) = rIdx γ' (pt γ x k) then (1:Real) else 0))
        = keyMask rIdx γ γ' (bKey pt Bee γ x) := by
    intro x
    rw [Finset.prod_boole]
    by_cases hc : ∀ k ∈ Bee, rIdx γ (pt γ x k) = rIdx γ' (pt γ x k)
    · rw [if_pos hc, keyMask_one ((keyIdxOK_bKey_iff (rIdx := rIdx) x).2 hc)]
    · rw [if_neg hc, keyMask_zero (fun hk => hc ((keyIdxOK_bKey_iff (rIdx := rIdx) x).1 hk))]
  have hsplitEq : ∀ (hA1 : ∀ k ∈ Bee, pt γ s k = pt γ' s' k)
      (hA2 : ∀ k ∈ Bee, pt γ u k = pt γ' u' k) (hA3 : ∀ k ∈ Bee, pt γ s k ≠ pt γ u k),
      unmCoef sites rIdx arr γ γ' s s' * unmCoef sites rIdx arr γ γ' u u' *
          multiMoment μ U ψ (quadSites sites γ γ' s s' u u') (quadIdx rIdx γ γ')
        = clsF μ U ψ sites rIdx arr lev pt Bee γ γ' s s' u u' := by
    intro hA1 hA2 hA3
    rw [clsF, multiMoment_split h hsite hptc hBeeγ hBeeγ' hA1 hA2 hA3, hmaskS s, hmaskS u]
    ring
  by_cases hT : clsGood lev pt Bee ∅ D γ γ' s s' u u' ∧ (∀ k ∈ Bee, pt γ s k ≠ pt γ u k)
  · rw [if_pos hT]
    obtain ⟨⟨hA1, hA2, hdet, hdet2, hDne⟩, hNe⟩ := hT
    rw [hsd] at hdet hdet2
    have hpat0 : ∀ k ∈ Bee, patAt pt γ γ' s s' u u' k = 0 :=
      fun k hk => patAt_eq_zero_of (hA1 k hk) (hA2 k hk) (hNe k hk)
    have hpatne : ∀ k ∈ (lev γ ∩ lev γ') \ Bee, patAt pt γ γ' s s' u u' k ≠ 0 := by
      intro k hk hcon
      rw [Finset.mem_sdiff, Finset.mem_inter] at hk
      have hkγ : k ∈ lev γ \ Bee := Finset.mem_sdiff.2 ⟨hk.1.1, hk.2⟩
      obtain ⟨p1, p2, p3⟩ := eq_of_patAt_eq_zero (pt := pt) hcon
      by_cases hkD : k ∈ D
      · rw [hdet k hkγ, if_pos hkD] at p3
        exact p3 p1
      · rw [hdet k hkγ, if_neg hkD] at p3
        exact p3 rfl
    have hpat2 : ∀ k ∈ D, patAt pt γ γ' s s' u u' k = 2 := by
      intro k hk
      have hk2 := hD hk
      rw [Finset.mem_sdiff, Finset.mem_inter] at hk2
      have hu : pt γ u k = pt γ' s' k := by
        rw [hdet k (Finset.mem_sdiff.2 ⟨hk2.1.1, hk2.2⟩), if_pos hk]
      have hu2 : pt γ' u' k = pt γ s k := by
        rw [hdet2 k (Finset.mem_sdiff.2 ⟨hk2.1.2, hk2.2⟩), if_pos hk]
      unfold patAt
      rw [if_neg (fun hc => hDne k hk hc.1), if_neg (fun hc => hDne k hk (hc.1.trans hu)),
        if_pos ⟨hu2.symm, hu.symm, hDne k hk⟩]
    have hpatn2 : ∀ k ∈ (lev γ ∩ lev γ') \ Bee, k ∉ D ->
        patAt pt γ γ' s s' u u' k ≠ 2 := by
      intro k hk hkD hcon
      rw [Finset.mem_sdiff, Finset.mem_inter] at hk
      have hu2 : pt γ' u' k = pt γ' s' k := by
        rw [hdet2 k (Finset.mem_sdiff.2 ⟨hk.1.2, hk.2⟩), if_neg hkD]
      obtain ⟨p1, p2⟩ := eq_of_patAt_eq_two (pt := pt) hcon
      exact ne_of_patAt_eq_two (pt := pt) hcon (p1.trans hu2)
    have hfib : clsFib lev pt γ γ' s s' u u' = (Bee, D) := by
      have hP : patAset lev pt γ γ' s s' u u' = Bee := by
        ext k
        simp only [patAset, Finset.mem_filter]
        constructor
        · rintro ⟨hk, hp⟩
          by_contra hkB
          exact hpatne k (Finset.mem_sdiff.2 ⟨hk, hkB⟩) hp
        · intro hk
          exact ⟨hBee hk, hpat0 k hk⟩
      rw [clsFib, hP]
      refine Prod.ext rfl ?_
      ext k
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hk, hp⟩
        by_contra hkD
        exact hpatn2 k hk hkD hp
      · intro hk
        exact ⟨hD hk, hpat2 k hk⟩
    rw [if_pos hfib]
    exact hsplitEq hA1 hA2 hNe
  · rw [if_neg hT]
    by_cases hfib : clsFib lev pt γ γ' s s' u u' = (Bee, D)
    · rw [if_pos hfib]
      by_cases hm : multiMoment μ U ψ (quadSites sites γ γ' s s' u u') (quadIdx rIdx γ γ') = 0
      · rw [hm]; ring
      · exfalso
        have hP : patAset lev pt γ γ' s s' u u' = Bee := congrArg Prod.fst hfib
        have hDq : ((lev γ ∩ lev γ') \ patAset lev pt γ γ' s s' u u').filter
            (fun k => patAt pt γ γ' s s' u u' k = 2) = D := congrArg Prod.snd hfib
        rw [hP] at hDq
        have hpat0 : ∀ k ∈ Bee, patAt pt γ γ' s s' u u' k = 0 := by
          intro k hk
          have hmem : k ∈ patAset lev pt γ γ' s s' u u' := by rw [hP]; exact hk
          exact (Finset.mem_filter.1 hmem).2
        have hB0 : ∀ k ∈ lev γ ∩ lev γ', k ∉ Bee -> patAt pt γ γ' s s' u u' k ≠ 0 := by
          intro k hk hkB hcon
          exact hkB (by rw [← hP]; exact Finset.mem_filter.2 ⟨hk, hcon⟩)
        refine hT ⟨⟨fun k hk => (eq_of_patAt_eq_zero (pt := pt) (hpat0 k hk)).1,
          fun k hk => (eq_of_patAt_eq_zero (pt := pt) (hpat0 k hk)).2.1, ?_, ?_, ?_⟩,
          fun k hk => (eq_of_patAt_eq_zero (pt := pt) (hpat0 k hk)).2.2⟩
        · intro k hk
          rw [hsd, Finset.mem_sdiff] at hk
          rw [pt_u_eq_of_patAt h hsite hptc hpos hm hk.1
            (fun hk2 => hB0 k (Finset.mem_inter.2 ⟨hk.1, hk2⟩) hk.2)]
          by_cases hkD : k ∈ D
          · have hk2 := hD hkD
            rw [Finset.mem_sdiff, Finset.mem_inter] at hk2
            have hp2 : patAt pt γ γ' s s' u u' k = 2 := by
              have hmem : k ∈ ((lev γ ∩ lev γ') \ Bee).filter
                  (fun k => patAt pt γ γ' s s' u u' k = 2) := by rw [hDq]; exact hkD
              exact (Finset.mem_filter.1 hmem).2
            rw [if_pos hkD, if_pos ⟨hp2, hk2.1.2⟩]
          · rw [if_neg hkD, if_neg]
            rintro ⟨hp2, hk2⟩
            refine hkD ?_
            rw [← hDq]
            exact Finset.mem_filter.2 ⟨Finset.mem_sdiff.2
              ⟨Finset.mem_inter.2 ⟨hk.1, hk2⟩, hk.2⟩, hp2⟩
        · intro k hk
          rw [hsd, Finset.mem_sdiff] at hk
          rw [pt_u'_eq_of_patAt h hsite hptc hpos hm hk.1
            (fun hk2 => hB0 k (Finset.mem_inter.2 ⟨hk2, hk.1⟩) hk.2)]
          by_cases hkD : k ∈ D
          · have hk2 := hD hkD
            rw [Finset.mem_sdiff, Finset.mem_inter] at hk2
            have hp2 : patAt pt γ γ' s s' u u' k = 2 := by
              have hmem : k ∈ ((lev γ ∩ lev γ') \ Bee).filter
                  (fun k => patAt pt γ γ' s s' u u' k = 2) := by rw [hDq]; exact hkD
              exact (Finset.mem_filter.1 hmem).2
            rw [if_pos hkD, if_pos ⟨hp2, hk2.1.1⟩]
          · rw [if_neg hkD, if_neg]
            rintro ⟨hp2, hk2⟩
            refine hkD ?_
            rw [← hDq]
            exact Finset.mem_filter.2 ⟨Finset.mem_sdiff.2
              ⟨Finset.mem_inter.2 ⟨hk2, hk.1⟩, hk.2⟩, hp2⟩
        · intro k hk
          have hmem : k ∈ ((lev γ ∩ lev γ') \ Bee).filter
              (fun k => patAt pt γ γ' s s' u u' k = 2) := by rw [hDq]; exact hk
          exact ne_of_patAt_eq_two (pt := pt) (Finset.mem_filter.1 hmem).2
    · rw [if_neg hfib]

/-! ### Reading the Class-2 conditions off the keys -/

omit [Fintype V] [DecidableEq V] [(γ : Γ) -> Fintype (S γ)] [Fintype I] [Fintype K] in
theorem bKey_eq_iff {Bs : Finset K} {γ γ' : Γ} (s : S γ) (s' : S γ') :
    bKey pt Bs γ s = bKey pt Bs γ' s' <-> ∀ k ∈ Bs, pt γ s k = pt γ' s' k := by
  constructor
  · intro hb k hk
    have hkk := congrFun hb k
    rw [bKey_apply_of_mem s hk, bKey_apply_of_mem s' hk] at hkk
    exact Option.some.inj hkk
  · intro hb
    funext k
    by_cases hk : k ∈ Bs
    · rw [bKey_apply_of_mem s hk, bKey_apply_of_mem s' hk, hb k hk]
    · rw [bKey, bKey, if_neg hk, if_neg hk]

omit [Fintype V] [DecidableEq V] [(γ : Γ) -> Fintype (S γ)] [Fintype I] [Fintype K] in
/-- The coordinatewise rule is `τ` on column keys. -/
theorem cKey_pair_eq_sigKey_iff {Bs D : Finset K} {γ γ' : Γ}
    (hD : ∀ k ∈ D, k ∈ lev γ ∧ k ∈ lev γ' ∧ k ∉ Bs)
    (s u : S γ) (s' u' : S γ') :
    ((cKey lev pt Bs γ u, cKey lev pt Bs γ' u')
        = sigKey D (cKey lev pt Bs γ s) (cKey lev pt Bs γ' s'))
      <-> ((∀ k ∈ lev γ \ Bs, pt γ u k = if k ∈ D then pt γ' s' k else pt γ s k)
        ∧ (∀ k ∈ lev γ' \ Bs, pt γ' u' k = if k ∈ D then pt γ s k else pt γ' s' k)) := by
  constructor
  · intro hEq
    have e1 : cKey lev pt Bs γ u
        = (sigKey D (cKey lev pt Bs γ s) (cKey lev pt Bs γ' s')).1 := congrArg Prod.fst hEq
    have e2 : cKey lev pt Bs γ' u'
        = (sigKey D (cKey lev pt Bs γ s) (cKey lev pt Bs γ' s')).2 := congrArg Prod.snd hEq
    constructor
    · intro k hk
      rw [Finset.mem_sdiff] at hk
      have hkk := congrFun e1 k
      rw [cKey_apply_of_mem (lev := lev) u hk.1 hk.2] at hkk
      simp only [sigKey] at hkk
      by_cases hkD : k ∈ D
      · rw [if_pos hkD] at hkk
        rw [if_pos hkD]
        rw [cKey_apply_of_mem (lev := lev) s' (hD k hkD).2.1 hk.2] at hkk
        exact Option.some.inj hkk
      · rw [if_neg hkD] at hkk
        rw [if_neg hkD]
        rw [cKey_apply_of_mem (lev := lev) s hk.1 hk.2] at hkk
        exact Option.some.inj hkk
    · intro k hk
      rw [Finset.mem_sdiff] at hk
      have hkk := congrFun e2 k
      rw [cKey_apply_of_mem (lev := lev) u' hk.1 hk.2] at hkk
      simp only [sigKey] at hkk
      by_cases hkD : k ∈ D
      · rw [if_pos hkD] at hkk
        rw [if_pos hkD]
        rw [cKey_apply_of_mem (lev := lev) s (hD k hkD).1 hk.2] at hkk
        exact Option.some.inj hkk
      · rw [if_neg hkD] at hkk
        rw [if_neg hkD]
        rw [cKey_apply_of_mem (lev := lev) s' hk.1 hk.2] at hkk
        exact Option.some.inj hkk
  · rintro ⟨h1, h2⟩
    refine Prod.ext ?_ ?_
    · funext k
      simp only [sigKey]
      by_cases hk : k ∈ lev γ \ Bs
      · rw [cKey_apply_of_mem (lev := lev) u (Finset.mem_sdiff.1 hk).1
          (Finset.mem_sdiff.1 hk).2, h1 k hk]
        by_cases hkD : k ∈ D
        · rw [if_pos hkD, if_pos hkD, cKey_apply_of_mem (lev := lev) s' (hD k hkD).2.1
            (Finset.mem_sdiff.1 hk).2]
        · rw [if_neg hkD, if_neg hkD, cKey_apply_of_mem (lev := lev) s
            (Finset.mem_sdiff.1 hk).1 (Finset.mem_sdiff.1 hk).2]
      · have hkD : k ∉ D := by
          intro hkD
          exact hk (Finset.mem_sdiff.2 ⟨(hD k hkD).1, (hD k hkD).2.2⟩)
        rw [cKey_apply_of_notMem (lev := lev) u hk, if_neg hkD,
          cKey_apply_of_notMem (lev := lev) s hk]
    · funext k
      simp only [sigKey]
      by_cases hk : k ∈ lev γ' \ Bs
      · rw [cKey_apply_of_mem (lev := lev) u' (Finset.mem_sdiff.1 hk).1
          (Finset.mem_sdiff.1 hk).2, h2 k hk]
        by_cases hkD : k ∈ D
        · rw [if_pos hkD, if_pos hkD, cKey_apply_of_mem (lev := lev) s (hD k hkD).1
            (Finset.mem_sdiff.1 hk).2]
        · rw [if_neg hkD, if_neg hkD, cKey_apply_of_mem (lev := lev) s'
            (Finset.mem_sdiff.1 hk).1 (Finset.mem_sdiff.1 hk).2]
      · have hkD : k ∉ D := by
          intro hkD
          exact hk (Finset.mem_sdiff.2 ⟨(hD k hkD).2.1, (hD k hkD).2.2⟩)
        rw [cKey_apply_of_notMem (lev := lev) u' hk, if_neg hkD,
          cKey_apply_of_notMem (lev := lev) s' hk]

set_option linter.unusedSectionVars false in
theorem keyMaskOn_cKey {J Bs : Finset K} {γ γ' : Γ} (hJ : ∀ k ∈ J, k ∈ lev γ ∧ k ∉ Bs)
    (x : S γ) :
    keyMaskOn J rIdx γ γ' (cKey lev pt Bs γ x)
      = if ∀ k ∈ J, rIdx γ (pt γ x k) = rIdx γ' (pt γ x k) then (1:Real) else 0 := by
  classical
  unfold keyMaskOn
  congr 1
  simp only [eq_iff_iff]
  constructor
  · intro hc k hk
    exact hc k hk (pt γ x k) (cKey_apply_of_mem (lev := lev) x (hJ k hk).1 (hJ k hk).2)
  · intro hc k hk w hw
    rw [cKey_apply_of_mem (lev := lev) x (hJ k hk).1 (hJ k hk).2] at hw
    cases Option.some.inj hw
    exact hc k hk

set_option linter.unusedSectionVars false in
/-- `𝟙{r = r'}` over `ℬ` splits into the part the row key sees and the part the column key
sees. -/
theorem keyMask_bKey_split {Bee J : Finset K} (hJ : J ⊆ Bee) {γ γ' : Γ} (x : S γ)
    (hJlev : ∀ k ∈ J, k ∈ lev γ) :
    keyMask rIdx γ γ' (bKey pt Bee γ x)
      = keyMask rIdx γ γ' (bKey pt (Bee \ J) γ x) *
        keyMaskOn J rIdx γ γ' (cKey lev pt (Bee \ J) γ x) := by
  classical
  have hJd : ∀ k ∈ J, k ∈ lev γ ∧ k ∉ Bee \ J := by
    intro k hk
    exact ⟨hJlev k hk, by simp [Finset.mem_sdiff, hk]⟩
  rw [keyMaskOn_cKey (rIdx := rIdx) hJd x]
  by_cases hc : ∀ k ∈ Bee, rIdx γ (pt γ x k) = rIdx γ' (pt γ x k)
  · rw [keyMask_one ((keyIdxOK_bKey_iff (rIdx := rIdx) x).2 hc),
      keyMask_one ((keyIdxOK_bKey_iff (rIdx := rIdx) x).2
        (fun k hk => hc k (Finset.mem_sdiff.1 hk).1)),
      if_pos (fun k hk => hc k (hJ hk))]
    ring
  · rw [keyMask_zero (fun hk => hc ((keyIdxOK_bKey_iff (rIdx := rIdx) x).1 hk))]
    by_cases hc2 : ∀ k ∈ Bee \ J, rIdx γ (pt γ x k) = rIdx γ' (pt γ x k)
    · have hc3 : ¬ ∀ k ∈ J, rIdx γ (pt γ x k) = rIdx γ' (pt γ x k) := by
        intro hc3
        refine hc fun k hk => ?_
        by_cases hkJ : k ∈ J
        · exact hc3 k hkJ
        · exact hc2 k (Finset.mem_sdiff.2 ⟨hk, hkJ⟩)
      rw [if_neg hc3]
      ring
    · rw [keyMask_zero (fun hk => hc2 ((keyIdxOK_bKey_iff (rIdx := rIdx) x).1 hk))]
      ring

/-! ### The configuration's coefficient, as a function of the column keys alone -/

open Classical in
/-- The contribution of a Class-2 configuration beyond the two coefficient arrays, as a
function of the column keys `(v,v')`: the orthonormality factors on `J`, the side conditions on
`(s,s')`, and the reduced moment. -/
noncomputable def clsTheta (μ : Measure Ω) (U : V -> Ω -> Real) (ψ : R -> Real -> Real)
    (rIdx : Γ -> V -> R) (γ γ' : Γ) (Bee J D : Finset K) (x y : K -> Option V) : Real :=
  (if (∀ k ∈ J, x k = y k) ∧ (∀ k ∈ D, x k ≠ y k) then (1:Real) else 0) *
    (keyMaskOn J rIdx γ γ' x * keyMaskOn J rIdx γ γ' (sigKey D x y).1) *
    multiMoment μ U ψ (keyQuadSites (keyDrop Bee x) (keyDrop Bee y)
      (keyDrop Bee (sigKey D x y).1) (keyDrop Bee (sigKey D x y).2)) (quadIdx rIdx γ γ')

set_option linter.unusedSectionVars false in
theorem abs_clsTheta_le_ofCard (h : IsBasisSystem μ U ψ Rpos B₀) {M : ℕ}
    (hkey : ∀ c : K -> Option V, (keySites c).card <= M)
    (γ γ' : Γ) (Bee J D : Finset K)
    (x y : K -> Option V) :
    |clsTheta μ U ψ rIdx γ γ' Bee J D x y| <= max B₀ 1 ^ (4 * M) := by
  classical
  unfold clsTheta
  rw [abs_mul, abs_mul, abs_mul]
  have hM : (0:Real) <= max B₀ 1 ^ (4 * M) := by positivity
  have h1 : |(if (∀ k ∈ J, x k = y k) ∧ (∀ k ∈ D, x k ≠ y k) then (1:Real) else 0)| <= 1 := by
    split_ifs <;> simp
  have h2 := abs_keyMaskOn_le J rIdx γ γ' x
  have h3 := abs_keyMaskOn_le J rIdx γ γ' (sigKey D x y).1
  have h4 := abs_multiMoment_le_ofCard h (keyQuadSites (keyDrop Bee x) (keyDrop Bee y)
    (keyDrop Bee (sigKey D x y).1) (keyDrop Bee (sigKey D x y).2))
    (card_keyQuadSites_le hkey _ _ _ _) (quadIdx rIdx γ γ')
  have hstep := mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) zero_le_one) h3
    (abs_nonneg _) (by norm_num : (0:Real) <= 1 * 1)) h4 (abs_nonneg _)
    (by norm_num : (0:Real) <= 1 * 1 * 1)
  rw [← mul_assoc]
  simpa using hstep


set_option linter.unusedSectionVars false in
/-- The Class-2 surrogate is bounded, with constant in terms of `|V|`. -/
theorem abs_clsTheta_le (h : IsBasisSystem μ U ψ Rpos B₀) (γ γ' : Γ) (Bee J D : Finset K)
    (x y : K -> Option V) :
    |clsTheta μ U ψ rIdx γ γ' Bee J D x y| <= max B₀ 1 ^ (4 * Fintype.card V) := by
  apply abs_clsTheta_le_ofCard (M := Fintype.card V) <;>
    first
      | assumption
      | exact fun _ _ => Finset.card_le_univ _
      | exact fun _ => Finset.card_le_univ _
set_option linter.unusedSectionVars false in
/-- The Class-2 condition is the contraction's shape plus a condition on the column keys. -/
theorem clsGood_iff {γ γ' : Γ} {Bee J D : Finset K} (hJ : J ⊆ Bee)
    (hBee : Bee ⊆ lev γ ∩ lev γ') (hD : D ⊆ (lev γ ∩ lev γ') \ Bee)
    (s : S γ) (s' : S γ') (u : S γ) (u' : S γ') :
    clsGood lev pt Bee J D γ γ' s s' u u'
      <-> ((bKey pt (Bee \ J) γ s = bKey pt (Bee \ J) γ' s' ∧
            bKey pt (Bee \ J) γ u = bKey pt (Bee \ J) γ' u' ∧
            (cKey lev pt (Bee \ J) γ u, cKey lev pt (Bee \ J) γ' u')
              = sigKey D (cKey lev pt (Bee \ J) γ s) (cKey lev pt (Bee \ J) γ' s'))
          ∧ ((∀ k ∈ J, cKey lev pt (Bee \ J) γ s k = cKey lev pt (Bee \ J) γ' s' k) ∧
             (∀ k ∈ D, cKey lev pt (Bee \ J) γ s k ≠ cKey lev pt (Bee \ J) γ' s' k))) := by
  classical
  have hBeeγ : Bee ⊆ lev γ := fun k hk => (Finset.mem_inter.1 (hBee hk)).1
  have hBeeγ' : Bee ⊆ lev γ' := fun k hk => (Finset.mem_inter.1 (hBee hk)).2
  have hJmem : ∀ k ∈ J, k ∈ lev γ ∧ k ∈ lev γ' ∧ k ∉ Bee \ J :=
    fun k hk => ⟨hBeeγ (hJ hk), hBeeγ' (hJ hk), by simp [Finset.mem_sdiff, hk]⟩
  have hDmem : ∀ k ∈ D, k ∈ lev γ ∧ k ∈ lev γ' ∧ k ∉ Bee \ J := by
    intro k hk
    have hk2 := hD hk
    rw [Finset.mem_sdiff, Finset.mem_inter] at hk2
    exact ⟨hk2.1.1, hk2.1.2, fun hc => hk2.2 (Finset.mem_sdiff.1 hc).1⟩
  have hJeq : ∀ k ∈ J, (cKey lev pt (Bee \ J) γ s k = cKey lev pt (Bee \ J) γ' s' k
      <-> pt γ s k = pt γ' s' k) := by
    intro k hk
    rw [cKey_apply_of_mem (lev := lev) s (hJmem k hk).1 (hJmem k hk).2.2,
      cKey_apply_of_mem (lev := lev) s' (hJmem k hk).2.1 (hJmem k hk).2.2]
    exact ⟨fun hc => Option.some.inj hc, fun hc => by rw [hc]⟩
  have hDeq : ∀ k ∈ D, (cKey lev pt (Bee \ J) γ s k = cKey lev pt (Bee \ J) γ' s' k
      <-> pt γ s k = pt γ' s' k) := by
    intro k hk
    rw [cKey_apply_of_mem (lev := lev) s (hDmem k hk).1 (hDmem k hk).2.2,
      cKey_apply_of_mem (lev := lev) s' (hDmem k hk).2.1 (hDmem k hk).2.2]
    exact ⟨fun hc => Option.some.inj hc, fun hc => by rw [hc]⟩
  have hDnot : ∀ k ∈ D, k ∉ J := by
    intro k hk hkJ
    have hk2 := hD hk
    rw [Finset.mem_sdiff] at hk2
    exact hk2.2 (hJ hkJ)
  have hBsplit : ∀ k ∈ Bee, k ∈ Bee \ J ∨ k ∈ J := by
    intro k hk
    by_cases hkJ : k ∈ J
    · exact Or.inr hkJ
    · exact Or.inl (Finset.mem_sdiff.2 ⟨hk, hkJ⟩)
  constructor
  · rintro ⟨hA1, hA2, hdet, hdet2, hDne⟩
    refine ⟨⟨(bKey_eq_iff (pt := pt) s s').2 (fun k hk => hA1 k (Finset.mem_sdiff.1 hk).1),
      (bKey_eq_iff (pt := pt) u u').2 (fun k hk => hA2 k (Finset.mem_sdiff.1 hk).1),
      (cKey_pair_eq_sigKey_iff (lev := lev) hDmem s u s' u').2 ⟨hdet, hdet2⟩⟩, ?_, ?_⟩
    · intro k hk
      exact (hJeq k hk).2 (hA1 k (hJ hk))
    · intro k hk
      exact fun hc => hDne k hk ((hDeq k hk).1 hc)
  · rintro ⟨⟨hb1, hb2, hsg⟩, hJc, hDc⟩
    obtain ⟨hdet, hdet2⟩ := (cKey_pair_eq_sigKey_iff (lev := lev) hDmem s u s' u').1 hsg
    have hA1 : ∀ k ∈ Bee, pt γ s k = pt γ' s' k := by
      intro k hk
      rcases hBsplit k hk with hk2 | hk2
      · exact (bKey_eq_iff (pt := pt) s s').1 hb1 k hk2
      · exact (hJeq k hk2).1 (hJc k hk2)
    refine ⟨hA1, ?_, hdet, hdet2, fun k hk => fun hc => hDc k hk ((hDeq k hk).2 hc)⟩
    intro k hk
    rcases hBsplit k hk with hk2 | hk2
    · exact (bKey_eq_iff (pt := pt) u u').1 hb2 k hk2
    · have hkγ : k ∈ lev γ \ (Bee \ J) :=
        Finset.mem_sdiff.2 ⟨(hJmem k hk2).1, (hJmem k hk2).2.2⟩
      have hkγ' : k ∈ lev γ' \ (Bee \ J) :=
        Finset.mem_sdiff.2 ⟨(hJmem k hk2).2.1, (hJmem k hk2).2.2⟩
      rw [hdet k hkγ, hdet2 k hkγ', if_neg (fun hc => hDnot k hc hk2),
        if_neg (fun hc => hDnot k hc hk2)]
      exact hA1 k hk

set_option linter.unusedSectionVars false in
/-- One relaxed configuration, written as a contraction sum. -/
theorem clsGood_term_eq {γ γ' : Γ} {Bee J D : Finset K} (hJ : J ⊆ Bee)
    (hBee : Bee ⊆ lev γ ∩ lev γ') (hD : D ⊆ (lev γ ∩ lev γ') \ Bee)
    (s : S γ) (s' : S γ') (u : S γ) (u' : S γ') :
    (if clsGood lev pt Bee J D γ γ' s s' u u' then
        clsF μ U ψ sites rIdx arr lev pt Bee γ γ' s s' u u' else 0)
      = (if bKey pt (Bee \ J) γ s = bKey pt (Bee \ J) γ' s' ∧
            bKey pt (Bee \ J) γ u = bKey pt (Bee \ J) γ' u' ∧
            (cKey lev pt (Bee \ J) γ u, cKey lev pt (Bee \ J) γ' u')
              = sigKey D (cKey lev pt (Bee \ J) γ s) (cKey lev pt (Bee \ J) γ' s')
          then clsTheta μ U ψ rIdx γ γ' Bee J D
              (cKey lev pt (Bee \ J) γ s) (cKey lev pt (Bee \ J) γ' s') *
            ((keyMask rIdx γ γ' (bKey pt (Bee \ J) γ s) * unmCoef sites rIdx arr γ γ' s s') *
              (keyMask rIdx γ γ' (bKey pt (Bee \ J) γ u) * unmCoef sites rIdx arr γ γ' u u'))
          else 0) := by
  classical
  have hBeeγ : Bee ⊆ lev γ := fun k hk => (Finset.mem_inter.1 (hBee hk)).1
  have hJlev : ∀ k ∈ J, k ∈ lev γ := fun k hk => hBeeγ (hJ hk)
  by_cases hG : clsGood lev pt Bee J D γ γ' s s' u u'
  · rw [if_pos hG]
    obtain ⟨hshape, hcond⟩ := (clsGood_iff (lev := lev) hJ hBee hD s s' u u').1 hG
    rw [if_pos hshape]
    have hw : cKey lev pt (Bee \ J) γ u
        = (sigKey D (cKey lev pt (Bee \ J) γ s) (cKey lev pt (Bee \ J) γ' s')).1 :=
      congrArg Prod.fst hshape.2.2
    have hw2 : cKey lev pt (Bee \ J) γ' u'
        = (sigKey D (cKey lev pt (Bee \ J) γ s) (cKey lev pt (Bee \ J) γ' s')).2 :=
      congrArg Prod.snd hshape.2.2
    simp only [clsF, clsTheta]
    rw [if_pos hcond, keyMask_bKey_split (rIdx := rIdx) hJ s hJlev,
      keyMask_bKey_split (rIdx := rIdx) hJ u hJlev,
      ← keyDrop_cKey (lev := lev) hJ γ s, ← keyDrop_cKey (lev := lev) hJ γ' s',
      ← keyDrop_cKey (lev := lev) hJ γ u, ← keyDrop_cKey (lev := lev) hJ γ' u', hw, hw2]
    ring
  · rw [if_neg hG]
    by_cases hshape : bKey pt (Bee \ J) γ s = bKey pt (Bee \ J) γ' s' ∧
        bKey pt (Bee \ J) γ u = bKey pt (Bee \ J) γ' u' ∧
        (cKey lev pt (Bee \ J) γ u, cKey lev pt (Bee \ J) γ' u')
          = sigKey D (cKey lev pt (Bee \ J) γ s) (cKey lev pt (Bee \ J) γ' s')
    · rw [if_pos hshape]
      have hno : ¬ ((∀ k ∈ J, cKey lev pt (Bee \ J) γ s k = cKey lev pt (Bee \ J) γ' s' k) ∧
          (∀ k ∈ D, cKey lev pt (Bee \ J) γ s k ≠ cKey lev pt (Bee \ J) γ' s' k)) :=
        fun hc => hG ((clsGood_iff (lev := lev) hJ hBee hD s s' u u').2 ⟨hshape, hc⟩)
      simp only [clsTheta]
      rw [if_neg hno]
      ring
    · rw [if_neg hshape]

set_option linter.unusedSectionVars false in
/-- The bound for one relaxed configuration, by Cauchy--Schwarz on the contraction of the
masked unmatched coefficient array. -/
theorem clsGood_sum_bound_ofCard (h : IsBasisSystem μ U ψ Rpos B₀) {M : ℕ}
    (hkey : ∀ c : K -> Option V, (keySites c).card <= M)
    {γ γ' : Γ} {Bee J D : Finset K}
    (hJ : J ⊆ Bee) (hBee : Bee ⊆ lev γ ∩ lev γ') (hD : D ⊆ (lev γ ∩ lev γ') \ Bee) :
    |Finset.univ.sum fun q : (S γ × S γ') × (S γ × S γ') =>
        (if clsGood lev pt Bee J D γ γ' q.1.1 q.1.2 q.2.1 q.2.2 then
          clsF μ U ψ sites rIdx arr lev pt Bee γ γ' q.1.1 q.1.2 q.2.1 q.2.2 else 0)|
      <= max B₀ 1 ^ (4 * M) *
        rectFrobSq (contrEntry lev pt (Bee \ J) γ γ'
          (fun a b => keyMask rIdx γ γ' (bKey pt (Bee \ J) γ a) *
            unmCoef sites rIdx arr γ γ' a b)) := by
  classical
  rw [Finset.sum_congr rfl fun q _ =>
    clsGood_term_eq (μ := μ) (U := U) (ψ := ψ) (sites := sites) (arr := arr) hJ hBee hD
      q.1.1 q.1.2 q.2.1 q.2.2]
  exact abs_sum_quad_contrEntry_le (Bee \ J) γ γ'
    (fun a b => keyMask rIdx γ γ' (bKey pt (Bee \ J) γ a) * unmCoef sites rIdx arr γ γ' a b)
    (sigKey D) (clsTheta μ U ψ rIdx γ γ' Bee J D) (by positivity)
    (fun x y => abs_clsTheta_le_ofCard h hkey γ γ' Bee J D x y) (sigKey_injective (V := V) D)

set_option linter.unusedSectionVars false in
/-- The bound for one relaxed configuration, with constant in terms of `|V|`. -/
theorem clsGood_sum_bound (h : IsBasisSystem μ U ψ Rpos B₀) {γ γ' : Γ} {Bee J D : Finset K}
    (hJ : J ⊆ Bee) (hBee : Bee ⊆ lev γ ∩ lev γ') (hD : D ⊆ (lev γ ∩ lev γ') \ Bee) :
    |Finset.univ.sum fun q : (S γ × S γ') × (S γ × S γ') =>
        (if clsGood lev pt Bee J D γ γ' q.1.1 q.1.2 q.2.1 q.2.2 then
          clsF μ U ψ sites rIdx arr lev pt Bee γ γ' q.1.1 q.1.2 q.2.1 q.2.2 else 0)|
      <= max B₀ 1 ^ (4 * Fintype.card V) *
        rectFrobSq (contrEntry lev pt (Bee \ J) γ γ'
          (fun a b => keyMask rIdx γ γ' (bKey pt (Bee \ J) γ a) *
            unmCoef sites rIdx arr γ γ' a b)) := by
  apply clsGood_sum_bound_ofCard (M := Fintype.card V) <;>
    first
      | assumption
      | exact fun _ _ => Finset.card_le_univ _
      | exact fun _ => Finset.card_le_univ _

/-! ### Inclusion--exclusion over the pattern-(A) set -/

/-- Inclusion--exclusion over the subsets `J ⊆ ℬ`: the side condition
`∏_{k ∈ ℬ}(1 − 𝟙{P k})` expands into `2^{|ℬ|}` signed terms. -/
theorem sum_powerset_sign {κ : Type*} [Fintype κ] [DecidableEq κ] (Bee : Finset κ) (P : κ -> Prop)
    [DecidablePred P] :
    (if ∀ k ∈ Bee, ¬ P k then (1:Real) else 0)
      = Bee.powerset.sum fun J => (-1:Real) ^ J.card * (if ∀ k ∈ J, P k then (1:Real) else 0) := by
  classical
  have hkey := Finset.prod_add (fun k => (if P k then (-1:Real) else 0)) (fun _ => (1:Real)) Bee
  have hL : (Bee.prod fun k => ((if P k then (-1:Real) else 0) + 1))
      = (if ∀ k ∈ Bee, ¬ P k then (1:Real) else 0) := by
    by_cases hc : ∀ k ∈ Bee, ¬ P k
    · rw [if_pos hc]
      refine Finset.prod_eq_one fun k hk => ?_
      rw [if_neg (hc k hk)]
      ring
    · rw [if_neg hc, not_forall] at *
      obtain ⟨k, hk⟩ := hc
      rw [not_imp, not_not] at hk
      exact Finset.prod_eq_zero hk.1 (by rw [if_pos hk.2]; ring)
  have hR : ∀ t ∈ Bee.powerset,
      (t.prod fun k => (if P k then (-1:Real) else 0)) * ((Bee \ t).prod fun _ => (1:Real))
        = (-1:Real) ^ t.card * (if ∀ k ∈ t, P k then (1:Real) else 0) := by
    intro t _
    rw [Finset.prod_const_one, mul_one]
    by_cases hc : ∀ k ∈ t, P k
    · rw [if_pos hc, mul_one, ← Finset.prod_const]
      exact Finset.prod_congr rfl fun k hk => by rw [if_pos (hc k hk)]
    · rw [if_neg hc, mul_zero, not_forall] at *
      obtain ⟨k, hk⟩ := hc
      rw [not_imp] at hk
      exact Finset.prod_eq_zero hk.1 (by rw [if_neg hk.2])
  rw [← hL, hkey]
  exact Finset.sum_congr rfl hR

set_option linter.unusedSectionVars false in
/-- The relaxed configurations are nested exactly as inclusion--exclusion needs. -/
theorem clsGood_iff_relax {γ γ' : Γ} {Bee J D : Finset K} (hJ : J ⊆ Bee)
    (hBee : Bee ⊆ lev γ ∩ lev γ') (hD : D ⊆ (lev γ ∩ lev γ') \ Bee)
    (s : S γ) (s' : S γ') (u : S γ) (u' : S γ') :
    clsGood lev pt Bee J D γ γ' s s' u u'
      <-> (clsGood lev pt Bee ∅ D γ γ' s s' u u' ∧ (∀ k ∈ J, pt γ s k = pt γ u k)) := by
  classical
  have hBeeγ : Bee ⊆ lev γ := fun k hk => (Finset.mem_inter.1 (hBee hk)).1
  have hBeeγ' : Bee ⊆ lev γ' := fun k hk => (Finset.mem_inter.1 (hBee hk)).2
  have hsd : Bee \ (∅ : Finset K) = Bee := Finset.sdiff_empty
  have hDnot : ∀ k ∈ J, k ∉ D := by
    intro k hk hkD
    have hk2 := hD hkD
    rw [Finset.mem_sdiff] at hk2
    exact hk2.2 (hJ hk)
  constructor
  · rintro ⟨hA1, hA2, hdet, hdet2, hDne⟩
    refine ⟨⟨hA1, hA2, ?_, ?_, hDne⟩, ?_⟩
    · intro k hk
      rw [hsd] at hk
      exact hdet k (Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hk).1,
        fun hc => (Finset.mem_sdiff.1 hk).2 (Finset.mem_sdiff.1 hc).1⟩)
    · intro k hk
      rw [hsd] at hk
      exact hdet2 k (Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hk).1,
        fun hc => (Finset.mem_sdiff.1 hk).2 (Finset.mem_sdiff.1 hc).1⟩)
    · intro k hk
      have hkm : k ∈ lev γ \ (Bee \ J) :=
        Finset.mem_sdiff.2 ⟨hBeeγ (hJ hk), by simp [Finset.mem_sdiff, hk]⟩
      rw [hdet k hkm, if_neg (hDnot k hk)]
  · rintro ⟨⟨hA1, hA2, hdet, hdet2, hDne⟩, hJeq⟩
    rw [hsd] at hdet hdet2
    refine ⟨hA1, hA2, ?_, ?_, hDne⟩
    · intro k hk
      rw [Finset.mem_sdiff] at hk
      by_cases hkB : k ∈ Bee
      · have hkJ : k ∈ J := by
          by_contra hc
          exact hk.2 (Finset.mem_sdiff.2 ⟨hkB, hc⟩)
        rw [if_neg (hDnot k hkJ)]
        exact (hJeq k hkJ).symm
      · exact hdet k (Finset.mem_sdiff.2 ⟨hk.1, hkB⟩)
    · intro k hk
      rw [Finset.mem_sdiff] at hk
      by_cases hkB : k ∈ Bee
      · have hkJ : k ∈ J := by
          by_contra hc
          exact hk.2 (Finset.mem_sdiff.2 ⟨hkB, hc⟩)
        rw [if_neg (hDnot k hkJ)]
        have h1 : pt γ u k = pt γ s k := (hJeq k hkJ).symm
        have h2 : pt γ u k = pt γ' u' k := hA2 k hkB
        have h3 : pt γ s k = pt γ' s' k := hA1 k hkB
        rw [← h2, h1, h3]
      · exact hdet2 k (Finset.mem_sdiff.2 ⟨hk.1, hkB⟩)

set_option linter.unusedSectionVars false in
/-- The `2^{|ℬ|}` decomposition of a Class-2 configuration, term by term. -/
theorem clsTgt_eq_sum {γ γ' : Γ} {Bee D : Finset K}
    (hBee : Bee ⊆ lev γ ∩ lev γ') (hD : D ⊆ (lev γ ∩ lev γ') \ Bee)
    (s : S γ) (s' : S γ') (u : S γ) (u' : S γ') (X : Real) :
    (if clsGood lev pt Bee ∅ D γ γ' s s' u u' ∧ (∀ k ∈ Bee, pt γ s k ≠ pt γ u k) then X else 0)
      = Bee.powerset.sum fun J => (-1:Real) ^ J.card *
          (if clsGood lev pt Bee J D γ γ' s s' u u' then X else 0) := by
  classical
  have hiff : ∀ J ∈ Bee.powerset, (clsGood lev pt Bee J D γ γ' s s' u u'
      <-> (clsGood lev pt Bee ∅ D γ γ' s s' u u' ∧ (∀ k ∈ J, pt γ s k = pt γ u k))) :=
    fun J hJ => clsGood_iff_relax (lev := lev) (Finset.mem_powerset.1 hJ) hBee hD s s' u u'
  by_cases hG : clsGood lev pt Bee ∅ D γ γ' s s' u u'
  · have hstep : ∀ J ∈ Bee.powerset,
        (-1:Real) ^ J.card * (if clsGood lev pt Bee J D γ γ' s s' u u' then X else 0)
          = ((-1:Real) ^ J.card *
              (if ∀ k ∈ J, pt γ s k = pt γ u k then (1:Real) else 0)) * X := by
      intro J hJ
      by_cases hc : ∀ k ∈ J, pt γ s k = pt γ u k
      · rw [if_pos ((hiff J hJ).2 ⟨hG, hc⟩), if_pos hc]; ring
      · rw [if_neg (fun hcon => hc ((hiff J hJ).1 hcon).2), if_neg hc]; ring
    have hIE : (Bee.powerset.sum fun J => (-1:Real) ^ J.card *
          (if ∀ k ∈ J, pt γ s k = pt γ u k then (1:Real) else 0))
        = (if ∀ k ∈ Bee, ¬ (pt γ s k = pt γ u k) then (1:Real) else 0) :=
      (sum_powerset_sign Bee (fun k => pt γ s k = pt γ u k)).symm
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul, hIE]
    by_cases hNe : ∀ k ∈ Bee, pt γ s k ≠ pt γ u k
    · rw [if_pos ⟨hG, hNe⟩, if_pos hNe]; ring
    · rw [if_neg (fun hc => hNe hc.2), if_neg hNe]; ring
  · rw [if_neg (fun hc => hG hc.1)]
    refine (Finset.sum_eq_zero fun J hJ => ?_).symm
    rw [if_neg (fun hcon => hG ((hiff J hJ).1 hcon).1)]
    ring

/-! ### The Class-2 bound -/

set_option linter.unusedSectionVars false in
/-- The trace bound at `A_𝒫 = ℬ ∪ {k^⋆}`: `A_𝒫` is a proper subset of `e_γ` or `e_{γ'}`, and
the other factor is bounded through `‖V ⊠_A V‖_F ≤ tot`. -/
theorem clsCutTot (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y -> x = y)
    {γ γ' : Γ} {Bee : Finset K} (hprop : Bee ⊂ lev γ ∨ Bee ⊂ lev γ')
    {cutmax totmax : Real} (hcutnn : 0 <= cutmax)
    (hcutA : ∀ (g : Γ) (Bs : Finset K), Bs ⊂ lev g ->
      rectFrobNorm (Matrix.of (levMat lev pt Bs g (arr g)) *
        (Matrix.of (levMat lev pt Bs g (arr g)))ᵀ) <= cutmax)
    (htot : ∀ g : Γ, rectFrobSq (arr g) <= totmax)
    (Bs : Finset K) (hBs : Bs ⊆ Bee) :
    rectFrobNorm (Matrix.of (levMat lev pt Bs γ (arr γ)) *
        (Matrix.of (levMat lev pt Bs γ (arr γ)))ᵀ) *
      rectFrobNorm (Matrix.of (levMat lev pt Bs γ' (arr γ')) *
        (Matrix.of (levMat lev pt Bs γ' (arr γ')))ᵀ)
      <= cutmax * totmax := by
  have htotγ : rectFrobNorm (Matrix.of (levMat lev pt Bs γ (arr γ)) *
      (Matrix.of (levMat lev pt Bs γ (arr γ)))ᵀ) <= totmax := by
    refine le_trans (rectFrobNorm_mul_transpose_self_le _) ?_
    rw [show rectFrobSq (Matrix.of (levMat lev pt Bs γ (arr γ)))
        = rectFrobSq (arr γ) from rectFrobSq_levMat (sites := sites) hsite hinj Bs γ (arr γ)]
    exact htot γ
  have htotγ2 : rectFrobNorm (Matrix.of (levMat lev pt Bs γ' (arr γ')) *
      (Matrix.of (levMat lev pt Bs γ' (arr γ')))ᵀ) <= totmax := by
    refine le_trans (rectFrobNorm_mul_transpose_self_le _) ?_
    rw [show rectFrobSq (Matrix.of (levMat lev pt Bs γ' (arr γ')))
        = rectFrobSq (arr γ') from rectFrobSq_levMat (sites := sites) hsite hinj Bs γ' (arr γ')]
    exact htot γ'
  have htotnn : (0:Real) <= totmax := le_trans (rectFrobNorm_nonneg _) htotγ
  rcases hprop with hp | hp
  · exact mul_le_mul (hcutA γ Bs (Finset.ssubset_of_subset_of_ssubset hBs hp)) htotγ2
      (rectFrobNorm_nonneg _) hcutnn
  · rw [mul_comm cutmax totmax]
    exact mul_le_mul htotγ (hcutA γ' Bs (Finset.ssubset_of_subset_of_ssubset hBs hp))
      (rectFrobNorm_nonneg _) htotnn

set_option linter.unusedSectionVars false in
/-- One Class-2 configuration, bounded. -/
theorem abs_clsFib_sum_le_ofCard (h : IsBasisSystem μ U ψ Rpos B₀) {M : ℕ}
    (hkey : ∀ c : K -> Option V, (keySites c).card <= M)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' -> k = k')
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y -> x = y)
    (γ γ' : Γ) (fib : Finset K × Finset K) {cutmax totmax : Real} (hcutnn : 0 <= cutmax)
    (hcutA : ∀ (g : Γ) (Bs : Finset K), Bs ⊂ lev g ->
      rectFrobNorm (Matrix.of (levMat lev pt Bs g (arr g)) *
        (Matrix.of (levMat lev pt Bs g (arr g)))ᵀ) <= cutmax)
    (htot : ∀ g : Γ, rectFrobSq (arr g) <= totmax) :
    |(Finset.univ.filter (fun q : (S γ × S γ') × (S γ × S γ') =>
        clsFib lev pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2 = fib)).sum
        (fun q => if IsClassTwo lev pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2 then
          unmCoef sites rIdx arr γ γ' q.1.1 q.1.2 * unmCoef sites rIdx arr γ γ' q.2.1 q.2.2 *
            multiMoment μ U ψ (quadSites sites γ γ' q.1.1 q.1.2 q.2.1 q.2.2)
              (quadIdx rIdx γ γ') else 0)|
      <= (2:Real) ^ Fintype.card K *
        (max B₀ 1 ^ (4 * M) * (4 * (cutmax * totmax))) := by
  classical
  obtain ⟨Bee, D⟩ := fib
  have htotnn : (0:Real) <= totmax := le_trans (rectFrobSq_nonneg _) (htot γ)
  have hMnn : (0:Real) <= max B₀ 1 ^ (4 * M) := by positivity
  have hRHSnn : (0:Real) <= (2:Real) ^ Fintype.card K *
      (max B₀ 1 ^ (4 * M) * (4 * (cutmax * totmax))) := by positivity
  rcases Finset.eq_empty_or_nonempty (Finset.univ.filter
      (fun q : (S γ × S γ') × (S γ × S γ') =>
        clsFib lev pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2 = (Bee, D))) with hEmp | ⟨q0, hq0⟩
  · rw [hEmp, Finset.sum_empty, abs_zero]
    exact hRHSnn
  rw [Finset.mem_filter] at hq0
  have hP0 : patAset lev pt γ γ' q0.1.1 q0.1.2 q0.2.1 q0.2.2 = Bee := congrArg Prod.fst hq0.2
  have hD0 : ((lev γ ∩ lev γ') \ patAset lev pt γ γ' q0.1.1 q0.1.2 q0.2.1 q0.2.2).filter
      (fun k => patAt pt γ γ' q0.1.1 q0.1.2 q0.2.1 q0.2.2 k = 2) = D := congrArg Prod.snd hq0.2
  have hBee : Bee ⊆ lev γ ∩ lev γ' := by
    rw [← hP0]
    exact Finset.filter_subset _ _
  have hD : D ⊆ (lev γ ∩ lev γ') \ Bee := by
    rw [← hD0, hP0]
    exact Finset.filter_subset _ _
  by_cases hC2 : Bee.Nonempty ∧ ¬ (lev γ = lev γ' ∧ Bee = lev γ)
  · -- the configuration really is Class 2
    have hprop : Bee ⊂ lev γ ∨ Bee ⊂ lev γ' := by
      have hsγ : Bee ⊆ lev γ := fun k hk => (Finset.mem_inter.1 (hBee hk)).1
      have hsγ2 : Bee ⊆ lev γ' := fun k hk => (Finset.mem_inter.1 (hBee hk)).2
      by_cases hEqγ : Bee = lev γ
      · refine Or.inr ?_
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨hsγ2, fun hc => hC2.2 ⟨?_, hEqγ⟩⟩
        rw [← hEqγ, ← hc]
      · exact Or.inl (Finset.ssubset_iff_subset_ne.2 ⟨hsγ, hEqγ⟩)
    have hIC : ∀ q : (S γ × S γ') × (S γ × S γ'),
        clsFib lev pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2 = (Bee, D) ->
        IsClassTwo lev pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2 := by
      intro q hq
      have hPq : patAset lev pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2 = Bee := congrArg Prod.fst hq
      rw [IsClassTwo, hPq]
      exact hC2
    -- rewrite the fibre sum as a full sum of the surrogate, then expand it
    have hEq1 : (Finset.univ.filter (fun q : (S γ × S γ') × (S γ × S γ') =>
          clsFib lev pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2 = (Bee, D))).sum
          (fun q => if IsClassTwo lev pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2 then
            unmCoef sites rIdx arr γ γ' q.1.1 q.1.2 * unmCoef sites rIdx arr γ γ' q.2.1 q.2.2 *
              multiMoment μ U ψ (quadSites sites γ γ' q.1.1 q.1.2 q.2.1 q.2.2)
                (quadIdx rIdx γ γ') else 0)
        = Finset.univ.sum fun q : (S γ × S γ') × (S γ × S γ') =>
            Bee.powerset.sum fun J => (-1:Real) ^ J.card *
              (if clsGood lev pt Bee J D γ γ' q.1.1 q.1.2 q.2.1 q.2.2 then
                clsF μ U ψ sites rIdx arr lev pt Bee γ γ' q.1.1 q.1.2 q.2.1 q.2.2 else 0) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← clsTgt_eq_sum (lev := lev) hBee hD q.1.1 q.1.2 q.2.1 q.2.2
        (clsF μ U ψ sites rIdx arr lev pt Bee γ γ' q.1.1 q.1.2 q.2.1 q.2.2),
        ← clsFib_term_eq h hsite hptc hpos hBee hD q.1.1 q.1.2 q.2.1 q.2.2]
      by_cases hf : clsFib lev pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2 = (Bee, D)
      · rw [if_pos hf, if_pos hf, if_pos (hIC q hf)]
      · rw [if_neg hf, if_neg hf]
    rw [hEq1, Finset.sum_comm]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hJ : ∀ J ∈ Bee.powerset,
        |Finset.univ.sum fun q : (S γ × S γ') × (S γ × S γ') => (-1:Real) ^ J.card *
            (if clsGood lev pt Bee J D γ γ' q.1.1 q.1.2 q.2.1 q.2.2 then
              clsF μ U ψ sites rIdx arr lev pt Bee γ γ' q.1.1 q.1.2 q.2.1 q.2.2 else 0)|
          <= max B₀ 1 ^ (4 * M) * (4 * (cutmax * totmax)) := by
      intro J hJmem
      rw [← Finset.mul_sum, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      refine le_trans (clsGood_sum_bound_ofCard h hkey (Finset.mem_powerset.1 hJmem) hBee hD) ?_
      refine mul_le_mul_of_nonneg_left ?_ hMnn
      refine le_trans (rectFrobSq_contrEntry_unm_le (arr := arr) hsite hptc
        (fun k hk => (Finset.mem_inter.1 (hBee (Finset.mem_sdiff.1 hk).1)).1)
        (fun k hk => (Finset.mem_inter.1 (hBee (Finset.mem_sdiff.1 hk).1)).2)) ?_
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:Real) <= 4)
      exact clsCutTot (sites := sites) hsite hinj hprop hcutnn hcutA htot (Bee \ J)
        (Finset.sdiff_subset)
    refine le_trans (Finset.sum_le_sum hJ) ?_
    rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have hcard : Bee.card <= Fintype.card K := Finset.card_le_univ Bee
    calc ((2 ^ Bee.card : ℕ) : Real) = (2:Real) ^ Bee.card := by push_cast; ring
      _ <= (2:Real) ^ Fintype.card K := by
          exact pow_le_pow_right₀ (by norm_num) hcard
  · -- not a Class-2 configuration: every term vanishes
    have hzero : ∀ q ∈ Finset.univ.filter (fun q : (S γ × S γ') × (S γ × S γ') =>
        clsFib lev pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2 = (Bee, D)),
        (if IsClassTwo lev pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2 then
          unmCoef sites rIdx arr γ γ' q.1.1 q.1.2 * unmCoef sites rIdx arr γ γ' q.2.1 q.2.2 *
            multiMoment μ U ψ (quadSites sites γ γ' q.1.1 q.1.2 q.2.1 q.2.2)
              (quadIdx rIdx γ γ') else 0) = 0 := by
      intro q hq
      rw [Finset.mem_filter] at hq
      have hPq : patAset lev pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2 = Bee := congrArg Prod.fst hq.2
      refine if_neg ?_
      rw [IsClassTwo, hPq]
      exact hC2
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, abs_zero]
    exact hRHSnn


set_option linter.unusedSectionVars false in
/-- One Class-2 configuration, bounded, with constant in terms of `|V|`. -/
theorem abs_clsFib_sum_le (h : IsBasisSystem μ U ψ Rpos B₀)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' -> k = k')
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y -> x = y)
    (γ γ' : Γ) (fib : Finset K × Finset K) {cutmax totmax : Real} (hcutnn : 0 <= cutmax)
    (hcutA : ∀ (g : Γ) (Bs : Finset K), Bs ⊂ lev g ->
      rectFrobNorm (Matrix.of (levMat lev pt Bs g (arr g)) *
        (Matrix.of (levMat lev pt Bs g (arr g)))ᵀ) <= cutmax)
    (htot : ∀ g : Γ, rectFrobSq (arr g) <= totmax) :
    |(Finset.univ.filter (fun q : (S γ × S γ') × (S γ × S γ') =>
        clsFib lev pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2 = fib)).sum
        (fun q => if IsClassTwo lev pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2 then
          unmCoef sites rIdx arr γ γ' q.1.1 q.1.2 * unmCoef sites rIdx arr γ γ' q.2.1 q.2.2 *
            multiMoment μ U ψ (quadSites sites γ γ' q.1.1 q.1.2 q.2.1 q.2.2)
              (quadIdx rIdx γ γ') else 0)|
      <= (2:Real) ^ Fintype.card K *
        (max B₀ 1 ^ (4 * Fintype.card V) * (4 * (cutmax * totmax))) := by
  apply abs_clsFib_sum_le_ofCard (M := Fintype.card V) <;>
    first
      | assumption
      | exact fun _ _ => Finset.card_le_univ _
      | exact fun _ => Finset.card_le_univ _
set_option linter.unusedSectionVars false in
/-- **The Class-2 bound.** `|classTwoSum| ≤ 4·8^{|K|}max(B_0,1)^{4M}·cut·tot`. -/
theorem abs_classTwoSum_le_ofCard (h : IsBasisSystem μ U ψ Rpos B₀) {M : ℕ}
    (hkey : ∀ c : K -> Option V, (keySites c).card <= M)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' -> k = k')
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y -> x = y)
    (γ γ' : Γ) {cutmax totmax : Real} (hcutnn : 0 <= cutmax)
    (hcutA : ∀ (g : Γ) (Bs : Finset K), Bs ⊂ lev g ->
      rectFrobNorm (Matrix.of (levMat lev pt Bs g (arr g)) *
        (Matrix.of (levMat lev pt Bs g (arr g)))ᵀ) <= cutmax)
    (htot : ∀ g : Γ, rectFrobSq (arr g) <= totmax) :
    |classTwoSum μ U ψ sites rIdx arr lev pt γ γ'|
      <= (4 * (2:Real) ^ Fintype.card K * (2:Real) ^ Fintype.card K * (2:Real) ^ Fintype.card K *
          max B₀ 1 ^ (4 * M)) * (cutmax * totmax) := by
  classical
  have hflat : classTwoSum μ U ψ sites rIdx arr lev pt γ γ'
      = Finset.univ.sum fun q : (S γ × S γ') × (S γ × S γ') =>
          (if IsClassTwo lev pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2 then
            unmCoef sites rIdx arr γ γ' q.1.1 q.1.2 * unmCoef sites rIdx arr γ γ' q.2.1 q.2.2 *
              multiMoment μ U ψ (quadSites sites γ γ' q.1.1 q.1.2 q.2.1 q.2.2)
                (quadIdx rIdx γ γ') else 0) := by
    simp only [classTwoSum, Fintype.sum_prod_type]
  rw [hflat, ← Finset.sum_fiberwise Finset.univ
    (fun q : (S γ × S γ') × (S γ × S γ') => clsFib lev pt γ γ' q.1.1 q.1.2 q.2.1 q.2.2) _]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun fib _ =>
    abs_clsFib_sum_le_ofCard h hkey hsite hptc hpos hinj γ γ' fib hcutnn hcutA htot) ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Fintype.card_finset]
  push_cast
  have hMnn : (0:Real) <= max B₀ 1 ^ (4 * M) := by positivity
  have htotnn : (0:Real) <= totmax := le_trans (rectFrobSq_nonneg _) (htot γ)
  have hct : (0:Real) <= cutmax * totmax := mul_nonneg hcutnn htotnn
  nlinarith [pow_nonneg (by norm_num : (0:Real) <= 2) (Fintype.card K), hMnn, hct,
    mul_nonneg (pow_nonneg (by norm_num : (0:Real) <= 2) (Fintype.card K))
      (pow_nonneg (by norm_num : (0:Real) <= 2) (Fintype.card K))]

set_option linter.unusedSectionVars false in
/-- **The Class-2 bound**, with constant in terms of `|V|`. -/
theorem abs_classTwoSum_le (h : IsBasisSystem μ U ψ Rpos B₀)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' -> k = k')
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y -> x = y)
    (γ γ' : Γ) {cutmax totmax : Real} (hcutnn : 0 <= cutmax)
    (hcutA : ∀ (g : Γ) (Bs : Finset K), Bs ⊂ lev g ->
      rectFrobNorm (Matrix.of (levMat lev pt Bs g (arr g)) *
        (Matrix.of (levMat lev pt Bs g (arr g)))ᵀ) <= cutmax)
    (htot : ∀ g : Γ, rectFrobSq (arr g) <= totmax) :
    |classTwoSum μ U ψ sites rIdx arr lev pt γ γ'|
      <= (4 * (2:Real) ^ Fintype.card K * (2:Real) ^ Fintype.card K * (2:Real) ^ Fintype.card K *
          max B₀ 1 ^ (4 * Fintype.card V)) * (cutmax * totmax) := by
  apply abs_classTwoSum_le_ofCard (M := Fintype.card V) <;>
    first
      | assumption
      | exact fun _ _ => Finset.card_le_univ _
      | exact fun _ => Finset.card_le_univ _

/-! ### The unmatched part at general level size, unconditionally -/

set_option linter.unusedSectionVars false in
/-- `𝔼[(Ξᵘ_{γγ'})²] ≤ C(M,B_0)·cut·tot` at general level size. -/
theorem integral_sq_unmatchedPart_le_general_ofCard (h : IsBasisSystem μ U ψ Rpos B₀)
    {M : ℕ}
    (hlev : ∀ (g : Γ) (x : S g), (sites g x).card ≤ M)
    (hkey : ∀ c : K -> Option V, (keySites c).card <= M)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' -> k = k')
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y -> x = y)
    (γ γ' : Γ) {cutmax totmax : Real} (hcutnn : 0 <= cutmax)
    (hcutA : ∀ (g : Γ) (Bs : Finset K), Bs ⊂ lev g ->
      rectFrobNorm (Matrix.of (levMat lev pt Bs g (arr g)) *
        (Matrix.of (levMat lev pt Bs g (arr g)))ᵀ) <= cutmax)
    (htot : ∀ g : Γ, rectFrobSq (arr g) <= totmax) :
    ∫ ω, (unmatchedPart U ψ sites rIdx arr tag γ γ' ω) ^ 2 ∂μ
      <= (4:Real) ^ Fintype.card K * max B₀ 1 ^ (4 * M) *
          rectFrobSq (Matrix.of (arr γ) * (Matrix.of (arr γ'))ᵀ)
        + (4 * (2:Real) ^ Fintype.card K * (2:Real) ^ Fintype.card K *
            (2:Real) ^ Fintype.card K * max B₀ 1 ^ (4 * M)) * (cutmax * totmax) :=
  integral_sq_unmatchedPart_le_of_classTwo_ofCard h hlev hsite hptc hpos hinj γ γ'
    (abs_classTwoSum_le_ofCard h hkey hsite hptc hpos hinj γ γ' hcutnn hcutA htot)


set_option linter.unusedSectionVars false in
/-- `𝔼[(Ξᵘ_{γγ'})²] ≤ C·cut·tot` at general level size, with constant in terms of `|V|`. -/
theorem integral_sq_unmatchedPart_le_general (h : IsBasisSystem μ U ψ Rpos B₀)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' -> k = k')
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y -> x = y)
    (γ γ' : Γ) {cutmax totmax : Real} (hcutnn : 0 <= cutmax)
    (hcutA : ∀ (g : Γ) (Bs : Finset K), Bs ⊂ lev g ->
      rectFrobNorm (Matrix.of (levMat lev pt Bs g (arr g)) *
        (Matrix.of (levMat lev pt Bs g (arr g)))ᵀ) <= cutmax)
    (htot : ∀ g : Γ, rectFrobSq (arr g) <= totmax) :
    ∫ ω, (unmatchedPart U ψ sites rIdx arr tag γ γ' ω) ^ 2 ∂μ
      <= (4:Real) ^ Fintype.card K * max B₀ 1 ^ (4 * Fintype.card V) *
          rectFrobSq (Matrix.of (arr γ) * (Matrix.of (arr γ'))ᵀ)
        + (4 * (2:Real) ^ Fintype.card K * (2:Real) ^ Fintype.card K *
            (2:Real) ^ Fintype.card K * max B₀ 1 ^ (4 * Fintype.card V)) * (cutmax * totmax) := by
  apply integral_sq_unmatchedPart_le_general_ofCard (M := Fintype.card V) <;>
    first
      | assumption
      | exact fun _ _ => Finset.card_le_univ _
      | exact fun _ => Finset.card_le_univ _

set_option linter.unusedSectionVars false in
/-- The same with constant in terms of `|K|`; the level bounds follow from `hsite`. -/
theorem integral_sq_unmatchedPart_le_general_uniform (h : IsBasisSystem μ U ψ Rpos B₀)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' -> k = k')
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y -> x = y)
    (γ γ' : Γ) {cutmax totmax : Real} (hcutnn : 0 <= cutmax)
    (hcutA : ∀ (g : Γ) (Bs : Finset K), Bs ⊂ lev g ->
      rectFrobNorm (Matrix.of (levMat lev pt Bs g (arr g)) *
        (Matrix.of (levMat lev pt Bs g (arr g)))ᵀ) <= cutmax)
    (htot : ∀ g : Γ, rectFrobSq (arr g) <= totmax) :
    ∫ ω, (unmatchedPart U ψ sites rIdx arr tag γ γ' ω) ^ 2 ∂μ
      <= (4:Real) ^ Fintype.card K * max B₀ 1 ^ (4 * Fintype.card K) *
          rectFrobSq (Matrix.of (arr γ) * (Matrix.of (arr γ'))ᵀ)
        + (4 * (2:Real) ^ Fintype.card K * (2:Real) ^ Fintype.card K *
            (2:Real) ^ Fintype.card K * max B₀ 1 ^ (4 * Fintype.card K)) * (cutmax * totmax) :=
  integral_sq_unmatchedPart_le_general_ofCard h (card_sites_le_card_K hsite)
    card_keySites_le hsite hptc hpos hinj γ γ' hcutnn hcutA htot
set_option linter.unusedSectionVars false in
/-- **Lemma SM.C.3(b)** at general level size, with the matched-part bound `hstep2` as a
hypothesis. -/
theorem concentration_clause_b_general_ofCard [Fintype Γ] [DecidableEq Γ]
    (h : IsBasisSystem μ U ψ Rpos B₀) {M : ℕ}
    (hlev : ∀ (g : Γ) (x : S g), (sites g x).card ≤ M)
    (hkey : ∀ c : K -> Option V, (keySites c).card <= M)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' -> k = k')
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y -> x = y)
    (hsep : ∀ (g g' : Γ) (x : S g) (y : S g'), tag g = tag g' -> sites g x = sites g' y ->
      (∀ w ∈ sites g x, rIdx g w = rIdx g' w) -> g = g')
    {lam : Γ -> Real} (hlam : Finset.univ.sum (fun γ => lam γ ^ 2) <= 1)
    {Cst cutmax totmax : Real} (hCst : 0 <= Cst)
    (hcut : ∀ γ : Γ, rectFrobNorm (Matrix.of (arr γ) * (Matrix.of (arr γ))ᵀ) <= cutmax)
    (hcutA : ∀ (g : Γ) (Bs : Finset K), Bs ⊂ lev g ->
      rectFrobNorm (Matrix.of (levMat lev pt Bs g (arr g)) *
        (Matrix.of (levMat lev pt Bs g (arr g)))ᵀ) <= cutmax)
    (htot : ∀ γ : Γ, rectFrobSq (arr γ) <= totmax)
    (hstep2 : ∀ γ : Γ, variance (matchedPart U ψ sites rIdx arr γ) μ <= Cst * (cutmax * totmax)) :
    variance (fun ω => Finset.univ.sum fun γ : Γ => Finset.univ.sum fun γ' : Γ =>
        lam γ * lam γ' * cvarEntry U ψ sites rIdx arr tag γ γ' ω) μ
      <= 4 * (Fintype.card Γ : Real) ^ 2 *
          (2 * (Cst + 4 * (2:Real) ^ Fintype.card K * (2:Real) ^ Fintype.card K *
              (2:Real) ^ Fintype.card K * max B₀ 1 ^ (4 * M)) +
            (4:Real) ^ Fintype.card K * max B₀ 1 ^ (4 * M)) *
          (cutmax * totmax) := by
  classical
  have hCcls : (0:Real) <= 4 * (2:Real) ^ Fintype.card K * (2:Real) ^ Fintype.card K *
      (2:Real) ^ Fintype.card K * max B₀ 1 ^ (4 * M) := by positivity
  refine concentration_clause_b_general_of_classTwo_ofCard h hlev hsite hptc hpos hinj hsep hlam
    (by linarith : (0:Real) <= Cst + 4 * (2:Real) ^ Fintype.card K * (2:Real) ^ Fintype.card K *
      (2:Real) ^ Fintype.card K * max B₀ 1 ^ (4 * M)) hcut htot ?_ ?_
  · intro γ
    have hnn : (0:Real) <= cutmax * totmax := by
      have h1 : (0:Real) <= cutmax := le_trans (rectFrobNorm_nonneg _) (hcut γ)
      have h2 : (0:Real) <= totmax := le_trans (rectFrobSq_nonneg _) (htot γ)
      exact mul_nonneg h1 h2
    nlinarith [hstep2 γ]
  · intro γ γ'
    have hcutnn : (0:Real) <= cutmax := le_trans (rectFrobNorm_nonneg _) (hcut γ)
    have hnn : (0:Real) <= cutmax * totmax := by
      have h2 : (0:Real) <= totmax := le_trans (rectFrobSq_nonneg _) (htot γ)
      exact mul_nonneg hcutnn h2
    refine le_trans (abs_classTwoSum_le_ofCard h hkey hsite hptc hpos hinj γ γ' hcutnn hcutA htot) ?_
    nlinarith

set_option linter.unusedSectionVars false in
/-- **Lemma SM.C.3(b)** at general level size with `hstep2` as a hypothesis, with constant in
terms of `|V|`; see `concentration_clause_b_general_uniform`. -/
theorem concentration_clause_b_general [Fintype Γ] [DecidableEq Γ]
    (h : IsBasisSystem μ U ψ Rpos B₀)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' -> k = k')
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y -> x = y)
    (hsep : ∀ (g g' : Γ) (x : S g) (y : S g'), tag g = tag g' -> sites g x = sites g' y ->
      (∀ w ∈ sites g x, rIdx g w = rIdx g' w) -> g = g')
    {lam : Γ -> Real} (hlam : Finset.univ.sum (fun γ => lam γ ^ 2) <= 1)
    {Cst cutmax totmax : Real} (hCst : 0 <= Cst)
    (hcut : ∀ γ : Γ, rectFrobNorm (Matrix.of (arr γ) * (Matrix.of (arr γ))ᵀ) <= cutmax)
    (hcutA : ∀ (g : Γ) (Bs : Finset K), Bs ⊂ lev g ->
      rectFrobNorm (Matrix.of (levMat lev pt Bs g (arr g)) *
        (Matrix.of (levMat lev pt Bs g (arr g)))ᵀ) <= cutmax)
    (htot : ∀ γ : Γ, rectFrobSq (arr γ) <= totmax)
    (hstep2 : ∀ γ : Γ, variance (matchedPart U ψ sites rIdx arr γ) μ <= Cst * (cutmax * totmax)) :
    variance (fun ω => Finset.univ.sum fun γ : Γ => Finset.univ.sum fun γ' : Γ =>
        lam γ * lam γ' * cvarEntry U ψ sites rIdx arr tag γ γ' ω) μ
      <= 4 * (Fintype.card Γ : Real) ^ 2 *
          (2 * (Cst + 4 * (2:Real) ^ Fintype.card K * (2:Real) ^ Fintype.card K *
              (2:Real) ^ Fintype.card K * max B₀ 1 ^ (4 * Fintype.card V)) +
            (4:Real) ^ Fintype.card K * max B₀ 1 ^ (4 * Fintype.card V)) *
          (cutmax * totmax) := by
  apply concentration_clause_b_general_ofCard (M := Fintype.card V) <;>
    first
      | assumption
      | exact fun _ _ => Finset.card_le_univ _
      | exact fun _ => Finset.card_le_univ _

set_option linter.unusedSectionVars false in
/-- The same with `max(B_0,1)^{4|K|}` in place of `max(B_0,1)^{4|V|}`. -/
theorem concentration_clause_b_general_uniform [Fintype Γ] [DecidableEq Γ]
    (h : IsBasisSystem μ U ψ Rpos B₀)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' -> k = k')
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y -> x = y)
    (hsep : ∀ (g g' : Γ) (x : S g) (y : S g'), tag g = tag g' -> sites g x = sites g' y ->
      (∀ w ∈ sites g x, rIdx g w = rIdx g' w) -> g = g')
    {lam : Γ -> Real} (hlam : Finset.univ.sum (fun γ => lam γ ^ 2) <= 1)
    {Cst cutmax totmax : Real} (hCst : 0 <= Cst)
    (hcut : ∀ γ : Γ, rectFrobNorm (Matrix.of (arr γ) * (Matrix.of (arr γ))ᵀ) <= cutmax)
    (hcutA : ∀ (g : Γ) (Bs : Finset K), Bs ⊂ lev g ->
      rectFrobNorm (Matrix.of (levMat lev pt Bs g (arr g)) *
        (Matrix.of (levMat lev pt Bs g (arr g)))ᵀ) <= cutmax)
    (htot : ∀ γ : Γ, rectFrobSq (arr γ) <= totmax)
    (hstep2 : ∀ γ : Γ, variance (matchedPart U ψ sites rIdx arr γ) μ <= Cst * (cutmax * totmax)) :
    variance (fun ω => Finset.univ.sum fun γ : Γ => Finset.univ.sum fun γ' : Γ =>
        lam γ * lam γ' * cvarEntry U ψ sites rIdx arr tag γ γ' ω) μ
      <= 4 * (Fintype.card Γ : Real) ^ 2 *
          (2 * (Cst + 4 * (2:Real) ^ Fintype.card K * (2:Real) ^ Fintype.card K *
              (2:Real) ^ Fintype.card K * max B₀ 1 ^ (4 * Fintype.card K)) +
            (4:Real) ^ Fintype.card K * max B₀ 1 ^ (4 * Fintype.card K)) *
          (cutmax * totmax) :=
  concentration_clause_b_general_ofCard h (card_sites_le_card_K hsite) card_keySites_le
    hsite hptc hpos hinj hsep hlam hCst hcut hcutA htot hstep2

end GeneralDischarge

end GeneralSites

/-! ### The fibre-sum bound at general level size

With `A = {k}`, the diagonal entries of `F^γ_{{k}}(F^γ_{{k}})'` are the fibre sums
`Σ^{(γ,k)}_j = ∑_{t : t_k = j} v^{(γ)2}_t`, so `∑_j(Σ^{(γ,k)}_j)² ≤ ‖V ⊠_{{k}} V‖_F² ≤ cut(γ)²`.
The matricization used is `levMat` at `Bs = (lev γ).erase k`, transposed, so that the index `I`
sits on the column side. The hypothesis `hptf` says that a site of coordinate `k ∈ lev g` lies in
`𝒩_k`. -/

section StepTwoClosed

variable {K : Type*} [Fintype K] [DecidableEq K] {N : K → Type*}
  [∀ k, Fintype (N k)] [∀ k, DecidableEq (N k)]
variable {Γ : Type*} {S : Γ → Type*} [∀ γ, Fintype (S γ)] {I : Type*} [Fintype I]
variable {U : Site K N → Ω → ℝ} {ψ : R → ℝ → ℝ} {Rpos : Set R} {B₀ : ℝ}
variable {sites : ∀ γ, S γ → Finset (Site K N)} {rIdx : Γ → Site K N → R}
variable {arr : ∀ γ, S γ → I → ℝ}
variable {lev : Γ → Finset K} {pt : ∀ γ, S γ → K → Site K N}

/-- The column key of the site `⟨k,j⟩` at the contraction set `(lev γ).erase k`. -/
def siteKey (k : K) (j : N k) : K → Option (Site K N) :=
  fun k' => if k' = k then some (⟨k, j⟩ : Site K N) else none

set_option linter.unusedSectionVars false in
theorem siteKey_injective (k : K) : Function.Injective (siteKey (N := N) k) := by
  intro j j' hjj
  have h := congrFun hjj k
  simp only [siteKey] at h
  have h2 : (⟨k, j⟩ : Site K N) = ⟨k, j'⟩ := Option.some.inj h
  simpa using h2

set_option linter.unusedSectionVars false in
/-- At `Bs = e_γ ∖ {k}` the column key is the single `k`-coordinate. -/
theorem cKey_erase (γ : Γ) {k : K} (hk : k ∈ lev γ) (s : S γ) :
    cKey lev pt ((lev γ).erase k) γ s
      = fun k' => if k' = k then some (pt γ s k) else none := by
  classical
  have hsd : lev γ \ (lev γ).erase k = {k} := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, h2⟩
      by_contra hne
      exact h2 ⟨hne, hx⟩
    · rintro rfl
      exact ⟨hk, fun h2 => h2.1 rfl⟩
  funext k'
  simp only [cKey, hsd, Finset.mem_singleton]
  by_cases h : k' = k
  · subst h; simp
  · simp [h]

set_option linter.unusedSectionVars false in
/-- `⟨k,j⟩ ∈ sites γ s` exactly when the column key of `s` at `(lev γ).erase k` is
`siteKey k j`. -/
theorem cKey_erase_eq_siteKey_iff
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptf : ∀ (g : Γ) (x : S g), ∀ k ∈ lev g, (pt g x k).1 = k)
    (γ : Γ) {k : K} (hk : k ∈ lev γ) (s : S γ) (j : N k) :
    cKey lev pt ((lev γ).erase k) γ s = siteKey k j
      ↔ (⟨k, j⟩ : Site K N) ∈ sites γ s := by
  classical
  have hpt : pt γ s k = (⟨k, j⟩ : Site K N) ↔ (⟨k, j⟩ : Site K N) ∈ sites γ s := by
    constructor
    · intro hEq
      rw [hsite γ s, ← hEq]
      exact Finset.mem_image_of_mem _ hk
    · intro hmem
      rw [hsite γ s, Finset.mem_image] at hmem
      obtain ⟨k', hk', hEq⟩ := hmem
      have hkk : k' = k := by
        have h1 := hptf γ s k' hk'
        rw [hEq] at h1
        exact h1.symm
      subst hkk
      exact hEq
  rw [← hpt, cKey_erase (lev := lev) (pt := pt) γ hk s]
  constructor
  · intro hc
    have hval := congrFun hc k
    simp only [siteKey] at hval
    exact Option.some.inj hval
  · intro hc
    funext k'
    simp only [siteKey]
    by_cases h : k' = k
    · subst h; simp [hc]
    · simp [h]

set_option linter.unusedSectionVars false in
/-- Off the level no site of coordinate `k` lies in a site set. -/
theorem notMem_sites_of_notMem_lev
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptf : ∀ (g : Γ) (x : S g), ∀ k ∈ lev g, (pt g x k).1 = k)
    (γ : Γ) {k : K} (hk : k ∉ lev γ) (s : S γ) (j : N k) :
    (⟨k, j⟩ : Site K N) ∉ sites γ s := by
  classical
  intro hmem
  rw [hsite γ s, Finset.mem_image] at hmem
  obtain ⟨k', hk', hEq⟩ := hmem
  have h1 := hptf γ s k' hk'
  rw [hEq] at h1
  have h2 : k = k' := h1
  subst h2
  exact hk hk'

set_option linter.unusedSectionVars false in
/-- The diagonal entries of `F^γ_A(F^γ_A)'`, where `F^γ_A = (levMat lev pt Bs γ (arr γ))'` and
`A = e_γ ∖ Bs`: each is the sum of `gramDiag` over the sub-tuples with the given `A`-key. -/
theorem levGram_diag (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y → x = y)
    (Bs : Finset K) (γ : Γ) (v : K → Option (Site K N)) :
    ((Matrix.of (levMat lev pt Bs γ (arr γ)))ᵀ * Matrix.of (levMat lev pt Bs γ (arr γ))) v v
      = ∑ s ∈ Finset.univ.filter (fun s => cKey lev pt Bs γ s = v), gramDiag arr γ s := by
  classical
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  have hsq : ∀ p : (K → Option (Site K N)) × I,
      levMat lev pt Bs γ (arr γ) p v * levMat lev pt Bs γ (arr γ) p v
        = ∑ x ∈ Finset.univ.filter
            (fun x => bKey pt Bs γ x = p.1 ∧ cKey lev pt Bs γ x = v), (arr γ x p.2) ^ 2 := by
    intro p
    rw [← sq, show p = (p.1, p.2) from rfl, levMat_apply]
    exact sq_sum_of_subsingleton _ _ (subsingleton_key_fiber (sites := sites) hsite hinj)
  rw [Finset.sum_congr rfl fun p _ => hsq p, Fintype.sum_prod_type]
  have hswap : ∀ r : K → Option (Site K N),
      (∑ i : I, ∑ x ∈ Finset.univ.filter
        (fun x => bKey pt Bs γ x = r ∧ cKey lev pt Bs γ x = v), (arr γ x i) ^ 2)
        = ∑ x ∈ (Finset.univ.filter (fun x : S γ => cKey lev pt Bs γ x = v)).filter
            (fun x => bKey pt Bs γ x = r), gramDiag arr γ x := by
    intro r
    rw [Finset.sum_comm]
    have hset : Finset.univ.filter
        (fun x : S γ => bKey pt Bs γ x = r ∧ cKey lev pt Bs γ x = v)
        = (Finset.univ.filter (fun x : S γ => cKey lev pt Bs γ x = v)).filter
            (fun x => bKey pt Bs γ x = r) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [hset]
    rfl
  rw [Finset.sum_congr rfl fun r _ => hswap r]
  exact Finset.sum_fiberwise _ _ _

set_option linter.unusedSectionVars false in
/-- **The fibre-sum bound.** `∑_j(Σ^{(γ,k)}_j)² ≤ bnd` for every `k`, from the contraction
bound at `Bs = e_γ ∖ {k}` supplied by `hcutA`. -/
theorem sum_sq_gramDiag_fiber_le
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y → x = y)
    (hptf : ∀ (g : Γ) (x : S g), ∀ k ∈ lev g, (pt g x k).1 = k)
    (γ : Γ) {bnd : ℝ} (hbnn : 0 ≤ bnd)
    (hcutA : ∀ Bs : Finset K, Bs ⊂ lev γ →
      rectFrobSq (Matrix.of (levMat lev pt Bs γ (arr γ)) *
        (Matrix.of (levMat lev pt Bs γ (arr γ)))ᵀ) ≤ bnd)
    (k : K) :
    ∑ j : N k, (∑ s ∈ Finset.univ.filter (fun s => (⟨k, j⟩ : Site K N) ∈ sites γ s),
      gramDiag arr γ s) ^ 2 ≤ bnd := by
  classical
  by_cases hk : k ∈ lev γ
  · set Bs := (lev γ).erase k with hBsdef
    set F := Matrix.of (levMat lev pt Bs γ (arr γ)) with hFdef
    set Sg : (K → Option (Site K N)) → ℝ :=
      fun v => ∑ s ∈ Finset.univ.filter (fun s => cKey lev pt Bs γ s = v), gramDiag arr γ s
      with hSgdef
    have hdiag : ∀ v : K → Option (Site K N), (Fᵀ * (Fᵀ)ᵀ) v v = Sg v := by
      intro v
      rw [Matrix.transpose_transpose]
      exact levGram_diag (sites := sites) hsite hinj Bs γ v
    have hstep := sum_sq_of_diag_le Fᵀ Sg hdiag
    have hfrob : rectFrobNorm (Fᵀ * (Fᵀ)ᵀ) ^ 2 = rectFrobSq (F * Fᵀ) := by
      rw [rectFrobNorm_sq, Matrix.transpose_transpose, ← rectFrobSq_mul_transpose_comm]
    have himg : ∑ v ∈ (Finset.univ : Finset (N k)).image (siteKey (N := N) k), (Sg v) ^ 2
        = ∑ j : N k, (Sg (siteKey k j)) ^ 2 :=
      Finset.sum_image (fun x _ y _ hxy => siteKey_injective k hxy)
    have hle1 : ∑ j : N k, (Sg (siteKey k j)) ^ 2
        ≤ ∑ v : K → Option (Site K N), (Sg v) ^ 2 := by
      rw [← himg]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => sq_nonneg _)
    have hSgeq : ∀ j : N k, Sg (siteKey k j)
        = ∑ s ∈ Finset.univ.filter (fun s => (⟨k, j⟩ : Site K N) ∈ sites γ s),
            gramDiag arr γ s := by
      intro j
      simp only [hSgdef]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact cKey_erase_eq_siteKey_iff hsite hptf γ hk s j
    calc ∑ j : N k, (∑ s ∈ Finset.univ.filter
          (fun s => (⟨k, j⟩ : Site K N) ∈ sites γ s), gramDiag arr γ s) ^ 2
        = ∑ j : N k, (Sg (siteKey k j)) ^ 2 :=
          Finset.sum_congr rfl fun j _ => by rw [hSgeq j]
      _ ≤ ∑ v : K → Option (Site K N), (Sg v) ^ 2 := hle1
      _ ≤ rectFrobSq (F * Fᵀ) := by rw [← hfrob]; exact hstep
      _ ≤ bnd := hcutA Bs (Finset.erase_ssubset hk)
  · have hempty : ∀ j : N k,
        Finset.univ.filter (fun s : S γ => (⟨k, j⟩ : Site K N) ∈ sites γ s) = ∅ := by
      intro j
      rw [Finset.filter_eq_empty_iff]
      intro s _
      exact notMem_sites_of_notMem_lev hsite hptf γ hk s j
    have hz : ∑ j : N k, (∑ s ∈ Finset.univ.filter
        (fun s => (⟨k, j⟩ : Site K N) ∈ sites γ s), gramDiag arr γ s) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hempty j, Finset.sum_empty]
      norm_num
    rw [hz]
    exact hbnn

set_option linter.unusedSectionVars false in
/-- `‖F_A F_A'‖_F² ≤ cut(γ)tot(γ)`, bounding one factor by `cut(γ)` and the other by
`tot(γ)`. -/
theorem rectFrobSq_levGram_le_cut_tot
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y → x = y)
    (γ : Γ) {cutγ totγ : ℝ} (hcutnn : 0 ≤ cutγ)
    (htotγ : rectFrobSq (arr γ) ≤ totγ) (Bs : Finset K)
    (hB : rectFrobNorm (Matrix.of (levMat lev pt Bs γ (arr γ)) *
        (Matrix.of (levMat lev pt Bs γ (arr γ)))ᵀ) ≤ cutγ) :
    rectFrobSq (Matrix.of (levMat lev pt Bs γ (arr γ)) *
        (Matrix.of (levMat lev pt Bs γ (arr γ)))ᵀ) ≤ cutγ * totγ := by
  have h2 : rectFrobNorm (Matrix.of (levMat lev pt Bs γ (arr γ)) *
      (Matrix.of (levMat lev pt Bs γ (arr γ)))ᵀ) ≤ totγ := by
    refine le_trans (rectFrobNorm_mul_transpose_self_le _) ?_
    have hz : rectFrobSq (Matrix.of (levMat lev pt Bs γ (arr γ))) = rectFrobSq (arr γ) :=
      rectFrobSq_levMat (sites := sites) hsite hinj Bs γ (arr γ)
    rw [hz]
    exact htotγ
  calc rectFrobSq (Matrix.of (levMat lev pt Bs γ (arr γ)) *
        (Matrix.of (levMat lev pt Bs γ (arr γ)))ᵀ)
      = rectFrobNorm (Matrix.of (levMat lev pt Bs γ (arr γ)) *
          (Matrix.of (levMat lev pt Bs γ (arr γ)))ᵀ) ^ 2 := (rectFrobNorm_sq _).symm
    _ = rectFrobNorm (Matrix.of (levMat lev pt Bs γ (arr γ)) *
          (Matrix.of (levMat lev pt Bs γ (arr γ)))ᵀ) *
        rectFrobNorm (Matrix.of (levMat lev pt Bs γ (arr γ)) *
          (Matrix.of (levMat lev pt Bs γ (arr γ)))ᵀ) := sq _
    _ ≤ cutγ * totγ := mul_le_mul hB h2 (rectFrobNorm_nonneg _) hcutnn

set_option linter.unusedSectionVars false in
/-- The matched-part bound from `hcutA` and the site model, when every site set has at most
`M` elements. -/
theorem variance_matchedPart_le_cutA_ofCard
    (h : IsBasisSystem μ U ψ Rpos B₀) {M : ℕ}
    (hlev : ∀ (g : Γ) (x : S g), (sites g x).card ≤ M)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y → x = y)
    (hptf : ∀ (g : Γ) (x : S g), ∀ k ∈ lev g, (pt g x k).1 = k)
    (γ : Γ) {cutγ : ℝ}
    (hcutA : ∀ Bs : Finset K, Bs ⊂ lev γ →
      rectFrobNorm (Matrix.of (levMat lev pt Bs γ (arr γ)) *
        (Matrix.of (levMat lev pt Bs γ (arr γ)))ᵀ) ≤ cutγ) :
    variance (matchedPart U ψ sites rIdx arr γ) μ
      ≤ ((max B₀ 1 ^ M) ^ 2) ^ 2
          * ((Fintype.card K : ℝ) * cutγ ^ 2) :=
  variance_matchedPart_le_bnd_ofCard (bnd := cutγ ^ 2) h hlev γ
    (sum_sq_gramDiag_fiber_le (bnd := cutγ ^ 2) hsite hinj hptf γ (sq_nonneg _)
      (fun Bs hBs => rectFrobSq_le_sq_of_rectFrobNorm_le _ (hcutA Bs hBs)))


set_option linter.unusedSectionVars false in
/-- The matched-part bound from `hcutA` and the site model. -/
theorem variance_matchedPart_le_cutA
    (h : IsBasisSystem μ U ψ Rpos B₀)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y → x = y)
    (hptf : ∀ (g : Γ) (x : S g), ∀ k ∈ lev g, (pt g x k).1 = k)
    (γ : Γ) {cutγ : ℝ}
    (hcutA : ∀ Bs : Finset K, Bs ⊂ lev γ →
      rectFrobNorm (Matrix.of (levMat lev pt Bs γ (arr γ)) *
        (Matrix.of (levMat lev pt Bs γ (arr γ)))ᵀ) ≤ cutγ) :
    variance (matchedPart U ψ sites rIdx arr γ) μ
      ≤ ((max B₀ 1 ^ Fintype.card (Site K N)) ^ 2) ^ 2
          * ((Fintype.card K : ℝ) * cutγ ^ 2) := by
  apply variance_matchedPart_le_cutA_ofCard (M := Fintype.card (Site K N)) <;>
    first
      | assumption
      | exact fun _ _ => Finset.card_le_univ _
      | exact fun _ => Finset.card_le_univ _
set_option linter.unusedSectionVars false in
/-- The same, in the `cut·tot` shape the assembly of clause (b) consumes. -/
theorem variance_matchedPart_le_cut_tot_ofCard
    (h : IsBasisSystem μ U ψ Rpos B₀) {M : ℕ}
    (hlev : ∀ (g : Γ) (x : S g), (sites g x).card ≤ M)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y → x = y)
    (hptf : ∀ (g : Γ) (x : S g), ∀ k ∈ lev g, (pt g x k).1 = k)
    (γ : Γ) {cutγ totγ : ℝ} (hcutnn : 0 ≤ cutγ) (htotnn : 0 ≤ totγ)
    (htotγ : rectFrobSq (arr γ) ≤ totγ)
    (hcutA : ∀ Bs : Finset K, Bs ⊂ lev γ →
      rectFrobNorm (Matrix.of (levMat lev pt Bs γ (arr γ)) *
        (Matrix.of (levMat lev pt Bs γ (arr γ)))ᵀ) ≤ cutγ) :
    variance (matchedPart U ψ sites rIdx arr γ) μ
      ≤ ((max B₀ 1 ^ M) ^ 2) ^ 2
          * ((Fintype.card K : ℝ) * (cutγ * totγ)) :=
  variance_matchedPart_le_bnd_ofCard (bnd := cutγ * totγ) h hlev γ
    (sum_sq_gramDiag_fiber_le (bnd := cutγ * totγ) hsite hinj hptf γ
      (mul_nonneg hcutnn htotnn)
      (fun Bs hBs => rectFrobSq_levGram_le_cut_tot (sites := sites) hsite hinj γ hcutnn htotγ Bs
        (hcutA Bs hBs)))


set_option linter.unusedSectionVars false in
/-- The same, in the `cut·tot` shape, with constant in terms of `|V|`. -/
theorem variance_matchedPart_le_cut_tot
    (h : IsBasisSystem μ U ψ Rpos B₀)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y → x = y)
    (hptf : ∀ (g : Γ) (x : S g), ∀ k ∈ lev g, (pt g x k).1 = k)
    (γ : Γ) {cutγ totγ : ℝ} (hcutnn : 0 ≤ cutγ) (htotnn : 0 ≤ totγ)
    (htotγ : rectFrobSq (arr γ) ≤ totγ)
    (hcutA : ∀ Bs : Finset K, Bs ⊂ lev γ →
      rectFrobNorm (Matrix.of (levMat lev pt Bs γ (arr γ)) *
        (Matrix.of (levMat lev pt Bs γ (arr γ)))ᵀ) ≤ cutγ) :
    variance (matchedPart U ψ sites rIdx arr γ) μ
      ≤ ((max B₀ 1 ^ Fintype.card (Site K N)) ^ 2) ^ 2
          * ((Fintype.card K : ℝ) * (cutγ * totγ)) := by
  apply variance_matchedPart_le_cut_tot_ofCard (M := Fintype.card (Site K N)) <;>
    first
      | assumption
      | exact fun _ _ => Finset.card_le_univ _
      | exact fun _ => Finset.card_le_univ _
set_option linter.unusedSectionVars false in
/-- **Lemma SM.C.3(b)** at general level size, with explicit constant, when every site set
and every key has at most `M` elements. `hptf` says a site of coordinate `k` lies in `𝒩_k`. -/
theorem concentration_clause_b_general_closed_ofCard [Fintype Γ] [DecidableEq Γ]
    {τ : Type*} [DecidableEq τ] {tag : Γ → τ}
    (h : IsBasisSystem μ U ψ Rpos B₀) {M : ℕ}
    (hlev : ∀ (g : Γ) (x : S g), (sites g x).card ≤ M)
    (hkey : ∀ c : K -> Option (Site K N), (keySites c).card <= M)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' → k = k')
    (hptf : ∀ (g : Γ) (x : S g), ∀ k ∈ lev g, (pt g x k).1 = k)
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y → x = y)
    (hsep : ∀ (g g' : Γ) (x : S g) (y : S g'), tag g = tag g' → sites g x = sites g' y →
      (∀ w ∈ sites g x, rIdx g w = rIdx g' w) → g = g')
    {lam : Γ → ℝ} (hlam : ∑ γ, lam γ ^ 2 ≤ 1)
    {cutmax totmax : ℝ}
    (hcut : ∀ γ : Γ, rectFrobNorm (Matrix.of (arr γ) * (Matrix.of (arr γ))ᵀ) ≤ cutmax)
    (hcutA : ∀ (g : Γ), ∀ Bs ⊂ lev g,
      rectFrobNorm (Matrix.of (levMat lev pt Bs g (arr g)) *
        (Matrix.of (levMat lev pt Bs g (arr g)))ᵀ) ≤ cutmax)
    (htot : ∀ γ : Γ, rectFrobSq (arr γ) ≤ totmax) :
    variance (fun ω => ∑ γ : Γ, ∑ γ' : Γ,
        lam γ * lam γ' * cvarEntry U ψ sites rIdx arr tag γ γ' ω) μ
      ≤ 4 * (Fintype.card Γ : ℝ) ^ 2 *
          (2 * (((max B₀ 1 ^ M) ^ 2) ^ 2 * (Fintype.card K : ℝ)
              + 4 * (2:ℝ) ^ Fintype.card K * (2:ℝ) ^ Fintype.card K * (2:ℝ) ^ Fintype.card K *
                max B₀ 1 ^ (4 * M)) +
            (4:ℝ) ^ Fintype.card K * max B₀ 1 ^ (4 * M)) *
          (cutmax * totmax) := by
  refine concentration_clause_b_general_ofCard
    (Cst := ((max B₀ 1 ^ M) ^ 2) ^ 2 * (Fintype.card K : ℝ))
    (cutmax := cutmax) (totmax := totmax)
    h hlev hkey hsite hptc hpos hinj hsep hlam (by positivity) hcut hcutA htot ?_
  intro γ
  have hcutnn : (0:ℝ) ≤ cutmax := le_trans (rectFrobNorm_nonneg _) (hcut γ)
  have htotnn : (0:ℝ) ≤ totmax := le_trans (rectFrobSq_nonneg _) (htot γ)
  have hb := variance_matchedPart_le_cut_tot_ofCard (rIdx := rIdx) h hlev hsite hinj hptf γ
    hcutnn htotnn
    (htot γ) (fun Bs hBs => hcutA γ Bs hBs)
  calc variance (matchedPart U ψ sites rIdx arr γ) μ
      ≤ ((max B₀ 1 ^ M) ^ 2) ^ 2 *
          ((Fintype.card K : ℝ) * (cutmax * totmax)) := hb
    _ = ((max B₀ 1 ^ M) ^ 2) ^ 2 * (Fintype.card K : ℝ) *
          (cutmax * totmax) := by ring

set_option linter.unusedSectionVars false in
/-- **Lemma SM.C.3(b)** at general level size, with constant in terms of `|V|`; see
`concentration_clause_b_general_closed_uniform`. -/
theorem concentration_clause_b_general_closed [Fintype Γ] [DecidableEq Γ]
    {τ : Type*} [DecidableEq τ] {tag : Γ → τ}
    (h : IsBasisSystem μ U ψ Rpos B₀)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' → k = k')
    (hptf : ∀ (g : Γ) (x : S g), ∀ k ∈ lev g, (pt g x k).1 = k)
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y → x = y)
    (hsep : ∀ (g g' : Γ) (x : S g) (y : S g'), tag g = tag g' → sites g x = sites g' y →
      (∀ w ∈ sites g x, rIdx g w = rIdx g' w) → g = g')
    {lam : Γ → ℝ} (hlam : ∑ γ, lam γ ^ 2 ≤ 1)
    {cutmax totmax : ℝ}
    (hcut : ∀ γ : Γ, rectFrobNorm (Matrix.of (arr γ) * (Matrix.of (arr γ))ᵀ) ≤ cutmax)
    (hcutA : ∀ (g : Γ), ∀ Bs ⊂ lev g,
      rectFrobNorm (Matrix.of (levMat lev pt Bs g (arr g)) *
        (Matrix.of (levMat lev pt Bs g (arr g)))ᵀ) ≤ cutmax)
    (htot : ∀ γ : Γ, rectFrobSq (arr γ) ≤ totmax) :
    variance (fun ω => ∑ γ : Γ, ∑ γ' : Γ,
        lam γ * lam γ' * cvarEntry U ψ sites rIdx arr tag γ γ' ω) μ
      ≤ 4 * (Fintype.card Γ : ℝ) ^ 2 *
          (2 * (((max B₀ 1 ^ Fintype.card (Site K N)) ^ 2) ^ 2 * (Fintype.card K : ℝ)
              + 4 * (2:ℝ) ^ Fintype.card K * (2:ℝ) ^ Fintype.card K * (2:ℝ) ^ Fintype.card K *
                max B₀ 1 ^ (4 * Fintype.card (Site K N))) +
            (4:ℝ) ^ Fintype.card K * max B₀ 1 ^ (4 * Fintype.card (Site K N))) *
          (cutmax * totmax) := by
  apply concentration_clause_b_general_closed_ofCard (M := Fintype.card (Site K N)) <;>
    first
      | assumption
      | exact fun _ _ => Finset.card_le_univ _
      | exact fun _ => Finset.card_le_univ _

set_option linter.unusedSectionVars false in
/-- **Lemma SM.C.3(b).** At general level size, with constant
`4|Γ|²(2(M·max(B_0,1)^{4M} + 4·8^M·max(B_0,1)^{4M}) + 4^M·max(B_0,1)^{4M})` at `M = |K|`, which
depends only on `B_0`, `|Γ|` and `M`. -/
theorem concentration_clause_b_general_closed_uniform [Fintype Γ] [DecidableEq Γ]
    {τ : Type*} [DecidableEq τ] {tag : Γ → τ}
    (h : IsBasisSystem μ U ψ Rpos B₀)
    (hsite : ∀ (g : Γ) (x : S g), sites g x = (lev g).image (pt g x))
    (hptc : ∀ (g g' : Γ) (x : S g) (y : S g') (k k' : K), pt g x k = pt g' y k' → k = k')
    (hptf : ∀ (g : Γ) (x : S g), ∀ k ∈ lev g, (pt g x k).1 = k)
    (hpos : ∀ (g : Γ) (x : S g), ∀ w ∈ sites g x, rIdx g w ∈ Rpos)
    (hinj : ∀ (g : Γ) (x y : S g), sites g x = sites g y → x = y)
    (hsep : ∀ (g g' : Γ) (x : S g) (y : S g'), tag g = tag g' → sites g x = sites g' y →
      (∀ w ∈ sites g x, rIdx g w = rIdx g' w) → g = g')
    {lam : Γ → ℝ} (hlam : ∑ γ, lam γ ^ 2 ≤ 1)
    {cutmax totmax : ℝ}
    (hcut : ∀ γ : Γ, rectFrobNorm (Matrix.of (arr γ) * (Matrix.of (arr γ))ᵀ) ≤ cutmax)
    (hcutA : ∀ (g : Γ), ∀ Bs ⊂ lev g,
      rectFrobNorm (Matrix.of (levMat lev pt Bs g (arr g)) *
        (Matrix.of (levMat lev pt Bs g (arr g)))ᵀ) ≤ cutmax)
    (htot : ∀ γ : Γ, rectFrobSq (arr γ) ≤ totmax) :
    variance (fun ω => ∑ γ : Γ, ∑ γ' : Γ,
        lam γ * lam γ' * cvarEntry U ψ sites rIdx arr tag γ γ' ω) μ
      ≤ 4 * (Fintype.card Γ : ℝ) ^ 2 *
          (2 * (((max B₀ 1 ^ Fintype.card K) ^ 2) ^ 2 * (Fintype.card K : ℝ)
              + 4 * (2:ℝ) ^ Fintype.card K * (2:ℝ) ^ Fintype.card K * (2:ℝ) ^ Fintype.card K *
                max B₀ 1 ^ (4 * Fintype.card K)) +
            (4:ℝ) ^ Fintype.card K * max B₀ 1 ^ (4 * Fintype.card K)) *
          (cutmax * totmax) :=
  concentration_clause_b_general_closed_ofCard h (card_sites_le_card_K hsite)
    card_keySites_le hsite hptc hptf hpos hinj hsep hlam hcut hcutA htot

end StepTwoClosed


/-! ### A model for clause (b)

The clause-(a) model with `λ_γ = 1/2`. The unmatched part `Ξᵘ_{01} = ψ_1(U_0)ψ_1(U_1)` takes the
values `±1` and the variance bounded is `1/4`. On a fair two-point law `(π^γ_s)² ≡ 1`, so the
matched part vanishes. -/

section WitnessB

open ClauseAWitness

namespace ClauseBWitness

/-- The coefficients of clause (b): `λ_γ = 1/2`, so `∑_γ λ_γ² = 1/2 ≤ 1`. -/
noncomputable def wlam : Fin 2 → ℝ := fun _ => 1 / 2

theorem wlam_sq_le : ∑ γ : Fin 2, wlam γ ^ 2 ≤ 1 := by
  simp [wlam]
  norm_num

/-- Every basis function of the witness system is a sign, so its square is `1`. -/
theorem wψ_sq (x : ℝ) : wψ 1 x ^ 2 = 1 := by
  simp only [wψ]
  split_ifs <;> norm_num

/-- `π^γ_s ω = ψ_1(U_γ(ω))`, a sign. -/
theorem wbasisProd_apply (γ : Fin 2) (s : Unit) (ω : Fin 2 → ℝ) :
    basisProd wU wψ wsites wrIdx γ s ω = wψ 1 (ω γ) := by
  simp [basisProd, wsites, wrIdx, wU]

theorem wbasisProd_sq (γ : Fin 2) (s : Unit) (ω : Fin 2 → ℝ) :
    basisProd wU wψ wsites wrIdx γ s ω ^ 2 = 1 := by
  rw [wbasisProd_apply]
  exact wψ_sq _

/-- On the two-sign model the matched part vanishes identically, since `(π^γ_s)² ≡ 1`. -/
theorem wmatchedPart_eq_zero (γ : Fin 2) :
    matchedPart wU wψ wsites wrIdx warr γ = fun _ => (0 : ℝ) := by
  funext ω
  simp [matchedPart, wbasisProd_sq]

theorem wmatched_variance (γ : Fin 2) :
    variance (matchedPart wU wψ wsites wrIdx warr γ) wμ ≤ 0 := by
  rw [wmatchedPart_eq_zero]
  exact le_of_eq (variance_const_fun 0)

theorem wIsMatched_iff (γ γ' : Fin 2) (s s' : Unit) :
    IsMatched wsites wrIdx γ γ' s s' ↔ γ = γ' := by
  constructor
  · rintro ⟨h1, -⟩
    exact Finset.singleton_inj.mp h1
  · rintro rfl
    exact ⟨rfl, fun _ _ => rfl⟩

/-- Off the diagonal the unmatched part is `ψ_1(U_0)ψ_1(U_1)`. -/
theorem wunmatchedPart_apply_ne {γ γ' : Fin 2} (hne : γ ≠ γ') (ω : Fin 2 → ℝ) :
    unmatchedPart wU wψ wsites wrIdx warr wtag γ γ' ω = wψ 1 (ω γ) * wψ 1 (ω γ') := by
  have hm : ¬ IsMatched wsites wrIdx γ γ' () () := fun hx => hne ((wIsMatched_iff γ γ' () ()).1 hx)
  have hg : gramEntry warr γ γ' () () = 1 := by simp [gramEntry, warr]
  simp [unmatchedPart, wtag, hm, hg, wbasisProd_apply]

theorem wunmatchedPart_sq_le (γ γ' : Fin 2) (ω : Fin 2 → ℝ) :
    (unmatchedPart wU wψ wsites wrIdx warr wtag γ γ' ω) ^ 2 ≤ 1 := by
  by_cases hg : γ = γ'
  · subst hg
    have hz : unmatchedPart wU wψ wsites wrIdx warr wtag γ γ ω = 0 := by
      have hm : IsMatched wsites wrIdx γ γ () () := (wIsMatched_iff γ γ () ()).2 rfl
      simp [unmatchedPart, wtag, hm]
    rw [hz]; norm_num
  · rw [wunmatchedPart_apply_ne hg, mul_pow, wψ_sq, wψ_sq]
    norm_num

theorem wunm (γ γ' : Fin 2) :
    ∫ ω, (unmatchedPart wU wψ wsites wrIdx warr wtag γ γ' ω) ^ 2 ∂wμ ≤ 1 :=
  integral_sq_le_of_bound (memLp_unmatchedPart wIsBasisSystem γ γ') (wunmatchedPart_sq_le γ γ')

/-- The statistic of clause (b) on this model: `∑_{γγ'}λ_γλ_{γ'}X_{γγ'} = ½ + ½ψ_1(U_0)ψ_1(U_1)`. -/
theorem wstat_apply (ω : Fin 2 → ℝ) :
    ∑ γ : Fin 2, ∑ γ' : Fin 2,
        wlam γ * wlam γ' * cvarEntry wU wψ wsites wrIdx warr wtag γ γ' ω
      = 1 / 2 + 1 / 2 * (wψ 1 (ω 0) * wψ 1 (ω 1)) := by
  have hcv : ∀ γ γ' : Fin 2, cvarEntry wU wψ wsites wrIdx warr wtag γ γ' ω
      = wψ 1 (ω γ) * wψ 1 (ω γ') := by
    intro γ γ'
    simp [cvarEntry, wtag, blockSum, warr, wbasisProd_apply]
  simp only [hcv, wlam, Fin.sum_univ_two]
  have h0 := wψ_sq (ω 0)
  have h1 := wψ_sq (ω 1)
  nlinarith [h0, h1]

/-- `𝔼[ψ_1(U_0)ψ_1(U_1)] = 0`, by the independence of the two signs. -/
theorem wintegral_prod : ∫ ω, wψ 1 (ω 0) * wψ 1 (ω 1) ∂wμ = 0 := by
  have hprod : ∀ ω : Fin 2 → ℝ,
      wψ 1 (ω 0) * wψ 1 (ω 1) = ∏ v ∈ (Finset.univ : Finset (Fin 2)), wψ 1 (wU v ω) := by
    intro ω
    rw [Fin.prod_univ_two]
    rfl
  simp only [hprod]
  rw [integral_prod_eq_prod_integral (g := fun _ v => wψ 1 v) wIsBasisSystem
    (fun _ => measurable_wψ 1)]
  refine Finset.prod_eq_zero (Finset.mem_univ 0) ?_
  exact wIsBasisSystem.integral_eq_zero 0 rfl

/-- The variance bounded by clause (b) is `1/4` on this model. -/
theorem wstat_variance :
    variance (fun ω => ∑ γ : Fin 2, ∑ γ' : Fin 2,
      wlam γ * wlam γ' * cvarEntry wU wψ wsites wrIdx warr wtag γ γ' ω) wμ = 1 / 4 := by
  have hY : Measurable (fun ω : Fin 2 → ℝ => wψ 1 (ω 0) * wψ 1 (ω 1)) :=
    ((measurable_wψ 1).comp (measurable_pi_apply 0)).mul
      ((measurable_wψ 1).comp (measurable_pi_apply 1))
  have hYb : ∀ ω : Fin 2 → ℝ, |wψ 1 (ω 0) * wψ 1 (ω 1)| ≤ 1 := by
    intro ω
    rw [abs_mul]
    have h0 : |wψ 1 (ω 0)| = 1 := by
      have := wψ_sq (ω 0); rw [← sq_abs] at this; nlinarith [abs_nonneg (wψ 1 (ω 0))]
    have h1 : |wψ 1 (ω 1)| = 1 := by
      have := wψ_sq (ω 1); rw [← sq_abs] at this; nlinarith [abs_nonneg (wψ 1 (ω 1))]
    rw [h0, h1]; norm_num
  have hYmem : MemLp (fun ω : Fin 2 → ℝ => wψ 1 (ω 0) * wψ 1 (ω 1)) 2 wμ :=
    memLp_two_of_bound hY hYb
  have hZ : (fun ω => ∑ γ : Fin 2, ∑ γ' : Fin 2,
      wlam γ * wlam γ' * cvarEntry wU wψ wsites wrIdx warr wtag γ γ' ω)
      = fun ω : Fin 2 → ℝ => 1 / 2 + 1 / 2 * (wψ 1 (ω 0) * wψ 1 (ω 1)) := by
    funext ω; exact wstat_apply ω
  rw [hZ, variance_const_add (X := fun ω : Fin 2 → ℝ => 1 / 2 * (wψ 1 (ω 0) * wψ 1 (ω 1)))
    (hYmem.const_mul _).aestronglyMeasurable (1 / 2)]
  rw [show (fun ω : Fin 2 → ℝ => 1 / 2 * (wψ 1 (ω 0) * wψ 1 (ω 1)))
      = fun ω : Fin 2 → ℝ => (1 / 2 : ℝ) * ((fun ω' : Fin 2 → ℝ =>
        wψ 1 (ω' 0) * wψ 1 (ω' 1)) ω) from rfl,
    variance_const_mul, variance_eq_sub hYmem, wintegral_prod]
  have hsq : ∫ ω, (fun ω' : Fin 2 → ℝ => wψ 1 (ω' 0) * wψ 1 (ω' 1)) ω ^ 2 ∂wμ = 1 := by
    have hone : ∀ ω : Fin 2 → ℝ,
        (fun ω' : Fin 2 → ℝ => wψ 1 (ω' 0) * wψ 1 (ω' 1)) ω ^ 2 = 1 := by
      intro ω; rw [mul_pow, wψ_sq, wψ_sq]; norm_num
    simp only [hone]
    simp
  rw [show wμ[(fun ω' : Fin 2 → ℝ => wψ 1 (ω' 0) * wψ 1 (ω' 1)) ^ 2]
      = ∫ ω, (fun ω' : Fin 2 → ℝ => wψ 1 (ω' 0) * wψ 1 (ω' 1)) ω ^ 2 ∂wμ by
    simp only [Pi.pow_apply], hsq]
  norm_num

/-- All hypotheses of `concentration_clause_b` hold on this model, and the variance it bounds
is nonzero. -/
theorem concentration_clause_b_witness :
    variance (fun ω => ∑ γ : Fin 2, ∑ γ' : Fin 2,
        wlam γ * wlam γ' * cvarEntry wU wψ wsites wrIdx warr wtag γ γ' ω) wμ
      ≤ (Fintype.card (Fin 2) : ℝ) ^ 2 * (2 * (0:ℝ) + 2 * 1)
    ∧ variance (fun ω => ∑ γ : Fin 2, ∑ γ' : Fin 2,
        wlam γ * wlam γ' * cvarEntry wU wψ wsites wrIdx warr wtag γ γ' ω) wμ = 1 / 4 :=
  ⟨concentration_clause_b wIsBasisSystem wHinj wHsep wlam_sq_le wmatched_variance wunm,
    wstat_variance⟩

end ClauseBWitness

end WitnessB

/-! ### A model for the matched-part bound

A biased two-point law, `2` with probability `1/5` and `-1/2` with probability `4/5`, on which
`ψ_1` has mean zero and unit variance and `ψ_1²` is not constant; there `Var[Ξᵐ_{γγ}] = 9/4`. -/

section WitnessStepTwo

open scoped ENNReal

namespace StepTwoWitness

/-- A **biased** two-point law: `2` with probability `1/5`, `-1/2` with probability `4/5`. -/
noncomputable def bLaw : Measure ℝ :=
  (1/5 : ℝ≥0∞) • Measure.dirac (2:ℝ) + (4/5 : ℝ≥0∞) • Measure.dirac (-1/2:ℝ)

instance : IsProbabilityMeasure bLaw := by
  constructor
  simp only [bLaw, Measure.coe_add, Pi.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ, Pi.one_apply, mul_one]
  rw [ENNReal.div_add_div_same, show (1 : ℝ≥0∞) + 4 = 5 by norm_num]
  have h5 : (5 : ℝ≥0∞) ≠ 0 := by norm_num
  have h5' : (5 : ℝ≥0∞) ≠ ⊤ := by norm_num
  exact ENNReal.div_self h5 h5'

/-- The witness probability space: one biased latent variable. -/
noncomputable def bμ : Measure (Fin 1 → ℝ) := Measure.pi fun _ => bLaw

instance : IsProbabilityMeasure bμ := by
  unfold bμ; infer_instance

def bU (v : Fin 1) (ω : Fin 1 → ℝ) : ℝ := ω v

/-- The orthonormal system on the biased law: the constant and the function with
`ψ_1(2) = 2`, `ψ_1(-1/2) = -1/2`, whose square is not constant. -/
noncomputable def bψ (r : Fin 2) (x : ℝ) : ℝ :=
  if r = 0 then 1 else if 1 ≤ x then 2 else -1/2

theorem measurable_bψ (r : Fin 2) : Measurable (bψ r) := by
  by_cases hr : r = 0
  · have hfun : bψ r = fun _ : ℝ => (1:ℝ) := by funext x; simp [bψ, hr]
    rw [hfun]; exact measurable_const
  · have hfun : bψ r = fun x : ℝ => if 1 ≤ x then (2:ℝ) else -1/2 := by
      funext x; simp [bψ, hr]
    rw [hfun]
    exact Measurable.ite (measurableSet_le measurable_const measurable_id)
      measurable_const measurable_const

theorem bintegral {f : ℝ → ℝ} (hf : Measurable f) (v : Fin 1) :
    ∫ ω, f (bU v ω) ∂bμ = f 2 / 5 + 4 * f (-1/2) / 5 := by
  have hmap : bμ.map (fun ω : Fin 1 → ℝ => ω v) = bLaw :=
    (MeasureTheory.measurePreserving_eval (fun _ => bLaw) v).map_eq
  have h1 : ∫ ω, f (bU v ω) ∂bμ = ∫ x, f x ∂bLaw := by
    rw [← hmap, integral_map (measurable_pi_apply v).aemeasurable hf.aestronglyMeasurable]
    rfl
  have hi1 : Integrable f ((1/5 : ℝ≥0∞) • Measure.dirac (2:ℝ)) :=
    (integrable_dirac' hf.stronglyMeasurable (by simp)).smul_measure (by simp)
  have hi2 : Integrable f ((4/5 : ℝ≥0∞) • Measure.dirac (-1/2:ℝ)) :=
    (integrable_dirac' hf.stronglyMeasurable (by simp)).smul_measure
      (by simp [ENNReal.div_eq_top])
  rw [h1, bLaw, integral_add_measure hi1 hi2, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  rw [show ((1/5 : ℝ≥0∞)).toReal = (1/5 : ℝ) by
      rw [ENNReal.toReal_div]; norm_num,
    show ((4/5 : ℝ≥0∞)).toReal = (4/5 : ℝ) by
      rw [ENNReal.toReal_div]; norm_num]
  simp only [smul_eq_mul]
  ring

theorem bIsBasisSystem : IsBasisSystem bμ bU bψ ({1} : Set (Fin 2)) 2 where
  measurable_latent v := measurable_pi_apply v
  measurable_psi := measurable_bψ
  indep := iIndepFun_pi (μ := fun _ : Fin 1 => bLaw) (X := fun _ => (id : ℝ → ℝ))
    (fun _ => aemeasurable_id)
  bound r x := by
    simp only [bψ]
    split_ifs <;> norm_num
  integral_eq_zero v {r} hr := by
    have hr1 : r = 1 := hr
    subst hr1
    rw [bintegral (measurable_bψ 1) v]
    norm_num [bψ]
  integral_mul v r r' := by
    rw [bintegral (f := fun x => bψ r x * bψ r' x)
      ((measurable_bψ r).mul (measurable_bψ r')) v]
    fin_cases r <;> fin_cases r' <;> norm_num [bψ]

def bsites : ∀ _γ : Fin 1, Unit → Finset (Fin 1) := fun _ _ => {0}

def brIdx : Fin 1 → Fin 1 → Fin 2 := fun _ _ => 1

def barr : ∀ _γ : Fin 1, Unit → Unit → ℝ := fun _ _ _ => 1

theorem bmatchedPart_apply (ω : Fin 1 → ℝ) :
    matchedPart bU bψ bsites brIdx barr 0 ω = bψ 1 (ω 0) ^ 2 - 1 := by
  simp [matchedPart, gramDiag, barr, basisProd, bsites, brIdx, bU]

theorem bmatchedPart_fun :
    matchedPart bU bψ bsites brIdx barr 0 = fun ω : Fin 1 → ℝ => bψ 1 (ω 0) ^ 2 - 1 := by
  funext ω; exact bmatchedPart_apply ω

theorem bmemLp_matched :
    MemLp (fun ω : Fin 1 → ℝ => bψ 1 (ω 0) ^ 2 - 1) 2 bμ := by
  refine memLp_two_of_bound
    ((((measurable_bψ 1).comp (measurable_pi_apply 0)).pow_const 2).sub measurable_const)
    (C := 3) fun ω => ?_
  simp only [bψ]
  split_ifs <;> norm_num

/-- `Var[Ξᵐ_{γγ}] = 9/4` on this model. -/
theorem bmatched_variance :
    variance (matchedPart bU bψ bsites brIdx barr 0) bμ = 9 / 4 := by
  rw [bmatchedPart_fun, variance_eq_sub bmemLp_matched]
  have hmean : ∫ ω : Fin 1 → ℝ, (bψ 1 (ω 0) ^ 2 - 1) ∂bμ = 0 := by
    have h := bintegral (f := fun x => bψ 1 x ^ 2 - 1)
      (((measurable_bψ 1).pow_const 2).sub measurable_const) 0
    simp only [bU] at h
    rw [h]
    norm_num [bψ]
  have hsq : bμ[(fun ω : Fin 1 → ℝ => bψ 1 (ω 0) ^ 2 - 1) ^ 2] = 9 / 4 := by
    have h := bintegral (f := fun x => (bψ 1 x ^ 2 - 1) ^ 2)
      ((((measurable_bψ 1).pow_const 2).sub measurable_const).pow_const 2) 0
    simp only [bU] at h
    simp only [Pi.pow_apply]
    rw [h]
    norm_num [bψ]
  rw [hsq, hmean]
  norm_num

/-- All hypotheses of `variance_matchedPart_le` hold on this model, where the matched part is
not constant. -/
theorem step2_witness :
    variance (matchedPart bU bψ bsites brIdx barr 0) bμ
      ≤ ((max (2:ℝ) 1 ^ Fintype.card (Fin 1)) ^ 2) ^ 2 *
        ∑ w : Fin 1, (∑ s ∈ Finset.univ.filter (fun s => w ∈ bsites 0 s),
          gramDiag barr 0 s) ^ 2
    ∧ variance (matchedPart bU bψ bsites brIdx barr 0) bμ = 9 / 4 :=
  ⟨variance_matchedPart_le bIsBasisSystem 0, bmatched_variance⟩

end StepTwoWitness

end WitnessStepTwo

/-! ### A model for clause (b) when `|e_γ| = 2`

The clause-(a) model has singleton site sets. On it the variance bounded by
`concentration_clause_b_singleton` is `1/4`, and `𝔼[(Ξᵘ_{01})²] = 1`. -/

section WitnessSingleton

open ClauseAWitness ClauseBWitness

namespace SingletonWitness

omit [MeasurableSpace Ω] [Fintype V] [DecidableEq V] [DecidableEq R] in
/-- `tot(γ) = ‖V^{(γ)}‖_F² = 1` on the witness model. -/
theorem wtot (γ : Fin 2) : rectFrobSq (warr γ) ≤ 1 := by
  simp [rectFrobSq, warr]

omit [MeasurableSpace Ω] [Fintype V] [DecidableEq V] [DecidableEq R] in
/-- `‖V^{(γ)} ⊠ V^{(γ)}‖_F = 1` on the witness model, so `cut(γ) = 1`. -/
theorem wcut (γ : Fin 2) :
    rectFrobNorm (Matrix.of (warr γ) * (Matrix.of (warr γ))ᵀ) ≤ 1 := by
  have hone : rectFrobSq (Matrix.of (warr γ) * (Matrix.of (warr γ))ᵀ) = 1 := by
    simp [rectFrobSq, Matrix.mul_apply, Matrix.transpose_apply, warr]
  rw [rectFrobNorm, hone, Real.sqrt_one]

omit [MeasurableSpace Ω] [Fintype V] [DecidableEq V] [DecidableEq R] in
/-- All hypotheses of `concentration_clause_b_singleton` hold on this model, and the variance
it bounds is `1/4`. -/
theorem concentration_clause_b_singleton_witness :
    variance (fun ω => ∑ γ : Fin 2, ∑ γ' : Fin 2,
        wlam γ * wlam γ' * cvarEntry wU wψ wsites wrIdx warr wtag γ γ' ω) wμ ≤ 48
    ∧ variance (fun ω => ∑ γ : Fin 2, ∑ γ' : Fin 2,
        wlam γ * wlam γ' * cvarEntry wU wψ wsites wrIdx warr wtag γ γ' ω) wμ = 1 / 4 := by
  refine ⟨le_trans (concentration_clause_b_singleton
    (st := fun (g : Fin 2) (_ : Unit) => g) wIsBasisSystem (fun _ _ => rfl) wHpos wHinj wHsep
    wlam_sq_le wcut wtot) ?_, wstat_variance⟩
  norm_num

omit [MeasurableSpace Ω] [Fintype V] [DecidableEq V] [DecidableEq R] in
/-- `𝔼[(Ξᵘ_{01})²] = 1` on this model. -/
theorem wunm_eq_one :
    ∫ ω, (unmatchedPart wU wψ wsites wrIdx warr wtag 0 1 ω) ^ 2 ∂wμ = 1 := by
  have hpt : ∀ ω : Fin 2 → ℝ,
      (unmatchedPart wU wψ wsites wrIdx warr wtag 0 1 ω) ^ 2 = 1 := by
    intro ω
    rw [wunmatchedPart_apply_ne (by decide : (0 : Fin 2) ≠ 1), mul_pow, wψ_sq, wψ_sq]
    norm_num
  simp only [hpt]
  simp

omit [MeasurableSpace Ω] [Fintype V] [DecidableEq V] [DecidableEq R] in
/-- All hypotheses of `integral_sq_unmatchedPart_le_of_singleton` hold on this model, and the
quantity it bounds is `1`. -/
theorem unmatched_singleton_witness :
    ∫ ω, (unmatchedPart wU wψ wsites wrIdx warr wtag 0 1 ω) ^ 2 ∂wμ
      ≤ 2 * max (1:ℝ) 1 ^ 4 * rectFrobSq (Matrix.of (warr 0) * (Matrix.of (warr 1))ᵀ)
    ∧ ∫ ω, (unmatchedPart wU wψ wsites wrIdx warr wtag 0 1 ω) ^ 2 ∂wμ = 1 :=
  ⟨integral_sq_unmatchedPart_le_of_singleton wIsBasisSystem
      (st := fun (g : Fin 2) (_ : Unit) => g) (fun _ _ => rfl) wHpos wHinj 0 1,
    wunm_eq_one⟩


end SingletonWitness

end WitnessSingleton

/-! ### A model with `|e_γ| = 3`

Two interaction coordinates: `K = Fin 2`, sites `V = Fin 2 × Fin 2` of the form
`(coordinate, index)`, and `sites γ = {(0,γ),(1,γ)}`, so `|f_γ| = 2`. The surviving quadruple
carries pattern (B) at both coordinates, so Class 2 is empty, and `𝔼[(Ξᵘ_{01})²] = 1`. The basis
system is the fair-sign system over a finite site type. -/

section WitnessGeneral

open ClauseAWitness ClauseBWitness

namespace GeneralWitness

open scoped ENNReal

/-- Independent fair signs indexed by a finite type `W`. -/
noncomputable def gmu (W : Type*) [Fintype W] : Measure (W → ℝ) := Measure.pi fun _ => signLaw

instance instIsProbabilityMeasureGmu (W : Type*) [Fintype W] :
    IsProbabilityMeasure (gmu W) := by
  unfold gmu
  infer_instance

/-- The latent variables: the coordinates. -/
def gU (W : Type*) (v : W) (ω : W → ℝ) : ℝ := ω v

theorem gintegral {W : Type*} [Fintype W] {f : ℝ → ℝ} (hf : Measurable f) (v : W) :
    ∫ ω, f (gU W v ω) ∂(gmu W) = (f 1 + f (-1)) / 2 := by
  have hmap : (gmu W).map (fun ω : W → ℝ => ω v) = signLaw :=
    (MeasureTheory.measurePreserving_eval (fun _ => signLaw) v).map_eq
  have h1 : ∫ ω, f (gU W v ω) ∂(gmu W) = ∫ x, f x ∂signLaw := by
    rw [← hmap, integral_map (measurable_pi_apply v).aemeasurable hf.aestronglyMeasurable]
    rfl
  have hi1 : Integrable f ((1/2 : ℝ≥0∞) • Measure.dirac (1:ℝ)) :=
    (integrable_dirac' hf.stronglyMeasurable (by simp)).smul_measure (by simp)
  have hi2 : Integrable f ((1/2 : ℝ≥0∞) • Measure.dirac (-1:ℝ)) :=
    (integrable_dirac' hf.stronglyMeasurable (by simp)).smul_measure (by simp)
  rw [h1, signLaw, integral_add_measure hi1 hi2, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  simp
  ring

/-- The fair-sign basis system over a finite site type. -/
theorem gIsBasisSystem (W : Type*) [Fintype W] :
    IsBasisSystem (gmu W) (gU W) wψ ({1} : Set (Fin 2)) 1 where
  measurable_latent v := measurable_pi_apply v
  measurable_psi := measurable_wψ
  indep := iIndepFun_pi (μ := fun _ : W => signLaw) (X := fun _ => (id : ℝ → ℝ))
    (fun _ => aemeasurable_id)
  bound r x := by
    simp only [wψ]
    split_ifs <;> simp
  integral_eq_zero v {r} hr := by
    have hr1 : r = 1 := hr
    subst hr1
    rw [gintegral (measurable_wψ 1) v]
    norm_num [wψ]
  integral_mul v r r' := by
    rw [gintegral (f := fun x => wψ r x * wψ r' x)
      ((measurable_wψ r).mul (measurable_wψ r')) v]
    fin_cases r <;> fin_cases r' <;> norm_num [wψ]

/-- The sites `(coordinate, index)`: two coordinates with two indices each. -/
abbrev gSite : Type := Fin 2 × Fin 2

/-- Two interaction coordinates, so `|f_γ| = 2` and `|e_γ| = 3`. -/
def glev : ∀ _γ : Fin 2, Finset (Fin 2) := fun _ => Finset.univ

/-- Component `γ` occupies index `γ` at every coordinate. -/
def gpt : ∀ _γ : Fin 2, Unit → Fin 2 → gSite := fun γ _ k => (k, γ)

/-- The site set of the single sub-tuple of `γ`: two sites, one per coordinate. -/
def gsites : ∀ _γ : Fin 2, Unit → Finset gSite := fun γ _ => {(0, γ), (1, γ)}

/-- Both components read the same mean-zero basis index. -/
def grIdx : Fin 2 → gSite → Fin 2 := fun _ _ => 1

/-- Equal tags, so `cvarEntry` is not identically zero off the diagonal. -/
def gtag : Fin 2 → Unit := fun _ => ()

/-- A nonzero coefficient array. -/
def garr : ∀ _γ : Fin 2, Unit → Unit → ℝ := fun _ _ _ => 1

theorem gHsite : ∀ (g : Fin 2) (x : Unit), gsites g x = (glev g).image (gpt g x) := by
  decide

theorem gHptc : ∀ (g g' : Fin 2) (x : Unit) (y : Unit) (k k' : Fin 2),
    gpt g x k = gpt g' y k' → k = k' := by
  intro g g' x y k k' hEq
  exact congrArg Prod.fst hEq

theorem gHpos : ∀ (g : Fin 2) (x : Unit), ∀ w ∈ gsites g x,
    grIdx g w ∈ ({1} : Set (Fin 2)) := fun _ _ _ _ => rfl

theorem gHinj : ∀ (g : Fin 2) (x y : Unit), gsites g x = gsites g y → x = y :=
  fun _ _ _ _ => rfl

/-- Class 2 is empty on this model: both coordinates carry pattern (B). -/
theorem gNotClassTwo : ¬ IsClassTwo glev gpt 0 1 () () () () := by decide

theorem gclassTwoSum_eq_zero :
    classTwoSum (gmu gSite) (gU gSite) wψ gsites grIdx garr glev gpt 0 1 = 0 :=
  Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ =>
    Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => ite_eq_right gNotClassTwo

theorem gsites_pair (γ : Fin 2) : ((0, γ) : gSite) ≠ (1, γ) := by simp

/-- `π^γ_s ω = ψ_1(U_{(0,γ)})ψ_1(U_{(1,γ)})`. -/
theorem gbasisProd_apply (γ : Fin 2) (ω : gSite → ℝ) :
    basisProd (gU gSite) wψ gsites grIdx γ () ω = wψ 1 (ω (0, γ)) * wψ 1 (ω (1, γ)) := by
  simp only [basisProd, gsites, grIdx, gU]
  rw [Finset.prod_pair (gsites_pair γ)]

theorem gbasisProd_sq (γ : Fin 2) (ω : gSite → ℝ) :
    basisProd (gU gSite) wψ gsites grIdx γ () ω ^ 2 = 1 := by
  rw [gbasisProd_apply, mul_pow, wψ_sq, wψ_sq]
  norm_num

theorem gNotMatched : ¬ IsMatched gsites grIdx 0 1 () () := by decide

/-- `𝔼[(Ξᵘ_{01})²] = 1` on this model. -/
theorem gunm_eq_one :
    ∫ ω, (unmatchedPart (gU gSite) wψ gsites grIdx garr gtag 0 1 ω) ^ 2 ∂(gmu gSite) = 1 := by
  have hpt : ∀ ω : gSite → ℝ,
      (unmatchedPart (gU gSite) wψ gsites grIdx garr gtag 0 1 ω) ^ 2 = 1 := by
    intro ω
    have hg : gramEntry garr 0 1 () () = 1 := by simp [gramEntry, garr]
    have hu : unmatchedPart (gU gSite) wψ gsites grIdx garr gtag 0 1 ω
        = basisProd (gU gSite) wψ gsites grIdx 0 () ω *
          basisProd (gU gSite) wψ gsites grIdx 1 () ω := by
      simp [unmatchedPart, gtag, gNotMatched, hg]
    rw [hu, mul_pow, gbasisProd_sq, gbasisProd_sq]
    norm_num
  simp only [hpt]
  simp

/-- All hypotheses of `integral_sq_unmatchedPart_le_of_classTwo` hold on this model with
`b₂ = 0`; the quantity bounded is `1` and the bound is `16`. -/
theorem unmatched_general_witness :
    ∫ ω, (unmatchedPart (gU gSite) wψ gsites grIdx garr gtag 0 1 ω) ^ 2 ∂(gmu gSite) ≤ 16
    ∧ ∫ ω, (unmatchedPart (gU gSite) wψ gsites grIdx garr gtag 0 1 ω) ^ 2 ∂(gmu gSite) = 1 := by
  refine ⟨le_trans (integral_sq_unmatchedPart_le_of_classTwo (lev := glev) (pt := gpt)
    (tag := gtag) (b₂ := (0:ℝ)) (gIsBasisSystem gSite) gHsite gHptc gHpos gHinj 0 1 ?_) ?_,
    gunm_eq_one⟩
  · rw [gclassTwoSum_eq_zero]
    simp
  · have hfrob : rectFrobSq (Matrix.of (garr 0) * (Matrix.of (garr 1))ᵀ) = 1 := by
      simp [rectFrobSq, Matrix.mul_apply, Matrix.transpose_apply, garr]
    rw [hfrob]
    norm_num


/-! ### The general unmatched-part bound on the `|e_γ| = 3` model -/

section WitnessClosed

/-- All hypotheses of `integral_sq_unmatchedPart_le_general` hold on the `|e_γ| = 3` model with
`cut = tot = 1`; the quantity bounded is `1` and the bound is `272 = 4^{|K|} + 4·8^{|K|}`. -/
theorem unmatched_general_witness_closed :
    ∫ ω, (unmatchedPart (gU gSite) wψ gsites grIdx garr gtag 0 1 ω) ^ 2 ∂(gmu gSite) ≤ 272
    ∧ ∫ ω, (unmatchedPart (gU gSite) wψ gsites grIdx garr gtag 0 1 ω) ^ 2 ∂(gmu gSite) = 1 := by
  refine ⟨le_trans (integral_sq_unmatchedPart_le_general (lev := glev) (pt := gpt)
    (tag := gtag) (cutmax := 1) (totmax := 1) (gIsBasisSystem gSite) gHsite gHptc gHpos gHinj
    0 1 (by norm_num) ?_ ?_) ?_, gunm_eq_one⟩
  · intro g Bs _
    refine le_trans (rectFrobNorm_mul_transpose_self_le _) ?_
    have hz : rectFrobSq (Matrix.of (levMat glev gpt Bs g (garr g))) = rectFrobSq (garr g) :=
      rectFrobSq_levMat (sites := gsites) gHsite gHinj Bs g (garr g)
    rw [hz]
    simp [rectFrobSq, garr]
  · intro g
    simp [rectFrobSq, garr]
  · have hfrob : rectFrobSq (Matrix.of (garr 0) * (Matrix.of (garr 1))ᵀ) = 1 := by
      simp [rectFrobSq, Matrix.mul_apply, Matrix.transpose_apply, garr]
    rw [hfrob]
    norm_num [gSite]

end WitnessClosed

end GeneralWitness

end WitnessGeneral

/-! ### A Class-2 configuration

A combinatorial check, by `decide`, that Class 2 is nonempty when a component has two
sub-tuples that differ at one coordinate and agree at another. -/

section ClassTwoReachable

namespace ClassTwoReachable

/-- Two coordinates with two sites each; a sub-tuple is named by its site index at
coordinate `0`, and coordinate `1` is shared. -/
abbrev rSite : Type := Fin 2 × Fin 2

/-- `f_γ = {0, 1}`, so `|e_γ| = 3`. -/
def rLev : Fin 1 -> Finset (Fin 2) := fun _ => Finset.univ

/-- `pt γ x k` = the site the sub-tuple `x` occupies at coordinate `k`. -/
def rPt : ∀ _γ : Fin 1, Fin 2 -> Fin 2 -> rSite := fun _ x k => (k, if k = 0 then x else 0)

/-- With `s = s' = 0` and `u = u' = 1`, coordinate `0` carries pattern (A) and coordinate `1`
pattern (D), so `ℬ = {0}` and the configuration is Class 2. -/
theorem isClassTwo_reachable : IsClassTwo rLev rPt 0 0 (0 : Fin 2) (0 : Fin 2) 1 1 := by decide

/-- The pattern-(A) set of that configuration is `{0}`. -/
theorem patAset_reachable : patAset rLev rPt 0 0 (0 : Fin 2) (0 : Fin 2) 1 1 = {0} := by decide

end ClassTwoReachable

end ClassTwoReachable


/-! ### Models for the fibre-sum bound

* `StepTwoClosedWitness`: two coordinates, `𝒩_k = Fin 2`, `I = Fin 3`. The fibre-sum bound holds
  with equality (`9 = 9`), and all hypotheses of `concentration_clause_b_general_closed` hold.
* `StepTwoSingletonWitness`: the same types with `e_γ = {0}`; it covers `k ∉ e_γ` and compares
  with `variance_matchedPart_le_of_singleton`.
* `StepTwoBiasedWitness`: the biased law over a `Σ_k𝒩_k` site type, where `Var[Ξᵐ] = 9/4`. -/

section WitnessStepTwoClosed

open scoped ENNReal

namespace StepTwoClosedWitness

open ClauseAWitness GeneralWitness

/-- Two interaction coordinates, two indices each. -/
abbrev sK : Type := Fin 2
abbrev sN : sK → Type := fun _ => Fin 2
abbrev sV : Type := Site sK sN

def slev : ∀ _γ : Fin 2, Finset sK := fun _ => Finset.univ
def spt : ∀ _γ : Fin 2, Unit → sK → sV := fun γ _ k => ⟨k, γ⟩
def ssites : ∀ _γ : Fin 2, Unit → Finset sV := fun γ _ => {⟨0, γ⟩, ⟨1, γ⟩}
def srIdx : Fin 2 → sV → Fin 2 := fun _ _ => 1
def stag : Fin 2 → Unit := fun _ => ()

/-- A constant coefficient array with `I = Fin 3`, so `gramDiag = 3`. -/
def sarr : ∀ _γ : Fin 2, Unit → Fin 3 → ℝ := fun _ _ _ => 1

noncomputable def slam : Fin 2 → ℝ := fun _ => 1 / 2

theorem sHsite : ∀ (g : Fin 2) (x : Unit), ssites g x = (slev g).image (spt g x) := by decide

theorem sHptf : ∀ (g : Fin 2) (x : Unit), ∀ k ∈ slev g, (spt g x k).1 = k :=
  fun _ _ _ _ => rfl

theorem sHptc : ∀ (g g' : Fin 2) (x y : Unit) (k k' : sK),
    spt g x k = spt g' y k' → k = k' := fun _ _ _ _ _ _ h => congrArg Sigma.fst h

theorem sHpos : ∀ (g : Fin 2) (x : Unit), ∀ w ∈ ssites g x,
    srIdx g w ∈ ({1} : Set (Fin 2)) := fun _ _ _ _ => rfl

theorem sHinj : ∀ (g : Fin 2) (x y : Unit), ssites g x = ssites g y → x = y :=
  fun _ _ _ _ => rfl

theorem sHsep : ∀ (g g' : Fin 2) (x y : Unit), stag g = stag g' → ssites g x = ssites g' y →
    (∀ w ∈ ssites g x, srIdx g w = srIdx g' w) → g = g' := by
  intro g g' x y _ hs _
  cases x
  cases y
  revert hs
  fin_cases g <;> fin_cases g' <;> decide

theorem sHtot : ∀ γ : Fin 2, rectFrobSq (sarr γ) ≤ 3 := by
  intro γ
  simp [rectFrobSq, sarr]

theorem sHcutA : ∀ (g : Fin 2), ∀ Bs ⊂ slev g,
    rectFrobNorm (Matrix.of (levMat slev spt Bs g (sarr g)) *
      (Matrix.of (levMat slev spt Bs g (sarr g)))ᵀ) ≤ 3 := by
  intro g Bs _
  refine le_trans (rectFrobNorm_mul_transpose_self_le _) ?_
  have hz : rectFrobSq (Matrix.of (levMat slev spt Bs g (sarr g))) = rectFrobSq (sarr g) :=
    rectFrobSq_levMat (sites := ssites) sHsite sHinj Bs g (sarr g)
  rw [hz]
  exact sHtot g

theorem sHcut : ∀ γ : Fin 2,
    rectFrobNorm (Matrix.of (sarr γ) * (Matrix.of (sarr γ))ᵀ) ≤ 3 := by
  intro γ
  refine le_trans (rectFrobNorm_mul_transpose_self_le _) ?_
  exact sHtot γ

theorem slam_sq_le : ∑ γ : Fin 2, slam γ ^ 2 ≤ 1 := by
  simp [slam]
  norm_num

/-- All hypotheses of `sum_sq_gramDiag_fiber_le` hold on the two-coordinate model, where the
contraction set is `{1}`; the fibre sum is `9` and the bound is `9`. -/
theorem sstep2_witness :
    (∀ k : sK, ∑ j : sN k, (∑ s ∈ Finset.univ.filter
        (fun s => (⟨k, j⟩ : sV) ∈ ssites 0 s), gramDiag sarr 0 s) ^ 2 ≤ 9)
    ∧ (∑ j : sN 0, (∑ s ∈ Finset.univ.filter
        (fun s => (⟨0, j⟩ : sV) ∈ ssites 0 s), gramDiag sarr 0 s) ^ 2 = 9) := by
  refine ⟨sum_sq_gramDiag_fiber_le (bnd := 9) sHsite sHinj sHptf 0 (by norm_num)
    (fun Bs hBs => ?_), ?_⟩
  · have := rectFrobSq_levGram_le_cut_tot (sites := ssites) (cutγ := 3) (totγ := 3)
      sHsite sHinj 0 (by norm_num) (sHtot 0) Bs (sHcutA 0 Bs hBs)
    exact le_trans this (by norm_num)
  · have hg : ∀ s : Unit, gramDiag sarr 0 s = 3 := by
      intro s
      simp [gramDiag, sarr]
    have hfil0 : (Finset.univ.filter
        (fun s : Unit => (⟨(0 : sK), (0 : Fin 2)⟩ : sV) ∈ ssites 0 s))
        = (Finset.univ : Finset Unit) := by decide
    have hfil1 : (Finset.univ.filter
        (fun s : Unit => (⟨(0 : sK), (1 : Fin 2)⟩ : sV) ∈ ssites 0 s))
        = (∅ : Finset Unit) := by decide
    rw [Fin.sum_univ_two, hfil0, hfil1]
    simp [hg]
    norm_num

/-- All hypotheses of `concentration_clause_b_general_closed` hold on the two-coordinate
model, with `cut = tot = 3`. -/
theorem sclause_b_closed_witness :
    variance (fun ω => ∑ γ : Fin 2, ∑ γ' : Fin 2,
        slam γ * slam γ' * cvarEntry (gU sV) wψ ssites srIdx sarr stag γ γ' ω) (gmu sV)
      ≤ 76608 := by
  refine le_trans (concentration_clause_b_general_closed (lev := slev) (pt := spt)
    (cutmax := 3) (totmax := 3) (GeneralWitness.gIsBasisSystem sV) sHsite sHptc sHptf sHpos
    sHinj sHsep slam_sq_le sHcut sHcutA sHtot) ?_
  have hcV : Fintype.card sV = 4 := by decide
  have hcK : Fintype.card sK = 2 := by decide
  rw [hcV, hcK]
  norm_num

end StepTwoClosedWitness

namespace StepTwoSingletonWitness

open ClauseAWitness GeneralWitness StepTwoClosedWitness

/-- A one-coordinate level on the same site type, so every site set is a singleton. -/
def tlev : ∀ _γ : Fin 2, Finset sK := fun _ => {0}
def tsites : ∀ _γ : Fin 2, Unit → Finset sV := fun γ _ => {⟨0, γ⟩}
def tst : ∀ _γ : Fin 2, Unit → sV := fun γ _ => ⟨0, γ⟩

theorem tHsite : ∀ (g : Fin 2) (x : Unit), tsites g x = (tlev g).image (spt g x) := by decide

theorem tHst : ∀ (g : Fin 2) (x : Unit), tsites g x = {tst g x} := by decide

theorem tHinj : ∀ (g : Fin 2) (x y : Unit), tsites g x = tsites g y → x = y :=
  fun _ _ _ _ => rfl

theorem tHptf : ∀ (g : Fin 2) (x : Unit), ∀ k ∈ tlev g, (spt g x k).1 = k :=
  fun _ _ _ _ => rfl

theorem tHtot : ∀ γ : Fin 2, rectFrobSq (sarr γ) ≤ 3 := sHtot

theorem tHcutA : ∀ Bs ⊂ tlev 0,
    rectFrobNorm (Matrix.of (levMat tlev spt Bs 0 (sarr 0)) *
      (Matrix.of (levMat tlev spt Bs 0 (sarr 0)))ᵀ) ≤ 3 := by
  intro Bs _
  refine le_trans (rectFrobNorm_mul_transpose_self_le _) ?_
  have hz : rectFrobSq (Matrix.of (levMat tlev spt Bs 0 (sarr 0))) = rectFrobSq (sarr 0) :=
    rectFrobSq_levMat (sites := tsites) tHsite tHinj Bs 0 (sarr 0)
  rw [hz]
  exact tHtot 0

/-- At `k = 1`, outside the level, the fibre sum is `0`; at `k = 0` it is `9` and the bound
is `9`. -/
theorem tstep2_witness :
    (∀ k : sK, ∑ j : sN k, (∑ s ∈ Finset.univ.filter
        (fun s => (⟨k, j⟩ : sV) ∈ tsites 0 s), gramDiag sarr 0 s) ^ 2 ≤ 9)
    ∧ (∑ j : sN 0, (∑ s ∈ Finset.univ.filter
        (fun s => (⟨0, j⟩ : sV) ∈ tsites 0 s), gramDiag sarr 0 s) ^ 2 = 9)
    ∧ (∑ j : sN 1, (∑ s ∈ Finset.univ.filter
        (fun s => (⟨1, j⟩ : sV) ∈ tsites 0 s), gramDiag sarr 0 s) ^ 2 = 0) := by
  have hg : ∀ s : Unit, gramDiag sarr 0 s = 3 := by
    intro s
    simp [gramDiag, sarr]
  refine ⟨sum_sq_gramDiag_fiber_le (bnd := 9) tHsite tHinj tHptf 0 (by norm_num)
    (fun Bs hBs => ?_), ?_, ?_⟩
  · have := rectFrobSq_levGram_le_cut_tot (sites := tsites) (cutγ := 3) (totγ := 3)
      tHsite tHinj 0 (by norm_num) (tHtot 0) Bs (tHcutA Bs hBs)
    exact le_trans this (by norm_num)
  · have hfil0 : (Finset.univ.filter
        (fun s : Unit => (⟨(0 : sK), (0 : Fin 2)⟩ : sV) ∈ tsites 0 s))
        = (Finset.univ : Finset Unit) := by decide
    have hfil1 : (Finset.univ.filter
        (fun s : Unit => (⟨(0 : sK), (1 : Fin 2)⟩ : sV) ∈ tsites 0 s))
        = (∅ : Finset Unit) := by decide
    rw [Fin.sum_univ_two, hfil0, hfil1]
    simp [hg]
    norm_num
  · have hfil0 : (Finset.univ.filter
        (fun s : Unit => (⟨(1 : sK), (0 : Fin 2)⟩ : sV) ∈ tsites 0 s))
        = (∅ : Finset Unit) := by decide
    have hfil1 : (Finset.univ.filter
        (fun s : Unit => (⟨(1 : sK), (1 : Fin 2)⟩ : sV) ∈ tsites 0 s))
        = (∅ : Finset Unit) := by decide
    rw [Fin.sum_univ_two, hfil0, hfil1]
    simp

/-- When every site set is a singleton, `variance_matchedPart_le_cutA` gives `18` and
`variance_matchedPart_le_of_singleton` gives `9`; the ratio is `Fintype.card K = 2`. -/
theorem tsingleton_agreement :
    variance (matchedPart (gU sV) wψ tsites srIdx sarr 0) (gmu sV) ≤ 18
    ∧ variance (matchedPart (gU sV) wψ tsites srIdx sarr 0) (gmu sV) ≤ 9 := by
  have hcV : Fintype.card sV = 4 := by decide
  have hcK : Fintype.card sK = 2 := by decide
  constructor
  · refine le_trans (variance_matchedPart_le_cutA (rIdx := srIdx) (lev := tlev) (pt := spt)
      (cutγ := 3) (GeneralWitness.gIsBasisSystem sV) tHsite tHinj tHptf 0 tHcutA) ?_
    rw [hcV, hcK]
    norm_num
  · refine le_trans (variance_matchedPart_le_of_singleton (rIdx := srIdx) (arr := sarr)
      (GeneralWitness.gIsBasisSystem sV) tHst tHinj 0) ?_
    have hfrob : rectFrobSq (Matrix.of (sarr 0) * (Matrix.of (sarr 0))ᵀ) = 9 := by
      simp [rectFrobSq, Matrix.mul_apply, Matrix.transpose_apply, sarr]
      norm_num
    rw [hcV, hfrob]
    norm_num

end StepTwoSingletonWitness

namespace StepTwoBiasedWitness

open StepTwoWitness

abbrev bK : Type := Fin 1
abbrev bN : bK → Type := fun _ => Fin 1
abbrev bV : Type := Site bK bN

/-- The biased two-point law over a `Σ_k𝒩_k` site type. -/
noncomputable def bmuV : Measure (bV → ℝ) := Measure.pi fun _ => bLaw

instance : IsProbabilityMeasure bmuV := by unfold bmuV; infer_instance

def bUV (v : bV) (ω : bV → ℝ) : ℝ := ω v

theorem bintegralV {f : ℝ → ℝ} (hf : Measurable f) (v : bV) :
    ∫ ω, f (bUV v ω) ∂bmuV = f 2 / 5 + 4 * f (-1/2) / 5 := by
  have hmap : bmuV.map (fun ω : bV → ℝ => ω v) = bLaw :=
    (MeasureTheory.measurePreserving_eval (fun _ => bLaw) v).map_eq
  have h1 : ∫ ω, f (bUV v ω) ∂bmuV = ∫ x, f x ∂bLaw := by
    rw [← hmap, integral_map (measurable_pi_apply v).aemeasurable hf.aestronglyMeasurable]
    rfl
  have hi1 : Integrable f ((1/5 : ℝ≥0∞) • Measure.dirac (2:ℝ)) :=
    (integrable_dirac' hf.stronglyMeasurable (by simp)).smul_measure (by simp)
  have hi2 : Integrable f ((4/5 : ℝ≥0∞) • Measure.dirac (-1/2:ℝ)) :=
    (integrable_dirac' hf.stronglyMeasurable (by simp)).smul_measure
      (by simp [ENNReal.div_eq_top])
  rw [h1, bLaw, integral_add_measure hi1 hi2, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  rw [show ((1/5 : ℝ≥0∞)).toReal = (1/5 : ℝ) by
      rw [ENNReal.toReal_div]; norm_num,
    show ((4/5 : ℝ≥0∞)).toReal = (4/5 : ℝ) by
      rw [ENNReal.toReal_div]; norm_num]
  simp only [smul_eq_mul]
  ring

theorem bIsBasisSystemV : IsBasisSystem bmuV bUV bψ ({1} : Set (Fin 2)) 2 where
  measurable_latent v := measurable_pi_apply v
  measurable_psi := measurable_bψ
  indep := iIndepFun_pi (μ := fun _ : bV => bLaw) (X := fun _ => (id : ℝ → ℝ))
    (fun _ => aemeasurable_id)
  bound r x := by
    simp only [bψ]
    split_ifs <;> norm_num
  integral_eq_zero v {r} hr := by
    have hr1 : r = 1 := hr
    subst hr1
    rw [bintegralV (measurable_bψ 1) v]
    norm_num [bψ]
  integral_mul v r r' := by
    rw [bintegralV (f := fun x => bψ r x * bψ r' x)
      ((measurable_bψ r).mul (measurable_bψ r')) v]
    fin_cases r <;> fin_cases r' <;> norm_num [bψ]

def blev : ∀ _γ : Fin 1, Finset bK := fun _ => Finset.univ
def bpt : ∀ _γ : Fin 1, Unit → bK → bV := fun _ _ k => ⟨k, 0⟩
def bsitesV : ∀ _γ : Fin 1, Unit → Finset bV := fun _ _ => {⟨0, 0⟩}
def brIdxV : Fin 1 → bV → Fin 2 := fun _ _ => 1
def barrV : ∀ _γ : Fin 1, Unit → Unit → ℝ := fun _ _ _ => 1

theorem bHsite : ∀ (g : Fin 1) (x : Unit), bsitesV g x = (blev g).image (bpt g x) := by decide

theorem bHinj : ∀ (g : Fin 1) (x y : Unit), bsitesV g x = bsitesV g y → x = y :=
  fun _ _ _ _ => rfl

theorem bHptf : ∀ (g : Fin 1) (x : Unit), ∀ k ∈ blev g, (bpt g x k).1 = k :=
  fun _ _ _ _ => rfl

theorem bHtot : ∀ γ : Fin 1, rectFrobSq (barrV γ) ≤ 1 := by
  intro γ
  simp [rectFrobSq, barrV]

theorem bHcutA : ∀ Bs ⊂ blev 0,
    rectFrobNorm (Matrix.of (levMat blev bpt Bs 0 (barrV 0)) *
      (Matrix.of (levMat blev bpt Bs 0 (barrV 0)))ᵀ) ≤ 1 := by
  intro Bs _
  refine le_trans (rectFrobNorm_mul_transpose_self_le _) ?_
  have hz : rectFrobSq (Matrix.of (levMat blev bpt Bs 0 (barrV 0))) = rectFrobSq (barrV 0) :=
    rectFrobSq_levMat (sites := bsitesV) bHsite bHinj Bs 0 (barrV 0)
  rw [hz]
  exact bHtot 0

theorem bmatchedPart_fun :
    matchedPart bUV bψ bsitesV brIdxV barrV 0
      = fun ω : bV → ℝ => bψ 1 (ω ⟨0, 0⟩) ^ 2 - 1 := by
  funext ω
  simp [matchedPart, gramDiag, barrV, basisProd, bsitesV, brIdxV, bUV]

theorem bmemLpV : MemLp (fun ω : bV → ℝ => bψ 1 (ω ⟨0, 0⟩) ^ 2 - 1) 2 bmuV := by
  refine memLp_two_of_bound
    ((((measurable_bψ 1).comp (measurable_pi_apply (⟨0, 0⟩ : bV))).pow_const 2).sub
      measurable_const)
    (C := 3) fun ω => ?_
  simp only [bψ]
  split_ifs <;> norm_num

/-- `Var[Ξᵐ] = 9/4` on this model. -/
theorem bmatched_varianceV :
    variance (matchedPart bUV bψ bsitesV brIdxV barrV 0) bmuV = 9 / 4 := by
  rw [bmatchedPart_fun, variance_eq_sub bmemLpV]
  have hmean : ∫ ω : bV → ℝ, (bψ 1 (ω ⟨0, 0⟩) ^ 2 - 1) ∂bmuV = 0 := by
    have h := bintegralV (f := fun x => bψ 1 x ^ 2 - 1)
      (((measurable_bψ 1).pow_const 2).sub measurable_const) (⟨0, 0⟩ : bV)
    simp only [bUV] at h
    rw [h]
    norm_num [bψ]
  have hsq : bmuV[(fun ω : bV → ℝ => bψ 1 (ω ⟨0, 0⟩) ^ 2 - 1) ^ 2] = 9 / 4 := by
    have h := bintegralV (f := fun x => (bψ 1 x ^ 2 - 1) ^ 2)
      ((((measurable_bψ 1).pow_const 2).sub measurable_const).pow_const 2) (⟨0, 0⟩ : bV)
    simp only [bUV] at h
    simp only [Pi.pow_apply]
    rw [h]
    norm_num [bψ]
  rw [hsq, hmean]
  norm_num

/-- All hypotheses of `variance_matchedPart_le_cut_tot` hold on the biased model; the bound
is `16` and the quantity bounded is `9/4`. -/
theorem bstep2_closed_witness :
    variance (matchedPart bUV bψ bsitesV brIdxV barrV 0) bmuV ≤ 16
    ∧ variance (matchedPart bUV bψ bsitesV brIdxV barrV 0) bmuV = 9 / 4 := by
  refine ⟨le_trans (variance_matchedPart_le_cut_tot (rIdx := brIdxV) (lev := blev) (pt := bpt)
    (cutγ := 1) (totγ := 1) bIsBasisSystemV bHsite bHinj bHptf 0 (by norm_num) (by norm_num)
    (bHtot 0) bHcutA) ?_, bmatched_varianceV⟩
  have hcV : Fintype.card bV = 1 := by decide
  have hcK : Fintype.card bK = 1 := by decide
  rw [hcV, hcK]
  norm_num

/-- The same through `variance_matchedPart_le_cut_tot_ofCard` at `M = 1` and `B_0 = 2`. -/
theorem bstep2_closed_uniform_witness :
    variance (matchedPart bUV bψ bsitesV brIdxV barrV 0) bmuV ≤ 16
    ∧ variance (matchedPart bUV bψ bsitesV brIdxV barrV 0) bmuV = 9 / 4 := by
  refine ⟨le_trans (variance_matchedPart_le_cut_tot_ofCard (rIdx := brIdxV) (lev := blev)
    (pt := bpt) (M := 1) (cutγ := 1) (totγ := 1) bIsBasisSystemV
    (fun g x => by simp [bsitesV]) bHsite bHinj bHptf 0 (by norm_num) (by norm_num)
    (bHtot 0) bHcutA) ?_, bmatched_varianceV⟩
  have hcK : Fintype.card bK = 1 := by decide
  rw [hcK]
  norm_num

end StepTwoBiasedWitness

/-! #### A model with `B_0 = 2`

The biased law, with `B_0 = 2`, over the two-coordinate site type, where `|V| = 4` and
`M = |K| = 2`. The uniform and the `|V|`-dependent forms of clause (b) give `19611648` and
`5020581888`, a ratio of `max(B_0,1)^{4(|V| - M)} = 2^8`. -/

namespace StepTwoUniformWitness

open StepTwoWitness StepTwoClosedWitness

/-- The biased two-point law over the two-coordinate site type `sV`, with `|V| = 4` and
`M = |K| = 2`. -/
noncomputable def cmuS : Measure (sV → ℝ) := Measure.pi fun _ => bLaw

instance : IsProbabilityMeasure cmuS := by unfold cmuS; infer_instance

def cUS (v : sV) (ω : sV → ℝ) : ℝ := ω v

theorem cintegralS {f : ℝ → ℝ} (hf : Measurable f) (v : sV) :
    ∫ ω, f (cUS v ω) ∂cmuS = f 2 / 5 + 4 * f (-1/2) / 5 := by
  have hmap : cmuS.map (fun ω : sV → ℝ => ω v) = bLaw :=
    (MeasureTheory.measurePreserving_eval (fun _ => bLaw) v).map_eq
  have h1 : ∫ ω, f (cUS v ω) ∂cmuS = ∫ x, f x ∂bLaw := by
    rw [← hmap, integral_map (measurable_pi_apply v).aemeasurable hf.aestronglyMeasurable]
    rfl
  have hi1 : Integrable f ((1/5 : ℝ≥0∞) • Measure.dirac (2:ℝ)) :=
    (integrable_dirac' hf.stronglyMeasurable (by simp)).smul_measure (by simp)
  have hi2 : Integrable f ((4/5 : ℝ≥0∞) • Measure.dirac (-1/2:ℝ)) :=
    (integrable_dirac' hf.stronglyMeasurable (by simp)).smul_measure
      (by simp [ENNReal.div_eq_top])
  rw [h1, bLaw, integral_add_measure hi1 hi2, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  rw [show ((1/5 : ℝ≥0∞)).toReal = (1/5 : ℝ) by
      rw [ENNReal.toReal_div]; norm_num,
    show ((4/5 : ℝ≥0∞)).toReal = (4/5 : ℝ) by
      rw [ENNReal.toReal_div]; norm_num]
  simp only [smul_eq_mul]
  ring

/-- The basis system on this model, with `B_0 = 2`. -/
theorem cIsBasisSystemS : IsBasisSystem cmuS cUS bψ ({1} : Set (Fin 2)) 2 where
  measurable_latent v := measurable_pi_apply v
  measurable_psi := measurable_bψ
  indep := iIndepFun_pi (μ := fun _ : sV => bLaw) (X := fun _ => (id : ℝ → ℝ))
    (fun _ => aemeasurable_id)
  bound r x := by
    simp only [bψ]
    split_ifs <;> norm_num
  integral_eq_zero v {r} hr := by
    have hr1 : r = 1 := hr
    subst hr1
    rw [cintegralS (measurable_bψ 1) v]
    norm_num [bψ]
  integral_mul v r r' := by
    rw [cintegralS (f := fun x => bψ r x * bψ r' x)
      ((measurable_bψ r).mul (measurable_bψ r')) v]
    fin_cases r <;> fin_cases r' <;> norm_num [bψ]

/-- All hypotheses of `concentration_clause_b_general_closed_uniform` hold on this model,
where `|V| = 4` and `M = 2`. -/
theorem sclause_b_closed_uniform_witness :
    variance (fun ω => ∑ γ : Fin 2, ∑ γ' : Fin 2,
        slam γ * slam γ' * cvarEntry cUS bψ ssites srIdx sarr stag γ γ' ω) cmuS
      ≤ 19611648 := by
  refine le_trans (concentration_clause_b_general_closed_uniform (lev := slev) (pt := spt)
    (cutmax := 3) (totmax := 3) cIsBasisSystemS sHsite sHptc sHptf sHpos
    sHinj sHsep slam_sq_le sHcut sHcutA sHtot) ?_
  have hcK : Fintype.card sK = 2 := by decide
  rw [hcK]
  norm_num

/-- The same model through `concentration_clause_b_general_closed`, whose bound
`5020581888` is `2^8` times the uniform one. -/
theorem sclause_b_closed_weak_witness :
    variance (fun ω => ∑ γ : Fin 2, ∑ γ' : Fin 2,
        slam γ * slam γ' * cvarEntry cUS bψ ssites srIdx sarr stag γ γ' ω) cmuS
      ≤ 5020581888 := by
  refine le_trans (concentration_clause_b_general_closed (lev := slev) (pt := spt)
    (cutmax := 3) (totmax := 3) cIsBasisSystemS sHsite sHptc sHptf sHpos
    sHinj sHsep slam_sq_le sHcut sHcutA sHtot) ?_
  have hcV : Fintype.card sV = 4 := by decide
  have hcK : Fintype.card sK = 2 := by decide
  rw [hcV, hcK]
  norm_num

end StepTwoUniformWitness


end WitnessStepTwoClosed

end ClauseB

end Multiway
