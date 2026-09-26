import Multiway.Sequence
import Multiway.Leverage
import Multiway.CLTMartingale
import Multiway.CondIndep

/-!
# Implications of the primitive regressor design

This file formalizes Proposition SM.D.1 of the paper (implications for the within design) and
Lemma SM.B.9 (the cluster-size condition under the primitive design). Under the primitive-design
assumption `x_o = μ_o + ξ_o`, with innovations `ξ_o` conditionally independent across `o`, mean
zero, common covariance `Σ_ξ` and bounded fourth moments,
`n⁻¹X'Q_[Δ]X - [n⁻¹μ'Q_[Δ]μ + (1 - d_[Δ]/n)Σ_ξ] ⟶^p 0`. The first sections work along a
realization of the conditioning σ-algebra, with `μ` and `P_[Δ]` deterministic; later sections
take them `𝒟`-measurable and decondition through `condExpKernel P 𝒟`, and the last section
derives the moment identities from independence of the innovation vectors.

## Main results

* `designcond_tendstoInProb_of_primitive`, `designcond_design_ii`,
  `designcond_quadForm_lower_bound`: the three claims of Proposition SM.D.1.
* `quadvar_compl_le`: the variance bound `E[((Θ'QΘ)_{jk} - tr(Q)(Σ_ξ)_{jk})²] ≤ 2C·n`.
* `cgmsharp_bddInProb_of_moments`, `cgmsharp_tendstoInProb`: Lemma SM.B.9.
* `CondP.tendstoInMeasure_of_deconditioning`, `CondP.lintegral_le_of_deconditioning`:
  deconditioning bridges for convergence in measure and for lower-integral bounds.
* `designcond_tendstoInProb_uncond`, `designcond_design_ii_uncond`: the first and third claims
  with a random design.
-/

namespace Multiway
namespace PrimitiveDesign

open Filter MeasureTheory
open scoped Topology ENNReal Matrix Matrix.Norms.L2Operator

/-! ### Algebra -/

section Algebra

variable {O ι : Type*} [Fintype O]

/-- `X'QX = μ'Qμ + μ'QΘ + Θ'Qμ + Θ'QΘ`. -/
theorem gram_decomposition (Q : Matrix O O ℝ) (mu th : Matrix O ι ℝ) :
    (mu + th)ᵀ * Q * (mu + th)
      = muᵀ * Q * mu + (muᵀ * Q * th + (thᵀ * Q * mu + thᵀ * Q * th)) := by
  simp only [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
  abel

/-- `tr(Q_[Δ]) = n - d_[Δ]`. -/
theorem trace_compl [DecidableEq O] (Pm : Matrix O O ℝ) :
    ((1 : Matrix O O ℝ) - Pm).trace = (Fintype.card O : ℝ) - Pm.trace := by
  rw [Matrix.trace_sub]; simp

/-- `(Θ'QΘ)_{jk} = ∑_{(o,o')} Q_{oo'} Θ_{oj}Θ_{o'k}`. -/
theorem quad_apply (Q : Matrix O O ℝ) (th : Matrix O ι ℝ) (j k : ι) :
    (thᵀ * Q * th) j k = ∑ p : O × O, Q p.1 p.2 * (th p.1 j * th p.2 k) := by
  have h : ∀ o' : O, (thᵀ * Q) j o' * th o' k = ∑ o : O, Q o o' * (th o j * th o' k) := by
    intro o'
    rw [Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun o _ => by rw [Matrix.transpose_apply]; ring
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun o' _ => h o', Finset.sum_comm,
    Fintype.sum_prod_type]

/-- `(μ'QΘ)_{jk} = ∑_{o} (Qμ)_{oj} Θ_{ok}`, using symmetry of `Q`. -/
theorem cross_apply {Q : Matrix O O ℝ} (hsymm : Qᵀ = Q) (mu th : Matrix O ι ℝ) (j k : ι) :
    (muᵀ * Q * th) j k = ∑ o : O, (Q * mu) o j * th o k := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun o _ => ?_
  congr 1
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun o' _ => ?_
  have hq : Q o' o = Q o o' := by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hsymm o) o'
  rw [Matrix.transpose_apply, hq]; ring

/-- `(Θ'Qμ)_{jk} = ∑_{o} (Qμ)_{ok} Θ_{oj}`. No symmetry is needed here. -/
theorem cross_apply' (Q : Matrix O O ℝ) (mu th : Matrix O ι ℝ) (j k : ι) :
    (thᵀ * Q * mu) j k = ∑ o : O, (Q * mu) o k * th o j := by
  have h : ∀ o' : O, (thᵀ * Q) j o' * mu o' k = ∑ o : O, (Q o o' * mu o' k) * th o j := by
    intro o'
    rw [Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun o _ => by rw [Matrix.transpose_apply]; ring
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun o' _ => h o', Finset.sum_comm]
  exact Finset.sum_congr rfl fun o _ => by rw [Matrix.mul_apply, Finset.sum_mul]

/-- `∑_o ((Av)_{oj})² = (v'Av)_{jj}` for `A` symmetric idempotent. -/
theorem sum_sq_mulVec_eq {A : Matrix O O ℝ} (hs : Aᵀ = A) (hi : A * A = A)
    (v : Matrix O ι ℝ) (j : ι) : ∑ o : O, ((A * v) o j) ^ 2 = (vᵀ * A * v) j j := by
  have h1 : ∑ o : O, ((A * v) o j) ^ 2 = ((A * v)ᵀ * (A * v)) j j := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun o _ => by rw [Matrix.transpose_apply]; ring
  rw [h1, Matrix.transpose_mul, hs]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc A A v, hi, Matrix.mul_assoc]

/-- `Q` is a contraction: `‖Q_[Δ]μ_{·j}‖² ≤ ‖μ_{·j}‖²`. -/
theorem sum_sq_compl_mulVec_le [DecidableEq O] {Pm : Matrix O O ℝ} (hs : Pmᵀ = Pm)
    (hi : Pm * Pm = Pm) (v : Matrix O ι ℝ) (j : ι) :
    ∑ o : O, ((((1 : Matrix O O ℝ) - Pm) * v) o j) ^ 2 ≤ ∑ o : O, (v o j) ^ 2 := by
  have h1 := sum_sq_mulVec_eq (SuffLeverage.compl_transpose hs)
    (SuffLeverage.compl_mul_self hi) v j
  have h2 := sum_sq_mulVec_eq hs hi v j
  have h3 : ∑ o : O, (v o j) ^ 2 = (vᵀ * (1 : Matrix O O ℝ) * v) j j := by
    rw [Matrix.mul_one, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun o _ => by rw [Matrix.transpose_apply]; ring
  have h4 : (vᵀ * ((1 : Matrix O O ℝ) - Pm) * v) j j
      = (vᵀ * (1 : Matrix O O ℝ) * v) j j - (vᵀ * Pm * v) j j := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    simp [Matrix.sub_apply]
  have h5 : 0 ≤ (vᵀ * Pm * v) j j := by
    rw [← h2]; positivity
  rw [h1, h4, ← h3]
  linarith


/-- `‖Q_[Δ]‖_F² = tr(Q_[Δ])` for a symmetric idempotent `Q_[Δ]`. -/
theorem rectFrobSq_eq_trace_of_symmProj {A : Matrix O O ℝ} (hs : Aᵀ = A) (hi : A * A = A) :
    rectFrobSq A = A.trace := by
  rw [rectFrobSq, Matrix.trace]
  refine Finset.sum_congr rfl fun o _ => ?_
  have h1 : (A * A) o o = A o o := by rw [hi]
  rw [Matrix.mul_apply] at h1
  rw [Matrix.diag_apply, ← h1]
  refine Finset.sum_congr rfl fun o' _ => ?_
  have hq : A o' o = A o o' := by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hs o) o'
  rw [hq]; ring

end Algebra


/-! ### The second-moment structure of the primitive design -/

section Moments

variable {O ι : Type*} [Fintype O] [DecidableEq O] [Fintype ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `Θ`, the matrix with rows `ξ_o'`. -/
def theta (xi : O → ι → Ω → ℝ) (ω : Ω) : Matrix O ι ℝ := Matrix.of fun o j => xi o j ω

omit [DecidableEq O] [Fintype ι] in
/-- `E[∑_o c_o ξ_{ok} ∣ 𝒪] = 0`, along a realization of `𝒪`. -/
theorem integral_linForm (c : O → ℝ) {xi : O → ι → Ω → ℝ} (k : ι)
    (hint1 : ∀ o j, Integrable (fun ω => xi o j ω) P)
    (hmean : ∀ o j, ∫ ω, xi o j ω ∂P = 0) :
    ∫ ω, (∑ o : O, c o * xi o k ω) ∂P = 0 := by
  rw [integral_finsetSum _ (fun o _ => (hint1 o k).const_mul _)]
  simp [integral_const_mul, hmean]

omit [Fintype ι] in
/-- `E[(∑_o c_o ξ_{ok})²] = (∑_o c_o²)(Σ_ξ)_{kk}`; in particular
`Var((μ'QΘ)_{jk} ∣ 𝒪) = (Σ_ξ)_{kk}‖Qμ_{·j}‖²`. -/
theorem integral_linForm_sq (c : O → ℝ) {xi : O → ι → Ω → ℝ} {Sig : Matrix ι ι ℝ} (k : ι)
    (hint2 : ∀ o o' j j', Integrable (fun ω => xi o j ω * xi o' j' ω) P)
    (hcov : ∀ o o' j j', ∫ ω, xi o j ω * xi o' j' ω ∂P = if o = o' then Sig j j' else 0) :
    ∫ ω, (∑ o : O, c o * xi o k ω) ^ 2 ∂P = (∑ o : O, (c o) ^ 2) * Sig k k := by
  have hexp : ∀ ω, (∑ o : O, c o * xi o k ω) ^ 2
      = ∑ p : O × O, (c p.1 * c p.2) * (xi p.1 k ω * xi p.2 k ω) := by
    intro ω
    rw [sq, Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => by ring
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun p _ => (hint2 p.1 p.2 k k).const_mul _)]
  simp_rw [integral_const_mul, hcov]
  rw [Fintype.sum_prod_type]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun o _ => by ring

omit [Fintype ι] in
/-- `E[(Θ'AΘ)_{jk}] = tr(A)(Σ_ξ)_{jk}`; in particular
`E[Θ'QΘ ∣ 𝒪] = Σ_ξ tr(Q) = Σ_ξ(n - d_[Δ])`. -/
theorem integral_quad (A : Matrix O O ℝ) {xi : O → ι → Ω → ℝ} {Sig : Matrix ι ι ℝ} (j k : ι)
    (hint2 : ∀ o o' j j', Integrable (fun ω => xi o j ω * xi o' j' ω) P)
    (hcov : ∀ o o' j j', ∫ ω, xi o j ω * xi o' j' ω ∂P = if o = o' then Sig j j' else 0) :
    ∫ ω, ((theta xi ω)ᵀ * A * theta xi ω) j k ∂P = A.trace * Sig j k := by
  have hpt : ∀ ω, ((theta xi ω)ᵀ * A * theta xi ω) j k
      = ∑ p : O × O, A p.1 p.2 * (xi p.1 j ω * xi p.2 k ω) := fun ω => quad_apply _ _ j k
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun p _ => (hint2 p.1 p.2 j k).const_mul _)]
  simp_rw [integral_const_mul, hcov]
  rw [Fintype.sum_prod_type]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Matrix.trace, Finset.sum_mul]
  exact Finset.sum_congr rfl fun o _ => rfl

end Moments

/-! ### Chebyshev, and a congruence for `⟶^p` -/

section Chebyshev

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Chebyshev's inequality along the sequence.** A second-moment bound by a null sequence
gives convergence in probability. -/
theorem tendstoInProb_zero_of_integral_sq_le {Z : ℕ → Ω → ℝ}
    (hint : ∀ n, Integrable (fun ω => (Z n ω) ^ 2) P) {c : ℕ → ℝ}
    (hle : ∀ n, ∫ ω, (Z n ω) ^ 2 ∂P ≤ c n) (hc : Tendsto c atTop (𝓝 0)) :
    TendstoInMeasure P Z atTop (fun _ => (0 : ℝ)) := by
  have h1 : TendstoInMeasure P (fun n ω => (Z n ω) ^ 2) atTop (fun _ => (0 : ℝ)) := by
    refine Sequence.tendstoInProb_zero_of_integral_abs_le hint (fun n => ?_) hc
    have habs : (fun ω => |(Z n ω) ^ 2|) = fun ω => (Z n ω) ^ 2 :=
      funext fun ω => abs_of_nonneg (sq_nonneg _)
    rw [habs]; exact hle n
  have h2 := Sequence.tendstoInProb_sqrt_zero h1
  refine Sequence.tendstoInProb_zero_of_abs_le (Y := fun n ω => Real.sqrt ((Z n ω) ^ 2)) ?_ h2
  intro n
  filter_upwards with ω
  rw [Real.sqrt_sq_eq_abs, abs_abs]

/-- `⟶^p` transfers along an eventual equality of the sequences. -/
theorem tendstoInProb_congr' {Z W : ℕ → Ω → ℝ} {a : ℝ}
    (h : ∀ᶠ n : ℕ in atTop, Z n = W n) (hZ : TendstoInMeasure P Z atTop (fun _ => a)) :
    TendstoInMeasure P W atTop (fun _ => a) := by
  rw [tendstoInMeasure_iff_dist] at hZ ⊢
  intro ε hε
  refine (hZ ε hε).congr' ?_
  filter_upwards [h] with n hn
  rw [hn]

end Chebyshev

/-! ### Proposition SM.D.1 -/

section Main

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

omit [Fintype ι] in
/-- **The cross term.** `n⁻¹(μ'Q_[Δ]Θ)_{jk} ⟶^p 0`, by Chebyshev's inequality from
`Var((μ'QΘ)_{jk}) = (Σ_ξ)_{kk}‖Qμ_{·j}‖² = O(n)`. -/
theorem cross_tendstoInProb
    {xi : ∀ n, O n → ι → Ω → ℝ} {mu : ∀ n, Matrix (O n) ι ℝ} {Q : ∀ n, Matrix (O n) (O n) ℝ}
    {Sig : Matrix ι ι ℝ} {Cmu : ℝ} (j k : ι) (hSig : 0 ≤ Sig k k)
    (hsymm : ∀ n, (Q n)ᵀ = Q n)
    (hbd : ∀ n, ∑ o : O n, ((Q n * mu n) o j) ^ 2 ≤ Cmu * n)
    (hint2 : ∀ n o o' a b, Integrable (fun ω => xi n o a ω * xi n o' b ω) P)
    (hcov : ∀ n o o' a b, ∫ ω, xi n o a ω * xi n o' b ω ∂P = if o = o' then Sig a b else 0)
    (hintsq : ∀ n : ℕ, Integrable
      (fun ω => ((n : ℝ)⁻¹ * ((mu n)ᵀ * Q n * theta (xi n) ω) j k) ^ 2) P) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ((mu n)ᵀ * Q n * theta (xi n) ω) j k)
      atTop (fun _ => (0 : ℝ)) := by
  refine tendstoInProb_zero_of_integral_sq_le hintsq (c := fun n => Cmu * Sig k k / n) ?_
    (tendsto_const_div_atTop_nhds_zero_nat _)
  intro n
  have hpt : ∀ ω, ((n : ℝ)⁻¹ * ((mu n)ᵀ * Q n * theta (xi n) ω) j k) ^ 2
      = ((n : ℝ)⁻¹) ^ 2 * (∑ o : O n, (Q n * mu n) o j * xi n o k ω) ^ 2 := by
    intro ω
    rw [cross_apply (hsymm n)]
    rw [mul_pow]
    rfl
  simp_rw [hpt]
  rw [integral_const_mul, integral_linForm_sq (P := P) (fun o => (Q n * mu n) o j) k
    (fun o o' a b => hint2 n o o' a b) (fun o o' a b => hcov n o o' a b)]
  have hn : (0 : ℝ) ≤ ((n : ℝ)⁻¹) ^ 2 := sq_nonneg _
  have hstep : ((n : ℝ)⁻¹) ^ 2 * ((∑ o : O n, ((Q n * mu n) o j) ^ 2) * Sig k k)
      ≤ ((n : ℝ)⁻¹) ^ 2 * ((Cmu * n) * Sig k k) := by
    refine mul_le_mul_of_nonneg_left ?_ hn
    exact mul_le_mul_of_nonneg_right (hbd n) hSig
  refine hstep.trans ?_
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · simp [h0]
  · have hnz : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
    have heq : ((n : ℝ)⁻¹) ^ 2 * ((Cmu * n) * Sig k k) = Cmu * Sig k k / n := by
      field_simp
    rw [heq]

omit [(n : ℕ) → DecidableEq (O n)] [Fintype ι] in
/-- **The quadratic term.** `n⁻¹[(Θ'Q_[Δ]Θ)_{jk} - tr(Q_[Δ])(Σ_ξ)_{jk}] ⟶^p 0`. -/
theorem quadCentered_tendstoInProb
    {xi : ∀ n, O n → ι → Ω → ℝ} {Q : ∀ n, Matrix (O n) (O n) ℝ}
    {Sig : Matrix ι ι ℝ} {Cq : ℝ} (j k : ι)
    (hquadvar : ∀ n, ∫ ω, (((theta (xi n) ω)ᵀ * Q n * theta (xi n) ω) j k
        - (Q n).trace * Sig j k) ^ 2 ∂P ≤ Cq * n)
    (hintsq : ∀ n : ℕ, Integrable (fun ω => ((n : ℝ)⁻¹
      * ((((theta (xi n) ω)ᵀ * Q n * theta (xi n) ω) j k) - (Q n).trace * Sig j k)) ^ 2) P) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => (n : ℝ)⁻¹
        * (((theta (xi n) ω)ᵀ * Q n * theta (xi n) ω) j k - (Q n).trace * Sig j k))
      atTop (fun _ => (0 : ℝ)) := by
  refine tendstoInProb_zero_of_integral_sq_le hintsq (c := fun n => Cq / n) ?_
    (tendsto_const_div_atTop_nhds_zero_nat _)
  intro n
  have hpt : ∀ ω, ((n : ℝ)⁻¹
      * ((((theta (xi n) ω)ᵀ * Q n * theta (xi n) ω) j k) - (Q n).trace * Sig j k)) ^ 2
      = ((n : ℝ)⁻¹) ^ 2 * ((((theta (xi n) ω)ᵀ * Q n * theta (xi n) ω) j k)
          - (Q n).trace * Sig j k) ^ 2 := fun ω => mul_pow _ _ 2
  simp_rw [hpt]
  rw [integral_const_mul]
  have hn : (0 : ℝ) ≤ ((n : ℝ)⁻¹) ^ 2 := sq_nonneg _
  refine (mul_le_mul_of_nonneg_left (hquadvar n) hn).trans ?_
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · simp [h0]
  · have hnz : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
    have heq : ((n : ℝ)⁻¹) ^ 2 * (Cq * n) = Cq / n := by
      field_simp
    rw [heq]

/-- `(Θ'Qμ)_{jk} = (μ'QΘ)_{kj}` for a symmetric `Q`. -/
theorem cross_transpose_apply {O' ι' : Type*} [Fintype O'] {Q : Matrix O' O' ℝ}
    (hsymm : Qᵀ = Q) (mu th : Matrix O' ι' ℝ) (j k : ι') :
    (thᵀ * Q * mu) j k = (muᵀ * Q * th) k j := by
  rw [cross_apply' Q mu th j k, cross_apply hsymm mu th k j]

omit [Fintype ι] in
/-- **Proposition SM.D.1, first display**, entry by entry:
`n⁻¹X'Q_[Δ]X - [n⁻¹μ'Q_[Δ]μ + (1 - d_[Δ]/n)Σ_ξ] ⟶^p 0`, given the variance bound `hquadvar`. -/
theorem designcond_tendstoInProb
    {xi : ∀ n, O n → ι → Ω → ℝ} {mu : ∀ n, Matrix (O n) ι ℝ} {Pm : ∀ n, Matrix (O n) (O n) ℝ}
    {Sig : Matrix ι ι ℝ} {Cmu Cq : ℝ} (j k : ι) (hSigj : 0 ≤ Sig j j) (hSigk : 0 ≤ Sig k k)
    (hsymm : ∀ n, (Pm n)ᵀ = Pm n) (hidem : ∀ n, Pm n * Pm n = Pm n)
    (hcard : ∀ᶠ n : ℕ in atTop, (Fintype.card (O n) : ℝ) = (n : ℝ))
    (hmubd : ∀ (n : ℕ) (a : ι), ∑ o : O n, (mu n o a) ^ 2 ≤ Cmu * n)
    (hint2 : ∀ n o o' a b, Integrable (fun ω => xi n o a ω * xi n o' b ω) P)
    (hcov : ∀ n o o' a b, ∫ ω, xi n o a ω * xi n o' b ω ∂P = if o = o' then Sig a b else 0)
    (hquadvar : ∀ n : ℕ, ∫ ω, (((theta (xi n) ω)ᵀ
        * ((1 : Matrix (O n) (O n) ℝ) - Pm n) * theta (xi n) ω) j k
        - ((1 : Matrix (O n) (O n) ℝ) - Pm n).trace * Sig j k) ^ 2 ∂P ≤ Cq * n)
    (hintsq1 : ∀ n : ℕ, Integrable (fun ω => ((n : ℝ)⁻¹
      * ((mu n)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n) * theta (xi n) ω) j k) ^ 2) P)
    (hintsq2 : ∀ n : ℕ, Integrable (fun ω => ((n : ℝ)⁻¹
      * ((mu n)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n) * theta (xi n) ω) k j) ^ 2) P)
    (hintsq3 : ∀ n : ℕ, Integrable (fun ω => ((n : ℝ)⁻¹
      * ((((theta (xi n) ω)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n) * theta (xi n) ω) j k)
         - ((1 : Matrix (O n) (O n) ℝ) - Pm n).trace * Sig j k)) ^ 2) P) :
    TendstoInMeasure P
      (fun (n : ℕ) ω =>
        (n : ℝ)⁻¹ * ((mu n + theta (xi n) ω)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n)
            * (mu n + theta (xi n) ω)) j k
          - ((n : ℝ)⁻¹ * ((mu n)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n) * mu n) j k
             + (1 - (Pm n).trace / n) * Sig j k))
      atTop (fun _ => (0 : ℝ)) := by
  set Q : ∀ n, Matrix (O n) (O n) ℝ := fun n => (1 : Matrix (O n) (O n) ℝ) - Pm n with hQdef
  have hQs : ∀ n, (Q n)ᵀ = Q n := fun n => SuffLeverage.compl_transpose (hsymm n)
  have hbd : ∀ (a : ι) (n : ℕ), ∑ o : O n, ((Q n * mu n) o a) ^ 2 ≤ Cmu * n := by
    intro a n
    exact le_trans (sum_sq_compl_mulVec_le (hsymm n) (hidem n) (mu n) a) (hmubd n a)
  have h1 := cross_tendstoInProb (P := P) (xi := xi) (mu := mu) (Q := Q) (Sig := Sig)
    (Cmu := Cmu) j k hSigk hQs (hbd j) hint2 hcov hintsq1
  have h2 := cross_tendstoInProb (P := P) (xi := xi) (mu := mu) (Q := Q) (Sig := Sig)
    (Cmu := Cmu) k j hSigj hQs (hbd k) hint2 hcov hintsq2
  have h3 := quadCentered_tendstoInProb (P := P) (xi := xi) (Q := Q) (Sig := Sig)
    (Cq := Cq) j k hquadvar hintsq3
  have hsum := SuffLeverage.tendstoInProb_add h1 (SuffLeverage.tendstoInProb_add h2 h3)
  rw [add_zero, add_zero] at hsum
  refine tendstoInProb_congr' ?_ hsum
  filter_upwards [hcard, eventually_ge_atTop 1] with n hc hn
  funext ω
  have hnz : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hgram : ((mu n + theta (xi n) ω)ᵀ * Q n * (mu n + theta (xi n) ω)) j k
      = ((mu n)ᵀ * Q n * mu n) j k + (((mu n)ᵀ * Q n * theta (xi n) ω) j k
        + ((((theta (xi n) ω)ᵀ * Q n * mu n) j k)
           + (((theta (xi n) ω)ᵀ * Q n * theta (xi n) ω) j k))) := by
    rw [gram_decomposition]
    simp [Matrix.add_apply]
  have hswap : (((theta (xi n) ω)ᵀ * Q n * mu n) j k) = ((mu n)ᵀ * Q n * theta (xi n) ω) k j :=
    cross_transpose_apply (hQs n) (mu n) (theta (xi n) ω) j k
  have htr : (Q n).trace = (n : ℝ) - (Pm n).trace := by
    rw [hQdef]; rw [trace_compl, hc]
  rw [hgram, hswap, htr]
  field_simp
  ring

/-- A deterministic convergent sequence converges in probability. -/
theorem tendstoInProb_of_tendsto {b : ℕ → ℝ} {c : ℝ} (hb : Tendsto b atTop (𝓝 c)) :
    TendstoInMeasure P (fun (n : ℕ) (_ : Ω) => b n) atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hb ε hε
  filter_upwards [eventually_ge_atTop N] with n hn
  have hempty : {ω : Ω | ε ≤ dist (b n) c} = (∅ : Set Ω) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
    exact hN n hn
  rw [hempty, measure_empty]
  exact zero_le

omit [Fintype ι] in
/-- **Proposition SM.D.1, third claim**: if in addition `n⁻¹μ'Q_[Δ]μ → H_μ` and `d_[Δ]/n → κ`,
then part (ii) of the design assumption holds with `H = H_μ + (1-κ)Σ_ξ`, entry by entry. -/
theorem designcond_design_ii
    {xi : ∀ n, O n → ι → Ω → ℝ} {mu : ∀ n, Matrix (O n) ι ℝ} {Pm : ∀ n, Matrix (O n) (O n) ℝ}
    {Sig Hmu : Matrix ι ι ℝ} {κ : ℝ} (j k : ι)
    (hdiff : TendstoInMeasure P
      (fun (n : ℕ) ω =>
        (n : ℝ)⁻¹ * ((mu n + theta (xi n) ω)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n)
            * (mu n + theta (xi n) ω)) j k
          - ((n : ℝ)⁻¹ * ((mu n)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n) * mu n) j k
             + (1 - (Pm n).trace / n) * Sig j k))
      atTop (fun _ => (0 : ℝ)))
    (hHmu : Tendsto (fun n : ℕ => (n : ℝ)⁻¹
      * ((mu n)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n) * mu n) j k) atTop (𝓝 (Hmu j k)))
    (hkappa : Tendsto (fun n : ℕ => (Pm n).trace / n) atTop (𝓝 κ)) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ((mu n + theta (xi n) ω)ᵀ
        * ((1 : Matrix (O n) (O n) ℝ) - Pm n) * (mu n + theta (xi n) ω)) j k)
      atTop (fun _ => Hmu j k + (1 - κ) * Sig j k) := by
  have hb : Tendsto (fun n : ℕ => (n : ℝ)⁻¹
      * ((mu n)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n) * mu n) j k
      + (1 - (Pm n).trace / n) * Sig j k) atTop (𝓝 (Hmu j k + (1 - κ) * Sig j k)) := by
    refine hHmu.add ?_
    exact ((tendsto_const_nhds.sub hkappa).mul tendsto_const_nhds)
  have hsum := SuffLeverage.tendstoInProb_add hdiff (tendstoInProb_of_tendsto (Ω := Ω) (P := P) hb)
  rw [zero_add] at hsum
  refine tendstoInProb_congr' ?_ hsum
  filter_upwards with n
  funext ω
  ring

/-- **Proposition SM.D.1, second display**, in quadratic-form form:
`H = H_μ + (1-κ)Σ_ξ ⪰ (1-κ)Σ_ξ`. The eigenvalue bound `λ_min(H) ≥ (1-κ)λ_min(Σ_ξ)` follows by
the variational characterization of the smallest eigenvalue. -/
theorem designcond_quadForm_lower_bound {Hmu Sig : Matrix ι ι ℝ} {κ : ℝ}
    (hHmu : ∀ v : ι → ℝ, 0 ≤ ∑ a : ι, ∑ b : ι, v a * (Hmu a b * v b)) (v : ι → ℝ) :
    (1 - κ) * (∑ a : ι, ∑ b : ι, v a * (Sig a b * v b))
      ≤ ∑ a : ι, ∑ b : ι, v a * ((Hmu + (1 - κ) • Sig) a b * v b) := by
  have hsplit : ∑ a : ι, ∑ b : ι, v a * ((Hmu + (1 - κ) • Sig) a b * v b)
      = (∑ a : ι, ∑ b : ι, v a * (Hmu a b * v b))
        + (1 - κ) * (∑ a : ι, ∑ b : ι, v a * (Sig a b * v b)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hsplit]
  linarith [hHmu v]

end Main

/-! ### Witnesses -/

section Witness

/-- The moment-level witness model: one observation, one regressor, the innovation equal to
`1`, so that `Sigma_xi = 1`. -/
def witnessXi : Fin 1 -> Fin 1 -> Unit -> Real := fun _ _ _ => 1

theorem witnessXi_int (o o' : Fin 1) (a b : Fin 1) :
    Integrable (fun u => witnessXi o a u * witnessXi o' b u) (Measure.dirac ()) := by
  simp [witnessXi]

theorem witnessXi_cov (o o' : Fin 1) (a b : Fin 1) :
    (integral (Measure.dirac ()) fun u => witnessXi o a u * witnessXi o' b u)
      = if o = o' then (1 : Matrix (Fin 1) (Fin 1) Real) a b else 0 := by
  have ho : o = o' := Subsingleton.elim _ _
  have hab : a = b := Subsingleton.elim _ _
  subst ho; subst hab
  simp [witnessXi]

/-- Witness for `integral_quad`, with right-hand side `tr(A)(Sigma_xi)_{00} = 1`. -/
theorem integral_quad_witness :
    (integral (Measure.dirac ()) fun u =>
        ((theta witnessXi u)ᵀ * (1 : Matrix (Fin 1) (Fin 1) Real) * theta witnessXi u) 0 0)
      = 1 := by
  have h := integral_quad (P := Measure.dirac ()) (1 : Matrix (Fin 1) (Fin 1) Real)
    (xi := witnessXi) (Sig := (1 : Matrix (Fin 1) (Fin 1) Real)) 0 0
    witnessXi_int witnessXi_cov
  rw [h]
  simp

/-- Witness for `integral_linForm_sq`: with `c = 2` the right-hand side is `4`. -/
theorem integral_linForm_sq_witness :
    (integral (Measure.dirac ()) fun u => (∑ o : Fin 1, (2 : Real) * witnessXi o 0 u) ^ 2)
      = 4 := by
  have h := integral_linForm_sq (P := Measure.dirac ()) (fun _ : Fin 1 => (2 : Real))
    (xi := witnessXi) (Sig := (1 : Matrix (Fin 1) (Fin 1) Real)) 0
    witnessXi_int witnessXi_cov
  rw [h]
  norm_num

/-- The design-level witness: `n` observations, one regressor identically `1`, and the
trivial fixed-effects space, so that `d_{[Delta]} = 0` and `H_mu = 1`. -/
def witnessMu (n : Nat) : Matrix (Fin n) (Fin 1) Real := fun _ _ => 1

theorem witnessMu_gram (n : Nat) :
    ((witnessMu n)ᵀ * ((1 : Matrix (Fin n) (Fin n) Real) - (0 : Matrix (Fin n) (Fin n) Real)) * witnessMu n) 0 0 = (n : Real) := by
  rw [sub_zero, Matrix.mul_one, Matrix.mul_apply]
  simp [witnessMu, Matrix.transpose_apply]

theorem witnessXi0_cov (n : Nat) (o o' : Fin n) (a b : Fin 1) :
    (integral (Measure.dirac ()) fun _ : Unit => (0 : Real) * (0 : Real))
      = if o = o' then (0 : Matrix (Fin 1) (Fin 1) Real) a b else 0 := by
  by_cases h : o = o' <;> simp [h]

/-- Witness for `designcond_tendstoInProb` and `designcond_design_ii`, with limit
`H = H_mu + (1-kappa) Sigma_xi = 1`. The innovations are degenerate. -/
theorem designcond_witness :
    TendstoInMeasure (Measure.dirac ())
      (fun (n : Nat) (u : Unit) => (n : Real)⁻¹
        * ((witnessMu n + theta (fun (_ : Fin n) (_ : Fin 1) (_ : Unit) => (0 : Real)) u)ᵀ
            * ((1 : Matrix (Fin n) (Fin n) Real) - (0 : Matrix (Fin n) (Fin n) Real))
            * (witnessMu n + theta (fun (_ : Fin n) (_ : Fin 1) (_ : Unit) => (0 : Real)) u)) 0 0)
      atTop (fun _ => (1 : Real)) := by
  have hth : ∀ (n : Nat) (u : Unit),
      theta (fun (_ : Fin n) (_ : Fin 1) (_ : Unit) => (0 : Real)) u = 0 := by
    intro n u; ext o j; rfl
  have hHmu : Tendsto (fun n : Nat => (n : Real)⁻¹
      * ((witnessMu n)ᵀ * ((1 : Matrix (Fin n) (Fin n) Real) - (0 : Matrix (Fin n) (Fin n) Real)) * witnessMu n) 0 0)
      atTop (nhds ((1 : Matrix (Fin 1) (Fin 1) Real) 0 0)) := by
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : Matrix (Fin 1) (Fin 1) Real) 0 0))
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnz : (n : Real) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [witnessMu_gram, Matrix.one_apply_eq]
    field_simp
  have hdiff := designcond_tendstoInProb (P := Measure.dirac ())
    (xi := fun (n : Nat) (_ : Fin n) (_ : Fin 1) (_ : Unit) => (0 : Real))
    (mu := witnessMu) (Pm := fun n => (0 : Matrix (Fin n) (Fin n) Real))
    (Sig := (0 : Matrix (Fin 1) (Fin 1) Real)) (Cmu := 1) (Cq := 0) 0 0 (le_refl 0) (le_refl 0)
    (fun n => Matrix.transpose_zero) (fun n => by simp)
    (Filter.Eventually.of_forall fun n => by simp)
    (fun n a => by simp [witnessMu])
    (fun n o o' a b => by simp)
    (fun n o o' a b => witnessXi0_cov n o o' a b)
    (fun n => by simp [hth]) (fun n => by simp) (fun n => by simp) (fun n => by simp [hth])
  have := designcond_design_ii (P := Measure.dirac ())
    (xi := fun (n : Nat) (_ : Fin n) (_ : Fin 1) (_ : Unit) => (0 : Real))
    (mu := witnessMu) (Pm := fun n => (0 : Matrix (Fin n) (Fin n) Real))
    (Sig := (0 : Matrix (Fin 1) (Fin 1) Real)) (Hmu := (1 : Matrix (Fin 1) (Fin 1) Real))
    (κ := 0) 0 0 hdiff hHmu (by simp)
  simpa [Matrix.one_apply_eq] using this


end Witness


/-! ### Two steps of the proof of Lemma SM.B.9 -/

section CgmSharpGroundwork

variable {O ι : Type*} [Fintype O] [DecidableEq O] [Fintype ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

omit [Fintype ι] in
/-- `∑_{o≠o'} Q_{oo'}² = ∑_{o≠o'} P_{[Δ],oo'}² ≤ tr(P_[Δ]²) = d_[Δ]`, using
`Q_{oo'} = -P_{[Δ],oo'}` off the diagonal. -/
theorem sum_offDiag_sq_compl_le_trace {Pm : Matrix O O ℝ} (hs : Pmᵀ = Pm)
    (hi : Pm * Pm = Pm) :
    ∑ p ∈ (Finset.univ : Finset O).offDiag, (((1 : Matrix O O ℝ) - Pm) p.1 p.2) ^ 2
      ≤ Pm.trace := by
  have hentry : ∀ p ∈ (Finset.univ : Finset O).offDiag,
      (((1 : Matrix O O ℝ) - Pm) p.1 p.2) ^ 2 = (Pm p.1 p.2) ^ 2 := by
    intro p hp
    rw [Finset.mem_offDiag] at hp
    rw [Matrix.sub_apply, Matrix.one_apply_ne hp.2.2]
    ring
  rw [Finset.sum_congr rfl hentry]
  have hsub : (Finset.univ : Finset O).offDiag ⊆ (Finset.univ : Finset (O × O)) :=
    fun p _ => Finset.mem_univ p
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => sq_nonneg _)) ?_
  rw [← rectFrobSq_eq_trace_of_symmProj hs hi, rectFrobSq, Fintype.sum_prod_type]

omit [Fintype ι] in
/-- `E[x̃_o x̃_{o'}' ∣ 𝒪] = (QQ')_{oo'}Σ_ξ = Q_{oo'}Σ_ξ` for `X̃ = Q_[Δ]Θ`. -/
theorem integral_within_mul_within {Q : Matrix O O ℝ} (hs : Qᵀ = Q) (hi : Q * Q = Q)
    {xi : O → ι → Ω → ℝ} {Sig : Matrix ι ι ℝ} (o o₂ : O) (j k : ι)
    (hint2 : ∀ a b c d, Integrable (fun ω => xi a c ω * xi b d ω) P)
    (hcov : ∀ a b c d, ∫ ω, xi a c ω * xi b d ω ∂P = if a = b then Sig c d else 0) :
    ∫ ω, (Q * theta xi ω) o j * (Q * theta xi ω) o₂ k ∂P = Q o o₂ * Sig j k := by
  have hpt : ∀ ω, (Q * theta xi ω) o j * (Q * theta xi ω) o₂ k
      = ∑ p : O × O, (Q o p.1 * Q o₂ p.2) * (xi p.1 j ω * xi p.2 k ω) := by
    intro ω
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      simp only [theta, Matrix.of_apply]; ring
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun p _ => (hint2 p.1 p.2 j k).const_mul _)]
  simp_rw [integral_const_mul, hcov]
  rw [Fintype.sum_prod_type]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hQQ : ∀ a ∈ (Finset.univ : Finset O),
      Q o a * Q o₂ a * Sig j k = Q o a * Q a o₂ * Sig j k := by
    intro a _
    have hq : Q o₂ a = Q a o₂ := by
      simpa [Matrix.transpose_apply] using congrFun (congrFun hs a) o₂
    rw [hq]
  rw [Finset.sum_congr rfl hQQ, ← Finset.sum_mul, ← Matrix.mul_apply, hi]

end CgmSharpGroundwork


/-! ### The variance expansion

For a general coefficient matrix `A` and general `(j,k)`,
`∫ ((Θ'AΘ)_{jk} - tr(A)(Σ_ξ)_{jk})² ≤ 2C‖A‖_F²`: only the pairings of `(o,o')` with itself or
with its transpose survive, and each is bounded by the fourth-moment bound. At `A = Q_[Δ]` this
gives `quadvar_compl_le`, since `‖Q_[Δ]‖_F² = tr(Q_[Δ]) = n - d_[Δ]`.

The hypotheses `hfour`, `hpair4`, `hmixed4`, `hmixed4'`, `hquad4` state the four-fold moments
of the innovations (bounded by `C`, and the values conditional independence gives them);
they are derived from the primitive-design assumption at the end of the file. `hint4` is the
integrability of the four-fold products.
-/

section BilinearVariance

variable {O ι : Type*} [Fintype O] [DecidableEq O]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `G_{(o,o')} := ξ_{oj}ξ_{o'k} - 𝟙{o = o'}(Σ_ξ)_{jk}`, the centered innovation pair, so that
`Θ'AΘ - tr(A)Σ_ξ = ∑_{(o,o')} A_{oo'}G_{(o,o')}`. -/
def centPair (xi : O → ι → Ω → ℝ) (Sig : Matrix ι ι ℝ) (j k : ι) (p : O × O) (ω : Ω) : ℝ :=
  xi p.1 j ω * xi p.2 k ω - (if p.1 = p.2 then Sig j k else 0)

omit [MeasurableSpace Ω] in
/-- `(Θ'AΘ)_{jk} - tr(A)(Σ_ξ)_{jk} = ∑_{(o,o')} A_{oo'}G_{(o,o')}`: the centering of
`integral_quad` written as a single sum over index pairs. -/
theorem quad_sub_trace_eq_sum (A : Matrix O O ℝ) (xi : O → ι → Ω → ℝ) (Sig : Matrix ι ι ℝ)
    (j k : ι) (ω : Ω) :
    ((theta xi ω)ᵀ * A * theta xi ω) j k - A.trace * Sig j k
      = ∑ p : O × O, A p.1 p.2 * centPair xi Sig j k p ω := by
  have hsplit : ∑ p : O × O, A p.1 p.2 * centPair xi Sig j k p ω
      = (∑ p : O × O, A p.1 p.2 * (xi p.1 j ω * xi p.2 k ω))
        - ∑ p : O × O, A p.1 p.2 * (if p.1 = p.2 then Sig j k else 0) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by rw [centPair]; ring
  have htr : ∑ p : O × O, A p.1 p.2 * (if p.1 = p.2 then Sig j k else 0)
      = A.trace * Sig j k := by
    rw [Fintype.sum_prod_type, Matrix.trace, Finset.sum_mul]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Finset.sum_eq_single o]
    · simp
    · intro o' _ hne; simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ o) h
  rw [hsplit, htr, quad_apply]
  rfl

variable {xi : O → ι → Ω → ℝ} {Sig : Matrix ι ι ℝ} {j k : ι} {C : ℝ}

omit [Fintype O] in
theorem integrable_centPair_mul
    (hint2 : ∀ o o' a b, Integrable (fun ω => xi o a ω * xi o' b ω) P)
    (hint4 : ∀ r s : O × O, Integrable
      (fun ω => (xi r.1 j ω * xi r.2 k ω) * (xi s.1 j ω * xi s.2 k ω)) P)
    [IsFiniteMeasure P] (p q : O × O) :
    Integrable (fun ω => centPair xi Sig j k p ω * centPair xi Sig j k q ω) P := by
  have hpt : (fun ω => centPair xi Sig j k p ω * centPair xi Sig j k q ω)
      = fun ω => (xi p.1 j ω * xi p.2 k ω) * (xi q.1 j ω * xi q.2 k ω)
        - (if q.1 = q.2 then Sig j k else 0) * (xi p.1 j ω * xi p.2 k ω)
        - (if p.1 = p.2 then Sig j k else 0) * (xi q.1 j ω * xi q.2 k ω)
        + (if p.1 = p.2 then Sig j k else 0) * (if q.1 = q.2 then Sig j k else 0) := by
    funext ω; simp only [centPair]; ring
  rw [hpt]
  exact (((hint4 p q).sub ((hint2 p.1 p.2 j k).const_mul _)).sub
    ((hint2 q.1 q.2 j k).const_mul _)).add (integrable_const _)

omit [Fintype O] in
/-- `E[G_pG_q] = E[ξ_{p₁j}ξ_{p₂k}ξ_{q₁j}ξ_{q₂k}] - 𝟙{p diagonal}𝟙{q diagonal}(Σ_ξ)²_{jk}`. -/
theorem integral_centPair_mul [IsProbabilityMeasure P]
    (hint2 : ∀ o o' a b, Integrable (fun ω => xi o a ω * xi o' b ω) P)
    (hint4 : ∀ r s : O × O, Integrable
      (fun ω => (xi r.1 j ω * xi r.2 k ω) * (xi s.1 j ω * xi s.2 k ω)) P)
    (hcov : ∀ o o' a b, ∫ ω, xi o a ω * xi o' b ω ∂P = if o = o' then Sig a b else 0)
    (p q : O × O) :
    ∫ ω, centPair xi Sig j k p ω * centPair xi Sig j k q ω ∂P
      = (∫ ω, (xi p.1 j ω * xi p.2 k ω) * (xi q.1 j ω * xi q.2 k ω) ∂P)
        - (if p.1 = p.2 then Sig j k else 0) * (if q.1 = q.2 then Sig j k else 0) := by
  have hpt : (fun ω => centPair xi Sig j k p ω * centPair xi Sig j k q ω)
      = fun ω => (xi p.1 j ω * xi p.2 k ω) * (xi q.1 j ω * xi q.2 k ω)
        - (if q.1 = q.2 then Sig j k else 0) * (xi p.1 j ω * xi p.2 k ω)
        - (if p.1 = p.2 then Sig j k else 0) * (xi q.1 j ω * xi q.2 k ω)
        + (if p.1 = p.2 then Sig j k else 0) * (if q.1 = q.2 then Sig j k else 0) := by
    funext ω; simp only [centPair]; ring
  have hA : Integrable
      (fun ω => (xi p.1 j ω * xi p.2 k ω) * (xi q.1 j ω * xi q.2 k ω)) P := hint4 p q
  have hB : Integrable
      (fun ω => (if q.1 = q.2 then Sig j k else 0) * (xi p.1 j ω * xi p.2 k ω)) P :=
    (hint2 p.1 p.2 j k).const_mul _
  have hC : Integrable
      (fun ω => (if p.1 = p.2 then Sig j k else 0) * (xi q.1 j ω * xi q.2 k ω)) P :=
    (hint2 q.1 q.2 j k).const_mul _
  have hAB : Integrable (fun ω => (xi p.1 j ω * xi p.2 k ω) * (xi q.1 j ω * xi q.2 k ω)
      - (if q.1 = q.2 then Sig j k else 0) * (xi p.1 j ω * xi p.2 k ω)) P := hA.sub hB
  have hABC : Integrable (fun ω => (xi p.1 j ω * xi p.2 k ω) * (xi q.1 j ω * xi q.2 k ω)
      - (if q.1 = q.2 then Sig j k else 0) * (xi p.1 j ω * xi p.2 k ω)
      - (if p.1 = p.2 then Sig j k else 0) * (xi q.1 j ω * xi q.2 k ω)) P := hAB.sub hC
  rw [hpt, integral_add hABC (integrable_const _), integral_sub hAB hC,
    integral_sub hA hB, integral_const_mul, integral_const_mul, integral_const, hcov, hcov]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  ring

omit [Fintype O] in
/-- The diagonal pairing is bounded by the fourth-moment bound: `E[G_p²] ≤ C`. -/
theorem integral_centPair_self_le [IsProbabilityMeasure P]
    (hint2 : ∀ o o' a b, Integrable (fun ω => xi o a ω * xi o' b ω) P)
    (hint4 : ∀ r s : O × O, Integrable
      (fun ω => (xi r.1 j ω * xi r.2 k ω) * (xi s.1 j ω * xi s.2 k ω)) P)
    (hcov : ∀ o o' a b, ∫ ω, xi o a ω * xi o' b ω ∂P = if o = o' then Sig a b else 0)
    (hfour : ∀ o o' : O, ∫ ω, (xi o j ω * xi o' k ω) ^ 2 ∂P ≤ C) (p : O × O) :
    ∫ ω, centPair xi Sig j k p ω * centPair xi Sig j k p ω ∂P ≤ C := by
  rw [integral_centPair_mul hint2 hint4 hcov p p]
  have hsq : ∫ ω, (xi p.1 j ω * xi p.2 k ω) * (xi p.1 j ω * xi p.2 k ω) ∂P
      = ∫ ω, (xi p.1 j ω * xi p.2 k ω) ^ 2 ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    ring
  rw [hsq]
  have h0 : (0 : ℝ) ≤ (if p.1 = p.2 then Sig j k else 0) * (if p.1 = p.2 then Sig j k else 0) :=
    mul_self_nonneg _
  linarith [hfour p.1 p.2]

omit [Fintype O] in
/-- Every surviving pairing is at most `C`: `|E[G_pG_q]| ≤ (E[G_p²] + E[G_q²])/2`. -/
theorem abs_integral_centPair_mul_le [IsProbabilityMeasure P]
    (hint2 : ∀ o o' a b, Integrable (fun ω => xi o a ω * xi o' b ω) P)
    (hint4 : ∀ r s : O × O, Integrable
      (fun ω => (xi r.1 j ω * xi r.2 k ω) * (xi s.1 j ω * xi s.2 k ω)) P)
    (hcov : ∀ o o' a b, ∫ ω, xi o a ω * xi o' b ω ∂P = if o = o' then Sig a b else 0)
    (hfour : ∀ o o' : O, ∫ ω, (xi o j ω * xi o' k ω) ^ 2 ∂P ≤ C) (p q : O × O) :
    |∫ ω, centPair xi Sig j k p ω * centPair xi Sig j k q ω ∂P| ≤ C := by
  have hipq := integrable_centPair_mul (Sig := Sig) (j := j) (k := k) hint2 hint4 p q
  have hipp := integrable_centPair_mul (Sig := Sig) (j := j) (k := k) hint2 hint4 p p
  have hiqq := integrable_centPair_mul (Sig := Sig) (j := j) (k := k) hint2 hint4 q q
  have hmid : ∫ ω, |centPair xi Sig j k p ω * centPair xi Sig j k q ω| ∂P
      ≤ ∫ ω, (centPair xi Sig j k p ω * centPair xi Sig j k p ω
          + centPair xi Sig j k q ω * centPair xi Sig j k q ω) / 2 ∂P := by
    refine integral_mono hipq.abs ((hipp.add hiqq).div_const 2) (fun ω => ?_)
    have hs := sq_nonneg (centPair xi Sig j k p ω - centPair xi Sig j k q ω)
    have hs' := sq_nonneg (centPair xi Sig j k p ω + centPair xi Sig j k q ω)
    rw [abs_le]
    constructor <;> nlinarith [hs, hs']
  have hsplit : ∫ ω, (centPair xi Sig j k p ω * centPair xi Sig j k p ω
        + centPair xi Sig j k q ω * centPair xi Sig j k q ω) / 2 ∂P
      = ((∫ ω, centPair xi Sig j k p ω * centPair xi Sig j k p ω ∂P)
          + ∫ ω, centPair xi Sig j k q ω * centPair xi Sig j k q ω ∂P) / 2 := by
    rw [integral_div, integral_add hipp hiqq]
  have habs : |∫ ω, centPair xi Sig j k p ω * centPair xi Sig j k q ω ∂P|
      ≤ ∫ ω, |centPair xi Sig j k p ω * centPair xi Sig j k q ω| ∂P := by
    simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (μ := P) (f := fun ω => centPair xi Sig j k p ω * centPair xi Sig j k q ω)
  have hp := integral_centPair_self_le hint2 hint4 hcov hfour p
  have hq := integral_centPair_self_le hint2 hint4 hcov hfour q
  rw [hsplit] at hmid
  linarith

omit [Fintype O] in
/-- Only the pairings of `p` with itself or with its transpose survive: `E[G_pG_q] = 0` whenever
`q ≠ p` and `q ≠ pᵀ`. -/
theorem integral_centPair_mul_eq_zero [IsProbabilityMeasure P]
    (hint2 : ∀ o o' a b, Integrable (fun ω => xi o a ω * xi o' b ω) P)
    (hint4 : ∀ r s : O × O, Integrable
      (fun ω => (xi r.1 j ω * xi r.2 k ω) * (xi s.1 j ω * xi s.2 k ω)) P)
    (hcov : ∀ o o' a b, ∫ ω, xi o a ω * xi o' b ω ∂P = if o = o' then Sig a b else 0)
    (hpair4 : ∀ o o' : O, o ≠ o' →
      ∫ ω, (xi o j ω * xi o k ω) * (xi o' j ω * xi o' k ω) ∂P = Sig j k * Sig j k)
    (hmixed4 : ∀ (a : O) (p : O × O), p.1 ≠ p.2 →
      ∫ ω, (xi a j ω * xi a k ω) * (xi p.1 j ω * xi p.2 k ω) ∂P = 0)
    (hmixed4' : ∀ (a : O) (p : O × O), p.1 ≠ p.2 →
      ∫ ω, (xi p.1 j ω * xi p.2 k ω) * (xi a j ω * xi a k ω) ∂P = 0)
    (hquad4 : ∀ p q : O × O, p.1 ≠ p.2 → q.1 ≠ q.2 → q ≠ p → q ≠ (p.2, p.1) →
      ∫ ω, (xi p.1 j ω * xi p.2 k ω) * (xi q.1 j ω * xi q.2 k ω) ∂P = 0)
    (p q : O × O) (hq : q ≠ p) (hqT : q ≠ (p.2, p.1)) :
    ∫ ω, centPair xi Sig j k p ω * centPair xi Sig j k q ω ∂P = 0 := by
  rw [integral_centPair_mul hint2 hint4 hcov p q]
  by_cases hp : p.1 = p.2
  · have hcp : (if p.1 = p.2 then Sig j k else 0) = Sig j k := by simp [hp]
    by_cases hqd : q.1 = q.2
    · have hcq : (if q.1 = q.2 then Sig j k else 0) = Sig j k := by simp [hqd]
      have hne : p.1 ≠ q.1 := by
        intro h
        exact hq (Prod.ext_iff.mpr ⟨h.symm, by rw [← hqd, ← h, hp]⟩)
      rw [hcp, hcq, ← hp, ← hqd, hpair4 p.1 q.1 hne, sub_self]
    · have hcq : (if q.1 = q.2 then Sig j k else 0) = 0 := by simp [hqd]
      rw [hcp, hcq, ← hp, hmixed4 p.1 q hqd]
      ring
  · have hcp : (if p.1 = p.2 then Sig j k else 0) = 0 := by simp [hp]
    by_cases hqd : q.1 = q.2
    · have hcq : (if q.1 = q.2 then Sig j k else 0) = Sig j k := by simp [hqd]
      rw [hcp, hcq, ← hqd, hmixed4' q.1 p hp]
      ring
    · have hcq : (if q.1 = q.2 then Sig j k else 0) = 0 := by simp [hqd]
      rw [hcp, hcq, hquad4 p q hp hqd hq hqT]
      ring

/-- **The bilinear variance bound**, at a general coefficient matrix `A` and general `(j,k)`:
`E[((Θ'AΘ)_{jk} - tr(A)(Σ_ξ)_{jk})²] ≤ 2C‖A‖_F²`. The factor `2` counts the two surviving
pairings. -/
theorem integral_quad_centered_sq_le [IsProbabilityMeasure P] (A : Matrix O O ℝ) (hC : 0 ≤ C)
    (hint2 : ∀ o o' a b, Integrable (fun ω => xi o a ω * xi o' b ω) P)
    (hint4 : ∀ r s : O × O, Integrable
      (fun ω => (xi r.1 j ω * xi r.2 k ω) * (xi s.1 j ω * xi s.2 k ω)) P)
    (hcov : ∀ o o' a b, ∫ ω, xi o a ω * xi o' b ω ∂P = if o = o' then Sig a b else 0)
    (hfour : ∀ o o' : O, ∫ ω, (xi o j ω * xi o' k ω) ^ 2 ∂P ≤ C)
    (hpair4 : ∀ o o' : O, o ≠ o' →
      ∫ ω, (xi o j ω * xi o k ω) * (xi o' j ω * xi o' k ω) ∂P = Sig j k * Sig j k)
    (hmixed4 : ∀ (a : O) (p : O × O), p.1 ≠ p.2 →
      ∫ ω, (xi a j ω * xi a k ω) * (xi p.1 j ω * xi p.2 k ω) ∂P = 0)
    (hmixed4' : ∀ (a : O) (p : O × O), p.1 ≠ p.2 →
      ∫ ω, (xi p.1 j ω * xi p.2 k ω) * (xi a j ω * xi a k ω) ∂P = 0)
    (hquad4 : ∀ p q : O × O, p.1 ≠ p.2 → q.1 ≠ q.2 → q ≠ p → q ≠ (p.2, p.1) →
      ∫ ω, (xi p.1 j ω * xi p.2 k ω) * (xi q.1 j ω * xi q.2 k ω) ∂P = 0) :
    ∫ ω, (((theta xi ω)ᵀ * A * theta xi ω) j k - A.trace * Sig j k) ^ 2 ∂P
      ≤ 2 * C * rectFrobSq A := by
  classical
  have hintpq : ∀ p q : O × O, Integrable
      (fun ω => (A p.1 p.2 * A q.1 q.2)
        * (centPair xi Sig j k p ω * centPair xi Sig j k q ω)) P :=
    fun p q => (integrable_centPair_mul (Sig := Sig) (j := j) (k := k) hint2 hint4 p q).const_mul _
  have hpt : ∀ ω, (((theta xi ω)ᵀ * A * theta xi ω) j k - A.trace * Sig j k) ^ 2
      = ∑ p : O × O, ∑ q : O × O, (A p.1 p.2 * A q.1 q.2)
          * (centPair xi Sig j k p ω * centPair xi Sig j k q ω) := by
    intro ω
    rw [quad_sub_trace_eq_sum A xi Sig j k ω, pow_two, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => hintpq p q))]
  have hinner : ∀ p : O × O,
      ∫ ω, ∑ q : O × O, (A p.1 p.2 * A q.1 q.2)
        * (centPair xi Sig j k p ω * centPair xi Sig j k q ω) ∂P
      = ∑ q : O × O, (A p.1 p.2 * A q.1 q.2)
          * ∫ ω, centPair xi Sig j k p ω * centPair xi Sig j k q ω ∂P := by
    intro p
    rw [integral_finsetSum _ (fun q _ => hintpq p q)]
    exact Finset.sum_congr rfl fun q _ => integral_const_mul _ _
  simp_rw [hinner]
  have hzero : ∀ p q : O × O, q ∉ ({p, (p.2, p.1)} : Finset (O × O)) →
      (A p.1 p.2 * A q.1 q.2)
        * ∫ ω, centPair xi Sig j k p ω * centPair xi Sig j k q ω ∂P = 0 := by
    intro p q hmem
    rw [Finset.mem_insert, Finset.mem_singleton] at hmem
    push Not at hmem
    rw [integral_centPair_mul_eq_zero hint2 hint4 hcov hpair4 hmixed4 hmixed4' hquad4
      p q hmem.1 hmem.2, mul_zero]
  have hbound : ∀ p : O × O, ∑ q : O × O, (A p.1 p.2 * A q.1 q.2)
        * ∫ ω, centPair xi Sig j k p ω * centPair xi Sig j k q ω ∂P
      ≤ C * (A p.1 p.2) ^ 2 + C * |A p.1 p.2 * A p.2 p.1| := by
    intro p
    rw [← Finset.sum_subset (Finset.subset_univ ({p, (p.2, p.1)} : Finset (O × O)))
      (fun q _ hmem => hzero p q hmem)]
    have hdiag : (A p.1 p.2 * A p.1 p.2)
        * ∫ ω, centPair xi Sig j k p ω * centPair xi Sig j k p ω ∂P ≤ C * (A p.1 p.2) ^ 2 := by
      have h1 := integral_centPair_self_le hint2 hint4 hcov hfour p
      nlinarith [sq_nonneg (A p.1 p.2)]
    have hoff : (A p.1 p.2 * A p.2 p.1)
        * ∫ ω, centPair xi Sig j k p ω * centPair xi Sig j k (p.2, p.1) ω ∂P
        ≤ C * |A p.1 p.2 * A p.2 p.1| := by
      have h1 := abs_integral_centPair_mul_le hint2 hint4 hcov hfour p (p.2, p.1)
      have h2 : (A p.1 p.2 * A p.2 p.1)
          * ∫ ω, centPair xi Sig j k p ω * centPair xi Sig j k (p.2, p.1) ω ∂P
          ≤ |A p.1 p.2 * A p.2 p.1|
            * |∫ ω, centPair xi Sig j k p ω * centPair xi Sig j k (p.2, p.1) ω ∂P| := by
        rw [← abs_mul]
        exact le_abs_self _
      have h3 : |A p.1 p.2 * A p.2 p.1|
          * |∫ ω, centPair xi Sig j k p ω * centPair xi Sig j k (p.2, p.1) ω ∂P|
          ≤ |A p.1 p.2 * A p.2 p.1| * C :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      calc _ ≤ _ := h2
        _ ≤ |A p.1 p.2 * A p.2 p.1| * C := h3
        _ = C * |A p.1 p.2 * A p.2 p.1| := mul_comm _ _
    by_cases hsw : (p.2, p.1) = p
    · have hset : ({p, (p.2, p.1)} : Finset (O × O)) = {p} := by rw [hsw]; simp
      rw [hset, Finset.sum_singleton]
      have hnn : 0 ≤ C * |A p.1 p.2 * A p.2 p.1| := mul_nonneg hC (abs_nonneg _)
      linarith
    · rw [Finset.sum_pair (fun hc => hsw hc.symm)]
      exact add_le_add hdiag hoff
  refine le_trans (Finset.sum_le_sum (fun p _ => hbound p)) ?_
  have hfrob : rectFrobSq A = ∑ p : O × O, (A p.1 p.2) ^ 2 := by
    rw [rectFrobSq, Fintype.sum_prod_type]
  have hswap : ∑ p : O × O, (A p.2 p.1) ^ 2 = ∑ p : O × O, (A p.1 p.2) ^ 2 :=
    Fintype.sum_equiv (Equiv.prodComm O O) _ _ (fun p => rfl)
  have habs : ∑ p : O × O, |A p.1 p.2 * A p.2 p.1| ≤ ∑ p : O × O, (A p.1 p.2) ^ 2 := by
    have hstep : ∑ p : O × O, |A p.1 p.2 * A p.2 p.1|
        ≤ ∑ p : O × O, ((A p.1 p.2) ^ 2 + (A p.2 p.1) ^ 2) / 2 := by
      refine Finset.sum_le_sum (fun p _ => ?_)
      have := sq_nonneg (|A p.1 p.2| - |A p.2 p.1|)
      rw [abs_mul]
      nlinarith [sq_abs (A p.1 p.2), sq_abs (A p.2 p.1)]
    have hhalf : ∑ p : O × O, ((A p.1 p.2) ^ 2 + (A p.2 p.1) ^ 2) / 2
        = ∑ p : O × O, (A p.1 p.2) ^ 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, hswap]
      ring
    linarith [hstep, hhalf.le, hhalf.ge]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hfrob]
  have hsum2 : C * ∑ p : O × O, |A p.1 p.2 * A p.2 p.1| ≤ C * ∑ p : O × O, (A p.1 p.2) ^ 2 :=
    mul_le_mul_of_nonneg_left habs hC
  linarith

/-- At `A = Q_[Δ]` the bound is `2C‖Q_[Δ]‖_F² = 2C·tr(Q_[Δ]) = 2C(n - d_[Δ]) ≤ 2C·n`. -/
theorem quadvar_compl_le [IsProbabilityMeasure P] {Pm : Matrix O O ℝ} (hC : 0 ≤ C)
    (hs : Pmᵀ = Pm) (hi : Pm * Pm = Pm)
    (hint2 : ∀ o o' a b, Integrable (fun ω => xi o a ω * xi o' b ω) P)
    (hint4 : ∀ r s : O × O, Integrable
      (fun ω => (xi r.1 j ω * xi r.2 k ω) * (xi s.1 j ω * xi s.2 k ω)) P)
    (hcov : ∀ o o' a b, ∫ ω, xi o a ω * xi o' b ω ∂P = if o = o' then Sig a b else 0)
    (hfour : ∀ o o' : O, ∫ ω, (xi o j ω * xi o' k ω) ^ 2 ∂P ≤ C)
    (hpair4 : ∀ o o' : O, o ≠ o' →
      ∫ ω, (xi o j ω * xi o k ω) * (xi o' j ω * xi o' k ω) ∂P = Sig j k * Sig j k)
    (hmixed4 : ∀ (a : O) (p : O × O), p.1 ≠ p.2 →
      ∫ ω, (xi a j ω * xi a k ω) * (xi p.1 j ω * xi p.2 k ω) ∂P = 0)
    (hmixed4' : ∀ (a : O) (p : O × O), p.1 ≠ p.2 →
      ∫ ω, (xi p.1 j ω * xi p.2 k ω) * (xi a j ω * xi a k ω) ∂P = 0)
    (hquad4 : ∀ p q : O × O, p.1 ≠ p.2 → q.1 ≠ q.2 → q ≠ p → q ≠ (p.2, p.1) →
      ∫ ω, (xi p.1 j ω * xi p.2 k ω) * (xi q.1 j ω * xi q.2 k ω) ∂P = 0) :
    ∫ ω, (((theta xi ω)ᵀ * ((1 : Matrix O O ℝ) - Pm) * theta xi ω) j k
        - ((1 : Matrix O O ℝ) - Pm).trace * Sig j k) ^ 2 ∂P
      ≤ 2 * C * (Fintype.card O : ℝ) := by
  refine le_trans (integral_quad_centered_sq_le ((1 : Matrix O O ℝ) - Pm) hC hint2 hint4 hcov
    hfour hpair4 hmixed4 hmixed4' hquad4) ?_
  rw [rectFrobSq_eq_trace_of_symmProj (SuffLeverage.compl_transpose hs)
    (SuffLeverage.compl_mul_self hi), trace_compl]
  have htr : 0 ≤ Pm.trace := Cgm.trace_nonneg_of_symmProj hs hi
  nlinarith

/-- The raw second moment: `E[((Θ'AΘ)_{jk})²] ≤ 2(tr(A)Σ_{jk})² + 4C‖A‖_F²`. -/
theorem integral_quad_sq_le [IsProbabilityMeasure P] (A : Matrix O O ℝ) (hC : 0 ≤ C)
    (hint2 : ∀ o o' a b, Integrable (fun ω => xi o a ω * xi o' b ω) P)
    (hint4 : ∀ r s : O × O, Integrable
      (fun ω => (xi r.1 j ω * xi r.2 k ω) * (xi s.1 j ω * xi s.2 k ω)) P)
    (hcov : ∀ o o' a b, ∫ ω, xi o a ω * xi o' b ω ∂P = if o = o' then Sig a b else 0)
    (hfour : ∀ o o' : O, ∫ ω, (xi o j ω * xi o' k ω) ^ 2 ∂P ≤ C)
    (hpair4 : ∀ o o' : O, o ≠ o' →
      ∫ ω, (xi o j ω * xi o k ω) * (xi o' j ω * xi o' k ω) ∂P = Sig j k * Sig j k)
    (hmixed4 : ∀ (a : O) (p : O × O), p.1 ≠ p.2 →
      ∫ ω, (xi a j ω * xi a k ω) * (xi p.1 j ω * xi p.2 k ω) ∂P = 0)
    (hmixed4' : ∀ (a : O) (p : O × O), p.1 ≠ p.2 →
      ∫ ω, (xi p.1 j ω * xi p.2 k ω) * (xi a j ω * xi a k ω) ∂P = 0)
    (hquad4 : ∀ p q : O × O, p.1 ≠ p.2 → q.1 ≠ q.2 → q ≠ p → q ≠ (p.2, p.1) →
      ∫ ω, (xi p.1 j ω * xi p.2 k ω) * (xi q.1 j ω * xi q.2 k ω) ∂P = 0)
    (hsq : Integrable (fun ω => (((theta xi ω)ᵀ * A * theta xi ω) j k) ^ 2) P)
    (hcsq : Integrable
      (fun ω => (((theta xi ω)ᵀ * A * theta xi ω) j k - A.trace * Sig j k) ^ 2) P) :
    ∫ ω, (((theta xi ω)ᵀ * A * theta xi ω) j k) ^ 2 ∂P
      ≤ 2 * (A.trace * Sig j k) ^ 2 + 4 * C * rectFrobSq A := by
  have hvar := integral_quad_centered_sq_le A hC hint2 hint4 hcov hfour hpair4 hmixed4
    hmixed4' hquad4
  have hmono : ∫ ω, (((theta xi ω)ᵀ * A * theta xi ω) j k) ^ 2 ∂P
      ≤ ∫ ω, (2 * (((theta xi ω)ᵀ * A * theta xi ω) j k - A.trace * Sig j k) ^ 2
          + 2 * (A.trace * Sig j k) ^ 2) ∂P := by
    refine integral_mono hsq ((hcsq.const_mul 2).add (integrable_const _)) (fun ω => ?_)
    nlinarith [sq_nonneg (((theta xi ω)ᵀ * A * theta xi ω) j k - 2 * (A.trace * Sig j k))]
  rw [integral_add (hcsq.const_mul 2) (integrable_const _), integral_const_mul,
    integral_const] at hmono
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hmono
  linarith

end BilinearVariance

section MainDischarged

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

omit [Fintype ι] in
/-- **Proposition SM.D.1, first display**, with the variance bound supplied by
`quadvar_compl_le` from the fourth-moment structure, at `Cq = 2C`. Here `hcardn` holds at every
`n`. -/
theorem designcond_tendstoInProb_of_moments [IsProbabilityMeasure P]
    {xi : ∀ n, O n → ι → Ω → ℝ} {mu : ∀ n, Matrix (O n) ι ℝ} {Pm : ∀ n, Matrix (O n) (O n) ℝ}
    {Sig : Matrix ι ι ℝ} {Cmu C : ℝ} (j k : ι) (hSigj : 0 ≤ Sig j j) (hSigk : 0 ≤ Sig k k)
    (hC : 0 ≤ C)
    (hsymm : ∀ n, (Pm n)ᵀ = Pm n) (hidem : ∀ n, Pm n * Pm n = Pm n)
    (hcardn : ∀ n : ℕ, (Fintype.card (O n) : ℝ) = (n : ℝ))
    (hmubd : ∀ (n : ℕ) (a : ι), ∑ o : O n, (mu n o a) ^ 2 ≤ Cmu * n)
    (hint2 : ∀ n o o' a b, Integrable (fun ω => xi n o a ω * xi n o' b ω) P)
    (hint4 : ∀ (n : ℕ) (r s : O n × O n), Integrable
      (fun ω => (xi n r.1 j ω * xi n r.2 k ω) * (xi n s.1 j ω * xi n s.2 k ω)) P)
    (hcov : ∀ n o o' a b, ∫ ω, xi n o a ω * xi n o' b ω ∂P = if o = o' then Sig a b else 0)
    (hfour : ∀ (n : ℕ) (o o' : O n), ∫ ω, (xi n o j ω * xi n o' k ω) ^ 2 ∂P ≤ C)
    (hpair4 : ∀ (n : ℕ) (o o' : O n), o ≠ o' →
      ∫ ω, (xi n o j ω * xi n o k ω) * (xi n o' j ω * xi n o' k ω) ∂P = Sig j k * Sig j k)
    (hmixed4 : ∀ (n : ℕ) (a : O n) (p : O n × O n), p.1 ≠ p.2 →
      ∫ ω, (xi n a j ω * xi n a k ω) * (xi n p.1 j ω * xi n p.2 k ω) ∂P = 0)
    (hmixed4' : ∀ (n : ℕ) (a : O n) (p : O n × O n), p.1 ≠ p.2 →
      ∫ ω, (xi n p.1 j ω * xi n p.2 k ω) * (xi n a j ω * xi n a k ω) ∂P = 0)
    (hquad4 : ∀ (n : ℕ) (p q : O n × O n), p.1 ≠ p.2 → q.1 ≠ q.2 → q ≠ p → q ≠ (p.2, p.1) →
      ∫ ω, (xi n p.1 j ω * xi n p.2 k ω) * (xi n q.1 j ω * xi n q.2 k ω) ∂P = 0)
    (hintsq1 : ∀ n : ℕ, Integrable (fun ω => ((n : ℝ)⁻¹
      * ((mu n)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n) * theta (xi n) ω) j k) ^ 2) P)
    (hintsq2 : ∀ n : ℕ, Integrable (fun ω => ((n : ℝ)⁻¹
      * ((mu n)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n) * theta (xi n) ω) k j) ^ 2) P)
    (hintsq3 : ∀ n : ℕ, Integrable (fun ω => ((n : ℝ)⁻¹
      * ((((theta (xi n) ω)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n) * theta (xi n) ω) j k)
         - ((1 : Matrix (O n) (O n) ℝ) - Pm n).trace * Sig j k)) ^ 2) P) :
    TendstoInMeasure P
      (fun (n : ℕ) ω =>
        (n : ℝ)⁻¹ * ((mu n + theta (xi n) ω)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n)
            * (mu n + theta (xi n) ω)) j k
          - ((n : ℝ)⁻¹ * ((mu n)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n) * mu n) j k
             + (1 - (Pm n).trace / n) * Sig j k))
      atTop (fun _ => (0 : ℝ)) := by
  refine designcond_tendstoInProb (Cq := 2 * C) j k hSigj hSigk hsymm hidem
    (Filter.Eventually.of_forall hcardn) hmubd hint2 hcov (fun n => ?_) hintsq1 hintsq2 hintsq3
  have h := quadvar_compl_le (P := P) (xi := xi n) (Sig := Sig) (j := j) (k := k) (C := C)
    (Pm := Pm n) hC (hsymm n) (hidem n) (hint2 n) (hint4 n) (hcov n) (hfour n) (hpair4 n)
    (hmixed4 n) (hmixed4' n) (hquad4 n)
  rwa [hcardn n] at h

end MainDischarged


/-! ### Lemma SM.B.9

Let `J ≥ 1`, let each maintained clustering dimension coincide with a fixed-effect dimension,
and let the primitive-design assumption hold with `μ ∈ 𝒮` columnwise, so that `X̃ = Q_[Δ]Θ`. For
`Ξ_n := X̃'(R ∘ (𝒮h - I))X̃` with `R = Q_[Δ] - Λ`, `‖Ξ_n‖ = O_p(d_[Δ] + (G_max n)^{1/2})`, hence
`‖Ξ_n‖/n ⟶^p 0` whenever `G_max/n → 0`.

The proof splits `Ξ_n = Ξ^{(1)}_n - Ξ^{(2)}_n` (`xiSharp_decomp`), with
`Ξ^{(1)}_n = Θ'(QW₀Q)Θ` and `W₀ = Q ∘ (𝒮h - I)`. The mean and the Frobenius norm of `QW₀Q` are
both bounded by `d_[Δ]` (`trace_conj_hadamardLink`, `rectFrobSq_hadamardLink_le_trace`), and the
fluctuation is bounded by the variance expansion above. `Ξ^{(2)}_n` is bounded by a pathwise
Cauchy–Schwarz inequality over the sharing pairs and the cluster count
`#{(o,o') : o ∼ o'} ≤ J·G_max·n`. The two halves are added in the Frobenius norm, which bounds
the `l2` operator norm. The hypothesis `hone` asks that the normalizer
`d_[Δ] + (G_max n)^{1/2}` be at least `1`, which excludes the empty design.
-/

section CgmSharpAlgebra

variable {O ι D L : Type*} [Fintype O] [DecidableEq O] [Fintype ι]
variable [DecidableEq D] [Fintype L] [DecidableEq L]

theorem xiMat_sub (c : D → O → L) (dims : Finset D) (R R' : Matrix O O ℝ) (x : Matrix O ι ℝ) :
    Cgm.xiMat c dims (R - R') x = Cgm.xiMat c dims R x - Cgm.xiMat c dims R' x := by
  have hh : (R - R') ⊙ (Cgm.linkMat c dims - 1)
      = R ⊙ (Cgm.linkMat c dims - 1) - R' ⊙ (Cgm.linkMat c dims - 1) := by
    ext o o'
    simp only [Matrix.hadamard_apply, Matrix.sub_apply]
    ring
  rw [Cgm.xiMat, Cgm.xiMat, Cgm.xiMat, hh, Matrix.mul_sub, Matrix.sub_mul]

theorem hadamardLink_apply (c : D → O → L) {dims : Finset D} (hdims : dims.Nonempty)
    (Q : Matrix O O ℝ) (o o' : O) :
    (Q ⊙ (Cgm.linkMat c dims - 1)) o o'
      = if o = o' then 0 else (if Linked c dims o o' then Q o o' else 0) := by
  rw [Matrix.hadamard_apply, Matrix.sub_apply, Cgm.linkMat_apply]
  by_cases h : o = o'
  · subst h
    have hl : Linked c dims o o := Cgm.linked_self hdims o
    simp [hl]
  · by_cases hl : Linked c dims o o' <;> simp [h, hl, Matrix.one_apply_ne h]

theorem hadamardLink_sq_le (c : D → O → L) {dims : Finset D} (hdims : dims.Nonempty)
    (Q : Matrix O O ℝ) (o o' : O) :
    ((Q ⊙ (Cgm.linkMat c dims - 1)) o o') ^ 2 ≤ (Q o o') ^ 2 := by
  rw [hadamardLink_apply c hdims Q o o']
  by_cases h : o = o'
  · simp [h, sq_nonneg]
  · by_cases hl : Linked c dims o o' <;> simp [h, hl, sq_nonneg]

theorem rectFrobSq_hadamardLink_le_trace (c : D → O → L) {dims : Finset D}
    (hdims : dims.Nonempty) {Pm : Matrix O O ℝ} (hs : Pmᵀ = Pm) (hi : Pm * Pm = Pm) :
    rectFrobSq (((1 : Matrix O O ℝ) - Pm) ⊙ (Cgm.linkMat c dims - 1)) ≤ Pm.trace := by
  classical
  have hdrop : ∀ p ∈ (Finset.univ : Finset (O × O)),
      p ∉ (Finset.univ : Finset O).offDiag →
      ((((1 : Matrix O O ℝ) - Pm) ⊙ (Cgm.linkMat c dims - 1)) p.1 p.2) ^ 2 = 0 := by
    intro p _ hp
    have hd : p.1 = p.2 := by
      by_contra hne
      exact hp (Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hne⟩)
    rw [hadamardLink_apply c hdims _ p.1 p.2]
    simp [hd]
  have hfs : rectFrobSq (((1 : Matrix O O ℝ) - Pm) ⊙ (Cgm.linkMat c dims - 1))
      = ∑ p ∈ (Finset.univ : Finset O).offDiag,
          ((((1 : Matrix O O ℝ) - Pm) ⊙ (Cgm.linkMat c dims - 1)) p.1 p.2) ^ 2 := by
    have hconv : rectFrobSq (((1 : Matrix O O ℝ) - Pm) ⊙ (Cgm.linkMat c dims - 1))
        = ∑ p : O × O, ((((1 : Matrix O O ℝ) - Pm) ⊙ (Cgm.linkMat c dims - 1)) p.1 p.2) ^ 2 := by
      rw [rectFrobSq, Fintype.sum_prod_type]
    rw [hconv]
    exact (Finset.sum_subset (Finset.subset_univ _) hdrop).symm
  rw [hfs]
  refine le_trans (Finset.sum_le_sum (fun p _ => hadamardLink_sq_le c hdims _ p.1 p.2)) ?_
  exact sum_offDiag_sq_compl_le_trace hs hi

theorem sum_sq_mulVec_le_of_symmProj {A : Matrix O O ℝ} (hs : Aᵀ = A) (hi : A * A = A)
    (v : Matrix O ι ℝ) (j : ι) : ∑ o : O, ((A * v) o j) ^ 2 ≤ ∑ o : O, (v o j) ^ 2 := by
  have h1 := sum_sq_mulVec_eq hs hi v j
  have h2 := sum_sq_mulVec_eq (SuffLeverage.compl_transpose hs) (SuffLeverage.compl_mul_self hi) v j
  have h3 : ∑ o : O, (v o j) ^ 2 = (vᵀ * (1 : Matrix O O ℝ) * v) j j := by
    rw [Matrix.mul_one, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun o _ => by rw [Matrix.transpose_apply]; ring
  have h4 : (vᵀ * ((1 : Matrix O O ℝ) - A) * v) j j
      = (vᵀ * (1 : Matrix O O ℝ) * v) j j - (vᵀ * A * v) j j := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    simp [Matrix.sub_apply]
  have h5 : 0 ≤ (vᵀ * ((1 : Matrix O O ℝ) - A) * v) j j := by
    rw [← h2]
    positivity
  rw [h1, h3]
  linarith

theorem rectFrobSq_mul_le_of_symmProj {A : Matrix O O ℝ} (hs : Aᵀ = A) (hi : A * A = A)
    (M : Matrix O ι ℝ) : rectFrobSq (A * M) ≤ rectFrobSq M := by
  have hL : rectFrobSq (A * M) = ∑ j : ι, ∑ o : O, ((A * M) o j) ^ 2 := by
    rw [rectFrobSq]; exact Finset.sum_comm
  have hR : rectFrobSq M = ∑ j : ι, ∑ o : O, (M o j) ^ 2 := by
    rw [rectFrobSq]; exact Finset.sum_comm
  rw [hL, hR]
  exact Finset.sum_le_sum fun j _ => sum_sq_mulVec_le_of_symmProj hs hi M j

theorem rectFrobSq_conj_le_of_symmProj {A : Matrix O O ℝ} (hs : Aᵀ = A) (hi : A * A = A)
    (W : Matrix O O ℝ) : rectFrobSq (A * W * A) ≤ rectFrobSq W := by
  have h1 : rectFrobSq (A * (W * A)) ≤ rectFrobSq (W * A) :=
    rectFrobSq_mul_le_of_symmProj hs hi _
  have h2 : rectFrobSq (W * A) ≤ rectFrobSq W := by
    have h3 : rectFrobSq ((W * A)ᵀ) ≤ rectFrobSq (Wᵀ) := by
      rw [Matrix.transpose_mul, hs]
      exact rectFrobSq_mul_le_of_symmProj hs hi _
    rw [rectFrobSq_transpose, rectFrobSq_transpose] at h3
    exact h3
  rw [Matrix.mul_assoc]
  linarith

theorem trace_conj_hadamardLink (c : D → O → L) {dims : Finset D} (hdims : dims.Nonempty)
    {Q : Matrix O O ℝ} (hs : Qᵀ = Q) (hi : Q * Q = Q) :
    (Q * (Q ⊙ (Cgm.linkMat c dims - 1)) * Q).trace
      = rectFrobSq (Q ⊙ (Cgm.linkMat c dims - 1)) := by
  have hcyc : (Q * (Q ⊙ (Cgm.linkMat c dims - 1)) * Q).trace
      = ((Q ⊙ (Cgm.linkMat c dims - 1)) * Q).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hi]
  rw [hcyc, Matrix.trace, rectFrobSq]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun o' _ => ?_
  have hqs : Q o' o = Q o o' := by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hs o) o'
  rw [hqs, hadamardLink_apply c hdims Q o o']
  by_cases h : o = o'
  · simp [h]
  · by_cases hl : Linked c dims o o' <;> simp [h, hl] <;> ring

theorem xiMat_compl_eq_quad (c : D → O → L) (dims : Finset D) {Q : Matrix O O ℝ} (hs : Qᵀ = Q)
    (th : Matrix O ι ℝ) :
    Cgm.xiMat c dims Q (Q * th)
      = thᵀ * (Q * (Q ⊙ (Cgm.linkMat c dims - 1)) * Q) * th := by
  rw [Cgm.xiMat, Matrix.transpose_mul, hs]
  simp [Matrix.mul_assoc]

/-! The 0/1 weight `(𝒮h - I)` and the counting step. -/

def linkOffInd (c : D → O → L) (dims : Finset D) (p : O × O) : ℝ :=
  if p.1 = p.2 then 0 else (if Linked c dims p.1 p.2 then 1 else 0)

theorem linkOffInd_nonneg (c : D → O → L) (dims : Finset D) (p : O × O) :
    0 ≤ linkOffInd c dims p := by
  rw [linkOffInd]
  by_cases h : p.1 = p.2
  · simp [h]
  · by_cases hl : Linked c dims p.1 p.2 <;> simp [h, hl]

theorem linkOffInd_sq (c : D → O → L) (dims : Finset D) (p : O × O) :
    (linkOffInd c dims p) ^ 2 = linkOffInd c dims p := by
  rw [linkOffInd]
  by_cases h : p.1 = p.2
  · simp [h]
  · by_cases hl : Linked c dims p.1 p.2 <;> simp [h, hl]

theorem linkMat_sub_one_apply (c : D → O → L) {dims : Finset D} (hdims : dims.Nonempty)
    (p : O × O) : (Cgm.linkMat c dims - 1) p.1 p.2 = linkOffInd c dims p := by
  obtain ⟨o, o'⟩ := p
  rw [Matrix.sub_apply, Cgm.linkMat_apply, linkOffInd]
  by_cases h : o = o'
  · subst h
    have hl : Linked c dims o o := Cgm.linked_self hdims o
    simp [hl, Matrix.one_apply_eq]
  · simp [h, Matrix.one_apply_ne h]

/-- **The union bound and the cluster count**: `#{(o,o') : o ∼ o'} ≤ J·G_max·n`. -/
theorem sum_linkOffInd_le (c : D → O → L) (dims : Finset D) {Gmax : ℝ}
    (hG : ∀ (d : D) (l : L), (Cgm.clusterCard (c d) l : ℝ) ≤ Gmax) :
    ∑ p : O × O, linkOffInd c dims p
      ≤ (dims.card : ℝ) * (Gmax * (Fintype.card O : ℝ)) := by
  classical
  have hnn : ∀ (d : D) (p : O × O), (0 : ℝ) ≤ (if c d p.1 = c d p.2 then (1 : ℝ) else 0) := by
    intro d p
    by_cases he : c d p.1 = c d p.2 <;> simp [he]
  have hind : ∀ p : O × O, linkOffInd c dims p
      ≤ ∑ d ∈ dims, (if c d p.1 = c d p.2 then (1 : ℝ) else 0) := by
    intro p
    have hsum0 : (0 : ℝ) ≤ ∑ d ∈ dims, (if c d p.1 = c d p.2 then (1 : ℝ) else 0) :=
      Finset.sum_nonneg fun d _ => hnn d p
    by_cases hl : Linked c dims p.1 p.2
    · obtain ⟨d, hd, hcd⟩ := hl
      have h1 : linkOffInd c dims p ≤ 1 := by
        rw [linkOffInd]
        by_cases h : p.1 = p.2
        · simp [h]
        · by_cases hl' : Linked c dims p.1 p.2 <;> simp [h, hl']
      refine h1.trans ?_
      have hd1 : (if c d p.1 = c d p.2 then (1 : ℝ) else 0) = 1 := by simp [hcd]
      have hmem := Finset.single_le_sum
        (f := fun e => (if c e p.1 = c e p.2 then (1 : ℝ) else 0)) (fun e _ => hnn e p) hd
      rwa [hd1] at hmem
    · have h0 : linkOffInd c dims p = 0 := by
        rw [linkOffInd]
        by_cases h : p.1 = p.2
        · simp [h]
        · simp [h, hl]
      rw [h0]
      exact hsum0
  refine le_trans (Finset.sum_le_sum fun p _ => hind p) ?_
  have hswap : ∑ p : O × O, ∑ d ∈ dims, (if c d p.1 = c d p.2 then (1 : ℝ) else 0)
      = ∑ d ∈ dims, ∑ p : O × O, (if c d p.1 = c d p.2 then (1 : ℝ) else 0) :=
    Finset.sum_comm
  rw [hswap]
  have hper : ∀ d ∈ dims, ∑ p : O × O, (if c d p.1 = c d p.2 then (1 : ℝ) else 0)
      ≤ Gmax * (Fintype.card O : ℝ) := by
    intro d _
    have hconv : ∑ p : O × O, (if c d p.1 = c d p.2 then (1 : ℝ) else 0)
        = ∑ o : O, ∑ o' : O, (if c d o = c d o' then (1 : ℝ) else 0) := by
      rw [Fintype.sum_prod_type]
    rw [hconv, Cgm.sum_pairs_sameCluster (c d)]
    exact Cgm.sum_clusterCard_sq_le (c d) (hG d)
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [Finset.sum_const, nsmul_eq_mul]

/-- **The pathwise Cauchy--Schwarz over the sharing pairs**, with `∑_{o,o'}Λ²_{oo'} = tr(Λ)`. -/
theorem xiMat_sq_le_of_symmProj (c : D → O → L) {dims : Finset D}
    (hdims : dims.Nonempty) {Lam : Matrix O O ℝ} (hLs : Lamᵀ = Lam) (hLi : Lam * Lam = Lam)
    (x : Matrix O ι ℝ) (a b : ι) :
    (Cgm.xiMat c dims Lam x a b) ^ 2
      ≤ Lam.trace * ∑ p : O × O, linkOffInd c dims p * (x p.1 a * x p.2 b) ^ 2 := by
  classical
  have hentry : Cgm.xiMat c dims Lam x a b
      = ∑ p : O × O, Lam p.1 p.2 * (linkOffInd c dims p * (x p.1 a * x p.2 b)) := by
    have hconv : ∑ p : O × O, Lam p.1 p.2 * (linkOffInd c dims p * (x p.1 a * x p.2 b))
        = ∑ o : O, ∑ o' : O,
            Lam o o' * (linkOffInd c dims (o, o') * (x o a * x o' b)) := by
      rw [Fintype.sum_prod_type]
    rw [Cgm.xiMat, Cgm.transpose_mul_mul_apply, hconv]
    refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => ?_
    rw [Matrix.hadamard_apply, linkMat_sub_one_apply c hdims (o, o')]
    ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (O × O))
    (fun p => Lam p.1 p.2) (fun p => linkOffInd c dims p * (x p.1 a * x p.2 b))
  have hfrob : ∑ p : O × O, (Lam p.1 p.2) ^ 2 = Lam.trace := by
    have hconv : rectFrobSq Lam = ∑ p : O × O, (Lam p.1 p.2) ^ 2 := by
      rw [rectFrobSq, Fintype.sum_prod_type]
    rw [← hconv, Cgm.rectFrobSq_of_symmProj hLs hLi]
  have hg : ∀ p : O × O, (linkOffInd c dims p * (x p.1 a * x p.2 b)) ^ 2
      = linkOffInd c dims p * (x p.1 a * x p.2 b) ^ 2 := by
    intro p
    rw [mul_pow, linkOffInd_sq]
  have hsum : ∑ p : O × O, (linkOffInd c dims p * (x p.1 a * x p.2 b)) ^ 2
      = ∑ p : O × O, linkOffInd c dims p * (x p.1 a * x p.2 b) ^ 2 :=
    Finset.sum_congr rfl fun p _ => hg p
  rw [hentry]
  refine le_trans hcs ?_
  rw [hfrob, hsum]

end CgmSharpAlgebra

section CgmSharpMoments

variable {O ι D L : Type*} [Fintype O] [DecidableEq O] [Fintype ι] [DecidableEq ι]
variable [DecidableEq D] [Fintype L] [DecidableEq L]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `E[x̃²_{oa}x̃²_{o'b}] ≤ C` from `E[x̃⁴_{oa}] ≤ C`. -/
theorem integral_sq_mul_sq_le (x : Ω → Matrix O ι ℝ) {C4 : ℝ}
    (hx4int : ∀ (o : O) (a : ι), Integrable (fun ω => (x ω o a) ^ 4) P)
    (hxxint : ∀ (o o' : O) (a b : ι), Integrable (fun ω => (x ω o a * x ω o' b) ^ 2) P)
    (hx4 : ∀ (o : O) (a : ι), ∫ ω, (x ω o a) ^ 4 ∂P ≤ C4)
    (o o' : O) (a b : ι) : ∫ ω, (x ω o a * x ω o' b) ^ 2 ∂P ≤ C4 := by
  have hmono : ∫ ω, (x ω o a * x ω o' b) ^ 2 ∂P
      ≤ ∫ ω, ((x ω o a) ^ 4 + (x ω o' b) ^ 4) / 2 ∂P := by
    refine integral_mono (hxxint o o' a b) (((hx4int o a).add (hx4int o' b)).div_const 2)
      (fun ω => ?_)
    nlinarith [sq_nonneg ((x ω o a) ^ 2 - (x ω o' b) ^ 2)]
  rw [integral_div, integral_add (hx4int o a) (hx4int o' b)] at hmono
  linarith [hx4 o a, hx4 o' b]

/-- **The `Ξ^{(2)}` half**: `E[(Ξ^{(2)}_{ab})²] ≤ tr(Λ)·C·J·G_max·n`. -/
theorem integral_xiTwo_sq_le [IsProbabilityMeasure P] (c : D → O → L) {dims : Finset D}
    (hdims : dims.Nonempty) {Lam : Matrix O O ℝ} (hLs : Lamᵀ = Lam) (hLi : Lam * Lam = Lam)
    (x : Ω → Matrix O ι ℝ) {C4 Gmax : ℝ} (hC4 : 0 ≤ C4)
    (hG : ∀ (d : D) (l : L), (Cgm.clusterCard (c d) l : ℝ) ≤ Gmax)
    (hxxint : ∀ (o o' : O) (a b : ι), Integrable (fun ω => (x ω o a * x ω o' b) ^ 2) P)
    (hxx : ∀ (o o' : O) (a b : ι), ∫ ω, (x ω o a * x ω o' b) ^ 2 ∂P ≤ C4)
    (hxi2int : ∀ a b : ι, Integrable (fun ω => (Cgm.xiMat c dims Lam (x ω) a b) ^ 2) P)
    (a b : ι) :
    ∫ ω, (Cgm.xiMat c dims Lam (x ω) a b) ^ 2 ∂P
      ≤ Lam.trace * (C4 * ((dims.card : ℝ) * (Gmax * (Fintype.card O : ℝ)))) := by
  classical
  have htr : (0 : ℝ) ≤ Lam.trace := Cgm.trace_nonneg_of_symmProj hLs hLi
  have hmajint : Integrable (fun ω => Lam.trace
      * ∑ p : O × O, linkOffInd c dims p * (x ω p.1 a * x ω p.2 b) ^ 2) P :=
    (integrable_finsetSum _ (fun p _ => (hxxint p.1 p.2 a b).const_mul _)).const_mul _
  have hstep := integral_mono (hxi2int a b) hmajint
    (fun ω => xiMat_sq_le_of_symmProj c hdims hLs hLi (x ω) a b)
  rw [integral_const_mul,
    integral_finsetSum _ (fun p _ => (hxxint p.1 p.2 a b).const_mul _)] at hstep
  simp_rw [integral_const_mul] at hstep
  refine hstep.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ htr
  have h1 : ∑ p : O × O, linkOffInd c dims p * ∫ ω, (x ω p.1 a * x ω p.2 b) ^ 2 ∂P
      ≤ ∑ p : O × O, linkOffInd c dims p * C4 :=
    Finset.sum_le_sum fun p _ =>
      mul_le_mul_of_nonneg_left (hxx p.1 p.2 a b) (linkOffInd_nonneg c dims p)
  have h2 : ∑ p : O × O, linkOffInd c dims p * C4
      = (∑ p : O × O, linkOffInd c dims p) * C4 := by rw [Finset.sum_mul]
  have h3 := sum_linkOffInd_le (O := O) c dims hG
  nlinarith [h1, h3]

/-- `X̃ = Q_[Δ]Θ`, the within-transformed design when `μ ∈ 𝒮` columnwise. -/
def within (Pm : Matrix O O ℝ) (xi : O → ι → Ω → ℝ) (ω : Ω) : Matrix O ι ℝ :=
  ((1 : Matrix O O ℝ) - Pm) * theta xi ω

/-- `QW₀Q` with `W₀ = Q ∘ (𝒮h - I)`. -/
def coefMat (c : D → O → L) (dims : Finset D) (Pm : Matrix O O ℝ) : Matrix O O ℝ :=
  ((1 : Matrix O O ℝ) - Pm)
    * (((1 : Matrix O O ℝ) - Pm) ⊙ (Cgm.linkMat c dims - 1)) * ((1 : Matrix O O ℝ) - Pm)

/-- `Ξ_n := X̃'(R ∘ (𝒮h - I))X̃`, at `R = Q_[Δ] - Λ`. -/
def xiSharp (c : D → O → L) (dims : Finset D) (Pm Lam : Matrix O O ℝ)
    (xi : O → ι → Ω → ℝ) (ω : Ω) : Matrix ι ι ℝ :=
  Cgm.xiMat c dims (((1 : Matrix O O ℝ) - Pm) - Lam) (within Pm xi ω)

/-- `Ξ^{(1)}_n = Θ'(QW₀Q)Θ`. -/
def xiSharpOne (c : D → O → L) (dims : Finset D) (Pm : Matrix O O ℝ)
    (xi : O → ι → Ω → ℝ) (ω : Ω) : Matrix ι ι ℝ :=
  (theta xi ω)ᵀ * coefMat c dims Pm * theta xi ω

/-- `Ξ^{(2)}_n = ∑_{o ≠ o', o ∼ o'} Λ_{oo'} x̃_o x̃_{o'}'`. -/
def xiSharpTwo (c : D → O → L) (dims : Finset D) (Pm Lam : Matrix O O ℝ)
    (xi : O → ι → Ω → ℝ) (ω : Ω) : Matrix ι ι ℝ :=
  Cgm.xiMat c dims Lam (within Pm xi ω)

theorem xiSharp_decomp (c : D → O → L) (dims : Finset D) {Pm : Matrix O O ℝ} (Lam : Matrix O O ℝ)
    (hs : Pmᵀ = Pm) (xi : O → ι → Ω → ℝ) (ω : Ω) :
    xiSharp c dims Pm Lam xi ω
      = xiSharpOne c dims Pm xi ω - xiSharpTwo c dims Pm Lam xi ω := by
  rw [xiSharp, xiSharpOne, xiSharpTwo, within, xiMat_sub,
    xiMat_compl_eq_quad c dims (SuffLeverage.compl_transpose hs), coefMat]

/-! #### The fourth moment of the within-transformed design

`x̃²_{oa} = (Θ'(q_oq_o')Θ)_{aa}` with `q_o := Q_{o·}` the `o`-th row of `Q`, so `E[x̃⁴_{oa}]` is
the second moment of a quadratic form in `Θ` at the rank-one matrix `q_oq_o'`, and
`integral_quad_sq_le` applies. With `tr(q_oq_o') = Q_{oo}` and `‖q_oq_o'‖_F² = Q²_{oo}` this
gives `E[x̃⁴_{oa}] ≤ C(∑_{o'}Q²_{oo'})² = CQ²_{oo} ≤ C`. The integrability conditions follow
from `hint4`.
-/

omit [DecidableEq O] in
/-- `q_oq_o'`, the rank-one coefficient matrix of `x̃²_{oa}`, with `q_o := Q_{o·}` the `o`-th
row of `Q`. -/
def rowOuter (A : Matrix O O ℝ) (o : O) : Matrix O O ℝ :=
  Matrix.of fun p q => A o p * A o q

omit [DecidableEq O] in
/-- `tr(q_oq_o') = ∑_{o'}A²_{oo'}`. -/
theorem rowOuter_trace (A : Matrix O O ℝ) (o : O) :
    (rowOuter A o).trace = ∑ p : O, (A o p) ^ 2 := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.diag_apply, rowOuter]
  simp only [Matrix.of_apply]
  ring

omit [DecidableEq O] in
/-- `‖q_oq_o'‖_F² = (∑_{o'}A²_{oo'})²`. -/
theorem rectFrobSq_rowOuter (A : Matrix O O ℝ) (o : O) :
    rectFrobSq (rowOuter A o) = (∑ p : O, (A o p) ^ 2) ^ 2 := by
  rw [pow_two, Finset.sum_mul_sum, rectFrobSq]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [rowOuter]
  simp only [Matrix.of_apply]
  ring

omit [DecidableEq O] in
/-- `∑_{o'}Q²_{oo'} = Q_{oo}` for a symmetric idempotent `Q`. -/
theorem sum_row_sq_eq_diag {A : Matrix O O ℝ} (hs : Aᵀ = A) (hi : A * A = A) (o : O) :
    ∑ p : O, (A o p) ^ 2 = A o o := by
  have h1 : (A * A) o o = A o o := by rw [hi]
  rw [Matrix.mul_apply] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hq : A p o = A o p := by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hs o) p
  rw [hq]; ring

omit [DecidableEq O] in
/-- `Q_{oo} ∈ [0,1]` for a symmetric idempotent `Q`, since `Q_{oo} = ∑_{o'}Q²_{oo'} ≥ Q²_{oo}`;
hence `Q²_{oo} ≤ 1`. -/
theorem diag_le_one_of_symmProj {A : Matrix O O ℝ} (hs : Aᵀ = A) (hi : A * A = A) (o : O) :
    A o o ≤ 1 := by
  have h := sum_row_sq_eq_diag hs hi o
  have hge : (A o o) ^ 2 ≤ ∑ p : O, (A o p) ^ 2 :=
    Finset.single_le_sum (f := fun p => (A o p) ^ 2) (fun p _ => sq_nonneg _) (Finset.mem_univ o)
  rw [h] at hge
  nlinarith

omit [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω] in
/-- `x̃_{oa}x̃_{o'b}` as one sum over index pairs. -/
theorem within_mul_within_eq_sum (Pm : Matrix O O ℝ) (xi : O → ι → Ω → ℝ)
    (o o' : O) (a b : ι) (ω : Ω) :
    within Pm xi ω o a * within Pm xi ω o' b
      = ∑ r : O × O, (((1 : Matrix O O ℝ) - Pm) o r.1 * ((1 : Matrix O O ℝ) - Pm) o' r.2)
          * (xi r.1 a ω * xi r.2 b ω) := by
  have hL : ∀ (e : O) (d : ι), within Pm xi ω e d
      = ∑ p : O, ((1 : Matrix O O ℝ) - Pm) e p * xi p d ω := by
    intro e d
    rw [within, Matrix.mul_apply]
    rfl
  rw [hL o a, hL o' b, Finset.sum_mul_sum, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

omit [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω] in
/-- `x̃²_{oa} = (Θ'(q_oq_o')Θ)_{aa}`. -/
theorem sq_within_eq_quad (Pm : Matrix O O ℝ) (xi : O → ι → Ω → ℝ) (o : O) (a : ι) (ω : Ω) :
    (within Pm xi ω o a) ^ 2
      = ((theta xi ω)ᵀ * rowOuter ((1 : Matrix O O ℝ) - Pm) o * theta xi ω) a a := by
  have hL : within Pm xi ω o a
      = ∑ p : O, ((1 : Matrix O O ℝ) - Pm) o p * theta xi ω p a := by
    rw [within, Matrix.mul_apply]
  rw [hL, quad_apply, pow_two, Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [rowOuter]
  simp only [Matrix.of_apply]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- `x̃²_{oa}` is integrable, from `hint2` alone. -/
theorem integrable_sq_within (Pm : Matrix O O ℝ) {xi : O → ι → Ω → ℝ}
    (hint2 : ∀ o o' a b, Integrable (fun ω => xi o a ω * xi o' b ω) P) (o : O) (a : ι) :
    Integrable (fun ω => (within Pm xi ω o a) ^ 2) P := by
  have h : (fun ω => (within Pm xi ω o a) ^ 2)
      = fun ω => ∑ r : O × O,
          (((1 : Matrix O O ℝ) - Pm) o r.1 * ((1 : Matrix O O ℝ) - Pm) o r.2)
            * (xi r.1 a ω * xi r.2 a ω) := by
    funext ω
    rw [pow_two, within_mul_within_eq_sum]
  rw [h]
  exact integrable_finsetSum _ (fun r _ => (hint2 r.1 r.2 a a).const_mul _)

omit [Fintype ι] [DecidableEq ι] in
/-- `(x̃_{oa}x̃_{o'b})²` is integrable, from `hint4`. -/
theorem integrable_sq_within_mul_within (Pm : Matrix O O ℝ) {xi : O → ι → Ω → ℝ}
    (hint4 : ∀ (a b : ι) (r s : O × O),
      Integrable (fun ω => (xi r.1 a ω * xi r.2 b ω) * (xi s.1 a ω * xi s.2 b ω)) P)
    (o o' : O) (a b : ι) :
    Integrable (fun ω => (within Pm xi ω o a * within Pm xi ω o' b) ^ 2) P := by
  have h : (fun ω => (within Pm xi ω o a * within Pm xi ω o' b) ^ 2)
      = fun ω => ∑ r : O × O, ∑ s : O × O,
          ((((1 : Matrix O O ℝ) - Pm) o r.1 * ((1 : Matrix O O ℝ) - Pm) o' r.2)
            * (((1 : Matrix O O ℝ) - Pm) o s.1 * ((1 : Matrix O O ℝ) - Pm) o' s.2))
            * ((xi r.1 a ω * xi r.2 b ω) * (xi s.1 a ω * xi s.2 b ω)) := by
    funext ω
    rw [pow_two, within_mul_within_eq_sum, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by ring
  rw [h]
  exact integrable_finsetSum _ (fun r _ =>
    integrable_finsetSum _ (fun s _ => ((hint4 a b r s).const_mul _)))

omit [Fintype ι] [DecidableEq ι] in
/-- `x̃⁴_{oa}` is integrable. -/
theorem integrable_within_pow_four (Pm : Matrix O O ℝ) {xi : O → ι → Ω → ℝ}
    (hint4 : ∀ (a b : ι) (r s : O × O),
      Integrable (fun ω => (xi r.1 a ω * xi r.2 b ω) * (xi s.1 a ω * xi s.2 b ω)) P)
    (o : O) (a : ι) :
    Integrable (fun ω => (within Pm xi ω o a) ^ 4) P := by
  have h : (fun ω => (within Pm xi ω o a) ^ 4)
      = fun ω => (within Pm xi ω o a * within Pm xi ω o a) ^ 2 := by
    funext ω; ring
  rw [h]
  exact integrable_sq_within_mul_within Pm hint4 o o a a

omit [Fintype ι] [DecidableEq ι] in
/-- `E[x̃⁴_{oa}] ≤ C'(∑_{o'}Q²_{oo'})² = C'Q²_{oo}`, with `C' := 2(Σ_ξ)²_{aa} + 4C`. -/
theorem integral_within_pow_four_le [IsProbabilityMeasure P] {Pm : Matrix O O ℝ}
    {xi : O → ι → Ω → ℝ} {Sig : Matrix ι ι ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hs : Pmᵀ = Pm) (hi : Pm * Pm = Pm) (a : ι)
    (hint2 : ∀ o o' a b, Integrable (fun ω => xi o a ω * xi o' b ω) P)
    (hint4 : ∀ (a b : ι) (r s : O × O), Integrable
      (fun ω => (xi r.1 a ω * xi r.2 b ω) * (xi s.1 a ω * xi s.2 b ω)) P)
    (hcov : ∀ o o' a b, ∫ ω, xi o a ω * xi o' b ω ∂P = if o = o' then Sig a b else 0)
    (hfour : ∀ o o' : O, ∫ ω, (xi o a ω * xi o' a ω) ^ 2 ∂P ≤ C)
    (hpair4 : ∀ o o' : O, o ≠ o' →
      ∫ ω, (xi o a ω * xi o a ω) * (xi o' a ω * xi o' a ω) ∂P = Sig a a * Sig a a)
    (hmixed4 : ∀ (e : O) (p : O × O), p.1 ≠ p.2 →
      ∫ ω, (xi e a ω * xi e a ω) * (xi p.1 a ω * xi p.2 a ω) ∂P = 0)
    (hmixed4' : ∀ (e : O) (p : O × O), p.1 ≠ p.2 →
      ∫ ω, (xi p.1 a ω * xi p.2 a ω) * (xi e a ω * xi e a ω) ∂P = 0)
    (hquad4 : ∀ p q : O × O, p.1 ≠ p.2 → q.1 ≠ q.2 → q ≠ p → q ≠ (p.2, p.1) →
      ∫ ω, (xi p.1 a ω * xi p.2 a ω) * (xi q.1 a ω * xi q.2 a ω) ∂P = 0)
    (o : O) :
    ∫ ω, (within Pm xi ω o a) ^ 4 ∂P
      ≤ (((1 : Matrix O O ℝ) - Pm) o o) ^ 2 * (2 * (Sig a a) ^ 2 + 4 * C) := by
  classical
  have hQs : ((1 : Matrix O O ℝ) - Pm)ᵀ = (1 : Matrix O O ℝ) - Pm :=
    SuffLeverage.compl_transpose hs
  have hQi : ((1 : Matrix O O ℝ) - Pm) * ((1 : Matrix O O ℝ) - Pm) = (1 : Matrix O O ℝ) - Pm :=
    SuffLeverage.compl_mul_self hi
  set A : Matrix O O ℝ := rowOuter ((1 : Matrix O O ℝ) - Pm) o with hA
  have hpt : ∀ ω, (within Pm xi ω o a) ^ 4
      = (((theta xi ω)ᵀ * A * theta xi ω) a a) ^ 2 := by
    intro ω
    rw [hA, ← sq_within_eq_quad Pm xi o a ω]
    ring
  have htr : A.trace = ((1 : Matrix O O ℝ) - Pm) o o := by
    rw [hA, rowOuter_trace, sum_row_sq_eq_diag hQs hQi]
  have hfr : rectFrobSq A = (((1 : Matrix O O ℝ) - Pm) o o) ^ 2 := by
    rw [hA, rectFrobSq_rowOuter, sum_row_sq_eq_diag hQs hQi]
  have hsqint : Integrable (fun ω => (((theta xi ω)ᵀ * A * theta xi ω) a a) ^ 2) P := by
    have h : (fun ω => (((theta xi ω)ᵀ * A * theta xi ω) a a) ^ 2)
        = fun ω => (within Pm xi ω o a) ^ 4 := by
      funext ω; rw [hpt ω]
    rw [h]
    exact integrable_within_pow_four Pm hint4 o a
  have hlinint : Integrable (fun ω => ((theta xi ω)ᵀ * A * theta xi ω) a a) P := by
    have h : (fun ω => ((theta xi ω)ᵀ * A * theta xi ω) a a)
        = fun ω => (within Pm xi ω o a) ^ 2 := by
      funext ω; rw [hA, sq_within_eq_quad]
    rw [h]
    exact integrable_sq_within Pm hint2 o a
  have hcsq : Integrable (fun ω =>
      (((theta xi ω)ᵀ * A * theta xi ω) a a - A.trace * Sig a a) ^ 2) P := by
    have h : (fun ω => (((theta xi ω)ᵀ * A * theta xi ω) a a - A.trace * Sig a a) ^ 2)
        = fun ω => ((((theta xi ω)ᵀ * A * theta xi ω) a a) ^ 2
            - (2 * (A.trace * Sig a a)) * (((theta xi ω)ᵀ * A * theta xi ω) a a))
            + (A.trace * Sig a a) ^ 2 := by
      funext ω; ring
    rw [h]
    exact (hsqint.sub (hlinint.const_mul _)).add (integrable_const _)
  have hmain := integral_quad_sq_le (P := P) (xi := xi) (Sig := Sig) (j := a) (k := a)
    (C := C) A hC hint2 (hint4 a a) hcov hfour hpair4 hmixed4 hmixed4' hquad4 hsqint hcsq
  have hint_eq : ∫ ω, (within Pm xi ω o a) ^ 4 ∂P
      = ∫ ω, (((theta xi ω)ᵀ * A * theta xi ω) a a) ^ 2 ∂P :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [hint_eq]
  refine hmain.trans (le_of_eq ?_)
  rw [htr, hfr]
  ring

omit [DecidableEq ι] in
/-- `E[x̃⁴_{oa}] ≤ C'`, with `C' := 2‖Σ_ξ‖_F² + 4C` uniform in `a`, since `Q_{oo} ≤ 1` and
`(Σ_ξ)²_{aa} ≤ ‖Σ_ξ‖_F²`. -/
theorem integral_within_pow_four_le_const [IsProbabilityMeasure P] {Pm : Matrix O O ℝ}
    {xi : O → ι → Ω → ℝ} {Sig : Matrix ι ι ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hs : Pmᵀ = Pm) (hi : Pm * Pm = Pm) (a : ι)
    (hint2 : ∀ o o' a b, Integrable (fun ω => xi o a ω * xi o' b ω) P)
    (hint4 : ∀ (a b : ι) (r s : O × O), Integrable
      (fun ω => (xi r.1 a ω * xi r.2 b ω) * (xi s.1 a ω * xi s.2 b ω)) P)
    (hcov : ∀ o o' a b, ∫ ω, xi o a ω * xi o' b ω ∂P = if o = o' then Sig a b else 0)
    (hfour : ∀ o o' : O, ∫ ω, (xi o a ω * xi o' a ω) ^ 2 ∂P ≤ C)
    (hpair4 : ∀ o o' : O, o ≠ o' →
      ∫ ω, (xi o a ω * xi o a ω) * (xi o' a ω * xi o' a ω) ∂P = Sig a a * Sig a a)
    (hmixed4 : ∀ (e : O) (p : O × O), p.1 ≠ p.2 →
      ∫ ω, (xi e a ω * xi e a ω) * (xi p.1 a ω * xi p.2 a ω) ∂P = 0)
    (hmixed4' : ∀ (e : O) (p : O × O), p.1 ≠ p.2 →
      ∫ ω, (xi p.1 a ω * xi p.2 a ω) * (xi e a ω * xi e a ω) ∂P = 0)
    (hquad4 : ∀ p q : O × O, p.1 ≠ p.2 → q.1 ≠ q.2 → q ≠ p → q ≠ (p.2, p.1) →
      ∫ ω, (xi p.1 a ω * xi p.2 a ω) * (xi q.1 a ω * xi q.2 a ω) ∂P = 0)
    (o : O) :
    ∫ ω, (within Pm xi ω o a) ^ 4 ∂P ≤ 2 * rectFrobSq Sig + 4 * C := by
  have hQs : ((1 : Matrix O O ℝ) - Pm)ᵀ = (1 : Matrix O O ℝ) - Pm :=
    SuffLeverage.compl_transpose hs
  have hQi : ((1 : Matrix O O ℝ) - Pm) * ((1 : Matrix O O ℝ) - Pm) = (1 : Matrix O O ℝ) - Pm :=
    SuffLeverage.compl_mul_self hi
  have h0 : 0 ≤ ((1 : Matrix O O ℝ) - Pm) o o := Cgm.diag_nonneg_of_symmProj hQs hQi o
  have h1 : ((1 : Matrix O O ℝ) - Pm) o o ≤ 1 := diag_le_one_of_symmProj hQs hQi o
  have hSig : (Sig a a) ^ 2 ≤ rectFrobSq Sig := by
    rw [rectFrobSq]
    refine le_trans (Finset.single_le_sum (f := fun y : ι => (Sig a y) ^ 2)
      (fun y _ => sq_nonneg _) (Finset.mem_univ a)) ?_
    exact Finset.single_le_sum (f := fun x : ι => ∑ y : ι, (Sig x y) ^ 2)
      (fun x _ => Finset.sum_nonneg fun y _ => sq_nonneg _) (Finset.mem_univ a)
  have hx2 : (((1 : Matrix O O ℝ) - Pm) o o) ^ 2 ≤ 1 := by nlinarith
  have ht : (0 : ℝ) ≤ 2 * (Sig a a) ^ 2 + 4 * C := by nlinarith [sq_nonneg (Sig a a)]
  refine (integral_within_pow_four_le hC hs hi a hint2 hint4 hcov hfour hpair4 hmixed4
    hmixed4' hquad4 o).trans ?_
  have hkey := mul_le_mul_of_nonneg_right hx2 ht
  rw [one_mul] at hkey
  linarith

/-- The finite-sample second-moment bound behind Lemma SM.B.9, given the fourth-moment bound
`hxx`. -/
theorem integral_rectFrobSq_xiSharp_le [IsProbabilityMeasure P] (c : D → O → L)
    {dims : Finset D} (hdims : dims.Nonempty) {Pm Lam : Matrix O O ℝ}
    (hs : Pmᵀ = Pm) (hi : Pm * Pm = Pm) (hLs : Lamᵀ = Lam) (hLi : Lam * Lam = Lam)
    {xi : O → ι → Ω → ℝ} {Sig : Matrix ι ι ℝ} {C C4 Gmax : ℝ} (hC : 0 ≤ C) (hC4 : 0 ≤ C4)
    (hG : ∀ (d : D) (l : L), (Cgm.clusterCard (c d) l : ℝ) ≤ Gmax)
    (hint2 : ∀ o o' a b, Integrable (fun ω => xi o a ω * xi o' b ω) P)
    (hint4 : ∀ (a b : ι) (r s : O × O), Integrable
      (fun ω => (xi r.1 a ω * xi r.2 b ω) * (xi s.1 a ω * xi s.2 b ω)) P)
    (hcov : ∀ o o' a b, ∫ ω, xi o a ω * xi o' b ω ∂P = if o = o' then Sig a b else 0)
    (hfour : ∀ (a b : ι) (o o' : O), ∫ ω, (xi o a ω * xi o' b ω) ^ 2 ∂P ≤ C)
    (hpair4 : ∀ (a b : ι) (o o' : O), o ≠ o' →
      ∫ ω, (xi o a ω * xi o b ω) * (xi o' a ω * xi o' b ω) ∂P = Sig a b * Sig a b)
    (hmixed4 : ∀ (a b : ι) (e : O) (p : O × O), p.1 ≠ p.2 →
      ∫ ω, (xi e a ω * xi e b ω) * (xi p.1 a ω * xi p.2 b ω) ∂P = 0)
    (hmixed4' : ∀ (a b : ι) (e : O) (p : O × O), p.1 ≠ p.2 →
      ∫ ω, (xi p.1 a ω * xi p.2 b ω) * (xi e a ω * xi e b ω) ∂P = 0)
    (hquad4 : ∀ (a b : ι) (p q : O × O), p.1 ≠ p.2 → q.1 ≠ q.2 → q ≠ p → q ≠ (p.2, p.1) →
      ∫ ω, (xi p.1 a ω * xi p.2 b ω) * (xi q.1 a ω * xi q.2 b ω) ∂P = 0)
    (hxxint : ∀ (o o' : O) (a b : ι),
      Integrable (fun ω => (within Pm xi ω o a * within Pm xi ω o' b) ^ 2) P)
    (hxx : ∀ (o o' : O) (a b : ι),
      ∫ ω, (within Pm xi ω o a * within Pm xi ω o' b) ^ 2 ∂P ≤ C4)
    (hsq1 : ∀ a b : ι, Integrable (fun ω => (xiSharpOne c dims Pm xi ω a b) ^ 2) P)
    (hcsq1 : ∀ a b : ι, Integrable (fun ω => (xiSharpOne c dims Pm xi ω a b
      - (coefMat c dims Pm).trace * Sig a b) ^ 2) P)
    (hsq2 : ∀ a b : ι, Integrable (fun ω => (xiSharpTwo c dims Pm Lam xi ω a b) ^ 2) P)
    (hsq : ∀ a b : ι, Integrable (fun ω => (xiSharp c dims Pm Lam xi ω a b) ^ 2) P) :
    ∫ ω, rectFrobSq (xiSharp c dims Pm Lam xi ω) ∂P
      ≤ 4 * (Pm.trace) ^ 2 * rectFrobSq Sig
        + (Fintype.card ι : ℝ) ^ 2 * (8 * C * Pm.trace
            + 2 * (Lam.trace * (C4 * ((dims.card : ℝ) * (Gmax * (Fintype.card O : ℝ)))))) := by
  classical
  have hQs : ((1 : Matrix O O ℝ) - Pm)ᵀ = (1 : Matrix O O ℝ) - Pm :=
    SuffLeverage.compl_transpose hs
  have hQi : ((1 : Matrix O O ℝ) - Pm) * ((1 : Matrix O O ℝ) - Pm) = (1 : Matrix O O ℝ) - Pm :=
    SuffLeverage.compl_mul_self hi
  have hW0le : rectFrobSq (((1 : Matrix O O ℝ) - Pm) ⊙ (Cgm.linkMat c dims - 1)) ≤ Pm.trace :=
    rectFrobSq_hadamardLink_le_trace c hdims hs hi
  have hW0nn : 0 ≤ rectFrobSq (((1 : Matrix O O ℝ) - Pm) ⊙ (Cgm.linkMat c dims - 1)) :=
    rectFrobSq_nonneg _
  have htrA : (coefMat c dims Pm).trace
      = rectFrobSq (((1 : Matrix O O ℝ) - Pm) ⊙ (Cgm.linkMat c dims - 1)) := by
    rw [coefMat]
    exact trace_conj_hadamardLink c hdims hQs hQi
  have hAle : rectFrobSq (coefMat c dims Pm) ≤ Pm.trace := by
    rw [coefMat]
    exact le_trans (rectFrobSq_conj_le_of_symmProj hQs hQi _) hW0le
  have hAnn : 0 ≤ rectFrobSq (coefMat c dims Pm) := rectFrobSq_nonneg _
  have hPtr : 0 ≤ Pm.trace := Cgm.trace_nonneg_of_symmProj hs hi
  set Kc : ℝ := 8 * C * Pm.trace
      + 2 * (Lam.trace * (C4 * ((dims.card : ℝ) * (Gmax * (Fintype.card O : ℝ))))) with hKc
  have hentry : ∀ a b : ι, ∫ ω, (xiSharp c dims Pm Lam xi ω a b) ^ 2 ∂P
      ≤ 4 * (Pm.trace) ^ 2 * (Sig a b) ^ 2 + Kc := by
    intro a b
    have h1 := integral_quad_sq_le (P := P) (xi := xi) (Sig := Sig) (j := a) (k := b) (C := C)
      (coefMat c dims Pm) hC hint2 (hint4 a b) hcov (hfour a b) (hpair4 a b) (hmixed4 a b)
      (hmixed4' a b) (hquad4 a b) (hsq1 a b) (hcsq1 a b)
    have h2 := integral_xiTwo_sq_le (P := P) c hdims hLs hLi (within Pm xi) hC4 hG
      hxxint hxx hsq2 a b
    have hmono : ∫ ω, (xiSharp c dims Pm Lam xi ω a b) ^ 2 ∂P
        ≤ ∫ ω, (2 * (xiSharpOne c dims Pm xi ω a b) ^ 2
            + 2 * (xiSharpTwo c dims Pm Lam xi ω a b) ^ 2) ∂P := by
      refine integral_mono (hsq a b) (((hsq1 a b).const_mul 2).add ((hsq2 a b).const_mul 2))
        (fun ω => ?_)
      rw [xiSharp_decomp c dims Lam hs xi ω, Matrix.sub_apply]
      nlinarith [sq_nonneg (xiSharpOne c dims Pm xi ω a b + xiSharpTwo c dims Pm Lam xi ω a b)]
    rw [integral_add ((hsq1 a b).const_mul 2) ((hsq2 a b).const_mul 2), integral_const_mul,
      integral_const_mul] at hmono
    have hm : (coefMat c dims Pm).trace ≤ Pm.trace := by rw [htrA]; exact hW0le
    have hm0 : 0 ≤ (coefMat c dims Pm).trace := by rw [htrA]; exact hW0nn
    have htr2 : ((coefMat c dims Pm).trace) ^ 2 ≤ (Pm.trace) ^ 2 := by nlinarith
    have hsqle : ((coefMat c dims Pm).trace * Sig a b) ^ 2 ≤ (Pm.trace) ^ 2 * (Sig a b) ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right htr2 (sq_nonneg (Sig a b))
    have hCA : 4 * C * rectFrobSq (coefMat c dims Pm) ≤ 4 * C * Pm.trace :=
      mul_le_mul_of_nonneg_left hAle (by linarith)
    have h1' : ∫ ω, (xiSharpOne c dims Pm xi ω a b) ^ 2 ∂P
        ≤ 2 * ((coefMat c dims Pm).trace * Sig a b) ^ 2
          + 4 * C * rectFrobSq (coefMat c dims Pm) := h1
    have h2' : ∫ ω, (xiSharpTwo c dims Pm Lam xi ω a b) ^ 2 ∂P
        ≤ Lam.trace * (C4 * ((dims.card : ℝ) * (Gmax * (Fintype.card O : ℝ)))) := h2
    rw [hKc]
    linarith [h1', h2', hmono, hsqle, hCA]
  have hfrob : ∀ ω : Ω, rectFrobSq (xiSharp c dims Pm Lam xi ω)
      = ∑ a : ι, ∑ b : ι, (xiSharp c dims Pm Lam xi ω a b) ^ 2 := fun ω => rfl
  simp_rw [hfrob]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hsq a b))]
  have hinner : ∀ a : ι, ∫ ω, ∑ b : ι, (xiSharp c dims Pm Lam xi ω a b) ^ 2 ∂P
      = ∑ b : ι, ∫ ω, (xiSharp c dims Pm Lam xi ω a b) ^ 2 ∂P :=
    fun a => integral_finsetSum _ (fun b _ => hsq a b)
  simp_rw [hinner]
  refine le_trans (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hentry a b) ?_
  have hrow : ∀ a : ι, ∑ b : ι, (4 * (Pm.trace) ^ 2 * (Sig a b) ^ 2 + Kc)
      = 4 * (Pm.trace) ^ 2 * (∑ b : ι, (Sig a b) ^ 2) + (Fintype.card ι : ℝ) * Kc := by
    intro a
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ]
  simp_rw [hrow]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hSig : rectFrobSq Sig = ∑ a : ι, ∑ b : ι, (Sig a b) ^ 2 := rfl
  rw [hSig]
  exact le_of_eq (by ring)


/-- The finite-sample second-moment bound behind Lemma SM.B.9, at `C4 := 2‖Σ_ξ‖_F² + 4C`, with
`hxx` and `hxxint` supplied by `integral_within_pow_four_le_const` and
`integrable_sq_within_mul_within`. -/
theorem integral_rectFrobSq_xiSharp_le_of_moments [IsProbabilityMeasure P] (c : D → O → L)
    {dims : Finset D} (hdims : dims.Nonempty) {Pm Lam : Matrix O O ℝ}
    (hs : Pmᵀ = Pm) (hi : Pm * Pm = Pm) (hLs : Lamᵀ = Lam) (hLi : Lam * Lam = Lam)
    {xi : O → ι → Ω → ℝ} {Sig : Matrix ι ι ℝ} {C Gmax : ℝ} (hC : 0 ≤ C)
    (hG : ∀ (d : D) (l : L), (Cgm.clusterCard (c d) l : ℝ) ≤ Gmax)
    (hint2 : ∀ o o' a b, Integrable (fun ω => xi o a ω * xi o' b ω) P)
    (hint4 : ∀ (a b : ι) (r s : O × O), Integrable
      (fun ω => (xi r.1 a ω * xi r.2 b ω) * (xi s.1 a ω * xi s.2 b ω)) P)
    (hcov : ∀ o o' a b, ∫ ω, xi o a ω * xi o' b ω ∂P = if o = o' then Sig a b else 0)
    (hfour : ∀ (a b : ι) (o o' : O), ∫ ω, (xi o a ω * xi o' b ω) ^ 2 ∂P ≤ C)
    (hpair4 : ∀ (a b : ι) (o o' : O), o ≠ o' →
      ∫ ω, (xi o a ω * xi o b ω) * (xi o' a ω * xi o' b ω) ∂P = Sig a b * Sig a b)
    (hmixed4 : ∀ (a b : ι) (e : O) (p : O × O), p.1 ≠ p.2 →
      ∫ ω, (xi e a ω * xi e b ω) * (xi p.1 a ω * xi p.2 b ω) ∂P = 0)
    (hmixed4' : ∀ (a b : ι) (e : O) (p : O × O), p.1 ≠ p.2 →
      ∫ ω, (xi p.1 a ω * xi p.2 b ω) * (xi e a ω * xi e b ω) ∂P = 0)
    (hquad4 : ∀ (a b : ι) (p q : O × O), p.1 ≠ p.2 → q.1 ≠ q.2 → q ≠ p → q ≠ (p.2, p.1) →
      ∫ ω, (xi p.1 a ω * xi p.2 b ω) * (xi q.1 a ω * xi q.2 b ω) ∂P = 0)
    (hsq1 : ∀ a b : ι, Integrable (fun ω => (xiSharpOne c dims Pm xi ω a b) ^ 2) P)
    (hcsq1 : ∀ a b : ι, Integrable (fun ω => (xiSharpOne c dims Pm xi ω a b
      - (coefMat c dims Pm).trace * Sig a b) ^ 2) P)
    (hsq2 : ∀ a b : ι, Integrable (fun ω => (xiSharpTwo c dims Pm Lam xi ω a b) ^ 2) P)
    (hsq : ∀ a b : ι, Integrable (fun ω => (xiSharp c dims Pm Lam xi ω a b) ^ 2) P) :
    ∫ ω, rectFrobSq (xiSharp c dims Pm Lam xi ω) ∂P
      ≤ 4 * (Pm.trace) ^ 2 * rectFrobSq Sig
        + (Fintype.card ι : ℝ) ^ 2 * (8 * C * Pm.trace
            + 2 * (Lam.trace * ((2 * rectFrobSq Sig + 4 * C)
                * ((dims.card : ℝ) * (Gmax * (Fintype.card O : ℝ)))))) := by
  have hC4 : (0 : ℝ) ≤ 2 * rectFrobSq Sig + 4 * C := by
    have := rectFrobSq_nonneg Sig
    linarith
  refine integral_rectFrobSq_xiSharp_le c hdims hs hi hLs hLi hC hC4 hG hint2 hint4 hcov
    hfour hpair4 hmixed4 hmixed4' hquad4
    (fun o o' a b => integrable_sq_within_mul_within Pm hint4 o o' a b) ?_ hsq1 hcsq1 hsq2 hsq
  intro o o' a b
  exact integral_sq_mul_sq_le (P := P) (fun ω => within Pm xi ω)
    (fun e d => integrable_within_pow_four Pm hint4 e d)
    (fun e e' d d' => integrable_sq_within_mul_within Pm hint4 e e' d d')
    (fun e d => integral_within_pow_four_le_const hC hs hi d hint2 hint4 hcov
      (fun p p' => hfour d d p p') (fun p p' hpp => hpair4 d d p p' hpp)
      (fun p q hq => hmixed4 d d p q hq) (fun p q hq => hmixed4' d d p q hq)
      (fun p q h1 h2 h3 h4 => hquad4 d d p q h1 h2 h3 h4) e)
    o o' a b

end CgmSharpMoments

section OpLift

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem bddInProb_of_integral_nonneg_le {W : ℕ → Ω → ℝ} (hmeas : ∀ n, AEMeasurable (W n) P)
    (hnn : ∀ n ω, 0 ≤ W n ω) (hint : ∀ n, Integrable (W n) P) {M : ℝ}
    (hle : ∀ n, ∫ ω, W n ω ∂P ≤ M) : Sequence.BddInProb P W := by
  refine Sequence.bddInProb_of_lintegral_le hmeas (M := ENNReal.ofReal M) ENNReal.ofReal_ne_top
    (fun n => ?_)
  have h1 : ∫⁻ ω, ‖W n ω‖ₑ ∂P = ENNReal.ofReal (∫ ω, W n ω ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hint n)
      (Filter.Eventually.of_forall (fun ω => hnn n ω))]
    exact lintegral_congr fun ω => Real.enorm_eq_ofReal (hnn n ω)
  rw [h1]
  exact ENNReal.ofReal_le_ofReal (hle n)

theorem bddInProb_of_abs_le_abs {Z W : ℕ → Ω → ℝ} (h : ∀ n ω, |Z n ω| ≤ |W n ω|)
    (hW : Sequence.BddInProb P W) : Sequence.BddInProb P Z := by
  intro δ hδ
  obtain ⟨Cb, hCb0, hCb⟩ := hW δ hδ
  refine ⟨Cb, hCb0, fun n => le_trans (measure_mono (fun ω hω => ?_)) (hCb n)⟩
  simp only [Set.mem_ofPred_eq] at hω ⊢
  exact le_trans hω (h n ω)

/-- `‖·‖ ≤ √S` with `E[S_n] ≤ M a_n²` gives `‖·‖ = O_p(a_n)`. -/
theorem bddInProb_of_integral_sq_le {Nrm S : ℕ → Ω → ℝ} {an : ℕ → ℝ} {M : ℝ}
    (han : ∀ n, 0 < an n) (hSnn : ∀ n ω, 0 ≤ S n ω) (hNrm : ∀ n ω, 0 ≤ Nrm n ω)
    (hle : ∀ n ω, Nrm n ω ≤ Real.sqrt (S n ω))
    (hmeas : ∀ n, AEMeasurable (S n) P) (hint : ∀ n, Integrable (S n) P)
    (hM : ∀ n, ∫ ω, S n ω ∂P ≤ M * (an n) ^ 2) :
    Sequence.BddInProb P (fun n ω => Nrm n ω / an n) := by
  have hW : Sequence.BddInProb P (fun n ω => S n ω / (an n) ^ 2) := by
    refine bddInProb_of_integral_nonneg_le (M := M) (fun n => (hmeas n).div_const _)
      (fun n ω => div_nonneg (hSnn n ω) (sq_nonneg _)) (fun n => (hint n).div_const _)
      (fun n => ?_)
    rw [integral_div, div_le_iff₀ (pow_pos (han n) 2)]
    exact hM n
  refine bddInProb_of_abs_le_abs (fun n ω => ?_) (Sequence.bddInProb_sqrt hW)
  have hsq : Real.sqrt (S n ω / (an n) ^ 2) = Real.sqrt (S n ω) / an n := by
    rw [Real.sqrt_div (hSnn n ω), Real.sqrt_sq (han n).le]
  rw [hsq, abs_of_nonneg (div_nonneg (hNrm n ω) (han n).le),
    abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (han n).le)]
  exact div_le_div_of_nonneg_right (hle n ω) (han n).le

/-- `O_p(a_n)` with `a_n/b_n → 0` gives `⟶^p 0` after dividing by `b_n`. -/
theorem tendstoInProb_of_bddInProb_div {Nrm : ℕ → Ω → ℝ} {an bn : ℕ → ℝ}
    (han : ∀ n, 0 < an n) (hbn : ∀ n, 0 ≤ bn n) (hNrm : ∀ n ω, 0 ≤ Nrm n ω)
    (hB : Sequence.BddInProb P (fun n ω => Nrm n ω / an n))
    (hk : Tendsto (fun n => an n / bn n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => Nrm n ω / bn n) atTop (fun _ => (0 : ℝ)) := by
  refine Sequence.tendstoInProb_zero_of_bddInProb_mul (k := fun n => an n / bn n)
    (fun n => div_nonneg (han n).le (hbn n)) (fun n => ?_) hB hk
  filter_upwards with ω
  rw [abs_of_nonneg (div_nonneg (hNrm n ω) (hbn n)),
    abs_of_nonneg (div_nonneg (hNrm n ω) (han n).le)]
  rcases eq_or_lt_of_le (hbn n) with h | h
  · simp [← h]
  · have ha : an n ≠ 0 := (han n).ne'
    have hb : bn n ≠ 0 := h.ne'
    refine le_of_eq ?_
    field_simp

theorem tendsto_cgmRate_div {dd Gn : ℕ → ℝ} (hGnn : ∀ n, 0 ≤ Gn n)
    (hd : Tendsto (fun n : ℕ => dd n / (n : ℝ)) atTop (𝓝 0))
    (hG : Tendsto (fun n : ℕ => Gn n / ((n : ℝ)) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (dd n + Real.sqrt (Gn n)) / (n : ℝ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => Real.sqrt (Gn n / ((n : ℝ)) ^ 2)) atTop (𝓝 0) := by
    simpa using hG.sqrt
  have h2 : Tendsto (fun n : ℕ => dd n / (n : ℝ) + Real.sqrt (Gn n / ((n : ℝ)) ^ 2))
      atTop (𝓝 0) := by simpa using hd.add h1
  refine Filter.Tendsto.congr' ?_ h2
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [Real.sqrt_div (hGnn n), Real.sqrt_sq hn0.le]
  ring

end OpLift

section CgmSharpSeq

variable {O D L : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable [∀ n, DecidableEq (D n)] [∀ n, Fintype (L n)] [∀ n, DecidableEq (L n)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Lemma SM.B.9**: `‖Ξ_n‖ = O_p(d_[Δ] + (G_max n)^{1/2})`, given the second-moment bound
`hmom`. -/
theorem cgmsharp_bddInProb [IsProbabilityMeasure P]
    (c : ∀ n, D n → O n → L n) (dims : ∀ n, Finset (D n))
    {Pm Lam : ∀ n, Matrix (O n) (O n) ℝ} {xi : ∀ n, O n → ι → Ω → ℝ}
    {Sig : Matrix ι ι ℝ} {C C4 Kbd Jbd : ℝ} {Gmax : ℕ → ℝ}
    (hC : 0 ≤ C) (hC4 : 0 ≤ C4)
    (hPnn : ∀ n, 0 ≤ (Pm n).trace)
    (hLnn : ∀ n, 0 ≤ (Lam n).trace) (hK : ∀ n, (Lam n).trace ≤ Kbd)
    (hJ : ∀ n, ((dims n).card : ℝ) ≤ Jbd)
    (hGnn : ∀ n, 0 ≤ Gmax n * (Fintype.card (O n) : ℝ))
    (hone : ∀ n, 1 ≤ (Pm n).trace + Real.sqrt (Gmax n * (Fintype.card (O n) : ℝ)))
    (hmom : ∀ n, ∫ ω, rectFrobSq (xiSharp (c n) (dims n) (Pm n) (Lam n) (xi n) ω) ∂P
      ≤ 4 * ((Pm n).trace) ^ 2 * rectFrobSq Sig
        + (Fintype.card ι : ℝ) ^ 2 * (8 * C * (Pm n).trace
            + 2 * ((Lam n).trace * (C4 * (((dims n).card : ℝ)
                * (Gmax n * (Fintype.card (O n) : ℝ)))))))
    (hmeas : ∀ n, AEMeasurable
      (fun ω => rectFrobSq (xiSharp (c n) (dims n) (Pm n) (Lam n) (xi n) ω)) P)
    (hint : ∀ n, Integrable
      (fun ω => rectFrobSq (xiSharp (c n) (dims n) (Pm n) (Lam n) (xi n) ω)) P) :
    Sequence.BddInProb P (fun n ω =>
      ‖xiSharp (c n) (dims n) (Pm n) (Lam n) (xi n) ω‖
        / ((Pm n).trace + Real.sqrt (Gmax n * (Fintype.card (O n) : ℝ)))) := by
  refine bddInProb_of_integral_sq_le
    (M := 4 * rectFrobSq Sig + (Fintype.card ι : ℝ) ^ 2 * (8 * C + 2 * (Kbd * (C4 * Jbd))))
    (fun n => lt_of_lt_of_le zero_lt_one (hone n))
    (fun _ _ => rectFrobSq_nonneg _) (fun _ _ => norm_nonneg _) (fun n ω => ?_)
    hmeas hint (fun n => ?_)
  · have hb := Cgm.l2_opNorm_le_rectFrobNorm (xiSharp (c n) (dims n) (Pm n) (Lam n) (xi n) ω)
    rwa [rectFrobNorm] at hb
  · refine le_trans (hmom n) ?_
    set Gn : ℝ := Gmax n * (Fintype.card (O n) : ℝ) with hGn
    set aN : ℝ := (Pm n).trace + Real.sqrt Gn with haN
    have ha1 : 1 ≤ aN := hone n
    have hs0 : 0 ≤ Real.sqrt Gn := Real.sqrt_nonneg _
    have hT0 : 0 ≤ (Pm n).trace := hPnn n
    have hGsq : Gn ≤ aN ^ 2 := by
      have hsq := Real.sq_sqrt (hGnn n)
      rw [haN]
      nlinarith [hsq]
    have ha0 : 0 ≤ aN := by linarith
    have ha2 : 0 ≤ aN ^ 2 := sq_nonneg _
    have hT2 : ((Pm n).trace) ^ 2 ≤ aN ^ 2 := by rw [haN]; nlinarith
    have hTa : (Pm n).trace ≤ aN ^ 2 := by nlinarith
    have hrf : 0 ≤ rectFrobSq Sig := rectFrobSq_nonneg Sig
    have hcard : (0 : ℝ) ≤ (Fintype.card ι : ℝ) ^ 2 := sq_nonneg _
    have hJ0 : (0 : ℝ) ≤ ((dims n).card : ℝ) := Nat.cast_nonneg _
    have hJbd0 : (0 : ℝ) ≤ Jbd := le_trans hJ0 (hJ n)
    have hstep1 : 4 * ((Pm n).trace) ^ 2 * rectFrobSq Sig ≤ 4 * aN ^ 2 * rectFrobSq Sig := by
      nlinarith
    have hstep2 : 8 * C * (Pm n).trace ≤ 8 * C * aN ^ 2 := by nlinarith
    have hB1 : ((dims n).card : ℝ) * Gn ≤ Jbd * aN ^ 2 := by
      have h1 : ((dims n).card : ℝ) * Gn ≤ ((dims n).card : ℝ) * aN ^ 2 :=
        mul_le_mul_of_nonneg_left hGsq hJ0
      have h2 : ((dims n).card : ℝ) * aN ^ 2 ≤ Jbd * aN ^ 2 :=
        mul_le_mul_of_nonneg_right (hJ n) ha2
      linarith
    have hB2 : C4 * (((dims n).card : ℝ) * Gn) ≤ C4 * (Jbd * aN ^ 2) :=
      mul_le_mul_of_nonneg_left hB1 hC4
    have hB2nn : 0 ≤ C4 * (Jbd * aN ^ 2) := by positivity
    have hstep3 : (Lam n).trace * (C4 * (((dims n).card : ℝ) * Gn))
        ≤ Kbd * (C4 * (Jbd * aN ^ 2)) := by
      have h4 : (Lam n).trace * (C4 * (((dims n).card : ℝ) * Gn))
          ≤ (Lam n).trace * (C4 * (Jbd * aN ^ 2)) := mul_le_mul_of_nonneg_left hB2 (hLnn n)
      have h5 : (Lam n).trace * (C4 * (Jbd * aN ^ 2)) ≤ Kbd * (C4 * (Jbd * aN ^ 2)) :=
        mul_le_mul_of_nonneg_right (hK n) hB2nn
      linarith
    have hbr : 8 * C * (Pm n).trace + 2 * ((Lam n).trace * (C4 * (((dims n).card : ℝ) * Gn)))
        ≤ 8 * C * aN ^ 2 + 2 * (Kbd * (C4 * (Jbd * aN ^ 2))) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hbr hcard
    nlinarith [hstep1, hmul]

/-- **Lemma SM.B.9, closing statement**: `‖Ξ_n‖/n ⟶^p 0`. -/
theorem cgmsharp_tendstoInProb [IsProbabilityMeasure P]
    (c : ∀ n, D n → O n → L n) (dims : ∀ n, Finset (D n))
    {Pm Lam : ∀ n, Matrix (O n) (O n) ℝ} {xi : ∀ n, O n → ι → Ω → ℝ} {Gmax : ℕ → ℝ}
    (hone : ∀ n, 1 ≤ (Pm n).trace + Real.sqrt (Gmax n * (Fintype.card (O n) : ℝ)))
    (hB : Sequence.BddInProb P (fun n ω =>
      ‖xiSharp (c n) (dims n) (Pm n) (Lam n) (xi n) ω‖
        / ((Pm n).trace + Real.sqrt (Gmax n * (Fintype.card (O n) : ℝ)))))
    (hrate : Tendsto (fun n : ℕ =>
      ((Pm n).trace + Real.sqrt (Gmax n * (Fintype.card (O n) : ℝ))) / (n : ℝ))
      atTop (𝓝 0)) :
    TendstoInMeasure P
      (fun n ω => ‖xiSharp (c n) (dims n) (Pm n) (Lam n) (xi n) ω‖ / (n : ℝ))
      atTop (fun _ => (0 : ℝ)) :=
  tendstoInProb_of_bddInProb_div (fun n => lt_of_lt_of_le zero_lt_one (hone n))
    (fun n => Nat.cast_nonneg n) (fun _ _ => norm_nonneg _) hB hrate


/-- **Lemma SM.B.9**: `‖Ξ_n‖ = O_p(d_[Δ] + (G_max n)^{1/2})`, with the second-moment bound
supplied at each index by `integral_rectFrobSq_xiSharp_le_of_moments` at
`C4 := 2‖Σ_ξ‖_F² + 4C`. -/
theorem cgmsharp_bddInProb_of_moments [IsProbabilityMeasure P]
    (c : ∀ n, D n → O n → L n) {dims : ∀ n, Finset (D n)} (hdims : ∀ n, (dims n).Nonempty)
    {Pm Lam : ∀ n, Matrix (O n) (O n) ℝ}
    (hs : ∀ n, (Pm n)ᵀ = Pm n) (hi : ∀ n, Pm n * Pm n = Pm n)
    (hLs : ∀ n, (Lam n)ᵀ = Lam n) (hLi : ∀ n, Lam n * Lam n = Lam n)
    {xi : ∀ n, O n → ι → Ω → ℝ} {Sig : Matrix ι ι ℝ} {C Kbd Jbd : ℝ} {Gmax : ℕ → ℝ}
    (hC : 0 ≤ C)
    (hG : ∀ (n : ℕ) (d : D n) (l : L n), (Cgm.clusterCard (c n d) l : ℝ) ≤ Gmax n)
    (hK : ∀ n, (Lam n).trace ≤ Kbd) (hJ : ∀ n, ((dims n).card : ℝ) ≤ Jbd)
    (hGnn : ∀ n, 0 ≤ Gmax n * (Fintype.card (O n) : ℝ))
    (hone : ∀ n, 1 ≤ (Pm n).trace + Real.sqrt (Gmax n * (Fintype.card (O n) : ℝ)))
    (hint2 : ∀ n o o' a b, Integrable (fun ω => xi n o a ω * xi n o' b ω) P)
    (hint4 : ∀ (n : ℕ) (a b : ι) (r s : O n × O n), Integrable
      (fun ω => (xi n r.1 a ω * xi n r.2 b ω) * (xi n s.1 a ω * xi n s.2 b ω)) P)
    (hcov : ∀ n o o' a b,
      ∫ ω, xi n o a ω * xi n o' b ω ∂P = if o = o' then Sig a b else 0)
    (hfour : ∀ (n : ℕ) (a b : ι) (o o' : O n),
      ∫ ω, (xi n o a ω * xi n o' b ω) ^ 2 ∂P ≤ C)
    (hpair4 : ∀ (n : ℕ) (a b : ι) (o o' : O n), o ≠ o' →
      ∫ ω, (xi n o a ω * xi n o b ω) * (xi n o' a ω * xi n o' b ω) ∂P = Sig a b * Sig a b)
    (hmixed4 : ∀ (n : ℕ) (a b : ι) (e : O n) (p : O n × O n), p.1 ≠ p.2 →
      ∫ ω, (xi n e a ω * xi n e b ω) * (xi n p.1 a ω * xi n p.2 b ω) ∂P = 0)
    (hmixed4' : ∀ (n : ℕ) (a b : ι) (e : O n) (p : O n × O n), p.1 ≠ p.2 →
      ∫ ω, (xi n p.1 a ω * xi n p.2 b ω) * (xi n e a ω * xi n e b ω) ∂P = 0)
    (hquad4 : ∀ (n : ℕ) (a b : ι) (p q : O n × O n),
      p.1 ≠ p.2 → q.1 ≠ q.2 → q ≠ p → q ≠ (p.2, p.1) →
      ∫ ω, (xi n p.1 a ω * xi n p.2 b ω) * (xi n q.1 a ω * xi n q.2 b ω) ∂P = 0)
    (hsq1 : ∀ (n : ℕ) (a b : ι),
      Integrable (fun ω => (xiSharpOne (c n) (dims n) (Pm n) (xi n) ω a b) ^ 2) P)
    (hcsq1 : ∀ (n : ℕ) (a b : ι), Integrable (fun ω =>
      (xiSharpOne (c n) (dims n) (Pm n) (xi n) ω a b
        - (coefMat (c n) (dims n) (Pm n)).trace * Sig a b) ^ 2) P)
    (hsq2 : ∀ (n : ℕ) (a b : ι),
      Integrable (fun ω => (xiSharpTwo (c n) (dims n) (Pm n) (Lam n) (xi n) ω a b) ^ 2) P)
    (hsq : ∀ (n : ℕ) (a b : ι),
      Integrable (fun ω => (xiSharp (c n) (dims n) (Pm n) (Lam n) (xi n) ω a b) ^ 2) P)
    (hmeas : ∀ n, AEMeasurable
      (fun ω => rectFrobSq (xiSharp (c n) (dims n) (Pm n) (Lam n) (xi n) ω)) P)
    (hint : ∀ n, Integrable
      (fun ω => rectFrobSq (xiSharp (c n) (dims n) (Pm n) (Lam n) (xi n) ω)) P) :
    Sequence.BddInProb P (fun n ω =>
      ‖xiSharp (c n) (dims n) (Pm n) (Lam n) (xi n) ω‖
        / ((Pm n).trace + Real.sqrt (Gmax n * (Fintype.card (O n) : ℝ)))) := by
  have hC4 : (0 : ℝ) ≤ 2 * rectFrobSq Sig + 4 * C := by
    have := rectFrobSq_nonneg Sig
    linarith
  exact cgmsharp_bddInProb (P := P) c dims (Sig := Sig) (C := C)
    (C4 := 2 * rectFrobSq Sig + 4 * C) (Kbd := Kbd) (Jbd := Jbd) (Gmax := Gmax) hC hC4
    (fun n => Cgm.trace_nonneg_of_symmProj (hs n) (hi n))
    (fun n => Cgm.trace_nonneg_of_symmProj (hLs n) (hLi n)) hK hJ hGnn hone
    (fun n => integral_rectFrobSq_xiSharp_le_of_moments (c n) (hdims n) (hs n) (hi n)
      (hLs n) (hLi n) hC (hG n) (hint2 n) (hint4 n) (hcov n) (hfour n) (hpair4 n)
      (hmixed4 n) (hmixed4' n) (hquad4 n) (hsq1 n) (hcsq1 n) (hsq2 n) (hsq n))
    hmeas hint

end CgmSharpSeq

/-! ### Witnesses for the variance expansion and Lemma SM.B.9

* `quadvar_compl_le_witness`: `quadvar_compl_le` at `j = 0 ≠ 1 = k`, on a deterministic model
  with `(Σ_ξ)_{01} = 2`.
* `cgmsharp_witness`: `cgmsharp_bddInProb` on a growing design with `n+1` observations at index
  `n`, `d_[Δ] = 1`, `Λ = 0` and `G_max = 1`, so the normalizer is `1 + √(n+1)`; the innovations
  are degenerate.
* `integral_within_pow_four_le_witness`, `integral_rectFrobSq_xiSharp_le_of_moments_witness`: a
  fair coin with two observations, where `E[x̃⁴_{0,0}] = 1/2` and `E‖Ξ_n‖_F² = 1/2`.
-/

section CgmSharpWitness

open scoped Matrix

/-- The bilinear witness innovations: one observation, two regressor coordinates, values `1`
and `2`, so that `(Σ_ξ)_{01} = 2`. -/
def bilWitnessXi : Fin 1 → Fin 2 → Unit → ℝ := fun _ a _ => if a = 0 then 1 else 2

/-- `Σ_ξ` for that model. `(Σ_ξ)_{01} = 2`. -/
def bilWitnessSig : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun a b => (if a = 0 then (1 : ℝ) else 2) * (if b = 0 then (1 : ℝ) else 2)

theorem bilWitnessSig_offDiag : bilWitnessSig 0 1 = 2 := by
  rw [bilWitnessSig]
  norm_num

theorem bilWitness_int (o o' : Fin 1) (a b : Fin 2) :
    Integrable (fun u => bilWitnessXi o a u * bilWitnessXi o' b u) (Measure.dirac ()) := by
  simp [bilWitnessXi]

theorem bilWitness_int4 (r s : Fin 1 × Fin 1) :
    Integrable (fun u => (bilWitnessXi r.1 0 u * bilWitnessXi r.2 1 u)
      * (bilWitnessXi s.1 0 u * bilWitnessXi s.2 1 u)) (Measure.dirac ()) := by
  simp [bilWitnessXi]

theorem bilWitness_cov (o o' : Fin 1) (a b : Fin 2) :
    (integral (Measure.dirac ()) fun u => bilWitnessXi o a u * bilWitnessXi o' b u)
      = if o = o' then bilWitnessSig a b else 0 := by
  have ho : o = o' := Subsingleton.elim _ _
  subst ho
  simp [bilWitnessXi, bilWitnessSig]

theorem bilWitness_four (o o' : Fin 1) :
    (integral (Measure.dirac ()) fun u => (bilWitnessXi o 0 u * bilWitnessXi o' 1 u) ^ 2)
      ≤ (4 : ℝ) := by
  simp [bilWitnessXi]
  norm_num

/-- `E[(Θ'IΘ)_{01}] = tr(I)(Σ_ξ)_{01} = 2`. -/
theorem bilWitness_mean :
    (integral (Measure.dirac ()) fun u =>
        ((theta bilWitnessXi u)ᵀ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * theta bilWitnessXi u) 0 1)
      = 2 := by
  have h := integral_quad (P := Measure.dirac ()) (1 : Matrix (Fin 1) (Fin 1) ℝ)
    (xi := bilWitnessXi) (Sig := bilWitnessSig) 0 1 bilWitness_int bilWitness_cov
  rw [h, bilWitnessSig_offDiag]
  simp

/-- Witness for `quadvar_compl_le` at `j = 0 ≠ 1 = k`. -/
theorem quadvar_compl_le_witness :
    (integral (Measure.dirac ()) fun u =>
        (((theta bilWitnessXi u)ᵀ
              * ((1 : Matrix (Fin 1) (Fin 1) ℝ) - (0 : Matrix (Fin 1) (Fin 1) ℝ))
              * theta bilWitnessXi u) 0 1
          - ((1 : Matrix (Fin 1) (Fin 1) ℝ) - (0 : Matrix (Fin 1) (Fin 1) ℝ)).trace
              * bilWitnessSig 0 1) ^ 2)
      ≤ 2 * 4 * (Fintype.card (Fin 1) : ℝ) :=
  quadvar_compl_le (P := Measure.dirac ()) (xi := bilWitnessXi) (Sig := bilWitnessSig)
    (j := 0) (k := 1) (C := 4) (Pm := (0 : Matrix (Fin 1) (Fin 1) ℝ))
    (by norm_num) Matrix.transpose_zero (by simp)
    bilWitness_int bilWitness_int4 bilWitness_cov bilWitness_four
    (fun o o' h => absurd (Subsingleton.elim o o') h)
    (fun _ p h => absurd (Subsingleton.elim p.1 p.2) h)
    (fun _ p h => absurd (Subsingleton.elim p.1 p.2) h)
    (fun p _ h _ _ _ => absurd (Subsingleton.elim p.1 p.2) h)

/-- The design-level witness: `P_[Δ]` a rank-one diagonal projector, so `d_[Δ] = 1`. -/
def sharpWitnessPm (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.diagonal (fun o => if o = 0 then (1 : ℝ) else 0)

theorem sharpWitnessPm_trace (n : ℕ) : (sharpWitnessPm n).trace = 1 := by
  rw [sharpWitnessPm, Matrix.trace_diagonal]
  simp

/-- The normalizer `d_[Δ] + (G_max n)^{1/2}` is `2` at `n = 0` and `1 + √2` at `n = 1`. -/
theorem cgmsharp_witness_boundary :
    (sharpWitnessPm 0).trace + Real.sqrt (1 * (Fintype.card (Fin 1) : ℝ)) = 2
      ∧ (sharpWitnessPm 1).trace + Real.sqrt (1 * (Fintype.card (Fin 2) : ℝ))
          = 1 + Real.sqrt 2 := by
  constructor
  · rw [sharpWitnessPm_trace]
    norm_num
  · rw [sharpWitnessPm_trace]
    norm_num

/-- Witness for `cgmsharp_bddInProb` on a growing design, with `ξ ≡ 0`. -/
theorem cgmsharp_witness :
    Sequence.BddInProb (Measure.dirac ())
      (fun (n : ℕ) (u : Unit) =>
        ‖xiSharp (fun (_ : Fin 1) (_ : Fin (n + 1)) => (0 : Fin 1)) ({0} : Finset (Fin 1))
            (sharpWitnessPm n) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
            (fun (_ : Fin (n + 1)) (_ : Fin 1) (_ : Unit) => (0 : ℝ)) u‖
          / ((sharpWitnessPm n).trace
              + Real.sqrt (1 * (Fintype.card (Fin (n + 1)) : ℝ)))) := by
  have hzero : ∀ (n : ℕ) (u : Unit),
      xiSharp (fun (_ : Fin 1) (_ : Fin (n + 1)) => (0 : Fin 1)) ({0} : Finset (Fin 1))
          (sharpWitnessPm n) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
          (fun (_ : Fin (n + 1)) (_ : Fin 1) (_ : Unit) => (0 : ℝ)) u = 0 := by
    intro n u
    have hth : theta (fun (_ : Fin (n + 1)) (_ : Fin 1) (_ : Unit) => (0 : ℝ)) u = 0 := by
      ext o j; rfl
    rw [xiSharp, within, hth, Matrix.mul_zero, Cgm.xiMat]
    simp
  refine cgmsharp_bddInProb (P := Measure.dirac ())
    (c := fun (n : ℕ) (_ : Fin 1) (_ : Fin (n + 1)) => (0 : Fin 1))
    (dims := fun (_ : ℕ) => ({0} : Finset (Fin 1)))
    (Pm := sharpWitnessPm) (Lam := fun n => (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
    (xi := fun (n : ℕ) (_ : Fin (n + 1)) (_ : Fin 1) (_ : Unit) => (0 : ℝ))
    (Sig := (0 : Matrix (Fin 1) (Fin 1) ℝ)) (C := 0) (C4 := 0) (Kbd := 0) (Jbd := 1)
    (Gmax := fun _ => 1)
    (hC := le_rfl) (hC4 := le_rfl)
    (hPnn := fun n => by rw [sharpWitnessPm_trace]; norm_num)
    (hLnn := fun n => by simp)
    (hK := fun n => by simp)
    (hJ := fun n => by simp)
    (hGnn := fun n => by positivity)
    (hone := fun n => ?_) (hmom := fun n => ?_)
    (hmeas := fun n => ?_) (hint := fun n => ?_)
  · have hnn := Real.sqrt_nonneg (1 * (Fintype.card (Fin (n + 1)) : ℝ))
    rw [sharpWitnessPm_trace]
    linarith
  · simp only [hzero n]
    rw [sharpWitnessPm_trace]
    simp [rectFrobSq]
  · simp only [hzero n]
    exact aemeasurable_const
  · simp only [hzero n]
    exact integrable_const _


/-! #### Witnesses with two observations and a random innovation

A fair coin on `Ω = Bool` with `O = Fin 2`, `ξ_0` a fair sign and `ξ_1 ≡ 1`, so that `Σ_ξ = 1`
and `E[ξ_0ξ_1] = 0`, and `P_[Δ] = ιι'/2`, so that `Q_{oo} = 1/2`. The identity `hquad4` is
vacuous on two observations.
-/

/-- A fair coin, the smallest space on which two observations can have zero covariance. -/
noncomputable def fourthCoin : Measure Bool :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure fourthCoin := by
  constructor
  simp only [fourthCoin, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [show (1 : ℝ≥0∞) + 1 = 2 by norm_num,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

theorem integral_fourthCoin (f : Bool → ℝ) :
    ∫ b, f b ∂fourthCoin = (f true + f false) / 2 := by
  rw [fourthCoin, integral_smul_measure,
    integral_add_measure (Integrable.of_finite) (Integrable.of_finite),
    integral_dirac, integral_dirac, ENNReal.toReal_inv]
  simp only [smul_eq_mul]
  norm_num
  ring

/-- Two observations, one regressor: `ξ_0` a fair sign, `ξ_1 ≡ 1`. -/
def fourthXi : Fin 2 → Fin 1 → Bool → ℝ :=
  fun o _ ω => if o = 0 then (if ω then (1 : ℝ) else -1) else 1

/-- `Σ_ξ = 1` for that model. -/
def fourthSig : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ => (1 : ℝ)

/-- `P_[Δ] = ιι'/2`, the mean projector on two observations, so `Q_{oo} = 1/2`. -/
noncomputable def fourthPm : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun _ _ => (1 / 2 : ℝ)

theorem fourthPm_symm : fourthPmᵀ = fourthPm := by
  ext i j; rfl

theorem fourthPm_idem : fourthPm * fourthPm = fourthPm := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp [fourthPm]
  norm_num

theorem fourth_int (o o' : Fin 2) (a b : Fin 1) :
    Integrable (fun ω => fourthXi o a ω * fourthXi o' b ω) fourthCoin := Integrable.of_finite

theorem fourth_int4 (a b : Fin 1) (r s : Fin 2 × Fin 2) :
    Integrable (fun ω => (fourthXi r.1 a ω * fourthXi r.2 b ω)
      * (fourthXi s.1 a ω * fourthXi s.2 b ω)) fourthCoin := Integrable.of_finite

theorem fourth_cov (o o' : Fin 2) (a b : Fin 1) :
    ∫ ω, fourthXi o a ω * fourthXi o' b ω ∂fourthCoin
      = if o = o' then fourthSig a b else 0 := by
  rw [integral_fourthCoin]
  fin_cases o <;> fin_cases o' <;> norm_num [fourthXi, fourthSig]

theorem fourth_four (a b : Fin 1) (o o' : Fin 2) :
    ∫ ω, (fourthXi o a ω * fourthXi o' b ω) ^ 2 ∂fourthCoin ≤ (1 : ℝ) := by
  rw [integral_fourthCoin]
  fin_cases o <;> fin_cases o' <;> norm_num [fourthXi]

theorem fourth_pair4 (a b : Fin 1) (o o' : Fin 2) (h : o ≠ o') :
    ∫ ω, (fourthXi o a ω * fourthXi o b ω) * (fourthXi o' a ω * fourthXi o' b ω) ∂fourthCoin
      = fourthSig a b * fourthSig a b := by
  rw [integral_fourthCoin]
  fin_cases o <;> fin_cases o' <;> simp_all <;> norm_num [fourthXi, fourthSig]

theorem fourth_mixed4 (a b : Fin 1) (e : Fin 2) (p : Fin 2 × Fin 2) (h : p.1 ≠ p.2) :
    ∫ ω, (fourthXi e a ω * fourthXi e b ω)
      * (fourthXi p.1 a ω * fourthXi p.2 b ω) ∂fourthCoin = 0 := by
  rw [integral_fourthCoin]
  obtain ⟨p1, p2⟩ := p
  fin_cases e <;> fin_cases p1 <;> fin_cases p2 <;> simp_all <;> norm_num [fourthXi]

theorem fourth_mixed4' (a b : Fin 1) (e : Fin 2) (p : Fin 2 × Fin 2) (h : p.1 ≠ p.2) :
    ∫ ω, (fourthXi p.1 a ω * fourthXi p.2 b ω)
      * (fourthXi e a ω * fourthXi e b ω) ∂fourthCoin = 0 := by
  rw [integral_fourthCoin]
  obtain ⟨p1, p2⟩ := p
  fin_cases e <;> fin_cases p1 <;> fin_cases p2 <;> simp_all <;> norm_num [fourthXi]

/-- Vacuous on two observations: with `p.1 ≠ p.2` and `q.1 ≠ q.2` on `Fin 2`, `q` is `p` or
`pᵀ`. -/
theorem fourth_quad4 (a b : Fin 1) (p q : Fin 2 × Fin 2) (hp : p.1 ≠ p.2) (hq : q.1 ≠ q.2)
    (h1 : q ≠ p) (h2 : q ≠ (p.2, p.1)) :
    ∫ ω, (fourthXi p.1 a ω * fourthXi p.2 b ω)
      * (fourthXi q.1 a ω * fourthXi q.2 b ω) ∂fourthCoin = 0 := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;> simp_all

theorem fourth_within_apply (ω : Bool) :
    within fourthPm fourthXi ω 0 0 = (if ω then (0 : ℝ) else -1) := by
  rw [within, Matrix.mul_apply, Fin.sum_univ_two]
  by_cases hw : ω = true <;>
    simp [fourthPm, fourthXi, theta, Matrix.sub_apply, hw] <;> norm_num

/-- `E[x̃⁴_{0,0}] = 1/2`. -/
theorem fourth_moment_nonzero :
    ∫ ω, (within fourthPm fourthXi ω 0 0) ^ 4 ∂fourthCoin = 1 / 2 := by
  simp_rw [fourth_within_apply]
  rw [integral_fourthCoin]
  norm_num

/-- Witness for `integral_within_pow_four_le`; the bound reads `1/2 ≤ (1/2)²·6 = 3/2`. -/
theorem integral_within_pow_four_le_witness :
    ∫ ω, (within fourthPm fourthXi ω 0 0) ^ 4 ∂fourthCoin
      ≤ (((1 : Matrix (Fin 2) (Fin 2) ℝ) - fourthPm) 0 0) ^ 2
          * (2 * (fourthSig 0 0) ^ 2 + 4 * 1) :=
  integral_within_pow_four_le (P := fourthCoin) (xi := fourthXi) (Sig := fourthSig) (C := 1)
    zero_le_one fourthPm_symm fourthPm_idem 0 fourth_int fourth_int4 fourth_cov
    (fourth_four 0 0) (fourth_pair4 0 0) (fourth_mixed4 0 0) (fourth_mixed4' 0 0)
    (fourth_quad4 0 0) 0

/-- One maintained dimension with one label: both observations share a cluster. -/
def fourthC : Fin 1 → Fin 2 → Fin 1 := fun _ _ => 0

theorem fourthC_clusterCard (d : Fin 1) (l : Fin 1) :
    (Cgm.clusterCard (fourthC d) l : ℝ) ≤ 2 := by
  have hd : d = 0 := Subsingleton.elim _ _
  have hl : l = 0 := Subsingleton.elim _ _
  subst hd; subst hl
  have h : Cgm.clusterCard (fourthC 0) 0 = 2 := by decide
  rw [h]
  norm_num

theorem fourth_xiSharp_apply (ω : Bool) :
    xiSharp fourthC ({0} : Finset (Fin 1)) fourthPm (0 : Matrix (Fin 2) (Fin 2) ℝ)
        fourthXi ω 0 0
      = (if ω then (0 : ℝ) else 1) := by
  rw [xiSharp, Cgm.xiMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Matrix.transpose_apply, Matrix.hadamard_apply, Matrix.sub_apply, Cgm.linkMat_apply,
    Matrix.one_apply, Matrix.zero_apply]
  rw [fourth_within_apply]
  have h1 : within fourthPm fourthXi ω 1 0 = (if ω then (0 : ℝ) else 1) := by
    rw [within, Matrix.mul_apply, Fin.sum_univ_two]
    by_cases hw : ω = true <;>
      simp [fourthPm, fourthXi, theta, Matrix.sub_apply, hw] <;> norm_num
  rw [h1]
  have hlink : ∀ o o' : Fin 2, Linked fourthC ({0} : Finset (Fin 1)) o o' :=
    fun o o' => ⟨0, Finset.mem_singleton_self 0, rfl⟩
  by_cases hw : ω = true <;> simp [fourthPm, hw, hlink] <;> norm_num

/-- `E‖Ξ_n‖_F² = 1/2`. -/
theorem fourth_xiSharp_moment :
    ∫ ω, rectFrobSq (xiSharp fourthC ({0} : Finset (Fin 1)) fourthPm
      (0 : Matrix (Fin 2) (Fin 2) ℝ) fourthXi ω) ∂fourthCoin = 1 / 2 := by
  have h : ∀ ω : Bool, rectFrobSq (xiSharp fourthC ({0} : Finset (Fin 1)) fourthPm
      (0 : Matrix (Fin 2) (Fin 2) ℝ) fourthXi ω) = (if ω then (0 : ℝ) else 1) := by
    intro ω
    rw [rectFrobSq, Fin.sum_univ_one, Fin.sum_univ_one, fourth_xiSharp_apply]
    by_cases hw : ω = true <;> simp [hw]
  simp_rw [h]
  rw [integral_fourthCoin]
  norm_num

/-- Witness for `integral_rectFrobSq_xiSharp_le_of_moments`, with `Ξ_n` not identically
zero. -/
theorem integral_rectFrobSq_xiSharp_le_of_moments_witness :
    ∫ ω, rectFrobSq (xiSharp fourthC ({0} : Finset (Fin 1)) fourthPm
        (0 : Matrix (Fin 2) (Fin 2) ℝ) fourthXi ω) ∂fourthCoin
      ≤ 4 * (fourthPm.trace) ^ 2 * rectFrobSq fourthSig
        + (Fintype.card (Fin 1) : ℝ) ^ 2 * (8 * 1 * fourthPm.trace
            + 2 * ((0 : Matrix (Fin 2) (Fin 2) ℝ).trace
                * ((2 * rectFrobSq fourthSig + 4 * 1)
                  * ((({0} : Finset (Fin 1)).card : ℝ)
                    * (2 * (Fintype.card (Fin 2) : ℝ)))))) :=
  integral_rectFrobSq_xiSharp_le_of_moments (P := fourthCoin) (xi := fourthXi)
    (Sig := fourthSig) (C := 1) (Gmax := 2) fourthC (Finset.singleton_nonempty 0)
    fourthPm_symm fourthPm_idem Matrix.transpose_zero (by simp) zero_le_one fourthC_clusterCard
    fourth_int fourth_int4 fourth_cov fourth_four fourth_pair4 fourth_mixed4 fourth_mixed4'
    fourth_quad4 (fun _ _ => Integrable.of_finite) (fun _ _ => Integrable.of_finite)
    (fun _ _ => Integrable.of_finite) (fun _ _ => Integrable.of_finite)


/-- Witness for `cgmsharp_bddInProb_of_moments` on a growing design, with each observation in
its own cluster (`Cgm.clusterCard = 1`) and degenerate innovations. -/
theorem cgmsharp_witness_of_moments :
    Sequence.BddInProb (Measure.dirac ())
      (fun (n : ℕ) (u : Unit) =>
        ‖xiSharp (fun (_ : Fin 1) (o : Fin (n + 1)) => o) ({0} : Finset (Fin 1))
            (sharpWitnessPm n) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
            (fun (_ : Fin (n + 1)) (_ : Fin 1) (_ : Unit) => (0 : ℝ)) u‖
          / ((sharpWitnessPm n).trace
              + Real.sqrt (1 * (Fintype.card (Fin (n + 1)) : ℝ)))) := by
  have hzero : ∀ (n : ℕ) (u : Unit),
      xiSharp (fun (_ : Fin 1) (o : Fin (n + 1)) => o) ({0} : Finset (Fin 1))
          (sharpWitnessPm n) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
          (fun (_ : Fin (n + 1)) (_ : Fin 1) (_ : Unit) => (0 : ℝ)) u = 0 := by
    intro n u
    have hth : theta (fun (_ : Fin (n + 1)) (_ : Fin 1) (_ : Unit) => (0 : ℝ)) u = 0 := by
      ext o j; rfl
    rw [xiSharp, within, hth, Matrix.mul_zero, Cgm.xiMat]
    simp
  refine cgmsharp_bddInProb_of_moments (P := Measure.dirac ())
    (c := fun (n : ℕ) (_ : Fin 1) (o : Fin (n + 1)) => o)
    (dims := fun (_ : ℕ) => ({0} : Finset (Fin 1)))
    (Pm := sharpWitnessPm) (Lam := fun n => (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
    (xi := fun (n : ℕ) (_ : Fin (n + 1)) (_ : Fin 1) (_ : Unit) => (0 : ℝ))
    (Sig := (0 : Matrix (Fin 1) (Fin 1) ℝ)) (C := 0) (Kbd := 0) (Jbd := 1)
    (Gmax := fun _ => 1)
    (hdims := fun _ => Finset.singleton_nonempty 0)
    (hs := fun n => by rw [sharpWitnessPm, Matrix.diagonal_transpose])
    (hi := fun n => by
      rw [sharpWitnessPm, Matrix.diagonal_mul_diagonal]
      congr 1
      funext o
      by_cases h : o = 0 <;> simp [h])
    (hLs := fun n => Matrix.transpose_zero) (hLi := fun n => by simp)
    (hC := le_rfl)
    (hG := fun n d l => by
      have h : Cgm.clusterCard (fun (o : Fin (n + 1)) => o) l = 1 := by
        rw [Cgm.clusterCard, Finset.filter_eq']
        simp
      rw [h]
      norm_num)
    (hK := fun n => by simp)
    (hJ := fun n => by simp)
    (hGnn := fun n => by positivity)
    (hone := fun n => ?_)
    (hint2 := fun n o o' a b => by simp)
    (hint4 := fun n a b r s => by simp)
    (hcov := fun n o o' a b => by by_cases h : o = o' <;> simp [h])
    (hfour := fun n a b o o' => by simp)
    (hpair4 := fun n a b o o' h => by simp)
    (hmixed4 := fun n a b e p h => by simp)
    (hmixed4' := fun n a b e p h => by simp)
    (hquad4 := fun n a b p q h1 h2 h3 h4 => by simp)
    (hsq1 := fun n a b => by simp [xiSharpOne, theta])
    (hcsq1 := fun n a b => by simp [xiSharpOne, theta])
    (hsq2 := fun n a b => by simp [xiSharpTwo, within, theta])
    (hsq := fun n a b => by simp [hzero n])
    (hmeas := fun n => by simp only [hzero n]; exact aemeasurable_const)
    (hint := fun n => by simp only [hzero n]; exact integrable_const _)
  · have hnn := Real.sqrt_nonneg (1 * (Fintype.card (Fin (n + 1)) : ℝ))
    rw [sharpWitnessPm_trace]
    linarith

end CgmSharpWitness


/-! ### Deconditioning bridges

Let `ℙ_ω := condExpKernel P 𝒟 ω`, which requires `[StandardBorelSpace Ω]`.

* `tendstoInMeasure_of_deconditioning`: if `ℙ_ω(ε ≤ |Z_n - g|) → 0` for `P`-almost every `ω`,
  then `P(ε ≤ |Z_n - g|) = ∫ℙ_ω(ε ≤ |Z_n - g|)dP → 0` by dominated convergence.
* `tendstoInMeasure_of_design`: a statistic of a `𝒟`-measurable design `D_n` agrees
  `ℙ_ω`-almost surely with the statistic at the frozen design `D_n(ω)`
  (`CLTMartingale.CondD.ae_ae_eq_condExpKernel`). The design type is a family `γ : ℕ → Type*`.
* `ae_ae_eq_design`: the same freezing for matrix-valued designs, entry by entry.
* `lintegral_le_of_deconditioning`: a lower-integral bound under `ℙ_ω` for `P`-almost every `ω`
  gives the same bound under `P`.
-/

open ProbabilityTheory

namespace CondP

variable {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The law of total probability: `P(A) = ∫ℙ_ω(A)dP`. -/
theorem integral_condExpKernel_real (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsFiniteMeasure P]
    {A : Set Ω} (hA : MeasurableSet A) :
    (∫ ω, (condExpKernel P 𝒟 ω).real A ∂P) = P.real A := by
  rw [integral_congr_ae (condExpKernel_ae_eq_condExp h𝒟 hA), integral_condExp h𝒟,
    integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one]

omit [StandardBorelSpace Ω] in
/-- `⟶^p` transfers along an almost-everywhere equality of the sequences. -/
theorem tendstoInMeasure_congr_ae {E : Type*} [EDist E] {P : Measure Ω}
    {Z Z' : ℕ → Ω → E} {g : Ω → E}
    (h : ∀ n, Z n =ᵐ[P] Z' n) (hZ : TendstoInMeasure P Z atTop g) :
    TendstoInMeasure P Z' atTop g := by
  intro ε hε
  refine Tendsto.congr (fun n => ?_) (hZ ε hε)
  refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
  filter_upwards [h n] with y hy
  rw [hy]

/-- Convergence in measure under `ℙ_ω := condExpKernel P 𝒟 ω`, at `P`-almost every `ω`, gives
convergence in measure under `P`. -/
theorem tendstoInMeasure_of_deconditioning {E : Type*} [EDist E]
    (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsFiniteMeasure P]
    {Z : ℕ → Ω → E} {g : Ω → E}
    (hA : ∀ (ε : ℝ≥0∞) (n : ℕ), MeasurableSet {y : Ω | ε ≤ edist (Z n y) (g y)})
    (hcond : ∀ᵐ ω ∂P, TendstoInMeasure (condExpKernel P 𝒟 ω) Z atTop g) :
    TendstoInMeasure P Z atTop g := by
  intro ε hε
  have hmeas : ∀ n : ℕ, Measurable
      (fun ω => (condExpKernel P 𝒟 ω).real {y : Ω | ε ≤ edist (Z n y) (g y)}) := by
    intro n
    simp only [measureReal_def]
    exact ((measurable_condExpKernel (hA ε n)).mono h𝒟 le_rfl).ennreal_toReal
  have hbound : ∀ n : ℕ, ∀ᵐ ω ∂P,
      ‖(condExpKernel P 𝒟 ω).real {y : Ω | ε ≤ edist (Z n y) (g y)}‖ ≤ (1 : ℝ) := by
    intro n
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
      (condExpKernel P 𝒟 ω).real {y : Ω | ε ≤ edist (Z n y) (g y)}) atTop (𝓝 0) := by
    filter_upwards [hcond] with ω hω
    simp only [measureReal_def]
    exact (ENNReal.tendsto_toReal_zero_iff (fun n => measure_ne_top _ _)).2 (hω ε hε)
  have hdom := tendsto_integral_of_dominated_convergence (μ := P) (fun _ => (1 : ℝ))
    (fun n => (hmeas n).aestronglyMeasurable) (integrable_const 1) hbound hlim
  have hreal : Tendsto (fun n : ℕ => P.real {y : Ω | ε ≤ edist (Z n y) (g y)}) atTop (𝓝 0) := by
    refine Tendsto.congr (fun n => integral_condExpKernel_real h𝒟 P (hA ε n)) ?_
    simpa using hdom
  exact (ENNReal.tendsto_toReal_zero_iff (fun n => measure_ne_top _ _)).1 hreal

/-- Convergence in measure with a frozen design: if the statistic is a measurable function
`F n` of the design `D n` and the data (`hZ`), the design is `𝒟`-measurable (`hD`), and the
frozen-design convergence holds under `ℙ_ω` at almost every `ω` (`hfrozen`), then the
convergence holds under `P`. -/
theorem tendstoInMeasure_of_design {E : Type*} [EDist E]
    (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsFiniteMeasure P]
    {γ : ℕ → Type*} [∀ n, MeasurableSpace (γ n)] [∀ n, MeasurableEq (γ n)]
    {D : ∀ n, Ω → γ n} (hD : ∀ n, Measurable[𝒟] (D n))
    {F : ∀ n, γ n → Ω → E} {Z : ℕ → Ω → E} (hZ : ∀ n y, Z n y = F n (D n y) y)
    {g : Ω → E}
    (hA : ∀ (ε : ℝ≥0∞) (n : ℕ), MeasurableSet {y : Ω | ε ≤ edist (Z n y) (g y)})
    (hfrozen : ∀ᵐ ω ∂P, TendstoInMeasure (condExpKernel P 𝒟 ω)
      (fun n y => F n (D n ω) y) atTop g) :
    TendstoInMeasure P Z atTop g := by
  refine tendstoInMeasure_of_deconditioning h𝒟 P hA ?_
  have hfz : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ᵐ y ∂(condExpKernel P 𝒟 ω), D n y = D n ω :=
    ae_all_iff.2 fun n => Multiway.CLTMartingale.CondD.ae_ae_eq_condExpKernel h𝒟 P (hD n)
  filter_upwards [hfz, hfrozen] with ω hω hcl
  refine tendstoInMeasure_congr_ae (Z := fun n y => F n (D n ω) y) (fun n => ?_) hcl
  filter_upwards [hω n] with y hy
  rw [hZ n y, hy]

/-- The freezing of a matrix-valued design, entry by entry: each real entry is frozen by
`ae_ae_eq_condExpKernel`, and the countably many a.e. statements are combined with
`ae_all_iff` and `Matrix.ext`. -/
theorem ae_ae_eq_design (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsFiniteMeasure P]
    {O : ℕ → Type*} [∀ n, Fintype (O n)] {ι : Type*} [Fintype ι]
    {mu : ∀ n, Ω → Matrix (O n) ι ℝ} {Pm : ∀ n, Ω → Matrix (O n) (O n) ℝ}
    (hmuD : ∀ n o a, Measurable[𝒟] fun ω => mu n ω o a)
    (hPmD : ∀ n o o', Measurable[𝒟] fun ω => Pm n ω o o') :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ᵐ y ∂(condExpKernel P 𝒟 ω), mu n y = mu n ω ∧ Pm n y = Pm n ω := by
  refine ae_all_iff.2 fun n => ?_
  have h1 : ∀ᵐ ω ∂P, ∀ p : O n × ι, ∀ᵐ y ∂(condExpKernel P 𝒟 ω),
      mu n y p.1 p.2 = mu n ω p.1 p.2 :=
    ae_all_iff.2 fun p =>
      Multiway.CLTMartingale.CondD.ae_ae_eq_condExpKernel h𝒟 P (hmuD n p.1 p.2)
  have h2 : ∀ᵐ ω ∂P, ∀ p : O n × O n, ∀ᵐ y ∂(condExpKernel P 𝒟 ω),
      Pm n y p.1 p.2 = Pm n ω p.1 p.2 :=
    ae_all_iff.2 fun p =>
      Multiway.CLTMartingale.CondD.ae_ae_eq_condExpKernel h𝒟 P (hPmD n p.1 p.2)
  filter_upwards [h1, h2] with ω hω1 hω2
  filter_upwards [ae_all_iff.2 hω1, ae_all_iff.2 hω2] with y hy1 hy2
  exact ⟨Matrix.ext fun o a => hy1 (o, a), Matrix.ext fun o o' => hy2 (o, o')⟩

/-- A bound on a lower integral under `ℙ_ω := condExpKernel P 𝒟 ω`, holding at `P`-almost every
`ω`, gives the same bound under `P`. The proof disintegrates `P` through
`condExpKernel_comp_trim`, `Measure.lintegral_bind_le` and `lintegral_trim`; `f` need only be
`AEMeasurable` under `P`. -/
theorem lintegral_le_of_deconditioning (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    {f : Ω → ℝ≥0∞} (hf : AEMeasurable f P) {M : ℝ≥0∞}
    (hcond : ∀ᵐ ω ∂P, ∫⁻ y, f y ∂(condExpKernel P 𝒟 ω) ≤ M) :
    ∫⁻ y, f y ∂P ≤ M := by
  have hbind : Measure.bind (P.trim h𝒟) (condExpKernel P 𝒟) = P := condExpKernel_comp_trim h𝒟
  have hgm : Measurable (hf.mk f) := hf.measurable_mk
  have hfg : f =ᵐ[P] hf.mk f := hf.ae_eq_mk
  have hfg_trim : ∀ᵐ ω ∂(P.trim h𝒟), ∀ᵐ y ∂(condExpKernel P 𝒟 ω), f y = hf.mk f y := by
    refine Measure.ae_ae_of_ae_comp ?_
    rw [hbind]
    exact hfg
  have hfg_P : ∀ᵐ ω ∂P, ∀ᵐ y ∂(condExpKernel P 𝒟 ω), f y = hf.mk f y :=
    ae_of_ae_trim h𝒟 hfg_trim
  have hcond' : ∀ᵐ ω ∂P, ∫⁻ y, hf.mk f y ∂(condExpKernel P 𝒟 ω) ≤ M := by
    filter_upwards [hcond, hfg_P] with ω h1 h2
    rwa [← lintegral_congr_ae h2]
  calc ∫⁻ y, f y ∂P
      = ∫⁻ y, hf.mk f y ∂P := lintegral_congr_ae hfg
    _ = ∫⁻ y, hf.mk f y ∂(Measure.bind (P.trim h𝒟) (condExpKernel P 𝒟)) := by rw [hbind]
    _ ≤ ∫⁻ ω, (∫⁻ y, hf.mk f y ∂(condExpKernel P 𝒟 ω)) ∂(P.trim h𝒟) :=
        Measure.lintegral_bind_le _ _ (Kernel.aemeasurable _)
    _ = ∫⁻ ω, (∫⁻ y, hf.mk f y ∂(condExpKernel P 𝒟 ω)) ∂P :=
        lintegral_trim h𝒟 (Measurable.lintegral_kernel hgm)
    _ ≤ ∫⁻ _ω, M ∂P := lintegral_mono_ae hcond'
    _ = M := by simp

end CondP

/-! ### Measurability of the statistic -/

section MatMeas

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Entrywise measurability passes through a matrix product. -/
theorem measurable_matmul_apply {m n p : Type*} [Fintype n] {A : Ω → Matrix m n ℝ}
    {B : Ω → Matrix n p ℝ}
    (hA : ∀ i l, Measurable fun y => A y i l) (hB : ∀ l j, Measurable fun y => B y l j) :
    ∀ (i : m) (j : p), Measurable fun y => (A y * B y) i j := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun l _ => (hA i l).mul (hB l j)

/-- ... and through the trace. -/
theorem measurable_trace_of_entries {m : Type*} [Fintype m] {A : Ω → Matrix m m ℝ}
    (hA : ∀ i l, Measurable fun y => A y i l) : Measurable fun y => (A y).trace := by
  simp only [Matrix.trace, Matrix.diag_apply]
  exact Finset.measurable_sum _ fun l _ => hA l l

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)] {ι : Type*}

/-- `n⁻¹(X'Q_[Δ]X)_{jk}` is measurable, for a random design. -/
theorem measurable_gramStat {xi : ∀ n, O n → ι → Ω → ℝ}
    {mu : ∀ n, Ω → Matrix (O n) ι ℝ} {Pm : ∀ n, Ω → Matrix (O n) (O n) ℝ} (j k : ι) (n : ℕ)
    (hxiM : ∀ o a, Measurable (xi n o a))
    (hmuM : ∀ o a, Measurable fun y => mu n y o a)
    (hPmM : ∀ o o', Measurable fun y => Pm n y o o') :
    Measurable (fun y : Ω =>
      (n : ℝ)⁻¹ * ((mu n y + theta (xi n) y)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n y)
          * (mu n y + theta (xi n) y)) j k) := by
  have hQ : ∀ o o', Measurable fun y : Ω => ((1 : Matrix (O n) (O n) ℝ) - Pm n y) o o' := by
    intro o o'
    simp only [Matrix.sub_apply]
    exact measurable_const.sub (hPmM o o')
  have hX : ∀ o a, Measurable fun y : Ω => (mu n y + theta (xi n) y) o a := by
    intro o a
    simp only [Matrix.add_apply, theta, Matrix.of_apply]
    exact (hmuM o a).add (hxiM o a)
  have hXt : ∀ a o, Measurable fun y : Ω => ((mu n y + theta (xi n) y)ᵀ) a o := by
    intro a o
    simpa only [Matrix.transpose_apply] using hX o a
  exact (measurable_matmul_apply (measurable_matmul_apply hXt hQ) hX j k).const_mul _

/-- The centered statistic of the first display is measurable, for a random design. -/
theorem measurable_designStat {xi : ∀ n, O n → ι → Ω → ℝ}
    {mu : ∀ n, Ω → Matrix (O n) ι ℝ} {Pm : ∀ n, Ω → Matrix (O n) (O n) ℝ}
    {Sig : Matrix ι ι ℝ} (j k : ι) (n : ℕ)
    (hxiM : ∀ o a, Measurable (xi n o a))
    (hmuM : ∀ o a, Measurable fun y => mu n y o a)
    (hPmM : ∀ o o', Measurable fun y => Pm n y o o') :
    Measurable (fun y : Ω =>
      (n : ℝ)⁻¹ * ((mu n y + theta (xi n) y)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n y)
          * (mu n y + theta (xi n) y)) j k
        - ((n : ℝ)⁻¹ * ((mu n y)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n y) * mu n y) j k
           + (1 - (Pm n y).trace / n) * Sig j k)) := by
  have hQ : ∀ o o', Measurable fun y : Ω => ((1 : Matrix (O n) (O n) ℝ) - Pm n y) o o' := by
    intro o o'
    simp only [Matrix.sub_apply]
    exact measurable_const.sub (hPmM o o')
  have hMut : ∀ a o, Measurable fun y : Ω => ((mu n y)ᵀ) a o := by
    intro a o
    simpa only [Matrix.transpose_apply] using hmuM o a
  have h1 := measurable_gramStat (mu := mu) (Pm := Pm) j k n hxiM hmuM hPmM
  have h2 := measurable_matmul_apply (measurable_matmul_apply hMut hQ) hmuM j k
  have h3 := measurable_trace_of_entries hPmM
  exact h1.sub ((h2.const_mul _).add ((measurable_const.sub (h3.div_const _)).mul_const _))

end MatMeas

/-! ### Proposition SM.D.1 with a random design

Here `μ`, `P_[Δ]` and `d_[Δ]` are `𝒟`-measurable random matrices, the hypotheses of the
primitive-design assumption hold under `ℙ_ω := condExpKernel P 𝒟 ω` at `P`-almost every `ω`, and
the conclusions hold under `P`.

* `designcond_tendstoInProb_cond`: the first display under `ℙ_ω` at the frozen design.
* `designcond_tendstoInProb_uncond`: the first display under `P`.
* `designcond_design_ii_uncond`: the third claim under `P`.
-/

section UncondMain

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsFiniteMeasure P]

omit [Fintype ι] in
/-- The first display, conditionally on `𝒟`, at almost every realization of the design. -/
theorem designcond_tendstoInProb_cond
    {xi : ∀ n, O n → ι → Ω → ℝ}
    {mu : ∀ n, Ω → Matrix (O n) ι ℝ} {Pm : ∀ n, Ω → Matrix (O n) (O n) ℝ}
    {Sig : Matrix ι ι ℝ} {Cmu Cq : Ω → ℝ} (j k : ι)
    (hSigj : 0 ≤ Sig j j) (hSigk : 0 ≤ Sig k k)
    (hsymm : ∀ᵐ ω ∂P, ∀ n, (Pm n ω)ᵀ = Pm n ω)
    (hidem : ∀ᵐ ω ∂P, ∀ n, Pm n ω * Pm n ω = Pm n ω)
    (hcard : ∀ᶠ n : ℕ in atTop, (Fintype.card (O n) : ℝ) = (n : ℝ))
    (hmubd : ∀ᵐ ω ∂P, ∀ (n : ℕ) (a : ι), ∑ o : O n, (mu n ω o a) ^ 2 ≤ Cmu ω * n)
    (hint2 : ∀ᵐ ω ∂P, ∀ n o o' a b,
      Integrable (fun y => xi n o a y * xi n o' b y) (condExpKernel P 𝒟 ω))
    (hcov : ∀ᵐ ω ∂P, ∀ n o o' a b, ∫ y, xi n o a y * xi n o' b y ∂(condExpKernel P 𝒟 ω)
      = if o = o' then Sig a b else 0)
    (hquadvar : ∀ᵐ ω ∂P, ∀ n : ℕ, ∫ y, (((theta (xi n) y)ᵀ
        * ((1 : Matrix (O n) (O n) ℝ) - Pm n ω) * theta (xi n) y) j k
        - ((1 : Matrix (O n) (O n) ℝ) - Pm n ω).trace * Sig j k) ^ 2
        ∂(condExpKernel P 𝒟 ω) ≤ Cq ω * n)
    (hintsq1 : ∀ᵐ ω ∂P, ∀ n : ℕ, Integrable (fun y => ((n : ℝ)⁻¹
      * ((mu n ω)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n ω) * theta (xi n) y) j k) ^ 2)
      (condExpKernel P 𝒟 ω))
    (hintsq2 : ∀ᵐ ω ∂P, ∀ n : ℕ, Integrable (fun y => ((n : ℝ)⁻¹
      * ((mu n ω)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n ω) * theta (xi n) y) k j) ^ 2)
      (condExpKernel P 𝒟 ω))
    (hintsq3 : ∀ᵐ ω ∂P, ∀ n : ℕ, Integrable (fun y => ((n : ℝ)⁻¹
      * ((((theta (xi n) y)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n ω) * theta (xi n) y) j k)
         - ((1 : Matrix (O n) (O n) ℝ) - Pm n ω).trace * Sig j k)) ^ 2)
      (condExpKernel P 𝒟 ω)) :
    ∀ᵐ ω ∂P, TendstoInMeasure (condExpKernel P 𝒟 ω)
      (fun (n : ℕ) y =>
        (n : ℝ)⁻¹ * ((mu n ω + theta (xi n) y)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n ω)
            * (mu n ω + theta (xi n) y)) j k
          - ((n : ℝ)⁻¹ * ((mu n ω)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n ω) * mu n ω) j k
             + (1 - (Pm n ω).trace / n) * Sig j k))
      atTop (fun _ => (0 : ℝ)) := by
  filter_upwards [hsymm, hidem, hmubd, hint2, hcov, hquadvar, hintsq1, hintsq2, hintsq3]
    with ω hs hi hmb h2 hc hqv hq1 hq2 hq3
  exact designcond_tendstoInProb (P := condExpKernel P 𝒟 ω) (xi := xi)
    (mu := fun n => mu n ω) (Pm := fun n => Pm n ω) (Sig := Sig) (Cmu := Cmu ω) (Cq := Cq ω)
    j k hSigj hSigk hs hi hcard hmb h2 hc hqv hq1 hq2 hq3

/-- **Proposition SM.D.1, first display**, unconditionally, with `μ`, `P_[Δ]` and `d_[Δ]`
random. -/
theorem designcond_tendstoInProb_uncond (h𝒟 : 𝒟 ≤ mΩ)
    {xi : ∀ n, O n → ι → Ω → ℝ}
    {mu : ∀ n, Ω → Matrix (O n) ι ℝ} {Pm : ∀ n, Ω → Matrix (O n) (O n) ℝ}
    {Sig : Matrix ι ι ℝ} (j k : ι)
    (hxiM : ∀ n o a, Measurable (xi n o a))
    (hmuD : ∀ n o a, Measurable[𝒟] fun ω => mu n ω o a)
    (hPmD : ∀ n o o', Measurable[𝒟] fun ω => Pm n ω o o')
    (hcond : ∀ᵐ ω ∂P, TendstoInMeasure (condExpKernel P 𝒟 ω)
      (fun (n : ℕ) y =>
        (n : ℝ)⁻¹ * ((mu n ω + theta (xi n) y)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n ω)
            * (mu n ω + theta (xi n) y)) j k
          - ((n : ℝ)⁻¹ * ((mu n ω)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n ω) * mu n ω) j k
             + (1 - (Pm n ω).trace / n) * Sig j k))
      atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P
      (fun (n : ℕ) y =>
        (n : ℝ)⁻¹ * ((mu n y + theta (xi n) y)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n y)
            * (mu n y + theta (xi n) y)) j k
          - ((n : ℝ)⁻¹ * ((mu n y)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n y) * mu n y) j k
             + (1 - (Pm n y).trace / n) * Sig j k))
      atTop (fun _ => (0 : ℝ)) := by
  have hmuM : ∀ n o a, Measurable fun y => mu n y o a := fun n o a =>
    (hmuD n o a).mono h𝒟 le_rfl
  have hPmM : ∀ n o o', Measurable fun y => Pm n y o o' := fun n o o' =>
    (hPmD n o o').mono h𝒟 le_rfl
  have hsets : ∀ (ε : ℝ≥0∞) (n : ℕ), MeasurableSet {y : Ω | ε ≤ edist
      ((n : ℝ)⁻¹ * ((mu n y + theta (xi n) y)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n y)
            * (mu n y + theta (xi n) y)) j k
          - ((n : ℝ)⁻¹ * ((mu n y)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n y) * mu n y) j k
             + (1 - (Pm n y).trace / n) * Sig j k)) ((fun _ => (0 : ℝ)) y)} := by
    intro ε n
    exact measurableSet_le measurable_const
      ((measurable_designStat (Sig := Sig) j k n (hxiM n) (hmuM n) (hPmM n)).edist
        measurable_const)
  refine CondP.tendstoInMeasure_of_deconditioning h𝒟 P hsets ?_
  filter_upwards [CondP.ae_ae_eq_design h𝒟 P hmuD hPmD, hcond] with ω hfz hcl
  refine CondP.tendstoInMeasure_congr_ae (fun n => ?_) hcl
  filter_upwards [hfz n] with y hy
  rw [hy.1, hy.2]

/-- **Proposition SM.D.1, third claim**, unconditionally: part (ii) of the design assumption
holds with `H = H_μ + (1-κ)Σ_ξ`, entry by entry, with `μ` and `P_[Δ]` random and the
convergences `hHmu`, `hkappa` holding almost surely. -/
theorem designcond_design_ii_uncond (h𝒟 : 𝒟 ≤ mΩ)
    {xi : ∀ n, O n → ι → Ω → ℝ}
    {mu : ∀ n, Ω → Matrix (O n) ι ℝ} {Pm : ∀ n, Ω → Matrix (O n) (O n) ℝ}
    {Sig Hmu : Matrix ι ι ℝ} {κ : ℝ} (j k : ι)
    (hxiM : ∀ n o a, Measurable (xi n o a))
    (hmuD : ∀ n o a, Measurable[𝒟] fun ω => mu n ω o a)
    (hPmD : ∀ n o o', Measurable[𝒟] fun ω => Pm n ω o o')
    (hcond : ∀ᵐ ω ∂P, TendstoInMeasure (condExpKernel P 𝒟 ω)
      (fun (n : ℕ) y =>
        (n : ℝ)⁻¹ * ((mu n ω + theta (xi n) y)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n ω)
            * (mu n ω + theta (xi n) y)) j k
          - ((n : ℝ)⁻¹ * ((mu n ω)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n ω) * mu n ω) j k
             + (1 - (Pm n ω).trace / n) * Sig j k))
      atTop (fun _ => (0 : ℝ)))
    (hHmu : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (n : ℝ)⁻¹
      * ((mu n ω)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n ω) * mu n ω) j k) atTop (𝓝 (Hmu j k)))
    (hkappa : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (Pm n ω).trace / n) atTop (𝓝 κ)) :
    TendstoInMeasure P
      (fun (n : ℕ) y => (n : ℝ)⁻¹ * ((mu n y + theta (xi n) y)ᵀ
        * ((1 : Matrix (O n) (O n) ℝ) - Pm n y) * (mu n y + theta (xi n) y)) j k)
      atTop (fun _ => Hmu j k + (1 - κ) * Sig j k) := by
  have hmuM : ∀ n o a, Measurable fun y => mu n y o a := fun n o a =>
    (hmuD n o a).mono h𝒟 le_rfl
  have hPmM : ∀ n o o', Measurable fun y => Pm n y o o' := fun n o o' =>
    (hPmD n o o').mono h𝒟 le_rfl
  have hsets : ∀ (ε : ℝ≥0∞) (n : ℕ), MeasurableSet {y : Ω | ε ≤ edist
      ((n : ℝ)⁻¹ * ((mu n y + theta (xi n) y)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n y)
        * (mu n y + theta (xi n) y)) j k)
      ((fun _ => Hmu j k + (1 - κ) * Sig j k) y)} := by
    intro ε n
    exact measurableSet_le measurable_const
      ((measurable_gramStat j k n (hxiM n) (hmuM n) (hPmM n)).edist measurable_const)
  refine CondP.tendstoInMeasure_of_deconditioning h𝒟 P hsets ?_
  filter_upwards [CondP.ae_ae_eq_design h𝒟 P hmuD hPmD, hcond, hHmu, hkappa]
    with ω hfz hcl hH hk
  have hfrozen := designcond_design_ii (P := condExpKernel P 𝒟 ω) (xi := xi)
    (mu := fun n => mu n ω) (Pm := fun n => Pm n ω) (Sig := Sig) (Hmu := Hmu) (κ := κ)
    j k hcl hH hk
  refine CondP.tendstoInMeasure_congr_ae (fun n => ?_) hfrozen
  filter_upwards [hfz n] with y hy
  rw [hy.1, hy.2]

end UncondMain

/-! ### Witnesses for the deconditioning

The model is `CLTMartingale.CondD.FrozenWitness`: two fair coins on `Bool × Bool` with
`𝒟 = σ(first coin)`, a proper sub-σ-algebra, so that `ℙ_ω ≠ P`. The design `μ_o` is `1` or
`1 + 1/(n+1)` according to the first coin, so the statistic is random at every `n` while both
halves have the limit `H_μ = 1`. The innovations are degenerate.
-/

section DecondWitnessSection

namespace DecondWitness

open Multiway.CLTMartingale.CondD.FrozenWitness

/-- The design's common entry: `1` on the first coin's `true` half and `1 + 1/(n+1)` on the
other. It is `𝒟`-measurable with the same limit on both halves. -/
noncomputable def dval (n : ℕ) (ω : Bool × Bool) : ℝ :=
  if ω.1 then 1 else 1 + ((n : ℝ) + 1)⁻¹

noncomputable def dmu (n : ℕ) (ω : Bool × Bool) : Matrix (Fin n) (Fin 1) ℝ :=
  Matrix.of fun _ _ => dval n ω

def dxi : ∀ n : ℕ, Fin n → Fin 1 → (Bool × Bool) → ℝ := fun _ _ _ _ => 0

def dPm (n : ℕ) (_ : Bool × Bool) : Matrix (Fin n) (Fin n) ℝ := 0

theorem dval_bounds (n : ℕ) (ω : Bool × Bool) : 0 ≤ dval n ω ∧ dval n ω ≤ 2 := by
  have hnn : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
  have hle : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    right
    linarith [Nat.cast_nonneg (α := ℝ) n]
  unfold dval
  split_ifs with hb
  · constructor <;> norm_num
  · constructor <;> linarith

theorem dval_sq_le_four (n : ℕ) (ω : Bool × Bool) : (dval n ω) ^ 2 ≤ 4 := by
  obtain ⟨h0, h2⟩ := dval_bounds n ω
  nlinarith [h0, h2]

theorem dval_sq_tendsto (ω : Bool × Bool) :
    Tendsto (fun n : ℕ => (dval n ω) ^ 2) atTop (𝓝 1) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    Tendsto.congr (fun n => one_div ((n : ℝ) + 1)) tendsto_one_div_add_atTop_nhds_zero_nat
  have hbase : Tendsto (fun n : ℕ => dval n ω) atTop (𝓝 1) := by
    unfold dval
    split_ifs with hb
    · exact tendsto_const_nhds
    · simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hinv
  simpa using hbase.pow 2

theorem dtheta (n : ℕ) (y : Bool × Bool) : theta (dxi n) y = 0 := by
  ext o a; rfl

theorem dmu_gram (n : ℕ) (ω : Bool × Bool) :
    ((dmu n ω)ᵀ * ((1 : Matrix (Fin n) (Fin n) ℝ) - dPm n ω) * dmu n ω) 0 0
      = (n : ℝ) * (dval n ω) ^ 2 := by
  simp only [dPm, sub_zero, Matrix.mul_one, Matrix.mul_apply]
  have h : ∀ o : Fin n, (dmu n ω)ᵀ 0 o * dmu n ω o 0 = (dval n ω) ^ 2 := by
    intro o
    rw [Matrix.transpose_apply]
    simp [dmu, sq]
  rw [Finset.sum_congr rfl fun o _ => h o]
  simp

theorem dmu_meas (n : ℕ) (o : Fin n) (a : Fin 1) :
    Measurable[Dsig] fun ω : Bool × Bool => dmu n ω o a :=
  (Measurable.of_discrete
    (f := fun b : Bool => if b then (1 : ℝ) else 1 + ((n : ℝ) + 1)⁻¹)).comp meas_fst

/-- The hypotheses of `designcond_tendstoInProb_cond` on this model. -/
theorem decond_witness_cond :
    ∀ᵐ ω ∂Pw, TendstoInMeasure (condExpKernel Pw Dsig ω)
      (fun (n : ℕ) y => (n : ℝ)⁻¹ * ((dmu n ω + theta (dxi n) y)ᵀ
          * ((1 : Matrix (Fin n) (Fin n) ℝ) - dPm n ω) * (dmu n ω + theta (dxi n) y)) 0 0
        - ((n : ℝ)⁻¹ * ((dmu n ω)ᵀ * ((1 : Matrix (Fin n) (Fin n) ℝ) - dPm n ω) * dmu n ω) 0 0
           + (1 - (dPm n ω).trace / n) * (0 : Matrix (Fin 1) (Fin 1) ℝ) 0 0))
      atTop (fun _ => (0 : ℝ)) :=
  designcond_tendstoInProb_cond (P := Pw) (𝒟 := Dsig) (xi := dxi)
    (mu := dmu) (Pm := dPm) (Sig := (0 : Matrix (Fin 1) (Fin 1) ℝ))
    (Cmu := fun _ => 4) (Cq := fun _ => 0) 0 0 le_rfl le_rfl
    (Filter.Eventually.of_forall fun ω n => by simp [dPm])
    (Filter.Eventually.of_forall fun ω n => by simp [dPm])
    (Filter.Eventually.of_forall fun n => by simp)
    (Filter.Eventually.of_forall fun ω n a => by
      have h : ∀ o : Fin n, (dmu n ω o a) ^ 2 = (dval n ω) ^ 2 := fun o => rfl
      rw [Finset.sum_congr rfl fun o _ => h o, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      exact (mul_le_mul_of_nonneg_left (dval_sq_le_four n ω)
        (Nat.cast_nonneg (α := ℝ) n)).trans_eq (mul_comm _ _))
    (Filter.Eventually.of_forall fun ω n o o' a b => by simp [dxi])
    (Filter.Eventually.of_forall fun ω n o o' a b => by simp [dxi])
    (Filter.Eventually.of_forall fun ω n => by simp [dtheta])
    (Filter.Eventually.of_forall fun ω n => by simp [dtheta])
    (Filter.Eventually.of_forall fun ω n => by simp [dtheta])
    (Filter.Eventually.of_forall fun ω n => by simp [dtheta])

/-- Witness for the deconditioned proposition: `𝒟` is a proper sub-σ-algebra; `ℙ_ω ≠ P`; the
statistic at `n = 1` equals `9/4` with probability `1/2`; and both theorems of the random-design
section apply, the second with limit `H = H_μ + (1-κ)Σ_ξ = 1`. -/
theorem decond_witness :
    (∃ B : Set (Bool × Bool), MeasurableSet B ∧ ¬ MeasurableSet[Dsig] B)
    ∧ ¬ (∀ᵐ ω ∂Pw, condExpKernel Pw Dsig ω = Pw)
    ∧ Pw {y : Bool × Bool | ((dmu 1 y + theta (dxi 1) y)ᵀ
        * ((1 : Matrix (Fin 1) (Fin 1) ℝ) - dPm 1 y) * (dmu 1 y + theta (dxi 1) y)) 0 0
        = 9 / 4} = 2⁻¹
    ∧ TendstoInMeasure Pw
        (fun (n : ℕ) y => (n : ℝ)⁻¹ * ((dmu n y + theta (dxi n) y)ᵀ
            * ((1 : Matrix (Fin n) (Fin n) ℝ) - dPm n y) * (dmu n y + theta (dxi n) y)) 0 0
          - ((n : ℝ)⁻¹ * ((dmu n y)ᵀ * ((1 : Matrix (Fin n) (Fin n) ℝ) - dPm n y) * dmu n y) 0 0
             + (1 - (dPm n y).trace / n) * (0 : Matrix (Fin 1) (Fin 1) ℝ) 0 0))
        atTop (fun _ => (0 : ℝ))
    ∧ TendstoInMeasure Pw
        (fun (n : ℕ) y => (n : ℝ)⁻¹ * ((dmu n y + theta (dxi n) y)ᵀ
          * ((1 : Matrix (Fin n) (Fin n) ℝ) - dPm n y) * (dmu n y + theta (dxi n) y)) 0 0)
        atTop (fun _ => (1 : ℝ)) := by
  have hrand : Pw {y : Bool × Bool | ((dmu 1 y + theta (dxi 1) y)ᵀ
      * ((1 : Matrix (Fin 1) (Fin 1) ℝ) - dPm 1 y) * (dmu 1 y + theta (dxi 1) y)) 0 0
      = 9 / 4} = 2⁻¹ := by
    have hset : {y : Bool × Bool | ((dmu 1 y + theta (dxi 1) y)ᵀ
        * ((1 : Matrix (Fin 1) (Fin 1) ℝ) - dPm 1 y) * (dmu 1 y + theta (dxi 1) y)) 0 0
        = 9 / 4} = {y : Bool × Bool | y.1 = false} := by
      ext y
      have h1 : ((dmu 1 y + theta (dxi 1) y)ᵀ
          * ((1 : Matrix (Fin 1) (Fin 1) ℝ) - dPm 1 y) * (dmu 1 y + theta (dxi 1) y)) 0 0
          = ((1 : ℕ) : ℝ) * (dval 1 y) ^ 2 := by
        rw [dtheta, add_zero, dmu_gram]
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, h1]
      cases hb : y.1 <;> norm_num [dval, hb]
    rw [hset, Pw_fst]
  have hHmu : ∀ᵐ ω ∂Pw, Tendsto (fun n : ℕ => (n : ℝ)⁻¹
      * ((dmu n ω)ᵀ * ((1 : Matrix (Fin n) (Fin n) ℝ) - dPm n ω) * dmu n ω) 0 0)
      atTop (𝓝 ((1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0)) := by
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Matrix.one_apply_eq]
    refine Tendsto.congr' ?_ (dval_sq_tendsto ω)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnz : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [dmu_gram]
    field_simp
  refine ⟨Dsig_proper, freeze_witness.2.2.2.2, hrand, ?_, ?_⟩
  · exact designcond_tendstoInProb_uncond (P := Pw) (𝒟 := Dsig) Dsig_le (xi := dxi)
      (mu := dmu) (Pm := dPm) (Sig := (0 : Matrix (Fin 1) (Fin 1) ℝ)) 0 0
      (fun n o a => measurable_const) dmu_meas (fun n o o' => measurable_const)
      decond_witness_cond
  · have hmain := designcond_design_ii_uncond (P := Pw) (𝒟 := Dsig) Dsig_le (xi := dxi)
      (mu := dmu) (Pm := dPm) (Sig := (0 : Matrix (Fin 1) (Fin 1) ℝ))
      (Hmu := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (κ := 0) 0 0
      (fun n o a => measurable_const) dmu_meas (fun n o o' => measurable_const)
      decond_witness_cond hHmu (Filter.Eventually.of_forall fun ω => by simp [dPm])
    simpa [Matrix.one_apply_eq] using hmain

/-- Witness for `tendstoInMeasure_of_design`, with the design the first coin itself. -/
theorem design_bridge_witness :
    TendstoInMeasure Pw (fun (n : ℕ) (y : Bool × Bool) => (dval n y) ^ 2 - 1) atTop
      (fun _ => (0 : ℝ)) := by
  have hmeas : ∀ n : ℕ, Measurable fun y : Bool × Bool => (dval n y) ^ 2 - 1 := by
    intro n
    exact ((Measurable.of_discrete
      (f := fun b : Bool => (if b then (1 : ℝ) else 1 + ((n : ℝ) + 1)⁻¹) ^ 2 - 1)).comp
      measurable_fst)
  refine CondP.tendstoInMeasure_of_design (𝒟 := Dsig) (γ := fun _ => Bool) Dsig_le Pw
    (D := fun _ => Prod.fst)
    (fun n => meas_fst)
    (F := fun n b _ => (if b then (1 : ℝ) else 1 + ((n : ℝ) + 1)⁻¹) ^ 2 - 1)
    (fun n y => rfl) (fun ε n => measurableSet_le measurable_const
      ((hmeas n).edist measurable_const)) ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  have hb : Tendsto (fun n : ℕ => (dval n ω) ^ 2 - 1) atTop (𝓝 0) := by
    simpa using (dval_sq_tendsto ω).sub_const 1
  exact tendstoInProb_of_tendsto (Ω := Bool × Bool) (P := condExpKernel Pw Dsig ω) hb

end DecondWitness

end DecondWitnessSection


/-! ## The moment identities, derived from the primitive-design assumption

The identities `hcov`, `hfour`, `hpair4`, `hmixed4`, `hmixed4'` and `hquad4` are derived from:

* `iIndepFun (xiVec xi) P`: independence across `o` of the innovation vectors in `ℝ^J`;
* `hmean`: `E[ξ_o] = 0`;
* `hSig`: `Var(ξ_o) = Σ_ξ`, the diagonal half of `hcov`;
* `hmom`: `∫ (∑_a ξ²_{oa})² ≤ C`.

`hfour` needs no independence: `ξ²_{oj}ξ²_{o'k} ≤ (‖ξ_o‖⁴ + ‖ξ_{o'}‖⁴)/2`. The others follow from
the three-against-one grouping `integral_mul_triple`. The integrability hypotheses remain. The
consumers `designcond_tendstoInProb_of_primitive`, `quadvar_compl_le_of_primitive` and
`integral_rectFrobSq_xiSharp_le_of_primitive` carry no moment-identity hypothesis.
-/

section FromIndep

variable {O ι : Type*} [Fintype O] [DecidableEq O] [Fintype ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {xi : O → ι → Ω → ℝ} {Sig : Matrix ι ι ℝ} {j k : ι} {C : ℝ}

/-- The innovation of observation `o` as a random element of `ℝ^J`: the row `Θ_{o·}`. -/
def xiVec (xi : O → ι → Ω → ℝ) (o : O) (ω : Ω) : ι → ℝ := fun a => xi o a ω

omit [Fintype O] [DecidableEq O] [Fintype ι] in
theorem measurable_xiVec {xi : O → ι → Ω → ℝ} (hxim : ∀ o a, Measurable (xi o a)) (o : O) :
    Measurable (xiVec xi o) := measurable_pi_iff.2 (hxim o)

/-! ### `hcov`, off the diagonal -/

omit [Fintype O] [Fintype ι] in
theorem integral_cov_of_indep (hxim : ∀ o a, Measurable (xi o a))
    (hindep : iIndepFun (xiVec xi) P) (hmean : ∀ o a, ∫ ω, xi o a ω ∂P = 0)
    (hSig : ∀ o a b, ∫ ω, xi o a ω * xi o b ω ∂P = Sig a b) (o o' : O) (a b : ι) :
    ∫ ω, xi o a ω * xi o' b ω ∂P = if o = o' then Sig a b else 0 := by
  by_cases h : o = o'
  · subst h
    simpa using hSig o a b
  · have hz : ∫ ω, xi o a ω * xi o' b ω ∂P = (∫ ω, xi o a ω ∂P) * ∫ ω, xi o' b ω ∂P :=
      CondIndep.integral_mul_triple (measurable_xiVec hxim) hindep (i := o) (j := o) (k := o)
        (l := o') h h h (G := fun r : (ι → ℝ) × (ι → ℝ) × (ι → ℝ) => r.1 a)
        (H := fun v : ι → ℝ => v b)
        ((measurable_pi_apply a).comp measurable_fst) (measurable_pi_apply b)
    have hif : (if o = o' then Sig a b else (0 : ℝ)) = 0 := by simp [h]
    rw [hif, hz, hmean, zero_mul]

/-! ### `hfour`, from `sup_o E[‖ξ_o‖⁴ ∣ 𝒪] ≤ C` -/

omit [Fintype O] [DecidableEq O] in
theorem integral_four_of_moments
    (hint4 : ∀ r s : O × O, Integrable
      (fun ω => (xi r.1 j ω * xi r.2 k ω) * (xi s.1 j ω * xi s.2 k ω)) P)
    (hintmom : ∀ o : O, Integrable (fun ω => (∑ a : ι, xi o a ω ^ 2) ^ 2) P)
    (hmom : ∀ o : O, ∫ ω, (∑ a : ι, xi o a ω ^ 2) ^ 2 ∂P ≤ C) (o o' : O) :
    ∫ ω, (xi o j ω * xi o' k ω) ^ 2 ∂P ≤ C := by
  have hisq : Integrable (fun ω => (xi o j ω * xi o' k ω) ^ 2) P := by
    refine (hint4 (o, o') (o, o')).congr (Filter.Eventually.of_forall fun ω => ?_)
    ring
  have hbound : ∀ ω, (xi o j ω * xi o' k ω) ^ 2
      ≤ ((∑ a : ι, xi o a ω ^ 2) ^ 2 + (∑ a : ι, xi o' a ω ^ 2) ^ 2) / 2 := by
    intro ω
    have hs : xi o j ω ^ 2 ≤ ∑ a : ι, xi o a ω ^ 2 :=
      Finset.single_le_sum (f := fun a : ι => xi o a ω ^ 2)
        (fun a _ => sq_nonneg _) (Finset.mem_univ j)
    have ht : xi o' k ω ^ 2 ≤ ∑ a : ι, xi o' a ω ^ 2 :=
      Finset.single_le_sum (f := fun a : ι => xi o' a ω ^ 2)
        (fun a _ => sq_nonneg _) (Finset.mem_univ k)
    have hsn : (0 : ℝ) ≤ ∑ a : ι, xi o a ω ^ 2 := le_trans (sq_nonneg _) hs
    have htn : (0 : ℝ) ≤ ∑ a : ι, xi o' a ω ^ 2 := le_trans (sq_nonneg _) ht
    nlinarith [sq_nonneg (xi o j ω), sq_nonneg (xi o' k ω),
      sq_nonneg ((∑ a : ι, xi o a ω ^ 2) - (∑ a : ι, xi o' a ω ^ 2))]
  have hint : Integrable
      (fun ω => ((∑ a : ι, xi o a ω ^ 2) ^ 2 + (∑ a : ι, xi o' a ω ^ 2) ^ 2) / 2) P :=
    ((hintmom o).add (hintmom o')).div_const 2
  have hmono := integral_mono hisq hint (fun ω => hbound ω)
  have heval : ∫ ω, ((∑ a : ι, xi o a ω ^ 2) ^ 2 + (∑ a : ι, xi o' a ω ^ 2) ^ 2) / 2 ∂P
      = ((∫ ω, (∑ a : ι, xi o a ω ^ 2) ^ 2 ∂P)
          + ∫ ω, (∑ a : ι, xi o' a ω ^ 2) ^ 2 ∂P) / 2 := by
    rw [integral_div, integral_add (hintmom o) (hintmom o')]
  rw [heval] at hmono
  linarith [hmom o, hmom o']

/-! ### `hpair4`, `hmixed4`, `hmixed4'` and `hquad4` -/

omit [Fintype O] [Fintype ι] in
theorem integral_pair4_of_indep (hxim : ∀ o a, Measurable (xi o a))
    (hindep : iIndepFun (xiVec xi) P)
    (hSig : ∀ o a b, ∫ ω, xi o a ω * xi o b ω ∂P = Sig a b) (o o' : O) (hne : o ≠ o') :
    ∫ ω, (xi o j ω * xi o k ω) * (xi o' j ω * xi o' k ω) ∂P = Sig j k * Sig j k := by
  have hz : ∫ ω, (xi o j ω * xi o k ω) * (xi o' j ω * xi o' k ω) ∂P
      = (∫ ω, xi o j ω * xi o k ω ∂P) * ∫ ω, xi o' j ω * xi o' k ω ∂P :=
    CondIndep.integral_mul_triple (measurable_xiVec hxim) hindep (i := o) (j := o) (k := o)
      (l := o') hne hne hne
      (G := fun r : (ι → ℝ) × (ι → ℝ) × (ι → ℝ) => r.1 j * r.1 k)
      (H := fun v : ι → ℝ => v j * v k)
      (((measurable_pi_apply j).comp measurable_fst).mul
        ((measurable_pi_apply k).comp measurable_fst))
      ((measurable_pi_apply j).mul (measurable_pi_apply k))
  rw [hz, hSig, hSig]

omit [Fintype O] [Fintype ι] in
theorem integral_mixed4_of_indep (hxim : ∀ o a, Measurable (xi o a))
    (hindep : iIndepFun (xiVec xi) P) (hmean : ∀ o a, ∫ ω, xi o a ω ∂P = 0)
    (a : O) (p : O × O) (hp : p.1 ≠ p.2) :
    ∫ ω, (xi a j ω * xi a k ω) * (xi p.1 j ω * xi p.2 k ω) ∂P = 0 := by
  by_cases ha : a = p.2
  · have hap : a ≠ p.1 := fun h => hp (h.symm.trans ha)
    have h' : ∫ ω, xi a j ω * xi a k ω * xi p.2 k ω * xi p.1 j ω ∂P
        = (∫ ω, xi a j ω * xi a k ω * xi p.2 k ω ∂P) * ∫ ω, xi p.1 j ω ∂P :=
      CondIndep.integral_mul_triple (Z := xiVec xi) (measurable_xiVec hxim) hindep
        (i := a) (j := a) (k := p.2) (l := p.1) hap hap (Ne.symm hp)
        (G := fun r : (ι → ℝ) × (ι → ℝ) × (ι → ℝ) => r.1 j * r.1 k * r.2.2 k)
        (H := fun v : ι → ℝ => v j)
        ((((measurable_pi_apply j).comp measurable_fst).mul
          ((measurable_pi_apply k).comp measurable_fst)).mul
          ((measurable_pi_apply k).comp (measurable_snd.comp measurable_snd)))
        (measurable_pi_apply j)
    have hA : ∫ ω, (xi a j ω * xi a k ω) * (xi p.1 j ω * xi p.2 k ω) ∂P
        = ∫ ω, xi a j ω * xi a k ω * xi p.2 k ω * xi p.1 j ω ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    rw [hA, h', hmean, mul_zero]
  · have h' : ∫ ω, xi a j ω * xi a k ω * xi p.1 j ω * xi p.2 k ω ∂P
        = (∫ ω, xi a j ω * xi a k ω * xi p.1 j ω ∂P) * ∫ ω, xi p.2 k ω ∂P :=
      CondIndep.integral_mul_triple (Z := xiVec xi) (measurable_xiVec hxim) hindep
        (i := a) (j := a) (k := p.1) (l := p.2) ha ha hp
        (G := fun r : (ι → ℝ) × (ι → ℝ) × (ι → ℝ) => r.1 j * r.1 k * r.2.2 j)
        (H := fun v : ι → ℝ => v k)
        ((((measurable_pi_apply j).comp measurable_fst).mul
          ((measurable_pi_apply k).comp measurable_fst)).mul
          ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)))
        (measurable_pi_apply k)
    have hA : ∫ ω, (xi a j ω * xi a k ω) * (xi p.1 j ω * xi p.2 k ω) ∂P
        = ∫ ω, xi a j ω * xi a k ω * xi p.1 j ω * xi p.2 k ω ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    rw [hA, h', hmean, mul_zero]

omit [Fintype O] [Fintype ι] in
theorem integral_mixed4'_of_indep (hxim : ∀ o a, Measurable (xi o a))
    (hindep : iIndepFun (xiVec xi) P) (hmean : ∀ o a, ∫ ω, xi o a ω ∂P = 0)
    (a : O) (p : O × O) (hp : p.1 ≠ p.2) :
    ∫ ω, (xi p.1 j ω * xi p.2 k ω) * (xi a j ω * xi a k ω) ∂P = 0 := by
  rw [← integral_mixed4_of_indep (j := j) (k := k) hxim hindep hmean a p hp]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)

omit [Fintype O] [Fintype ι] in
theorem integral_quad4_of_indep (hxim : ∀ o a, Measurable (xi o a))
    (hindep : iIndepFun (xiVec xi) P) (hmean : ∀ o a, ∫ ω, xi o a ω ∂P = 0)
    (p q : O × O) (_hp : p.1 ≠ p.2) (hq : q.1 ≠ q.2) (hqp : q ≠ p) (hqT : q ≠ (p.2, p.1)) :
    ∫ ω, (xi p.1 j ω * xi p.2 k ω) * (xi q.1 j ω * xi q.2 k ω) ∂P = 0 := by
  have hlone : p.1 ≠ q.1 → p.2 ≠ q.1 →
      ∫ ω, (xi p.1 j ω * xi p.2 k ω) * (xi q.1 j ω * xi q.2 k ω) ∂P = 0 := by
    intro h1 h2
    have h' : ∫ ω, xi p.1 j ω * xi p.2 k ω * xi q.2 k ω * xi q.1 j ω ∂P
        = (∫ ω, xi p.1 j ω * xi p.2 k ω * xi q.2 k ω ∂P) * ∫ ω, xi q.1 j ω ∂P :=
      CondIndep.integral_mul_triple (Z := xiVec xi) (measurable_xiVec hxim) hindep
        (i := p.1) (j := p.2) (k := q.2) (l := q.1) h1 h2 (Ne.symm hq)
        (G := fun r : (ι → ℝ) × (ι → ℝ) × (ι → ℝ) => r.1 j * r.2.1 k * r.2.2 k)
        (H := fun v : ι → ℝ => v j)
        ((((measurable_pi_apply j).comp measurable_fst).mul
          ((measurable_pi_apply k).comp (measurable_fst.comp measurable_snd))).mul
          ((measurable_pi_apply k).comp (measurable_snd.comp measurable_snd)))
        (measurable_pi_apply j)
    have hA : ∫ ω, (xi p.1 j ω * xi p.2 k ω) * (xi q.1 j ω * xi q.2 k ω) ∂P
        = ∫ ω, xi p.1 j ω * xi p.2 k ω * xi q.2 k ω * xi q.1 j ω ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    rw [hA, h', hmean, mul_zero]
  by_cases h1 : q.2 = p.1
  · exact hlone (fun h => hq (h.symm.trans h1.symm))
      (fun h => hqT (Prod.ext_iff.mpr ⟨h.symm, h1⟩))
  by_cases h2 : q.2 = p.2
  · exact hlone (fun h => hqp (Prod.ext_iff.mpr ⟨h.symm, h2⟩))
      (fun h => hq (h.symm.trans h2.symm))
  · have h' : ∫ ω, xi p.1 j ω * xi p.2 k ω * xi q.1 j ω * xi q.2 k ω ∂P
        = (∫ ω, xi p.1 j ω * xi p.2 k ω * xi q.1 j ω ∂P) * ∫ ω, xi q.2 k ω ∂P :=
      CondIndep.integral_mul_triple (Z := xiVec xi) (measurable_xiVec hxim) hindep
        (i := p.1) (j := p.2) (k := q.1) (l := q.2) (Ne.symm h1) (Ne.symm h2) hq
        (G := fun r : (ι → ℝ) × (ι → ℝ) × (ι → ℝ) => r.1 j * r.2.1 k * r.2.2 j)
        (H := fun v : ι → ℝ => v k)
        ((((measurable_pi_apply j).comp measurable_fst).mul
          ((measurable_pi_apply k).comp (measurable_fst.comp measurable_snd))).mul
          ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)))
        (measurable_pi_apply k)
    have hA : ∫ ω, (xi p.1 j ω * xi p.2 k ω) * (xi q.1 j ω * xi q.2 k ω) ∂P
        = ∫ ω, xi p.1 j ω * xi p.2 k ω * xi q.1 j ω * xi q.2 k ω ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    rw [hA, h', hmean, mul_zero]

/-! ### Proposition SM.D.1 and Lemma SM.B.9 from the primitive-design assumption -/

/-- `hquadvar` from the primitive-design assumption. -/
theorem quadvar_compl_le_of_primitive [IsProbabilityMeasure P] {Pm : Matrix O O ℝ} (hC : 0 ≤ C)
    (hs : Pmᵀ = Pm) (hi : Pm * Pm = Pm)
    (hint2 : ∀ o o' a b, Integrable (fun ω => xi o a ω * xi o' b ω) P)
    (hint4 : ∀ r s : O × O, Integrable
      (fun ω => (xi r.1 j ω * xi r.2 k ω) * (xi s.1 j ω * xi s.2 k ω)) P)
    (hintmom : ∀ o : O, Integrable (fun ω => (∑ a : ι, xi o a ω ^ 2) ^ 2) P)
    (hxim : ∀ o a, Measurable (xi o a)) (hindep : iIndepFun (xiVec xi) P)
    (hmean : ∀ o a, ∫ ω, xi o a ω ∂P = 0)
    (hSig : ∀ o a b, ∫ ω, xi o a ω * xi o b ω ∂P = Sig a b)
    (hmom : ∀ o : O, ∫ ω, (∑ a : ι, xi o a ω ^ 2) ^ 2 ∂P ≤ C) :
    ∫ ω, (((theta xi ω)ᵀ * ((1 : Matrix O O ℝ) - Pm) * theta xi ω) j k
        - ((1 : Matrix O O ℝ) - Pm).trace * Sig j k) ^ 2 ∂P
      ≤ 2 * C * (Fintype.card O : ℝ) :=
  quadvar_compl_le hC hs hi hint2 hint4
    (integral_cov_of_indep hxim hindep hmean hSig)
    (integral_four_of_moments hint4 hintmom hmom)
    (integral_pair4_of_indep hxim hindep hSig)
    (integral_mixed4_of_indep hxim hindep hmean)
    (integral_mixed4'_of_indep hxim hindep hmean)
    (integral_quad4_of_indep hxim hindep hmean)

end FromIndep

section FromIndepCgm

variable {O ι D L : Type*} [Fintype O] [DecidableEq O] [Fintype ι] [DecidableEq ι]
variable [DecidableEq D] [Fintype L] [DecidableEq L]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The finite-sample second-moment bound of Lemma SM.B.9, with the moment identities derived
from the primitive-design assumption. -/
theorem integral_rectFrobSq_xiSharp_le_of_primitive [IsProbabilityMeasure P] (c : D → O → L)
    {dims : Finset D} (hdims : dims.Nonempty) {Pm Lam : Matrix O O ℝ}
    (hs : Pmᵀ = Pm) (hi : Pm * Pm = Pm) (hLs : Lamᵀ = Lam) (hLi : Lam * Lam = Lam)
    {xi : O → ι → Ω → ℝ} {Sig : Matrix ι ι ℝ} {C Gmax : ℝ} (hC : 0 ≤ C)
    (hG : ∀ (d : D) (l : L), (Cgm.clusterCard (c d) l : ℝ) ≤ Gmax)
    (hint2 : ∀ o o' a b, Integrable (fun ω => xi o a ω * xi o' b ω) P)
    (hint4 : ∀ (a b : ι) (r s : O × O), Integrable
      (fun ω => (xi r.1 a ω * xi r.2 b ω) * (xi s.1 a ω * xi s.2 b ω)) P)
    (hintmom : ∀ o : O, Integrable (fun ω => (∑ a : ι, xi o a ω ^ 2) ^ 2) P)
    (hxim : ∀ o a, Measurable (xi o a)) (hindep : iIndepFun (xiVec xi) P)
    (hmean : ∀ o a, ∫ ω, xi o a ω ∂P = 0)
    (hSig : ∀ o a b, ∫ ω, xi o a ω * xi o b ω ∂P = Sig a b)
    (hmom : ∀ o : O, ∫ ω, (∑ a : ι, xi o a ω ^ 2) ^ 2 ∂P ≤ C)
    (hsq1 : ∀ a b : ι, Integrable (fun ω => (xiSharpOne c dims Pm xi ω a b) ^ 2) P)
    (hcsq1 : ∀ a b : ι, Integrable (fun ω => (xiSharpOne c dims Pm xi ω a b
      - (coefMat c dims Pm).trace * Sig a b) ^ 2) P)
    (hsq2 : ∀ a b : ι, Integrable (fun ω => (xiSharpTwo c dims Pm Lam xi ω a b) ^ 2) P)
    (hsq : ∀ a b : ι, Integrable (fun ω => (xiSharp c dims Pm Lam xi ω a b) ^ 2) P) :
    ∫ ω, rectFrobSq (xiSharp c dims Pm Lam xi ω) ∂P
      ≤ 4 * (Pm.trace) ^ 2 * rectFrobSq Sig
        + (Fintype.card ι : ℝ) ^ 2 * (8 * C * Pm.trace
            + 2 * (Lam.trace * ((2 * rectFrobSq Sig + 4 * C)
                * ((dims.card : ℝ) * (Gmax * (Fintype.card O : ℝ)))))) :=
  integral_rectFrobSq_xiSharp_le_of_moments c hdims hs hi hLs hLi hC hG hint2 hint4
    (integral_cov_of_indep hxim hindep hmean hSig)
    (fun a b => integral_four_of_moments (j := a) (k := b) (hint4 a b) hintmom hmom)
    (fun a b => integral_pair4_of_indep (j := a) (k := b) hxim hindep hSig)
    (fun a b => integral_mixed4_of_indep (j := a) (k := b) hxim hindep hmean)
    (fun a b => integral_mixed4'_of_indep (j := a) (k := b) hxim hindep hmean)
    (fun a b => integral_quad4_of_indep (j := a) (k := b) hxim hindep hmean)
    hsq1 hcsq1 hsq2 hsq

end FromIndepCgm

section FromIndepSeq

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Proposition SM.D.1, first display**, from the primitive-design assumption. -/
theorem designcond_tendstoInProb_of_primitive [IsProbabilityMeasure P]
    {xi : ∀ n, O n → ι → Ω → ℝ} {mu : ∀ n, Matrix (O n) ι ℝ} {Pm : ∀ n, Matrix (O n) (O n) ℝ}
    {Sig : Matrix ι ι ℝ} {Cmu C : ℝ} (j k : ι) (hSigj : 0 ≤ Sig j j) (hSigk : 0 ≤ Sig k k)
    (hC : 0 ≤ C)
    (hsymm : ∀ n, (Pm n)ᵀ = Pm n) (hidem : ∀ n, Pm n * Pm n = Pm n)
    (hcardn : ∀ n : ℕ, (Fintype.card (O n) : ℝ) = (n : ℝ))
    (hmubd : ∀ (n : ℕ) (a : ι), ∑ o : O n, (mu n o a) ^ 2 ≤ Cmu * n)
    (hint2 : ∀ n o o' a b, Integrable (fun ω => xi n o a ω * xi n o' b ω) P)
    (hint4 : ∀ (n : ℕ) (r s : O n × O n), Integrable
      (fun ω => (xi n r.1 j ω * xi n r.2 k ω) * (xi n s.1 j ω * xi n s.2 k ω)) P)
    (hintmom : ∀ (n : ℕ) (o : O n), Integrable (fun ω => (∑ a : ι, xi n o a ω ^ 2) ^ 2) P)
    (hxim : ∀ n o a, Measurable (xi n o a))
    (hindep : ∀ n, iIndepFun (xiVec (xi n)) P)
    (hmean : ∀ n o a, ∫ ω, xi n o a ω ∂P = 0)
    (hSig : ∀ n o a b, ∫ ω, xi n o a ω * xi n o b ω ∂P = Sig a b)
    (hmom : ∀ (n : ℕ) (o : O n), ∫ ω, (∑ a : ι, xi n o a ω ^ 2) ^ 2 ∂P ≤ C)
    (hintsq1 : ∀ n : ℕ, Integrable (fun ω => ((n : ℝ)⁻¹
      * ((mu n)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n) * theta (xi n) ω) j k) ^ 2) P)
    (hintsq2 : ∀ n : ℕ, Integrable (fun ω => ((n : ℝ)⁻¹
      * ((mu n)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n) * theta (xi n) ω) k j) ^ 2) P)
    (hintsq3 : ∀ n : ℕ, Integrable (fun ω => ((n : ℝ)⁻¹
      * ((((theta (xi n) ω)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n) * theta (xi n) ω) j k)
         - ((1 : Matrix (O n) (O n) ℝ) - Pm n).trace * Sig j k)) ^ 2) P) :
    TendstoInMeasure P
      (fun (n : ℕ) ω =>
        (n : ℝ)⁻¹ * ((mu n + theta (xi n) ω)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n)
            * (mu n + theta (xi n) ω)) j k
          - ((n : ℝ)⁻¹ * ((mu n)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n) * mu n) j k
             + (1 - (Pm n).trace / n) * Sig j k))
      atTop (fun _ => (0 : ℝ)) :=
  designcond_tendstoInProb_of_moments j k hSigj hSigk hC hsymm hidem hcardn hmubd hint2 hint4
    (fun n => integral_cov_of_indep (hxim n) (hindep n) (hmean n) (hSig n))
    (fun n => integral_four_of_moments (hint4 n) (hintmom n) (hmom n))
    (fun n => integral_pair4_of_indep (hxim n) (hindep n) (hSig n))
    (fun n => integral_mixed4_of_indep (hxim n) (hindep n) (hmean n))
    (fun n => integral_mixed4'_of_indep (hxim n) (hindep n) (hmean n))
    (fun n => integral_quad4_of_indep (hxim n) (hindep n) (hmean n))
    hintsq1 hintsq2 hintsq3

end FromIndepSeq

/-! ### Witness for the derived identities

Three observations with independent fair signs, so that `hquad4` is exercised at `p = (0,1)`,
`q = (0,2)`, with `(Σ_ξ)_{00} = 1`.
-/

section FromIndepWitness

open Filter MeasureTheory ProbabilityTheory
open Multiway.GeneralWitness

/-- Truncation to `[-1,1]`, so that every integrability condition holds. -/
def pdClamp (x : ℝ) : ℝ := max (-1) (min 1 x)

theorem measurable_pdClamp : Measurable pdClamp := by
  unfold pdClamp
  fun_prop

theorem pdClamp_one : pdClamp 1 = 1 := by norm_num [pdClamp]

theorem pdClamp_neg_one : pdClamp (-1) = -1 := by norm_num [pdClamp]

theorem abs_pdClamp_le (x : ℝ) : |pdClamp x| ≤ 1 :=
  abs_le.2 ⟨le_max_left _ _, max_le (by norm_num) (min_le_left 1 x)⟩

/-- Three observations, one regressor coordinate, independent fair signs. -/
noncomputable def pdP : Measure (Fin 3 → Fin 1 → ℝ) := Measure.pi fun _ => gmu (Fin 1)

instance : IsProbabilityMeasure pdP := by
  unfold pdP
  infer_instance

/-- The innovations. -/
def pdXi (o : Fin 3) (a : Fin 1) (ω : Fin 3 → Fin 1 → ℝ) : ℝ := pdClamp (ω o a)

/-- `Σ_ξ`, the `1 × 1` identity. -/
def pdSig : Matrix (Fin 1) (Fin 1) ℝ := 1

theorem measurable_pdXi (o : Fin 3) (a : Fin 1) : Measurable (pdXi o a) :=
  measurable_pdClamp.comp ((measurable_pi_apply a).comp (measurable_pi_apply o))

theorem abs_pdXi_le (o : Fin 3) (a : Fin 1) (ω : Fin 3 → Fin 1 → ℝ) : |pdXi o a ω| ≤ 1 :=
  abs_pdClamp_le _

theorem pdIntegrable {f : (Fin 3 → Fin 1 → ℝ) → ℝ} (hf : Measurable f) {B : ℝ}
    (hb : ∀ ω, |f ω| ≤ B) : Integrable f pdP :=
  Integrable.mono' (integrable_const B) hf.aestronglyMeasurable
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hb ω)

/-- The one-coordinate integral: the blocks are independent and each is a fair sign. -/
theorem pdIntegral {f : ℝ → ℝ} (hf : Measurable f) (o : Fin 3) (a : Fin 1) :
    ∫ ω, f (ω o a) ∂pdP = (f 1 + f (-1)) / 2 := by
  have hmp : Measure.map (fun ω : Fin 3 → Fin 1 → ℝ => ω o) pdP = gmu (Fin 1) :=
    (MeasureTheory.measurePreserving_eval (fun _ : Fin 3 => gmu (Fin 1)) o).map_eq
  have hfm : Measurable fun v : Fin 1 → ℝ => f (v a) :=
    hf.comp (measurable_pi_apply a : Measurable fun v : Fin 1 → ℝ => v a)
  have hstep : ∫ ω, f (ω o a) ∂pdP = ∫ v : Fin 1 → ℝ, f (v a) ∂(gmu (Fin 1)) := by
    rw [← hmp, integral_map (measurable_pi_apply o).aemeasurable hfm.aestronglyMeasurable]
  rw [hstep]
  exact gintegral hf a

theorem pdIndep : iIndepFun (xiVec pdXi) pdP := by
  have h0 : iIndepFun (fun (o : Fin 3) (ω : Fin 3 → Fin 1 → ℝ) => ω o) pdP := by
    rw [show pdP = Measure.pi fun _ : Fin 3 => gmu (Fin 1) from rfl]
    exact iIndepFun_pi (μ := fun _ : Fin 3 => gmu (Fin 1))
      (X := fun _ => (id : (Fin 1 → ℝ) → Fin 1 → ℝ)) (fun _ => aemeasurable_id)
  exact h0.comp (fun _ (v : Fin 1 → ℝ) (a : Fin 1) => pdClamp (v a))
    (fun _ => measurable_pi_iff.2 fun a => measurable_pdClamp.comp (measurable_pi_apply a))

theorem pdMean (o : Fin 3) (a : Fin 1) : ∫ ω, pdXi o a ω ∂pdP = 0 := by
  have h := pdIntegral measurable_pdClamp o a
  rw [pdClamp_one, pdClamp_neg_one] at h
  simpa [pdXi] using h

theorem pdSigma (o : Fin 3) (a b : Fin 1) :
    ∫ ω, pdXi o a ω * pdXi o b ω ∂pdP = pdSig a b := by
  have hab : a = b := Subsingleton.elim a b
  subst hab
  have h := pdIntegral (f := fun x => pdClamp x * pdClamp x)
    (measurable_pdClamp.mul measurable_pdClamp) o a
  rw [pdClamp_one, pdClamp_neg_one] at h
  have hone : pdSig a a = 1 := by simp [pdSig, Matrix.one_apply_eq]
  rw [hone]
  simpa [pdXi] using h

theorem pdMom (o : Fin 3) :
    ∫ ω, (∑ a : Fin 1, pdXi o a ω ^ 2) ^ 2 ∂pdP ≤ 1 := by
  have h := pdIntegral (f := fun x => (pdClamp x ^ 2) ^ 2)
    ((measurable_pdClamp.pow_const 2).pow_const 2) o 0
  rw [pdClamp_one, pdClamp_neg_one] at h
  have hrw : ∫ ω, (∑ a : Fin 1, pdXi o a ω ^ 2) ^ 2 ∂pdP
      = ∫ ω, (pdClamp (ω o 0) ^ 2) ^ 2 ∂pdP := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    show (∑ a : Fin 1, pdXi o a ω ^ 2) ^ 2 = (pdClamp (ω o 0) ^ 2) ^ 2
    rw [Fin.sum_univ_one]
    rfl
  rw [hrw, h]
  norm_num

theorem pdIntMom (o : Fin 3) :
    Integrable (fun ω => (∑ a : Fin 1, pdXi o a ω ^ 2) ^ 2) pdP := by
  refine pdIntegrable ?_ (B := 1) (fun ω => ?_)
  · exact (Finset.measurable_sum _ fun a _ => (measurable_pdXi o a).pow_const 2).pow_const 2
  · show |(∑ a : Fin 1, pdXi o a ω ^ 2) ^ 2| ≤ 1
    rw [Fin.sum_univ_one]
    have h := abs_le.1 (abs_pdXi_le o 0 ω)
    have hx2 : pdXi o 0 ω ^ 2 ≤ 1 := by nlinarith [h.1, h.2]
    have hx0 : (0:ℝ) ≤ pdXi o 0 ω ^ 2 := sq_nonneg _
    rw [abs_le]
    constructor <;> nlinarith [hx2, hx0]

theorem pdInt4 (j k : Fin 1) (r s : Fin 3 × Fin 3) :
    Integrable (fun ω => (pdXi r.1 j ω * pdXi r.2 k ω)
      * (pdXi s.1 j ω * pdXi s.2 k ω)) pdP := by
  refine pdIntegrable ?_ (B := 1) (fun ω => ?_)
  · exact (((measurable_pdXi r.1 j).mul (measurable_pdXi r.2 k)).mul
      ((measurable_pdXi s.1 j).mul (measurable_pdXi s.2 k)))
  · simp only [abs_mul]
    have b1 := abs_pdXi_le r.1 j ω
    have b2 := abs_pdXi_le r.2 k ω
    have b3 := abs_pdXi_le s.1 j ω
    have b4 := abs_pdXi_le s.2 k ω
    have h1 : |pdXi r.1 j ω| * |pdXi r.2 k ω| ≤ 1 * 1 :=
      mul_le_mul b1 b2 (abs_nonneg _) zero_le_one
    have h2 : |pdXi s.1 j ω| * |pdXi s.2 k ω| ≤ 1 * 1 :=
      mul_le_mul b3 b4 (abs_nonneg _) zero_le_one
    have h3 := mul_le_mul h1 h2 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (by norm_num : (0:ℝ) ≤ 1 * 1)
    linarith

/-- The witness: the six derived identities on this model, together with two nonzero
values. -/
theorem primitive_identities_witness :
    (∫ ω, pdXi 0 0 ω * pdXi 1 0 ω ∂pdP = if (0 : Fin 3) = 1 then pdSig 0 0 else 0)
    ∧ (∫ ω, pdXi 0 0 ω * pdXi 0 0 ω ∂pdP = if (0 : Fin 3) = 0 then pdSig 0 0 else 0)
    ∧ (∫ ω, (pdXi 0 0 ω * pdXi 0 0 ω) * (pdXi 1 0 ω * pdXi 1 0 ω) ∂pdP
        = pdSig 0 0 * pdSig 0 0)
    ∧ (∫ ω, (pdXi 2 0 ω * pdXi 2 0 ω) * (pdXi 0 0 ω * pdXi 1 0 ω) ∂pdP = 0)
    ∧ (∫ ω, (pdXi 0 0 ω * pdXi 1 0 ω) * (pdXi 0 0 ω * pdXi 2 0 ω) ∂pdP = 0)
    ∧ (∫ ω, (pdXi 0 0 ω * pdXi 1 0 ω) ^ 2 ∂pdP ≤ 1)
    ∧ pdSig 0 0 = 1 := by
  refine ⟨integral_cov_of_indep measurable_pdXi pdIndep pdMean pdSigma 0 1 0 0,
    integral_cov_of_indep measurable_pdXi pdIndep pdMean pdSigma 0 0 0 0,
    integral_pair4_of_indep (j := 0) (k := 0) measurable_pdXi pdIndep pdSigma 0 1
      (by decide),
    integral_mixed4_of_indep (j := 0) (k := 0) measurable_pdXi pdIndep pdMean 2 (0, 1)
      (by decide),
    integral_quad4_of_indep (j := 0) (k := 0) measurable_pdXi pdIndep pdMean (0, 1) (0, 2)
      (by decide) (by decide) (by decide) (by decide),
    integral_four_of_moments (j := 0) (k := 0) (pdInt4 0 0) pdIntMom pdMom 0 1,
    by simp [pdSig, Matrix.one_apply_eq]⟩

end FromIndepWitness

end PrimitiveDesign
end Multiway
