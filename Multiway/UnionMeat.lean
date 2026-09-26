import Multiway.QuadformE2
import Multiway.IdentE2
import Multiway.Sequence
import Mathlib.LinearAlgebra.Matrix.Hadamard

/-!
# The union meat under interaction components

This file formalizes Theorem 8 of the paper (the union meat under interaction components),
all three clauses together with their asymptotic tails, and part (i) of Lemma SM.B.10
(identification after residualization). The covariance structure
`Ω = ∑_e σ_e² Sh_e + diag(σ_ε²(o))` enters as the hypothesis `hOmega`; `hXD` is
`X̃'Δ_m = 0` (Theorem 3(c)) in cell-weight form, `hRD` is `RΔ = 0` (Lemma SM.B.6), `hCS` is the
sharing-support count of Lemma SM.B.8(c), and `hOpNorm` bounds `‖Ω'‖` by `L`.

## Notation

* `xt` is `x̃`, and `xGram xt Ξ` is `X̃'ΞX̃`.
* `sharingMat c dims` is `Sh`, and `sharedGram c dims xt Ξ` is `X̃'(Ξ ∘ Sh)X̃`.
* `shMat c e` and `IdentE2.weightGram c xt e` are `Sh_e` and `∑_{t∈𝒯_e} w_t^{(e)}w_t^{(e)'}`.
* `Om`, `Om1`, `Omp` are `Ω`, `Ω₁`, `Ω' = Ω - Ω₁`; `R` and `P` are `I - Π` and `Π`.
* `residVec R z` is `ν̂_FE = Rζ`.

## Main results

* `unionmeat_a`, `unionmeat_b_identity`, `unionmeat_b_bound`, `unionmeat_c`: Theorem 8(a)–(c).
* `identE2_i`: Lemma SM.B.10(i).
* `tendsto_frobNorm_bias_div_card`, `tendstoInProb_frobNorm_meat_div_card`: the tails of (b), (c).
* `tendstoInProb_nVhatDelta`: `nV̂_[Δ] ⟶^p H^{-1}SH^{-1}`.
-/

namespace Multiway
namespace UnionMeat

open Finset
open Matrix

/-! ## A Frobenius-norm toolkit

Transposition invariance of `frobSq`, contraction by a symmetric idempotent, and the bound
`‖A Sh_e‖_F ≤ c_max ‖A‖_F`. -/

section Frob

variable {O : Type*} [Fintype O]

theorem frobSq_smul (r : ℝ) (A : Matrix O O ℝ) : frobSq (r • A) = r ^ 2 * frobSq A := by
  simp only [frobSq, Matrix.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

/-- `‖AP‖_F² = tr(P A'A)` for a symmetric idempotent `P`. -/
theorem frobSq_mul_proj_eq_trace {P : Matrix O O ℝ} (hs : P.IsSymm) (hi : P * P = P)
    (A : Matrix O O ℝ) : frobSq (A * P) = (P * (Aᵀ * A)).trace := by
  rw [frobSq_eq_trace, Matrix.transpose_mul, hs.eq]
  have h1 : P * Aᵀ * (A * P) = P * (Aᵀ * A) * P := by
    simp only [Matrix.mul_assoc]
  rw [h1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hi]

/-- `‖P‖_F² = tr(P)` for a symmetric idempotent `P`. -/
theorem frobSq_proj_eq_trace {P : Matrix O O ℝ} (hs : P.IsSymm) (hi : P * P = P) :
    frobSq P = P.trace := by
  rw [frobSq_eq_trace, hs.eq, hi]


/-- The bound `‖Ω'‖ ≤ L` in the form `‖AΩ'‖_F ≤ L‖A‖_F`. -/
theorem frobNorm_mul_le_of_opNorm {Omp : Matrix O O ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hOpNorm : ∀ A : Matrix O O ℝ, frobSq (A * Omp) ≤ L ^ 2 * frobSq A) (A : Matrix O O ℝ) :
    frobNorm (A * Omp) ≤ L * frobNorm A := by
  rw [frobNorm, frobNorm]
  refine (Real.sqrt_le_sqrt (hOpNorm A)).trans_eq ?_
  rw [Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL]

variable [DecidableEq O]

/-- A symmetric idempotent `P` splits the Frobenius norm:
`‖AP‖_F² + ‖A(I-P)‖_F² = ‖A‖_F²`. -/
theorem frobSq_mul_proj_add {P : Matrix O O ℝ} (hs : P.IsSymm) (hi : P * P = P)
    (A : Matrix O O ℝ) : frobSq (A * P) + frobSq (A * (1 - P)) = frobSq A := by
  have hs' : (1 - P : Matrix O O ℝ).IsSymm := by
    show (1 - P : Matrix O O ℝ)ᵀ = 1 - P
    rw [Matrix.transpose_sub, Matrix.transpose_one, hs.eq]
  have hi' : (1 - P) * (1 - P) = (1 - P : Matrix O O ℝ) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hi]
    abel
  rw [frobSq_mul_proj_eq_trace hs hi, frobSq_mul_proj_eq_trace hs' hi', frobSq_eq_trace,
    ← Matrix.trace_add, ← Matrix.add_mul,
    show P + (1 - P) = (1 : Matrix O O ℝ) by abel, Matrix.one_mul]

theorem frobSq_mul_proj_le {P : Matrix O O ℝ} (hs : P.IsSymm) (hi : P * P = P)
    (A : Matrix O O ℝ) : frobSq (A * P) ≤ frobSq A := by
  have h := frobSq_mul_proj_add hs hi A
  have h2 := frobSq_nonneg (A * (1 - P))
  linarith

theorem frobSq_proj_mul_le {P : Matrix O O ℝ} (hs : P.IsSymm) (hi : P * P = P)
    (A : Matrix O O ℝ) : frobSq (P * A) ≤ frobSq A := by
  have h : frobSq (P * A) = frobSq (Aᵀ * P) := by
    rw [← frobSq_transpose (P * A), Matrix.transpose_mul, hs.eq]
  rw [h]
  exact (frobSq_mul_proj_le hs hi Aᵀ).trans_eq (frobSq_transpose A)

end Frob

/-! ### `‖Sh_e‖ ≤ c_max`

Each `Sh_e` is block diagonal with all-ones blocks of size at most `c_max`; the bound is proved
in Frobenius-contraction form from the cell structure alone. -/

section ShNorm

variable {O D L : Type*} [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

theorem mul_shMat_apply (c : D → O → L) (e : Finset D) (A : Matrix O O ℝ) (o o' : O) :
    (A * shMat c e) o o' = ∑ k ∈ cellOf c e o', A o k := by
  classical
  rw [Matrix.mul_apply]
  rw [← sum_indicator (cellOf c e o') (fun k => A o k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : SameOn c e k o' <;> simp [shMat, h]

/-- `‖A Sh_e‖_F² ≤ c_max² ‖A‖_F²`. -/
theorem frobSq_mul_shMat_le (c : D → O → L) (e : Finset D) {cmax : ℕ}
    (hc : ∀ o : O, (cellOf c e o).card ≤ cmax) (A : Matrix O O ℝ) :
    frobSq (A * shMat c e) ≤ (cmax : ℝ) ^ 2 * frobSq A := by
  classical
  rw [frobSq, frobSq, Finset.mul_sum]
  refine Finset.sum_le_sum fun o _ => ?_
  have step1 : ∀ o' : O, ((A * shMat c e) o o') ^ 2
      ≤ (cmax : ℝ) * ∑ k ∈ cellOf c e o', (A o k) ^ 2 := by
    intro o'
    rw [mul_shMat_apply c e A o o']
    refine (sq_sum_le_card_mul_sum_sq).trans ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc o')
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have swap : ∑ o' : O, ∑ k ∈ cellOf c e o', (A o k) ^ 2
      = ∑ k : O, ((cellOf c e k).card : ℝ) * (A o k) ^ 2 := by
    have h1 : ∀ o' : O, ∑ k ∈ cellOf c e o', (A o k) ^ 2
        = ∑ k : O, (if k ∈ cellOf c e o' then (A o k) ^ 2 else 0) := fun o' =>
      (sum_indicator (cellOf c e o') (fun k => (A o k) ^ 2)).symm
    rw [Finset.sum_congr rfl fun o' _ => h1 o', Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h2 : ∀ o' : O, (if k ∈ cellOf c e o' then (A o k) ^ 2 else 0)
        = (if o' ∈ cellOf c e k then (A o k) ^ 2 else 0) := by
      intro o'
      by_cases h : SameOn c e k o'
      · have h' : SameOn c e o' k := sameOn_symm h
        simp [h, h']
      · have h' : ¬ SameOn c e o' k := fun hc => h (sameOn_symm hc)
        simp [h, h']
    rw [Finset.sum_congr rfl fun o' _ => h2 o', sum_indicator, Finset.sum_const,
      nsmul_eq_mul]
  calc ∑ o' : O, ((A * shMat c e) o o') ^ 2
      ≤ ∑ o' : O, (cmax : ℝ) * ∑ k ∈ cellOf c e o', (A o k) ^ 2 :=
        Finset.sum_le_sum fun o' _ => step1 o'
    _ = (cmax : ℝ) * ∑ k : O, ((cellOf c e k).card : ℝ) * (A o k) ^ 2 := by
        rw [← Finset.mul_sum, swap]
    _ ≤ (cmax : ℝ) * ∑ k : O, (cmax : ℝ) * (A o k) ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_)
          (Nat.cast_nonneg _)
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc k) (sq_nonneg _)
    _ = (cmax : ℝ) ^ 2 * ∑ k : O, (A o k) ^ 2 := by rw [← Finset.mul_sum]; ring

end ShNorm

/-! ## `X̃'ΞX̃`, the sharing matrix, and the union sum -/

section Gram

variable {O D L K : Type*} [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

/-- `X̃'ΞX̃`. -/
def xGram (xt : O → K → ℝ) (Xi : Matrix O O ℝ) : Matrix K K ℝ :=
  Matrix.of fun a b => ∑ o : O, ∑ o' : O, xt o a * Xi o o' * xt o' b

omit [DecidableEq O] in
@[simp] theorem xGram_apply (xt : O → K → ℝ) (Xi : Matrix O O ℝ) (a b : K) :
    xGram xt Xi a b = ∑ o : O, ∑ o' : O, xt o a * Xi o o' * xt o' b := rfl

omit [DecidableEq O] in
theorem xGram_zero (xt : O → K → ℝ) : xGram xt (0 : Matrix O O ℝ) = 0 := by
  ext a b; simp

omit [DecidableEq O] in
theorem xGram_add (xt : O → K → ℝ) (X Y : Matrix O O ℝ) :
    xGram xt (X + Y) = xGram xt X + xGram xt Y := by
  ext a b
  simp only [xGram_apply, Matrix.add_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => by ring

omit [DecidableEq O] in
theorem xGram_sub (xt : O → K → ℝ) (X Y : Matrix O O ℝ) :
    xGram xt (X - Y) = xGram xt X - xGram xt Y := by
  ext a b
  simp only [xGram_apply, Matrix.sub_apply, Matrix.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => by ring

omit [DecidableEq O] in
theorem xGram_smul (xt : O → K → ℝ) (r : ℝ) (X : Matrix O O ℝ) :
    xGram xt (r • X) = r • xGram xt X := by
  ext a b
  simp only [xGram_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => by ring

omit [DecidableEq O] in
theorem xGram_sum {ι : Type*} (xt : O → K → ℝ) (s : Finset ι) (f : ι → Matrix O O ℝ) :
    xGram xt (∑ i ∈ s, f i) = ∑ i ∈ s, xGram xt (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [xGram_zero]
  · intro i t hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, xGram_add, ih]

/-- `X̃'Sh_eX̃ = ∑_{t∈𝒯_e} w^{(e)}_tw^{(e)'}_t`. -/
theorem xGram_shMat (c : D → O → L) (xt : O → K → ℝ) (e : Finset D) :
    xGram xt (shMat c e) = IdentE2.weightGram c xt e := by
  classical
  ext a b
  rw [xGram_apply, IdentE2.weightGram, Matrix.of_apply,
    ← sum_mul_kernel c e (fun o => xt o a) (fun t => cellWeight (fun o' => xt o' b) t)]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [cellWeight, ← sum_indicator (cellOf c e o) (fun o' => xt o' b), Finset.mul_sum]
  refine Finset.sum_congr rfl fun o' _ => ?_
  by_cases h : SameOn c e o o'
  · have h' : SameOn c e o' o := sameOn_symm h
    simp [shMat, h, h']
  · have h' : ¬ SameOn c e o' o := fun hc => h (sameOn_symm hc)
    simp [shMat, h, h']

theorem xGram_one (xt : O → K → ℝ) : xGram xt (1 : Matrix O O ℝ) = IdentE2.obsGram xt := by
  ext a b
  rw [xGram_apply, IdentE2.obsGram, Matrix.of_apply]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Finset.sum_eq_single o]
  · simp
  · intro o' _ hne; simp [Matrix.one_apply_ne (Ne.symm hne)]
  · intro h; exact absurd (Finset.mem_univ o) h

/-- The sharing matrix `Sh`, `Sh_{oo'} = 𝟙{E(o,o') ≠ ∅}`. -/
def sharingMat (c : D → O → L) (dims : Finset D) : Matrix O O ℝ :=
  Matrix.of fun o o' => if Linked c dims o o' then 1 else 0

omit [Fintype O] [DecidableEq O] [DecidableEq D] in
theorem sharingMat_of_linked {c : D → O → L} {dims : Finset D} {o o' : O}
    (h : Linked c dims o o') : sharingMat c dims o o' = 1 := by
  rw [sharingMat, Matrix.of_apply]
  simp [h]

omit [Fintype O] [DecidableEq O] [DecidableEq D] in
theorem sharingMat_of_not_linked {c : D → O → L} {dims : Finset D} {o o' : O}
    (h : ¬ Linked c dims o o') : sharingMat c dims o o' = 0 := by
  rw [sharingMat, Matrix.of_apply]
  simp [h]

omit [Fintype O] [DecidableEq O] [DecidableEq D] in
/-- `Sh` is an indicator, so its entries are idempotent. -/
theorem sharingMat_sq (c : D → O → L) (dims : Finset D) (o o' : O) :
    sharingMat c dims o o' ^ 2 = sharingMat c dims o o' := by
  by_cases h : Linked c dims o o'
  · rw [sharingMat_of_linked h]; norm_num
  · rw [sharingMat_of_not_linked h]; norm_num

omit [Fintype O] [DecidableEq O] [DecidableEq D] in
/-- `Ξ ∘ Sh = Ξ` whenever `Ξ` is supported on the sharing pairs. -/
theorem hadamard_sharingMat_eq {c : D → O → L} {dims : Finset D} {Xi : Matrix O O ℝ}
    (hsupp : ∀ o o' : O, ¬ Linked c dims o o' → Xi o o' = 0) :
    Matrix.hadamard Xi (sharingMat c dims) = Xi := by
  ext o o'
  rw [Matrix.hadamard_apply]
  by_cases h : Linked c dims o o'
  · rw [sharingMat_of_linked h, mul_one]
  · rw [sharingMat_of_not_linked h, mul_zero, hsupp o o' h]

omit [Fintype O] [DecidableEq O] in
theorem hadamard_sub (X Y S : Matrix O O ℝ) :
    Matrix.hadamard (X - Y) S = Matrix.hadamard X S - Matrix.hadamard Y S := by
  ext o o'; simp [Matrix.hadamard_apply, sub_mul]

omit [Fintype O] [DecidableEq O] in
theorem hadamard_add (X Y S : Matrix O O ℝ) :
    Matrix.hadamard (X + Y) S = Matrix.hadamard X S + Matrix.hadamard Y S := by
  ext o o'; simp [Matrix.hadamard_apply, add_mul]

/-- The union sum `∑_{o ∼ o'} x̃_ox̃_{o'}'Ξ_{oo'} = X̃'(Ξ ∘ Sh)X̃`. -/
def sharedGram (c : D → O → L) (dims : Finset D) (xt : O → K → ℝ) (Xi : Matrix O O ℝ) :
    Matrix K K ℝ := xGram xt (Matrix.hadamard Xi (sharingMat c dims))

omit [DecidableEq O] [DecidableEq D] in
theorem sharedGram_sub (c : D → O → L) (dims : Finset D) (xt : O → K → ℝ)
    (X Y : Matrix O O ℝ) :
    sharedGram c dims xt X - sharedGram c dims xt Y
      = xGram xt (Matrix.hadamard (X - Y) (sharingMat c dims)) := by
  rw [sharedGram, sharedGram, hadamard_sub, xGram_sub]

omit [DecidableEq O] [DecidableEq D] in
theorem sharedGram_add (c : D → O → L) (dims : Finset D) (xt : O → K → ℝ)
    (X Y : Matrix O O ℝ) :
    sharedGram c dims xt (X + Y) = sharedGram c dims xt X + sharedGram c dims xt Y := by
  rw [sharedGram, sharedGram, sharedGram, hadamard_add, xGram_add]

omit [DecidableEq O] [DecidableEq D] in
/-- On a matrix supported on the sharing pairs, the union sum is the full quadratic
form. -/
theorem sharedGram_eq_xGram {c : D → O → L} {dims : Finset D} (xt : O → K → ℝ)
    {Xi : Matrix O O ℝ} (hsupp : ∀ o o' : O, ¬ Linked c dims o o' → Xi o o' = 0) :
    sharedGram c dims xt Xi = xGram xt Xi := by
  rw [sharedGram, hadamard_sharingMat_eq hsupp]

omit [DecidableEq D] in
/-- `X̃'Δ_m = 0` forces `∑_{t∈𝒯_{\{m\}}} w_tw_t' = 0`, hence `X̃'Ω₁X̃ = 0`. -/
theorem weightGram_singleton_eq_zero (c : D → O → L) (xt : O → K → ℝ) {m : D}
    (hXD : ∀ t ∈ cells c ({m} : Finset D), ∀ k : K, cellWeight (fun o => xt o k) t = 0) :
    IdentE2.weightGram c xt ({m} : Finset D) = (0 : Matrix K K ℝ) := by
  ext a b
  rw [IdentE2.weightGram, Matrix.of_apply, Matrix.zero_apply]
  exact Finset.sum_eq_zero fun t ht => by rw [hXD t ht a, zero_mul]

theorem xGram_levelOne_eq_zero (c : D → O → L) (dims : Finset D) (xt : O → K → ℝ)
    (sig1 : D → ℝ)
    (hXD : ∀ m ∈ dims, ∀ t ∈ cells c ({m} : Finset D), ∀ k : K,
      cellWeight (fun o => xt o k) t = 0) :
    xGram xt (∑ m ∈ dims, sig1 m • shMat c ({m} : Finset D)) = 0 := by
  rw [xGram_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [xGram_smul, xGram_shMat, weightGram_singleton_eq_zero c xt (hXD m hm), smul_zero]

end Gram

/-! ## Clause (a): the union meat in the true disturbances is unbiased -/

section ClauseA

variable {O D L K : Type*} [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

/-- **Theorem 8(a).** `𝔼[∑_{o∼o'} x̃_ox̃_{o'}'ν_oν_{o'} ∣ 𝒟] = X̃'ΩX̃ = nS_n`.

`hOmega` is the covariance structure of `Ω`, `hsupp` says `Ω` is supported on the sharing
pairs, `hXD` is `X̃'Δ_m = 0` in cell-weight form, and `hnSn` defines `nS_n`. The matrix `Om`
is `Var(ν ∣ 𝒟)`. -/
theorem unionmeat_a (c : D → O → L) (dims : Finset D) (xt : O → K → ℝ)
    (levels : Finset (Finset D)) (sig1 : D → ℝ) (sige : Finset D → ℝ) (sigeps : O → ℝ)
    {Om Om1 Omp : Matrix O O ℝ} {nSn : Matrix K K ℝ}
    (hOm1 : Om1 = ∑ m ∈ dims, sig1 m • shMat c ({m} : Finset D))
    (hOmp : Omp = Matrix.diagonal sigeps + ∑ e ∈ levels, sige e • shMat c e)
    (hOmega : Om = Om1 + Omp)
    (hsupp : ∀ o o' : O, ¬ Linked c dims o o' → Om o o' = 0)
    (hXD : ∀ m ∈ dims, ∀ t ∈ cells c ({m} : Finset D), ∀ k : K,
      cellWeight (fun o => xt o k) t = 0)
    (hnSn : nSn = xGram xt (Matrix.diagonal sigeps)
      + ∑ e ∈ levels, sige e • IdentE2.weightGram c xt e) :
    sharedGram c dims xt Om = nSn := by
  rw [sharedGram_eq_xGram xt hsupp, hOmega, xGram_add, hOm1,
    xGram_levelOne_eq_zero c dims xt sig1 hXD, zero_add, hOmp, xGram_add, xGram_sum, hnSn]
  congr 1
  exact Finset.sum_congr rfl fun e _ => by rw [xGram_smul, xGram_shMat]

/-- With the level-one blocks removed, the union sum in `Ω'` is still `nS_n`, since
`Ω₁ ∘ Sh = Ω₁` and `X̃'Ω₁X̃ = 0`. -/
theorem sharedGram_omegaPrime (c : D → O → L) (dims : Finset D) (xt : O → K → ℝ)
    (sig1 : D → ℝ) {Om Om1 Omp : Matrix O O ℝ} {nSn : Matrix K K ℝ}
    (hOm1 : Om1 = ∑ m ∈ dims, sig1 m • shMat c ({m} : Finset D))
    (hOmega : Om = Om1 + Omp)
    (hsupp1 : ∀ o o' : O, ¬ Linked c dims o o' → Om1 o o' = 0)
    (hXD : ∀ m ∈ dims, ∀ t ∈ cells c ({m} : Finset D), ∀ k : K,
      cellWeight (fun o => xt o k) t = 0)
    (ha : sharedGram c dims xt Om = nSn) :
    sharedGram c dims xt Omp = nSn := by
  have h1 : sharedGram c dims xt Om1 = 0 := by
    rw [sharedGram_eq_xGram xt hsupp1, hOm1, xGram_levelOne_eq_zero c dims xt sig1 hXD]
  rw [hOmega, sharedGram_add, h1, zero_add] at ha
  exact ha

end ClauseA

/-! ## Lemma SM.B.10(i)

The level-one variances `σ²_1,…,σ²_M` appear neither in the second moments of the fixed-effects
residuals nor, by Theorem 8(a), in `nS_n`. The support hypothesis at the second variance vector
is derived from the first by `levelOne_eq_zero_of_not_linked`. -/

section IdentE2Clause

variable {O D L K : Type*} [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

omit [Fintype O] [DecidableEq O] [DecidableEq D] in
/-- A level-one block `Ω₁ = ∑_m σ²_m Sh_{\{m\}}` vanishes off the sharing pairs, whatever the
variances are. -/
theorem levelOne_eq_zero_of_not_linked (c : D → O → L) (dims : Finset D) (sig1 : D → ℝ)
    {o o' : O} (h : ¬ Linked c dims o o') :
    (∑ m ∈ dims, sig1 m • shMat c ({m} : Finset D)) o o' = 0 := by
  rw [Matrix.sum_apply]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hne : ¬ SameOn c ({m} : Finset D) o o' := fun hs =>
    h ⟨m, hm, hs m (Finset.mem_singleton_self m)⟩
  rw [Matrix.smul_apply, shMat, Matrix.of_apply]
  simp [hne]

omit [Fintype O] [DecidableEq D] in
/-- The two decompositions of `Ω'` agree: under `σ²_ε(o) ≡ σ²_ε` and
`s̄² = σ²_ε + ∑_{e ∈ 𝓔} σ_e²`, one has
`diag(σ²_ε(o)) + ∑_{e ∈ 𝓔} σ_e² Sh_e = s̄²I_n + ∑_{e ∈ 𝓔} σ_e² Sh^off_e`, because
`Sh_e = Sh^off_e + I_n`. -/
theorem omegaPrime_eq_sbar_shOff (c : D → O → L) (Esets : Finset (Finset D))
    (sige : Finset D → ℝ) (sigeps0 sbar : ℝ)
    (hsbar : sbar = sigeps0 + ∑ e ∈ Esets, sige e) :
    (Matrix.diagonal (fun _ : O => sigeps0) + ∑ e ∈ Esets, sige e • shMat c e)
      = sbar • (1 : Matrix O O ℝ) + ∑ e ∈ Esets, sige e • shOff c e := by
  have hdiag : Matrix.diagonal (fun _ : O => sigeps0) = sigeps0 • (1 : Matrix O O ℝ) := by
    ext i j
    rcases eq_or_ne i j with h | h
    · subst h; simp
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.smul_apply, Matrix.one_apply_ne h, smul_zero]
  have hsh : ∀ e : Finset D, shMat c e = shOff c e + (1 : Matrix O O ℝ) := by
    intro e
    rw [shOff]
    abel
  calc (Matrix.diagonal (fun _ : O => sigeps0) + ∑ e ∈ Esets, sige e • shMat c e)
      = sigeps0 • (1 : Matrix O O ℝ)
          + ∑ e ∈ Esets, (sige e • shOff c e + sige e • (1 : Matrix O O ℝ)) := by
        rw [hdiag]
        exact congrArg _ (Finset.sum_congr rfl fun e _ => by rw [hsh e, smul_add])
    _ = sigeps0 • (1 : Matrix O O ℝ)
          + ((∑ e ∈ Esets, sige e • shOff c e) + (∑ e ∈ Esets, sige e) • (1 : Matrix O O ℝ)) := by
        rw [Finset.sum_add_distrib, Finset.sum_smul]
    _ = (sigeps0 + ∑ e ∈ Esets, sige e) • (1 : Matrix O O ℝ)
          + ∑ e ∈ Esets, sige e • shOff c e := by
        rw [add_smul]; abel
    _ = sbar • (1 : Matrix O O ℝ) + ∑ e ∈ Esets, sige e • shOff c e := by rw [hsbar]

/-- **Lemma SM.B.10(i), second half.** Changing the level-one variances leaves
`nS_n = X̃'(Ω ∘ Sh)X̃` unchanged: by `unionmeat_a`, both values equal an expression in which the
level-one variances do not occur. -/
theorem nSn_levelOne_invariant (c : D → O → L) (dims : Finset D) (xt : O → K → ℝ)
    (levels : Finset (Finset D)) (sig1 sig1' : D → ℝ) (sige : Finset D → ℝ) (sigeps : O → ℝ)
    {Om Om' Om1 Om1' Omp : Matrix O O ℝ}
    (hOm1 : Om1 = ∑ m ∈ dims, sig1 m • shMat c ({m} : Finset D))
    (hOm1' : Om1' = ∑ m ∈ dims, sig1' m • shMat c ({m} : Finset D))
    (hOmp : Omp = Matrix.diagonal sigeps + ∑ e ∈ levels, sige e • shMat c e)
    (hOmega : Om = Om1 + Omp) (hOmega' : Om' = Om1' + Omp)
    (hsupp : ∀ o o' : O, ¬ Linked c dims o o' → Om o o' = 0)
    (hXD : ∀ m ∈ dims, ∀ t ∈ cells c ({m} : Finset D), ∀ k : K,
      cellWeight (fun o => xt o k) t = 0) :
    sharedGram c dims xt Om = sharedGram c dims xt Om' := by
  have hsupp' : ∀ o o' : O, ¬ Linked c dims o o' → Om' o o' = 0 := by
    intro o o' h
    have h1 : Om1 o o' = 0 := by
      rw [hOm1]; exact levelOne_eq_zero_of_not_linked c dims sig1 h
    have h1' : Om1' o o' = 0 := by
      rw [hOm1']; exact levelOne_eq_zero_of_not_linked c dims sig1' h
    have hp : Omp o o' = 0 := by
      have := hsupp o o' h
      rw [hOmega, Matrix.add_apply, h1, zero_add] at this
      exact this
    rw [hOmega', Matrix.add_apply, h1', hp, add_zero]
  rw [unionmeat_a c dims xt levels sig1 sige sigeps hOm1 hOmp hOmega hsupp hXD rfl,
    unionmeat_a c dims xt levels sig1' sige sigeps hOm1' hOmp hOmega' hsupp' hXD rfl]

/-- **Lemma SM.B.10(i).** Under one set of hypotheses on `Ω`, changing the level-one
variances leaves both `RΩR` (`IdentE2.levelOne_variances_absent`) and `nS_n`
(`nSn_levelOne_invariant`) unchanged. `hsbar` defines `s̄²` and `sigeps0` imposes
`σ²_ε(o) ≡ σ²_ε`. -/
theorem identE2_i (c : D → O → L) (dims : Finset D) (xt : O → K → ℝ)
    (Esets : Finset (Finset D)) (sig1 sig1' : D → ℝ) (sige : Finset D → ℝ)
    (sigeps0 sbar : ℝ) {R Om Om' Om1 Om1' Omp : Matrix O O ℝ}
    (hsymm : R.IsSymm)
    (hRD : ∀ m ∈ dims, ∀ t ∈ cells c ({m} : Finset D), ∀ o : O, ∑ o' ∈ t, R o o' = 0)
    (hsbar : sbar = sigeps0 + ∑ e ∈ Esets, sige e)
    (hOm1 : Om1 = ∑ m ∈ dims, sig1 m • shMat c ({m} : Finset D))
    (hOm1' : Om1' = ∑ m ∈ dims, sig1' m • shMat c ({m} : Finset D))
    (hOmp : Omp = Matrix.diagonal (fun _ : O => sigeps0) + ∑ e ∈ Esets, sige e • shMat c e)
    (hOmega : Om = Om1 + Omp) (hOmega' : Om' = Om1' + Omp)
    (hsupp : ∀ o o' : O, ¬ Linked c dims o o' → Om o o' = 0)
    (hXD : ∀ m ∈ dims, ∀ t ∈ cells c ({m} : Finset D), ∀ k : K,
      cellWeight (fun o => xt o k) t = 0) :
    R * Om * R = R * Om' * R
      ∧ sharedGram c dims xt Om = sharedGram c dims xt Om' := by
  refine ⟨?_, nSn_levelOne_invariant c dims xt Esets sig1 sig1' sige (fun _ => sigeps0)
    hOm1 hOm1' hOmp hOmega hOmega' hsupp hXD⟩
  have hbridge : Omp = sbar • (1 : Matrix O O ℝ) + ∑ e ∈ Esets, sige e • shOff c e := by
    rw [hOmp]
    exact omegaPrime_eq_sbar_shOff c Esets sige sigeps0 sbar hsbar
  exact IdentE2.levelOne_variances_absent c dims Esets sig1 sig1' sige sbar hsymm hRD
    (by rw [hOmega, hOm1, hbridge]) (by rw [hOmega', hOm1', hbridge])

end IdentE2Clause

/-! ## Clause (b): the bias of the residual union meat and its Frobenius bound -/

section ClauseB

variable {O D L K : Type*} [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

/-- **Theorem 8(b), the identity.**
`𝔼[𝓜̂_[Δ] ∣ 𝒟] - nS_n = X̃'((RΩ'R - Ω') ∘ Sh)X̃`.
`hRD` is `RΔ = 0` in cell form, which gives `RΩ₁R = 0` and hence `RΩR = RΩ'R`. -/
theorem unionmeat_b_identity (c : D → O → L) (dims : Finset D) (xt : O → K → ℝ)
    (sig1 : D → ℝ) {R Om Om1 Omp : Matrix O O ℝ} {nSn : Matrix K K ℝ}
    (hRsymm : R.IsSymm)
    (hOm1 : Om1 = ∑ m ∈ dims, sig1 m • shMat c ({m} : Finset D))
    (hOmega : Om = Om1 + Omp)
    (hRD : ∀ m ∈ dims, ∀ t ∈ cells c ({m} : Finset D), ∀ o : O, ∑ o' ∈ t, R o o' = 0)
    (hnSnp : sharedGram c dims xt Omp = nSn) :
    sharedGram c dims xt (R * Om * R) - nSn
      = xGram xt (Matrix.hadamard (R * Omp * R - Omp) (sharingMat c dims)) := by
  have hzero : R * Om1 * R = 0 := by
    rw [hOm1, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul,
      IdentE2.residual_shMat_eq_zero c _ hRsymm (hRD m hm), smul_zero]
  have hconj : R * Om * R = R * Omp * R := by
    rw [hOmega, Matrix.mul_add, Matrix.add_mul, hzero, zero_add]
  rw [hconj, ← hnSnp, sharedGram_sub]

/-- `‖RΩ'R - Ω'‖_F ≤ 3‖ΠΩ'‖_F` for `R = I - Π`, from
`RΩ'R - Ω' = -ΠΩ' - Ω'Π + ΠΩ'Π`. -/
theorem frobNorm_conj_sub_le {P Omp : Matrix O O ℝ} (hPs : P.IsSymm) (hPi : P * P = P)
    (hOs : Omp.IsSymm) :
    frobNorm ((1 - P) * Omp * (1 - P) - Omp) ≤ 3 * frobNorm (P * Omp) := by
  have hexp : (1 - P) * Omp * (1 - P) - Omp
      = (-(P * Omp) + -(Omp * P)) + P * Omp * P := by
    simp only [sub_mul, mul_sub, one_mul, mul_one]
    abel
  have h1 : frobNorm (Omp * P) = frobNorm (P * Omp) := by
    rw [← frobNorm_transpose (Omp * P), Matrix.transpose_mul, hPs.eq, hOs.eq]
  have h2 : frobNorm (P * Omp * P) ≤ frobNorm (P * Omp) :=
    frobNorm_mono (frobSq_mul_proj_le hPs hPi _)
  have h3 := frobNorm_add_le (-(P * Omp) + -(Omp * P)) (P * Omp * P)
  have h4 := frobNorm_add_le (-(P * Omp)) (-(Omp * P))
  rw [frobNorm_neg, frobNorm_neg, h1] at h4
  rw [hexp]
  linarith

omit [DecidableEq O] in
/-- `‖ΠΩ'‖_F ≤ ‖Π‖_F‖Ω'‖ ≤ √(tr Π)‖Ω'‖`. -/
theorem frobNorm_proj_mul_le {P Omp : Matrix O O ℝ} (hPs : P.IsSymm) (hPi : P * P = P)
    {L : ℝ} (hL : 0 ≤ L)
    (hOpNorm : ∀ A : Matrix O O ℝ, frobSq (A * Omp) ≤ L ^ 2 * frobSq A) :
    frobNorm (P * Omp) ≤ L * Real.sqrt P.trace := by
  refine (frobNorm_mul_le_of_opNorm hL hOpNorm P).trans_eq ?_
  rw [frobNorm, frobSq_proj_eq_trace hPs hPi]

omit [DecidableEq O] [DecidableEq D] in
/-- Cauchy–Schwarz over the sharing support:
`|(bias)_{ab}|² ≤ (∑_{o∼o'} x̃_{oa}²x̃_{o'b}²)‖Ξ‖_F²`. -/
theorem sq_xGram_hadamard_le (c : D → O → L) (dims : Finset D) (xt : O → K → ℝ)
    (Xi : Matrix O O ℝ) (a b : K) :
    (xGram xt (Matrix.hadamard Xi (sharingMat c dims)) a b) ^ 2
      ≤ (∑ o : O, ∑ o' : O, (xt o a * xt o' b) ^ 2 * sharingMat c dims o o')
          * frobSq Xi := by
  classical
  have key := sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (O × O))
    (fun p => xt p.1 a * xt p.2 b * sharingMat c dims p.1 p.2) (fun p => Xi p.1 p.2)
  have hentry : xGram xt (Matrix.hadamard Xi (sharingMat c dims)) a b
      = ∑ p : O × O, (xt p.1 a * xt p.2 b * sharingMat c dims p.1 p.2) * Xi p.1 p.2 := by
    rw [xGram_apply, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => by
      rw [Matrix.hadamard_apply]; ring
  have hfsq : (∑ p : O × O, (xt p.1 a * xt p.2 b * sharingMat c dims p.1 p.2) ^ 2)
      = ∑ o : O, ∑ o' : O, (xt o a * xt o' b) ^ 2 * sharingMat c dims o o' := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => by
      rw [mul_pow, sharingMat_sq]
  have hgsq : (∑ p : O × O, (Xi p.1 p.2) ^ 2) = frobSq Xi := by
    rw [frobSq, Fintype.sum_prod_type]
  rw [hentry, ← hfsq, ← hgsq]
  exact key

omit [DecidableEq D] in
/-- **Theorem 8(b), the bound.** `|(bias)_{ab}| ≤ √Q · 3L√(tr Π)`, with `Q` the
sharing-support count (`hCS`) and `L` a bound on `‖Ω'‖` (`hOpNorm`). -/
theorem unionmeat_b_bound (c : D → O → L) (dims : Finset D) (xt : O → K → ℝ)
    {P Omp : Matrix O O ℝ} (hPs : P.IsSymm) (hPi : P * P = P) (hOs : Omp.IsSymm)
    {Lop Q : ℝ} (hL : 0 ≤ Lop) (hQ : 0 ≤ Q)
    (hOpNorm : ∀ A : Matrix O O ℝ, frobSq (A * Omp) ≤ Lop ^ 2 * frobSq A) (a b : K)
    (hCS : (∑ o : O, ∑ o' : O, (xt o a * xt o' b) ^ 2 * sharingMat c dims o o') ≤ Q) :
    |xGram xt (Matrix.hadamard ((1 - P) * Omp * (1 - P) - Omp) (sharingMat c dims)) a b|
      ≤ Real.sqrt Q * (3 * (Lop * Real.sqrt P.trace)) := by
  set Xi : Matrix O O ℝ := (1 - P) * Omp * (1 - P) - Omp with hXi
  set x : ℝ := xGram xt (Matrix.hadamard Xi (sharingMat c dims)) a b with hx
  have hfrob : frobNorm Xi ≤ 3 * (Lop * Real.sqrt P.trace) := by
    refine (frobNorm_conj_sub_le hPs hPi hOs).trans ?_
    have := frobNorm_proj_mul_le hPs hPi hL hOpNorm
    linarith
  have hsq : x ^ 2 ≤ Q * frobSq Xi := by
    refine (sq_xGram_hadamard_le c dims xt Xi a b).trans ?_
    exact mul_le_mul_of_nonneg_right hCS (frobSq_nonneg Xi)
  have hRHSnn : 0 ≤ Real.sqrt Q * (3 * (Lop * Real.sqrt P.trace)) :=
    mul_nonneg (Real.sqrt_nonneg _)
      (by positivity)
  have hstep : x ^ 2 ≤ (Real.sqrt Q * (3 * (Lop * Real.sqrt P.trace))) ^ 2 := by
    refine hsq.trans ?_
    have h1 : frobSq Xi ≤ (3 * (Lop * Real.sqrt P.trace)) ^ 2 := by
      rw [frobSq_eq_frobNorm_sq]
      nlinarith [frobNorm_nonneg Xi, hfrob]
    calc Q * frobSq Xi ≤ Q * (3 * (Lop * Real.sqrt P.trace)) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 hQ
      _ = (Real.sqrt Q) ^ 2 * (3 * (Lop * Real.sqrt P.trace)) ^ 2 := by
          rw [Real.sq_sqrt hQ]
      _ = (Real.sqrt Q * (3 * (Lop * Real.sqrt P.trace))) ^ 2 := by ring
  have := Real.sqrt_le_sqrt hstep
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hRHSnn] at this

end ClauseB

/-! ## Clause (c): the residual union meat as a quadratic form, and its variance -/

section ClauseC

variable {O : Type*} [Fintype O] [DecidableEq O]

/-- `ν̂_FE = Rζ`. -/
def residVec (R : Matrix O O ℝ) {Ω : Type*} (z : O → Ω → ℝ) : O → Ω → ℝ :=
  fun o ω => ∑ o', R o o' * z o' ω

omit [DecidableEq O] in
theorem quadForm_eq_dotProduct {Ω : Type*} (M : Matrix O O ℝ) (z : O → Ω → ℝ) (ω : Ω) :
    QuadformE2.quadForm M z ω = (fun o => z o ω) ⬝ᵥ (M *ᵥ (fun o => z o ω)) := by
  rw [QuadformE2.quadForm_apply]
  simp only [dotProduct, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun o' _ => by ring

omit [DecidableEq O] in
/-- `ζ'(RCR)ζ = (Rζ)'C(Rζ)` for symmetric `R`. -/
theorem quadForm_conj {Ω : Type*} (R C : Matrix O O ℝ) (hR : R.IsSymm) (z : O → Ω → ℝ)
    (ω : Ω) :
    QuadformE2.quadForm (R * C * R) z ω = QuadformE2.quadForm C (residVec R z) ω := by
  have hv : (fun o => residVec R z o ω) = R *ᵥ (fun o => z o ω) := by
    funext o
    simp [residVec, Matrix.mulVec, dotProduct]
  have hvm : (fun o => z o ω) ᵥ* R = R *ᵥ (fun o => z o ω) := by
    conv_lhs => rw [← hR.eq]
    rw [Matrix.vecMul_transpose]
  rw [quadForm_eq_dotProduct, quadForm_eq_dotProduct, hv, Matrix.mul_assoc,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hvm]

omit [DecidableEq O] in
theorem quadForm_transpose {Ω : Type*} (M : Matrix O O ℝ) (z : O → Ω → ℝ) (ω : Ω) :
    QuadformE2.quadForm Mᵀ z ω = QuadformE2.quadForm M z ω := by
  rw [QuadformE2.quadForm_apply, QuadformE2.quadForm_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => by
    rw [Matrix.transpose_apply]; ring

omit [DecidableEq O] in
theorem quadForm_add {Ω : Type*} (M N : Matrix O O ℝ) (z : O → Ω → ℝ) (ω : Ω) :
    QuadformE2.quadForm (M + N) z ω
      = QuadformE2.quadForm M z ω + QuadformE2.quadForm N z ω := by
  simp only [QuadformE2.quadForm_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => by ring

omit [DecidableEq O] in
theorem quadForm_smul {Ω : Type*} (r : ℝ) (M : Matrix O O ℝ) (z : O → Ω → ℝ) (ω : Ω) :
    QuadformE2.quadForm (r • M) z ω = r * QuadformE2.quadForm M z ω := by
  simp only [QuadformE2.quadForm_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => by ring

omit [DecidableEq O] in
/-- Replacing `C` by its symmetric part leaves the quadratic form unchanged. -/
theorem quadForm_symmetrize {Ω : Type*} (M : Matrix O O ℝ) (z : O → Ω → ℝ) (ω : Ω) :
    QuadformE2.quadForm ((2⁻¹ : ℝ) • (M + Mᵀ)) z ω = QuadformE2.quadForm M z ω := by
  rw [quadForm_smul, quadForm_add, quadForm_transpose]
  ring

omit [Fintype O] [DecidableEq O] in
theorem isSymm_symmetrize (M : Matrix O O ℝ) : ((2⁻¹ : ℝ) • (M + Mᵀ)).IsSymm := by
  show ((2⁻¹ : ℝ) • (M + Mᵀ))ᵀ = (2⁻¹ : ℝ) • (M + Mᵀ)
  rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose]
  rw [add_comm]

omit [DecidableEq O] in
theorem isSymm_conj {R C : Matrix O O ℝ} (hR : R.IsSymm) (hC : C.IsSymm) :
    (R * C * R).IsSymm := by
  show (R * C * R)ᵀ = R * C * R
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hR.eq, hC.eq, ← Matrix.mul_assoc]

omit [DecidableEq O] in
theorem frobSq_symmetrize_le (M : Matrix O O ℝ) :
    frobSq ((2⁻¹ : ℝ) • (M + Mᵀ)) ≤ frobSq M := by
  have h1 : frobNorm (M + Mᵀ) ≤ 2 * frobNorm M := by
    have := frobNorm_add_le M Mᵀ
    rw [frobNorm_transpose] at this
    linarith
  have h2 : frobSq (M + Mᵀ) ≤ 4 * frobSq M := by
    rw [frobSq_eq_frobNorm_sq, frobSq_eq_frobNorm_sq]
    nlinarith [frobNorm_nonneg (M + Mᵀ), frobNorm_nonneg M, h1]
  rw [frobSq_smul]
  nlinarith [frobSq_nonneg M]

/-- `tr(W̃Ω'W̃Ω') ≤ L²‖C_s‖_F²` for `W̃ = RC_sR`: by cyclicity,
`tr(W̃Ω'W̃Ω') = tr(C_sΩ*C_sΩ*)` with `Ω* = RΩ'R`, then `tr(MM) ≤ ‖M‖_F²` and `‖Ω*‖ ≤ ‖Ω'‖ ≤ L`.
No symmetry of `C_s` or `Ω'` is assumed. -/
theorem trace_conj_le {R Omp Cs : Matrix O O ℝ} (hRs : R.IsSymm) (hRi : R * R = R)
    {L : ℝ}
    (hOpNorm : ∀ A : Matrix O O ℝ, frobSq (A * Omp) ≤ L ^ 2 * frobSq A) :
    ((R * Cs * R) * Omp * (R * Cs * R) * Omp).trace ≤ L ^ 2 * frobSq Cs := by
  have hcyc : ((R * Cs * R) * Omp * (R * Cs * R) * Omp).trace
      = ((Cs * (R * Omp * R)) * (Cs * (R * Omp * R))).trace := by
    have h1 : (R * Cs * R) * Omp * (R * Cs * R) * Omp
        = R * (Cs * (R * Omp * R) * Cs * (R * Omp)) := by
      simp only [Matrix.mul_assoc]
    rw [h1, Matrix.trace_mul_comm]
    congr 1
    simp only [Matrix.mul_assoc]
  have hfrob : frobSq (Cs * (R * Omp * R)) ≤ L ^ 2 * frobSq Cs := by
    have hassoc : Cs * (R * Omp * R) = (Cs * R * Omp) * R := by
      simp only [Matrix.mul_assoc]
    rw [hassoc]
    calc frobSq ((Cs * R * Omp) * R) ≤ frobSq (Cs * R * Omp) :=
          frobSq_mul_proj_le hRs hRi _
      _ ≤ L ^ 2 * frobSq (Cs * R) := hOpNorm (Cs * R)
      _ ≤ L ^ 2 * frobSq Cs :=
          mul_le_mul_of_nonneg_left (frobSq_mul_proj_le hRs hRi Cs) (sq_nonneg L)
  rw [hcyc]
  exact (trace_mul_self_le_frobSq _).trans hfrob

/-- **Theorem 8(c), the variance bound.**
`Var(ζ'W̃ζ ∣ 𝒟) ≤ 2‖Ω*‖²‖C‖_F² + C(M)G_max c_max‖C‖_F²` for `W̃ = RC_sR`. The `ζ`-side
hypotheses are those of `QuadformE2.var_quadForm_le`, and `hOpNorm` is `‖Ω'‖ ≤ L`. -/
theorem unionmeat_c {Ω Γ : Type*} (E : (Ω → ℝ) →ₗ[ℝ] ℝ)
    {R Omp Cmat Cs : Matrix O O ℝ}
    (hRs : R.IsSymm) (hRi : R * R = R) (hOs : Omp.IsSymm)
    (z : O → Ω → ℝ) (hOmdef : ∀ o o', Omp o o' = E (z o * z o'))
    (hCs : Cs = (2⁻¹ : ℝ) • (Cmat + Cmatᵀ))
    (s : Finset Γ) (cc : Γ → O → O → O → O → ℝ)
    (hdecomp : ∀ o₁ o₂ o₃ o₄ : O,
      QuadformE2.cum4 E (z o₁) (z o₂) (z o₃) (z o₄) = ∑ g ∈ s, cc g o₁ o₂ o₃ o₄)
    (Adm : Γ → (O × O) → (O × O) → Prop) [∀ g, DecidableRel (Adm g)]
    {Kb Lam Lop : ℝ} (hK : 0 ≤ Kb) (hLam : 0 ≤ Lam)
    (hsupp : ∀ g ∈ s, ∀ p q : O × O, ¬ Adm g p q → cc g p.1 p.2 q.1 q.2 = 0)
    (hbdd : ∀ g ∈ s, ∀ p q : O × O, |cc g p.1 p.2 q.1 q.2| ≤ Kb)
    (hrow : ∀ g ∈ s, ∀ p : O × O,
      ((Finset.univ.filter fun q => Adm g p q).card : ℝ) ≤ Lam)
    (hcol : ∀ g ∈ s, ∀ q : O × O,
      ((Finset.univ.filter fun p => Adm g p q).card : ℝ) ≤ Lam)
    (hOpNorm : ∀ A : Matrix O O ℝ, frobSq (A * Omp) ≤ Lop ^ 2 * frobSq A) :
    QuadformE2.varQuad E (R * Cs * R) z
      ≤ 2 * (Lop ^ 2 * frobSq Cmat) + s.card * Kb * Lam * frobSq Cmat := by
  have hCsSymm : Cs.IsSymm := by rw [hCs]; exact isSymm_symmetrize Cmat
  have hWsymm : (R * Cs * R).IsSymm := isSymm_conj hRs hCsSymm
  have hCsFrob : frobSq Cs ≤ frobSq Cmat := by
    rw [hCs]; exact frobSq_symmetrize_le Cmat
  have hWfrob : frobSq (R * Cs * R) ≤ frobSq Cmat := by
    calc frobSq (R * Cs * R) ≤ frobSq (R * Cs) := frobSq_mul_proj_le hRs hRi _
      _ ≤ frobSq Cs := frobSq_proj_mul_le hRs hRi Cs
      _ ≤ frobSq Cmat := hCsFrob
  have htr : ((R * Cs * R) * Omp * (R * Cs * R) * Omp).trace ≤ Lop ^ 2 * frobSq Cmat :=
    (trace_conj_le hRs hRi hOpNorm).trans
      (mul_le_mul_of_nonneg_left hCsFrob (sq_nonneg Lop))
  have hmain := QuadformE2.var_quadForm_le E hWsymm hOs z hOmdef s cc hdecomp Adm hK
    hsupp hbdd hrow hcol (Λ := Lam)
  have hcoef : (0 : ℝ) ≤ s.card * Kb * Lam :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hK) hLam
  have hsecond : s.card * Kb * Lam * frobSq (R * Cs * R)
      ≤ s.card * Kb * Lam * frobSq Cmat := mul_le_mul_of_nonneg_left hWfrob hcoef
  linarith

end ClauseC

/-! ## The asymptotic tails of (b) and (c)

The designs are indexed by `j` on one probability space. The mean of the quadratic form of
clause (c) is the bias object of clause (b) (`expect_wMat_quadForm`), so the two bounds combine
in one Chebyshev step. The rate hypothesis `hrate` is stated on `tr(Π_n) = d_[Δ]+K` and includes
the factor `(#K)²` that comes from bounding the Frobenius norm by the entries. The abstract
functional `E` of `Multiway.QuadformE2` is related to `∫·dP` by the hypotheses `hEmean` and
`hEsq`. -/

section Tails

open Filter MeasureTheory
open scoped Topology

/-! ### From a uniform entry bound to the Frobenius norm -/

section Entries

variable {K : Type*} [Fintype K]

/-- A uniform bound `t` on the entries gives `‖M‖_F² ≤ (#K · t)²`. -/
theorem frobSq_le_of_entries {M : Matrix K K ℝ} {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ a b, |M a b| ≤ t) : frobSq M ≤ ((Fintype.card K : ℝ) * t) ^ 2 := by
  have hb : ∀ a b : K, M a b ^ 2 ≤ t ^ 2 := by
    intro a b
    nlinarith [h a b, abs_nonneg (M a b), sq_abs (M a b)]
  calc frobSq M = ∑ a : K, ∑ b : K, M a b ^ 2 := rfl
    _ ≤ ∑ _a : K, ∑ _b : K, t ^ 2 :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hb a b
    _ = ((Fintype.card K : ℝ) * t) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- A uniform bound `t` on the entries gives `‖M‖_F ≤ #K · t`. -/
theorem frobNorm_le_of_entries {M : Matrix K K ℝ} {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ a b, |M a b| ≤ t) : frobNorm M ≤ (Fintype.card K : ℝ) * t := by
  rw [frobNorm]
  refine (Real.sqrt_le_sqrt (frobSq_le_of_entries ht h)).trans_eq ?_
  exact Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg _) ht)

end Entries

/-! ### The Frobenius pairing and `C := A_{ab} ∘ Sh` -/

section Pairing

variable {O : Type*} [Fintype O]

/-- `⟨A,B⟩ := ∑_{o,o'}A_{oo'}B_{oo'}`. -/
def dotMat (A B : Matrix O O ℝ) : ℝ := ∑ o : O, ∑ o' : O, A o o' * B o o'

theorem dotMat_eq_trace (A B : Matrix O O ℝ) : dotMat A B = (A * Bᵀ).trace := by
  simp only [dotMat, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]

theorem dotMat_transpose_left (A B : Matrix O O ℝ) : dotMat Aᵀ B = dotMat A Bᵀ := by
  simp only [dotMat, Matrix.transpose_apply]
  exact Finset.sum_comm

theorem dotMat_add_left (A B M : Matrix O O ℝ) :
    dotMat (A + B) M = dotMat A M + dotMat B M := by
  simp only [dotMat, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => by ring

theorem dotMat_smul_left (r : ℝ) (A M : Matrix O O ℝ) :
    dotMat (r • A) M = r * dotMat A M := by
  simp only [dotMat, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => by ring

/-- `⟨C_s,M⟩ = ⟨C,M⟩` for symmetric `M`. -/
theorem dotMat_symmetrize {C M : Matrix O O ℝ} (hM : M.IsSymm) :
    dotMat ((2⁻¹ : ℝ) • (C + Cᵀ)) M = dotMat C M := by
  have h1 : dotMat Cᵀ M = dotMat C M := by rw [dotMat_transpose_left, hM.eq]
  rw [dotMat_smul_left, dotMat_add_left, h1]
  ring

/-- `⟨RC_sR,Ω'⟩ = ⟨C_s,RΩ'R⟩` for symmetric `R` and `Ω'`. -/
theorem dotMat_conj {R Cs Omp : Matrix O O ℝ} (hRs : R.IsSymm) (hOs : Omp.IsSymm) :
    dotMat (R * Cs * R) Omp = dotMat Cs (R * Omp * R) := by
  have h1 : dotMat (R * Cs * R) Omp = (R * (Cs * R * Omp)).trace := by
    rw [dotMat_eq_trace, hOs.eq]
    congr 1
    simp only [Matrix.mul_assoc]
  have h2 : dotMat Cs (R * Omp * R) = (Cs * R * Omp * R).trace := by
    rw [dotMat_eq_trace, (isSymm_conj hRs hOs).eq]
    congr 1
    simp only [Matrix.mul_assoc]
  rw [h1, h2, Matrix.trace_mul_comm]

end Pairing

section CMat

variable {O D L K : Type*} [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

/-- `C := A_{ab} ∘ Sh`, with `(A_{ab})_{oo'} := x̃_{oa}x̃_{o'b}`. -/
def cMat (c : D → O → L) (dims : Finset D) (xt : O → K → ℝ) (a b : K) : Matrix O O ℝ :=
  Matrix.hadamard (Matrix.of fun o o' => xt o a * xt o' b) (sharingMat c dims)

/-- `W̃ := RC_sR`, the weight matrix of clause (c). -/
noncomputable def wMat (c : D → O → L) (dims : Finset D) (xt : O → K → ℝ)
    (R : Matrix O O ℝ) (a b : K) :
    Matrix O O ℝ :=
  R * ((2⁻¹ : ℝ) • (cMat c dims xt a b + (cMat c dims xt a b)ᵀ)) * R

omit [DecidableEq O] [DecidableEq D] in
theorem xGram_hadamard_eq_dotMat (c : D → O → L) (dims : Finset D) (xt : O → K → ℝ)
    (M : Matrix O O ℝ) (a b : K) :
    xGram xt (Matrix.hadamard M (sharingMat c dims)) a b = dotMat (cMat c dims xt a b) M := by
  rw [xGram_apply, dotMat]
  refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => ?_
  simp only [cMat, Matrix.hadamard_apply, Matrix.of_apply]
  ring

omit [DecidableEq O] [DecidableEq D] in
/-- `‖C‖_F²` is the sharing-support count `∑_{o∼o'} x̃_{oa}²x̃_{o'b}²`. -/
theorem frobSq_cMat (c : D → O → L) (dims : Finset D) (xt : O → K → ℝ) (a b : K) :
    frobSq (cMat c dims xt a b)
      = ∑ o : O, ∑ o' : O, (xt o a * xt o' b) ^ 2 * sharingMat c dims o o' := by
  rw [frobSq]
  refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => ?_
  simp only [cMat, Matrix.hadamard_apply, Matrix.of_apply, mul_pow, sharingMat_sq]

omit [Fintype O] [DecidableEq D] [DecidableEq L] in
theorem isSymm_one_sub {Pm : Matrix O O ℝ} (hP : Pm.IsSymm) :
    ((1 : Matrix O O ℝ) - Pm).IsSymm := by
  show ((1 : Matrix O O ℝ) - Pm)ᵀ = 1 - Pm
  rw [Matrix.transpose_sub, Matrix.transpose_one, hP.eq]

omit [DecidableEq O] in
/-- `E[ζ'Wζ] = ⟨W,Ω'⟩`, from `QuadformE2.expect_quadForm` and `hOmdef`. -/
theorem expect_quadForm_eq_dotMat {Ωz : Type*} (E : (Ωz → ℝ) →ₗ[ℝ] ℝ) (W Omp : Matrix O O ℝ)
    (z : O → Ωz → ℝ) (hOmdef : ∀ o o', Omp o o' = E (z o * z o')) :
    E (QuadformE2.quadForm W z) = dotMat W Omp := by
  rw [QuadformE2.expect_quadForm, dotMat]
  exact Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => by rw [hOmdef]

omit [DecidableEq O] [DecidableEq D] in
/-- The mean of the quadratic form of clause (c) is the bias object of clause (b):
`E[ζ'W̃ζ] = X̃'((RΩ'R)∘Sh)X̃` at entry `(a,b)`. -/
theorem expect_wMat_quadForm {Ωz : Type*} (c : D → O → L) (dims : Finset D) (xt : O → K → ℝ)
    (E : (Ωz → ℝ) →ₗ[ℝ] ℝ) {R Omp : Matrix O O ℝ} (hRs : R.IsSymm) (hOs : Omp.IsSymm)
    (z : O → Ωz → ℝ) (hOmdef : ∀ o o', Omp o o' = E (z o * z o')) (a b : K) :
    E (QuadformE2.quadForm (wMat c dims xt R a b) z)
      = xGram xt (Matrix.hadamard (R * Omp * R) (sharingMat c dims)) a b := by
  rw [expect_quadForm_eq_dotMat E _ Omp z hOmdef, wMat, dotMat_conj hRs hOs,
    dotMat_symmetrize (isSymm_conj hRs hOs), xGram_hadamard_eq_dotMat]

end CMat

/-! ### The majorant of clause (b), and that it is null

`biasEntryBound` is the bound of `unionmeat_b_bound` with `Q = Q_c·n`. -/

section Majorant

/-- The entry bound of clause (b): `(Q_cn)^{1/2}·3‖Ω'‖(tr Π)^{1/2}`. -/
noncomputable def biasEntryBound (Lop trP Qc Nv : ℝ) : ℝ :=
  Real.sqrt (Qc * Nv) * (3 * (Lop * Real.sqrt trP))

theorem tendsto_bias_majorant {Kc Lop trP Qc N : ℕ → ℝ}
    (hKc : ∀ j, 0 ≤ Kc j) (hLop : ∀ j, 0 ≤ Lop j) (htrP : ∀ j, 0 ≤ trP j)
    (hQc : ∀ j, 0 ≤ Qc j) (hN : ∀ j, 0 < N j)
    (hrate : Tendsto (fun j => Kc j ^ 2 * (Lop j ^ 2 * trP j) * Qc j / N j) atTop (𝓝 0)) :
    Tendsto (fun j => Kc j * biasEntryBound (Lop j) (trP j) (Qc j) (N j) / N j)
      atTop (𝓝 0) := by
  have hkey : ∀ j, Kc j * biasEntryBound (Lop j) (trP j) (Qc j) (N j) / N j
      = 3 * (Real.sqrt (Kc j ^ 2 * (Lop j ^ 2 * trP j) * (Qc j * N j)) / N j) := by
    intro j
    have h1 : Real.sqrt (Kc j ^ 2 * (Lop j ^ 2 * trP j) * (Qc j * N j))
        = Kc j * Lop j * Real.sqrt (trP j) * Real.sqrt (Qc j * N j) := by
      rw [show Kc j ^ 2 * (Lop j ^ 2 * trP j) * (Qc j * N j)
            = (Kc j * Lop j) ^ 2 * (trP j * (Qc j * N j)) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (mul_nonneg (hKc j) (hLop j)),
        Real.sqrt_mul (htrP j)]
      ring
    rw [biasEntryBound, h1]
    ring
  simp only [hkey]
  have hsq := Sequence.tendsto_sqrt_mul_div
    (a := fun j => Kc j ^ 2 * (Lop j ^ 2 * trP j)) (G := Qc) (N := N)
    (fun j => mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (htrP j))) hQc hN hrate
  simpa using hsq.const_mul 3

end Majorant

/-! ### Chebyshev's inequality -/

section Cheb

variable {Ωp : Type*} [MeasurableSpace Ωp] {P : Measure Ωp}

/-- `Z_n² ⟶^p 0` implies `Z_n ⟶^p 0`: the sets `{ε ≤ |Z|}` and `{ε² ≤ |Z²|}` are equal. -/
theorem tendstoInProb_zero_of_sq {Z : ℕ → Ωp → ℝ}
    (h : TendstoInMeasure P (fun j ω => Z j ω ^ 2) atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P Z atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist] at h ⊢
  intro ε hε
  refine Tendsto.congr (fun j => ?_) (h (ε ^ 2) (by positivity))
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero]
  have h2 : |Z j ω ^ 2| = |Z j ω| ^ 2 := by rw [abs_pow]
  rw [h2]
  constructor
  · intro hx
    by_contra hcon
    have h1 : |Z j ω| < ε := not_le.mp hcon
    nlinarith [abs_nonneg (Z j ω)]
  · intro hx
    nlinarith [abs_nonneg (Z j ω)]

/-- **Chebyshev along the sequence.** A null second moment gives convergence in
probability. -/
theorem tendstoInProb_zero_of_integral_sq_le {Z : ℕ → Ωp → ℝ}
    (hint : ∀ j, Integrable (fun ω => Z j ω ^ 2) P) {m : ℕ → ℝ}
    (hle : ∀ j, ∫ ω, Z j ω ^ 2 ∂P ≤ m j) (hm : Tendsto m atTop (𝓝 0)) :
    TendstoInMeasure P Z atTop (fun _ => (0 : ℝ)) := by
  refine tendstoInProb_zero_of_sq ?_
  refine Sequence.tendstoInProb_zero_of_integral_abs_le hint (fun j => ?_) hm
  have habs : ∀ ω, |Z j ω ^ 2| = Z j ω ^ 2 := fun ω => abs_of_nonneg (sq_nonneg _)
  simp only [habs]
  exact hle j

omit [MeasurableSpace Ωp] in
theorem sq_centered_eq {Q : Ωp → ℝ} {Nv Sv : ℝ} (hN : Nv ≠ 0) :
    (fun ω => (Q ω / Nv - Sv) ^ 2)
      = fun ω => (Nv ^ 2)⁻¹ * (Q ω ^ 2 - 2 * (Nv * Sv) * Q ω + (Nv * Sv) ^ 2) := by
  funext ω
  have h1 : Q ω / Nv - Sv = (Q ω - Nv * Sv) / Nv := by field_simp
  rw [h1, div_pow, div_eq_inv_mul]
  ring

theorem integrable_sq_centered [IsFiniteMeasure P] {Q : Ωp → ℝ} {Nv Sv : ℝ} (hN : Nv ≠ 0)
    (hint : Integrable Q P) (hsq : Integrable (fun ω => Q ω ^ 2) P) :
    Integrable (fun ω => (Q ω / Nv - Sv) ^ 2) P := by
  have hi1 : Integrable (fun ω => Q ω ^ 2 - 2 * (Nv * Sv) * Q ω) P :=
    hsq.sub (hint.const_mul (2 * (Nv * Sv)))
  have hi2 : Integrable (fun _ : Ωp => ((Nv * Sv) ^ 2 : ℝ)) P := integrable_const _
  rw [sq_centered_eq hN]
  exact (hi1.add hi2).const_mul _

/-- The mean-square error of `Q/n` about `S` is bounded by the variance plus the squared bias,
both divided by `n²`. -/
theorem integral_sq_centered_le [IsProbabilityMeasure P] {Q : Ωp → ℝ} {Nv Sv bd vv : ℝ}
    (hN : 0 < Nv) (hint : Integrable Q P) (hsq : Integrable (fun ω => Q ω ^ 2) P)
    (hbias : |(∫ ω, Q ω ∂P) - Nv * Sv| ≤ bd)
    (hvar : (∫ ω, Q ω ^ 2 ∂P) - (∫ ω, Q ω ∂P) ^ 2 ≤ vv) :
    ∫ ω, (Q ω / Nv - Sv) ^ 2 ∂P ≤ (vv + bd ^ 2) / Nv ^ 2 := by
  have hNne : Nv ≠ 0 := hN.ne'
  have hi1 : Integrable (fun ω => Q ω ^ 2 - 2 * (Nv * Sv) * Q ω) P :=
    hsq.sub (hint.const_mul (2 * (Nv * Sv)))
  have hi2 : Integrable (fun _ : Ωp => ((Nv * Sv) ^ 2 : ℝ)) P := integrable_const _
  have hI : ∫ ω, (Q ω / Nv - Sv) ^ 2 ∂P
      = (Nv ^ 2)⁻¹ * ((∫ ω, Q ω ^ 2 ∂P) - 2 * (Nv * Sv) * (∫ ω, Q ω ∂P) + (Nv * Sv) ^ 2) := by
    rw [sq_centered_eq hNne, integral_const_mul]
    congr 1
    have e1 : ∫ ω, (Q ω ^ 2 - 2 * (Nv * Sv) * Q ω + (Nv * Sv) ^ 2) ∂P
        = (∫ ω, (Q ω ^ 2 - 2 * (Nv * Sv) * Q ω) ∂P)
          + ∫ _ω : Ωp, ((Nv * Sv) ^ 2 : ℝ) ∂P := integral_add hi1 hi2
    have e2 : ∫ ω, (Q ω ^ 2 - 2 * (Nv * Sv) * Q ω) ∂P
        = (∫ ω, Q ω ^ 2 ∂P) - ∫ ω, 2 * (Nv * Sv) * Q ω ∂P :=
      integral_sub hsq (hint.const_mul (2 * (Nv * Sv)))
    rw [e1, e2, integral_const_mul, integral_const]
    simp
  have hb2 : ((∫ ω, Q ω ∂P) - Nv * Sv) ^ 2 ≤ bd ^ 2 := by
    have h0 : 0 ≤ bd := le_trans (abs_nonneg _) hbias
    nlinarith [abs_nonneg ((∫ ω, Q ω ∂P) - Nv * Sv), sq_abs ((∫ ω, Q ω ∂P) - Nv * Sv), hbias]
  have hexp : (∫ ω, Q ω ^ 2 ∂P) - 2 * (Nv * Sv) * (∫ ω, Q ω ∂P) + (Nv * Sv) ^ 2
      = ((∫ ω, Q ω ^ 2 ∂P) - (∫ ω, Q ω ∂P) ^ 2) + ((∫ ω, Q ω ∂P) - Nv * Sv) ^ 2 := by ring
  rw [hI, div_eq_inv_mul, hexp]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (sq_nonneg Nv))
  linarith

end Cheb

/-! ### The tails over a sequence of designs

Each hypothesis of the one-design lemmas appears below as `∀ j, <the same hypothesis>`. -/

section Sequences

variable {D O L K : ℕ → Type*}
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Fintype (K j)]
  [∀ j, DecidableEq (D j)] [∀ j, DecidableEq (L j)]

theorem biasEntryBound_nonneg {Lop trP Qc Nv : ℝ} (hLop : 0 ≤ Lop) :
    0 ≤ biasEntryBound Lop trP Qc Nv :=
  mul_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg (by norm_num) (mul_nonneg hLop (Real.sqrt_nonneg _)))

omit [∀ j, DecidableEq (D j)] in
/-- **Theorem 8(b), asymptotic tail.** `n^{-1}‖𝔼[𝓜̂_[Δ] ∣ 𝒟] - nS_n‖_F ⟶ 0`.
The count of `hCS` is split as `Q = Q_c·n`; `hrate` is stated on `tr(Π_n)` with the factor
`(#K)²`. -/
theorem tendsto_frobNorm_bias_div_card
    (c : ∀ j, D j → O j → L j) (dims : ∀ j, Finset (D j)) (xt : ∀ j, O j → K j → ℝ)
    {Pm Omp : ∀ j, Matrix (O j) (O j) ℝ}
    (hPs : ∀ j, (Pm j).IsSymm) (hPi : ∀ j, Pm j * Pm j = Pm j) (hOs : ∀ j, (Omp j).IsSymm)
    {Lop Qc N : ℕ → ℝ}
    (hLop : ∀ j, 0 ≤ Lop j) (hQc : ∀ j, 0 ≤ Qc j) (hN : ∀ j, 0 < N j)
    (hOpNorm : ∀ j, ∀ A : Matrix (O j) (O j) ℝ, frobSq (A * Omp j) ≤ Lop j ^ 2 * frobSq A)
    (hCS : ∀ j, ∀ a b : K j, (∑ o : O j, ∑ o' : O j,
      (xt j o a * xt j o' b) ^ 2 * sharingMat (c j) (dims j) o o') ≤ Qc j * N j)
    (hrate : Tendsto (fun j => (Fintype.card (K j) : ℝ) ^ 2
      * (Lop j ^ 2 * (Pm j).trace) * Qc j / N j) atTop (𝓝 0)) :
    Tendsto (fun j => frobNorm (xGram (xt j) (Matrix.hadamard
        ((1 - Pm j) * Omp j * (1 - Pm j) - Omp j) (sharingMat (c j) (dims j)))) / N j)
      atTop (𝓝 0) := by
  have htr : ∀ j, 0 ≤ (Pm j).trace := by
    intro j
    rw [← frobSq_proj_eq_trace (hPs j) (hPi j)]
    exact frobSq_nonneg _
  refine Sequence.tendsto_zero_of_le
    (fun j => div_nonneg (frobNorm_nonneg _) (hN j).le) (fun j => ?_)
    (tendsto_bias_majorant (Kc := fun j => (Fintype.card (K j) : ℝ))
      (fun j => Nat.cast_nonneg _) hLop htr hQc hN hrate)
  have hent : frobNorm (xGram (xt j) (Matrix.hadamard
      ((1 - Pm j) * Omp j * (1 - Pm j) - Omp j) (sharingMat (c j) (dims j))))
      ≤ (Fintype.card (K j) : ℝ) * biasEntryBound (Lop j) ((Pm j).trace) (Qc j) (N j) := by
    refine frobNorm_le_of_entries (biasEntryBound_nonneg (hLop j)) (fun a b => ?_)
    exact unionmeat_b_bound (c j) (dims j) (xt j) (hPs j) (hPi j) (hOs j) (hLop j)
      (mul_nonneg (hQc j) (hN j).le) (hOpNorm j) a b (hCS j a b)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hent (inv_nonneg.mpr (hN j).le)

omit [∀ j, DecidableEq (D j)] in
/-- **Theorem 8(b), asymptotic tail, random design.** For a random `X̃` satisfying the design
bounds almost everywhere, `n^{-1}‖𝔼[𝓜̂_[Δ] ∣ 𝒟] - nS_n‖_F ⟶^p 0`. The projectors are
nonrandom. -/
theorem tendstoInProb_frobNorm_bias_div_card {Ωp : Type*} [MeasurableSpace Ωp]
    {P : Measure Ωp}
    (c : ∀ j, D j → O j → L j) (dims : ∀ j, Finset (D j)) (xt : ∀ j, Ωp → O j → K j → ℝ)
    {Pm Omp : ∀ j, Matrix (O j) (O j) ℝ}
    (hPs : ∀ j, (Pm j).IsSymm) (hPi : ∀ j, Pm j * Pm j = Pm j) (hOs : ∀ j, (Omp j).IsSymm)
    {Lop Qc N : ℕ → ℝ}
    (hLop : ∀ j, 0 ≤ Lop j) (hQc : ∀ j, 0 ≤ Qc j) (hN : ∀ j, 0 < N j)
    (hOpNorm : ∀ j, ∀ A : Matrix (O j) (O j) ℝ, frobSq (A * Omp j) ≤ Lop j ^ 2 * frobSq A)
    (hCS : ∀ j, ∀ᵐ ω ∂P, ∀ a b : K j, (∑ o : O j, ∑ o' : O j,
      (xt j ω o a * xt j ω o' b) ^ 2 * sharingMat (c j) (dims j) o o') ≤ Qc j * N j)
    (hrate : Tendsto (fun j => (Fintype.card (K j) : ℝ) ^ 2
      * (Lop j ^ 2 * (Pm j).trace) * Qc j / N j) atTop (𝓝 0)) :
    TendstoInMeasure P (fun j ω => frobNorm (xGram (xt j ω) (Matrix.hadamard
        ((1 - Pm j) * Omp j * (1 - Pm j) - Omp j) (sharingMat (c j) (dims j)))) / N j)
      atTop (fun _ => (0 : ℝ)) := by
  have htr : ∀ j, 0 ≤ (Pm j).trace := by
    intro j
    rw [← frobSq_proj_eq_trace (hPs j) (hPi j)]
    exact frobSq_nonneg _
  refine Sequence.tendstoInProb_zero_of_abs_le_const
    (b := fun j => (Fintype.card (K j) : ℝ)
      * biasEntryBound (Lop j) ((Pm j).trace) (Qc j) (N j) / N j) (fun j => ?_)
    (tendsto_bias_majorant (Kc := fun j => (Fintype.card (K j) : ℝ))
      (fun j => Nat.cast_nonneg _) hLop htr hQc hN hrate)
  filter_upwards [hCS j] with ω hcs
  have hent : frobNorm (xGram (xt j ω) (Matrix.hadamard
      ((1 - Pm j) * Omp j * (1 - Pm j) - Omp j) (sharingMat (c j) (dims j))))
      ≤ (Fintype.card (K j) : ℝ) * biasEntryBound (Lop j) ((Pm j).trace) (Qc j) (N j) := by
    refine frobNorm_le_of_entries (biasEntryBound_nonneg (hLop j)) (fun a b => ?_)
    exact unionmeat_b_bound (c j) (dims j) (xt j ω) (hPs j) (hPi j) (hOs j) (hLop j)
      (mul_nonneg (hQc j) (hN j).le) (hOpNorm j) a b (hcs a b)
  rw [abs_of_nonneg (div_nonneg (frobNorm_nonneg _) (hN j).le), div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hent (inv_nonneg.mpr (hN j).le)

omit [∀ j, DecidableEq (D j)] in
/-- **Theorem 8(c), first asymptotic tail.** `n^{-1}𝓜̂_[Δ] - S_n ⟶^p 0`.

The bias is controlled by `unionmeat_b_bound` through `expect_wMat_quadForm`, and the
fluctuation by the variance bound `hvar` of `unionmeat_c`; Chebyshev's inequality concludes.
`hOmdef` defines `Ω'` as the second-moment matrix of `ζ`, `hnSn` is `X̃'(Ω'∘Sh)X̃ = nS_n`
entrywise, `hEmean` and `hEsq` relate `E` to `∫·dP`, and `hratebias`, `hratevar` are the rate
conditions `c_max²d_[Δ]G_max = o(n)` and `(c_max+G_max)c_maxG_max = o(n)`. -/
theorem tendstoInProb_frobNorm_meat_div_card {Ωp : Type*} [MeasurableSpace Ωp]
    {P : Measure Ωp} [IsProbabilityMeasure P]
    (c : ∀ j, D j → O j → L j) (dims : ∀ j, Finset (D j)) (xt : ∀ j, O j → K j → ℝ)
    (E : ℕ → ((Ωp → ℝ) →ₗ[ℝ] ℝ)) (z : ∀ j, O j → Ωp → ℝ)
    {Pm Omp : ∀ j, Matrix (O j) (O j) ℝ} {Sn : ∀ j, Matrix (K j) (K j) ℝ}
    (hPs : ∀ j, (Pm j).IsSymm) (hPi : ∀ j, Pm j * Pm j = Pm j) (hOs : ∀ j, (Omp j).IsSymm)
    (hOmdef : ∀ j, ∀ o o' : O j, Omp j o o' = E j (z j o * z j o'))
    {Lop Qc N v : ℕ → ℝ}
    (hLop : ∀ j, 0 ≤ Lop j) (hQc : ∀ j, 0 ≤ Qc j) (hN : ∀ j, 0 < N j)
    (hOpNorm : ∀ j, ∀ A : Matrix (O j) (O j) ℝ, frobSq (A * Omp j) ≤ Lop j ^ 2 * frobSq A)
    (hCS : ∀ j, ∀ a b : K j, (∑ o : O j, ∑ o' : O j,
      (xt j o a * xt j o' b) ^ 2 * sharingMat (c j) (dims j) o o') ≤ Qc j * N j)
    (hnSn : ∀ j, ∀ a b : K j,
      xGram (xt j) (Matrix.hadamard (Omp j) (sharingMat (c j) (dims j))) a b
        = N j * Sn j a b)
    (hint : ∀ j, ∀ a b : K j,
      Integrable (QuadformE2.quadForm (wMat (c j) (dims j) (xt j) (1 - Pm j) a b) (z j)) P)
    (hintsq : ∀ j, ∀ a b : K j, Integrable (fun ω =>
      QuadformE2.quadForm (wMat (c j) (dims j) (xt j) (1 - Pm j) a b) (z j) ω ^ 2) P)
    (hEmean : ∀ j, ∀ a b : K j,
      E j (QuadformE2.quadForm (wMat (c j) (dims j) (xt j) (1 - Pm j) a b) (z j))
        = ∫ ω, QuadformE2.quadForm (wMat (c j) (dims j) (xt j) (1 - Pm j) a b) (z j) ω ∂P)
    (hEsq : ∀ j, ∀ a b : K j,
      E j (QuadformE2.quadForm (wMat (c j) (dims j) (xt j) (1 - Pm j) a b) (z j) ^ 2)
        = ∫ ω, QuadformE2.quadForm (wMat (c j) (dims j) (xt j) (1 - Pm j) a b) (z j) ω ^ 2 ∂P)
    (hvar : ∀ j, ∀ a b : K j, QuadformE2.varQuad (E j)
      (wMat (c j) (dims j) (xt j) (1 - Pm j) a b) (z j) ≤ v j)
    (hratebias : Tendsto (fun j => (Fintype.card (K j) : ℝ) ^ 2
      * (Lop j ^ 2 * (Pm j).trace) * Qc j / N j) atTop (𝓝 0))
    (hratevar : Tendsto (fun j => (Fintype.card (K j) : ℝ) ^ 2 * (v j / N j ^ 2))
      atTop (𝓝 0)) :
    TendstoInMeasure P (fun j ω => frobNorm ((N j)⁻¹ •
        (Matrix.of fun a b => QuadformE2.quadForm
          (wMat (c j) (dims j) (xt j) (1 - Pm j) a b) (z j) ω) - Sn j))
      atTop (fun _ => (0 : ℝ)) := by
  have htr : ∀ j, 0 ≤ (Pm j).trace := by
    intro j
    rw [← frobSq_proj_eq_trace (hPs j) (hPi j)]
    exact frobSq_nonneg _
  set bd : ℕ → ℝ := fun j => biasEntryBound (Lop j) ((Pm j).trace) (Qc j) (N j) with hbd
  -- the per-entry mean-square error
  have hQint : ∀ j, ∀ a b : K j,
      ∫ ω, (QuadformE2.quadForm (wMat (c j) (dims j) (xt j) (1 - Pm j) a b) (z j) ω / N j
        - Sn j a b) ^ 2 ∂P ≤ (v j + bd j ^ 2) / N j ^ 2 := by
    intro j a b
    refine integral_sq_centered_le (hN j) (hint j a b) (hintsq j a b) ?_ ?_
    · rw [← hEmean j a b, expect_wMat_quadForm (c j) (dims j) (xt j) (E j)
        (isSymm_one_sub (hPs j)) (hOs j) (z j) (hOmdef j) a b, ← hnSn j a b]
      have hdiff : xGram (xt j) (Matrix.hadamard ((1 - Pm j) * Omp j * (1 - Pm j))
              (sharingMat (c j) (dims j))) a b
            - xGram (xt j) (Matrix.hadamard (Omp j) (sharingMat (c j) (dims j))) a b
          = xGram (xt j) (Matrix.hadamard ((1 - Pm j) * Omp j * (1 - Pm j) - Omp j)
              (sharingMat (c j) (dims j))) a b := by
        rw [hadamard_sub, xGram_sub]
        rfl
      rw [hdiff, hbd]
      exact unionmeat_b_bound (c j) (dims j) (xt j) (hPs j) (hPi j) (hOs j) (hLop j)
        (mul_nonneg (hQc j) (hN j).le) (hOpNorm j) a b (hCS j a b)
    · have hv := hvar j a b
      simp only [QuadformE2.varQuad] at hv
      rw [hEmean j a b, hEsq j a b] at hv
      exact hv
  -- `‖·‖_F²` is the sum of the squared entries
  have hfrobsq : ∀ (j : ℕ) (ω : Ωp), frobNorm ((N j)⁻¹ •
      (Matrix.of fun a b => QuadformE2.quadForm
        (wMat (c j) (dims j) (xt j) (1 - Pm j) a b) (z j) ω) - Sn j) ^ 2
      = ∑ a : K j, ∑ b : K j,
          (QuadformE2.quadForm (wMat (c j) (dims j) (xt j) (1 - Pm j) a b) (z j) ω / N j
            - Sn j a b) ^ 2 := by
    intro j ω
    rw [← frobSq_eq_frobNorm_sq, frobSq]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    congr 1
    simp [div_eq_inv_mul]
  have hg : ∀ (j : ℕ) (a b : K j), Integrable (fun ω =>
      (QuadformE2.quadForm (wMat (c j) (dims j) (xt j) (1 - Pm j) a b) (z j) ω / N j
        - Sn j a b) ^ 2) P :=
    fun j a b => integrable_sq_centered (hN j).ne' (hint j a b) (hintsq j a b)
  have hint2 : ∀ j, Integrable (fun ω => frobNorm ((N j)⁻¹ •
      (Matrix.of fun a b => QuadformE2.quadForm
        (wMat (c j) (dims j) (xt j) (1 - Pm j) a b) (z j) ω) - Sn j) ^ 2) P := by
    intro j
    rw [funext (hfrobsq j)]
    exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hg j a b
  have hbound : ∀ j, ∫ ω, frobNorm ((N j)⁻¹ •
      (Matrix.of fun a b => QuadformE2.quadForm
        (wMat (c j) (dims j) (xt j) (1 - Pm j) a b) (z j) ω) - Sn j) ^ 2 ∂P
      ≤ (Fintype.card (K j) : ℝ) ^ 2 * ((v j + bd j ^ 2) / N j ^ 2) := by
    intro j
    rw [funext (hfrobsq j),
      integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => hg j a b)]
    have hin : ∀ a : K j, (∫ ω, ∑ b : K j,
        (QuadformE2.quadForm (wMat (c j) (dims j) (xt j) (1 - Pm j) a b) (z j) ω / N j
          - Sn j a b) ^ 2 ∂P) ≤ ∑ _b : K j, (v j + bd j ^ 2) / N j ^ 2 := by
      intro a
      rw [integral_finsetSum _ (fun b _ => hg j a b)]
      exact Finset.sum_le_sum fun b _ => hQint j a b
    calc ∑ a : K j, ∫ ω, ∑ b : K j,
          (QuadformE2.quadForm (wMat (c j) (dims j) (xt j) (1 - Pm j) a b) (z j) ω / N j
            - Sn j a b) ^ 2 ∂P
        ≤ ∑ _a : K j, ∑ _b : K j, (v j + bd j ^ 2) / N j ^ 2 :=
          Finset.sum_le_sum fun a _ => hin a
      _ = (Fintype.card (K j) : ℝ) ^ 2 * ((v j + bd j ^ 2) / N j ^ 2) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  refine tendstoInProb_zero_of_integral_sq_le hint2 hbound ?_
  have hexp : ∀ j, (Fintype.card (K j) : ℝ) ^ 2 * ((v j + bd j ^ 2) / N j ^ 2)
      = (Fintype.card (K j) : ℝ) ^ 2 * (v j / N j ^ 2)
        + 9 * ((Fintype.card (K j) : ℝ) ^ 2
          * (Lop j ^ 2 * (Pm j).trace) * Qc j / N j) := by
    intro j
    have hNne : N j ≠ 0 := (hN j).ne'
    have e1 : Real.sqrt (Qc j * N j) ^ 2 = Qc j * N j :=
      Real.sq_sqrt (mul_nonneg (hQc j) (hN j).le)
    have e2 : Real.sqrt ((Pm j).trace) ^ 2 = (Pm j).trace := Real.sq_sqrt (htr j)
    have hb2 : bd j ^ 2 = Qc j * N j * (9 * (Lop j ^ 2 * (Pm j).trace)) := by
      simp only [hbd, biasEntryBound]
      rw [mul_pow, e1, mul_pow, mul_pow, e2]
      ring
    rw [hb2]
    field_simp
  simp only [hexp]
  simpa using hratevar.add (hratebias.const_mul 9)

end Sequences

/-! ### Examples for the asymptotic tails

`𝒪_j = {0,…,j}` with one dimension that has a single category, so `Sh = ιι'`; `K = 1`;
`x̃_o = 𝟙{o = 0}`, so `‖C‖_F² = 1`; `Π_j = ee'` with `e_o = 𝟙{o = 0}`; and `n = j+1`. The
probabilistic example is on `(Unit, dirac ())`. -/

section Witnesses

/-- `e_o = 𝟙{o = 0}` on `𝒪_j = {0,…,j}`. -/
def witE0 (j : ℕ) : Fin (j + 1) → ℝ := fun o => if o = 0 then 1 else 0

theorem witE0_mul_self (j : ℕ) (o : Fin (j + 1)) : witE0 j o * witE0 j o = witE0 j o := by
  simp only [witE0]
  split_ifs <;> norm_num

theorem witE0_sum (j : ℕ) : ∑ o : Fin (j + 1), witE0 j o = 1 := by
  simp [witE0]

/-- One maintained dimension with a single category: every pair is a sharing pair. -/
def witSeqC (j : ℕ) : Fin 1 → Fin (j + 1) → Fin 1 := fun _ _ => 0

theorem witSeq_linked (j : ℕ) (o o' : Fin (j + 1)) :
    Linked (witSeqC j) (Finset.univ : Finset (Fin 1)) o o' :=
  ⟨0, Finset.mem_univ 0, rfl⟩

/-- `x̃_o = 𝟙{o = 0}`, one regressor, so that `‖C‖_F² = 1`. -/
def witSeqX (j : ℕ) : Fin (j + 1) → Fin 1 → ℝ := fun o _ => witE0 j o

/-- `Π_j = ee'`, the rank-one coordinate projector at `o = 0`. -/
def witSeqPm (j : ℕ) : Matrix (Fin (j + 1)) (Fin (j + 1)) ℝ :=
  Matrix.of fun o o' => witE0 j o * witE0 j o'

theorem witSeqPm_isSymm (j : ℕ) : (witSeqPm j).IsSymm := by
  show (witSeqPm j)ᵀ = witSeqPm j
  ext o o'
  simp only [Matrix.transpose_apply, witSeqPm, Matrix.of_apply]
  ring

theorem witSeqPm_idem (j : ℕ) : witSeqPm j * witSeqPm j = witSeqPm j := by
  ext o o'
  rw [Matrix.mul_apply]
  have h : ∀ k : Fin (j + 1), witSeqPm j o k * witSeqPm j k o'
      = witSeqPm j o o' * witE0 j k := by
    intro k
    simp only [witSeqPm, Matrix.of_apply]
    rw [show witE0 j o * witE0 j k * (witE0 j k * witE0 j o')
        = witE0 j o * witE0 j o' * (witE0 j k * witE0 j k) by ring, witE0_mul_self]
  rw [Finset.sum_congr rfl fun k _ => h k, ← Finset.mul_sum, witE0_sum, mul_one]

/-- `tr(Π_j) = 1` at every index. -/
theorem witSeqPm_trace (j : ℕ) : (witSeqPm j).trace = 1 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, witSeqPm, Matrix.of_apply, witE0_mul_self]
  exact witE0_sum j

/-- `‖C‖_F² = 1`. -/
theorem witSeq_cs (j : ℕ) (a b : Fin 1) :
    (∑ o : Fin (j + 1), ∑ o' : Fin (j + 1), (witSeqX j o a * witSeqX j o' b) ^ 2
      * sharingMat (witSeqC j) (Finset.univ : Finset (Fin 1)) o o') = 1 := by
  have h : ∀ o o' : Fin (j + 1), (witSeqX j o a * witSeqX j o' b) ^ 2
      * sharingMat (witSeqC j) (Finset.univ : Finset (Fin 1)) o o'
      = witE0 j o * witE0 j o' := by
    intro o o'
    rw [sharingMat_of_linked (witSeq_linked j o o'), mul_one]
    simp only [witSeqX, witE0]
    split_ifs <;> norm_num
  simp only [h]
  rw [← Finset.sum_mul_sum, witE0_sum]
  norm_num

theorem witSeq_grow : Tendsto (fun j : ℕ => ((j : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
  have hgrow : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop := by
    refine Filter.tendsto_atTop_mono (fun j => ?_) tendsto_natCast_atTop_atTop
    linarith
  exact hgrow.inv_tendsto_atTop

/-- The hypotheses of `tendsto_frobNorm_bias_div_card` are jointly satisfiable, with
`Ω' = I`, `Π_j` the rank-one coordinate projector and `n = j+1`. -/
theorem tendsto_frobNorm_bias_div_card_witness :
    Tendsto (fun j : ℕ => frobNorm (xGram (witSeqX j) (Matrix.hadamard
        ((1 - witSeqPm j) * 1 * (1 - witSeqPm j) - 1)
        (sharingMat (witSeqC j) (Finset.univ : Finset (Fin 1)))))
      / ((j : ℝ) + 1)) atTop (𝓝 0) := by
  refine tendsto_frobNorm_bias_div_card (D := fun _ => Fin 1) (O := fun j => Fin (j + 1))
    (L := fun _ => Fin 1) (K := fun _ => Fin 1) witSeqC (fun _ => Finset.univ) witSeqX
    (Pm := witSeqPm) (Omp := fun _ => 1) witSeqPm_isSymm witSeqPm_idem
    (fun _ => Matrix.isSymm_one) (Lop := fun _ => 1) (Qc := fun _ => 1)
    (N := fun j => (j : ℝ) + 1) (fun _ => zero_le_one) (fun _ => zero_le_one)
    (fun j => by positivity) ?_ ?_ ?_
  · intro j A
    simp
  · intro j a b
    rw [witSeq_cs j a b, one_mul]
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  · have hfun : ∀ j : ℕ, (Fintype.card (Fin 1) : ℝ) ^ 2
        * ((1 : ℝ) ^ 2 * (witSeqPm j).trace) * 1 / ((j : ℝ) + 1) = ((j : ℝ) + 1)⁻¹ := by
      intro j
      rw [witSeqPm_trace]
      norm_num
    simp only [hfun]
    exact witSeq_grow

/-- The hypotheses of `tendstoInProb_frobNorm_bias_div_card` are jointly satisfiable. -/
theorem tendstoInProb_frobNorm_bias_div_card_witness :
    TendstoInMeasure (Measure.dirac ())
      (fun (j : ℕ) (_ : Unit) => frobNorm (xGram (witSeqX j) (Matrix.hadamard
        ((1 - witSeqPm j) * 1 * (1 - witSeqPm j) - 1)
        (sharingMat (witSeqC j) (Finset.univ : Finset (Fin 1)))))
      / ((j : ℝ) + 1)) atTop (fun _ => (0 : ℝ)) := by
  refine tendstoInProb_frobNorm_bias_div_card (D := fun _ => Fin 1)
    (O := fun j => Fin (j + 1)) (L := fun _ => Fin 1) (K := fun _ => Fin 1)
    (P := Measure.dirac ()) witSeqC (fun _ => Finset.univ) (fun j _ => witSeqX j)
    (Pm := witSeqPm) (Omp := fun _ => 1) witSeqPm_isSymm witSeqPm_idem
    (fun _ => Matrix.isSymm_one) (Lop := fun _ => 1) (Qc := fun _ => 1)
    (N := fun j => (j : ℝ) + 1) (fun _ => zero_le_one) (fun _ => zero_le_one)
    (fun j => by positivity) ?_ ?_ ?_
  · intro j A
    simp
  · intro j
    refine Filter.Eventually.of_forall fun ω a b => ?_
    rw [witSeq_cs j a b, one_mul]
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  · have hfun : ∀ j : ℕ, (Fintype.card (Fin 1) : ℝ) ^ 2
        * ((1 : ℝ) ^ 2 * (witSeqPm j).trace) * 1 / ((j : ℝ) + 1) = ((j : ℝ) + 1)⁻¹ := by
      intro j
      rw [witSeqPm_trace]
      norm_num
    simp only [hfun]
    exact witSeq_grow

/-! #### The probabilistic example -/

/-- Evaluation at the single point of `Unit`, a linear functional that agrees with
`∫·d(dirac ())`. -/
def witEval : (Unit → ℝ) →ₗ[ℝ] ℝ where
  toFun f := f ()
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem witEval_apply (f : Unit → ℝ) : witEval f = f () := rfl

/-- `ζ_o = 𝟙{o = 0}`, deterministic on the one-point space. -/
def witSeqZ (j : ℕ) : Fin (j + 1) → Unit → ℝ := fun o _ => witE0 j o

theorem witDiracIntegral (g : Unit → ℝ) : ∫ ω, g ω ∂(Measure.dirac ()) = g () := by
  have h : g = fun _ => g () := funext fun u => by cases u; rfl
  rw [h]
  simp

theorem witDiracIntegrable (g : Unit → ℝ) : Integrable g (Measure.dirac ()) := by
  have h : g = fun _ => g () := funext fun u => by cases u; rfl
  rw [h]
  exact integrable_const _

/-- `‖Ω'‖ ≤ 1` for the rank-one `Ω' = ee'`, in the form `hOpNorm` takes. -/
theorem frobSq_mul_witSeqPm_le (j : ℕ) (A : Matrix (Fin (j + 1)) (Fin (j + 1)) ℝ) :
    frobSq (A * witSeqPm j) ≤ (1 : ℝ) ^ 2 * frobSq A := by
  have hsq0 : ∀ o' : Fin (j + 1), witE0 j o' ^ 2 = witE0 j o' := by
    intro o'
    simp only [witE0]
    split_ifs <;> norm_num
  have hentry : ∀ o o' : Fin (j + 1), (A * witSeqPm j) o o' = A o 0 * witE0 j o' := by
    intro o o'
    rw [Matrix.mul_apply]
    have h1 : ∀ k : Fin (j + 1), A o k * witSeqPm j k o'
        = (if k = 0 then A o k else 0) * witE0 j o' := by
      intro k
      simp only [witSeqPm, Matrix.of_apply, witE0]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun k _ => h1 k, ← Finset.sum_mul]
    congr 1
    simp
  have hfs : frobSq (A * witSeqPm j) = ∑ o : Fin (j + 1), (A o 0) ^ 2 := by
    rw [frobSq]
    refine Finset.sum_congr rfl fun o _ => ?_
    have h2 : ∀ o' : Fin (j + 1), ((A * witSeqPm j) o o') ^ 2 = (A o 0) ^ 2 * witE0 j o' := by
      intro o'
      rw [hentry o o', mul_pow, hsq0 o']
    rw [Finset.sum_congr rfl fun o' _ => h2 o', ← Finset.mul_sum, witE0_sum, mul_one]
  rw [hfs, one_pow, one_mul, frobSq]
  refine Finset.sum_le_sum fun o _ => ?_
  exact Finset.single_le_sum (f := fun k => (A o k) ^ 2) (fun k _ => sq_nonneg _)
    (Finset.mem_univ 0)

/-- `X̃'(Ω'∘Sh)X̃ = 1`, so that `nS_n = 1` and `S_n = (j+1)^{-1}`. -/
theorem witSeq_nSn (j : ℕ) (a b : Fin 1) :
    xGram (witSeqX j) (Matrix.hadamard (witSeqPm j)
      (sharingMat (witSeqC j) (Finset.univ : Finset (Fin 1)))) a b = 1 := by
  rw [xGram_apply]
  have h : ∀ o o' : Fin (j + 1), witSeqX j o a * (Matrix.hadamard (witSeqPm j)
      (sharingMat (witSeqC j) (Finset.univ : Finset (Fin 1)))) o o' * witSeqX j o' b
      = witE0 j o * witE0 j o' := by
    intro o o'
    rw [Matrix.hadamard_apply, sharingMat_of_linked (witSeq_linked j o o'), mul_one]
    simp only [witSeqX, witSeqPm, Matrix.of_apply]
    rw [show witE0 j o * (witE0 j o * witE0 j o') * witE0 j o'
        = witE0 j o * witE0 j o * (witE0 j o' * witE0 j o') by ring,
      witE0_mul_self, witE0_mul_self]
  simp only [h]
  rw [← Finset.sum_mul_sum, witE0_sum]
  norm_num

/-- The hypotheses of `tendstoInProb_frobNorm_meat_div_card` are jointly satisfiable. -/
theorem tendstoInProb_frobNorm_meat_div_card_witness :
    TendstoInMeasure (Measure.dirac ())
      (fun (j : ℕ) (ω : Unit) => frobNorm ((((j : ℝ) + 1)⁻¹) •
        (Matrix.of fun a b => QuadformE2.quadForm
          (wMat (witSeqC j) (Finset.univ : Finset (Fin 1)) (witSeqX j) (1 - witSeqPm j) a b)
          (witSeqZ j) ω)
        - (Matrix.of fun _ _ => ((j : ℝ) + 1)⁻¹ : Matrix (Fin 1) (Fin 1) ℝ)))
      atTop (fun _ => (0 : ℝ)) := by
  have hfun : ∀ j : ℕ, (Fintype.card (Fin 1) : ℝ) ^ 2
      * ((1 : ℝ) ^ 2 * (witSeqPm j).trace) * 1 / ((j : ℝ) + 1) = ((j : ℝ) + 1)⁻¹ := by
    intro j
    rw [witSeqPm_trace]
    norm_num
  refine tendstoInProb_frobNorm_meat_div_card (D := fun _ => Fin 1)
    (O := fun j => Fin (j + 1)) (L := fun _ => Fin 1) (K := fun _ => Fin 1)
    (P := Measure.dirac ()) witSeqC (fun _ => Finset.univ) witSeqX (fun _ => witEval) witSeqZ
    (Pm := witSeqPm) (Omp := witSeqPm)
    (Sn := fun j => Matrix.of fun _ _ => ((j : ℝ) + 1)⁻¹)
    witSeqPm_isSymm witSeqPm_idem witSeqPm_isSymm (fun j o o' => rfl)
    (Lop := fun _ => 1) (Qc := fun _ => 1) (N := fun j => (j : ℝ) + 1) (v := fun _ => 1)
    (fun _ => zero_le_one) (fun _ => zero_le_one) (fun j => by positivity)
    (fun j => frobSq_mul_witSeqPm_le j) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j a b
    rw [witSeq_cs j a b, one_mul]
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  · intro j a b
    rw [witSeq_nSn j a b, Matrix.of_apply]
    have hne : ((j : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  · exact fun j a b => witDiracIntegrable _
  · exact fun j a b => witDiracIntegrable _
  · intro j a b
    rw [witDiracIntegral]
    rfl
  · intro j a b
    rw [witDiracIntegral]
    rfl
  · intro j a b
    have h0 : QuadformE2.varQuad witEval
        (wMat (witSeqC j) (Finset.univ : Finset (Fin 1)) (witSeqX j) (1 - witSeqPm j) a b)
        (witSeqZ j) = 0 := by
      simp [QuadformE2.varQuad]
    rw [h0]
    norm_num
  · simp only [hfun]
    exact witSeq_grow
  · have hsq : Tendsto (fun j : ℕ => (((j : ℝ) + 1)⁻¹) ^ 2) atTop (𝓝 0) := by
      simpa using witSeq_grow.pow 2
    refine Tendsto.congr (fun j => ?_) hsq
    rw [Fintype.card_fin]
    norm_num

end Witnesses

end Tails

/-! ## Examples for the finite-sample clauses

For clause (a), two observations share one category, `x̃ = (1, -1)'`, the idiosyncratic variance
is `1` and the level-one variance is `3`; the union meat is `2`. For clause (b), one observation
with `Π = I` and `Ω' = I`, so `R = 0`. For clause (c), one Rademacher observation with `R = I`
and `Ω' = I`. -/

section Witness

/-- One fixed-effect dimension, one category: both observations share it. -/
def witC : Fin 1 → Fin 2 → Fin 1 := fun _ _ => 0

/-- The within-transformed regressor `x̃ = (1, -1)'`, which sums to zero over the one cell. -/
def witX : Fin 2 → Fin 1 → ℝ := fun o _ => if o = 0 then (1 : ℝ) else -1

/-- `Ω = 3·Sh_{\{0\}} + I`: a level-one variance of `3` and unit idiosyncratic variance. -/
noncomputable def witOm : Matrix (Fin 2) (Fin 2) ℝ :=
  (∑ m ∈ (Finset.univ : Finset (Fin 1)), (3 : ℝ) • shMat witC ({m} : Finset (Fin 1)))
    + (Matrix.diagonal (fun _ : Fin 2 => (1 : ℝ))
        + ∑ e ∈ (∅ : Finset (Finset (Fin 1))), (0 : ℝ) • shMat witC e)

theorem witLinked (o o' : Fin 2) : Linked witC Finset.univ o o' :=
  ⟨0, Finset.mem_univ 0, rfl⟩

theorem unionmeat_a_witness :
    sharedGram witC Finset.univ witX witOm = Matrix.of (fun _ _ => (2 : ℝ)) := by
  refine unionmeat_a witC Finset.univ witX ∅ (fun _ => 3) (fun _ => 0)
    (fun _ => 1) rfl rfl rfl ?_ ?_ ?_
  · intro o o' h
    exact absurd (witLinked o o') h
  · intro m _ t ht k
    have hcell : ∀ o : Fin 2, cellOf witC ({m} : Finset (Fin 1)) o = Finset.univ := by
      intro o
      ext o'
      simp [SameOn, witC]
    obtain ⟨o₀, -, rfl⟩ := Finset.mem_image.1 ht
    rw [hcell o₀, cellWeight]
    simp [witX, Fin.sum_univ_two]
  · ext a b
    rw [Matrix.of_apply, Matrix.add_apply, xGram_apply, Finset.sum_empty,
      Matrix.zero_apply, add_zero]
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha; subst hb
    simp [witX, Matrix.diagonal, Fin.sum_univ_two]
    norm_num

/-- The same model with the level-one variance `7` in place of `3`. -/
noncomputable def witOm7 : Matrix (Fin 2) (Fin 2) ℝ :=
  (∑ m ∈ (Finset.univ : Finset (Fin 1)), (7 : ℝ) • shMat witC ({m} : Finset (Fin 1)))
    + (Matrix.diagonal (fun _ : Fin 2 => (1 : ℝ))
        + ∑ e ∈ (∅ : Finset (Finset (Fin 1))), (0 : ℝ) • shMat witC e)

/-- The hypotheses of `identE2_i` are jointly satisfiable, on the model of
`unionmeat_a_witness` with `R = I₂ - ιι'/2` and level-one variances `3` and `7`. Both
conjuncts are nontrivial, since `RΩR = wR ≠ 0` and the union meat equals `2`. -/
theorem identE2_i_witness :
    IdentE2.wR * witOm * IdentE2.wR = IdentE2.wR * witOm7 * IdentE2.wR
      ∧ sharedGram witC Finset.univ witX witOm
          = sharedGram witC Finset.univ witX witOm7 := by
  refine identE2_i witC Finset.univ witX ∅ (fun _ => 3) (fun _ => 7) (fun _ => 0) 1 1
    IdentE2.wR_isSymm ?_ (by simp) rfl rfl rfl rfl rfl ?_ ?_
  · intro m _ t ht o
    have hcell : ∀ o : Fin 2, cellOf witC ({m} : Finset (Fin 1)) o = Finset.univ := by
      intro o
      ext o'
      simp [SameOn, witC]
    obtain ⟨o₀, -, rfl⟩ := Finset.mem_image.1 ht
    rw [hcell o₀]
    exact IdentE2.wR_row_sum o
  · intro o o' h
    exact absurd (witLinked o o') h
  · intro m _ t ht k
    have hcell : ∀ o : Fin 2, cellOf witC ({m} : Finset (Fin 1)) o = Finset.univ := by
      intro o
      ext o'
      simp [SameOn, witC]
    obtain ⟨o₀, -, rfl⟩ := Finset.mem_image.1 ht
    rw [hcell o₀, cellWeight]
    simp [witX, Fin.sum_univ_two]

/-- One observation, one dimension, one category, unit regressor. -/
def witC1 : Fin 1 → Fin 1 → Fin 1 := fun _ _ => 0

def witX1 : Fin 1 → Fin 1 → ℝ := fun _ _ => 1

theorem witLinked1 (o o' : Fin 1) : Linked witC1 Finset.univ o o' :=
  ⟨0, Finset.mem_univ 0, rfl⟩

/-- Clause (b)'s bound at `Π = I`, where `R = 0` and all of `Ω'` is bias:
`|-1| ≤ 3·‖Ω'‖·√(tr Π)`. -/
theorem unionmeat_b_bound_witness :
    |xGram witX1 (Matrix.hadamard
        (((1 : Matrix (Fin 1) (Fin 1) ℝ) - 1) * 1 * ((1 : Matrix (Fin 1) (Fin 1) ℝ) - 1) - 1)
        (sharingMat witC1 Finset.univ)) 0 0| ≤ 3 := by
  refine (unionmeat_b_bound witC1 Finset.univ witX1 (P := (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (Omp := (1 : Matrix (Fin 1) (Fin 1) ℝ)) Matrix.isSymm_one (by simp) Matrix.isSymm_one
    (Lop := 1) (Q := 1) (by norm_num) (by norm_num) (fun A => by simp) 0 0 ?_).trans_eq ?_
  · rw [Fin.sum_univ_one, Fin.sum_univ_one, sharingMat_of_linked (witLinked1 0 0)]
    simp [witX1]
  · rw [Matrix.trace_one]
    simp

theorem unionmeat_c_witness :
    QuadformE2.varQuad QuadformE2.witE
        ((1 : Matrix (Fin 1) (Fin 1) ℝ) * ((2⁻¹ : ℝ) • ((1 : Matrix (Fin 1) (Fin 1) ℝ)
          + (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ)) * (1 : Matrix (Fin 1) (Fin 1) ℝ))
        QuadformE2.witZ
      ≤ 4 := by
  have hone : frobSq (1 : Matrix (Fin 1) (Fin 1) ℝ) = 1 := by
    simp [frobSq, Matrix.one_apply]
  refine (unionmeat_c (Ω := Bool) (Γ := Unit) QuadformE2.witE
    (R := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (Omp := (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (Cmat := (1 : Matrix (Fin 1) (Fin 1) ℝ))
    Matrix.isSymm_one (by simp) Matrix.isSymm_one QuadformE2.witZ ?_ rfl
    {()} (fun _ _ _ _ _ => -2) ?_ (fun _ _ _ => True) (Kb := 2) (Lam := 1) (Lop := 1)
    (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_).trans_eq ?_
  · intro o o'
    have ho : o = 0 := Subsingleton.elim _ _
    have ho' : o' = 0 := Subsingleton.elim _ _
    subst ho; subst ho'
    simp
  · intro o₁ o₂ o₃ o₄
    simp only [QuadformE2.cum4, Finset.sum_singleton, QuadformE2.witE_apply, Pi.mul_apply,
      QuadformE2.witZ_true, QuadformE2.witZ_false]
    norm_num
  · intro g _ p q h
    exact absurd trivial h
  · intro g _ p q; norm_num
  · intro g _ p
    have : (Finset.univ.filter fun _ : Fin 1 × Fin 1 => True) = Finset.univ := by
      simp
    rw [this]
    simp
  · intro g _ q
    have : (Finset.univ.filter fun _ : Fin 1 × Fin 1 => True) = Finset.univ := by
      simp
    rw [this]
    simp
  · intro A
    simp
  · rw [hone]
    norm_num

end Witness

/-! ## Theorem 8(c): `nV̂_[Δ] ⟶^p H^{-1}SH^{-1}`

The estimator is `V̂_[Δ] := (X̃'X̃)^{-1}𝓜̂_[Δ](X̃'X̃)^{-1}`. The hypotheses are `hH : H.PosDef` and
`hG : n^{-1}X̃'X̃ ⟶^p H` (the design assumption), `hM : n^{-1}𝓜̂_[Δ] - S_n ⟶^p 0` (the
conclusion of `tendstoInProb_frobNorm_meat_div_card`), `hS : S_n ⟶^p S`, and `hN : 0 < N n`.
`X̃'X̃` is not assumed invertible, since `Matrix.inv` is total and the event that `n^{-1}X̃'X̃` is
singular has vanishing probability. Continuity of inversion is `NormedRing.inverse_continuousAt`
under the scoped `Matrix.Norms.L2Operator` instance.
-/

section ContinuousMapping

open Filter MeasureTheory

open scoped Topology

variable {Ωp : Type*} {mΩp : MeasurableSpace Ωp} {P : Measure Ωp}

/-! ### Convergence in probability to a constant limit -/

/-- `u_n ⟶^p a` is the same statement as `d(u_n, a) ⟶^p 0`: the two index sets are equal. -/
theorem tendstoInProb_const_iff_dist {E : Type*} [PseudoMetricSpace E]
    {u : ℕ → Ωp → E} {a : E} :
    TendstoInMeasure P u atTop (fun _ => a)
      ↔ TendstoInMeasure P (fun n ω => dist (u n ω) a) atTop (fun _ => (0 : ℝ)) := by
  have hset : ∀ (n : ℕ) (ε : ℝ),
      {ω | ε ≤ dist (dist (u n ω) a) (0 : ℝ)} = {ω | ε ≤ dist (u n ω) a} := by
    intro n ε
    ext ω
    simp [abs_of_nonneg dist_nonneg]
  rw [tendstoInMeasure_iff_dist, tendstoInMeasure_iff_dist]
  constructor <;> intro h ε hε
  · simpa only [hset] using h ε hε
  · simpa only [hset] using h ε hε

/-- **Continuous mapping in probability**, two arguments, constant limits. No measurability
of `u` or `v` is needed. -/
theorem tendstoInProb_comp₂ {E F Z : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    [PseudoMetricSpace Z] {u : ℕ → Ωp → E} {v : ℕ → Ωp → F} {a : E} {b : F} {g : E → F → Z}
    (hg : ContinuousAt (fun p : E × F => g p.1 p.2) (a, b))
    (hu : TendstoInMeasure P u atTop (fun _ => a))
    (hv : TendstoInMeasure P v atTop (fun _ => b)) :
    TendstoInMeasure P (fun n ω => g (u n ω) (v n ω)) atTop (fun _ => g a b) := by
  rw [tendstoInMeasure_iff_dist] at hu hv ⊢
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.1 hg ε hε
  have hmono : ∀ n : ℕ, P {ω | ε ≤ dist (g (u n ω) (v n ω)) (g a b)}
      ≤ P {ω | δ ≤ dist (u n ω) a} + P {ω | δ ≤ dist (v n ω) b} := by
    intro n
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro ω hω
    replace hω : ε ≤ dist (g (u n ω) (v n ω)) (g a b) := hω
    by_cases h1 : δ ≤ dist (u n ω) a
    · exact Or.inl h1
    by_cases h2 : δ ≤ dist (v n ω) b
    · exact Or.inr h2
    replace h1 : dist (u n ω) a < δ := not_le.1 h1
    replace h2 : dist (v n ω) b < δ := not_le.1 h2
    exfalso
    have hd : dist ((u n ω, v n ω)) (a, b) < δ := by
      rw [Prod.dist_eq]
      exact max_lt h1 h2
    exact absurd (hδ hd) (not_lt.2 hω)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun n => zero_le) hmono
  simpa using (hu δ hδpos).add (hv δ hδpos)

/-- A nonnegative sequence dominated by a fixed multiple of a null sequence is null. -/
theorem tendstoInProb_zero_of_le_const_mul {u v : ℕ → Ωp → ℝ} {c : ℝ} (hc : 0 < c)
    (hu0 : ∀ n ω, 0 ≤ u n ω) (hle : ∀ n ω, u n ω ≤ c * v n ω)
    (hv : TendstoInMeasure P v atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P u atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist] at hv ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hv (ε / c) (by positivity)) (fun n => zero_le) (fun n => measure_mono fun ω hω => ?_)
  replace hω : ε ≤ dist (u n ω) (0 : ℝ) := hω
  show ε / c ≤ dist (v n ω) (0 : ℝ)
  rw [Real.dist_eq, sub_zero] at hω ⊢
  rw [abs_of_nonneg (hu0 n ω)] at hω
  have h1 : ε ≤ c * v n ω := le_trans hω (hle n ω)
  have h2 : ε / c ≤ v n ω := (div_le_iff₀ hc).2 (by linarith)
  exact le_trans h2 (le_abs_self _)

theorem tendstoInProb_congr_eventually {E : Type*} [PseudoMetricSpace E]
    {u v : ℕ → Ωp → E} {a : E} (h : ∀ᶠ n in atTop, u n = v n)
    (hu : TendstoInMeasure P u atTop (fun _ => a)) :
    TendstoInMeasure P v atTop (fun _ => a) := by
  rw [tendstoInMeasure_iff_dist] at hu ⊢
  intro ε hε
  refine (hu ε hε).congr' ?_
  filter_upwards [h] with n hn
  rw [hn]

theorem tendstoInProb_zero_add {v w : ℕ → Ωp → ℝ}
    (hv : TendstoInMeasure P v atTop (fun _ => (0 : ℝ)))
    (hw : TendstoInMeasure P w atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P (fun n ω => v n ω + w n ω) atTop (fun _ => (0 : ℝ)) := by
  have h := tendstoInProb_comp₂ (g := fun x y : ℝ => x + y) continuous_add.continuousAt hv hw
  simpa using h

theorem tendstoInProb_zero_of_le_add {u v w : ℕ → Ωp → ℝ} (hu0 : ∀ n ω, 0 ≤ u n ω)
    (hle : ∀ n ω, u n ω ≤ v n ω + w n ω)
    (hv : TendstoInMeasure P v atTop (fun _ => (0 : ℝ)))
    (hw : TendstoInMeasure P w atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P u atTop (fun _ => (0 : ℝ)) :=
  tendstoInProb_zero_of_le_const_mul one_pos hu0
    (fun n ω => by rw [one_mul]; exact hle n ω) (tendstoInProb_zero_add hv hw)

/-- A deterministic limit is a limit in probability. -/
theorem tendstoInProb_of_tendsto [IsFiniteMeasure P] {a : ℕ → ℝ} {c : ℝ}
    (h : Tendsto a atTop (𝓝 c)) :
    TendstoInMeasure P (fun n (_ : Ωp) => a n) atTop (fun _ => c) :=
  tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
    (Filter.Eventually.of_forall fun _ => h)

/-! ### `‖·‖_F` against the `ℓ²` operator norm, and continuity of inversion

The scoped instance `Matrix.Norms.L2Operator` is opened only in this section; the comparisons
`‖A‖ ≤ ‖A‖_F ≤ √K‖A‖` let every exported statement be phrased with `frobNorm`. -/

section MatrixNorms

open scoped Matrix.Norms.L2Operator

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- `‖A‖ ≤ ‖A‖_F`. -/
theorem l2_opNorm_le_frobNorm (A : Matrix K K ℝ) : ‖A‖ ≤ frobNorm A := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (frobNorm_nonneg A) fun x => ?_
  have hx : ‖x‖ ^ 2 = ∑ j : K, (x.ofLp j) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    exact Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, sq_abs]
  have hy : ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) A) x‖ ^ 2
      = ∑ i : K, (∑ j : K, A i j * x.ofLp j) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show ((Matrix.toEuclideanCLM (𝕜 := ℝ) A) x).ofLp i = ∑ j : K, A i j * x.ofLp j from rfl,
      Real.norm_eq_abs, sq_abs]
  have hsum : ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) A) x‖ ^ 2 ≤ (frobNorm A * ‖x‖) ^ 2 := by
    rw [hy, mul_pow, sq_frobNorm, hx, frobSq, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ =>
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => A i j) (fun j => x.ofLp j)
  have hnn : 0 ≤ frobNorm A * ‖x‖ := mul_nonneg (frobNorm_nonneg A) (norm_nonneg x)
  have h := Real.sqrt_le_sqrt hsum
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hnn] at h

/-- `‖A‖_F ≤ √(card K)‖A‖`: the columns are the images of the standard basis. -/
theorem frobNorm_le_sqrt_card_mul_l2_opNorm (A : Matrix K K ℝ) :
    frobNorm A ≤ Real.sqrt (Fintype.card K) * ‖A‖ := by
  have hcol : ∀ j : K, ∑ i : K, (A i j) ^ 2 ≤ ‖A‖ ^ 2 := by
    intro j
    have hb := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single j (1 : ℝ))
    rw [show ((EuclideanSpace.single j (1 : ℝ)) : EuclideanSpace ℝ K).ofLp = Pi.single j (1 : ℝ)
      from rfl] at hb
    have hmv : A.mulVec (Pi.single j (1 : ℝ)) = fun i => A i j := by
      funext i; simp [Matrix.mulVec_single]
    rw [hmv] at hb
    have hone : ‖EuclideanSpace.single j (1 : ℝ)‖ = 1 := by simp
    rw [hone, mul_one] at hb
    have hnorm : ‖(EuclideanSpace.equiv K ℝ).symm (fun i => A i j)‖ ^ 2
        = ∑ i : K, (A i j) ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]; rfl
    calc ∑ i : K, (A i j) ^ 2 = ‖(EuclideanSpace.equiv K ℝ).symm (fun i => A i j)‖ ^ 2 :=
          hnorm.symm
      _ ≤ ‖A‖ ^ 2 := by
          nlinarith [norm_nonneg ((EuclideanSpace.equiv K ℝ).symm (fun i => A i j)),
            norm_nonneg A]
  have hfs : frobSq A ≤ (Fintype.card K : ℝ) * ‖A‖ ^ 2 := by
    rw [frobSq, Finset.sum_comm]
    calc ∑ j : K, ∑ i : K, (A i j) ^ 2 ≤ ∑ _j : K, ‖A‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => hcol j
      _ = (Fintype.card K : ℝ) * ‖A‖ ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hnn : 0 ≤ Real.sqrt (Fintype.card K) * ‖A‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg A)
  have hsq : frobNorm A ^ 2 ≤ (Real.sqrt (Fintype.card K) * ‖A‖) ^ 2 := by
    rw [sq_frobNorm, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    exact hfs
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (frobNorm_nonneg A), Real.sqrt_sq hnn] at h

/-- The map `(G,M) ↦ G^{-1}MG^{-1}` is continuous at an invertible `G`. -/
theorem continuousAt_conj_inverse {H : Matrix K K ℝ} (hH : IsUnit H) (S : Matrix K K ℝ) :
    ContinuousAt (fun p : Matrix K K ℝ × Matrix K K ℝ =>
      Ring.inverse p.1 * p.2 * Ring.inverse p.1) (H, S) := by
  obtain ⟨u, rfl⟩ := hH
  have h1 : ContinuousAt (fun p : Matrix K K ℝ × Matrix K K ℝ => Ring.inverse p.1)
      (((u : Matrix K K ℝ)), S) := by
    have h := ContinuousAt.comp (x := ((u : Matrix K K ℝ), S))
      (NormedRing.inverse_continuousAt u) continuousAt_fst
    simpa [Function.comp_def] using h
  exact (h1.mul continuousAt_snd).mul h1

/-- **Continuous mapping for `G^{-1}MG^{-1}`**, in `‖·‖_F`. `G_n` is not assumed
invertible. -/
theorem tendstoInProb_conj_inverse {G M : ℕ → Ωp → Matrix K K ℝ} {H S : Matrix K K ℝ}
    (hH : IsUnit H)
    (hG : TendstoInMeasure P (fun n ω => frobNorm (G n ω - H)) atTop (fun _ => (0 : ℝ)))
    (hM : TendstoInMeasure P (fun n ω => frobNorm (M n ω - S)) atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P
      (fun n ω => frobNorm ((G n ω)⁻¹ * M n ω * (G n ω)⁻¹ - H⁻¹ * S * H⁻¹))
      atTop (fun _ => (0 : ℝ)) := by
  have hGn : TendstoInMeasure P G atTop (fun _ => H) := by
    rw [tendstoInProb_const_iff_dist]
    refine tendstoInProb_zero_of_le_const_mul one_pos (fun n ω => dist_nonneg)
      (fun n ω => ?_) hG
    rw [one_mul, dist_eq_norm]
    exact l2_opNorm_le_frobNorm _
  have hMn : TendstoInMeasure P M atTop (fun _ => S) := by
    rw [tendstoInProb_const_iff_dist]
    refine tendstoInProb_zero_of_le_const_mul one_pos (fun n ω => dist_nonneg)
      (fun n ω => ?_) hM
    rw [one_mul, dist_eq_norm]
    exact l2_opNorm_le_frobNorm _
  have hcomp := tendstoInProb_comp₂ (g := fun x y : Matrix K K ℝ =>
    Ring.inverse x * y * Ring.inverse x) (continuousAt_conj_inverse hH S) hGn hMn
  rw [tendstoInProb_const_iff_dist] at hcomp
  simp only [Matrix.nonsing_inv_eq_ringInverse]
  refine tendstoInProb_zero_of_le_const_mul (c := Real.sqrt (Fintype.card K) + 1)
    (by positivity) (fun n ω => frobNorm_nonneg _) (fun n ω => ?_) hcomp
  rw [dist_eq_norm]
  have h1 := frobNorm_le_sqrt_card_mul_l2_opNorm
    (Ring.inverse (G n ω) * M n ω * Ring.inverse (G n ω)
      - Ring.inverse H * S * Ring.inverse H)
  nlinarith [norm_nonneg (Ring.inverse (G n ω) * M n ω * Ring.inverse (G n ω)
    - Ring.inverse H * S * Ring.inverse H)]

end MatrixNorms

/-! ### The normalization

`nV̂_[Δ] = (n^{-1}X̃'X̃)^{-1}(n^{-1}𝓜̂_[Δ])(n^{-1}X̃'X̃)^{-1}`, which requires `n ≠ 0`. -/

section Normalization

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- `(cA)^{-1} = c^{-1}A^{-1}` for `c ≠ 0`, with no invertibility hypothesis on `A`. -/
theorem inv_smul_of_ne_zero {c : ℝ} (hc : c ≠ 0) (A : Matrix K K ℝ) :
    (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  by_cases h : IsUnit A.det
  · refine Matrix.inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, one_smul, Matrix.nonsing_inv_mul A h]
  · have hdet0 : A.det = 0 := by rwa [isUnit_iff_ne_zero, not_not] at h
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, smul_zero,
      Matrix.nonsing_inv_apply_not_isUnit]
    rw [Matrix.det_smul, hdet0, mul_zero, isUnit_iff_ne_zero]
    simp

theorem conj_inv_smul {c : ℝ} (hc : c ≠ 0) (Gr Mh : Matrix K K ℝ) :
    (c • Gr)⁻¹ * (c • Mh) * (c • Gr)⁻¹ = c⁻¹ • (Gr⁻¹ * Mh * Gr⁻¹) := by
  rw [inv_smul_of_ne_zero hc, smul_mul_smul_comm, smul_mul_smul_comm,
    show c⁻¹ * c * c⁻¹ = c⁻¹ by field_simp]

end Normalization

/-! ### `nV̂_[Δ] ⟶^p H^{-1}SH^{-1}` -/

section NVhatDelta

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- **Theorem 8(c), second limit.**
`nV̂_[Δ] = n(X̃'X̃)^{-1}𝓜̂_[Δ](X̃'X̃)^{-1} ⟶^p H^{-1}SH^{-1}`, with `Gr = X̃'X̃`, `Mh = 𝓜̂_[Δ]`
and `Sn = S_n` unnormalized. -/
theorem tendstoInProb_nVhatDelta {Gr Mh Sn : ℕ → Ωp → Matrix K K ℝ} {H S : Matrix K K ℝ}
    {N : ℕ → ℝ} (hN : ∀ n, 0 < N n) (hH : H.PosDef)
    (hG : TendstoInMeasure P (fun n ω => frobNorm ((N n)⁻¹ • Gr n ω - H))
      atTop (fun _ => (0 : ℝ)))
    (hM : TendstoInMeasure P (fun n ω => frobNorm ((N n)⁻¹ • Mh n ω - Sn n ω))
      atTop (fun _ => (0 : ℝ)))
    (hS : TendstoInMeasure P (fun n ω => frobNorm (Sn n ω - S)) atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P
      (fun n ω => frobNorm (N n • ((Gr n ω)⁻¹ * Mh n ω * (Gr n ω)⁻¹) - H⁻¹ * S * H⁻¹))
      atTop (fun _ => (0 : ℝ)) := by
  have hHu : IsUnit H :=
    H.isUnit_iff_isUnit_det.2 (isUnit_iff_ne_zero.2 hH.det_pos.ne')
  have hMS : TendstoInMeasure P (fun n ω => frobNorm ((N n)⁻¹ • Mh n ω - S))
      atTop (fun _ => (0 : ℝ)) := by
    refine tendstoInProb_zero_of_le_add (fun n ω => frobNorm_nonneg _) (fun n ω => ?_) hM hS
    have hsplit : (N n)⁻¹ • Mh n ω - S
        = ((N n)⁻¹ • Mh n ω - Sn n ω) + (Sn n ω - S) := by abel
    rw [hsplit]
    exact frobNorm_add_le _ _
  have hconj := tendstoInProb_conj_inverse (G := fun n ω => (N n)⁻¹ • Gr n ω)
    (M := fun n ω => (N n)⁻¹ • Mh n ω) hHu hG hMS
  refine tendstoInProb_congr_eventually (Filter.Eventually.of_forall fun n => ?_) hconj
  funext ω
  rw [conj_inv_smul (inv_ne_zero (hN n).ne'), inv_inv]

end NVhatDelta

/-! ### Example

`K = 1` on a one-point space, `n = N_j = j+1`, `X̃'X̃ = [j+1]`, `H = S = [1]`,
`S_n = [1 + (j+1)^{-1}]` and `𝓜̂_[Δ] = [(j+1)(1 + (j+1)^{-1})]`; the limit is the identity and
`‖S_n - S‖_F = (j+1)^{-1} > 0`. -/

section NVhatDeltaWitness

theorem frobNorm_scalar (r : ℝ) :
    frobNorm ((Matrix.of fun _ _ => r : Matrix (Fin 1) (Fin 1) ℝ)) = |r| := by
  simp [frobNorm, frobSq, Real.sqrt_sq_eq_abs]

theorem tendstoInProb_nVhatDelta_witness :
    TendstoInMeasure (Measure.dirac ())
      (fun (n : ℕ) (_ : Unit) => frobNorm (((n : ℝ) + 1) •
          (((Matrix.of fun _ _ => (n : ℝ) + 1) : Matrix (Fin 1) (Fin 1) ℝ)⁻¹
              * ((Matrix.of fun _ _ => ((n : ℝ) + 1) * (1 + ((n : ℝ) + 1)⁻¹))
                  : Matrix (Fin 1) (Fin 1) ℝ)
              * ((Matrix.of fun _ _ => (n : ℝ) + 1) : Matrix (Fin 1) (Fin 1) ℝ)⁻¹)
            - (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ * 1 * (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹))
      atTop (fun _ => (0 : ℝ)) := by
  refine tendstoInProb_nVhatDelta (P := Measure.dirac ()) (H := 1) (S := 1)
    (N := fun n : ℕ => (n : ℝ) + 1)
    (Sn := fun (n : ℕ) (_ : Unit) => (Matrix.of fun _ _ => 1 + ((n : ℝ) + 1)⁻¹))
    (fun n => by positivity) Matrix.PosDef.one ?_ ?_ ?_
  · refine tendstoInProb_of_tendsto ?_
    have hval : ∀ n : ℕ, frobNorm ((((n : ℝ) + 1)⁻¹ • (Matrix.of fun _ _ => (n : ℝ) + 1) - 1 :
        Matrix (Fin 1) (Fin 1) ℝ)) = 0 := by
      intro n
      have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
      have heq : ((((n : ℝ) + 1)⁻¹ • (Matrix.of fun _ _ => (n : ℝ) + 1) - 1 :
          Matrix (Fin 1) (Fin 1) ℝ)) = Matrix.of fun _ _ => (0 : ℝ) := by
        ext i j
        fin_cases i; fin_cases j; simp [inv_mul_cancel₀ hne]
      rw [heq, frobNorm_scalar]
      simp
    simp only [hval]
    exact tendsto_const_nhds
  · refine tendstoInProb_of_tendsto ?_
    have hval : ∀ n : ℕ, frobNorm ((((n : ℝ) + 1)⁻¹
        • (Matrix.of fun _ _ => ((n : ℝ) + 1) * (1 + ((n : ℝ) + 1)⁻¹))
        - (Matrix.of fun _ _ => 1 + ((n : ℝ) + 1)⁻¹) : Matrix (Fin 1) (Fin 1) ℝ)) = 0 := by
      intro n
      have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
      have heq : ((((n : ℝ) + 1)⁻¹
          • (Matrix.of fun _ _ => ((n : ℝ) + 1) * (1 + ((n : ℝ) + 1)⁻¹))
          - (Matrix.of fun _ _ => 1 + ((n : ℝ) + 1)⁻¹) : Matrix (Fin 1) (Fin 1) ℝ))
          = Matrix.of fun _ _ => (0 : ℝ) := by
        ext i j
        fin_cases i; fin_cases j
        simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
          inv_mul_cancel_left₀ hne, sub_self]
      rw [heq, frobNorm_scalar]
      simp
    simp only [hval]
    exact tendsto_const_nhds
  · refine tendstoInProb_of_tendsto ?_
    have hval : ∀ n : ℕ, frobNorm (((Matrix.of fun _ _ => 1 + ((n : ℝ) + 1)⁻¹) - 1 :
        Matrix (Fin 1) (Fin 1) ℝ)) = ((n : ℝ) + 1)⁻¹ := by
      intro n
      have heq : (((Matrix.of fun _ _ => 1 + ((n : ℝ) + 1)⁻¹) - 1 :
          Matrix (Fin 1) (Fin 1) ℝ)) = Matrix.of fun _ _ => ((n : ℝ) + 1)⁻¹ := by
        ext i j
        fin_cases i; fin_cases j; simp
      rw [heq, frobNorm_scalar, abs_of_nonneg (by positivity)]
    simp only [hval]
    refine tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n => ?_
    rw [one_div]

end NVhatDeltaWitness

end ContinuousMapping

end UnionMeat
end Multiway
