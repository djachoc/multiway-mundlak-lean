import Multiway.Cgm
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Sequences of designs: from finite-sample bounds to limits

This file provides the asymptotic layer for statements over a sequence of designs indexed by
`n`, on one probability space `(Ω, P)`. Convergence in probability `⟶^p` is
`MeasureTheory.TendstoInMeasure P Z atTop (fun _ => 0)`, and `BddInProb` is `O_p(1)`.

## Main results

* `tendsto_sqrt_mul_div`: `√(a_n G_n n)/n → 0` whenever `a_n G_n/n → 0`.
* `tendstoInProb_zero_of_abs_le_const`, `tendstoInProb_zero_of_lintegral_le`: domination and
  Markov bridges into `⟶^p`.
* `tendstoInProb_zero_of_bddInProb_mul`, `tendstoInProb_zero_of_mul_bddInProb`:
  `o(1)·O_p(1)` and `o_p(1)·O_p(1)` are `o_p(1)`.
* `tendstoInProb_zero_of_le_sqrt_mul`: `κ√(S_nT_n) ⟶^p 0` when `S_n ⟶^p 0`, `T_n = O_p(1)`.
* `tendstoInProb_zero_of_condExp_abs_le`: a null bound on a conditional first moment.
* `tendsto_xiMat_div_card`, `tendstoInProb_xiMat_div_card`: `‖Ξ_n‖/n → 0` in Lemma SM.B.8(b).
-/

namespace Multiway
namespace Sequence

open Filter MeasureTheory
open scoped Topology ENNReal Matrix Matrix.Norms.L2Operator

/-! ## The `o`-calculus -/

section Rates

/-- A nonnegative sequence under a null majorant is null. -/
theorem tendsto_zero_of_le {f b : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hle : ∀ n, f n ≤ b n)
    (hb : Tendsto b atTop (𝓝 0)) : Tendsto f atTop (𝓝 0) :=
  squeeze_zero hf hle hb

/-- `√(a_n (G_n n))/n → 0` whenever `a_n G_n / n → 0`, via `√(aGn)/n = √(aG/n)`. -/
theorem tendsto_sqrt_mul_div {a G N : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hG : ∀ n, 0 ≤ G n) (hN : ∀ n, 0 < N n)
    (h : Tendsto (fun n => a n * G n / N n) atTop (𝓝 0)) :
    Tendsto (fun n => Real.sqrt (a n * (G n * N n)) / N n) atTop (𝓝 0) := by
  have key : ∀ n, Real.sqrt (a n * (G n * N n)) / N n = Real.sqrt (a n * G n / N n) := by
    intro n
    have hn := hN n
    have h1 : a n * G n / N n = a n * (G n * N n) / N n ^ 2 := by
      field_simp
    rw [h1, Real.sqrt_div (mul_nonneg (ha n) (mul_nonneg (hG n) hn.le)), Real.sqrt_sq hn.le]
  simp only [key]
  simpa using h.sqrt

end Rates

/-! ## Bridges into `⟶^p` -/

section InProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A sequence dominated almost everywhere by a null sequence of constants converges in
probability to zero. -/
theorem tendstoInProb_zero_of_abs_le_const {Z : ℕ → Ω → ℝ} {b : ℕ → ℝ}
    (hZ : ∀ n, ∀ᵐ ω ∂P, |Z n ω| ≤ b n) (hb : Tendsto b atTop (𝓝 0)) :
    TendstoInMeasure P Z atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hsmall : ∀ᶠ n in atTop, b n < ε := Filter.Tendsto.eventually_lt_const hε hb
  have hnull : ∀ᶠ n in atTop, P {ω | ε ≤ dist (Z n ω) 0} = 0 := by
    filter_upwards [hsmall] with n hn
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.mp (hZ n))
    have hω' : ε ≤ dist (Z n ω) 0 := hω
    rw [Real.dist_eq, sub_zero] at hω'
    intro hcon
    linarith
  exact Tendsto.congr' (hnull.mono fun n hn => hn.symm) tendsto_const_nhds

/-- Domination: if `|Z_n| ≤ |Y_n|` almost everywhere and `Y_n ⟶^p 0`, then `Z_n ⟶^p 0`. -/
theorem tendstoInProb_zero_of_abs_le {Z Y : ℕ → Ω → ℝ}
    (hle : ∀ n, ∀ᵐ ω ∂P, |Z n ω| ≤ |Y n ω|)
    (hY : TendstoInMeasure P Y atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P Z atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist] at hY ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hY ε hε)
    (fun n => zero_le) (fun n => ?_)
  refine measure_mono_ae ?_
  filter_upwards [hle n] with ω hω hmem
  have h1 : ε ≤ dist (Z n ω) 0 := hmem
  show ε ≤ dist (Y n ω) 0
  rw [Real.dist_eq, sub_zero] at h1 ⊢
  exact h1.trans hω

/-- **Markov's inequality along the sequence.** A first-moment bound by a null sequence gives
convergence in probability. The bound is stated for the Lebesgue integral in `ℝ≥0∞`, so no
integrability hypothesis enters. -/
theorem tendstoInProb_zero_of_lintegral_le {Z : ℕ → Ω → ℝ}
    (hmeas : ∀ n, AEMeasurable (Z n) P) {c : ℕ → ℝ≥0∞}
    (hle : ∀ n, ∫⁻ ω, ‖Z n ω‖ₑ ∂P ≤ c n) (hc : Tendsto c atTop (𝓝 0)) :
    TendstoInMeasure P Z atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_enorm]
  intro ε hε hεtop
  have hstep : ∀ n, P {ω | ε ≤ ‖Z n ω - (fun _ => (0 : ℝ)) ω‖ₑ} ≤ c n / ε := by
    intro n
    have hset : {ω | ε ≤ ‖Z n ω - (fun _ => (0 : ℝ)) ω‖ₑ} = {ω | ε ≤ ‖Z n ω‖ₑ} := by
      simp
    rw [hset]
    exact le_trans (meas_ge_le_lintegral_div (hmeas n).enorm hε.ne' hεtop)
      (ENNReal.div_le_div_right (hle n) ε)
  have hdiv : Tendsto (fun n => c n / ε) atTop (𝓝 0) := by
    simp_rw [div_eq_mul_inv]
    have h := ENNReal.Tendsto.mul_const hc (Or.inr (ENNReal.inv_ne_top.mpr hε.ne'))
    simpa using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiv
    (fun n => zero_le) hstep

/-- The Bochner-integral form of `tendstoInProb_zero_of_lintegral_le`. -/
theorem tendstoInProb_zero_of_integral_abs_le {Z : ℕ → Ω → ℝ}
    (hint : ∀ n, Integrable (Z n) P) {c : ℕ → ℝ}
    (hle : ∀ n, ∫ ω, |Z n ω| ∂P ≤ c n) (hc : Tendsto c atTop (𝓝 0)) :
    TendstoInMeasure P Z atTop (fun _ => (0 : ℝ)) := by
  refine tendstoInProb_zero_of_lintegral_le (fun n => (hint n).aemeasurable)
    (c := fun n => ENNReal.ofReal (c n)) (fun n => ?_) ?_
  · have h1 : ENNReal.ofReal (∫ ω, ‖Z n ω‖ ∂P) = ∫⁻ ω, ‖Z n ω‖ₑ ∂P :=
      ofReal_integral_norm_eq_lintegral_enorm (hint n)
    rw [← h1]
    refine ENNReal.ofReal_le_ofReal ?_
    simpa [Real.norm_eq_abs] using hle n
  · simpa using ENNReal.tendsto_ofReal hc

/-- `W_n = O_p(1)`: stochastic boundedness, uniform in `n`. -/
def BddInProb (P : Measure Ω) (W : ℕ → Ω → ℝ) : Prop :=
  ∀ δ : ℝ≥0∞, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∀ n, P {ω | C ≤ |W n ω|} ≤ δ

/-- **Markov's inequality gives `O_p(1)`.** A first moment bounded uniformly in `n` by a
finite constant implies stochastic boundedness. -/
theorem bddInProb_of_lintegral_le {W : ℕ → Ω → ℝ} (hmeas : ∀ n, AEMeasurable (W n) P)
    {M : ℝ≥0∞} (hM : M ≠ ⊤) (hle : ∀ n, ∫⁻ ω, ‖W n ω‖ₑ ∂P ≤ M) :
    BddInProb P W := by
  intro δ hδ
  by_cases hδtop : δ = ⊤
  · exact ⟨1, one_pos, fun n => by simp [hδtop]⟩
  · set E : ℝ≥0∞ := (M + 1) * δ⁻¹ with hEdef
    have hM1 : M + 1 ≠ 0 := by simp
    have hE0 : E ≠ 0 := mul_ne_zero hM1 (ENNReal.inv_ne_zero.mpr hδtop)
    have hEtop : E ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp [hM]) (ENNReal.inv_ne_top.mpr hδ.ne')
    have hEδ : E * δ = M + 1 := by
      rw [hEdef, mul_assoc, ENNReal.inv_mul_cancel hδ.ne' hδtop, mul_one]
    refine ⟨E.toReal, ENNReal.toReal_pos hE0 hEtop, fun n => ?_⟩
    have hsetE : {ω | E.toReal ≤ |W n ω|} = {ω | E ≤ ‖W n ω‖ₑ} := by
      ext ω
      show E.toReal ≤ |W n ω| ↔ E ≤ ‖W n ω‖ₑ
      rw [Real.enorm_eq_ofReal_abs]
      exact (ENNReal.le_ofReal_iff_toReal_le hEtop (abs_nonneg _)).symm
    rw [hsetE]
    by_contra hcon
    have hcon' : δ < P {ω | E ≤ ‖W n ω‖ₑ} := not_le.mp hcon
    have hmul : δ * E < P {ω | E ≤ ‖W n ω‖ₑ} * E :=
      ENNReal.mul_lt_mul_left hE0 hEtop hcon'
    have hmk : E * P {ω | E ≤ ‖W n ω‖ₑ} ≤ M :=
      le_trans (mul_meas_ge_le_lintegral₀ (hmeas n).enorm E) (hle n)
    rw [mul_comm δ E, hEδ] at hmul
    rw [mul_comm] at hmk
    exact absurd (lt_of_lt_of_le hmul hmk) (not_lt.mpr (le_of_lt (ENNReal.lt_add_right hM
      one_ne_zero)))

/-- **`o(1) · O_p(1) = o_p(1)`.** A sequence dominated by a vanishing deterministic factor
times a stochastically bounded one converges in probability to zero. -/
theorem tendstoInProb_zero_of_bddInProb_mul {Z W : ℕ → Ω → ℝ} {k : ℕ → ℝ}
    (hk0 : ∀ n, 0 ≤ k n) (hle : ∀ n, ∀ᵐ ω ∂P, |Z n ω| ≤ k n * |W n ω|)
    (hW : BddInProb P W) (hk : Tendsto k atTop (𝓝 0)) :
    TendstoInMeasure P Z atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨C, hC0, hCb⟩ := hW δ hδ
  have hmulC : Tendsto (fun n => k n * C) atTop (𝓝 0) := by
    simpa using hk.mul_const C
  filter_upwards [Filter.Tendsto.eventually_lt_const hε hmulC] with n hn
  refine le_trans (measure_mono_ae ?_) (hCb n)
  filter_upwards [hle n] with ω hω hmem
  have hmem' : ε ≤ dist (Z n ω) 0 := hmem
  rw [Real.dist_eq, sub_zero] at hmem'
  show C ≤ |W n ω|
  by_contra hlt
  have hlt' : |W n ω| < C := not_le.mp hlt
  have h1 : k n * |W n ω| ≤ k n * C := mul_le_mul_of_nonneg_left hlt'.le (hk0 n)
  linarith

/-! ### Random null factors and closure laws

Closure laws for `⟶^p 0` and `O_p(1)`: sums, products with a random null factor, square roots
and constant multiples, assembled in `tendstoInProb_zero_of_le_sqrt_mul`.
-/

/-- **`o_p(1) + o_p(1) = o_p(1)`, in domination form.** A sequence dominated almost everywhere
by the sum of two null sequences is null. -/
theorem tendstoInProb_zero_of_abs_le_add {Z Y W : ℕ → Ω → ℝ}
    (hle : ∀ n, ∀ᵐ ω ∂P, |Z n ω| ≤ |Y n ω| + |W n ω|)
    (hY : TendstoInMeasure P Y atTop (fun _ => (0 : ℝ)))
    (hW : TendstoInMeasure P W atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P Z atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist] at hY hW ⊢
  intro ε hε
  have hhalf : (0 : ℝ) < ε / 2 := by linarith
  have hsum : Tendsto (fun n => P {ω | ε / 2 ≤ dist (Y n ω) ((fun _ => (0 : ℝ)) ω)}
      + P {ω | ε / 2 ≤ dist (W n ω) ((fun _ => (0 : ℝ)) ω)}) atTop (𝓝 0) := by
    simpa using (hY (ε / 2) hhalf).add (hW (ε / 2) hhalf)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun n => ?_)
  refine le_trans (measure_mono_ae ?_) (measure_union_le _ _)
  filter_upwards [hle n] with ω hω hmem
  simp only [Set.mem_union, Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at hmem ⊢
  by_contra hc
  rw [not_or, not_le, not_le] at hc
  linarith [hc.1, hc.2]

/-- **`o_p(1) · O_p(1) = o_p(1)`.** If `|Z_n| ≤ |S_n||W_n|` almost everywhere,
`S_n ⟶^p 0` and `W_n = O_p(1)`, then `Z_n ⟶^p 0`. The proof uses
`{ε ≤ |Z_n|} ⊆ {ε/C ≤ |S_n|} ∪ {C ≤ |W_n|}` with `C` chosen from the bound on `W_n`. -/
theorem tendstoInProb_zero_of_mul_bddInProb {Z S W : ℕ → Ω → ℝ}
    (hle : ∀ n, ∀ᵐ ω ∂P, |Z n ω| ≤ |S n ω| * |W n ω|)
    (hS : TendstoInMeasure P S atTop (fun _ => (0 : ℝ)))
    (hW : BddInProb P W) :
    TendstoInMeasure P Z atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist] at hS ⊢
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨C, hC0, hCb⟩ := hW (δ / 2) (ENNReal.half_pos hδ.ne')
  have hεC : (0 : ℝ) < ε / C := div_pos hε hC0
  have hSsmall : ∀ᶠ n in atTop,
      P {ω | ε / C ≤ dist (S n ω) ((fun _ => (0 : ℝ)) ω)} ≤ δ / 2 :=
    (ENNReal.tendsto_nhds_zero.mp (hS (ε / C) hεC)) (δ / 2) (ENNReal.half_pos hδ.ne')
  filter_upwards [hSsmall] with n hn
  have hsub : P {ω | ε ≤ dist (Z n ω) ((fun _ => (0 : ℝ)) ω)}
      ≤ P {ω | ε / C ≤ dist (S n ω) ((fun _ => (0 : ℝ)) ω)} + P {ω | C ≤ |W n ω|} := by
    refine le_trans (measure_mono_ae ?_) (measure_union_le _ _)
    filter_upwards [hle n] with ω hω hmem
    simp only [Set.mem_union, Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at hmem ⊢
    by_contra hc
    rw [not_or, not_le, not_le] at hc
    obtain ⟨h1, h2⟩ := hc
    have h3 : |S n ω| * |W n ω| ≤ |S n ω| * C :=
      mul_le_mul_of_nonneg_left h2.le (abs_nonneg _)
    have h4 : |S n ω| * C < ε / C * C := mul_lt_mul_of_pos_right h1 hC0
    have h5 : ε / C * C = ε := by field_simp
    linarith
  calc P {ω | ε ≤ dist (Z n ω) ((fun _ => (0 : ℝ)) ω)}
      ≤ P {ω | ε / C ≤ dist (S n ω) ((fun _ => (0 : ℝ)) ω)} + P {ω | C ≤ |W n ω|} := hsub
    _ ≤ δ / 2 + δ / 2 := add_le_add hn (hCb n)
    _ = δ := ENNReal.add_halves δ

/-- `S_n ⟶^p 0` implies `√S_n ⟶^p 0`; no nonnegativity is needed since `Real.sqrt`
vanishes on `(-∞, 0]`. -/
theorem tendstoInProb_sqrt_zero {S : ℕ → Ω → ℝ}
    (hS : TendstoInMeasure P S atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P (fun n ω => Real.sqrt (S n ω)) atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist] at hS ⊢
  intro ε hε
  have hsq : (0 : ℝ) < ε ^ 2 := by positivity
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hS (ε ^ 2) hsq)
    (fun _ => zero_le) (fun n => measure_mono (fun ω hω => ?_))
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at hω ⊢
  rw [abs_of_nonneg (Real.sqrt_nonneg _)] at hω
  have hsqle : ε ^ 2 ≤ Real.sqrt (S n ω) ^ 2 := by
    nlinarith [Real.sqrt_nonneg (S n ω)]
  rw [Real.sq_sqrt'] at hsqle
  exact hsqle.trans (max_le (le_abs_self _) (abs_nonneg _))

/-- A uniformly bounded sequence is `O_p(1)`. -/
theorem bddInProb_of_abs_le_const {W : ℕ → Ω → ℝ} {M : ℝ}
    (hM : ∀ n, ∀ᵐ ω ∂P, |W n ω| ≤ M) : BddInProb P W := by
  intro δ hδ
  refine ⟨|M| + 1, by positivity, fun n => ?_⟩
  have hnull : P {ω | |M| + 1 ≤ |W n ω|} = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.mp (hM n))
    have h1 : |M| + 1 ≤ |W n ω| := hω
    intro hcon
    have h2 : M ≤ |M| := le_abs_self M
    linarith
  rw [hnull]
  exact zero_le

/-- `W_n = O_p(1)` implies `√W_n = O_p(1)`, with `√C` as the new threshold. -/
theorem bddInProb_sqrt {W : ℕ → Ω → ℝ} (hW : BddInProb P W) :
    BddInProb P (fun n ω => Real.sqrt (W n ω)) := by
  intro δ hδ
  obtain ⟨C, hC0, hCb⟩ := hW δ hδ
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC0, fun n => ?_⟩
  refine le_trans (measure_mono (fun ω hω => ?_)) (hCb n)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [abs_of_nonneg (Real.sqrt_nonneg _)] at hω
  have h1 : Real.sqrt C ^ 2 ≤ Real.sqrt (W n ω) ^ 2 := by
    nlinarith [Real.sqrt_nonneg C, Real.sqrt_nonneg (W n ω)]
  rw [Real.sq_sqrt hC0.le, Real.sq_sqrt'] at h1
  exact h1.trans (max_le (le_abs_self _) (abs_nonneg _))

/-- `W_n = O_p(1)` implies `rW_n = O_p(1)` for a real constant `r`, with threshold
`(|r|+1)C`. -/
theorem bddInProb_const_mul (r : ℝ) {W : ℕ → Ω → ℝ} (hW : BddInProb P W) :
    BddInProb P (fun n ω => r * W n ω) := by
  intro δ hδ
  obtain ⟨C, hC0, hCb⟩ := hW δ hδ
  refine ⟨(|r| + 1) * C, mul_pos (by positivity) hC0, fun n => ?_⟩
  refine le_trans (measure_mono (fun ω hω => ?_)) (hCb n)
  simp only [Set.mem_ofPred_eq, abs_mul] at hω ⊢
  by_contra hc
  rw [not_le] at hc
  have h1 : |r| * |W n ω| ≤ |r| * C := mul_le_mul_of_nonneg_left hc.le (abs_nonneg r)
  have h2 : (|r| + 1) * C = |r| * C + C := by ring
  linarith

/-- **Cross-term rule.** `κ√(S_nT_n) ⟶^p 0` when `S_n ⟶^p 0` and `T_n = O_p(1)`, via
`√(S_nT_n) = √S_n·√T_n`. -/
theorem tendstoInProb_zero_of_le_sqrt_mul {Z S T : ℕ → Ω → ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hS0 : ∀ n, ∀ᵐ ω ∂P, 0 ≤ S n ω)
    (hle : ∀ n, ∀ᵐ ω ∂P, |Z n ω| ≤ κ * Real.sqrt (S n ω * T n ω))
    (hS : TendstoInMeasure P S atTop (fun _ => (0 : ℝ)))
    (hT : BddInProb P T) :
    TendstoInMeasure P Z atTop (fun _ => (0 : ℝ)) := by
  refine tendstoInProb_zero_of_mul_bddInProb
    (S := fun n ω => Real.sqrt (S n ω)) (W := fun n ω => κ * Real.sqrt (T n ω))
    (fun n => ?_) (tendstoInProb_sqrt_zero hS) (bddInProb_const_mul κ (bddInProb_sqrt hT))
  filter_upwards [hS0 n, hle n] with ω h0 hω
  show |Z n ω| ≤ |Real.sqrt (S n ω)| * |κ * Real.sqrt (T n ω)|
  rw [Real.sqrt_mul h0] at hω
  rw [abs_of_nonneg (Real.sqrt_nonneg (S n ω)), abs_mul, abs_of_nonneg hκ,
    abs_of_nonneg (Real.sqrt_nonneg (T n ω))]
  calc |Z n ω| ≤ κ * (Real.sqrt (S n ω) * Real.sqrt (T n ω)) := hω
    _ = Real.sqrt (S n ω) * (κ * Real.sqrt (T n ω)) := by ring

end InProb

/-! ## The conditional entry point

`𝒟` is declared first and explicitly, so that instance resolution for `MeasurableSpace Ω`
finds the ambient `mΩ`.
-/

section Conditional

variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- A bound `E[|Z_n| | 𝒟] ≤ c_n` by real constants `c_n → 0` gives `Z_n ⟶^p 0`, by the
tower property and Markov's inequality. -/
theorem tendstoInProb_zero_of_condExp_abs_le [IsProbabilityMeasure P]
    {Z : ℕ → Ω → ℝ} (hm : 𝒟 ≤ mΩ) [SigmaFinite (P.trim hm)]
    (hint : ∀ n, Integrable (Z n) P) {c : ℕ → ℝ}
    (hle : ∀ n, (P[fun ω => |Z n ω| | 𝒟]) ≤ᵐ[P] fun _ => c n)
    (hc : Tendsto c atTop (𝓝 0)) :
    TendstoInMeasure P Z atTop (fun _ => (0 : ℝ)) := by
  refine tendstoInProb_zero_of_integral_abs_le hint (fun n => ?_) hc
  have h1 : ∫ ω, (P[fun ω => |Z n ω| | 𝒟]) ω ∂P = ∫ ω, |Z n ω| ∂P := integral_condExp hm
  rw [← h1]
  refine le_trans (integral_mono_ae integrable_condExp (integrable_const _) (hle n)) ?_
  simp

end Conditional

/-! ## The limit in Lemma SM.B.8(b)

`‖Ξ_n‖/n → 0` over an indexed family of designs, deduced from the finite-sample bound
`Cgm.xiMat_opNorm_le`. The rate conditions are `hA`: `(d_[Δ]−N_m)G^{(m)}_max = o(n)`,
`hL`: `K G^{(m)}_max = o(n)`, and `hT`: `tr(Π_n)/n → 0`.
-/

section CgmLimit

/-- The majorant delivered by `Cgm.xiMat_opNorm_le`, divided by `n`. -/
noncomputable def xiBound (B aT lT tT G N : ℝ) : ℝ :=
  B ^ 2 * (Real.sqrt (aT * (G * N)) + Real.sqrt (lT * (G * N)) + tT) / N

/-- The majorant is null under the three rate conditions. -/
theorem tendsto_xiBound {B : ℝ} {aT lT tT G N : ℕ → ℝ}
    (haT : ∀ j, 0 ≤ aT j) (hlT : ∀ j, 0 ≤ lT j) (hG : ∀ j, 0 ≤ G j) (hN : ∀ j, 0 < N j)
    (hA : Tendsto (fun j => aT j * G j / N j) atTop (𝓝 0))
    (hL : Tendsto (fun j => lT j * G j / N j) atTop (𝓝 0))
    (hT : Tendsto (fun j => tT j / N j) atTop (𝓝 0)) :
    Tendsto (fun j => xiBound B (aT j) (lT j) (tT j) (G j) (N j)) atTop (𝓝 0) := by
  have hsplit : ∀ j, xiBound B (aT j) (lT j) (tT j) (G j) (N j)
      = B ^ 2 * (Real.sqrt (aT j * (G j * N j)) / N j
          + Real.sqrt (lT j * (G j * N j)) / N j + tT j / N j) := by
    intro j
    rw [xiBound, mul_div_assoc, add_div, add_div]
  simp only [hsplit]
  have hsa := tendsto_sqrt_mul_div haT hG hN hA
  have hsl := tendsto_sqrt_mul_div hlT hG hN hL
  simpa using ((hsa.add hsl).add hT).const_mul (B ^ 2)

variable {D O L N K : ℕ → Type*}
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
  [∀ j, Fintype (K j)] [∀ j, DecidableEq (K j)]
  [∀ j, Fintype (N j)] [∀ j, DecidableEq (N j)]
  [∀ j, DecidableEq (D j)] [∀ j, DecidableEq (L j)]

omit [∀ j, DecidableEq (D j)] in
/-- **Lemma SM.B.8(b), limit.** `‖Ξ_n‖/n → 0` under the hypotheses of `Cgm.xiMat_opNorm_le`
for each `j` and the three rate conditions. `hGnn` requires `0 ≤ G^{(m)}_max`. -/
theorem tendsto_xiMat_div_card
    (c : ∀ j, D j → O j → L j) (dims : ∀ j, Finset (D j)) (hdims : ∀ j, (dims j).Nonempty)
    (i : ∀ j, O j → N j)
    (hlink : ∀ j, ∀ o o' : O j, Linked (c j) (dims j) o o' ↔ i j o = i j o')
    (x : ∀ j, Matrix (O j) (K j) ℝ) {R Pi Pm A Lam : ∀ j, Matrix (O j) (O j) ℝ}
    (hPi : ∀ j, Pi j = 1 - R j) (hdecomp : ∀ j, Pi j = Pm j + A j + Lam j)
    (hPm : ∀ j, ∀ o o' : O j,
      Pm j o o' = if i j o = i j o' then ((Cgm.clusterCard (i j) (i j o) : ℝ))⁻¹ else 0)
    (hAsym : ∀ j, (A j)ᵀ = A j) (hAidem : ∀ j, A j * A j = A j)
    (hLsym : ∀ j, (Lam j)ᵀ = Lam j) (hLidem : ∀ j, Lam j * Lam j = Lam j)
    (hXcl : ∀ j, ∀ (t : N j) (k : K j),
      ∑ o ∈ Finset.univ.filter (fun o : O j => i j o = t), x j o k = 0)
    {B : ℝ} {Gmax : ℕ → ℝ}
    (hB : ∀ j, ∀ o : O j, ∑ k : K j, x j o k ^ 2 ≤ B ^ 2)
    (hG : ∀ j, ∀ t : N j, ((Cgm.clusterCard (i j) t : ℝ)) ≤ Gmax j)
    (hGnn : ∀ j, 0 ≤ Gmax j) (hcard : ∀ j, 0 < (Fintype.card (O j) : ℝ))
    (hA : Tendsto (fun j => (A j).trace * Gmax j / (Fintype.card (O j) : ℝ)) atTop (𝓝 0))
    (hL : Tendsto (fun j => (Lam j).trace * Gmax j / (Fintype.card (O j) : ℝ)) atTop (𝓝 0))
    (hT : Tendsto (fun j => (Pi j).trace / (Fintype.card (O j) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun j => ‖Cgm.xiMat (c j) (dims j) (R j) (x j)‖ / (Fintype.card (O j) : ℝ))
      atTop (𝓝 0) := by
  have haT : ∀ j, 0 ≤ (A j).trace := fun j => Cgm.trace_nonneg_of_symmProj (hAsym j) (hAidem j)
  have hlT : ∀ j, 0 ≤ (Lam j).trace :=
    fun j => Cgm.trace_nonneg_of_symmProj (hLsym j) (hLidem j)
  refine tendsto_zero_of_le (fun j => div_nonneg (norm_nonneg _) (hcard j).le) (fun j => ?_)
    (tendsto_xiBound (B := B) haT hlT hGnn hcard hA hL hT)
  have hfs := Cgm.xiMat_opNorm_le (c j) (hdims j) (i j) (hlink j) (x j) (hPi j) (hdecomp j)
    (hPm j) (hAsym j) (hAidem j) (hLsym j) (hLidem j) (hXcl j) (hB j) (hG j)
  rw [xiBound]
  gcongr

omit [∀ j, DecidableEq (D j)] in
/-- **Lemma SM.B.8(b), limit in probability.** For a random regressor matrix satisfying the
design bounds almost everywhere, `‖Ξ_n‖/n ⟶^p 0`. The fixed-effect projectors are
nonrandom. -/
theorem tendstoInProb_xiMat_div_card {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (c : ∀ j, D j → O j → L j) (dims : ∀ j, Finset (D j)) (hdims : ∀ j, (dims j).Nonempty)
    (i : ∀ j, O j → N j)
    (hlink : ∀ j, ∀ o o' : O j, Linked (c j) (dims j) o o' ↔ i j o = i j o')
    (x : ∀ j, Ω → Matrix (O j) (K j) ℝ) {R Pi Pm A Lam : ∀ j, Matrix (O j) (O j) ℝ}
    (hPi : ∀ j, Pi j = 1 - R j) (hdecomp : ∀ j, Pi j = Pm j + A j + Lam j)
    (hPm : ∀ j, ∀ o o' : O j,
      Pm j o o' = if i j o = i j o' then ((Cgm.clusterCard (i j) (i j o) : ℝ))⁻¹ else 0)
    (hAsym : ∀ j, (A j)ᵀ = A j) (hAidem : ∀ j, A j * A j = A j)
    (hLsym : ∀ j, (Lam j)ᵀ = Lam j) (hLidem : ∀ j, Lam j * Lam j = Lam j)
    (hXcl : ∀ j, ∀ᵐ ω ∂P, ∀ (t : N j) (k : K j),
      ∑ o ∈ Finset.univ.filter (fun o : O j => i j o = t), x j ω o k = 0)
    {B : ℝ} {Gmax : ℕ → ℝ}
    (hB : ∀ j, ∀ᵐ ω ∂P, ∀ o : O j, ∑ k : K j, x j ω o k ^ 2 ≤ B ^ 2)
    (hG : ∀ j, ∀ t : N j, ((Cgm.clusterCard (i j) t : ℝ)) ≤ Gmax j)
    (hGnn : ∀ j, 0 ≤ Gmax j) (hcard : ∀ j, 0 < (Fintype.card (O j) : ℝ))
    (hA : Tendsto (fun j => (A j).trace * Gmax j / (Fintype.card (O j) : ℝ)) atTop (𝓝 0))
    (hL : Tendsto (fun j => (Lam j).trace * Gmax j / (Fintype.card (O j) : ℝ)) atTop (𝓝 0))
    (hT : Tendsto (fun j => (Pi j).trace / (Fintype.card (O j) : ℝ)) atTop (𝓝 0)) :
    TendstoInMeasure P
      (fun j ω => ‖Cgm.xiMat (c j) (dims j) (R j) (x j ω)‖ / (Fintype.card (O j) : ℝ))
      atTop (fun _ => (0 : ℝ)) := by
  have haT : ∀ j, 0 ≤ (A j).trace := fun j => Cgm.trace_nonneg_of_symmProj (hAsym j) (hAidem j)
  have hlT : ∀ j, 0 ≤ (Lam j).trace :=
    fun j => Cgm.trace_nonneg_of_symmProj (hLsym j) (hLidem j)
  refine tendstoInProb_zero_of_abs_le_const (b := fun j =>
      xiBound B ((A j).trace) ((Lam j).trace) ((Pi j).trace) (Gmax j)
        ((Fintype.card (O j) : ℝ))) (fun j => ?_)
    (tendsto_xiBound (B := B) haT hlT hGnn hcard hA hL hT)
  filter_upwards [hXcl j, hB j] with ω hxcl hb
  have hfs := Cgm.xiMat_opNorm_le (c j) (hdims j) (i j) (hlink j) (x j ω) (hPi j) (hdecomp j)
    (hPm j) (hAsym j) (hAidem j) (hLsym j) (hLidem j) hxcl hb (hG j)
  rw [abs_of_nonneg (div_nonneg (norm_nonneg _) (hcard j).le), xiBound]
  gcongr

end CgmLimit

/-! ## Witness for `tendsto_xiMat_div_card`

`𝒪_j = {1,…,j+1} × {1,2}` with a single cluster, `K = 1`, `x̃_{(o,s)} = ±1` according to `s`,
`P_m = (2(j+1))^{-1}ιι'`, `Π = P_m`, `A^{(m)} = Λ = 0`, `R = I − P_m`, `B = 1` and
`G^{(m)}_max = 2(j+1)`. Since `tr(Π_n) = 1`, the rate `tr(Π_n)/n → 0` holds because the design
grows.
-/

section Witness

/-- The `P_m` of the witness at index `j`: a single cluster of size `2(j+1)`, every entry
equal to `(2(j+1))^{-1}`. -/
noncomputable def witnessPm (j : ℕ) : Matrix (Fin (j + 1) × Fin 2) (Fin (j + 1) × Fin 2) ℝ :=
  Matrix.of fun _ _ => ((2 * (j + 1) : ℕ) : ℝ)⁻¹

/-- The within regressors of the witness at index `j`: `+1` and `−1` on each pair, so they
sum to zero over the cluster. -/
def witnessX (j : ℕ) : Matrix (Fin (j + 1) × Fin 2) (Fin 1) ℝ :=
  Matrix.of fun o _ => if o.2 = 0 then 1 else -1

/-- The witness's cluster has `2(j+1)` members. -/
theorem witness_clusterCard (j : ℕ) :
    Cgm.clusterCard (fun _ : Fin (j + 1) × Fin 2 => (0 : Fin 1)) 0 = 2 * (j + 1) := by
  rw [Cgm.clusterCard, Finset.filter_true_of_mem (fun _ _ => rfl)]
  simp [Finset.card_univ, Nat.mul_comm]

/-- The witness's `tr(Π_n)` is `1` at every index. -/
theorem witness_trace (j : ℕ) : (witnessPm j).trace = 1 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, witnessPm, Matrix.of_apply, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  have hc : (Fintype.card (Fin (j + 1) × Fin 2) : ℝ) = ((2 * (j + 1) : ℕ) : ℝ) := by
    simp [Nat.mul_comm]
  rw [hc]
  refine mul_inv_cancel₀ ?_
  positivity

/-- The hypotheses of `tendsto_xiMat_div_card` are jointly satisfiable. -/
theorem tendsto_xiMat_div_card_witness :
    Tendsto (fun j : ℕ =>
        ‖Cgm.xiMat (fun _ _ => (0 : Fin 1)) ({0} : Finset (Fin 1))
            (1 - witnessPm j) (witnessX j)‖ / (Fintype.card (Fin (j + 1) × Fin 2) : ℝ))
      atTop (𝓝 0) := by
  have hcardR : ∀ j : ℕ, (Fintype.card (Fin (j + 1) × Fin 2) : ℝ) = 2 * ((j : ℝ) + 1) := by
    intro j
    simp [Fintype.card_prod]
    ring
  have hpos : ∀ j : ℕ, 0 < (Fintype.card (Fin (j + 1) × Fin 2) : ℝ) := by
    intro j
    rw [hcardR j]
    positivity
  have hgrow : Tendsto (fun j : ℕ => 2 * ((j : ℝ) + 1)) atTop atTop := by
    refine Filter.tendsto_atTop_mono (fun j => ?_) tendsto_natCast_atTop_atTop
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hinv : Tendsto (fun j : ℕ => (2 * ((j : ℝ) + 1))⁻¹) atTop (𝓝 0) :=
    hgrow.inv_tendsto_atTop
  refine tendsto_xiMat_div_card (D := fun _ => Fin 1) (O := fun j => Fin (j + 1) × Fin 2)
    (L := fun _ => Fin 1) (N := fun _ => Fin 1) (K := fun _ => Fin 1)
    (fun _ _ _ => (0 : Fin 1)) (fun _ => ({0} : Finset (Fin 1)))
    (fun _ => Finset.singleton_nonempty 0) (fun _ _ => (0 : Fin 1)) ?_ witnessX
    (R := fun j => 1 - witnessPm j) (Pi := witnessPm) (Pm := witnessPm)
    (A := fun _ => 0) (Lam := fun _ => 0) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (B := 1)
    (Gmax := fun j => 2 * ((j : ℝ) + 1)) ?_ ?_ ?_ hpos ?_ ?_ ?_
  · exact fun j o o' => ⟨fun _ => rfl, fun _ => ⟨0, Finset.mem_singleton_self 0, rfl⟩⟩
  · exact fun j => (sub_sub_cancel _ _).symm
  · exact fun j => by rw [add_zero, add_zero]
  · intro j o o'
    rw [witnessPm]
    simp [witness_clusterCard j]
  · exact fun _ => Matrix.transpose_zero
  · exact fun _ => Matrix.zero_mul 0
  · exact fun _ => Matrix.transpose_zero
  · exact fun _ => Matrix.zero_mul 0
  · intro j t k
    have hfil : (Finset.univ.filter (fun o : Fin (j + 1) × Fin 2 => (0 : Fin 1) = t))
        = (Finset.univ : Finset (Fin (j + 1) × Fin 2)) :=
      Finset.filter_true_of_mem fun _ _ => Subsingleton.elim _ _
    rw [hfil, Fintype.sum_prod_type]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Fin.sum_univ_two]
    simp [witnessX]
  · intro j o
    rw [Fin.sum_univ_one]
    simp only [witnessX, Matrix.of_apply]
    split_ifs <;> norm_num
  · intro j t
    have ht : t = 0 := Subsingleton.elim _ _
    subst ht
    rw [witness_clusterCard j]
    push_cast
    linarith
  · intro j
    positivity
  · simp only [Matrix.trace_zero, zero_mul, zero_div]
    exact tendsto_const_nhds
  · simp only [Matrix.trace_zero, zero_mul, zero_div]
    exact tendsto_const_nhds
  · simp only [witness_trace]
    refine hinv.congr fun j => ?_
    rw [hcardR j, one_div]

end Witness

/-! ## Witness for `tendstoInProb_zero_of_le_sqrt_mul`

On a point mass, with `S_n(ω) = (1 + |ω|/(1+|ω|))/(n+1)` and `T_n ≡ 2`, the quantity
`√(2S_n)` equals `√(2/(n+1))` at the atom.
-/

section SqrtWitness

/-- The null factor of the witness, bounded by `2/(n+1)` for every `ω`. -/
noncomputable def witnessS (n : ℕ) (ω : ℝ) : ℝ := (1 + |ω| / (1 + |ω|)) / ((n : ℝ) + 1)

theorem witnessS_nonneg (n : ℕ) (ω : ℝ) : 0 ≤ witnessS n ω := by
  rw [witnessS]
  positivity

theorem witnessS_le (n : ℕ) (ω : ℝ) : witnessS n ω ≤ 2 / ((n : ℝ) + 1) := by
  have hb : |ω| / (1 + |ω|) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [abs_nonneg ω]
  rw [witnessS]
  gcongr
  linarith

/-- `S_n(0) = (n+1)^{-1}`. -/
theorem witnessS_at_zero (n : ℕ) : witnessS n 0 = ((n : ℝ) + 1)⁻¹ := by
  rw [witnessS]
  norm_num

/-- The hypotheses of `tendstoInProb_zero_of_le_sqrt_mul` are jointly satisfiable. -/
theorem tendstoInProb_zero_of_le_sqrt_mul_witness :
    TendstoInMeasure (Measure.dirac (0 : ℝ))
      (fun (n : ℕ) (ω : ℝ) => Real.sqrt (witnessS n ω * 2)) atTop (fun _ => (0 : ℝ)) := by
  have hbase : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h2 : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa using h.const_mul 2
    exact h2.congr fun n => by rw [div_eq_mul_inv]
  have hS : TendstoInMeasure (Measure.dirac (0 : ℝ)) witnessS atTop (fun _ => (0 : ℝ)) :=
    tendstoInProb_zero_of_abs_le_const
      (fun n => Filter.Eventually.of_forall fun ω => by
        rw [abs_of_nonneg (witnessS_nonneg n ω)]; exact witnessS_le n ω) hbase
  have hT : BddInProb (Measure.dirac (0 : ℝ)) (fun (_ : ℕ) (_ : ℝ) => (2 : ℝ)) := by
    intro δ hδ
    refine ⟨3, by norm_num, fun n => ?_⟩
    have hset : {ω : ℝ | (3 : ℝ) ≤ |(2 : ℝ)|} = (∅ : Set ℝ) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      norm_num
    rw [hset, measure_empty]
    exact zero_le
  refine tendstoInProb_zero_of_le_sqrt_mul (κ := 1) zero_le_one
    (fun n => Filter.Eventually.of_forall fun ω => witnessS_nonneg n ω)
    (fun n => Filter.Eventually.of_forall fun ω => ?_) hS hT
  rw [abs_of_nonneg (Real.sqrt_nonneg _), one_mul]

end SqrtWitness

end Sequence
end Multiway
