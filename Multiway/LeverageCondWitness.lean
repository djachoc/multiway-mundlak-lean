import Multiway.LeverageCondRegime1
import Multiway.Quadform

/-!
# A witness for the exact leverage correction under Regime 1 at a random design

This file exhibits a model satisfying every hypothesis of the Regime 1, random-design forms of
Proposition SM.D.4 (exact leverage correction) and Lemma SM.B.6 (ii)–(iii) proved in
`Multiway.LeverageCondRegime1`, and derives their conclusions through those theorems.

The sample space is `Option 𝒪 → ℝ` with independent fair signs, one per observation and one
(indexed by `none`) for the design; `𝒟` is the σ-field of the design coordinate, a proper
sub-σ-field. The innovations are `ε_o = c_o · sign_o`, so `σ²_ε(o) = c_o²` may be
heteroskedastic, and their mutual conditional independence given `𝒟` is derived. The design
`R` is the identity on one half of the design and the grand-mean projector `P_0` on the other,
so it is random, symmetric idempotent, and has nonzero off-diagonal entries. The signs are
independent of `𝒟`; what depends on `𝒟` is the design `rW` and the weights `wW`.

## Main results

* `prop_lc_a_random_regimeOne_witness`: part (a) of Proposition SM.D.4 on this model.
* `prop_lc_b_random_regimeOne_witness`: part (b), at a constant scaling.
* `prop_lc_heteroskedastic_random_witness`: the instance `𝒪 = Fin 2`, `c = (1, 1/2)`.
-/

namespace Multiway
namespace LeverageCondWitness

open MeasureTheory ProbabilityTheory
open Multiway.GeneralWitness
open Multiway.Quadform.CondIndepWitness

section Model

variable (O : Type*) [Fintype O] [DecidableEq O]

/-! ### The scaled innovations `ε_o = c_o · sign_o` -/

/-- The innovations of the witness: the fair sign at site `o`, scaled by `c_o`, so that
`σ²_ε(o) = c_o²`. -/
noncomputable def epsC (c : O → ℝ) (o : O) (ω : Option O → ℝ) : ℝ := c o * wEps O o ω

omit [Fintype O] [DecidableEq O] in
theorem measurable_epsC (c : O → ℝ) (o : O) : Measurable (epsC O c o) :=
  (measurable_wEps O o).const_mul (c o)

omit [Fintype O] [DecidableEq O] in
theorem abs_epsC_le {c : O → ℝ} (hcb : ∀ o, |c o| ≤ 1) (o : O) (ω : Option O → ℝ) :
    |epsC O c o ω| ≤ 1 := by
  rw [epsC, abs_mul]
  exact abs_mul_le_of (hcb o) (abs_wEps_le O o ω) zero_le_one |>.trans (le_of_eq (one_mul 1))

omit [Fintype O] [DecidableEq O] in
/-- The scaled family generates a smaller σ-algebra than the signs do. -/
theorem epsC_comap_le (c : O → ℝ) (o : O) :
    MeasurableSpace.comap (epsC O c o) inferInstance
      ≤ MeasurableSpace.comap (wEps O o) inferInstance := by
  have h : Measurable[MeasurableSpace.comap (wEps O o) inferInstance] (epsC O c o) :=
    (measurable_const_mul (c o)).comp
      (measurable_iff_comap_le.2 (le_refl
        (MeasurableSpace.comap (wEps O o) (inferInstance : MeasurableSpace ℝ))))
  exact h.comap_le

omit [DecidableEq O] in
theorem epsC_indep (c : O → ℝ) : iIndepFun (epsC O c) (wP O) :=
  (wIndep O).comp (fun o => fun x : ℝ => c o * x) (fun o => measurable_const_mul (c o))

omit [DecidableEq O] in
theorem epsC_indepD (c : O → ℝ) :
    Indep (⨆ o : O, MeasurableSpace.comap (epsC O c o) inferInstance) (wD O) (wP O) :=
  indep_of_indep_of_le_left (wIndepD O)
    (iSup_le fun o => (epsC_comap_le O c o).trans
      (le_iSup (fun o : O => MeasurableSpace.comap (wEps O o) inferInstance) o))

omit [DecidableEq O] in
/-- The innovations are mutually conditionally independent given `𝒟`. -/
theorem epsC_condIndep (c : O → ℝ) :
    iCondIndepFun (wD O) (wD_le O) (epsC O c) (wP O) :=
  Multiway.CondIndep.iCondIndepFun_of_indep (wD O) (measurable_epsC O c) (epsC_indep O c)
    (epsC_indepD O c)

omit [DecidableEq O] in
/-- The innovations have conditional mean zero given `𝒟`. -/
theorem epsC_mean (c : O → ℝ) (o : O) : (wP O)[epsC O c o | wD O] =ᵐ[wP O] 0 := by
  have hs : epsC O c o = (c o) • wEps O o := rfl
  rw [hs]
  filter_upwards [condExp_smul (μ := wP O) (m := wD O) (c o) (wEps O o), wMean O o]
    with ω h1 h2
  rw [h1]
  simp only [Pi.smul_apply, smul_eq_mul]
  simp only [Pi.zero_apply] at h2 ⊢
  rw [h2, mul_zero]

omit [DecidableEq O] in
/-- The signs square to `1` almost everywhere: they are `±1` under the two-point law, and
the truncation `clamp` is the identity there. -/
theorem wEps_sq_ae (o : O) :
    (fun ω => wEps O o ω * wEps O o ω) =ᵐ[wP O] fun _ => (1 : ℝ) := by
  set g : (Option O → ℝ) → ℝ := fun ω => 1 - wEps O o ω * wEps O o ω with hgdef
  have hb : ∀ ω, 0 ≤ g ω ∧ g ω ≤ 1 := by
    intro ω
    have h := abs_le.1 (abs_wEps_le O o ω)
    constructor <;> simp only [hgdef] <;> nlinarith [h.1, h.2, mul_self_nonneg (wEps O o ω)]
  have hmeas : Measurable g :=
    measurable_const.sub ((measurable_wEps O o).mul (measurable_wEps O o))
  have hint : Integrable g (wP O) :=
    integrable_of_bound O hmeas (B := 1) fun ω => by
      rw [abs_of_nonneg (hb ω).1]; exact (hb ω).2
  have hzero : ∫ ω, g ω ∂(wP O) = 0 := by
    have hgi := gintegral (W := Option O) (f := fun x => 1 - clamp x * clamp x)
      (measurable_const.sub (measurable_clamp.mul measurable_clamp)) (some o)
    rw [clamp_one, clamp_neg_one] at hgi
    norm_num at hgi
    simpa [wP, wEps, gU, hgdef] using hgi
  filter_upwards [(integral_eq_zero_iff_of_nonneg (fun ω => (hb ω).1) hint).1 hzero] with ω hω
  have h0 : 1 - wEps O o ω * wEps O o ω = 0 := hω
  linarith

omit [DecidableEq O] in
/-- The conditional variance `Var(ε_o | 𝒟) = σ²_ε(o)` holds with `σ²_ε(o) = c_o²`. -/
theorem epsC_var (c : O → ℝ) (o : O) :
    Var[epsC O c o ; wP O | wD O] =ᵐ[wP O] fun _ => c o ^ 2 := by
  have h1 : (wP O)[fun ω => epsC O c o ω * epsC O c o ω | wD O]
      =ᵐ[wP O] Var[epsC O c o ; wP O | wD O] :=
    LeverageCondRegime1.condExp_mul_self_eq_condVar (wD O) (epsC_mean O c o)
  have h2 : (fun ω => epsC O c o ω * epsC O c o ω)
      =ᵐ[wP O] (fun _ : Option O → ℝ => c o ^ 2) := by
    filter_upwards [wEps_sq_ae O o] with ω hω
    show c o * wEps O o ω * (c o * wEps O o ω) = c o ^ 2
    have hs : wEps O o ω * wEps O o ω = 1 := hω
    nlinarith [hs]
  have h3 : (wP O)[fun ω => epsC O c o ω * epsC O c o ω | wD O]
      =ᵐ[wP O] (wP O)[fun _ : Option O → ℝ => c o ^ 2 | wD O] := condExp_congr_ae h2
  refine h1.symm.trans (h3.trans ?_)
  rw [condExp_const (wD_le O)]

/-! ### The random design `R`

The identity on one half of the design and the grand-mean projector `P_0` on the other. -/

/-- The entries `R_{oo'}` of the witness design: `𝟙{o = o'}` where the design coordinate is
positive and `1/n` where it is not. Both matrices are symmetric idempotent projectors. -/
noncomputable def rW (o o' : O) (ω : Option O → ℝ) : ℝ :=
  if 0 < ω none then (if o = o' then (1 : ℝ) else 0) else (Fintype.card O : ℝ)⁻¹

omit [DecidableEq O] in
theorem card_pos_real (o₀ : O) : (0 : ℝ) < (Fintype.card O : ℝ) := by
  exact_mod_cast Fintype.card_pos_iff.2 ⟨o₀⟩

omit [DecidableEq O] in
theorem one_le_card_real (o₀ : O) : (1 : ℝ) ≤ (Fintype.card O : ℝ) := by
  exact_mod_cast Fintype.card_pos_iff.2 ⟨o₀⟩

theorem stronglyMeasurable_rW (o o' : O) : StronglyMeasurable[wD O] (rW O o o') := by
  have hset : MeasurableSet[wD O] {ω : Option O → ℝ | 0 < ω none} :=
    ⟨Set.Ioi (0 : ℝ), measurableSet_Ioi, rfl⟩
  exact (Measurable.ite (p := fun ω : Option O → ℝ => 0 < ω none) hset
    measurable_const measurable_const).stronglyMeasurable

theorem measurable_rW (o o' : O) : Measurable (rW O o o') :=
  ((stronglyMeasurable_rW O o o').mono (wD_le O)).measurable

theorem abs_rW_le (o₀ o o' : O) (ω : Option O → ℝ) : |rW O o o' ω| ≤ 1 := by
  have hc := one_le_card_real O o₀
  have hcpos := card_pos_real O o₀
  rw [rW]
  split_ifs with h1 h2
  · norm_num
  · norm_num
  · rw [abs_of_nonneg (by positivity)]
    rw [inv_le_one_iff₀]
    exact Or.inr hc

/-- The diagonal of the witness design, with the inner branch resolved: `1` where the design
coordinate is positive and `1/n` where it is not. -/
theorem rW_diag (o : O) (ω : Option O → ℝ) :
    rW O o o ω = if 0 < ω none then (1 : ℝ) else (Fintype.card O : ℝ)⁻¹ := by
  unfold rW
  simp

theorem rW_diag_pos (o₀ o : O) (ω : Option O → ℝ) : 0 < rW O o o ω := by
  rw [rW_diag]
  split_ifs with h1
  · norm_num
  · exact inv_pos.2 (card_pos_real O o₀)

theorem inv_rW_diag_le (o₀ o : O) (ω : Option O → ℝ) :
    (rW O o o ω)⁻¹ ≤ (Fintype.card O : ℝ) := by
  rw [rW_diag]
  split_ifs with h1
  · simpa using one_le_card_real O o₀
  · rw [inv_inv]

/-- `∑_{o'} R²_{oo'} = R_oo` in every realization, for both branches of the design. -/
theorem sum_rW_sq (o₀ o : O) (ω : Option O → ℝ) :
    ∑ o' : O, rW O o o' ω ^ 2 = rW O o o ω := by
  classical
  have hcpos := card_pos_real O o₀
  by_cases h1 : 0 < ω none
  · have hterm : ∀ o' : O, rW O o o' ω ^ 2 = if o' = o then (1 : ℝ) else 0 := by
      intro o'
      unfold rW
      by_cases h2 : o = o'
      · subst h2
        simp [h1]
      · have h3 : ¬ (o' = o) := fun h => h2 h.symm
        simp [h1, h2, h3]
    have hd : rW O o o ω = (1 : ℝ) := by rw [rW_diag]; simp [h1]
    rw [Finset.sum_congr rfl fun o' _ => hterm o',
      Finset.sum_ite_eq' Finset.univ o (fun _ => (1 : ℝ)), hd]
    simp
  · have hterm : ∀ o' : O, rW O o o' ω ^ 2 = ((Fintype.card O : ℝ)⁻¹) ^ 2 := by
      intro o'
      unfold rW
      simp [h1]
    have hd : rW O o o ω = (Fintype.card O : ℝ)⁻¹ := by rw [rW_diag]; simp [h1]
    rw [Finset.sum_congr rfl fun o' _ => hterm o', Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hd, sq, ← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]

/-! ### The residuals and the weights -/

/-- `ν̂_{FE,o} = ∑_{o'} R_{oo'} ε_{o'}`, so that `hres` holds by definition. -/
noncomputable def residW (c : O → ℝ) (o : O) (ω : Option O → ℝ) : ℝ :=
  ∑ o' : O, rW O o o' ω * epsC O c o' ω

theorem measurable_residW (c : O → ℝ) (o : O) : Measurable (residW O c o) :=
  Finset.measurable_sum _ fun o' _ => (measurable_rW O o o').mul (measurable_epsC O c o')

theorem abs_residW_le {c : O → ℝ} (hcb : ∀ o, |c o| ≤ 1) (o₀ o : O) (ω : Option O → ℝ) :
    |residW O c o ω| ≤ (Fintype.card O : ℝ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ o' ∈ (Finset.univ : Finset O),
      |rW O o o' ω * epsC O c o' ω| ≤ (1 : ℝ) := by
    intro o' _
    rw [abs_mul]
    have h := abs_mul_le_of (abs_rW_le O o₀ o o' ω) (abs_epsC_le O hcb o' ω) zero_le_one
    linarith
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- The `𝒟`-measurable weight `x̃_o x̃_o'`, equal to `1 + (design coordinate)`, which is
the diagonal of `wMat`; it takes the values `2` and `0`. -/
noncomputable def wW (o : O) (ω : Option O → ℝ) : ℝ := wMat O ω o o

omit [Fintype O] [DecidableEq O] in
theorem stronglyMeasurable_wW (o : O) : StronglyMeasurable[wD O] (wW O o) :=
  wMeasurableW O o o

omit [Fintype O] [DecidableEq O] in
theorem measurable_wW (o : O) : Measurable (wW O o) :=
  ((stronglyMeasurable_wW O o).mono (wD_le O)).measurable

omit [Fintype O] [DecidableEq O] in
theorem abs_wW_le (o : O) (ω : Option O → ℝ) : |wW O o ω| ≤ 2 := abs_wMat_le O ω o o

/-! ### Integrability side conditions -/

omit [DecidableEq O] in
theorem int_epsC {c : O → ℝ} (hcb : ∀ o, |c o| ≤ 1) (o : O) :
    Integrable (epsC O c o) (wP O) :=
  integrable_of_bound O (measurable_epsC O c o) (B := 1) (abs_epsC_le O hcb o)

omit [DecidableEq O] in
theorem int_epsC_mul {c : O → ℝ} (hcb : ∀ o, |c o| ≤ 1) (o' o'' : O) :
    Integrable (fun ω => epsC O c o' ω * epsC O c o'' ω) (wP O) :=
  integrable_of_bound O ((measurable_epsC O c o').mul (measurable_epsC O c o'')) (B := 1)
    fun ω => by
      rw [abs_mul]
      have h := abs_mul_le_of (abs_epsC_le O hcb o' ω) (abs_epsC_le O hcb o'' ω) zero_le_one
      linarith

theorem int_rr_epsC {c : O → ℝ} (hcb : ∀ o, |c o| ≤ 1) (o₀ o o' o'' : O) :
    Integrable (fun ω => (rW O o o' ω * rW O o o'' ω)
      * (epsC O c o' ω * epsC O c o'' ω)) (wP O) :=
  integrable_of_bound O
    (((measurable_rW O o o').mul (measurable_rW O o o'')).mul
      ((measurable_epsC O c o').mul (measurable_epsC O c o''))) (B := 1)
    fun ω => by
      rw [abs_mul, abs_mul, abs_mul]
      have h1 := abs_mul_le_of (abs_rW_le O o₀ o o' ω) (abs_rW_le O o₀ o o'' ω) zero_le_one
      have h2 := abs_mul_le_of (abs_epsC_le O hcb o' ω) (abs_epsC_le O hcb o'' ω) zero_le_one
      have h3 := mul_le_mul h1 h2 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (by norm_num : (0 : ℝ) ≤ 1 * 1)
      linarith

theorem int_weighted {c : O → ℝ} (hcb : ∀ o, |c o| ≤ 1) (o₀ o : O) :
    Integrable (fun ω => wW O o ω / rW O o o ω * residW O c o ω ^ 2) (wP O) := by
  have hcpos := card_pos_real O o₀
  refine integrable_of_bound O
    (((measurable_wW O o).div (measurable_rW O o o)).mul
      ((measurable_residW O c o).pow_const 2))
    (B := 2 * (Fintype.card O : ℝ) * (Fintype.card O : ℝ) ^ 2) fun ω => ?_
  rw [abs_mul, abs_div]
  have hr := rW_diag_pos O o₀ o ω
  have hrabs : |rW O o o ω| = rW O o o ω := abs_of_pos hr
  have hquot : |wW O o ω| / |rW O o o ω| ≤ 2 * (Fintype.card O : ℝ) := by
    rw [hrabs, div_le_iff₀ hr]
    have h1 := abs_wW_le O o ω
    have h2 : (1 : ℝ) ≤ (Fintype.card O : ℝ) * rW O o o ω := by
      have := inv_rW_diag_le O o₀ o ω
      rw [inv_le_iff_one_le_mul₀ hr] at this
      linarith [this]
    nlinarith [h1, hr, abs_nonneg (wW O o ω)]
  have hsq : |residW O c o ω ^ 2| ≤ (Fintype.card O : ℝ) ^ 2 := by
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ residW O c o ω ^ 2)]
    have h := abs_residW_le O hcb o₀ o ω
    nlinarith [abs_nonneg (residW O c o ω), sq_abs (residW O c o ω)]
  have hnn : (0 : ℝ) ≤ |wW O o ω| / |rW O o o ω| := by positivity
  nlinarith [hquot, hsq, hnn, abs_nonneg (residW O c o ω ^ 2), hcpos]

/-! ### Non-degeneracy -/

omit [DecidableEq O] in
theorem integral_epsC_sq (c : O → ℝ) (o : O) :
    ∫ ω, epsC O c o ω * epsC O c o ω ∂(wP O) = c o ^ 2 := by
  have h : (fun ω => epsC O c o ω * epsC O c o ω)
      = fun ω => c o ^ 2 * (wEps O o ω * wEps O o ω) := by
    funext ω
    rw [epsC]
    ring
  rw [h, integral_const_mul, wEps_second_moment O o, mul_one]

end Model

/-! ## The witnesses -/

section Witness

variable {O : Type*} [Fintype O] [DecidableEq O]

/-- A witness for part (a) of Proposition SM.D.4 at a random design under Regime 1: every
hypothesis of `LeverageCondRegime1.prop_lc_a_random_regimeOne` holds on one model and the
conclusion is derived through it.

The conjuncts are: `𝒟` is a proper sub-σ-field; the mutual conditional independence; the
conditional covariance identity; the two values the design takes; part (a); and the
innovations are not degenerate. The design values are stated as equations, since at a
one-observation support the design is constant. -/
theorem prop_lc_a_random_regimeOne_witness {c : O → ℝ} (hcb : ∀ o, |c o| ≤ 1) (o₀ : O) :
    (∃ B : Set (Option O → ℝ), MeasurableSet B ∧ ¬ MeasurableSet[wD O] B)
    ∧ iCondIndepFun (wD O) (wD_le O) (epsC O c) (wP O)
    ∧ (∀ o o', (wP O)[fun ω => epsC O c o ω * epsC O c o' ω | wD O]
        =ᵐ[wP O] fun _ => if o = o' then c o ^ 2 else 0)
    ∧ rW O o₀ o₀ (fun _ => (1 : ℝ)) = 1
    ∧ rW O o₀ o₀ (fun _ => (-1 : ℝ)) = (Fintype.card O : ℝ)⁻¹
    ∧ ((fun ω => (wP O)[fun ω => ∑ o : O,
            wW O o ω * (residW O c o ω ^ 2 / rW O o o ω) | wD O] ω
          - ∑ o : O, wW O o ω * c o ^ 2)
        =ᵐ[wP O] fun ω => ∑ o : O, wW O o ω / rW O o o ω
            * ∑ o' ∈ Finset.univ.erase o, rW O o o' ω ^ 2 * (c o' ^ 2 - c o ^ 2))
    ∧ ∫ ω, epsC O c o₀ ω * epsC O c o₀ ω ∂(wP O) = c o₀ ^ 2 := by
  have hcross := LeverageCondRegime1.condExp_cross_of_regimeOne (wD O)
    (sig := fun o _ => c o ^ 2) (measurable_epsC O c) (epsC_condIndep O c)
    (int_epsC O hcb) (int_epsC_mul O hcb) (epsC_mean O c) (epsC_var O c)
  refine ⟨wD_proper O o₀, epsC_condIndep O c, hcross, ?_, ?_, ?_,
    integral_epsC_sq O c o₀⟩
  · rw [rW_diag]
    norm_num
  · rw [rW_diag]
    norm_num
  · exact LeverageCondRegime1.prop_lc_a_random_regimeOne (wD O) (stronglyMeasurable_rW O)
      (fun _ _ => rfl) (sum_rW_sq O o₀) (rW_diag_pos O o₀) (stronglyMeasurable_wW O)
      (measurable_epsC O c) (epsC_condIndep O c) (int_epsC O hcb) (int_epsC_mul O hcb)
      (fun o o' o'' => int_rr_epsC O hcb o₀ o o' o'') (epsC_mean O c) (epsC_var O c)
      (int_weighted O hcb o₀)

/-- A witness for part (b) of Proposition SM.D.4 at a random design under Regime 1, at a
constant scaling `c ≡ a` with `|a| ≤ 1`; for `a ≠ 0` the variance is nonzero. -/
theorem prop_lc_b_random_regimeOne_witness {a : ℝ} (hab : |a| ≤ 1) (o₀ : O) :
    (∃ B : Set (Option O → ℝ), MeasurableSet B ∧ ¬ MeasurableSet[wD O] B)
    ∧ iCondIndepFun (wD O) (wD_le O) (epsC O (fun _ => a)) (wP O)
    ∧ ((wP O)[fun ω => ∑ o : O, wW O o ω
            * (residW O (fun _ => a) o ω ^ 2 / rW O o o ω) | wD O]
        =ᵐ[wP O] fun ω => ∑ o : O, wW O o ω * a ^ 2)
    ∧ ∫ ω, epsC O (fun _ => a) o₀ ω * epsC O (fun _ => a) o₀ ω ∂(wP O) = a ^ 2 := by
  have hcb : ∀ _o : O, |a| ≤ 1 := fun _ => hab
  refine ⟨wD_proper O o₀, epsC_condIndep O _, ?_, integral_epsC_sq O (fun _ => a) o₀⟩
  exact LeverageCondRegime1.prop_lc_b_random_regimeOne (wD O) (s := fun _ => a ^ 2)
    (stronglyMeasurable_rW O) (fun _ _ => rfl) (sum_rW_sq O o₀) (rW_diag_pos O o₀)
    (fun _ _ => rfl) (stronglyMeasurable_wW O) (measurable_epsC O _)
    (epsC_condIndep O _) (int_epsC O hcb) (int_epsC_mul O hcb)
    (fun o o' o'' => int_rr_epsC O hcb o₀ o o' o'') (epsC_mean O _)
    (epsC_var O (fun _ => a)) (int_weighted O hcb o₀)

/-- The witness at `𝒪 = Fin 2` and `c = (1, 1/2)`, where `σ²_ε(0) = 1 ≠ 1/4 = σ²_ε(1)`
and the design takes the diagonal values `1` and `1/2`, with nonzero off-diagonal entries on
the second half, so the correction term of part (a) is nonzero. -/
theorem prop_lc_heteroskedastic_random_witness :
    (fun o : Fin 2 => if o = 0 then (1 : ℝ) else 1 / 2) 0 ^ 2
        ≠ (fun o : Fin 2 => if o = 0 then (1 : ℝ) else 1 / 2) 1 ^ 2
    ∧ rW (Fin 2) 0 1 (fun _ => (-1 : ℝ)) ≠ 0
    ∧ rW (Fin 2) 0 0 (fun _ => (1 : ℝ)) ≠ rW (Fin 2) 0 0 (fun _ => (-1 : ℝ))
    ∧ ((fun ω => (wP (Fin 2))[fun ω => ∑ o : Fin 2,
            wW (Fin 2) o ω
              * (residW (Fin 2) (fun o => if o = 0 then (1 : ℝ) else 1 / 2) o ω ^ 2
                  / rW (Fin 2) o o ω) | wD (Fin 2)] ω
          - ∑ o : Fin 2, wW (Fin 2) o ω
              * (if o = 0 then (1 : ℝ) else 1 / 2) ^ 2)
        =ᵐ[wP (Fin 2)] fun ω => ∑ o : Fin 2,
            wW (Fin 2) o ω / rW (Fin 2) o o ω
            * ∑ o' ∈ Finset.univ.erase o, rW (Fin 2) o o' ω ^ 2
                * ((if o' = 0 then (1 : ℝ) else 1 / 2) ^ 2
                    - (if o = 0 then (1 : ℝ) else 1 / 2) ^ 2)) := by
  have hcb : ∀ o : Fin 2, |(if o = 0 then (1 : ℝ) else 1 / 2)| ≤ 1 := by
    intro o
    by_cases h : o = 0
    · simp [h]
    · have hval : (if o = 0 then (1 : ℝ) else 1 / 2) = 1 / 2 := by simp [h]
      rw [hval, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      norm_num
  have hw := prop_lc_a_random_regimeOne_witness hcb (0 : Fin 2)
  refine ⟨by norm_num, ?_, ?_, hw.2.2.2.2.2.1⟩
  · have hoff : rW (Fin 2) 0 1 (fun _ => (-1 : ℝ)) = (Fintype.card (Fin 2) : ℝ)⁻¹ := by
      unfold rW
      norm_num
    rw [hoff]
    norm_num
  · rw [hw.2.2.2.1, hw.2.2.2.2.1]
    norm_num

end Witness

end LeverageCondWitness
end Multiway
