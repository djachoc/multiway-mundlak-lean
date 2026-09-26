/-
PORTED FILE — NOTICE REQUIRED BY THE APACHE LICENSE, VERSION 2.0, SECTION 4.

Upstream repository : Stat-Lean (StatLean)
Upstream path       : StatLean/TimeSeries/ForMathlib/Probability/MartingaleCLT/BrownCLT.lean
Upstream toolchain  : leanprover/lean4:v4.29.1
Upstream licence    : Apache License, Version 2.0
                      http://www.apache.org/licenses/LICENSE-2.0

MODIFICATIONS: this file has been modified in this package to
build against leanprover/lean4:v4.34.0 and its matching Mathlib. The changes made here,
relative to the upstream v4.29.1 file, are:
  * this notice was prepended;
  * the module path in the `import` lines was changed from `StatLean.TimeSeries.…` to
    `Multiway.BrownCLT.…`, the modules being re-rooted under this package (the upstream
    `MartingaleCLT/BrownCLT.lean` is this package's `Multiway/BrownCLT/Brown.lean`);
  * proof steps rejected by the newer Mathlib were repaired in place; each such repair is
    marked with a `-- PORT v4.34.0:` comment giving what changed;
  * docstrings and comments were shortened;
No mathematical content or attribution of the upstream file was removed.
-/
import Multiway.BrownCLT.CondCharFun
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Probability.Distributions.Gaussian.Real
-- PORT v4.34.0: `Measurable.abs` (the `to_additive` image of `Measurable.mabs`) is no longer
-- reachable through the imports above (the upstream import graph was pruned between
-- v4.29.1 and v4.34.0), so its home module is now named explicitly.
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# The Brown/Hall–Heyde martingale central limit theorem

A martingale-difference triangular array whose conditional variance process converges in
probability to a constant `σ²` and which satisfies the unconditional Lindeberg condition has
asymptotically `N(0, σ²)` row sums, stated through pointwise convergence of characteristic
functions.

The proof truncates the array (Hall–Heyde), then compares `E e^{iuS_n}` with
`e^{−u²σ²/2}` through the conditional Taylor telescope of `CondCharFun.lean`. The main results
are `mds_clt` (triangular arrays) and `mds_clt_sequence` (a single sequence).

References: B. M. Brown, *Martingale central limit theorems*, Ann. Math. Statist. 42
(1971), 59–66, Thm 2; P. Hall & C. C. Heyde, *Martingale Limit Theory and Its Application*,
Academic Press, 1980, Thm 3.2 / Cor 3.1.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

section Truncation

/-!
### The truncated array

A uniform `L¹` bound on the conditional variance process does not follow from `hvar` and
`hlind`, so the array is stopped at the first index at which the accumulated conditional
variance would exceed `σ² + 1`, and at every index whose conditional variance exceeds `d`.
Both events have vanishing probability, the second by `tendsto_measure_exists_cvar_ge`.
-/

variable {k : ℕ → ℕ} {X : (n : ℕ) → Fin (k n) → Ω → ℝ}
  {F : (n : ℕ) → Fin (k n + 1) → MeasurableSpace Ω}

/-- The `i`-th conditional variance `E[X_{n,i}² | 𝓕_{n,i}]` of the row `n`. -/
private noncomputable def cvar (k : ℕ → ℕ) (X : (n : ℕ) → Fin (k n) → Ω → ℝ)
    (F : (n : ℕ) → Fin (k n + 1) → MeasurableSpace Ω) (μ : Measure Ω) (n : ℕ)
    (i : Fin (k n)) : Ω → ℝ :=
  μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc]

private lemma mdsCondVariance_eq_sum_cvar (n : ℕ) (ω : Ω) :
    mdsCondVariance k X F μ n ω = ∑ i, cvar k X F μ n i ω := rfl

private lemma cvar_measurable (n : ℕ) (i : Fin (k n)) :
    Measurable[F n i.castSucc] (cvar k X F μ n i) :=
  stronglyMeasurable_condExp.measurable

private lemma cvar_measurable_le (h : IsMDSArray k X F μ) (n : ℕ) {i j : Fin (k n)} (hij : j ≤ i) :
    Measurable[F n i.castSucc] (cvar k X F μ n j) :=
  (cvar_measurable n j).mono (h.mono n (Fin.castSucc_le_castSucc_iff.2 hij)) le_rfl

private lemma cvar_nonneg (n : ℕ) (i : Fin (k n)) : 0 ≤ᵐ[μ] cvar k X F μ n i :=
  condExp_nonneg (ae_of_all _ fun _ => sq_nonneg _)

private lemma measurable_of_mds (h : IsMDSArray k X F μ) (n : ℕ) (i : Fin (k n)) :
    Measurable (X n i) := (h.adapted n i).mono (h.le_ambient n _) le_rfl

private lemma integrable_of_mds [IsFiniteMeasure μ] (h : IsMDSArray k X F μ) (n : ℕ)
    (i : Fin (k n)) : Integrable (X n i) μ := (h.memLp n i).integrable one_le_two

private lemma integrable_sq_of_mds (h : IsMDSArray k X F μ) (n : ℕ) (i : Fin (k n)) :
    Integrable (fun ω => X n i ω ^ 2) μ := (h.memLp n i).integrable_sq

private lemma integrable_mdsCondVariance : Integrable (mdsCondVariance k X F μ n) μ :=
  integrable_finset_sum _ fun _ _ => integrable_condExp

/-- The stopping set: the conditional variance accumulated up to and including `i` has not
exceeded `c`, and the `i`-th conditional variance has not exceeded `d`. Both conditions are
`𝓕_{n,i}`-measurable, so the truncated array is again a martingale-difference array. -/
private def truncSet (k : ℕ → ℕ) (X : (n : ℕ) → Fin (k n) → Ω → ℝ)
    (F : (n : ℕ) → Fin (k n + 1) → MeasurableSpace Ω) (μ : Measure Ω) (c d : ℝ) (n : ℕ)
    (i : Fin (k n)) : Set Ω :=
  {ω | ∑ j ∈ Finset.Iic i, cvar k X F μ n j ω ≤ c} ∩ {ω | cvar k X F μ n i ω ≤ d}

/-- The truncated array. The differences are set to zero from the first index at which the
accumulated conditional variance would exceed `c`, and at every index whose conditional
variance exceeds `d`. -/
private noncomputable def truncArray (k : ℕ → ℕ) (X : (n : ℕ) → Fin (k n) → Ω → ℝ)
    (F : (n : ℕ) → Fin (k n + 1) → MeasurableSpace Ω) (μ : Measure Ω) (c d : ℝ) (n : ℕ)
    (i : Fin (k n)) : Ω → ℝ :=
  (truncSet k X F μ c d n i).indicator (X n i)

private lemma measurableSet_truncSet (h : IsMDSArray k X F μ) (c d : ℝ) (n : ℕ)
    (i : Fin (k n)) : MeasurableSet[F n i.castSucc] (truncSet k X F μ c d n i) :=
  MeasurableSet.inter
    (measurableSet_le
      (Finset.measurable_sum _ fun _ hj => cvar_measurable_le h n (Finset.mem_Iic.1 hj))
      measurable_const)
    (measurableSet_le (cvar_measurable n i) measurable_const)

private lemma isMDSArray_truncArray [IsProbabilityMeasure μ] (h : IsMDSArray k X F μ)
    (c d : ℝ) : IsMDSArray k (truncArray k X F μ c d) F μ where
  le_ambient := h.le_ambient
  mono := h.mono
  adapted := fun n i =>
    (h.adapted n i).indicator
      (h.mono n (Fin.castSucc_le_succ i) _ (measurableSet_truncSet h c d n i))
  memLp := fun n i =>
    (h.memLp n i).indicator (h.le_ambient n _ _ (measurableSet_truncSet h c d n i))
  condexp_zero := fun n i => by
    have h1 := condExp_indicator (m := F n i.castSucc) (integrable_of_mds h n i)
      (measurableSet_truncSet h c d n i)
    filter_upwards [h1, h.condexp_zero n i] with ω e1 e2
    change μ[(truncSet k X F μ c d n i).indicator (X n i) | F n i.castSucc] ω = (0 : Ω → ℝ) ω
    rw [e1]
    by_cases hω : ω ∈ truncSet k X F μ c d n i
    · simp [Set.indicator_of_mem hω, e2]
    · simp [Set.indicator_of_notMem hω]

private lemma cvar_truncArray (h : IsMDSArray k X F μ) (c d : ℝ) (n : ℕ) (i : Fin (k n)) :
    cvar k (truncArray k X F μ c d) F μ n i
      =ᵐ[μ] (truncSet k X F μ c d n i).indicator (cvar k X F μ n i) := by
  have hsq : (fun ω => truncArray k X F μ c d n i ω ^ 2)
      = (truncSet k X F μ c d n i).indicator (fun ω => X n i ω ^ 2) := by
    funext ω; by_cases hω : ω ∈ truncSet k X F μ c d n i <;> simp [truncArray, hω]
  change μ[fun ω => truncArray k X F μ c d n i ω ^ 2 | F n i.castSucc] =ᵐ[μ] _
  rw [hsq]
  exact condExp_indicator (integrable_sq_of_mds h n i) (measurableSet_truncSet h c d n i)

/-- The truncated conditional variance process never exceeds the truncation level. -/
private lemma mdsCondVariance_truncArray_le (h : IsMDSArray k X F μ) {c d : ℝ} (hc : 0 ≤ c)
    (n : ℕ) : ∀ᵐ ω ∂μ, mdsCondVariance k (truncArray k X F μ c d) F μ n ω ≤ c := by
  have hnn : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ cvar k X F μ n i ω :=
    ae_all_iff.2 fun i => cvar_nonneg (μ := μ) n i
  have hc' : ∀ᵐ ω ∂μ, ∀ i, cvar k (truncArray k X F μ c d) F μ n i ω
      = (truncSet k X F μ c d n i).indicator (cvar k X F μ n i) ω :=
    ae_all_iff.2 fun i => cvar_truncArray h c d n i
  filter_upwards [hnn, hc'] with ω hω hωc
  classical
  rw [mdsCondVariance_eq_sum_cvar]
  have hstep : ∀ i : Fin (k n), cvar k (truncArray k X F μ c d) F μ n i ω
      = if i ∈ Finset.univ.filter (fun i => ω ∈ truncSet k X F μ c d n i) then
          cvar k X F μ n i ω else 0 := by
    intro i
    rw [hωc i]
    by_cases hi : ω ∈ truncSet k X F μ c d n i <;> simp [hi]
  rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_ite_mem, Finset.univ_inter]
  set T : Finset (Fin (k n)) := Finset.univ.filter (fun i => ω ∈ truncSet k X F μ c d n i) with hT
  rcases T.eq_empty_or_nonempty with he | hne
  · simpa [he] using hc
  · have hsub : T ⊆ Finset.Iic (T.max' hne) := fun j hj =>
      Finset.mem_Iic.2 (Finset.le_max' T j hj)
    have hmem : ω ∈ truncSet k X F μ c d n (T.max' hne) :=
      (Finset.mem_filter.1 (T.max'_mem hne)).2
    calc ∑ i ∈ T, cvar k X F μ n i ω
        ≤ ∑ i ∈ Finset.Iic (T.max' hne), cvar k X F μ n i ω :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hω j
      _ ≤ c := hmem.1

/-- Conditional monotonicity against a constant shift. -/
private lemma condExp_le_const_add {α : Type*} {m mα : MeasurableSpace α} {ν : Measure α}
    [IsFiniteMeasure ν] (hm : m ≤ mα) {f g : α → ℝ} (hf : Integrable f ν) (hg : Integrable g ν)
    {c : ℝ} (hfg : ∀ᵐ ω ∂ν, f ω ≤ c + g ω) :
    ∀ᵐ ω ∂ν, ν[f | m] ω ≤ c + ν[g | m] ω := by
  have h1 : ν[f | m] ≤ᵐ[ν] ν[fun ω => c + g ω | m] :=
    condExp_mono hf ((integrable_const c).add hg) hfg
  have h2 : ν[fun ω => c + g ω | m] =ᵐ[ν] ν[fun _ : α => c | m] + ν[g | m] :=
    condExp_add (integrable_const c) hg m
  filter_upwards [h1, h2] with ω e1 e2
  have e3 : ν[fun _ : α => c | m] ω = c := by rw [condExp_const (μ := ν) hm c]
  calc ν[f | m] ω ≤ ν[fun ω => c + g ω | m] ω := e1
    _ = ν[fun _ : α => c | m] ω + ν[g | m] ω := e2
    _ = c + ν[g | m] ω := by rw [e3]

/-- Uniform asymptotic negligibility of the conditional variances follows from the
Lindeberg condition: `E[X²|𝓕] ≤ ε² + E[X²1_{|X| ≥ ε}|𝓕]`, and Markov's inequality applies to
the sum of the latter. -/
private lemma tendsto_measure_exists_cvar_ge [IsProbabilityMeasure μ] (h : IsMDSArray k X F μ)
    (hlind : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε ≤ |X n i ω|}, (X n i ω) ^ 2 ∂μ) atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => (μ {ω | ∃ i, δ ≤ cvar k X F μ n i ω}).toReal) atTop (𝓝 0) := by
  obtain ⟨ε, hε, hε2⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ^ 2 = δ / 2 :=
    ⟨Real.sqrt (δ / 2), Real.sqrt_pos.2 (by linarith), Real.sq_sqrt (by linarith)⟩
  have hmeasS : ∀ (n : ℕ) (i : Fin (k n)), MeasurableSet {x : Ω | ε ≤ |X n i x|} := fun n i =>
    measurableSet_le measurable_const (measurable_of_mds h n i).abs
  set Y : (n : ℕ) → (i : Fin (k n)) → Ω → ℝ := fun n i =>
    Set.indicator {x : Ω | ε ≤ |X n i x|} (fun ω' => X n i ω' ^ 2) with hYdef
  have hYint : ∀ (n : ℕ) (i : Fin (k n)), Integrable (Y n i) μ := fun n i =>
    (integrable_sq_of_mds h n i).indicator (hmeasS n i)
  have hYnn : ∀ (n : ℕ) (i : Fin (k n)), 0 ≤ᵐ[μ] Y n i := fun n i =>
    ae_of_all _ fun ω => Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω
  set Z : ℕ → Ω → ℝ := fun n ω => ∑ i, μ[Y n i | F n i.castSucc] ω with hZdef
  have hZint : ∀ n, Integrable (Z n) μ := fun n =>
    integrable_finset_sum _ fun _ _ => integrable_condExp
  have hZnn : ∀ n, 0 ≤ᵐ[μ] Z n := fun n => by
    have hall : ∀ᵐ ω ∂μ, ∀ i : Fin (k n), 0 ≤ μ[Y n i | F n i.castSucc] ω :=
      ae_all_iff.2 fun i => condExp_nonneg (hYnn n i)
    filter_upwards [hall] with ω hω
    exact Finset.sum_nonneg fun i _ => hω i
  have hZmean : ∀ n, ∫ ω, Z n ω ∂μ = ∑ i, ∫ ω in {ω | ε ≤ |X n i ω|}, X n i ω ^ 2 ∂μ := by
    intro n
    rw [hZdef]
    rw [integral_finset_sum _ fun (i : Fin (k n)) _ =>
      (integrable_condExp : Integrable (μ[Y n i | F n i.castSucc]) μ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_condExp (h.le_ambient n i.castSucc), hYdef, integral_indicator (hmeasS n i)]
  have hincl : ∀ n, μ {ω | ∃ i, δ ≤ cvar k X F μ n i ω} ≤ μ {ω | δ / 2 ≤ Z n ω} := by
    intro n
    refine measure_mono_ae ?_
    have hkey : ∀ᵐ ω ∂μ, ∀ i : Fin (k n),
        cvar k X F μ n i ω ≤ ε ^ 2 + μ[Y n i | F n i.castSucc] ω := by
      refine ae_all_iff.2 fun i => ?_
      refine condExp_le_const_add (h.le_ambient n i.castSucc) (integrable_sq_of_mds h n i)
        (hYint n i) (ae_of_all _ fun ω => ?_)
      by_cases hω : ω ∈ {x : Ω | ε ≤ |X n i x|}
      · have hY : Y n i ω = X n i ω ^ 2 := by
          change Set.indicator {x : Ω | ε ≤ |X n i x|} (fun ω' => X n i ω' ^ 2) ω = _
          exact Set.indicator_of_mem hω _
        rw [hY]; nlinarith [sq_nonneg ε]
      · have hY : Y n i ω = 0 := by
          change Set.indicator {x : Ω | ε ≤ |X n i x|} (fun ω' => X n i ω' ^ 2) ω = 0
          exact Set.indicator_of_notMem hω _
        have hlt : |X n i ω| < ε := lt_of_not_ge hω
        rw [hY, add_zero]
        nlinarith [abs_nonneg (X n i ω), sq_abs (X n i ω)]
    have hnn : ∀ᵐ ω ∂μ, ∀ i : Fin (k n), 0 ≤ μ[Y n i | F n i.castSucc] ω :=
      ae_all_iff.2 fun i => condExp_nonneg (hYnn n i)
    filter_upwards [hkey, hnn] with ω e1 e2 hmem
    obtain ⟨i, hi⟩ := hmem
    have hhalf : δ / 2 ≤ μ[Y n i | F n i.castSucc] ω := by
      have := e1 i; rw [hε2] at this; linarith
    exact hhalf.trans (Finset.single_le_sum
      (f := fun j => μ[Y n j | F n j.castSucc] ω) (fun j _ => e2 j) (Finset.mem_univ i))
  have hg : Tendsto (fun n => 2 / δ * ∑ i, ∫ ω in {ω | ε ≤ |X n i ω|}, X n i ω ^ 2 ∂μ)
      atTop (𝓝 0) := by simpa using (hlind ε hε).const_mul (2 / δ)
  refine squeeze_zero (fun n => ENNReal.toReal_nonneg) (fun n => ?_) hg
  have hmark := mul_meas_ge_le_integral_of_nonneg (hZnn n) (hZint n) (δ / 2)
  rw [hZmean n] at hmark
  have h1 : (μ {ω | ∃ i, δ ≤ cvar k X F μ n i ω}).toReal ≤ μ.real {ω | δ / 2 ≤ Z n ω} := by
    rw [measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top μ _) (hincl n)
  refine h1.trans ?_
  have hc : (0 : ℝ) < 2 / δ := by positivity
  calc μ.real {ω | δ / 2 ≤ Z n ω}
      = 2 / δ * (δ / 2 * μ.real {ω | δ / 2 ≤ Z n ω}) := by field_simp
    _ ≤ 2 / δ * ∑ i, ∫ ω in {ω | ε ≤ |X n i ω|}, X n i ω ^ 2 ∂μ :=
        mul_le_mul_of_nonneg_left hmark hc.le

/-- Every truncated conditional variance is at most the per-index level `d`. -/
private lemma cvar_truncArray_le (h : IsMDSArray k X F μ) (c : ℝ) {d : ℝ} (hd : 0 ≤ d)
    (n : ℕ) (i : Fin (k n)) :
    ∀ᵐ ω ∂μ, cvar k (truncArray k X F μ c d) F μ n i ω ≤ d := by
  filter_upwards [cvar_truncArray h c d n i] with ω hω
  rw [hω]
  by_cases hi : ω ∈ truncSet k X F μ c d n i
  · rw [Set.indicator_of_mem hi]
    exact hi.2
  · rw [Set.indicator_of_notMem hi]
    exact hd

/-- Below both truncation levels, `ω` lies in every stopping set. -/
private lemma mem_truncSet_of_le {c d : ℝ} (n : ℕ) {ω : Ω}
    (hnn : ∀ i, 0 ≤ cvar k X F μ n i ω) (hle : mdsCondVariance k X F μ n ω ≤ c)
    (hdle : ∀ i, cvar k X F μ n i ω ≤ d)
    (i : Fin (k n)) : ω ∈ truncSet k X F μ c d n i := by
  refine Set.mem_inter ?_ (hdle i)
  change ∑ j ∈ Finset.Iic i, cvar k X F μ n j ω ≤ c
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun j _ _ => hnn j)) ?_
  rw [← mdsCondVariance_eq_sum_cvar]
  exact hle

private lemma ae_truncArray_eq (c d : ℝ) (n : ℕ) :
    ∀ᵐ ω ∂μ, mdsCondVariance k X F μ n ω ≤ c → (∀ i, cvar k X F μ n i ω ≤ d) →
      ∀ i, truncArray k X F μ c d n i ω = X n i ω := by
  have hnn0 : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ cvar k X F μ n i ω :=
    ae_all_iff.2 fun i => cvar_nonneg (μ := μ) n i
  filter_upwards [hnn0] with ω hnn hle hdle i
  exact Set.indicator_of_mem (mem_truncSet_of_le n hnn hle hdle i) _

private lemma ae_mdsRowSum_eq (c d : ℝ) (n : ℕ) :
    ∀ᵐ ω ∂μ, mdsCondVariance k X F μ n ω ≤ c → (∀ i, cvar k X F μ n i ω ≤ d) →
      mdsRowSum k (truncArray k X F μ c d) n ω = mdsRowSum k X n ω := by
  filter_upwards [ae_truncArray_eq (X := X) c d n] with ω hω hle hdle
  exact Finset.sum_congr rfl fun i _ => hω hle hdle i

private lemma ae_mdsCondVariance_eq (h : IsMDSArray k X F μ) (c d : ℝ) (n : ℕ) :
    ∀ᵐ ω ∂μ, mdsCondVariance k X F μ n ω ≤ c → (∀ i, cvar k X F μ n i ω ≤ d) →
      mdsCondVariance k (truncArray k X F μ c d) F μ n ω = mdsCondVariance k X F μ n ω := by
  have hnn0 : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ cvar k X F μ n i ω :=
    ae_all_iff.2 fun i => cvar_nonneg (μ := μ) n i
  have hc0 : ∀ᵐ ω ∂μ, ∀ i, cvar k (truncArray k X F μ c d) F μ n i ω
      = (truncSet k X F μ c d n i).indicator (cvar k X F μ n i) ω :=
    ae_all_iff.2 fun i => cvar_truncArray h c d n i
  filter_upwards [hnn0, hc0] with ω hnn hcc hle hdle
  rw [mdsCondVariance_eq_sum_cvar, mdsCondVariance_eq_sum_cvar]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hcc i, Set.indicator_of_mem (mem_truncSet_of_le n hnn hle hdle i)]

/-- The truncated array inherits the Lindeberg condition. -/
private lemma tendsto_lindeberg_truncArray [IsProbabilityMeasure μ] (h : IsMDSArray k X F μ)
    (hlind : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε ≤ |X n i ω|}, (X n i ω) ^ 2 ∂μ) atTop (𝓝 0))
    (c d : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => ∑ i, ∫ ω in {ω | ε ≤ |truncArray k X F μ c d n i ω|},
      (truncArray k X F μ c d n i ω) ^ 2 ∂μ) atTop (𝓝 0) := by
  have hmeas' : ∀ (n : ℕ) (i : Fin (k n)), Measurable (truncArray k X F μ c d n i) := fun n i =>
    measurable_of_mds (isMDSArray_truncArray h c d) n i
  refine squeeze_zero (fun n => Finset.sum_nonneg fun i _ => ?_) (fun n => ?_) (hlind ε hε)
  · exact setIntegral_nonneg (measurableSet_le measurable_const (hmeas' n i).abs)
      fun ω _ => sq_nonneg _
  refine Finset.sum_le_sum fun i _ => ?_
  have hS'meas : MeasurableSet {ω | ε ≤ |truncArray k X F μ c d n i ω|} :=
    measurableSet_le measurable_const (hmeas' n i).abs
  have hmem : ∀ ω ∈ {ω | ε ≤ |truncArray k X F μ c d n i ω|}, ω ∈ truncSet k X F μ c d n i := by
    intro ω hω
    by_contra hA
    rw [Set.mem_setOf_eq, show truncArray k X F μ c d n i ω = 0 from
      Set.indicator_of_notMem hA _] at hω
    simp only [abs_zero] at hω
    linarith
  have heq : ∫ ω in {ω | ε ≤ |truncArray k X F μ c d n i ω|},
      (truncArray k X F μ c d n i ω) ^ 2 ∂μ
      = ∫ ω in {ω | ε ≤ |truncArray k X F μ c d n i ω|}, X n i ω ^ 2 ∂μ :=
    setIntegral_congr_fun hS'meas fun ω hω => by
      rw [show truncArray k X F μ c d n i ω = X n i ω from
        Set.indicator_of_mem (hmem ω hω) _]
  rw [heq]
  refine setIntegral_mono_set (integrable_sq_of_mds h n i).integrableOn
    (ae_of_all _ fun ω => sq_nonneg _) (HasSubset.Subset.eventuallyLE fun ω hω => ?_)
  have := hmem ω hω
  rw [Set.mem_setOf_eq, show truncArray k X F μ c d n i ω = X n i ω from
    Set.indicator_of_mem this _] at hω
  exact hω

private lemma measurable_mdsCondVariance (h : IsMDSArray k X F μ) (n : ℕ) :
    Measurable (mdsCondVariance k X F μ n) :=
  Finset.measurable_sum _ fun i _ =>
    (cvar_measurable (X := X) n i).mono (h.le_ambient n i.castSucc) le_rfl

/-- The set on which the `i`-th conditional variance already exceeds the clamp level. -/
private lemma measurableSet_exists_cvar_ge (h : IsMDSArray k X F μ) (d : ℝ) (n : ℕ) :
    MeasurableSet {ω | ∃ i, d ≤ cvar k X F μ n i ω} := by
  have hEq : {ω | ∃ i, d ≤ cvar k X F μ n i ω}
      = ⋃ i, {ω | d ≤ cvar k X F μ n i ω} := by ext ω; simp
  rw [hEq]
  exact MeasurableSet.iUnion fun i => measurableSet_le measurable_const
    ((cvar_measurable (X := X) n i).mono (h.le_ambient n i.castSucc) le_rfl)

/-- The truncated array inherits the convergence of the conditional variance process: the two
processes differ only on `{V_n > σ² + 1} ∪ {∃ i, vᵢ ≥ d}`, which is asymptotically negligible. -/
private lemma tendsto_measure_truncArray_var [IsProbabilityMeasure μ] (h : IsMDSArray k X F μ)
    {σ2 : ℝ}
    (hvar : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => (μ {ω | δ ≤ |mdsCondVariance k X F μ n ω - σ2|}).toReal)
        atTop (𝓝 0))
    (hunif : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => (μ {ω | ∃ i, δ ≤ cvar k X F μ n i ω}).toReal) atTop (𝓝 0))
    {d : ℝ} (hd0 : 0 < d) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => (μ {ω | δ ≤
        |mdsCondVariance k (truncArray k X F μ (σ2 + 1) d) F μ n ω - σ2|}).toReal) atTop (𝓝 0) := by
  have hg : Tendsto (fun n => (μ {ω | δ ≤ |mdsCondVariance k X F μ n ω - σ2|}).toReal
      + ((μ {ω | (1 : ℝ) ≤ |mdsCondVariance k X F μ n ω - σ2|}).toReal
        + (μ {ω | ∃ i, d ≤ cvar k X F μ n i ω}).toReal)) atTop (𝓝 0) := by
    simpa using (hvar δ hδ).add ((hvar 1 one_pos).add (hunif d hd0))
  refine squeeze_zero (fun n => ENNReal.toReal_nonneg) (fun n => ?_) hg
  have hsub : μ {ω | δ ≤ |mdsCondVariance k (truncArray k X F μ (σ2 + 1) d) F μ n ω - σ2|}
      ≤ μ {ω | δ ≤ |mdsCondVariance k X F μ n ω - σ2|}
        + (μ {ω | (1 : ℝ) ≤ |mdsCondVariance k X F μ n ω - σ2|}
          + μ {ω | ∃ i, d ≤ cvar k X F μ n i ω}) := by
    refine le_trans (measure_mono_ae ?_)
      (le_trans (measure_union_le _ _) (add_le_add le_rfl (measure_union_le _ _)))
    filter_upwards [ae_mdsCondVariance_eq h (σ2 + 1) d n] with ω hω hmem
    by_cases hdle : ∀ i, cvar k X F μ n i ω ≤ d
    · by_cases hle : mdsCondVariance k X F μ n ω ≤ σ2 + 1
      · refine Set.mem_union_left _ ?_
        have hm : δ ≤ |mdsCondVariance k (truncArray k X F μ (σ2 + 1) d) F μ n ω - σ2| := hmem
        rw [hω hle hdle] at hm
        exact hm
      · refine Set.mem_union_right _ (Set.mem_union_left _ ?_)
        have hle : σ2 + 1 < mdsCondVariance k X F μ n ω := lt_of_not_ge hle
        change (1 : ℝ) ≤ |mdsCondVariance k X F μ n ω - σ2|
        rw [abs_of_nonneg (by linarith)]
        linarith
    · refine Set.mem_union_right _ (Set.mem_union_right _ ?_)
      push_neg at hdle
      obtain ⟨i, hi⟩ := hdle
      exact ⟨i, hi.le⟩
  refine le_trans (ENNReal.toReal_mono ?_ hsub) (le_of_eq ?_)
  · exact ENNReal.add_ne_top.2 ⟨measure_ne_top _ _,
      ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩⟩
  · rw [ENNReal.toReal_add (measure_ne_top _ _)
      (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩),
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]

/-- The characteristic function of the law of the row sum is the integral of the exponential
against the underlying measure. -/
private lemma charFun_map_mdsRowSum (h : IsMDSArray k X F μ) (n : ℕ) (u : ℝ) :
    charFun (μ.map (mdsRowSum k X n)) u
      = ∫ ω, Complex.exp (Complex.I * (u * mdsRowSum k X n ω : ℝ)) ∂μ := by
  have hmeas : Measurable (mdsRowSum k X n) :=
    Finset.measurable_sum _ fun i _ => measurable_of_mds h n i
  rw [charFun_apply_real,
    integral_map hmeas.aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop : Continuous fun x : ℝ =>
        Complex.exp (u * x * Complex.I)))]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  have harg : (u : ℂ) * ((mdsRowSum k X n ω : ℝ) : ℂ) * Complex.I
      = Complex.I * ((u * mdsRowSum k X n ω : ℝ) : ℂ) := by push_cast; ring
  simp only [harg]

private lemma integrable_exp_rowSum (h : IsMDSArray k X F μ) [IsProbabilityMeasure μ] (n : ℕ)
    (u : ℝ) : Integrable (fun ω => Complex.exp (Complex.I * (u * mdsRowSum k X n ω : ℝ))) μ := by
  have hmeas : Measurable (mdsRowSum k X n) :=
    Finset.measurable_sum _ fun i _ => measurable_of_mds h n i
  have hm2 : Measurable fun ω => Complex.exp (Complex.I * ((u * mdsRowSum k X n ω : ℝ) : ℂ)) :=
    Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp (measurable_const.mul hmeas)).const_mul Complex.I)
  refine Integrable.mono' (integrable_const (1 : ℝ)) hm2.aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [Complex.norm_exp]
  simp

/-- The characteristic functions of the row sums of the array and of its truncation differ by
at most twice the probability that the truncation is active. -/
private lemma norm_integral_exp_rowSum_sub_trunc [IsProbabilityMeasure μ] (h : IsMDSArray k X F μ)
    (c : ℝ) {d : ℝ} (n : ℕ) (u : ℝ) :
    ‖(∫ ω, Complex.exp (Complex.I * (u * mdsRowSum k X n ω : ℝ)) ∂μ)
        - ∫ ω, Complex.exp (Complex.I *
            (u * mdsRowSum k (truncArray k X F μ c d) n ω : ℝ)) ∂μ‖
      ≤ 2 * ((μ {ω | ¬ mdsCondVariance k X F μ n ω ≤ c}).toReal
          + (μ {ω | ∃ i, d ≤ cvar k X F μ n i ω}).toReal) := by
  have h' : IsMDSArray k (truncArray k X F μ c d) F μ := isMDSArray_truncArray h c d
  have hB : MeasurableSet {ω | ¬ mdsCondVariance k X F μ n ω ≤ c} :=
    (measurableSet_le (measurable_mdsCondVariance h n) measurable_const).compl
  have hC : MeasurableSet {ω | ∃ i, d ≤ cvar k X F μ n i ω} :=
    measurableSet_exists_cvar_ge h d n
  have hA : MeasurableSet ({ω | ¬ mdsCondVariance k X F μ n ω ≤ c}
      ∪ {ω | ∃ i, d ≤ cvar k X F μ n i ω}) := hB.union hC
  have hfint := integrable_exp_rowSum h n u
  have hgint := integrable_exp_rowSum h' n u
  rw [← integral_sub hfint hgint]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hbound : ∀ᵐ ω ∂μ, ‖Complex.exp (Complex.I * (u * mdsRowSum k X n ω : ℝ))
      - Complex.exp (Complex.I * (u * mdsRowSum k (truncArray k X F μ c d) n ω : ℝ))‖
      ≤ 2 * Set.indicator ({ω | ¬ mdsCondVariance k X F μ n ω ≤ c}
          ∪ {ω | ∃ i, d ≤ cvar k X F μ n i ω}) (fun _ => (1 : ℝ)) ω := by
    filter_upwards [ae_mdsRowSum_eq (X := X) c d n] with ω hω
    by_cases hmem : ω ∈ ({ω | ¬ mdsCondVariance k X F μ n ω ≤ c}
        ∪ {ω | ∃ i, d ≤ cvar k X F μ n i ω})
    · rw [Set.indicator_of_mem hmem]
      refine le_trans (norm_sub_le _ _) ?_
      rw [Complex.norm_exp, Complex.norm_exp]
      norm_num
    · have hle : mdsCondVariance k X F μ n ω ≤ c := by
        by_contra hc'
        exact hmem (Set.mem_union_left _ hc')
      have hdle : ∀ i, cvar k X F μ n i ω ≤ d := by
        intro i
        by_contra hc'
        exact hmem (Set.mem_union_right _ ⟨i, (lt_of_not_ge hc').le⟩)
      rw [hω hle hdle, sub_self, norm_zero]
      have : (0 : ℝ) ≤ Set.indicator ({ω | ¬ mdsCondVariance k X F μ n ω ≤ c}
          ∪ {ω | ∃ i, d ≤ cvar k X F μ n i ω}) (fun _ => (1 : ℝ)) ω :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) ω
      linarith
  refine le_trans (integral_mono_ae (hfint.sub hgint).norm
    (((integrable_const (1 : ℝ)).indicator hA).const_mul 2) hbound) ?_
  rw [integral_const_mul, integral_indicator_const _ hA, smul_eq_mul, mul_one, measureReal_def]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine le_trans (ENNReal.toReal_mono ?_ (measure_union_le _ _)) (le_of_eq ?_)
  · exact ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩
  · exact ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)

end Truncation

/-- **The Brown/Hall–Heyde martingale CLT**, in characteristic-function form. A
martingale-difference array with conditional variance `→p σ²` satisfying the Lindeberg
condition has asymptotically `N(0, σ²)` row sums. -/
theorem mds_clt [IsProbabilityMeasure μ]
    {k : ℕ → ℕ} {X : (n : ℕ) → Fin (k n) → Ω → ℝ}
    {F : (n : ℕ) → Fin (k n + 1) → MeasurableSpace Ω}
    (h : IsMDSArray k X F μ) {σ2 : ℝ} (hσ : 0 ≤ σ2)
    -- conditional variance → σ² in probability (Brown's condition)
    (hvar : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => (μ {ω | δ ≤ |mdsCondVariance k X F μ n ω - σ2|}).toReal)
        atTop (𝓝 0))
    -- the Lindeberg condition, unconditional form (Hall–Heyde (3.7))
    (hlind : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε ≤ |X n i ω|}, (X n i ω) ^ 2 ∂μ)
        atTop (𝓝 0))
    (u : ℝ) :
    Tendsto (fun n => charFun (μ.map (mdsRowSum k X n)) u) atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal σ2)) u)) := by
  classical
  set c : ℝ := σ2 + 1 with hcdef
  have hc0 : (0 : ℝ) ≤ c := by rw [hcdef]; linarith
  -- the per-index level `d`, with `u²d ≤ 1` so that each factor `1 - u²vᵢ/2` lies in `[1/2, 1]`
  set d : ℝ := 1 / (u ^ 2 + 1) with hddef
  have hd0 : (0 : ℝ) < d := by
    rw [hddef]
    have : (0:ℝ) < u ^ 2 + 1 := by positivity
    positivity
  have hdu : u ^ 2 * d ≤ 1 := by
    rw [hddef, mul_one_div, div_le_one (by positivity : (0:ℝ) < u ^ 2 + 1)]
    linarith
  set X' := truncArray k X F μ c d with hX'def
  have h' : IsMDSArray k X' F μ := isMDSArray_truncArray h c d
  -- uniform asymptotic negligibility for the original array
  have hunif0 : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => (μ {ω | ∃ i, δ ≤ cvar k X F μ n i ω}).toReal) atTop (𝓝 0) :=
    fun δ hδ => tendsto_measure_exists_cvar_ge h hlind hδ
  -- the truncated array satisfies the Lindeberg condition,
  have hlind' : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε ≤ |X' n i ω|}, (X' n i ω) ^ 2 ∂μ) atTop (𝓝 0) :=
    fun ε hε => tendsto_lindeberg_truncArray h hlind c d hε
  -- the variance condition,
  have hvar' : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => (μ {ω | δ ≤ |mdsCondVariance k X' F μ n ω - σ2|}).toReal)
        atTop (𝓝 0) := fun δ hδ => tendsto_measure_truncArray_var h hvar hunif0 hd0 hδ
  -- uniform asymptotic negligibility,
  have hunif' : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => (μ {ω | ∃ i, δ ≤ μ[fun ω' => X' n i ω' ^ 2 | F n i.castSucc] ω}).toReal)
        atTop (𝓝 0) := fun δ hδ => tendsto_measure_exists_cvar_ge h' hlind' hδ
  -- and both truncation bounds
  have hclampc : ∀ n, ∀ᵐ ω ∂μ, mdsCondVariance k X' F μ n ω ≤ c :=
    fun n => mdsCondVariance_truncArray_le h hc0 n
  have hclampd : ∀ (n : ℕ) (i : Fin (k n)), ∀ᵐ ω ∂μ,
      μ[fun ω' => X' n i ω' ^ 2 | F n i.castSucc] ω ≤ d :=
    fun n i => cvar_truncArray_le h c hd0.le n i
  -- the `L¹` product comparison for the truncated array
  have hL1 := tendsto_integral_abs_prod_one_sub_condVar_sub h' hσ hvar' hunif' hclampc u
  -- the row variance identity `Σᵢ E Xᵢ² = E V_n` for the truncated array
  have hsumsq : ∀ n, ∑ i, ∫ ω, X' n i ω ^ 2 ∂μ = ∫ ω, mdsCondVariance k X' F μ n ω ∂μ := by
    intro n
    have e0 : ∫ ω, mdsCondVariance k X' F μ n ω ∂μ = ∑ i, ∫ ω, cvar k X' F μ n i ω ∂μ := by
      simp only [mdsCondVariance_eq_sum_cvar]
      exact integral_finset_sum _ fun i _ => integrable_condExp
    rw [e0]
    exact Finset.sum_congr rfl fun i _ =>
      (integral_condExp (h'.le_ambient n i.castSucc)).symm
  -- the assembled comparison, with `ε` chosen after `η`
  have hmain : Tendsto (fun n =>
      (∫ ω, Complex.exp (Complex.I * (u * mdsRowSum k X' n ω : ℝ)) ∂μ)
        - ((Real.exp (-(u ^ 2 * σ2 / 2)) : ℝ) : ℂ)) atTop (𝓝 0) := by
    refine NormedAddGroup.tendsto_nhds_zero.2 fun η hη => ?_
    obtain ⟨ε, hε, hεbd⟩ : ∃ ε : ℝ, 0 < ε ∧
        2 * Real.exp (u ^ 2 * c) * (|u| ^ 3 * ε * c) < η / 3 := by
      have hW0 : (0:ℝ) ≤ 2 * Real.exp (u ^ 2 * c) * (|u| ^ 3 * c) := by positivity
      have hW1 : (0:ℝ) < 2 * Real.exp (u ^ 2 * c) * (|u| ^ 3 * c) + 1 := by linarith
      refine ⟨(η / 3) / (2 * Real.exp (u ^ 2 * c) * (|u| ^ 3 * c) + 1),
        div_pos (by linarith) hW1, ?_⟩
      have expand : 2 * Real.exp (u ^ 2 * c) * (|u| ^ 3 *
          ((η / 3) / (2 * Real.exp (u ^ 2 * c) * (|u| ^ 3 * c) + 1)) * c)
          = (2 * Real.exp (u ^ 2 * c) * (|u| ^ 3 * c)) * (η / 3)
            / (2 * Real.exp (u ^ 2 * c) * (|u| ^ 3 * c) + 1) := by
        field_simp
      rw [expand, div_lt_iff₀ hW1]
      nlinarith
    have hL2 : Tendsto (fun n => 2 * Real.exp (u ^ 2 * c) * (u ^ 2 *
        ∑ i, ∫ ω in {ω | ε ≤ |X' n i ω|}, (X' n i ω) ^ 2 ∂μ)) atTop (𝓝 0) := by
      simpa using ((hlind' ε hε).const_mul (u ^ 2)).const_mul (2 * Real.exp (u ^ 2 * c))
    have hL3 : Tendsto (fun n => Real.exp (u ^ 2 * c) * ∫ ω, |(∏ i, (1 - u ^ 2 / 2 *
        μ[fun ω' => X' n i ω' ^ 2 | F n i.castSucc] ω))
        - Real.exp (-(u ^ 2 * σ2 / 2))| ∂μ) atTop (𝓝 0) := by
      simpa using hL1.const_mul (Real.exp (u ^ 2 * c))
    filter_upwards [NormedAddGroup.tendsto_nhds_zero.1 hL2 (η / 3) (by linarith),
      NormedAddGroup.tendsto_nhds_zero.1 hL3 (η / 3) (by linarith)] with n hn2' hn3'
    have hn2 : 2 * Real.exp (u ^ 2 * c) * (u ^ 2 *
        ∑ i, ∫ ω in {ω | ε ≤ |X' n i ω|}, (X' n i ω) ^ 2 ∂μ) < η / 3 :=
      lt_of_le_of_lt (le_abs_self _) hn2'
    have hn3 : Real.exp (u ^ 2 * c) * ∫ ω, |(∏ i, (1 - u ^ 2 / 2 *
        μ[fun ω' => X' n i ω' ^ 2 | F n i.castSucc] ω))
        - Real.exp (-(u ^ 2 * σ2 / 2))| ∂μ < η / 3 :=
      lt_of_le_of_lt (le_abs_self _) hn3'
    refine lt_of_le_of_lt (norm_integral_exp_rowSum_sub_gaussian_le h' n u hε hσ
      (hclampd n) hdu (hclampc n)) ?_
    have e1 : ∑ i, (u ^ 2 * ∫ ω, X' n i ω ^ 2 *
          Set.indicator {x : Ω | ε ≤ |X' n i x|} (fun _ => (1 : ℝ)) ω ∂μ)
        = u ^ 2 * ∑ i, ∫ ω in {ω | ε ≤ |X' n i ω|}, (X' n i ω) ^ 2 ∂μ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      rw [← integral_indicator (measurableSet_le measurable_const
        (measurable_of_mds h' n i).abs)]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      by_cases hω : ω ∈ {x : Ω | ε ≤ |X' n i x|}
      · simp only [Set.indicator_of_mem hω, mul_one]
      · simp only [Set.indicator_of_notMem hω, mul_zero]
    have e2 : ∑ i, (|u| ^ 3 * ε * ∫ ω, X' n i ω ^ 2 ∂μ)
        = |u| ^ 3 * ε * ∫ ω, mdsCondVariance k X' F μ n ω ∂μ := by
      rw [← Finset.mul_sum, hsumsq n]
    have hbound2 : |u| ^ 3 * ε * ∫ ω, mdsCondVariance k X' F μ n ω ∂μ ≤ |u| ^ 3 * ε * c := by
      have hmono : ∫ ω, mdsCondVariance k X' F μ n ω ∂μ ≤ c := by
        calc ∫ ω, mdsCondVariance k X' F μ n ω ∂μ
            ≤ ∫ _ω, c ∂μ := integral_mono_ae integrable_mdsCondVariance (integrable_const c)
              (hclampc n)
          _ = c := by simp
      have : (0 : ℝ) ≤ |u| ^ 3 * ε := by positivity
      nlinarith
    have hb : 2 * Real.exp (u ^ 2 * c) *
          (|u| ^ 3 * ε * ∫ ω, mdsCondVariance k X' F μ n ω ∂μ)
        ≤ 2 * Real.exp (u ^ 2 * c) * (|u| ^ 3 * ε * c) :=
      mul_le_mul_of_nonneg_left hbound2 (by positivity)
    have hdist : 2 * Real.exp (u ^ 2 * c) *
        (u ^ 2 * (∑ i, ∫ ω in {ω | ε ≤ |X' n i ω|}, (X' n i ω) ^ 2 ∂μ)
          + |u| ^ 3 * ε * ∫ ω, mdsCondVariance k X' F μ n ω ∂μ)
        = 2 * Real.exp (u ^ 2 * c) *
            (u ^ 2 * ∑ i, ∫ ω in {ω | ε ≤ |X' n i ω|}, (X' n i ω) ^ 2 ∂μ)
          + 2 * Real.exp (u ^ 2 * c) *
            (|u| ^ 3 * ε * ∫ ω, mdsCondVariance k X' F μ n ω ∂μ) := by ring
    rw [e1, e2, hdist]
    linarith
  -- the truncation changes the row sum only on a vanishing event
  have hcomp : Tendsto (fun n => (∫ ω, Complex.exp (Complex.I * (u * mdsRowSum k X n ω : ℝ)) ∂μ)
      - ∫ ω, Complex.exp (Complex.I * (u * mdsRowSum k X' n ω : ℝ)) ∂μ) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => norm_integral_exp_rowSum_sub_trunc h c n u) ?_
    have hlim : Tendsto (fun n => 2 * ((μ {ω | (1 : ℝ) ≤
        |mdsCondVariance k X F μ n ω - σ2|}).toReal
        + (μ {ω | ∃ i, d ≤ cvar k X F μ n i ω}).toReal)) atTop (𝓝 0) := by
      simpa using ((hvar 1 one_pos).add (hunif0 d hd0)).const_mul 2
    refine squeeze_zero (fun n => ?_) (fun n => ?_) hlim
    · have h1 : (0:ℝ) ≤ (μ {ω | ¬ mdsCondVariance k X F μ n ω ≤ c}).toReal :=
        ENNReal.toReal_nonneg
      have h2 : (0:ℝ) ≤ (μ {ω | ∃ i, d ≤ cvar k X F μ n i ω}).toReal := ENNReal.toReal_nonneg
      linarith
    have hsub : μ {ω | ¬ mdsCondVariance k X F μ n ω ≤ c}
        ≤ μ {ω | (1 : ℝ) ≤ |mdsCondVariance k X F μ n ω - σ2|} := by
      refine measure_mono fun ω hω => ?_
      have hω' : σ2 + 1 < mdsCondVariance k X F μ n ω := by
        rw [hcdef] at hω; exact lt_of_not_ge hω
      change (1 : ℝ) ≤ |mdsCondVariance k X F μ n ω - σ2|
      rw [abs_of_nonneg (by linarith)]
      linarith
    have := ENNReal.toReal_mono (measure_ne_top μ _) hsub
    linarith
  -- assemble and identify the Gaussian characteristic function
  have hsum := hcomp.add hmain
  simp only [add_zero] at hsum
  have hAγ : Tendsto (fun n => (∫ ω, Complex.exp (Complex.I * (u * mdsRowSum k X n ω : ℝ)) ∂μ)
      - ((Real.exp (-(u ^ 2 * σ2 / 2)) : ℝ) : ℂ)) atTop (𝓝 0) := hsum.congr fun n => by ring
  have hgc : Complex.exp (-(u ^ 2 * σ2 / 2 : ℝ))
      = ((Real.exp (-(u ^ 2 * σ2 / 2)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hfinal : Tendsto (fun n => ∫ ω, Complex.exp (Complex.I * (u * mdsRowSum k X n ω : ℝ)) ∂μ)
      atTop (𝓝 (Complex.exp (-(u ^ 2 * σ2 / 2 : ℝ)))) := by
    rw [hgc]
    exact tendsto_sub_nhds_zero_iff.1 hAγ
  have hgauss : charFun (gaussianReal 0 (Real.toNNReal σ2)) u
      = Complex.exp (-(u ^ 2 * σ2 / 2 : ℝ)) := by
    rw [charFun_gaussianReal]
    congr 1
    rw [Real.coe_toNNReal σ2 hσ]
    push_cast
    ring
  rw [hgauss]
  exact (tendsto_congr fun n => charFun_map_mdsRowSum h n u).2 hfinal

/-- **Stationary-sequence corollary.** A martingale-difference sequence `ξ` for a filtration
`G` with `n⁻¹ Σ_{i<n} E[ξᵢ² | Gᵢ] →p σ²` and the averaged Lindeberg property has
`S_n/√n →d N(0, σ²)`. This is `mds_clt` at `X_{n,i} = ξ_i/√n`. -/
theorem mds_clt_sequence [IsProbabilityMeasure μ]
    {ξ : ℕ → Ω → ℝ} {G : ℕ → MeasurableSpace Ω}
    (hle : ∀ i, G i ≤ ‹MeasurableSpace Ω›) (hmono : Monotone G)
    (hadapted : ∀ i, Measurable[G (i + 1)] (ξ i))
    (hL2 : ∀ i, MemLp (ξ i) 2 μ)
    -- martingale-difference property
    (hmds : ∀ i, μ[ξ i | G i] =ᵐ[μ] 0)
    {σ2 : ℝ} (hσ : 0 ≤ σ2)
    -- averaged conditional variance → σ² in probability
    (hvar : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n : ℕ => (μ {ω | δ ≤ |(n : ℝ)⁻¹ *
          (∑ i ∈ Finset.range n, μ[fun ω' => ξ i ω' ^ 2 | G i] ω) - σ2|}).toReal)
        atTop (𝓝 0))
    -- averaged Lindeberg condition
    (hlind : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
          ∫ ω in {ω | ε * Real.sqrt n ≤ |ξ i ω|}, (ξ i ω) ^ 2 ∂μ)
        atTop (𝓝 0))
    (u : ℝ) :
    Tendsto (fun n : ℕ => charFun (μ.map fun ω =>
        (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, ξ i ω) u) atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal σ2)) u)) := by
  classical
  set X : (n : ℕ) → Fin n → Ω → ℝ := fun n i ω => ξ (i : ℕ) ω / Real.sqrt n with hXdef
  set F : (n : ℕ) → Fin (n + 1) → MeasurableSpace Ω := fun n i => G (i : ℕ) with hFdef
  have hsq : ∀ (n : ℕ) (i : Fin n) (ω : Ω), X n i ω ^ 2 = ((n : ℝ))⁻¹ * ξ (i : ℕ) ω ^ 2 := by
    intro n i ω
    simp only [hXdef]
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    ring
  -- the array `X_{n,i} = ξ_i/√n` is a martingale-difference array for `F_{n,i} = G_i`
  have harray : IsMDSArray (fun n => n) X F μ := by
    refine ⟨fun n i => hle _, fun n i j hij => hmono hij, fun n i => ?_, fun n i => ?_,
      fun n i => ?_⟩
    · simp only [hXdef]
      exact (hadapted (i : ℕ)).div_const _
    · simp only [hXdef]
      simpa [div_eq_inv_mul] using (hL2 (i : ℕ)).const_mul (Real.sqrt n)⁻¹
    · have hXi : X n i = (Real.sqrt n)⁻¹ • ξ (i : ℕ) := by
        funext ω; simp [hXdef, div_eq_inv_mul]
      have h2 : μ[X n i | G (i : ℕ)] =ᵐ[μ] (Real.sqrt n)⁻¹ • μ[ξ (i : ℕ) | G (i : ℕ)] := by
        rw [hXi]; exact condExp_smul _ _ _
      filter_upwards [h2, hmds (i : ℕ)] with ω e1 e2
      change μ[X n i | G (i : ℕ)] ω = (0 : Ω → ℝ) ω
      simp [e1, e2]
  -- the conditional variance process is the average of the `E[ξᵢ²|Gᵢ]`
  have hVar : ∀ n : ℕ, ∀ᵐ ω ∂μ, mdsCondVariance (fun n => n) X F μ n ω
      = ((n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, μ[fun ω' => ξ i ω' ^ 2 | G i] ω := by
    intro n
    have hall : ∀ᵐ ω ∂μ, ∀ i : Fin n, μ[fun ω' => X n i ω' ^ 2 | G (i : ℕ)] ω
        = ((n : ℝ))⁻¹ * μ[fun ω' => ξ (i : ℕ) ω' ^ 2 | G (i : ℕ)] ω := by
      refine ae_all_iff.2 fun i => ?_
      have e0 : (fun ω' => X n i ω' ^ 2) = ((n : ℝ))⁻¹ • fun ω' => ξ (i : ℕ) ω' ^ 2 := by
        funext ω'; rw [hsq n i ω']; rfl
      rw [e0]
      exact condExp_smul _ _ _
    filter_upwards [hall] with ω hω
    change ∑ i : Fin n, μ[fun ω' => X n i ω' ^ 2 | G (i : ℕ)] ω = _
    rw [Finset.sum_congr rfl fun i _ => hω i, ← Finset.mul_sum,
      Fin.sum_univ_eq_sum_range (fun i => μ[fun ω' => ξ i ω' ^ 2 | G i] ω) n]
  have hvar' : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => (μ {ω | δ ≤ |mdsCondVariance (fun n => n) X F μ n ω - σ2|}).toReal)
        atTop (𝓝 0) := by
    intro δ hδ
    refine (hvar δ hδ).congr fun n => ?_
    congr 1
    refine measure_congr ?_
    filter_upwards [hVar n] with ω hω
    change (δ ≤ |(n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, μ[fun ω' => ξ i ω' ^ 2 | G i] ω) - σ2|)
      = (δ ≤ |mdsCondVariance (fun n => n) X F μ n ω - σ2|)
    rw [hω]
  -- the Lindeberg sets agree: `{|ξᵢ/√n| ≥ ε} = {|ξᵢ| ≥ ε√n}`
  have hlind' : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i : Fin n, ∫ ω in {ω | ε ≤ |X n i ω|}, (X n i ω) ^ 2 ∂μ)
        atTop (𝓝 0) := by
    intro ε hε
    refine (hlind ε hε).congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hset : ∀ i : Fin n, {ω | ε ≤ |X n i ω|}
        = {ω | ε * Real.sqrt n ≤ |ξ (i : ℕ) ω|} := by
      intro i
      ext ω
      simp only [Set.mem_setOf_eq, hXdef, abs_div, abs_of_nonneg (Real.sqrt_nonneg (n : ℝ))]
      rw [le_div_iff₀ hsqrt]
    have hterm : ∀ i : Fin n, ∫ ω in {ω | ε ≤ |X n i ω|}, (X n i ω) ^ 2 ∂μ
        = ((n : ℝ))⁻¹ * ∫ ω in {ω | ε * Real.sqrt n ≤ |ξ (i : ℕ) ω|}, ξ (i : ℕ) ω ^ 2 ∂μ := by
      intro i
      calc ∫ ω in {ω | ε ≤ |X n i ω|}, (X n i ω) ^ 2 ∂μ
          = ∫ ω in {ω | ε * Real.sqrt n ≤ |ξ (i : ℕ) ω|}, ((n : ℝ))⁻¹ * ξ (i : ℕ) ω ^ 2 ∂μ := by
            rw [hset i]
            exact integral_congr_ae (ae_of_all _ fun ω => hsq n i ω)
        _ = ((n : ℝ))⁻¹ * ∫ ω in {ω | ε * Real.sqrt n ≤ |ξ (i : ℕ) ω|}, ξ (i : ℕ) ω ^ 2 ∂μ :=
            integral_const_mul _ _
    rw [Finset.sum_congr rfl fun (i : Fin n) _ => hterm i, ← Finset.mul_sum,
      Fin.sum_univ_eq_sum_range
        (fun i => ∫ ω in {ω | ε * Real.sqrt n ≤ |ξ i ω|}, ξ i ω ^ 2 ∂μ) n]
  -- the row sums are the normalized partial sums
  have hrow : ∀ n : ℕ, mdsRowSum (fun n => n) X n
      = fun ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, ξ i ω := by
    intro n
    funext ω
    change ∑ i : Fin n, X n i ω = _
    simp only [hXdef]
    rw [Fin.sum_univ_eq_sum_range (fun i => ξ i ω / Real.sqrt n) n, ← Finset.sum_div,
      div_eq_inv_mul]
  simpa only [hrow] using mds_clt harray hσ hvar' hlind' u

end StatLean.TimeSeries
