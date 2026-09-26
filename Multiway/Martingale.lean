import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Martingale representation of a degenerate multilinear sum

This file formalizes Lemma SM.C.2 of the paper (Martingale representation of a degenerate
multilinear sum). For independent latent variables revealed in an arbitrary order, the
increments `D_κ` of `𝔼[T ∣ ℱ_κ]` of a completely degenerate multilinear sum `T` form a
martingale-difference sequence with `T = ∑_κ D_κ`, and `D_κ` is the sum of the terms whose
last coordinate is revealed at step `κ`. Indices are zero-based: `degenDiff … κ` is `D_{κ+1}`.

## Main results

* `condExp_sup_of_indep`: dropping an independent σ-field from the conditioning.
* `martingale_representation`: Lemma SM.C.2, all four conclusions.
* `multi_martingale_representation`: the same for a family of components of different arities
  sharing one filtration.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped MeasureTheory

namespace Multiway

namespace DegenerateSum

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- The π-system of intersections `a ∩ b` with `a` an `𝒜`-set and `b` a `ℬ`-set. -/
def interPi (𝒜 ℬ : MeasurableSpace Ω) : Set (Set Ω) :=
  {s | ∃ a b, MeasurableSet[𝒜] a ∧ MeasurableSet[ℬ] b ∧ s = a ∩ b}

theorem isPiSystem_interPi (𝒜 ℬ : MeasurableSpace Ω) : IsPiSystem (interPi 𝒜 ℬ) := by
  rintro s ⟨a, b, ha, hb, rfl⟩ t ⟨a', b', ha', hb', rfl⟩ -
  refine ⟨a ∩ a', b ∩ b', ha.inter ha', hb.inter hb', ?_⟩
  ext x
  simp only [Set.mem_inter_iff]
  tauto

theorem generateFrom_interPi (𝒜 ℬ : MeasurableSpace Ω) :
    MeasurableSpace.generateFrom (interPi 𝒜 ℬ) = 𝒜 ⊔ ℬ := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) (sup_le ?_ ?_)
  · rintro s ⟨a, b, ha, hb, rfl⟩
    exact MeasurableSet.inter ((le_sup_left : 𝒜 ≤ 𝒜 ⊔ ℬ) _ ha)
      ((le_sup_right : ℬ ≤ 𝒜 ⊔ ℬ) _ hb)
  · intro a ha
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨a, Set.univ, ha, MeasurableSet.univ, (Set.inter_univ a).symm⟩
  · intro b hb
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨Set.univ, b, MeasurableSet.univ, hb, (Set.univ_inter b).symm⟩

/-- **Dropping an independent σ-field from the conditioning.** If `X` is `𝒞`-measurable,
`𝒜 ≤ 𝒞` and `𝒞` is independent of `ℬ`, then `𝔼[X ∣ 𝒜 ⊔ ℬ] = 𝔼[X ∣ 𝒜]`. Proved from
`MeasureTheory.condExp_indep_eq` by a Dynkin argument over the π-system `interPi 𝒜 ℬ`. -/
theorem condExp_sup_of_indep [IsProbabilityMeasure μ] {𝒜 ℬ 𝒞 : MeasurableSpace Ω}
    (h𝒜𝒞 : 𝒜 ≤ 𝒞) (h𝒞 : 𝒞 ≤ m0) (hℬ : ℬ ≤ m0) (hind : Indep 𝒞 ℬ μ)
    {X : Ω → ℝ} (hXm : StronglyMeasurable[𝒞] X) (hX : Integrable X μ) :
    μ[X | 𝒜 ⊔ ℬ] =ᵐ[μ] μ[X | 𝒜] := by
  have h𝒜 : 𝒜 ≤ m0 := h𝒜𝒞.trans h𝒞
  have hAB : 𝒜 ⊔ ℬ ≤ m0 := sup_le h𝒜 hℬ
  -- Over a `ℬ`-set, a `𝒞`-measurable integrand integrates to its mean times the measure.
  have hfac : ∀ Z : Ω → ℝ, StronglyMeasurable[𝒞] Z → Integrable Z μ →
      ∀ b, MeasurableSet[ℬ] b → ∫ x in b, Z x ∂μ = ∫ _x in b, (∫ x, Z x ∂μ) ∂μ := by
    intro Z hZm hZ b hb
    have hce : μ[Z | ℬ] =ᵐ[μ] fun _ => ∫ x, Z x ∂μ := condExp_indep_eq h𝒞 hℬ hZm hind
    calc ∫ x in b, Z x ∂μ = ∫ x in b, (μ[Z | ℬ]) x ∂μ := (setIntegral_condExp hℬ hZ hb).symm
      _ = ∫ _x in b, (∫ x, Z x ∂μ) ∂μ := integral_congr_ae (ae_restrict_of_ae hce)
  -- The π-system case.
  have hbasic : ∀ a b, MeasurableSet[𝒜] a → MeasurableSet[ℬ] b →
      ∫ x in a ∩ b, (μ[X | 𝒜]) x ∂μ = ∫ x in a ∩ b, X x ∂μ := by
    intro a b ha hb
    have hXm' : StronglyMeasurable[𝒞] (a.indicator X) := hXm.indicator (h𝒜𝒞 _ ha)
    have hYm' : StronglyMeasurable[𝒞] (a.indicator (μ[X | 𝒜])) :=
      (stronglyMeasurable_condExp.mono h𝒜𝒞).indicator (h𝒜𝒞 _ ha)
    have hXi : Integrable (a.indicator X) μ := hX.indicator (h𝒜 _ ha)
    have hYi : Integrable (a.indicator (μ[X | 𝒜])) μ := integrable_condExp.indicator (h𝒜 _ ha)
    have hmeans : ∫ x, a.indicator (μ[X | 𝒜]) x ∂μ = ∫ x, a.indicator X x ∂μ := by
      rw [integral_indicator (h𝒜 _ ha), integral_indicator (h𝒜 _ ha)]
      exact setIntegral_condExp h𝒜 hX ha
    calc ∫ x in a ∩ b, (μ[X | 𝒜]) x ∂μ
        = ∫ x in b, a.indicator (μ[X | 𝒜]) x ∂μ := by
          rw [setIntegral_indicator (h𝒜 _ ha), Set.inter_comm]
      _ = ∫ _x in b, (∫ x, a.indicator (μ[X | 𝒜]) x ∂μ) ∂μ := hfac _ hYm' hYi b hb
      _ = ∫ _x in b, (∫ x, a.indicator X x ∂μ) ∂μ := by rw [hmeans]
      _ = ∫ x in b, a.indicator X x ∂μ := (hfac _ hXm' hXi b hb).symm
      _ = ∫ x in a ∩ b, X x ∂μ := by rw [setIntegral_indicator (h𝒜 _ ha), Set.inter_comm]
  -- Dynkin's lemma extends it from the π-system to every `𝒜 ⊔ ℬ`-set.
  have key : ∀ s, MeasurableSet[𝒜 ⊔ ℬ] s →
      ∫ x in s, (μ[X | 𝒜]) x ∂μ = ∫ x in s, X x ∂μ := by
    refine MeasurableSpace.induction_on_inter
      (C := fun s _ => ∫ x in s, (μ[X | 𝒜]) x ∂μ = ∫ x in s, X x ∂μ)
      (generateFrom_interPi 𝒜 ℬ).symm (isPiSystem_interPi 𝒜 ℬ) (by simp) ?_ ?_ ?_
    · rintro t ⟨a, b, ha, hb, rfl⟩
      exact hbasic a b ha hb
    · intro t htm ih
      have hY : ∫ x in t, (μ[X | 𝒜]) x ∂μ + ∫ x in tᶜ, (μ[X | 𝒜]) x ∂μ
          = ∫ x, (μ[X | 𝒜]) x ∂μ :=
        integral_add_compl (hAB _ htm) integrable_condExp
      have hX' := integral_add_compl (hAB _ htm) hX
      have htot : ∫ x, (μ[X | 𝒜]) x ∂μ = ∫ x, X x ∂μ := integral_condExp h𝒜
      rw [ih, htot] at hY
      linarith [hY, hX']
    · intro f hfd hfm ihf
      rw [integral_iUnion (fun i => hAB _ (hfm i)) hfd integrable_condExp.integrableOn,
        integral_iUnion (fun i => hAB _ (hfm i)) hfd hX.integrableOn]
      exact tsum_congr ihf
  exact (ae_eq_condExp_of_forall_setIntegral_eq hAB hX
    (fun _ _ _ => integrable_condExp.integrableOn) (fun s hs _ => key s hs)
    (stronglyMeasurable_condExp.mono (le_sup_left : 𝒜 ≤ 𝒜 ⊔ ℬ)).aestronglyMeasurable).symm

/-- Conditioning a completely degenerate term on a proper part of its coordinates gives
zero. -/
theorem condExp_sup_eq_zero [IsProbabilityMeasure μ] {𝒜 ℬ 𝒞 : MeasurableSpace Ω}
    (h𝒜𝒞 : 𝒜 ≤ 𝒞) (h𝒞 : 𝒞 ≤ m0) (hℬ : ℬ ≤ m0) (hind : Indep 𝒞 ℬ μ)
    {X : Ω → ℝ} (hXm : StronglyMeasurable[𝒞] X) (hX : Integrable X μ)
    (h0 : μ[X | 𝒜] =ᵐ[μ] 0) :
    μ[X | 𝒜 ⊔ ℬ] =ᵐ[μ] 0 :=
  (condExp_sup_of_indep h𝒜𝒞 h𝒞 hℬ hind hXm hX).trans h0

/-! ## The latent variables, the levels and the revealing order -/

section Latent

variable {V ι T : Type*}

set_option warn.classDefReducibility false in
/-- `latentSigma U S` is the σ-field generated by the latent variables indexed by `S`. -/
def latentSigma (U : V → Ω → ℝ) (S : Set V) : MeasurableSpace Ω :=
  ⨆ v ∈ S, MeasurableSpace.comap (U v) inferInstance

theorem latentSigma_mono (U : V → Ω → ℝ) {S S' : Set V} (h : S ⊆ S') :
    latentSigma U S ≤ latentSigma U S' :=
  biSup_mono fun _ hv => h hv

theorem latentSigma_union (U : V → Ω → ℝ) (S S' : Set V) :
    latentSigma U (S ∪ S') = latentSigma U S ⊔ latentSigma U S' := by
  refine le_antisymm (iSup₂_le fun v hv => ?_)
    (sup_le (latentSigma_mono U Set.subset_union_left)
      (latentSigma_mono U Set.subset_union_right))
  rcases hv with h | h
  · exact le_sup_of_le_left (le_iSup₂ (f := fun w (_ : w ∈ S) =>
      MeasurableSpace.comap (U w) inferInstance) v h)
  · exact le_sup_of_le_right (le_iSup₂ (f := fun w (_ : w ∈ S') =>
      MeasurableSpace.comap (U w) inferInstance) v h)

theorem latentSigma_le {U : V → Ω → ℝ} (hU : ∀ v, Measurable (U v)) (S : Set V) :
    latentSigma U S ≤ m0 :=
  iSup₂_le fun v _ => (hU v).comap_le

theorem measurable_latentSigma (U : V → Ω → ℝ) {S : Set V} {v : V} (hv : v ∈ S) :
    Measurable[latentSigma U S] (U v) :=
  (comap_measurable (U v)).mono
    (le_iSup₂ (f := fun w (_ : w ∈ S) => MeasurableSpace.comap (U w) inferInstance) v hv) le_rfl

/-- Latent variables indexed by disjoint sets generate independent σ-fields. -/
theorem latentSigma_indep [IsProbabilityMeasure μ] {U : V → Ω → ℝ}
    (hU : ∀ v, Measurable (U v)) (hindep : iIndepFun U μ) {S S' : Set V}
    (hSS' : Disjoint S S') : Indep (latentSigma U S) (latentSigma U S') μ :=
  indep_iSup_of_disjoint (fun v => (hU v).comap_le) hindep hSS'

/-- `U_t = (U^{(k)}_{t_k})_{k ∈ e}`, the latent tuple indexed by the sub-tuple `t`. -/
def latentTuple (U : V → Ω → ℝ) (coord : T → ι → V) (t : T) : Ω → ι → ℝ :=
  fun ω k => U (coord t k) ω

/-- `g(U_t)`, the unweighted `t`-th term of the multilinear sum. -/
def degenTerm (U : V → Ω → ℝ) (coord : T → ι → V) (g : (ι → ℝ) → ℝ) (t : T) : Ω → ℝ :=
  fun ω => g (latentTuple U coord t ω)

/-- The indices of the latent variables in the sub-tuple `t`. -/
def tupleSupport (coord : T → ι → V) (t : T) : Set V := Set.range (coord t)

/-- `T := ∑_{t ∈ 𝒯_e} c_t g(U_t)`. -/
def degenSum [Fintype T] (U : V → Ω → ℝ) (coord : T → ι → V) (g : (ι → ℝ) → ℝ) (c : T → ℝ) :
    Ω → ℝ :=
  ∑ t : T, c t • degenTerm U coord g t

theorem degenSum_apply [Fintype T] (U : V → Ω → ℝ) (coord : T → ι → V) (g : (ι → ℝ) → ℝ)
    (c : T → ℝ) (ω : Ω) : degenSum U coord g c ω = ∑ t : T, c t * degenTerm U coord g t ω := by
  simp [degenSum, Finset.sum_apply]

theorem stronglyMeasurable_degenTerm (U : V → Ω → ℝ) (coord : T → ι → V) {g : (ι → ℝ) → ℝ}
    (hg : Measurable g) (t : T) {S : Set V} (hS : tupleSupport coord t ⊆ S) :
    StronglyMeasurable[latentSigma U S] (degenTerm U coord g t) := by
  have h : Measurable[latentSigma U S] (latentTuple U coord t) :=
    @Measurable.of_eval Ω ι (fun _ => ℝ) (latentSigma U S) (fun _ => inferInstance)
      (latentTuple U coord t) fun k => measurable_latentSigma U (hS ⟨k, rfl⟩)
  exact (hg.comp h).stronglyMeasurable

/-- The latent variables revealed before step `κ` of the ordering `step : V → ℕ`. No property
of `step` is assumed. -/
def revealed (step : V → ℕ) (κ : ℕ) : Set V := {v | step v < κ}

/-- `(ℱ_κ)`, the σ-field generated by the first `κ` latent variables, as a `Filtration`. -/
def latentFiltration {U : V → Ω → ℝ} (hU : ∀ v, Measurable (U v)) (step : V → ℕ) :
    Filtration ℕ m0 where
  seq κ := latentSigma U (revealed step κ)
  mono' _ _ hij := latentSigma_mono U fun _ hv => lt_of_lt_of_le hv hij
  le' _ := latentSigma_le hU _

@[simp] theorem latentFiltration_apply {U : V → Ω → ℝ} (hU : ∀ v, Measurable (U v))
    (step : V → ℕ) (κ : ℕ) :
    latentFiltration (m0 := m0) hU step κ = latentSigma U (revealed step κ) := rfl

section Revealed

variable [Fintype ι] [Fintype T]

/-- The sub-tuples all of whose coordinates are revealed by step `κ`. -/
def fullyRevealed (coord : T → ι → V) (step : V → ℕ) (κ : ℕ) : Finset T :=
  Finset.univ.filter fun t => ∀ k, step (coord t k) < κ

/-- `R_κ`: the sub-tuples all of whose coordinates are revealed by step `κ`, the last of them
at step `κ`. With zero-based indices this is `R_{κ+1}`. -/
def completedAt [DecidableEq T] (coord : T → ι → V) (step : V → ℕ) (κ : ℕ) : Finset T :=
  fullyRevealed coord step (κ + 1) \ fullyRevealed coord step κ

theorem mem_fullyRevealed {coord : T → ι → V} {step : V → ℕ} {κ : ℕ} {t : T} :
    t ∈ fullyRevealed coord step κ ↔ ∀ k, step (coord t k) < κ := by
  simp [fullyRevealed]

theorem fullyRevealed_subset {coord : T → ι → V} {step : V → ℕ} {κ κ' : ℕ} (h : κ ≤ κ') :
    fullyRevealed coord step κ ⊆ fullyRevealed coord step κ' := fun _ ht =>
  mem_fullyRevealed.2 fun k => lt_of_lt_of_le (mem_fullyRevealed.1 ht k) h

theorem tupleSupport_subset_revealed {coord : T → ι → V} {step : V → ℕ} {κ : ℕ} {t : T}
    (ht : t ∈ fullyRevealed coord step κ) : tupleSupport coord t ⊆ revealed step κ := by
  rintro v ⟨k, rfl⟩
  exact mem_fullyRevealed.1 ht k

theorem mem_completedAt [DecidableEq T] {coord : T → ι → V} {step : V → ℕ} {κ : ℕ} {t : T} :
    t ∈ completedAt coord step κ ↔
      (∀ k, step (coord t k) ≤ κ) ∧ ∃ k, κ ≤ step (coord t k) := by
  simp only [completedAt, Finset.mem_sdiff, mem_fullyRevealed, Nat.lt_succ_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [not_forall] at h2
    obtain ⟨k, hk⟩ := h2
    exact ⟨k, not_lt.1 hk⟩
  · rintro ⟨h1, k, hk⟩
    exact ⟨h1, fun h => absurd (h k) (not_lt.2 hk)⟩

/-- Each `t ∈ 𝒯_e` belongs to exactly one `R_κ`, namely at the largest position among its
coordinates. -/
theorem existsUnique_completedAt [DecidableEq T] [Nonempty ι] (coord : T → ι → V)
    (step : V → ℕ) (t : T) : ∃! κ, t ∈ completedAt coord step κ := by
  classical
  obtain ⟨k₀, -, hk₀⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset ι) Finset.univ_nonempty
      fun k => step (coord t k)
  refine ⟨Finset.univ.sup fun k => step (coord t k), mem_completedAt.2 ⟨?_, ⟨k₀, ?_⟩⟩, ?_⟩
  · exact fun k => Finset.le_sup (f := fun k => step (coord t k)) (Finset.mem_univ k)
  · exact hk₀.le
  · intro κ hκ
    obtain ⟨h1, k, hk⟩ := mem_completedAt.1 hκ
    refine le_antisymm ?_ ?_
    · exact le_trans hk (Finset.le_sup (f := fun k => step (coord t k)) (Finset.mem_univ k))
    · exact Finset.sup_le fun k _ => h1 k

end Revealed

end Latent

/-! ## The martingale representation -/

section Main

variable {V ι T : Type*} [Fintype ι] [Fintype T] [DecidableEq T] [IsProbabilityMeasure μ]
  {U : V → Ω → ℝ} {coord : T → ι → V} {g : (ι → ℝ) → ℝ} {c : T → ℝ} {step : V → ℕ}

omit [DecidableEq T] in
/-- The fully revealed terms are already `ℱ_κ`-measurable, so conditioning leaves them unchanged. -/
theorem condExp_degenTerm_of_mem (hU : ∀ v, Measurable (U v)) (hg : Measurable g) {t : T}
    (hint : Integrable (degenTerm U coord g t) μ) {κ : ℕ}
    (ht : t ∈ fullyRevealed coord step κ) :
    μ[degenTerm U coord g t | latentSigma U (revealed step κ)] = degenTerm U coord g t :=
  condExp_of_stronglyMeasurable (latentSigma_le hU _)
    (stronglyMeasurable_degenTerm U coord hg t (tupleSupport_subset_revealed ht)) hint

omit [DecidableEq T] in
/-- A term not yet fully revealed conditions to zero, by independence and complete
degeneracy. -/
theorem condExp_degenTerm_eq_zero (hU : ∀ v, Measurable (U v)) (hindep : iIndepFun U μ)
    (hg : Measurable g) {t : T} (hint : Integrable (degenTerm U coord g t) μ)
    (hdeg : ∀ e' : Set ι, e' ≠ Set.univ →
      μ[degenTerm U coord g t | latentSigma U (coord t '' e')] =ᵐ[μ] 0)
    {κ : ℕ} (ht : t ∉ fullyRevealed coord step κ) :
    μ[degenTerm U coord g t | latentSigma U (revealed step κ)] =ᵐ[μ] 0 := by
  have hsplit : latentSigma U (revealed step κ) =
      latentSigma U (revealed step κ ∩ tupleSupport coord t) ⊔
        latentSigma U (revealed step κ \ tupleSupport coord t) := by
    rw [← latentSigma_union]
    exact congrArg _ (Set.inter_union_sdiff _ _).symm
  have he' : (coord t) ⁻¹' revealed step κ ≠ Set.univ := by
    intro h
    refine ht (mem_fullyRevealed.2 fun k => ?_)
    have hk : k ∈ (coord t) ⁻¹' revealed step κ := by rw [h]; trivial
    exact hk
  have h0 : μ[degenTerm U coord g t |
      latentSigma U (revealed step κ ∩ tupleSupport coord t)] =ᵐ[μ] 0 := by
    have himg : coord t '' ((coord t) ⁻¹' revealed step κ)
        = revealed step κ ∩ tupleSupport coord t := Set.image_preimage_eq_inter_range
    rw [← himg]
    exact hdeg _ he'
  rw [hsplit]
  refine condExp_sup_eq_zero (𝒞 := latentSigma U (tupleSupport coord t))
    (latentSigma_mono U Set.inter_subset_right) (latentSigma_le hU _) (latentSigma_le hU _)
    (latentSigma_indep hU hindep (Set.disjoint_left.2 fun v hv hv' => hv'.2 hv))
    (stronglyMeasurable_degenTerm U coord hg t le_rfl) hint h0

/-- `𝔼[T ∣ ℱ_κ] = ∑_{t fully revealed by κ} c_t g(U_t)`. -/
theorem condExp_degenSum (hU : ∀ v, Measurable (U v)) (hindep : iIndepFun U μ)
    (hg : Measurable g) (hint : ∀ t, Integrable (degenTerm U coord g t) μ)
    (hdeg : ∀ (t : T) (e' : Set ι), e' ≠ Set.univ →
      μ[degenTerm U coord g t | latentSigma U (coord t '' e')] =ᵐ[μ] 0) (κ : ℕ) :
    μ[degenSum U coord g c | latentSigma U (revealed step κ)]
      =ᵐ[μ] fun ω => ∑ t ∈ fullyRevealed coord step κ, c t * degenTerm U coord g t ω := by
  have hterm : ∀ t : T, μ[c t • degenTerm U coord g t | latentSigma U (revealed step κ)]
      =ᵐ[μ] fun ω =>
        if t ∈ fullyRevealed coord step κ then c t * degenTerm U coord g t ω else 0 := by
    intro t
    have hsm := condExp_smul (μ := μ) (c t) (degenTerm U coord g t)
      (latentSigma U (revealed step κ))
    by_cases ht : t ∈ fullyRevealed coord step κ
    · filter_upwards [hsm] with ω hω
      rw [hω]
      simp [condExp_degenTerm_of_mem hU hg (hint t) ht, ht]
    · filter_upwards [hsm,
        condExp_degenTerm_eq_zero hU hindep hg (hint t) (hdeg t) ht] with ω hω hω0
      rw [hω]
      simp [ht, hω0]
  have hsum : μ[degenSum U coord g c | latentSigma U (revealed step κ)]
      =ᵐ[μ] ∑ t : T, μ[c t • degenTerm U coord g t | latentSigma U (revealed step κ)] :=
    condExp_finsetSum (fun t _ => (hint t).smul (c t)) _
  refine hsum.trans ?_
  filter_upwards [ae_all_iff.2 hterm] with ω hω
  simp only [Finset.sum_apply]
  rw [Finset.sum_congr rfl fun t _ => hω t]
  simp [Finset.sum_ite_mem]

/-- `D_κ`, the martingale difference across step `κ` (zero-based, so this is `D_{κ+1}`). -/
noncomputable def degenDiff (μ : Measure Ω) (U : V → Ω → ℝ) (coord : T → ι → V) (g : (ι → ℝ) → ℝ)
    (c : T → ℝ) (step : V → ℕ) (κ : ℕ) : Ω → ℝ :=
  μ[degenSum U coord g c | latentSigma U (revealed step (κ + 1))] -
    μ[degenSum U coord g c | latentSigma U (revealed step κ)]

/-- `D_κ = ∑_{t ∈ R_κ} c_t g(U_t)`. -/
theorem degenDiff_eq_sum_completedAt (hU : ∀ v, Measurable (U v)) (hindep : iIndepFun U μ)
    (hg : Measurable g) (hint : ∀ t, Integrable (degenTerm U coord g t) μ)
    (hdeg : ∀ (t : T) (e' : Set ι), e' ≠ Set.univ →
      μ[degenTerm U coord g t | latentSigma U (coord t '' e')] =ᵐ[μ] 0) (κ : ℕ) :
    degenDiff μ U coord g c step κ
      =ᵐ[μ] fun ω => ∑ t ∈ completedAt coord step κ, c t * degenTerm U coord g t ω := by
  filter_upwards [condExp_degenSum (c := c) hU hindep hg hint hdeg (κ + 1),
    condExp_degenSum (c := c) hU hindep hg hint hdeg κ] with ω h1 h2
  have hsub : fullyRevealed coord step κ ⊆ fullyRevealed coord step (κ + 1) :=
    fullyRevealed_subset (Nat.le_succ κ)
  show μ[degenSum U coord g c | latentSigma U (revealed step (κ + 1))] ω -
      μ[degenSum U coord g c | latentSigma U (revealed step κ)] ω = _
  rw [h1, h2, completedAt, Finset.sum_sdiff_eq_sub hsub]

omit [Fintype ι] [DecidableEq T] in
/-- `(D_κ)` is a martingale-difference sequence for `(ℱ_κ)`. -/
theorem condExp_degenDiff_eq_zero (hU : ∀ v, Measurable (U v)) (κ : ℕ) :
    μ[degenDiff μ U coord g c step κ | latentSigma U (revealed step κ)] =ᵐ[μ] 0 := by
  have hM : Martingale
      (fun κ => μ[degenSum U coord g c | latentFiltration (m0 := m0) hU step κ])
      (latentFiltration (m0 := m0) hU step) μ := martingale_condExp _ _ _
  have h1 : μ[degenDiff μ U coord g c step κ | latentSigma U (revealed step κ)] =ᵐ[μ]
      μ[μ[degenSum U coord g c | latentSigma U (revealed step (κ + 1))] |
          latentSigma U (revealed step κ)] -
        μ[μ[degenSum U coord g c | latentSigma U (revealed step κ)] |
          latentSigma U (revealed step κ)] :=
    condExp_sub integrable_condExp integrable_condExp _
  refine h1.trans ?_
  have h2 : μ[μ[degenSum U coord g c | latentSigma U (revealed step (κ + 1))] |
      latentSigma U (revealed step κ)]
      =ᵐ[μ] μ[degenSum U coord g c | latentSigma U (revealed step κ)] :=
    hM.condExp_ae_eq (Nat.le_succ κ)
  have h3 : μ[μ[degenSum U coord g c | latentSigma U (revealed step κ)] |
      latentSigma U (revealed step κ)]
      = μ[degenSum U coord g c | latentSigma U (revealed step κ)] :=
    condExp_of_stronglyMeasurable (latentSigma_le hU _) stronglyMeasurable_condExp
      integrable_condExp
  rw [h3]
  filter_upwards [h2] with ω hω2
  simp only [Pi.sub_apply, hω2, sub_self, Pi.zero_apply]

/-- `T = ∑_κ D_κ`: the sum telescopes, `𝔼[T ∣ ℱ_0] = 𝔼[T] = 0` and `T` is measurable with
respect to the final σ-field. `N` is any step by which every latent variable is revealed. -/
theorem degenSum_eq_sum_degenDiff [Nonempty ι] (hU : ∀ v, Measurable (U v))
    (hindep : iIndepFun U μ) (hg : Measurable g)
    (hint : ∀ t, Integrable (degenTerm U coord g t) μ)
    (hdeg : ∀ (t : T) (e' : Set ι), e' ≠ Set.univ →
      μ[degenTerm U coord g t | latentSigma U (coord t '' e')] =ᵐ[μ] 0)
    (N : ℕ) (hN : ∀ v, step v < N) :
    degenSum U coord g c
      =ᵐ[μ] fun ω => ∑ κ ∈ Finset.range N, degenDiff μ U coord g c step κ ω := by
  have hfull : fullyRevealed coord step N = Finset.univ :=
    Finset.eq_univ_of_forall fun t => mem_fullyRevealed.2 fun k => hN _
  have hnil : fullyRevealed coord step 0 = (∅ : Finset T) :=
    Finset.eq_empty_of_forall_notMem fun t ht =>
      absurd (mem_fullyRevealed.1 ht (Classical.arbitrary ι)) (Nat.not_lt_zero _)
  filter_upwards [condExp_degenSum (c := c) hU hindep hg hint hdeg N,
    condExp_degenSum (c := c) hU hindep hg hint hdeg 0] with ω hN' h0'
  have htel : ∑ κ ∈ Finset.range N, degenDiff μ U coord g c step κ ω =
      μ[degenSum U coord g c | latentSigma U (revealed step N)] ω -
        μ[degenSum U coord g c | latentSigma U (revealed step 0)] ω := by
    simpa [degenDiff] using
      Finset.sum_range_sub
        (fun κ => μ[degenSum U coord g c | latentSigma U (revealed step κ)] ω) N
  rw [htel, hN', h0', hfull, hnil]
  simp [degenSum_apply]

/-- **Lemma SM.C.2.** For independent latent variables, a square-integrable completely
degenerate kernel `g`, nonrandom weights `c` and any ordering `step`, `(D_κ)` is a
martingale-difference sequence, `T = ∑_κ D_κ`, `D_κ = ∑_{t ∈ R_κ} c_t g(U_t)`, and each
`t ∈ 𝒯_e` belongs to exactly one `R_κ`. -/
theorem martingale_representation [Nonempty ι] (hU : ∀ v, Measurable (U v))
    (hindep : iIndepFun U μ) (hg : Measurable g)
    (hsq : ∀ t, MemLp (degenTerm U coord g t) 2 μ)
    (hdeg : ∀ (t : T) (e' : Set ι), e' ≠ Set.univ →
      μ[degenTerm U coord g t | latentSigma U (coord t '' e')] =ᵐ[μ] 0)
    (N : ℕ) (hN : ∀ v, step v < N) :
    (∀ κ, μ[degenDiff μ U coord g c step κ | latentSigma U (revealed step κ)] =ᵐ[μ] 0) ∧
      degenSum U coord g c
        =ᵐ[μ] (fun ω => ∑ κ ∈ Finset.range N, degenDiff μ U coord g c step κ ω) ∧
      (∀ κ, degenDiff μ U coord g c step κ
        =ᵐ[μ] fun ω => ∑ t ∈ completedAt coord step κ, c t * degenTerm U coord g t ω) ∧
      (∀ t : T, ∃! κ, t ∈ completedAt coord step κ) := by
  have hint : ∀ t, Integrable (degenTerm U coord g t) μ := fun t => (hsq t).integrable one_le_two
  exact ⟨fun κ => condExp_degenDiff_eq_zero hU κ,
    degenSum_eq_sum_degenDiff hU hindep hg hint hdeg N hN,
    fun κ => degenDiff_eq_sum_completedAt hU hindep hg hint hdeg κ,
    existsUnique_completedAt coord step⟩

end Main

/-! ## A family of levels through one filtration

The components `γ` may have levels `ι γ` and sub-tuple types `T γ` of different sizes, but share
the latent index type `V` and the ordering `step`, so `∑_γ T^γ` is a single martingale. Each
statement below is the sum over `γ` of the corresponding single-component statement, using
linearity of `condExp`; complete degeneracy is required of each component at its level.
-/

section Multi

variable {V Γ : Type*} [Fintype Γ] {ι : Γ → Type*} [∀ γ, Fintype (ι γ)]
  {T : Γ → Type*} [∀ γ, Fintype (T γ)] [∀ γ, DecidableEq (T γ)] [IsProbabilityMeasure μ]
  {U : V → Ω → ℝ} {coord : ∀ γ, T γ → ι γ → V} {g : ∀ γ, (ι γ → ℝ) → ℝ}
  {c : ∀ γ, T γ → ℝ} {step : V → ℕ}

/-- `T := ∑_{γ ∈ Γ}∑_{t ∈ 𝒯_{e_γ}} c^γ_t g_γ(U_t)`, one term per component `γ`, the
components' levels of different sizes. -/
def multiDegenSum (U : V → Ω → ℝ) (coord : ∀ γ, T γ → ι γ → V)
    (g : ∀ γ, (ι γ → ℝ) → ℝ) (c : ∀ γ, T γ → ℝ) : Ω → ℝ :=
  ∑ γ : Γ, degenSum U (coord γ) (g γ) (c γ)

omit [∀ γ, Fintype (ι γ)] [∀ γ, DecidableEq (T γ)] in
theorem multiDegenSum_apply (U : V → Ω → ℝ) (coord : ∀ γ, T γ → ι γ → V)
    (g : ∀ γ, (ι γ → ℝ) → ℝ) (c : ∀ γ, T γ → ℝ) (ω : Ω) :
    multiDegenSum U coord g c ω
      = ∑ γ : Γ, ∑ t : T γ, c γ t * degenTerm U (coord γ) (g γ) t ω := by
  simp only [multiDegenSum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun γ _ => degenSum_apply U (coord γ) (g γ) (c γ) ω

omit [Fintype Γ] [∀ γ, Fintype (ι γ)] [∀ γ, DecidableEq (T γ)] [IsProbabilityMeasure μ] in
theorem integrable_degenSum_of_terms {γ : Γ}
    (hint : ∀ t : T γ, Integrable (degenTerm U (coord γ) (g γ) t) μ) :
    Integrable (degenSum U (coord γ) (g γ) (c γ)) μ :=
  integrable_finsetSum' _ fun t _ => (hint t).smul (c γ t)

omit [∀ γ, Fintype (ι γ)] [∀ γ, DecidableEq (T γ)] [IsProbabilityMeasure μ] in
theorem integrable_multiDegenSum
    (hint : ∀ (γ : Γ) (t : T γ), Integrable (degenTerm U (coord γ) (g γ) t) μ) :
    Integrable (multiDegenSum U coord g c) μ :=
  integrable_finsetSum' _ fun γ _ => integrable_degenSum_of_terms (hint γ)

/-- `D_κ` for the pooled sum, zero-based as `degenDiff` is. -/
noncomputable def multiDegenDiff (μ : Measure Ω) (U : V → Ω → ℝ)
    (coord : ∀ γ, T γ → ι γ → V) (g : ∀ γ, (ι γ → ℝ) → ℝ) (c : ∀ γ, T γ → ℝ)
    (step : V → ℕ) (κ : ℕ) : Ω → ℝ :=
  μ[multiDegenSum U coord g c | latentSigma U (revealed step (κ + 1))] -
    μ[multiDegenSum U coord g c | latentSigma U (revealed step κ)]

omit [∀ γ, Fintype (ι γ)] [∀ γ, DecidableEq (T γ)] [IsProbabilityMeasure μ] in
/-- `D_κ` of the pooled sum is the sum of the componentwise `D_κ`. -/
theorem multiDegenDiff_eq_sum_degenDiff
    (hint : ∀ (γ : Γ) (t : T γ), Integrable (degenTerm U (coord γ) (g γ) t) μ) (κ : ℕ) :
    multiDegenDiff μ U coord g c step κ
      =ᵐ[μ] fun ω => ∑ γ : Γ, degenDiff μ U (coord γ) (g γ) (c γ) step κ ω := by
  have hI : ∀ γ : Γ, Integrable (degenSum U (coord γ) (g γ) (c γ)) μ := fun γ =>
    integrable_degenSum_of_terms (hint γ)
  have h1 := condExp_finsetSum (μ := μ) (s := (Finset.univ : Finset Γ))
    (f := fun γ => degenSum U (coord γ) (g γ) (c γ)) (fun γ _ => hI γ)
    (latentSigma U (revealed step (κ + 1)))
  have h2 := condExp_finsetSum (μ := μ) (s := (Finset.univ : Finset Γ))
    (f := fun γ => degenSum U (coord γ) (g γ) (c γ)) (fun γ _ => hI γ)
    (latentSigma U (revealed step κ))
  filter_upwards [h1, h2] with ω hω1 hω2
  show (μ[∑ γ : Γ, degenSum U (coord γ) (g γ) (c γ) |
        latentSigma U (revealed step (κ + 1))]) ω
      - (μ[∑ γ : Γ, degenSum U (coord γ) (g γ) (c γ) |
        latentSigma U (revealed step κ)]) ω = _
  rw [hω1, hω2]
  simp only [Finset.sum_apply, degenDiff, Pi.sub_apply]
  rw [Finset.sum_sub_distrib]

omit [∀ γ, Fintype (ι γ)] [∀ γ, DecidableEq (T γ)] in
/-- `(D_κ)` is a martingale-difference sequence for the pooled sum. Only measurability of the
latent variables is needed. -/
theorem condExp_multiDegenDiff_eq_zero (hU : ∀ v, Measurable (U v)) (κ : ℕ) :
    μ[multiDegenDiff μ U coord g c step κ | latentSigma U (revealed step κ)] =ᵐ[μ] 0 := by
  have hM : Martingale
      (fun κ => μ[multiDegenSum U coord g c | latentFiltration (m0 := m0) hU step κ])
      (latentFiltration (m0 := m0) hU step) μ := martingale_condExp _ _ _
  have h1 : μ[multiDegenDiff μ U coord g c step κ | latentSigma U (revealed step κ)] =ᵐ[μ]
      μ[μ[multiDegenSum U coord g c | latentSigma U (revealed step (κ + 1))] |
          latentSigma U (revealed step κ)] -
        μ[μ[multiDegenSum U coord g c | latentSigma U (revealed step κ)] |
          latentSigma U (revealed step κ)] :=
    condExp_sub integrable_condExp integrable_condExp _
  refine h1.trans ?_
  have h2 : μ[μ[multiDegenSum U coord g c | latentSigma U (revealed step (κ + 1))] |
      latentSigma U (revealed step κ)]
      =ᵐ[μ] μ[multiDegenSum U coord g c | latentSigma U (revealed step κ)] :=
    hM.condExp_ae_eq (Nat.le_succ κ)
  have h3 : μ[μ[multiDegenSum U coord g c | latentSigma U (revealed step κ)] |
      latentSigma U (revealed step κ)]
      = μ[multiDegenSum U coord g c | latentSigma U (revealed step κ)] :=
    condExp_of_stronglyMeasurable (latentSigma_le hU _) stronglyMeasurable_condExp
      integrable_condExp
  rw [h3]
  filter_upwards [h2] with ω hω2
  simp only [Pi.sub_apply, hω2, sub_self, Pi.zero_apply]

/-- `D_κ = ∑_γ∑_{t ∈ R^γ_κ}c^γ_tg_γ(U_t)`, where `R^γ_κ` are the completion sets of component `γ`. -/
theorem multiDegenDiff_eq_sum_completedAt (hU : ∀ v, Measurable (U v))
    (hindep : iIndepFun U μ) (hg : ∀ γ : Γ, Measurable (g γ))
    (hint : ∀ (γ : Γ) (t : T γ), Integrable (degenTerm U (coord γ) (g γ) t) μ)
    (hdeg : ∀ (γ : Γ) (t : T γ) (e' : Set (ι γ)), e' ≠ Set.univ →
      μ[degenTerm U (coord γ) (g γ) t | latentSigma U (coord γ t '' e')] =ᵐ[μ] 0) (κ : ℕ) :
    multiDegenDiff μ U coord g c step κ
      =ᵐ[μ] fun ω => ∑ γ : Γ, ∑ t ∈ completedAt (coord γ) step κ,
        c γ t * degenTerm U (coord γ) (g γ) t ω := by
  have hcomp : ∀ γ : Γ, degenDiff μ U (coord γ) (g γ) (c γ) step κ
      =ᵐ[μ] fun ω => ∑ t ∈ completedAt (coord γ) step κ,
        c γ t * degenTerm U (coord γ) (g γ) t ω := fun γ =>
    degenDiff_eq_sum_completedAt (c := c γ) hU hindep (hg γ) (hint γ) (hdeg γ) κ
  filter_upwards [multiDegenDiff_eq_sum_degenDiff (c := c) hint κ, ae_all_iff.2 hcomp]
    with ω hω hωγ
  rw [hω]
  exact Finset.sum_congr rfl fun γ _ => hωγ γ

/-- `T = ∑_κ D_κ` for the pooled sum. -/
theorem multiDegenSum_eq_sum_multiDegenDiff [∀ γ, Nonempty (ι γ)] (hU : ∀ v, Measurable (U v))
    (hindep : iIndepFun U μ) (hg : ∀ γ : Γ, Measurable (g γ))
    (hint : ∀ (γ : Γ) (t : T γ), Integrable (degenTerm U (coord γ) (g γ) t) μ)
    (hdeg : ∀ (γ : Γ) (t : T γ) (e' : Set (ι γ)), e' ≠ Set.univ →
      μ[degenTerm U (coord γ) (g γ) t | latentSigma U (coord γ t '' e')] =ᵐ[μ] 0)
    (N : ℕ) (hN : ∀ v, step v < N) :
    multiDegenSum U coord g c
      =ᵐ[μ] fun ω => ∑ κ ∈ Finset.range N, multiDegenDiff μ U coord g c step κ ω := by
  have hone : ∀ γ : Γ, degenSum U (coord γ) (g γ) (c γ)
      =ᵐ[μ] fun ω => ∑ κ ∈ Finset.range N,
        degenDiff μ U (coord γ) (g γ) (c γ) step κ ω := fun γ =>
    degenSum_eq_sum_degenDiff (c := c γ) hU hindep (hg γ) (hint γ) (hdeg γ) N hN
  have hdiff : ∀ κ : ℕ, multiDegenDiff μ U coord g c step κ
      =ᵐ[μ] fun ω => ∑ γ : Γ, degenDiff μ U (coord γ) (g γ) (c γ) step κ ω := fun κ =>
    multiDegenDiff_eq_sum_degenDiff (c := c) hint κ
  filter_upwards [ae_all_iff.2 hone, ae_all_iff.2 hdiff] with ω hωγ hωκ
  have hL : ∑ γ : Γ, degenSum U (coord γ) (g γ) (c γ) ω
      = ∑ γ : Γ, ∑ κ ∈ Finset.range N,
        degenDiff μ U (coord γ) (g γ) (c γ) step κ ω :=
    Finset.sum_congr rfl fun γ _ => hωγ γ
  have hR : ∑ κ ∈ Finset.range N, multiDegenDiff μ U coord g c step κ ω
      = ∑ κ ∈ Finset.range N, ∑ γ : Γ,
        degenDiff μ U (coord γ) (g γ) (c γ) step κ ω :=
    Finset.sum_congr rfl fun κ _ => hωκ κ
  show (∑ γ : Γ, degenSum U (coord γ) (g γ) (c γ)) ω = _
  rw [Finset.sum_apply, hL, hR, Finset.sum_comm]

/-- **Lemma SM.C.2 for a family of components of different arities.** The hypotheses are
the single-component ones held componentwise; the last conclusion holds for each `γ`
separately. -/
theorem multi_martingale_representation [∀ γ, Nonempty (ι γ)] (hU : ∀ v, Measurable (U v))
    (hindep : iIndepFun U μ) (hg : ∀ γ : Γ, Measurable (g γ))
    (hsq : ∀ (γ : Γ) (t : T γ), MemLp (degenTerm U (coord γ) (g γ) t) 2 μ)
    (hdeg : ∀ (γ : Γ) (t : T γ) (e' : Set (ι γ)), e' ≠ Set.univ →
      μ[degenTerm U (coord γ) (g γ) t | latentSigma U (coord γ t '' e')] =ᵐ[μ] 0)
    (N : ℕ) (hN : ∀ v, step v < N) :
    (∀ κ, μ[multiDegenDiff μ U coord g c step κ | latentSigma U (revealed step κ)] =ᵐ[μ] 0) ∧
      multiDegenSum U coord g c
        =ᵐ[μ] (fun ω => ∑ κ ∈ Finset.range N, multiDegenDiff μ U coord g c step κ ω) ∧
      (∀ κ, multiDegenDiff μ U coord g c step κ
        =ᵐ[μ] fun ω => ∑ γ : Γ, ∑ t ∈ completedAt (coord γ) step κ,
          c γ t * degenTerm U (coord γ) (g γ) t ω) ∧
      (∀ (γ : Γ) (t : T γ), ∃! κ, t ∈ completedAt (coord γ) step κ) := by
  have hint : ∀ (γ : Γ) (t : T γ), Integrable (degenTerm U (coord γ) (g γ) t) μ :=
    fun γ t => (hsq γ t).integrable one_le_two
  exact ⟨fun κ => condExp_multiDegenDiff_eq_zero hU κ,
    multiDegenSum_eq_sum_multiDegenDiff hU hindep hg hint hdeg N hN,
    fun κ => multiDegenDiff_eq_sum_completedAt hU hindep hg hint hdeg κ,
    fun γ => existsUnique_completedAt (coord γ) step⟩

end Multi


end DegenerateSum

end Multiway
