import Multiway.QuadformE2

/-!
# Variance of a quadratic form under interaction dependence: the independence inputs

This file completes Lemma SM.C.6 of the paper (variance of a quadratic form under interaction
dependence) under Regime 2 of the dependence assumption, with latent variables taking finitely
many values. It proves the two hypotheses `hsupp` (vanishing of fourth cumulants of unsupported
assignments) and `hbdd` (a uniform cumulant bound) that `QuadformE2.var_quadForm_le_levels`
leaves open. The expectation is `prodExp q`, the average under a product law `q` over
`Ω := Site D L O → V`, a linear functional on `Ω → ℝ`.

## Notation

* `Site D L O := (D × L) ⊕ O`: `Sum.inl (k, j)` carries the latent `U^{(k)}_j` and `Sum.inr o`
  carries `ε_o` (distinct from `Multiway.Site`);
* `xi γ o` is `ξ^γ_o`, and `siteSet γ o` is the set of sites it depends on.

## Main results

* `assignCum_eq_zero_of_not_supported`, `abs_cum4_le`: the hypotheses `hsupp` and `hbdd`, with
  `K = C + 3((C+1)/2)²` for `E[ξ⁴] ≤ C`.
* `var_quadForm_le_regime2`: Lemma SM.C.6 under Regime 2.
* `regime2_witness`: a model satisfying every hypothesis, with `Var(ζ'Wζ ∣ 𝒟) = 4`.
-/

namespace Multiway
namespace QuadformE2Indep

open Finset
open Multiway.QuadformE2

/-! ## 1. A finite product law

`Ω := S → V`, one coordinate per site with values in a finite set `V`; `q s` is the marginal
law at site `s`. -/

section Product

variable {S V : Type*} [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V]

/-- `f` does not see coordinate `s`. -/
def FreeAt (s : S) (f : (S → V) → ℝ) : Prop :=
  ∀ (ω : S → V) (v : V), f (Function.update ω s v) = f ω

/-- `f` is a function of the coordinates in `T` alone. -/
def DependsOn (T : Finset S) (f : (S → V) → ℝ) : Prop :=
  ∀ ω ω' : S → V, (∀ s ∈ T, ω s = ω' s) → f ω = f ω'

/-- Complete degeneracy at one coordinate: averaging `f` over the coordinate `s`, with every
other coordinate held fixed, gives zero. -/
def AvgZeroAt (q : S → V → ℝ) (s : S) (f : (S → V) → ℝ) : Prop :=
  ∀ ω : S → V, ∑ v : V, q s v * f (Function.update ω s v) = 0

/-- The product law on `Ω`. -/
def prodLaw (q : S → V → ℝ) : (S → V) → ℝ := fun ω => ∏ s, q s (ω s)

/-- The expectation under the product law, as `QuadformE2.condAvg` on the finite space `Ω`: a
linear functional `(Ω → ℝ) →ₗ[ℝ] ℝ`. -/
noncomputable def prodExp (q : S → V → ℝ) : ((S → V) → ℝ) →ₗ[ℝ] ℝ :=
  condAvg (prodLaw q) Finset.univ

omit [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V] in
theorem dependsOn_mono {T T' : Finset S} {f : (S → V) → ℝ} (hTT : T ⊆ T')
    (hf : DependsOn T f) : DependsOn T' f :=
  fun ω ω' h => hf ω ω' fun s hs => h s (hTT hs)

omit [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V] in
theorem dependsOn_mul {T : Finset S} {f g : (S → V) → ℝ} (hf : DependsOn T f)
    (hg : DependsOn T g) : DependsOn T (f * g) := by
  intro ω ω' h
  simp only [Pi.mul_apply, hf ω ω' h, hg ω ω' h]

omit [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V] in
theorem dependsOn_one (T : Finset S) : DependsOn T (1 : (S → V) → ℝ) := by
  intro ω ω' _; rfl

omit [Fintype S] [Fintype V] [DecidableEq V] in
/-- A function of the coordinates in `T` does not see a coordinate outside `T`. -/
theorem freeAt_of_dependsOn {T : Finset S} {s : S} (hs : s ∉ T) {f : (S → V) → ℝ}
    (hf : DependsOn T f) : FreeAt s f := by
  intro ω v
  refine hf _ _ fun t ht => ?_
  exact Function.update_of_ne (by rintro rfl; exact hs ht) _ _

omit [Fintype S] [Fintype V] [DecidableEq V] in
theorem freeAt_mul {s : S} {f g : (S → V) → ℝ} (hf : FreeAt s f) (hg : FreeAt s g) :
    FreeAt s (f * g) := by
  intro ω v
  simp only [Pi.mul_apply, hf ω v, hg ω v]

omit [Fintype S] [Fintype V] [DecidableEq V] in
theorem freeAt_one (s : S) : FreeAt s (1 : (S → V) → ℝ) := fun _ _ => rfl

end Product

/-! ## 2. Splitting the sum over `Ω`

`Ω` splits along one coordinate, and along a set of coordinates. -/

section Splitting

variable {S V : Type*} [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V]

/-- The point of `Ω` with value `v` at `s₀` and `ω'` elsewhere. -/
def splice (s₀ : S) (v : V) (ω' : {t : S // t ≠ s₀} → V) : S → V :=
  fun t => if h : t = s₀ then v else ω' ⟨t, h⟩

omit [Fintype S] [Fintype V] [DecidableEq V] in
@[simp] theorem splice_self (s₀ : S) (v : V) (ω' : {t : S // t ≠ s₀} → V) :
    splice s₀ v ω' s₀ = v := by simp [splice]

omit [Fintype S] [Fintype V] [DecidableEq V] in
theorem splice_of_ne {s₀ t : S} (h : t ≠ s₀) (v : V) (ω' : {t : S // t ≠ s₀} → V) :
    splice s₀ v ω' t = ω' ⟨t, h⟩ := by simp [splice, h]

omit [Fintype S] [Fintype V] [DecidableEq V] in
/-- Changing the value at `s₀` is `Function.update`. -/
theorem splice_eq_update (s₀ : S) (v v₀ : V) (ω' : {t : S // t ≠ s₀} → V) :
    splice s₀ v ω' = Function.update (splice s₀ v₀ ω') s₀ v := by
  funext t
  by_cases h : t = s₀
  · subst h; simp
  · rw [Function.update_of_ne h, splice_of_ne h, splice_of_ne h]

omit [Fintype S] [Fintype V] [DecidableEq V] in
theorem splice_bijective (s₀ : S) :
    Function.Bijective (fun x : V × ({t : S // t ≠ s₀} → V) => splice s₀ x.1 x.2) := by
  constructor
  · rintro ⟨v₁, a₁⟩ ⟨v₂, a₂⟩ h
    replace h : splice s₀ v₁ a₁ = splice s₀ v₂ a₂ := h
    have h0 : v₁ = v₂ := by
      have := congrFun h s₀; simpa using this
    subst h0
    refine Prod.ext rfl ?_
    funext t
    have ht := congrFun h t.1
    rw [splice_of_ne t.2, splice_of_ne t.2] at ht
    exact ht
  · intro ω
    refine ⟨(ω s₀, fun t => ω t.1), ?_⟩
    show splice s₀ (ω s₀) (fun t => ω t.1) = ω
    funext t
    by_cases h : t = s₀
    · subst h; simp
    · rw [splice_of_ne h]

omit [DecidableEq V] in
/-- `Ω` splits along one coordinate. -/
theorem sum_split_one (s₀ : S) (F : (S → V) → ℝ) :
    ∑ ω : S → V, F ω = ∑ v : V, ∑ ω' : {t : S // t ≠ s₀} → V, F (splice s₀ v ω') := by
  rw [← (splice_bijective (V := V) s₀).sum_comp F, Fintype.sum_prod_type]

/-- The point of `Ω` with values `a` on `T` and `b` on `Tᶜ`. The second block is indexed by
`↥(Tᶜ)`, so that `Finset.prod_coe_sort` and `Finset.prod_mul_prod_compl` apply directly. -/
def splice2 (T : Finset S) (a : ↥T → V) (b : ↥(Tᶜ) → V) : S → V :=
  fun t => if h : t ∈ T then a ⟨t, h⟩ else b ⟨t, Finset.mem_compl.mpr h⟩

omit [Fintype V] [DecidableEq V] in
theorem splice2_of_mem {T : Finset S} {t : S} (h : t ∈ T) (a : ↥T → V) (b : ↥(Tᶜ) → V) :
    splice2 T a b t = a ⟨t, h⟩ := by simp [splice2, h]

omit [Fintype V] [DecidableEq V] in
theorem splice2_of_memCompl {T : Finset S} {t : S} (h : t ∈ Tᶜ) (a : ↥T → V) (b : ↥(Tᶜ) → V) :
    splice2 T a b t = b ⟨t, h⟩ := by
  have h' : t ∉ T := Finset.mem_compl.mp h
  simp [splice2, h']

omit [Fintype V] [DecidableEq V] in
theorem splice2_bijective (T : Finset S) :
    Function.Bijective (fun x : (↥T → V) × (↥(Tᶜ) → V) => splice2 T x.1 x.2) := by
  constructor
  · rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
    replace h : splice2 T a₁ b₁ = splice2 T a₂ b₂ := h
    refine Prod.ext ?_ ?_
    · funext t
      have ht := congrFun h t.1
      rw [splice2_of_mem t.2, splice2_of_mem t.2] at ht
      exact ht
    · funext t
      have ht := congrFun h t.1
      rw [splice2_of_memCompl t.2, splice2_of_memCompl t.2] at ht
      exact ht
  · intro ω
    refine ⟨(fun t => ω t.1, fun t => ω t.1), ?_⟩
    show splice2 T (fun t => ω t.1) (fun t => ω t.1) = ω
    funext t
    by_cases h : t ∈ T
    · rw [splice2_of_mem h]
    · rw [splice2_of_memCompl (Finset.mem_compl.mpr h)]

omit [DecidableEq V] in
/-- `Ω` splits along a set of coordinates. -/
theorem sum_split_block (T : Finset S) (F : (S → V) → ℝ) :
    ∑ ω : S → V, F ω = ∑ a : ↥T → V, ∑ b : ↥(Tᶜ) → V, F (splice2 T a b) := by
  rw [← (splice2_bijective (V := V) T).sum_comp F, Fintype.sum_prod_type]

end Splitting

/-! ## 3. Two properties of the product law -/

section ProdExp

variable {S V : Type*} [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V]
variable {q : S → V → ℝ}

omit [DecidableEq S] [Fintype V] [DecidableEq V] in
theorem prodLaw_nonneg (hq0 : ∀ s v, 0 ≤ q s v) (ω : S → V) : 0 ≤ prodLaw q ω :=
  Finset.prod_nonneg fun s _ => hq0 s (ω s)

omit [DecidableEq V] in
/-- The product law is a probability law: `∑_ω ∏_s q_s(ω_s) = ∏_s ∑_v q_s(v) = 1`. -/
theorem sum_prod_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → V → ℝ)
    (h1 : ∀ i, ∑ v : V, r i v = 1) : ∑ x : ι → V, ∏ i, r i (x i) = 1 := by
  rw [← Fintype.prod_sum r]
  simp [h1]

omit [DecidableEq V] in
theorem sum_prodLaw (hq1 : ∀ s, ∑ v : V, q s v = 1) :
    ∑ ω : S → V, prodLaw q ω = 1 :=
  sum_prod_eq_one q hq1

/-- The marginal law of the block `T`, as a function of that block's coordinates alone. -/
def blockLaw (q : S → V → ℝ) (T : Finset S) (a : ↥T → V) : ℝ := ∏ t : ↥T, q t.1 (a t)

omit [Fintype S] in
omit [DecidableEq V] in
theorem sum_blockLaw (hq1 : ∀ s, ∑ v : V, q s v = 1) (T : Finset S) :
    ∑ a : ↥T → V, blockLaw q T a = 1 :=
  sum_prod_eq_one (fun (t : ↥T) (v : V) => q t.1 v) fun t => hq1 t.1

omit [Fintype V] [DecidableEq V] in
/-- The product law factorizes across a block and its complement. -/
theorem prodLaw_splice2 (T : Finset S) (a : ↥T → V) (b : ↥(Tᶜ) → V) :
    prodLaw q (splice2 T a b) = blockLaw q T a * blockLaw q Tᶜ b := by
  have e1 : (∏ t : ↥T, q t.1 (splice2 T a b t.1)) = blockLaw q T a :=
    Finset.prod_congr rfl fun t _ => by rw [splice2_of_mem t.2]
  have e2 : (∏ t : ↥(Tᶜ), q t.1 (splice2 T a b t.1)) = blockLaw q Tᶜ b :=
    Finset.prod_congr rfl fun t _ => by rw [splice2_of_memCompl t.2]
  rw [← e1, ← e2, Finset.prod_coe_sort T fun s => q s (splice2 T a b s),
    Finset.prod_coe_sort Tᶜ fun s => q s (splice2 T a b s)]
  exact (Finset.prod_mul_prod_compl T fun s => q s (splice2 T a b s)).symm

omit [DecidableEq V] in
theorem prodExp_apply (hq1 : ∀ s, ∑ v : V, q s v = 1) (f : (S → V) → ℝ) :
    prodExp q f = ∑ ω : S → V, prodLaw q ω * f ω := by
  simp [prodExp, condAvg_apply, sum_prodLaw hq1]

omit [DecidableEq V] in
theorem prodExp_one (hq1 : ∀ s, ∑ v : V, q s v = 1) :
    prodExp q (1 : (S → V) → ℝ) = 1 := by
  rw [prodExp_apply hq1]
  simpa using sum_prodLaw (q := q) hq1

omit [DecidableEq V] in
theorem prodExp_mono (hq0 : ∀ s v, 0 ≤ q s v) (hq1 : ∀ s, ∑ v : V, q s v = 1)
    {f g : (S → V) → ℝ} (h : ∀ ω, f ω ≤ g ω) : prodExp q f ≤ prodExp q g := by
  rw [prodExp_apply hq1, prodExp_apply hq1]
  exact Finset.sum_le_sum fun ω _ =>
    mul_le_mul_of_nonneg_left (h ω) (prodLaw_nonneg hq0 ω)

omit [DecidableEq V] in
/-- `|E f| ≤ c` from a pointwise two-sided bound by a function of expectation at most `c`. -/
theorem abs_prodExp_le (hq0 : ∀ s v, 0 ≤ q s v) (hq1 : ∀ s, ∑ v : V, q s v = 1)
    {f g : (S → V) → ℝ} (h : ∀ ω, |f ω| ≤ g ω) {c : ℝ} (hg : prodExp q g ≤ c) :
    |prodExp q f| ≤ c := by
  have h1 : prodExp q f ≤ prodExp q g :=
    prodExp_mono hq0 hq1 fun ω => le_trans (le_abs_self _) (h ω)
  have h2 : prodExp q (-f) ≤ prodExp q g :=
    prodExp_mono hq0 hq1 fun ω => by
      simpa using le_trans (neg_le_abs (f ω)) (h ω)
  rw [map_neg] at h2
  rw [abs_le]
  constructor <;> linarith

omit [DecidableEq V] in
/-- If `f` averages to zero over the coordinate `s₀` and `g` does not depend on it, then
`E[fg] = 0`. -/
theorem prodExp_mul_eq_zero_of_avgZeroAt [Nonempty V] (hq1 : ∀ s, ∑ v : V, q s v = 1)
    {s₀ : S} {f g : (S → V) → ℝ} (hf : AvgZeroAt q s₀ f) (hg : FreeAt s₀ g) :
    prodExp q (f * g) = 0 := by
  classical
  obtain ⟨v₀⟩ := ‹Nonempty V›
  rw [prodExp_apply hq1]
  rw [sum_split_one s₀ (fun ω => prodLaw q ω * (f * g) ω), Finset.sum_comm]
  refine Finset.sum_eq_zero fun ω' _ => ?_
  set τ : S → V := splice s₀ v₀ ω' with hτ
  have hrest : ∀ v : V, prodLaw q (splice s₀ v ω')
      = q s₀ v * ∏ t ∈ Finset.univ.erase s₀, q t (τ t) := by
    intro v
    rw [prodLaw, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ s₀), splice_self]
    congr 1
    refine Finset.prod_congr rfl fun t ht => ?_
    have htne : t ≠ s₀ := (Finset.mem_erase.mp ht).1
    rw [splice_of_ne htne, hτ, splice_of_ne htne]
  have hupd : ∀ v : V, splice s₀ v ω' = Function.update τ s₀ v := fun v =>
    splice_eq_update s₀ v v₀ ω'
  calc ∑ v : V, prodLaw q (splice s₀ v ω') * (f * g) (splice s₀ v ω')
      = (∏ t ∈ Finset.univ.erase s₀, q t (τ t)) * g τ
          * ∑ v : V, q s₀ v * f (Function.update τ s₀ v) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [hrest v, hupd v]
        simp only [Pi.mul_apply, hg τ v]
        ring
    _ = 0 := by rw [hf τ]; ring

omit [DecidableEq V] in
/-- Functions of disjoint sets of coordinates are independent: `E[fg] = E[f]E[g]`. -/
theorem prodExp_mul_eq_mul_of_disjoint [Nonempty V] (hq1 : ∀ s, ∑ v : V, q s v = 1)
    {T T' : Finset S} (hTT : ∀ s ∈ T', s ∉ T) {f g : (S → V) → ℝ}
    (hf : DependsOn T f) (hg : DependsOn T' g) :
    prodExp q (f * g) = prodExp q f * prodExp q g := by
  classical
  obtain ⟨v₀⟩ := ‹Nonempty V›
  have hfval : ∀ (a : ↥T → V) (b b' : ↥(Tᶜ) → V),
      f (splice2 T a b) = f (splice2 T a b') := by
    intro a b b'
    refine hf _ _ fun s hs => ?_
    rw [splice2_of_mem hs, splice2_of_mem hs]
  have hgval : ∀ (a a' : ↥T → V) (b : ↥(Tᶜ) → V),
      g (splice2 T a b) = g (splice2 T a' b) := by
    intro a a' b
    refine hg _ _ fun s hs => ?_
    have hsT : s ∈ Tᶜ := Finset.mem_compl.mpr (hTT s hs)
    rw [splice2_of_memCompl hsT, splice2_of_memCompl hsT]
  set a₀ : ↥T → V := fun _ => v₀
  set b₀ : ↥(Tᶜ) → V := fun _ => v₀
  have hEf : prodExp q f = ∑ a : ↥T → V, blockLaw q T a * f (splice2 T a b₀) := by
    rw [prodExp_apply hq1, sum_split_block T (fun ω => prodLaw q ω * f ω)]
    refine Finset.sum_congr rfl fun a _ => ?_
    calc ∑ b : ↥(Tᶜ) → V, prodLaw q (splice2 T a b) * f (splice2 T a b)
        = ∑ b : ↥(Tᶜ) → V, (blockLaw q T a * f (splice2 T a b₀)) * blockLaw q Tᶜ b := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [prodLaw_splice2 T a b, hfval a b b₀]; ring
      _ = blockLaw q T a * f (splice2 T a b₀) := by
          rw [← Finset.mul_sum, sum_blockLaw hq1, mul_one]
  have hEg : prodExp q g = ∑ b : ↥(Tᶜ) → V, blockLaw q Tᶜ b * g (splice2 T a₀ b) := by
    rw [prodExp_apply hq1, sum_split_block T (fun ω => prodLaw q ω * g ω)]
    calc ∑ a : ↥T → V, ∑ b : ↥(Tᶜ) → V,
            prodLaw q (splice2 T a b) * g (splice2 T a b)
        = ∑ a : ↥T → V, blockLaw q T a
            * ∑ b : ↥(Tᶜ) → V, blockLaw q Tᶜ b * g (splice2 T a₀ b) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [prodLaw_splice2 T a b, hgval a a₀ b]; ring
      _ = ∑ b : ↥(Tᶜ) → V, blockLaw q Tᶜ b * g (splice2 T a₀ b) := by
          rw [← Finset.sum_mul, sum_blockLaw hq1, one_mul]
  rw [prodExp_apply hq1, sum_split_block T (fun ω => prodLaw q ω * (f * g) ω), hEf, hEg,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.mul_apply]
  rw [prodLaw_splice2 T a b, hfval a b b₀, hgval a a₀ b]
  ring

end ProdExp

/-! ## 4. The sites

Each latent `U^{(k)}_j` and each `ε_o` has its own coordinate, so the independence of the `ε_o`
from each other and from the latent collection is a consequence of the product law. -/

section Sites

variable {D L O Γ₀ : Type*} [DecidableEq D] [DecidableEq L] [DecidableEq O]

/-- The coordinates of the latent space: one per (dimension, category) pair, and one private
coordinate per observation. -/
abbrev Site (D L O : Type*) := (D × L) ⊕ O

/-- The site that `ξ^γ_o` occupies at dimension `k`: `(k, i_k(o))` for a kernel, and `o`'s own
private site for the symbol `ε`. -/
def sitemap (idio : Γ₀ → Prop) [DecidablePred idio] (idx : D → O → L)
    (γ : Γ₀) (k : D) (o : O) : Site D L O :=
  if idio γ then Sum.inr o else Sum.inl (k, idx k o)

/-- The set of sites `ξ^γ_o` may see: `{(k, i_k(o)) : k ∈ e_γ}` for a kernel, `{o}` for `ε`. -/
def siteSet (idio : Γ₀ → Prop) [DecidablePred idio] (idx : D → O → L) (lev : Γ₀ → Finset D)
    (γ : Γ₀) (o : O) : Finset (Site D L O) :=
  (lev γ).image fun k => sitemap idio idx γ k o

variable {idio : Γ₀ → Prop} [DecidablePred idio] {idx : D → O → L} {lev : Γ₀ → Finset D}

omit [DecidableEq D] [DecidableEq L] [DecidableEq O] in
theorem sitemap_of_idio {γ : Γ₀} (h : idio γ) (k : D) (o : O) :
    sitemap idio idx γ k o = Sum.inr o := by simp [sitemap, h]

omit [DecidableEq D] [DecidableEq L] [DecidableEq O] in
theorem sitemap_of_not_idio {γ : Γ₀} (h : ¬ idio γ) (k : D) (o : O) :
    sitemap idio idx γ k o = Sum.inl (k, idx k o) := by simp [sitemap, h]

theorem mem_siteSet {γ : Γ₀} {k : D} {o : O} (hk : k ∈ lev γ) :
    sitemap idio idx γ k o ∈ siteSet idio idx lev γ o :=
  Finset.mem_image_of_mem _ hk

theorem siteSet_nonempty {γ : Γ₀} (o : O) (h : (lev γ).Nonempty) :
    (siteSet idio idx lev γ o).Nonempty :=
  h.image _

/-- If the site that `(γ, o)` occupies at `k` is also occupied by `(γ', o')`, then `k` belongs to
the level set of `γ'` and the two observations agree at `k`. -/
theorem mem_lev_and_idx_eq_of_mem_siteSet [Fintype D]
    (hidio : ∀ γ : Γ₀, idio γ → lev γ = Finset.univ)
    {γ γ' : Γ₀} {k : D} {o o' : O} (hk : k ∈ lev γ)
    (hmem : sitemap idio idx γ k o ∈ siteSet idio idx lev γ' o') :
    k ∈ lev γ' ∧ idx k o' = idx k o := by
  rw [siteSet, Finset.mem_image] at hmem
  obtain ⟨k', hk', heq⟩ := hmem
  by_cases hg : idio γ <;> by_cases hg' : idio γ'
  · rw [sitemap_of_idio hg', sitemap_of_idio hg] at heq
    have ho : o' = o := Sum.inr_injective heq
    subst ho
    exact ⟨by rw [hidio γ' hg']; exact Finset.mem_univ k, rfl⟩
  · rw [sitemap_of_not_idio hg', sitemap_of_idio hg] at heq
    exact absurd heq (by simp)
  · rw [sitemap_of_idio hg', sitemap_of_not_idio hg] at heq
    exact absurd heq (by simp)
  · rw [sitemap_of_not_idio hg', sitemap_of_not_idio hg] at heq
    have hpair : (k', idx k' o') = (k, idx k o) := Sum.inl_injective heq
    have hk2 : k' = k := congrArg Prod.fst hpair
    have hl : idx k' o' = idx k o := congrArg Prod.snd hpair
    subst hk2
    exact ⟨hk', hl⟩

end Sites

/-! ## 5. An unshared site kills the cumulant

If one argument occupies a site no other argument occupies, it averages to zero over that site
while the others do not depend on it, so every term of the moment-cumulant formula vanishes. -/

section PropertyOne

variable {S V : Type*} [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V] [Nonempty V]
variable {q : S → V → ℝ}

omit [DecidableEq V] in
/-- The mean of a variable that averages to zero over one of its own coordinates. -/
theorem prodExp_eq_zero_of_avgZeroAt (hq1 : ∀ s, ∑ v : V, q s v = 1) {s₀ : S}
    {f : (S → V) → ℝ} (hf : AvgZeroAt q s₀ f) : prodExp q f = 0 := by
  calc prodExp q f = prodExp q (f * 1) := by rw [mul_one]
    _ = 0 := prodExp_mul_eq_zero_of_avgZeroAt hq1 hf (freeAt_one s₀)

omit [DecidableEq V] in
/-- The fourth cumulant vanishes when the first argument averages to zero over a site the other
three do not see. -/
theorem cum4_eq_zero_of_avgZeroAt (hq1 : ∀ s, ∑ v : V, q s v = 1) {s₀ : S}
    {a b c d : (S → V) → ℝ} (ha : AvgZeroAt q s₀ a) (hb : FreeAt s₀ b) (hc : FreeAt s₀ c)
    (hd : FreeAt s₀ d) : cum4 (prodExp q) a b c d = 0 := by
  refine cum4_eq_zero_of_moments_vanish _ ?_ ?_ ?_ ?_
  · have hass : a * b * c * d = a * (b * c * d) := by ring
    rw [hass]
    exact prodExp_mul_eq_zero_of_avgZeroAt hq1 ha (freeAt_mul (freeAt_mul hb hc) hd)
  · exact prodExp_mul_eq_zero_of_avgZeroAt hq1 ha hb
  · exact prodExp_mul_eq_zero_of_avgZeroAt hq1 ha hc
  · exact prodExp_mul_eq_zero_of_avgZeroAt hq1 ha hd

omit [DecidableEq V] in
/-- The same, with the unshared argument in any of the four positions. -/
theorem cum4_eq_zero_of_unshared (hq1 : ∀ s, ∑ v : V, q s v = 1) {s₀ : S}
    {X : Fin 4 → (S → V) → ℝ} {i₀ : Fin 4} (hz : AvgZeroAt q s₀ (X i₀))
    (hf : ∀ i, i ≠ i₀ → FreeAt s₀ (X i)) :
    cum4 (prodExp q) (X 0) (X 1) (X 2) (X 3) = 0 := by
  fin_cases i₀
  · exact cum4_eq_zero_of_avgZeroAt hq1 hz (hf 1 (by decide)) (hf 2 (by decide))
      (hf 3 (by decide))
  · rw [cum4_swap_one_two]
    exact cum4_eq_zero_of_avgZeroAt hq1 hz (hf 0 (by decide)) (hf 2 (by decide))
      (hf 3 (by decide))
  · rw [cum4_swap_two_three, cum4_swap_one_two]
    exact cum4_eq_zero_of_avgZeroAt hq1 hz (hf 0 (by decide)) (hf 1 (by decide))
      (hf 3 (by decide))
  · rw [cum4_swap_three_four, cum4_swap_two_three, cum4_swap_one_two]
    exact cum4_eq_zero_of_avgZeroAt hq1 hz (hf 0 (by decide)) (hf 1 (by decide))
      (hf 2 (by decide))

omit [DecidableEq V] in
/-- If the two pairs depend on disjoint sets of sites, the fourth cumulant vanishes. -/
theorem cum4_eq_zero_of_disjoint (hq1 : ∀ s, ∑ v : V, q s v = 1) {T₁ T₂ : Finset S}
    (hdisj : ∀ s ∈ T₂, s ∉ T₁) {a b c d : (S → V) → ℝ}
    (ha : DependsOn T₁ a) (hb : DependsOn T₁ b) (hc : DependsOn T₂ c) (hd : DependsOn T₂ d)
    (ha0 : prodExp q a = 0) (hb0 : prodExp q b = 0) : cum4 (prodExp q) a b c d = 0 := by
  refine cum4_eq_zero_of_indep_pair _ ?_ ?_ ?_ ?_ ?_ ha0 hb0
  · have hass : a * b * c * d = (a * b) * (c * d) := by ring
    rw [hass]
    exact prodExp_mul_eq_mul_of_disjoint hq1 hdisj (dependsOn_mul ha hb) (dependsOn_mul hc hd)
  · exact prodExp_mul_eq_mul_of_disjoint hq1 hdisj ha hc
  · exact prodExp_mul_eq_mul_of_disjoint hq1 hdisj ha hd
  · exact prodExp_mul_eq_mul_of_disjoint hq1 hdisj hb hc
  · exact prodExp_mul_eq_mul_of_disjoint hq1 hdisj hb hd

end PropertyOne

/-! ## 6. The support condition `hsupp` -/

section Supp

variable {D L O Γ₀ V : Type*}
  [Fintype D] [DecidableEq D] [Fintype L] [DecidableEq L] [Fintype O] [DecidableEq O]
  [Fintype V] [DecidableEq V] [Nonempty V]
  {idio : Γ₀ → Prop} [DecidablePred idio] {idx : D → O → L} {lev : Γ₀ → Finset D}
  {q : Site D L O → V → ℝ}

omit [Fintype L] [Fintype O] in
/-- Two variables occupying a common site share a dimension at which their observations
agree. -/
theorem sharesSite_of_mem_both (hidio : ∀ γ : Γ₀, idio γ → lev γ = Finset.univ)
    {γ γ' : Γ₀} {o o' : O} {s : Site D L O}
    (h : s ∈ siteSet idio idx lev γ o) (h' : s ∈ siteSet idio idx lev γ' o') :
    ∃ k ∈ lev γ, k ∈ lev γ' ∧ idx k o = idx k o' := by
  rw [siteSet, Finset.mem_image] at h
  obtain ⟨k, hk, hks⟩ := h
  subst hks
  obtain ⟨h1, h2⟩ := mem_lev_and_idx_eq_of_mem_siteSet hidio hk h'
  exact ⟨k, hk, h1, h2.symm⟩

omit [DecidableEq V] in
/-- The hypothesis `hsupp` of `var_quadForm_le_levels`. -/
theorem assignCum_eq_zero_of_not_supported (hq1 : ∀ s, ∑ v : V, q s v = 1)
    (hidio : ∀ γ : Γ₀, idio γ → lev γ = Finset.univ)
    {Lv : Finset Γ₀} (he : ∀ γ ∈ Lv, 2 ≤ (lev γ).card)
    {xi : Γ₀ → O → (Site D L O → V) → ℝ}
    (hdep : ∀ γ ∈ Lv, ∀ o, DependsOn (siteSet idio idx lev γ o) (xi γ o))
    (hdeg : ∀ γ ∈ Lv, ∀ o, ∀ s ∈ siteSet idio idx lev γ o, AvgZeroAt q s (xi γ o))
    {g : Γ₀ × Γ₀ × Γ₀ × Γ₀} (hg : g ∈ levelQuadruples Lv) (o₁ o₂ o₃ o₄ : O)
    (hns : ¬ (Admissible idx (assignLevels lev g) (quad o₁ o₂ o₃ o₄)
        ∧ QuadformE2.Linked idx (assignLevels lev g) (quad o₁ o₂ o₃ o₄))) :
    assignCum (prodExp q) xi g o₁ o₂ o₃ o₄ = 0 := by
  classical
  rw [mem_levelQuadruples] at hg
  have hγmem : ∀ i : Fin 4, quad g.1 g.2.1 g.2.2.1 g.2.2.2 i ∈ Lv := by
    intro i
    fin_cases i
    · simpa using hg.1
    · simpa using hg.2.1
    · simpa using hg.2.2.1
    · simpa using hg.2.2.2
  set γf : Fin 4 → Γ₀ := quad g.1 g.2.1 g.2.2.1 g.2.2.2 with hγf
  set of : Fin 4 → O := quad o₁ o₂ o₃ o₄ with hof
  set X : Fin 4 → (Site D L O → V) → ℝ := fun i => xi (γf i) (of i) with hX
  have hcum : assignCum (prodExp q) xi g o₁ o₂ o₃ o₄
      = cum4 (prodExp q) (X 0) (X 1) (X 2) (X 3) := by
    simp [assignCum, hX, hγf, hof]
  rw [hcum]
  rw [not_and_or] at hns
  rcases hns with hna | hnl
  · rw [Admissible] at hna
    push Not at hna
    obtain ⟨i₀, k₀, hk₀, hno⟩ := hna
    have hk₀' : k₀ ∈ lev (γf i₀) := hk₀
    refine cum4_eq_zero_of_unshared (q := q) (s₀ := sitemap idio idx (γf i₀) k₀ (of i₀))
      hq1 (hdeg (γf i₀) (hγmem i₀) (of i₀) _ (mem_siteSet hk₀')) ?_
    intro i hi
    refine freeAt_of_dependsOn ?_ (hdep (γf i) (hγmem i) (of i))
    intro hcon
    obtain ⟨h1, h2⟩ := mem_lev_and_idx_eq_of_mem_siteSet hidio hk₀' hcon
    exact hno i hi h1 h2
  · have h20 : ¬ QuadformE2.SharesSite idx (assignLevels lev g) of 2 0 :=
      fun h => hnl (Or.inl h)
    have h21 : ¬ QuadformE2.SharesSite idx (assignLevels lev g) of 2 1 :=
      fun h => hnl (Or.inr (Or.inl h))
    have h30 : ¬ QuadformE2.SharesSite idx (assignLevels lev g) of 3 0 :=
      fun h => hnl (Or.inr (Or.inr (Or.inl h)))
    have h31 : ¬ QuadformE2.SharesSite idx (assignLevels lev g) of 3 1 :=
      fun h => hnl (Or.inr (Or.inr (Or.inr h)))
    have hdisj : ∀ s ∈ siteSet idio idx lev (γf 2) (of 2) ∪ siteSet idio idx lev (γf 3) (of 3),
        s ∉ siteSet idio idx lev (γf 0) (of 0) ∪ siteSet idio idx lev (γf 1) (of 1) := by
      intro s hs hs'
      rw [Finset.mem_union] at hs hs'
      rcases hs with h2 | h3 <;> rcases hs' with h0 | h1
      · exact h20 (sharesSite_of_mem_both hidio h2 h0)
      · exact h21 (sharesSite_of_mem_both hidio h2 h1)
      · exact h30 (sharesSite_of_mem_both hidio h3 h0)
      · exact h31 (sharesSite_of_mem_both hidio h3 h1)
    have hmean : ∀ i : Fin 4, prodExp q (X i) = 0 := by
      intro i
      obtain ⟨s, hs⟩ : (siteSet idio idx lev (γf i) (of i)).Nonempty :=
        siteSet_nonempty (of i) (Finset.card_pos.mp (by have := he _ (hγmem i); omega))
      exact prodExp_eq_zero_of_avgZeroAt hq1 (hdeg (γf i) (hγmem i) (of i) s hs)
    exact cum4_eq_zero_of_disjoint hq1 hdisj
      (dependsOn_mono Finset.subset_union_left (hdep (γf 0) (hγmem 0) (of 0)))
      (dependsOn_mono Finset.subset_union_right (hdep (γf 1) (hγmem 1) (of 1)))
      (dependsOn_mono Finset.subset_union_left (hdep (γf 2) (hγmem 2) (of 2)))
      (dependsOn_mono Finset.subset_union_right (hdep (γf 3) (hγmem 3) (of 3)))
      (hmean 0) (hmean 1)

end Supp

/-! ## 7. The cumulant bound `hbdd`

By Young's inequality, `|abcd| ≤ (a⁴+b⁴+c⁴+d⁴)/4` and `|ab| ≤ (a⁴+b⁴+2)/4` pointwise, so every
fourth cumulant is bounded by `K = C + 3((C+1)/2)²` whenever `E[ξ⁴] ≤ C`. -/

section Bound

variable {S V : Type*} [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V]
variable {q : S → V → ℝ}

/-- Young's inequality, four variables. -/
theorem abs_mul_four_le (a b c d : ℝ) : |a * b * c * d| ≤ (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) / 4 := by
  rw [abs_le]
  constructor <;>
    nlinarith [sq_nonneg (a * b - c * d), sq_nonneg (a * b + c * d), sq_nonneg (a ^ 2 - b ^ 2),
      sq_nonneg (c ^ 2 - d ^ 2), sq_nonneg (a * b), sq_nonneg (c * d)]

/-- Young's inequality, two variables, against the fourth powers. -/
theorem abs_mul_two_le (a b : ℝ) : |a * b| ≤ (a ^ 4 + b ^ 4 + 2) / 4 := by
  rw [abs_le]
  constructor <;>
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a ^ 2 - 1), sq_nonneg (b ^ 2 - 1),
      sq_nonneg (a * b)]

omit [DecidableEq V] in
theorem abs_prodExp_mul_four_le (hq0 : ∀ s v, 0 ≤ q s v) (hq1 : ∀ s, ∑ v : V, q s v = 1)
    {a b c d : (S → V) → ℝ} {C : ℝ} (ha : prodExp q (a ^ 4) ≤ C) (hb : prodExp q (b ^ 4) ≤ C)
    (hc : prodExp q (c ^ 4) ≤ C) (hd : prodExp q (d ^ 4) ≤ C) :
    |prodExp q (a * b * c * d)| ≤ C := by
  refine abs_prodExp_le hq0 hq1 (g := (4 : ℝ)⁻¹ • (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4)) ?_ ?_
  · intro ω
    simp only [Pi.mul_apply, Pi.smul_apply, Pi.add_apply, Pi.pow_apply, smul_eq_mul]
    have h := abs_mul_four_le (a ω) (b ω) (c ω) (d ω)
    linarith
  · rw [map_smul, map_add, map_add, map_add, smul_eq_mul]
    linarith

omit [DecidableEq V] in
theorem abs_prodExp_mul_two_le (hq0 : ∀ s v, 0 ≤ q s v) (hq1 : ∀ s, ∑ v : V, q s v = 1)
    {a b : (S → V) → ℝ} {C : ℝ} (ha : prodExp q (a ^ 4) ≤ C) (hb : prodExp q (b ^ 4) ≤ C) :
    |prodExp q (a * b)| ≤ (C + 1) / 2 := by
  refine abs_prodExp_le hq0 hq1
    (g := (4 : ℝ)⁻¹ • (a ^ 4 + b ^ 4 + (2 : ℝ) • (1 : (S → V) → ℝ))) ?_ ?_
  · intro ω
    simp only [Pi.mul_apply, Pi.smul_apply, Pi.add_apply, Pi.pow_apply, Pi.one_apply,
      smul_eq_mul, mul_one]
    have h := abs_mul_two_le (a ω) (b ω)
    linarith
  · rw [map_smul, map_add, map_add, map_smul, smul_eq_mul, smul_eq_mul, prodExp_one hq1]
    linarith

omit [DecidableEq V] in
/-- The fourth-cumulant bound, with explicit constant. -/
theorem abs_cum4_le (hq0 : ∀ s v, 0 ≤ q s v) (hq1 : ∀ s, ∑ v : V, q s v = 1)
    {a b c d : (S → V) → ℝ} {C : ℝ} (hC : 0 ≤ C) (ha : prodExp q (a ^ 4) ≤ C)
    (hb : prodExp q (b ^ 4) ≤ C) (hc : prodExp q (c ^ 4) ≤ C) (hd : prodExp q (d ^ 4) ≤ C) :
    |cum4 (prodExp q) a b c d| ≤ C + 3 * ((C + 1) / 2) ^ 2 := by
  have hk : (0:ℝ) ≤ (C + 1) / 2 := by linarith
  have hprod : ∀ x y : ℝ, |x| ≤ (C + 1) / 2 → |y| ≤ (C + 1) / 2 →
      |x * y| ≤ ((C + 1) / 2) ^ 2 := by
    intro x y hx hy
    rw [abs_mul, sq]
    exact mul_le_mul hx hy (abs_nonneg _) hk
  have h4 := abs_le.mp (abs_prodExp_mul_four_le hq0 hq1 ha hb hc hd)
  have h1 := abs_le.mp (hprod _ _ (abs_prodExp_mul_two_le hq0 hq1 ha hb)
    (abs_prodExp_mul_two_le hq0 hq1 hc hd))
  have h2 := abs_le.mp (hprod _ _ (abs_prodExp_mul_two_le hq0 hq1 ha hc)
    (abs_prodExp_mul_two_le hq0 hq1 hb hd))
  have h3 := abs_le.mp (hprod _ _ (abs_prodExp_mul_two_le hq0 hq1 ha hd)
    (abs_prodExp_mul_two_le hq0 hq1 hb hc))
  rw [cum4, abs_le]
  constructor <;> linarith [h4.1, h4.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

end Bound

/-! ## 8. Lemma SM.C.6 under Regime 2 -/

section Assembled

variable {D L O Γ₀ V : Type*}
  [Fintype D] [DecidableEq D] [Fintype L] [DecidableEq L] [Fintype O] [DecidableEq O]
  [Fintype V] [DecidableEq V] [Nonempty V]

/-- `ζ_o = ∑_{2≤|e|≤M} ξ^e_o + ε_o`, the level decomposition. -/
def levelSum (Lv : Finset Γ₀) (xi : Γ₀ → O → (Site D L O → V) → ℝ) :
    O → (Site D L O → V) → ℝ := fun o => ∑ γ ∈ Lv, xi γ o

/-- `Ω'_{oo'} = E[ζ_oζ_{o'} ∣ 𝒟]`, computed in the model. -/
noncomputable def levelGram (q : Site D L O → V → ℝ) (Lv : Finset Γ₀)
    (xi : Γ₀ → O → (Site D L O → V) → ℝ) : Matrix O O ℝ :=
  Matrix.of fun o o' => prodExp q (levelSum Lv xi o * levelSum Lv xi o')

omit [DecidableEq D] in
/-- With fewer than two fixed-effect dimensions there is no level set of size `2`, so `he` forces
`Lv = ∅`. -/
theorem lv_eq_empty_of_card_lt_two {Lv : Finset Γ₀} {lev : Γ₀ → Finset D}
    (hM : Fintype.card D < 2) (he : ∀ γ ∈ Lv, 2 ≤ (lev γ).card) : Lv = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr fun γ hγ => ?_
  have h1 := he γ hγ
  have h2 : (lev γ).card ≤ Fintype.card D := by simpa using Finset.card_le_univ (lev γ)
  omega

omit [DecidableEq V] [Nonempty V] in
theorem levelGram_isSymm (q : Site D L O → V → ℝ) (Lv : Finset Γ₀)
    (xi : Γ₀ → O → (Site D L O → V) → ℝ) : (levelGram q Lv xi).IsSymm := by
  ext o o'
  simp only [Matrix.transpose_apply, levelGram, Matrix.of_apply]
  rw [mul_comm]

omit [DecidableEq V] in
/-- **Lemma SM.C.6** under Regime 2:
`Var(ζ'Wζ ∣ 𝒟) ≤ 2 tr(WΩ'WΩ') + C(M) G_max c_max ‖W‖_F²`, with `C(M) = (2^M)^4 · 4M` times the
per-cumulant constant `K = C + 3((C+1)/2)²`.

`hq0`, `hq1` make `q` a probability law at each site; `hW` makes `W` symmetric; `hC`, `hmom`
bound fourth moments; `hLv`, `he` describe the levels; `hG`, `hc` bound cell sizes; `hdep` makes
each variable a function of the latents at its own sites; `hdeg` is complete degeneracy; `hidio`
gives the symbol `ε` the full dimension set, which forces `M ≥ 2`. -/
theorem var_quadForm_le_regime2 {idio : Γ₀ → Prop} [DecidablePred idio] (idx : D → O → L)
    (lev : Γ₀ → Finset D) (q : Site D L O → V → ℝ) (hq0 : ∀ s v, 0 ≤ q s v)
    (hq1 : ∀ s, ∑ v : V, q s v = 1) {W : Matrix O O ℝ} (hW : W.IsSymm)
    (Lv : Finset Γ₀) (xi : Γ₀ → O → (Site D L O → V) → ℝ)
    {Gmax cmax : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hLv : Lv.card ≤ 2 ^ Fintype.card D)
    (he : ∀ γ ∈ Lv, 2 ≤ (lev γ).card)
    (hidio : ∀ γ : Γ₀, idio γ → lev γ = Finset.univ)
    (hG : ∀ (k : D) (o : O), (cellOf idx ({k} : Finset D) o).card ≤ Gmax)
    (hc : ∀ (A : Finset D) (o : O), 2 ≤ A.card → (cellOf idx A o).card ≤ cmax)
    (hdep : ∀ γ ∈ Lv, ∀ o, DependsOn (siteSet idio idx lev γ o) (xi γ o))
    (hdeg : ∀ γ ∈ Lv, ∀ o, ∀ s ∈ siteSet idio idx lev γ o, AvgZeroAt q s (xi γ o))
    (hmom : ∀ γ ∈ Lv, ∀ o, prodExp q ((xi γ o) ^ 4) ≤ C) :
    varQuad (prodExp q) W (levelSum Lv xi)
      ≤ 2 * (W * levelGram q Lv xi * W * levelGram q Lv xi).trace
        + ((2 ^ Fintype.card D) ^ 4 : ℕ) * (C + 3 * ((C + 1) / 2) ^ 2)
            * (4 * Fintype.card D * Gmax * cmax : ℕ) * frobSq W := by
  refine var_quadForm_le_levels (prodExp q) hW (levelGram_isSymm q Lv xi) (levelSum Lv xi)
    (fun _ _ => rfl) Lv xi (fun _ => rfl) lev idx
    (by nlinarith [sq_nonneg ((C + 1) / 2)]) hLv he hG hc ?_ ?_
  · intro g hg o₁ o₂ o₃ o₄ hns
    exact assignCum_eq_zero_of_not_supported hq1 hidio he hdep hdeg hg o₁ o₂ o₃ o₄ hns
  · intro g hg o₁ o₂ o₃ o₄
    rw [mem_levelQuadruples] at hg
    exact abs_cum4_le hq0 hq1 hC (hmom _ hg.1 o₁) (hmom _ hg.2.1 o₂) (hmom _ hg.2.2.1 o₃)
      (hmom _ hg.2.2.2 o₄)

end Assembled

/-! ## 9. A model satisfying the hypotheses

A model with `M = 2` fixed-effect dimensions, one category per dimension, one observation, a fair
two-point latent alphabet, the two-way interaction kernel `ξ_o = σ(U^{(1)})σ(U^{(2)})` and an
idiosyncratic `ε_o = σ(U_o)`. Here `Var(ζ'Wζ ∣ 𝒟) = 4` and `tr(WΩ'WΩ') = 4`. -/

section Witness

/-- The Rademacher value map on the two-point latent alphabet. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem sgn_true : sgn true = 1 := rfl
@[simp] theorem sgn_false : sgn false = -1 := rfl

/-- The witness site type: two fixed-effect dimensions, one category each, one observation. -/
abbrev WSite := Site (Fin 2) (Fin 1) (Fin 1)

/-- The witness sample space. -/
abbrev WOmega := WSite → Bool

/-- All observations carry the same category in both dimensions. -/
def witIdx : Fin 2 → Fin 1 → Fin 1 := fun _ _ => 0

/-- Both symbols carry the full dimension set: the kernel is the two-way interaction, and the
symbol `ε` is given `{1,2}` as `hidio` requires. -/
def witLev : Bool → Finset (Fin 2) := fun _ => Finset.univ

/-- `true` is the symbol `ε`. -/
abbrev witIdio : Bool → Prop := fun γ => γ = true

/-- The fair product law. -/
noncomputable def witQ : WSite → Bool → ℝ := fun _ _ => 1 / 2

/-- The two-way interaction kernel `h^{\{1,2\}}(U^{(1)},U^{(2)}) = σ(U^{(1)})σ(U^{(2)})`, which is
completely degenerate. -/
def witKernel (ω : WOmega) : ℝ := sgn (ω (Sum.inl (0, 0))) * sgn (ω (Sum.inl (1, 0)))

/-- The idiosyncratic term, at `o`'s own private site. -/
def witEps (o : Fin 1) (ω : WOmega) : ℝ := sgn (ω (Sum.inr o))

/-- The level family. -/
def witXi : Bool → Fin 1 → WOmega → ℝ := fun γ o => if γ then witEps o else witKernel

@[simp] theorem witXi_true (o : Fin 1) : witXi true o = witEps o := by simp [witXi]
@[simp] theorem witXi_false (o : Fin 1) : witXi false o = witKernel := by simp [witXi]

theorem witQ_nonneg : ∀ (s : WSite) (v : Bool), 0 ≤ witQ s v := by
  intro s v; norm_num [witQ]

theorem witQ_sum : ∀ s : WSite, ∑ v : Bool, witQ s v = 1 := by
  intro s; simp [witQ]

/-- The kernel's two sites, and the idiosyncratic term's one. -/
theorem witSite_kernel (k : Fin 2) (o : Fin 1) :
    (Sum.inl (k, 0) : WSite) ∈ siteSet witIdio witIdx witLev false o := by
  have h : sitemap witIdio witIdx false k o = (Sum.inl (k, 0) : WSite) := by
    rw [sitemap_of_not_idio (by decide)]
    rfl
  rw [← h]
  exact mem_siteSet (by simp [witLev])

theorem witSite_eps (o : Fin 1) :
    (Sum.inr o : WSite) ∈ siteSet witIdio witIdx witLev true o := by
  have h : sitemap witIdio witIdx true 0 o = (Sum.inr o : WSite) := by
    rw [sitemap_of_idio (by decide)]
  rw [← h]
  exact mem_siteSet (by simp [witLev])

theorem witSite_mem_false {s : WSite} {o : Fin 1}
    (hs : s ∈ siteSet witIdio witIdx witLev false o) :
    s = Sum.inl (0, 0) ∨ s = Sum.inl (1, 0) := by
  rw [siteSet, Finset.mem_image] at hs
  obtain ⟨k, _, hk⟩ := hs
  rw [sitemap_of_not_idio (by decide)] at hk
  fin_cases k
  · exact Or.inl hk.symm
  · exact Or.inr hk.symm

theorem witSite_mem_true {s : WSite} {o : Fin 1}
    (hs : s ∈ siteSet witIdio witIdx witLev true o) : s = Sum.inr o := by
  rw [siteSet, Finset.mem_image] at hs
  obtain ⟨k, _, hk⟩ := hs
  rw [sitemap_of_idio (by decide)] at hk
  exact hk.symm

theorem witDep : ∀ γ ∈ (Finset.univ : Finset Bool), ∀ o : Fin 1,
    DependsOn (siteSet witIdio witIdx witLev γ o) (witXi γ o) := by
  intro γ _ o
  cases γ
  · intro ω ω' h
    simp only [witXi_false, witKernel]
    rw [h _ (witSite_kernel 0 o), h _ (witSite_kernel 1 o)]
  · intro ω ω' h
    simp only [witXi_true, witEps]
    rw [h _ (witSite_eps o)]

theorem witDeg : ∀ γ ∈ (Finset.univ : Finset Bool), ∀ o : Fin 1,
    ∀ s ∈ siteSet witIdio witIdx witLev γ o, AvgZeroAt witQ s (witXi γ o) := by
  intro γ _ o s hs
  cases γ
  · rcases witSite_mem_false hs with rfl | rfl <;> intro ω <;>
      simp [witXi_false, witKernel, witQ]
  · rw [witSite_mem_true hs]
    intro ω
    simp [witXi_true, witEps, witQ]

theorem witXi_pow_four (γ : Bool) (o : Fin 1) : (witXi γ o) ^ 4 = (1 : WOmega → ℝ) := by
  funext ω
  simp only [Pi.pow_apply, Pi.one_apply]
  cases γ
  · simp only [witXi_false, witKernel]
    cases ω (Sum.inl (0, 0)) <;> cases ω (Sum.inl (1, 0)) <;> norm_num
  · simp only [witXi_true, witEps]
    cases ω (Sum.inr o) <;> norm_num

theorem witMom : ∀ γ ∈ (Finset.univ : Finset Bool), ∀ o : Fin 1,
    prodExp witQ ((witXi γ o) ^ 4) ≤ (1 : ℝ) := by
  intro γ _ o
  rw [witXi_pow_four γ o, prodExp_one witQ_sum]

/-- `E[ε_oξ_o ∣ 𝒟] = 0`. -/
theorem witMix : prodExp witQ (witKernel * witEps 0) = 0 := by
  refine prodExp_mul_eq_zero_of_avgZeroAt witQ_sum
    (s₀ := (Sum.inl (0, 0) : WSite)) ?_ ?_
  · have h := witDeg false (Finset.mem_univ _) 0 _ (witSite_kernel 0 0)
    simpa using h
  · intro ω v
    simp [witEps]

theorem sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by cases b <;> norm_num

theorem witKernel_mul_self (ω : WOmega) : witKernel ω * witKernel ω = 1 := by
  simp only [witKernel]
  have h1 := sgn_mul_self (ω (Sum.inl (0, 0)))
  have h2 := sgn_mul_self (ω (Sum.inl (1, 0)))
  nlinarith [h1, h2]

theorem witEps_mul_self (o : Fin 1) (ω : WOmega) : witEps o ω * witEps o ω = 1 :=
  sgn_mul_self _

theorem witZ_apply (ω : WOmega) :
    levelSum (Finset.univ : Finset Bool) witXi 0 ω = witEps 0 ω + witKernel ω := by
  simp [levelSum]

/-- The quadratic form on the witness: `ζ² = 2 + 2ξε` pointwise, since `ξ² = ε² = 1`. -/
theorem witQuadForm_eq :
    quadForm (1 : Matrix (Fin 1) (Fin 1) ℝ) (levelSum (Finset.univ : Finset Bool) witXi)
      = (2 : ℝ) • (1 : WOmega → ℝ) + (2 : ℝ) • (witKernel * witEps 0) := by
  funext ω
  have hk := witKernel_mul_self ω
  have he := witEps_mul_self 0 ω
  simp only [quadForm_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply, Pi.mul_apply,
    smul_eq_mul, Fin.sum_univ_one, Matrix.one_apply_eq, witZ_apply]
  linear_combination hk + he

/-- And its square: `ζ⁴ = 8 + 8ξε`. -/
theorem witQuadForm_sq_eq :
    quadForm (1 : Matrix (Fin 1) (Fin 1) ℝ) (levelSum (Finset.univ : Finset Bool) witXi) ^ 2
      = (8 : ℝ) • (1 : WOmega → ℝ) + (8 : ℝ) • (witKernel * witEps 0) := by
  rw [witQuadForm_eq]
  funext ω
  have hk := witKernel_mul_self ω
  have he := witEps_mul_self 0 ω
  simp only [Pi.pow_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply, Pi.mul_apply, smul_eq_mul]
  linear_combination (4 * (witEps 0 ω) ^ 2) * hk + 4 * he

/-- `Var(ζ'Wζ ∣ 𝒟) = 4`. -/
theorem witness_varQuad :
    varQuad (prodExp witQ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (levelSum (Finset.univ : Finset Bool) witXi) = 4 := by
  rw [varQuad, witQuadForm_sq_eq, witQuadForm_eq]
  rw [map_add, map_add, map_smul, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, smul_eq_mul, prodExp_one witQ_sum, witMix]
  norm_num

/-- `Ω'_{oo'} = 2`, so `tr(WΩ'WΩ') = 4` and the bound's leading term is `8`. -/
theorem witness_levelGram :
    levelGram witQ (Finset.univ : Finset Bool) witXi 0 0 = 2 := by
  have h : levelSum (Finset.univ : Finset Bool) witXi 0
      * levelSum (Finset.univ : Finset Bool) witXi 0
      = quadForm (1 : Matrix (Fin 1) (Fin 1) ℝ) (levelSum (Finset.univ : Finset Bool) witXi) := by
    funext ω
    simp [quadForm_apply, Matrix.one_apply_eq]
  rw [levelGram, Matrix.of_apply, h, witQuadForm_eq, map_add, map_smul, map_smul, smul_eq_mul,
    smul_eq_mul, prodExp_one witQ_sum, witMix]
  norm_num

/-- `tr(WΩ'WΩ') = 4`, so the bound reads `4 ≤ 8 + (positive)`. -/
theorem witness_trace :
    ((1 : Matrix (Fin 1) (Fin 1) ℝ) * levelGram witQ Finset.univ witXi * 1
        * levelGram witQ Finset.univ witXi).trace = 4 := by
  have h : ((1 : Matrix (Fin 1) (Fin 1) ℝ) * levelGram witQ Finset.univ witXi * 1
      * levelGram witQ Finset.univ witXi)
      = levelGram witQ Finset.univ witXi * levelGram witQ Finset.univ witXi := by
    rw [one_mul, mul_one]
  rw [h]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_one,
    witness_levelGram]
  norm_num

/-- The hypotheses of `var_quadForm_le_regime2` hold on the model above. -/
theorem regime2_witness :
    varQuad (prodExp witQ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (levelSum (Finset.univ : Finset Bool) witXi)
      ≤ 2 * ((1 : Matrix (Fin 1) (Fin 1) ℝ) * levelGram witQ Finset.univ witXi * 1
              * levelGram witQ Finset.univ witXi).trace
        + ((2 ^ Fintype.card (Fin 2)) ^ 4 : ℕ) * ((1 : ℝ) + 3 * (((1 : ℝ) + 1) / 2) ^ 2)
            * (4 * Fintype.card (Fin 2) * 1 * 1 : ℕ)
            * frobSq (1 : Matrix (Fin 1) (Fin 1) ℝ) :=
  var_quadForm_le_regime2 (idio := witIdio) witIdx witLev witQ witQ_nonneg witQ_sum
    Matrix.isSymm_one Finset.univ witXi (Gmax := 1) (cmax := 1) (C := 1) zero_le_one
    (by decide) (by intro γ _; simp [witLev]) (fun _ _ => rfl)
    (fun _ _ => le_trans (Finset.card_le_univ _) (by simp))
    (fun _ _ _ => le_trans (Finset.card_le_univ _) (by simp))
    witDep witDeg witMom

end Witness

end QuadformE2Indep
end Multiway
