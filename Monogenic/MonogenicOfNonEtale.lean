/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Authors: Bianca Viray, Bryan Boehnke, Grant Yang, George Peykanu, Tianshuo Wang
-/
import Monogenic.Generator
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Polynomial.Eval.Algebra
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Algebra.Star.Subalgebra


open Polynomial
open Function
open RingHom

namespace Monogenic
variable {R S} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

/-!
## Monogenicity from Étale Height-One Quotients

This theorem states that if R and S are regular local rings with S a finite extension of R,
and there exists a height one prime ideal q in S such that the induced map R/(q ∩ R) → S/q
is étale, then S is a monogenic extension of R.

The key idea is that the étale condition on the quotient forces the extension to have a
particularly simple structure, which can be captured by a single generator.

## Extracted Sub-lemmas

The following lemmas are extracted from the main theorem to improve modularity.
-/

section SubLemmas

/-- In a quotient of a local ring by a prime, the maximal ideal is the image of the original. -/
lemma maximalIdeal_quotient_eq_map {R : Type*} [CommRing R] [IsLocalRing R]
    (p : Ideal R) [p.IsPrime] [IsLocalRing (R ⧸ p)] :
    IsLocalRing.maximalIdeal (R ⧸ p) =
      Ideal.map (Ideal.Quotient.mk p) (IsLocalRing.maximalIdeal R) := by
  haveI : IsLocalHom (Ideal.Quotient.mk p) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  ext x; obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact ⟨fun h => ⟨x, (map_mem_nonunits_iff _ x).mp h, rfl⟩,
         fun ⟨y, hy, hxy⟩ => hxy ▸ (map_mem_nonunits_iff _ y).mpr hy⟩

omit [IsLocalRing R] [IsLocalRing S] in
/-- If `S` is a finite `R`-module and `q` is an ideal of `S`, then the induced quotient map
    `R/(q ∩ R) →+* S/q` is finite. -/
lemma quotientMap_finite [Algebra R S] [Module.Finite R S] (q : Ideal S) :
    (Ideal.quotientMap q (algebraMap R S) le_rfl).Finite := by
  let φ := algebraMap R S
  let p := q.comap φ
  let φ₀ := Ideal.quotientMap q φ (le_refl p)
  letI : Algebra (R ⧸ p) (S ⧸ q) := φ₀.toAlgebra
  classical
  obtain ⟨s, hs⟩ := Module.finite_def.mp ‹Module.Finite R S›
  refine ⟨⟨s.image (Ideal.Quotient.mk q), ?_⟩⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
  have hx' : x' ∈ Submodule.span R (s : Set S) := hs ▸ trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx'
  · intro y hy
    exact Submodule.subset_span (Finset.mem_image_of_mem _ hy)
  · simp only [map_zero]; exact Submodule.zero_mem _
  · intro _ _ _ _ hy hz; simp only [map_add]; exact Submodule.add_mem _ hy hz
  · intro r _ _ hy
    rw [Algebra.smul_def, map_mul, ← Ideal.quotientMap_mk (f := φ) (H := le_refl p)]
    exact Submodule.smul_mem _ _ hy

omit [IsLocalRing R] [IsLocalRing S] in
/-- In a UFD, a height one prime ideal is principal. -/
lemma height_one_prime_principal_of_UFD {S : Type*} [CommRing S] [IsDomain S]
    [UniqueFactorizationMonoid S]
    (q : Ideal S) [hq_prime : q.IsPrime] (hq_height : q.height = 1) :
    ∃ q₀ : S, q = Ideal.span {q₀} := by
  -- Step 1: q ≠ ⊥ because height q = 1 > 0
  have hq_ne_bot : q ≠ ⊥ := by
    intro h
    rw [h, Ideal.height_bot] at hq_height
    exact zero_ne_one hq_height
  -- Step 2: By UFD property, every nonzero prime ideal contains a prime element
  obtain ⟨p, hp_mem, hp_prime⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot hq_prime hq_ne_bot
  -- Step 3: span {p} is a prime ideal since p is prime
  have h_span_prime : (Ideal.span {p}).IsPrime := by
    rw [Ideal.span_singleton_prime hp_prime.ne_zero]
    exact hp_prime
  -- Step 4: span {p} ⊆ q
  have h_span_le : Ideal.span {p} ≤ q := (Ideal.span_singleton_le_iff_mem (I := q)).mpr hp_mem
  -- Step 5: span {p} ≠ ⊥
  have h_span_ne_bot : Ideal.span {p} ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact hp_prime.ne_zero
  -- Step 6: Since height q = 1, if span {p} < q, then span {p} has height 0
  -- In a domain, height 0 primes are just ⊥, but span {p} ≠ ⊥, contradiction.
  -- So span {p} = q.
  have h_eq : Ideal.span {p} = q := by
    by_contra h_ne
    have h_lt : Ideal.span {p} < q := lt_of_le_of_ne h_span_le h_ne
    -- height (span {p}) < height q = 1, so height (span {p}) = 0
    haveI : (Ideal.span {p}).IsPrime := h_span_prime
    have hq_ht_ne_top : q.height ≠ ⊤ := by
      rw [hq_height]
      exact ENat.one_ne_top
    haveI : q.FiniteHeight := ⟨Or.inr hq_ht_ne_top⟩
    haveI : (Ideal.span {p}).FiniteHeight := Ideal.finiteHeight_of_le h_span_le hq_prime.ne_top
    have h_ht_lt := Ideal.height_strict_mono_of_is_prime h_lt
    rw [hq_height] at h_ht_lt
    -- height (span {p}) < 1 means height (span {p}) = 0
    have h_ht_zero : (Ideal.span {p}).height = 0 := ENat.lt_one_iff_eq_zero.mp h_ht_lt
    -- span {p} is a minimal prime of S (height 0 prime)
    rw [Ideal.height_eq_primeHeight, Ideal.primeHeight_eq_zero_iff] at h_ht_zero
    -- In a domain, minimalPrimes of (⊥ : Ideal S) is just {⊥}
    have h_span_eq_bot : Ideal.span {p} = ⊥ := by
      have h_mem : Ideal.span {p} ∈ (⊥ : Ideal S).minimalPrimes := h_ht_zero
      -- (⊥ : Ideal S).minimalPrimes = minimalPrimes S by definition
      have : (⊥ : Ideal S).minimalPrimes = minimalPrimes S := rfl
      rw [this, IsDomain.minimalPrimes_eq_singleton_bot] at h_mem
      exact Set.mem_singleton_iff.mp h_mem
    exact h_span_ne_bot h_span_eq_bot
  exact ⟨p, h_eq.symm⟩

/-- Taylor expansion for polynomial evaluation over a commutative ring:
    For any polynomial `f` and elements `x`, `h`, there exists `c` such that
    `f(x + h) = f(x) + f'(x) · h + h² · c`. -/
lemma taylor_expansion_aeval {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (f : R[X]) (x h : S) :
    ∃ c : S, f.aeval (x + h) = f.aeval x + f.derivative.aeval x * h + h^2 * c := by
  induction f using Polynomial.induction_on with
  | C r =>
    -- Constant polynomial: f(x+h) = r = f(x), derivative = 0
    use 0
    simp only [Polynomial.aeval_C, Polynomial.derivative_C, Polynomial.aeval_zero,
      mul_zero, add_zero, sq, zero_mul]
  | add p₁ p₂ ih₁ ih₂ =>
    -- Addition: use linearity
    obtain ⟨c₁, hc₁⟩ := ih₁
    obtain ⟨c₂, hc₂⟩ := ih₂
    use c₁ + c₂
    simp only [Polynomial.aeval_add, Polynomial.derivative_add] at *
    rw [hc₁, hc₂]
    ring
  | monomial n r ih =>
    -- Monomial: C r * X^(n+1)
    simp only [Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow,
      Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
      Polynomial.derivative_X_pow]
    -- Use binomial theorem: (x+h)^(n+1) = Σ_{m=0}^{n+1} C(n+1,m) * x^m * h^(n+1-m)
    have h_binom : (x + h) ^ (n + 1) = ∑ m ∈ Finset.range (n + 2),
        x ^ m * h ^ (n + 1 - m) * (n + 1).choose m := add_pow x h (n + 1)
    -- Construct the remainder term (sum of terms with h² or higher)
    let c' := ∑ m ∈ Finset.range n, x ^ m * h ^ (n - 1 - m) * (n + 1).choose m
    use algebraMap R S r * c'
    rw [h_binom]
    -- Split sum: Σ_{m=0}^{n+1} = (Σ_{m=0}^{n-1}) + term(m=n) + term(m=n+1)
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_self, pow_zero,
      Nat.add_sub_cancel]
    -- (n+1).choose n = n+1
    have h_choose_n : (n + 1).choose n = n + 1 := Nat.choose_succ_self_right n
    rw [h_choose_n]
    -- Since n+1-m ≥ 2 for m < n, we have h^(n+1-m) = h² * h^(n-1-m)
    have h_sum_eq : (∑ m ∈ Finset.range n, x ^ m * h ^ (n + 1 - m) * (n + 1).choose m) =
        h ^ 2 * c' := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mem_range] at hm
      -- m < n, so n + 1 - m ≥ 2, hence n + 1 - m = (n - 1 - m) + 2
      have h_exp : n + 1 - m = (n - 1 - m) + 2 := by omega
      rw [h_exp, pow_add]
      ring
    rw [h_sum_eq]
    -- Normalize: n + 1 - n = 1, and Nat cast factors through algebraMap
    have h_exp_simp : n + 1 - n = 1 := by omega
    simp only [h_exp_simp, pow_one, ← map_natCast (algebraMap R S)]
    ring

/-- When the quotient map `R/p → S/q` is étale (with p = q.comap (algebraMap R S)),
    and both rings are local, the maximal ideal of `S` decomposes as
    `m_S = q + m_R S`. -/
lemma maximalIdeal_eq_sup_of_etale_quotient
    [IsDomain R] [IsDomain S] [Algebra R S] [Module.Finite R S]
    (q : Ideal S) [hq_prime : q.IsPrime]
    (hétale : (Ideal.quotientMap q (algebraMap R S) le_rfl).Etale) :
    IsLocalRing.maximalIdeal S =
      q ⊔ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) := by
  let φ := algebraMap R S
  let p : Ideal R := q.comap φ
  let R₀ := R ⧸ p
  let S₀ := S ⧸ q
  let φ₀ : R₀ →+* S₀ := Ideal.quotientMap q φ (le_refl p)
  let mr := IsLocalRing.maximalIdeal R
  let ms := IsLocalRing.maximalIdeal S
  have hq_le_ms : q ≤ ms := IsLocalRing.le_maximalIdeal hq_prime.ne_top
  -- Set up algebra structure on φ₀
  letI : Algebra R₀ S₀ := φ₀.toAlgebra
  have hφ₀_eq : algebraMap R₀ S₀ = φ₀ := RingHom.algebraMap_toAlgebra φ₀
  -- φ₀ is finite and injective
  have hφ₀_fin : φ₀.Finite := quotientMap_finite q
  have hφ₀_inj : Injective φ₀ := Ideal.quotientMap_injective
  -- R₀ and S₀ are domains and local rings
  haveI hp_prime : p.IsPrime := Ideal.IsPrime.comap φ
  haveI : IsDomain R₀ := Ideal.Quotient.isDomain p
  haveI : IsDomain S₀ := Ideal.Quotient.isDomain q
  haveI : Nontrivial R₀ := Ideal.Quotient.nontrivial_iff.mpr hp_prime.ne_top
  haveI : IsLocalRing R₀ :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  haveI : Nontrivial S₀ := Ideal.Quotient.nontrivial_iff.mpr hq_prime.ne_top
  haveI : IsLocalRing S₀ :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  -- Extract formally unramified from étale
  have h_etale := (RingHom.etale_iff_formallyUnramified_and_smooth φ₀).mp hétale
  have unram_φ₀ : φ₀.FormallyUnramified := h_etale.1
  haveI : Algebra.FormallyUnramified R₀ S₀ := by rwa [← hφ₀_eq] at unram_φ₀
  -- φ₀ finite and injective implies local homomorphism
  haveI : IsLocalHom (algebraMap R₀ S₀) := by
    rw [hφ₀_eq]
    exact RingHom.IsIntegral.isLocalHom (RingHom.IsIntegral.of_finite hφ₀_fin) hφ₀_inj
  -- EssFiniteType needed for map_maximalIdeal
  haveI : Algebra.EssFiniteType R₀ S₀ :=
    RingHom.FiniteType.essFiniteType (RingHom.FiniteType.of_finite hφ₀_fin)
  -- Key lemma: for formally unramified local maps, maximal ideals match
  have h_max_eq : Ideal.map φ₀ (IsLocalRing.maximalIdeal R₀) = IsLocalRing.maximalIdeal S₀ := by
    rw [← hφ₀_eq]; exact Algebra.FormallyUnramified.map_maximalIdeal
  -- Maximal ideal of R/p = image of mr
  have h_max_R₀ : IsLocalRing.maximalIdeal R₀ = Ideal.map (Ideal.Quotient.mk p) mr :=
    maximalIdeal_quotient_eq_map p
  -- Maximal ideal of S/q = image of ms
  have h_max_S₀ : IsLocalRing.maximalIdeal S₀ = Ideal.map (Ideal.Quotient.mk q) ms :=
    maximalIdeal_quotient_eq_map q
  -- Composition property: φ₀ ∘ (mk p) = (mk q) ∘ φ
  have h_comp : φ₀.comp (Ideal.Quotient.mk p) = (Ideal.Quotient.mk q).comp φ := by
    ext r
    change φ₀ (Ideal.Quotient.mk p r) = Ideal.Quotient.mk q (φ r)
    exact Ideal.quotientMap_mk
  -- Chain of equalities: map (mk q) ms = map (mk q) (map φ mr)
  have h_images_eq : Ideal.map (Ideal.Quotient.mk q) ms =
      Ideal.map (Ideal.Quotient.mk q) (Ideal.map φ mr) :=
    calc Ideal.map (Ideal.Quotient.mk q) ms
      _ = IsLocalRing.maximalIdeal S₀ := h_max_S₀.symm
      _ = Ideal.map φ₀ (IsLocalRing.maximalIdeal R₀) := h_max_eq.symm
      _ = Ideal.map φ₀ (Ideal.map (Ideal.Quotient.mk p) mr) := by rw [h_max_R₀]
      _ = Ideal.map (Ideal.Quotient.mk q) (Ideal.map φ mr) := by
          rw [Ideal.map_map, Ideal.map_map, h_comp]
  -- Since map (mk q) (q ⊔ X) = map (mk q) X (q maps to 0)
  have h_sup_image : Ideal.map (Ideal.Quotient.mk q) (q ⊔ Ideal.map φ mr) =
      Ideal.map (Ideal.Quotient.mk q) (Ideal.map φ mr) := by
    rw [Ideal.map_sup, Ideal.map_quotient_self]; simp
  -- Apply correspondence theorem: map f I = map f J ↔ I ⊔ ker f = J ⊔ ker f
  rw [← h_sup_image, Ideal.map_eq_iff_sup_ker_eq_of_surjective _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, sup_eq_left.mpr hq_le_ms] at h_images_eq
  -- Simplify RHS: (q ⊔ X) ⊔ q = q ⊔ X
  calc ms = (q ⊔ Ideal.map φ mr) ⊔ q := h_images_eq
    _ = q ⊔ Ideal.map φ mr := by rw [sup_comm, sup_left_idem]


end SubLemmas

/-- Given regular local rings `R` and `S` with `S` a finite extension of `R`, if there exists a
height one prime ideal `q ⊆ S` such that the induced map `R/(q ∩ R) → S/q` is étale,
then `S` is a monogenic extension of `R`.

Here:
- `φ : R →+* S` is the structure map making S an extension of R
- `hφ_fin` asserts that S is a finite R-module via φ
- `hφ_inj` asserts that φ is injective (so R embeds into S)
- `q` is a prime ideal of S with height 1
- The "intersection" q ∩ R is formalized as `q.comap φ` (the preimage of q under φ)
- The induced quotient map is `Ideal.quotientMap q φ` which gives `R/(q ∩ R) →+* S/q`
- `hétale` asserts this quotient map is étale
-/
theorem monogenic_of_etale_height_one_quotient
    [IsDomain R] [IsDomain S] [IsIntegrallyClosed R] [UniqueFactorizationMonoid S] [Algebra R S]
    [FaithfulSMul R S] [Module.Finite R S]
    (q : Ideal S) [IsIntegrallyClosed <| R ⧸ (q.comap <| algebraMap R S)]
    [hq_prime : q.IsPrime] (hq_height : q.height = 1)
    (hétale : (Ideal.quotientMap q (algebraMap R S) le_rfl).Etale) :
    ∃ f : R[X], Nonempty (IsAdjoinRootMonic S f) := by
  -- Set up algebra structure
  let φ := algebraMap R S
  have φ_eq : algebraMap R S = φ := RingHom.algebraMap_toAlgebra φ
  -- Step 1: If φ is already étale, apply FiniteInjectiveEtale_IsMonogenic directly
  by_cases hφ_etale : Algebra.Etale R S
  · let ⟨β, adj⟩ := monogenic_of_finiteInjectiveEtale (R:=R) (S:=S)
    have hβ_int := Algebra.IsIntegral.isIntegral (R:=R) β
    exact ⟨minpoly R β, ⟨IsAdjoinRootMonic.mkOfAdjoinEqTop hβ_int adj⟩⟩
  -- Step 2: Define the quotient structures
  -- p = q ∩ R (preimage of q under φ)
  let p : Ideal R := q.comap φ
  -- R₀ = R/p, S₀ = S/q
  let R₀ := R ⧸ p
  let S₀ := S ⧸ q
  -- The quotient map φ₀ : R₀ → S₀
  let φ₀ : R₀ →+* S₀ := Ideal.quotientMap q φ (le_refl p)
  -- φ₀ is étale by hypothesis
  have hφ₀_etale : Etale φ₀ := hétale
  -- Step 3: Show φ₀ is finite and injective, then apply FiniteInjectiveEtale_IsMonogenic
  -- φ₀ is finite (quotient of finite extension)
  have hφ₀_fin : φ₀.Finite := quotientMap_finite q
  -- φ₀ is injective (since p = q.comap φ, quotientMap is automatically injective)
  have hφ₀_inj : Injective φ₀ := Ideal.quotientMap_injective
  -- R₀ is a domain (quotient by prime ideal)
  haveI : IsDomain R₀ := Ideal.Quotient.isDomain p
  -- S₀ is a domain (quotient by prime ideal)
  haveI : IsDomain S₀ := Ideal.Quotient.isDomain q
  -- Note: IsIntegrallyClosed R₀ is not needed for FiniteInjectiveEtale_IsMonogenic
  -- The general claim "quotient of integrally closed by prime is integrally closed" is false
  -- (counterexample: k[x,y]/(y²-x³) is not integrally closed)
  -- R₀ and S₀ are local rings (quotient of local ring by proper ideal is local)
  -- p is prime (comap of prime ideal is prime)
  haveI hp_prime : p.IsPrime := Ideal.IsPrime.comap φ
  -- R₀ is nontrivial (quotient by prime ideal is a domain, hence nontrivial)
  haveI : Nontrivial R₀ := Ideal.Quotient.nontrivial_iff.mpr hp_prime.ne_top
  haveI : IsLocalRing R₀ :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  -- S₀ is nontrivial (quotient by prime ideal is a domain, hence nontrivial)
  haveI : Nontrivial S₀ := Ideal.Quotient.nontrivial_iff.mpr hq_prime.ne_top
  haveI : IsLocalRing S₀ :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  -- Apply FiniteInjectiveEtale_IsMonogenic to get B₀ such that R₀[B₀] = S₀
  haveI : Module.Finite R₀ S₀ := RingHom.finite_algebraMap.mp hφ₀_fin
  haveI : Algebra.Etale R₀ S₀ := RingHom.etale_algebraMap.mp hφ₀_etale
  obtain ⟨B₀, adj⟩ :=
    monogenic_of_finiteInjectiveEtale (R:=R₀) (S:=S₀)
  let f₀ := minpoly R₀ B₀
  -- Lift B₀ to B ∈ S
  obtain ⟨B, hB⟩ := Ideal.Quotient.mk_surjective B₀
  -- Step 5: Lift f₀ to a monic polynomial f₁ over R
  -- First, we need to lift the coefficients of f₀ from R₀ to R
  have h_f₀_exists : ∃ f₁ : R[X], (f₁.map (Ideal.Quotient.mk p)) = f₀ ∧ f₁.Monic := by
    -- For this to work, we need f₀ to be monic (or have unit leading coefficient)
    -- In a finite étale extension R₀[X]/(f₀) ≅ S₀, f₀ can be chosen monic
    -- First show f₀ ∈ lifts (Ideal.Quotient.mk p) - true since quotient map is surjective
    have h_lifts : f₀ ∈ Polynomial.lifts (Ideal.Quotient.mk p) := by
      rw [Polynomial.mem_lifts]
      exact Polynomial.map_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective f₀
    have h_f₀_monic : f₀.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral B₀)
    -- Now apply the lifting theorem for monic polynomials
    obtain ⟨f₁, hf₁_eq, _, hf₁_monic⟩ :=
      Polynomial.lifts_and_degree_eq_and_monic h_lifts h_f₀_monic
    exact ⟨f₁, hf₁_eq, hf₁_monic⟩
  obtain ⟨f₁, hf₁_map, hf₁_monic⟩ := h_f₀_exists
  -- Step 6: Key relation - since R₀ → S₀ is étale, we have ms₀ = mr₀·S₀
  -- This means ms = q + mr·S in S
  let mr := IsLocalRing.maximalIdeal R
  let ms := IsLocalRing.maximalIdeal S
  have hq_le_ms : q ≤ ms := IsLocalRing.le_maximalIdeal hq_prime.ne_top
  have h_ms_eq : ms = q ⊔ Ideal.map φ mr :=
    maximalIdeal_eq_sup_of_etale_quotient q hétale
  -- Step 7: Two cases based on whether f₁(B) generates the right ideal
  -- Case analysis: does f₁(B) generate q modulo mr·S?
  -- The element f₁(B) ∈ S
  let f₁_B := Polynomial.aeval B f₁
  -- Since S is a UFD and q has height 1, q is principal
  have h_q_principal : ∃ q₀ : S, q = Ideal.span {q₀} :=
    height_one_prime_principal_of_UFD q hq_height
  obtain ⟨q₀, hq₀⟩ := h_q_principal
  -- Check if f₁(B) generates the right structure
  by_cases h_gen : f₁_B ∈ ms ∧ Ideal.span {f₁_B} ⊔ Ideal.map φ mr • ⊤ = ms
  · -- Case 1: f₁(B) generates ms/(mr·S), so R[B] = S
    -- TODO: Fill in this proof using Nakayama's lemma
    have h_adjoin_top : Algebra.adjoin R {B} = ⊤ := by
      -- Convert `adj : Algebra.adjoin R₀ {B₀} = ⊤` to the form needed by the helper
      have h_gen' : Algebra.adjoin (R ⧸ q.comap (algebraMap R S))
          {Ideal.Quotient.mk q B} = ⊤ := by
        convert adj using 2
        simp [hB]
      -- aeval B f₁ ∈ Algebra.adjoin R {B}
      have hπ_mem : f₁_B ∈ Algebra.adjoin R {B} := by
        rw [Algebra.adjoin_singleton_eq_range_aeval]
        exact ⟨f₁, rfl⟩
      -- Convert h_gen.2 to the right form: ms = span {f₁_B} ⊔ map φ mr
      have h_ms' : IsLocalRing.maximalIdeal S =
          Ideal.span {f₁_B} ⊔ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) := by
        have h := h_gen.2
        simp only [Ideal.smul_eq_mul, Ideal.mul_top] at h
        exact h.symm
      exact adjoin_eq_top_of_quotient_gen B q h_gen' f₁_B hπ_mem h_ms'
    have hB_int := Algebra.IsIntegral.isIntegral (R:=R) B
    exact ⟨minpoly R B, ⟨IsAdjoinRootMonic.mkOfAdjoinEqTop hB_int h_adjoin_top⟩⟩
  · -- Case 2: f₁(B) does not generate the right ideal
    -- Then f₁(B) = q₀ * a for some a ∈ ms (since f₁(B) ∈ q but doesn't generate q alone)
    have h_f₁B_in_q : f₁_B ∈ q := by
      -- Suffices to show mk q (aeval B f₁) = 0 in S₀
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      change Ideal.Quotient.mk q (Polynomial.aeval B f₁) = 0
      -- Push mk q through eval₂: σ(p.eval₂ f x) = p.eval₂ (σ∘f) (σ x)
      simp only [Polynomial.aeval_def]
      rw [Polynomial.hom_eval₂]
      -- Replace mk q B = B₀
      rw [hB]
      -- Replace composite ring hom using the commutative square
      have hcomp : (Ideal.Quotient.mk q).comp (algebraMap R S) =
          φ₀.comp (Ideal.Quotient.mk p) := by
        ext r
        change Ideal.Quotient.mk q (φ r) = φ₀ (Ideal.Quotient.mk p r)
        exact Ideal.quotientMap_mk.symm
      rw [hcomp]
      -- Use eval₂_map: (f.map g).eval₂ h x = f.eval₂ (h.comp g) x
      rw [← Polynomial.eval₂_map]
      rw [hf₁_map]
      -- Goal: f₀.eval₂ φ₀ B₀ = 0
      -- Convert to aeval (requires algebraMap R₀ S₀ = φ₀)
      change Polynomial.aeval B₀ f₀ = 0
      exact minpoly.aeval (A:=R₀) (B:=S₀) B₀
    have h_f₁B_factorization : ∃ a : S, f₁_B = q₀ * a := by
      rw [hq₀] at h_f₁B_in_q
      exact Ideal.mem_span_singleton.mp h_f₁B_in_q
    obtain ⟨a, ha⟩ := h_f₁B_factorization
    -- Key: f₁'(B) is not in ms (derivative is a unit modulo ms)
    have h_deriv_unit : f₁.derivative.aeval B ∉ ms := by
      -- Step 3: Get FaithfulSMul R₀ S₀ from injectivity of φ₀
      haveI : FaithfulSMul R₀ S₀ := by
        rw [faithfulSMul_iff_algebraMap_injective]
        exact hφ₀_inj
      have h_unit_B₀ : IsUnit (Polynomial.aeval B₀ (minpoly R₀ B₀).derivative) :=
        deriv_isUnit_of_monogenic B₀ adj
      -- Step 5: Commutative diagram - mk q (f₁'.aeval B) = f₀'.aeval B₀
      have h_deriv_comm : Ideal.Quotient.mk q (f₁.derivative.aeval B) =
          (f₀.derivative).aeval B₀ := by
        -- Push mk q through aeval using hom_eval₂
        simp only [Polynomial.aeval_def]
        rw [Polynomial.hom_eval₂]
        rw [hB]
        -- Replace composite ring hom
        have hcomp : (Ideal.Quotient.mk q).comp (algebraMap R S) =
            φ₀.comp (Ideal.Quotient.mk p) := by
          ext r
          change Ideal.Quotient.mk q (φ r) = φ₀ (Ideal.Quotient.mk p r)
          exact Ideal.quotientMap_mk.symm
        rw [hcomp]
        -- Use eval₂_map
        rw [← Polynomial.eval₂_map]
        -- Need: f₁.derivative.map (mk p) = f₀.derivative
        congr 1
        rw [← Polynomial.derivative_map, hf₁_map]
      -- Step 6: Conclude f₁'(B) ∉ ms
      intro h_in_ms
      -- f₁'.aeval B ∈ ms means it's not a unit
      have h_not_unit : ¬ IsUnit (f₁.derivative.aeval B) :=
        (IsLocalRing.mem_maximalIdeal _).mp h_in_ms
      -- For a local hom, non-units map to non-units; for surjective local hom, units
      -- lift to units. So non-unit maps to non-unit.
      haveI : IsLocalHom (Ideal.Quotient.mk q) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      have h_nonunit_image : ¬ IsUnit (Ideal.Quotient.mk q (f₁.derivative.aeval B)) :=
        fun h_unit => h_not_unit (isUnit_of_map_unit (Ideal.Quotient.mk q) _ h_unit)
      -- But h_deriv_comm says the image equals aeval B₀ f₀', which is a unit
      rw [h_deriv_comm] at h_nonunit_image
      exact h_nonunit_image h_unit_B₀
    -- Consider B' = B + q₀
    let B' := B + q₀
    -- Compute f₁(B') using Taylor expansion
    -- f₁(B') = f₁(B) + f₁'(B) * q₀ + q₀² * (higher order terms)
    -- = q₀ * a + f₁'(B) * q₀ + q₀² * b
    -- = q₀ * (a + f₁'(B) + q₀ * b)
    have h_f₁B'_factorization : ∃ b : S, Polynomial.aeval B' f₁ =
      q₀ * (a + f₁.derivative.aeval B + q₀ * b) := by
      -- Apply the Taylor expansion to f₁ with x = B and h = q₀
      obtain ⟨c, hc⟩ := taylor_expansion_aeval f₁ B q₀
      -- We have: f₁.aeval (B + q₀) = f₁.aeval B + f₁.derivative.aeval B * q₀ + q₀² * c
      -- Substitute ha: f₁.aeval B = q₀ * a (note: f₁_B = aeval B f₁)
      use c
      -- Unfold f₁_B in ha to get: Polynomial.aeval B f₁ = q₀ * a
      have ha' : Polynomial.aeval B f₁ = q₀ * a := ha
      rw [hc, ha']
      -- Goal: q₀ * a + f₁.derivative.aeval B * q₀ + q₀² * c =
      --       q₀ * (a + f₁.derivative.aeval B + q₀ * c)
      ring
    obtain ⟨b, hb⟩ := h_f₁B'_factorization
    -- Since f₁'(B) ∉ ms and a + f₁'(B) + q₀ * b has f₁'(B) as the "main term",
    -- (a + f₁'(B) + q₀ * b) is a unit (not in ms)
    have h_cofactor_unit : IsUnit (a + f₁.derivative.aeval B + q₀ * b) := by
      -- Strategy: show (a + q₀ * b) ∈ ms, then use that unit + ms element = unit
      have hq_le_ms' : q ≤ ms := IsLocalRing.le_maximalIdeal hq_prime.ne_top
      have hq₀_in_ms : q₀ ∈ ms := hq_le_ms' (hq₀ ▸ Ideal.mem_span_singleton_self q₀)
      have hq₀b_in_ms : q₀ * b ∈ ms := mul_comm q₀ b ▸ Ideal.mul_mem_left ms b hq₀_in_ms
      -- a ∈ ms: If a were a unit, then span {q₀ * a} = span {q₀} = q, contradicting h_gen
      have ha_in_ms : a ∈ ms := by
        by_contra ha_not_in_ms
        have ha_unit : IsUnit a := IsLocalRing.notMem_maximalIdeal.mp ha_not_in_ms
        have h_span_eq' : Ideal.span {f₁_B} = q := by
          rw [show f₁_B = q₀ * a from ha, hq₀]
          exact Ideal.span_singleton_mul_right_unit ha_unit q₀
        have h_f₁B_in_ms' : f₁_B ∈ ms := hq_le_ms' h_f₁B_in_q
        have h_contains : Ideal.span {f₁_B} ⊔ Ideal.map φ mr • ⊤ = ms := by
          rw [h_span_eq', h_ms_eq, Ideal.smul_eq_mul, Ideal.mul_top]
        exact h_gen ⟨h_f₁B_in_ms', h_contains⟩
      have h_sum_in_ms : a + q₀ * b ∈ ms := Ideal.add_mem ms ha_in_ms hq₀b_in_ms
      -- Rewrite: a + f₁'(B) + q₀*b = f₁'(B) + (a + q₀*b)
      have h_eq : a + f₁.derivative.aeval B + q₀ * b = f₁.derivative.aeval B + (a + q₀ * b) := by
        ring
      rw [h_eq, ← IsLocalRing.notMem_maximalIdeal]
      -- If x ∉ ms and y ∈ ms, then x + y ∉ ms (since x = (x+y) - y)
      intro h
      have : f₁.derivative.aeval B ∈ ms := by
        convert Ideal.sub_mem ms h h_sum_in_ms using 1; ring
      exact h_deriv_unit this
    -- Therefore, Ideal.span {f₁(B')} = Ideal.span {q₀} = q
    have h_span_eq : Ideal.span {Polynomial.aeval B' f₁} = q := by
      rw [hb, hq₀]
      -- Goal: Ideal.span {q₀ * (a + f₁.derivative.aeval B + q₀ * b)} = Ideal.span {q₀}
      -- Use that multiplication by unit preserves span
      exact Ideal.span_singleton_mul_right_unit h_cofactor_unit q₀
    -- Now we can show R[B'] = S using B' = B + q₀
    -- The key is that B' still lifts B₀ (since q₀ ∈ q, it maps to 0 in S₀)
    have hB'_lifts : Ideal.Quotient.mk q B' = B₀ := by
      have hq₀_in_q : q₀ ∈ q := hq₀ ▸ Ideal.mem_span_singleton_self q₀
      change Ideal.Quotient.mk q (B + q₀) = B₀
      simp only [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hq₀_in_q, add_zero, hB]
    -- Step 8: Show Algebra.adjoin R {B'} = ⊤ and derive the isomorphism
    -- The correct witness polynomial is minpoly R B', not f₁.
    -- (f₁(B') = q₀ · unit ≠ 0, so eval at B' doesn't factor through R[X]/(f₁))
    --
    -- Proof that Algebra.adjoin R {B'} = ⊤:
    -- (1) adj + hB'_lifts ⟹ Algebra.adjoin R {B'} + q = S (as R-submodules),
    --     since every element of S₀ = S/q is a polynomial in β₀ = mk q B' over R₀.
    -- (2) aeval B' f₁ ∈ Algebra.adjoin R {B'} generates q (by h_span_eq),
    --     so S = A + (aeval B' f₁)·S, and iterating: S = A + qⁿ for all n ≥ 1.
    -- (3) The subalgebra A is local: S is integral over A (since S is integral
    --     over R ⊆ A), so by lying-over/going-up, A has unique maximal ideal
    --     ms ∩ A, and (aeval B' f₁) ∈ ms ∩ A is in the Jacobson radical of A.
    -- (4) S is finitely generated as an A-module (since f.g. over R ⊆ A).
    --     By Nakayama over A: the A-module S/A satisfies q·(S/A) = S/A with q
    --     in the Jacobson radical, so S/A = 0, i.e., A = S.
    have h_adjoin_top : Algebra.adjoin R {B'} = ⊤ := by
      -- Convert `adj : Algebra.adjoin R₀ {B₀} = ⊤` using `hB'_lifts : mk q B' = B₀`
      have h_gen' : Algebra.adjoin (R ⧸ q.comap (algebraMap R S))
          {Ideal.Quotient.mk q B'} = ⊤ := by
        convert adj using 2
        simp [hB'_lifts]
      -- aeval B' f₁ ∈ Algebra.adjoin R {B'}
      have hπ_mem : Polynomial.aeval B' f₁ ∈ Algebra.adjoin R {B'} := by
        rw [Algebra.adjoin_singleton_eq_range_aeval]
        exact ⟨f₁, rfl⟩
      -- ms = span {aeval B' f₁} ⊔ map φ mr (from h_span_eq and h_ms_eq)
      have h_ms' : IsLocalRing.maximalIdeal S =
          Ideal.span {Polynomial.aeval B' f₁} ⊔
            Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) := by
        have h := h_ms_eq
        rw [← h_span_eq] at h
        exact h
      exact adjoin_eq_top_of_quotient_gen B' q h_gen' (Polynomial.aeval B' f₁) hπ_mem h_ms'
    have hB'_int := Algebra.IsIntegral.isIntegral (R:=R) B'
    exact ⟨minpoly R B', ⟨IsAdjoinRootMonic.mkOfAdjoinEqTop hB'_int h_adjoin_top⟩⟩

-- Alternative formulation using explicit ring homomorphism
theorem monogenic_of_etale_height_one_quotient'
    [IsDomain R] [IsDomain S] [IsIntegrallyClosed R]
    [UniqueFactorizationMonoid S]
    (φ : R →+* S) (hφ_fin : φ.Finite) (hφ_inj : Injective φ)
    (q : Ideal S) [ic : IsIntegrallyClosed <| R ⧸ (q.comap <| φ)]
    [hq_prime : q.IsPrime] (hq_height : q.height = 1)
    (hétale : Etale (Ideal.quotientMap q φ (le_refl (q.comap φ)))) :
    ∃(β : S), Algebra.adjoin φ.range {β} = ⊤ := by
  letI : Algebra R S := φ.toAlgebra
  have eq : φ = algebraMap R S := (algebraMap_toAlgebra φ).symm
  rw [eq] at hφ_inj
  rw [eq] at ic
  rw [eq]
  haveI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hφ_inj
  haveI : Module.Finite R S := finite_algebraMap.mp hφ_fin
  have ⟨f, ⟨adj_monic⟩⟩ := monogenic_of_etale_height_one_quotient (R:=R) (S:=S) q hq_height hétale
  use adj_monic.root
  -- adj_monic.adjoin_root_eq_top gives: Algebra.adjoin R {adj_monic.root} = ⊤
  -- Goal: Algebra.adjoin φ.range {adj_monic.root} = ⊤
  -- Key: algebraMap R S = φ (by `eq`), so (algebraMap R S).range = φ.range
  -- Since φ is injective, R ≃ φ.range, and the R-subalgebra equals the φ.range-subalgebra
  have h_adjoin_R : Algebra.adjoin R {adj_monic.root} = ⊤ := adj_monic.adjoin_root_eq_top
  -- Show: for any s ∈ S, s ∈ Algebra.adjoin φ.range {adj_monic.root}
  -- From h_adjoin_R, s can be written as a polynomial in adj_monic.root with R-coefficients
  -- Since algebraMap R S = φ, these coefficients land in φ.range
  ext s
  constructor
  · -- mp: s ∈ Algebra.adjoin φ.range {β} → s ∈ ⊤ (trivial)
    intro _; trivial
  · -- mpr: s ∈ ⊤ → s ∈ Algebra.adjoin φ.range {β}
    intro _
    -- From h_adjoin_R, s ∈ Algebra.adjoin R {adj_monic.root}
    have hs : s ∈ Algebra.adjoin R {adj_monic.root} := by rw [h_adjoin_R]; trivial
    -- Use that Algebra.adjoin R {x} = (aeval x).range
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hs ⊢
    -- hs : s ∈ (Polynomial.aeval adj_monic.root).range (as R-alg hom)
    -- Goal: s ∈ (Polynomial.aeval adj_monic.root).range (as φ.range-alg hom)
    obtain ⟨p, hp⟩ := hs
    -- hp : (aeval adj_monic.root) p = s (where aeval is the R-algebra hom)
    -- Construct the corresponding polynomial over φ.range
    -- Map p : R[X] to p' : φ.range[X] using the isomorphism R ≃ φ.range
    let equiv_R_range : R ≃+* φ.range := RingEquiv.ofBijective
      (φ.rangeRestrict) ⟨fun _ _ h => hφ_inj (Subtype.ext_iff.mp h), φ.rangeRestrict_surjective⟩
    let p' : Polynomial φ.range := p.map equiv_R_range.toRingHom
    use p'
    -- Show: aeval adj_monic.root p' = aeval adj_monic.root p = s
    -- Both aevals evaluate to the same thing because:
    -- - The polynomial maps p.coeff i ↦ equiv_R_range (p.coeff i) = ⟨φ (p.coeff i), _⟩
    -- - algebraMap φ.range S is the subtype inclusion, so it maps ⟨x, _⟩ ↦ x
    -- - Therefore algebraMap φ.range S (equiv_R_range r) = φ r = algebraMap R S r
    -- hp : (aeval adj_monic.root) p = s definitionally equals Polynomial.eval₂ ... p = s
    -- Goal is also in terms of aeval, need to unfold to eval₂
    change Polynomial.eval₂ (algebraMap φ.range S) adj_monic.root p' = s
    rw [Polynomial.eval₂_map]
    -- Goal: eval₂ ((Subtype.val).comp equiv_R_range) adj_monic.root p = s
    -- hp: eval₂ (algebraMap R S) adj_monic.root p = s
    -- Need to show the ring homs are equal; convert handles this by definitional equality
    convert hp using 2

end Monogenic
