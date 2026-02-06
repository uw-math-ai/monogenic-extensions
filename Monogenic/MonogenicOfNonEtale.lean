/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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

/-!
# Monogenicity from Étale Height-One Quotients

This file proves that if `R` and `S` are regular local rings with `S` a finite extension of `R`,
and there exists a height one prime `q ⊆ S` such that `R/(q ∩ R) → S/q` is étale,
then `S` is a monogenic extension of `R`.

## Main results

- `monogenic_of_etale_height_one_quotient`: the main theorem.
- `monogenic_of_etale_height_one_quotient'`: variant with explicit ring homomorphism.
-/

open Polynomial Function RingHom

namespace Monogenic

variable {R S} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
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
/-- If `S` is a finite `R`-module, the induced quotient map `R/(q ∩ R) →+* S/q` is finite. -/
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
  · intro y hy; exact Submodule.subset_span (Finset.mem_image_of_mem _ hy)
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
  have hq_ne_bot : q ≠ ⊥ := by
    intro h
    rw [h, Ideal.height_bot] at hq_height
    exact zero_ne_one hq_height
  obtain ⟨p, hp_mem, hp_prime⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot hq_prime hq_ne_bot
  have h_span_prime : (Ideal.span {p}).IsPrime := by
    rw [Ideal.span_singleton_prime hp_prime.ne_zero]
    exact hp_prime
  have h_span_le : Ideal.span {p} ≤ q := (Ideal.span_singleton_le_iff_mem (I := q)).mpr hp_mem
  have h_span_ne_bot : Ideal.span {p} ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact hp_prime.ne_zero
  have h_eq : Ideal.span {p} = q := by
    by_contra h_ne
    have h_lt : Ideal.span {p} < q := lt_of_le_of_ne h_span_le h_ne
    haveI : (Ideal.span {p}).IsPrime := h_span_prime
    have hq_ht_ne_top : q.height ≠ ⊤ := by
      rw [hq_height]
      exact ENat.one_ne_top
    haveI : q.FiniteHeight := ⟨Or.inr hq_ht_ne_top⟩
    haveI : (Ideal.span {p}).FiniteHeight := Ideal.finiteHeight_of_le h_span_le hq_prime.ne_top
    have h_ht_lt := Ideal.height_strict_mono_of_is_prime h_lt
    rw [hq_height] at h_ht_lt
    have h_ht_zero : (Ideal.span {p}).height = 0 := ENat.lt_one_iff_eq_zero.mp h_ht_lt
    rw [Ideal.height_eq_primeHeight, Ideal.primeHeight_eq_zero_iff] at h_ht_zero
    have h_span_eq_bot : Ideal.span {p} = ⊥ := by
      have h_mem : Ideal.span {p} ∈ (⊥ : Ideal S).minimalPrimes := h_ht_zero
      have : (⊥ : Ideal S).minimalPrimes = minimalPrimes S := rfl
      rw [this, IsDomain.minimalPrimes_eq_singleton_bot] at h_mem
      exact Set.mem_singleton_iff.mp h_mem
    exact h_span_ne_bot h_span_eq_bot
  exact ⟨p, h_eq.symm⟩

/-- Taylor expansion: `f(x + h) = f(x) + f'(x) · h + h² · c` for some `c`. -/
lemma taylor_expansion_aeval {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (f : R[X]) (x h : S) :
    ∃ c : S, f.aeval (x + h) = f.aeval x + f.derivative.aeval x * h + h^2 * c := by
  induction f using Polynomial.induction_on with
  | C r =>
    use 0
    simp only [Polynomial.aeval_C, Polynomial.derivative_C, Polynomial.aeval_zero,
      mul_zero, add_zero, sq, zero_mul]
  | add p₁ p₂ ih₁ ih₂ =>
    obtain ⟨c₁, hc₁⟩ := ih₁
    obtain ⟨c₂, hc₂⟩ := ih₂
    use c₁ + c₂
    simp only [Polynomial.aeval_add, Polynomial.derivative_add] at *
    rw [hc₁, hc₂]
    ring
  | monomial n r ih =>
    simp only [Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow,
      Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
      Polynomial.derivative_X_pow]
    have h_binom : (x + h) ^ (n + 1) = ∑ m ∈ Finset.range (n + 2),
        x ^ m * h ^ (n + 1 - m) * (n + 1).choose m := add_pow x h (n + 1)
    let c' := ∑ m ∈ Finset.range n, x ^ m * h ^ (n - 1 - m) * (n + 1).choose m
    use algebraMap R S r * c'
    rw [h_binom]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_self, pow_zero,
      Nat.add_sub_cancel]
    have h_choose_n : (n + 1).choose n = n + 1 := Nat.choose_succ_self_right n
    rw [h_choose_n]
    have h_sum_eq : (∑ m ∈ Finset.range n, x ^ m * h ^ (n + 1 - m) * (n + 1).choose m) =
        h ^ 2 * c' := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mem_range] at hm
      have h_exp : n + 1 - m = (n - 1 - m) + 2 := by omega
      rw [h_exp, pow_add]
      ring
    rw [h_sum_eq]
    have h_exp_simp : n + 1 - n = 1 := by omega
    simp only [h_exp_simp, pow_one, ← map_natCast (algebraMap R S)]
    ring

/-- For étale quotients of local rings, `m_S = q ⊔ (m_R · S)`. -/
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
  letI : Algebra R₀ S₀ := φ₀.toAlgebra
  have hφ₀_eq : algebraMap R₀ S₀ = φ₀ := RingHom.algebraMap_toAlgebra φ₀
  have hφ₀_fin : φ₀.Finite := quotientMap_finite q
  have hφ₀_inj : Injective φ₀ := Ideal.quotientMap_injective
  haveI hp_prime : p.IsPrime := Ideal.IsPrime.comap φ
  haveI : IsDomain R₀ := Ideal.Quotient.isDomain p
  haveI : IsDomain S₀ := Ideal.Quotient.isDomain q
  haveI : Nontrivial R₀ := Ideal.Quotient.nontrivial_iff.mpr hp_prime.ne_top
  haveI : IsLocalRing R₀ :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  haveI : Nontrivial S₀ := Ideal.Quotient.nontrivial_iff.mpr hq_prime.ne_top
  haveI : IsLocalRing S₀ :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  have h_etale := (RingHom.etale_iff_formallyUnramified_and_smooth φ₀).mp hétale
  have unram_φ₀ : φ₀.FormallyUnramified := h_etale.1
  haveI : Algebra.FormallyUnramified R₀ S₀ := by rwa [← hφ₀_eq] at unram_φ₀
  haveI : IsLocalHom (algebraMap R₀ S₀) := by
    rw [hφ₀_eq]
    exact RingHom.IsIntegral.isLocalHom (RingHom.IsIntegral.of_finite hφ₀_fin) hφ₀_inj
  haveI : Algebra.EssFiniteType R₀ S₀ :=
    RingHom.FiniteType.essFiniteType (RingHom.FiniteType.of_finite hφ₀_fin)
  have h_max_eq : Ideal.map φ₀ (IsLocalRing.maximalIdeal R₀) = IsLocalRing.maximalIdeal S₀ := by
    rw [← hφ₀_eq]; exact Algebra.FormallyUnramified.map_maximalIdeal
  have h_max_R₀ : IsLocalRing.maximalIdeal R₀ = Ideal.map (Ideal.Quotient.mk p) mr :=
    maximalIdeal_quotient_eq_map p
  have h_max_S₀ : IsLocalRing.maximalIdeal S₀ = Ideal.map (Ideal.Quotient.mk q) ms :=
    maximalIdeal_quotient_eq_map q
  have h_comp : φ₀.comp (Ideal.Quotient.mk p) = (Ideal.Quotient.mk q).comp φ := by
    ext r
    change φ₀ (Ideal.Quotient.mk p r) = Ideal.Quotient.mk q (φ r)
    exact Ideal.quotientMap_mk
  have h_images_eq : Ideal.map (Ideal.Quotient.mk q) ms =
      Ideal.map (Ideal.Quotient.mk q) (Ideal.map φ mr) :=
    calc Ideal.map (Ideal.Quotient.mk q) ms
      _ = IsLocalRing.maximalIdeal S₀ := h_max_S₀.symm
      _ = Ideal.map φ₀ (IsLocalRing.maximalIdeal R₀) := h_max_eq.symm
      _ = Ideal.map φ₀ (Ideal.map (Ideal.Quotient.mk p) mr) := by rw [h_max_R₀]
      _ = Ideal.map (Ideal.Quotient.mk q) (Ideal.map φ mr) := by
          rw [Ideal.map_map, Ideal.map_map, h_comp]
  have h_sup_image : Ideal.map (Ideal.Quotient.mk q) (q ⊔ Ideal.map φ mr) =
      Ideal.map (Ideal.Quotient.mk q) (Ideal.map φ mr) := by
    rw [Ideal.map_sup, Ideal.map_quotient_self]; simp
  rw [← h_sup_image, Ideal.map_eq_iff_sup_ker_eq_of_surjective _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, sup_eq_left.mpr hq_le_ms] at h_images_eq
  calc ms = (q ⊔ Ideal.map φ mr) ⊔ q := h_images_eq
    _ = q ⊔ Ideal.map φ mr := by rw [sup_comm, sup_left_idem]


end SubLemmas

/-- Given regular local rings R and S with S a finite extension of R, if there exists a
height one prime ideal q ⊆ S such that the induced map R/(q ∩ R) → S/q is étale,
then S is a monogenic extension of R.

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
  let φ := algebraMap R S
  have φ_eq : algebraMap R S = φ := RingHom.algebraMap_toAlgebra φ
  by_cases hφ_etale : Algebra.Etale R S
  · let ⟨β, adj⟩ := monogenic_of_finiteInjectiveEtale (R:=R) (S:=S)
    have hβ_int := Algebra.IsIntegral.isIntegral (R:=R) β
    exact ⟨minpoly R β, ⟨IsAdjoinRootMonic.mkOfAdjoinEqTop hβ_int adj⟩⟩
  let p : Ideal R := q.comap φ
  let R₀ := R ⧸ p
  let S₀ := S ⧸ q
  let φ₀ : R₀ →+* S₀ := Ideal.quotientMap q φ (le_refl p)
  have hφ₀_etale : Etale φ₀ := hétale
  have hφ₀_fin : φ₀.Finite := quotientMap_finite q
  have hφ₀_inj : Injective φ₀ := Ideal.quotientMap_injective
  haveI : IsDomain R₀ := Ideal.Quotient.isDomain p
  haveI : IsDomain S₀ := Ideal.Quotient.isDomain q
  haveI hp_prime : p.IsPrime := Ideal.IsPrime.comap φ
  haveI : Nontrivial R₀ := Ideal.Quotient.nontrivial_iff.mpr hp_prime.ne_top
  haveI : IsLocalRing R₀ :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  haveI : Nontrivial S₀ := Ideal.Quotient.nontrivial_iff.mpr hq_prime.ne_top
  haveI : IsLocalRing S₀ :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  haveI : Module.Finite R₀ S₀ := RingHom.finite_algebraMap.mp hφ₀_fin
  haveI : Algebra.Etale R₀ S₀ := RingHom.etale_algebraMap.mp hφ₀_etale
  obtain ⟨B₀, adj⟩ :=
    monogenic_of_finiteInjectiveEtale (R:=R₀) (S:=S₀)
  let f₀ := minpoly R₀ B₀
  obtain ⟨B, hB⟩ := Ideal.Quotient.mk_surjective B₀
  have h_f₀_exists : ∃ f₁ : R[X], (f₁.map (Ideal.Quotient.mk p)) = f₀ ∧ f₁.Monic := by
    have h_lifts : f₀ ∈ Polynomial.lifts (Ideal.Quotient.mk p) := by
      rw [Polynomial.mem_lifts]
      exact Polynomial.map_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective f₀
    have h_f₀_monic : f₀.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral B₀)
    obtain ⟨f₁, hf₁_eq, _, hf₁_monic⟩ :=
      Polynomial.lifts_and_degree_eq_and_monic h_lifts h_f₀_monic
    exact ⟨f₁, hf₁_eq, hf₁_monic⟩
  obtain ⟨f₁, hf₁_map, hf₁_monic⟩ := h_f₀_exists
  let mr := IsLocalRing.maximalIdeal R
  let ms := IsLocalRing.maximalIdeal S
  have hq_le_ms : q ≤ ms := IsLocalRing.le_maximalIdeal hq_prime.ne_top
  have h_ms_eq : ms = q ⊔ Ideal.map φ mr :=
    maximalIdeal_eq_sup_of_etale_quotient q hétale
  let f₁_B := Polynomial.aeval B f₁
  have h_q_principal : ∃ q₀ : S, q = Ideal.span {q₀} :=
    height_one_prime_principal_of_UFD q hq_height
  obtain ⟨q₀, hq₀⟩ := h_q_principal
  by_cases h_gen : f₁_B ∈ ms ∧ Ideal.span {f₁_B} ⊔ Ideal.map φ mr • ⊤ = ms
  · have h_adjoin_top : Algebra.adjoin R {B} = ⊤ := by
      have h_gen' : Algebra.adjoin (R ⧸ q.comap (algebraMap R S))
          {Ideal.Quotient.mk q B} = ⊤ := by
        convert adj using 2
        simp [hB]
      have hπ_mem : f₁_B ∈ Algebra.adjoin R {B} := by
        rw [Algebra.adjoin_singleton_eq_range_aeval]
        exact ⟨f₁, rfl⟩
      have h_ms' : IsLocalRing.maximalIdeal S =
          Ideal.span {f₁_B} ⊔ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) := by
        have h := h_gen.2
        simp only [Ideal.smul_eq_mul, Ideal.mul_top] at h
        exact h.symm
      exact adjoin_eq_top_of_quotient_gen B q h_gen' f₁_B hπ_mem h_ms'
    have hB_int := Algebra.IsIntegral.isIntegral (R:=R) B
    exact ⟨minpoly R B, ⟨IsAdjoinRootMonic.mkOfAdjoinEqTop hB_int h_adjoin_top⟩⟩
  · have h_f₁B_in_q : f₁_B ∈ q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      change Ideal.Quotient.mk q (Polynomial.aeval B f₁) = 0
      simp only [Polynomial.aeval_def]
      rw [Polynomial.hom_eval₂]
      rw [hB]
      have hcomp : (Ideal.Quotient.mk q).comp (algebraMap R S) =
          φ₀.comp (Ideal.Quotient.mk p) := by
        ext r
        change Ideal.Quotient.mk q (φ r) = φ₀ (Ideal.Quotient.mk p r)
        exact Ideal.quotientMap_mk.symm
      rw [hcomp]
      rw [← Polynomial.eval₂_map]
      rw [hf₁_map]
      change Polynomial.aeval B₀ f₀ = 0
      exact minpoly.aeval (A:=R₀) (B:=S₀) B₀
    have h_f₁B_factorization : ∃ a : S, f₁_B = q₀ * a := by
      rw [hq₀] at h_f₁B_in_q
      exact Ideal.mem_span_singleton.mp h_f₁B_in_q
    obtain ⟨a, ha⟩ := h_f₁B_factorization
    have h_deriv_unit : f₁.derivative.aeval B ∉ ms := by
      haveI : FaithfulSMul R₀ S₀ := by
        rw [faithfulSMul_iff_algebraMap_injective]
        exact hφ₀_inj
      have h_unit_B₀ : IsUnit (Polynomial.aeval B₀ (minpoly R₀ B₀).derivative) :=
        derivative_isUnit_of_monogenic B₀ adj
      have h_deriv_comm : Ideal.Quotient.mk q (f₁.derivative.aeval B) =
          (f₀.derivative).aeval B₀ := by
        simp only [Polynomial.aeval_def]
        rw [Polynomial.hom_eval₂]
        rw [hB]
        have hcomp : (Ideal.Quotient.mk q).comp (algebraMap R S) =
            φ₀.comp (Ideal.Quotient.mk p) := by
          ext r
          change Ideal.Quotient.mk q (φ r) = φ₀ (Ideal.Quotient.mk p r)
          exact Ideal.quotientMap_mk.symm
        rw [hcomp]
        rw [← Polynomial.eval₂_map]
        congr 1
        rw [← Polynomial.derivative_map, hf₁_map]
      intro h_in_ms
      have h_not_unit : ¬ IsUnit (f₁.derivative.aeval B) :=
        (IsLocalRing.mem_maximalIdeal _).mp h_in_ms
      haveI : IsLocalHom (Ideal.Quotient.mk q) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      have h_nonunit_image : ¬ IsUnit (Ideal.Quotient.mk q (f₁.derivative.aeval B)) :=
        fun h_unit => h_not_unit (isUnit_of_map_unit (Ideal.Quotient.mk q) _ h_unit)
      rw [h_deriv_comm] at h_nonunit_image
      exact h_nonunit_image h_unit_B₀
    let B' := B + q₀
    have h_f₁B'_factorization : ∃ b : S, Polynomial.aeval B' f₁ =
      q₀ * (a + f₁.derivative.aeval B + q₀ * b) := by
      obtain ⟨c, hc⟩ := taylor_expansion_aeval f₁ B q₀
      use c
      have ha' : Polynomial.aeval B f₁ = q₀ * a := ha
      rw [hc, ha']
      ring
    obtain ⟨b, hb⟩ := h_f₁B'_factorization
    have h_cofactor_unit : IsUnit (a + f₁.derivative.aeval B + q₀ * b) := by
      have hq_le_ms' : q ≤ ms := IsLocalRing.le_maximalIdeal hq_prime.ne_top
      have hq₀_in_ms : q₀ ∈ ms := hq_le_ms' (hq₀ ▸ Ideal.mem_span_singleton_self q₀)
      have hq₀b_in_ms : q₀ * b ∈ ms := mul_comm q₀ b ▸ Ideal.mul_mem_left ms b hq₀_in_ms
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
      have h_eq : a + f₁.derivative.aeval B + q₀ * b = f₁.derivative.aeval B + (a + q₀ * b) := by
        ring
      rw [h_eq, ← IsLocalRing.notMem_maximalIdeal]
      intro h
      have : f₁.derivative.aeval B ∈ ms := by
        convert Ideal.sub_mem ms h h_sum_in_ms using 1; ring
      exact h_deriv_unit this
    have h_span_eq : Ideal.span {Polynomial.aeval B' f₁} = q := by
      rw [hb, hq₀]
      exact Ideal.span_singleton_mul_right_unit h_cofactor_unit q₀
    have hB'_lifts : Ideal.Quotient.mk q B' = B₀ := by
      have hq₀_in_q : q₀ ∈ q := hq₀ ▸ Ideal.mem_span_singleton_self q₀
      change Ideal.Quotient.mk q (B + q₀) = B₀
      simp only [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hq₀_in_q, add_zero, hB]
    have h_adjoin_top : Algebra.adjoin R {B'} = ⊤ := by
      have h_gen' : Algebra.adjoin (R ⧸ q.comap (algebraMap R S))
          {Ideal.Quotient.mk q B'} = ⊤ := by
        convert adj using 2
        simp [hB'_lifts]
      have hπ_mem : Polynomial.aeval B' f₁ ∈ Algebra.adjoin R {B'} := by
        rw [Algebra.adjoin_singleton_eq_range_aeval]
        exact ⟨f₁, rfl⟩
      have h_ms' : IsLocalRing.maximalIdeal S =
          Ideal.span {Polynomial.aeval B' f₁} ⊔
            Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) := by
        have h := h_ms_eq
        rw [← h_span_eq] at h
        exact h
      exact adjoin_eq_top_of_quotient_gen B' q h_gen' (Polynomial.aeval B' f₁) hπ_mem h_ms'
    have hB'_int := Algebra.IsIntegral.isIntegral (R:=R) B'
    exact ⟨minpoly R B', ⟨IsAdjoinRootMonic.mkOfAdjoinEqTop hB'_int h_adjoin_top⟩⟩

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
  have h_adjoin_R : Algebra.adjoin R {adj_monic.root} = ⊤ := adj_monic.adjoin_root_eq_top
  ext s
  constructor
  · intro _; trivial
  · intro _
    have hs : s ∈ Algebra.adjoin R {adj_monic.root} := by rw [h_adjoin_R]; trivial
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hs ⊢
    obtain ⟨p, hp⟩ := hs
    let equiv_R_range : R ≃+* φ.range := RingEquiv.ofBijective
      (φ.rangeRestrict) ⟨fun _ _ h => hφ_inj (Subtype.ext_iff.mp h), φ.rangeRestrict_surjective⟩
    let p' : Polynomial φ.range := p.map equiv_R_range.toRingHom
    use p'
    change Polynomial.eval₂ (algebraMap φ.range S) adj_monic.root p' = s
    rw [Polynomial.eval₂_map]
    convert hp using 2

end Monogenic
