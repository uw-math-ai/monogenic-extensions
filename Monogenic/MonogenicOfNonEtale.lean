/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Authors: Bianca Viray, Bryan Boehnke, Grant Yang, George Peykanu, Tianshuo Wang
-/
import Monogenic.Generator
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Ideal.Height


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


omit [IsLocalRing R] [IsLocalRing S] in
--Can be placed in Height.lean with no additional imports
/-- In a UFD, a height one prime ideal is principal. -/
lemma Ideal.exists_span_singleton_eq_of_prime_of_height_one {S : Type*} [CommRing S] [IsDomain S]
    [UniqueFactorizationMonoid S]
    (q : Ideal S) [hq_prime : q.IsPrime] (hq_height : q.height = 1) :
    ∃ q₀ : S, q = Ideal.span {q₀} := by
  have hq_ne_bot : q ≠ ⊥ := by rintro rfl; simp at hq_height
  obtain ⟨p, hp_mem, hp_prime⟩ := hq_prime.exists_mem_prime_of_ne_bot hq_ne_bot
  suffices h : Ideal.span {p} = q from ⟨p, h.symm⟩
  by_contra h_ne
  have h_lt := lt_of_le_of_ne (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hp_mem)) h_ne
  haveI : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp_prime.ne_zero).mpr hp_prime
  haveI : q.FiniteHeight := ⟨Or.inr (by rw [hq_height]; exact ENat.one_ne_top)⟩
  haveI := Ideal.finiteHeight_of_le h_lt.le hq_prime.ne_top
  have h0 : (Ideal.span {p}).height = 0 := ENat.lt_one_iff_eq_zero.mp (by
    have := Ideal.height_strict_mono_of_is_prime h_lt; rwa [hq_height] at this)
  rw [Ideal.height_eq_primeHeight, Ideal.primeHeight_eq_zero_iff,
    IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff,
    Ideal.span_singleton_eq_bot] at h0
  exact hp_prime.ne_zero h0

--Can be placed in Taylor.lean with no additional imports.
/-- Taylor expansion for polynomial evaluation over a commutative ring:
    For any polynomial `f` and elements `x`, `h`, there exists `c` such that
    `f(x + h) = f(x) + f'(x) · h + h² · c`.

    Proved by lifting `Polynomial.aeval_add_of_sq_eq_zero` from `S ⧸ ⟨h²⟩`. -/
lemma exists_aeval_add_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (f : R[X]) (x h : S) :
    ∃ c : S, f.aeval (x + h) = f.aeval x + f.derivative.aeval x * h + h ^ 2 * c := by
  set π := Ideal.Quotient.mkₐ R (Ideal.span ({h ^ 2} : Set S))
  have hsq : (π h) ^ 2 = 0 := by
    rw [← map_pow]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have key : π (f.aeval (x + h) - (f.aeval x + f.derivative.aeval x * h)) = 0 := by
    simp only [map_sub, map_add, map_mul, ← Polynomial.aeval_algHom_apply]
    exact sub_eq_zero.mpr (Polynomial.aeval_add_of_sq_eq_zero f _ _ hsq)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp key)
  exact ⟨c, by linear_combination hc⟩

/-- When the quotient map `R/p → S/q` is étale (with p = q.comap (algebraMap R S)),
    and both rings are local, the maximal ideal of `S` decomposes as
    `m_S = q + m_R S`. -/
lemma maximalIdeal_eq_sup_of_etale_quotient
    [Algebra R S] [Module.Finite R S]
    (q : Ideal S) [hq_prime : q.IsPrime]
    (hétale : (Ideal.quotientMap q (algebraMap R S) le_rfl).Etale) :
    IsLocalRing.maximalIdeal S =
      q ⊔ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) := by
  set φ := algebraMap R S; set p := q.comap φ
  set φ₀ : R ⧸ p →+* S ⧸ q := Ideal.quotientMap q φ le_rfl
  letI : Algebra (R ⧸ p) (S ⧸ q) := φ₀.toAlgebra
  have hφ₀_eq : algebraMap (R ⧸ p) (S ⧸ q) = φ₀ := RingHom.algebraMap_toAlgebra φ₀
  haveI hp : p.IsPrime := Ideal.IsPrime.comap φ
  haveI : IsLocalRing (R ⧸ p) := .of_surjective' _ Ideal.Quotient.mk_surjective
  haveI : IsLocalRing (S ⧸ q) := .of_surjective' _ Ideal.Quotient.mk_surjective
  haveI : Algebra.FormallyUnramified (R ⧸ p) (S ⧸ q) := by
    have := ((RingHom.etale_iff_formallyUnramified_and_smooth φ₀).mp hétale).1
    rwa [← hφ₀_eq] at this
  haveI : IsScalarTower R (R ⧸ p) (S ⧸ q) := .of_algebraMap_eq' rfl
  haveI : Module.Finite (R ⧸ p) (S ⧸ q) := Module.Finite.of_restrictScalars_finite R _ _
  haveI : IsLocalHom (algebraMap (R ⧸ p) (S ⧸ q)) := by
    rw [hφ₀_eq]; exact RingHom.IsIntegral.isLocalHom (.of_finite
      (RingHom.finite_algebraMap.mpr ‹_›)) Ideal.quotientMap_injective
  haveI : Algebra.EssFiniteType (R ⧸ p) (S ⧸ q) := .of_finiteType _ _
  -- map (mk I) (maximalIdeal T) = maximalIdeal (T ⧸ I) for prime I
  have mk_max_R : (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk p) =
      IsLocalRing.maximalIdeal (R ⧸ p) := by
    haveI := IsLocalHom.of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
    ext x; obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [sup_eq_left.mpr (IsLocalRing.le_maximalIdeal hp.ne_top)]
  have mk_max_S : (IsLocalRing.maximalIdeal S).map (Ideal.Quotient.mk q) =
      IsLocalRing.maximalIdeal (S ⧸ q) := by
    haveI := IsLocalHom.of_surjective (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
    ext x; obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [sup_eq_left.mpr (IsLocalRing.le_maximalIdeal hq_prime.ne_top)]
  have key : (IsLocalRing.maximalIdeal S).map (Ideal.Quotient.mk q) =
      (Ideal.map φ (IsLocalRing.maximalIdeal R)).map (Ideal.Quotient.mk q) := by
    rw [mk_max_S, ← (by rw [← hφ₀_eq]; exact Algebra.FormallyUnramified.map_maximalIdeal :
      Ideal.map φ₀ (IsLocalRing.maximalIdeal (R ⧸ p)) = IsLocalRing.maximalIdeal (S ⧸ q)),
      ← mk_max_R, Ideal.map_map, Ideal.map_map]; congr 1
  rwa [Ideal.map_eq_iff_sup_ker_eq_of_surjective _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker, sup_eq_left.mpr (IsLocalRing.le_maximalIdeal hq_prime.ne_top),
    sup_comm] at key


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
theorem exists_isAdjoinRootMonic_of_quotientMap_etale
    [IsDomain R] [IsDomain S] [IsIntegrallyClosed R] [UniqueFactorizationMonoid S] [Algebra R S]
    [FaithfulSMul R S] [Module.Finite R S]
    (q : Ideal S)
    [hq_prime : q.IsPrime] (hq_height : q.height = 1)
    (hétale : (Ideal.quotientMap q (algebraMap R S) le_rfl).Etale) :
    ∃ f : R[X], Nonempty (IsAdjoinRootMonic S f) := by
  let φ := algebraMap R S
  by_cases hφ_etale : Algebra.Etale R S
  · let ⟨β, adj⟩ := exists_adjoin_eq_top (R:=R) (S:=S)
    haveI : Module.Free R S := Module.free_of_flat_of_isLocalRing
    exact ⟨minpoly R β, ⟨IsAdjoinRoot.mkOfAdjoinEqTop' adj⟩⟩
  let p : Ideal R := q.comap φ
  let R₀ := R ⧸ p; let S₀ := S ⧸ q
  let φ₀ : R₀ →+* S₀ := Ideal.quotientMap q φ (le_refl p)
  haveI : IsLocalRing R₀ := .of_surjective' _ Ideal.Quotient.mk_surjective
  haveI : IsLocalRing S₀ := .of_surjective' _ Ideal.Quotient.mk_surjective
  haveI : Module.Finite R₀ S₀ := Module.Finite.of_restrictScalars_finite R _ _
  haveI : Algebra.Etale R₀ S₀ := RingHom.etale_algebraMap.mp hétale
  obtain ⟨B₀, adj⟩ := exists_adjoin_eq_top (R:=R₀) (S:=S₀)
  let f₀ := minpoly R₀ B₀
  obtain ⟨B, hB⟩ := Ideal.Quotient.mk_surjective B₀
  obtain ⟨f₁, hf₁_map, hf₁_monic⟩ : ∃ f₁ : R[X], f₁.map (Ideal.Quotient.mk p) = f₀ ∧ f₁.Monic := by
    have h_lifts : f₀ ∈ Polynomial.lifts (Ideal.Quotient.mk p) :=
      (Polynomial.mem_lifts _).mpr
        (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective f₀)
    obtain ⟨f₁, hf₁_eq, _, hf₁_monic⟩ := Polynomial.lifts_and_degree_eq_and_monic
      h_lifts (minpoly.monic (Algebra.IsIntegral.isIntegral B₀))
    exact ⟨f₁, hf₁_eq, hf₁_monic⟩
  let mr := IsLocalRing.maximalIdeal R; let ms := IsLocalRing.maximalIdeal S
  have hq_le_ms : q ≤ ms := IsLocalRing.le_maximalIdeal hq_prime.ne_top
  have h_ms_eq : ms = q ⊔ Ideal.map φ mr := maximalIdeal_eq_sup_of_etale_quotient q hétale
  let f₁_B := Polynomial.aeval B f₁
  obtain ⟨q₀, hq₀⟩ := Ideal.exists_span_singleton_eq_of_prime_of_height_one q hq_height
  have hcomp : (Ideal.Quotient.mk q).comp (algebraMap R S) =
      φ₀.comp (Ideal.Quotient.mk p) := by
    ext r; change Ideal.Quotient.mk q (φ r) = φ₀ (Ideal.Quotient.mk p r)
    exact Ideal.quotientMap_mk.symm
  by_cases h_gen : f₁_B ∈ ms ∧ Ideal.span {f₁_B} ⊔ Ideal.map φ mr • ⊤ = ms
  · have h_adjoin_top : Algebra.adjoin R {B} = ⊤ :=
      adjoin_eq_top_of_quotient B q (by convert adj using 3)
        f₁_B (by rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨f₁, rfl⟩)
        (by simpa [Ideal.smul_eq_mul, Ideal.mul_top] using h_gen.2.symm)
    exact ⟨minpoly R B, ⟨IsAdjoinRootMonic.mkOfAdjoinEqTop
      (Algebra.IsIntegral.isIntegral (R:=R) B) h_adjoin_top⟩⟩
  · have h_f₁B_in_q : f₁_B ∈ q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      change Ideal.Quotient.mk q (Polynomial.aeval B f₁) = 0
      simp only [Polynomial.aeval_def]
      rw [Polynomial.hom_eval₂, hB, hcomp, ← Polynomial.eval₂_map, hf₁_map]
      change Polynomial.aeval B₀ f₀ = 0
      exact minpoly.aeval (A:=R₀) (B:=S₀) B₀
    obtain ⟨a, ha⟩ : ∃ a : S, f₁_B = q₀ * a := by
      rw [hq₀] at h_f₁B_in_q; exact Ideal.mem_span_singleton.mp h_f₁B_in_q
    have h_deriv_unit : f₁.derivative.aeval B ∉ ms := by
      have h_deriv_comm : Ideal.Quotient.mk q (f₁.derivative.aeval B) =
          (f₀.derivative).aeval B₀ := by
        simp only [Polynomial.aeval_def]
        rw [Polynomial.hom_eval₂, hB, hcomp, ← Polynomial.eval₂_map]
        congr 1; rw [← Polynomial.derivative_map, hf₁_map]
      intro h_in_ms
      haveI : IsLocalHom (Ideal.Quotient.mk q) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      have := fun h => (IsLocalRing.mem_maximalIdeal _).mp h_in_ms
        (isUnit_of_map_unit (Ideal.Quotient.mk q) _ h)
      rw [h_deriv_comm] at this
      exact this (isUnit_aeval_derivative_minpoly_of_adjoin_eq_top adj)
    let B' := B + q₀
    obtain ⟨b, hb⟩ : ∃ b : S, Polynomial.aeval B' f₁ =
        q₀ * (a + f₁.derivative.aeval B + q₀ * b) := by
      obtain ⟨c, hc⟩ := exists_aeval_add_eq f₁ B q₀
      exact ⟨c, by rw [hc, show (aeval B) f₁ = q₀ * a from ha]; ring⟩
    have h_cofactor_unit : IsUnit (a + f₁.derivative.aeval B + q₀ * b) := by
      have hq₀_in_ms : q₀ ∈ ms := hq_le_ms (hq₀ ▸ Ideal.mem_span_singleton_self q₀)
      have ha_in_ms : a ∈ ms := by
        by_contra ha_not_in_ms
        have ha_unit := IsLocalRing.notMem_maximalIdeal.mp ha_not_in_ms
        exact h_gen ⟨hq_le_ms h_f₁B_in_q, by
          rw [show Ideal.span {f₁_B} = q from by
            rw [show f₁_B = q₀ * a from ha, hq₀]
            exact Ideal.span_singleton_mul_right_unit ha_unit q₀]
          rw [h_ms_eq, Ideal.smul_eq_mul, Ideal.mul_top]⟩
      have h_sum_in_ms : a + q₀ * b ∈ ms :=
        Ideal.add_mem ms ha_in_ms (mul_comm q₀ b ▸ Ideal.mul_mem_left ms b hq₀_in_ms)
      rw [show a + f₁.derivative.aeval B + q₀ * b =
        f₁.derivative.aeval B + (a + q₀ * b) from by ring]
      rw [← IsLocalRing.notMem_maximalIdeal]
      exact fun h => h_deriv_unit (by convert Ideal.sub_mem ms h h_sum_in_ms using 1; ring)
    have h_span_eq : Ideal.span {Polynomial.aeval B' f₁} = q := by
      rw [hb, hq₀]; exact Ideal.span_singleton_mul_right_unit h_cofactor_unit q₀
    have hB'_lifts : Ideal.Quotient.mk q B' = B₀ := by
      change Ideal.Quotient.mk q (B + q₀) = B₀
      rw [map_add, hB, Ideal.Quotient.eq_zero_iff_mem.mpr
        (hq₀ ▸ Ideal.mem_span_singleton_self q₀)]; exact add_zero B₀
    have h_adjoin_top : Algebra.adjoin R {B'} = ⊤ :=
      adjoin_eq_top_of_quotient B' q (by convert adj using 3)
        (Polynomial.aeval B' f₁)
        (by rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨f₁, rfl⟩)
        (by rw [h_span_eq]; exact h_ms_eq)
    exact ⟨minpoly R B', ⟨IsAdjoinRootMonic.mkOfAdjoinEqTop
      (Algebra.IsIntegral.isIntegral (R:=R) B') h_adjoin_top⟩⟩

theorem exists_adjoin_eq_top_of_quotientMap_etale
    [IsDomain R] [IsDomain S] [IsIntegrallyClosed R]
    [UniqueFactorizationMonoid S]
    (φ : R →+* S) (hφ_fin : φ.Finite) (hφ_inj : Injective φ)
    (q : Ideal S)
    [hq_prime : q.IsPrime] (hq_height : q.height = 1)
    (hétale : Etale (Ideal.quotientMap q φ (le_refl (q.comap φ)))) :
    ∃(β : S), Algebra.adjoin φ.range {β} = ⊤ := by
  letI : Algebra R S := φ.toAlgebra
  have eq : φ = algebraMap R S := (algebraMap_toAlgebra φ).symm
  rw [eq] at hφ_inj; rw [eq]
  haveI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hφ_inj
  haveI : Module.Finite R S := finite_algebraMap.mp hφ_fin
  obtain ⟨f, ⟨adj_monic⟩⟩ :=
    exists_isAdjoinRootMonic_of_quotientMap_etale (R:=R) (S:=S) q hq_height hétale
  use adj_monic.root
  ext s; constructor
  · intro _; trivial
  · intro _
    have hs : s ∈ Algebra.adjoin R {adj_monic.root} := by
      rw [adj_monic.adjoin_root_eq_top]; trivial
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hs ⊢
    obtain ⟨p, hp⟩ := hs
    let p' : Polynomial φ.range := p.map (RingEquiv.ofBijective (φ.rangeRestrict)
      ⟨fun _ _ h => hφ_inj (Subtype.ext_iff.mp h), φ.rangeRestrict_surjective⟩).toRingHom
    use p'
    change Polynomial.eval₂ (algebraMap φ.range S) adj_monic.root p' = s
    rw [Polynomial.eval₂_map]; convert hp using 2

end Monogenic
