/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bianca Viray, Bryan Boehnke, Grant Yang, George Peykanu, Tianshuo Wang
-/
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Nakayama
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Monogenic Extension Generators

This file provides helper lemmas for establishing monogenic extensions, particularly for
étale extensions of local rings.

## Main results

- `gensUnivQuot_of_monogenic`: for an integral generator `β`, there is an isomorphism
  `R[X]/(minpoly R β) ≃ₐ[R] S`.
- `deriv_isUnit_of_monogenic`: for étale extensions, the derivative of the minimal polynomial
  at the generator is a unit.
- `adjoin_eq_top_of_quotient_gen`: Nakayama-based argument showing a quotient generator lifts
  to a full generator.
- `monogenic_of_finiteInjectiveEtale`: finite étale extensions of local rings are monogenic.

## References

See Lemma 3.2 of arXiv:2503.07846.
-/

open Polynomial
open Function
open RingHom

namespace Monogenic

variable {R S} [CommRing R] [CommRing S] [Algebra R S]

lemma gensUnivQuot_of_monogenic
    [Module.Finite R S] [FaithfulSMul R S] [IsDomain R] [IsDomain S] [IsIntegrallyClosed R]
    (β : S) (adjoin_top : Algebra.adjoin R {β} = ⊤) :
    Nonempty ((R[X] ⧸ Ideal.span {minpoly R β}) ≃ₐ[R] S) :=
  ⟨(IsAdjoinRootMonic.mkOfAdjoinEqTop (Algebra.IsIntegral.isIntegral β)
    adjoin_top).adjoinRootAlgEquiv⟩

/-! ### Derivative unit condition -/

variable [IsLocalRing S]

/-- The residue of `aeval β p` equals `eval₂` applied to the residues. -/
theorem residue_aeval_eq (β : S) (p : R[X]) :
    IsLocalRing.residue S (aeval β p) =
    p.eval₂ ((IsLocalRing.residue S).comp (algebraMap R S)) (IsLocalRing.residue S β) := by
  simp only [aeval_def, hom_eval₂]

lemma isUnit_of_residue_ne_zero {s : S} (h : IsLocalRing.residue S s ≠ 0) : IsUnit s :=
  IsLocalRing.notMem_maximalIdeal.mp <| mt (IsLocalRing.residue_eq_zero_iff s).mpr h

variable [IsLocalRing R] [Module.Finite R S] [FaithfulSMul R S]

/-- The residue field map from `R` to `k_S` factors as `R → k_R → k_S`. -/
lemma residue_algebraMap_eq :
    (IsLocalRing.residue S).comp (algebraMap R S) =
    (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)).comp
      (IsLocalRing.residue R) :=
  rfl

/-- For étale extensions of local rings, `comap m_S = m_R`. -/
lemma comap_maximalIdeal_eq_of_etale [Algebra.Etale R S] :
    Ideal.comap (algebraMap R S) (IsLocalRing.maximalIdeal S) = IsLocalRing.maximalIdeal R := by
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_comap] at hx
    by_contra h_not_in_mR
    exact (IsLocalRing.mem_maximalIdeal _).mp hx
      ((IsLocalRing.notMem_maximalIdeal.mp h_not_in_mR).map (algebraMap R S))
  · intro x hx
    rw [Ideal.mem_comap, ← Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S)]
    exact Ideal.mem_map_of_mem _ hx

lemma residue_generates_of_generates (β : S) (hβ_gen : Algebra.adjoin R {β} = ⊤) :
    Algebra.adjoin (IsLocalRing.ResidueField R) {IsLocalRing.residue S β} = ⊤ := by
  set kR := IsLocalRing.ResidueField R
  set kS := IsLocalRing.ResidueField S
  rw [eq_top_iff]
  intro x _
  obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective (R := S) x
  have hs : s ∈ Algebra.adjoin R {β} := hβ_gen ▸ trivial
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx]
    exact Algebra.subset_adjoin rfl
  | algebraMap r =>
    have : (IsLocalRing.residue S) (algebraMap R S r) =
        algebraMap kR kS (IsLocalRing.residue R r) := rfl
    rw [this]; exact Subalgebra.algebraMap_mem _ _
  | add _ _ _ _ hx hy =>
    simp only [map_add]
    exact Subalgebra.add_mem _ (hx trivial) (hy trivial)
  | mul _ _ _ _ hx hy =>
    simp only [map_mul]
    exact Subalgebra.mul_mem _ (hx trivial) (hy trivial)

/-- For étale extensions of local rings, finrank is preserved under residue field extension. -/
lemma finrank_eq_finrank_residueField [Algebra.Etale R S] :
    Module.finrank R S =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) := by
  haveI : Algebra.FormallySmooth R S := inferInstance
  haveI : Algebra.FinitePresentation R S := inferInstance
  haveI : Algebra.Smooth R S := ⟨inferInstance, inferInstance⟩
  haveI : Module.Flat R S := Algebra.Smooth.flat R S
  haveI : Module.Free R S := Module.free_of_flat_of_isLocalRing
  have hmaximal : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal S := Algebra.FormallyUnramified.map_maximalIdeal
  have h := IsLocalRing.finrank_quotient_map (R := R) (S := S)
  simp only [IsLocalRing.ResidueField]
  let e : (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
      ≃ₗ[R ⧸ IsLocalRing.maximalIdeal R] (S ⧸ IsLocalRing.maximalIdeal S) :=
    AddEquiv.toLinearEquiv (Ideal.quotEquivOfEq hmaximal).toAddEquiv (fun r x => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp only [RingEquiv.toAddEquiv_eq_coe]
      rfl)
  rw [← e.finrank_eq, h]

lemma minpoly_map_eq_minpoly_residue [Algebra.Etale R S]
    [IsDomain R] [IsDomain S] [IsIntegrallyClosed R]
    (β : S) (adjoin_eq_top : Algebra.adjoin R {β} = ⊤) :
    (minpoly R β).map (IsLocalRing.residue R) = minpoly (IsLocalRing.ResidueField R)
      (IsLocalRing.residue S β) := by
  set β₀ := IsLocalRing.residue S β
  set kR := IsLocalRing.ResidueField R
  have hβ_int : IsIntegral R β := Algebra.IsIntegral.isIntegral β
  have hβ₀_int : IsIntegral kR β₀ := Algebra.IsIntegral.isIntegral β₀
  have hdvd : minpoly kR β₀ ∣ (minpoly R β).map (IsLocalRing.residue R) := minpoly.dvd kR β₀ (by
    rw [aeval_def, eval₂_map, ← residue_algebraMap_eq, ← hom_eval₂, ← aeval_def, minpoly.aeval,
      map_zero])
  have hβ₀_gen : Algebra.adjoin kR {β₀} = ⊤ := residue_generates_of_generates β adjoin_eq_top
  have hβ₀_field_gen : IntermediateField.adjoin kR {β₀} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic β₀)] at hβ₀_gen
    exact IntermediateField.toSubalgebra_injective hβ₀_gen
  have hdeg_eq : ((minpoly R β).map (IsLocalRing.residue R)).natDegree =
      (minpoly kR β₀).natDegree := by
    rw [(minpoly.monic hβ_int).natDegree_map _,
      ← (IsAdjoinRootMonic.mkOfAdjoinEqTop hβ_int adjoin_eq_top).finrank,
      finrank_eq_finrank_residueField, ← IntermediateField.finrank_top', ← hβ₀_field_gen,
      IntermediateField.adjoin.finrank hβ₀_int]
  exact eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hβ₀_int)
    ((minpoly.monic hβ_int).map _) hdvd hdeg_eq.le

lemma derivative_isUnit_of_monogenic [Algebra.Etale R S] [IsDomain R] [IsDomain S]
    [IsIntegrallyClosed R] (β : S) (adjoin_eq_top : Algebra.adjoin R {β} = ⊤) :
    IsUnit (aeval β (minpoly R β).derivative) := by
  set β₀ := IsLocalRing.residue S β
  set kR := IsLocalRing.ResidueField R
  apply isUnit_of_residue_ne_zero
  have hderiv_ne_zero : aeval β₀ (minpoly kR β₀).derivative ≠ 0 :=
    (Algebra.IsSeparable.isSeparable kR β₀).aeval_derivative_ne_zero (minpoly.aeval kR β₀)
  rw [residue_aeval_eq, residue_algebraMap_eq, ← eval₂_map, ← derivative_map,
    minpoly_map_eq_minpoly_residue β adjoin_eq_top, ← aeval_def]
  exact hderiv_ne_zero

/-! ### Nakayama helpers -/

omit [IsLocalRing S] [IsLocalRing R] [Module.Finite R S] [FaithfulSMul R S] in
/-- If `β` generates `S/q` over `R/p`, every element of `S` is congruent to an element of
`Algebra.adjoin R {β}` modulo `q`. -/
lemma exists_adjoin_sub_mem
    (β : S) (q : Ideal S)
    (h_gen : Algebra.adjoin (R ⧸ q.comap (algebraMap R S))
      {Ideal.Quotient.mk q β} = ⊤) (s : S) :
    ∃ t ∈ Algebra.adjoin R {β}, s - t ∈ q := by
  let p := q.comap (algebraMap R S)
  let R₀ := R ⧸ p
  let S₀ := S ⧸ q
  let β₀ := Ideal.Quotient.mk q β
  have hs₀ : Ideal.Quotient.mk q s ∈ Algebra.adjoin R₀ {β₀} := by
    rw [h_gen]; trivial
  obtain ⟨t, ht_mem, ht_eq⟩ : ∃ t ∈ Algebra.adjoin R {β},
      Ideal.Quotient.mk q s = Ideal.Quotient.mk q t := by
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hs₀
    · intro x hx
      simp only [Set.mem_singleton_iff] at hx
      exact ⟨β, Algebra.subset_adjoin (Set.mem_singleton _), by rw [hx]⟩
    · intro r
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      exact ⟨algebraMap R S r, Subalgebra.algebraMap_mem _ _,
        (Ideal.quotientMap_mk (I := q) (f := algebraMap R S) (H := le_rfl)).symm⟩
    · rintro x y _ _ ⟨t₀, ht₀, rfl⟩ ⟨t₁, ht₁, rfl⟩
      exact ⟨t₀ + t₁, Subalgebra.add_mem _ ht₀ ht₁, by simp [map_add]⟩
    · rintro x y _ _ ⟨t₀, ht₀, rfl⟩ ⟨t₁, ht₁, rfl⟩
      exact ⟨t₀ * t₁, Subalgebra.mul_mem _ ht₀ ht₁, by simp [map_mul]⟩
  exact ⟨t, ht_mem, Ideal.Quotient.eq.mp ht_eq⟩

omit [IsLocalRing S] [IsLocalRing R] [Module.Finite R S] [FaithfulSMul R S] in
/-- If `β` generates `S/q` over `R/p` and `m_S = ⟨π⟩ ⊔ m_R·S` with `π ∈ Algebra.adjoin R {β}`,
then `Algebra.adjoin R {β} = ⊤`. -/
lemma adjoin_eq_top_of_quotient_gen
    [IsLocalRing R] [IsLocalRing S] [Module.Finite R S]
    (β : S) (q : Ideal S) [q.IsPrime]
    (h_gen : Algebra.adjoin (R ⧸ q.comap (algebraMap R S))
      {Ideal.Quotient.mk q β} = ⊤)
    (π : S) (hπ_mem : π ∈ Algebra.adjoin R {β})
    (h_ms : IsLocalRing.maximalIdeal S =
      Ideal.span {π} ⊔ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) :
    Algebra.adjoin R {β} = ⊤ := by
  set A := Algebra.adjoin R {β}
  set mR := IsLocalRing.maximalIdeal R
  set ms := IsLocalRing.maximalIdeal S with ms_def
  set mR_S := Ideal.map (algebraMap R S) mR
  haveI : IsArtinianRing (S ⧸ mR_S) := by
    letI : Field (R ⧸ mR) := Ideal.Quotient.field mR
    haveI : IsArtinianRing (R ⧸ mR) := DivisionRing.instIsArtinianRing
    haveI : Module.Finite (R ⧸ mR) (S ⧸ mR_S) :=
      Module.Finite.of_restrictScalars_finite R (R ⧸ mR) (S ⧸ mR_S)
    exact IsArtinianRing.of_finite (R ⧸ mR) (S ⧸ mR_S)
  obtain ⟨n, hn⟩ := IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient mR_S
  have h_lift : ∀ s : S, ∃ t ∈ A, s - t ∈ q :=
    exists_adjoin_sub_mem β q h_gen
  have hπ_ms : π ∈ ms :=
    h_ms ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self π)
  have hq_le_ms : q ≤ ms := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)
  have h_ms_pow : ∀ k : ℕ, ms ^ k ≤ Ideal.span {π ^ k} ⊔ mR_S := by
    intro k
    induction k with
    | zero => simp [Ideal.span_singleton_one]
    | succ k ih =>
      intro x hx
      rw [pow_succ] at hx
      refine Submodule.smul_induction_on hx (fun a ha b hb => ?_) (fun _ _ hx hy => ?_)
      · obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Submodule.mem_sup.mp (ih ha)
        obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Submodule.mem_sup.mp (h_ms ▸ hb)
        obtain ⟨ca, rfl⟩ := Ideal.mem_span_singleton.mp ha₁
        obtain ⟨cb, rfl⟩ := Ideal.mem_span_singleton.mp hb₁
        have h1 : π ^ k * ca * (π * cb) ∈ Ideal.span {π ^ (k + 1)} :=
          Ideal.mem_span_singleton.mpr ⟨ca * cb, by ring⟩
        have h_rest : π ^ k * ca * b₂ + a₂ * (π * cb) + a₂ * b₂ ∈ mR_S :=
          Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ hb₂)
            (Ideal.mul_mem_right _ _ ha₂)) (Ideal.mul_mem_left _ _ hb₂)
        change (π ^ k * ca + a₂) • (π * cb + b₂) ∈ _
        have : (π ^ k * ca + a₂) • (π * cb + b₂) =
            π ^ k * ca * (π * cb) + (π ^ k * ca * b₂ + a₂ * (π * cb) + a₂ * b₂) := by
          simp only [smul_eq_mul]; ring
        rw [this]
        exact Submodule.add_mem_sup h1 h_rest
      · exact Ideal.add_mem _ hx hy
  have h_iterate : ∀ (k : ℕ) (x : S), x ∈ q →
      ∃ a ∈ A.toSubmodule, x - a ∈ (Ideal.span {π ^ k} ⊔ mR_S : Ideal S) := by
    intro k
    induction k with
    | zero =>
      intro x _
      exact ⟨0, Subalgebra.zero_mem A, by simp [Ideal.span_singleton_one]⟩
    | succ k ih =>
      intro x hx
      obtain ⟨a₀, ha₀, hz⟩ := ih x hx
      obtain ⟨y, hy, r, hr, hzyr⟩ := Submodule.mem_sup.mp hz
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hy
      obtain ⟨a₁, ha₁, hc⟩ := h_lift c
      have hπk_A : π ^ k ∈ A := Subalgebra.pow_mem A hπ_mem k
      have ha' : a₀ + a₁ * π ^ k ∈ A :=
        Subalgebra.add_mem A ha₀ (Subalgebra.mul_mem A ha₁ hπk_A)
      refine ⟨a₀ + a₁ * π ^ k, ha', ?_⟩
      have hcma₁_ms : c - a₁ ∈ ms := hq_le_ms hc
      have hπk_cma₁ : π ^ k * (c - a₁) ∈ ms ^ (k + 1) := by
        rw [pow_succ]
        exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hπ_ms k) hcma₁_ms
      have h_eq : x - (a₀ + a₁ * π ^ k) = π ^ k * (c - a₁) + r := by
        have h1 : x - a₀ = π ^ k * c + r := hzyr.symm
        calc x - (a₀ + a₁ * π ^ k)
            = (x - a₀) - a₁ * π ^ k := by ring
          _ = (π ^ k * c + r) - a₁ * π ^ k := by rw [h1]
          _ = π ^ k * (c - a₁) + r := by ring
      rw [h_eq]
      exact Ideal.add_mem _ (h_ms_pow (k + 1) hπk_cma₁) (Ideal.mem_sup_right hr)
  have h_πn_le : Ideal.span {π ^ n} ⊔ mR_S ≤ mR_S :=
    sup_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hn (Ideal.pow_mem_pow hπ_ms n))))
      le_rfl
  have h_q_le : (q.restrictScalars R : Submodule R S) ≤ A.toSubmodule ⊔ mR • ⊤ := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := h_iterate n x hx
    rw [Ideal.smul_top_eq_map]
    exact Submodule.mem_sup.mpr ⟨a, ha, x - a,
      show x - a ∈ mR_S.restrictScalars R from h_πn_le hxa, by ring⟩
  have h_le_sup : (⊤ : Submodule R S) ≤ A.toSubmodule ⊔ mR • ⊤ := by
    intro s _
    obtain ⟨t, ht, hst⟩ := h_lift s
    have h_diff := h_q_le (show s - t ∈ q.restrictScalars R from hst)
    exact (show s = t + (s - t) by ring) ▸
      Submodule.add_mem _ (Submodule.mem_sup_left ht) h_diff
  have h_fg : (⊤ : Submodule R S).FG := Module.finite_def.mp inferInstance
  have h_jac : mR ≤ Ideal.jacobson ⊥ := IsLocalRing.maximalIdeal_le_jacobson ⊥
  exact eq_top_iff.mpr (Submodule.le_of_le_smul_of_le_jacobson_bot h_fg h_jac h_le_sup)

lemma monogenic_of_finiteInjectiveEtale [Algebra.Etale R S] :
    ∃(β : S), Algebra.adjoin R {β} = ⊤ := by
  have eq_max : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal S :=
    Algebra.FormallyUnramified.map_maximalIdeal
  obtain ⟨β₀, hβ₀⟩ := Field.exists_primitive_element (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField S)
  obtain ⟨β, hβ⟩ := Ideal.Quotient.mk_surjective β₀
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  let S' := Algebra.adjoin R {β}
  have adjoin_eq_top : S' = ⊤ := by
    have h_alg_β₀ : IsAlgebraic (IsLocalRing.ResidueField R) β₀ :=
      Algebra.IsAlgebraic.isAlgebraic β₀
    have h_subalg := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic h_alg_β₀
    have h_adjoin_top : Algebra.adjoin (IsLocalRing.ResidueField R) {β₀} = ⊤ := by
      rw [← h_subalg, hβ₀, IntermediateField.top_toSubalgebra]
    let mR := IsLocalRing.maximalIdeal R
    have h_mS : mR • (⊤ : Submodule R S) = (IsLocalRing.maximalIdeal S).restrictScalars R := by
      rw [Ideal.smul_top_eq_map, Algebra.FormallyUnramified.map_maximalIdeal]
    let mS := IsLocalRing.maximalIdeal S
    have h_adjoin_top' : Algebra.adjoin (R ⧸ Ideal.comap (algebraMap R S) mS)
        {(Ideal.Quotient.mk mS) β} = ⊤ := by
      have h_comap_eq : Ideal.comap (algebraMap R S) mS = mR := comap_maximalIdeal_eq_of_etale
      rw [eq_top_iff]
      intro x _
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hs₀ : IsLocalRing.residue S s ∈ Algebra.adjoin (IsLocalRing.ResidueField R)
          {IsLocalRing.residue S β} := by
        have : IsLocalRing.residue S β = β₀ := hβ
        rw [this, h_adjoin_top]; trivial
      refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hs₀
      · intro y hy
        simp only [Set.mem_singleton_iff] at hy
        subst hy
        exact Algebra.subset_adjoin rfl
      · intro r
        obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective r
        have : (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
            (Ideal.Quotient.mk mR r') =
            (algebraMap (R ⧸ Ideal.comap (algebraMap R S) mS) (S ⧸ mS))
            (Ideal.Quotient.mk (Ideal.comap (algebraMap R S) mS) r') := by
          simp only [Algebra.algebraMap_eq_smul_one]
          rfl
        rw [this]
        exact Subalgebra.algebraMap_mem _ _
      · intro _ _ _ _ hx hy
        exact Subalgebra.add_mem _ hx hy
      · intro _ _ _ _ hx hy
        exact Subalgebra.mul_mem _ hx hy
    have h_ms_eq : mS = Ideal.span {(0 : S)} ⊔ Ideal.map (algebraMap R S) mR := by
      simp only [Ideal.span_singleton_zero, bot_sup_eq]
      exact eq_max.symm
    haveI : mS.IsPrime := Ideal.IsMaximal.isPrime inferInstance
    exact adjoin_eq_top_of_quotient_gen β mS h_adjoin_top' 0 (Subalgebra.zero_mem _) h_ms_eq
  exact ⟨β, adjoin_eq_top⟩

end Monogenic
