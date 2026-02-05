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

open Polynomial
open Function
open RingHom
namespace Monogenic

variable {R S} [CommRing R] [CommRing S] [Algebra R S]

/-- Let `R -> S` be a finite extension of integral domains.
    Suppose there exists `β ∈ S` such that `S = R[β]`.
    If `R` is integrally closed, then there exists a polynomial `f ∈ R[x]` such that
    `R[x]/f` and `S` are isomorphic as `R`-algebras.
-/
-- Note: We add [IsDomain R], [IsIntegrallyClosed R], and [IsDomain S] hypotheses.
-- The [IsDomain R] and [IsIntegrallyClosed R] are needed for the minimal polynomial
-- to have the divisibility property (minpoly.isIntegrallyClosed_dvd).
-- [IsDomain S] follows naturally for étale extensions of domains.
-- We also add étale hypothesis to prove the derivative is a unit via separability.
lemma gensUnivQuot_of_monogenic
  [Module.Finite R S] [FaithfulSMul R S]
  [IsDomain R] [IsDomain S] [IsIntegrallyClosed R]
  (β : S)
  (adjoin_top : Algebra.adjoin R {β} = ⊤) :
    Nonempty ((R[X] ⧸ Ideal.span {minpoly R β}) ≃ₐ[R] S) := by
  have hβ_int : IsIntegral R β := Algebra.IsIntegral.isIntegral β
  have adjoin := IsAdjoinRootMonic.mkOfAdjoinEqTop hβ_int adjoin_top
  exact ⟨adjoin.adjoinRootAlgEquiv⟩

/-!
## Helper lemmas for the derivative unit condition

A key fact from Lemma 3.2 of arXiv:2503.07846 is that for a finite étale extension of local rings,
the derivative of the minimal polynomial evaluated at the generator is a unit.

The proof proceeds through the residue fields:
1. Since `R -> S` is étale, the residue field extension `R / m_R → S / m_S` is separable
2. For separable extensions, the minimal polynomial is separable.
3. Separable polynomial ⟹ derivative at root is non-zero
4. Non-zero in residue field ⟹ unit in local ring
-/

-- For a local ring `S`, we denote its maximal ideal by `m_S`.
variable [IsLocalRing S]

/-- Given a polynomial `p ∈ R[x]` and `β ∈ S`,
    `p(β) mod m_S = (p mod m_S)(β mod m_S)` -/
theorem residue_aeval_eq (β : S) (p : R[X]) :
    IsLocalRing.residue S (aeval β p) =
    p.eval₂ ((IsLocalRing.residue S).comp (algebraMap R S)) (IsLocalRing.residue S β) := by
  simp only [aeval_def, hom_eval₂]


/-- In a local ring `S`, an element is a unit iff its image in `S/m_S` is non-zero. -/
lemma isUnit_of_residue_ne_zero {s : S} (h : IsLocalRing.residue S s ≠ 0) : IsUnit s := by
  rw [ne_eq, IsLocalRing.residue_eq_zero_iff] at h
  exact IsLocalRing.notMem_maximalIdeal.mp h

variable [IsLocalRing R] [Module.Finite R S] [FaithfulSMul R S]

/-- The square
      S -> S/m_S
      ↑      ↑
      R -> R/m_R
    commutes. -/
lemma residue_algebraMap_eq :
    (IsLocalRing.residue S).comp (algebraMap R S) =
    (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)).comp
      (IsLocalRing.residue R) :=
  rfl

/-- When `β` generates `S` over `R`, the residue `β₀ = β mod m_S`
     generates `S / m_S` over `R / m_R.` -/
lemma residue_generates_of_generates
    (β : S) (hβ_gen : Algebra.adjoin R {β} = ⊤) :
    Algebra.adjoin (IsLocalRing.ResidueField R) {IsLocalRing.residue S β} = ⊤ := by
  let kR := IsLocalRing.ResidueField R
  let kS := IsLocalRing.ResidueField S
  let β₀ : kS := IsLocalRing.residue S β
  -- The residue map is surjective and respects the algebra structure
  -- Algebra.adjoin R {β} = ⊤ maps onto Algebra.adjoin k_R {β₀} = k_S
  rw [eq_top_iff]
  intro x _
  obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective (R := S) x
  have hs : s ∈ Algebra.adjoin R {β} := by rw [hβ_gen]; trivial
  -- s is in the adjoin of β over R, so residue(s) is in the adjoin of β₀ over k_R
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    simp only [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Algebra.subset_adjoin (Set.mem_singleton _)
  | algebraMap r =>
    -- (residue S) (algebraMap R S r) = algebraMap kR kS (residue R r)
    -- which is in any subalgebra
    have : (IsLocalRing.residue S) (algebraMap R S r)
        = algebraMap kR kS (IsLocalRing.residue R r) := by
      rw [← RingHom.comp_apply, ← RingHom.comp_apply]
      rfl
    rw [this]
    exact Subalgebra.algebraMap_mem (Algebra.adjoin kR {β₀}) _
  | add x y _ _ hx hy =>
    simp only [map_add]
    exact Subalgebra.add_mem _ (hx trivial) (hy trivial)
  | mul x y _ _ hx hy =>
    simp only [map_mul]
    exact Subalgebra.mul_mem _ (hx trivial) (hy trivial)

/-- For finite étale extensions of local rings, `rank_R S = rank_{R/m_R} S/m_S`.
-- Q: Is this in the right level of generality?
    The proof uses:
    1. Étale ⟹ Smooth ⟹ Flat
    2. Finite + Flat over local ring ⟹ Free
    3. m_R · S = m_S (étale condition) gives S / (m_R · S) = kS
    4. finrank_quotient_map: finrank kR (S / m_R·S) = finrank R S
-/
lemma finrank_eq_finrank_residueField [Algebra.Etale R S] :
    Module.finrank R S =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) := by
  -- Étale implies FormallySmooth and FinitePresentation, hence Smooth
  haveI : Algebra.FormallySmooth R S := inferInstance
  haveI : Algebra.FinitePresentation R S := inferInstance
  haveI : Algebra.Smooth R S := ⟨inferInstance, inferInstance⟩
  haveI : Module.Flat R S := Algebra.Smooth.flat R S
  -- Finite + Flat over local ring ⟹ Free
  haveI : Module.Free R S := Module.free_of_flat_of_isLocalRing
  -- For étale: m_R · S = m_S
  have hmaximal : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal S := Algebra.FormallyUnramified.map_maximalIdeal
  -- finrank_quotient_map gives: finrank (R ⧸ m_R) (S ⧸ Ideal.map m_R) = finrank R S
  -- ResidueField S = S ⧸ maximalIdeal S, and hmaximal says Ideal.map m_R = m_S
  -- Use Eq.rec to transport along hmaximal
  have h := IsLocalRing.finrank_quotient_map (R := R) (S := S)
  -- h : finrank (R ⧸ mR) (S ⧸ Ideal.map mR) = finrank R S
  -- We need: finrank R S = finrank kR kS
  -- where kR = R ⧸ mR = ResidueField R, kS = S ⧸ mS = ResidueField S
  -- hmaximal gives: Ideal.map mR = mS, so S ⧸ Ideal.map mR ≃ₗ S ⧸ mS = kS
  -- ResidueField R = R ⧸ maximalIdeal R and ResidueField S = S ⧸ maximalIdeal S by definition
  simp only [IsLocalRing.ResidueField]
  -- Use the linear equivalence from quotEquivOfEq to transfer finrank
  let e : (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
      ≃ₗ[R ⧸ IsLocalRing.maximalIdeal R] (S ⧸ IsLocalRing.maximalIdeal S) :=
    AddEquiv.toLinearEquiv (Ideal.quotEquivOfEq hmaximal).toAddEquiv (fun r x => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      -- Goal: quotEquivOfEq(mk(algebraMap r * x)) = mk(r) • quotEquivOfEq(mk(x))
      -- LHS: quotEquivOfEq(mk(algebraMap r * x)) = mk(algebraMap r * x) (in S ⧸ mS)
      -- RHS: mk(r) • mk(x) = mk(algebraMap r * x) (in S ⧸ mS)
      simp only [RingEquiv.toAddEquiv_eq_coe]
      rfl)
  rw [← e.finrank_eq, h]

/-- Let `β ∈ S`, and let `f ∈ R[x]` be the minimal polynomial for `β` over `R`.
    Then `f mod m_S` is the minimal polynomial for `β mod m_S`.
    The proof uses the degree equality: since minpoly kR β₀ | f_bar, both are monic, and we
    show they have the same degree, hence they're equal.
-/
lemma minpoly_map_eq_minpoly_residue [Algebra.Etale R S]
    [IsDomain R] [IsDomain S] [IsIntegrallyClosed R]
    (β : S) (adjoin_eq_top : Algebra.adjoin R {β} = ⊤) :
    (minpoly R β).map (IsLocalRing.residue R) = minpoly (IsLocalRing.ResidueField R)
      (IsLocalRing.residue S β) := by
  let hβ_int : IsIntegral R β := Algebra.IsIntegral.isIntegral β
  let kR := IsLocalRing.ResidueField R
  let kS := IsLocalRing.ResidueField S
  let β₀ := IsLocalRing.residue S β
  let f := minpoly R β
  let f_bar := f.map (IsLocalRing.residue R)
  -- f_bar is monic
  have hf_monic : f.Monic := minpoly.monic hβ_int
  have hf_bar_monic : f_bar.Monic := hf_monic.map (IsLocalRing.residue R)
  -- β₀ is integral (finite extension)
  haveI : Module.Finite kR kS := inferInstance
  haveI : Algebra.IsIntegral kR kS := Algebra.IsIntegral.of_finite kR kS
  have hβ₀_int : IsIntegral kR β₀ := Algebra.IsIntegral.isIntegral β₀
  -- β₀ is a root of f_bar, so minpoly kR β₀ divides f_bar
  have hdvd : minpoly kR β₀ ∣ f_bar := minpoly.dvd kR β₀ (by
    rw [aeval_def, eval₂_map, ← residue_algebraMap_eq, ← hom_eval₂, ← aeval_def, minpoly.aeval,
      map_zero])
  have hβ₀_gen : Algebra.adjoin kR {β₀} = ⊤ := residue_generates_of_generates β adjoin_eq_top
  -- Degree chain: natDegree f_bar = natDegree f = finrank R S
  --             = finrank kR kS = natDegree (minpoly kR β₀)
  have hβ₀_field_gen : IntermediateField.adjoin kR {β₀} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic β₀)] at hβ₀_gen
    exact IntermediateField.toSubalgebra_injective hβ₀_gen
  have hdeg_eq : f_bar.natDegree = (minpoly kR β₀).natDegree := by
    rw [show f_bar.natDegree = f.natDegree from hf_monic.natDegree_map _,
      ← (IsAdjoinRootMonic.mkOfAdjoinEqTop hβ_int adjoin_eq_top).finrank,
      finrank_eq_finrank_residueField, ← IntermediateField.finrank_top', ← hβ₀_field_gen,
      IntermediateField.adjoin.finrank hβ₀_int]
  -- Both monic, same degree, divisibility ⟹ equal
  exact eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hβ₀_int) hf_bar_monic
    hdvd hdeg_eq.le

/-- A key technical fact: if `R -> S` is étale and `R[β] = S`,
      then `f'(β) is a unit in S`.

    The proof uses:
    1. (minpoly R β).map(residue) = minpoly kR β₀ (degree equality from generation)
    2. Separability gives aeval β₀ (minpoly kR β₀).derivative ≠ 0
    3. Therefore aeval β (minpoly R β).derivative ∉ m_S, hence is a unit
-/
lemma deriv_isUnit_of_monogenic [Algebra.Etale R S] [IsDomain R] [IsDomain S]
    [IsIntegrallyClosed R]
    (β : S)
    (adjoin_eq_top : Algebra.adjoin R {β} = ⊤) :
    IsUnit (aeval β (minpoly R β).derivative) := by
  -- Strategy: show residue of (aeval β f') is non-zero, hence aeval β f' is a unit
  apply isUnit_of_residue_ne_zero
  let kR := IsLocalRing.ResidueField R
  let kS := IsLocalRing.ResidueField S
  let β₀ := IsLocalRing.residue S β
  -- The residue field extension is separable (from étale)
  haveI : Algebra.IsSeparable kR kS := inferInstance
  -- β₀ is integral over k_R (since k_S is finite over k_R)
  haveI : Module.Finite kR kS := inferInstance
  haveI : Algebra.IsIntegral kR kS := Algebra.IsIntegral.of_finite kR kS
  have hβ₀_int : IsIntegral kR β₀ := Algebra.IsIntegral.isIntegral β₀
  -- β₀ is separable, so its minimal polynomial is separable
  have hβ₀_sep : (minpoly kR β₀).Separable := Algebra.IsSeparable.isSeparable kR β₀
  -- Therefore, derivative of minpoly at β₀ is non-zero
  have hderiv_ne_zero : aeval β₀ (minpoly kR β₀).derivative ≠ 0 :=
    hβ₀_sep.aeval_derivative_ne_zero (minpoly.aeval kR β₀)
  -- The key fact: (minpoly R β).map(residue R) = minpoly kR β₀
  have hminpoly_eq : (minpoly R β).map (IsLocalRing.residue R) = minpoly kR β₀ :=
    minpoly_map_eq_minpoly_residue β adjoin_eq_top
  -- Now connect the derivatives
  rw [residue_aeval_eq, residue_algebraMap_eq, ← eval₂_map, ← derivative_map, hminpoly_eq,
    ← aeval_def]
  exact hderiv_ne_zero

/-!
## Nakayama helpers for the quotient-lifting argument

These lemmas support the proof that `Algebra.adjoin R {β} = ⊤` when β generates
the quotient `S/q` over `R/(q ∩ R)`, and a suitable element π ∈ Algebra.adjoin R {β}
generates the maximal ideal modulo `mR · S`.
-/

omit [IsLocalRing S] [IsLocalRing R] [Module.Finite R S] [FaithfulSMul R S] in
/-- Let `ϕ : R → S` be a ring map. Given an ideal `q` in `S`, let `p = ϕ^{-1} q`.
    If `R/p [β] = S/q`, then every element of `S` is congruent to an element of `R[β]` mod `q`. -/
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
  -- Induct on membership in Algebra.adjoin R₀ {β₀}
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
/-- Nakayama argument: if `R/p[β] = S/q`, and `mS = π S + m_R · S` for some `π ∈ R[β]`,
    then `R[β] = S`.

    The proof combines:
    1. Quotient lifting: S = A + q (from `h_gen`)
    2. Artinian descent: ms^n ⊆ mR·S for some n
    3. Iterative reduction: q ⊆ A + mR·S (using π ∈ A and ms = ⟨π⟩ + mR·S)
    4. Nakayama's lemma: S ⊆ A + mR·S implies A = S -/
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
  -- Step 1: Show ms^n ≤ mR_S for some n, via Artinian quotient
  -- S ⧸ mR_S is a finite module over the field R ⧸ mR, hence Artinian
  haveI : IsArtinianRing (S ⧸ mR_S) := by
    letI : Field (R ⧸ mR) := Ideal.Quotient.field mR
    haveI : IsArtinianRing (R ⧸ mR) := DivisionRing.instIsArtinianRing
    haveI : Module.Finite (R ⧸ mR) (S ⧸ mR_S) :=
      Module.Finite.of_restrictScalars_finite R (R ⧸ mR) (S ⧸ mR_S)
    exact IsArtinianRing.of_finite (R ⧸ mR) (S ⧸ mR_S)
  obtain ⟨n, hn⟩ := IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient mR_S
  -- Step 2: Quotient lifting - every s ∈ S is in A + q
  have h_lift : ∀ s : S, ∃ t ∈ A, s - t ∈ q :=
    exists_adjoin_sub_mem β q h_gen
  -- Step 3: Key structural fact - ms^k ≤ Ideal.span {π ^ k} ⊔ mR_S
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
      · -- a ∈ ms^k ≤ ⟨π^k⟩ ⊔ mR_S, b ∈ ms = ⟨π⟩ ⊔ mR_S
        obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Submodule.mem_sup.mp (ih ha)
        obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Submodule.mem_sup.mp (h_ms ▸ hb)
        obtain ⟨ca, rfl⟩ := Ideal.mem_span_singleton.mp ha₁
        obtain ⟨cb, rfl⟩ := Ideal.mem_span_singleton.mp hb₁
        -- (π^k * ca + a₂) • (π * cb + b₂) lands in ⟨π^(k+1)⟩ ⊔ mR_S
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
  -- Step 4: For x ∈ q, iterate to show x ∈ A + mR_S
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
      -- Decompose x - a₀ ∈ ⟨π^k⟩ ⊔ mR_S as π^k * c + r
      obtain ⟨y, hy, r, hr, hzyr⟩ := Submodule.mem_sup.mp hz
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hy
      -- c = a₁ + (c - a₁), with c - a₁ ∈ q
      obtain ⟨a₁, ha₁, hc⟩ := h_lift c
      have hπk_A : π ^ k ∈ A := Subalgebra.pow_mem A hπ_mem k
      have ha' : a₀ + a₁ * π ^ k ∈ A :=
        Subalgebra.add_mem A ha₀ (Subalgebra.mul_mem A ha₁ hπk_A)
      refine ⟨a₀ + a₁ * π ^ k, ha', ?_⟩
      have hcma₁_ms : c - a₁ ∈ ms := hq_le_ms hc
      -- π^k * (c - a₁) ∈ ms^k * ms = ms^(k+1)
      have hπk_cma₁ : π ^ k * (c - a₁) ∈ ms ^ (k + 1) := by
        rw [pow_succ]
        exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hπ_ms k) hcma₁_ms
      -- x - (a₀ + a₁ * π^k) = π^k * (c - a₁) + r
      have h_eq : x - (a₀ + a₁ * π ^ k) = π ^ k * (c - a₁) + r := by
        have h1 : x - a₀ = π ^ k * c + r := hzyr.symm
        calc x - (a₀ + a₁ * π ^ k)
            = (x - a₀) - a₁ * π ^ k := by ring
          _ = (π ^ k * c + r) - a₁ * π ^ k := by rw [h1]
          _ = π ^ k * (c - a₁) + r := by ring
      rw [h_eq]
      exact Ideal.add_mem _ (h_ms_pow (k + 1) hπk_cma₁) (Ideal.mem_sup_right hr)
  -- Step 5: At k = n, ⟨π^n⟩ + mR_S ≤ mR_S (since π^n ∈ ms^n ⊆ mR_S)
  have h_πn_le : Ideal.span {π ^ n} ⊔ mR_S ≤ mR_S :=
    sup_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hn (Ideal.pow_mem_pow hπ_ms n))))
      le_rfl
  have h_q_le : (q.restrictScalars R : Submodule R S) ≤ A.toSubmodule ⊔ mR • ⊤ := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := h_iterate n x hx
    rw [Ideal.smul_top_eq_map]
    exact Submodule.mem_sup.mpr ⟨a, ha, x - a,
      show x - a ∈ mR_S.restrictScalars R from h_πn_le hxa, by ring⟩
  -- Step 6: Combine to get ⊤ ≤ A.toSubmodule ⊔ mR • ⊤
  have h_le_sup : (⊤ : Submodule R S) ≤ A.toSubmodule ⊔ mR • ⊤ := by
    intro s _
    obtain ⟨t, ht, hst⟩ := h_lift s
    have h_diff := h_q_le (show s - t ∈ q.restrictScalars R from hst)
    exact (show s = t + (s - t) by ring) ▸
      Submodule.add_mem _ (Submodule.mem_sup_left ht) h_diff
  -- Step 7: Apply Nakayama's lemma
  have h_fg : (⊤ : Submodule R S).FG := Module.finite_def.mp inferInstance
  have h_jac : mR ≤ Ideal.jacobson ⊥ := IsLocalRing.maximalIdeal_le_jacobson ⊥
  exact eq_top_iff.mpr (Submodule.le_of_le_smul_of_le_jacobson_bot h_fg h_jac h_le_sup)

/-
initial part without the integral domain hypothesis.
for the statement about the isomorphism with the quotient ring,
see isIntegrallyClosed_existsPolyQuotIso below
(idk, cant come up with a name. i think these new names are roughly
mathlib convention? i tried.)

see FaithfulSMul.iff_algebraMapInjective below for a proof its equivalent
to asserting that phi is injective.
-/
theorem monogenic_of_finiteInjectiveEtale [Algebra.Etale R S] :
    ∃(β : S), Algebra.adjoin R {β} = ⊤ := by
  -- Key: maximal ideal maps to maximal ideal (from Mathlib's unramified local ring theory)
  have eq_max : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal S :=
    Algebra.FormallyUnramified.map_maximalIdeal
  -- Primitive element theorem: ∃ β₀ such that k_R⟮β₀⟯ = k_S
  obtain ⟨β₀, hβ₀⟩ := Field.exists_primitive_element (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField S)
  -- Lift β₀ to β in S via the quotient map
  obtain ⟨β, hβ⟩ := Ideal.Quotient.mk_surjective β₀
  -- φ finite implies S is integral over R
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  -- The key claim: Algebra.adjoin R {β} = ⊤
  -- This follows from Nakayama's lemma: since the image of adjoin R {β} in S/m_S
  -- equals k_R⟮β₀⟯ = k_S (by primitive element theorem and the lift), and S is
  -- finitely generated over R, we get adjoin R {β} = S.
  let S' := Algebra.adjoin R {β}
  have adjoin_eq_top : S' = ⊤ := by
    -- The intermediate field k_R⟮β₀⟯ = ⊤ means β₀ generates k_S over k_R
    -- Since β₀ is algebraic (k_S is finite over k_R), the subalgebra equals the intermediate field
    have h_alg_β₀ : IsAlgebraic (IsLocalRing.ResidueField R) β₀ :=
      Algebra.IsAlgebraic.isAlgebraic β₀
    -- Use the fact that IntermediateField.adjoin K {α} has
    -- toSubalgebra = Algebra.adjoin K {α} when α is algebraic
    have h_subalg := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic h_alg_β₀
    -- Now k_R⟮β₀⟯ = ⊤ implies Algebra.adjoin k_R {β₀} = ⊤
    have h_adjoin_top : Algebra.adjoin (IsLocalRing.ResidueField R) {β₀} = ⊤ := by
      rw [← h_subalg, hβ₀, IntermediateField.top_toSubalgebra]
    let mR := IsLocalRing.maximalIdeal R
    have h_mS : mR • (⊤ : Submodule R S) = (IsLocalRing.maximalIdeal S).restrictScalars R := by
      rw [Ideal.smul_top_eq_map, Algebra.FormallyUnramified.map_maximalIdeal]
    -- Parameters for le_of_le_smul_of_le_jacobson_bot
    have h_fg : (⊤ : Submodule R S).FG := Module.finite_def.mp inferInstance
    have h_jac : mR ≤ Ideal.jacobson ⊥ := IsLocalRing.maximalIdeal_le_jacobson ⊥
    -- S ⊆ S' + mR • S
    have h_le_sup : (⊤ : Submodule R S) ≤ S'.toSubmodule ⊔ mR • ⊤ := by
      -- Prove every s is in the sup by lifting from the residue field...
      intro s _
      -- 1. Identify s₀ in the residue field k_S
      let s₀ := IsLocalRing.residue S s
      -- 2. Use the fact that k_R⟮β₀⟯ = ⊤ implies Algebra.adjoin kR {β₀} = ⊤
      -- (Since the extension is finite, the intermediate field is the subalgebra)
      have hs₀ : s₀ ∈ Algebra.adjoin (IsLocalRing.ResidueField R) {β₀} := by
        rw [h_adjoin_top]; trivial
      -- aristotle proof:
      simp +zetaDelta only [IntermediateField.adjoin_eq_top_iff,
        IntermediateField.adjoin_toSubalgebra, Ideal.smul_top_eq_map, Submodule.restrictScalars_inj,
        Submodule.mem_top] at *;
      -- Since $s₀$ is in the adjoin of $\beta₀$ over the residue field,
      -- there exists some $t \in \text{adjoin } R \{β\}$ such that $s - t \in m_S$.
      obtain ⟨t, ht⟩ : ∃ t ∈ Algebra.adjoin R {β},
          s - t ∈ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) := by
        -- Since $s₀$ is in the adjoin of $β₀$ over the residue field,
        -- there exists some $t₀ \in \text{adjoin } R \{β\}$ such that $s₀ = \text{residue } S(t₀)$.
        obtain ⟨t₀, ht₀⟩ : ∃ t₀ ∈ Algebra.adjoin R {β},
            IsLocalRing.residue S s = IsLocalRing.residue S t₀ := by
          refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hs₀
          · exact fun x hx => ⟨ β, Algebra.subset_adjoin <| Set.mem_singleton _, by aesop ⟩
          · intro r
            obtain ⟨ r, rfl ⟩ := Ideal.Quotient.mk_surjective r
            exact ⟨ algebraMap R S r, Subalgebra.algebraMap_mem _ _, rfl ⟩
          · rintro x y hx hy ⟨ t₀, ht₀, rfl ⟩ ⟨ t₁, ht₁, rfl ⟩
            exact ⟨ t₀ + t₁, Subalgebra.add_mem _ ht₀ ht₁, by simp +decide ⟩
          · rintro x y hx hy ⟨ t₀, ht₀, rfl ⟩ ⟨ t₁, ht₁, rfl ⟩
            exact ⟨ t₀ * t₁, Subalgebra.mul_mem _ ht₀ ht₁, by simp +decide ⟩
        exact ⟨ t₀, ht₀.1, by rw [ h_mS ] ; exact Ideal.Quotient.eq.mp ht₀.2 ⟩;
      exact Submodule.mem_sup.mpr ⟨ t, ht.1, s - t, ht.2, by simp +decide ⟩
    -- Apply the lemma directly to get ⊤ ≤ S'
    have h_top_le : (⊤ : Submodule R S) ≤ S'.toSubmodule :=
      Submodule.le_of_le_smul_of_le_jacobson_bot h_fg h_jac h_le_sup
    -- Result: S' = ⊤
    exact eq_top_iff.mpr h_top_le
  exact ⟨β, adjoin_eq_top⟩

end Monogenic

-- note: the old thing was already in mathlib oops
-- #check faithfulSMul_iff_algebraMap_injective
