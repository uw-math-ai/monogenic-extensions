import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.RingTheory.IsAdjoinRoot

open Polynomial
open Function
open RingHom
namespace Monogenic

variable {R S} [CommRing R] [CommRing S] [Algebra R S]

#check minpoly.natDegree_le
-- considered
-- Mathlib.LinearAlgebra.FreeModule.Finite.Basic
-- but charpoly imports that...
-- so maybe just next to LinearMap.charpoly_natDegree? (which we use here!)
-- in Mathlib.LinearAlgebra.Charpoly.Basic
-- doesn't really make sense to put it with charpoly though...
theorem _root_.minpoly.natDegree_le' [Module.Finite R S]
    [Module.Free R S] [Nontrivial R] (α : S) :
    (minpoly R α).natDegree ≤ Module.finrank R S := by
  set lα := Algebra.lmul R S α
  have haeval : aeval α lα.charpoly = 0 := Algebra.lmul_injective
    (by rw [map_zero, ← aeval_algHom_apply]; exact lα.aeval_self_charpoly)
  calc (minpoly R α).natDegree
      ≤ lα.charpoly.natDegree :=
        natDegree_le_natDegree (minpoly.min R α lα.charpoly_monic haeval)
    _ = Module.finrank R S := lα.charpoly_natDegree

/-- Let `R -> S` be a finite étale extension of local integral domains.
    Suppose there exists `β ∈ S` such that `S = R[β]`.
    Then `R[x]/(minpoly R β)` is isomorphic to `S` as an `R`-algebra.

    This avoids the `IsIntegrallyClosed` hypothesis by using:
    1. Cayley-Hamilton to bound `natDegree (minpoly R β) ≤ finrank R S`
    2. Quotient rank inequality for the reverse bound
    3. Surjective endomorphism injectivity for free modules
-/
noncomputable def _root_.IsAdjoinRoot.mkOfAdjoinEqTop'
  [Module.Finite R S]
  [Module.Free R S] [Nontrivial R]
  {α : S} (hα : Algebra.adjoin R {α} = ⊤) :
    IsAdjoinRootMonic S (minpoly R α) := by
  set f := minpoly R α
  have hf : f.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral α)
  haveI := hf.free_adjoinRoot; haveI := hf.finite_adjoinRoot
  let φ : AdjoinRoot f →ₐ[R] S :=
    AdjoinRoot.liftAlgHom f (Algebra.ofId R S) α (minpoly.aeval R α)
  have hφ_surj : Surjective φ := by
    rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top] at hα
    exact fun s => let ⟨p, hp⟩ := hα s; ⟨AdjoinRoot.mk f p, by simp [φ, ← aeval_def, hp]⟩
  have hrank : f.natDegree = Module.finrank R S := le_antisymm (minpoly.natDegree_le' α) (by
    have e := φ.toLinearMap.quotKerEquivRange.trans
      (LinearEquiv.ofTop _ (LinearMap.range_eq_top.mpr hφ_surj))
    rw [← e.finrank_eq]
    exact (Submodule.finrank_quotient_le _).trans (finrank_quotient_span_eq_natDegree' hf).le)
  have e := LinearEquiv.ofFinrankEq (R := R) (AdjoinRoot f) S
    ((finrank_quotient_span_eq_natDegree' hf).trans hrank)
  have hφ_inj : Injective φ := fun x y h => OrzechProperty.injective_of_surjective_endomorphism
    (e.symm.toLinearMap.comp φ.toLinearMap) (e.symm.surjective.comp hφ_surj) (congr_arg e.symm h)
  exact { IsAdjoinRoot.ofAdjoinRootEquiv (AlgEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩) with monic := hf }

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
lemma isUnit_of_residue_ne_zero {s : S} (h : IsLocalRing.residue S s ≠ 0) : IsUnit s :=
  IsLocalRing.notMem_maximalIdeal.mp <| mt (IsLocalRing.residue_eq_zero_iff s).mpr h

variable [IsLocalRing R] [Module.Finite R S] [FaithfulSMul R S]

/-- The square
      S → S/m_S
      ↑     ↑
      R → R/m_R
    commutes. -/
lemma residue_comp_algebraMap :
    (IsLocalRing.residue S).comp (algebraMap R S) =
    (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)).comp
      (IsLocalRing.residue R) :=
  rfl

/--
In Mathlib.RingTheory.LocalRing.ResidueField.Basic? maybe?

When `β` generates `S` over `R`, the residue `β₀ = β mod m_S`
generates `S / m_S` over `R / m_R.`

  R[X] --aeval β-->  S
   |                 |
map(residue R)    residue S
   v                 v
  kR[X] --aeval β₀-> kS
-/
lemma adjoin_residue_eq_top_of_adjoin_eq_top
    {β : S} (hβ_gen : Algebra.adjoin R {β} = ⊤) :
    Algebra.adjoin (IsLocalRing.ResidueField R) {IsLocalRing.residue S β} = ⊤ := by
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top] at *
  intro x
  obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective (R := S) x
  obtain ⟨p, rfl⟩ := hβ_gen s
  exact ⟨p.map (IsLocalRing.residue R),
    by simp only [aeval_def, eval₂_map, hom_eval₂]; rfl⟩

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
  -- Étale ⟹ flat, and finite + flat over local ring ⟹ Free
  haveI : Module.Free R S := Module.free_of_flat_of_isLocalRing
  -- Étale ⟹ m_R · S = m_S
  have hmaximal : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal S := Algebra.FormallyUnramified.map_maximalIdeal
  -- finrank_quotient_map gives: finrank (R ⧸ m_R) (S ⧸ Ideal.map m_R) = finrank R S
  have h := IsLocalRing.finrank_quotient_map (R := R) (S := S)
  -- Use the linear equivalence from quotEquivOfEq to transfer finrank
  let e : (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
      ≃ₗ[R ⧸ IsLocalRing.maximalIdeal R] (S ⧸ IsLocalRing.maximalIdeal S) :=
    AddEquiv.toLinearEquiv (Ideal.quotEquivOfEq hmaximal).toAddEquiv (fun r x => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp only [RingEquiv.toAddEquiv_eq_coe]; rfl)
  erw [← e.finrank_eq, h]

/-- Let `β ∈ S`, and let `f ∈ R[x]` be the minimal polynomial for `β` over `R`.
    Then `f mod m_S` is the minimal polynomial for `β mod m_S`.
    The proof uses the degree equality: since minpoly kR β₀ | f_bar, both are monic, and we
    show they have the same degree, hence they're equal.
-/
lemma minpoly_map_residue [Algebra.Etale R S]
    {β : S} (hadj : Algebra.adjoin R {β} = ⊤) :
    (minpoly R β).map (IsLocalRing.residue R) = minpoly (IsLocalRing.ResidueField R)
      (IsLocalRing.residue S β) := by
  have hmonic := minpoly.monic <| Algebra.IsIntegral.isIntegral (R:=R) β
  let kR := IsLocalRing.ResidueField R
  let β₀ := IsLocalRing.residue S β
  let f_bar := (minpoly R β).map (IsLocalRing.residue R)
  have hβ₀_int : IsIntegral kR β₀ := Algebra.IsIntegral.isIntegral β₀
  -- β₀ is a root of f_bar, so minpoly kR β₀ divides f_bar
  have hdvd : minpoly kR β₀ ∣ f_bar := minpoly.dvd kR β₀ (by
    rw [aeval_def, eval₂_map, ← residue_comp_algebraMap,  ← hom_eval₂, ← aeval_def, minpoly.aeval,
      map_zero])
  have hβ₀_gen : Algebra.adjoin kR {β₀} = ⊤ := adjoin_residue_eq_top_of_adjoin_eq_top hadj
  -- Degree chain: natDegree f_bar = natDegree f = finrank R S
  --             = finrank kR kS = natDegree (minpoly kR β₀)
  have hβ₀_field_gen : IntermediateField.adjoin kR {β₀} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic β₀)] at hβ₀_gen
    exact IntermediateField.toSubalgebra_injective hβ₀_gen
  have hdeg_eq : f_bar.natDegree = (minpoly kR β₀).natDegree := by
    haveI : Module.Free R S := Module.free_of_flat_of_isLocalRing
    rw [hmonic.natDegree_map _,
      ← (IsAdjoinRoot.mkOfAdjoinEqTop' hadj).finrank,
      finrank_eq_finrank_residueField, ← IntermediateField.finrank_top', ← hβ₀_field_gen,
      IntermediateField.adjoin.finrank hβ₀_int]
  -- Both monic, same degree, divisibility ⟹ equal
  exact eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hβ₀_int)
    (hmonic.map _) hdvd hdeg_eq.le

/-- A key technical fact: if `R -> S` is étale and `R[β] = S`,
      then `f'(β) is a unit in S`.

    The proof uses:
    1. (minpoly R β).map(residue) = minpoly kR β₀ (degree equality from generation)
    2. Separability gives aeval β₀ (minpoly kR β₀).derivative ≠ 0
    3. Therefore aeval β (minpoly R β).derivative ∉ m_S, hence is a unit
-/
lemma isUnit_aeval_derivative_minpoly_of_adjoin_eq_top
    [Algebra.Etale R S] {β : S}
    (hadj : Algebra.adjoin R {β} = ⊤) :
    IsUnit (aeval β (minpoly R β).derivative) := by
  -- Strategy: show residue of (aeval β f') is non-zero, hence aeval β f' is a unit
  apply fun s h =>
    IsLocalRing.notMem_maximalIdeal.mp <| mt (IsLocalRing.residue_eq_zero_iff s).mpr h
  let kR := IsLocalRing.ResidueField R
  let β₀ := IsLocalRing.residue S β
  -- Therefore, derivative of minpoly at β₀ is non-zero
  have hderiv_ne_zero : aeval β₀ (minpoly kR β₀).derivative ≠ 0 :=
    (Algebra.IsSeparable.isSeparable kR β₀).aeval_derivative_ne_zero (minpoly.aeval kR β₀)
  let p := (minpoly R β).derivative
  have residue_aeval_eq : IsLocalRing.residue S (aeval β <| p) =
      p.eval₂ ((IsLocalRing.residue S).comp (algebraMap R S)) (IsLocalRing.residue S β) := by
    simp only [aeval_def, hom_eval₂]
  rw [residue_aeval_eq, residue_comp_algebraMap, ← eval₂_map,
    ← derivative_map, minpoly_map_residue hadj, ← aeval_def]
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
  have hs₀ : Ideal.Quotient.mk q s ∈ Algebra.adjoin (R ⧸ q.comap (algebraMap R S))
      {Ideal.Quotient.mk q β} := by rw [h_gen]; trivial
  obtain ⟨t, ht, ht_eq⟩ : ∃ t ∈ Algebra.adjoin R {β},
      Ideal.Quotient.mk q s = Ideal.Quotient.mk q t := by
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hs₀
    · intro x hx; simp only [Set.mem_singleton_iff] at hx
      exact ⟨β, Algebra.subset_adjoin rfl, by rw [hx]⟩
    · intro r; obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      exact ⟨algebraMap R S r, Subalgebra.algebraMap_mem _ _,
        (Ideal.quotientMap_mk (I := q) (f := algebraMap R S) (H := le_rfl)).symm⟩
    · rintro x y _ _ ⟨t₀, ht₀, rfl⟩ ⟨t₁, ht₁, rfl⟩
      exact ⟨t₀ + t₁, Subalgebra.add_mem _ ht₀ ht₁, (map_add _ t₀ t₁).symm⟩
    · rintro x y _ _ ⟨t₀, ht₀, rfl⟩ ⟨t₁, ht₁, rfl⟩
      exact ⟨t₀ * t₁, Subalgebra.mul_mem _ ht₀ ht₁, (map_mul _ t₀ t₁).symm⟩
  exact ⟨t, ht, Ideal.Quotient.eq.mp ht_eq⟩

omit [IsLocalRing S] [IsLocalRing R] [Module.Finite R S] [FaithfulSMul R S] in
/-- Nakayama argument: if `R/p[β] = S/q`, and `mS = π S + m_R · S` for some `π ∈ R[β]`,
    then `R[β] = S`.

    The proof combines:
    1. Quotient lifting: S = A + q (from `h_gen`)
    2. Artinian descent: ms^n ⊆ mR·S for some n
    3. Iterative reduction: q ⊆ A + mR·S (using π ∈ A and ms = ⟨π⟩ + mR·S)
    4. Nakayama's lemma: S ⊆ A + mR·S implies A = S -/
lemma adjoin_eq_top_of_quotient
    [IsLocalRing R] [IsLocalRing S] [Module.Finite R S]
    (β : S) (q : Ideal S) [q.IsPrime]
    (h_gen : Algebra.adjoin (R ⧸ q.comap (algebraMap R S))
      {Ideal.Quotient.mk q β} = ⊤)
    (π : S) (hπ_mem : π ∈ Algebra.adjoin R {β})
    (h_ms : IsLocalRing.maximalIdeal S =
      Ideal.span {π} ⊔ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) :
    Algebra.adjoin R {β} = ⊤ := by
  set A := Algebra.adjoin R {β}; set mR := IsLocalRing.maximalIdeal R
  set ms := IsLocalRing.maximalIdeal S; set mR_S := Ideal.map (algebraMap R S) mR
  haveI : IsArtinianRing (S ⧸ mR_S) := by
    letI := Ideal.Quotient.field mR
    haveI := Module.Finite.of_restrictScalars_finite R (R ⧸ mR) (S ⧸ mR_S)
    exact IsArtinianRing.of_finite (R ⧸ mR) (S ⧸ mR_S)
  obtain ⟨n, hn⟩ := IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient mR_S
  have h_lift := exists_adjoin_sub_mem β q h_gen
  have hπ_ms : π ∈ ms := h_ms ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self π)
  have hq_le : q ≤ ms := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)
  have h_pow : ∀ k : ℕ, ms ^ k ≤ Ideal.span {π ^ k} ⊔ mR_S := by
    intro k; induction k with
    | zero => simp [Ideal.span_singleton_one]
    | succ k ih =>
      rw [pow_succ]; calc ms ^ k * ms
          ≤ (Ideal.span {π ^ k} ⊔ mR_S) * (Ideal.span {π} ⊔ mR_S) :=
            Ideal.mul_mono ih h_ms.le
        _ ≤ Ideal.span {π ^ (k + 1)} ⊔ mR_S := by
            rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
            refine sup_le (sup_le ?_ (Ideal.mul_le_left.trans le_sup_right))
              (sup_le (Ideal.mul_le_right.trans le_sup_right)
                (Ideal.mul_le_left.trans le_sup_right))
            rw [Ideal.span_singleton_mul_span_singleton, pow_succ]; exact le_sup_left
  have h_iter : ∀ (k : ℕ) (x : S), x ∈ q →
      ∃ a ∈ A.toSubmodule, x - a ∈ (Ideal.span {π ^ k} ⊔ mR_S : Ideal S) := by
    intro k; induction k with
    | zero => exact fun _ _ => ⟨0, Subalgebra.zero_mem A, by simp [Ideal.span_singleton_one]⟩
    | succ k ih =>
      intro x hx; obtain ⟨a₀, ha₀, hz⟩ := ih x hx
      obtain ⟨y, hy, r, hr, hyr⟩ := Submodule.mem_sup.mp hz
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hy
      obtain ⟨a₁, ha₁, hc⟩ := h_lift c
      refine ⟨a₀ + a₁ * π ^ k, Subalgebra.add_mem A ha₀
        (Subalgebra.mul_mem A ha₁ (Subalgebra.pow_mem A hπ_mem k)), ?_⟩
      rw [show x - (a₀ + a₁ * π ^ k) = π ^ k * (c - a₁) + r from
        by linear_combination hyr.symm]
      have hmem : π ^ k * (c - a₁) ∈ ms ^ (k + 1) := by
        rw [pow_succ]; exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hπ_ms k) (hq_le hc)
      exact Ideal.add_mem _ (h_pow (k + 1) hmem) (Ideal.mem_sup_right hr)
  have h_q : (q.restrictScalars R : Submodule R S) ≤ A.toSubmodule ⊔ mR • ⊤ := by
    intro x hx; obtain ⟨a, ha, hxa⟩ := h_iter n x hx; rw [Ideal.smul_top_eq_map]
    exact Submodule.mem_sup.mpr ⟨a, ha, x - a, show x - a ∈ mR_S.restrictScalars R from
      (sup_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
        (hn (Ideal.pow_mem_pow hπ_ms n)))) le_rfl) hxa, by ring⟩
  exact eq_top_iff.mpr (Submodule.le_of_le_smul_of_le_jacobson_bot
    (Module.finite_def.mp inferInstance) (IsLocalRing.maximalIdeal_le_jacobson ⊥) (by
      intro s _; obtain ⟨t, ht, hst⟩ := h_lift s
      rw [show s = t + (s - t) from by ring]
      exact Submodule.add_mem _ (Submodule.mem_sup_left ht) (h_q hst)))

/-
initial part without the integral domain hypothesis.
for the statement about the isomorphism with the quotient ring,
see isIntegrallyClosed_existsPolyQuotIso below
(idk, cant come up with a name. i think these new names are roughly
mathlib convention? i tried.)

see FaithfulSMul.iff_algebraMapInjective below for a proof its equivalent
to asserting that phi is injective.
-/
theorem exists_adjoin_eq_top [Algebra.Etale R S] :
    ∃(β : S), Algebra.adjoin R {β} = ⊤ := by
  obtain ⟨β₀, hβ₀⟩ := Field.exists_primitive_element (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField S)
  obtain ⟨β, hβ⟩ := Ideal.Quotient.mk_surjective β₀
  refine ⟨β, ?_⟩
  have h_adjoin_top : Algebra.adjoin (IsLocalRing.ResidueField R) {β₀} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic β₀), hβ₀, IntermediateField.top_toSubalgebra]
  set mR := IsLocalRing.maximalIdeal R
  have h_le_sup : (⊤ : Submodule R S) ≤ (Algebra.adjoin R {β}).toSubmodule ⊔ mR • ⊤ := by
    intro s _
    have hs₀ : IsLocalRing.residue S s ∈ Algebra.adjoin (IsLocalRing.ResidueField R) {β₀} :=
      h_adjoin_top ▸ trivial
    obtain ⟨t₀, ht₀_mem, ht₀_eq⟩ : ∃ t₀ ∈ Algebra.adjoin R {β},
        IsLocalRing.residue S s = IsLocalRing.residue S t₀ := by
      refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hs₀
      · exact fun x hx => ⟨β, Algebra.subset_adjoin rfl,
          (Set.mem_singleton_iff.mp hx).symm ▸ hβ.symm⟩
      · intro r; obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        exact ⟨algebraMap R S r, Subalgebra.algebraMap_mem _ _, rfl⟩
      · rintro _ _ - - ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, Subalgebra.add_mem _ ha hb, (map_add _ a b).symm⟩
      · rintro _ _ - - ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, Subalgebra.mul_mem _ ha hb, (map_mul _ a b).symm⟩
    rw [Ideal.smul_top_eq_map]
    exact Submodule.mem_sup.mpr ⟨t₀, ht₀_mem, s - t₀,
      (Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S)) ▸
        Ideal.Quotient.eq.mp ht₀_eq, by ring⟩
  exact eq_top_iff.mpr (Submodule.le_of_le_smul_of_le_jacobson_bot
    (Module.finite_def.mp inferInstance) (IsLocalRing.maximalIdeal_le_jacobson ⊥) h_le_sup)

/-!
## Converse: monogenic with unit derivative implies étale

The converse direction: if `S ≅ R[X]/(f)` with `f` monic and `f'(root)` a unit,
then the algebra map `R → S` is étale. This completes the characterization:
for finite local extensions, étale with single generator is equivalent to
monogenic with unit derivative (i.e., standard étale).
-/

omit [IsLocalRing S] [IsLocalRing R] [Module.Finite R S] [FaithfulSMul R S] in
/-- If `S ≅ R[X]/(f)` with `f` monic and `f'(root)` a unit in `S`, then `R → S` is étale.
This is the converse of `isUnit_aeval_derivative_minpoly`: together they show that
for finite extensions of local rings, the étale condition is equivalent to
being a monogenic extension with unit derivative.

The proof constructs a `StandardEtalePresentation` using the pair `(f, f')`:
since `f' · 1 + f · 0 = f'^1`, the derivative condition gives the Bézout-type
relation needed for standard étaleness. -/
theorem IsAdjoinRootMonic.algebra_etale
    {f : R[X]} (adj : IsAdjoinRootMonic S f)
    (hunit : IsUnit (aeval adj.root f.derivative)) :
    Algebra.Etale R S := by
  -- Standard étale pair (f, f') with trivial Bézout: f' · 1 + f · 0 = f'^1
  let P : StandardEtalePair R :=
    ⟨f, adj.monic, f.derivative, 1, 0, 1, by ring⟩
  have hmap : P.HasMap adj.root := ⟨adj.aeval_root_self, hunit⟩
  -- Build an explicit inverse of P.lift: compose S ≃ AdjoinRoot f →[liftHom] P.Ring
  set e := adj.toIsAdjoinRoot.adjoinRootAlgEquiv with he_def
    -- e : AdjoinRoot f ≃ₐ[R] S
  set bwd : S →ₐ[R] P.Ring :=
    (AdjoinRoot.liftAlgHom f _ P.X P.hasMap_X.1).comp e.symm.toAlgHom with hbwd_def
    -- bwd sends adj.root → AdjoinRoot.root f → P.X
  -- bwd is a left inverse of P.lift (checked on P.X via hom_ext)
  have h_left_eq : bwd.comp (P.lift adj.root hmap) = AlgHom.id R P.Ring := by
    apply P.hom_ext
    change bwd (P.lift adj.root hmap P.X) = P.X
    simp [hbwd_def, he_def]
  have h_left : ∀ x, bwd (P.lift adj.root hmap x) = x :=
    fun x => by simpa using DFunLike.congr_fun h_left_eq x
  -- bwd is a right inverse of P.lift (checked on adj.map p for all p)
  have h_right : ∀ s, P.lift adj.root hmap (bwd s) = s := by
    intro s
    obtain ⟨p, rfl⟩ := adj.map_surjective s
    -- e.symm (adj.map p) = mk f p (the canonical representative in AdjoinRoot f)
    have h1 : e.symm (adj.map p) = AdjoinRoot.mk f p :=
      e.symm_apply_eq.mpr (adj.toIsAdjoinRoot.adjoinRootAlgEquiv_apply_mk p).symm
    -- Compute bwd (adj.map p) = aeval P.X p
    have h_bwd_val : bwd (adj.map p) = aeval P.X p := by
      change (AdjoinRoot.liftAlgHom f _ P.X P.hasMap_X.1) (e.symm (adj.map p)) = aeval P.X p
      rw [h1]; simp [aeval_def]
    -- Chain: P.lift (aeval P.X p) = aeval adj.root p = adj.map p
    rw [h_bwd_val]
    calc P.lift adj.root hmap (aeval P.X p)
        = aeval (P.lift adj.root hmap P.X) p := (aeval_algHom_apply _ _ _).symm
      _ = aeval adj.root p := by rw [P.lift_X]
      _ = adj.map p := by simp
  -- Conclude: P.lift is bijective, so S is standard étale, hence étale
  have lift_bij : Function.Bijective (P.lift adj.root hmap) :=
    ⟨fun a b hab => by rw [← h_left a, ← h_left b, hab],
     fun s => ⟨bwd s, h_right s⟩⟩
  haveI : Algebra.IsStandardEtale R S := ⟨⟨P, adj.root, hmap, lift_bij⟩⟩
  exact inferInstance

end Monogenic

-- note: the old thing was already in mathlib oops
-- #check faithfulSMul_iff_algebraMap_injective
