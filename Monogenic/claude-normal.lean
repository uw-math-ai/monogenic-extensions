import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.AdjoinRoot

open Polynomial
open Function
open RingHom

class Monogenic (R : Type*) (S : Type*) [CommSemiring R] [Semiring S] [Algebra R S] : Prop where
  exists_adjoin_eq_top : ∃(β : S), Algebra.adjoin R {β} = ⊤

structure GeneratesUnivQuot (R : Type*) (S : Type*) (β : S)
    [CommRing R] [Ring S] [Algebra R S] : Prop where
  integral : IsIntegral R β
  iso : Nonempty ((R[X] ⧸ Ideal.span {minpoly R β}) ≃ₐ[R] S)
  derivUnit : IsUnit (aeval β (minpoly R β).derivative)

class UnivQuotient (R : Type*) (S : Type*)
    [CommRing R] [Ring S] [Algebra R S] : Prop where
  minpoly_iso : ∃(β : S), GeneratesUnivQuot R S β

namespace Monogenic

variable {R S} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

/-
initial part without the integral domain hypothesis.
for the statement about the isomorphism with the quotient ring,
see isIntegrallyClosed_existsPolyQuotIso below
(idk, cant come up with a name. i think these new names are roughly
mathlib convention? i tried.)

see FaithfulSMul.iff_algebraMapInjective below for a proof its equivalent
to asserting that phi is injective.
-/
lemma if_finiteInjectiveEtale [Algebra R S] [FaithfulSMul R S]
  [Module.Finite R S] [Algebra.Etale R S] :
    Monogenic R S := by
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

-- Note: We add [IsDomain R], [IsIntegrallyClosed R], and [IsDomain S] hypotheses.
-- The [IsDomain R] and [IsIntegrallyClosed R] are needed for the minimal polynomial
-- to have the divisibility property (minpoly.isIntegrallyClosed_dvd).
-- [IsDomain S] follows naturally for étale extensions of domains.
omit [IsLocalRing S]
lemma isIntegrallyClosed_univQuot [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [IsDomain R] [IsDomain S] [IsIntegrallyClosed R] [Monogenic R S] :
    UnivQuotient R S := by
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  -- Since adjoin R {β} = ⊤, the minimal polynomial f of β gives S ≃ R[X]/(f)
  -- by the universal property of AdjoinRoot
  let ⟨β, adjoin_eq_top⟩ := (inferInstance : Monogenic R S)
  have hβ_int : IsIntegral R β := Algebra.IsIntegral.isIntegral β
  let f := minpoly R β
  use β
  -- The isomorphism S ≃ R[X]/(f) follows from:
  -- 1. lift : R[X]/(f) →ₐ[R] S sending [X] to β
  -- 2. This is surjective since adjoin R {β} = ⊤
  -- 3. This is injective because f = minpoly (kernel is exactly (f))

  -- Define the lift: R[X]/(f) →ₐ[R] S
  have hf_aeval : aeval β f = 0 := minpoly.aeval R β
  have hker : ∀ p ∈ Ideal.span {f}, aeval β p = 0 := by
    intro p hp
    rw [Ideal.mem_span_singleton] at hp
    obtain ⟨q, hq⟩ := hp
    simp only [hq, map_mul, hf_aeval, zero_mul]
  let lift_hom : (R[X] ⧸ Ideal.span {f}) →ₐ[R] S :=
    Ideal.Quotient.liftₐ (Ideal.span {f}) (Polynomial.aeval β) hker
  -- Prove bijectivity
  have lift_bij : Function.Bijective lift_hom := by
    constructor
    · -- Injectivity: kernel is trivial because f is minimal polynomial
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp only [lift_hom, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk] at hx
      -- aeval β p = 0 implies f ∣ p by minimality (using isIntegrallyClosed_dvd)
      simp only [Ideal.Quotient.eq_zero_iff_mem]
      apply Ideal.mem_span_singleton.mpr
      -- β is integral since S is finite over R
      exact minpoly.isIntegrallyClosed_dvd hβ_int hx
    · -- Surjectivity: image contains Algebra.adjoin R {β} = ⊤
      intro s
      -- s ∈ Algebra.adjoin R {β} since adjoin_eq_top
      have hs : s ∈ Algebra.adjoin R {β} := by
        -- have : S' = Algebra.adjoin R {β} := rfl
        rw [adjoin_eq_top]; trivial
      -- Induction on the adjoin structure
      induction hs using Algebra.adjoin_induction with
      | mem x hx =>
        -- x ∈ {β}, so x = β
        simp only [Set.mem_singleton_iff] at hx
        rw [hx]
        -- β = aeval β X, so use [X]
        use Ideal.Quotient.mk (Ideal.span {f}) X
        simp only [lift_hom, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
        exact aeval_X β
      | algebraMap r =>
        -- algebraMap R S r = aeval β (C r)
        use Ideal.Quotient.mk (Ideal.span {f}) (C r)
        simp only [lift_hom, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
        exact aeval_C β r
      | add x y _ _ ihx ihy =>
        obtain ⟨px, hpx⟩ := ihx
        obtain ⟨py, hpy⟩ := ihy
        use px + py
        simp only [map_add, hpx, hpy]
      | mul x y _ _ ihx ihy =>
        obtain ⟨px, hpx⟩ := ihx
        obtain ⟨py, hpy⟩ := ihy
        use px * py
        simp only [map_mul, hpx, hpy]

  exact ⟨hβ_int, ⟨AlgEquiv.ofBijective lift_hom lift_bij⟩, sorry⟩

end Monogenic

-- note: the old thing was already in mathlib oops
-- #check faithfulSMul_iff_algebraMap_injective
