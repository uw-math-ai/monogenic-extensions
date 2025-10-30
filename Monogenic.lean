import Monogenic.Basic
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
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


#eval Lean.versionString
#eval 3+4

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
def RingHom.IsSeparable (f : R →+* S) : Prop :=
      Algebra.IsSeparable R S

lemma Lemma_3_2 (R S : Type)
  [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S]
  (ϕ : R →+* S) (hfin : ϕ.Finite) (hinj : Function.Injective ϕ)
  (etale : RingHom.Etale ϕ) :
  ∃ β : S, (Algebra.adjoin ϕ.range {β} = S) ∧
  ∃ (f : Polynomial R) (fmon : f.Monic), Polynomial.eval β (Polynomial.map ϕ f) =
  0 ∧ (∀ (g : Polynomial R), Polynomial.eval β (Polynomial.map ϕ g) = 0 → f ∣ g) ∧
  IsUnit (Polynomial.eval β (Polynomial.map ϕ (Polynomial.derivative f))) := by
    let mr : Ideal R := IsLocalRing.maximalIdeal R
    let ms : Ideal S := IsLocalRing.maximalIdeal S
    let S_is_R_algebra : Algebra R S := RingHom.toAlgebra ϕ
    have ϕ_S_R_map : algebraMap R S = ϕ :=
        RingHom.algebraMap_toAlgebra ϕ
    have eq_max_prod : Ideal.map ϕ mr  = ms := by
      have unramified_ϕ: ϕ.FormallyUnramified :=
        ((RingHom.etale_iff_formallyUnramified_and_smooth ϕ).mp etale).1
      have unramifed_alg_rs: Algebra.FormallyUnramified R S := by
        rw [← ϕ_S_R_map] at unramified_ϕ; exact unramified_ϕ;
      have local_ϕ : IsLocalHom (algebraMap R S) :=
        RingHom.IsIntegral.isLocalHom (RingHom.IsIntegral.of_finite hfin) hinj
      have fin_R_S : Algebra.EssFiniteType R S :=
        RingHom.FiniteType.essFiniteType (RingHom.FiniteType.of_finite hfin)
      apply Algebra.FormallyUnramified.map_maximalIdeal


    /-  (Task 2)lemma packaging sentence 2 and first part of sentence 3 from Lemma 3.2
    hypotheses: TBD
    result: R/mr-> S/ms separable -/
    have induced_algebra : Algebra (R ⧸ mr) (S ⧸ms) := by
      refine Ideal.Quotient.algebraQuotientOfLEComap ?_
      rw [ϕ_S_R_map]; apply Ideal.le_comap_of_map_le; simp[eq_max_prod]
    have separable_of_induced_map : Algebra.IsSeparable (R ⧸ mr) (S ⧸ ms) := by
      sorry


    /- (Task 3) lemma packaging last part of sentence 3 + sentence 4 from Lemma 3.2
    hypotheses: TBD
    result: R/mr-> S/ms = R/mr[β_0] and the minimal polynomial f0 is separable -/
    have adjoined_algebra : ∃ β_0 : (S ⧸ ms), Algebra.adjoin (R ⧸ mr) {β_0} = (S ⧸ ms) := by
      sorry


---------------------

    /- (Task 4) lemma packaging sentence 5 (displayed equation) from Lemma 3.2
    hypotheses: TBD
    result: If β is a lift of β_0, then R[β]/(mr R[β]) simeq S/ms -/

    -- exhibit β_0 from previous step
    rcases adjoined_algebra with ⟨β_0, hb⟩

    -- get a preimage β in S of β_0 in S/ms
    let exists_preimage : ∃ (β : S), (Ideal.Quotient.mk ms) β = β_0 := by
      have surj_of : Function.Surjective (Ideal.Quotient.mk ms) := by
        exact Ideal.Quotient.mk_surjective
      exact surj_of β_0

    -- exhibit such a β (in S)
    rcases exists_preimage with ⟨β, hb2⟩

    -- get inclusions R -> R[β] and R[β] → S
    let R_beta : Subalgebra R S := (Algebra.adjoin R {β})

    let μ : (R →+* R_beta) := by apply RingHom.smulOneHom

    let ν : (R_beta →+* S) := by apply RingHom.smulOneHom

    have composition : ν ∘ μ = ϕ := by
      sorry

    -- get the ideal mr R[β]
    let mrR_beta : Ideal R_beta := Ideal.map μ mr

    -- want to witness R[β]/mr R[β] as a subalgebra of S/ms
    -- need to show mr R[β] maps into ms (then leverage univ prop of quotient)

    let mrR_betaS : Ideal S := Ideal.map ν mrR_beta

    have ideal_inc : mrR_betaS ≤ ms := by
      sorry

    have extensionintower : mrR_betaS = ms := by
      sorry




    -- statement of isomorphism
    have compared_quotients : (R_beta ⧸ mrR_beta) = (S ⧸ ms) := by
      sorry



    -- have extended_algebra : Algebra.adjoin ϕ.range {β} := by
    --   sorry

    -- have Image_Rmr : Subalgebra (Algebra.adjoin (R ⧸ mr) {β_0}) (S ⧸ ms) := by
    --   sorry

    -- \quot -> ⧸
    -- have Image_Rbeta : Subalgebra ((Algebra.adjoin R {β}) ⧸ (Algebra.ideal.span R {mr})) (S ⧸ ms) := by
      -- sorry
    -- have quotient_iso_adjoin_beta : (Image_Rmr) ≃ (Image_Rbeta) := by
      -- sorry

---------------------

    /- (Task 5) lemma packaging sentence 6  from Lemma 3.2, uses Nakayama
    hypotheses: TBD
    result: R[β] = S
    -/
    -- rcases exists_preimage with ⟨β,hb⟩
    have lifted_adjoined : Algebra.adjoin R {β} = S := by
      sorry

    /- (Task 6) lemma packaging sentence 7 & 8 from Lemma 3.2
    hypotheses: TBD
    result: f'(β) is not in ms
    -/
    let f := Polynomial.derivative (Polynomial.map ϕ (minpoly R β))
    have is_unit_minpoly : Polynomial.eval β f ∉ ms := by
      sorry

    sorry
