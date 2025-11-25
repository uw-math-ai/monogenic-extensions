import Monogenic.Basic
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.Algebra.Algebra.Basic
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
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib/LinearAlgebra/TensorProduct

import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Polynomial.Eval.Algebra


-- #eval Lean.versionString
-- #eval 3+4

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
def RingHom.IsSeparable (f : R →+* S) : Prop :=
  Algebra.IsSeparable R S

lemma Lemma_3_2 (R S : Type)
  [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S]
  (ϕ : R →+* S) (hfin : ϕ.Finite) (hinj : Function.Injective ϕ)
  (etale : RingHom.Etale ϕ) :
  ∃ β : S, (Algebra.adjoin ϕ.range {β} = S) ∧
  ∃ (f : Polynomial R) (fmon : f.Monic), Polynomial.eval β (Polynomial.map ϕ f) = 0 ∧
  (∀ (g : Polynomial R), Polynomial.eval β (Polynomial.map ϕ g) = 0 → f ∣ g) ∧
  IsUnit (Polynomial.eval β (Polynomial.map ϕ (Polynomial.derivative f))) := by
  let mr : Ideal R := IsLocalRing.maximalIdeal R
  let ms : Ideal S := IsLocalRing.maximalIdeal S
  let S_is_R_algebra : Algebra R S := RingHom.toAlgebra ϕ
  have ϕ_S_R_map : algebraMap R S = ϕ :=
    RingHom.algebraMap_toAlgebra ϕ
  have eq_max_prod : Ideal.map ϕ mr = ms := by
    have unramified_ϕ: ϕ.FormallyUnramified :=
      ((RingHom.etale_iff_formallyUnramified_and_smooth ϕ).mp etale).1
    have unramifed_alg_rs: Algebra.FormallyUnramified R S := by
      rw [← ϕ_S_R_map] at unramified_ϕ
      exact unramified_ϕ
    have local_ϕ : IsLocalHom (algebraMap R S) :=
      RingHom.IsIntegral.isLocalHom (RingHom.IsIntegral.of_finite hfin) hinj
    have fin_R_S : Algebra.EssFiniteType R S :=
      RingHom.FiniteType.essFiniteType (RingHom.FiniteType.of_finite hfin)
    apply Algebra.FormallyUnramified.map_maximalIdeal


/-  (Task 2) lemma packaging sentence 2 and first part of sentence 3 from Lemma 3.2
      hypotheses: TBD
      result: R/mr -> S/ms separable -/
  have induced_algebra : Algebra (R ⧸ mr) (S ⧸ ms) := by
    refine Ideal.Quotient.algebraQuotientOfLEComap ?_
    rw [ϕ_S_R_map]
    apply Ideal.le_comap_of_map_le
    simp [eq_max_prod]

  -- REQUIRED: register the algebra structure
  letI : Algebra (R ⧸ mr) (S ⧸ ms) := induced_algebra

  have separable_of_induced_map :
      Algebra.IsSeparable (R ⧸ mr) (S ⧸ ms) := by

    -- Extract formally unramified and formally smooth for the ring hom ϕ
    -- Extract unramified and smooth from etale
    have h := (RingHom.etale_iff_formallyUnramified_and_smooth ϕ).mp etale

    -- Step 1: Extract formally unramified + smooth from etale
    have unram_ϕ : ϕ.FormallyUnramified := h.1

    -- Step 2: Convert smooth → formally smooth
    have h_smooth :
        ϕ.FormallySmooth ∧ ϕ.FinitePresentation :=
      (RingHom.smooth_def (f := ϕ)).1 h.2

    have smooth_ϕ : ϕ.FormallySmooth :=
      h_smooth.1

    have unram_alg : Algebra.FormallyUnramified R S := by
      simpa [RingHom.FormallyUnramified] using unram_ϕ

    have smooth_alg : Algebra.FormallySmooth R S :=
      RingHom.FormallySmooth.toAlgebra smooth_ϕ

    -- Step 3: define the quotient map R → R ⧸ mr (this will be our base-change map)
    let f : R →+* (R ⧸ mr) := Ideal.Quotient.mk mr

    -- Step 4: perform base-change of ϕ using the “étale is stable under base change” lemma
    classical
    -- we now move into CommRingCat so we can use `pushout_inl`
    let R₀ : CommRingCat := CommRingCat.of R
    let S₀ : CommRingCat := CommRingCat.of S
    let T₀ : CommRingCat := CommRingCat.of (R ⧸ mr)

    -- the two maps R → S and R → R ⧸ mr as morphisms in CommRingCat
    let g₀ : R₀ ⟶ S₀ := CommRingCat.ofHom ϕ
    let f₀ : R₀ ⟶ T₀ := CommRingCat.ofHom f

    -- “Etale is stable under base change” as a morphism property P(f) := f.Etale
    have hP :
        RingHom.IsStableUnderBaseChange
          (fun {R S} [CommRing R] [CommRing S] (f : R →+* S) =>
            f.Etale) :=
      RingHom.Etale.isStableUnderBaseChange

    -- Etale respects isomorphisms (this is needed by `pushout_inl`)
    have hP' :
        RingHom.RespectsIso
          (fun {R S} [CommRing R] [CommRing S] (f : R →+* S) =>
            f.Etale) :=
      RingHom.Etale.respectsIso

    -- view your given hypothesis `etale : ϕ.Etale` as a property of g₀
    have etale_g₀ :
        (CommRingCat.Hom.hom g₀).Etale := by
      simpa using etale

    -- Apply stability-under-base-change to the pushout square
    have etale_base_pushout :
        (CommRingCat.Hom.hom
          (CategoryTheory.Limits.pushout.inl f₀ g₀)).Etale :=
      RingHom.IsStableUnderBaseChange.pushout_inl
        hP hP' f₀ g₀ etale_g₀

    -- Now rewrite the pushout as the tensor product (R ⧸ mr) ⊗[R] S
    -- using the standard isomorphism of pushouts with tensor products.
    -- Placeholder iso — you will fill this in later.
    have iso_pushout_tensor :
        CategoryTheory.Arrow.mk
            (CategoryTheory.Limits.pushout.inl f₀ g₀)
          ≅
        CategoryTheory.Arrow.mk
          (CommRingCat.ofHom
            (algebraMap (R ⧸ mr) (TensorProduct R (R ⧸ mr) S))) :=
      by
        admit


    have etale_base :
        (algebraMap (R ⧸ mr) (TensorProduct R (R ⧸ mr) S)).Etale := by
      -- transport etaleness along the iso in the arrow category
      have h₁ :
          (CommRingCat.Hom.hom
            (CategoryTheory.Limits.pushout.inl f₀ g₀)).Etale :=
        etale_base_pushout
      have h₂ :=
        (RingHom.RespectsIso.arrow_mk_iso_iff hP' iso_pushout_tensor).mp h₁
      -- rewrite the conclusion into the desired form
      simpa using h₂


    -- Step 5: etale ⇒ separable
    -- use the etale result above; replace `etale_quot` with the name you actually constructed
    admit



    /- (Task 3) lemma packaging last part of sentence 3 + sentence 4 from Lemma 3.2
    hypotheses: TBD
    result: R/mr-> S/ms = R/mr[β_0] and the minimal polynomial f0 is separable -/
    have adjoined_algebra : ∃ β_0 : (S ⧸ ms), Algebra.adjoin (R ⧸ mr) {β_0} = (S ⧸ ms) := by
      -- Use separability to find a generator
      obtain ⟨β_0, hβ_0⟩ := Algebra.IsSeparable.exists_adjoin_eq_top separable_of_induced_map
      exact ⟨β_0, hβ_0⟩


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

    let μ : R →+* R_beta := algebraMap R R_beta

    let ν : R_beta →+* S := (R_beta.val : R_beta →ₐ[R] S)

    have nualgmap : algebraMap R_beta S = ν := by
      rfl

    -- describe relations between μ, ν, and ϕ
    have composition : ν.comp μ = ϕ := by
      apply RingHom.ext
      intro r
      dsimp [μ, ν]
      -- R_beta.val (algebraMap R R_beta r) is (algebraMap R R_beta r : S),
      -- and that equals algebraMap R S r, which by `ϕ_S_R_map` is `ϕ r`.
      simp [ϕ_S_R_map]

    -- get the ideal mr R[β]
    let mrR_beta : Ideal R_beta := Ideal.map μ mr

    -- want to witness R[β]/mr R[β] as a subalgebra of S/ms?
    -- need to show mr R[β] maps into ms (then leverage universal property of quotient)
    let mrR_betaS : Ideal S := Ideal.map ν mrR_beta

    have extensionintower : mrR_betaS = ms := by
      sorry
      -- exact Ideal.comap_map_eq_of_surjective ν (Ideal.le_refl ms)

    -- the kernel of π ∘ ν is the preimage under ν of the kernel of π
    have ker_eq : RingHom.ker (π.comp ν) = mrR_beta := by
      rw[← RingHom.comap_ker]
      rw[kerpi_eq]
      exact preim


    -- have identifykernel : Ideal.comap (pi ∘ ν) mrR_beta = mrR_beta := by
      -- sorry

    have compared_quotients : (R_beta ⧸ mrR_beta) ≃ₐ[R ⧸ mr] (S ⧸ ms) := by
      -- Use the universal property of quotients
      refine Ideal.quotientEquivOfEq ideal_inc _
      exact extensionintower
    have compared_quotients : (R_beta ⧸ mrR_beta) = (S ⧸ ms) := by
      sorry
      -- exact Ideal.comap_map_eq_of_surjective ν (Ideal.le_refl ms)

    -- the kernel of π ∘ ν is the preimage under ν of the kernel of π
    have ker_eq : RingHom.ker (π.comp ν) = mrR_beta := by
      rw[← RingHom.comap_ker]
      rw[kerpi_eq]
      exact preim


    -- have identifykernel : Ideal.comap (pi ∘ ν) mrR_beta = mrR_beta := by
      -- sorry

    have compared_quotients : (R_beta ⧸ mrR_beta) ≃ₐ[R ⧸ mr] (S ⧸ ms) := by
      -- Use the universal property of quotients
      refine Ideal.quotientEquivOfEq ideal_inc _
      exact extensionintower

    -- have Image_Rmr : Subalgebra (Algebra.adjoin (R ⧸ mr) {β_0}) (S ⧸ ms) := by
    --   sorry

    -- \quot -> ⧸
    -- have Image_Rbeta : Subalgebra ((Algebra.adjoin R {β}) ⧸ (Algebra.ideal.span R {mr})) (S ⧸ ms) := by
      -- sorry
    -- have quotient_iso_adjoin_beta : (Image_Rmr) ≃ (Image_Rbeta) := by
      -- sorry

---------------------

    /- (Task 5) lemma packaging sentence 6  from Lemma 3.2, uses Nakayama
    have lifted_adjoined : Algebra.adjoin R {β} = S := by
      -- Use Nakayama's lemma to show equality
      apply Algebra.adjoin_eq_of_le
      · exact Algebra.subset_adjoin
      · apply Ideal.eq_top_of_is_unit
        exact is_unit_minpoly
    -/
    -- rcases exists_preimage with ⟨β,hb⟩
    have lifted_adjoined : Algebra.adjoin R {β} = S := by
      sorry

    /- (Task 6) lemma packaging sentence 7 & 8 from Lemma 3.2
    hypotheses: TBD
    result: f'(β) is not in ms
    -/
    /-
    let f' : Polynomial S := Polynomial.derivative (Polynomial.map ϕ (minpoly R β))
    have is_unit_minpoly_deriv : Polynomial.aeval β f' ∉ ms := by

      sorry
    -/

    /-
    let f'_map_ideal := Polynomial.map (Ideal.Quotient.mk ms) f'
      have poly_zero : (Ideal.Quotient.mk ms) (Polynomial.aeval β f') = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 cont
      unfold f' at poly_zero
      rw[Polynomial.derivative_map (minpoly R β) ϕ] at poly_zero
      have eq_mod_ms :  Polynomial.map (Ideal.Quotient.mk ms) (Polynomial.map ϕ f)
        = Polynomial.map (algebraMap (R ⧸ mr) (S ⧸ ms)) f_0 := by
        unfold f_0 f
        have div_min_of_min : Polynomial.map (algebraMap (R ⧸ mr) (S ⧸ ms)) f_0 ∣
          Polynomial.map (Ideal.Quotient.mk ms) (Polynomial.map ϕ f) := by
          have eval_zero_of_f : Polynomial.eval β_0 (Polynomial.map (Ideal.Quotient.mk ms)
            (Polynomial.map ϕ f)) = 0 := by
    -/


    have field_quot_S : Field (S ⧸ ms) := Ideal.Quotient.field ms
    have field_quot_R : Field (R ⧸ mr) := Ideal.Quotient.field mr
    let f' : Polynomial S := Polynomial.derivative (Polynomial.map ϕ (minpoly R β))
    let f : Polynomial R := minpoly R β
    let f_0 : Polynomial (R ⧸ mr) :=  minpoly (R ⧸ mr) β_0
    have is_unit_minpoly_deriv : Polynomial.eval β f' ∉ ms := by
      by_contra cont
      have not_zero_of_β_0 : Polynomial.eval β_0 (Polynomial.derivative
        (Polynomial.map (Ideal.Quotient.mk ms) (Polynomial.map ϕ f))) ≠ 0 := by
        by_contra ct
        rw [Polynomial.derivative_map] at ct
        rw [Polynomial.eval_map] at ct
        have h_comm_map : ∀(a : S), Commute ((Ideal.Quotient.mk ms) a)
          ((Ideal.Quotient.mk ms β)) :=
          fun a ↦ Commute.all ((Ideal.Quotient.mk ms) a) ((Ideal.Quotient.mk ms) β)
        let preimage_β: β_0 = (Ideal.Quotient.mk ms) β := id (Eq.symm hb2)
        rw [preimage_β] at ct
        rw [← Polynomial.eval₂RingHom'_apply (Ideal.Quotient.mk ms) β h_comm_map
          (Polynomial.derivative (Polynomial.map ϕ f))] at ct
        have  β_0_from_ct : (Polynomial.eval₂RingHom' (Ideal.Quotient.mk ms) ((Ideal.Quotient.mk ms) β) h_comm_map) = Polynomial.eval₂ β_0 := by
          sorry

        #check Polynomial.aeval_algebraMap_apply
        sorry



      sorry

    sorry

        #check Polynomial.Separable.aeval_derivative_ne_zero

      sorry

    sorry
