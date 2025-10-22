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

variable (R S : Type*) [CommRing R] [CommRing S][Algebra R S]
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
    have eq_max_prod : Ideal.map ϕ mr  = ms := by
      have unramified_ϕ: ϕ.FormallyUnramified :=
        ((RingHom.etale_iff_formallyUnramified_and_smooth ϕ).mp etale).1
      let S_is_R_algebra : Algebra R S := RingHom.toAlgebra ϕ
      have ϕ_S_R_map : algebraMap R S = ϕ :=
        RingHom.algebraMap_toAlgebra ϕ
      have unramifed_alg_rs: Algebra.FormallyUnramified R S := by
        rw [← ϕ_S_R_map] at unramified_ϕ; exact unramified_ϕ;
      have local_ϕ : IsLocalHom (algebraMap R S) := by
        refine RingHom.IsIntegral.isLocalHom ?_ ?_
        exact RingHom.IsIntegral.of_finite hfin
        exact hinj
      have fin_R_S : Algebra.EssFiniteType R S :=
        RingHom.FiniteType.essFiniteType (RingHom.FiniteType.of_finite hfin)
      apply Algebra.FormallyUnramified.map_maximalIdeal


    /-  (Task 2)lemma packaging sentence 2 and first part of sentence 3 from Lemma 3.2
    hypotheses: TBD
    result: R/mr-> S/ms separable
    -/
    have induced_algebra : Algebra (R ⧸ mr) (S ⧸ms) := by
      sorry
    have separable_of_induced_map : Algebra.IsSeparable (R ⧸ mr) (S ⧸ ms) := by
      sorry



    /- () lemma packaging last part of sentence 3 + sentence 4 from Lemma 3.2
    hypotheses: TBD
    result: R/mr-> S/ms = R/mr[beta0] and the minimal polynomial f0 is separable
    -/




    sorry




/-  lemma packaging last part of sentence 3 + sentence 4 from Lemma 3.2
hypotheses: TBD
result: R/mr-> S/ms = R/mr[beta0] and the minimal polynomial f0 is separable
-/


/-  lemma packaging sentence 5 (displayed equation) from Lemma 3.2
hypotheses: TBD
result: If beta is a lift of beta0, then R[beta]/mr simeq S/ms
-/

/-  lemma packaging sentence 6  from Lemma 3.2, uses Nakayama
hypotheses: TBD
result: R[beta] = S
-/

/-  lemma packaging sentence 7 & 8 from Lemma 3.2
hypotheses: TBD
result: f'(beta) is not in ms
-/



/-
lemma lemma_3_2' (R S : Type)
  [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S]
  [Algebra R S] : let ϕ := algebraMap R S;
  ∃ β : S, (Algebra.adjoin ϕ.range {β} = S) ∧
  ∃ (f : Polynomial R) (fmon : f.Monic), Polynomial.eval β (Polynomial.map ϕ f) = 0 ∧
  (∀ (g : Polynomial R), Polynomial.eval β (Polynomial.map ϕ g) = 0 → f ∣ g) ∧
  IsUnit (Polynomial.eval β (Polynomial.map ϕ (Polynomial.derivative f))) := by
    let ϕ := algebraMap R S
    rcases IsLocalRing.maximal_ideal_unique R with ⟨mr, hmr⟩
    rcases IsLocalRing.maximal_ideal_unique S with ⟨ms, hms⟩
    have eq_max_prod : Ideal.span (ϕ '' mr)  = ms := by
      have unramified_ϕ: ϕ.FormallyUnramified := sorry
        --((RingHom.etale_iff_formallyUnramified_and_smooth ϕ).mp etale).1
      #check RingHom.FormallyUnramified ϕ
      #check RingHom.OfLocalizationSpanTarget
      --have unramifed_alg_rs: Algebra.FormallyUnramified R S := by sorry
      sorry




    sorry
  -/
