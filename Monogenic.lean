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


#eval Lean.versionString

#eval 3+4




lemma lemma_3_2 (R S : Type)
  [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S]
  (ϕ : R →+* S) (hfin : ϕ.Finite)(hinj: Function.Injective ϕ)
  (etale : RingHom.Etale ϕ) :
  ∃ β : S, (Algebra.adjoin ϕ.range {β} = S) ∧
  ∃ (f : Polynomial R) (fmon : f.Monic), Polynomial.eval β (Polynomial.map ϕ f) = 0 ∧
  (∀ (g : Polynomial R), Polynomial.eval β (Polynomial.map ϕ g) = 0 → f ∣ g) ∧
  IsUnit (Polynomial.eval β (Polynomial.map ϕ (Polynomial.derivative f))) := by
    rcases IsLocalRing.maximal_ideal_unique R with ⟨mr, hmr⟩
    rcases IsLocalRing.maximal_ideal_unique S with ⟨ms, hms⟩
    have eq_max_prod : Ideal.map ϕ mr  = ms := by
      have unramified_ϕ: ϕ.FormallyUnramified :=
        ((RingHom.etale_iff_formallyUnramified_and_smooth ϕ).mp etale).1
      let S_is_R_algebra : Algebra R S := RingHom.toAlgebra ϕ
      have ϕ_S_R_map : algebraMap R S = ϕ :=
        RingHom.algebraMap_toAlgebra ϕ
      have unramifed_alg_rs: Algebra.FormallyUnramified R S := by
        rw [← ϕ_S_R_map] at unramified_ϕ
        exact unramified_ϕ;
      have local_ϕ : IsLocalHom ϕ := by
        refine RingHom.IsIntegral.isLocalHom ?_ ?_
        exact RingHom.IsIntegral.of_finite hfin
        exact hinj





      sorry
    sorry



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
