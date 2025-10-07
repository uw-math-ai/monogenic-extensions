import Monogenic.Basic
import Mathlib

#eval Lean.versionString

#eval 3+4

#check IsLocalRing.maximal_ideal_unique


lemma lemma_3_2 (R S : Type)
  [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S]
  --[Algebra R S]
  (ϕ : R →+* S)
  (étale : RingHom.Etale ϕ) :
  ∃ β : S, (Algebra.adjoin ϕ.range {β} = S) ∧
            ∃ (f : Polynomial R) (fmon : f.Monic), Polynomial.eval β f = 0 ∧
            (∀ (g : Polynomial R), Polynomial.eval β g = 0 → f ∣ g) ∧
            IsUnit (Polynomial.eval β (ϕ (Polynomial.derivative f))) := by sorry
