import Mathlib.RingTheory.IsAdjoinRoot

open Polynomial
open Function
open RingHom

/-!

# Monogenic Extensions

We say that a ring homomorphism φ : R →+* S is a monogenic extension
if there exists a polynomial f ∈ R[X] and an R-algebra isomorphism S ≃ R[X]/(f).

We show in `isMonogenicExtension_iff` that this is equivalent to the existence of
f ∈ R[X] and β ∈ S such that the map R[X] → S, X ↦ β is surjective with
kernel (f) with the formulation matching `Lemma_3_2` in `Mongenic.lean`.

To add
* definition of strong monogenic extension requiring that $f$ is monic
  and that $f'(β)$ is a unit
* analogous equivalence for strong monogenic extension

# Use of AI
The definitions and statements were mostly written by me with assistance
from Claude 3.5 Sonnet within the Cursor Copilot.

The proof of `isMonogenicExtension_iff` was generated using Claude Code with some
assistance from Gemini CLI.  In this workflow, I both prompted the models
and tweaked the generated code.
-/

namespace Monogenic
variable {R S} [CommRing R] [CommRing S] [Algebra R S]

noncomputable def _isAdjoinRoot_ofAlgEquiv (f : R[X])
    (e : (R[X] ⧸ Ideal.span {f}) ≃ₐ[R] S) :
    IsAdjoinRoot S f := IsAdjoinRoot.ofAdjoinRootEquiv e

/-An equivalent defintion of isMonogenicExtension:
  ∃ β ∈ S such that R[X] → S, X ↦ β is surjective with kernel (f)
-/
-- already in mathlib: compose IsAdjoinRoot.ofAdjoinRootEquiv
lemma _monogenic_of_univQuot
    (hiso : ∃ f : R[X], Nonempty ((R[X] ⧸ Ideal.span {f}) ≃ₐ[R] S)) :
    ∃ β : S, (Algebra.adjoin R {β} = ⊤) := by
  let ⟨f, ⟨e⟩⟩ := hiso
  let adj := IsAdjoinRoot.ofAdjoinRootEquiv e
  exact ⟨adj.root, adj.adjoin_root_eq_top⟩


-- Both lemmas follow from Algebra.adjoin_singleton_eq_range_aeval:
--   adjoin R {x} = (aeval x).range
lemma _monogenic_of_surjective_map (f : R[X] →ₐ[R] S) (hsurj : Function.Surjective f) :
    Algebra.adjoin R {f X} = ⊤ := by
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top]
  intro s; obtain ⟨p, hp⟩ := hsurj s
  exact ⟨p, by simp [aeval_algHom_apply f, hp]⟩

lemma _surjective_map_of_monogenic (β : S) (adjoin_eq_top : Algebra.adjoin R {β} = ⊤) :
    Function.Surjective (aeval (R:=R) β) := by
  rwa [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top] at adjoin_eq_top

end Monogenic
