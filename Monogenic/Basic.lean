import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
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

/-An equivalent defintion of isMonogenicExtension:
  ∃ β ∈ S such that R[X] → S, X ↦ β is surjective with kernel (f)
-/
lemma monogenic_of_univQuot
    (hiso : ∃ f : R[X], Nonempty ((R[X] ⧸ Ideal.span {f}) ≃ₐ[R] S)) :
    ∃ β : S, (Algebra.adjoin R {β} = ⊤) := by
  -- Forward direction: isMonogenicExtension φ → ∃ β ...
  obtain ⟨f, ⟨e⟩⟩ := hiso
  let φ := algebraMap R S
  -- e : (R[X] ⧸ Ideal.span {f}) ≃ₐ[R] S
  -- Let β be the image of the root
  let mk : R[X] →ₐ[R] (R[X] ⧸ Ideal.span {f}) := Ideal.Quotient.mkₐ R (Ideal.span {f})
  let β : S := e (mk X)
  use β
  rw [eq_top_iff]
  intro s _
  obtain ⟨q, rfl⟩ := e.surjective s
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  -- e (mk (C r)) = e (algebraMap R _ r) = algebraMap R S r = φ r
  have heC (r : R): e ((Ideal.Quotient.mk (Ideal.span {f})) (C r)) = φ r := by
    -- C r = algebraMap R R[X] r, so mk (C r) = algebraMap R (R[X]/I) r
    have h1 : C r = algebraMap R R[X] r := rfl
    rw [h1]
    -- mk ∘ algebraMap R R[X] = algebraMap R (R[X]/I)
    have h2 : (Ideal.Quotient.mk (Ideal.span {f})) (algebraMap R R[X] r)
      = algebraMap R (R[X] ⧸ Ideal.span {f}) r := rfl
    rw [h2, AlgEquiv.commutes]
  induction p using Polynomial.induction_on with
  | C r =>
    rw [heC]
    exact Subalgebra.algebraMap_mem (Algebra.adjoin R {β}) r
  | add p₁ p₂ hp₁ hp₂ =>
    rw [map_add, map_add]
    exact Subalgebra.add_mem _ (hp₁ trivial) (hp₂ trivial)
  | monomial n r _ =>
    -- e (mk (C r * X^(n+1))) = φ r * β^(n+1)
    rw [map_mul, map_mul, map_pow, map_pow]
    apply Subalgebra.mul_mem
    · rw [heC]
      exact Subalgebra.algebraMap_mem (Algebra.adjoin R {β}) r
    · apply Subalgebra.pow_mem
      have hβ : e ((Ideal.Quotient.mk (Ideal.span {f})) X) = β := rfl
      rw [hβ]
      exact Algebra.self_mem_adjoin_singleton R β

def isAdjoinRoot_ofAlgEquiv (f : R[X])
    (e : (R[X] ⧸ Ideal.span {f}) ≃ₐ[R] S) :
    IsAdjoinRoot S f := by
  let h₀ := AdjoinRoot.isAdjoinRoot f
  exact {
    map := e.toAlgHom.comp h₀.map
    map_surjective := e.surjective.comp h₀.map_surjective
    ker_map := by ext; simp [Ideal.mem_span_singleton]
  }

lemma monogenic_of_surjective_map (f : R[X] →ₐ[R] S) (hsurj : Function.Surjective f) :
    ∃(β : S), Algebra.adjoin R {β} = ⊤ := by
  use f X
  rw [eq_top_iff]
  intro s _
  obtain ⟨p, rfl⟩ := hsurj s
  have algebraMap_C (r : R): f (C r) = algebraMap R S r := by
    have test : algebraMap R R[X] r = C r := by rfl
    rw [← test, AlgHom.commutes]
  induction p using Polynomial.induction_on with
  | C r =>
    rw [algebraMap_C]
    exact Subalgebra.algebraMap_mem (Algebra.adjoin R {f X}) r
  | add p₁ p₂ hp₁ hp₂ =>
    rw [map_add]
    exact Subalgebra.add_mem _ (hp₁ trivial) (hp₂ trivial)
  | monomial n r _ =>
    rw [map_mul, map_pow, algebraMap_C]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ r)
      (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton R (f X)) _)

lemma surjective_map_of_monogenic (β : S) (adjoin_eq_top : Algebra.adjoin R {β} = ⊤) :
    ∃(f : R[X] →ₐ[R] S), Function.Surjective f := by
  use aeval β
  intro b
  have hb : b ∈ Algebra.adjoin R {β} := adjoin_eq_top ▸ trivial
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact ⟨X, aeval_X β⟩
  | algebraMap r =>
    use (C r)
    change (aeval β) (C r) = (algebraMap R S) r
    simp
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

end Monogenic
