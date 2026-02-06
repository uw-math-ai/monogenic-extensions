/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bianca Viray, Bryan Boehnke, Grant Yang, George Peykanu, Tianshuo Wang
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IsAdjoinRoot

/-!
# Monogenic Extensions

We say that a ring homomorphism `φ : R →+* S` is a monogenic extension if there exists a
polynomial `f ∈ R[X]` and an `R`-algebra isomorphism `S ≃ₐ[R] R[X]/(f)`.

## Main results

- `algEquiv_quotient_C`: the quotient map composed with an algebra equivalence sends constant
  polynomials to their images under the structure map.
- `monogenic_of_univQuot`: if `S ≃ₐ[R] R[X]/(f)` for some `f`, then there exists `β ∈ S` such
  that `Algebra.adjoin R {β} = ⊤`.

## References

We show in `isMonogenicExtension_iff` that this is equivalent to the existence of
`f ∈ R[X]` and `β ∈ S` such that the map `R[X] → S, X ↦ β` is surjective with
kernel `(f)`.

## Implementation notes

- Strong monogenic extensions (requiring `f` monic with `f'(β)` a unit) are not yet defined.
-/

open Polynomial
open Function
open RingHom

namespace Monogenic
variable {R S} [CommRing R] [CommRing S] [Algebra R S]

/-- The quotient map composed with an algebra equivalence sends constant polynomials
    to their images under the structure map. -/
lemma algEquiv_quotient_C {f : R[X]} (e : (R[X] ⧸ Ideal.span {f}) ≃ₐ[R] S) (r : R) :
    e ((Ideal.Quotient.mk (Ideal.span {f})) (C r)) = algebraMap R S r :=
  AlgEquiv.commutes e r

lemma monogenic_of_univQuot
    (hiso : ∃ f : R[X], Nonempty ((R[X] ⧸ Ideal.span {f}) ≃ₐ[R] S)) :
    ∃ β : S, (Algebra.adjoin R {β} = ⊤) := by
  obtain ⟨f, ⟨e⟩⟩ := hiso
  let β : S := e ((Ideal.Quotient.mkₐ R (Ideal.span {f})) X)
  use β
  rw [eq_top_iff]
  intro s _
  obtain ⟨q, rfl⟩ := e.surjective s
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  induction p using Polynomial.induction_on with
  | C r =>
    rw [algEquiv_quotient_C]
    exact Subalgebra.algebraMap_mem (Algebra.adjoin R {β}) r
  | add p₁ p₂ hp₁ hp₂ =>
    rw [map_add, map_add]
    exact Subalgebra.add_mem _ (hp₁ trivial) (hp₂ trivial)
  | monomial n r _ =>
    rw [map_mul, map_mul, map_pow, map_pow, algEquiv_quotient_C]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ r)
      (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton R β) _)

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

lemma surj_fun_of_monogenic (β : S) (adjoin_eq_top : Algebra.adjoin R {β} = ⊤) :
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
