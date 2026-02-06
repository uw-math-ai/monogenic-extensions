import Mathlib

universe u

open Polynomial
open Function
open RingHom
open IsLocalRing

namespace MathlibFix
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S]
-- aristotle llm: your version of mathlib is old and these properties are way
-- harder to derive with it, so I just give them to you to use.
-- however, they are true and follow from etaleness.
lemma formallyUnramified : Algebra.FormallyUnramified R S := by admit
lemma formallyEtale : Algebra.FormallyEtale R S := by admit
lemma formSmooth : Algebra.FormallySmooth R S := by admit
lemma finitePres : Algebra.FinitePresentation R S := by admit
lemma smooth : Algebra.Smooth R S := by admit

-- this theorem is already proven in another file
-- the proof uses primitive element theorem on the residue fields
-- and lifts the generator using nakayama's.
lemma monogenicTheorem [Module.Finite R S] [FaithfulSMul R S] [IsLocalRing R] [IsLocalRing S] :
  ∃(β : S), Algebra.adjoin R {β} = ⊤ := by admit

end MathlibFix

namespace Results

lemma nontrivial_of_local {R} [CommRing R] [IsLocalRing R] : Nontrivial R
  := ⟨⟨0, 1, fun h0 =>
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (Ideal.eq_top_of_isUnit_mem _ (IsLocalRing.maximalIdeal R).zero_mem
        (by rw [h0]; exact isUnit_one))⟩⟩

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

def isAdjoinRootMonic_ofAlgEquiv (f : R[X]) (hmonic : f.Monic)
    (e : (R[X] ⧸ Ideal.span {f}) ≃ₐ[R] S) :
    IsAdjoinRootMonic S f := by
  let h₀ := AdjoinRoot.isAdjoinRootMonic f hmonic
  exact {
    map := e.toAlgHom.comp h₀.map
    map_surjective := e.surjective.comp h₀.map_surjective
    ker_map := by ext; simp [Ideal.mem_span_singleton]
    monic := hmonic
  }

theorem IsAdjoinRootMonic.powerBasis_minpolyGen_eq [Module.IsTorsionFree R S]
    [IsIntegrallyClosed R] [IsDomain R] [IsDomain S]
    (f : R[X]) (h : IsAdjoinRootMonic S f)
    [Nontrivial R] : h.powerBasis.minpolyGen = f := by
  rw [PowerBasis.minpolyGen_eq]
  have hker : RingHom.ker h.map = Ideal.span {minpoly R h.root} := by
    conv_lhs => rw [← h.aeval_root_eq_map]
    exact minpoly.ker_eval h.isIntegral_root
  have hspan : Ideal.span {f} = Ideal.span {minpoly R h.root} := by
    rw [← h.ker_map, hker]
  have hassoc : Associated f (minpoly R h.root) :=
    Ideal.span_singleton_eq_span_singleton.mp hspan
  exact (eq_of_monic_of_associated h.monic (minpoly.monic h.isIntegral_root) hassoc).symm

lemma minpoly_generates_of_isAdjoinRootMonic
    [IsIntegrallyClosed R] [Nontrivial R]
    [Module.IsTorsionFree R S] [IsDomain R] [IsDomain S]
    (f : R[X]) (hn : Nonempty <| IsAdjoinRootMonic S f) :
    ∃(β : S), Nonempty ((R[X] ⧸ Ideal.span {minpoly R β}) ≃ₐ[R] S) := by
  obtain ⟨h⟩ := hn
  refine ⟨h.root, ⟨?_⟩⟩
  let pb := h.powerBasis
  -- let equiv := h.adjoinRootAlgEquiv
  -- unfold AdjoinRoot at equiv
  have heq : minpoly R h.root = f := calc
    minpoly R h.root = minpoly R pb.gen := rfl
    _ = pb.minpolyGen := (PowerBasis.minpolyGen_eq pb).symm
    _ = f := IsAdjoinRootMonic.powerBasis_minpolyGen_eq f h
  rw [heq]
  exact h.adjoinRootAlgEquiv

lemma isAdjoinRootMonic_of_powerBasis [IsIntegrallyClosed R]
    [IsDomain R] [IsDomain S] [Module.IsTorsionFree R S] [Nontrivial R]
    (pb : PowerBasis R S) :
    ∃(f : R[X]), Nonempty (IsAdjoinRootMonic S f) := by
  have hgen_int : IsIntegral R pb.gen := pb.isIntegral_gen
  have hgen_monic : (minpoly R pb.gen).Monic := minpoly.monic hgen_int
  refine ⟨minpoly R pb.gen, ⟨{
    map := aeval pb.gen
    map_surjective := by
      have h := pb.adjoin_gen_eq_top
      rw [Algebra.adjoin_singleton_eq_range_aeval] at h
      intro x
      have hx : x ∈ (aeval pb.gen : R[X] →ₐ[R] S).range := by simp [h]
      exact (AlgHom.mem_range (φ := aeval pb.gen)).mp hx
    ker_map := minpoly.ker_eval hgen_int
    monic := hgen_monic
  }⟩⟩


#check Algebra.adjoin

variable [Module.Finite R S]

lemma integral : Algebra.IsIntegral R S := inferInstance

variable [Algebra.Etale R S] [FaithfulSMul R S] [IsLocalRing S] [IsLocalRing R] [IsDomain S]

omit [Module.Finite R S] [Algebra.Etale R S] [IsLocalRing S] in
lemma torsionFree : Module.IsTorsionFree R S := inferInstance

#check Algebra.IsIntegral.isIntegral
#check IsAdjoinRootMonic.mkOfAdjoinEqTop

end Results

-- Find a counterexample: étale extension with a generator but no PowerBasis.
-- This can be VERY HARD so finish the equivs first.
theorem counterexample : ∃(R S : Type u)
    (_ : CommRing R) (_ : CommRing S) (_ : Algebra R S) (_ : Algebra.Etale R S)
    (_ : Module.Finite R S) (_ : FaithfulSMul R S) (_ : IsDomain R) (_ : IsDomain S)
    (_ : IsLocalRing R) (_ : IsLocalRing S),
    IsEmpty (PowerBasis R S) := by sorry

/-
if we have [Module.IsTorsionFree R S], [IsDomain R], [IsDomain S], and
[IsIntegrallyClosed R], then all of the following statements are equivalent.

1) PowerBasis R S
2) ∃(β : S), Algebra.adjoin R {β} = ⊤
3) ∃(f : R[X]), IsAdjoinRootMonic S f
     ∃(f : R[X]), f.Monic ∧ Nonempty (R[X] ⧸ Ideal.span {f}) ≃ₐ[R] S)
4) ∃(f : R[X]), IsAdjoinRoot S f
     ∃(f : R[X]), Nonempty (R[X] ⧸ Ideal.span {f}) ≃ₐ[R] S)
5) ∃(β : S), Nonempty (R[X] ⧸ Ideal.span {minpoly R β}) ≃ₐ[R] S)
-/
