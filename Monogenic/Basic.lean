import Mathlib

universe u

open Polynomial
open Function
open RingHom

/-!

# Monogenic Extensions

We say that a ring homomorphism φ : R →+* S is a monogenic extension if there exists a polynomial f ∈ R[X] and an R-algebra isomorphism S ≃ R[X]/(f).

We show in `isMonogenicExtension_iff` that this is equivalent to the existence of f ∈ R[X] and β ∈ S such that the map R[X] → S, X ↦ β is surjective with kernel (f) with the formulation matching `Lemma_3_2` in `Mongenic.lean`.

To add
* definition of strong monogenic extension requiring that $f$ is monic and that $f'(β)$ is a unit
* analogous equivalence for strong monogenic extension

# Use of AI 
The definitions and statements were mostly written by me with assistance from Claude 3.5 Sonnet within the Cursor Copilot. 

The proof of `isMonogenicExtension_iff` was generated using Claude Code with some assistance from Gemini CLI.  In this workflow, I both prompted the models and tweaked the generated code. 
-/

variable {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

def isMonogenicExtension (φ : R →+* S) : Prop :=
  /-Let's instruct Lean to view S as an R-algebra via φ.
  The following is a shortcut for letI : Algebra R S := RingHom.toAlgebra -/
  let _ := RingHom.toAlgebra φ
  /-∃ f such that S ≃ R[X]/(f)-/
  ∃ f : R[X], Nonempty ((R[X] ⧸ Ideal.span {f}) ≃ₐ[R] S)

/-An equivalent defintion of isMonogenicExtension:
  ∃ β ∈ S such that R[X] → S, X ↦ β is surjective with kernel (f)
-/
lemma isMonogenicExtension_iff (φ : R →+* S) : isMonogenicExtension φ ↔ ∃ β : S, (Algebra.adjoin φ.range {β} = ⊤) ∧
  ∃ (f : R[X]), Polynomial.eval β (Polynomial.map φ f) =
  0 ∧ (∀ (g : Polynomial R), Polynomial.eval β (Polynomial.map φ g) = 0 → f ∣ g) := by
  letI : Algebra R S := RingHom.toAlgebra φ
  have halg : algebraMap R S = φ := rfl
  -- Key observation: eval β (map φ g) = aeval β g when algebraMap R S = φ
  have eval_eq_aeval : ∀ (β : S) (g : R[X]), eval β (map φ g) = aeval β g := fun β g => by
    simp only [aeval_def, eval₂_eq_eval_map, halg]
  constructor
  · -- Forward direction: isMonogenicExtension φ → ∃ β ...
    intro ⟨f, ⟨e⟩⟩
    -- e : (R[X] ⧸ Ideal.span {f}) ≃ₐ[R] S
    -- Let β be the image of the root
    let mk : R[X] →ₐ[R] (R[X] ⧸ Ideal.span {f}) := Ideal.Quotient.mkₐ R (Ideal.span {f})
    let β : S := e (mk X)
    use β
    constructor
    · -- Show Algebra.adjoin φ.range {β} = ⊤
      rw [eq_top_iff]
      intro s _
      obtain ⟨q, rfl⟩ := e.surjective s
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
      induction p using Polynomial.induction_on with
      | C r =>
        -- e (mk (C r)) = e (algebraMap R _ r) = algebraMap R S r = φ r
        have heC : e ((Ideal.Quotient.mk (Ideal.span {f})) (C r)) = φ r := by
          -- C r = algebraMap R R[X] r, so mk (C r) = algebraMap R (R[X]/I) r
          have h1 : C r = algebraMap R R[X] r := rfl
          rw [h1]
          -- mk ∘ algebraMap R R[X] = algebraMap R (R[X]/I)
          have h2 : (Ideal.Quotient.mk (Ideal.span {f})) (algebraMap R R[X] r) =
                    algebraMap R (R[X] ⧸ Ideal.span {f}) r := rfl
          rw [h2, AlgEquiv.commutes, halg]
        rw [heC]
        have hr : φ r ∈ φ.range := Set.mem_range_self r
        exact Subalgebra.algebraMap_mem (Algebra.adjoin (↥φ.range) {β}) ⟨φ r, hr⟩
      | add p₁ p₂ hp₁ hp₂ =>
        rw [map_add, map_add]
        exact Subalgebra.add_mem _ (hp₁ trivial) (hp₂ trivial)
      | monomial n r _ =>
        -- e (mk (C r * X^(n+1))) = φ r * β^(n+1)
        rw [map_mul, map_mul, map_pow, map_pow]
        apply Subalgebra.mul_mem
        · have heC : e ((Ideal.Quotient.mk (Ideal.span {f})) (C r)) = φ r := by
            have h1 : C r = algebraMap R R[X] r := rfl
            rw [h1]
            have h2 : (Ideal.Quotient.mk (Ideal.span {f})) (algebraMap R R[X] r) =
                      algebraMap R (R[X] ⧸ Ideal.span {f}) r := rfl
            rw [h2, AlgEquiv.commutes, halg]
          rw [heC]
          have hr : φ r ∈ φ.range := Set.mem_range_self r
          exact Subalgebra.algebraMap_mem (Algebra.adjoin (↥φ.range) {β}) ⟨φ r, hr⟩
        · apply Subalgebra.pow_mem
          have hβ : e ((Ideal.Quotient.mk (Ideal.span {f})) X) = β := rfl
          rw [hβ]
          exact Algebra.self_mem_adjoin_singleton (↥φ.range) β
    · use f
      constructor
      · -- f(β) = 0: Since mk f = 0 in the quotient, e(mk f) = 0
        rw [eval_eq_aeval]
        have hmk : mk f = 0 := by
          simp only [mk, Ideal.Quotient.mkₐ_eq_mk]
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
        -- aeval (mk X) f = mk f (quotient map is the evaluation at mk X)
        have haeval : aeval (mk X) f = mk f := by
          have hmk_aeval : mk = Polynomial.aeval (mk X) := by
            apply AlgHom.ext_iff.mpr
            intro p
            induction p using Polynomial.induction_on with
            | C r =>
              simp only [mk, Ideal.Quotient.mkₐ_eq_mk, aeval_C]
              rfl
            | add p q hp hq =>
              simp only [map_add, hp, hq]
            | monomial n r _ =>
              simp only [map_mul, map_pow, mk, Ideal.Quotient.mkₐ_eq_mk, aeval_X, aeval_C, pow_succ]
              congr 1
          exact congrFun (congrArg DFunLike.coe hmk_aeval.symm) f
        -- e preserves aeval: aeval (e x) = e ∘ aeval x
        have hcomm : aeval (e (mk X)) f = e (aeval (mk X) f) := by
          have h := aeval_algEquiv e (mk X)
          exact congrFun (congrArg DFunLike.coe h) f
        calc aeval β f = aeval (e (mk X)) f := rfl
          _ = e (aeval (mk X) f) := hcomm
          _ = e (mk f) := by rw [haeval]
          _ = e 0 := by rw [hmk]
          _ = 0 := map_zero e
      · -- f divides all g with g(β) = 0
        intro g hg
        rw [eval_eq_aeval] at hg
        have haeval_g : aeval (mk X) g = mk g := by
          have hmk_aeval : mk = Polynomial.aeval (mk X) := by
            apply AlgHom.ext_iff.mpr
            intro p
            induction p using Polynomial.induction_on with
            | C r =>
              simp only [mk, Ideal.Quotient.mkₐ_eq_mk, aeval_C]
              rfl
            | add p q hp hq =>
              simp only [map_add, hp, hq]
            | monomial n r _ =>
              simp only [map_mul, map_pow, mk, Ideal.Quotient.mkₐ_eq_mk, aeval_X, aeval_C, pow_succ]
              congr 1
          exact congrFun (congrArg DFunLike.coe hmk_aeval.symm) g
        have hcomm_g : aeval (e (mk X)) g = e (aeval (mk X) g) := by
          have h := aeval_algEquiv e (mk X)
          exact congrFun (congrArg DFunLike.coe h) g
        have hg' : e (mk g) = 0 := by
          calc e (mk g) = e (aeval (mk X) g) := by rw [haeval_g]
            _ = aeval (e (mk X)) g := hcomm_g.symm
            _ = aeval β g := rfl
            _ = 0 := hg
        have hmk_g : mk g = 0 := by
          rw [← map_zero e] at hg'
          exact e.injective hg'
        have hg_mem : g ∈ Ideal.span {f} := by
          simp only [mk, Ideal.Quotient.mkₐ_eq_mk] at hmk_g
          exact Ideal.Quotient.eq_zero_iff_mem.mp hmk_g
        exact (Ideal.mem_span_singleton.mp hg_mem)
  · -- Backward direction: ∃ β ... → isMonogenicExtension φ
    intro ⟨β, hβ_gen, f, hf_zero, hf_div⟩
    use f
    rw [eval_eq_aeval] at hf_zero
    -- Construct lift: (R[X] ⧸ Ideal.span {f}) →ₐ[R] S
    have hker : ∀ p ∈ Ideal.span {f}, aeval β p = 0 := by
      intro p hp
      rw [Ideal.mem_span_singleton] at hp
      obtain ⟨q, hq⟩ := hp
      simp only [hq, map_mul, hf_zero, zero_mul]
    let lift_hom : (R[X] ⧸ Ideal.span {f}) →ₐ[R] S :=
      Ideal.Quotient.liftₐ (Ideal.span {f}) (Polynomial.aeval β) hker
    -- Build the AlgEquiv
    have lift_bij : Function.Bijective lift_hom := by
      constructor
      · -- Injectivity: kernel is trivial
        rw [injective_iff_map_eq_zero]
        intro x hx
        obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
        simp only [lift_hom, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk] at hx
        -- So aeval β p = 0, which means eval β (map φ p) = 0
        have hx' : eval β (map φ p) = 0 := by rw [eval_eq_aeval]; exact hx
        -- By hf_div, f ∣ p
        have hdiv := hf_div p hx'
        simp only [Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_span_singleton.mpr hdiv
      · -- Surjectivity from hβ_gen
        -- hβ_gen : Algebra.adjoin φ.range {β} = ⊤ means S = R[β] (polynomials in β)
        -- lift_hom sends mk p ↦ aeval β p, i.e., p̄ ↦ p(β)
        -- Since every element of S is a polynomial in β (by hβ_gen), lift_hom is surjective
        intro s
        -- s is in Algebra.adjoin φ.range {β} since it equals ⊤
        have hs : s ∈ Algebra.adjoin φ.range {β} := by rw [hβ_gen]; trivial
        -- Use induction on the adjoin structure to find a polynomial
        induction hs using Algebra.adjoin_induction with
        | mem x hx =>
          -- x ∈ {β}, so x = β
          simp only [Set.mem_singleton_iff] at hx
          rw [hx]
          -- β = aeval β X, so use mk X
          use Ideal.Quotient.mk (Ideal.span {f}) X
          simp only [lift_hom, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
          exact aeval_X β
        | algebraMap r =>
          -- r ∈ φ.range, so r = φ r' for some r' : R
          obtain ⟨r', hr'⟩ := r.property
          -- φ r' = aeval β (C r'), so use mk (C r')
          use Ideal.Quotient.mk (Ideal.span {f}) (C r')
          simp only [lift_hom, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
          -- Goal: (aeval β) (C r') = (algebraMap φ.range S) r
          -- aeval β (C r') = algebraMap R S r' = φ r' (by aeval_C and halg)
          -- (algebraMap φ.range S) r = ↑r = φ r' (by hr')
          show (aeval β) (C r') = (algebraMap φ.range S) r
          have h1 : (aeval β) (C r') = algebraMap R S r' := aeval_C β r'
          have h2 : algebraMap R S r' = φ r' := halg ▸ rfl
          have h3 : (algebraMap φ.range S) r = ↑r := by
            simp only [Algebra.algebraMap_eq_smul_one, Subring.smul_def, smul_eq_mul, mul_one]
          rw [h1, h2, h3, hr']
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
    exact ⟨AlgEquiv.ofBijective lift_hom lift_bij⟩
