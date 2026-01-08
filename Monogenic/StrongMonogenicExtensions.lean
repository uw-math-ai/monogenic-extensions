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
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Polynomial.Eval.Algebra
import Mathlib.RingTheory.AdjoinRoot


open Polynomial
open Function
open RingHom

noncomputable section


variable (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
variable (φ : R →+* S)
instance : Algebra R S := RingHom.toAlgebra φ

def isMonogenicExtension [Algebra R S] : Prop :=
  ∃ f : R[X], Nonempty ((R[X] ⧸ Ideal.span {f}) ≃ₐ[R] S)

lemma Lemma_3_2_weak [Algebra R S]  (φ_fin : φ.Finite) (φ_inj : Injective φ) (etale : Etale φ) : isMonogenicExtension R S := by
  sorry


def isStrongMonogenicExtension [Algebra R S] : Prop :=
  ∃ f : R[X], ∃ ψ : ((R[X] ⧸ Ideal.span {f}) ≃ₐ[R] S),
    f.Monic ∧ (IsUnit (Polynomial.eval (ψ (Ideal.Quotient.mk (Ideal.span {f}) X)) (Polynomial.derivative ((Polynomial.map (algebraMap R S)) f))))

/-
An injective, finite, and etale ring homomorphism between local rings is strongly monogenic, i.e., there exists a monic polynomial f in R[X] such that S ≃ R[X]/(f) and the derivative of f is a unit in S.

PROVIDED SOLUTION:
        Since \(R\to S\) is \'etale and \(S\) is local, \(\frakm_R S = \frakm_S\). Furthermore, \'etale maps are preserved under base change, so \(R/\mm_R \to S\otimes R/\mm_R = S/\mm_S\) is \'etale. Thus, \(S/\mm_S\) is a separable extension of \(R/\mm_R\) %~\cite{stacks-project}*{\href{https://stacks.math.columbia.edu/tag/00U3}{Lemma 00U3}}
        so by the primitive element theorem %(see, e.g., \cite{LangAlgebra}*{Chapter V, Theorem 4.6})
        there exists a \(\beta_0\in S/\mm_S\) such that \(S/\mm_S = R/\mm_R[\beta_0]\) and whose minimal polynomial \(f_0(z)\in R/\mm_R[z]\) is separable. In particular, \(f'_0(\beta_0)\not\equiv 0 \bmod \mm_S\).  If \(\beta\in S\) is a lift of \(\beta_0\), then we have:
        \[
        R[\beta]/\mm_R \simeq (R/\mm_R)[\beta\bmod \mm_R S] = (R/\mm_R)[\beta\bmod \mm_S] = (R/\mm_R)[\beta_0] = S/\mm_S = S/\mm_RS.
        \]
        Thus, by Nakayama's lemma, \(R[\beta] = S\).  If \(f(z)\in R[z]\) denotes the minimal polynomial of \(\beta\), then \(f'(\beta)\bmod \mm_S= f_0'(\beta_0)\neq 0\). Therefore \(f'(\beta)\notin \mm_S\) and hence is a unit.
-/

lemma Lemma_3_2_strong [Algebra R S]  (φ_fin : φ.Finite) (φ_inj : Injective φ) (etale : Etale φ) : isStrongMonogenicExtension R S := by
  sorry
