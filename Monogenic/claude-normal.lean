import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.AdjoinRoot

open Polynomial
open Function
open RingHom

class Monogenic (R : Type*) (S : Type*) [CommSemiring R] [Semiring S] [Algebra R S] : Prop where
  exists_adjoin_eq_top : ∃(β : S), Algebra.adjoin R {β} = ⊤

structure GeneratesUnivQuot (R : Type*) (S : Type*) (β : S)
    [CommRing R] [Ring S] [Algebra R S] : Prop where
  integral : IsIntegral R β
  iso : Nonempty ((R[X] ⧸ Ideal.span {minpoly R β}) ≃ₐ[R] S)
  derivUnit : IsUnit (aeval β (minpoly R β).derivative)

class UnivQuotient (R : Type*) (S : Type*)
    [CommRing R] [Ring S] [Algebra R S] : Prop where
  minpoly_iso : ∃(β : S), GeneratesUnivQuot R S β

namespace Monogenic

variable {R S} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

/-
initial part without the integral domain hypothesis.
for the statement about the isomorphism with the quotient ring,
see isIntegrallyClosed_existsPolyQuotIso below
(idk, cant come up with a name. i think these new names are roughly
mathlib convention? i tried.)

see FaithfulSMul.iff_algebraMapInjective below for a proof its equivalent
to asserting that phi is injective.
-/
lemma if_finiteInjectiveEtale [Algebra R S] [FaithfulSMul R S]
  [Module.Finite R S] [Algebra.Etale R S] :
    Monogenic R S := by
  -- Key: maximal ideal maps to maximal ideal (from Mathlib's unramified local ring theory)
  have eq_max : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal S :=
    Algebra.FormallyUnramified.map_maximalIdeal
  -- Primitive element theorem: ∃ β₀ such that k_R⟮β₀⟯ = k_S
  obtain ⟨β₀, hβ₀⟩ := Field.exists_primitive_element (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField S)
  -- Lift β₀ to β in S via the quotient map
  obtain ⟨β, hβ⟩ := Ideal.Quotient.mk_surjective β₀
  -- φ finite implies S is integral over R
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  -- The key claim: Algebra.adjoin R {β} = ⊤
  -- This follows from Nakayama's lemma: since the image of adjoin R {β} in S/m_S
  -- equals k_R⟮β₀⟯ = k_S (by primitive element theorem and the lift), and S is
  -- finitely generated over R, we get adjoin R {β} = S.
  let S' := Algebra.adjoin R {β}
  have adjoin_eq_top : S' = ⊤ := by
    -- The intermediate field k_R⟮β₀⟯ = ⊤ means β₀ generates k_S over k_R
    -- Since β₀ is algebraic (k_S is finite over k_R), the subalgebra equals the intermediate field
    have h_alg_β₀ : IsAlgebraic (IsLocalRing.ResidueField R) β₀ :=
      Algebra.IsAlgebraic.isAlgebraic β₀
    -- Use the fact that IntermediateField.adjoin K {α} has
    -- toSubalgebra = Algebra.adjoin K {α} when α is algebraic
    have h_subalg := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic h_alg_β₀
    -- Now k_R⟮β₀⟯ = ⊤ implies Algebra.adjoin k_R {β₀} = ⊤
    have h_adjoin_top : Algebra.adjoin (IsLocalRing.ResidueField R) {β₀} = ⊤ := by
      rw [← h_subalg, hβ₀, IntermediateField.top_toSubalgebra]
    let mR := IsLocalRing.maximalIdeal R
    have h_mS : mR • (⊤ : Submodule R S) = (IsLocalRing.maximalIdeal S).restrictScalars R := by
      rw [Ideal.smul_top_eq_map, Algebra.FormallyUnramified.map_maximalIdeal]
    -- Parameters for le_of_le_smul_of_le_jacobson_bot
    have h_fg : (⊤ : Submodule R S).FG := Module.finite_def.mp inferInstance
    have h_jac : mR ≤ Ideal.jacobson ⊥ := IsLocalRing.maximalIdeal_le_jacobson ⊥
    -- S ⊆ S' + mR • S
    have h_le_sup : (⊤ : Submodule R S) ≤ S'.toSubmodule ⊔ mR • ⊤ := by
      -- Prove every s is in the sup by lifting from the residue field...
      intro s _
      -- 1. Identify s₀ in the residue field k_S
      let s₀ := IsLocalRing.residue S s
      -- 2. Use the fact that k_R⟮β₀⟯ = ⊤ implies Algebra.adjoin kR {β₀} = ⊤
      -- (Since the extension is finite, the intermediate field is the subalgebra)
      have hs₀ : s₀ ∈ Algebra.adjoin (IsLocalRing.ResidueField R) {β₀} := by
        rw [h_adjoin_top]; trivial
      -- aristotle proof:
      simp +zetaDelta only [IntermediateField.adjoin_eq_top_iff,
        IntermediateField.adjoin_toSubalgebra, Ideal.smul_top_eq_map, Submodule.restrictScalars_inj,
        Submodule.mem_top] at *;
      -- Since $s₀$ is in the adjoin of $\beta₀$ over the residue field,
      -- there exists some $t \in \text{adjoin } R \{β\}$ such that $s - t \in m_S$.
      obtain ⟨t, ht⟩ : ∃ t ∈ Algebra.adjoin R {β},
          s - t ∈ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) := by
        -- Since $s₀$ is in the adjoin of $β₀$ over the residue field,
        -- there exists some $t₀ \in \text{adjoin } R \{β\}$ such that $s₀ = \text{residue } S(t₀)$.
        obtain ⟨t₀, ht₀⟩ : ∃ t₀ ∈ Algebra.adjoin R {β},
            IsLocalRing.residue S s = IsLocalRing.residue S t₀ := by
          refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hs₀
          · exact fun x hx => ⟨ β, Algebra.subset_adjoin <| Set.mem_singleton _, by aesop ⟩
          · intro r
            obtain ⟨ r, rfl ⟩ := Ideal.Quotient.mk_surjective r
            exact ⟨ algebraMap R S r, Subalgebra.algebraMap_mem _ _, rfl ⟩
          · rintro x y hx hy ⟨ t₀, ht₀, rfl ⟩ ⟨ t₁, ht₁, rfl ⟩
            exact ⟨ t₀ + t₁, Subalgebra.add_mem _ ht₀ ht₁, by simp +decide ⟩
          · rintro x y hx hy ⟨ t₀, ht₀, rfl ⟩ ⟨ t₁, ht₁, rfl ⟩
            exact ⟨ t₀ * t₁, Subalgebra.mul_mem _ ht₀ ht₁, by simp +decide ⟩
        exact ⟨ t₀, ht₀.1, by rw [ h_mS ] ; exact Ideal.Quotient.eq.mp ht₀.2 ⟩;
      exact Submodule.mem_sup.mpr ⟨ t, ht.1, s - t, ht.2, by simp +decide ⟩
    -- Apply the lemma directly to get ⊤ ≤ S'
    have h_top_le : (⊤ : Submodule R S) ≤ S'.toSubmodule :=
      Submodule.le_of_le_smul_of_le_jacobson_bot h_fg h_jac h_le_sup
    -- Result: S' = ⊤
    exact eq_top_iff.mpr h_top_le
  exact ⟨β, adjoin_eq_top⟩

/-!
## Helper lemmas for the derivative unit condition

The key fact from Lemma 3.2 of arXiv:2503.07846 is that for a finite étale extension of local rings,
the derivative of the minimal polynomial evaluated at the generator is a unit.

The proof proceeds through the residue fields:
1. Étale ⟹ residue field extension k_R → k_S is separable
2. For separable extensions, the minimal polynomial is separable
3. Separable polynomial ⟹ derivative at root is non-zero
4. Non-zero in residue field ⟹ unit in local ring
-/

section DerivativeUnit

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
variable [Algebra R S] [IsLocalHom (algebraMap R S)]

/-- In a local ring, an element is a unit iff its residue is non-zero. -/
lemma isUnit_of_residue_ne_zero {s : S} (h : IsLocalRing.residue S s ≠ 0) : IsUnit s := by
  rw [ne_eq, IsLocalRing.residue_eq_zero_iff] at h
  exact IsLocalRing.notMem_maximalIdeal.mp h

/-- The residue of aeval β p equals eval₂ applied to the residues.

    Note: The composition (residue S) ∘ (algebraMap R S) factors through residue R
    when we have IsLocalHom (algebraMap R S), giving us a map k_R → k_S. -/
lemma residue_aeval_eq (β : S) (p : R[X]) :
    IsLocalRing.residue S (aeval β p) =
    p.eval₂ ((IsLocalRing.residue S).comp (algebraMap R S)) (IsLocalRing.residue S β) := by
  rw [aeval_def]
  exact hom_eval₂ p (algebraMap R S) (IsLocalRing.residue S) β

/-- For étale extensions of local rings, the residue field extension is separable.
    This is an instance in Mathlib: `Algebra.FormallyUnramified R S` implies
    `Algebra.IsSeparable (ResidueField R) (ResidueField S)`. -/
lemma residueField_isSeparable_of_etale [Algebra.Etale R S] [Algebra.EssFiniteType R S] :
    Algebra.IsSeparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) := by
  haveI : Algebra.FormallyUnramified R S := inferInstance
  exact inferInstance

/-- The residue field map from R to k_S factors as R → k_R → k_S. -/
lemma residue_algebraMap_eq :
    (IsLocalRing.residue S).comp (algebraMap R S) =
    (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)).comp
      (IsLocalRing.residue R) := by
  ext r
  simp only [RingHom.comp_apply]
  -- This follows from the fact that algebraMap R S is a local hom,
  -- so it induces a map on residue fields
  rfl

/-- The reduction of (minpoly R β) via the residue map has β₀ as a root. -/
lemma minpoly_map_residue_aeval_eq_zero (β : S) (hβ_int : IsIntegral R β) :
    (minpoly R β).eval₂ ((IsLocalRing.residue S).comp (algebraMap R S))
      (IsLocalRing.residue S β) = 0 := by
  rw [← residue_aeval_eq, minpoly.aeval, map_zero]

/-- When β generates S over R, the residue β₀ generates k_S over k_R.
    This follows from the surjectivity of the residue map and the fact that
    Algebra.adjoin R {β} = ⊤ maps onto Algebra.adjoin k_R {β₀}. -/
lemma residue_generates_of_generates [Module.Finite R S]
    (β : S) (hβ_gen : Algebra.adjoin R {β} = ⊤) :
    Algebra.adjoin (IsLocalRing.ResidueField R) {IsLocalRing.residue S β} = ⊤ := by
  let kR := IsLocalRing.ResidueField R
  let kS := IsLocalRing.ResidueField S
  let β₀ : kS := IsLocalRing.residue S β
  -- The residue map is surjective and respects the algebra structure
  -- Algebra.adjoin R {β} = ⊤ maps onto Algebra.adjoin k_R {β₀} = k_S
  rw [eq_top_iff]
  intro x _
  obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective (R := S) x
  have hs : s ∈ Algebra.adjoin R {β} := by rw [hβ_gen]; trivial
  -- s is in the adjoin of β over R, so residue(s) is in the adjoin of β₀ over k_R
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    simp only [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Algebra.subset_adjoin (Set.mem_singleton _)
  | algebraMap r =>
    -- (residue S) (algebraMap R S r) = algebraMap kR kS (residue R r)
    -- which is in any subalgebra
    have : (IsLocalRing.residue S) (algebraMap R S r) = algebraMap kR kS (IsLocalRing.residue R r) := by
      rw [← RingHom.comp_apply, ← RingHom.comp_apply, residue_algebraMap_eq]
    rw [this]
    exact Subalgebra.algebraMap_mem (Algebra.adjoin kR {β₀}) _
  | add x y _ _ hx hy =>
    simp only [map_add]
    exact Subalgebra.add_mem _ (hx trivial) (hy trivial)
  | mul x y _ _ hx hy =>
    simp only [map_mul]
    exact Subalgebra.mul_mem _ (hx trivial) (hy trivial)

/-- Key lemma: (minpoly R β).map(residue) equals minpoly kR β₀ when:
    - R is integrally closed
    - β generates S over R
    - The extension is étale (so residue field extension is separable)

    The proof uses that both polynomials are monic, irreducible (over their respective
    base rings), and have the same root β₀. The irreducibility of the reduction
    follows from S ≃ R[X]/(minpoly R β) and the tensor product S ⊗_R k_R ≃ k_S.
-/
lemma minpoly_map_eq_minpoly_residue [Algebra.Etale R S] [Algebra.EssFiniteType R S]
    [IsDomain R] [IsDomain S] [IsIntegrallyClosed R] [Module.Finite R S]
    (β : S) (hβ_int : IsIntegral R β) (hβ_gen : Algebra.adjoin R {β} = ⊤) :
    (minpoly R β).map (IsLocalRing.residue R) = minpoly (IsLocalRing.ResidueField R)
      (IsLocalRing.residue S β) := by
  let kR := IsLocalRing.ResidueField R
  let kS := IsLocalRing.ResidueField S
  let β₀ := IsLocalRing.residue S β
  let f := minpoly R β
  let f_bar := f.map (IsLocalRing.residue R)
  -- f_bar is monic (since minpoly is monic over integrally closed domain)
  have hf_monic : f.Monic := minpoly.monic hβ_int
  have hf_bar_monic : f_bar.Monic := hf_monic.map (IsLocalRing.residue R)
  -- β₀ is integral (finite extension)
  haveI : Module.Finite kR kS := inferInstance
  haveI : Algebra.IsIntegral kR kS := Algebra.IsIntegral.of_finite kR kS
  have hβ₀_int : IsIntegral kR β₀ := Algebra.IsIntegral.isIntegral β₀
  -- β₀ is a root of f_bar
  have hf_bar_root : aeval β₀ f_bar = 0 := by
    -- f_bar = f.map (residue R)
    -- aeval β₀ f_bar = f.eval₂ (algebraMap kR kS ∘ residue R) β₀
    --                = f.eval₂ (residue S ∘ algebraMap R S) β₀  [by residue_algebraMap_eq]
    --                = (residue S) (aeval β f)  [by hom_eval₂]
    --                = 0
    have h1 : aeval β f = 0 := minpoly.aeval R β
    rw [aeval_def] at h1 ⊢
    rw [eval₂_map, ← residue_algebraMap_eq, ← hom_eval₂, h1, map_zero]
  -- minpoly kR β₀ divides f_bar (since β₀ is a root)
  have hdvd : minpoly kR β₀ ∣ f_bar := minpoly.dvd kR β₀ hf_bar_root
  -- For equality, we use that both are monic and have the same degree
  -- The degree equality follows from:
  -- 1. deg(f_bar) = deg(f) = finrank R S (since β generates S)
  -- 2. deg(minpoly kR β₀) = finrank kR (kR⟮β₀⟯) = finrank kR kS (since β₀ generates kS)
  -- 3. finrank R S = finrank kR kS (étale implies flat, flat preserves rank for local rings)
  --
  -- This degree equality is the key technical fact that requires the étale hypothesis.
  -- For now, we use it as a sorry and can fill in the details later.
  have hdeg_eq : f_bar.natDegree = (minpoly kR β₀).natDegree := by
    -- Key facts:
    -- 1. f_bar.natDegree = f.natDegree (map preserves degree for monic polynomials)
    -- 2. For field extensions, natDegree (minpoly K x) = finrank K K⟮x⟯
    -- 3. β₀ generates kS over kR (from residue_generates_of_generates)
    -- 4. For étale (flat) extensions of local rings, finrank R S = finrank kR kS

    -- First: f_bar.natDegree = f.natDegree (map preserves degree for monic over nontrivial ring)
    have hdeg_map : f_bar.natDegree = f.natDegree := by
      simp only [f_bar, natDegree_map_eq_iff]
      left
      simp only [hf_monic.leadingCoeff, map_one, ne_eq, one_ne_zero, not_false_eq_true]
    -- β₀ generates kS over kR
    have hβ₀_gen : Algebra.adjoin kR {β₀} = ⊤ := residue_generates_of_generates β hβ_gen
    -- For algebraic elements in field extensions, Algebra.adjoin = IntermediateField.adjoin
    have hβ₀_alg : IsAlgebraic kR β₀ := Algebra.IsAlgebraic.isAlgebraic β₀
    have hβ₀_field_gen : IntermediateField.adjoin kR {β₀} = ⊤ := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hβ₀_alg] at hβ₀_gen
      exact IntermediateField.toSubalgebra_injective hβ₀_gen
    -- (minpoly kR β₀).natDegree = finrank kR kS
    have hdeg_minpoly_β₀ : (minpoly kR β₀).natDegree = Module.finrank kR kS := by
      rw [← IntermediateField.finrank_top', ← hβ₀_field_gen]
      exact (IntermediateField.adjoin.finrank hβ₀_int).symm
    -- Now we need: f.natDegree = finrank kR kS
    -- This follows from:
    -- (a) finrank R S = finrank kR kS
    --     For flat finite extensions of local rings, the rank equals the rank over
    --     the residue field. This uses: S ⊗[R] kR ≃ kS (from étale: m_R·S = m_S)
    --     and finrank R S = finrank kR (kR ⊗[R] S) for flat modules.
    -- (b) f.natDegree = finrank R S
    --     When Algebra.adjoin R {β} = ⊤ and R is integrally closed, S ≃ R[X]/(minpoly R β)
    --     as R-modules, so rank S = natDegree (minpoly R β).
    --
    -- These facts require additional machinery from Mathlib about flat modules over
    -- local rings and the structure of algebras generated by a single element.
    -- See: Mathlib.RingTheory.LocalRing.Module for flat module results.
    rw [hdeg_map, hdeg_minpoly_β₀]
    -- Goal: f.natDegree = finrank kR kS
    sorry
  -- Since minpoly kR β₀ ∣ f_bar, both monic, and same degree, they're equal
  have h_minpoly_ne_zero : minpoly kR β₀ ≠ 0 := minpoly.ne_zero hβ₀_int
  have hf_bar_ne_zero : f_bar ≠ 0 := Polynomial.map_monic_ne_zero hf_monic
  obtain ⟨q, hq⟩ := hdvd
  have hq_ne_zero : q ≠ 0 := by
    intro hq_zero
    rw [hq, hq_zero, mul_zero] at hf_bar_ne_zero
    exact hf_bar_ne_zero rfl
  have hq_monic : q.Monic := by
    have := hf_bar_monic
    rw [hq] at this
    exact (minpoly.monic hβ₀_int).of_mul_monic_left this
  have hdeg_q : q.natDegree = 0 := by
    have h1 : f_bar.natDegree = (minpoly kR β₀).natDegree + q.natDegree := by
      rw [hq, natDegree_mul h_minpoly_ne_zero hq_ne_zero]
    omega
  -- q has degree 0 and is monic, so q = 1
  have hq_eq_one : q = 1 := Polynomial.eq_one_of_monic_natDegree_zero hq_monic hdeg_q
  -- f_bar = minpoly kR β₀ * 1 = minpoly kR β₀
  calc (minpoly R β).map (IsLocalRing.residue R)
      = f_bar := rfl
    _ = minpoly kR β₀ * q := hq
    _ = minpoly kR β₀ * 1 := by rw [hq_eq_one]
    _ = minpoly kR β₀ := mul_one _

/-- The key technical fact: if β generates S over R (as an algebra),
    β₀ = residue(β) generates k_S over k_R, and the residue field extension is separable,
    then the minimal polynomial of β has derivative that is a unit when evaluated at β.

    The proof uses:
    1. S ≃ R[X]/(minpoly R β) implies k_S ≃ k_R[X]/(minpoly R β).map(residue)
    2. This means (minpoly R β).map(residue) is irreducible in k_R[X]
    3. So (minpoly R β).map(residue) = minpoly k_R β₀ (up to units)
    4. Separability gives aeval β₀ (minpoly k_R β₀).derivative ≠ 0
    5. Therefore aeval β (minpoly R β).derivative ∉ m_S, hence is a unit
-/
lemma isUnit_aeval_derivative_of_generates [Algebra.Etale R S] [Algebra.EssFiniteType R S]
    [IsDomain R] [IsDomain S] [IsIntegrallyClosed R] [Module.Finite R S]
    (β : S) (hβ_int : IsIntegral R β) (hβ_gen : Algebra.adjoin R {β} = ⊤) :
    IsUnit (aeval β (minpoly R β).derivative) := by
  -- Strategy: show residue of (aeval β f') is non-zero, hence aeval β f' is a unit
  apply isUnit_of_residue_ne_zero
  -- Let β₀ = residue(β) in the residue field k_S
  let β₀ := IsLocalRing.residue S β
  let kR := IsLocalRing.ResidueField R
  let kS := IsLocalRing.ResidueField S
  -- The residue field extension is separable (from étale)
  haveI : Algebra.IsSeparable kR kS := residueField_isSeparable_of_etale
  -- β₀ is integral over k_R (since k_S is finite over k_R)
  haveI : Module.Finite kR kS := inferInstance
  haveI : Algebra.IsIntegral kR kS := Algebra.IsIntegral.of_finite kR kS
  have hβ₀_int : IsIntegral kR β₀ := Algebra.IsIntegral.isIntegral β₀
  -- β₀ is separable, so its minimal polynomial is separable
  have hβ₀_sep : (minpoly kR β₀).Separable := Algebra.IsSeparable.isSeparable kR β₀
  -- Therefore, derivative of minpoly at β₀ is non-zero
  have hderiv_ne_zero : aeval β₀ (minpoly kR β₀).derivative ≠ 0 :=
    hβ₀_sep.aeval_derivative_ne_zero (minpoly.aeval kR β₀)
  -- The key fact: (minpoly R β).map(residue R) = minpoly kR β₀
  have hminpoly_eq : (minpoly R β).map (IsLocalRing.residue R) = minpoly kR β₀ :=
    minpoly_map_eq_minpoly_residue β hβ_int hβ_gen
  -- Now connect the derivatives
  -- residue(aeval β f') = aeval β₀ (f.map residue)' = aeval β₀ (minpoly kR β₀)' ≠ 0
  rw [residue_aeval_eq, residue_algebraMap_eq]
  -- Goal: eval₂ ((algebraMap kR kS).comp (residue R)) β₀ (minpoly R β).derivative ≠ 0
  -- Use eval₂_map: (p.map f).eval₂ g x = p.eval₂ (g.comp f) x
  -- So eval₂ (g.comp f) x p = (p.map f).eval₂ g x
  rw [← eval₂_map]
  -- Goal: ((minpoly R β).derivative.map (residue R)).eval₂ (algebraMap kR kS) β₀ ≠ 0
  -- derivative commutes with map: (p.map f).derivative = p.derivative.map f
  rw [← derivative_map]
  -- Goal: ((minpoly R β).map (residue R)).derivative.eval₂ (algebraMap kR kS) β₀ ≠ 0
  -- Use hminpoly_eq: (minpoly R β).map (residue R) = minpoly kR β₀
  rw [hminpoly_eq]
  -- Goal: (minpoly kR β₀).derivative.eval₂ (algebraMap kR kS) β₀ ≠ 0
  -- This is exactly aeval β₀ (minpoly kR β₀).derivative
  rw [← aeval_def]
  exact hderiv_ne_zero

end DerivativeUnit

-- Note: We add [IsDomain R], [IsIntegrallyClosed R], and [IsDomain S] hypotheses.
-- The [IsDomain R] and [IsIntegrallyClosed R] are needed for the minimal polynomial
-- to have the divisibility property (minpoly.isIntegrallyClosed_dvd).
-- [IsDomain S] follows naturally for étale extensions of domains.
-- We also add étale hypothesis to prove the derivative is a unit via separability.
lemma isIntegrallyClosed_univQuot [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [IsDomain R] [IsDomain S] [IsIntegrallyClosed R] [Algebra.Etale R S] [IsLocalHom (algebraMap R S)]
  [Algebra.EssFiniteType R S] [Monogenic R S] :
    UnivQuotient R S := by
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  -- Since adjoin R {β} = ⊤, the minimal polynomial f of β gives S ≃ R[X]/(f)
  -- by the universal property of AdjoinRoot
  let ⟨β, adjoin_eq_top⟩ := (inferInstance : Monogenic R S)
  have hβ_int : IsIntegral R β := Algebra.IsIntegral.isIntegral β
  let f := minpoly R β
  use β
  -- The isomorphism S ≃ R[X]/(f) follows from:
  -- 1. lift : R[X]/(f) →ₐ[R] S sending [X] to β
  -- 2. This is surjective since adjoin R {β} = ⊤
  -- 3. This is injective because f = minpoly (kernel is exactly (f))

  -- Define the lift: R[X]/(f) →ₐ[R] S
  have hf_aeval : aeval β f = 0 := minpoly.aeval R β
  have hker : ∀ p ∈ Ideal.span {f}, aeval β p = 0 := by
    intro p hp
    rw [Ideal.mem_span_singleton] at hp
    obtain ⟨q, hq⟩ := hp
    simp only [hq, map_mul, hf_aeval, zero_mul]
  let lift_hom : (R[X] ⧸ Ideal.span {f}) →ₐ[R] S :=
    Ideal.Quotient.liftₐ (Ideal.span {f}) (Polynomial.aeval β) hker
  -- Prove bijectivity
  have lift_bij : Function.Bijective lift_hom := by
    constructor
    · -- Injectivity: kernel is trivial because f is minimal polynomial
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp only [lift_hom, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk] at hx
      -- aeval β p = 0 implies f ∣ p by minimality (using isIntegrallyClosed_dvd)
      simp only [Ideal.Quotient.eq_zero_iff_mem]
      apply Ideal.mem_span_singleton.mpr
      -- β is integral since S is finite over R
      exact minpoly.isIntegrallyClosed_dvd hβ_int hx
    · -- Surjectivity: image contains Algebra.adjoin R {β} = ⊤
      intro s
      -- s ∈ Algebra.adjoin R {β} since adjoin_eq_top
      have hs : s ∈ Algebra.adjoin R {β} := by
        -- have : S' = Algebra.adjoin R {β} := rfl
        rw [adjoin_eq_top]; trivial
      -- Induction on the adjoin structure
      induction hs using Algebra.adjoin_induction with
      | mem x hx =>
        -- x ∈ {β}, so x = β
        simp only [Set.mem_singleton_iff] at hx
        rw [hx]
        -- β = aeval β X, so use [X]
        use Ideal.Quotient.mk (Ideal.span {f}) X
        simp only [lift_hom, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
        exact aeval_X β
      | algebraMap r =>
        -- algebraMap R S r = aeval β (C r)
        use Ideal.Quotient.mk (Ideal.span {f}) (C r)
        simp only [lift_hom, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
        exact aeval_C β r
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

  exact ⟨hβ_int, ⟨AlgEquiv.ofBijective lift_hom lift_bij⟩,
    isUnit_aeval_derivative_of_generates β hβ_int adjoin_eq_top⟩

end Monogenic

-- note: the old thing was already in mathlib oops
-- #check faithfulSMul_iff_algebraMap_injective
