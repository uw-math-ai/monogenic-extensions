import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Nakayama
import Mathlib.FieldTheory.PrimitiveElement

open Polynomial
open Function
open RingHom
namespace Monogenic

variable {R S} [CommRing R] [CommRing S] [Algebra R S]

-- This might be redundant: IsAdjoinRootMonic.mkOfAdjoinEqTop
-- does basically the same job in Mathlib.
lemma gensUnivQuot_of_monogenic
  [Module.Finite R S] [FaithfulSMul R S]
  [IsDomain R] [IsDomain S] [IsIntegrallyClosed R]
  (β : S)
  (adjoin_top : Algebra.adjoin R {β} = ⊤) :
    Nonempty ((R[X] ⧸ Ideal.span {minpoly R β}) ≃ₐ[R] S) := by
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  -- Since adjoin R {β} = ⊤, the minimal polynomial f of β gives S ≃ R[X]/(f)
  -- by the universal property of AdjoinRoot
  have hβ_int : IsIntegral R β := Algebra.IsIntegral.isIntegral β
  let f := minpoly R β
  -- The isomorphism S ≃ R[X]/(f) follows from:
  -- 1. lift : R[X]/(f) →ₐ[R] S sending [X] to β
  -- 2. This is surjective since adjoin R {β} = ⊤
  -- 3. This is injective because f = minpoly (kernel is exactly (f))

  -- Define the lift: R[X]/(f) →ₐ[R] S
  have hf_aeval : aeval β f = 0 := minpoly.aeval R β
  have hker : ∀ p ∈ Ideal.span {f}, aeval β p = 0 := fun p hp => by
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hp
    simp [hf_aeval]
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
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton.mpr (minpoly.isIntegrallyClosed_dvd hβ_int hx))
    · -- Surjectivity: image contains Algebra.adjoin R {β} = ⊤
      intro s
      have hs : s ∈ Algebra.adjoin R {β} := adjoin_top ▸ trivial
      -- Induction on the adjoin structure
      induction hs using Algebra.adjoin_induction with
      | mem x hx =>
        simp only [Set.mem_singleton_iff] at hx
        exact ⟨Ideal.Quotient.mk _ X, by simp [lift_hom, hx, aeval_X]⟩
      | algebraMap r =>
        exact ⟨Ideal.Quotient.mk _ (C r), by simp [lift_hom, aeval_C]⟩
      | add x y _ _ ihx ihy =>
        obtain ⟨px, hpx⟩ := ihx; obtain ⟨py, hpy⟩ := ihy
        exact ⟨px + py, by simp [hpx, hpy]⟩
      | mul x y _ _ ihx ihy =>
        obtain ⟨px, hpx⟩ := ihx; obtain ⟨py, hpy⟩ := ihy
        exact ⟨px * py, by simp [hpx, hpy]⟩
  let iso := AlgEquiv.ofBijective lift_hom lift_bij
  exact ⟨iso⟩

#check IsAdjoinRootMonic.mkOfAdjoinEqTop
lemma isAdjoinRootMonic_of_monogenic
  [Module.Finite R S] [FaithfulSMul R S]
  (β : S)
  (adjoin_top : Algebra.adjoin R {β} = ⊤) :
    Nonempty (IsAdjoinRootMonic S (minpoly R β)) := by
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have hβ_int : IsIntegral R β := Algebra.IsIntegral.isIntegral β
  let f := minpoly R β
  let map := Polynomial.aeval (R:=R) β
  have hf_aeval : aeval β f = 0 := minpoly.aeval R β
  have surj : Surjective map := by
    intro s
    have hs : s ∈ Algebra.adjoin R {β} := adjoin_top ▸ trivial
    -- Induction on the adjoin structure
    unfold map
    induction hs using Algebra.adjoin_induction with
    | mem x hx =>
      simp only [Set.mem_singleton_iff] at hx
      exact ⟨X, by rw [hx]; simp only [aeval_X]⟩
    | algebraMap r =>
      exact ⟨(C r), by simp only [aeval_C]⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨px, hpx⟩ := ihx; obtain ⟨py, hpy⟩ := ihy
      exact ⟨px + py, by simp [hpx, hpy]⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨px, hpx⟩ := ihx; obtain ⟨py, hpy⟩ := ihy
      exact ⟨px * py, by simp [hpx, hpy]⟩
  have hkerspec : ker map = Ideal.span {f} := by
    ext x
    constructor
    · intro hx
      simp only [mem_ker, map] at hx
      sorry
    · intro hx
      simp only [mem_ker]
      unfold map
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hx
      simp [hf_aeval]
  exact ⟨⟨⟨map, surj, hkerspec⟩, minpoly.monic hβ_int⟩⟩

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

variable [IsLocalRing S]

/-- The residue of aeval β p equals eval₂ applied to the residues.

    Note: The composition (residue S) ∘ (algebraMap R S) factors through residue R
    when we have IsLocalHom (algebraMap R S), giving us a map k_R → k_S. -/
theorem residue_aeval_eq (β : S) (p : R[X]) :
    IsLocalRing.residue S (aeval β p) =
    p.eval₂ ((IsLocalRing.residue S).comp (algebraMap R S)) (IsLocalRing.residue S β) := by
  simp only [aeval_def, hom_eval₂]

/-- The reduction of (minpoly R β) via the residue map has β₀ as a root. -/
lemma minpoly_map_residue_aeval_eq_zero (β : S) :
    (minpoly R β).eval₂ ((IsLocalRing.residue S).comp (algebraMap R S))
      (IsLocalRing.residue S β) = 0 := by
  rw [← residue_aeval_eq, minpoly.aeval, map_zero]


/-- In a local ring, an element is a unit iff its residue is non-zero. -/
lemma isUnit_of_residue_ne_zero {s : S} (h : IsLocalRing.residue S s ≠ 0) : IsUnit s := by
  rw [ne_eq, IsLocalRing.residue_eq_zero_iff] at h
  exact IsLocalRing.notMem_maximalIdeal.mp h

variable [IsLocalRing R] [Module.Finite R S] [FaithfulSMul R S]

/-- The residue field map from R to k_S factors as R → k_R → k_S. -/
lemma residue_algebraMap_eq :
    (IsLocalRing.residue S).comp (algebraMap R S) =
    (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)).comp
      (IsLocalRing.residue R) :=
  rfl

/-- When β generates S over R, the residue β₀ generates k_S over k_R.
    This follows from the surjectivity of the residue map and the fact that
    Algebra.adjoin R {β} = ⊤ maps onto Algebra.adjoin k_R {β₀}. -/
lemma residue_generates_of_generates
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
    have : (IsLocalRing.residue S) (algebraMap R S r)
        = algebraMap kR kS (IsLocalRing.residue R r) := by
      rw [← RingHom.comp_apply, ← RingHom.comp_apply, residue_algebraMap_eq]
    rw [this]
    exact Subalgebra.algebraMap_mem (Algebra.adjoin kR {β₀}) _
  | add x y _ _ hx hy =>
    simp only [map_add]
    exact Subalgebra.add_mem _ (hx trivial) (hy trivial)
  | mul x y _ _ hx hy =>
    simp only [map_mul]
    exact Subalgebra.mul_mem _ (hx trivial) (hy trivial)

/-- For étale extensions of local rings, finrank is preserved under base change to residue field.

    The proof uses:
    1. Étale ⟹ Smooth ⟹ Flat
    2. Finite + Flat over local ring ⟹ Free
    3. m_R · S = m_S (étale condition) gives S / (m_R · S) = kS
    4. finrank_quotient_map: finrank kR (S / m_R·S) = finrank R S
-/
lemma finrank_eq_finrank_residueField [Algebra.Etale R S] :
    Module.finrank R S =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) := by
  -- Étale implies FormallySmooth and FinitePresentation, hence Smooth
  haveI : Algebra.FormallySmooth R S := inferInstance
  haveI : Algebra.FinitePresentation R S := inferInstance
  haveI : Algebra.Smooth R S := ⟨inferInstance, inferInstance⟩
  haveI : Module.Flat R S := Algebra.Smooth.flat R S
  -- Finite + Flat over local ring ⟹ Free
  haveI : Module.Free R S := Module.free_of_flat_of_isLocalRing
  -- For étale: m_R · S = m_S
  have hmaximal : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal S := Algebra.FormallyUnramified.map_maximalIdeal
  -- finrank_quotient_map gives: finrank (R ⧸ m_R) (S ⧸ Ideal.map m_R) = finrank R S
  -- ResidueField S = S ⧸ maximalIdeal S, and hmaximal says Ideal.map m_R = m_S
  -- Use Eq.rec to transport along hmaximal
  have h := IsLocalRing.finrank_quotient_map (R := R) (S := S)
  -- h : finrank (R ⧸ mR) (S ⧸ Ideal.map mR) = finrank R S
  -- We need: finrank R S = finrank kR kS
  -- where kR = R ⧸ mR = ResidueField R, kS = S ⧸ mS = ResidueField S
  -- hmaximal gives: Ideal.map mR = mS, so S ⧸ Ideal.map mR ≃ₗ S ⧸ mS = kS
  -- ResidueField R = R ⧸ maximalIdeal R and ResidueField S = S ⧸ maximalIdeal S by definition
  simp only [IsLocalRing.ResidueField]
  -- Use the linear equivalence from quotEquivOfEq to transfer finrank
  let e : (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
      ≃ₗ[R ⧸ IsLocalRing.maximalIdeal R] (S ⧸ IsLocalRing.maximalIdeal S) :=
    AddEquiv.toLinearEquiv (Ideal.quotEquivOfEq hmaximal).toAddEquiv (fun r x => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      -- Goal: quotEquivOfEq(mk(algebraMap r * x)) = mk(r) • quotEquivOfEq(mk(x))
      -- LHS: quotEquivOfEq(mk(algebraMap r * x)) = mk(algebraMap r * x) (in S ⧸ mS)
      -- RHS: mk(r) • mk(x) = mk(algebraMap r * x) (in S ⧸ mS)
      simp only [RingEquiv.toAddEquiv_eq_coe]
      rfl)
  rw [← e.finrank_eq, h]

/-- Key lemma: (minpoly R β).map(residue) equals minpoly kR β₀ when we have an isomorphism
    S ≃ R[X]/(minpoly R β).

    The proof uses the degree equality: since minpoly kR β₀ | f_bar, both are monic, and we
    show they have the same degree, hence they're equal.
-/
lemma minpoly_map_eq_minpoly_residue [Algebra.Etale R S]
    [IsDomain R] [IsDomain S] [IsIntegrallyClosed R]
    (β : S) (adjoin_eq_top : Algebra.adjoin R {β} = ⊤) :
    (minpoly R β).map (IsLocalRing.residue R) = minpoly (IsLocalRing.ResidueField R)
      (IsLocalRing.residue S β) := by
  let hβ_int : IsIntegral R β := Algebra.IsIntegral.isIntegral β
  let kR := IsLocalRing.ResidueField R
  let kS := IsLocalRing.ResidueField S
  let β₀ := IsLocalRing.residue S β
  let f := minpoly R β
  let f_bar := f.map (IsLocalRing.residue R)
  -- f_bar is monic
  have hf_monic : f.Monic := minpoly.monic hβ_int
  have hf_bar_monic : f_bar.Monic := hf_monic.map (IsLocalRing.residue R)
  have hf_bar_ne_zero : f_bar ≠ 0 := Polynomial.map_monic_ne_zero hf_monic
  -- β₀ is integral (finite extension)
  haveI : Module.Finite kR kS := inferInstance
  haveI : Algebra.IsIntegral kR kS := Algebra.IsIntegral.of_finite kR kS
  have hβ₀_int : IsIntegral kR β₀ := Algebra.IsIntegral.isIntegral β₀
  -- β₀ is a root of f_bar
  have hf_bar_root : aeval β₀ f_bar = 0 := by
    rw [aeval_def, eval₂_map, ← residue_algebraMap_eq, ← hom_eval₂, ← aeval_def, minpoly.aeval,
      map_zero]
  -- minpoly kR β₀ divides f_bar (since β₀ is a root)
  have hdvd : minpoly kR β₀ ∣ f_bar := minpoly.dvd kR β₀ hf_bar_root
  have h_minpoly_ne_zero : minpoly kR β₀ ≠ 0 := minpoly.ne_zero hβ₀_int
  have hβ₀_gen : Algebra.adjoin kR {β₀} = ⊤ := residue_generates_of_generates β adjoin_eq_top
  -- For equality of f_bar and minpoly kR β₀, we use that both are monic and have the same degree
  have hdeg_map : f_bar.natDegree = f.natDegree := by
    simp only [f_bar, natDegree_map_eq_iff]
    left
    simp only [hf_monic.leadingCoeff, map_one, ne_eq, one_ne_zero, not_false_eq_true]
  have hβ₀_alg : IsAlgebraic kR β₀ := Algebra.IsAlgebraic.isAlgebraic β₀
  have hβ₀_field_gen : IntermediateField.adjoin kR {β₀} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hβ₀_alg] at hβ₀_gen
    exact IntermediateField.toSubalgebra_injective hβ₀_gen
  have hdeg_minpoly_β₀ : (minpoly kR β₀).natDegree = Module.finrank kR kS := by
    rw [← IntermediateField.finrank_top', ← hβ₀_field_gen]
    exact (IntermediateField.adjoin.finrank hβ₀_int).symm
  -- Key: use the isomorphism to get finrank R S = f.natDegree
  let adjoin := IsAdjoinRootMonic.mkOfAdjoinEqTop hβ_int adjoin_eq_top
  let pb := IsAdjoinRootMonic.powerBasis adjoin
  have hfinrank_S : Module.finrank R S = f.natDegree := pb.finrank
  -- For étale extensions: finrank R S = finrank kR kS
  -- This follows from: S ⊗_R kR ≃ kS (since m_R · S = m_S for étale)
  -- and for free modules over local rings, rank = rank after tensoring with residue field
  have hdeg_eq : f_bar.natDegree = (minpoly kR β₀).natDegree := by
    rw [hdeg_map, hdeg_minpoly_β₀]
    -- Goal: f.natDegree = finrank kR kS
    -- We have: finrank R S = f.natDegree (from hfinrank_S)
    -- Need: finrank R S = finrank kR kS (flat base change)
    rw [← hfinrank_S]
    exact finrank_eq_finrank_residueField
  -- Since minpoly kR β₀ ∣ f_bar, both monic, and same degree, they're equal
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
  change f_bar = _
  rw [hq, Polynomial.eq_one_of_monic_natDegree_zero hq_monic hdeg_q, mul_one]

/-- The key technical fact: if β₀ generates kS over kR (as an intermediate field) and the
    extension is étale, then the minimal polynomial of β has derivative that is a unit when
    evaluated at β.

    The proof uses:
    1. (minpoly R β).map(residue) = minpoly kR β₀ (degree equality from generation)
    2. Separability gives aeval β₀ (minpoly kR β₀).derivative ≠ 0
    3. Therefore aeval β (minpoly R β).derivative ∉ m_S, hence is a unit
-/
lemma deriv_isUnit_of_monogenic [Algebra.Etale R S] [IsDomain R] [IsDomain S]
    [IsIntegrallyClosed R]
    (β : S)
    (adjoin_eq_top : Algebra.adjoin R {β} = ⊤) :
    IsUnit (aeval β (minpoly R β).derivative) := by
  -- Strategy: show residue of (aeval β f') is non-zero, hence aeval β f' is a unit
  apply isUnit_of_residue_ne_zero
  let kR := IsLocalRing.ResidueField R
  let kS := IsLocalRing.ResidueField S
  let β₀ := IsLocalRing.residue S β
  -- The residue field extension is separable (from étale)
  haveI : Algebra.IsSeparable kR kS := inferInstance
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
    minpoly_map_eq_minpoly_residue β adjoin_eq_top
  -- Now connect the derivatives
  rw [residue_aeval_eq, residue_algebraMap_eq, ← eval₂_map, ← derivative_map, hminpoly_eq,
    ← aeval_def]
  exact hderiv_ne_zero

/-
initial part without the integral domain hypothesis.
for the statement about the isomorphism with the quotient ring,
see isIntegrallyClosed_existsPolyQuotIso below
(idk, cant come up with a name. i think these new names are roughly
mathlib convention? i tried.)

see FaithfulSMul.iff_algebraMapInjective below for a proof its equivalent
to asserting that phi is injective.
-/
lemma monogenic_of_finiteInjectiveEtale [Algebra.Etale R S] :
    ∃(β : S), Algebra.adjoin R {β} = ⊤ := by
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

end Monogenic

-- note: the old thing was already in mathlib oops
-- #check faithfulSMul_iff_algebraMap_injective
