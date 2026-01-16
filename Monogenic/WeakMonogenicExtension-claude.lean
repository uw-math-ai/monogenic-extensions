import Mathlib
universe u

open Polynomial
open Function
open RingHom

variable {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

-- Note: We add [IsDomain R], [IsIntegrallyClosed R], and [IsDomain S] hypotheses.
-- The [IsDomain R] and [IsIntegrallyClosed R] are needed for the minimal polynomial
-- to have the divisibility property (minpoly.isIntegrallyClosed_dvd).
-- [IsDomain S] follows naturally for étale extensions of domains.
lemma FiniteInjectiveEtale_IsMonogenic [Algebra R S] [FaithfulSMul R S]
  [Module.Finite R S] [Algebra.Etale R S] :
    ∃(β : S), Algebra.adjoin R {β} = ⊤ := by
  let φ := algebraMap R S
  -- Key: maximal ideal maps to maximal ideal (from Mathlib's unramified local ring theory)
  have eq_max : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal S :=
    Algebra.FormallyUnramified.map_maximalIdeal
  -- Residue field extension is separable and finite (automatic instances from Mathlib)
  haveI sep_res : Algebra.IsSeparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    inferInstance
  haveI fin_res : Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    inferInstance
  -- Primitive element theorem: ∃ β₀ such that k_R⟮β₀⟯ = k_S
  obtain ⟨β₀, hβ₀⟩ := Field.exists_primitive_element (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField S)
  -- Lift β₀ to β in S via the quotient map
  obtain ⟨β, hβ⟩ := Ideal.Quotient.mk_surjective β₀
  -- φ finite implies S is integral over R
  -- haveI : Module.Finite R S := φ_fin
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  -- The key claim: Algebra.adjoin R {β} = ⊤
  -- This follows from Nakayama's lemma: since the image of adjoin R {β} in S/m_S
  -- equals k_R⟮β₀⟯ = k_S (by primitive element theorem and the lift), and S is
  -- finitely generated over R, we get adjoin R {β} = S.
  let S' := Algebra.adjoin R {β}
  have adjoin_eq_top : S' = ⊤ := by
    -- The intermediate field k_R⟮β₀⟯ = ⊤ means β₀ generates k_S over k_R
    -- Since β₀ is algebraic (k_S is finite over k_R), the subalgebra equals the intermediate field
    haveI h_alg_ext : Algebra.IsAlgebraic (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S) :=
        Algebra.IsAlgebraic.of_finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
    have h_alg_β₀ : IsAlgebraic (IsLocalRing.ResidueField R) β₀ :=
      Algebra.IsAlgebraic.isAlgebraic β₀
    -- Use the fact that IntermediateField.adjoin K {α} has
    -- toSubalgebra = Algebra.adjoin K {α} when α is algebraic
    have h_subalg := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic h_alg_β₀
    -- Now k_R⟮β₀⟯ = ⊤ implies Algebra.adjoin k_R {β₀} = ⊤
    have h_adjoin_top : Algebra.adjoin (IsLocalRing.ResidueField R) {β₀} = ⊤ := by
      rw [← h_subalg, hβ₀, IntermediateField.top_toSubalgebra]

    -- ... (Initial parts of the proof to define β and S') ...
    let mR := IsLocalRing.maximalIdeal R

    -- 1. Satisfy (hN : N.FG)
    have h_fg : (⊤ : Submodule R S).FG := Module.finite_def.mp inferInstance

    -- 2. Satisfy (hIjac : I ≤ jacobson ⊥)
    have h_jac : mR ≤ Ideal.jacobson ⊥ := IsLocalRing.maximalIdeal_le_jacobson ⊥

    -- 3. Satisfy (hmaple : map (I • N).mkQ N = map (I • N).mkQ N')
    -- We show the image of S' in S / (mR • S) is the same as the image of ⊤ (which is S/(mR • S))
    have h_map : Submodule.map (mR • ⊤ : Submodule R S).mkQ S'.toSubmodule =
                Submodule.map (mR • ⊤ : Submodule R S).mkQ ⊤ := by
      -- aristotle output: i swear this is even less understandable
      apply le_antisymm _ _;
      · exact Submodule.map_mono ( by aesop_cat );
      · intro x hx;
        obtain ⟨ y, hy, rfl ⟩ := hx;
        -- tactic state is:
        -- ⊢ (mR • ⊤).mkQ y ∈ Submodule.map (mR • ⊤).mkQ (Subalgebra.toSubmodule S')
        -- with y : S and hy : y ∈ ↑⊤
        -- might be a manual way to do this better?

        -- Since $y \in S$, we can write $y$ as a polynomial in $\beta$ with coefficients in $R$.
        obtain ⟨ p, hp ⟩ : ∃ p : Polynomial R,
            y - p.eval₂ (algebraMap R S) β ∈ mR • (⊤ : Submodule R S) := by
          have h_poly : ∀ y : S, ∃ p : Polynomial R,
              y - p.eval₂ (algebraMap R S) β ∈ IsLocalRing.maximalIdeal S := by
            -- Since $S$ is a local ring with maximal ideal $mS$,
            -- and $\beta$ is a lift of $\beta₀$, which generates the residue field,
            -- any element in $S$ can be written as a polynomial in $\beta$ plus an element in $mS$.
            have h_poly : ∀ y : S, ∃ p : Polynomial R,
                y - p.eval₂ (algebraMap R S) β ∈ IsLocalRing.maximalIdeal S := by
              intro y
              have h_res : ∃ p : Polynomial (IsLocalRing.ResidueField R),
                  (Ideal.Quotient.mk (IsLocalRing.maximalIdeal S) y) = p.eval₂ (algebraMap
                    (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)) β₀ := by
                have h_res : ∀ y : IsLocalRing.ResidueField S,
                    ∃ p : Polynomial (IsLocalRing.ResidueField R),
                    y = p.eval₂ (algebraMap (IsLocalRing.ResidueField R)
                      (IsLocalRing.ResidueField S)) β₀ := by
                  intro y;
                  have h_res : y ∈ Algebra.adjoin (IsLocalRing.ResidueField R) {β₀} := by
                    aesop;
                  rw [ Algebra.adjoin_singleton_eq_range_aeval ] at h_res ; aesop;
                exact h_res _
              obtain ⟨ p, hp ⟩ := h_res;
              -- Let $q$ be the polynomial in $R[X]$ obtained by
              -- lifting the coefficients of $p$ from the residue field to $R$.
              obtain ⟨ q, hq ⟩ : ∃ q : Polynomial R,
                  p = Polynomial.map (algebraMap R (IsLocalRing.ResidueField R)) q := by
                choose f hf using fun i => IsLocalRing.residue_surjective ( p.coeff i );
                use ∑ i ∈ p.support, f i • Polynomial.X ^ i;
                ext i; aesop;
              use q;
              rw [ ← Ideal.Quotient.eq_zero_iff_mem ];
              simp_all +decide only [IntermediateField.adjoin_eq_top_iff,
                IntermediateField.adjoin_toSubalgebra, Submodule.top_coe, Set.mem_univ,
                IsLocalRing.ResidueField.algebraMap_eq, eval₂_map, map_sub];
              simp +decide only [eval₂_eq_sum_range, coe_comp, Function.comp_apply,
                IsLocalRing.ResidueField.algebraMap_residue, map_sum, map_mul,
                Ideal.Quotient.mk_algebraMap, map_pow, hβ];
              exact sub_eq_zero_of_eq <| Finset.sum_congr rfl fun _ _ => by erw [ ← hβ ] ; rfl;
            exact h_poly;
          obtain ⟨ p, hp ⟩ := h_poly y;
          rw [ ← eq_max ] at hp;
          exact ⟨ p, by simpa [ Ideal.map ] using hp ⟩;
        refine' ⟨ p.eval₂ ( algebraMap R S ) β, _, _ ⟩
          <;> simp_all +decide [ Submodule.Quotient.eq ];
        · rw [ Polynomial.eval₂_eq_sum_range ];
          exact Subalgebra.sum_mem _ fun i hi => Subalgebra.mul_mem _
            (Subalgebra.algebraMap_mem _ _)
            (Subalgebra.pow_mem _ ( Algebra.subset_adjoin <| Set.mem_singleton _) _);
        · simpa using Submodule.neg_mem _ hp
    -- Apply the requested lemma
    have h_final := Submodule.eq_of_map_mkQ_eq_map_mkQ_of_le_jacobson_bot h_fg h_jac h_map.symm
    -- Conclude
    -- If h_final is (⊤ : Submodule R S) = S'.toSubmodule
    have myrw : (⊤ : Subalgebra R S).toSubmodule = (⊤ : Submodule R S) := by rfl
    rw [← myrw] at h_final
    let test := Subalgebra.toSubmodule_injective h_final
    exact test.symm
  exact ⟨β, adjoin_eq_top⟩

omit [IsLocalRing S]
lemma minpolyStuff [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [IsDomain R] [IsDomain S] [IsIntegrallyClosed R] :
    (∃ β : S, Algebra.adjoin R {β} = ⊤)
      → ∃ f : R[X], Nonempty ((R[X] ⧸ Ideal.span {f}) ≃ₐ[R] S) := by
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  -- Since adjoin R {β} = ⊤, the minimal polynomial f of β gives S ≃ R[X]/(f)
  -- by the universal property of AdjoinRoot
  intro hyp
  let ⟨β, adjoin_eq_top⟩ := hyp
  let f := minpoly R β
  -- Unfold the definition and construct the isomorphism
  -- unfold isMonogenicExtension
  use f
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
      have hβ_int : IsIntegral R β := Algebra.IsIntegral.isIntegral β
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
  exact ⟨AlgEquiv.ofBijective lift_hom lift_bij⟩



#check RingHom.finite_algebraMap
#check RingHom.etale_algebraMap

#check RingHom.toAlgebra
#check RingHom.algebraMap_toAlgebra

-- aristotle was able to give this pretty easily
-- true for all CommRing R and CommRing S.
omit [IsLocalRing R] [IsLocalRing S]
theorem faithful_smul_iff_injective [Algebra R S] :
  Injective (algebraMap R S) ↔ FaithfulSMul R S := by
  constructor
  · -- If the algebra map is injective, then the scalar multiplication is faithful.
    intro h_inj
    apply FaithfulSMul.mk
    intro r s h_eq
    have h_eq' : algebraMap R S r = algebraMap R S s := by
      -- By definition of scalar multiplication in the algebra, we have $r • 1 = s • 1$.
      have h_one : r • (1 : S) = s • (1 : S) := by
        exact h_eq 1;
      -- Since multiplying by 1 in S is the same as applying the algebra map,
      -- we have algebraMap R S r = r • 1 and algebraMap R S s = s • 1.
      simp only [Algebra.smul_def, mul_one] at h_one ⊢;
      exact h_one
    have h_eq'' : r = s := by
      -- Apply the injectivity of the algebra map to conclude that $r = s$.
      apply h_inj; exact h_eq'
    exact h_eq''
  · intro faithful
    unfold Injective
    -- Apply the fact that `FaithfulSMul R S` implies injectivity of the algebra map.
    apply FaithfulSMul.algebraMap_injective R S
