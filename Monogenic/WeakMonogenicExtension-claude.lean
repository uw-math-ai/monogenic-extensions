import Mathlib
import Monogenic.Basic
universe u

open Polynomial
open Function
open RingHom

variable {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

#check isMonogenicExtension

-- Note: We add [IsDomain R], [IsIntegrallyClosed R], and [IsDomain S] hypotheses.
-- The [IsDomain R] and [IsIntegrallyClosed R] are needed for the minimal polynomial
-- to have the divisibility property (minpoly.isIntegrallyClosed_dvd).
-- [IsDomain S] follows naturally for étale extensions of domains.
lemma FiniteInjectiveEtale_IsMonogenic [Algebra R S] [FaithfulSMul R S]
  [mod_fin : Module.Finite R S] [Algebra.Etale R S] :
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
    -- Key: S'.toSubmodule ⊔ (maximalIdeal S).restrictScalars R = ⊤
    -- because the image of S' in k_S = Algebra.adjoin k_R {β₀} = ⊤
    have h_sup : S'.toSubmodule ⊔ (IsLocalRing.maximalIdeal S).restrictScalars R = ⊤ := by
      rw [eq_top_iff]
      intro s _
      -- For every y ∈ k_S, there exists t ∈ S with residue t = y and t ∈ S' ⊔ m_S
      -- We prove this by induction on y ∈ Algebra.adjoin k_R {β₀}
      suffices h : ∀ y ∈ Algebra.adjoin (IsLocalRing.ResidueField R) {β₀},
          ∀ t : S, IsLocalRing.residue S t = y →
          t ∈ S'.toSubmodule ⊔ (IsLocalRing.maximalIdeal S).restrictScalars R by
        exact h _ (by rw [h_adjoin_top]; trivial) s rfl
      intro y hy
      induction hy using Algebra.adjoin_induction with
      | mem x hx =>
        intro t ht
        -- x ∈ {β₀}, so x = β₀ = residue S β
        simp only [Set.mem_singleton_iff] at hx
        -- t has residue x = β₀ = residue S β
        -- So t - β ∈ maximalIdeal S, and t = β + (t - β) ∈ S' ⊔ m_S
        have h_diff : t - β ∈ IsLocalRing.maximalIdeal S := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
          calc Ideal.Quotient.mk _ t = IsLocalRing.residue S t := rfl
            _ = x := ht
            _ = β₀ := hx
            _ = Ideal.Quotient.mk _ β := hβ.symm
        refine Submodule.mem_sup.mpr ⟨β, ?_, t - β, ?_, by ring⟩
        · exact Algebra.self_mem_adjoin_singleton R β
        · exact h_diff
      | algebraMap r =>
        intro t ht
        -- r ∈ k_R = R/m_R, so r = residue R r' for some r' : R
        obtain ⟨r', hr'⟩ := IsLocalRing.residue_surjective r
        -- algebraMap k_R k_S r = residue S (algebraMap R S r')
        have h_alg : algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) r =
            IsLocalRing.residue S (algebraMap R S r') := by
          rw [← hr']; rfl
        -- t has residue = algebraMap k_R k_S r = residue S (algebraMap R S r')
        -- So t - algebraMap R S r' ∈ m_S
        have h_diff : t - algebraMap R S r' ∈ IsLocalRing.maximalIdeal S := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
          calc Ideal.Quotient.mk _ t = IsLocalRing.residue S t := rfl
            _ = algebraMap _ _ r := ht
            _ = IsLocalRing.residue S (algebraMap R S r') := h_alg
            _ = Ideal.Quotient.mk _ (algebraMap R S r') := rfl
        refine Submodule.mem_sup.mpr ⟨algebraMap R S r', ?_, t - algebraMap R S r', ?_, by ring⟩
        · exact Subalgebra.algebraMap_mem S' r'
        · exact h_diff
      | add x y _ _ ihx ihy =>
        intro t ht
        -- t has residue x + y
        -- Choose t_x with residue x, t_y with residue y
        obtain ⟨t_x, ht_x⟩ := IsLocalRing.residue_surjective x
        obtain ⟨t_y, ht_y⟩ := IsLocalRing.residue_surjective y
        -- t - (t_x + t_y) ∈ m_S since residue t = x + y = residue(t_x + t_y)
        have h_diff : t - (t_x + t_y) ∈ IsLocalRing.maximalIdeal S := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add, sub_eq_zero]
          calc Ideal.Quotient.mk _ t = IsLocalRing.residue S t := rfl
            _ = x + y := ht
            _ = IsLocalRing.residue S t_x + IsLocalRing.residue S t_y := by rw [ht_x, ht_y]
            _ = Ideal.Quotient.mk _ t_x + Ideal.Quotient.mk _ t_y := rfl
        have ht_x_mem := ihx t_x ht_x
        have ht_y_mem := ihy t_y ht_y
        -- t = (t_x + t_y) + (t - (t_x + t_y))
        have : t = (t_x + t_y) + (t - (t_x + t_y)) := by ring
        rw [this]
        apply Submodule.add_mem
        · exact Submodule.add_mem _ ht_x_mem ht_y_mem
        · exact Submodule.mem_sup_right h_diff
      | mul x y _ _ ihx ihy =>
        intro t ht
        -- t has residue x * y
        obtain ⟨t_x, ht_x⟩ := IsLocalRing.residue_surjective x
        obtain ⟨t_y, ht_y⟩ := IsLocalRing.residue_surjective y
        -- t - t_x * t_y ∈ m_S since residue t = x * y = residue(t_x * t_y)
        have h_diff : t - t_x * t_y ∈ IsLocalRing.maximalIdeal S := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, sub_eq_zero]
          calc Ideal.Quotient.mk _ t = IsLocalRing.residue S t := rfl
            _ = x * y := ht
            _ = IsLocalRing.residue S t_x * IsLocalRing.residue S t_y := by rw [ht_x, ht_y]
            _ = Ideal.Quotient.mk _ t_x * Ideal.Quotient.mk _ t_y := rfl
        have ht_x_mem := ihx t_x ht_x
        have ht_y_mem := ihy t_y ht_y
        -- t = t_x * t_y + (t - t_x * t_y)
        have ht_eq : t = t_x * t_y + (t - t_x * t_y) := by ring
        rw [ht_eq]
        apply Submodule.add_mem
        · -- Need to show t_x * t_y ∈ S'.toSubmodule ⊔ m_S
          -- Decompose t_x = s_x + m_x, t_y = s_y + m_y
          rw [Submodule.mem_sup] at ht_x_mem ht_y_mem
          obtain ⟨s_x, hs_x, m_x, hm_x, hx_eq⟩ := ht_x_mem
          obtain ⟨s_y, hs_y, m_y, hm_y, hy_eq⟩ := ht_y_mem
          -- t_x * t_y = (s_x + m_x) * (s_y + m_y) = s_x * s_y + (s_x * m_y + m_x * s_y + m_x * m_y)
          have h_prod : t_x * t_y = s_x * s_y + (s_x * m_y + m_x * s_y + m_x * m_y) := by
            rw [← hx_eq, ← hy_eq]; ring
          rw [h_prod]
          apply Submodule.add_mem
          · -- s_x * s_y ∈ S' because S' is a subalgebra
            have hs_x' : s_x ∈ S' := hs_x
            have hs_y' : s_y ∈ S' := hs_y
            exact Submodule.mem_sup_left (S'.mul_mem hs_x' hs_y')
          · -- The rest is in m_S
            apply Submodule.mem_sup_right
            rw [Submodule.restrictScalars_mem] at hm_x hm_y ⊢
            apply Ideal.add_mem
            apply Ideal.add_mem
            · exact Ideal.mul_mem_left _ s_x hm_y
            · exact Ideal.mul_mem_right _ _ hm_x
            · exact Ideal.mul_mem_left _ m_x hm_y
        · exact Submodule.mem_sup_right h_diff
    -- Now apply Nakayama-type argument
    -- We have S'.toSubmodule ⊔ m_S = ⊤
    -- By Nakayama (S finite over R, m_R ⊆ jacobson(0)), S' = ⊤

    -- Use the sup_eq_sup_smul Nakayama variant
    -- First show m_R ≤ Jac(0) for local ring R
    have h_jac : IsLocalRing.maximalIdeal R ≤ Ideal.jacobson (⊥ : Ideal R) :=
      IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R)
    -- S is finitely generated over R
    have h_fg : (⊤ : Submodule R S).FG := Module.finite_def.mp inferInstance
    -- Key: use the fact that m_S = Ideal.map φ m_R and apply Nakayama
    -- The approach: show S' ⊔ m_S.restrictScalars R = ⊤ implies S' = ⊤
    -- by showing the quotient (⊤ : Submodule R S) / S'.toSubmodule is zero

    -- Use Nakayama via sup_eq_sup_smul_of_le_smul_of_le_jacobson
    -- This says: if N' ⊆ N ⊔ I • N' and I ≤ Jac(J), then N ⊔ N' = N ⊔ J • N'
    -- Taking N = S'.toSubmodule, N' = ⊤, J = ⊥:
    -- If ⊤ ≤ S' ⊔ I • ⊤ and I ≤ Jac(0), then S' ⊔ ⊤ = S' ⊔ 0 • ⊤ = S'
    -- So ⊤ = S', i.e., S' = ⊤

    -- First, we need ⊤ ≤ S' ⊔ m_R • ⊤
    -- We have h_sup : S' ⊔ m_S.restrictScalars R = ⊤
    -- Since m_S = Ideal.map φ m_R, we have m_S.restrictScalars R ≤ m_R • ⊤
    have h_map_le_smul : (IsLocalRing.maximalIdeal S).restrictScalars R ≤
        (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R S) := by
      rw [← eq_max, Ideal.smul_top_eq_map]
    have h_le_sup : (⊤ : Submodule R S) ≤
        S'.toSubmodule ⊔ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R S) := by
      calc (⊤ : Submodule R S)
        = S'.toSubmodule ⊔ (IsLocalRing.maximalIdeal S).restrictScalars R := h_sup.symm
        _ ≤ S'.toSubmodule ⊔ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R S) :=
            sup_le_sup_left h_map_le_smul _
    -- Apply Nakayama: N ⊔ N' = N ⊔ J • N' when N' ≤ N ⊔ I • N' and I ≤ Jac(J)
    have h_nak := Submodule.sup_eq_sup_smul_of_le_smul_of_le_jacobson h_fg h_jac h_le_sup
    -- h_nak : S'.toSubmodule ⊔ ⊤ = S'.toSubmodule ⊔ ⊥ • ⊤
    -- ⊥ • ⊤ = ⊥ and S' ⊔ ⊥ = S', so S' ⊔ ⊤ = S', i.e., ⊤ ≤ S'
    simp only [Submodule.bot_smul, sup_bot_eq] at h_nak
    -- h_nak : S'.toSubmodule ⊔ ⊤ = S'.toSubmodule
    -- This means ⊤ ≤ S'.toSubmodule
    have h_top_le : (⊤ : Submodule R S) ≤ S'.toSubmodule := by
      calc (⊤ : Submodule R S) ≤ S'.toSubmodule ⊔ ⊤ := le_sup_right
        _ = S'.toSubmodule := h_nak
    exact eq_top_iff.mpr h_top_le
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
