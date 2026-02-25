# Monogenic Extensions Project Memory

## Detailed Reference Files
- [Mathlib structure, PR planning, simplifications](mathlib-structure.md)

## Key Lean 4 / Mathlib Patterns

### API Changes (Current Mathlib)
- `AdjoinRoot.liftHom` is **deprecated** → use `AdjoinRoot.liftAlgHom f (Algebra.ofId R S) β h`
- `Module.End.injective_of_surjective` → use `OrzechProperty.injective_of_surjective_endomorphism ψ hψ_surj`
- `Module.Free.finrank_eq_card_chooseBasisIndex` → use `Module.finrank_eq_card_chooseBasisIndex` (declared with `_root_`)
- Every `CommRing` has `OrzechProperty` (instance in `Mathlib.RingTheory.FiniteType`)

### Cayley-Hamilton Transfer Pattern
To show `aeval β (charpoly (lmul β)) = 0` from `LinearMap.aeval_self_charpoly`:
```lean
have h : Algebra.lmul R S (aeval β lβ.charpoly) = 0 := by
  rw [← aeval_algHom_apply]; exact LinearMap.aeval_self_charpoly lβ
have h2 := DFunLike.congr_fun h (1 : S)
-- then use simp [mul_one] to simplify lmul applied to 1
```

### Degree Comparison Pattern
When comparing `natDegree` via `degree` inequalities:
```lean
rw [degree_eq_natDegree hf_monic.ne_zero, degree_eq_natDegree hg_monic.ne_zero] at h
have : (f.natDegree : WithBot ℕ) ≤ (n : WithBot ℕ) := h.trans (by simp [...])
exact_mod_cast this
```

### Étale → Free Chain
```lean
haveI : Algebra.Smooth R S := ⟨inferInstance, inferInstance⟩
haveI : Module.Flat R S := Algebra.Smooth.flat R S
haveI : Module.Free R S := Module.free_of_flat_of_isLocalRing
```

### Linter Notes
- `show` that changes goals triggers linter → use `change` instead
- Check for unused simp args (e.g., `map_zero`, `Nat.cast_le`)

## Proof: gensUnivQuot_of_monogenic (without IsIntegrallyClosed)
Strategy: Cayley-Hamilton + quotient rank + Orzech surjective endo injectivity.
See `Monogenic/Generator.lean` lines 37-59.

## Known Mathlib Duplicates
- `isUnit_of_residue_ne_zero` = `IsLocalRing.residue_ne_zero_iff_isUnit` (ResidueField/Basic.lean:41)
- `residue_comp_algebraMap` ≈ `IsLocalRing.ResidueField.map_comp_residue` (ResidueField/Basic.lean:112)
- `Ideal.span_singleton_mul_right_unit` exists as `Ideal.span_singleton_mul_left_unit` (Ideal/Span.lean:111)

## Key Import Fact
`IsAdjoinRoot.lean` does NOT transitively import `LinearAlgebra.Charpoly.Basic`.
PR 1 needs to add this import (or put `natDegree_le'` in a separate file).

## Blueprint
See `blueprint/src/content.tex` for full blueprint with dependency graph and PR plan (7 PRs).
