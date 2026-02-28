# Mathlib Structure & PR Planning Notes

## Key Mathlib File Locations

### Minimal Polynomials
- `minpoly.natDegree_le` (field version, needs FiniteDimensional): `Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:545`
- `minpoly.aeval`, `minpoly.monic`, `minpoly.dvd`: `Mathlib/FieldTheory/Minpoly/IsIntegrallyClosed.lean`
- `Polynomial.lifts_and_degree_eq_and_monic`: `Mathlib/Algebra/Polynomial/Lifts.lean:164`

### IsAdjoinRoot
- `IsAdjoinRoot`, `IsAdjoinRootMonic`: `Mathlib/RingTheory/IsAdjoinRoot.lean`
- `finrank_quotient_span_eq_natDegree'`: same file
- **Imports**: `FieldTheory.Minpoly.IsIntegrallyClosed`, `RingTheory.PowerBasis`
- **Does NOT transitively import** `LinearAlgebra.Charpoly.Basic`

### Charpoly
- `LinearMap.aeval_self_charpoly`, `LinearMap.charpoly_natDegree`: `Mathlib/LinearAlgebra/Charpoly/Basic.lean`
- `Matrix.charpoly_natDegree_eq_dim`, `Matrix.aeval_self_charpoly`: `Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean`
- **Imports**: `LinearAlgebra.FreeModule.Finite.Basic`, `LinearAlgebra.Matrix.Charpoly.Coeff`

### Étale Ring Theory
- `Algebra.Etale`: `Mathlib/RingTheory/Etale/Basic.lean:217`
- `StandardEtalePair`, `StandardEtalePresentation`, `Algebra.IsStandardEtale`: `Mathlib/RingTheory/Etale/StandardEtale.lean`
- Étale directory files: `Basic.lean`, `StandardEtale.lean`, `Field.lean`, `Kaehler.lean`, `Locus.lean`, `Pi.lean`, `QuasiFinite.lean`

### Local Rings & Residue Fields
- `IsLocalRing.residue`, `IsLocalRing.ResidueField`: `Mathlib/RingTheory/LocalRing/ResidueField/Defs.lean`
- `residue_ne_zero_iff_isUnit`: `ResidueField/Basic.lean:41`
- `ResidueField.map_comp_residue`: `ResidueField/Basic.lean:112` (requires `IsLocalHom`)
- `ResidueField.map_residue`: `ResidueField/Basic.lean:116` (pointwise version)
- `IsLocalRing.finrank_quotient_map`: `Mathlib/RingTheory/LocalRing/Quotient.lean`
- `IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient`: same file
- `Module.free_of_flat_of_isLocalRing`: `Mathlib/RingTheory/LocalRing/Module.lean:304`
- `Algebra.FormallyUnramified.map_maximalIdeal`: `Mathlib/RingTheory/Unramified/LocalRing.lean`
- ResidueField directory: `Defs.lean`, `Basic.lean`, `Ideal.lean`, `Instances.lean`, `Fiber.lean`, `Polynomial.lean`

### Other Key Locations
- `Field.exists_primitive_element`: `Mathlib/FieldTheory/PrimitiveElement.lean`
- `Algebra.IsSeparable`: `Mathlib/FieldTheory/Separable.lean:564`
- Nakayama (`Submodule.le_of_le_smul_of_le_jacobson_bot`): `Mathlib/RingTheory/Nakayama.lean:146`
- `Ideal.height`: `Mathlib/RingTheory/Ideal/Height.lean:41`
- `Polynomial.aeval_add_of_sq_eq_zero`: `Mathlib/Algebra/Polynomial/Taylor.lean:170`
- `OrzechProperty.injective_of_surjective_endomorphism`: `Mathlib/RingTheory/OrzechProperty.lean:98`
- `Algebra.adjoin_image`: `Mathlib/RingTheory/Adjoin/Basic.lean` — `adjoin R (f '' s) = (adjoin R s).map f`
- `Ideal.span_singleton_mul_left_unit`: `Mathlib/RingTheory/Ideal/Span.lean:111`

## Simplification Opportunities

### 4. `exists_adjoin_eq_top` (lines 323-353) — same adjoin_induction pattern
The manual 4-case adjoin_induction lifting from kR[β₀] to R[β] could similarly benefit from `adjoin_image`, but same AlgHom vs RingHom issue applies.

### 7. `maximalIdeal_eq_sup_of_etale_quotient` — verbose instance setup
Lines 84-101 set up many instances manually. Some may be inferable:
- `IsDomain (R ⧸ p)` from `Ideal.Quotient.isDomain`
- `IsLocalRing (R ⧸ p)` from `IsLocalRing.of_surjective'`
These are standard but Lean's instance search may not find them automatically due to the quotient algebra setup.

## Import Considerations for PRs

### PR 1 (natDegree_le' + mkOfAdjoinEqTop')
- Need to add `import Mathlib.LinearAlgebra.Charpoly.Basic` (or Matrix version)
- This is NOT in the transitive closure of `IsAdjoinRoot.lean`
- Risk: increases compile time for anything importing `IsAdjoinRoot`
- Alternative: put `natDegree_le'` in a new file and import it

### PR 2 (residue field helpers)
- `finrank_eq_finrank_residueField` needs: `Etale.Basic`, `Unramified.LocalRing`, `Smooth.Flat`, `LocalRing.Module`, `LocalRing.Quotient`
- First 3-4 lemmas only need: `ResidueField.Defs`, basic polynomial evaluation
- Consider splitting: pure local ring facts vs étale-specific facts

### PR 5 (exists_adjoin_eq_top)
- Needs: `PrimitiveElement`, `Unramified.LocalRing`, `Nakayama`, `ResidueField.Defs`
- Independent of PRs 1-4

### PR 6 (algebra_etale converse)
- Only needs: `Etale.StandardEtale`, `IsAdjoinRoot`
- Both already import each other's dependencies
- Should fit cleanly at end of `StandardEtale.lean`

## Naming Conventions for Mathlib

- Drop prime suffixes (`natDegree_le'` → `natDegree_le_finrank` or similar)
- Drop `Monogenic.` namespace prefix
- `_root_` prefixed names become their natural namespace
- Use `IsLocalRing.` namespace for local ring facts
- Use `Algebra.Etale.` or bare namespace for étale results
