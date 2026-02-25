---
description: How to work with the Lean 4 monogenic extensions project
---

# Monogenic Extensions Project Workflow

## Project Location
The project is at `/Volumes/Extreme SSD/monogenic-extensions`.

## Key Files
- `Monogenic/MonogenicOfNonEtale.lean` - Main theorem (Lemma 3.1 from arXiv:2503.07846)
- `Monogenic/Generator.lean` - Helper lemmas including `deriv_isUnit_of_monogenic`
- `Monogenic/Basic.lean` - Basic definitions and `monogenic_of_univQuot`

## Building and Checking
// turbo
1. Run `lake env lean Monogenic/MonogenicOfNonEtale.lean 2>&1 | head -50` to check for errors
2. Wait for compilation to complete (typically 1-3 minutes)
3. Check output for errors vs warnings (warnings about `sorry` are expected during development)

## Important Type Considerations
- `Ideal S` is NOT the same as `Submodule R S` - use `q.restrictScalars R` to coerce
- `RingHom` is NOT the same as `AlgHom` - `Ideal.Quotient.mk` is a RingHom, not an AlgHom
- `Polynomial.aeval_mem_adjoin_singleton R β` takes the ring R and element β, NOT the polynomial
- `Ideal.mem_restrictScalars` may need `.mpr` or `.mp` to convert between membership types

## Mathlib Patterns
- `IsAdjoinRootMonic.mkOfAdjoinEqTop` constructs an `IsAdjoinRootMonic` from `Algebra.adjoin R {β} = ⊤`
- `Submodule.le_of_le_smul_of_le_jacobson_bot` is the Nakayama lemma for submodules
- `Algebra.adjoin_map` relates subalgebras under ring homomorphisms (requires AlgHom not RingHom)

## Common Errors and Fixes
1. **Type mismatch `Ideal S` vs `Submodule R S`**:
   - Use `q.restrictScalars R` to coerce an ideal to a submodule over R
   - For membership, use `Ideal.mem_restrictScalars.mpr` / `.mp`

2. **`Algebra.adjoin_map` requires AlgHom**:
   - `Ideal.Quotient.mk q` is a RingHom, not an AlgHom
   - May need to use `Ideal.Quotient.mkₐ` or work around this

3. **`eq_top_iff` rewrite direction**:
   - `eq_top_iff` rewrites `X = ⊤` to `⊤ ≤ X`
   - For `⊤ = X`, use `rw [eq_comm, eq_top_iff]`

4. **`aeval_mem_adjoin_singleton` usage**:
   - Correct: `Polynomial.aeval_mem_adjoin_singleton R β` (returns `aeval β p ∈ Algebra.adjoin R {β}`)
   - It takes the ring and element as arguments, the polynomial is implicit

## Current State (as of this session)
- Main theorem `monogenic_of_etale_height_one_quotient` has structure complete
- Case 1 proof (when f₁(B) generates) has `sorry` - needs Nakayama argument
- Case 2 proof (when f₁(B) doesn't generate) has `sorry` - needs Nakayama argument with B'
- Both cases need to properly handle `Submodule R S` vs `Ideal S` coercions
- The `IsIntegrallyClosed R₀` assumption is being kept (per user request)

## Mathematical Context
The paper arXiv:2503.07846 proves that under certain conditions, a finite extension of regular local rings is monogenic. The key steps:
1. Étale quotient map gives a monogenic residue field extension (primitive element theorem)
2. Lift the generator from the quotient
3. Use Nakayama's lemma to show the lift generates the whole ring
