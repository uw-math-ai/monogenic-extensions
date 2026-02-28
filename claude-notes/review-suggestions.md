# Review Suggestions for Mathlib Readiness

## 3. Consolidate PRs 2+3+4 into one or two PRs

The dependency chain PR 2 → PR 3 → PR 4 is very linear and each PR is tiny:
- PR 2: 2 lemmas
- PR 3: 1 lemma
- PR 4: 1 lemma

Each has its own file placement, namespace, imports section — that's a lot of reviewer overhead for 4 total declarations. Suggestions:
- **Option A**: Merge into 2 PRs: PR 2 (residue field basics) + PR 3+4 (minpoly descends + unit derivative). The latter is a natural "separability gives unit derivative" package.
- **Option B**: Merge all into one PR — "Residue field properties for étale local extensions." This is still small (4 lemmas, ~80 lines of proof) and very cohesive.

## 6. Consider whether `exists_isAdjoinRootMonic_of_principal_adjust` can be simplified

This lemma has 9 hypotheses (q, q₀, hq₀, B, f₁, h_f₁B_in_q, h_deriv_not_in_ms, h_ms_eq, h_adj, h_not_gen). That's a lot. The negation hypothesis `h_not_gen` is especially awkward — it's used only to show `a ∈ m_S` (when it isn't, the calling code would have already handled that case).

This suggests the case split should be inside the main theorem rather than at the API boundary. You could potentially inline this lemma into `exists_isAdjoinRootMonic_of_quotientMap_etale`, or restructure it to take the already-proven `a ∈ m_S` as a positive hypothesis instead of the double negation.

## 7. Naming: `natDegree_le'` should probably not use a prime

The prime `'` usually means "variant with slightly different hypotheses" in Mathlib, and it's a bit unusual for brand-new results. Since this genuinely generalizes `minpoly.natDegree_le` (from fields to free modules), consider naming it something more descriptive like `minpoly.natDegree_le_finrank` or just replacing the Mathlib name (since the generalization subsumes the original). Reviewers may want to see this replace the existing lemma rather than sit beside it with a prime.

Similarly, `mkOfAdjoinEqTop'` might better be named `mkOfAdjoinEqTop_of_free` or similar, to distinguish from the `IsIntegrallyClosed` version by what's assumed rather than by a prime.

## 8. The `exists_adjoin_eq_top` proof could be slightly shorter

Lines 305-309 could be simplified. Currently you construct `h_adjoin_top` by manually converting between `IntermediateField.adjoin` and `Algebra.adjoin`, then rewriting. Since you only need `Algebra.adjoin kR {β₀} = ⊤` (which `Field.exists_primitive_element` gives via intermediate fields), consider whether the conversion step can be streamlined or if there's a more direct Mathlib API.

## 9. `Ideal.pow_le_span_pow_sup` is a general result — good standalone PR candidate

This pure ideal arithmetic lemma (`I = ⟨π⟩ ⊔ J → I^k ≤ ⟨π^k⟩ ⊔ J`) has no local ring hypotheses and could be a small, independent PR to `Mathlib.RingTheory.Ideal.Operations`. This is exactly the kind of small, self-contained lemma that gets merged quickly. Consider submitting it early as a "warmup PR" like 7a and 7b.

## 10. Consider the PR submission order strategically

Given the dependency graph, the fastest path to getting everything merged:

1. **Submit immediately in parallel**: PR 7a (height-one principal), PR 7b (Taylor), `Ideal.pow_le_span_pow_sup`, PR 6 (converse). These are all independent and self-contained.
2. **Next**: PR 1 (the key new result), PR 2 (or combined PR 2+3+4), PR 5.
3. **Finally**: PR 7c+7d (which depends on everything above).

This gets the independent pieces reviewed first while the dependent ones are still being polished.

## Summary of priorities

| Priority | Suggestion | Effort | Impact |
|----------|-----------|--------|--------|
| Medium | Consolidate PRs 2+3+4 | Low | Less reviewer overhead |
| Medium | Better names than primes (`'`) | Low | Avoids reviewer bikeshed |
| Low | Restructure `principal_adjust` hypotheses | Medium | Cleaner API |
| Low | Submit independent PRs first | — | Faster merging |
