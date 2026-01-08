# Jarod's branch of monogenic

I've updated to the latest version Lean & mathlib.  The current files won't compile in the Lean version `lean4:v4.25.0-rc2` of the master branch.  You should either run `lake update` in your version, or switch to my branch and run `lake exe cache get`.

# There are three new files to look at:
* `Monogenic/Basic.lean` defines monogenic extensions and gives an equivalence, which is formulated close to how `Lemma 3.2` is stated in `Monogenic.lean`
* `Monogenic/WeakMonogenicExtension-claude.lean` proves a version of `Lemma 3.2` called  `FiniteInjectiveEtale_IsMonogenic` with extra hypotheses that Claude added (see below)
* `Monogenic/WeakMonogenicExtension.lean` has the same version of `Lemma 3.2` with no additional domain or integrally closed hypotheses, but it has one `sorry`, namely the injectivity of $R[x]/(f) \to S$.

# Some comments on the mathematics
* The notion of a `monogenic extension` is closely related to a `standard etale` map.  This is defined in https://stacks.math.columbia.edu/tag/00UB:  $R->S$ is standard etale if there exist an $R$-algebra isomorphism $S \cong R[x]_g/(f)$ where $f$ is monic and the derivative $f'$ is a unit in $R[x]_g/(f)$.  This is proven in this PR https://github.com/leanprover-community/mathlib4/blob/c6f1b19c0e33c7be0155605faba9e84d61299690/Mathlib/CFT/IsStandardEtale.lean#L828, but it doesn't seem to incorporated into Mathlib yet
* `Lemma 3.2` is closely related to the fact https://stacks.math.columbia.edu/tag/00UE: for any ring map R->S that is etale at a prime $q \subseteq S$, there exists $g \in S$ with $g \notin q$ such that $R -> S_g$ is standard etale.  The slogan here is that every etale map is locally standard etale. 
* The proof of Lemma 3.2 in the paper needs to use the etaleness in a fundamental way, as it's not true for any finite injective map of local rings.
* In the proof of Lemma 3.2, Nakayama's lemma can be used to show that the natural map $R[x]/(f) \to S, x \mapsto \beta$ is surjective.  I think it takes more work to get injectivity and this where etaleness needs to be used.  The challenging thing to show is that if a polynomial $g \in R[x]$ satisfies $g(\beta) = 0$, then $f | g$.  When $R$ and $S$ are domains and  R is integrally closed, this follows from a fact about minimial polynomials, which is `minpoly.isIntegrallyClosed_dvd` in mathlib (I couldn't locate it in the Stacks Project).  I think the strategy would be to show that $f'(\beta)$ is a unit as in the last line of the proof in the paper.  This ensures that $R -> R[x]/(f)$ is finite etale, which further implies that the surjective map $R[x]/(f) -> S$ is finite etale.  Since the map on residue fields is an isomorphism, it is a finite etale map of degree $1$, hence an isomorphism.

# Some comments on the formalization
* In order to write code closer to the quality of Mathlib, it is useful to look through Mathlib.  In this case, files in `Mathlib/RingTheory/Etale` are useful, especially `StandardEtale.lean` and the PR above for Tag 00UB.

# Some comments on the workflow
* I used Claude Code, Harmonic's Aristotle, and Gemini CLI.  Several new results relating to this project have been added to mathlib over the last few months.  I think this explains why Harmonic's Aristotle did not perform on this code because Aristotle uses an older version of Mathlib.  Claude Code performed pretty well and sometimes Gemini CLI was helpful.  These have the advantage of Aristotle in that they keep producing code that you can examine and edit during the process, often leaving sorries that you ask other agents to fill in, while Aristotle often will simply report failure and doesn't often (although sometimes it does) give a partial formalization.
* Claude code automatically added the hypothesis into Lemma_3_2_weak that R and S were domains and that R is integrally closed.  This allowed it to use the fact that for the map $R[x]/(f) -> S$ sending $x$ to $\beta \in S$ is injective.