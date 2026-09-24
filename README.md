# Graphs with fewer than C(d + 2, 2) edges have unit-distance representations in ℝᵈ

A Lean 4 proof of Theorem 3 of Frankl, Kupavskii and Swanepoel, *Embedding graphs in Euclidean
space* (J. Combin. Theory Ser. A 171 (2020) 105146, [arXiv:1802.03092](https://arxiv.org/abs/1802.03092)):
for every `d ≥ 4`, every finite simple graph with fewer than `C(d + 2, 2)` edges has a
unit-distance representation in `ℝᵈ`, and `K_{d+2}`, which has exactly `C(d + 2, 2)` edges, has
none.

> A **unit-distance representation** of a graph in `ℝᵈ` places its vertices at distinct points so
> that every edge is a unit segment; non-edges may also be at distance one (Erdős, Harary and Tutte,
> 1965). Write `f(d)` for the least number of edges of a graph with no such representation in `ℝᵈ`.
> The theorem says `f(d) = C(d + 2, 2)` for every `d ≥ 4`, answering a question of Erdős and
> Simonovits (1980).

| | |
|---|---|
| Proof | complete: no `sorry`; only `propext`, `Classical.choice` and `Quot.sound` |
| Comparator | accepted by Lean's kernel and by NanoDa ([record](docs/comparator-2026-09-23.md)) |
| Library | [GraphDimension](https://github.com/Dishah3241/GraphDimension), which Lake fetches at the revision pinned in `lake-manifest.json`; the proof is `SimpleGraph.unitDistEmbeddable_of_ncard_edgeSet_lt` there |
| Statement review | the statement was written twice, independently, and the two versions are proved equivalent in Lean (`FKSEdgeThreshold/Stage1/`); the owner signed the [Compass list](docs/compass.md) |
| Review | an independent, read-only review found no misformalization ([record](docs/review-2026-09-23.md)) |
| Blueprint | [web](https://dishah3241.github.io/FKSEdgeThreshold/), built by CI from `blueprint/src/content.tex` and checked against the Lean by `leanblueprint checkdecls` |
| `formal-conjectures` link | none: the statement is not in `formal-conjectures` |
| Mathlib | candidate lemmas are recorded for later proposal; no pull request is open |
| Palomar entry | not yet submitted |

## The statement

`FKSEdgeThreshold/Standalone/Mathlib/InlineFKSEdgeThreshold.lean` states the claim with Mathlib
alone; `Challenge.lean` repeats it and `Solution.lean` proves it:

```lean
def UnitDistanceRealizable (d : ℕ) {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ f : V → EuclideanSpace ℝ (Fin d),
    Function.Injective f ∧ ∀ u v : V, G.Adj u v → dist (f u) (f v) = 1

noncomputable def edgeThreshold : Prop :=
  ∀ d : ℕ, 4 ≤ d →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        G.edgeSet.ncard < Nat.choose (d + 2) 2 → UnitDistanceRealizable d G) ∧
      (SimpleGraph.completeGraph (Fin (d + 2))).edgeSet.ncard = Nat.choose (d + 2) 2 ∧
      ¬ UnitDistanceRealizable d (SimpleGraph.completeGraph (Fin (d + 2)))
```

Finite simple graphs are represented as `SimpleGraph (Fin n)`, which covers every finite graph up to
relabelling. The paper's theorem also has a spherical clause, which the library proves as
`SimpleGraph.fksStatement` but which this statement does not include.

## The proof

The library follows the paper's induction on `d`, carrying both halves of the statement
`S(k)`: a graph with at most `g(k)` edges has a representation in `ℝᵏ`, and one on the sphere of
radius `1/√2` if it avoids `K_{k+1}` and `K_{k+2} − K₃`. The induction starts at `S(2)` and runs
through the paper's case analysis, with Lovász's partition lemma, FKS Proposition 2, and the
cross-polytope placement as supporting results.

One step of the published proof needed a repair. In Case 2 at `d = 3`, the paper deduces from an
edge count that the configuration has exactly `d + 3` vertices. That deduction fails at `d = 3`: the
library exhibits a seven-vertex counterexample (`SimpleGraph.exists_fks_case_two_extra_vertex`).
The theorem is unaffected. At `d = 3`, deleting the centre of the star that the count forces,
together with the maximum-degree vertex, leaves at most two edges, and the poles then place the
graph (`Extremal/FKS/CaseTwoBridge.lean` in the library).

## Checking it

Every gate below passes on the published commit. CI runs the same list.

```sh
lake build && lake exe axioms && lake exe fidelity && lake exe module-system \
  && lake exe standalone-mathlib && lake exe proof-links && lake exe style \
  && lake exe documentation && lake exe layering && lake exe palomar-compatibility \
  && scripts/check-palomar-challenge.sh && scripts/lint-env.sh \
  && leanblueprint checkdecls && scripts/audit-probes.sh
```

`formalization.yaml` records the sources, the AI assistance used for every phase, and the review.
