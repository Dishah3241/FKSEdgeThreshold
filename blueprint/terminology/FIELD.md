# Field vocabulary

Terminology below is taken from Frankl, Kupavskii, and Swanepoel, *Embedding graphs in Euclidean
space*, arXiv:1802.03092 (`main.tex`).

## Part 0 — Terms this project uses

| Term | Meaning | Source, at a pinpoint |
|---|---|---|
| unit distance graph | A graph whose vertex set is a subset of `ℝ^d` and whose edges are unit-distance pairs. The edge set need not contain every unit-distance pair. | `main.tex`, definition at lines 55–56 |
| realizable | A graph isomorphic to a unit distance graph on a subset of `ℝ^d` (or of the sphere). Distinct vertices are distinct points, so the placement is injective. | `main.tex`, definition at line 57 |
| `f(d)` | The least number of edges of a graph that is not realizable in `ℝ^d`. | `main.tex`, definition at line 82 |
| Euclidean dimension | The least `k` such that the graph is realizable in `ℝ^k`. | `main.tex`, definition at line 62 |

`edgeThreshold` is the formal name of the claim `f(d) = C(d + 2, 2)` for every natural number
`d ≥ 4`, for finite simple graphs. The paper states that equality, for `d > 3`, as the first
clause of the theorem labeled `d+2 choose 2` (`main.tex`, line 91), together with the bound
`f(d) ≤ C(d + 2, 2)` from `K_{d+2}` (line 85).

## Part 1 — Terms deliberately avoided

| Term | Why avoided / which convention chosen | Source |
|---|---|---|
| unit distance graph, as requiring every unit-distance pair to be an edge | The paper explicitly allows non-edges at distance one. The predicate only constrains edges. | `main.tex`, lines 55–56 |
| spherical dimension, `f_D`, `f_SD` | The frozen statement is the Euclidean edge threshold. The spherical clause of the same theorem is not part of it. | `main.tex`, lines 62 and 91, and the definition of `f_D` at lines 98–101 |

## Spelling

Lean declaration names follow Mathlib spelling. Reader-facing prose and the blueprint follow the
field's spelling. Where those differ, both are correct in their place — Lean writes
`Factorization` while prose writes "factorisation" — and cited titles stay verbatim.
