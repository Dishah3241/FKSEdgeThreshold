# Compass list

The declarations whose meaning decides whether the statement says what Frankl, Kupavskii and
Swanepoel proved. This is the owner's whole review surface. Everything else, including the whole
proof interior and the GraphDimension library, is checked by the kernel and the gates.

The project declarations are in `FKSEdgeThreshold/Standalone/Mathlib/InlineFKSEdgeThreshold.lean`,
namespace `FKSEdgeThreshold.Standalone.Mathlib.InlineFKSEdgeThreshold`. Rows 8–11 are Mathlib's.

**Owner sign-off: not yet given.** Any change to a row cancels a sign-off.

- The statement is authored, not inherited: `formal-conjectures` does not state it. Stage 1 wrote it
  twice, blind, from the paper: statement A by cursor (Grok 4.7), statement B by codex (gpt-6-sol).
  pi (glm-5.3-flash), a third lineage, proved `A ↔ B` in Lean
  (`FKSEdgeThreshold/Stage1/Equivalence.lean`). The frozen statement is A, and the kernel checks that too
  (`inlineIffStatementA`, `Iff.rfl`, in the same file).
- Stage 1's briefs fixed the reading of the paper in advance (finite simple graphs, injective placements,
  unconstrained non-edges, `d ≥ 4`, the `K_{d+2}` clause). So `A ↔ B` guards against encoding drift, not
  against a misreading of the paper; this list and the independent review are that check.
- The proof reaches the statement through the library's `SimpleGraph.UnitDistEmbeddable`, whose
  body is row 1's. The kernel identifies them (`unitDistanceRealizable_iff`, `Iff.rfl`), so that bridge
  needs no row.

| # | Declaration | Must mean | Check |
|---|---|---|---|
| 1 | `UnitDistanceRealizable d G` | an **injective** placement of the vertices in `ℝᵈ` with every edge at distance one | Non-edges are unconstrained, which is the source's reading (Erdős–Harary–Tutte), not the stricter unit-distance *graph*. The placement need not span `ℝᵈ`. |
| 2 | `edgeThreshold` | for every `d ≥ 4`: every finite simple graph with **fewer than** `C(d + 2, 2)` edges is realizable in `ℝᵈ`; `K_{d+2}` has exactly `C(d + 2, 2)` edges; `K_{d+2}` is not realizable in `ℝᵈ` | Together, `f(d) = C(d + 2, 2)` (FKS Theorem 3 with its sharpness remark). The bound is strict. `SimpleGraph (Fin n)` for every `n` covers every finite graph up to relabelling, including `n = 0`. |
| 3 | `FKSEdgeThreshold.Palomar.target` | exactly row 2 | It is `edgeThreshold` itself, with no extra hypothesis. `Solution.lean` proves it. |
| 4 | `edgeThreshold.witness` | at `d = 4`, `K₆` has `15` edges and is not realizable in `ℝ⁴`, and the claim holds | Guards against vacuity: the non-realizable example exists at the boundary. |
| 5 | `edgeThreshold.drop1` | without `4 ≤ d` the claim is false | At `d = 0`, two isolated vertices have no injective placement in `ℝ⁰`, yet `0 < C(2, 2) = 1`. Shows the hypothesis is load-bearing. |
| 6 | `UnitDistanceRealizable.separating`, first half | the star `K₁,₃` has a non-injective unit-length map into `ℝ¹` but no injective one | Separates row 1 from the reading without injectivity. |
| 7 | `UnitDistanceRealizable.separating`, second half | `K₃` has an injective map into `ℝ¹` with every edge **at most** one, but none with every edge exactly one | Separates row 1 from the reading "length at most one". |
| 8 | Mathlib `SimpleGraph.completeGraph (Fin (d + 2))` | `K_{d+2}` | Every two distinct vertices are adjacent. |
| 9 | Mathlib `G.edgeSet.ncard` | the number of edges | `ncard` is `0` on an infinite set, but every graph here is on `Fin n`, so this is the true count. |
| 10 | Mathlib `dist` on `EuclideanSpace ℝ (Fin d)` | the Euclidean (L²) distance | `EuclideanSpace` is `PiLp 2`, so `dist` is the L² norm of the difference. The plain function type `Fin d → ℝ` would carry the sup metric instead, a different, wrong reading. |
| 11 | Mathlib `Nat.choose (d + 2) 2` | the binomial coefficient `C(d + 2, 2) = (d + 2)(d + 1)/2` | `28` at `d = 6`, `15` at `d = 4`. |

Not in scope: FKS Theorem 3's second sentence, about placements on the sphere of radius `1/√2`,
is proved in the library as `SimpleGraph.fksStatement`, but it is not part of this statement.
