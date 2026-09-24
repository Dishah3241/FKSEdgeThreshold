/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Set.Card

/-!
# Frankl–Kupavskii–Swanepoel edge threshold

Frankl, Kupavskii, and Swanepoel, *Embedding graphs in Euclidean space*, Theorem 3, for
`d > 3`: every graph with fewer than `C(d + 2, 2)` edges is realizable in Euclidean
`d`-space. The introduction records that `K_{d+2}` is not realizable in `ℝ^d` and
therefore `f(d) ≤ C(d + 2, 2)`, where `f(d)` is the least number of edges in a graph
that is not realizable in `ℝ^d`. For every integer `d > 3` the two assertions give
`f(d) = C(d + 2, 2)`.

The printed statement says "any graph" and does not say "finite" or "simple". Read as
allowing an arbitrary vertex set, the universal clause is false: a discrete graph of
cardinality greater than the continuum has no edges, hence fewer than `C(d + 2, 2)`
edges, and admits no injective map into `ℝ^d`. The proof deletes vertices of degree at
most `d - 2` until none remain, and it compares finite edge counts with
`g(d) = C(d + 2, 2) - 1` for `d ≥ 4`. That argument requires a finite simple graph.
This file states that reading. For a natural number, `d > 3` is `4 ≤ d`.

Edge counts are natural numbers, so "fewer than `C(d + 2, 2)`" is the same cutoff as
"at most `C(d + 2, 2) - 1`". The claim includes the boundary `d = 4`, where the
binomial coefficient is `C(6, 2) = 15`, and the boundary edge count
`C(d + 2, 2) - 1`. It does not assert that every graph with exactly `C(d + 2, 2)`
edges fails to be realizable: `K_{d+2}` fails, and it is a graph of that size, so the
least such size equals `C(d + 2, 2)`.

At `n = 0` the only simple graph on `Fin 0` has an empty edge set, so its edge count
is `0`. For every `d ≥ 4` one has `0 < C(d + 2, 2)`, and the claim asserts that this
graph is realizable. The empty function `Fin 0 → ℝ^d` is injective, and there is no
edge whose length must be `1`. The same clause asserts that every edgeless graph on
`Fin n` is realizable: there is no positive lower bound on the number of vertices or
edges. For `d ≥ 4` the codomain is infinite, so a finite injective placement exists.

`Challenge.lean` is generated from this file, up to the proof-link note, with
`scripts/palomar-challenge-footer.txt`.
-/

@[expose] public section

namespace FKSEdgeThreshold.Standalone.Mathlib.InlineFKSEdgeThreshold

/-- A simple graph is unit-distance realizable in Euclidean `d`-space when its vertices
admit an injective placement in `EuclideanSpace ℝ (Fin d)` under which every edge has
length exactly `1`.

This is realizability in `ℝ^d` as defined by Frankl–Kupavskii–Swanepoel. Their unit
distance graph has vertex set a subset of `ℝ^d`, so distinct vertices are distinct
points, and its edge set is contained in the set of pairs at distance `1`. A non-edge
may therefore have length `1`. The placement need not span all of `ℝ^d`, and `d` need
not be the least dimension in which a placement exists.

The empty graph on `Fin 0` is realizable in every dimension, including `d = 0`: the
empty function is injective and there is no edge to check. An edgeless graph on two
or more vertices is not realizable in `ℝ^0`, whose only point set is a singleton. -/
def UnitDistanceRealizable (d : ℕ) {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ f : V → EuclideanSpace ℝ (Fin d),
    Function.Injective f ∧ ∀ u v : V, G.Adj u v → dist (f u) (f v) = 1

/-- Separating examples for `UnitDistanceRealizable`.

The nearest weaker reading drops injectivity and keeps the unit-length condition on
edges. The star `K_{1,3}`, written as the complete bipartite graph with parts of size
`1` and `3`, has an edge. Sending the center to `0` and all three leaves to `1` in
`ℝ^1` makes every edge have length `1`, but the three leaves are not distinct. No
injective placement exists in `ℝ^1`: the three leaves would be distinct points of the
unit sphere about the center, and that sphere consists of two points.

The nearest weaker reading of "length exactly `1`" replaces the equality by `≤ 1`.
The triangle `K_3` has an edge. It has an injective placement in `ℝ^1` with all three
distances at most `1`, and it has no injective placement in `ℝ^1` with all three
distances equal to `1`. -/
def UnitDistanceRealizable.separating : Prop :=
  ((∃ u v : Fin 1 ⊕ Fin 3, (completeBipartiteGraph (Fin 1) (Fin 3)).Adj u v) ∧
      (∃ f : Fin 1 ⊕ Fin 3 → EuclideanSpace ℝ (Fin 1),
        ∀ a b : Fin 1 ⊕ Fin 3,
          (completeBipartiteGraph (Fin 1) (Fin 3)).Adj a b → dist (f a) (f b) = 1) ∧
      ¬ UnitDistanceRealizable 1 (completeBipartiteGraph (Fin 1) (Fin 3))) ∧
    ((∃ u v : Fin 3, (SimpleGraph.completeGraph (Fin 3)).Adj u v) ∧
      (∃ f : Fin 3 → EuclideanSpace ℝ (Fin 1),
        Function.Injective f ∧
          ∀ a b : Fin 3,
            (SimpleGraph.completeGraph (Fin 3)).Adj a b → dist (f a) (f b) ≤ 1) ∧
      ¬ UnitDistanceRealizable 1 (SimpleGraph.completeGraph (Fin 3)))

/-- For every natural number `d ≥ 4`, every finite simple graph with fewer than
`C(d + 2, 2)` edges is unit-distance realizable in `ℝ^d`, and the complete graph
`K_{d+2}` has exactly `C(d + 2, 2)` edges and is not.

Finite simple graphs are represented as `SimpleGraph (Fin n)` for `n : ℕ`. Every
finite simple graph arises this way up to a bijection of vertices, and an injective
placement transports along that bijection. The quantifier includes `n = 0` and every
edgeless graph. The inequality on the number of edges is strict. Because that number
is a natural number, the graphs asserted to be realizable are exactly those with at
most `C(d + 2, 2) - 1` edges, including `K_{d+2}` minus one edge.

The conjunction is the statement `f(d) = C(d + 2, 2)`. The first clause says that no
finite simple graph with fewer edges fails to be realizable, so every unrealizable
example has at least `C(d + 2, 2)` edges. The second and third clauses say that
`K_{d+2}` is an unrealizable example with exactly that many edges. Hence that number
is the least element of the set of edge counts of finite simple graphs with no
unit-distance representation in `ℝ^d`. -/
noncomputable def edgeThreshold : Prop :=
  ∀ d : ℕ, 4 ≤ d →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        G.edgeSet.ncard < Nat.choose (d + 2) 2 → UnitDistanceRealizable d G) ∧
      (SimpleGraph.completeGraph (Fin (d + 2))).edgeSet.ncard = Nat.choose (d + 2) 2 ∧
      ¬ UnitDistanceRealizable d (SimpleGraph.completeGraph (Fin (d + 2)))

/-- Dropping `4 ≤ d` leaves a false statement.

The resulting claim quantifies over every natural number, including `d = 3` and
`d = 0`. At `d = 3` the same paper records that `K_{3,3}` is not realizable in `ℝ^3`
and that `f(3) ≤ 9 < C(5, 2)`. At `d = 0`, `C(2, 2) = 1`, and the edgeless graph on
two vertices has no edge and no injective placement in `ℝ^0`. -/
noncomputable def edgeThreshold.drop1 : Prop :=
  ¬ ∀ d : ℕ,
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)),
          G.edgeSet.ncard < Nat.choose (d + 2) 2 → UnitDistanceRealizable d G) ∧
        (SimpleGraph.completeGraph (Fin (d + 2))).edgeSet.ncard = Nat.choose (d + 2) 2 ∧
        ¬ UnitDistanceRealizable d (SimpleGraph.completeGraph (Fin (d + 2)))

/-- The hypothesis `4 ≤ d` is satisfiable at the boundary `d = 4`, where
`C(6, 2) = 15` and `K_6` has fifteen edges, and the claim itself holds.

The instance is not the empty graph: `K_6` has edges. The numerical conjuncts are
the boundary values of the dimension hypothesis and of the binomial cutoff. -/
noncomputable def edgeThreshold.witness : Prop :=
  ∃ d : ℕ, 4 ≤ d ∧ d = 4 ∧ Nat.choose (d + 2) 2 = 15 ∧
    (SimpleGraph.completeGraph (Fin (d + 2))).edgeSet.ncard = 15 ∧
    ¬ UnitDistanceRealizable d (SimpleGraph.completeGraph (Fin (d + 2))) ∧
    edgeThreshold

end FKSEdgeThreshold.Standalone.Mathlib.InlineFKSEdgeThreshold

namespace FKSEdgeThreshold.Palomar

set_option warningAsError false in
/-- For every `d ≥ 4`, every finite simple graph with fewer than `C(d + 2, 2)` edges is
unit-distance realizable in `ℝ^d`, and `K_{d+2}` has exactly that many edges and is not. -/
theorem target :
    FKSEdgeThreshold.Standalone.Mathlib.InlineFKSEdgeThreshold.edgeThreshold := by
  sorry

end FKSEdgeThreshold.Palomar
