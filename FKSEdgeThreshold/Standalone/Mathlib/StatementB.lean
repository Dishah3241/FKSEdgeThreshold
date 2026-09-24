module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Frankl–Kupavskii–Swanepoel's edge threshold

The edge threshold for injective unit-distance placements of finite simple graphs in Euclidean
space, including the complete-graph obstruction at equality.
-/

@[expose] public section

namespace FKSEdgeThreshold.StatementB

/-- Frankl–Kupavskii–Swanepoel's edge threshold, as a `Prop`. The manager converted the
author's `sorry` theorem into this definition, text unchanged, so that it can be imported
under `warningAsError`: for every `d ≥ 4`, every finite simple graph
with fewer than `C(d + 2, 2)` edges has an injective unit-distance placement in `ℝᵈ`, while
`K_(d + 2)` has exactly that many edges and has no such placement. Nonedges may also be at unit
distance. The quantifier over `n` includes `n = 0`: the empty graph has zero edges and its empty
placement is injective. The strict bound excludes graphs at equality, where `K_(d + 2)` is the
specified obstruction. -/
def edgeThreshold : Prop :=
  ∀ (d : ℕ), 4 ≤ d →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.edgeSet.ncard < (d + 2).choose 2 →
        ∃ p : Fin n → EuclideanSpace ℝ (Fin d),
          Function.Injective p ∧
            ∀ v w : Fin n, G.Adj v w → dist (p v) (p w) = 1) ∧
      (SimpleGraph.completeGraph (Fin (d + 2))).edgeSet.ncard =
        (d + 2).choose 2 ∧
      ¬ ∃ p : Fin (d + 2) → EuclideanSpace ℝ (Fin d),
          Function.Injective p ∧
            ∀ v w : Fin (d + 2),
              (SimpleGraph.completeGraph (Fin (d + 2))).Adj v w →
                dist (p v) (p w) = 1

/-- Dropping the anonymous hypothesis `4 ≤ d` leaves a false statement. At `d = 0` the edgeless
graph on two vertices has no injective placement in `ℝ⁰`. -/
def edgeThreshold.drop1 : Prop :=
  ¬ ∀ (d : ℕ),
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        G.edgeSet.ncard < (d + 2).choose 2 →
          ∃ p : Fin n → EuclideanSpace ℝ (Fin d),
            Function.Injective p ∧
              ∀ v w : Fin n, G.Adj v w → dist (p v) (p w) = 1) ∧
        (SimpleGraph.completeGraph (Fin (d + 2))).edgeSet.ncard =
          (d + 2).choose 2 ∧
        ¬ ∃ p : Fin (d + 2) → EuclideanSpace ℝ (Fin d),
            Function.Injective p ∧
              ∀ v w : Fin (d + 2),
                (SimpleGraph.completeGraph (Fin (d + 2))).Adj v w →
                  dist (p v) (p w) = 1

/-- The claim holds, and its dimension and edge-count hypotheses have a joint instance: the empty
graph on `Fin 0` at `d = 4`. -/
def edgeThreshold.witness : Prop :=
  edgeThreshold ∧
    ∃ (d n : ℕ) (G : SimpleGraph (Fin n)),
      4 ≤ d ∧ G.edgeSet.ncard < (d + 2).choose 2

/-- Without `d ≥ 4`, the edgeless two-vertex graph cannot be injected into `ℝ⁰`. -/
theorem edgeThreshold.dropHdim :
    ¬ ∀ (d : ℕ),
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        G.edgeSet.ncard < (d + 2).choose 2 →
          ∃ p : Fin n → EuclideanSpace ℝ (Fin d),
            Function.Injective p ∧
              ∀ v w : Fin n, G.Adj v w → dist (p v) (p w) = 1) ∧
        (SimpleGraph.completeGraph (Fin (d + 2))).edgeSet.ncard =
          (d + 2).choose 2 ∧
        ¬ ∃ p : Fin (d + 2) → EuclideanSpace ℝ (Fin d),
            Function.Injective p ∧
              ∀ v w : Fin (d + 2),
                (SimpleGraph.completeGraph (Fin (d + 2))).Adj v w →
                  dist (p v) (p w) = 1 := by
  intro h
  have hsmall : (⊥ : SimpleGraph (Fin 2)).edgeSet.ncard < (0 + 2).choose 2 := by simp
  obtain ⟨p, hp, _⟩ := (h 0).1 2 ⊥ hsmall
  have hneq : (0 : Fin 2) ≠ 1 := by decide
  exact hneq (hp (Subsingleton.elim (p 0) (p 1)))

end FKSEdgeThreshold.StatementB

/-!
## Formal proof

Proved in `StatementBProof`.

* `edgeThreshold` → `edgeThreshold.proof`
* `drop1` → `drop1.proof`
* `witness` → `witness.proof`
-/
