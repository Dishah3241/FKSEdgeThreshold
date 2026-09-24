/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import FKSEdgeThreshold.Standalone.Mathlib.StatementA
public import FKSEdgeThreshold.Standalone.Mathlib.StatementB

/-!
# Equivalence of Statements A and B

`FKSEdgeThreshold.StatementA.edgeThreshold` names the placement condition through the
predicate `FKSEdgeThreshold.StatementA.UnitDistanceRealizable`, while
`FKSEdgeThreshold.StatementB.edgeThreshold` inlines the same condition. This file imports
both statements untouched and proves the equivalence: first between the placement
predicate and its inlined form, then between the two full statements.
-/

@[expose] public section

namespace FKSEdgeThreshold.Stage1.Equivalence

/-- Statement A's placement predicate is exactly the placement condition that Statement B
inlines: the vertices admit an injective placement in `EuclideanSpace ℝ (Fin d)` under
which every edge has length exactly `1`. -/
theorem unitDistanceRealizableIff {d : ℕ} {V : Type*} (G : SimpleGraph V) :
    FKSEdgeThreshold.StatementA.UnitDistanceRealizable d G ↔
      ∃ p : V → EuclideanSpace ℝ (Fin d),
        Function.Injective p ∧ ∀ v w : V, G.Adj v w → dist (p v) (p w) = 1 :=
  Iff.rfl

/-- Statements A and B are the same claim. Both quantify over `d : ℕ` under `4 ≤ d`, and
inside that conjunction all three conjuncts agree: A writes the binomial coefficient as
`Nat.choose (d + 2) 2` where B writes `(d + 2).choose 2`, the same term, and A names the
placement condition through `UnitDistanceRealizable` where B inlines it. -/
theorem edgeThresholdIff :
    FKSEdgeThreshold.StatementA.edgeThreshold ↔ FKSEdgeThreshold.StatementB.edgeThreshold := by
  constructor
  · intro h d hd
    obtain ⟨hreal, hK, hnoK⟩ := h d hd
    exact ⟨fun n G hG => (unitDistanceRealizableIff G).mp (hreal n G hG), hK,
      fun h => hnoK ((unitDistanceRealizableIff _).mpr h)⟩
  · intro h d hd
    obtain ⟨hreal, hK, hnoK⟩ := h d hd
    exact ⟨fun n G hG => (unitDistanceRealizableIff G).mpr (hreal n G hG), hK,
      fun h => hnoK ((unitDistanceRealizableIff _).mp h)⟩

end FKSEdgeThreshold.Stage1.Equivalence
