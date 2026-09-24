/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import FKSEdgeThreshold.Standalone.Mathlib.StatementB

import FKSEdgeThreshold.Standalone.Mathlib.InlineFKSEdgeThresholdProof
import GraphDimension.Extremal.FKS.Theorem3

/-!
# Proof of statement B

The inlined placement condition is `SimpleGraph.UnitDistEmbeddable`. The edge bound is
`SimpleGraph.unitDistEmbeddable_of_ncard_edgeSet_lt`, and `K_{d+2}` is the same obstruction
as in the inline statement.
-/

public section

namespace FKSEdgeThreshold.StatementB

open SimpleGraph

theorem edgeThreshold.proof : edgeThreshold := by
  intro d hd
  refine ⟨fun n G hcard => ?_, ?_, ?_⟩
  · simpa [UnitDistEmbeddable] using (G.unitDistEmbeddable_of_ncard_edgeSet_lt hd hcard)
  · simpa using FKSEdgeThreshold.Bridge.ncard_edgeSet_completeGraph (d + 2)
  · simpa [UnitDistEmbeddable] using
      FKSEdgeThreshold.Bridge.not_unitDistEmbeddable_completeGraph_add_two d

theorem edgeThreshold.drop1.proof : edgeThreshold.drop1 :=
  edgeThreshold.dropHdim

theorem edgeThreshold.witness.proof : edgeThreshold.witness := by
  refine ⟨edgeThreshold.proof, ?_⟩
  refine ⟨4, 0, ⊥, by decide, ?_⟩
  simp only [edgeSet_bot, Set.ncard_empty, Nat.reduceAdd]
  decide

end FKSEdgeThreshold.StatementB
