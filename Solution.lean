/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import FKSEdgeThreshold.Standalone.Mathlib.InlineFKSEdgeThresholdProof

/-!
# Frankl–Kupavskii–Swanepoel edge threshold

Connects Palomar's advertised declaration to the proof. This module contains no mathematics: it
restates the theorem Comparator checks and discharges it from the development.

The statement here must match `Challenge.lean`'s. Comparator compiles the two modules in separate
sandboxes and rejects any difference.
-/

public section

namespace FKSEdgeThreshold.Palomar

/-- For every `d ≥ 4`, every finite simple graph with fewer than `C(d + 2, 2)` edges is
unit-distance realizable in `ℝ^d`, and `K_{d+2}` has exactly that many edges and is not. -/
theorem target :
    FKSEdgeThreshold.Standalone.Mathlib.InlineFKSEdgeThreshold.edgeThreshold :=
  FKSEdgeThreshold.Standalone.Mathlib.InlineFKSEdgeThreshold.edgeThreshold.proof

end FKSEdgeThreshold.Palomar
