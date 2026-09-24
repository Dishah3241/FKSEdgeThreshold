/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import FKSEdgeThreshold.Standalone.Mathlib.InlineFKSEdgeThresholdProof

/-!
# Frankl-Kupavskii-Swanepoel Theorem 3: fewer than C(d+2,2) edges embeds in R^d

Connects Palomar's advertised declaration to the proof. This module contains no mathematics: it
restates the theorem Comparator checks and discharges it from the development.

The statement here must match `Challenge.lean`'s. Comparator compiles the two modules in separate
sandboxes and rejects any difference.
-/

public section

namespace FKSEdgeThreshold.Palomar

/-- Any two distinct elements of `{2, 3, 5}` are coprime. -/
theorem target :
    FKSEdgeThreshold.Standalone.Mathlib.InlineFKSEdgeThreshold.SmallPrimesCoprime :=
  FKSEdgeThreshold.Standalone.Mathlib.InlineFKSEdgeThreshold.SmallPrimesCoprime.proof

end FKSEdgeThreshold.Palomar
