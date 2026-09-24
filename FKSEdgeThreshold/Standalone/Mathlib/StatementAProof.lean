/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import FKSEdgeThreshold.Standalone.Mathlib.StatementA

import FKSEdgeThreshold.Standalone.Mathlib.InlineFKSEdgeThresholdProof

/-!
# Proofs of statement A

Statement A and the inline statement have the same bodies, so each companion is the
corresponding inline proof.
-/

public section

open FKSEdgeThreshold.Standalone.Mathlib

namespace FKSEdgeThreshold.StatementA

theorem UnitDistanceRealizable.separating.proof : UnitDistanceRealizable.separating :=
  InlineFKSEdgeThreshold.UnitDistanceRealizable.separating.proof

theorem edgeThreshold.proof : edgeThreshold :=
  InlineFKSEdgeThreshold.edgeThreshold.proof

theorem edgeThreshold.drop1.proof : edgeThreshold.drop1 :=
  InlineFKSEdgeThreshold.edgeThreshold.drop1.proof

theorem edgeThreshold.witness.proof : edgeThreshold.witness :=
  InlineFKSEdgeThreshold.edgeThreshold.witness.proof

end FKSEdgeThreshold.StatementA
