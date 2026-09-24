/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import FKSEdgeThreshold.Standalone.Mathlib.InlineFKSEdgeThreshold
public import GraphDimension.Basic

import GraphDimension.Extremal.FKS.Theorem3
import GraphDimension.Geometry.CompleteGraph
import GraphDimension.Geometry.Equilateral
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Proof of the Frankl–Kupavskii–Swanepoel edge threshold

`UnitDistanceRealizable` matches `SimpleGraph.UnitDistEmbeddable`. Fewer than `C(d + 2, 2)`
edges gives a placement by `SimpleGraph.unitDistEmbeddable_of_ncard_edgeSet_lt`. The complete
graph `K_{d+2}` has `C(d + 2, 2)` edges, and `SimpleGraph.hasUnitDistDim_completeGraph` rules
out a placement in `ℝ^d`.
-/

public section

namespace FKSEdgeThreshold.Bridge

open SimpleGraph

/-- The complete graph on `n` vertices has `n` choose `2` edges. -/
theorem ncard_edgeSet_completeGraph (n : ℕ) :
    (completeGraph (Fin n)).edgeSet.ncard = Nat.choose n 2 := by
  rw [completeGraph_eq_top]
  have hfin : (⊤ : SimpleGraph (Fin n)).edgeSet.ncard =
      Finset.card (⊤ : SimpleGraph (Fin n)).edgeFinset := by
    rw [edgeFinset_card, Set.fintypeCard_eq_ncard]
  rw [hfin, card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]

/-- `K_{d+2}` has no injective unit-distance placement in `ℝ^d`. -/
theorem not_unitDistEmbeddable_completeGraph_add_two (d : ℕ) :
    ¬ (completeGraph (Fin (d + 2))).UnitDistEmbeddable d := by
  intro h
  rw [completeGraph_eq_top] at h
  have hdim := hasUnitDistDim_completeGraph (d + 2)
  have hAnd :
      (d + 2) - 1 ∈ {m | (⊤ : SimpleGraph (Fin (d + 2))).UnitDistEmbeddable m} ∧
        (d + 2) - 1 ∈
          lowerBounds {m | (⊤ : SimpleGraph (Fin (d + 2))).UnitDistEmbeddable m} := by
    simpa [HasUnitDistDim, IsLeast] using hdim
  rw [mem_lowerBounds] at hAnd
  have hle : (d + 2) - 1 ≤ d := hAnd.2 d h
  omega

end FKSEdgeThreshold.Bridge

namespace FKSEdgeThreshold.Standalone.Mathlib.InlineFKSEdgeThreshold

open SimpleGraph

/-- `UnitDistanceRealizable` is `SimpleGraph.UnitDistEmbeddable`: the two definitions have the
same body. -/
theorem unitDistanceRealizable_iff (d : ℕ) {V : Type*} (G : SimpleGraph V) :
    UnitDistanceRealizable d G ↔ G.UnitDistEmbeddable d :=
  Iff.rfl

private lemma dist_fin1 (x y : EuclideanSpace ℝ (Fin 1)) : dist x y = |x 0 - y 0| := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_one, Real.dist_eq, Real.sqrt_sq_eq_abs, abs_abs]

private lemma eq_of_coord_fin1 (x y : EuclideanSpace ℝ (Fin 1)) (h : x 0 = y 0) : x = y := by
  ext i
  have hi : i = 0 := Subsingleton.elim i 0
  rw [hi]
  exact h

private noncomputable def star_point (v : Fin 1 ⊕ Fin 3) : EuclideanSpace ℝ (Fin 1) :=
  EuclideanSpace.single 0 (if v.isLeft then (0 : ℝ) else 1)

private lemma star_dist (a b : Fin 1 ⊕ Fin 3)
    (hab : (completeBipartiteGraph (Fin 1) (Fin 3)).Adj a b) :
    dist (star_point a) (star_point b) = 1 := by
  cases a with
  | inl _ =>
    cases b with
    | inl _ => simp [completeBipartiteGraph_adj] at hab
    | inr _ =>
      rw [dist_fin1]
      simp [star_point, PiLp.single_eq_same, Sum.isLeft]
  | inr _ =>
    cases b with
    | inl _ =>
      rw [dist_fin1]
      simp [star_point, PiLp.single_eq_same, Sum.isLeft]
    | inr _ => simp [completeBipartiteGraph_adj] at hab

private lemma not_unitDistanceRealizable_star :
    ¬ UnitDistanceRealizable 1 (completeBipartiteGraph (Fin 1) (Fin 3)) := by
  intro h
  unfold UnitDistanceRealizable at h
  obtain ⟨f, hf, hdist⟩ := h
  let c : ℝ := (f (Sum.inl 0)) 0
  let g : Fin 3 → ℝ := fun i => (f (Sum.inr i)) 0
  have hg (i : Fin 3) : |g i - c| = 1 := by
    have hadj : (completeBipartiteGraph (Fin 1) (Fin 3)).Adj (Sum.inl 0) (Sum.inr i) := by
      simp [completeBipartiteGraph_adj]
    have hdi := hdist (Sum.inl 0) (Sum.inr i) hadj
    rw [dist_fin1, abs_sub_comm] at hdi
    simpa [c, g] using hdi
  have hslot (i : Fin 3) : g i = c + 1 ∨ g i = c - 1 := by
    rcases eq_or_eq_neg_of_abs_eq (hg i) with hEq | hEq
    · left
      linarith
    · right
      linarith
  have hne (i j : Fin 3) (hij : i ≠ j) : g i ≠ g j := by
    intro hge
    exact (hf.ne (Sum.inr_injective.ne hij))
      (eq_of_coord_fin1 _ _ (by simpa [g] using hge))
  have both_pos (i j : Fin 3) (hi : g i = c + 1) (hj : g j = c + 1) : i = j := by
    by_contra hij
    exact hne i j hij (hi.trans hj.symm)
  have both_neg (i j : Fin 3) (hi : g i = c - 1) (hj : g j = c - 1) : i = j := by
    by_contra hij
    exact hne i j hij (hi.trans hj.symm)
  rcases hslot 0 with h0 | h0 <;> rcases hslot 1 with h1 | h1 <;> rcases hslot 2 with h2 | h2
  · exact absurd (both_pos 0 1 h0 h1) (by decide : (0 : Fin 3) ≠ 1)
  · exact absurd (both_pos 0 1 h0 h1) (by decide : (0 : Fin 3) ≠ 1)
  · exact absurd (both_pos 0 2 h0 h2) (by decide : (0 : Fin 3) ≠ 2)
  · exact absurd (both_neg 1 2 h1 h2) (by decide : (1 : Fin 3) ≠ 2)
  · exact absurd (both_pos 1 2 h1 h2) (by decide : (1 : Fin 3) ≠ 2)
  · exact absurd (both_neg 0 2 h0 h2) (by decide : (0 : Fin 3) ≠ 2)
  · exact absurd (both_neg 0 1 h0 h1) (by decide : (0 : Fin 3) ≠ 1)
  · exact absurd (both_neg 0 1 h0 h1) (by decide : (0 : Fin 3) ≠ 1)

private noncomputable def triangle_point (i : Fin 3) : EuclideanSpace ℝ (Fin 1) :=
  EuclideanSpace.single 0 (((i : ℕ) : ℝ) / 2)

private lemma triangle_dist_le (a b : Fin 3) :
    dist (triangle_point a) (triangle_point b) ≤ 1 := by
  rw [dist_fin1]
  fin_cases a <;> fin_cases b <;> simp [triangle_point, PiLp.single_eq_same] <;> norm_num

private lemma triangle_injective : Function.Injective triangle_point := by
  intro a b h
  have hcoord := congrArg (fun p : EuclideanSpace ℝ (Fin 1) => p 0) h
  simp only [triangle_point, PiLp.single_eq_same] at hcoord
  fin_cases a <;> fin_cases b
  all_goals try norm_num at hcoord
  all_goals rfl

private lemma not_unitDistanceRealizable_triangle :
    ¬ UnitDistanceRealizable 1 (completeGraph (Fin 3)) := by
  intro h
  unfold UnitDistanceRealizable at h
  obtain ⟨f, -, hdist⟩ := h
  have hpw : Pairwise fun i j : Fin 3 => dist (f i) (f j) = 1 := by
    intro i j hij
    exact hdist i j (by simpa [completeGraph_eq_top, top_adj] using hij)
  have hcard := EuclideanGeometry.card_le_of_equilateral hpw
  simp only [Fintype.card_fin] at hcard
  omega

theorem UnitDistanceRealizable.separating.proof : UnitDistanceRealizable.separating := by
  unfold UnitDistanceRealizable.separating
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · exact ⟨Sum.inl 0, Sum.inr 0, by simp [completeBipartiteGraph_adj]⟩
  · exact ⟨star_point, star_dist⟩
  · exact not_unitDistanceRealizable_star
  · exact ⟨0, 1, by simp [completeGraph_eq_top, top_adj]⟩
  · exact ⟨triangle_point, triangle_injective, fun a b _ => triangle_dist_le a b⟩
  · exact not_unitDistanceRealizable_triangle

private lemma not_unitDistanceRealizable_complete (d : ℕ) :
    ¬ UnitDistanceRealizable d (completeGraph (Fin (d + 2))) := by
  intro h
  exact FKSEdgeThreshold.Bridge.not_unitDistEmbeddable_completeGraph_add_two d
    ((unitDistanceRealizable_iff d _).mp h)

theorem edgeThreshold.proof : edgeThreshold := by
  unfold edgeThreshold
  intro d hd
  refine ⟨fun n G hcard => ?_, ?_, not_unitDistanceRealizable_complete d⟩
  · exact (unitDistanceRealizable_iff d G).mpr
      (G.unitDistEmbeddable_of_ncard_edgeSet_lt hd hcard)
  · exact FKSEdgeThreshold.Bridge.ncard_edgeSet_completeGraph (d + 2)

theorem edgeThreshold.drop1.proof : edgeThreshold.drop1 := by
  unfold edgeThreshold.drop1
  intro h
  have hsmall : (⊥ : SimpleGraph (Fin 2)).edgeSet.ncard < Nat.choose (0 + 2) 2 := by
    simp [edgeSet_bot, Set.ncard_empty]
  have hreal := (h 0).1 2 ⊥ hsmall
  unfold UnitDistanceRealizable at hreal
  obtain ⟨f, hf, -⟩ := hreal
  have hf01 : f 0 = f 1 := by
    ext i
    exact i.elim0
  exact (by decide : (0 : Fin 2) ≠ 1) (hf hf01)

theorem edgeThreshold.witness.proof : edgeThreshold.witness := by
  unfold edgeThreshold.witness
  refine ⟨4, ?_⟩
  refine ⟨by decide, rfl, by decide, ?_, ?_, edgeThreshold.proof⟩
  · rw [FKSEdgeThreshold.Bridge.ncard_edgeSet_completeGraph]
    decide
  · exact not_unitDistanceRealizable_complete 4

end FKSEdgeThreshold.Standalone.Mathlib.InlineFKSEdgeThreshold
