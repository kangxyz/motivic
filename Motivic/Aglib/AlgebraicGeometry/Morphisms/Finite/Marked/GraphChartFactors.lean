/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.ThickBoundaryBaseChange
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.FullBoundaryCoordinate

/-! # Actual marked and residual factors of the original graph chart

Both factors are built from the original finite-map square and the actual
chart projection. The residual uses its scheme-theoretic map to the full
chosen boundary, not a factorization through reduced support.


Intended upstream module: `Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.GraphChartFactors`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.GraphChartOpen`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Norm.PrescribedGraphMarked`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairGraphMarkedNorm`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

variable {S C Y Z K T V Q A D : Scheme.{u}}
  (q : C ⟶ S) (j : Y ⟶ C) (s : Z ⟶ Y)
  (f : C ⟶ K) [IsFinite f] (z : Z ⟶ K) (hs : (s ≫ j) ≫ f = z)
  (n : T ⟶ A) [IsFinite n] (k : V ⟶ T) (σ : Q ⟶ V)
  (z' : Q ⟶ A) (hn : (σ ≫ k) ≫ n = z')
  (u : T ⟶ C) (t : A ⟶ K) (Hf : IsPullback u n f t)
  (a : Q ⟶ Z) (hz : z' ≫ t = a ≫ z)
  (hj : a ≫ (s ≫ j) = (σ ≫ k) ≫ u)
  (v : T ⟶ pullback (j ≫ q) q)
  (hv : v ≫ pullback.snd (j ≫ q) q = u)

/-- The marked chart retains its original parameter and its original marked point. -/
def graphChartMarkedFactor : Q ⟶ pullback (j ≫ q) (s ≫ j ≫ q) :=
  pullback.lift ((σ ≫ k) ≫ v ≫ pullback.fst (j ≫ q) q) a (by
    calc
      ((σ ≫ k) ≫ v ≫ pullback.fst (j ≫ q) q) ≫ (j ≫ q) =
          (σ ≫ k) ≫ v ≫ pullback.snd (j ≫ q) q ≫ q := by
            simp only [Category.assoc, pullback.condition]
      _ = a ≫ s ≫ j ≫ q := by
        rw [← Category.assoc v, hv]
        simpa only [Category.assoc] using congrArg (fun l => l ≫ q) hj.symm)

/-- The constructed marked factor has the literal original ambient map. -/
@[reassoc] theorem graphChartMarkedFactor_ambient :
    graphChartMarkedFactor q j s k σ u a hj v hv ≫
      Hom.graphBoundaryRestriction q j s = (σ ≫ k) ≫ v := by
  apply pullback.hom_ext
  · simp [graphChartMarkedFactor, Hom.graphBoundaryRestriction]
  · simpa only [graphChartMarkedFactor, Hom.graphBoundaryRestriction,
      Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hv] using hj

variable (d : D ⟶ C)
  (b : (residualMarkedFiberOpen f j z s hs).toScheme ⟶ D)
  (hb : b ≫ d = residualMarkedFiberMap f j z s hs)

/-- The whole actual chart residual maps to the full parameter-boundary product. -/
def graphChartResidualFactor :
    (residualMarkedFiberOpen n k z' σ hn).toScheme ⟶
      pullback (pullback.snd (j ≫ q) q) d :=
  pullback.lift (residualMarkedFiberMap n k z' σ hn ≫ v)
    (residualBaseChangeMap f j z s hs n k z' σ hn u t Hf a hz hj ≫ b) (by
      rw [Category.assoc, hv]
      exact (residualBaseChangeMap_boundary f j z s hs n k z' σ hn
        u t Hf a hz hj d b hb).symm)

/-- The residual factor retains the exact chart ambient map and all nilpotents. -/
@[reassoc] theorem graphChartResidualFactor_ambient :
    graphChartResidualFactor q j s f z hs n k σ z' hn u t Hf a hz hj v hv d b hb ≫
      Hom.infinityProductMap q j d = residualMarkedFiberMap n k z' σ hn ≫ v :=
  pullback.lift_fst _ _ _

end AlgebraicGeometry.Scheme
