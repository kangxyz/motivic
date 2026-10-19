/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Nisnevich.Points.CechKernel
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.QuasiFinite.Fibers.ClosedCentersFiniteSupport

/-!
# Closed-center input for the point-local Čech kernel relation

For a closed source point, every center of the common finite support fiber is
closed in the smooth target. It suffices to lift precisely these closed target
centers. The hypothesis does not ask for lifts at all points of the target,
or even at closed target points outside that finite fiber's image.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondence
open _root_.AlgebraicGeometry.Scheme

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Only the closed target centers of the actual finite support fiber need
residue lifts in order to contract a signed relation at a closed source point. -/
theorem exists_pointed_cech_boundary_of_common_support_closed_centers
    (k : Type u) [Field k] {X Y V : SmoothSite (Spec (.of k))}
    (α : FiniteCorrespondence X.hom V.hom) (q : V ⟶ Y) [Etale q.left]
    (hzero : (α : Cor.mk X ⟶ Cor.mk V) ≫ (Cor.graphFunctor k).map q = 0)
    (C : Scheme.{u}) (j : C ⟶ pullback X.hom Y.hom) [IsClosedImmersion j]
    [IsFinite (j ≫ pullback.fst X.hom Y.hom)]
    (r : ∀ A ∈ α.support, A.scheme ⟶ C)
    (hr : ∀ A hA, r A hA ≫ j =
      A.graphPostcompositionMap q.left (MorphismProperty.Over.w q))
    (x : X.left) (hx : IsClosed ({x} : Set X.left))
    (hq : ∀ y : Y.left, IsClosed ({y} : Set Y.left) →
      (∃ z : C, (j ≫ pullback.fst X.hom Y.hom) z = x ∧
        (j ≫ pullback.snd X.hom Y.hom) z = y) →
      ∃ v : V.left, q.left v = y ∧ IsIso (q.left.residueFieldMap v)) :
    ∃ (N : SmoothSite.NisnevichNeighborhood X x)
      (β : Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N) ⟶
        Cor.mk (SmoothSite.etalePullback q q)),
      (Cor.graphFunctor k).map N.toBase ≫ α =
        β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) -
          β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q) := by
  have : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace
    (Y := Spec (.of k)) (show Y.left ⟶ Spec (.of k) from Y.hom)
  apply exists_pointed_cech_boundary_of_common_support_fiber k α q hzero C j r hr x
  intro z hz
  apply hq _ _ ⟨z, hz, rfl⟩
  exact Scheme.Hom.isClosed_target_of_locallyQuasiFinite_source (Y := Y.left)
    (j ≫ pullback.fst X.hom Y.hom) (j ≫ pullback.snd X.hom Y.hom) z
    (by simpa only [hz] using hx)

end Motivic.FiniteCorrespondence
