/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.FiniteScalarRestrictionDifference
public import Motivic.Cohomology.A1.Boundary.Presheaf.GeometricImage

/-!
# Coprime scalar descent into the original canonical boundary image

This consumes extended signed section relations on scalar extensions of one
original geometric refinement. It constructs original Laurent and ambient
corrections with actual traces, before using the original quotient and its
sheafification. It neither assumes nor constructs a transfer-presheaf structure
on the relative boundary sheaf. Producing the common original refinement is a
separate geometric obligation, not a consequence of this theorem.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers

universe u

namespace Motivic.FiniteEtaleSite.OriginalPresheaf
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (P : PresheafWithTransfers.{u + 1} k)
variable {E : Type u} [Field E] [Algebra k E]
  [Module.Finite k E] [Algebra.IsSeparable k E]
variable {L : Type u} [Field L] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L]

/-- Descended signed corrections give an actual image-sieve witness for the
unchanged original contraction-to-boundary map. All geometric arrows are fixed
over the original field before either finite extension is applied. -/
theorem imageSieve_of_coprime_finiteScalar_geometric_difference
    {W W' : EtaleSeparatedFiniteType (SmoothSite.a1Cylinder (.of k) X).left}
    (V : EtaleSeparatedFiniteType X.left) (b : W' ⟶ (cylinderNeighborhood X).obj V)
    (z : V.left ⟶ W'.left)
    (hz : z ≫ b.left =
      (SmoothSite.a1Section (.of k) ((toSmoothSite X).obj V) 0).left)
    (O : SmoothSite (Spec (.of k)))
    (α : O ⟶ (toSmoothSite (SmoothSite.a1Cylinder (.of k) X)).obj W') [Flat α.left]
    (β : O ⟶ SmoothSite.torusCylinder (.of k) ((toSmoothSite X).obj V)) [Flat β.left]
    (H : IsPullback β.left α.left
      (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj V)).left b.left)
    (f : W' ⟶ W)
    (φ : O ⟶ (toSmoothSite (SmoothSite.torusCylinder (.of k) X)).obj
      ((baseChange (SmoothSite.contractionOpen (.of k) X).left).obj W))
    (hφ₁ : φ.left ≫ pullback.fst W.hom
      (SmoothSite.contractionOpen (.of k) X).left = α.left ≫ f.left)
    (hφ₂ : φ.left ≫ pullback.snd W.hom
      (SmoothSite.contractionOpen (.of k) X).left = β.left ≫
        (SmoothSite.productMap (toBase X V) (𝟙 (SmoothSite.torus (.of k)))).left)
    (s : sections P (Cor.mk ((toSmoothSite (SmoothSite.torusCylinder (.of k) X)).obj
      ((baseChange (SmoothSite.contractionOpen (.of k) X).left).obj W))))
    (hE : ∃ (a : sections P (Cor.mk (SmoothSite.finiteScalarExtension (E := E)
        (SmoothSite.torusCylinder (.of k) ((toSmoothSite X).obj V)))))
      (c : sections P (Cor.mk (SmoothSite.finiteScalarExtension (E := E)
        ((toSmoothSite (SmoothSite.a1Cylinder (.of k) X)).obj W')))),
      transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := E) β)) a -
        transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := E) α)) c =
        transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := E) φ))
          (transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarProjection (E := E)
            ((toSmoothSite (SmoothSite.torusCylinder (.of k) X)).obj
              ((baseChange (SmoothSite.contractionOpen (.of k) X).left).obj W)))) s))
    (hL : ∃ (a : sections P (Cor.mk (SmoothSite.finiteScalarExtension (E := L)
        (SmoothSite.torusCylinder (.of k) ((toSmoothSite X).obj V)))))
      (c : sections P (Cor.mk (SmoothSite.finiteScalarExtension (E := L)
        ((toSmoothSite (SmoothSite.a1Cylinder (.of k) X)).obj W')))),
      transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := L) β)) a -
        transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := L) α)) c =
        transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := L) φ))
          (transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarProjection (E := L)
            ((toSmoothSite (SmoothSite.torusCylinder (.of k) X)).obj
              ((baseChange (SmoothSite.contractionOpen (.of k) X).left).obj W)))) s))
    (hdegree : (Module.finrank k E).Coprime (Module.finrank k L)) :
    Presheaf.imageSieve (contractionToBoundary X P).hom
      ((presheafBoundaryGenerator ((PresheafWithTransfers.toPresheaf k).obj P)
        (SmoothSite.contractionOpen (.of k) X)
        (SmoothSite.a1Section (.of k) X 0)).app (op W) s)
      (geometricZeroLift X V b z hz ≫
        (baseChange (SmoothSite.a1Section (.of k) X 0).left).map f) := by
  obtain ⟨a, c, h⟩ := exists_restriction_difference_of_coprime_finiteScalar
    (E := E) (L := L) P β α φ s hE hL hdegree
  exact imageSieve_of_geometric_difference X V b z hz P O α β H f φ hφ₁ hφ₂ s a c h

end Motivic.FiniteEtaleSite.OriginalPresheaf
