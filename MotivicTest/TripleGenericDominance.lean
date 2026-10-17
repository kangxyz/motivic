/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.TripleGenericDominance

/-! # Actual scheme-image stalk and collision-fiber consumers -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace Motivic.MotivicTest.TripleGenericDominance

variable (k : Type u) [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- The actual pair-image local ring at a generic incidence image is Artinian,
without reducing the image or assuming the image point generic. -/
theorem actualPairImageArtinian (x : genericPoints (F.incidence G)) :
    IsArtinianRing ((F.incidenceMap G).image.presheaf.stalk
      ((F.incidenceMap G).toImage x.1)) := by
  have : IsLocallyNoetherian ((𝟭 Scheme).obj X.left) :=
    inferInstanceAs (IsLocallyNoetherian X.left)
  have := F.isFinite_incidenceImageProjection k G
  have := LocallyOfFiniteType.isLocallyNoetherian
    ((F.incidenceMap G).imageι ≫ pullback.fst X.hom Z.hom)
  exact isArtinianRing_stalk_of_mem_genericPoints _
    (F.incidenceToImage_mem_genericPoints k G x.1 x.2)

/-- The whole actual final image, including possible nilpotents, has an
Artinian local ring at the image of every genuine triple component. -/
theorem actualTripleImageArtinian (x : genericPoints (F.tripleIncidence G H)) :
    IsArtinianRing ((F.tripleIncidenceMap G H).image.presheaf.stalk
      ((F.tripleIncidenceMap G H).toImage x.1)) := by
  have : IsLocallyNoetherian ((𝟭 Scheme).obj X.left) :=
    inferInstanceAs (IsLocallyNoetherian X.left)
  have := F.isFinite_tripleIncidenceImageProjection k G H
  have := LocallyOfFiniteType.isLocallyNoetherian
    ((F.tripleIncidenceMap G H).imageι ≫ pullback.fst X.hom W.hom)
  exact isArtinianRing_stalk_of_mem_genericPoints _
    (F.tripleIncidenceToImage_mem_genericPoints k G H x.1 x.2)

/-- Every actual point colliding with a pair-component image is itself generic;
the finite image fiber can therefore be summed over component generic points. -/
theorem actualPairCollisionFiberGeneric (x : genericPoints (F.incidence G))
    (y : F.incidence G)
    (hy : (F.incidenceMap G).toImage y = (F.incidenceMap G).toImage x.1) :
    y ∈ genericPoints (F.incidence G) := by
  have : IsFinite ((F.incidenceMap G).toImage ≫ (F.incidenceMap G).imageι) := by
    rw [Scheme.Hom.toImage_imageι]
    infer_instance
  have : IsFinite (F.incidenceMap G).toImage := IsFinite.of_comp _ (F.incidenceMap G).imageι
  apply mem_genericPoints_of_image_generic (F.incidenceMap G).toImage
  rw [hy]
  exact F.incidenceToImage_mem_genericPoints k G x.1 x.2

/-- Every actual point colliding with a final triple-component image is generic;
no assertion that the triple-to-right-pair projection is finite is used. -/
theorem actualTripleCollisionFiberGeneric (x : genericPoints (F.tripleIncidence G H))
    (y : F.tripleIncidence G H)
    (hy : (F.tripleIncidenceMap G H).toImage y =
      (F.tripleIncidenceMap G H).toImage x.1) :
    y ∈ genericPoints (F.tripleIncidence G H) := by
  have : IsFinite ((F.tripleIncidenceMap G H).toImage ≫
      (F.tripleIncidenceMap G H).imageι) := by
    rw [Scheme.Hom.toImage_imageι]
    infer_instance
  have : IsFinite (F.tripleIncidenceMap G H).toImage :=
    IsFinite.of_comp _ (F.tripleIncidenceMap G H).imageι
  apply mem_genericPoints_of_image_generic (F.tripleIncidenceMap G H).toImage
  rw [hy]
  exact F.tripleIncidenceToImage_mem_genericPoints k G H x.1 x.2

end Motivic.MotivicTest.TripleGenericDominance
