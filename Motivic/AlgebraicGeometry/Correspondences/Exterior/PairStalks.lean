/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Intersection.Tor.ExteriorPair

public import Motivic.Aglib.Algebra.Homology.Koszul.FlatLocalMultiplicity
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Generalizing.GenericPoints
public import Motivic.Aglib.AlgebraicGeometry.Intersection.StalkTorTransport
public import Motivic.Aglib.AlgebraicGeometry.Intersection.ClosedIntersectionTorLocalization
public import Motivic.Aglib.AlgebraicGeometry.Intersection.Triple.DiagonalRegularity
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Motivic.Aglib.AlgebraicGeometry.Diagonal.FlatBaseChange
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.DiagonalAmbient
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.Tor

/-!
# One original pair list in the actual exterior stalks

The actual projection to the original pair transports its regular diagonal
list through a Cartesian square. The original coefficient-stalk square then
identifies its literal image list. Flatness of the exterior coefficient
projection gives the degreewise Tor length formula with the genuine local
closed fiber. No independently chosen exterior list or assumed Tor comparison
is used.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u


namespace Motivic

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)

namespace FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Hom
open _root_.AlgebraicGeometry.Scheme.Products

variable {f g h i}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- The actual exterior first-stage projection retains the unreduced pair incidence. -/
abbrev leftExteriorPairProjection : F.leftIntermediateSupportProduct G H ⟶ F.incidence G :=
  pullback.fst (F.incidenceTarget G ≫ h) (H.projection ≫ h)

/-- The actual exterior coefficient projection retains the original pair support product. -/
abbrev leftExteriorCoefficientProjection : F.tripleSupportProduct G H ⟶ F.supportProduct G :=
  pullback.fst (F.supportProductTarget G ≫ h) (H.projection ≫ h)

/-- The pair-incidence closed embedding also commutes with exterior projection. -/
theorem leftExteriorIncidence_pair_isPullback :
    IsPullback (F.leftExteriorPairProjection G H)
      (F.leftIntermediateToTripleSupport G H) (F.incidenceToSupportProduct G)
      (F.leftExteriorCoefficientProjection G H) := by
  refine IsPullback.of_bot
    (t := IsPullback.of_hasPullback (F.supportProductTarget G ≫ h) (H.projection ≫ h)) ?_
    (F.leftIntermediateToTripleSupport_fst G H).symm
  simpa [incidenceTarget, supportProductTarget] using
    (IsPullback.of_hasPullback (F.incidenceTarget G ≫ h) (H.projection ≫ h))

/-- Exterior flatness sends a generic first-stage point to a genuine generic
pair-incidence point, not to an ambient support-product generic point. -/
theorem leftExteriorPairProjection_mem_genericPoints [Flat (H.projection ≫ h)]
    (w : F.leftIntermediateSupportProduct G H)
    (hw : w ∈ genericPoints (F.leftIntermediateSupportProduct G H)) :
    F.leftExteriorPairProjection G H w ∈ genericPoints (F.incidence G) :=
  mem_genericPoints_of_generalizing _ (Flat.generalizingMap _) w hw

/-- The original pair projection identifies the first diagonal source point. -/
theorem leftExteriorPairSourcePoint (w : F.leftIntermediateSupportProduct G H) :
    F.incidenceInclusion G (F.leftExteriorPairProjection G H w) =
      pullback.fst (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h)
        (F.leftIntermediateSupportInclusion G H w) :=
  (congrArg (fun m => m w) (F.leftIntermediateSupportInclusion_fst G H)).symm

/-- The original pair projection identifies the coefficient-support point. -/
theorem leftExteriorPairCoefficientPoint (w : F.leftIntermediateSupportProduct G H) :
    F.incidenceToSupportProduct G (F.leftExteriorPairProjection G H w) =
      F.leftExteriorCoefficientProjection G H (F.leftIntermediateToTripleSupport G H w) :=
  (congrArg (fun m => m w) (F.leftIntermediateToTripleSupport_fst G H)).symm

/-- The genuine exterior incidence closed fiber, before any integer conversion. -/
abbrev leftExteriorClosedFiber (w : F.leftIntermediateSupportProduct G H) :=
  _root_.ChainComplex.Koszul.coefficientClosedFiber ((F.leftExteriorPairProjection G H).stalkMap
      w).hom

variable [IsSeparated g]

/-- The actual first-stage Tor length equals the original pair Tor length
times the actual exterior incidence closed-fiber length. The original regular
pair list is transported through the proved Cartesian square, and the support
quotient square proves equality of the two initially different fiber lengths. -/
theorem leftExteriorSupportedTor_length [Flat f] [Smooth g] [Flat h] [Flat i]
    [Flat (H.projection ≫ h)] (w : F.leftIntermediateSupportProduct G H) (n : ℕ) :
    Module.length ((F.leftIntermediateSupportProduct G H).presheaf.stalk w)
        (Intersection.closedIntersectionSupportedStalkTor
          (correspondenceFirstDiagonalInclusion f g h i) (F.tripleSupportProductInclusion G H)
          (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
          (F.leftIntermediate_ambient_isPullback G H) w n) =
      Module.length (F.incidenceAmbientStalk G (F.leftExteriorPairProjection G H w))
        (F.incidenceTor G (F.leftExteriorPairProjection G H w) n) *
          Module.length ((F.leftIntermediateSupportProduct G H).presheaf.stalk w)
            (F.leftExteriorClosedFiber G H w) := by
  let d := correspondenceTripleInclusion f g h
  let j := F.supportProductInclusion G
  let d' := correspondenceFirstDiagonalInclusion f g h i
  let j' := F.tripleSupportProductInclusion G H
  let a := F.incidenceInclusion G
  let b := F.incidenceToSupportProduct G
  let a' := F.leftIntermediateSupportInclusion G H
  let b' := F.leftIntermediateToTripleSupport G H
  let uD := pullback.fst (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h)
  let uT := F.leftExteriorCoefficientProjection G H
  let uP := pullback.fst (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h)
  let z := F.leftExteriorPairProjection G H w
  have he := Intersection.exteriorPairStalkTor_length
    d (a z) j (b z) (Intersection.point_eq a b d j (F.incidence_ambient_isPullback G) z)
    d' (a' w) j' (b' w)
      (Intersection.point_eq a' b' d' j' (F.leftIntermediate_ambient_isPullback G H) w)
    uD uT uP (correspondenceFirstDiagonal_pair_isPullback f g h i)
      (F.tripleSupportProductInclusion_fst G H).symm
      (F.leftExteriorPairSourcePoint G H w) (F.leftExteriorPairCoefficientPoint G H w)
      (exists_regular_kernel_correspondenceTripleInclusion f g h (a z)) n
  have hlen := (Intersection.closedIntersectionSupportedStalkTorRestrictIso
    d' j' a' b' (F.leftIntermediate_ambient_isPullback G H) w n).toLinearEquiv.length_eq
  rw [_root_.ModuleCat.length_restrictScalars_of_surjective _
    (Intersection.intersectionStalkMap_surjective a' b' d' j'
      (F.leftIntermediate_ambient_isPullback G H) w)] at hlen
  refine hlen.trans (he.trans ?_)
  congr 1
  exact Intersection.exteriorClosedFiber_length
    (F.leftExteriorPairProjection G H) b' b uT (F.leftExteriorIncidence_pair_isPullback G H) w

end FiniteCorrespondenceGenerator

end Motivic
