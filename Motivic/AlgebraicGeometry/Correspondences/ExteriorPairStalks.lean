/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulFlatLocalMultiplicity
public import Motivic.AlgebraicGeometry.Cycles.GenericDominance
public import Motivic.AlgebraicGeometry.Intersection.StalkTorTransport
public import Motivic.AlgebraicGeometry.Intersection.ClosedIntersectionTorLocalization
public import Motivic.AlgebraicGeometry.Correspondences.TripleDiagonalRegularity
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

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

namespace Motivic.StalkTransport

/-- A pointed actual stalk map retains the flatness of its scheme morphism. -/
theorem pointedMap_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (x : X) (y : Y) (h : y = f x) : (pointedMap f x y h).hom.Flat := by
  subst y
  simpa only [pointedMap_image] using Flat.stalkMap f x

/-- Equal-point transport preserves the local nature of an actual stalk map. -/
instance pointedMap_isLocalHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (h : y = f x) : IsLocalHom (pointedMap f x y h).hom := by
  subst y
  rw [pointedMap_image]
  infer_instance

end Motivic.StalkTransport

namespace Motivic.Intersection

open StalkTransport

variable {D T P D' T' P' : Scheme.{u}}
  (i : D ⟶ P) (d : D) (j : T ⟶ P) (t : T) (hp : i d = j t)
  (i' : D' ⟶ P') (d' : D') (j' : T' ⟶ P') (t' : T') (hp' : i' d' = j' t')
  (uD : D' ⟶ D) (uT : T' ⟶ T) (uP : P' ⟶ P)
  (sq : IsPullback uD i' i uP) (hj : uT ≫ j = j' ≫ uP)
  (hd : d = uD d') (ht : t = uT t')
  [IsClosedImmersion i] [IsClosedImmersion i'] [IsClosedImmersion j]
  [IsClosedImmersion j'] [Flat uP] [Flat uT]

omit [IsClosedImmersion i'] in
/-- The very same original diagonal list remains regular and generates the
actual exterior diagonal kernel after its literal pointed stalk map. -/
theorem exteriorPairList_regular_kernel (s : List (ambientStalk i d))
    (hs : IsRegular (ambientStalk i d) s)
    (hker : RingHom.ker (i.stalkMap d).hom = Ideal.ofList s) :
    let g := pointedMap uP (i' d') (i d)
      (neighborhoodAmbientPoint i d i' d' uD uP sq.w hd)
    IsRegular (ambientStalk i' d') (s.map g.hom) ∧
      RingHom.ker (i'.stalkMap d').hom = Ideal.ofList (s.map g.hom) := by
  subst d
  exact Diagonal.mapped_equations_regular_kernel sq d' hs hker

omit [IsClosedImmersion i] [IsClosedImmersion i'] [IsClosedImmersion j]
  [IsClosedImmersion j'] [Flat uP] [Flat uT] in
include hj in
/-- The original scheme square proves equality of the literal coefficient
lists after both actual stalk routes. -/
theorem exteriorPairList_coefficient_square (s : List (ambientStalk i d)) :
    (s.map (pointedMap uP (i' d') (i d)
      (neighborhoodAmbientPoint i d i' d' uD uP sq.w hd)).hom).map
        (coefficientStalkMap i' d' j' t' hp').hom =
      (s.map (coefficientStalkMap i d j t hp).hom).map
        (pointedMap uT t' t ht).hom := by
  simp only [List.map_map]
  congr 1
  funext r
  exact (ConcreteCategory.congr_hom
    (neighborhoodCoefficientStalkMap_square i d j t hp i' d' j' t' hp'
      uD uT uP sq.w hj hd ht) r).symm

include sq hj hd in
/-- Flat exterior coefficient projection compares every actual Tor degree.
The source diagonal uses the transported original pair list throughout. -/
theorem exteriorPairStalkTor_length
    (hregular : ∃ s : List (ambientStalk i d),
      IsRegular (ambientStalk i d) s ∧
        RingHom.ker (i.stalkMap d).hom = Ideal.ofList s) (n : ℕ) :
    Module.length (ambientStalk i' d')
        ((((Tor (ModuleCat (ambientStalk i' d')) n).obj
          (coefficientStalkModule i' d' j' t' hp')).obj (sourceStalkModule i' d'))) =
      Module.length (ambientStalk i d)
        ((((Tor (ModuleCat (ambientStalk i d)) n).obj
          (coefficientStalkModule i d j t hp)).obj (sourceStalkModule i d))) *
        Module.length (T'.presheaf.stalk t')
          (Koszul.coefficientClosedFiber (pointedMap uT t' t ht).hom) := by
  obtain ⟨s, hs, hker⟩ := hregular
  let g := pointedMap uP (i' d') (i d)
    (neighborhoodAmbientPoint i d i' d' uD uP sq.w hd)
  obtain ⟨hs', hker'⟩ := exteriorPairList_regular_kernel i d i' d' uD uP sq hd s hs hker
  rw [(torIsoHomology i' d' j' t' hp' (s.map g.hom) hker' hs' n).toLinearEquiv.length_eq,
    (torIsoHomology i d j t hp s hker hs n).toLinearEquiv.length_eq]
  exact Koszul.coordinateFlatLocalHomology_length
    (coefficientStalkMap i d j t hp).hom (coefficientStalkMap_surjective i d j t hp)
    (coefficientStalkMap i' d' j' t' hp').hom (coefficientStalkMap_surjective i' d' j' t' hp')
    (pointedMap uT t' t ht).hom (pointedMap_flat uT t' t ht)
    s (s.map g.hom)
    (exteriorPairList_coefficient_square i d j t hp i' d' j' t' hp'
      uD uT uP sq hj hd ht s) n

/-- A genuine Cartesian closed-immersion square identifies the two local
closed fibers by the actual support quotient and its exact stalk kernel. -/
theorem exteriorClosedFiber_length {V D P Q : Scheme.{u}}
    (a : V ⟶ D) (b : V ⟶ Q) (i : D ⟶ P) (q : Q ⟶ P)
    [IsClosedImmersion i] (sq : IsPullback a b i q) (w : V) :
    Module.length (Q.presheaf.stalk (b w))
        (Koszul.coefficientClosedFiber (Diagonal.baseChangeStalkMap sq w).hom) =
      Module.length (V.presheaf.stalk w)
        (Koszul.coefficientClosedFiber (a.stalkMap w).hom) := by
  have : IsClosedImmersion b := MorphismProperty.of_isPullback sq inferInstance
  exact Module.closedFiberQuotient_length
    (i.stalkMap (a w)).hom (i.stalkMap_surjective (a w))
    (b.stalkMap w).hom (b.stalkMap_surjective w)
    (Diagonal.baseChangeStalkMap sq w).hom (a.stalkMap w).hom
    (congrArg CommRingCat.Hom.hom (Diagonal.baseChangeStalkMap_comp sq w)).symm
    (Diagonal.baseChange_stalk_kernel sq w)

end Motivic.Intersection

namespace Motivic

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)

/-- Projection of the actual exterior diagonal to the original pair is Cartesian. -/
theorem correspondenceFirstDiagonal_pair_isPullback :
    IsPullback
      (pullback.fst (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h))
      (correspondenceFirstDiagonalInclusion f g h i)
      (correspondenceTripleInclusion f g h)
      (pullback.fst (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h)) := by
  refine IsPullback.of_bot
    (t := IsPullback.of_hasPullback
      (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h)) ?_
    (correspondenceFirstDiagonalInclusion_fst f g h i).symm
  simpa [correspondenceTripleTarget, correspondenceAmbientTarget] using
    (IsPullback.of_hasPullback
      (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h))

namespace FiniteCorrespondenceGenerator

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
  Koszul.coefficientClosedFiber ((F.leftExteriorPairProjection G H).stalkMap w).hom

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
  rw [TorComparison.length_restrictScalars_of_surjective _
    (Intersection.intersectionStalkMap_surjective a' b' d' j'
      (F.leftIntermediate_ambient_isPullback G H) w)] at hlen
  refine hlen.trans (he.trans ?_)
  congr 1
  exact Intersection.exteriorClosedFiber_length
    (F.leftExteriorPairProjection G H) b' b uT (F.leftExteriorIncidence_pair_isPullback G H) w

end FiniteCorrespondenceGenerator

end Motivic
