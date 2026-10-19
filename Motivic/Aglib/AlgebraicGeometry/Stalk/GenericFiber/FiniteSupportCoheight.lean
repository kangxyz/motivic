/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.GenericFiber
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.CodimensionOneDominance

/-!
# Coheight of an actual finite support on a generic curve fibre

The support is pulled back along the original generic-fibre projection, without
reduction or a flatness assumption. Finiteness is transported from the original
closed support. The native projection stalk equivalence identifies the original
local ring, so later quotient-length comparisons use the same ring map.
No finite numerator/denominator cut or correspondence endpoint identity is assumed.


Intended upstream module: `Aglib.AlgebraicGeometry.Stalk.GenericFiber.FiniteSupportCoheight`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.FiniteCurve.Faces.FiniteDominantFaceCurvePlacement`,
`Motivic.Aglib.AlgebraicGeometry.Cycles.FiniteCurve.Faces.FiniteDominantFacePlacement`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Order

universe u

namespace AlgebraicGeometry.Scheme.LocalRing.GenericFiber

variable (A F : Type u) [CommRing A] [Field F]
  [Algebra A F] [IsFractionRing A F]
  {V D : Scheme.{u}} (q : V ⟶ Spec (.of A)) (i : D ⟶ V)

/-- The full original support after the actual generic-fibre base change. -/
abbrev support := pullback i (projection A F q)

/-- The original closed immersion after base change, retaining all multiplicities. -/
abbrev supportInclusion : support A F q i ⟶ scheme A F q :=
  pullback.snd i (projection A F q)

/-- The structure morphism of the original generic fibre. -/
abbrev structureMap : scheme A F q ⟶ Spec (.of F) :=
  pullback.snd q (baseMap A F)

instance [IsClosedImmersion i] : IsClosedImmersion (supportInclusion A F q i) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance [IsFinite (i ≫ q)] :
    IsFinite (supportInclusion A F q i ≫ structureMap A F q) :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback i (projection A F q)).paste_vert
      (IsPullback.of_hasPullback q (baseMap A F))) inferInstance

omit [IsFractionRing A F] in
/-- Every point of the actual finite support is closed in the generic curve.
Separatedness is inherited from the original relative curve, not added on the support. -/
theorem support_image_isClosed [IsClosedImmersion i] [IsFinite (i ≫ q)]
    [IsSeparated q] (x : support A F q i) :
    IsClosed ({supportInclusion A F q i x} : Set (scheme A F q)) := by
  let r := structureMap A F q
  have : IsSeparated r := MorphismProperty.pullback_snd _ _ inferInstance
  let y := supportInclusion A F q i x
  have hf := _root_.AlgebraicGeometry.Scheme.residueFieldMap_finite_of_finite_closed_support
    (supportInclusion A F q i) r x
  have hc := _root_.AlgebraicGeometry.Scheme.isClosed_asFiber_of_finite_residueFieldMap r y hf
  have : IsClosedImmersion ((Spec (.of F)).fromSpecResidueField (r y)) :=
    isClosed_singleton_iff_isClosedImmersion.mp (isClosed_singleton (x := r y))
  have : IsClosedImmersion (r.fiberι (r y)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  simpa only [Set.image_singleton, Scheme.Hom.fiberι_asFiber] using
    (r.fiberι (r y)).isClosedMap _ hc

/-- The image in the unchanged original curve has coheight one. The dimension
comparison is the actual generic-fibre projection's stalk equivalence. -/
theorem support_image_coheight [IsClosedImmersion i] [IsFinite (i ≫ q)]
    [IsSeparated q] [SmoothOfRelativeDimension 1 q] (x : support A F q i) :
    coheight (projection A F q (supportInclusion A F q i x)) = 1 := by
  have : SmoothOfRelativeDimension 1 (structureMap A F q) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have hd := Scheme.smoothClosedPointDimension F (scheme A F q)
    (structureMap A F q) 1 inferInstance (supportInclusion A F q i x)
    (support_image_isClosed A F q i x)
  have hd' : ringKrullDim (V.presheaf.stalk
      (projection A F q (supportInclusion A F q i x))) = 1 := by
    rw [ringKrullDim_eq_of_ringEquiv
      (stalkEquiv A F q (supportInclusion A F q i x))]
    exact hd
  rw [ringKrullDim_stalk_eq_coheight] at hd'
  exact_mod_cast hd'

end AlgebraicGeometry.Scheme.LocalRing.GenericFiber
