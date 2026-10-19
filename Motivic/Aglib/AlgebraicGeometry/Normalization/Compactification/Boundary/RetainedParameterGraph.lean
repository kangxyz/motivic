/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.ParameterGraphChartFrame

/-! # The original finite target graph and its retained parameter square

The retained commutation identifies the original target graph with the native
parameter-pulled graph through the literal pullback congruence isomorphism.
No original graph or parameter is replaced by a newly chosen subscheme.


Intended upstream module:
`Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.RetainedParameterGraph`.
Incoming project consumers:
Module prefix: `Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.`
Module suffix: `RetainedMarkedChartProjection`,
`Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.RetainedTargetChartFrame`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom

variable {S C P X Y : Scheme.{u}} (q : P ⟶ S) (f : C ⟶ P)
  (jB : Y ⟶ C) (jA : X ⟶ P) (p : Y ⟶ X) (h : jB ≫ f = p ≫ jA)

/-- Only the original retained commutation changes the presentation of the product. -/
def retainedParameterProductIso :
    pullback (jB ≫ f ≫ q) q ≅ pullback ((p ≫ jA) ≫ q) q :=
  pullback.congrHom (by
    simpa only [Category.assoc] using congrArg (fun l => l ≫ q) h) rfl

/-- The original target graph has its exact parameter-graph image. -/
@[reassoc] theorem targetGraph_retainedParameterProductIso :
    targetCompactificationGraph q f jB ≫ (retainedParameterProductIso q f jB jA p h).hom =
      compactificationGraph q (p ≫ jA) := by
  apply pullback.hom_ext
  · simp [retainedParameterProductIso, targetCompactificationGraph, compactificationGraph]
  · simpa [retainedParameterProductIso, targetCompactificationGraph, compactificationGraph] using h

/-- The actual target-to-native-target parameter map, retaining the original product. -/
def retainedParameterProductMap :
    pullback (jB ≫ f ≫ q) q ⟶ pullback (jA ≫ q) q :=
  (retainedParameterProductIso q f jB jA p h).hom ≫ parameterProductMap q jA p

instance [Flat p] : Flat (retainedParameterProductMap q f jB jA p h) := by
  unfold retainedParameterProductMap
  infer_instance

/-- The original target graph is the actual Cartesian pullback of the native
original target diagonal graph along the retained parameter map. -/
theorem retainedParameterGraph_isPullback :
    IsPullback p (targetCompactificationGraph q f jB) (compactificationGraph q jA)
      (retainedParameterProductMap q f jB jA p h) := by
  have hi : IsPullback (𝟙 Y) (targetCompactificationGraph q f jB)
      (compactificationGraph q (p ≫ jA)) (retainedParameterProductIso q f jB jA p h).hom :=
    IsPullback.of_horiz_isIso ⟨by
      simpa only [Category.id_comp] using
        (targetGraph_retainedParameterProductIso q f jB jA p h).symm⟩
  simpa only [Category.id_comp, retainedParameterProductMap] using
    hi.paste_horiz (parameterGraph_isPullback q jA p)

/-- The corresponding comparison of the original target graph ideals. -/
def retainedParameterGraphIdealIso [Flat p]
    [IsClosedImmersion (compactificationGraph q jA)]
    [IsClosedImmersion (targetCompactificationGraph q f jB)]
    (hI : IsLocallyRankOne _ (idealModule (compactificationGraph q jA))) :
    (Modules.pullback (retainedParameterProductMap q f jB jA p h)).obj
      (idealModule (compactificationGraph q jA)) ≅
        idealModule (targetCompactificationGraph q f jB) :=
  flatChartIdealIso (compactificationGraph q jA) (targetCompactificationGraph q f jB)
    (retainedParameterProductMap q f jB jA p h) p
    (retainedParameterGraph_isPullback q f jB jA p h) hI

/-- The comparison retains the exact inclusion of the original target graph. -/
theorem retainedParameterGraphIdealIso_inclusion [Flat p]
    [IsClosedImmersion (compactificationGraph q jA)]
    [IsClosedImmersion (targetCompactificationGraph q f jB)]
    (hI : IsLocallyRankOne _ (idealModule (compactificationGraph q jA))) :
    (retainedParameterGraphIdealIso q f jB jA p h hI).hom ≫
      idealInclusion (targetCompactificationGraph q f jB) =
    pullbackUnitMap (retainedParameterProductMap q f jB jA p h)
      (idealInclusion (compactificationGraph q jA)) := by
  simp only [retainedParameterGraphIdealIso, flatChartIdealIso, asIso_hom]
  rw [idealPullbackMap_inclusion]
  rfl

end AlgebraicGeometry.Scheme.Hom
