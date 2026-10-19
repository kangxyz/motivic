/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalNormParameterChart
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.LineRatioIso
/-! # The component norm and the literal original pullback norm

The native finite second-factor map and the canonical Cartesian presentation
are related by the actual chart isomorphism. Their generic ratio norms agree
for the same original compactification line and the same two functionals.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalNormParameterGenericRatio`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Pencils.NativeSectionPairTransferAction`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme.Hom
open Modules Modules.Invertible

variable {S C P Y K : Scheme.{u}} (π : P ⟶ S) (f : C ⟶ P)
  (q : Y ⟶ S) (α : K ⟶ Y) (b : K ⟶ S) (hb : b = α ≫ q)
  [IsIntegral (pullback b π)]

/-- The actual generic fibers of the direct product and Cartesian presentations. -/
def normProductParameterGenericIso :
    Limits.pullback (normProductMap π f b) ((pullback b π).fromSpecStalk
      (genericPoint (pullback b π : Scheme))) ≅
    Limits.pullback (pullback.snd (normProductMap π f q) (constantSourceMapOfEq α q π b hb))
      ((pullback b π).fromSpecStalk (genericPoint (pullback b π : Scheme))) :=
  normProductParameterChartIso π f q α b hb _ ≪≫
    (pullbackLeftPullbackSndIso (normProductMap π f q)
      (constantSourceMapOfEq α q π b hb) _).symm

@[reassoc (attr := simp)]
theorem normProductParameterGenericIso_hom_snd :
    (normProductParameterGenericIso π f q α b hb).hom ≫
      pullback.snd (pullback.snd (normProductMap π f q)
        (constantSourceMapOfEq α q π b hb))
        ((pullback b π).fromSpecStalk (genericPoint (pullback b π : Scheme))) =
      pullback.snd (normProductMap π f b)
        ((pullback b π).fromSpecStalk (genericPoint (pullback b π : Scheme))) := by
  simp [normProductParameterGenericIso, Category.assoc]

@[reassoc (attr := simp)]
theorem normProductParameterGenericIso_hom_original_compact :
    (normProductParameterGenericIso π f q α b hb).hom ≫
      pullback.fst (pullback.snd (normProductMap π f q)
        (constantSourceMapOfEq α q π b hb))
        ((pullback b π).fromSpecStalk (genericPoint (pullback b π : Scheme))) ≫
      pullback.fst (normProductMap π f q) (constantSourceMapOfEq α q π b hb) =
      pullback.fst (normProductMap π f b)
        ((pullback b π).fromSpecStalk (genericPoint (pullback b π : Scheme))) ≫
          constantSourceMapOfEq α q (f ≫ π) b hb := by
  simp [normProductParameterGenericIso, Category.assoc]

/-- The exact native source norm used by the component action diagram equals
the norm produced by the original Cartesian parameter normalization. -/
theorem normProductParameter_genericRatio_eq [IsFinite f]
    (L : LineBundle (pullback q (f ≫ π)))
    (a c : L.val ⟶ SheafOfModules.unit (pullback q (f ≫ π)).ringCatSheaf)
    [Mono (pullbackUnitMap (constantSourceMapOfEq α q (f ≫ π) b hb) a)]
    [Mono (pullbackUnitMap (constantSourceMapOfEq α q (f ≫ π) b hb) c)]
    [Mono (pullbackUnitMap
      (pullback.fst (normProductMap π f q) (constantSourceMapOfEq α q π b hb)) a)]
    [Mono (pullbackUnitMap
      (pullback.fst (normProductMap π f q) (constantSourceMapOfEq α q π b hb)) c)] :
    genericFiberLineRatioNorm (normProductMap π f b)
      (pullbackLineBundle (constantSourceMapOfEq α q (f ≫ π) b hb) L)
      (pullbackUnitMap (constantSourceMapOfEq α q (f ≫ π) b hb) a)
      (pullbackUnitMap (constantSourceMapOfEq α q (f ≫ π) b hb) c) =
    genericFiberLineRatioNorm
      (pullback.snd (normProductMap π f q) (constantSourceMapOfEq α q π b hb))
      (pullbackLineBundle
        (pullback.fst (normProductMap π f q) (constantSourceMapOfEq α q π b hb)) L)
      (pullbackUnitMap
        (pullback.fst (normProductMap π f q) (constantSourceMapOfEq α q π b hb)) a)
      (pullbackUnitMap
        (pullback.fst (normProductMap π f q) (constantSourceMapOfEq α q π b hb)) c) :=
  genericFiberLineRatioNorm_eq_of_source_iso _ _ _ _ L a c
    (normProductParameterGenericIso π f q α b hb)
    (normProductParameterGenericIso_hom_snd π f q α b hb)
    (normProductParameterGenericIso_hom_original_compact π f q α b hb)

end AlgebraicGeometry.Scheme.Hom
