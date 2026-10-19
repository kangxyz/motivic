/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalRetainedNormMaps
/-! # Original norm charts under an actual first-parameter change

Both original second factors and the original compactification sections remain
unchanged. The canonical chart isomorphism preserves the scalar structure and
the projection to the original compact source.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalNormParameterChart`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Norm.OriginalNormParameterGenericRatio`, `Norm.OriginalPairNormDiagram`,
`Norm.SectionPairNormParameterNeighborhood`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.Hom

variable {S C P Y K W : Scheme.{u}} (π : P ⟶ S) (f : C ⟶ P)
  (q : Y ⟶ S) (α : K ⟶ Y) (b : K ⟶ S) (hb : b = α ≫ q)

/-- The actual compact norm square commutes under first-parameter change. -/
theorem normProductMap_parameter_comm :
    constantSourceMapOfEq α q (f ≫ π) b hb ≫ normProductMap π f q =
      normProductMap π f b ≫ constantSourceMapOfEq α q π b hb := by
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- Unlike the retained second-factor square, this whole compactification
first-parameter norm square is Cartesian. -/
theorem normProductMap_parameter_isPullback :
    IsPullback (constantSourceMapOfEq α q (f ≫ π) b hb) (normProductMap π f b)
      (normProductMap π f q) (constantSourceMapOfEq α q π b hb) := by
  have H : IsPullback
      (constantSourceMapOfEq α q (f ≫ π) b hb ≫ pullback.snd q (f ≫ π))
      (normProductMap π f b) f
      (constantSourceMapOfEq α q π b hb ≫ pullback.snd q π) := by
    simpa only [constantSourceMapOfEq_snd] using normProductMap_isPullback π f b
  exact H.of_right (normProductMap_parameter_comm π f q α b hb)
    (normProductMap_isPullback π f q)

variable (w : W ⟶ pullback b π)

/-- A chart on the component product is the original norm chart pulled along
its actual first-parameter map. -/
def normProductParameterChartIso :
    pullback (normProductMap π f b) w ≅
      pullback (normProductMap π f q) (w ≫ constantSourceMapOfEq α q π b hb) :=
  ((IsPullback.of_hasPullback (normProductMap π f b) w).paste_horiz
    (normProductMap_parameter_isPullback π f q α b hb)).isoPullback

@[reassoc (attr := simp)]
theorem normProductParameterChartIso_hom_fst :
    (normProductParameterChartIso π f q α b hb w).hom ≫
        pullback.fst (normProductMap π f q) (w ≫ constantSourceMapOfEq α q π b hb) =
      pullback.fst (normProductMap π f b) w ≫ constantSourceMapOfEq α q (f ≫ π) b hb :=
  IsPullback.isoPullback_hom_fst _

@[reassoc (attr := simp)]
theorem normProductParameterChartIso_hom_snd :
    (normProductParameterChartIso π f q α b hb w).hom ≫
        pullback.snd (normProductMap π f q) (w ≫ constantSourceMapOfEq α q π b hb) =
      pullback.snd (normProductMap π f b) w :=
  IsPullback.isoPullback_hom_snd _

@[reassoc]
theorem normProductParameterChartIso_hom_original_source :
    (normProductParameterChartIso π f q α b hb w).hom ≫
        pullback.fst (normProductMap π f q) (w ≫ constantSourceMapOfEq α q π b hb) ≫
          pullback.snd q (f ≫ π) =
      pullback.fst (normProductMap π f b) w ≫ pullback.snd b (f ≫ π) := by
  rw [normProductParameterChartIso_hom_fst_assoc, constantSourceMapOfEq_snd]

end AlgebraicGeometry.Scheme.Hom
