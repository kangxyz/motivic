/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
/-! # Actual open charts of the schematic image -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
universe u
namespace AlgebraicGeometry.Scheme
variable {X Y U : Scheme.{u}} (f : X ⟶ Y) (j : U ⟶ Y)
  [QuasiCompact f] [IsOpenImmersion j] (g : X ⟶ U) (h : g ≫ j = f)

include h
/-- Restricting the original schematic image to an open through which the source factors
retains the whole kernel ideal, not merely its support. -/
theorem ker_comap_open_factor : f.ker.comap j = g.ker := by
  have hp : IsPullback g (𝟙 X) j f := IsPullback.of_vert_isIso_mono ⟨by simpa using h⟩
  ext1
  funext W
  rw [IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact (ker_ideal_of_isPullback_of_isOpenImmersion f g (𝟙 X) j hp W).symm

/-- The actual chart of the global schematic image is the schematic image of the
literal factored chart map. -/
def imageOpenChartIso : pullback j f.imageι ≅ g.image :=
  (f.ker.comapIso j).symm ≪≫
    eqToIso (congrArg IdealSheafData.subscheme (ker_comap_open_factor f j g h))

omit [QuasiCompact f] [IsOpenImmersion j] h in
/-- Equality of ideal data preserves the literal closed inclusion. -/
@[reassoc]
theorem subscheme_eqToHom_inclusion {S : Scheme.{u}} {I J : S.IdealSheafData}
    (h : I = J) :
    eqToHom (congrArg IdealSheafData.subscheme h) ≫ J.subschemeι = I.subschemeι := by
  subst J
  simp

/-- The chart comparison commutes with its original closed immersion. -/
@[reassoc]
theorem imageOpenChartIso_hom_inclusion :
    (imageOpenChartIso f j g h).hom ≫ g.imageι = pullback.fst j f.imageι := by
  dsimp only [imageOpenChartIso, Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
  rw [Category.assoc, subscheme_eqToHom_inclusion (ker_comap_open_factor f j g h),
    IdealSheafData.comapIso_inv_subschemeι]

end AlgebraicGeometry.Scheme
