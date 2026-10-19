/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DualTensor.MixedBoundary
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.FunctionalRatio
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.PrescribedPairPullback

/-! # Coordinates from the same ideal frame and the original pole functional

The chosen domain only needs the original pole functional to be invertible.
The graph-twisted pole need not be a unit, even at marked boundary incidence.


Intended upstream module:
`Aglib.AlgebraicGeometry.Modules.Invertible.Sections.NormalizedTwistedIdealCoordinate`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairGraphCoordinate`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X W : Scheme.{u}} (f : W ⟶ X) (I T : LineBundle X)
  (b : SheafOfModules.unit X.ringCatSheaf ⟶ T.val)
  [IsIso (Hom.pullbackToUnit (sectionDualFunctional X T b) f)]
  (e : (Modules.pullback f).obj I.val ≅ SheafOfModules.unit W.ringCatSheaf)

/-- The same ideal frame and inverse original pole functional frame the actual
pulled numerator dual line, through its canonical ordered tensor comparison. -/
def normalizedTwistedIdealFrame :
    (Modules.pullback f).obj
      (dualLineBundle X (tensorLineBundle X T (dualLineBundle X I))).val ≅
        SheafOfModules.unit W.ringCatSheaf :=
  (pulledDualTwistedIdealIso f I T).symm ≪≫
    tensorSheafIso W e (asIso (Hom.pullbackToUnit (sectionDualFunctional X T b) f)) ≪≫
      tensorSheafLeftUnit W (SheafOfModules.unit W.ringCatSheaf)

/-- Normalizing the original product by its original unit factor leaves precisely
its ideal coefficient in the same frame. No cancellation of that coefficient occurs. -/
theorem normalizedTwistedIdealFrame_product
    (φ : (Modules.pullback f).obj I.val ⟶ SheafOfModules.unit W.ringCatSheaf) :
    (normalizedTwistedIdealFrame f I T b e).inv ≫
      (pulledDualTwistedIdealIso f I T).inv ≫
        Hom.productSection φ (Hom.pullbackToUnit (sectionDualFunctional X T b) f) =
      e.inv ≫ φ := by
  simp only [normalizedTwistedIdealFrame, Iso.trans_inv, Iso.symm_inv, Category.assoc,
    Iso.hom_inv_id_assoc]
  change (tensorSheafLeftUnit W (SheafOfModules.unit W.ringCatSheaf)).inv ≫
    tensorSheafMap W e.inv (inv (Hom.pullbackToUnit (sectionDualFunctional X T b) f)) ≫
      Hom.productSection φ (Hom.pullbackToUnit (sectionDualFunctional X T b) f) = _
  rw [Hom.productSection_naturality, IsIso.inv_hom_id]
  unfold Hom.productSection
  rw [tensorToUnit_unit]
  simp only [Category.assoc]
  change (tensorSheafLeftUnit W (SheafOfModules.unit W.ringCatSheaf)).inv ≫
    (SheafOfModulesOfCommRing.tensorRightUnitIso W.sheaf).hom.app
      (SheafOfModules.unit W.ringCatSheaf) ≫ _ = _
  rw [← tensorUnitors_eq]
  exact (tensorSheafLeftUnit W (SheafOfModules.unit W.ringCatSheaf)).inv_hom_id_assoc _

/-- The actual graph-twisted section has exactly the original ideal coefficient. -/
theorem normalizedTwistedIdealFrame_twistedSection
    (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (normalizedTwistedIdealFrame f I T b e).inv ≫
      Hom.pullbackToUnit
        (sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I))
          (twistedIdealSection X I T φ b)) f =
      e.inv ≫ Hom.pullbackToUnit φ f := by
  have h := pulledDualTwistedIdealIso_section f I T φ b
  have h' := congrArg (fun k => (pulledDualTwistedIdealIso f I T).inv ≫ k) h
  simp only [Iso.inv_hom_id_assoc] at h'
  rw [h']
  exact normalizedTwistedIdealFrame_product f I T b e (Hom.pullbackToUnit φ f)

/-- Evaluating the original graph-twisted pole at one gives the same ideal
scalar, without requiring the graph scalar to be invertible. -/
theorem normalizedTwistedIdealFrame_twistedSection_scalar
    (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    Modules.Hom.app ((normalizedTwistedIdealFrame f I T b e).inv ≫
      Hom.pullbackToUnit
        (sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I))
          (twistedIdealSection X I T φ b)) f) ⊤ (1 : Γ(W, ⊤)) =
      Modules.Hom.app (e.inv ≫ Hom.pullbackToUnit φ f) ⊤ (1 : Γ(W, ⊤)) := by
  rw [normalizedTwistedIdealFrame_twistedSection]

/-- An actual normalized numerator functional equation gives coefficient one;
the equation is retained explicitly until supplied by the original section pairing. -/
theorem normalizedTwistedIdealFrame_numerator
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      (tensorLineBundle X T (dualLineBundle X I)).val)
    (h : (pulledDualTwistedIdealIso f I T).hom ≫
      Hom.pullbackToUnit
        (sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I)) a) f =
      Hom.productSection e.hom (Hom.pullbackToUnit (sectionDualFunctional X T b) f)) :
    (normalizedTwistedIdealFrame f I T b e).inv ≫
      Hom.pullbackToUnit
        (sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I)) a) f = 𝟙 _ := by
  have h' := congrArg (fun k => (pulledDualTwistedIdealIso f I T).inv ≫ k) h
  simp only [Iso.inv_hom_id_assoc] at h'
  rw [h', normalizedTwistedIdealFrame_product, Iso.inv_hom_id]

/-- The original unit pole functional identifies the pulled ideal line with
its actual twisted dual, with no independently chosen ideal frame. -/
def poleFunctionalIdealIso :
    (Modules.pullback f).obj I.val ≅
      (Modules.pullback f).obj
        (dualLineBundle X (tensorLineBundle X T (dualLineBundle X I))).val :=
  (tensorSheafRightUnit W ((Modules.pullback f).obj I.val)).symm ≪≫
    tensorSheafIso W (Iso.refl _)
      (asIso (Hom.pullbackToUnit (sectionDualFunctional X T b) f)).symm ≪≫
        pulledDualTwistedIdealIso f I T

/-- Under the original pole-induced identification, the graph-twisted functional
is the original ideal functional. The latter is not assumed invertible. -/
theorem poleFunctionalIdealIso_twistedSection
    (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (poleFunctionalIdealIso f I T b).hom ≫
      Hom.pullbackToUnit
        (sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I))
          (twistedIdealSection X I T φ b)) f =
      Hom.pullbackToUnit φ f := by
  simp only [poleFunctionalIdealIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [pulledDualTwistedIdealIso_section]
  change (tensorSheafRightUnit W ((Modules.pullback f).obj I.val)).inv ≫
    tensorSheafMap W (𝟙 _) (inv (Hom.pullbackToUnit (sectionDualFunctional X T b) f)) ≫
      Hom.productSection (Hom.pullbackToUnit φ f)
        (Hom.pullbackToUnit (sectionDualFunctional X T b) f) = _
  rw [Hom.productSection_naturality, Category.id_comp, IsIso.inv_hom_id]
  unfold Hom.productSection
  rw [tensorToUnit_unit]
  simp only [Category.assoc]
  exact (tensorSheafRightUnit W ((Modules.pullback f).obj I.val)).inv_hom_id_assoc _

variable (a : SheafOfModules.unit X.ringCatSheaf ⟶
    (tensorLineBundle X T (dualLineBundle X I)).val)
  [IsIso (Hom.pullbackToUnit
    (sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I)) a) f)]

/-- The same original numerator and pole functionals determine an ideal frame.
This changes neither section and makes no independent frame choice. -/
def sectionPairIdealFrame :
    (Modules.pullback f).obj I.val ≅ SheafOfModules.unit W.ringCatSheaf :=
  poleFunctionalIdealIso f I T b ≪≫
    asIso (Hom.pullbackToUnit
      (sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I)) a) f)

/-- The graph coefficient in the section-induced ideal frame is the actual
original graph-twisted functional divided by the original numerator functional.
It may vanish; only the numerator and the untwisted pole are inverted. -/
theorem sectionPairIdealFrame_graphCoefficient
    (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (sectionPairIdealFrame f I T b a).inv ≫ Hom.pullbackToUnit φ f =
      inv (Hom.pullbackToUnit
        (sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I)) a) f) ≫
          Hom.pullbackToUnit
            (sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I))
              (twistedIdealSection X I T φ b)) f := by
  rw [← poleFunctionalIdealIso_twistedSection f I T b φ]
  simp only [sectionPairIdealFrame, Iso.trans_inv, asIso_inv, Category.assoc,
    Iso.inv_hom_id_assoc]

/-- The full original boundary section equation computes the same induced ideal
coordinate, including graph zeros and nonreduced boundary structure. -/
theorem sectionPairIdealFrame_graphCoefficient_boundary
    {B : Scheme.{u}} (r : B ⟶ W)
    (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (θ : SheafOfModules.unit B.ringCatSheaf ⟶ SheafOfModules.unit B.ringCatSheaf)
    (h : pullbackSectionMap (r ≫ f) (twistedIdealSection X I T φ b) =
      θ ≫ pullbackSectionMap (r ≫ f) a) :
    Scheme.Hom.unitEndomorphismPullback r
      ((sectionPairIdealFrame f I T b a).inv ≫ Hom.pullbackToUnit φ f) = θ := by
  rw [sectionPairIdealFrame_graphCoefficient]
  have : IsIso (pullbackUnitMap f
      (sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I)) a)) := by
    change IsIso (Hom.pullbackToUnit
      (sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I)) a) f)
    infer_instance
  exact functionalQuotient_boundary_of_sectionEquation f r
    (tensorLineBundle X T (dualLineBundle X I)) (twistedIdealSection X I T φ b) a θ h

/-- A genuine factorization through the original full boundary preserves its
coordinate on the section-induced ideal frame, without any boundary unit premise. -/
theorem sectionPairIdealFrame_graphCoefficient_boundary_of_factorization
    {B Q : Scheme.{u}} (g : B ⟶ X) (r : Q ⟶ W) (t : Q ⟶ B)
    (hfactor : r ≫ f = t ≫ g)
    (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (θ : SheafOfModules.unit B.ringCatSheaf ⟶ SheafOfModules.unit B.ringCatSheaf)
    (h : pullbackSectionMap g (twistedIdealSection X I T φ b) =
      θ ≫ pullbackSectionMap g a) :
    Scheme.Hom.unitEndomorphismPullback r
      ((sectionPairIdealFrame f I T b a).inv ≫ Hom.pullbackToUnit φ f) =
        Scheme.Hom.unitEndomorphismPullback t θ := by
  apply sectionPairIdealFrame_graphCoefficient_boundary
  rw [hfactor]
  exact scalar_pair_pullback t g (twistedIdealSection X I T φ b) a θ h

end AlgebraicGeometry.Scheme.Modules.Invertible
