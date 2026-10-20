module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.FunctionField.Extension
public import Aglib.AlgebraicGeometry.FunctionField.Map
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.Finite
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Finite compactification for an actual generically étale normal source

The finite coordinate map need not be étale on its branch locus. Its original
normal source embeds in the finite normalization of its actual function field.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.GenericallyEtaleCompactification
variable (X Y : Scheme.{u}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  [∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)]
  (f : Y ⟶ X) [IsDominant f]
  [IsFinite (Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap f)))]
  [Etale (Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap f)))]

/-- The actual extension of original function fields, not a chosen cover. -/
def genericCover : Scheme.FiniteEtale (Spec X.functionField) :=
  Scheme.FiniteEtale.mk (Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap f)))

/-- The map from the original source function field to the original target. -/
abbrev genericMap :=
  Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap f)) ≫
    X.fromSpecStalk (genericPoint X)

/-- The literal normal-source extension into the finite generic normalization. -/
def inclusion : Y ⟶ (genericMap X Y f).normalization :=
  Scheme.extendFromFunctionField Y f (genericMap X Y f).fromNormalization
    (genericMap X Y f).toNormalization (by
      rw [Scheme.Hom.toNormalization_fromNormalization]
      exact (Scheme.fromSpecStalk_genericPoint_naturality f).symm)

omit [IsLocallyNoetherian X] [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  [Etale (Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap f)))] in
@[reassoc (attr := simp)]
theorem inclusion_over : inclusion X Y f ≫ (genericMap X Y f).fromNormalization = f :=
  Scheme.extendFromFunctionField_over ..

omit [IsLocallyNoetherian X] [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  [Etale (Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap f)))] in
@[reassoc (attr := simp)]
theorem generic_inclusion : Y.fromSpecStalk (genericPoint Y) ≫ inclusion X Y f =
    (genericMap X Y f).toNormalization := Scheme.extendFromFunctionField_comp ..

variable [QuasiCompact f] [QuasiSeparated f]

/-- Original relative normalization equals the constructed finite generic normalization. -/
def normalizationIso : f.normalization ≅ (genericMap X Y f).normalization := by
  let a := f.normalizationDesc (inclusion X Y f) (genericMap X Y f).fromNormalization
    (inclusion_over X Y f).symm
  let b := (genericMap X Y f).normalizationDesc
    (Y.fromSpecStalk (genericPoint Y) ≫ f.toNormalization) f.fromNormalization (by
      simp only [Category.assoc, Scheme.Hom.toNormalization_fromNormalization]
      exact (Scheme.fromSpecStalk_genericPoint_naturality f).symm)
  have ha : f.toNormalization ≫ a = inclusion X Y f := by simp [a]
  have hb : (genericMap X Y f).toNormalization ≫ b =
      Y.fromSpecStalk (genericPoint Y) ≫ f.toNormalization := by simp [b]
  have hao : a ≫ (genericMap X Y f).fromNormalization = f.fromNormalization := by simp [a]
  have hbo : b ≫ f.fromNormalization = (genericMap X Y f).fromNormalization := by simp [b]
  have hi : inclusion X Y f ≫ b = f.toNormalization := by
    apply Scheme.functionField_extension_hom_ext Y f f.fromNormalization
    · simp only [Category.assoc, hbo, inclusion_over]
    · exact f.toNormalization_fromNormalization
    · rw [← Category.assoc, generic_inclusion, hb]
  refine ⟨a, b, ?_, ?_⟩
  · apply Scheme.Hom.normalization.hom_ext f _ _ f.fromNormalization
    · simpa only [← Category.assoc, ha, Category.comp_id] using hi
    · simp only [Category.assoc, hbo, hao]
    · simp
  · apply Scheme.Hom.normalization.hom_ext (genericMap X Y f) _ _
      (genericMap X Y f).fromNormalization
    · rw [← Category.assoc, hb, Category.assoc, ha, Category.comp_id]
      exact generic_inclusion X Y f
    · simp only [Category.assoc, hao, hbo]
    · simp

omit [IsLocallyNoetherian X] [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  [Etale (Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap f)))] in
@[reassoc (attr := simp)]
theorem normalizationIso_hom_over : (normalizationIso X Y f).hom ≫
    (genericMap X Y f).fromNormalization = f.fromNormalization := by simp [normalizationIso]

instance finite_genericNormalization : IsFinite (genericMap X Y f).fromNormalization :=
  Scheme.FiniteEtale.GenericNormalization.instIsFinite X (genericCover X Y f)

/-- The open immersion is derived by Zariski's main theorem for the original map. -/
instance inclusion_isOpenImmersion [LocallyQuasiFinite f] [LocallyOfFiniteType f]
    [IsSeparated f] :
    IsOpenImmersion (inclusion X Y f) := by
  have he : f.toNormalization ≫ (normalizationIso X Y f).hom = inclusion X Y f := by
    simp [normalizationIso]
  rw [← he]
  infer_instance

end AlgebraicGeometry.Scheme.GenericallyEtaleCompactification
