module
public import Aglib.AlgebraicGeometry.FunctionField.Normalization

/-! # Extend the original function-field map from a normal source

Unlike generic-fiber extension over a smooth morphism, this construction only
uses normality of the source itself. This is needed for finite coordinate maps
which are generically étale but have a genuine branch locus.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme
variable (Y : Scheme.{u}) [IsIntegral Y]
  [∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)]
  {X Z : Scheme.{u}} (p : Y ⟶ X) (q : Z ⟶ X) [IsIntegralHom q]

/-- An actual map on the original source function field extends across a normal
source when its target is integral over the original base. -/
def extendFromFunctionField (m : Spec Y.functionField ⟶ Z)
    (hm : m ≫ q = Y.fromSpecStalk (genericPoint Y) ≫ p) : Y ⟶ Z :=
  inv (Y.fromSpecStalk (genericPoint Y)).fromNormalization ≫
    (Y.fromSpecStalk (genericPoint Y)).normalizationDesc
      (pullback.lift m (Y.fromSpecStalk (genericPoint Y)) hm)
      (pullback.snd q p) (by simp) ≫ pullback.fst q p

@[reassoc (attr := simp)]
theorem extendFromFunctionField_over (m : Spec Y.functionField ⟶ Z)
    (hm : m ≫ q = Y.fromSpecStalk (genericPoint Y) ≫ p) :
    extendFromFunctionField Y p q m hm ≫ q = p := by
  simp only [extendFromFunctionField, Category.assoc, pullback.condition]
  rw [← Category.assoc _ _ p, Scheme.Hom.normalizationDesc_comp]
  simp

@[reassoc (attr := simp)]
theorem extendFromFunctionField_comp (m : Spec Y.functionField ⟶ Z)
    (hm : m ≫ q = Y.fromSpecStalk (genericPoint Y) ≫ p) :
    Y.fromSpecStalk (genericPoint Y) ≫ extendFromFunctionField Y p q m hm = m := by
  have hi : Y.fromSpecStalk (genericPoint Y) ≫
      inv (Y.fromSpecStalk (genericPoint Y)).fromNormalization =
      (Y.fromSpecStalk (genericPoint Y)).toNormalization := by
    apply (cancel_mono (Y.fromSpecStalk (genericPoint Y)).fromNormalization).mp
    simp
  simp only [extendFromFunctionField]
  rw [← Category.assoc, hi]
  simp only [Scheme.Hom.toNormalization_normalizationDesc_assoc, pullback.lift_fst]

/-- The extension is determined by the original function-field map and base square. -/
theorem functionField_extension_hom_ext {f g : Y ⟶ Z}
    (hf : f ≫ q = p) (hg : g ≫ q = p)
    (h : Y.fromSpecStalk (genericPoint Y) ≫ f =
      Y.fromSpecStalk (genericPoint Y) ≫ g) : f = g := by
  let jf := pullback.lift f (𝟙 Y) (by simpa using hf)
  let jg := pullback.lift g (𝟙 Y) (by simpa using hg)
  have hj : (Y.fromSpecStalk (genericPoint Y)).fromNormalization ≫ jf =
      (Y.fromSpecStalk (genericPoint Y)).fromNormalization ≫ jg := by
    apply Scheme.Hom.normalization.hom_ext
      (Y.fromSpecStalk (genericPoint Y)) _ _ (pullback.snd q p)
    · simp only [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization]
      apply pullback.hom_ext
      · simpa [jf, jg] using h
      · simp [jf, jg]
    · simp [jf]
    · simp [jg]
  have he : jf = jg := (cancel_epi _).mp hj
  simpa [jf, jg] using congrArg (fun j => j ≫ pullback.fst q p) he

end AlgebraicGeometry.Scheme
