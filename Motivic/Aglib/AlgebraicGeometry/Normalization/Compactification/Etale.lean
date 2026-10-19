/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.Finite
public import Aglib.AlgebraicGeometry.FunctionField.Normalization
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Finite normalization compactifying the original étale morphism

The generic finite étale cover is constructed from the original morphism. Its finite
normalization is compared with the original relative normalization, whose open immersion
is supplied by Zariski's main theorem. No compactification is assumed as input.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleCompactification

/-- Étaleness gives actual quasi-finiteness on affine charts. -/
theorem locallyQuasiFinite_of_etale {A B : Scheme.{u}} (g : A ⟶ B) [Etale g] :
    LocallyQuasiFinite g := by
  constructor
  intro U hU V hV e
  have he := g.etale_appLE hU hV e
  algebraize [(g.appLE U V e).hom]
  exact inferInstanceAs (Algebra.QuasiFinite _ _)

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  {Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] [QuasiCompact f] [IsSeparated f]

/-- The actual generic fibre of the original étale morphism is finite étale. -/
def genericCover : Scheme.FiniteEtale (Spec X.functionField) := by
  let g := pullback.fst (X.fromSpecStalk (genericPoint X)) f
  have : LocallyQuasiFinite g := locallyQuasiFinite_of_etale g
  have : IsFinite g := IsFinite.of_locallyQuasiFinite g
  exact Scheme.FiniteEtale.mk g

/-- The composite of the actual generic cover with the original generic inclusion. -/
abbrev genericMap := (genericCover X f).obj.hom ≫ X.fromSpecStalk (genericPoint X)

/-- Extend the actual generic inclusion into its finite normalization. -/
def inclusion : Y ⟶ (genericMap X f).normalization :=
  Scheme.extendFromGenericFiber X f (genericMap X f).fromNormalization
    (genericMap X f).toNormalization (by
      rw [Scheme.Hom.toNormalization_fromNormalization]
      exact pullback.condition)

omit [IsLocallyNoetherian X] [IsSeparated f] in
@[reassoc (attr := simp)]
theorem inclusion_over : inclusion X f ≫ (genericMap X f).fromNormalization = f :=
  Scheme.extendFromGenericFiber_over ..

omit [IsLocallyNoetherian X] [IsSeparated f] in
@[reassoc (attr := simp)]
theorem generic_inclusion : pullback.snd (X.fromSpecStalk (genericPoint X)) f ≫ inclusion X f =
    (genericMap X f).toNormalization :=
  Scheme.extendFromGenericFiber_comp ..

/-- The relative normalization of the original morphism is its generic finite normalization. -/
def normalizationIso : f.normalization ≅ (genericMap X f).normalization := by
  let a := f.normalizationDesc (inclusion X f) (genericMap X f).fromNormalization
    (inclusion_over X f).symm
  let b := (genericMap X f).normalizationDesc
    (pullback.snd (X.fromSpecStalk (genericPoint X)) f ≫ f.toNormalization)
    f.fromNormalization (by
      simp only [Category.assoc, Scheme.Hom.toNormalization_fromNormalization]
      exact pullback.condition)
  have ha : f.toNormalization ≫ a = inclusion X f := by simp [a]
  have hb : (genericMap X f).toNormalization ≫ b =
      pullback.snd (X.fromSpecStalk (genericPoint X)) f ≫ f.toNormalization := by simp [b]
  have hao : a ≫ (genericMap X f).fromNormalization = f.fromNormalization := by simp [a]
  have hbo : b ≫ f.fromNormalization = (genericMap X f).fromNormalization := by simp [b]
  have hi : inclusion X f ≫ b = f.toNormalization := by
    apply Scheme.genericFiber_hom_ext X f f.fromNormalization
    · simp only [Category.assoc, hbo, inclusion_over]
    · exact f.toNormalization_fromNormalization
    · rw [← Category.assoc, generic_inclusion, hb]
  refine ⟨a, b, ?_, ?_⟩
  · apply Scheme.Hom.normalization.hom_ext f _ _ f.fromNormalization
    · simpa only [← Category.assoc, ha, Category.comp_id] using hi
    · simp only [Category.assoc, hbo, hao]
    · simp
  · apply Scheme.Hom.normalization.hom_ext (genericMap X f) _ _
      (genericMap X f).fromNormalization
    · rw [← Category.assoc, hb, Category.assoc, ha, Category.comp_id]
      exact generic_inclusion X f
    · simp only [Category.assoc, hao, hbo]
    · simp


/-- The comparison retains the literal map to the original target. -/
@[reassoc (attr := simp)]
theorem normalizationIso_hom_over :
    (normalizationIso X f).hom ≫ (genericMap X f).fromNormalization = f.fromNormalization := by
  simp [normalizationIso]

/-- The original étale source embeds openly in its actual finite generic normalization. -/
instance inclusion_isOpenImmersion : IsOpenImmersion (inclusion X f) := by
  have : LocallyQuasiFinite f := locallyQuasiFinite_of_etale f
  have he : f.toNormalization ≫ (normalizationIso X f).hom = inclusion X f := by
    simp [normalizationIso]
  rw [← he]
  infer_instance

/-- Finiteness is derived from the constructed generic cover, not supplied as a model. -/
instance finite_genericNormalization : IsFinite (genericMap X f).fromNormalization :=
  Scheme.FiniteEtale.GenericNormalization.instIsFinite X (genericCover X f)

/-- The original relative normalization itself is finite over the target. -/
theorem finite_normalization : IsFinite f.fromNormalization := by
  rw [← normalizationIso_hom_over X f]
  infer_instance

omit [IsSeparated f] in
/-- Over a proper target the constructed finite normalization is proper as well. -/
theorem proper_compactification {S : Scheme.{u}} (q : X ⟶ S) [IsProper q] :
    IsProper ((genericMap X f).fromNormalization ≫ q) := by infer_instance

end AlgebraicGeometry.Scheme.EtaleCompactification
