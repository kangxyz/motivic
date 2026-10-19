/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Identity.Basic
public import Motivic.Aglib.AlgebraicGeometry.Graph.ProductTransversality
public import Motivic.AlgebraicGeometry.Correspondences.Graph.Components.Composition

/-!
# The actual coefficient chart for mixed graph and exterior incidence

The product of a graph-component support with an exterior support is an open
part of the literal mixed product coefficient scheme. The chart retains both
middle-coordinate maps; neither the support nor the parameter map is assumed
flat.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X Y T T' : SmoothSite (Spec (.of k))}
  (V : FiniteCorrespondenceGenerator X.hom Y.hom)

/-- The actual exterior support and its closed image are isomorphic. -/
def exteriorIdentitySchemeIso (T : SmoothSite (Spec (.of k)))
    [GeometricallyIntegral T.hom] :
    V.exteriorIdentitySupport T ≅ (V.exteriorIdentityGenerator T).scheme :=
  asIso (V.exteriorIdentityInclusion T).toImage

@[reassoc (attr := simp)]
theorem exteriorIdentitySchemeIso_hom_projection (T : SmoothSite (Spec (.of k)))
    [GeometricallyIntegral T.hom] :
    (V.exteriorIdentitySchemeIso T).hom ≫ (V.exteriorIdentityGenerator T).projection =
      V.exteriorIdentitySource T :=
  V.exteriorIdentityInclusion_toImage_source T

@[reassoc (attr := simp)]
theorem exteriorIdentitySchemeIso_hom_targetProjection (T : SmoothSite (Spec (.of k)))
    [GeometricallyIntegral T.hom] :
    (V.exteriorIdentitySchemeIso T).hom ≫ (V.exteriorIdentityGenerator T).targetProjection =
      V.exteriorIdentityTarget T := by
  change (V.exteriorIdentityInclusion T).toImage ≫
    (V.exteriorIdentityInclusion T).imageι ≫ _ = _
  rw [← Category.assoc, Scheme.Hom.toImage_imageι, exteriorIdentityInclusion_snd]

@[reassoc (attr := simp)]
theorem exteriorIdentitySchemeIso_inv_source (T : SmoothSite (Spec (.of k)))
    [GeometricallyIntegral T.hom] :
    (V.exteriorIdentitySchemeIso T).inv ≫ V.exteriorIdentitySource T =
      (V.exteriorIdentityGenerator T).projection := by
  rw [← exteriorIdentitySchemeIso_hom_projection, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
theorem exteriorIdentitySchemeIso_inv_target (T : SmoothSite (Spec (.of k)))
    [GeometricallyIntegral T.hom] :
    (V.exteriorIdentitySchemeIso T).inv ≫ V.exteriorIdentityTarget T =
      (V.exteriorIdentityGenerator T).targetProjection := by
  rw [← exteriorIdentitySchemeIso_hom_targetProjection, Iso.inv_hom_id_assoc]

end Motivic.FiniteCorrespondenceGenerator

namespace Motivic.SimplexExteriorGraph
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Graph
open _root_.AlgebraicGeometry.Scheme.Products

variable {k : Type u} [Field k] {X Y T T' : SmoothSite (Spec (.of k))}
  (u : T ⟶ T')

/-- The original product source, with the parameter structure equality made explicit. -/
def parameterProductIso :
    (SmoothSite.product X T).left ≅ pullback X.hom (u.left ≫ T'.hom) :=
  pullback.congrHom rfl (MorphismProperty.Over.w u).symm

@[reassoc (attr := simp)]
theorem parameterProductIso_hom_fst :
    (parameterProductIso (X := X) u).hom ≫ pullback.fst X.hom (u.left ≫ T'.hom) =
      pullback.fst X.hom T.hom := by
  simp only [parameterProductIso, pullback.congrHom_hom, pullback.map,
    pullback.lift_fst, Category.comp_id]

@[reassoc (attr := simp)]
theorem parameterProductIso_hom_snd :
    (parameterProductIso (X := X) u).hom ≫ pullback.snd X.hom (u.left ≫ T'.hom) =
      pullback.snd X.hom T.hom := by
  simp only [parameterProductIso, pullback.congrHom_hom, pullback.map,
    pullback.lift_snd, Category.comp_id]

@[reassoc (attr := simp)]
theorem productMap_id_fst :
    (SmoothSite.productMap (𝟙 X) u).left ≫ pullback.fst X.hom T'.hom =
      pullback.fst X.hom T.hom := by
  change (SmoothSite.productMap (𝟙 X) u ≫ SmoothSite.productFst X T').left = _
  rw [SmoothSite.productMap_fst]
  rfl

@[reassoc (attr := simp)]
theorem productMap_id_snd :
    (SmoothSite.productMap (𝟙 X) u).left ≫ pullback.snd X.hom T'.hom =
      pullback.snd X.hom T.hom ≫ u.left := by
  change (SmoothSite.productMap (𝟙 X) u ≫ SmoothSite.productSnd X T').left = _
  rw [SmoothSite.productMap_snd]
  rfl

variable (V : FiniteCorrespondenceGenerator X.hom Y.hom)
  [GeometricallyIntegral T'.hom]
  (A : FiniteCorrespondenceGenerator (SmoothSite.product X T).hom
    (SmoothSite.product X T').hom)

/-- The source support's map into the original first product factor. -/
def firstChart : A.scheme ⟶ pullback X.hom (u.left ≫ T'.hom) :=
  A.projection ≫ (parameterProductIso (X := X) u).hom

omit [GeometricallyIntegral T'.hom] in
@[reassoc (attr := simp)]
theorem firstChart_over :
    firstChart u A ≫ Product.productHom X.hom (u.left ≫ T'.hom) =
      A.targetProjection ≫ (SmoothSite.product X T').hom := by
  simp only [firstChart, Product.productHom, Category.assoc,
    parameterProductIso_hom_fst_assoc]
  exact A.projection_base

/-- The exterior image support is returned to the literal second product factor. -/
abbrev secondChart : (V.exteriorIdentityGenerator T').scheme ⟶
    pullback (V.projection ≫ X.hom) T'.hom :=
  (V.exteriorIdentitySchemeIso T').inv

@[reassoc (attr := simp)]
theorem secondChart_over :
    secondChart V ≫ Product.productHom (V.projection ≫ X.hom) T'.hom =
      (V.exteriorIdentityGenerator T').projection ≫ (SmoothSite.product X T').hom := by
  rw [← V.exteriorIdentitySchemeIso_inv_source T']
  simp only [secondChart, Product.productHom, SmoothSite.product_hom,
    Category.assoc, V.exteriorIdentitySource_fst_assoc]

/-- The genuine coefficient product maps to the mixed product chart. -/
def coefficientChart : A.supportProduct (V.exteriorIdentityGenerator T') ⟶
    Product.coefficient X.hom T'.hom V.projection u.left :=
  pullback.map _ _ _ _ (firstChart u A) (secondChart V) (𝟙 _)
    (by simp)
    (by simp)

instance coefficientChart_isOpenImmersion [IsOpenImmersion A.projection] :
    IsOpenImmersion (coefficientChart u V A) := by
  have : IsOpenImmersion (firstChart u A) := by unfold firstChart; infer_instance
  unfold coefficientChart
  infer_instance

@[reassoc (attr := simp)]
theorem coefficientChart_first :
    coefficientChart u V A ≫
      Product.first X.hom (u.left ≫ T'.hom) (V.projection ≫ X.hom) T'.hom =
    pullback.fst _ _ ≫ A.projection ≫ pullback.fst X.hom T.hom := by
  simp only [coefficientChart, Product.first, pullback.map,
    pullback.lift_fst_assoc, firstChart, Category.assoc, parameterProductIso_hom_fst]

@[reassoc (attr := simp)]
theorem coefficientChart_second :
    coefficientChart u V A ≫
      Product.second X.hom (u.left ≫ T'.hom) (V.projection ≫ X.hom) T'.hom =
    pullback.fst _ _ ≫ A.projection ≫ pullback.snd X.hom T.hom := by
  simp only [coefficientChart, Product.second, pullback.map,
    pullback.lift_fst_assoc, firstChart, Category.assoc, parameterProductIso_hom_snd]

@[reassoc (attr := simp)]
theorem coefficientChart_third :
    coefficientChart u V A ≫
      Product.third X.hom (u.left ≫ T'.hom) (V.projection ≫ X.hom) T'.hom =
    pullback.snd _ _ ≫ secondChart V ≫ pullback.fst (V.projection ≫ X.hom) T'.hom := by
  simp only [coefficientChart, Product.third, pullback.map,
    pullback.lift_snd_assoc, Category.assoc]

@[reassoc (attr := simp)]
theorem coefficientChart_fourth :
    coefficientChart u V A ≫
      Product.fourth X.hom (u.left ≫ T'.hom) (V.projection ≫ X.hom) T'.hom =
    pullback.snd _ _ ≫ secondChart V ≫ pullback.snd (V.projection ≫ X.hom) T'.hom := by
  simp only [coefficientChart, Product.fourth, pullback.map,
    pullback.lift_snd_assoc, Category.assoc]

/-- Both literal middle coordinates survive the open coefficient chart. -/
theorem coefficientChart_middlePair
    (hA : A.projection ≫ (SmoothSite.productMap (𝟙 X) u).left = A.targetProjection) :
    coefficientChart u V A ≫ Product.mixedPair X.hom T'.hom V.projection u.left =
      A.supportProductInclusion (V.exteriorIdentityGenerator T') ≫
        correspondenceMiddlePair (SmoothSite.product X T).hom
          (SmoothSite.product X T').hom (SmoothSite.product Y T').hom := by
  apply pullback.hom_ext (f := (SmoothSite.product X T').hom)
    (g := (SmoothSite.product X T').hom)
  · simp only [Category.assoc, correspondenceMiddlePair_fst,
      FiniteCorrespondenceGenerator.supportProductInclusion_fst_assoc]
    change _ = pullback.fst (A.targetProjection ≫ (SmoothSite.product X T').hom)
      ((V.exteriorIdentityGenerator T').projection ≫ (SmoothSite.product X T').hom) ≫
        A.targetProjection
    apply Eq.trans ?_ (congrArg (fun q =>
      pullback.fst (A.targetProjection ≫ (SmoothSite.product X T').hom)
        ((V.exteriorIdentityGenerator T').projection ≫ (SmoothSite.product X T').hom) ≫ q) hA)
    apply pullback.hom_ext (f := X.hom) (g := T'.hom)
    · simp [Product.mixedPair, Category.assoc]
    · simp [Product.mixedPair, Category.assoc]
  · simp only [Category.assoc, correspondenceMiddlePair_snd,
      FiniteCorrespondenceGenerator.supportProductInclusion_snd_assoc]
    change _ = pullback.snd (A.targetProjection ≫ (SmoothSite.product X T').hom)
      ((V.exteriorIdentityGenerator T').projection ≫ (SmoothSite.product X T').hom) ≫
        (V.exteriorIdentityGenerator T').projection
    apply Eq.trans ?_ (congrArg (fun q =>
      pullback.snd (A.targetProjection ≫ (SmoothSite.product X T').hom)
        ((V.exteriorIdentityGenerator T').projection ≫ (SmoothSite.product X T').hom) ≫ q)
      (V.exteriorIdentitySchemeIso_inv_source T'))
    apply pullback.hom_ext (f := X.hom) (g := T'.hom)
    · simp [Product.mixedPair, Category.assoc, secondChart,
        -FiniteCorrespondenceGenerator.exteriorIdentitySchemeIso_inv_source,
        -FiniteCorrespondenceGenerator.exteriorIdentitySchemeIso_inv_source_assoc]
    · simp [Product.mixedPair, Category.assoc, secondChart,
        -FiniteCorrespondenceGenerator.exteriorIdentitySchemeIso_inv_source,
        -FiniteCorrespondenceGenerator.exteriorIdentitySchemeIso_inv_source_assoc]

end Motivic.SimplexExteriorGraph
