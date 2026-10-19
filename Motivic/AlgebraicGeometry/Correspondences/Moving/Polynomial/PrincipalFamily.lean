/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyUnitOpen
public import Motivic.AlgebraicGeometry.Correspondences.Moving.PrincipalOrder
public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.Relative.GeneratorComposition
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Morphisms.Affine


/-!
# The original signed principal family as a finite correspondence

The whole-boundary unit locus is constructed from the literal polynomial.
Properness and retained relative smoothness are transported through the actual
Cartesian square. The native principal-order producer proves support finiteness
and component dominance; no flatness of the support is assumed. Integrality of
the actual ambient product is explicit in this componentwise intermediate.
Zero/one endpoint identification is not asserted here.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules.Invertible.PolynomialBoundaryPencil
open AlgebraicGeometry.PrincipalFamilyUnitOpen

universe u


namespace Motivic.PrincipalFamilyCorrespondence

variable {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k)))
  [IsAffine X.left] {C V W B : Scheme.{u}}
  (q : C ⟶ X.left) [IsProper q]
  (j : V ⟶ C) [IsOpenImmersion j] [V.IsQuasiAffine]
  [SmoothOfRelativeDimension 1 (j ≫ q)]
  (v : W ⟶ C) [IsOpenImmersion v] (b : B ⟶ W) [Nonempty B]
  (hcover : (Set.range j)ᶜ ⊆ Set.range (b ≫ v))
  (f : Γ(W, ⊤)) (hf : b.appTop f = 1)
  [AlgebraicGeometry.IsIntegral (parameterSpace (q ≫ X.hom))]
  [AlgebraicGeometry.IsNoetherian (parameterSpace (q ≫ X.hom))]
  (g : V ⟶ Y.left) (hbase : j ≫ q ≫ X.hom = g ≫ Y.hom)

/-- The original compactification projection after polynomial base change. -/
abbrev familyProjection := lineMap X.hom q

/-- The original retained open after polynomial base change. -/
abbrev retainedInclusion := lineMap (q ≫ X.hom) j

instance : IsProper (familyProjection X q) :=
  MorphismProperty.of_isPullback (lineMap_isPullback X.hom q).flip inferInstance

instance : SmoothOfRelativeDimension 1 (retainedInclusion X q j ≫ familyProjection X q) :=
  MorphismProperty.of_isPullback
    ((lineMap_isPullback (q ≫ X.hom) j).paste_horiz
      (lineMap_isPullback X.hom q)).flip inferInstance

instance : (parameterSpace (j ≫ (q ≫ X.hom))).IsQuasiAffine := by
  have : IsAffineHom (projection (j ≫ (q ≫ X.hom))) := by
    dsimp only [projection, parameterSpace]
    exact MorphismProperty.pullback_fst _ _ inferInstance
  exact Scheme.IsQuasiAffine.of_isAffineHom (projection (j ≫ (q ≫ X.hom)))

include hbase in
omit [IsAffine X.left] [IsProper q] [IsOpenImmersion j] [V.IsQuasiAffine]
  [SmoothOfRelativeDimension 1 (j ≫ q)]
  [AlgebraicGeometry.IsIntegral (parameterSpace (q ≫ X.hom))]
  [AlgebraicGeometry.IsNoetherian (parameterSpace (q ≫ X.hom))] in
/-- The original target map commutes with the unchanged scalar structural maps. -/
theorem family_base :
    retainedInclusion X q j ≫ familyProjection X q ≫
        _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineHom X.hom =
      (projection (j ≫ (q ≫ X.hom)) ≫ g) ≫ Y.hom := by
  change lineMap (q ≫ X.hom) j ≫ lineMap X.hom q ≫ projection X.hom ≫ X.hom = _
  rw [lineMap_projection_assoc, lineMap_projection_assoc]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun r => projection (j ≫ (q ≫ X.hom)) ≫ r) hbase)

/-- The actual native-order signed cylinder correspondence. Finiteness and
component dominance are derived internally from the whole original boundary. -/
def correspondence : Cor.mk
    (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X) ⟶ Cor.mk Y
    := by
  let : IsAffine ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsAffine X.left)
  have : IsAffineHom (projection X.hom) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : IsAffine (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite
      X).left :=
    isAffine_of_isAffineHom (projection X.hom)
  let U := ambientUnitOpen (q ≫ X.hom) v f
  let s := ambientUnitSection (q ≫ X.hom) v f
  have : Nonempty U := nonempty_ambientUnitOpen_of_boundary (q ≫ X.hom) v b f hf
  exact PrincipalOrderCorrespondence.correspondence (familyProjection X q)
    (retainedInclusion X q j) U
    (complement_subset_ambientUnitOpen (q ≫ X.hom) j v b hcover f hf)
    s (isUnit_ambientUnitSection (q ≫ X.hom) v f)
    (projection (j ≫ (q ≫ X.hom)) ≫ g) (family_base X Y q j g hbase)

end Motivic.PrincipalFamilyCorrespondence
