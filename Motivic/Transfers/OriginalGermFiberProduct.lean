/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.OriginalGermInverseImageGraph
public import Motivic.Transfers.OriginalGermTupleEnvelope
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleOriginalFiberSections
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleImageFamily

/-! # Original germ coordinates on the actual residue-field fiber components -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace Motivic.SmoothSite
variable {B : Scheme.{u}} [IsAffine B] (X : SmoothSite B)
  (F : Sheaf (nisnevichTopology B) AddCommGrpCat.{u + 1})

/-- The original structural arrow of a small étale object, in the smooth site. -/
def fiberProductToBase (V : FiniteEtaleSite X.left) :
    (FiniteEtaleSite.toSmoothSite X).obj V ⟶ X :=
  SmoothSite.homMk V.hom rfl

instance fiberProductToBase_etale (V : FiniteEtaleSite X.left) :
    Etale (fiberProductToBase X V).left := inferInstanceAs (Etale V.hom)

/-- The ordinary coefficient on the literal residue-field site. -/
def originalResidueCoefficient (x : X.left) :
    Sheaf (FiniteEtaleSite.nisnevichTopology (Spec (X.left.residueField x)))
      AddCommGrpCat.{u + 1} :=
  (FiniteEtaleSite.inverseImage (X.left.fromSpecResidueField x)).obj
    ((FiniteEtaleSite.restrict X AddCommGrpCat).obj F)

omit [IsAffine B] in
/-- The actual field factorization at an original point of the fiber. -/
theorem originalFiberFactorization (V : FiniteEtaleSite X.left) (x : X.left)
    (v : V.hom ⁻¹' {x}) :
    V.hom.originalFiberFieldMap x v ≫ X.left.fromSpecResidueField x =
      V.left.fromSpecResidueField v.1 ≫ (fiberProductToBase X V).left := by
  rcases v with ⟨v, hv⟩
  change V.hom v = x at hv
  subst x
  exact V.hom.SpecMap_residueFieldMap_fromSpecResidueField v

/-- Each original germ is the literal field component of the inverse-image coefficient. -/
def originalFiberGermIso (V : FiniteEtaleSite X.left) (x : X.left)
    (v : V.hom ⁻¹' {x}) :
    (nisnevichPointFiberCocone ((FiniteEtaleSite.toSmoothSite X).obj V) v.1 F.obj).pt ≅
      (originalResidueCoefficient X F x).obj.obj
        (op (FiniteEtaleSite.originalFiberObject V x v)) :=
  originalGermInverseImageOfFactorization F (fiberProductToBase X V) v.1
    (X.left.fromSpecResidueField x) (V.hom.originalFiberFieldMap x v)
    (originalFiberFactorization X V x v)

/-- The graph comparison also accepts equal original presentations of both maps. -/
@[reassoc]
theorem originalGermFactorizationGraph_of_eq
    {U V : SmoothSite B} (f : V ⟶ X) [Etale f.left]
    (g : U ⟶ V) [Etale g.left] (fs : U ⟶ X) [Etale fs.left]
    (hfs : g ≫ f = fs) (v : U.left) {S : Scheme.{u}} (b : S ⟶ X.left)
    (q : Spec (V.left.residueField (g.left v)) ⟶ S)
    [Etale q] [IsSeparated q] [QuasiCompact q]
    (qs : Spec (U.left.residueField v) ⟶ S)
    [Etale qs] [IsSeparated qs] [QuasiCompact qs]
    (hq : Spec.map (g.left.residueFieldMap v) ≫ q = qs)
    (hf : q ≫ b = V.left.fromSpecResidueField (g.left v) ≫ f.left)
    (hs : qs ≫ b = U.left.fromSpecResidueField v ≫ fs.left) :
    originalGermPullback.{u, u + 1} F.obj g v ≫
      (originalGermInverseImageOfFactorization F fs v b qs hs).hom =
    (originalGermInverseImageOfFactorization F f (g.left v) b q hf).hom ≫
      ((FiniteEtaleSite.inverseImage b).obj
        ((FiniteEtaleSite.restrict X AddCommGrpCat).obj F)).obj.map
          (MorphismProperty.Over.homMk (Spec.map (g.left.residueFieldMap v)) hq :
            FiniteEtaleSite.fieldObject _ qs ⟶ FiniteEtaleSite.fieldObject _ q).op := by
  subst fs
  subst qs
  exact originalGermInverseImageOfFactorization_pullback F f g v b q hf

/-- Actual germ restriction agrees with the original component field map. -/
@[reassoc]
theorem originalFiberGermIso_naturality {U V : FiniteEtaleSite X.left}
    (g : U ⟶ V) (x : X.left) (v : U.hom ⁻¹' {x}) :
    originalGermPullback.{u, u + 1} F.obj ((FiniteEtaleSite.toSmoothSite X).map g) v.1 ≫
      (originalFiberGermIso X F U x v).hom =
    (originalFiberGermIso X F V x (FiniteEtaleSite.originalFiberIndex x g v)).hom ≫
      (originalResidueCoefficient X F x).obj.map
        (FiniteEtaleSite.originalFiberObjectMap x g v).op := by
  have hg : Etale ((FiniteEtaleSite.toSmoothSite X).map g).left := by
    change Etale g.left
    have : Etale (g.left ≫ V.hom) := by
      rw [MorphismProperty.Over.w]
      infer_instance
    exact Etale.of_comp g.left V.hom
  have hbase : (FiniteEtaleSite.toSmoothSite X).map g ≫ fiberProductToBase X V =
      fiberProductToBase X U := by
    apply MorphismProperty.Over.Hom.ext
    exact MorphismProperty.Over.w g
  exact originalGermFactorizationGraph_of_eq X F (fiberProductToBase X V)
    ((FiniteEtaleSite.toSmoothSite X).map g) (fiberProductToBase X U) hbase v.1
    (X.left.fromSpecResidueField x)
    (V.hom.originalFiberFieldMap x (FiniteEtaleSite.originalFiberIndex x g v))
    (U.hom.originalFiberFieldMap x v)
    (MorphismProperty.Over.w (FiniteEtaleSite.originalFiberObjectMap x g v))
    (originalFiberFactorization X V x (FiniteEtaleSite.originalFiberIndex x g v))
    (originalFiberFactorization X U x v)

end Motivic.SmoothSite
