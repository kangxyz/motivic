module

public import Motivic.Aglib.AlgebraicGeometry.Simplex.AffineSchemeUnitProjection
public import Motivic.Aglib.AlgebraicGeometry.Simplex.CategoricalProduct

/-! # Actual simplex products over affine smooth schemes -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicSimplex
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- The actual base-changed simplex as a scheme-valued cosimplicial object. -/
def relativeSimplexScheme (X : SmoothSite (Spec (.of k))) : CosimplicialObject Scheme.{u} :=
  cosimplicialSmoothSite k ⋙ SmoothSite.baseChange X.hom ⋙ SmoothSite.forgetScheme X.left

/-- Affine coordinates on the source, without changing the actual relative products. -/
def affineSourceCoefficient (X : SmoothSite (Spec (.of k))) : k →+* Γ(X.left, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop).hom

/-- Every face and degeneracy respects the actual affine-source comparison. -/
def affineSourceRelativeSimplexIso (X : SmoothSite (Spec (.of k))) [IsAffine X.left] :
    affineRelativeSimplex (affineSourceCoefficient X) ≅ relativeSimplexScheme X :=
  NatIso.ofComponents (fun n => asIso
    (pullback.map ((cosimplicialSmoothSite k).obj n).hom
      (Spec.map (CommRingCat.ofHom (affineSourceCoefficient X)))
      ((cosimplicialSmoothSite k).obj n).hom X.hom
      (𝟙 _) X.left.isoSpec.inv (𝟙 _) (by simp)
      (by simpa [affineSourceCoefficient] using
        (@isoSpec_inv_map k _ X.left inferInstance X.hom).symm))) (by
    intro n m f
    apply pullback.hom_ext <;>
      simp [relativeSimplexScheme, affineRelativeSimplex, SmoothSite.baseChange_map_left])

/-- Categorical parameter products are the same relative scheme products,
including the swap of the two actual Cartesian factors. -/
def parameterRelativeSimplexIso (X : SmoothSite (Spec (.of k))) :
    SingularComplex.parameterCosimplicial (cosimplicialSmoothSite k) X ⋙
      SmoothSite.forgetScheme (Spec (.of k)) ≅ relativeSimplexScheme X :=
  (isoWhiskerRight (categoricalSimplexProductIso X)
    (SmoothSite.forgetScheme (Spec (.of k)))) ≪≫
      NatIso.ofComponents (fun n => pullbackSymmetry X.hom
        ((cosimplicialSmoothSite k).obj n).hom) (by
          intro n m f
          apply pullback.hom_ext <;>
            simp [productCosimplicialSmoothSite, relativeSimplexScheme,
              SmoothSite.baseChange_map_left, SmoothSite.productMap, SmoothSite.productLift,
              SmoothSite.homMk, SmoothSite.productFst, SmoothSite.productSnd])

end AlgebraicSimplex
