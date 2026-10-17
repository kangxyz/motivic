module

public import Motivic.AlgebraicGeometry.AffineBoundaryOneComplex
public import Motivic.AlgebraicGeometry.AffineSchemeSimplexComparison
public import Motivic.AlgebraicGeometry.SmoothSiteIntegralAffineHomology

/-! # The actual boundary-one singular sheaf complex is acyclic

The ordinary coefficient is global sections of the genuine localized-function
functor. The comparison to affine coordinate rings preserves all face maps.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicTopology

universe u

namespace Motivic.SmoothSite

open AlgebraicSimplex Polynomial.BoundaryOneRationalFunctions

variable (k : Type u) [Field k]

/-- Actual global boundary-one rational functions, with ordinary restriction. -/
def boundaryOnePresheaf : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (forgetScheme (Spec (.of k))).op ⋙ Scheme.Γ ⋙ functor

/-- The same actual coefficient in the original motivic coefficient universe. -/
def largeBoundaryOnePresheaf : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  boundaryOnePresheaf k ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- The original categorical parameter complex is acyclic on every affine smooth source. -/
theorem isZero_homology_boundaryOne_affine (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] (n : ℕ) :
    IsZero ((SingularComplex.parameterObj (cosimplicialSmoothSite k)
      (boundaryOnePresheaf k) X).homology n) := by
  let e := parameterRelativeSimplexIso X ≪≫ (affineSourceRelativeSimplexIso X).symm
  let e' := (alternatingFaceMapComplex AddCommGrpCat).mapIso
    (isoWhiskerRight (NatIso.op e.symm) (Scheme.Γ ⋙ functor))
  exact (isZero_homology_affineRelativeBoundaryOne Γ(X.left, ⊤)
    (affineSourceCoefficient X) n).of_iso
      ((HomologicalComplex.homologyFunctor AddCommGrpCat (.down ℕ) n).mapIso e')

private instance ulift_additive : AddCommGrpCat.uliftFunctor.{u + 1, u}.Additive where
  map_add := by intros; ext x; rfl

/-- Universe lifting preserves the actual all-degree affine acyclicity. -/
theorem isZero_homology_largeBoundaryOne_affine (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] (n : ℕ) :
    IsZero ((SingularComplex.parameterObj (cosimplicialSmoothSite k)
      (largeBoundaryOnePresheaf k) X).homology n) := by
  let K := SingularComplex.parameterObj (cosimplicialSmoothSite k) (boundaryOnePresheaf k) X
  let F := AddCommGrpCat.uliftFunctor.{u + 1, u}
  let e := (alternatingFaceMapComplexCompMapHomologicalComplexIso F).app
    (SingularComplex.simplicial
      (SingularComplex.parameterCosimplicial (cosimplicialSmoothSite k) X)
      (boundaryOnePresheaf k))
  have h : IsZero (((F.mapHomologicalComplex (.down ℕ)).obj K).homology n) :=
    (F.map_isZero (isZero_homology_boundaryOne_affine k X n)).of_iso
      ((K.sc n).mapHomologyIso F)
  exact h.of_iso
    ((HomologicalComplex.homologyFunctor AddCommGrpCat (.down ℕ) n).mapIso e.symm)

/-- The genuine singular coefficient sheaf complex in the original coefficient universe. -/
def boundaryOneSheafComplex :=
  SingularComplex.sheafObj (nisnevichTopology (Spec (.of k)))
    (cosimplicialSmoothSite k) (largeBoundaryOnePresheaf k)

/-- Every homology sheaf vanishes; no degree is omitted. -/
theorem isZero_homology_boundaryOneSheafComplex (n : ℕ) :
    IsZero ((boundaryOneSheafComplex k).homology n) := by
  apply isZero_sheafified_homology_of_integral_affine k
  intro X _ _
  let K := SingularComplex.presheafObj (cosimplicialSmoothSite k) (largeBoundaryOnePresheaf k)
  let E := (evaluation (SmoothSite (Spec (.of k)))ᵒᵖ AddCommGrpCat.{u + 1}).obj (op X)
  have h : IsZero (((E.mapHomologicalComplex (.down ℕ)).obj K).homology n) :=
    isZero_homology_largeBoundaryOne_affine k X n
  exact h.of_iso ((K.sc n).mapHomologyIso E).symm

end Motivic.SmoothSite
