/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightOne.Geometry.BoundaryOneDivisor
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Simplex.IntegralAffineSimplex

/-! # Boundary divisors into the original sheafified reduced-torus singular terms

The construction is degreewise on the original aC* complexes. It does not
replace aC*(F) by C*(aF), or assume these commute.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Simplicial

universe u

namespace Motivic.SmoothSiteBoundaryOneDivisor
open _root_.AlgebraicGeometry.Scheme

open _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The actual original reduced torus, with only its transfers forgotten. -/
abbrev rawReducedTorus := (toPresheaf k).obj (reducedTorus k 1)

/-- The genuine quotient map sends a boundary divisor into the original reduced torus. -/
def largeAffineReducedDivisor (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] [IsIntegral X.left] :
    (SmoothSite.largeBoundaryOnePresheaf k).obj (op X) ⟶ (rawReducedTorus k).obj (op X) :=
  largeAffineDivisor X ≫ ((toPresheaf k).map (toReducedTorus k 1)).app (op X)

/-- The original quotient retains ordinary naturality of the divisor. -/
theorem largeAffineReducedDivisor_natural
    {X Y : SmoothSite (Spec (.of k))} [IsAffine X.left] [IsAffine Y.left]
    [IsIntegral X.left] [IsIntegral Y.left] (f : X ⟶ Y) :
    (SmoothSite.largeBoundaryOnePresheaf k).map f.op ≫ largeAffineReducedDivisor k X =
      largeAffineReducedDivisor k Y ≫ (rawReducedTorus k).map f.op := by
  dsimp only [largeAffineReducedDivisor]
  rw [← Category.assoc, largeAffineDivisor_natural, Category.assoc,
    NatTrans.naturality, ← Category.assoc]

/-- The original raw singular reduced-torus complex, without substitute coefficients. -/
abbrev rawReducedSingular := SingularComplex.presheafObj
  (cosimplicialSmoothSite k) (rawReducedTorus k)

/-- The actual local divisor in every original singular degree. -/
def integralAffineSingularDivisor (n : ℕ) :
    (SmoothSite.integralAffineInclusion k).op ⋙
        (SingularComplex.presheafObj (cosimplicialSmoothSite k)
          (SmoothSite.largeBoundaryOnePresheaf k)).X n ⟶
      (SmoothSite.integralAffineInclusion k).op ⋙ (rawReducedSingular k).X n where
  app X := by
    let : IsAffine X.unop.obj.left := X.unop.property.1
    let : IsIntegral X.unop.obj.left := X.unop.property.2
    exact largeAffineReducedDivisor k (X.unop.obj ⨯ smoothSiteObj k n)
  naturality {X Y} f := by
    let : IsAffine X.unop.obj.left := X.unop.property.1
    let : IsIntegral X.unop.obj.left := X.unop.property.2
    let : IsAffine Y.unop.obj.left := Y.unop.property.1
    let : IsIntegral Y.unop.obj.left := Y.unop.property.2
    exact largeAffineReducedDivisor_natural k
      (prod.map f.unop.hom (𝟙 (smoothSiteObj k n)))

/-- Degreewise dense gluing into the original sheafified reduced singular term. -/
def singularDivisorToSheaf (n : ℕ) :
    (SingularComplex.presheafObj (cosimplicialSmoothSite k)
      (SmoothSite.largeBoundaryOnePresheaf k)).X n ⟶
    ((presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj ((rawReducedSingular k).X n)).obj :=
  SmoothSite.extendIntegralAffineHom k
    (G := (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj ((rawReducedSingular k).X n))
    (integralAffineSingularDivisor k n ≫
      whiskerLeft (SmoothSite.integralAffineInclusion k).op
        (toSheafify (SmoothSite.nisnevichTopology (Spec (.of k))) ((rawReducedSingular k).X n)))

/-- The map on the original aC* terms, obtained by the ordinary sheafification adjunction. -/
def singularSheafDivisor (n : ℕ) :
    (SmoothSite.boundaryOneSheafComplex k).X n ⟶
      (SingularComplex.sheafObj (SmoothSite.nisnevichTopology (Spec (.of k)))
        (cosimplicialSmoothSite k) (rawReducedTorus k)).X n :=
  ⟨sheafifyLift _ (singularDivisorToSheaf k n)
    (((presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj ((rawReducedSingular k).X n)).property)⟩

/-- Dense gluing preserves the literal original divisor on every integral affine source. -/
theorem singularDivisorToSheaf_app (n : ℕ) (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] [IsIntegral X.left] :
    (singularDivisorToSheaf k n).app (op X) =
      largeAffineReducedDivisor k (X ⨯ smoothSiteObj k n) ≫
        (toSheafify (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((rawReducedSingular k).X n)).app (op X) := by
  have h := Functor.IsCoverDense.sheafHom_restrict_eq
    (G := SmoothSite.integralAffineInclusion k)
    (ℱ' := (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj ((rawReducedSingular k).X n))
    (integralAffineSingularDivisor k n ≫
      whiskerLeft (SmoothSite.integralAffineInclusion k).op
        (toSheafify (SmoothSite.nisnevichTopology (Spec (.of k))) ((rawReducedSingular k).X n)))
  exact congrArg (fun η => η.app (op ⟨X, inferInstance, inferInstance⟩)) h

/-- The actual local divisor commutes with every alternating-face differential. -/
theorem largeAffineReducedDivisor_d (n : ℕ) (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] [IsIntegral X.left] :
    ((SingularComplex.presheafObj (cosimplicialSmoothSite k)
      (SmoothSite.largeBoundaryOnePresheaf k)).d (n + 1) n).app (op X) ≫
      largeAffineReducedDivisor k (X ⨯ smoothSiteObj k n) =
    largeAffineReducedDivisor k (X ⨯ smoothSiteObj k (n + 1)) ≫
      ((rawReducedSingular k).d (n + 1) n).app (op X) := by
  let : IsAffine (X ⨯ (cosimplicialSmoothSite k).obj ⦋n⦌).left :=
    inferInstanceAs (IsAffine (X ⨯ smoothSiteObj k n).left)
  let : IsIntegral (X ⨯ (cosimplicialSmoothSite k).obj ⦋n⦌).left :=
    inferInstanceAs (IsIntegral (X ⨯ smoothSiteObj k n).left)
  let : IsAffine (X ⨯ (cosimplicialSmoothSite k).obj ⦋n + 1⦌).left :=
    inferInstanceAs (IsAffine (X ⨯ smoothSiteObj k (n + 1)).left)
  let : IsIntegral (X ⨯ (cosimplicialSmoothSite k).obj ⦋n + 1⦌).left :=
    inferInstanceAs (IsIntegral (X ⨯ smoothSiteObj k (n + 1)).left)
  rw [SingularComplex.presheafObj_d_app, SingularComplex.presheafObj_d_app]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum,
    Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact largeAffineReducedDivisor_natural k
    (prod.map (𝟙 X) ((cosimplicialSmoothSite k).δ i))

/-- The degreewise extended maps preserve the original differential before source sheafification. -/
theorem singularDivisorToSheaf_d (n : ℕ) :
    (SingularComplex.presheafObj (cosimplicialSmoothSite k)
      (SmoothSite.largeBoundaryOnePresheaf k)).d (n + 1) n ≫ singularDivisorToSheaf k n =
    singularDivisorToSheaf k (n + 1) ≫
      sheafifyMap (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((rawReducedSingular k).d (n + 1) n) := by
  apply (Functor.IsCoverDense.restrictHomEquivHom
    (G := SmoothSite.integralAffineInclusion k)
    (ℱ' := (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj ((rawReducedSingular k).X n))).symm.injective
  apply NatTrans.ext
  funext X
  let : IsAffine X.unop.obj.left := X.unop.property.1
  let : IsIntegral X.unop.obj.left := X.unop.property.2
  change ((SingularComplex.presheafObj (cosimplicialSmoothSite k)
    (SmoothSite.largeBoundaryOnePresheaf k)).d (n + 1) n).app (op X.unop.obj) ≫
      (singularDivisorToSheaf k n).app (op X.unop.obj) =
    (singularDivisorToSheaf k (n + 1)).app (op X.unop.obj) ≫
      (sheafifyMap (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((rawReducedSingular k).d (n + 1) n)).app (op X.unop.obj)
  rw [singularDivisorToSheaf_app, singularDivisorToSheaf_app,
    ← Category.assoc, largeAffineReducedDivisor_d, Category.assoc, Category.assoc]
  congr 1
  exact (congrArg (fun η => η.app (op X.unop.obj))
    (toSheafify_naturality (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((rawReducedSingular k).d (n + 1) n)))

/-- The sheafified divisor commutes with the original differential. -/
theorem singularSheafDivisor_d (j : ℕ) :
    (SmoothSite.boundaryOneSheafComplex k).d (j + 1) j ≫ singularSheafDivisor k j =
      singularSheafDivisor k (j + 1) ≫
        (SingularComplex.sheafObj (SmoothSite.nisnevichTopology (Spec (.of k)))
          (cosimplicialSmoothSite k) (rawReducedTorus k)).d (j + 1) j := by
  apply Sheaf.hom_ext
  change sheafifyMap _ _ ≫ sheafifyLift _ _ _ =
    sheafifyLift _ _ _ ≫ sheafifyMap _ _
  rw [sheafifyMap_sheafifyLift, ← sheafifyLift_comp]
  · congr 1
    exact singularDivisorToSheaf_d k j
  · exact ((presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj ((rawReducedSingular k).X j)).property

/-- The actual divisor is a chain map into the original sheafified reduced-torus complex. -/
def sheafDivisorChainMap : SmoothSite.boundaryOneSheafComplex k ⟶
    SingularComplex.sheafObj (SmoothSite.nisnevichTopology (Spec (.of k)))
      (cosimplicialSmoothSite k) (rawReducedTorus k) where
  f := singularSheafDivisor k
  comm' i j hij := by
    have h : j + 1 = i := hij
    subst i
    exact (singularSheafDivisor_d k j).symm

end Motivic.SmoothSiteBoundaryOneDivisor
