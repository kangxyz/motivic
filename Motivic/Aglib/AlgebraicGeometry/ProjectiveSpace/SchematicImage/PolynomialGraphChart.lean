/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Charts.GraphChartEquations
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Compactification.OriginalCompactification
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Actual polynomial charts of a graph ambient fiber product -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry _root_.MvPolynomial
universe u
namespace AlgebraicGeometry.Scheme
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A] (n : ℕ)

/-- The native polynomial square is Cartesian, including its entire ring structure. -/
theorem polynomialBaseChange_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin n) (algebraMap k A))))
      (Spec.map (CommRingCat.ofHom (C : A →+* MvPolynomial (Fin n) A)))
      (Spec.map (CommRingCat.ofHom (C : k →+* MvPolynomial (Fin n) k)))
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
  apply isPullback_SpecMap_of_isPushout
  exact CommRingCat.isPushout_iff_isPushout.mpr
    (inferInstance : Algebra.IsPushout k (MvPolynomial (Fin n) k) A
      (MvPolynomial (Fin n) A))

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (j : Spec (.of A) ⟶ X)
  (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k A)))

/-- The actual affine chart in the original product with affine space. -/
def polynomialChart : Spec (.of (MvPolynomial (Fin n) A)) ⟶
    pullback f (Spec.map (CommRingCat.ofHom (C : k →+* MvPolynomial (Fin n) k))) :=
  pullback.lift (Spec.map (CommRingCat.ofHom C) ≫ j)
    (Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap k A)))) (by
      rw [Category.assoc, hj]
      exact (polynomialBaseChange_isPullback k A n).w.symm)

@[reassoc (attr := simp)]
theorem polynomialChart_fst :
    polynomialChart k A n f j hj ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom C) ≫ j := pullback.lift_fst ..

@[reassoc (attr := simp)]
theorem polynomialChart_snd :
    polynomialChart k A n f j hj ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap k A))) :=
  pullback.lift_snd ..

/-- The chart is precisely the base change of the original source chart. -/
theorem polynomialChart_isPullback :
    IsPullback (polynomialChart k A n f j hj)
      (Spec.map (CommRingCat.ofHom (C : A →+* MvPolynomial (Fin n) A)))
      (pullback.fst _ _) j := by
  apply IsPullback.of_right _ (polynomialChart_fst k A n f j hj)
    (IsPullback.of_hasPullback f
      (Spec.map (CommRingCat.ofHom (C : k →+* MvPolynomial (Fin n) k)))).flip
  rw [polynomialChart_snd, hj]
  exact polynomialBaseChange_isPullback k A n

instance [IsOpenImmersion j] : IsOpenImmersion (polynomialChart k A n f j hj) :=
  MorphismProperty.of_isPullback (polynomialChart_isPullback k A n f j hj).flip inferInstance

end AlgebraicGeometry.Scheme
