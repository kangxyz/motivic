/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.AlgebraicGeometry.Correspondences.RelativePolynomialSpanIdentities
public import Motivic.AlgebraicGeometry.Correspondences.PolynomialOpenPencilEndpoints
/-! # Relative-target polynomial homotopies remain original k-correspondences -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient Motivic.RelativeEndpointDiagram
universe u
namespace Motivic.RelativePolynomialOpenSpans
variable {k R A : Type u} [Field k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra.Smooth k R] [Algebra R A] [Algebra k A]
    [IsScalarTower k R A] [Algebra.Smooth k A]

local instance polynomial_smooth : Algebra.Smooth k A[X] := by
  let : Algebra.Smooth A A[X] := ⟨inferInstance, inferInstance⟩
  exact Algebra.Smooth.comp k A A[X]

abbrev parameterCoefficients : R →+* A[X] := C.comp (algebraMap R A)

/-- The family retains both relative coefficients and its original k-structure. -/
theorem family_affine_base (p : A[X][X]) :
    familySource (algebraMap k A) p ≫
      (SmoothSite.a1Cylinder (.of k) (sourceSite (k := k) (A := A))).hom =
      target (parameterCoefficients (R := R) (A := A)) p ≫
        (lineSite (k := k) (R := R)).hom := by
  rw [familySource, Category.assoc]
  change source p ≫ ((ambientIso (algebraMap k A)).hom ≫
    relativeLineHom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) = _
  rw [ambientIso_base]
  exact affine_base (k := k) (R := R) (A := A[X]) p

/-- The original relative open is the actual target of the family. -/
theorem family_open_base (p : A[X][X]) (f : R[X])
    (hf : IsUnit (AdjoinRoot.mk p (f.map (parameterCoefficients (R := R) (A := A))))) :
    familySource (algebraMap k A) p ≫
      (SmoothSite.a1Cylinder (.of k) (sourceSite (k := k) (A := A))).hom =
      openTarget (parameterCoefficients (R := R) (A := A)) p f hf ≫
        (openSite (k := k) f).hom := by
  change _ = openTarget _ p f hf ≫ ((principalOpen f).ι ≫
    (lineSite (k := k) (R := R)).hom)
  rw [← Category.assoc, openTarget_inclusion]
  exact family_affine_base (k := k) (R := R) p

/-- A whole monic quotient defines the actual relative-target cylinder correspondence. -/
def familyCycle (p : A[X][X]) (hp : p.Monic) (f : R[X])
    (hf : IsUnit (AdjoinRoot.mk p (f.map (parameterCoefficients (R := R) (A := A))))) :
    Cor.mk (SmoothSite.a1Cylinder (.of k) (sourceSite (k := k) (A := A))) ⟶
      Cor.mk (openSite (k := k) f) := by
  let : IsFinite (familySource (algebraMap k A) p) := family_finite _ _ hp
  let : Flat (familySource (algebraMap k A) p) := family_flat _ _ hp
  exact Cor.ofFiniteFlatSpan (familySource (algebraMap k A) p)
    (openTarget (parameterCoefficients (R := R) (A := A)) p f hf)
    (family_open_base (k := k) p f hf)

/-- The unchanged family source and relative target are jointly closed over k. -/
theorem family_joint_closed (p : A[X][X]) : IsClosedImmersion
    (pullback.lift (familySource (algebraMap k A) p)
      (target (parameterCoefficients (R := R) (A := A)) p) (family_affine_base (k := k) p)) := by
  let σ := algebraMap k A
  let b := Spec.map (CommRingCat.ofHom σ)
  let c := (sourceSite (k := k) (A := A[X])).hom
  let t := (lineSite (k := k) (R := R)).hom
  have he : (ambientIso σ).inv ≫ c = relativeLineHom b := by
    rw [show c = (ambientIso σ).hom ≫ relativeLineHom b from (ambientIso_base σ).symm]
    simp
  let m := pullback.map (relativeLineHom b) t c t (ambientIso σ).inv (𝟙 _) (𝟙 _)
    (by simpa using he.symm) (by simp)
  have : IsIso m := by dsimp [m]; infer_instance
  have hm : pullback.lift (familySource σ p)
      (target (parameterCoefficients (R := R) (A := A)) p) (family_affine_base (k := k) p) ≫ m =
      pullback.lift (source p) (target (algebraMap R A[X]) p) (affine_base (k := k) p) := by
    apply pullback.hom_ext
    · dsimp only [m, b, c, t, pullback.map]
      erw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst]
      simp [familySource]
    · dsimp only [m, b, c, t, pullback.map]
      erw [Category.assoc, pullback.lift_snd, Category.comp_id,
        pullback.lift_snd, pullback.lift_snd]
      rfl
  have : IsClosedImmersion (pullback.lift (familySource σ p)
      (target (parameterCoefficients (R := R) (A := A)) p)
        (family_affine_base (k := k) p) ≫ m) := by
    rw [hm]
    exact joint_closed p
  exact IsClosedImmersion.of_comp _ m

end Motivic.RelativePolynomialOpenSpans
