/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.ProjectiveSpace.CoordinateRing
public import Aglib.AlgebraicGeometry.ProjectiveSpace.PrincipalOpen
public import Mathlib.Algebra.MvPolynomial.Equiv
/-! # Literal affine charts of the relative projective line -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory TopologicalSpace
namespace AlgebraicGeometry.RelativeProjectiveLine
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable (R : Type u) [CommRing R]
/-- The complementary homogeneous coordinate is unique. -/
local instance otherUnique (i : ULift.{u} (Fin 2)) :
    Unique {j : ULift.{u} (Fin 2) // j ≠ i} where
  default := ⟨⟨1 - i.down⟩, by rcases i with ⟨i⟩; fin_cases i <;> decide⟩
  uniq j := by
    rcases i with ⟨i⟩
    rcases j with ⟨⟨j⟩, hj⟩
    fin_cases i <;> fin_cases j <;>
      simp_all only [Fin.zero_eta, Fin.mk_one, Fin.isValue, ne_eq, sub_zero, sub_self,
        Subtype.mk.injEq, ULift.up.injEq, zero_ne_one, one_ne_zero] <;> exact (hj rfl).elim

/-- The actual homogeneous coordinate ring, identified with the one-variable polynomial ring. -/
def chartRingEquiv (i : ULift.{u} (Fin 2)) :
    ProjectiveSpace.coordinateRing R (ULift.{u} (Fin 2)) i ≃+* Polynomial R :=
  (ProjectiveSpace.coordinateRingEquivPolynomial R (ULift.{u} (Fin 2)) i).trans
    (MvPolynomial.uniqueAlgEquiv R {j : ULift.{u} (Fin 2) // j ≠ i}).toRingEquiv

/-- The affine line included in the actual projective line at coordinate `i`. -/
def chart (i : ULift.{u} (Fin 2)) :
    Spec (.of (Polynomial R)) ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)) :=
  Spec.map (chartRingEquiv R i).toCommRingCatIso.hom ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) R) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one

instance chart_isOpenImmersion (i : ULift.{u} (Fin 2)) : IsOpenImmersion (chart R i) := by
  have : IsIso (Spec.map (chartRingEquiv R i).toCommRingCatIso.hom) := inferInstance
  unfold chart
  infer_instance

@[reassoc]
theorem chart_toSpec (i : ULift.{u} (Fin 2)) :
    chart R i ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)) =
    Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) := by
  rw [chart, Category.assoc, ProjectiveSpace.coordinateChart_toSpec, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change chartRingEquiv R i
    (ProjectiveSpace.coordinateRingCoefficient R (ULift.{u} (Fin 2)) i a) = _
  simp [chartRingEquiv, ProjectiveSpace.coordinateRingEquivPolynomial,
    ProjectiveSpace.coordinateRingToPolynomial_coefficient]

/-- The chart image is exactly the native homogeneous coordinate open. -/
theorem chart_opensRange (i : ULift.{u} (Fin 2)) :
    (chart R i).opensRange = ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) i := by
  have : IsIso (Spec.map (chartRingEquiv R i).toCommRingCatIso.hom) := inferInstance
  unfold chart
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]
  rfl

/-- These actual affine-line charts cover the projective line. -/
theorem iSup_chart_opensRange : (⨆ i, (chart R i).opensRange) = ⊤ := by
  simp only [chart_opensRange]
  exact ProjectiveSpace.iSup_coordinateOpen_eq_top R (ULift.{u} (Fin 2))

end AlgebraicGeometry.RelativeProjectiveLine
