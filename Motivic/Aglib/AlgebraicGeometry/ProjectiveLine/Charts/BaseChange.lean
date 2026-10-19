module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Charts.Basic
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange
/-! # Literal relative projective charts under coefficient base change -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
attribute [local instance] otherUnique MvPolynomial.gradedAlgebra
variable {R A : Type u} [CommRing R] [CommRing A]

lemma chartRingEquiv_map (ρ : R →+* A) (i : ULift.{u} (Fin 2)) :
    (chartRingEquiv A i).toRingHom.comp (ProjectiveSpace.coordinateRingMap ρ _ i) =
      (Polynomial.mapRingHom ρ).comp (chartRingEquiv R i).toRingHom := by
  have hu : (MvPolynomial.uniqueAlgEquiv A {j // j ≠ i}).toRingHom.comp
        (MvPolynomial.map ρ) =
      (Polynomial.mapRingHom ρ).comp
        (MvPolynomial.uniqueAlgEquiv R {j // j ≠ i}).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [MvPolynomial.uniqueAlgEquiv]
    · intro j
      simp [MvPolynomial.uniqueAlgEquiv]
  apply RingHom.ext
  intro x
  change (MvPolynomial.uniqueAlgEquiv A {j // j ≠ i})
      ((ProjectiveSpace.coordinateRingEquivPolynomial A _ i)
        (ProjectiveSpace.coordinateRingMap ρ _ i x)) = _
  rw [show (ProjectiveSpace.coordinateRingEquivPolynomial A _ i)
      (ProjectiveSpace.coordinateRingMap ρ _ i x) =
      MvPolynomial.map ρ ((ProjectiveSpace.coordinateRingEquivPolynomial R _ i) x) from
    RingHom.congr_fun (ProjectiveSpace.coordinateRingEquivPolynomial_map ρ _ i) x]
  exact RingHom.congr_fun hu _

@[reassoc]
lemma chart_map (ρ : R →+* A) (i : ULift.{u} (Fin 2)) :
    chart A i ≫ ProjectiveSpace.map ρ (ULift.{u} (Fin 2)) =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom ρ)) ≫ chart R i := by
  rw [chart, Category.assoc, ProjectiveSpace.coordinateRingMap_awayι,
    ← Category.assoc, ← Spec.map_comp]
  rw [chart, ← Category.assoc, ← Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  exact chartRingEquiv_map ρ i
end AlgebraicGeometry.RelativeProjectiveLine
