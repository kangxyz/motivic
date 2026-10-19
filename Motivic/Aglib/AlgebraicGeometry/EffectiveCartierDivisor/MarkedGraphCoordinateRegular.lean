/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.CoordinateGraphIdeal
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.FiniteSchemeNormBaseChange
public import Motivic.Aglib.RingTheory.TensorProduct.RegularGraphBoundary
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# The original marked graph coordinate under a flat parameter map

The original parameter map is base changed to the full marked affine scheme.
The canonical polynomial product comparison identifies its coordinate map;
flatness of this actual map makes the same monic graph equation regular.
No reducedness of the marked coefficient ring is used.


Intended upstream module:
`Aglib.AlgebraicGeometry.EffectiveCartierDivisor.MarkedGraphCoordinateRegular`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u
namespace AlgebraicGeometry.Scheme.Hom

variable (A Q : Type u) [CommRing A] [CommRing Q] [Algebra A Q]
  {P : Scheme.{u}} (p : P ⟶ Spec (.of (Polynomial A)))

/-- The actual parameter-times-marked scheme maps to the polynomial coordinate
scheme by the canonical pullback pasting and polynomial product isomorphisms. -/
def parameterMarkedCoordinateMap :
    pullback (p ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)))
      (Spec.map (CommRingCat.ofHom (algebraMap A Q))) ⟶ Spec (.of (Polynomial Q)) :=
  (pullbackRightPullbackFstIso
    (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)))
    (Spec.map (CommRingCat.ofHom (algebraMap A Q))) p).inv ≫
    pullback.snd p _ ≫ (coordinateProductIso A (algebraMap A Q)).inv

/-- The polynomial coordinate map retains the original parameter projection. -/
@[reassoc (attr := simp)]
theorem parameterMarkedCoordinateMap_parameter :
    parameterMarkedCoordinateMap A Q p ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A Q))) =
      pullback.fst _ _ ≫ p := by
  rw [← coordinateProductIso_hom_fst A (algebraMap A Q)]
  simp only [parameterMarkedCoordinateMap, Category.assoc, Iso.inv_hom_id_assoc,
    pullbackRightPullbackFstIso_inv_snd_fst]

/-- The polynomial coordinate map retains the entire marked coefficient scheme. -/
@[reassoc (attr := simp)]
theorem parameterMarkedCoordinateMap_marked :
    parameterMarkedCoordinateMap A Q p ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : Q →+* Polynomial Q)) =
      pullback.snd _ _ := by
  rw [← coordinateProductIso_hom_snd A (algebraMap A Q)]
  simp only [parameterMarkedCoordinateMap, Category.assoc, Iso.inv_hom_id_assoc,
    pullbackRightPullbackFstIso_inv_snd_snd]

instance parameterMarkedCoordinateMap_flat [Flat p] :
    Flat (parameterMarkedCoordinateMap A Q p) := by
  unfold parameterMarkedCoordinateMap
  infer_instance

/-- Flatness of the exact scalar action follows from the original parameter
map, not from an additional algebra-flatness premise. -/
theorem parameterMarkedCoordinateMap_scalarMap_flat [IsAffine P] [Flat p] :
    (FiniteSchemeNormBaseChange.scalarMap (parameterMarkedCoordinateMap A Q p)).Flat := by
  apply RingHom.Flat.comp
  · exact RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (ΓSpecIso (.of (Polynomial Q))).inv)
  · exact (parameterMarkedCoordinateMap A Q p).flat_appTop

/-- The same marked graph equation is regular on the actual full marked
base change of the original flat parameter scheme. -/
theorem parameterMarkedCoordinateMap_graph_regular [IsAffine P] [Flat p] (z : Q) :
    IsSMulRegular
      Γ(pullback
        (p ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)))
        (Spec.map (CommRingCat.ofHom (algebraMap A Q))), ⊤)
      (FiniteSchemeNormBaseChange.scalarMap (parameterMarkedCoordinateMap A Q p)
        (Polynomial.X - Polynomial.C z)) := by
  let ρ := FiniteSchemeNormBaseChange.scalarMap (parameterMarkedCoordinateMap A Q p)
  let : Algebra (Polynomial Q) _ := ρ.toAlgebra
  let : Module.Flat (Polynomial Q)
      Γ(pullback
        (p ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)))
        (Spec.map (CommRingCat.ofHom (algebraMap A Q))), ⊤) :=
    parameterMarkedCoordinateMap_scalarMap_flat A Q p
  exact (Polynomial.monic_X_sub_C z).isRegular.left.isSMulRegular.of_flat

end AlgebraicGeometry.Scheme.Hom
