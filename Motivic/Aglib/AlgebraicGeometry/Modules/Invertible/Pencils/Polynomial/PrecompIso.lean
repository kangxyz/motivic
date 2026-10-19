module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Pencils.Polynomial.FiniteFlat
/-! # Whole polynomial pencils under the original line-bundle isomorphism -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible GlobalBoundaryPencil
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible.PolynomialBoundaryPencil
variable {R : Type u} [CommRing R] {X : Scheme.{u}} (b : X ⟶ Spec (.of R))
  (L M : LineBundle X) (e : L.val ≅ M.val)
  (a c : M.val ⟶ SheafOfModules.unit X.ringCatSheaf)

/-- Precomposition changes only the original coefficient domain, not the family. -/
theorem familyMap_precompIso :
    familyMap b L (e.hom ≫ a) (e.hom ≫ c) =
      (Scheme.Modules.pullback (projection b)).map e.hom ≫ familyMap b M a c := by
  simp [familyMap, pencil, Hom.pullbackToUnit, Functor.map_comp,
    Category.assoc, Preadditive.comp_add, Preadditive.comp_sub]

/-- The entire zero scheme is preserved, with all its scheme structure. -/
def familyZeroPrecompIso :
    Hom.zeroScheme (familyMap b L (e.hom ≫ a) (e.hom ≫ c)) ≅
      Hom.zeroScheme (familyMap b M a c) :=
  eqToIso (congrArg Hom.zeroScheme (familyMap_precompIso b L M e a c)) ≪≫
    zeroSchemePrecompIso ((Scheme.Modules.pullback (projection b)).mapIso e)
      (familyMap b M a c)

@[reassoc (attr := simp)]
theorem familyZeroPrecompIso_hom_inclusion :
    (familyZeroPrecompIso b L M e a c).hom ≫ Hom.zeroInclusion (familyMap b M a c) =
      Hom.zeroInclusion (familyMap b L (e.hom ≫ a) (e.hom ≫ c)) := by
  simp only [familyZeroPrecompIso, Iso.trans_hom, Category.assoc,
    zeroSchemePrecompIso_hom_inclusion, Functor.mapIso_hom, eqToIso.hom]
  exact zeroScheme_congr_inclusion (familyMap_precompIso b L M e a c)

/-- Finiteness of the actual whole family is unchanged by its coefficient isomorphism. -/
theorem familyZeroPrecomp_isFinite {T : Scheme.{u}} (q : parameterSpace b ⟶ T)
    [IsFinite (Hom.zeroInclusion (familyMap b M a c) ≫ q)] :
    IsFinite (Hom.zeroInclusion (familyMap b L (e.hom ≫ a) (e.hom ≫ c)) ≫ q) := by
  rw [← familyZeroPrecompIso_hom_inclusion b L M e a c, Category.assoc]
  infer_instance

/-- Flatness likewise transports through the literal whole-zero-scheme isomorphism. -/
theorem familyZeroPrecomp_flat {T : Scheme.{u}} (q : parameterSpace b ⟶ T)
    [Flat (Hom.zeroInclusion (familyMap b M a c) ≫ q)] :
    Flat (Hom.zeroInclusion (familyMap b L (e.hom ≫ a) (e.hom ≫ c)) ≫ q) := by
  rw [← familyZeroPrecompIso_hom_inclusion b L M e a c, Category.assoc]
  infer_instance

end AlgebraicGeometry.Scheme.Modules.Invertible.PolynomialBoundaryPencil
