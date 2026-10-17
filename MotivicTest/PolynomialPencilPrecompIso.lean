module
public import Motivic.Aglib.AlgebraicGeometry.PolynomialPencilPrecompIso
/-! # Whole finite-flat parameter families survive the original coefficient isomorphism -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible PolynomialBoundaryPencil
universe u
example {R : Type u} [CommRing R] {S D : Scheme.{u}}
    (b : S ⟶ Spec (.of R)) (p : D ⟶ S)
    (L M : LineBundle D) (e : L.val ≅ M.val)
    (a c : M.val ⟶ SheafOfModules.unit D.ringCatSheaf)
    [IsFinite (Hom.zeroInclusion (familyMap (p ≫ b) M a c) ≫ parameterMap b p)]
    [Flat (Hom.zeroInclusion (familyMap (p ≫ b) M a c) ≫ parameterMap b p)] :
    IsFinite (Hom.zeroInclusion (familyMap (p ≫ b) L (e.hom ≫ a) (e.hom ≫ c)) ≫
      parameterMap b p) ∧
    Flat (Hom.zeroInclusion (familyMap (p ≫ b) L (e.hom ≫ a) (e.hom ≫ c)) ≫
      parameterMap b p) :=
  ⟨familyZeroPrecomp_isFinite (p ≫ b) L M e a c (parameterMap b p),
    familyZeroPrecomp_flat (p ≫ b) L M e a c (parameterMap b p)⟩

open Lean in
run_cmd do
  for name in #[``familyMap_precompIso, ``familyZeroPrecompIso,
      ``familyZeroPrecompIso_hom_inclusion, ``familyZeroPrecomp_isFinite,
      ``familyZeroPrecomp_flat] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original whole polynomial pencil isomorphism uses only standard foundations."
