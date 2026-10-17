module

public import Motivic.Aglib.AlgebraicGeometry.EtaleOriginalFiberCoproduct

/-! # Original residue fields and original points in the actual étale fiber -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace MotivicTest.EtaleOriginalFiberCoproduct

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (y : Y)

/-- No fiber-point residue field replaces the original residue field. -/
def actual_decomposition :
    (∐ fun x : f ⁻¹' {y} ↦ Spec (X.residueField x.1)) ≅ f.fiber y :=
  f.originalFiberCoproductIso y

/-- The inclusion into the original scheme remains the canonical residue-field map. -/
theorem actual_original_inclusion (x : f ⁻¹' {y}) :
    Sigma.ι (fun x : f ⁻¹' {y} ↦ Spec (X.residueField x.1)) x ≫
      (f.originalFiberCoproductIso y).hom ≫ f.fiberι y = X.fromSpecResidueField x.1 := by
  simp

/-- The structural morphism remains the native residue-field map, with equality transport. -/
theorem actual_structural_map (x : f ⁻¹' {y}) :
    Sigma.ι (fun x : f ⁻¹' {y} ↦ Spec (X.residueField x.1)) x ≫
      (f.originalFiberCoproductIso y).hom ≫ f.fiberToSpecResidueField y =
        f.originalFiberFieldMap y x := by
  simp

open Lean in
run_cmd do
  for name in #[``actual_decomposition, ``actual_original_inclusion, ``actual_structural_map,
      ``Scheme.Hom.originalFiberCofanIsColimit, ``Scheme.Hom.originalFiberComponent_apply] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original étale fiber decomposition: standard foundations only."

end MotivicTest.EtaleOriginalFiberCoproduct
