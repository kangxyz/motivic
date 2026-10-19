module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Dual.Restriction
import Lean.Util.CollectAxioms
/-! # Direct audit of restriction preserving actual dual evaluation -/
public section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace MotivicTest.RestrictDual

/-- Direct use on the original restricted ideal and original canonical section. -/
theorem original_canonical_section {X : Scheme.{u}} (U : X.Opens)
    (I : LineBundle X) (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (restrictUnitIso U.ι).inv ≫ (Scheme.Modules.restrictFunctor U.ι).map
        (canonicalDualHom X I.val φ) ≫ (restrictDualIso U.ι I).hom =
      canonicalDualHom U.toScheme (restrictLineBundle U.ι I).val
        ((Scheme.Modules.restrictFunctor U.ι).map φ ≫ (restrictUnitIso U.ι).hom) :=
  restrictDualIso_canonicalDualHom U I φ

end MotivicTest.RestrictDual
open Lean in
run_cmd do
  let targets := #[
    `MotivicTest.RestrictDual.original_canonical_section,
    `AlgebraicGeometry.Scheme.Modules.Invertible.restrictDualIso_evaluation,
    `AlgebraicGeometry.Scheme.Modules.Invertible.perfectPairingDualIso_pairing]
  for name in targets do
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual restricted evaluation and canonical divisor section: standard axioms only."
