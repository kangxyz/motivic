import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Sections.OpenRestrictionPullback
import Lean.Util.CollectAxioms

/-! # Direct consumer of the original prescribed boundary value on an open -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible Scheme.Modules.Pullback.OpenRestriction
open Scheme.CoherentGraph
universe u
namespace MotivicTest.OpenBoundaryPullback

theorem actual_open_boundary_unit {Z C : Scheme.{u}}
    (z : Z ⟶ C) [IsClosedImmersion z] (L M : C.Modules) (U : C.Opens)
    (s : Γ((moduleTensorLeftFunctor C L).obj M, U))
    (σ : Γ((moduleTensorLeftFunctor Z ((Scheme.Modules.pullback z).obj L)).obj
      ((Scheme.Modules.pullback z).obj M), z ⁻¹ᵁ U))
    (h : (boundaryRestriction z L M).app U s = σ)
    [IsIso (openSectionHom Z (z ⁻¹ᵁ U)
      ((moduleTensorLeftFunctor Z ((Scheme.Modules.pullback z).obj L)).obj
        ((Scheme.Modules.pullback z).obj M)) σ)] :
    IsIso (pullbackSectionMap (z ∣_ U)
      (openSectionHom C U ((moduleTensorLeftFunctor C L).obj M) s)) :=
  isIso_pullback_openSection_of_boundary_value z L M U s σ h

/-- The original transported unit needs no equality of boundary opens by definition. -/
theorem actual_transported_unit {X : Scheme.{u}} (U V : X.Opens) (h : U = V)
    (Q : X.Modules) (e : Q.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf) :
    IsIso (openSectionHom X U Q ((Q.presheaf.mapIso (eqToIso h).op).hom
      ((openUnitSectionsIso V Q e).inv (1 : Γ(V.toScheme, ⊤))))) :=
  isIso_openSectionHom_unit_boundary_of_eq U V h Q e

end MotivicTest.OpenBoundaryPullback

open Lean in
run_cmd do
  let targets := #[
    `MotivicTest.OpenBoundaryPullback.actual_open_boundary_unit,
    `MotivicTest.OpenBoundaryPullback.actual_transported_unit,
    `AlgebraicGeometry.Scheme.CoherentGraph.isIso_pullback_openSection_of_boundary_value,
    `AlgebraicGeometry.Scheme.CoherentGraph.pullback_openSection_of_boundary_value,
    `AlgebraicGeometry.Scheme.CoherentGraph.pullback_openSection_of_unit_boundary]
  for name in targets do
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original open boundary pullback and prescribed unit: standard axioms only."
