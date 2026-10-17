module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.CommonNeighborhoodPencil
/-! The actual prescribed pairs give literal equal, invertible full-boundary pencil values. -/
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry RelativeProjectiveLine
open Scheme.Modules Scheme.Modules.Invertible
universe u
variable (R : Type u) [CommRing R]
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
  (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
  (r : R) (l m : ℕ) (e : neighborhoodFrame R V r l)
  (d : NeighborhoodSectionPair R V hV r l e)
  (n t : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶
    (fixedPsiTwistLine R r m).val)
  (hn : pullbackSectionMap (fixedPsiBoundaryMap R r V) n =
    (fixedPsiBoundaryUnit R V r).hom ≫ pullbackSectionMap (fixedPsiBoundaryMap R r V) t)
example : Scheme.Modules.Hom.pullbackToUnit (d.pencilStart R V hV r l m e t)
    (commonNeighborhoodBoundaryMap R V r) =
    Scheme.Modules.Hom.pullbackToUnit (d.pencilEnd R V hV r l m e n)
      (commonNeighborhoodBoundaryMap R V r) :=
  d.pencil_boundary R V hV r l m e n t hn
example [IsIso (pullbackSectionMap (fixedPsiBoundaryMap R r V) n)] :
    IsIso ((Scheme.Modules.pullback (commonNeighborhoodBoundaryMap R V r)).map
      (d.pencilStart R V hV r l m e t)) :=
  d.pencilStart_boundary_isIso R V hV r l m e n t hn
#print axioms NeighborhoodSectionPair.common_boundary_tensor
#print axioms NeighborhoodSectionPair.pencil_boundary
#print axioms NeighborhoodSectionPair.pencilStart_boundary_isIso
