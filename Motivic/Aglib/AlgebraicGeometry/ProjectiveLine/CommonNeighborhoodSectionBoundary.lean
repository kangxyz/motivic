module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.CommonNeighborhoodSectionMaps
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.CommonNeighborhoodCoordinate
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.NeighborhoodLocalBoundaryCoordinate
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.FixedPsiNormalizedSectionPair
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.PrescribedPairPullback
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.MixedPrescribedPencilBoundary
/-! # The actual relative section pairs agree on the whole common boundary -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
  (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
  (r : R) (l m : ℕ) (e : neighborhoodFrame R V r l)

theorem NeighborhoodSectionPair.common_boundary_tensor
    (d : NeighborhoodSectionPair R V hV r l e)
    (n t : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶
      (fixedPsiTwistLine R r m).val)
    (hn : pullbackSectionMap (fixedPsiBoundaryMap R r V) n =
      (fixedPsiBoundaryUnit R V r).hom ≫ pullbackSectionMap (fixedPsiBoundaryMap R r V) t) :
    let f := commonNeighborhoodBoundaryToSection R V r hV ≫
      (neighborhoodGraphBoundaryMap R V hV ∣_ neighborhoodSectionOpen R V r)
    let g := commonNeighborhoodBoundaryToPsi R V r ≫ fixedPsiBoundaryMap R r V
    tensorSectionMap _ (pullbackSectionMap f d.normalizedNumerator)
      (pullbackSectionMap g n) =
    tensorSectionMap _ (pullbackSectionMap f (twistedIdealSection _
      (neighborhoodLocalIdeal R V r) (neighborhoodLocalTwist R V r l)
      (neighborhoodLocalGraphFunctional R V r) d.normalizedDenominator))
      (pullbackSectionMap g t) := by
  let vA := commonNeighborhoodBoundaryToSection R V r hV
  let zA := neighborhoodGraphBoundaryMap R V hV ∣_ neighborhoodSectionOpen R V r
  let vN := commonNeighborhoodBoundaryToPsi R V r
  let zN := fixedPsiBoundaryMap R r V
  let E := neighborhoodLocalBoundaryFrame R V hV r
  let I := neighborhoodLocalIdeal R V r
  let T := neighborhoodLocalTwist R V r l
  let φ := neighborhoodLocalGraphFunctional R V r
  have hn' := scalar_pair_pullback vN zN n t (fixedPsiBoundaryUnit R V r).hom hn
  have hδ := compositeBoundaryFrame_coordinate vA zA (dualLineBundle _ I).val E
    (canonicalDualHom _ I.val φ)
  have hc : Scheme.Hom.unitEndomorphismPullback vA
      (pullbackSectionMap zA (canonicalDualHom _ I.val φ) ≫ E.hom) =
      Scheme.Hom.unitEndomorphismPullback vN (fixedPsiBoundaryUnit R V r).hom := by
    rw [neighborhoodLocalBoundaryFrame_coordinate,
      Scheme.Hom.unitEndomorphismPullback_comp]
    change Scheme.Hom.unitEndomorphismPullback
      (commonNeighborhoodBoundaryToSection R V r hV ≫ _) _ = _
    rw [commonNeighborhoodBoundaryToSection_ι]
    exact commonNeighborhoodBoundary_coordinate_eq R V r hV
  rw [← hc, ← hδ] at hn'
  exact mixed_prescribed_boundary_tensor (vA ≫ zA) (vN ≫ zN) I T
    (fixedPsiTwistLine R r m) φ d.normalizedDenominator t n d.normalizedNumerator
    (compositeBoundaryFrame vA zA (dualLineBundle _ I).val E)
    (prescribed_pair_pullback vA zA T.val (dualLineBundle _ I).val E
      d.normalizedNumerator d.normalizedDenominator d.normalized_boundary_tensor) hn'
end AlgebraicGeometry.RelativeProjectiveLine
