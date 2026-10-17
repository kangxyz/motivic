module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.FixedPsiNormalizedSectionPair
/-! The unchanged punctured source retains the literal prescribed ratio. -/
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry RelativeProjectiveLine
open Scheme.Modules Scheme.Modules.Invertible
universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
  (r : R) (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
example (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
    (e : (n : ℕ) → (Scheme.Modules.pullback ((fullBoundaryPrincipalOpen R V r).ι ≫
        fullNeighborhoodBoundaryMap R V)).obj
      (ProjectiveSpace.twistingSheaf R (ULift.{u} (Fin 2)) (n : ℤ)) ≅
        SheafOfModules.unit (fullBoundaryPrincipalOpen R V r).toScheme.ringCatSheaf) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      ∃ n t : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶
        (fixedPsiTwistLine R r d).val,
        pullbackSectionMap (fixedPsiBoundaryMap R r V) n =
          (fixedPsiBoundaryUnit R V r).hom ≫ pullbackSectionMap (fixedPsiBoundaryMap R r V) t ∧
        FixedPsiLineSectionFiniteFlat R r V (fixedPsiTwistLine R r d) n ∧
        FixedPsiLineSectionFiniteFlat R r V (fixedPsiTwistLine R r d) t := by
  obtain ⟨N, hN⟩ := exists_fixedPsiNormalizedSectionPair R r V hV e
  exact ⟨N, fun d hd => by
    obtain ⟨n, t, h, _, _, hn, ht⟩ := hN d hd
    exact ⟨n, t, h, hn, ht⟩⟩
#print axioms exists_fixedPsiNormalizedSectionPair
