module
import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.DisjointBoundary

/-! # Direct tests for the constructed scheme-theoretic boundary -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCompactification
universe u

section
variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  {Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] [QuasiCompact f] [IsSeparated f]
  {Z : Scheme.{u}} (s : Z ⟶ Y) [IsClosedImmersion s]
  {S : Scheme.{u}} (p : X ⟶ S) [IsSeparated p] [IsFinite (s ≫ f ≫ p)]

-- The finite scheme Z itself, including nilpotents, occurs as the right summand.
example : IsClosedImmersion (boundaryInclusion X f s) :=
  boundaryInclusion_isClosedImmersion X f s p

example (M : ((genericMap X f).normalization).Modules) :
    ((Scheme.Modules.pullback (boundaryInclusion X f s)).obj M).restrict
      (coprod.inr : Z ⟶ infinity X f ⨿ Z) ≅
    (Scheme.Modules.pullback (s ≫ inclusion X f)).obj M :=
  (Scheme.Modules.coprodPullbackRestrictRight (infinityInclusion X f)
    (s ≫ inclusion X f)).app M

example : coprod.inr ≫ boundaryInclusion X f s ≫ (genericMap X f).fromNormalization = s ≫ f := by
  simp
end
