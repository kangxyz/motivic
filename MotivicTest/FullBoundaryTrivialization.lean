module
import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.FullBoundaryProduct
import Motivic.Aglib.AlgebraicGeometry.Normalization.EtaleDisjointBoundary

/-! # Canonical infinity trivialization on the constructed compactification -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.EtaleCompactification Scheme.Hom
universe u

example (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    {Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] [QuasiCompact f] [IsSeparated f]
    {S : Scheme.{u}} (p : X ⟶ S) [IsSeparated p] :
    IsIso (Scheme.Modules.Hom.pullbackToUnit
      (idealInclusion (compactificationGraph ((genericMap X f).fromNormalization ≫ p)
        (inclusion X f)))
      (infinityProductMap ((genericMap X f).fromNormalization ≫ p)
        (inclusion X f) (infinityInclusion X f))) := by
  apply infinity_pullbackIdealInclusion_isIso
  rw [range_infinityInclusion]
  exact disjoint_compl_right


example {S C Y D Z : Scheme.{u}} (q : C ⟶ S) (j : Y ⟶ C)
    (d : D ⟶ C) (s : Z ⟶ Y) [IsFinite (d ≫ q)] [IsFinite (s ≫ j ≫ q)] :
    IsFinite (fullBoundaryProductMap q j d s ≫ pullback.fst (j ≫ q) q) :=
  fullBoundaryProduct_finite q j d s
