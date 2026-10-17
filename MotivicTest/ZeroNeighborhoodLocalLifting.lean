module
import Motivic.Cohomology.A1.ZeroNeighborhoodLocalLifting
/-! # Original punctured-neighborhood sections lift on one original base shrink -/
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.RelativeProjectiveLine
universe v u
namespace Motivic.PresheafWithTransfers
variable {k : Type u} [Field k]
example
    (P : PresheafWithTransfers.{v} k) (hP : IsA1Invariant P)
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (b : Spec (.of R) ⟶ Spec (.of k)) [Smooth b]
    (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
    (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
    (s : Spec (.of R)) :
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧
      ∀ d : sections P (Cor.mk (neighborhoodTargetSite k R b V)),
      ∃ a : sections P (Cor.mk (neighborhoodPsiSite k R b r)),
      ∃ c : sections P (Cor.mk (neighborhoodLambdaSite k R b V r)),
        ((toPresheaf k).obj P).map (neighborhoodPencilBeta k R b V r).op a -
          ((toPresheaf k).obj P).map (neighborhoodPencilAlpha k R b V r).op c =
        ((toPresheaf k).obj P).map (neighborhoodPencilGraph k R b V r).op d :=
  exists_zeroNeighborhood_local_lifting P hP R b V hV s
#print axioms exists_zeroNeighborhood_local_lifting
end Motivic.PresheafWithTransfers
