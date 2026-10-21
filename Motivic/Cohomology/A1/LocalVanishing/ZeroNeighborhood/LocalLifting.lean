/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.AlgebraicGeometry.Correspondences.Pencils.ProjectiveLine.CorrectingEndpoints
public import Motivic.Cohomology.A1.Boundary.SquareDifferenceActions
/-! # Actual relative Zariski-neighborhood class lifting for homotopy-invariant transfers

Only restrictions of original punctured-neighborhood sections are claimed to lift.
This does not identify arbitrary étale neighborhood classes or prove cylinder purity.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.RelativeProjectiveLine
universe v u
namespace Motivic.PresheafWithTransfers
variable {k : Type u} [Field k]

theorem exists_zeroNeighborhood_local_lifting
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
        ((toPresheaf k).obj P).map (neighborhoodPencilGraph k R b V r).op d := by
  obtain ⟨r, hr, lam, psi, alpha, h0, h1⟩ :=
    exists_neighborhoodCorrectingEndpoints k R b V hV s
  refine ⟨r, hr, fun d => ⟨-transfer P psi d, -transfer P lam d, ?_⟩⟩
  exact restriction_difference_eq_restriction_of_homotopy P hP
    (neighborhoodPencilGraph k R b V r) (neighborhoodPencilBeta k R b V r)
    (neighborhoodPencilAlpha k R b V r) lam psi alpha h0 h1 d
end Motivic.PresheafWithTransfers
