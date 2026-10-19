/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.ZeroNeighborhood.LocalLifting
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Retained.Identification

/-! # Whole-zero neighborhood correction on original affine punctured sections -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.RelativeProjectiveLine

universe v u

namespace Motivic.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- The local correction consumes sections of the literal original affine puncture,
not sections postulated on an auxiliary projective target. Its right-hand side is
restriction along the unchanged original open inclusion. -/
theorem exists_zeroNeighborhood_original_lifting
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (b : Spec (.of R) ⟶ Spec (.of k)) [Smooth b]
    (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
    (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
    (s : Spec (.of R)) :
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧
      ∀ d : sections P (Cor.mk (neighborhoodCommonSite k R b V 1)),
      ∃ a : sections P (Cor.mk (neighborhoodPsiSite k R b r)),
      ∃ c : sections P (Cor.mk (neighborhoodLambdaSite k R b V r)),
        ((toPresheaf k).obj P).map (neighborhoodPencilBeta k R b V r).op a -
          ((toPresheaf k).obj P).map (neighborhoodPencilAlpha k R b V r).op c =
        ((toPresheaf k).obj P).map (neighborhoodOriginalRestriction R V k b r).op d := by
  obtain ⟨r, hr, hL⟩ := P.exists_zeroNeighborhood_local_lifting hP R b V hV s
  refine ⟨r, hr, fun d => ?_⟩
  obtain ⟨a, c, hac⟩ := hL (((toPresheaf k).obj P).map
    (neighborhoodPunctureIso R V k b).inv.op d)
  refine ⟨a, c, ?_⟩
  rw [neighborhoodOriginalRestriction, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  exact hac

end Motivic.PresheafWithTransfers
