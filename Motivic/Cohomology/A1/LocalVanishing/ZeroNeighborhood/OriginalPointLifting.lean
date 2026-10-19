/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.ZeroNeighborhood.OriginalLifting
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Retained.BaseChange
public import Motivic.Aglib.AlgebraicGeometry.AffineLine.Open.AffineLineZeroNeighborhoodBaseShrink

/-! # Correct original punctured sections from just a zero-point neighborhood

The first shrink is along the true coefficient base and makes the whole zero
section lie in the actual inverse-image open. The correction then restricts the
original punctured section along the literal coefficient-extension map.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.RelativeProjectiveLine

universe v u

namespace Motivic.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- No whole-zero hypothesis on the original neighborhood: it is constructed by
an actual base localization around the chosen original point. -/
theorem exists_zeroPoint_original_lifting
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (b : Spec (.of R) ⟶ Spec (.of k)) [Smooth b]
    (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
    (s : Spec (.of R))
    (hs : Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) s ∈ V) :
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧
      ∃ hV : IsAffineOpen (neighborhoodBaseChangeOpen
        (algebraMap R (Localization.Away r)) V),
      let : IsAffine (neighborhoodBaseChangeOpen
        (algebraMap R (Localization.Away r)) V).toScheme := hV
      Set.range (Spec.map (CommRingCat.ofHom
        (Polynomial.evalRingHom (0 : Localization.Away r)))) ⊆
          neighborhoodBaseChangeOpen (algebraMap R (Localization.Away r)) V ∧
      ∃ s' : Spec (.of (Localization.Away r)),
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) s' = s ∧
      ∃ t : Localization.Away r, s' ∈ PrimeSpectrum.basicOpen t ∧
        ∀ d : sections P (Cor.mk (neighborhoodCommonSite k R b V 1)),
        ∃ a : sections P (Cor.mk (neighborhoodPsiSite k (Localization.Away r)
          (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ b) t)),
        ∃ c : sections P (Cor.mk (neighborhoodLambdaSite k (Localization.Away r)
          (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ b)
          (neighborhoodBaseChangeOpen (algebraMap R (Localization.Away r)) V) t)),
          ((toPresheaf k).obj P).map (neighborhoodPencilBeta k (Localization.Away r)
            (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ b)
            (neighborhoodBaseChangeOpen (algebraMap R (Localization.Away r)) V) t).op a -
          ((toPresheaf k).obj P).map (neighborhoodPencilAlpha k (Localization.Away r)
            (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ b)
            (neighborhoodBaseChangeOpen (algebraMap R (Localization.Away r)) V) t).op c =
          ((toPresheaf k).obj P).map
            (neighborhoodOriginalRestriction (Localization.Away r)
              (neighborhoodBaseChangeOpen (algebraMap R (Localization.Away r)) V) k
              (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ b) t ≫
              neighborhoodPunctureBaseChange (algebraMap R (Localization.Away r)) V k b).op d := by
  obtain ⟨r, hr, hV, hzero⟩ := Scheme.exists_affine_whole_zero_base_restriction R V
    (show IsAffineOpen V from ‹IsAffine V.toScheme›) s hs
  let : IsAffine (neighborhoodBaseChangeOpen
    (algebraMap R (Localization.Away r)) V).toScheme := hV
  have hs' : s ∈ Set.range
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) := by
    change s ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r)))
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hr
  obtain ⟨s', hs'⟩ := hs'
  obtain ⟨t, ht, hL⟩ := P.exists_zeroNeighborhood_original_lifting hP (Localization.Away r)
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ b)
    (neighborhoodBaseChangeOpen (algebraMap R (Localization.Away r)) V) hzero s'
  refine ⟨r, hr, hV, hzero, s', hs', t, ht, fun d => ?_⟩
  obtain ⟨a, c, hac⟩ := hL (((toPresheaf k).obj P).map
    (neighborhoodPunctureBaseChange (algebraMap R (Localization.Away r)) V k b).op d)
  refine ⟨a, c, ?_⟩
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  exact hac

end Motivic.PresheafWithTransfers
