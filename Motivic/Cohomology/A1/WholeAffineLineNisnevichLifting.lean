/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.WholeAffineLineBaseLifting
public import Motivic.Aglib.AlgebraicGeometry.Normalization.RelativeAffineLineFullOverlap

/-! # Base-only correction for an original whole affine-line Nisnevich square -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic ProjectiveSpace
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom
universe u
namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f
local instance (R : Type u) [CommRing R] : SmoothOfRelativeDimension 1 (boundaryLineProjection R) :=
  AffineLineEtaleCompactification.polynomialProjection_smooth_one R
variable (k : Type u) [Field k] (R : Type u) [CommRing R] [IsDomain R]
  [IsIntegrallyClosed R] [IsNoetherianRing R]
  (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]
  {Y A : Scheme.{u}} [IsAffine Y] [IsAffine A]
  (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (a : A ⟶ Spec (.of (Polynomial R))) [IsOpenImmersion a]
  (B : Type u) [CommRing B] (z : Polynomial R →+* B)
  (s : Spec (.of B) ⟶ Y) [IsClosedImmersion s]
  (hs : s ≫ p = boundaryCoordinateMap R B z)
  (H : IsPullback s (𝟙 _) p (boundaryCoordinateMap R B z))
  [IsFinite (boundaryCoordinateMap R B z ≫ boundaryLineProjection R)]
  (hcomp : Set.range (boundaryCoordinateMap R B z) = (Set.range a)ᶜ)

include hs H hcomp in
/-- The original full overlap itself is the retained target. All compactification,
boundary-cover and frame data are constructed; only the coefficient base is shrunk. -/
theorem exists_originalNisSquare_base_lifting
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    ∃ (V : (Spec (.of R)).Opens) (hV : IsAffineOpen V),
      let : IsAffine V.toScheme := hV
      genericPoint (Spec (.of R)) ∈ V ∧
      ∃ hW : IsAffineOpen (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ V),
        let : IsAffine (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ V).toScheme := hW
        PresheafWithTransfers.HasRestrictionDifferenceLifting P
          (boundaryBasePencilGraph k R (ULift.{u} (Fin 2)) t (boundaryLineProjection R)
            p a (toProjectiveLine R p) (inclusion R p) (inclusion_projection R p)
            ⊤ V (overlapInclusion R p a) (𝟙 _) (Category.id_comp _))
          (boundaryBasePencilBeta k R (ULift.{u} (Fin 2)) t (boundaryLineProjection R)
            p a (toProjectiveLine R p) (inclusion R p) (inclusion_projection R p) ⊤ V)
          (boundaryBasePencilAlpha k R (ULift.{u} (Fin 2)) t (boundaryLineProjection R)
            p a (toProjectiveLine R p) (inclusion R p) (inclusion_projection R p) ⊤ V) := by
  have ha : Disjoint (Set.range a) (Set.range (boundaryCoordinateMap R B z)) := by
    rw [hcomp]
    exact disjoint_compl_right
  exact exists_wholeAffineLine_base_lifting k R t p a B z s hs H ha
    (overlapInclusion R p a)
    (overlap_infinity_boundary_cover R p a (boundaryCoordinateMap R B z) s H hcomp)
    (𝟙 _) (Category.id_comp _) P hP

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
