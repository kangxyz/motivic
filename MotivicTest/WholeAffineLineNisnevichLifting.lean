/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.AffineLine.NisnevichLifting
import Lean

/-! # Direct original-square consumer of whole affine-line base-only correction -/

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
theorem actual_original_square_base_only_lifting
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
  exact exists_originalNisSquare_base_lifting k R t p a B z s hs H hcomp P hP

open Lean in
run_cmd do
  for name in #[``actual_original_square_base_only_lifting,
      ``exists_originalNisSquare_base_lifting,
      ``exists_wholeAffineLine_base_lifting,
      ``Scheme.RelativeCurvePencil.exists_baseOnly_relativeCurve_lifting,
      ``exists_base_open_full_boundary_twist_frames,
      ``exists_base_open_finite_infinity,
      ``Scheme.finite_generic_base_fiber_of_finite_projectiveLine,
      ``Scheme.Modules.Invertible.exists_base_open_unitIso_of_isProper_finite_fiber] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original whole affine-line square, base-only correction: standard foundations only."

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
