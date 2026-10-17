/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.WholeAffineLineH1BaseZero
public import Lean
/-! # Actual whole-line H¹ base restriction and transitive trust audit -/
public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic ProjectiveSpace
open Scheme.Hom Opposite Motivic.SheafCohomology
open Scheme.RelativeAffineLineEtaleCompactification
universe w u
namespace MotivicTest.WholeAffineLineH1BaseZero
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f
local instance (R : Type u) [CommRing R] : SmoothOfRelativeDimension 1 (boundaryLineProjection R) :=
  Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one R
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


variable [IsClosedImmersion (boundaryCoordinateMap R B z)]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [EnoughInjectives
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

include hs H hcomp in
/-- The original H¹ class becomes zero on the entire line over a smaller base.
Only the base open is shrunk; the positive-cohomology presheaf is never glued. -/
theorem actual_whole_line_base_zero
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (x : Motivic.SheafCohomology.H.{w, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1
      (originalAmbientSite k R t (boundaryLineProjection R)))
    (hA : (Motivic.SheafCohomology.presheaf.{w, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1).map
        (originalOpenArrow k R t (boundaryLineProjection R) a).op x = 0)
    (hY : (Motivic.SheafCohomology.presheaf.{w, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1).map
        (originalEtaleArrow k R t (boundaryLineProjection R) p).op x = 0) :
    ∃ (V : (Spec (.of R)).Opens) (hV : IsAffineOpen V),
      let : IsAffine V.toScheme := hV
      genericPoint (Spec (.of R)) ∈ V ∧
      ∃ hW : IsAffineOpen (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ V),
        let : IsAffine (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ V).toScheme := hW
        (Motivic.SheafCohomology.presheaf.{w, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) 1).map
          (boundaryBaseAmbientRestriction k R t (boundaryLineProjection R) ⊤ V).op x = 0 :=
  exists_original_h_one_base_restriction_eq_zero k R t p a B z s hs H hcomp F hF x hA hY

open Lean in
run_cmd do
  for name in #[``actual_whole_line_base_zero,
      ``exists_original_h_one_base_restriction_eq_zero,
      ``h_one_restriction_eq_zero_of_square_difference_lifting,
      ``injectiveSectionBoundary_restriction,
      ``exists_injective_lift_of_boundary_restriction_zero,
      ``boundaryBasePencilSquare_isPullback,
      ``boundaryBaseOriginalOverlapTargetRestriction_graph,
      ``boundaryBaseWholeLift_range, ``boundaryBaseWholeLift_iso] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original whole-line H1 base-only restriction: standard axioms only."
end MotivicTest.WholeAffineLineH1BaseZero
