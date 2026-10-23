/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.H1.WholeBaseCorrection
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.WholeComplement
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.FullOverlap
public import Aglib.CategoryTheory.Sites.SheafCohomology.Large.Basic
public import Motivic.Cohomology.A1.LocalVanishing.AffineLine.NisnevichLifting

/-! # Base-only correction for an original whole affine-line Nisnevich square -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic ProjectiveSpace
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom
open _root_.CategoryTheory.Sheaf.LargeCohomology _root_.Motivic.SheafCohomology Opposite
universe w u
namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
open _root_.AlgebraicGeometry.Scheme.SmoothSite (nisnevichTopology)
/-- The smoothness instance used in this module. -/
local instance wholeBaseZeroSmooth {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f
/-- The relative-dimension instance used in this module. -/
local instance wholeBaseZeroSmoothRelativeDimension
    (R : Type u) [CommRing R] : SmoothOfRelativeDimension 1 (boundaryLineProjection R) :=
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


variable [IsClosedImmersion (boundaryCoordinateMap R B z)]
  [HasExt.{w} (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [EnoughInjectives
    (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

include hs H hcomp in
/-- The original H¹ class becomes zero on the entire line over a smaller base.
Only the base open is shrunk; the positive-cohomology presheaf is never glued. -/
theorem exists_original_h_one_base_restriction_eq_zero
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (x : _root_.CategoryTheory.Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1
      (originalAmbientSite k R t (boundaryLineProjection R)))
    (hA : (_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{w, u + 1, u, u + 1}
      (nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1).map
        (originalOpenArrow k R t (boundaryLineProjection R) a).op x = 0)
    (hY : (_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{w, u + 1, u, u + 1}
      (nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1).map
        (originalEtaleArrow k R t (boundaryLineProjection R) p).op x = 0) :
    ∃ (V : (Spec (.of R)).Opens) (hV : IsAffineOpen V),
      let : IsAffine V.toScheme := hV
      genericPoint (Spec (.of R)) ∈ V ∧
      ∃ hW : IsAffineOpen (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ V),
        let : IsAffine (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ V).toScheme := hW
        (_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{w, u + 1, u, u + 1}
      (nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) 1).map
          (boundaryBaseAmbientRestriction k R t (boundaryLineProjection R) ⊤ V).op x = 0 := by
  obtain ⟨V, hV, hη, hW, hL⟩ :=
    exists_originalNisSquare_base_lifting k R t p a B z s hs H hcomp F.obj hF
  let : IsAffine V.toScheme := hV
  let : IsAffine (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ V).toScheme := hW
  let z' := boundaryBaseWholeLift (boundaryLineProjection R) (boundaryCoordinateMap R B z) V
  let : IsIso (pullback.snd (boundaryBaseCoverMap (boundaryLineProjection R) p ⊤ V) z') :=
    boundaryBaseWholeLift_iso (boundaryLineProjection R) p (boundaryCoordinateMap R B z) V s hs H
  let : SmoothOfRelativeDimension 1
      ((pullback.fst p a ≫ inclusion R p) ≫
        (toProjectiveLine R p ≫ toSpec R (ULift.{u} (Fin 2)))) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (overlapInclusion R p a ≫ projection R p))
  refine ⟨V, hV, hη, hW, ?_⟩
  exact h_one_boundaryBase_restriction_eq_zero k R (ULift.{u} (Fin 2)) t
    (boundaryLineProjection R) p a (toProjectiveLine R p) (inclusion R p)
    (inclusion_projection R p) ⊤ V F hL z'
    (boundaryBaseWholeLift_range (boundaryLineProjection R) a
      (boundaryCoordinateMap R B z) V hcomp) x hA hY

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
