/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.H1.WholeBaseZero
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.WholeBase.OpenMaps
public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialQuotient.PolynomialQuotientComplement
public import Motivic.Cohomology.Sheaf.RelativeMonicZeroSquare
public import Motivic.Aglib.RingTheory.Smooth.Normal

/-! # Whole-line H¹ base vanishing from an actual monic zero square -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Polynomial
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.PolynomialOpenQuotient
open AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
universe w u
namespace AlgebraicGeometry.Scheme.Hom

/-- The original section supplied by the given full-neighborhood isomorphism. -/
def fullNeighborhoodSection {X Y Z : Scheme.{u}} (p : Y ⟶ X) (z : Z ⟶ X)
    [IsIso (pullback.snd p z)] : Z ⟶ Y :=
  inv (pullback.snd p z) ≫ pullback.fst p z

lemma fullNeighborhoodSection_comp {X Y Z : Scheme.{u}} (p : Y ⟶ X) (z : Z ⟶ X)
    [IsIso (pullback.snd p z)] : fullNeighborhoodSection p z ≫ p = z := by
  simp [fullNeighborhoodSection, pullback.condition]

lemma fullNeighborhoodSection_isPullback {X Y Z : Scheme.{u}} (p : Y ⟶ X) (z : Z ⟶ X)
    [IsIso (pullback.snd p z)] : IsPullback (fullNeighborhoodSection p z) (𝟙 Z) p z :=
  (IsPullback.of_hasPullback p z).of_iso (asIso (pullback.snd p z))
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [fullNeighborhoodSection])
    (by simp) (by simp) (by simp)

instance fullNeighborhoodSection_closed {X Y Z : Scheme.{u}} (p : Y ⟶ X) (z : Z ⟶ X)
    [IsIso (pullback.snd p z)] [IsClosedImmersion z] :
    IsClosedImmersion (fullNeighborhoodSection p z) := by
  dsimp [fullNeighborhoodSection]
  infer_instance

end AlgebraicGeometry.Scheme.Hom

namespace Motivic.SheafCohomology
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.Sheaf.LargeCohomology
open _root_.Algebra.Smooth _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
variable {k R : Type u} [Field k] [CommRing R] [IsDomain R]
  [Algebra k R] [Algebra.Smooth k R]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
attribute [local instance] away_smooth

local instance relativeMonic_base_smooth :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
  PolynomialLaurent.baseMap_smooth (k := k) (R := R)
local instance relativeMonic_line_smooth : SmoothOfRelativeDimension 1 (boundaryLineProjection R) :=
  Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one R

/-- No extra lifting or compactification hypothesis: the original two zero legs
and the original full monic closed neighborhood are the entire input. -/
theorem exists_monic_h_one_base_restriction_zero
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (f : R[X]) (hf : f.Monic)
    (x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1 (lineSite (k := k) (R := R)))
    {Y : SmoothSite (Spec (.of k))} [IsAffine Y.left]
    (p : Y ⟶ lineSite (k := k) (R := R)) [Etale p.left]
    [IsIso (pullback.snd p.left (AlgebraicGeometry.PolynomialOpenQuotient.inclusion f))]
    (hA : (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1).map (openInclusion f).op x = 0)
    (hY : (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1).map p.op x = 0) :
    ∃ (V : (Spec (.of R)).Opens) (hV : IsAffineOpen V),
      let : IsAffine V.toScheme := hV
      genericPoint (Spec (.of R)) ∈ V ∧
      ∃ hW : IsAffineOpen (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ V),
        let : IsAffine (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ V).toScheme := hW
        (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) 1).map
          (boundaryBaseAmbientRestriction k R
            (Spec.map (CommRingCat.ofHom (algebraMap k R))) (boundaryLineProjection R) ⊤ V).op
          x = 0 := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let : IsIntegrallyClosed R := isIntegrallyClosed_of_smooth_field k R
  let t := Spec.map (CommRingCat.ofHom (algebraMap k R))
  let : Smooth t := PolynomialLaurent.baseMap_smooth (k := k) (R := R)
  let q := boundaryLineProjection R
  let : SmoothOfRelativeDimension 1 q :=
    Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one R
  let z := AlgebraicGeometry.PolynomialOpenQuotient.inclusion f
  let s := fullNeighborhoodSection p.left z
  have hs := fullNeighborhoodSection_comp p.left z
  have Hs := fullNeighborhoodSection_isPullback p.left z
  let : IsFinite (boundaryCoordinateMap R (AdjoinRoot f) (AdjoinRoot.mk f) ≫ q) := by
    change IsFinite (z ≫ q)
    rw [show z ≫ q = source f from
      AlgebraicGeometry.PolynomialOpenQuotient.inclusion_projection f]
    exact source_finite f hf
  have hY' := originalEtale_restriction_zero k R t q
    (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1) p x hY
  let : IsAffine (principalOpen f).toScheme :=
    IsAffineOpen.Spec_basicOpen (R := CommRingCat.of R[X]) f
  let : IsClosedImmersion (boundaryCoordinateMap R (AdjoinRoot f) (AdjoinRoot.mk f)) :=
    inferInstanceAs (IsClosedImmersion z)
  exact exists_original_h_one_base_restriction_eq_zero
    k R t p.left (principalOpen f).ι (AdjoinRoot f) (AdjoinRoot.mk f) s hs Hs
    (by
      change Set.range (AlgebraicGeometry.PolynomialOpenQuotient.inclusion f) = _
      rw [range_inclusion_complement, Scheme.Opens.range_ι]) F hF x hA hY'

/-- The zero square kills the original class under the literal base-open inclusion. -/
theorem exists_monic_h_one_base_open_zero
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (f : R[X]) (hf : f.Monic)
    (x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1 (lineSite (k := k) (R := R)))
    {Y : SmoothSite (Spec (.of k))} [IsAffine Y.left]
    (p : Y ⟶ lineSite (k := k) (R := R)) [Etale p.left]
    [IsIso (pullback.snd p.left (AlgebraicGeometry.PolynomialOpenQuotient.inclusion f))]
    (hA : (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1).map (openInclusion f).op x = 0)
    (hY : (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1).map p.op x = 0) :
    ∃ V : (Spec (.of R)).Opens, IsAffineOpen V ∧ genericPoint (Spec (.of R)) ∈ V ∧
      (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((SheafWithTransfers.toSheaf k).obj F) 1).map
        (SmoothSite.openInclusion (lineSite (k := k) (R := R))
          (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ V)).op x = 0 := by
  exact exists_boundaryBase_open_zero_of_restriction k R
    (Spec.map (CommRingCat.ofHom (algebraMap k R))) (boundaryLineProjection R)
    (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1) x
    (exists_monic_h_one_base_restriction_zero F hF f hf x p hA hY)

end Motivic.SheafCohomology
