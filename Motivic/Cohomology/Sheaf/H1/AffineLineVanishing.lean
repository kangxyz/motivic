/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.LocalVanishing.H1.Pencil.Transport
public import Motivic.AlgebraicGeometry.Correspondences.Pencils.NormalizedCurve.CorrectingEndpoints
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Normalized.SiteMaps
public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.CorrectionTransport
/-! # Vanishing of ordinary H¹ on the affine line from the actual correcting pencil -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Scheme.AffineLineEtaleCompactification
universe w u
namespace Motivic
open _root_.AlgebraicGeometry.Scheme
/-- Existential correcting endpoints transport along the original source and target maps. -/
theorem correctingEndpoints_exists_transport {k : Type u} [Field k]
    {X T V Y X' T' V' Y' : SmoothSite (Spec (.of k))}
    (f : X ⟶ T) (g : X ⟶ V) (j : X ⟶ Y)
    (f' : X' ⟶ T') (g' : X' ⟶ V') (j' : X' ⟶ Y')
    (eX : X' ⟶ X) (eT : T' ⟶ T) (eV : V' ⟶ V) (eY : Y ⟶ Y')
    (hf : f' ≫ eT = eX ≫ f) (hg : g' ≫ eV = eX ≫ g)
    (hj : eX ≫ j ≫ eY = j')
    (hc : HasCorrectingEndpoints f g j) : HasCorrectingEndpoints f' g' j' := by
  obtain ⟨lam, psi, alpha, h0, h1⟩ := hc
  have he := correctingEndpoints_transport f g j f' g' j' eX eT eV eY hf hg hj
    lam psi alpha h0 h1
  exact ⟨(Cor.graphFunctor k).map eT ≫ lam ≫ (Cor.graphFunctor k).map eY,
    (Cor.graphFunctor k).map eV ≫ psi ≫ (Cor.graphFunctor k).map eY,
    (Cor.graphFunctor k).map (SmoothSite.a1Map (.of k) eX) ≫
      alpha ≫ (Cor.graphFunctor k).map eY, he.1, he.2⟩
end Motivic

namespace Motivic.SheafCohomology
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.AffineLineReducedComplement
variable {k : Type u} [Field k]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [EnoughInjectives
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

namespace AffineLineH1LiftData
open _root_.AlgebraicGeometry.Scheme
variable {F : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}}
  {x : Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
    F 1 (SmoothSite.affineLine (.of k))} (D : AffineLineH1LiftData F x)

/-- The canonical affine presentation of the whole fixed open avoids the full complement. -/
theorem openSpecMap_disjoint_complement :
    Disjoint (Set.range D.openSpecMap) (Set.range (inclusion D.U)) := by
  apply Set.disjoint_left.mpr
  rintro y ⟨a, rfl⟩ hy
  rw [range_inclusion] at hy
  exact hy (D.openSpecIso.inv a).property

/-- The boundary square of the actual affine refinement gives the required literal
scheme pullback isomorphism, without assuming a new covering condition. -/
theorem affineRefinement_iso_complement
    (R : CommRingCat.{u}) (r : Spec R ⟶ D.Y.left)
    (t : closedComplement D.U ⟶ Spec R)
    (H : IsPullback t (𝟙 _) (r ≫ D.p.left) (inclusion D.U)) :
    IsIso (pullback.snd (r ≫ D.p.left) (inclusion D.U)) := by
  rw [← H.isoPullback_inv_snd]
  infer_instance

/-- The two canonical-site endpoints of the actual correcting correspondence. -/
def CanonicalCorrectingHomotopy (R : CommRingCat.{u}) (r : Spec R ⟶ D.Y.left)
    [IsOpenImmersion r] : Prop :=
  HasCorrectingEndpoints
    (pencilAlpha k D.p.left r (D.pencilSourceAlpha R r))
    (pencilBeta k D.p.left r D.openSpecMap (D.pencilSourceAlpha R r)
      (D.pencilSourceBeta R r) (D.pencilSourceEq R r))
    (pencilGraphMap k D.p.left r (D.pencilSourceAlpha R r) D.U
      (D.pencilSourceGraphMap R r) (D.pencilGraphEq R r))

/-- The original affine open has a Noetherian coordinate ring. -/
theorem openSpec_noetherian : IsNoetherianRing Γ(D.U.toScheme, ⊤) := by
  let : IsAffine D.U.toScheme := D.affine_open
  exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top D.U.toScheme⟩

/-- The actual refined section has the original full-complement coordinate. -/
theorem affineBoundary_comp (R : CommRingCat.{u}) (r : Spec R ⟶ D.Y.left)
    (t : closedComplement D.U ⟶ Spec R) (ht : t ≫ r = D.complementLift) :
    t ≫ r ≫ D.p.left = inclusion D.U := by
  rw [← Category.assoc, ht, D.complementLift_comp]

/-- The original whole boundary square survives its actual affine factorization. -/
theorem affineBoundary_isPullback (R : CommRingCat.{u}) (r : Spec R ⟶ D.Y.left)
    (t : closedComplement D.U ⟶ Spec R) (ht : t ≫ r = D.complementLift) :
    IsPullback (t ≫ r) (𝟙 _) D.p.left (inclusion D.U) := by
  rw [ht]
  exact D.complementLift_isPullback

/-- Specialize the actual producer to the original source curves before boundary inputs. -/
theorem canonicalCorrectionProducer (R : CommRingCat.{u}) [IsNoetherianRing R]
    [IsNoetherianRing Γ(D.U.toScheme, ⊤)]
    (r : Spec R ⟶ D.Y.left) [IsOpenImmersion r] : type_of% (
  has_actualCorrectingEndpoints k D.p.left
    (R := R) (Q := Γ(D.U.toScheme, ⊤)) r
    D.openSpecMap (D.pencilSourceAlpha R r) (D.pencilSourceBeta R r)
    (D.pencilSourceEq R r)) :=
  has_actualCorrectingEndpoints k D.p.left
    (R := R) (Q := Γ(D.U.toScheme, ⊤)) r
    D.openSpecMap (D.pencilSourceAlpha R r) (D.pencilSourceBeta R r)
    (D.pencilSourceEq R r)

/-- The actual affine refinement constructs the correction without supplied section data. -/
theorem exists_canonical_correcting_homotopy
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (r : Spec R ⟶ D.Y.left) [IsOpenImmersion r]
    (t : closedComplement D.U ⟶ Spec R) (ht : t ≫ r = D.complementLift)
    (H : IsPullback t (𝟙 _) (r ≫ D.p.left) (inclusion D.U)) :
    D.CanonicalCorrectingHomotopy R r := by
  let : IsNoetherianRing Γ(D.U.toScheme, ⊤) := D.openSpec_noetherian
  let B := Polynomial k ⧸ complementIdeal D.U
  let z : Polynomial k →+* B := Ideal.Quotient.mk (complementIdeal D.U)
  let : IsClosedImmersion (Scheme.Hom.boundaryCoordinateMap k B z) :=
    inferInstanceAs (IsClosedImmersion (inclusion D.U))
  let : IsFinite
      (Scheme.Hom.boundaryCoordinateMap k B z ≫ Scheme.Hom.boundaryLineProjection k) :=
    finite_projection D.U D.generic_mem
  have hs : t ≫ r ≫ D.p.left = Scheme.Hom.boundaryCoordinateMap k B z :=
    D.affineBoundary_comp R r t ht
  have H0 : IsPullback (t ≫ r) (𝟙 _) D.p.left
      (Scheme.Hom.boundaryCoordinateMap k B z) :=
    D.affineBoundary_isPullback R r t ht
  have hc := D.canonicalCorrectionProducer R r B z D.openSpecMap_disjoint_complement t hs H D.U
    (D.pencilSourceGraphMap R r) (D.pencilGraphEq R r) H0 (range_inclusion D.U)
  exact hc

/-- Specialize only the canonical objects and source maps of the endpoint transport. -/
theorem canonicalCorrectionTransport (R : CommRingCat.{u})
    (r : Spec R ⟶ D.Y.left) [IsOpenImmersion r] : type_of% (
  correctingEndpoints_exists_transport
    (X' := D.pencilOverlap R r) (T' := diagonalSourceSite k D.p.left r)
    (V' := openObject D.U) (Y' := D.overlap)
    (pencilAlpha k D.p.left r (D.pencilSourceAlpha R r))
    (pencilBeta k D.p.left r D.openSpecMap (D.pencilSourceAlpha R r)
      (D.pencilSourceBeta R r) (D.pencilSourceEq R r))
    (pencilGraphMap k D.p.left r (D.pencilSourceAlpha R r) D.U
      (D.pencilSourceGraphMap R r) (D.pencilGraphEq R r))) :=
  correctingEndpoints_exists_transport
    (X' := D.pencilOverlap R r) (T' := diagonalSourceSite k D.p.left r)
    (V' := openObject D.U) (Y' := D.overlap)
    (pencilAlpha k D.p.left r (D.pencilSourceAlpha R r))
    (pencilBeta k D.p.left r D.openSpecMap (D.pencilSourceAlpha R r)
      (D.pencilSourceBeta R r) (D.pencilSourceEq R r))
    (pencilGraphMap k D.p.left r (D.pencilSourceAlpha R r) D.U
      (D.pencilSourceGraphMap R r) (D.pencilGraphEq R r))

/-- Specialize the original square maps without rebuilding the canonical correspondence. -/
theorem originalCorrectionTransport (R : CommRingCat.{u})
    (r : Spec R ⟶ D.Y.left) [IsOpenImmersion r] : type_of% (
  D.canonicalCorrectionTransport R r
    (D.refinedSquare (D.pencilRefinementSiteMap R r)).f₁₃
    (D.refinedSquare (D.pencilRefinementSiteMap R r)).f₁₂
    (D.overlapMap (D.pencilRefinementSiteMap R r))
    (D.pencilCommonSourceIso R r).inv (𝟙 _) D.pencilFixedSourceIso.inv
    D.pencilRetainedTargetIso.hom) :=
  D.canonicalCorrectionTransport R r
    (D.refinedSquare (D.pencilRefinementSiteMap R r)).f₁₃
    (D.refinedSquare (D.pencilRefinementSiteMap R r)).f₁₂
    (D.overlapMap (D.pencilRefinementSiteMap R r))
    (D.pencilCommonSourceIso R r).inv (𝟙 _) D.pencilFixedSourceIso.inv
    D.pencilRetainedTargetIso.hom

/-- Transport the constructed canonical endpoints back to the original fixed-U square. -/
theorem correcting_homotopy_of_canonical
    (R : CommRingCat.{u}) (r : Spec R ⟶ D.Y.left) [IsOpenImmersion r]
    (hc : D.CanonicalCorrectingHomotopy R r) :
    HasCorrectingEndpoints
      (D.refinedSquare (D.pencilRefinementSiteMap R r)).f₁₃
      (D.refinedSquare (D.pencilRefinementSiteMap R r)).f₁₂
      (D.overlapMap (D.pencilRefinementSiteMap R r)) := by
  exact D.originalCorrectionTransport R r
    (D.pencilAlpha_transport R r) (D.pencilBeta_transport R r)
    (D.pencilGraph_transport R r) hc

/-- The actual class-dependent cover produces a correction on an étale-leg refinement.
All three correspondences and both endpoints are conclusions, not input data. -/
theorem exists_correcting_homotopy :
    ∃ (Y' : SmoothSite (Spec (.of k))) (r : Y' ⟶ D.Y),
      Etale (r ≫ D.p).left ∧ IsIso (pullback.snd (r ≫ D.p).left (inclusion D.U)) ∧
      HasCorrectingEndpoints (D.refinedSquare r).f₁₃ (D.refinedSquare r).f₁₂
        (D.overlapMap r) := by
  obtain ⟨R, r, t, hR, hr, ht, Sheaf.LargeCohomology.H, hEt⟩ := D.exists_affineGeometry
  let : IsNoetherianRing R := hR
  let : IsOpenImmersion r := hr
  have hc := D.exists_canonical_correcting_homotopy R r t ht Sheaf.LargeCohomology.H
  have ho := D.correcting_homotopy_of_canonical R r hc
  exact ⟨_, D.pencilRefinementSiteMap R r, hEt,
    D.affineRefinement_iso_complement R r t Sheaf.LargeCohomology.H, ho⟩

end AffineLineH1LiftData

/-- A homotopy-invariant sheaf with transfers has no ordinary Nisnevich H¹ on the
field affine line. The fixed generic open, affine étale refinement, all local lifts,
and the correcting correspondence are constructed from the original class. -/
theorem h_one_affineLine_eq_zero
    (F : SheafWithTransfers.{u + 1} k)
    (hF : PresheafWithTransfers.IsA1Invariant F.obj)
    (x : Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1 (SmoothSite.affineLine (.of k))) : x = 0 := by
  let D := affineLineH1LiftData ((SheafWithTransfers.toSheaf k).obj F) x
  obtain ⟨Y', r, hEt, hIso, lam, psi, alpha, h0, h1⟩ := D.exists_correcting_homotopy
  let : Etale (r ≫ D.p).left := hEt
  let : IsIso (pullback.snd (r ≫ D.p).left (inclusion D.U)) := hIso
  exact h_one_eq_zero_of_affineLine_correcting_homotopy F hF x r lam psi alpha h0 h1

end Motivic.SheafCohomology
