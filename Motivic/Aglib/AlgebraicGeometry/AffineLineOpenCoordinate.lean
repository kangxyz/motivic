/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.AffineLineCoprimeOpenPresentation
public import Motivic.AlgebraicGeometry.SmoothSiteAffineCoordinates

/-! # Original affine-line opens in their actual global-section coordinates -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Motivic.AffineLineReducedComplement
variable {k : Type u} [Field k] (U : (line k).Opens)

/-- The actual global sections of the original open subscheme. -/
abbrev openCoordinateRing : CommRingCat.{u} := Γ(U.toScheme, ⊤)

/-- Scalars act via the original structure morphism, not a chosen localization model. -/
@[instance_reducible] def openCoordinateAlgebra : Algebra k (openCoordinateRing U) :=
  SmoothSiteAffineCoordinates.sectionsAlgebra (openObject U)

attribute [local instance] openCoordinateAlgebra

/-- A literal principal-open equality proves affineness of the original open. -/
theorem open_isAffine_of_basicOpen_eq (f : k[X]) (h : PrimeSpectrum.basicOpen f = U) :
    IsAffine U.toScheme := by
  have hU : IsAffineOpen U := h ▸ IsAffineOpen.Spec_basicOpen (R := .of k[X]) f
  exact hU

/-- The original nonempty open has an integral coordinate ring. -/
theorem openCoordinateRing_isDomain (hU : (U : Set (line k)).Nonempty) :
    IsDomain (openCoordinateRing U) := by
  let : Nonempty U := hU.to_subtype
  infer_instance

/-- Noetherianity follows on the actual open's global sections. -/
theorem openCoordinateRing_noetherian [IsAffine U.toScheme] :
    IsNoetherianRing (openCoordinateRing U) := by
  let : IsAffine (openObject U).left := ‹IsAffine U.toScheme›
  exact SmoothSiteAffineCoordinates.sectionsNoetherian (openObject U)

/-- Smoothness uses the original scalar action on actual sections. -/
theorem openCoordinateRing_smooth [IsAffine U.toScheme] :
    Algebra.Smooth k (openCoordinateRing U) := by
  let : IsAffine (openObject U).left := ‹IsAffine U.toScheme›
  exact SmoothSiteAffineCoordinates.sectionsSmooth (openObject U)

/-- Restrict the original affine polynomial coordinate ring to the original open. -/
def openPolynomialRestriction : k[X] →+* openCoordinateRing U :=
  U.ι.appTop.hom.comp (Scheme.ΓSpecIso (.of k[X])).inv.hom

/-- The actual original coordinate section. -/
def openCoordinate : openCoordinateRing U := openPolynomialRestriction U X

theorem openPolynomialRestriction_C (r : k) :
    openPolynomialRestriction U (C r) = algebraMap k (openCoordinateRing U) r := by
  have hn := congrArg CommRingCat.Hom.hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Polynomial.C : k →+* k[X])))
  change (Scheme.ΓSpecIso (.of k[X])).inv.hom.comp C =
    (polynomialProjection (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom at hn
  change U.ι.appTop ((Scheme.ΓSpecIso (.of k[X])).inv (C r)) =
    (U.ι ≫ polynomialProjection (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv r)
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  exact congrArg (fun z => U.ι.appTop z) (RingHom.congr_fun hn r)

/-- Evaluation at the original coordinate is exactly restriction of polynomials. -/
theorem openPolynomialRestriction_eq_eval :
    openPolynomialRestriction U =
      Polynomial.eval₂RingHom (algebraMap k (openCoordinateRing U)) (openCoordinate U) := by
  ext r
  · simpa using openPolynomialRestriction_C U r
  · simp [openCoordinate]

/-- Polynomial evaluation retains the canonical original open embedding. -/
theorem spec_eval_eq_original_inclusion [IsAffine U.toScheme] :
    Spec.map (CommRingCat.ofHom
      (Polynomial.eval₂RingHom (algebraMap k (openCoordinateRing U)) (openCoordinate U))) =
      U.toScheme.isoSpec.inv ≫ U.ι := by
  rw [← openPolynomialRestriction_eq_eval, ← Scheme.isoSpec_inv_naturality U.ι,
    Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/-- A defining polynomial is a unit on the actual original open's coordinate ring. -/
theorem openPolynomialRestriction_isUnit (f : k[X])
    (hU : U ≤ PrimeSpectrum.basicOpen f) : IsUnit (openPolynomialRestriction U f) := by
  apply U.toScheme.toRingedSpace.isUnit_of_isUnit_germ ⊤
  intro x hx
  apply (U.toScheme.mem_basicOpen_top (openPolynomialRestriction U f) x).mp
  change x ∈ U.toScheme.basicOpen (U.ι.appTop ((Scheme.ΓSpecIso (.of k[X])).inv f))
  rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  exact hU x.property

/-- Exactly the unit condition needed by the moving pair, with no condition on g(a). -/
theorem openCoordinate_eval_isUnit (f : k[X]) (hU : U ≤ PrimeSpectrum.basicOpen f) :
    IsUnit ((f.map (algebraMap k (openCoordinateRing U))).eval (openCoordinate U)) := by
  have h := openPolynomialRestriction_isUnit U f hU
  rw [openPolynomialRestriction_eq_eval] at h
  change IsUnit (Polynomial.eval₂ (algebraMap k (openCoordinateRing U))
    (openCoordinate U) f) at h
  simpa only [Polynomial.eval_map] using h

end Motivic.AffineLineReducedComplement
