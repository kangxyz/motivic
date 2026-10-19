/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Intersection.ClosedIntersectionTorSheafRestrictionCoherence
public import Motivic.Aglib.AlgebraicGeometry.Intersection.ClosedAffineOverlap
public import Motivic.Aglib.AlgebraicGeometry.Modules.Gluing.AffineCharts
public import Motivic.Aglib.AlgebraicGeometry.Modules.Gluing.FiniteOpenCover.RelativeQuasicoherent

/-!
# Genuine finite descent of closed-intersection Tor chart sheaves

The overlap maps pass through the actual affine intersection in the separated
ambient. Their common-open cocycle is derived from the proved nested Tor
restriction equations and the genuine open-restriction associators. Finite
compatible-sections gluing then constructs a module sheaf whose restriction
to the union is quasi-coherent. No datum, cocycle or desired global coefficient
is an input. Independence of the chosen cover is not asserted here.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Intersection
open _root_.AlgebraicGeometry.Scheme.Modules.Gluing

open Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Hom.ClosedAffineCover
open _root_.AlgebraicGeometry.Scheme.Modules.Gluing.FiniteOpenCover
open _root_.AlgebraicGeometry.Scheme.Modules.Restriction.Refinement

variable {P T D W : Scheme.{u}} [P.IsSeparated]
  (i : T ⟶ P) (j : D ⟶ P) (a : W ⟶ D) (b : W ⟶ T)
  [IsClosedImmersion i] [IsClosedImmersion j] (sq : IsPullback a b j i)

/-- The actual transition uses both original chart restrictions to their genuine affine overlap. -/
def closedIntersectionTorTransition (U V : P.affineOpens) (n : ℕ) :
    (_root_.AlgebraicGeometry.Scheme.Modules.restrictFunctor (W.homOfLE (inf_le_left :
      ((a ≫ j) ⁻¹ᵁ U) ⊓ ((a ≫ j) ⁻¹ᵁ V) ≤ (a ≫ j) ⁻¹ᵁ U))).obj
        (closedIntersectionTorChartSheaf i a b j sq U n) ≅
      (_root_.AlgebraicGeometry.Scheme.Modules.restrictFunctor (W.homOfLE (inf_le_right :
        ((a ≫ j) ⁻¹ᵁ U) ⊓ ((a ≫ j) ⁻¹ᵁ V) ≤ (a ≫ j) ⁻¹ᵁ V))).obj
        (closedIntersectionTorChartSheaf i a b j sq V n) :=
  closedIntersectionTorSheafRestrictionIso i j a b sq (affineOverlap_le_left U V) n ≪≫
    (closedIntersectionTorSheafRestrictionIso i j a b sq
      (affineOverlap_le_right U V) n).symm

/-- Repeated-chart transitions are identities by the original map/inverse cancellation. -/
theorem closedIntersectionTorTransition_identity (U : P.affineOpens) (n : ℕ) :
    closedIntersectionTorTransition i j a b sq U U n = Iso.refl _ := by
  apply Iso.ext
  exact Iso.hom_inv_id _

variable {ι : Type u} (U : ι → P.affineOpens)

set_option backward.isDefEq.respectTransparency false in
/-- The genuine Tor datum instantiates nested coherence with the proved original Tor equation. -/
def closedIntersectionTorDatum (n : ℕ) :
    Datum (fun t => (a ≫ j) ⁻¹ᵁ U t)
      (fun t => closedIntersectionTorChartSheaf i a b j sq (U t) n) :=
  AffineCharts.datum (a ≫ j)
    (fun V => closedIntersectionTorChartSheaf i a b j sq V n)
    (fun h => closedIntersectionTorSheafRestrictionIso i j a b sq h n)
    (by
      intro V L K h k
      apply Iso.ext
      exact closedIntersectionTorSheafRestrictionIso_hom_comp i j a b sq h k n) U

/-- The datum retains exactly the original Tor maps on the genuine affine overlap. -/
theorem closedIntersectionTorDatum_transition (n : ℕ) (r s : ι) :
    (closedIntersectionTorDatum i j a b sq U n).transition r s =
      closedIntersectionTorTransition i j a b sq (U r) (U s) n := rfl

variable [Fintype ι]

/-- The actual finite compatible-sections equalizer on the original support scheme. -/
def closedIntersectionTorGlued (n : ℕ) : W.Modules :=
  glued (fun t => (a ≫ j) ⁻¹ᵁ U t)
    (fun t => closedIntersectionTorChartSheaf i a b j sq (U t) n)
      (closedIntersectionTorDatum i j a b sq U n)

/-- Every original chart is recovered by the proved local comparison of the actual equalizer. -/
def closedIntersectionTorGluedLocalIso (n : ℕ) (r : ι) :
    (_root_.AlgebraicGeometry.Scheme.Modules.restrictFunctor ((a ≫ j) ⁻¹ᵁ U r).ι).obj
      (closedIntersectionTorGlued i j a b sq U n) ≅
        closedIntersectionTorChartSheaf i a b j sq (U r) n :=
  localIso _ _ (closedIntersectionTorDatum i j a b sq U n) r

/-- The constructed coefficient on the actual union retains all chosen source charts. -/
def closedIntersectionTorCoefficient (V : W.Opens) (n : ℕ) : V.toScheme.Modules :=
  (_root_.AlgebraicGeometry.Scheme.Modules.restrictFunctor V.ι).obj (closedIntersectionTorGlued
      i j a b sq U n)

/-- Quasi-coherence holds on the actual covered union, without a global open-pushforward claim. -/
theorem closedIntersectionTorCoefficient_quasicoherent (V : W.Opens)
    (hU : ⨆ r, (a ≫ j) ⁻¹ᵁ U r = V) (n : ℕ) :
    (closedIntersectionTorCoefficient i j a b sq U V n).IsQuasicoherent :=
  @glued_restrict_isQuasicoherent W ι _
    (fun r => (a ≫ j) ⁻¹ᵁ U r)
    (fun r => closedIntersectionTorChartSheaf i a b j sq (U r) n)
    (closedIntersectionTorDatum i j a b sq U n) V hU
    (fun r => closedIntersectionTorChartSheaf_quasicoherent i a b j sq (U r) n)

end AlgebraicGeometry.Scheme.Intersection
