/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Intersection.ClosedIntersectionAffineChart
public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.FiniteGeneration
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Actual finite Tor coefficients on closed-intersection affine charts

Canonical quotient-supported Tor is transported through the proved section-ring
isomorphism to the actual whole affine inverse image. Its ambient scalar action
is the original section map, and its finite generation is derived over locally
Noetherian ambients. Tilde and the genuine affine chart produce a quasi-coherent
module sheaf on this actual inverse image. Gluing these local sheaves still
requires the separately constructed coherent Tor restriction transitions.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Intersection

open _root_.ComplexShape
open _root_.HomologicalComplex
open _root_.HomologicalComplex₂
open _root_.ModuleCat.TorComparison

variable {P T W D : Scheme.{u}} (i : T ⟶ P) [IsClosedImmersion i]
  (a : W ⟶ D) (b : W ⟶ T) (j : D ⟶ P) [IsClosedImmersion j]
  (sq : IsPullback a b j i)

/-- The canonical supported Tor module over the actual intersection section ring. -/
def closedIntersectionAffineTor (U : P.affineOpens) (n : ℕ) :
    ModuleCat.{u} Γ(W, (a ≫ j) ⁻¹ᵁ U) :=
  (ModuleCat.restrictScalars
      (closedIntersectionAffineQuotientEquiv i a b j sq U).symm.toRingHom).obj
    (torSupportModule (j.ker.ideal U) (i.ker.ideal U) n)

/-- The inverse quotient chart composes with the true section map to the quotient projection. -/
theorem closedIntersectionAffineQuotientEquiv_symm_comp (U : P.affineOpens) :
    (closedIntersectionAffineQuotientEquiv i a b j sq U).symm.toRingHom.comp
      ((a ≫ j).app U).hom = Ideal.Quotient.mk (j.ker.ideal U ⊔ i.ker.ideal U) := by
  ext r
  change (closedIntersectionAffineQuotientEquiv i a b j sq U).symm ((a ≫ j).app U r) = _
  rw [← closedIntersectionAffineQuotientEquiv_mk i a b j sq U r]
  exact RingEquiv.symm_apply_apply _ _

/-- Restricting the actual section-ring coefficient along the original section map
recovers precisely the original ambient categorical Tor module. -/
def closedIntersectionAffineTorAmbientIso (U : P.affineOpens) (n : ℕ) :
    (ModuleCat.restrictScalars ((a ≫ j).app U).hom).obj
      (closedIntersectionAffineTor i a b j sq U n) ≅
    ((Tor (ModuleCat Γ(P, U)) n).obj (ModuleCat.of Γ(P, U) (Γ(P, U) ⧸ i.ker.ideal U))).obj
      (ModuleCat.of Γ(P, U) (Γ(P, U) ⧸ j.ker.ideal U)) :=
  (ModuleCat.restrictScalarsComp ((a ≫ j).app U).hom
    (closedIntersectionAffineQuotientEquiv i a b j sq U).symm.toRingHom).symm.app _ ≪≫
  (ModuleCat.restrictScalarsCongr
    (closedIntersectionAffineQuotientEquiv_symm_comp i a b j sq U)).app _ ≪≫
  (torSupportModuleRestrictIso (j.ker.ideal U) (i.ker.ideal U) n).symm

/-- The actual chart coefficient is finite when its ambient section ring is Noetherian. -/
theorem closedIntersectionAffineTor_finite (U : P.affineOpens)
    [IsNoetherianRing Γ(P, U)] (n : ℕ) :
    Module.Finite Γ(W, (a ≫ j) ⁻¹ᵁ U) (closedIntersectionAffineTor i a b j sq U n) := by
  let e := closedIntersectionAffineTorAmbientIso i a b j sq U n
  let l : (((Tor (ModuleCat Γ(P, U)) n).obj
      (ModuleCat.of Γ(P, U) (Γ(P, U) ⧸ i.ker.ideal U))).obj
      (ModuleCat.of Γ(P, U) (Γ(P, U) ⧸ j.ker.ideal U))) →ₛₗ[((a ≫ j).app U).hom]
      closedIntersectionAffineTor i a b j sq U n :=
    { __ := e.inv.hom.toAddMonoidHom
      map_smul' := e.inv.hom.map_smul }
  exact Module.Finite.of_surjective l
    ((ModuleCat.epi_iff_surjective e.inv).mp inferInstance)

/-- Locally Noetherian geometry supplies finite coefficients without a separate ring premise. -/
instance [IsLocallyNoetherian P] (U : P.affineOpens) (n : ℕ) :
    Module.Finite Γ(W, (a ≫ j) ⁻¹ᵁ U) (closedIntersectionAffineTor i a b j sq U n) := by
  let := IsLocallyNoetherian.component_noetherian U
  exact closedIntersectionAffineTor_finite i a b j sq U n

/-- The whole actual intersection inverse image is an affine open, not one pointwise chart. -/
def closedIntersectionAffineOpen (U : P.affineOpens) : W.affineOpens := by
  have : IsClosedImmersion a := by
    rw [← sq.isoPullback_hom_fst]
    infer_instance
  exact ⟨(a ≫ j) ⁻¹ᵁ U, U.2.preimage (a ≫ j)⟩

/-- A genuine module sheaf on the actual affine inverse image, constructed from canonical Tor. -/
def closedIntersectionTorChartSheaf (U : P.affineOpens) (n : ℕ) :
    ((closedIntersectionAffineOpen i a b j sq U).1).toScheme.Modules :=
  (Scheme.Modules.restrictFunctor
    (closedIntersectionAffineOpen i a b j sq U).2.isoSpec.hom).obj
      ((tilde.functor Γ(W, (a ≫ j) ⁻¹ᵁ U)).obj
        (closedIntersectionAffineTor i a b j sq U n))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The constructed chart sheaf is actually quasi-coherent. -/
instance closedIntersectionTorChartSheaf_quasicoherent (U : P.affineOpens) (n : ℕ) :
    (closedIntersectionTorChartSheaf i a b j sq U n).IsQuasicoherent := by
  unfold closedIntersectionTorChartSheaf
  exact Scheme.Modules.isQuasicoherent_restrictFunctor _ _

end AlgebraicGeometry.Scheme.Intersection
