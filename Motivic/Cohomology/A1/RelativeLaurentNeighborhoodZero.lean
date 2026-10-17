/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.RelativeLaurentGenericOpenZero
public import Motivic.Cohomology.SheafCohomologyGenericOpen
/-! # Original torus neighborhoods give genuine whole-torus zero after base shrinking -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
open AlgebraicGeometry.PolynomialOpenQuotient
universe v u
namespace Motivic.RelativePolynomialOpenSpans
variable {k R : Type u} [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.Smooth k R]
attribute [local instance] away_smooth

/-- This consumes the original open-neighborhood restriction, not a substituted stalk. -/
theorem exists_base_shrink_of_neighborhood_zero
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (W : (openSite (k := k) (X : R[X])).left.Opens)
    (hW : (W : Set (openSite (k := k) (X : R[X])).left).Nonempty)
    (s : P.sections (Cor.mk (openSite (k := k) (X : R[X]))))
    (hs : P.transfer ((Cor.graphFunctor k).map
      (SmoothSite.openInclusion (openSite (k := k) (X : R[X])) W)) s = 0) :
    ∃ r : R, r ≠ 0 ∧ P.transfer ((Cor.graphFunctor k).map
      (puncturedBaseMap (IsScalarTower.toAlgHom k R (Localization.Away r)))) s = 0 := by
  let j := W.ι ≫ (principalOpen (X : R[X])).ι
  let V := j.opensRange
  have hV : (V : Set (Spec (.of R[X]))).Nonempty := by
    obtain ⟨x, hx⟩ := hW
    exact ⟨j ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩
  have hVX : V ≤ principalOpen X := by
    rintro x ⟨y, rfl⟩
    exact (W.ι y).property
  let t : V.toScheme ⟶ W.toScheme := IsOpenImmersion.lift j V.ι (by
    rw [Scheme.Opens.range_ι]
    exact Set.Subset.rfl)
  have ht : t ≫ j = V.ι := IsOpenImmersion.lift_fac _ _ _
  have htX : t ≫ W.ι = (Spec (.of R[X])).homOfLE hVX := by
    apply (cancel_mono (principalOpen (X : R[X])).ι).mp
    rw [Category.assoc, ht, Scheme.homOfLE_ι]
  let b : originalOpenSite (k := k) V ⟶
      (SmoothSite.opensFunctor (openSite (k := k) (X : R[X]))).obj W :=
    SmoothSite.homMk t (by
      change t ≫ (W.ι ≫ ((principalOpen (X : R[X])).ι ≫ _)) = V.ι ≫ _
      rw [← Category.assoc, htX, ← Category.assoc, Scheme.homOfLE_ι])
  have hb : b ≫ SmoothSite.openInclusion (openSite (k := k) (X : R[X])) W =
      originalInclusion (k := k) (principalOpen X) V hVX := by
    apply MorphismProperty.Over.Hom.ext
    exact htX
  apply exists_base_shrink_restriction_eq_zero P hP V hV hVX s
  rw [← hb, Functor.map_comp, PresheafWithTransfers.transfer_comp, ConcreteCategory.comp_apply, hs]
  exact map_zero (P.transfer ((Cor.graphFunctor k).map b)).hom

end Motivic.RelativePolynomialOpenSpans
