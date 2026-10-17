/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.RelativeLaurentRestrictionInjective
public import Motivic.AlgebraicGeometry.Correspondences.RelativeAffineLineOpenSquares
public import Motivic.Aglib.AlgebraicGeometry.AffineLineOpenMonicShrinking
/-! # A generic-open zero becomes zero on the whole torus after shrinking the base -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient
universe v u
namespace Motivic.RelativePolynomialOpenSpans
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]

/-- Localization in a base element is a genuine smooth k-algebra. -/
theorem away_smooth (r : R) : Algebra.Smooth k (Localization.Away r) := by
  let : Algebra.Smooth R (Localization.Away r) := Algebra.Smooth.of_isLocalization_Away r
  exact Algebra.Smooth.comp k R (Localization.Away r)

attribute [local instance] away_smooth

/-- A section vanishing on an original nonempty open of the relative torus vanishes
on the entire torus after one actual principal shrinking of the smooth integral base. -/
theorem exists_base_shrink_restriction_eq_zero [IsDomain R]
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (W : (Spec (.of R[X])).Opens)
    (hW : (W : Set (Spec (.of R[X]))).Nonempty) (hWX : W ≤ principalOpen X)
    (s : P.sections (Cor.mk (openSite (k := k) (X : R[X]))))
    (hs : P.transfer ((Cor.graphFunctor k).map
      (originalInclusion (k := k) (principalOpen X) W hWX)) s = 0) :
    ∃ r : R, r ≠ 0 ∧ P.transfer ((Cor.graphFunctor k).map
      (puncturedBaseMap (IsScalarTower.toAlgHom k R (Localization.Away r)))) s = 0 := by
  obtain ⟨r, hr, g, hg, _, hXg, hWg⟩ :=
    AffineLineOpenMonicShrinking.exists_coprime_monic_punctured_open R W hW
  let S := Localization.Away r
  let : IsDomain S := Localization.Away.isDomain hr
  let φ : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
  let b := puncturedBaseMap φ
  let i := originalInclusion (k := k) (principalOpen X) W hWX
  let u := narrowInclusion (k := k) X g
  let v := openMapOfLE φ W (principalOpen (X * g)) hWg
  have hcomm : u ≫ b = v ≫ i := punctured_open_square φ W hWX g hWg
  refine ⟨r, hr, ?_⟩
  apply laurent_principal_restriction_injective P hP g hg hXg
  have hz : P.transfer ((Cor.graphFunctor k).map u)
      (P.transfer ((Cor.graphFunctor k).map b) s) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← PresheafWithTransfers.transfer_comp,
      ← Functor.map_comp, hcomm, Functor.map_comp, PresheafWithTransfers.transfer_comp,
      ConcreteCategory.comp_apply]
    change P.transfer ((Cor.graphFunctor k).map v)
      (P.transfer ((Cor.graphFunctor k).map i) s) = 0
    rw [hs]
    exact map_zero (P.transfer ((Cor.graphFunctor k).map v)).hom
  exact hz.trans (map_zero (P.transfer ((Cor.graphFunctor k).map u)).hom).symm

end Motivic.RelativePolynomialOpenSpans
