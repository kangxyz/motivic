/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.LocalVanishing.Laurent.RestrictionInjective
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeAffineLineOpenSquares
public import Motivic.Aglib.AlgebraicGeometry.AffineLine.Open.AffineLineOpenMonicShrinking
public import Motivic.Aglib.RingTheory.Smooth.Localization
/-! # A generic-open zero becomes zero on the whole torus after shrinking the base -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient
universe v u
section
open _root_.Algebra.Smooth _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]


attribute [local instance] away_smooth

/-- A section vanishing on an original nonempty open of the relative torus vanishes
on the entire torus after one actual principal shrinking of the smooth integral base. -/
theorem
  _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite.exists_base_shrink_restriction_eq_zero
    [IsDomain R]
    (P : _root_.Motivic.PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (W : (Spec (.of R[X])).Opens)
    (hW : (W : Set (Spec (.of R[X]))).Nonempty) (hWX : W ≤ principalOpen X)
    (s : P.sections (_root_.Motivic.Cor.mk (openSite (k := k) (X : R[X]))))
    (hs : P.transfer ((_root_.Motivic.Cor.graphFunctor k).map
      (originalInclusion (k := k) (principalOpen X) W hWX)) s = 0) :
    ∃ r : R, r ≠ 0 ∧ P.transfer ((_root_.Motivic.Cor.graphFunctor k).map
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
  have hz : P.transfer ((_root_.Motivic.Cor.graphFunctor k).map u)
      (P.transfer ((_root_.Motivic.Cor.graphFunctor k).map b) s) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← _root_.Motivic.PresheafWithTransfers.transfer_comp,
      ← Functor.map_comp, hcomm, Functor.map_comp,
          _root_.Motivic.PresheafWithTransfers.transfer_comp,
      ConcreteCategory.comp_apply]
    change P.transfer ((_root_.Motivic.Cor.graphFunctor k).map v)
      (P.transfer ((_root_.Motivic.Cor.graphFunctor k).map i) s) = 0
    rw [hs]
    exact map_zero (P.transfer ((_root_.Motivic.Cor.graphFunctor k).map v)).hom
  exact hz.trans (map_zero (P.transfer ((_root_.Motivic.Cor.graphFunctor k).map u)).hom).symm

end
