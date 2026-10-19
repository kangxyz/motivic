/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.LocalVanishing.Laurent.GenericOpenZero
public import Lean
/-! # The original generic-open section dies after an actual base shrinking -/
public noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial Motivic
open AlgebraicGeometry.PolynomialOpenQuotient
open _root_.Algebra.Smooth
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
universe v u
namespace MotivicTest.RelativeLaurentGenericOpenZero
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
attribute [local instance] away_smooth

/-- The output uses the original coefficient localization map, not an abstract field value. -/
theorem actual_base_shrink (k R : Type u) [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.Smooth k R]
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (W : (Spec (.of R[X])).Opens) (hW : (W : Set (Spec (.of R[X]))).Nonempty)
    (hWX : W ≤ principalOpen X)
    (s : P.sections (Cor.mk (openSite (k := k) (X : R[X]))))
    (hs : P.transfer ((Cor.graphFunctor k).map
      (originalInclusion (k := k) (principalOpen X) W hWX)) s = 0) :
    ∃ r : R, r ≠ 0 ∧ P.transfer ((Cor.graphFunctor k).map
      (puncturedBaseMap (IsScalarTower.toAlgHom k R (Localization.Away r)))) s = 0 :=
  exists_base_shrink_restriction_eq_zero P hP W hW hWX s hs

open Lean in
run_cmd do
  for name in #[``actual_base_shrink, ``exists_base_shrink_restriction_eq_zero,
      ``laurent_principal_restriction_injective,
          ``_root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite.laurentSiteIso_coordinate,
      ``_root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite.punctured_open_square,
          ``_root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite.exists_moving_action] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original-base shrinking of the HI PST section: standard foundations only."

end MotivicTest.RelativeLaurentGenericOpenZero
