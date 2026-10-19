/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.Moving.PolynomialOpen
public import Motivic.Aglib.AlgebraicGeometry.AffineLine.Open.AffineLineOpenCoordinate
/-! # Dense-open restriction for an arbitrary homotopy-invariant presheaf with transfers -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
open AlgebraicGeometry.PolynomialOpenQuotient
universe v u
namespace Motivic.PolynomialOpenSpans
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.AlgebraicGeometry.Scheme.AffineLineReducedComplement
variable {k : Type u} [Field k]

/-- The actual restriction to D(fg) is injective. No sheaf condition is imposed. -/
theorem principal_restriction_injective
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (f g : k[X]) (hf : f.Monic) (hg : g.Monic) (hfg : IsCoprime f g)
    (hU : (principalOpen f : Set (line k)).Nonempty) :
    Function.Injective (P.transfer ((Cor.graphFunctor k).map (narrowInclusion f g))) := by
  let U := principalOpen f
  let : Algebra k (openCoordinateRing U) := openCoordinateAlgebra U
  let : IsAffine U.toScheme := open_isAffine_of_basicOpen_eq U f rfl
  let : IsDomain (openCoordinateRing U) := openCoordinateRing_isDomain U hU
  let : IsNoetherianRing (openCoordinateRing U) := openCoordinateRing_noetherian U
  let : Algebra.Smooth k (openCoordinateRing U) := openCoordinateRing_smooth U
  let : IsAffine (openObject U).left := ‹IsAffine U.toScheme›
  let e := AffineCoordinates.affineIso (openObject U)
  have hj : e.hom ≫ openInclusion f = coordinateMorphism (openCoordinate U) := by
    apply MorphismProperty.Over.Hom.ext
    exact (spec_eval_eq_original_inclusion U).symm
  obtain ⟨β, hβ⟩ := exists_moving_action f g hf hg hfg (openCoordinate U)
    (openCoordinate_eval_isUnit U f le_rfl) e.hom hj
  have he : Function.Injective (P.transfer ((Cor.graphFunctor k).map e.hom)) :=
    (ConcreteCategory.bijective_of_isIso _).injective
  intro x y hxy
  apply he
  have hx := ConcreteCategory.congr_hom (hβ P hP) x
  have hy := ConcreteCategory.congr_hom (hβ P hP) y
  exact hx.trans ((congrArg (fun z => (P.transfer β) z) hxy).trans hy.symm)

/-- Literal inclusion of the original affine-line opens. -/
def originalOpenInclusion (U V : (line k).Opens) (hVU : V ≤ U) :
    openObject V ⟶ openObject U :=
  SmoothSite.homMk (Scheme.homOfLE (line k) hVU) (by
    change Scheme.homOfLE _ _ ≫ (U.ι ≫ _) = _
    rw [← Category.assoc, Scheme.homOfLE_ι]
    rfl)

/-- Restriction to any nonempty smaller open of the affine line is injective for an arbitrary
homotopy-invariant presheaf with transfers, including over finite fields. -/
theorem original_open_restriction_injective
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (U V : (line k).Opens) (hVU : V ≤ U) (hV : (V : Set (line k)).Nonempty) :
    Function.Injective (P.transfer ((Cor.graphFunctor k).map
      (originalOpenInclusion U V hVU))) := by
  obtain ⟨f, g, hf, hg, hfg, rfl, rfl⟩ :=
    exists_coprime_monic_open_presentation U V hVU hV
  exact principal_restriction_injective P hP f g hf hg hfg
    (hV.mono (PrimeSpectrum.basicOpen_mul_le_left f g))

end Motivic.PolynomialOpenSpans
