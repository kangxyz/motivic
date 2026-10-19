/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.FlatBaseChangeIdentity
public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.FlatBaseChangeLocalization
public import MotivicTest.TorQuotientFiniteness

/-!
# Successive principal-localization consumers for canonical Tor

The iterated localization is itself a localization of the original ring at the
product. The comparison equation uses the genuine scalar-extension associator.
A positive-degree consumer uses the actual nonzero Tor of the nonradical
integer quotient by four. Nonvanishing is asserted for the original Tor module.
-/

@[expose] public section

open CategoryTheory

universe u

namespace Motivic.MotivicTest.TorComparisonFlatBaseChangeComposition

variable {R : Type u} [CommRing R]

/-- The first genuine principal localization. -/
abbrev first (r : R) := Localization.Away r

/-- The second principal localization, at the actual image of a second element. -/
abbrev second (r s : R) := Localization.Away (algebraMap R (first r) s)

/-- The iterated target is an actual direct localization at the product. -/
theorem directProductLocalization (r s : R) : IsLocalization.Away (s * r) (second r s) :=
  inferInstance

/-- The composed restriction map is exactly the original-ring localization map. -/
theorem directScalarMap (r s : R) :
    (algebraMap (first r) (second r s)).comp (algebraMap R (first r)) =
      algebraMap R (second r s) :=
  (IsScalarTower.algebraMap_eq R (first r) (second r s)).symm

/-- Two successive principal restrictions equal direct restriction on all actual Tor degrees. -/
theorem successivePrincipal (r s : R) (M N : ModuleCat.{u} R) (n : ℕ) :
    (ModuleCat.extendScalarsComp (algebraMap R (first r))
      (algebraMap (first r) (second r s))).hom.app
        (((Tor (ModuleCat R) n).obj M).obj N) ≫
      (ModuleCat.extendScalars (algebraMap (first r) (second r s))).map
        (_root_.ModuleCat.TorComparison.flatBaseChangeTorIso (algebraMap R (first r))
          (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (first r) (.powers r)))
          M N n).hom ≫
      (_root_.ModuleCat.TorComparison.flatBaseChangeTorIso (algebraMap (first r) (second r s))
        (RingHom.flat_algebraMap_iff.mpr
          (IsLocalization.flat (second r s) (.powers (algebraMap R (first r) s))))
        ((ModuleCat.extendScalars (algebraMap R (first r))).obj M)
        ((ModuleCat.extendScalars (algebraMap R (first r))).obj N) n).hom =
      (_root_.ModuleCat.TorComparison.flatBaseChangeTorIso
        ((algebraMap (first r) (second r s)).comp (algebraMap R (first r)))
        ((RingHom.flat_algebraMap_iff.mpr
          (IsLocalization.flat (first r) (.powers r))).comp
          (RingHom.flat_algebraMap_iff.mpr
            (IsLocalization.flat (second r s) (.powers (algebraMap R (first r) s)))))
        M N n).hom ≫
      ((Tor (ModuleCat (second r s)) n).map
        ((ModuleCat.extendScalarsComp (algebraMap R (first r))
          (algebraMap (first r) (second r s))).hom.app M)).app
          ((ModuleCat.extendScalars
            ((algebraMap (first r) (second r s)).comp (algebraMap R (first r)))).obj N) ≫
      ((Tor (ModuleCat (second r s)) n).obj
        ((ModuleCat.extendScalars (algebraMap R (first r)) ⋙
          ModuleCat.extendScalars (algebraMap (first r) (second r s))).obj M)).map
          ((ModuleCat.extendScalarsComp (algebraMap R (first r))
            (algebraMap (first r) (second r s))).hom.app N) :=
  _root_.ModuleCat.TorComparison.flatBaseChangeTorIso_hom_comp _ _ _ _ M N n

/-- The concrete degree-one test has a genuinely nonzero starting Tor module. -/
theorem concreteHigherTorNonzero :
    ¬ Limits.IsZero (((Tor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ TorQuotientFiniteness.Q)).obj (ModuleCat.of ℤ TorQuotientFiniteness.Q)) :=
  TorQuotientFiniteness.higherTor_nonzero


/-- The comparison at three then five uses a proven nonzero, nonradical degree-one Tor. -/
theorem nonradicalTorOneSuccessive :
    let f := algebraMap ℤ (first (3 : ℤ))
    let g := algebraMap (first (3 : ℤ)) (second (3 : ℤ) 5)
    let M := ModuleCat.of ℤ TorQuotientFiniteness.Q
    ∃ (hf : f.Flat) (hg : g.Flat),
      ((ModuleCat.extendScalarsComp f g).hom.app (((Tor (ModuleCat ℤ) 1).obj M).obj M) ≫
        (ModuleCat.extendScalars g).map (_root_.ModuleCat.TorComparison.flatBaseChangeTorIso f hf M
            M 1).hom ≫
        (_root_.ModuleCat.TorComparison.flatBaseChangeTorIso g hg ((ModuleCat.extendScalars f).obj
            M)
          ((ModuleCat.extendScalars f).obj M) 1).hom =
      (_root_.ModuleCat.TorComparison.flatBaseChangeTorIso (g.comp f) (hf.comp hg) M M 1).hom ≫
        ((Tor (ModuleCat (second (3 : ℤ) 5)) 1).map
          ((ModuleCat.extendScalarsComp f g).hom.app M)).app
          ((ModuleCat.extendScalars (g.comp f)).obj M) ≫
        ((Tor (ModuleCat (second (3 : ℤ) 5)) 1).obj
          ((ModuleCat.extendScalars f ⋙ ModuleCat.extendScalars g).obj M)).map
          ((ModuleCat.extendScalarsComp f g).hom.app M)) ∧
      ¬ Limits.IsZero (((Tor (ModuleCat ℤ) 1).obj M).obj M) := by
  dsimp only
  refine ⟨RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat (first (3 : ℤ)) (.powers (3 : ℤ))),
    RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (second (3 : ℤ) 5)
        (.powers (algebraMap ℤ (first (3 : ℤ)) 5))), ?_, concreteHigherTorNonzero⟩
  exact _root_.ModuleCat.TorComparison.flatBaseChangeTorIso_hom_comp _ _ _ _ _ _ _

/-- The same nonzero degree-one Tor also satisfies the genuine scalar identity law. -/
theorem nonradicalTorOneIdentity :
    let M := ModuleCat.of ℤ TorQuotientFiniteness.Q
    (_root_.ModuleCat.TorComparison.flatBaseChangeTorIso (RingHom.id ℤ) (RingHom.Flat.id ℤ) M M
        1).hom ≫
        ((Tor (ModuleCat ℤ) 1).map ((ModuleCat.extendScalarsId ℤ).hom.app M)).app
          ((ModuleCat.extendScalars (RingHom.id ℤ)).obj M) ≫
        ((Tor (ModuleCat ℤ) 1).obj M).map ((ModuleCat.extendScalarsId ℤ).hom.app M) =
      (ModuleCat.extendScalarsId ℤ).hom.app (((Tor (ModuleCat ℤ) 1).obj M).obj M) :=
  _root_.ModuleCat.TorComparison.flatBaseChangeTorIso_hom_id _ _ _

end Motivic.MotivicTest.TorComparisonFlatBaseChangeComposition
