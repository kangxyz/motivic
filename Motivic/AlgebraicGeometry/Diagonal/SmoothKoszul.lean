/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Diagonal.Smooth
public import Motivic.Algebra.Homology.KoszulFiniteTor
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Finite Koszul resolutions and actual Tor of smooth diagonal stalks

The proved smooth-diagonal theorem supplies a regular list in the actual
ambient stalk. The diagonal stalk map is surjective, so its generated-ideal
quotient is identified with the actual source stalk as a module over the
ambient stalk. The genuine finite Koszul complex therefore resolves that
source stalk and computes categorical Tor with arbitrary coefficients.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.Diagonal

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)

/-- The actual ambient local ring at a point of the scheme diagonal. -/
abbrev ambientStalk := (pullback f f).presheaf.stalk (pullback.diagonal f x)

/-- The source stalk with its scalar action induced by the actual diagonal stalk map. -/
def sourceStalkModule : ModuleCat (ambientStalk f x) :=
  let := ((pullback.diagonal f).stalkMap x).hom.toAlgebra
  ModuleCat.of (ambientStalk f x) (X.presheaf.stalk x)

variable [Smooth f]

/-- A genuine regular list obtained from the proved smooth-chart construction. -/
def equations : List (ambientStalk f x) :=
  (exists_regular_kernel_of_smooth f x).choose

/-- The chosen equations are regular on the ambient stalk. -/
theorem equations_isRegular : IsRegular (ambientStalk f x) (equations f x) :=
  (exists_regular_kernel_of_smooth f x).choose_spec.1

/-- The chosen equations generate the literal kernel of the diagonal stalk map. -/
theorem equations_kernel :
    RingHom.ker ((pullback.diagonal f).stalkMap x).hom = Ideal.ofList (equations f x) :=
  (exists_regular_kernel_of_smooth f x).choose_spec.2

set_option backward.isDefEq.respectTransparency false in
/-- The quotient by the actual regular equations is the actual source stalk module. -/
def quotientStalkIso :
    ModuleCat.of (ambientStalk f x)
      ((ambientStalk f x) ⧸ Ideal.ofList (equations f x)) ≅ sourceStalkModule f x := by
  let := ((pullback.diagonal f).stalkMap x).hom.toAlgebra
  let μ : ambientStalk f x →ₐ[ambientStalk f x] X.presheaf.stalk x :=
    Algebra.ofId _ _
  have hμ : Function.Surjective μ := (pullback.diagonal f).stalkMap_surjective x
  have hk : Ideal.ofList (equations f x) = RingHom.ker μ := (equations_kernel f x).symm
  exact ((Ideal.quotientEquivAlgOfEq (ambientStalk f x) hk).trans
    (Ideal.quotientKerAlgEquivOfSurjective hμ)).toLinearEquiv.toModuleIso

/-- The quotient comparison sends an ambient element to its actual diagonal stalk image. -/
@[simp]
theorem quotientStalkIso_mk (a : ambientStalk f x) :
    (quotientStalkIso f x).hom (Ideal.Quotient.mk (Ideal.ofList (equations f x)) a) =
      (pullback.diagonal f).stalkMap x a := rfl

/-- A finite projective resolution of the actual source stalk over the actual ambient stalk. -/
def projectiveResolution : ProjectiveResolution (sourceStalkModule f x) where
  complex := Koszul.chainComplex (equations f x)
  π := Koszul.idealAugmentation (equations f x) ≫
    (ChainComplex.single₀ (ModuleCat (ambientStalk f x))).map (quotientStalkIso f x).hom
  quasiIso := by
    have := Koszul.idealAugmentation_quasiIso_of_weaklyRegular (equations f x)
      (equations_isRegular f x).toIsWeaklyRegular
    infer_instance

@[simp]
theorem projectiveResolution_complex :
    (projectiveResolution f x).complex = Koszul.chainComplex (equations f x) := rfl

/-- The constructed resolution has no terms above its finite coordinate length. -/
theorem projectiveResolution_isZero_X (n : ℕ) (hn : (equations f x).length < n) :
    IsZero ((projectiveResolution f x).complex.X n) :=
  Koszul.isZero_X (equations f x) n hn

/-- Actual categorical Tor with the diagonal source stalk is coefficient Koszul homology. -/
def torIsoHomology (M : ModuleCat (ambientStalk f x)) (n : ℕ) :
    ((Tor (ModuleCat (ambientStalk f x)) n).obj M).obj (sourceStalkModule f x) ≅
      (Koszul.coefficientComplex M (equations f x)).homology n :=
  ((Tor (ModuleCat (ambientStalk f x)) n).obj M).mapIso (quotientStalkIso f x).symm ≪≫
    Koszul.finiteTorIsoHomology M (equations f x)
      (equations_isRegular f x).toIsWeaklyRegular n

/-- For arbitrary coefficient modules, diagonal Tor vanishes above the coordinate length. -/
theorem isZero_tor_above_length (M : ModuleCat (ambientStalk f x)) (n : ℕ)
    (hn : (equations f x).length < n) :
    IsZero (((Tor (ModuleCat (ambientStalk f x)) n).obj M).obj (sourceStalkModule f x)) :=
  (HomologicalComplex.ExactAt.of_isZero
    (Koszul.coefficient_isZero_X M (equations f x) n hn)).isZero_homology.of_iso
      (torIsoHomology f x M n)

end Motivic.Diagonal
