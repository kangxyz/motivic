/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Diagonal.SmoothKoszul
public import Motivic.Algebra.Homology.KoszulFiniteSupportEuler

/-!
# Actual smooth diagonal Tor lengths on coefficient support

The actual diagonal kernel and the coefficient annihilator annihilate every
Tor module. Under explicit Noetherian, finite-generation, and Artinian-support
hypotheses, all these actual modules have finite length and finitely many
nonzero degrees. A local minimal-prime criterion gives a second sufficient
support condition. The genuine Tor Euler sum agrees with coefficient Koszul
Euler length; no proper intersection or correspondence cycle is inferred.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic.LengthEuler

universe u

namespace Motivic.Diagonal

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (x : X)
  (M : ModuleCat (ambientStalk f x))

/-- The actual diagonal kernel and coefficient support annihilate every actual Tor degree. -/
theorem support_le_annihilator_tor (n : ℕ) :
    RingHom.ker ((pullback.diagonal f).stalkMap x).hom ⊔
        Module.annihilator (ambientStalk f x) M ≤
      Module.annihilator (ambientStalk f x)
        (((Tor (ModuleCat (ambientStalk f x)) n).obj M).obj (sourceStalkModule f x)) := by
  rw [equations_kernel]
  exact (Koszul.support_le_annihilator_coefficient_homology M (equations f x) n).trans
    ((torIsoHomology f x M n).hom.hom.annihilator_le_of_injective
      ((ModuleCat.mono_iff_injective _).mp inferInstance))

variable [IsNoetherianRing (ambientStalk f x)] [Module.Finite (ambientStalk f x) M]

/-- Artinianness on actual diagonal coefficient support proves finite Koszul homology length. -/
theorem finiteHomology_of_artinian_support
    [IsArtinianRing ((ambientStalk f x) ⧸
      (RingHom.ker ((pullback.diagonal f).stalkMap x).hom ⊔
        Module.annihilator (ambientStalk f x) M))] :
    FiniteHomology (Koszul.coefficientComplex M (equations f x)) := by
  have : IsArtinianRing ((ambientStalk f x) ⧸
      (Ideal.ofList (equations f x) ⊔ Module.annihilator (ambientStalk f x) M)) := by
    rw [← equations_kernel]
    infer_instance
  exact Koszul.finiteHomology_of_artinian_support_quotient M (equations f x)

/-- Explicit Artinian support gives finite module lengths and degree support for actual Tor. -/
theorem finiteLengthSupport_tor_of_artinian_support
    [IsArtinianRing ((ambientStalk f x) ⧸
      (RingHom.ker ((pullback.diagonal f).stalkMap x).hom ⊔
        Module.annihilator (ambientStalk f x) M))] :
    FiniteLengthSupport (fun n =>
      ((Tor (ModuleCat (ambientStalk f x)) n).obj M).obj (sourceStalkModule f x)) :=
  (finiteHomology_of_artinian_support f x M).of_iso
    (fun n => (torIsoHomology f x M n).symm)

/-- Minimality at the actual local support gives finite module lengths and degree support. -/
theorem finiteLengthSupport_tor_of_mem_minimalPrimes_support
    (hm : IsLocalRing.maximalIdeal (ambientStalk f x) ∈
      (RingHom.ker ((pullback.diagonal f).stalkMap x).hom ⊔
        Module.annihilator (ambientStalk f x) M).minimalPrimes) :
    FiniteLengthSupport (fun n =>
      ((Tor (ModuleCat (ambientStalk f x)) n).obj M).obj (sourceStalkModule f x)) := by
  rw [equations_kernel] at hm
  exact (Koszul.finiteHomology_of_mem_minimalPrimes_support M (equations f x) hm).of_iso
    (fun n => (torIsoHomology f x M n).symm)

/-- With actual finite-length evidence, the Tor Euler sum equals coefficient Koszul Euler length. -/
theorem torEuler_eq_chainEuler_of_artinian_support
    [IsArtinianRing ((ambientStalk f x) ⧸
      (RingHom.ker ((pullback.diagonal f).stalkMap x).hom ⊔
        Module.annihilator (ambientStalk f x) M))] :
    signedLengthSum (fun n =>
      ((Tor (ModuleCat (ambientStalk f x)) n).obj M).obj (sourceStalkModule f x))
      (fun n => (-1 : ℤ) ^ n) (finiteLengthSupport_tor_of_artinian_support f x M) =
      chainEuler (Koszul.coefficientComplex M (equations f x))
        (finiteHomology_of_artinian_support f x M) :=
  signedLengthSum_eq_of_iso _ _ _ (fun n => torIsoHomology f x M n)

end Motivic.Diagonal
