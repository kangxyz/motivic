/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Sections.DivisorPairs.Serre
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.SupportRegularity

/-! # Global regularity of the original Serre section divisors

The existing finite-flat divisor package already records both the containment
of the whole zero scheme in the retained open and monicity there. These two
properties, rather than finite flatness alone, give global regularity of the
same dual functional.


Intended upstream module: `Aglib.AlgebraicGeometry.RelativeCurve.Sections.SerreDivisorRegularity`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.BoundarySectionRegularity`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.CoherentGraph

/-- The original finite-flat Serre section package supplies global monicity of
its original dual functional, without any further regularity hypothesis. -/
theorem SectionDivisorFiniteFlat.mono {C U S : Scheme.{u}}
    {q : C ⟶ S} {j : U ⟶ C} [IsOpenImmersion j]
    {L : LineBundle C} {s : SheafOfModules.unit C.ringCatSheaf ⟶ L.val}
    (h : SectionDivisorFiniteFlat q j L s) : Mono (sectionDualFunctional C L s) := by
  let φ := sectionDualFunctional C L s
  have : Mono (Hom.pullbackToUnit φ j) := h.2.2.2.2.1
  have : Mono ((Modules.pullback j).map φ) :=
    mono_of_mono_fac (show (Modules.pullback j).map φ ≫ (pullbackUnitIso j).hom =
      Hom.pullbackToUnit φ j from rfl)
  apply mono_of_zero_support_subset_range (dualLineBundle C L) φ j
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact h.2.2.1

end AlgebraicGeometry.Scheme.CoherentGraph
