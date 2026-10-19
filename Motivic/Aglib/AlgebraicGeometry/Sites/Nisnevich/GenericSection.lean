/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Basic
public import Mathlib.AlgebraicGeometry.SpreadingOut

/-!
# A genuine section of a Nisnevich cover near the generic point

Over an integral scheme, a singleton Nisnevich cover lifts the spectrum of the
actual generic stalk. Finite-type spreading then produces a section on an open
neighborhood of the generic point, with its original equation over the base.
This is geometric spreading of a scheme morphism, not a coefficient extension
or a whole-cylinder lifting theorem.


Intended upstream module: `Aglib.AlgebraicGeometry.Sites.Nisnevich.GenericSection`.
Incoming project consumers: `Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.MonicRefinement`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Nisnevich

/-- A genuine singleton Nisnevich cover of an integral scheme has a section on
an open neighborhood of its generic point. The original covering map appears
in the literal section equation; its finite-type hypothesis follows from étaleness. -/
theorem exists_generic_open_section
    {X Y : Scheme.{u}} [IsIntegral X] (q : Y ⟶ X)
    (hq : Presieve.singleton q ∈ _root_.AlgebraicGeometry.Nisnevich.precoverage X) :
    ∃ (U : X.Opens), genericPoint X ∈ U ∧
      ∃ s : U.toScheme ⟶ Y, s ≫ q = U.ι := by
  let : Etale q := (mem_precoverage_iff.mp hq).1 q (Presieve.singleton_self q)
  obtain ⟨Z, f, hf, φ, hφ⟩ := mem_fieldLiftingPrecoverage_iff.mp hq.2
    X.functionField (X.fromSpecStalk (genericPoint X))
  cases hf
  obtain ⟨U, hU, s, _, hs⟩ := spread_out_of_isGermInjective' (𝟙 X) q φ
    (by simpa only [Category.comp_id] using hφ)
  exact ⟨U, hU, s, by simpa only [Category.comp_id] using hs⟩

end AlgebraicGeometry.Nisnevich
