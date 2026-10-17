/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.RingTheory.Length

/-!
# Finite local lengths at generic points

For a locally Noetherian scheme the actual local ring at the generic point of
any irreducible component is Artinian, and its length as a module over itself
is finite and positive. On a reduced scheme that length is one. No replacement
of the local ring by the residue field is made in the nonreduced case.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace Motivic

variable {X : Scheme.{u}}

/-- A generic point of an irreducible component has coheight zero. -/
theorem coheight_eq_zero_of_mem_genericPoints (x : X) (hx : x ∈ genericPoints X) :
    Order.coheight x = 0 := by
  apply Order.coheight_eq_zero.mpr
  intro y hy
  apply Scheme.le_iff_specializes.mpr
  apply specializes_iff_closure_subset.mpr
  exact hx.2 isIrreducible_singleton.closure
    (Scheme.le_iff_specializes.mp hy).closure_subset

/-- The actual generic local ring of a locally Noetherian scheme is Artinian. -/
theorem isArtinianRing_stalk_of_mem_genericPoints [IsLocallyNoetherian X]
    (x : X) (hx : x ∈ genericPoints X) : IsArtinianRing (X.presheaf.stalk x) := by
  apply isArtinianRing_iff_krullDimLE_zero.mpr
  apply krullDimLE_of_coheight_le
  exact le_of_eq (coheight_eq_zero_of_mem_genericPoints x hx)

/-- Generic local length is genuinely finite, before conversion to a natural number. -/
theorem stalk_length_ne_top_of_mem_genericPoints [IsLocallyNoetherian X]
    (x : X) (hx : x ∈ genericPoints X) :
    Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) ≠ ⊤ := by
  let := isArtinianRing_stalk_of_mem_genericPoints x hx
  exact Module.length_ne_top

/-- Every finite module over an actual generic local ring has finite length. -/
theorem stalk_module_length_ne_top_of_mem_genericPoints [IsLocallyNoetherian X]
    (x : X) (hx : x ∈ genericPoints X) (M : Type v) [AddCommGroup M]
    [Module (X.presheaf.stalk x) M] [Module.Finite (X.presheaf.stalk x) M] :
    Module.length (X.presheaf.stalk x) M ≠ ⊤ := by
  let := isArtinianRing_stalk_of_mem_genericPoints x hx
  exact Module.length_ne_top

/-- The natural-valued generic local length, measured on the original structure sheaf.
The following finiteness theorem shows that `ENat.toNat` loses no information in
locally Noetherian applications. Outside that scope an infinite length is sent to zero. -/
noncomputable def genericMultiplicity (x : genericPoints X) : ℕ :=
  (Module.length (X.presheaf.stalk x.val) (X.presheaf.stalk x.val)).toNat

/-- The natural multiplicity recovers the literal finite extended-natural length. -/
theorem genericMultiplicity_eq_length [IsLocallyNoetherian X] (x : genericPoints X) :
    (genericMultiplicity x : ℕ∞) =
      Module.length (X.presheaf.stalk x.val) (X.presheaf.stalk x.val) :=
  ENat.natCast_toNat (stalk_length_ne_top_of_mem_genericPoints x.val x.property)

/-- Every irreducible component occurs with positive generic local multiplicity. -/
theorem genericMultiplicity_pos [IsLocallyNoetherian X] (x : genericPoints X) :
    0 < genericMultiplicity x :=
  ENat.toNat_pos Module.length_pos.ne'
    (stalk_length_ne_top_of_mem_genericPoints x.val x.property)

/-- On a reduced scheme the actual generic stalk has module length one. -/
theorem stalk_length_eq_one_of_mem_genericPoints [IsReduced X]
    (x : X) (hx : x ∈ genericPoints X) :
    Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) = 1 := by
  let := (isField_stalk_of_closure_mem_irreducibleComponents X x hx).toField
  exact Module.length_eq_one _ _

/-- Reduced components have multiplicity one. -/
@[simp]
theorem genericMultiplicity_eq_one [IsReduced X] (x : genericPoints X) :
    genericMultiplicity x = 1 := by
  simp [genericMultiplicity, stalk_length_eq_one_of_mem_genericPoints x.val x.property]

end Motivic
