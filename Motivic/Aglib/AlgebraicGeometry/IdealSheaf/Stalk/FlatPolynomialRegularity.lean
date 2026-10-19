/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.IdealSheaf.Stalk.ClosedQuotientLinearEquiv
public import Motivic.Aglib.RingTheory.Multiplicity.Cartier.CutLength
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flat fiber parameters on actual closed-support stalk quotients

Flatness of a closed support over the affine line makes the literal fiber
parameter regular on its ambient ideal-sheaf stalk quotient. The scalar is
transported through the actual composite stalk map; the ambient scheme is
not assumed reduced, integral, or flat.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped Polynomial

universe u

namespace AlgebraicGeometry

/-- The literal polynomial fiber parameter is regular in every stalk of a
scheme flat over the affine line. -/
theorem flat_polynomial_fiber_stalk_isSMulRegular
    {k : Type u} [CommRing k] {C : Scheme.{u}}
    (g : C ⟶ Spec (.of k[X])) [Flat g] (a : k) (c : C) :
    IsSMulRegular (C.presheaf.stalk c)
      (g.stalkMap c (StructureSheaf.toStalk k[X] (g c)
        (Polynomial.X - Polynomial.C a))) := by
  let φ := (g.stalkMap c).hom.comp (StructureSheaf.toStalk k[X] (g c)).hom
  let : Algebra k[X] (C.presheaf.stalk c) := φ.toAlgebra
  have hloc : (StructureSheaf.toStalk k[X] (g c)).hom.Flat := by
    let : Algebra k[X] ((Spec (.of k[X])).presheaf.stalk (g c)) :=
      (StructureSheaf.toStalk k[X] (g c)).hom.toAlgebra
    have : IsLocalization.AtPrime ((Spec (.of k[X])).presheaf.stalk (g c))
        (g c).asIdeal :=
      inferInstanceAs (IsLocalization.AtPrime
        ((Spec.structureSheaf k[X]).presheaf.stalk (g c)) (g c).asIdeal)
    exact IsLocalization.flat _ (g c).asIdeal.primeCompl
  have : Module.Flat k[X] (C.presheaf.stalk c) :=
    hloc.comp (Flat.stalkMap g c)
  exact IsSMulRegular.polynomial_fiber_of_flat a

/-- Flatness of the actual closed support suffices for regularity of the
original ambient fiber scalar on the literal ideal-sheaf stalk quotient. -/
theorem closedImmersion_polynomial_fiber_isSMulRegular
    {k : Type u} [CommRing k] {C P : Scheme.{u}}
    (f : P ⟶ Spec (.of k[X])) (j : C ⟶ P) [IsClosedImmersion j]
    [Flat (j ≫ f)] (a : k) (c : C) :
    IsSMulRegular ((P.presheaf.stalk (j c)) ⧸ j.ker.stalk (j c))
      (f.stalkMap (j c) (StructureSheaf.toStalk k[X] (f (j c))
        (Polynomial.X - Polynomial.C a))) := by
  let e := Scheme.Hom.closedStalkQuotientLinearEquiv j c
  apply (e.isSMulRegular_congr _).mpr
  change IsSMulRegular (C.presheaf.stalk c)
    (j.stalkMap c (f.stalkMap (j c) (StructureSheaf.toStalk k[X] (f (j c))
      (Polynomial.X - Polynomial.C a))))
  have h := flat_polynomial_fiber_stalk_isSMulRegular (j ≫ f) a c
  rw [Scheme.Hom.stalkMap_comp] at h
  convert! h using 1

end AlgebraicGeometry
