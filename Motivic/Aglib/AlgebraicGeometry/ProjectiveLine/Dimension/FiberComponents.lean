/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Fiber
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Dimension.FiniteFlatComponents

/-!
# Component dimension on the native projective-cover fiber

For a commutative ring `R : Type u`, schemes `C S : Scheme.{u}`, an actual
map `q : C ⟶ S`, a finite flat map `F : C ⟶ ProjectiveSpace R (ULift (Fin 2))`,
an isomorphism `e : S ≅ Spec R`, and the exact equation `F ≫ toSpec = q ≫ e.hom`,
every irreducible component of `q.fiber s` has dimension one. The coefficient
field is literally `S.residueField s`. Empty fibers are allowed; no reducedness,
connectedness, positive rank, or further coefficient restriction is assumed.

Intended upstream module:
`Aglib.AlgebraicGeometry.ProjectiveLine.Dimension.FiberComponents`.
Current direct consumer:
`Normalization.Compactification.RelativeAffineLine.CoefficientFiberDimension`.
The coordinate map comes from `ProjectiveLine.Fiber`. No new relative-dimension
object or standard-triple assembly is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RelativeProjectiveLine

variable (R : Type u) [CommRing R] {C S : Scheme.{u}}
  (q : C ⟶ S) (F : C ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))
  (e : S ≅ Spec (.of R))
  (hF : F ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)) = q ≫ e.hom)

include hF in
/-- Every component of the actual native fiber has dimension one. -/
theorem topologicalKrullDim_eq_one_of_mem_nativeFiberComponents
    [IsFinite F] [Flat F] (s : S) {Z : Set (q.fiber s)}
    (hZ : Z ∈ irreducibleComponents (q.fiber s)) :
    topologicalKrullDim Z = 1 := by
  exact topologicalKrullDim_eq_one_of_mem_irreducibleComponents_of_finite_flat
    (S.residueField s) (nativeFiberToProjectiveLine R q F e hF s) hZ

end AlgebraicGeometry.RelativeProjectiveLine
