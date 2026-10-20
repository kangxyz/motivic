/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.ImageFamily
public import Lean.Util.CollectAxioms

/-! The family adjunction uses the original ordinary sheaf functors. -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
universe u
namespace MotivicTest.FiniteEtaleImageFamily
variable {I : Type u} {X : Scheme.{u}} (S : I → Scheme.{u}) (b : ∀ i, S i ⟶ X)

/-- The right adjoint is the actual product of ordinary direct images. -/
def actualFamilyAdjunction : familyInverseImage S b ⊣ productDirectImage S b :=
  familyImageAdjunction S b

open Lean in
run_cmd do
  for name in #[``actualFamilyAdjunction,
      ``_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.familyImageHomEquiv,
      ``_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.familyImageAdjunction] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual ordinary family adjunction: standard foundations only."

end MotivicTest.FiniteEtaleImageFamily
