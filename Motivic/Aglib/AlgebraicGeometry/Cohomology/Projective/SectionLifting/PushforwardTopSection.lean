/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Sections.GlobalUnitPair

/-! Literal transport of whole-boundary sections to the double direct image. -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph
/-- A global section of the original boundary sheaf, in the section producer's native type. -/
def pushforwardTopSection {P C W : Scheme.{u}} (a : C ⟶ P) (z : W ⟶ C)
    (Q : W.Modules) (σ : Γ(Q, ⊤)) :
    Γ((Modules.pushforward a).obj ((Modules.pushforward z).obj Q), ⊤) :=
  Q.presheaf.map (eqToHom (show z ⁻¹ᵁ (a ⁻¹ᵁ ⊤) = ⊤ by simp)).op σ
end AlgebraicGeometry.Scheme.CoherentGraph
