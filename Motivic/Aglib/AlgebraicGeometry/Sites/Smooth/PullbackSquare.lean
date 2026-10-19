/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Pullbacks
public import Mathlib.CategoryTheory.Square

/-! # Extracted ordinary primitive with the original parameters and maps -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe w t u
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}}
  {U X V V' : SmoothSite S} (j : U ⟶ X) (p : V ⟶ X) [IsOpenImmersion j.left]

/-- The actual pullback square, not an abstract replacement diagram. -/
abbrev ordinaryPullbackSquare : Square (SmoothSite S) where
  f₁₂ := pullback.fst j p
  f₁₃ := pullback.snd j p
  f₂₄ := j
  f₃₄ := p
  fac := pullback.condition

end AlgebraicGeometry.Scheme.SmoothSite
