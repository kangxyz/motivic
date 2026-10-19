/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Basic
public import Motivic.Aglib.CategoryTheory.Sites.Hypercohomology.FreeSheafMonomorphisms

/-!
# Free-sheaf monomorphisms on smooth sites
-/

@[expose] public noncomputable section

universe t v u

open CategoryTheory AlgebraicGeometry

namespace CategoryTheory.Sheaf.Hypercohomology
open _root_.AlgebraicGeometry.Scheme
section SmoothSite

variable {S : Scheme.{u}} {U X : SmoothSite S}

/-- An open immersion of underlying schemes is a monomorphism in the actual smooth site. -/
theorem smoothSite_mono_of_isOpenImmersion (j : U ⟶ X) [IsOpenImmersion j.left] :
    Mono j := by
  have : Mono ((SmoothSite.forgetScheme S).map j) := inferInstanceAs (Mono j.left)
  exact (SmoothSite.forgetScheme S).mono_of_mono_map this

/-- An open immersion in the smooth site induces a mono of actual free abelian sheaves. -/
theorem freeAbelianSheafFunctor_map_mono_of_isOpenImmersion
    (J : GrothendieckTopology (SmoothSite S))
    [HasSheafify J AddCommGrpCat.{max u t}]
    (j : U ⟶ X) [IsOpenImmersion j.left] :
    Mono ((freeAbelianSheafFunctor.{t, u, u + 1} J).map j) := by
  have := smoothSite_mono_of_isOpenImmersion j
  exact freeAbelianSheafFunctor_map_mono J j

end SmoothSite

end CategoryTheory.Sheaf.Hypercohomology
