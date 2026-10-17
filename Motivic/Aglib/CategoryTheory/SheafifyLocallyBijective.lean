/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Comparing sheafification with a locally bijective map

A locally bijective morphism from a presheaf to a sheaf identifies its target
with ordinary sheafification, provided the topology's local equivalences are
exactly the locally bijective maps. The resulting isomorphism is the canonical
`sheafifyLift`, so its compatibility with the sheafification unit is retained.
-/

@[expose] public section

universe u v w u' v'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A : Type u'} [Category.{v'} A] {FA : A → A → Type*} {CA : A → Type w}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
  [HasWeakSheafify J A] [J.WEqualsLocallyBijective A]
  {P Q : Cᵒᵖ ⥤ A}

/-- A locally bijective map to a sheaf presents its target as the ordinary
sheafification, via the canonical lift of that map. -/
theorem isIso_sheafifyLift_of_isLocallyBijective
    (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    [Presheaf.IsLocallyInjective J η] [Presheaf.IsLocallySurjective J η] :
    IsIso (sheafifyLift J η hQ) := by
  let φ : (presheafToSheaf J A).obj P ⟶ ⟨Q, hQ⟩ :=
    ⟨sheafifyLift J η hQ⟩
  have : IsIso φ := by
    apply (J.W_sheafToPresheaf_map_iff_isIso φ).mp
    change J.W (sheafifyLift J η hQ)
    rw [← (J.W).precomp_iff _ _ (J.W_toSheafify P), toSheafify_sheafifyLift]
    exact J.W_of_isLocallyBijective η
  exact inferInstanceAs (IsIso ((sheafToPresheaf J A).map φ))

end CategoryTheory
