/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.BaseChange

/-!
# Consumers of the actual smooth-category base change

The base morphisms in these tests are completely arbitrary. In particular the
field-map consumer has no finite-generation or finite-type hypothesis. The
checks expose the underlying schemes and maps, not just abstract isomorphisms.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open  _root_.AlgebraicGeometry.Scheme.SmoothSite

universe u

noncomputable section

namespace Motivic.MotivicTest.SmoothSite

variable {S T U : Scheme.{u}}

example (X : SmoothSite S) : Smooth X.hom := inferInstance

example (X : SmoothSite S) : LocallyOfFiniteType X.hom := inferInstance

example (X : SmoothSite S) : IsSeparated X.hom := inferInstance

example (X : SmoothSite S) : QuasiCompact X.hom := inferInstance

example (S : Scheme.{u}) : (forget S).Full := inferInstance

example (S : Scheme.{u}) : (forget S).Faithful := inferInstance

example (f : T ⟶ S) (X : SmoothSite S) :
    Smooth ((baseChange f).obj X).hom := inferInstance

example (f : T ⟶ S) (X : SmoothSite S) :
    ((baseChange f).obj X).left = pullback X.hom f := rfl

example (f : T ⟶ S) {X Y : SmoothSite S} (g : X ⟶ Y) :
    ((baseChange f).map g).left ≫ pullback.fst Y.hom f =
      pullback.fst X.hom f ≫ g.left := baseChange_map_fst f g

example (S : Scheme.{u}) (X : SmoothSite S) :
    ((baseChangeId S).hom.app X).left = pullback.fst X.hom (𝟙 S) := rfl

example (f : U ⟶ T) (g : T ⟶ S) (X : SmoothSite S) :
    ((baseChangeComp f g).hom.app X).left ≫
      pullback.fst (pullback.snd X.hom g) f ≫ pullback.fst X.hom g =
        pullback.fst X.hom (f ≫ g) := baseChangeComp_hom_fst_fst f g X

example {K L : Type u} [Field K] [Field L] (φ : K →+* L) (X : overField K) :
    ((fieldBaseChange φ).obj X).hom =
      pullback.snd X.hom (Spec.map (CommRingCat.ofHom φ)) := rfl

end Motivic.MotivicTest.SmoothSite
