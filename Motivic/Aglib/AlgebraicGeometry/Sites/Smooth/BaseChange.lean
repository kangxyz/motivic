/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Basic
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Arbitrary base change on smooth schemes

The functor `SmoothSite.baseChange f` is the actual fiber-product construction
for an arbitrary scheme morphism `f : T ⟶ S`. No smoothness, quasi-compactness
or finite-type hypothesis is imposed on `f`. Smoothness, separatedness and
quasi-compactness are instead preserved from the object being pulled back.

The identity and composition comparisons are natural isomorphisms with their
literal pullback projections identified. Specialization to field maps therefore
allows arbitrary extensions, including those not finitely generated over the
original field. This constructs change of ground field on the underlying
smooth categories; it does not yet construct the transfer or sheaf functors.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S T U : Scheme.{u}}

/-- Actual base change of smooth separated finite-type schemes along any base morphism. -/
def baseChange (f : T ⟶ S) : SmoothSite S ⥤ SmoothSite T :=
  MorphismProperty.Over.pullback smoothSeparatedFiniteType ⊤ f

@[simp]
theorem baseChange_obj_left (f : T ⟶ S) (X : SmoothSite S) :
    ((baseChange f).obj X).left = pullback X.hom f := rfl

@[simp]
theorem baseChange_obj_hom (f : T ⟶ S) (X : SmoothSite S) :
    ((baseChange f).obj X).hom = pullback.snd X.hom f := rfl

/-- The underlying map is the canonical pullback lift, with its original source projection. -/
theorem baseChange_map_left (f : T ⟶ S) {X Y : SmoothSite S} (g : X ⟶ Y) :
    ((baseChange f).map g).left =
      pullback.lift (pullback.fst X.hom f ≫ g.left) (pullback.snd X.hom f)
        (by simp [MorphismProperty.Over.w, pullback.condition]) := rfl

@[reassoc (attr := simp)]
theorem baseChange_map_fst (f : T ⟶ S) {X Y : SmoothSite S} (g : X ⟶ Y) :
    ((baseChange f).map g).left ≫ pullback.fst Y.hom f =
      pullback.fst X.hom f ≫ g.left := by
  rw [baseChange_map_left]
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem baseChange_map_snd (f : T ⟶ S) {X Y : SmoothSite S} (g : X ⟶ Y) :
    ((baseChange f).map g).left ≫ pullback.snd Y.hom f = pullback.snd X.hom f := by
  rw [baseChange_map_left]
  exact pullback.lift_snd _ _ _

/-- The base-change square is a genuine pullback of schemes. -/
theorem baseChange_isPullback (f : T ⟶ S) (X : SmoothSite S) :
    IsPullback (pullback.fst X.hom f) ((baseChange f).obj X).hom X.hom f :=
  IsPullback.of_hasPullback _ _

/-- Forgetting to schemes, the projection to the original object is natural. -/
def baseChangeProjection (f : T ⟶ S) :
    baseChange f ⋙ forgetScheme T ⟶ forgetScheme S where
  app X := pullback.fst X.hom f
  naturality _ _ g := baseChange_map_fst f g

set_option backward.isDefEq.respectTransparency false in
/-- Base change along the identity is naturally isomorphic to the identity functor. -/
def baseChangeId (S : Scheme.{u}) : baseChange (𝟙 S) ≅ 𝟭 (SmoothSite S) :=
  NatIso.ofComponents
    (fun X ↦ MorphismProperty.Over.isoMk (asIso (pullback.fst X.hom (𝟙 S)))
      (by simpa using (pullback.condition (f := X.hom) (g := 𝟙 S))))
    (fun g ↦ by
      apply MorphismProperty.Over.Hom.ext
      exact baseChange_map_fst (𝟙 S) g)

/-- The identity comparison is literally the first pullback projection. -/
@[simp]
theorem baseChangeId_hom_left (S : Scheme.{u}) (X : SmoothSite S) :
    ((baseChangeId S).hom.app X).left = pullback.fst X.hom (𝟙 S) := rfl

/-- Base change reverses composition, with the canonical iterated-pullback isomorphism. -/
def baseChangeComp (f : U ⟶ T) (g : T ⟶ S) :
    baseChange (f ≫ g) ≅ baseChange g ⋙ baseChange f :=
  MorphismProperty.Over.pullbackComp f g

@[reassoc, simp]
theorem baseChangeComp_hom_fst_fst (f : U ⟶ T) (g : T ⟶ S) (X : SmoothSite S) :
    ((baseChangeComp f g).hom.app X).left ≫
      pullback.fst (pullback.snd X.hom g) f ≫ pullback.fst X.hom g =
        pullback.fst X.hom (f ≫ g) :=
  MorphismProperty.Over.pullbackComp_left_fst_fst f g X

@[reassoc (attr := simp)]
theorem baseChangeComp_hom_snd (f : U ⟶ T) (g : T ⟶ S) (X : SmoothSite S) :
    ((baseChangeComp f g).hom.app X).left ≫ pullback.snd (pullback.snd X.hom g) f =
      pullback.snd X.hom (f ≫ g) :=
  MorphismProperty.Over.w _

/-- The smooth category over a field, always using that field as its own ground field. -/
abbrev overField (K : Type u) [Field K] := SmoothSite (Spec (CommRingCat.of K))

/-- Arbitrary field homomorphisms induce actual base-change functors. -/
def fieldBaseChange {K L : Type u} [Field K] [Field L] (φ : K →+* L) :
    overField K ⥤ overField L :=
  baseChange (Spec.map (CommRingCat.ofHom φ))

@[simp]
theorem fieldBaseChange_obj_hom {K L : Type u} [Field K] [Field L] (φ : K →+* L)
    (X : overField K) :
    ((fieldBaseChange φ).obj X).hom =
      pullback.snd X.hom (Spec.map (CommRingCat.ofHom φ)) := rfl

/-- The field identity has the same canonical identity comparison. -/
def fieldBaseChangeId (K : Type u) [Field K] :
    fieldBaseChange (RingHom.id K) ≅ 𝟭 (overField K) := by
  simpa only [fieldBaseChange, CommRingCat.ofHom_id, Spec.map_id] using
    baseChangeId (Spec (CommRingCat.of K))

/-- Successive arbitrary field extensions agree with their composite by actual base change. -/
def fieldBaseChangeComp {K L M : Type u} [Field K] [Field L] [Field M]
    (φ : K →+* L) (ψ : L →+* M) :
    fieldBaseChange (ψ.comp φ) ≅ fieldBaseChange φ ⋙ fieldBaseChange ψ :=
  MorphismProperty.Over.pullbackComp
    (Spec.map (CommRingCat.ofHom ψ)) (Spec.map (CommRingCat.ofHom φ))
    (Spec.map (CommRingCat.ofHom (ψ.comp φ))) (by rw [← Spec.map_comp]; rfl)

end AlgebraicGeometry.Scheme.SmoothSite
