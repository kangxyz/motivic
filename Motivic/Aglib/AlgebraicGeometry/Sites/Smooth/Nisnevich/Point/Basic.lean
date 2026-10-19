/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Sites.Point.OfIsCofiltered

/-!
# Nisnevich points of the smooth site

An actual point `x` of a smooth scheme `X` determines the category of étale
neighborhoods equipped with a lift of the canonical map `Spec κ(x) ⟶ X`.
We restrict to neighborhoods which remain smooth, separated and quasi-compact
over the affine base. This full subcategory is weakly initial, by choosing an
affine open through the chosen point. Its cofilteredness therefore follows from
the finite limits in the small étale category, including actual equalizers.

The point is constructed with Mathlib's existing cofiltered-point API. Its
presheaf fiber is the colimit of the actual restriction maps on these
neighborhoods, with arbitrary coefficient categories admitting the indicated
colimits. No separable closure or algebraic henselization construction is used.

This does not construct the finite-correspondence action on MVW's closed-point
envelope, identify that envelope with a product of skyscrapers, or assert
acyclicity of the underlying ordinary sheaf of a transfer-injective.

This geometric consumer depends on the existing `SmoothSiteNisnevich` module
and uses its native `Motivic.SmoothSite` namespace. Its location under
`Motivic/Aglib` does not make it a standalone upstream extraction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} (X : SmoothSite S) (x : X.left)

/-- Étale neighborhoods with a specified lift of the canonical residue-field point. -/
abbrev PointedEtaleNeighborhood :=
  (Scheme.Etale.forget X.left ⋙
    coyoneda.obj (op (Over.mk (X.left.fromSpecResidueField x)))).Elements

instance : IsCofiltered (PointedEtaleNeighborhood X x) :=
  Functor.isCofiltered_elements _

/-- The condition that a pointed neighborhood is still an object of the smooth site. -/
def smoothNeighborhoodProperty : ObjectProperty (PointedEtaleNeighborhood X x) :=
  fun N ↦ smoothSeparatedFiniteType (N.obj.hom ≫ X.hom)

/-- The actual pointed étale neighborhoods inside the smooth finite-type site. -/
abbrev NisnevichNeighborhood := (smoothNeighborhoodProperty X x).FullSubcategory

set_option backward.isDefEq.respectTransparency false in
/-- Every pointed étale neighborhood admits an affine pointed refinement in the smooth site. -/
theorem exists_smoothNeighborhood_refinement [IsAffine S] (N : PointedEtaleNeighborhood X x) :
    ∃ M : NisnevichNeighborhood X x,
      Nonempty ((smoothNeighborhoodProperty X x).ι.obj M ⟶ N) := by
  let y : Spec (X.left.residueField x) ⟶ N.obj.left := N.val.left
  obtain ⟨R, j, _, hj, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := y.base default) (U := ⊤) (by simp)
  have hy : Set.range y ⊆ Set.range j := by
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a default]
  let y' := IsOpenImmersion.lift j y hy
  have hy' : y' ≫ j = y := IsOpenImmersion.lift_fac j y hy
  let M : PointedEtaleNeighborhood X x :=
    Functor.elementsMk _ (Scheme.Etale.mk (j ≫ N.obj.hom))
      (Over.homMk y' (by simpa [← Category.assoc, hy', y] using Over.w N.val))
  have hM : smoothNeighborhoodProperty X x M := by
    change smoothSeparatedFiniteType ((j ≫ N.obj.hom) ≫ X.hom)
    have : IsAffineHom ((j ≫ N.obj.hom) ≫ X.hom) := isAffineHom_of_isAffine (Y := S) _
    exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  refine ⟨⟨M, hM⟩, ⟨Functor.Elements.homMk
    (MorphismProperty.Over.homMk j rfl) ?_⟩⟩
  apply Over.OverMorphism.ext
  exact hy'

instance [IsAffine S] : IsCofiltered (NisnevichNeighborhood X x) :=
  IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful
    (smoothNeighborhoodProperty X x).ι (exists_smoothNeighborhood_refinement X x)

set_option backward.isDefEq.respectTransparency false in
/-- Forget a pointed neighborhood to its actual object of the smooth site. -/
def nisnevichNeighborhoodFunctor : NisnevichNeighborhood X x ⥤ SmoothSite S where
  obj N := MorphismProperty.Over.mk ⊤ (N.obj.obj.hom ≫ X.hom) N.property
  map {N M} f := homMk f.hom.hom.left (by
    change f.hom.hom.left ≫ (M.obj.obj.hom ≫ X.hom) = N.obj.obj.hom ≫ X.hom
    rw [← Category.assoc, MorphismProperty.Over.w])

@[simp]
theorem nisnevichNeighborhoodFunctor_obj_left (N : NisnevichNeighborhood X x) :
    ((nisnevichNeighborhoodFunctor X x).obj N).left = N.obj.obj.left := rfl

@[simp]
theorem nisnevichNeighborhoodFunctor_map_left {N M : NisnevichNeighborhood X x}
    (f : N ⟶ M) : ((nisnevichNeighborhoodFunctor X x).map f).left = f.hom.hom.left := rfl

set_option backward.isDefEq.respectTransparency false in
/-- A Nisnevich cover lifts after an actual pointed étale pullback refinement. -/
theorem nisnevichNeighborhood_cover_lifting
    {Y : SmoothSite S} (R : Sieve Y) (hR : R ∈ nisnevichTopology S Y)
    {N : NisnevichNeighborhood X x} (f : (nisnevichNeighborhoodFunctor X x).obj N ⟶ Y) :
    ∃ (V : SmoothSite S) (g : V ⟶ Y) (_ : R g)
      (M : NisnevichNeighborhood X x) (q : M ⟶ N)
        (a : (nisnevichNeighborhoodFunctor X x).obj M ⟶ V),
          a ≫ g = (nisnevichNeighborhoodFunctor X x).map q ≫ f := by
  obtain ⟨Q, hQ, hQR⟩ := mem_nisnevichTopology_iff.mp hR
  obtain ⟨ι, V, g, rfl⟩ := Q.exists_eq_ofArrows
  have hQ' : Presieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (g i).left) ∈
      Nisnevich.precoverage Y.left := by
    have h := mem_nisnevichPrecoverage_iff.mp hQ
    rw [Presieve.map_ofArrows] at h
    exact h
  obtain ⟨_, _, ⟨i⟩, y, hy⟩ := Nisnevich.mem_fieldLiftingPrecoverage_iff.mp hQ'.2
    (X.left.residueField x) (N.obj.val.left ≫ f.left)
  have : Etale (g i).left := etale_of_mem_nisnevichPrecoverage hQ ⟨i⟩
  let t := pullback.lift y N.obj.val.left hy
  let M₀ : PointedEtaleNeighborhood X x :=
    Functor.elementsMk _ (Scheme.Etale.mk
      (pullback.snd (g i).left f.left ≫ N.obj.obj.hom))
      (Over.homMk t (by
        change t ≫ (pullback.snd (g i).left f.left ≫ N.obj.obj.hom) = _
        rw [← Category.assoc, pullback.lift_snd]
        exact Over.w N.obj.val))
  have hM : smoothNeighborhoodProperty X x M₀ := by
    change smoothSeparatedFiniteType
      ((pullback.snd (g i).left f.left ≫ N.obj.obj.hom) ≫ X.hom)
    rw [Category.assoc]
    exact (etalePullback (g i) f).prop
  let M : NisnevichNeighborhood X x := ⟨M₀, hM⟩
  let q : M ⟶ N := ObjectProperty.homMk (Functor.Elements.homMk
    (MorphismProperty.Over.homMk (pullback.snd (g i).left f.left) rfl) (by
      apply Over.OverMorphism.ext
      exact pullback.lift_snd y N.obj.val.left hy))
  let a : (nisnevichNeighborhoodFunctor X x).obj M ⟶ V i :=
    homMk (pullback.fst (g i).left f.left) (by
      change pullback.fst (g i).left f.left ≫ (V i).hom =
        (pullback.snd (g i).left f.left ≫ N.obj.obj.hom) ≫ X.hom
      rw [Category.assoc, ← MorphismProperty.Over.w (g i), ← Category.assoc,
        pullback.condition, Category.assoc, MorphismProperty.Over.w f]
      rfl)
  refine ⟨V i, g i, hQR _ _ ⟨i⟩, M, q, a, ?_⟩
  apply MorphismProperty.Over.Hom.ext
  exact pullback.condition

instance : InitiallySmall.{u + 1} (NisnevichNeighborhood X x) :=
  initiallySmall_of_essentiallySmall _

/-- The Nisnevich point determined by the canonical residue-field point of `X`.
Its fiber uses the existing cofiltered-colimit point constructor. -/
def nisnevichPoint [IsAffine S] : (nisnevichTopology S).Point.{u + 1} :=
  GrothendieckTopology.Point.ofIsCofiltered.{u + 1}
    (nisnevichNeighborhoodFunctor X x)
    (fun {_} R hR {_} f ↦ nisnevichNeighborhood_cover_lifting X x R hR f)

section Fiber

variable [IsAffine S] {A : Type v} [Category.{w} A]
  [HasColimitsOfSize.{u + 1, u + 1} A]

/-- The actual point fiber with its canonical maps from pointed-neighborhood sections. -/
def nisnevichPointFiberCocone (F : (SmoothSite S)ᵒᵖ ⥤ A) :
    Cocone ((nisnevichNeighborhoodFunctor X x).op ⋙ F) :=
  GrothendieckTopology.Point.presheafFiberOfIsCofilteredCocone.{u + 1}
    (nisnevichNeighborhoodFunctor X x)
    (fun {_} R hR {_} f ↦ nisnevichNeighborhood_cover_lifting X x R hR f) F

@[simp]
theorem nisnevichPointFiberCocone_pt (F : (SmoothSite S)ᵒᵖ ⥤ A) :
    (nisnevichPointFiberCocone X x F).pt = (nisnevichPoint X x).presheafFiber.obj F := rfl

/-- The ordinary presheaf fiber is the colimit of the actual neighborhood restrictions. -/
def isColimitNisnevichPointFiberCocone (F : (SmoothSite S)ᵒᵖ ⥤ A) :
    IsColimit (nisnevichPointFiberCocone X x F) :=
  GrothendieckTopology.Point.isColimitPresheafFiberOfIsCofilteredCocone.{u + 1}
    (nisnevichNeighborhoodFunctor X x)
    (fun {_} R hR {_} f ↦ nisnevichNeighborhood_cover_lifting X x R hR f) F

/-- Compatibility with the original maps between coefficient presheaves. -/
@[reassoc]
theorem nisnevichPointFiberCocone_naturality
    {F G : (SmoothSite S)ᵒᵖ ⥤ A} (φ : F ⟶ G) (N : NisnevichNeighborhood X x) :
    (nisnevichPointFiberCocone X x F).ι.app (op N) ≫
        (nisnevichPoint X x).presheafFiber.map φ =
      φ.app (op ((nisnevichNeighborhoodFunctor X x).obj N)) ≫
        (nisnevichPointFiberCocone X x G).ι.app (op N) :=
  GrothendieckTopology.Point.toPresheafFiberOfIsCofiltered_naturality.{u + 1}
    (nisnevichNeighborhoodFunctor X x)
    (fun {_} R hR {_} f ↦ nisnevichNeighborhood_cover_lifting X x R hR f) φ N

end Fiber

end AlgebraicGeometry.Scheme.SmoothSite
