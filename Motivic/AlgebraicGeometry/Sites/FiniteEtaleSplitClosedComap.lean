/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleSplitClosedNeighborhood
public import Motivic.AlgebraicGeometry.Sites.FiniteEtalePointInverseImageUnit

/-! # Native comapped-point neighborhoods for split closed immersions

The literal marked initiality theorem is transported to the native point
comap. This is the index used by the already proved adjunction-unit equation.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
variable {Z Y : Scheme.{u}} (i : Z ⟶ Y) (K : Type u) [Field K]
  (c : Spec (.of K) ⟶ Z)

/-- The pullback universal property on full original field-valued marks. -/
def closedMarkEquiv (V : FiniteEtaleSite Y) :
    (Over.mk (𝟙 _ ≫ c) ⟶
      (MorphismProperty.Over.forget _ _ Z).obj ((baseChange i).obj V)) ≃
    (Over.mk (𝟙 _ ≫ (c ≫ i)) ⟶
      (MorphismProperty.Over.forget _ _ Y).obj V) where
  toFun a := Over.homMk (a.left ≫ pullback.fst V.hom i) (by
    change (a.left ≫ pullback.fst V.hom i) ≫ V.hom = 𝟙 _ ≫ (c ≫ i)
    have ha : a.left ≫ pullback.snd V.hom i = c :=
      (Over.w a).trans (Category.id_comp c)
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun t => a.left ≫ t) (pullback.condition (f := V.hom) (g := i))).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun t => t ≫ i) ha).trans (Category.id_comp (c ≫ i)).symm))))
  invFun a := Over.homMk (pullback.lift a.left c (by simp)) (by
    change pullback.lift a.left c _ ≫ pullback.snd V.hom i = 𝟙 _ ≫ c
    simp only [pullback.lift_snd, Category.id_comp])
  left_inv a := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans ((Over.w a).trans (Category.id_comp c)).symm
  right_inv a := by
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _

/-- Full-mark pullback identification commutes with the actual ambient arrow. -/
theorem closedMarkEquiv_naturality {V W : FiniteEtaleSite Y} (f : V ⟶ W)
    (a : Over.mk (𝟙 _ ≫ c) ⟶
      (MorphismProperty.Over.forget _ _ Z).obj ((baseChange i).obj V)) :
    closedMarkEquiv i K c W
      (a ≫ (MorphismProperty.Over.forget _ _ Z).map ((baseChange i).map f)) =
    closedMarkEquiv i K c V a ≫ (MorphismProperty.Over.forget _ _ Y).map f := by
  apply Over.OverMorphism.ext
  change (a.left ≫ ((baseChange i).map f).left) ≫ pullback.fst W.hom i =
    (a.left ≫ pullback.fst V.hom i) ≫ f.left
  rw [Category.assoc, Category.assoc]
  exact congrArg (fun t => a.left ≫ t) (pullback.lift_fst _ _ _)

local notation "Φ" => relativeFieldPoint c K (𝟙 _)
local instance : InitiallySmall.{u + 1} (baseChange i ⋙ (Φ).fiber).Elements :=
  initiallySmall_of_essentiallySmall _
local notation "hcover" => CoverPreserving.of_isContinuous (baseChange i)
  (nisnevichTopology Y) (nisnevichTopology Z)
local notation "Ξ" => GrothendieckTopology.Point.comap
  (relativeFieldPoint c K (𝟙 _)) (baseChange i)
  (CoverPreserving.of_isContinuous (baseChange i) (nisnevichTopology Y) (nisnevichTopology Z))

/-- Native comapped-point marks identified with literal ambient full marks. -/
def splitClosedComapFiberEquiv (V : FiniteEtaleSite Y) :
    (Ξ).fiber.obj V ≃
      (Over.mk (𝟙 _ ≫ (c ≫ i)) ⟶ (MorphismProperty.Over.forget _ _ Y).obj V) :=
  (relativeFieldPointFiberEquiv c K (𝟙 _) ((baseChange i).obj V)).trans
    (closedMarkEquiv i K c V)

/-- Naturality of the native comap's full-mark identification. -/
theorem splitClosedComapFiberEquiv_naturality {V W : FiniteEtaleSite Y} (f : V ⟶ W)
    (a : (Ξ).fiber.obj V) :
    splitClosedComapFiberEquiv i K c W ((Ξ).fiber.map f a) =
      splitClosedComapFiberEquiv i K c V a ≫ (MorphismProperty.Over.forget _ _ Y).map f := by
  change closedMarkEquiv i K c W
      (relativeFieldPointFiberEquiv c K (𝟙 _) ((baseChange i).obj W)
        ((Φ).fiber.map ((baseChange i).map f) a)) = _
  rw [relativeFieldPointFiberEquiv_naturality, closedMarkEquiv_naturality]
  rfl

/-- Forget only the native pullback presentation of a marked ambient point. -/
def splitClosedComapToNeighborhood :
    (Ξ).fiber.Elements ⥤ FieldValuedNeighborhood (c ≫ i) K (𝟙 _) where
  obj N := Functor.elementsMk _ N.obj (splitClosedComapFiberEquiv i K c N.obj N.val)
  map {N M} a := Functor.Elements.homMk a.hom (by
    exact (splitClosedComapFiberEquiv_naturality i K c a.hom N.val).symm.trans
      (congrArg (splitClosedComapFiberEquiv i K c M.obj) a.map_val))
  map_id _ := rfl
  map_comp _ _ := rfl

instance splitClosedComapToNeighborhood_faithful :
    (splitClosedComapToNeighborhood i K c).Faithful where
  map_injective h := Functor.Elements.hom_ext (congrArg (fun a => a.hom) h)

instance splitClosedComapToNeighborhood_full :
    (splitClosedComapToNeighborhood i K c).Full where
  map_surjective {N M} a := by
    refine ⟨Functor.Elements.homMk a.hom ?_, rfl⟩
    apply (splitClosedComapFiberEquiv i K c M.obj).injective
    exact (splitClosedComapFiberEquiv_naturality i K c a.hom N.val).trans a.map_val

instance splitClosedComapToNeighborhood_initial :
    (splitClosedComapToNeighborhood i K c).Initial := by
  apply Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
  intro N
  refine ⟨Functor.elementsMk _ N.obj
    ((splitClosedComapFiberEquiv i K c N.obj).symm N.val), ?_⟩
  refine ⟨Functor.Elements.homMk (𝟙 _) ?_⟩
  change splitClosedComapFiberEquiv i K c N.obj
    ((splitClosedComapFiberEquiv i K c N.obj).symm N.val) ≫ 𝟙 _ = N.val
  rw [Equiv.apply_symm_apply, Category.comp_id]

/-- The native projection from comapped point neighborhoods to source point
neighborhoods, on precisely the existing elements categories. -/
def splitClosedComapProjection : (Ξ).fiber.Elements ⥤ (Φ).fiber.Elements where
  obj N := Functor.elementsMk _ ((baseChange i).obj N.obj) N.val
  map a := Functor.Elements.homMk ((baseChange i).map a.hom) a.map_val
  map_id _ := by apply Functor.Elements.hom_ext; exact (baseChange i).map_id _
  map_comp _ _ := by apply Functor.Elements.hom_ext; exact (baseChange i).map_comp _ _

/-- The two actual closed-mark constructions agree by the pullback universal property. -/
def splitClosedComapProjectionNeighborhoodIso :
    splitClosedComapProjection i K c ⋙ pointElementsToNeighborhood c K (𝟙 _) ≅
      splitClosedComapToNeighborhood i K c ⋙ closedNeighborhoodBaseChange i K c := by
  refine NatIso.ofComponents (fun N => ?_) ?_
  · let h : ((splitClosedComapProjection i K c ⋙
        pointElementsToNeighborhood c K (𝟙 _)).obj N).val =
      ((splitClosedComapToNeighborhood i K c ⋙
        closedNeighborhoodBaseChange i K c).obj N).val := by
        exact ((closedMarkEquiv i K c N.obj).symm_apply_apply
          (relativeFieldPointFiberEquiv c K (𝟙 _) ((baseChange i).obj N.obj) N.val)).symm
    exact Functor.Elements.isoMk (Iso.refl _) (by
      change (relativeFieldPointFiberEquiv c K (𝟙 _) ((baseChange i).obj N.obj) N.val) ≫
        𝟙 _ = _
      exact (Category.comp_id _).trans h)
  · intro N M f
    apply Functor.Elements.hom_ext
    simp
    rfl

/-- The native comap projection is initial, with all geometry supplied by the
proved split-closed literal marked-neighborhood theorem. -/
theorem splitClosedComapProjection_initial [IsClosedImmersion i] [IsNoetherian Y]
    (p : Y ⟶ Z) (hip : i ≫ p = 𝟙 Z) : (splitClosedComapProjection i K c).Initial := by
  let := closedNeighborhoodBaseChange_initial i K c p hip
  let : (splitClosedComapProjection i K c ⋙ pointElementsToNeighborhood c K (𝟙 _)).Initial :=
    Functor.initial_of_natIso (splitClosedComapProjectionNeighborhoodIso i K c).symm
  exact Functor.initial_of_comp_full_faithful (splitClosedComapProjection i K c)
    (pointElementsToNeighborhood c K (𝟙 _))

end Motivic.FiniteEtaleSite
