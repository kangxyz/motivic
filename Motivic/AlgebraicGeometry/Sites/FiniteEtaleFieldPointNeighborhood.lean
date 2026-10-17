/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleFieldPointInverseImage
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat

/-! # Literal field-valued points in a base-changed small neighborhood -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace Motivic.FiniteEtaleSite
variable {S T : Scheme.{u}} (b : S ⟶ T) (K : Type u) [Field K]
  (q : Spec (.of K) ⟶ S) [Etale q] [IsSeparated q] [QuasiCompact q]

/-- The actual pullback universal property identifies field points of base-changed
neighborhoods with field-valued points over the original base. -/
def fieldPointLiftEquiv (V : FiniteEtaleSite T) :
    (fieldObject K q ⟶ (baseChange b).obj V) ≃
      (Over.mk (q ≫ b) ⟶ (MorphismProperty.Over.forget _ _ T).obj V) where
  toFun a := Over.homMk (a.left ≫ pullback.fst V.hom b) (by
    change (a.left ≫ pullback.fst V.hom b) ≫ V.hom = q ≫ b
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun t => t ≫ b) (MorphismProperty.Over.w a))
  invFun a := MorphismProperty.Over.homMk (pullback.lift a.left q (Over.w a))
    (pullback.lift_snd _ _ _)
  left_inv a := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans (MorphismProperty.Over.w a).symm
  right_inv a := by
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _

/-- The field-point identification preserves the actual maps between small neighborhoods. -/
@[reassoc]
theorem fieldPointLiftEquiv_naturality {V W : FiniteEtaleSite T} (g : V ⟶ W)
    (a : fieldObject K q ⟶ (baseChange b).obj V) :
    fieldPointLiftEquiv b K q W (a ≫ (baseChange b).map g) =
      fieldPointLiftEquiv b K q V a ≫ (MorphismProperty.Over.forget _ _ T).map g := by
  apply Over.OverMorphism.ext
  change (a.left ≫ ((baseChange b).map g).left) ≫ pullback.fst W.hom b =
    (a.left ≫ pullback.fst V.hom b) ≫ g.left
  rw [Category.assoc, Category.assoc]
  exact congrArg (fun t => a.left ≫ t) (pullback.lift_fst _ _ _)

/-- The comapped point's native shrunk fiber has the literal field-valued description. -/
def relativeFieldPointFiberEquiv (V : FiniteEtaleSite T) :
    (relativeFieldPoint b K q).fiber.obj V ≃
      (Over.mk (q ≫ b) ⟶ (MorphismProperty.Over.forget _ _ T).obj V) :=
  shrinkYonedaObjObjEquiv.{u + 1}.trans (fieldPointLiftEquiv b K q V)


/-- Literal field-valued pointed neighborhoods over the target scheme. -/
abbrev FieldValuedNeighborhood :=
  (MorphismProperty.Over.forget etaleSeparatedFiniteType ⊤ T ⋙
    coyoneda.obj (op (Over.mk (q ≫ b)))).Elements

instance : IsCofiltered (FieldValuedNeighborhood b K q) :=
  Functor.isCofiltered_elements _

/-- Naturality includes the native universe-shrinking used in the point fiber. -/
theorem relativeFieldPointFiberEquiv_naturality {V W : FiniteEtaleSite T} (g : V ⟶ W)
    (a : (relativeFieldPoint b K q).fiber.obj V) :
    relativeFieldPointFiberEquiv b K q W ((relativeFieldPoint b K q).fiber.map g a) =
      relativeFieldPointFiberEquiv b K q V a ≫ (MorphismProperty.Over.forget _ _ T).map g := by
  change fieldPointLiftEquiv b K q W
      (shrinkYonedaObjObjEquiv.{u + 1}
        ((shrinkYoneda.{u + 1}.map ((baseChange b).map g)).app (op (fieldObject K q)) a)) = _
  exact (congrArg (fieldPointLiftEquiv b K q W)
    (shrinkYonedaObjObjEquiv_map_app a ((baseChange b).map g))).trans
      (fieldPointLiftEquiv_naturality b K q g _)

/-- Forget the pullback presentation of the marked field-valued point, not its actual map. -/
def pointElementsToNeighborhood :
    (relativeFieldPoint b K q).fiber.Elements ⥤ FieldValuedNeighborhood b K q where
  obj N := Functor.elementsMk _ N.obj (relativeFieldPointFiberEquiv b K q N.obj N.val)
  map {N M} a := Functor.Elements.homMk a.hom (by
    exact (relativeFieldPointFiberEquiv_naturality b K q a.hom N.val).symm.trans
      (congrArg (relativeFieldPointFiberEquiv b K q M.obj) a.map_val))
  map_id _ := rfl
  map_comp _ _ := rfl

instance pointElementsToNeighborhood_faithful : (pointElementsToNeighborhood b K q).Faithful where
  map_injective h := Functor.Elements.hom_ext (congrArg (fun a => a.hom) h)

instance pointElementsToNeighborhood_full : (pointElementsToNeighborhood b K q).Full where
  map_surjective {N M} a := by
    refine ⟨Functor.Elements.homMk a.hom ?_, rfl⟩
    apply (relativeFieldPointFiberEquiv b K q M.obj).injective
    exact (relativeFieldPointFiberEquiv_naturality b K q a.hom N.val).trans a.map_val

/-- The original point category is initial in the literal field-valued neighborhood diagram. -/
instance pointElementsToNeighborhood_initial : (pointElementsToNeighborhood b K q).Initial := by
  apply Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
  intro N
  refine ⟨Functor.elementsMk _ N.obj
    ((relativeFieldPointFiberEquiv b K q N.obj).symm N.val), ?_⟩
  refine ⟨Functor.Elements.homMk (𝟙 _) ?_⟩
  change relativeFieldPointFiberEquiv b K q N.obj
    ((relativeFieldPointFiberEquiv b K q N.obj).symm N.val) ≫ 𝟙 _ = N.val
  rw [Equiv.apply_symm_apply, Category.comp_id]


variable (F : (FiniteEtaleSite T)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

instance fieldNeighborhoodDiagramHasColimit :
    HasColimit ((Functor.Elements.π
      (MorphismProperty.Over.forget etaleSeparatedFiniteType ⊤ T ⋙
        coyoneda.obj (op (Over.mk (q ≫ b))))).op ⋙ F) := by
  let : HasColimit ((pointElementsToNeighborhood b K q).op ⋙
      (Functor.Elements.π _).op ⋙ F) :=
    inferInstanceAs (HasColimit ((Functor.Elements.π (relativeFieldPoint b K q).fiber).op ⋙ F))
  exact Functor.Final.hasColimit_of_comp (pointElementsToNeighborhood b K q).op

/-- The literal field-valued neighborhood colimit computes the existing comapped point fiber. -/
def fieldNeighborhoodFiberIso :
    colimit ((Functor.Elements.π
      (MorphismProperty.Over.forget etaleSeparatedFiniteType ⊤ T ⋙
        coyoneda.obj (op (Over.mk (q ≫ b))))).op ⋙ F) ≅
      (relativeFieldPoint b K q).presheafFiber.obj F :=
  (Functor.Final.colimitIso (pointElementsToNeighborhood b K q).op
    ((Functor.Elements.π _).op ⋙ F)).symm


/-- The genuine inverse-image evaluation is computed by the actual field-valued
small-neighborhood diagram, with no substituted cohomology or stalk functor. -/
def fieldNeighborhoodInverseImageIso
    (G : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) :
    colimit ((Functor.Elements.π
      (MorphismProperty.Over.forget etaleSeparatedFiniteType ⊤ T ⋙
        coyoneda.obj (op (Over.mk (q ≫ b))))).op ⋙ G.obj) ≅
      ((inverseImage b).obj G).obj.obj (op (fieldObject K q)) :=
  fieldNeighborhoodFiberIso b K q G.obj ≪≫
    (relativeFieldPointInverseImageIso b K q).app G

end Motivic.FiniteEtaleSite
