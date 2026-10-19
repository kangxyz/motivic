/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Germs.Original.FiberProduct
public import Motivic.Aglib.CategoryTheory.Sites.SheafProducts.Sections

/-! # The all-point envelope as the actual product of residue direct images -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace Motivic.SheafWithTransfers
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.Sheaf
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable (k : Type u) [Field k] (P : SheafWithTransfers.{u + 1} k)
  (X : SmoothSite (Spec (.of k)))

/-- The original ordinary coefficient sheaf, not a replacement category. -/
abbrev envelopeCoefficient := (toSheaf k).obj P

/-- The existing envelope restricted to the actual small site. -/
abbrev restrictedOriginalEnvelope :=
  (EtaleSeparatedFiniteType.restrict X AddCommGrpCat).obj ((toSheaf k).obj (originalGermEnvelope k
      P))

/-- Each factor is the actual direct image of the actual residue inverse image. -/
def originalEnvelopeFactor (x : X.left) :
    Sheaf (EtaleSeparatedFiniteType.nisnevichTopology X.left) AddCommGrpCat.{u + 1} :=
  (Scheme.EtaleSeparatedFiniteType.directImage (X.left.fromSpecResidueField x)).obj
    (originalResidueCoefficient X (envelopeCoefficient k P) x)

/-- Original germ tuples glue to a section of each literal residue direct image. -/
def originalEnvelopeCoordinate (V : EtaleSeparatedFiniteType X.left) (x : X.left) :
    (restrictedOriginalEnvelope k P X).obj.obj (op V) →+
      (originalEnvelopeFactor k P X x).obj.obj (op V) where
  toFun a := (Scheme.EtaleSeparatedFiniteType.originalFiberSectionsEquiv V x
    (originalResidueCoefficient X (envelopeCoefficient k P) x)).symm
      (fun v ↦ (originalFiberGermIso X (envelopeCoefficient k P) V x v).hom (a v.1))
  map_zero' := by
    change (Scheme.EtaleSeparatedFiniteType.originalFiberSectionsEquiv V x
      (originalResidueCoefficient X (envelopeCoefficient k P) x)).symm
        (fun v ↦ (originalFiberGermIso X (envelopeCoefficient k P) V x v).hom 0) = 0
    simp only [map_zero]
    exact map_zero _
  map_add' a b := by
    change (Scheme.EtaleSeparatedFiniteType.originalFiberSectionsEquiv V x
      (originalResidueCoefficient X (envelopeCoefficient k P) x)).symm
        (fun v ↦ (originalFiberGermIso X (envelopeCoefficient k P) V x v).hom
          (a v.1 + b v.1)) = _
    simp only [map_add]
    exact map_add _ _ _

/-- The gluing formula is precisely the old germ comparison at every original point. -/
theorem originalEnvelopeCoordinate_apply (V : EtaleSeparatedFiniteType X.left) (x : X.left)
    (a : (restrictedOriginalEnvelope k P X).obj.obj (op V)) (v : V.hom ⁻¹' {x}) :
    Scheme.EtaleSeparatedFiniteType.originalFiberSectionsEquiv V x (originalResidueCoefficient X
        (envelopeCoefficient k P) x)
        (originalEnvelopeCoordinate k P X V x a) v =
      (originalFiberGermIso X (envelopeCoefficient k P) V x v).hom (a v.1) := by
  exact congrFun (AddEquiv.apply_symm_apply _ _) v

/-- Coordinate gluing is natural for every original small-site restriction. -/
theorem originalEnvelopeCoordinate_naturality {U V : EtaleSeparatedFiniteType X.left}
    (g : U ⟶ V) (x : X.left)
    (a : (restrictedOriginalEnvelope k P X).obj.obj (op V)) :
    originalEnvelopeCoordinate k P X U x
        ((restrictedOriginalEnvelope k P X).obj.map g.op a) =
      (originalEnvelopeFactor k P X x).obj.map g.op
        (originalEnvelopeCoordinate k P X V x a) := by
  apply (Scheme.EtaleSeparatedFiniteType.originalFiberSectionsEquiv U x
    (originalResidueCoefficient X (envelopeCoefficient k P) x)).injective
  funext v
  rw [originalEnvelopeCoordinate_apply]
  change _ = Scheme.EtaleSeparatedFiniteType.originalFiberSectionsEquiv U x
    (originalResidueCoefficient X (envelopeCoefficient k P) x)
      ((originalResidueCoefficient X (envelopeCoefficient k P) x).obj.map
        ((Scheme.EtaleSeparatedFiniteType.baseChange (X.left.fromSpecResidueField x)).map g).op
        (originalEnvelopeCoordinate k P X V x a)) v
  rw [Scheme.EtaleSeparatedFiniteType.originalFiberSectionsEquiv_map,
      originalEnvelopeCoordinate_apply]
  have hn := ConcreteCategory.congr_hom
    (originalFiberGermIso_naturality X (envelopeCoefficient k P) g x v) (a (g.left v.1))
  change (originalFiberGermIso X (envelopeCoefficient k P) U x v).hom
    (((PresheafWithTransfers.toPresheaf k).obj
      (PresheafWithTransfers.originalGermTuplePresheaf k P.obj P.property)).map
        ((Scheme.EtaleSeparatedFiniteType.toSmoothSite X).map g).op a v.1) = _
  rw [PresheafWithTransfers.originalGermTuplePresheaf_map_apply]
  exact hn

/-- A genuine ordinary sheaf morphism, not merely an objectwise comparison. -/
def originalEnvelopeToFactor (x : X.left) :
    restrictedOriginalEnvelope k P X ⟶ originalEnvelopeFactor k P X x where
  hom :=
    { app := fun V ↦ AddCommGrpCat.ofHom (originalEnvelopeCoordinate k P X V.unop x)
      naturality := by
        intro U V g
        ext a
        exact originalEnvelopeCoordinate_naturality k P X g.unop x a }

/-- The map lands in the actual categorical product of direct-image sheaves. -/
def originalEnvelopeToProduct : restrictedOriginalEnvelope k P X ⟶
    ∏ᶜ originalEnvelopeFactor k P X :=
  Limits.Pi.lift (originalEnvelopeToFactor k P X)

/-- Reindexing over all fibers loses no original germ coordinate. -/
theorem originalEnvelopeCoordinates_bijective (V : EtaleSeparatedFiniteType X.left) :
    Function.Bijective (fun a : (restrictedOriginalEnvelope k P X).obj.obj (op V) ↦
      fun x ↦ originalEnvelopeCoordinate k P X V x a) := by
  constructor
  · intro a b hab
    funext v
    apply (ConcreteCategory.bijective_of_isIso
      (originalFiberGermIso X (envelopeCoefficient k P) V (V.hom v) ⟨v, rfl⟩).hom).injective
    have h := congrArg (fun s ↦ Scheme.EtaleSeparatedFiniteType.originalFiberSectionsEquiv V (V.hom
        v)
      (originalResidueCoefficient X (envelopeCoefficient k P) (V.hom v)) s ⟨v, rfl⟩)
        (congrFun hab (V.hom v))
    simpa only [originalEnvelopeCoordinate_apply] using h
  · intro s
    let a : (restrictedOriginalEnvelope k P X).obj.obj (op V) := fun v ↦
      (originalFiberGermIso X (envelopeCoefficient k P) V (V.hom v) ⟨v, rfl⟩).inv
        (Scheme.EtaleSeparatedFiniteType.originalFiberSectionsEquiv V (V.hom v)
          (originalResidueCoefficient X (envelopeCoefficient k P) (V.hom v))
          (s (V.hom v)) ⟨v, rfl⟩)
    refine ⟨a, funext fun x ↦ ?_⟩
    apply (Scheme.EtaleSeparatedFiniteType.originalFiberSectionsEquiv V x
      (originalResidueCoefficient X (envelopeCoefficient k P) x)).injective
    funext v
    rw [originalEnvelopeCoordinate_apply]
    rcases v with ⟨v, hv⟩
    change V.hom v = x at hv
    subst x
    change ((originalFiberGermIso X (envelopeCoefficient k P) V (V.hom v) ⟨v, rfl⟩).inv ≫
      (originalFiberGermIso X (envelopeCoefficient k P) V (V.hom v) ⟨v, rfl⟩).hom) _ = _
    exact ConcreteCategory.congr_hom
      (originalFiberGermIso X (envelopeCoefficient k P) V (V.hom v) ⟨v, rfl⟩).inv_hom_id _

/-- The actual categorical-product morphism retains every original coordinate. -/
theorem originalEnvelopeToProduct_π (x : X.left) :
    originalEnvelopeToProduct k P X ≫ Limits.Pi.π (originalEnvelopeFactor k P X) x =
      originalEnvelopeToFactor k P X x := Limits.Pi.lift_comp_π _ _

/-- The genuine sheaf morphism is bijective on each original section group. -/
theorem originalEnvelopeToProduct_app_bijective (V : EtaleSeparatedFiniteType X.left) :
    Function.Bijective ((originalEnvelopeToProduct k P X).hom.app (op V)) := by
  let e := Products.sectionsEquiv (EtaleSeparatedFiniteType.nisnevichTopology X.left)
    (originalEnvelopeFactor k P X) V
  have he (a : (restrictedOriginalEnvelope k P X).obj.obj (op V)) :
      e ((originalEnvelopeToProduct k P X).hom.app (op V) a) =
        fun x ↦ originalEnvelopeCoordinate k P X V x a := by
    funext x
    exact ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.hom.app (op V)) (originalEnvelopeToProduct_π k P X x)) a
  constructor
  · intro a b hab
    apply (originalEnvelopeCoordinates_bijective k P X V).injective
    exact (he a).symm.trans ((congrArg e hab).trans (he b))
  · intro t
    obtain ⟨a, ha⟩ := (originalEnvelopeCoordinates_bijective k P X V).surjective (e t)
    exact ⟨a, e.injective ((he a).trans ha)⟩

instance originalEnvelopeToProduct_isIso : IsIso (originalEnvelopeToProduct k P X) := by
  have (V : (EtaleSeparatedFiniteType X.left)ᵒᵖ) :
      IsIso ((originalEnvelopeToProduct k P X).hom.app V) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (originalEnvelopeToProduct_app_bijective k P X V.unop)
  have : IsIso (originalEnvelopeToProduct k P X).hom := NatIso.isIso_of_isIso_app _
  have : IsIso ((sheafToPresheaf _ _).map (originalEnvelopeToProduct k P X)) :=
    inferInstanceAs (IsIso (originalEnvelopeToProduct k P X).hom)
  exact isIso_of_reflects_iso (originalEnvelopeToProduct k P X) (sheafToPresheaf _ _)

/-- The existing all-point envelope is the actual sheaf product of residue direct images. -/
def originalEnvelopeProductIso : restrictedOriginalEnvelope k P X ≅
    ∏ᶜ originalEnvelopeFactor k P X := asIso (originalEnvelopeToProduct k P X)

end Motivic.SheafWithTransfers
