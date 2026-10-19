/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.BaseChangeProducts
public import Motivic.Aglib.AlgebraicGeometry.Products.Diagonal.Basic
public import Motivic.Aglib.AlgebraicGeometry.Diagonal.FlatBaseChange

/-!
# The original diagonal under arbitrary field base change

The pair projection uses the inverse of the actual relative-product comparison.
Its Cartesian diagonal square transports a given list of original stalk equations
to a regular list generating the literal new diagonal stalk kernel. No finite-type
or separability hypothesis on a field extension is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S T : Scheme.{u}} (f : T ⟶ S) (Y : SmoothSite S)

/-- The literal projection from the new relative pair to the original pair. -/
def baseChangePairProjection :
    (product ((baseChange f).obj Y) ((baseChange f).obj Y)).left ⟶ (product Y Y).left :=
  (baseChangeProductIso f Y Y).inv.left ≫ pullback.fst (product Y Y).hom f

@[reassoc (attr := simp)]
theorem baseChangePairProjection_fst :
    baseChangePairProjection f Y ≫ pullback.fst Y.hom Y.hom =
      pullback.fst ((baseChange f).obj Y).hom ((baseChange f).obj Y).hom ≫
        pullback.fst Y.hom f := by
  simpa only [baseChangePairProjection, MorphismProperty.Comma.comp_left,
    Category.assoc, baseChange_map_fst, productFst, homMk_left] using
    congrArg (fun k => k.left ≫ pullback.fst Y.hom f)
      (baseChangeProductIso_inv_fst f Y Y)

@[reassoc (attr := simp)]
theorem baseChangePairProjection_snd :
    baseChangePairProjection f Y ≫ pullback.snd Y.hom Y.hom =
      pullback.snd ((baseChange f).obj Y).hom ((baseChange f).obj Y).hom ≫
        pullback.fst Y.hom f := by
  simpa only [baseChangePairProjection, MorphismProperty.Comma.comp_left,
    Category.assoc, baseChange_map_fst, productSnd, homMk_left] using
    congrArg (fun k => k.left ≫ pullback.fst Y.hom f)
      (baseChangeProductIso_inv_snd f Y Y)

instance baseChangePairProjection_flat [Flat f] : Flat (baseChangePairProjection f Y) := by
  unfold baseChangePairProjection
  have : IsIso (baseChangeProductIso f Y Y).inv.left :=
    inferInstanceAs (IsIso ((forgetScheme T).mapIso (baseChangeProductIso f Y Y)).inv)
  infer_instance

/-- The common-parameter diagonal is the actual new diagonal under the product comparison. -/
@[reassoc]
theorem baseChangeProductIso_diagonal :
    ProductDiagonal.diagonalBaseChange Y.hom f ≫ (baseChangeProductIso f Y Y).hom.left =
      pullback.diagonal ((baseChange f).obj Y).hom := by
  apply pullback.hom_ext <;> apply pullback.hom_ext <;>
    simp [baseChangeProductIso, productLift, ProductDiagonal.diagonalBaseChange,
      baseChange_map_left, productFst, productSnd]

/-- The square with the literal new diagonal and the original diagonal is Cartesian. -/
theorem baseChangeDiagonal_isPullback :
    IsPullback (pullback.fst Y.hom f) (pullback.diagonal ((baseChange f).obj Y).hom)
      (pullback.diagonal Y.hom) (baseChangePairProjection f Y) := by
  apply (ProductDiagonal.diagonalBaseChange_isPullback Y.hom f).of_iso
    (Iso.refl _) (Iso.refl _) ((forgetScheme T).mapIso (baseChangeProductIso f Y Y))
    (Iso.refl _)
  · simp
  · simpa using baseChangeProductIso_diagonal f Y
  · simp
  · change _ ≫ 𝟙 _ = (baseChangeProductIso f Y Y).hom.left ≫
      (baseChangeProductIso f Y Y).inv.left ≫ pullback.fst (product Y Y).hom f
    simp only [Category.comp_id, ← Category.assoc]
    change _ = (((forgetScheme T).mapIso (baseChangeProductIso f Y Y)).hom ≫
      ((forgetScheme T).mapIso (baseChangeProductIso f Y Y)).inv) ≫ _
    rw [Iso.hom_inv_id, Category.id_comp]
    rfl

/-- The original diagonal stalk maps to the actual new diagonal stalk, with its point equality. -/
abbrev baseChangeDiagonalStalkMap (y : ((baseChange f).obj Y).left) :=
  Diagonal.baseChangeStalkMap (baseChangeDiagonal_isPullback f Y) y

/-- Literal images of any given regular kernel-generating list generate the new diagonal kernel. -/
theorem baseChangeDiagonal_regular_kernel [Flat f] (y : ((baseChange f).obj Y).left)
    (rs : List ((product Y Y).left.presheaf.stalk
      (pullback.diagonal Y.hom (pullback.fst Y.hom f y))))
    (hrs : IsRegular ((product Y Y).left.presheaf.stalk
      (pullback.diagonal Y.hom (pullback.fst Y.hom f y))) rs)
    (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap
      (pullback.fst Y.hom f y)).hom = Ideal.ofList rs) :
    IsRegular ((pullback ((baseChange f).obj Y).hom ((baseChange f).obj Y).hom).presheaf.stalk
        (pullback.diagonal ((baseChange f).obj Y).hom y))
      (rs.map (baseChangeDiagonalStalkMap f Y y).hom) ∧
    RingHom.ker ((pullback.diagonal ((baseChange f).obj Y).hom).stalkMap y).hom =
      Ideal.ofList (rs.map (baseChangeDiagonalStalkMap f Y y).hom) :=
  Diagonal.mapped_equations_regular_kernel (baseChangeDiagonal_isPullback f Y) y hrs hker

section Fields

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L) (Y : overField k)

/-- The new pair projects to the old pair for every field homomorphism. -/
abbrev fieldBaseChangePairProjection :=
  baseChangePairProjection (Spec.map (CommRingCat.ofHom φ)) Y

@[reassoc (attr := simp)]
theorem fieldBaseChangePairProjection_fst :
    fieldBaseChangePairProjection φ Y ≫ pullback.fst Y.hom Y.hom =
      pullback.fst ((fieldBaseChange φ).obj Y).hom ((fieldBaseChange φ).obj Y).hom ≫
        pullback.fst Y.hom (Spec.map (CommRingCat.ofHom φ)) :=
  baseChangePairProjection_fst _ _

@[reassoc (attr := simp)]
theorem fieldBaseChangePairProjection_snd :
    fieldBaseChangePairProjection φ Y ≫ pullback.snd Y.hom Y.hom =
      pullback.snd ((fieldBaseChange φ).obj Y).hom ((fieldBaseChange φ).obj Y).hom ≫
        pullback.fst Y.hom (Spec.map (CommRingCat.ofHom φ)) :=
  baseChangePairProjection_snd _ _

/-- The pair projection is flat for an arbitrary field extension. -/
theorem fieldBaseChangePairProjection_flat : Flat (fieldBaseChangePairProjection φ Y) :=
  inferInstance

/-- The old and new middle diagonals form the literal Cartesian square. -/
theorem fieldBaseChangeDiagonal_isPullback :
    IsPullback (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom φ)))
      (pullback.diagonal ((fieldBaseChange φ).obj Y).hom)
      (pullback.diagonal Y.hom) (fieldBaseChangePairProjection φ Y) :=
  baseChangeDiagonal_isPullback _ _

/-- The exact stalk map from the original middle diagonal to the new one. -/
abbrev fieldBaseChangeDiagonalStalkMap (y : ((fieldBaseChange φ).obj Y).left) :=
  Diagonal.baseChangeStalkMap (fieldBaseChangeDiagonal_isPullback φ Y) y

/-- The point-aligned middle-pair stalk map is flat over every field extension. -/
theorem fieldBaseChangeDiagonalStalkMap_flat (y : ((fieldBaseChange φ).obj Y).left) :
    (fieldBaseChangeDiagonalStalkMap φ Y y).hom.Flat :=
  Diagonal.baseChangeStalkMap_flat (fieldBaseChangeDiagonal_isPullback φ Y) y

/-- The same original list becomes a regular list generating the exact new diagonal kernel. -/
theorem fieldBaseChangeDiagonal_regular_kernel (y : ((fieldBaseChange φ).obj Y).left)
    (rs : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom φ)) y))))
    (hrs : IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom φ)) y))) rs)
    (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap
      (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom φ)) y)).hom = Ideal.ofList rs) :
    IsRegular ((pullback ((fieldBaseChange φ).obj Y).hom
        ((fieldBaseChange φ).obj Y).hom).presheaf.stalk
        (pullback.diagonal ((fieldBaseChange φ).obj Y).hom y))
      (rs.map (fieldBaseChangeDiagonalStalkMap φ Y y).hom) ∧
    RingHom.ker ((pullback.diagonal ((fieldBaseChange φ).obj Y).hom).stalkMap y).hom =
      Ideal.ofList (rs.map (fieldBaseChangeDiagonalStalkMap φ Y y).hom) :=
  baseChangeDiagonal_regular_kernel _ _ y rs hrs hker

end Fields

end AlgebraicGeometry.Scheme.SmoothSite
