/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.NisnevichComparison
public import Motivic.Aglib.CategoryTheory.SheafifyAdditive
public import Motivic.Aglib.CategoryTheory.SheafifyLocallyBijective
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Transfer-preserving Nisnevich sheafification

Ordinary Mathlib sheafification on the actual finite-correspondence Nisnevich
site preserves addition of source arrows. Its output therefore has genuine
signed transfers, and the proved comparison of sheaf conditions puts it in
`SheafWithTransfers`, defined using the ordinary smooth Nisnevich topology.
The canonical unit and lifting property give a left adjoint to the inclusion.

The coefficient universe is explicitly `u + 1` for a field in `Type u`:
the correspondence objects live in `Type (u + 1)`. The required sheafification
and compatibility-with-forget hypotheses remain explicit and are available
from the imported standard abelian-group instances. No conclusion for
arbitrary smaller coefficient universes or continuity of the graph functor
on nonadditive correspondence presheaves is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]
variable [HasWeakSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]

/-- The actual sheafification is additive in signed correspondence arrows. -/
theorem nisnevichSheafify_additive (P : PresheafWithTransfers.{u + 1} k) :
    (sheafify (Cor.nisnevichTopology k) P.obj).Additive :=
  sheafify_additive_of_principal_covering_basis (Cor.nisnevichTopology k)
    (Cor.principal_covering_basis k) P.obj

/-- Sheafification of a transfer presheaf, with actual signed transfers and
ordinary smooth-site Nisnevich descent. -/
def nisnevichSheafify : PresheafWithTransfers.{u + 1} k ⥤ SheafWithTransfers.{u + 1} k where
  obj P :=
    ⟨⟨sheafify (Cor.nisnevichTopology k) P.obj, nisnevichSheafify_additive k P⟩,
      (isNisnevichSheaf_iff_correspondenceTopology _).mpr
        ((presheafToSheaf (Cor.nisnevichTopology k) AddCommGrpCat).obj P.obj).property⟩
  map η := ⟨⟨sheafifyMap (Cor.nisnevichTopology k) η.hom⟩⟩
  map_id P := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact sheafifyMap_id (Cor.nisnevichTopology k) P.obj
  map_comp η θ := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact sheafifyMap_comp (Cor.nisnevichTopology k) η.hom θ.hom

@[simp]
theorem nisnevichSheafify_obj_obj (P : PresheafWithTransfers.{u + 1} k) :
    ((nisnevichSheafify k).obj P).obj.obj = sheafify (Cor.nisnevichTopology k) P.obj := rfl

@[simp]
theorem nisnevichSheafify_map_hom {P Q : PresheafWithTransfers.{u + 1} k} (η : P ⟶ Q) :
    ((nisnevichSheafify k).map η).hom.hom =
      sheafifyMap (Cor.nisnevichTopology k) η.hom := rfl

/-- The transfer-natural canonical sheafification unit. -/
def toNisnevichSheafify (P : PresheafWithTransfers.{u + 1} k) :
    P ⟶ ((nisnevichSheafify k).obj P).obj :=
  ⟨toSheafify (Cor.nisnevichTopology k) P.obj⟩

@[simp]
theorem toNisnevichSheafify_hom (P : PresheafWithTransfers.{u + 1} k) :
    (toNisnevichSheafify k P).hom = toSheafify (Cor.nisnevichTopology k) P.obj := rfl

/-- Naturality of the unit for all transfer-presheaf morphisms. -/
@[reassoc (attr := simp)]
theorem toNisnevichSheafify_naturality {P Q : PresheafWithTransfers.{u + 1} k}
    (η : P ⟶ Q) :
    η ≫ toNisnevichSheafify k Q =
      toNisnevichSheafify k P ≫ ((nisnevichSheafify k).map η).hom := by
  apply ObjectProperty.hom_ext
  exact toSheafify_naturality (Cor.nisnevichTopology k) η.hom

/-- The canonical unit as a natural transformation. -/
def nisnevichSheafificationUnit :
    𝟭 (PresheafWithTransfers.{u + 1} k) ⟶
      nisnevichSheafify k ⋙ SheafWithTransfers.forget k where
  app P := toNisnevichSheafify k P
  naturality _ _ η := toNisnevichSheafify_naturality k η

/-- Extend a transfer-natural map into an actual Nisnevich sheaf with transfers. -/
def nisnevichSheafifyLift {P : PresheafWithTransfers.{u + 1} k}
    {Q : SheafWithTransfers.{u + 1} k} (η : P ⟶ Q.obj) :
    (nisnevichSheafify k).obj P ⟶ Q :=
  ⟨⟨sheafifyLift (Cor.nisnevichTopology k) η.hom
    ((isNisnevichSheaf_iff_correspondenceTopology Q.obj).mp Q.property)⟩⟩

/-- The lifted map extends the given map along the canonical unit. -/
@[reassoc (attr := simp)]
theorem toNisnevichSheafify_lift {P : PresheafWithTransfers.{u + 1} k}
    {Q : SheafWithTransfers.{u + 1} k} (η : P ⟶ Q.obj) :
    toNisnevichSheafify k P ≫ (nisnevichSheafifyLift k η).hom = η := by
  apply ObjectProperty.hom_ext
  exact toSheafify_sheafifyLift (Cor.nisnevichTopology k) η.hom _

/-- The extension is unique among maps natural for all signed transfers. -/
theorem nisnevichSheafifyLift_unique {P : PresheafWithTransfers.{u + 1} k}
    {Q : SheafWithTransfers.{u + 1} k} (η : P ⟶ Q.obj)
    (γ : (nisnevichSheafify k).obj P ⟶ Q)
    (hγ : toNisnevichSheafify k P ≫ γ.hom = η) :
    γ = nisnevichSheafifyLift k η := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  exact sheafifyLift_unique (Cor.nisnevichTopology k) η.hom _ γ.hom.hom
    (congrArg (fun f => f.hom) hγ)

/-- Equality of maps out of transfer sheafification can be tested on the unit. -/
theorem nisnevichSheafify_hom_ext {P : PresheafWithTransfers.{u + 1} k}
    {Q : SheafWithTransfers.{u + 1} k} (η θ : (nisnevichSheafify k).obj P ⟶ Q)
    (h : toNisnevichSheafify k P ≫ η.hom = toNisnevichSheafify k P ≫ θ.hom) :
    η = θ := by
  exact (nisnevichSheafifyLift_unique k _ η h).trans
    (nisnevichSheafifyLift_unique k _ θ rfl).symm

/-- The actual universal hom-set equivalence for transfer sheafification. -/
def nisnevichSheafificationHomEquiv (P : PresheafWithTransfers.{u + 1} k)
    (Q : SheafWithTransfers.{u + 1} k) :
    ((nisnevichSheafify k).obj P ⟶ Q) ≃ (P ⟶ Q.obj) where
  toFun η := toNisnevichSheafify k P ≫ η.hom
  invFun := nisnevichSheafifyLift k
  left_inv η := (nisnevichSheafifyLift_unique k _ η rfl).symm
  right_inv η := toNisnevichSheafify_lift k η

/-- Transfer-preserving Nisnevich sheafification is left adjoint to the
original inclusion of sheaves with transfers into presheaves with transfers. -/
def nisnevichSheafificationAdjunction :
    nisnevichSheafify k ⊣ SheafWithTransfers.forget k :=
  Adjunction.mkOfHomEquiv
    { homEquiv := nisnevichSheafificationHomEquiv k
      homEquiv_naturality_left_symm := by
        intro P' P Q η θ
        apply ObjectProperty.hom_ext
        apply ObjectProperty.hom_ext
        exact (sheafifyMap_sheafifyLift (Cor.nisnevichTopology k) η.hom θ.hom _).symm
      homEquiv_naturality_right := by
        intro P Q Q' η θ
        change toNisnevichSheafify k P ≫ (η.hom ≫ θ.hom) =
          (toNisnevichSheafify k P ≫ η.hom) ≫ θ.hom
        exact (Category.assoc _ _ _).symm }

/-- The adjunction uses precisely the actual sheafification unit. -/
@[simp]
theorem nisnevichSheafificationAdjunction_unit_app (P : PresheafWithTransfers.{u + 1} k) :
    (nisnevichSheafificationAdjunction k).unit.app P = toNisnevichSheafify k P := by
  change toNisnevichSheafify k P ≫ 𝟙 _ = _
  exact Category.comp_id _

instance : (nisnevichSheafify k).IsLeftAdjoint :=
  (nisnevichSheafificationAdjunction k).isLeftAdjoint

/-- Sheafification changes no object already satisfying ordinary Nisnevich
sheaf descent, including its complete signed transfer action. -/
theorem isIso_toNisnevichSheafify (P : PresheafWithTransfers.{u + 1} k)
    (hP : IsNisnevichSheaf k P) : IsIso (toNisnevichSheafify k P) := by
  apply (ObjectProperty.isIso_hom_iff _).mp
  exact isIso_toSheafify (Cor.nisnevichTopology k)
    ((isNisnevichSheaf_iff_correspondenceTopology P).mp hP)

/-- Additivity on morphisms between transfer presheaves, separate from the
source-arrow additivity used to construct every sheafified object. -/
instance : (nisnevichSheafify k).Additive where
  map_add {P Q} η θ := by
    apply nisnevichSheafify_hom_ext k
    change toNisnevichSheafify k P ≫ ((nisnevichSheafify k).map (η + θ)).hom =
      toNisnevichSheafify k P ≫
        (((nisnevichSheafify k).map η).hom + ((nisnevichSheafify k).map θ).hom)
    simp only [Preadditive.comp_add, ← toNisnevichSheafify_naturality,
      Preadditive.add_comp]

/-- The ordinary restriction of the transfer sheafification unit is locally
injective. Only genuine graph cover lifting is used. -/
instance isLocallyInjective_toNisnevichSheafify (P : PresheafWithTransfers.{u + 1} k) :
    Presheaf.IsLocallyInjective (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((toPresheaf k).map (toNisnevichSheafify k P)) := by
  let : (Cor.graphFunctor k).IsCocontinuous
      (SmoothSite.nisnevichTopology (Spec (.of k))) (Cor.nisnevichTopology k) :=
    ⟨fun h => Cor.graph_functorPullback_mem_nisnevichTopology k h⟩
  exact Presheaf.isLocallyInjective_whisker
    (SmoothSite.nisnevichTopology (Spec (.of k))) (Cor.nisnevichTopology k)
    (Cor.graphFunctor k) (toSheafify (Cor.nisnevichTopology k) P.obj)

/-- The ordinary restriction of the transfer sheafification unit is locally
surjective on actual smooth Nisnevich covers. -/
instance isLocallySurjective_toNisnevichSheafify (P : PresheafWithTransfers.{u + 1} k) :
    Presheaf.IsLocallySurjective (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((toPresheaf k).map (toNisnevichSheafify k P)) := by
  let : (Cor.graphFunctor k).IsCocontinuous
      (SmoothSite.nisnevichTopology (Spec (.of k))) (Cor.nisnevichTopology k) :=
    ⟨fun h => Cor.graph_functorPullback_mem_nisnevichTopology k h⟩
  exact Presheaf.isLocallySurjective_whisker
    (SmoothSite.nisnevichTopology (Spec (.of k))) (Cor.nisnevichTopology k)
    (Cor.graphFunctor k) (toSheafify (Cor.nisnevichTopology k) P.obj)

section OrdinaryComparison

variable [HasWeakSheafify (SmoothSite.nisnevichTopology (Spec (.of k)))
  AddCommGrpCat.{u + 1}]

/-- The canonical comparison from ordinary Nisnevich sheafification to the
underlying ordinary sheaf of transfer-preserving sheafification. -/
def nisnevichSheafifyUnderlyingComparison (P : PresheafWithTransfers.{u + 1} k) :
    (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat).obj
      ((toPresheaf k).obj P) ⟶
    (SheafWithTransfers.toSheaf k).obj ((nisnevichSheafify k).obj P) :=
  ⟨sheafifyLift (SmoothSite.nisnevichTopology (Spec (.of k)))
    ((toPresheaf k).map (toNisnevichSheafify k P)) ((nisnevichSheafify k).obj P).property⟩

/-- The ordinary comparison carries the ordinary unit to the restriction of
the transfer-natural unit. -/
@[reassoc (attr := simp)]
theorem toSheafify_nisnevichSheafifyUnderlyingComparison
    (P : PresheafWithTransfers.{u + 1} k) :
    toSheafify (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P) ≫
      (nisnevichSheafifyUnderlyingComparison k P).hom =
        (toPresheaf k).map (toNisnevichSheafify k P) :=
  toSheafify_sheafifyLift _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the ordinary comparison for transfer-natural morphisms. -/
@[reassoc]
theorem nisnevichSheafifyUnderlyingComparison_naturality
    {P Q : PresheafWithTransfers.{u + 1} k} (η : P ⟶ Q) :
    (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat).map
      ((toPresheaf k).map η) ≫ nisnevichSheafifyUnderlyingComparison k Q =
    nisnevichSheafifyUnderlyingComparison k P ≫
      (SheafWithTransfers.toSheaf k).map ((nisnevichSheafify k).map η) := by
  apply ObjectProperty.hom_ext
  apply sheafify_hom_ext (SmoothSite.nisnevichTopology (Spec (.of k))) _ _
    ((nisnevichSheafify k).obj Q).property
  change toSheafify _ _ ≫ (sheafifyMap _ ((toPresheaf k).map η) ≫
    (nisnevichSheafifyUnderlyingComparison k Q).hom) =
    toSheafify _ _ ≫ ((nisnevichSheafifyUnderlyingComparison k P).hom ≫
      (toPresheaf k).map ((nisnevichSheafify k).map η).hom)
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    toSheafify_nisnevichSheafifyUnderlyingComparison,
    ← Category.assoc, toSheafify_nisnevichSheafifyUnderlyingComparison,
    ← Functor.map_comp, ← Functor.map_comp, toNisnevichSheafify_naturality]

variable [(SmoothSite.nisnevichTopology (Spec (.of k))).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(SmoothSite.nisnevichTopology (Spec (.of k))).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]

/-- The ordinary comparison is an isomorphism because the restricted
transfer unit is locally bijective and its target is an ordinary sheaf. -/
instance isIso_nisnevichSheafifyUnderlyingComparison
    (P : PresheafWithTransfers.{u + 1} k) :
    IsIso (nisnevichSheafifyUnderlyingComparison k P) := by
  apply (ObjectProperty.isIso_hom_iff _).mp
  exact isIso_sheafifyLift_of_isLocallyBijective
    (SmoothSite.nisnevichTopology (Spec (.of k)))
    ((toPresheaf k).map (toNisnevichSheafify k P)) ((nisnevichSheafify k).obj P).property

/-- Forgetting transfers after transfer sheafification is canonically
isomorphic to genuine ordinary smooth-site Nisnevich sheafification. -/
def nisnevichSheafificationUnderlyingIso :
    toPresheaf k ⋙ presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1} ≅
    nisnevichSheafify k ⋙ SheafWithTransfers.toSheaf k :=
  NatIso.ofComponents (fun P => asIso (nisnevichSheafifyUnderlyingComparison k P))
    (fun η => nisnevichSheafifyUnderlyingComparison_naturality k η)

/-- The natural comparison agrees with the canonical unit on the nose. -/
@[reassoc (attr := simp)]
theorem toSheafify_nisnevichSheafificationUnderlyingIso
    (P : PresheafWithTransfers.{u + 1} k) :
    toSheafify (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P) ≫
      ((nisnevichSheafificationUnderlyingIso k).hom.app P).hom =
        (toPresheaf k).map (toNisnevichSheafify k P) :=
  toSheafify_nisnevichSheafifyUnderlyingComparison k P

end OrdinaryComparison

end Motivic.PresheafWithTransfers
