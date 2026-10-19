/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Basic
public import Motivic.Transfers.Presheaf.NisnevichSheafification
public import Motivic.Transfers.Presheaf.Limits
public import Motivic.Aglib.CategoryTheory.AdditiveFunctorAbelian


/-!
# The homotopy-invariant image of the actual sheafification unit

The native image of the transfer-natural Nisnevich unit is an HI presheaf
whenever the original presheaf is HI. It is separated and locally generates
the actual sheafification. These statements do not assume or prove homotopy
invariance of the sheafification itself.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v w w'

namespace Motivic.A1

variable (R : CommRingCat.{u}) {A : Type w} [Category.{w'} A]

/-- Homotopy invariance descends along a pointwise epimorphic natural map.
The inverse is the original zero-section pullback. -/
theorem isInvariant_of_epi_app
    {P Q : (SmoothSite (Spec R))ᵒᵖ ⥤ A} (η : P ⟶ Q)
    [∀ X, Epi (η.app X)] (hP : IsInvariant R P) : IsInvariant R Q := by
  intro X
  let p := projectionPullback R Q X
  let s := sectionPullback R Q X 0
  have hp : p ≫ s = 𝟙 _ := projectionPullback_sectionPullback R Q X 0
  have hs : s ≫ p = 𝟙 _ := by
    apply (cancel_epi (η.app (op (SmoothSite.a1Cylinder R X)))).mp
    have hn := η.naturality (SmoothSite.a1Section R X 0).op
    have hm := η.naturality (SmoothSite.a1Projection R X).op
    change sectionPullback R P X 0 ≫ η.app (op X) =
      η.app (op (SmoothSite.a1Cylinder R X)) ≫ s at hn
    change projectionPullback R P X ≫ η.app (op (SmoothSite.a1Cylinder R X)) =
      η.app (op X) ≫ p at hm
    rw [← Category.assoc, ← hn, Category.assoc, ← hm, ← Category.assoc]
    have he : sectionPullback R P X 0 ≫ projectionPullback R P X = 𝟙 _ := by
      rw [← projectionIso_inv R P hP X 0]
      exact (projectionIso R P hP X).inv_hom_id
    rw [he, Category.id_comp, Category.comp_id]
  exact ⟨⟨s, hp, hs⟩⟩

end Motivic.A1

namespace Motivic.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- HI of the original graph restrictions descends through a pointwise epi. -/
theorem isA1Invariant_of_epi_app
    {P Q : PresheafWithTransfers.{v} k} (η : P ⟶ Q)
    [∀ X : Cor k, Epi (η.hom.app (op X))] (hP : P.IsA1Invariant) :
    Q.IsA1Invariant := by
  have (X : (SmoothSite (Spec (.of k)))ᵒᵖ) :
      Epi (((toPresheaf k).map η).app X) :=
    inferInstanceAs (Epi (η.hom.app (op (Cor.mk X.unop))))
  exact A1.isInvariant_of_epi_app (.of k) ((toPresheaf k).map η) hP

/-- The native PST image of the actual transfer-preserving sheafification unit. -/
def nisnevichImage (P : PresheafWithTransfers.{u + 1} k) :
    PresheafWithTransfers.{u + 1} k := image (toNisnevichSheafify k P)

/-- The actual epimorphism from the original presheaf onto its unit image. -/
def toNisnevichImage (P : PresheafWithTransfers.{u + 1} k) : P ⟶ nisnevichImage P :=
  factorThruImage (toNisnevichSheafify k P)

/-- The actual monomorphism from the unit image into the original sheafification. -/
def nisnevichImageι (P : PresheafWithTransfers.{u + 1} k) :
    nisnevichImage P ⟶ ((nisnevichSheafify k).obj P).obj :=
  image.ι (toNisnevichSheafify k P)

@[reassoc (attr := simp)]
theorem toNisnevichImage_ι (P : PresheafWithTransfers.{u + 1} k) :
    toNisnevichImage P ≫ nisnevichImageι P = toNisnevichSheafify k P :=
  image.fac _

instance (P : PresheafWithTransfers.{u + 1} k) : Epi (toNisnevichImage P) := by
  dsimp [toNisnevichImage]
  infer_instance

instance (P : PresheafWithTransfers.{u + 1} k) : Mono (nisnevichImageι P) := by
  dsimp [nisnevichImageι]
  infer_instance

instance (P : PresheafWithTransfers.{u + 1} k) : Epi (toNisnevichImage P).hom :=
  inferInstanceAs (Epi ((forget).map (toNisnevichImage P)))

instance (P : PresheafWithTransfers.{u + 1} k) : Mono (nisnevichImageι P).hom :=
  inferInstanceAs (Mono ((forget).map (nisnevichImageι P)))

instance (P : PresheafWithTransfers.{u + 1} k) (X : Cor k) :
    Epi ((toNisnevichImage P).hom.app (op X)) := by infer_instance

instance (P : PresheafWithTransfers.{u + 1} k) (X : Cor k) :
    Mono ((nisnevichImageι P).hom.app (op X)) := by infer_instance

instance (P : PresheafWithTransfers.{u + 1} k) :
    Mono ((toPresheaf k).map (nisnevichImageι P)) := by
  exact NatTrans.mono_of_mono_app _

/-- The image is HI by descending the original zero-section inverse. -/
theorem nisnevichImage_isA1Invariant (P : PresheafWithTransfers.{u + 1} k)
    (hP : P.IsA1Invariant) : (nisnevichImage P).IsA1Invariant :=
  isA1Invariant_of_epi_app (toNisnevichImage P) hP

/-- The image is separated because its actual inclusion lands in a sheaf. -/
theorem nisnevichImage_isSeparated (P : PresheafWithTransfers.{u + 1} k) :
    Presheaf.IsSeparated (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((toPresheaf k).obj (nisnevichImage P)) := by
  intro X R hR x y hxy
  let m := (toPresheaf k).map (nisnevichImageι P)
  apply (AddCommGrpCat.mono_iff_injective (m.app (op X))).mp inferInstance
  apply ((nisnevichSheafify k).obj P).property.isSeparated X R hR
  intro Y f hf
  rw [← m.naturality_apply, ← m.naturality_apply, hxy Y f hf]

/-- The unit image locally generates the genuine ordinary sheafification. -/
instance isLocallySurjective_nisnevichImageι (P : PresheafWithTransfers.{u + 1} k) :
    Presheaf.IsLocallySurjective (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((toPresheaf k).map (nisnevichImageι P)) := by
  apply Presheaf.isLocallySurjective_of_isLocallySurjective_fac
    (SmoothSite.nisnevichTopology (Spec (.of k)))
    (f₁ := (toPresheaf k).map (toNisnevichImage P))
    (f₃ := (toPresheaf k).map (toNisnevichSheafify k P))
  rw [← Functor.map_comp, toNisnevichImage_ι]

instance isLocallyInjective_nisnevichImageι (P : PresheafWithTransfers.{u + 1} k) :
    Presheaf.IsLocallyInjective (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((toPresheaf k).map (nisnevichImageι P)) := by
  apply Presheaf.isLocallyInjective_of_injective
  intro X
  exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance

/-- Canonical ordinary sheafification comparison for the actual unit image. -/
def nisnevichImageSheafificationComparison (P : PresheafWithTransfers.{u + 1} k) :
    (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj ((toPresheaf k).obj (nisnevichImage P)) ⟶
    (SheafWithTransfers.toSheaf k).obj ((nisnevichSheafify k).obj P) :=
  ⟨sheafifyLift _ ((toPresheaf k).map (nisnevichImageι P))
    ((nisnevichSheafify k).obj P).property⟩

instance (P : PresheafWithTransfers.{u + 1} k) :
    IsIso (nisnevichImageSheafificationComparison P) := by
  apply (ObjectProperty.isIso_hom_iff _).mp
  exact isIso_sheafifyLift_of_isLocallyBijective _
    ((toPresheaf k).map (nisnevichImageι P)) ((nisnevichSheafify k).obj P).property

/-- Sheafifying the separated image recovers the original sheafification. -/
def nisnevichImageSheafificationIso (P : PresheafWithTransfers.{u + 1} k) :
    (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj ((toPresheaf k).obj (nisnevichImage P)) ≅
    (SheafWithTransfers.toSheaf k).obj ((nisnevichSheafify k).obj P) :=
  asIso (nisnevichImageSheafificationComparison P)

/-- The comparison identifies the sheafification unit with the actual image inclusion. -/
@[reassoc (attr := simp)]
theorem toSheafify_nisnevichImageSheafificationIso
    (P : PresheafWithTransfers.{u + 1} k) :
    toSheafify (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((toPresheaf k).obj (nisnevichImage P)) ≫
      (nisnevichImageSheafificationIso P).hom.hom =
        (toPresheaf k).map (nisnevichImageι P) :=
  toSheafify_sheafifyLift _ _ _

end Motivic.PresheafWithTransfers
