/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.Purity.FieldZeroSection.Basic
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Cohomology.RelativeExcision
/-! # The field zero-section model on genuine Nisnevich neighborhoods

The comparison uses the original relative restriction through a Cartesian
étale neighborhood, isomorphic over the whole closed complement. No purity,
cohomology vanishing, or abstract comparison isomorphism is an input.
This remains a field zero-section model, not general smooth-divisor purity.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe w u
namespace AlgebraicGeometry.Scheme.SmoothSite
variable (k : Type u) [Field k]
instance fieldContractionOpen_open : IsOpenImmersion
    (contractionOpen (.of k) (base (Spec (.of k)))).left := by
  let e := baseCylinderCurveLineIso k
  have he : contractionOpen (.of k) (base (Spec (.of k))) ≫ e.hom =
      productSnd (base (Spec (.of k))) (torus (.of k)) ≫ torusInAffineLine (.of k) :=
    productMap_snd _ _
  have : IsOpenImmersion (productSnd (base (Spec (.of k))) (torus (.of k))).left :=
    inferInstanceAs (IsOpenImmersion (pullback.snd (𝟙 (Spec (.of k))) (torus (.of k)).hom))
  have : IsOpenImmersion
      ((contractionOpen (.of k) (base (Spec (.of k)))).left ≫ e.hom.left) := by
    change IsOpenImmersion ((contractionOpen (.of k) (base (Spec (.of k)))) ≫ e.hom).left
    rw [he]
    change IsOpenImmersion ((productSnd (base (Spec (.of k))) (torus (.of k))).left ≫
      (torusInAffineLine (.of k)).left)
    infer_instance
  exact IsOpenImmersion.of_comp _ e.hom.left
end AlgebraicGeometry.Scheme.SmoothSite
namespace Motivic.SheafWithTransfers
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.Sheaf
variable {k : Type u} [Field k]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [EnoughInjectives
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  (F : SheafWithTransfers.{u + 1} k) (hF : PresheafWithTransfers.IsA1Invariant F.obj)
  {W V : SmoothSite (Spec (.of k))}
  (j : W ⟶ V)
  (a : W ⟶ SmoothSite.torusCylinder (.of k) (SmoothSite.base (Spec (.of k))))
  (b : V ⟶ SmoothSite.a1Cylinder (.of k) (SmoothSite.base (Spec (.of k))))
  (h : j ≫ b = a ≫ SmoothSite.contractionOpen (.of k) (SmoothSite.base (Spec (.of k))))
  (hpb : IsPullback a j
    (SmoothSite.contractionOpen (.of k) (SmoothSite.base (Spec (.of k)))) b)
  [Etale b.left]
  {Z : Scheme.{u}} (z : Z ⟶ (SmoothSite.a1Cylinder (.of k)
    (SmoothSite.base (Spec (.of k)))).left) [IsClosedImmersion z]
  (hcomp : Set.range z = (Set.range
    (SmoothSite.contractionOpen (.of k) (SmoothSite.base (Spec (.of k)))).left)ᶜ)
  [IsIso (pullback.snd b.left z)]

/-- The actual field model transported by genuine relative Nisnevich restriction. -/
def fieldZeroSectionExcision :
    PresheafWithTransfers.sections (PresheafWithTransfers.contraction F.obj)
      (Cor.mk (SmoothSite.base (Spec (.of k)))) ≃+
    LargeCohomology.relativeH.{w, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      j ((toSheaf k).obj F) 1 :=
  (fieldZeroSectionPurity F hF).trans
    (LargeCohomology.relativeNisnevichExcisionIso.{w, u + 1, u}
      ⟨a, j, SmoothSite.contractionOpen (.of k) (SmoothSite.base (Spec (.of k))), b, h.symm⟩
      hpb z hcomp ((toSheaf k).obj F) 1).addCommGroupIsoToAddEquiv

/-- Its map is exactly the original relative restriction of the signed field boundary. -/
theorem fieldZeroSectionExcision_apply
    (c : PresheafWithTransfers.sections (PresheafWithTransfers.contraction F.obj)
      (Cor.mk (SmoothSite.base (Spec (.of k))))) :
    fieldZeroSectionExcision F hF j a b h hpb z hcomp c =
      LargeCohomology.relativeRestriction.{w, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) j
        (SmoothSite.contractionOpen (.of k) (SmoothSite.base (Spec (.of k))))
        a b h ((toSheaf k).obj F) 1 (contractionToRelative F _ c) := rfl
end Motivic.SheafWithTransfers
