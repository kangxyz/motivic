module
import Motivic.Cohomology.A1.Purity.FieldZeroSection.Excision
/-! Direct original-map consumer for field zero-section Nisnevich excision. -/
set_option linter.hashCommand false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe w u
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

example
    (c : PresheafWithTransfers.sections (PresheafWithTransfers.contraction F.obj)
      (Cor.mk (SmoothSite.base (Spec (.of k))))) :
    fieldZeroSectionExcision F hF j a b h hpb z hcomp c =
      LargeCohomology.relativeRestriction.{w, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) j
        (SmoothSite.contractionOpen (.of k) (SmoothSite.base (Spec (.of k))))
        a b h ((toSheaf k).obj F) 1 (contractionToRelative F _ c) :=
  fieldZeroSectionExcision_apply F hF j a b h hpb z hcomp c
#print axioms fieldZeroSectionExcision
#print axioms fieldZeroSectionExcision_apply
end Motivic.SheafWithTransfers
