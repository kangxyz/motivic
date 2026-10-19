module

import Motivic.Cohomology.A1.Purity.FieldZeroSection.Basic

/-! Direct consumers of the field zero-section model and its signed boundary. -/
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry

universe w u

namespace Motivic.MotivicTest
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [EnoughInjectives
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  (F : SheafWithTransfers.{u + 1} k)
  (hF : PresheafWithTransfers.IsA1Invariant F.obj)

example (z : SheafWithTransfers.contractionRelativeH F
    (Cor.mk (SmoothSite.base (Spec (.of k))))) :
    ∃ c, SheafWithTransfers.contractionToRelative F _ c = z :=
  SheafWithTransfers.field_contractionToRelative_surjective F hF z

example (c : PresheafWithTransfers.sections (PresheafWithTransfers.contraction F.obj)
    (Cor.mk (SmoothSite.base (Spec (.of k))))) :
    SheafWithTransfers.fieldZeroSectionPurity F hF c =
      SheafWithTransfers.contractionToRelative F _ c := rfl

example (s : PresheafWithTransfers.sections (PresheafWithTransfers.torusSections F.obj)
    (Cor.mk (SmoothSite.base (Spec (.of k))))) :
    SheafWithTransfers.fieldZeroSectionPurity F hF
        ((PresheafWithTransfers.toContraction F.obj).hom.app
          (Opposite.op (Cor.mk (SmoothSite.base (Spec (.of k))))) s) =
      SheafWithTransfers.contractionSectionBoundary F _ s :=
  SheafWithTransfers.fieldZeroSectionPurity_toContraction F hF s

#print axioms Motivic.SheafWithTransfers.fieldZeroSectionPurity
#print axioms Motivic.SheafWithTransfers.field_contractionToRelative_surjective

end Motivic.MotivicTest
