module

public import Motivic.Cohomology.Sheaf.H1.AffineLineVanishing
public import Motivic.Cohomology.A1.Contraction.Relative
public import Motivic.Cohomology.A1.Moving.CurveEndpointActions

/-!
# The field zero-section model for codimension-one purity

The original contraction quotient is the actual relative degree-one group for
zero in the field affine line. The comparison is the existing signed boundary,
not an abstract isomorphism between groups. Surjectivity follows from the proved
ordinary affine-line H¹ vanishing. No general smooth-divisor purity is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe w u

namespace Motivic.SheafWithTransfers
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.Sheaf

variable {k : Type u} [Field k]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [EnoughInjectives
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  (F : SheafWithTransfers.{u + 1} k)
  (hF : PresheafWithTransfers.IsA1Invariant F.obj)

include hF

/-- The actual relative-forget obstruction vanishes over the field base. -/
theorem field_contractionRelativeForget_eq_zero
    (z : contractionRelativeH F (Cor.mk (SmoothSite.base (Spec (.of k))))) :
    contractionRelativeForget F (Cor.mk (SmoothSite.base (Spec (.of k)))) z = 0 := by
  let P := LargeCohomology.presheaf.{w, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F) 1
  let e := P.mapIso (SmoothSite.baseCylinderCurveLineIso k).symm.op
  apply e.addCommGroupIsoToAddEquiv.injective
  change P.map (SmoothSite.baseCylinderCurveLineIso k).inv.op
      (contractionRelativeForget F (Cor.mk (SmoothSite.base (Spec (.of k)))) z) =
    P.map (SmoothSite.baseCylinderCurveLineIso k).inv.op 0
  rw [map_zero]
  exact SheafCohomology.h_one_affineLine_eq_zero F hF _

/-- Every original relative class is the signed boundary of an actual contraction class. -/
theorem field_contractionToRelative_surjective : Function.Surjective
    (contractionToRelative F (Cor.mk (SmoothSite.base (Spec (.of k))))) := by
  intro z
  exact (contractionToRelative_mem_range_iff F _ z).mpr
    (field_contractionRelativeForget_eq_zero F hF z)

/-- The field zero-section purity model, with the original signed boundary as its map. -/
def fieldZeroSectionPurity :
    PresheafWithTransfers.sections (PresheafWithTransfers.contraction F.obj)
      (Cor.mk (SmoothSite.base (Spec (.of k)))) ≃+
    contractionRelativeH F (Cor.mk (SmoothSite.base (Spec (.of k)))) :=
  AddEquiv.ofBijective (contractionToRelative F _)
    ⟨contractionToRelative_injective F _, field_contractionToRelative_surjective F hF⟩

@[simp] theorem fieldZeroSectionPurity_apply
    (c : PresheafWithTransfers.sections (PresheafWithTransfers.contraction F.obj)
      (Cor.mk (SmoothSite.base (Spec (.of k))))) :
    fieldZeroSectionPurity F hF c = contractionToRelative F _ c := rfl

/-- On an original Laurent section the comparison is the original signed boundary. -/
theorem fieldZeroSectionPurity_toContraction
    (s : PresheafWithTransfers.sections (PresheafWithTransfers.torusSections F.obj)
      (Cor.mk (SmoothSite.base (Spec (.of k))))) :
    fieldZeroSectionPurity F hF
        ((PresheafWithTransfers.toContraction F.obj).hom.app
          (op (Cor.mk (SmoothSite.base (Spec (.of k))))) s) =
      contractionSectionBoundary F (Cor.mk (SmoothSite.base (Spec (.of k)))) s :=
  contractionToRelative_toContraction F _ s

end Motivic.SheafWithTransfers
