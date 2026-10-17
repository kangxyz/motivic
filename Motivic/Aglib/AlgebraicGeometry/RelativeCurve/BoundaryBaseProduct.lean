module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryBaseOpenGeometry
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.OpenSourceBoundaryFrame
/-! # Canonical boundary products under the simultaneous actual base and source shrink -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X Z : Scheme.{u}} (q : X ⟶ S) (z : Z ⟶ X)
  (U : X.Opens) (V : S.Opens)
  (h : ∀ t : Z, (z ≫ q) t ∈ V → z t ∈ U)

theorem boundaryBaseOuter_isPullback :
    IsPullback
      (pullback.fst (boundaryBaseSourceProjection q U V) ((z ≫ q) ∣_ V))
      (pullback.snd (boundaryBaseSourceProjection q U V) ((z ≫ q) ∣_ V) ≫
        (boundaryBaseClosedOpen q z V).ι)
      ((boundaryBaseSourceOpen q U V).ι ≫ q) (z ≫ q) := by
  have H := ((IsPullback.of_hasPullback (boundaryBaseSourceProjection q U V)
    ((z ≫ q) ∣_ V)).flip.paste_horiz
      (isPullback_morphismRestrict (z ≫ q) V).flip).flip
  simpa only [boundaryBaseSourceProjection_ι] using H

/-- The native product of the new curve and full retained boundary is precisely an open
restriction of the original product. Both comparisons are actual Cartesian comparisons. -/
def boundaryBaseProductIso :
    pullback (boundaryBaseSourceProjection q U V)
      (boundaryBaseLift q z U V h ≫ boundaryBaseSourceProjection q U V) ≅
    ((pullback.fst q (z ≫ q)) ⁻¹ᵁ boundaryBaseSourceOpen q U V).toScheme :=
  pullback.congrHom rfl (boundaryBaseLift_projection q z U V h) ≪≫
    (boundaryBaseOuter_isPullback q z U V).isoPullback ≪≫
    openBoundaryProductIso q (boundaryBaseSourceOpen q U V) z

/-- The literal map to the original product, not an abstract identification of fibres. -/
def boundaryBaseProductMap :
    pullback (boundaryBaseSourceProjection q U V)
      (boundaryBaseLift q z U V h ≫ boundaryBaseSourceProjection q U V) ⟶
    pullback q (z ≫ q) :=
  (boundaryBaseProductIso q z U V h).hom ≫
    ((pullback.fst q (z ≫ q)) ⁻¹ᵁ boundaryBaseSourceOpen q U V).ι

instance boundaryBaseProductMap_open : IsOpenImmersion (boundaryBaseProductMap q z U V h) := by
  dsimp [boundaryBaseProductMap]
  infer_instance

@[reassoc (attr := simp)]
theorem boundaryBaseProductMap_fst :
    boundaryBaseProductMap q z U V h ≫ pullback.fst q (z ≫ q) =
      pullback.fst _ _ ≫ (boundaryBaseSourceOpen q U V).ι := by
  simp only [boundaryBaseProductMap, boundaryBaseProductIso, Iso.trans_hom, Category.assoc,
    openBoundaryProductIso_hom_ι_assoc, boundaryProductMap, pullback.lift_fst,
    IsPullback.isoPullback_hom_fst_assoc]
  simp [pullback.congrHom]

@[reassoc (attr := simp)]
theorem boundaryBaseProductMap_snd :
    boundaryBaseProductMap q z U V h ≫ pullback.snd q (z ≫ q) =
      pullback.snd _ _ ≫ (boundaryBaseClosedOpen q z V).ι := by
  simp only [boundaryBaseProductMap, boundaryBaseProductIso, Iso.trans_hom, Category.assoc,
    openBoundaryProductIso_hom_ι_assoc, boundaryProductMap, pullback.lift_snd,
    IsPullback.isoPullback_hom_snd]
  simp [pullback.congrHom]

/-- The canonical boundary graph has the original full closed-scheme pullback. -/
theorem boundaryBaseGraph_isPullback :
    IsPullback (boundaryBaseClosedOpen q z V).ι
      (boundaryGraphTarget (boundaryBaseSourceProjection q U V) (boundaryBaseLift q z U V h))
      (boundaryGraphTarget q z) (boundaryBaseProductMap q z U V h) := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · apply pullback.hom_ext <;>
      simp [boundaryGraphTarget, boundaryBaseLift_ι]
  · simp only [boundaryBaseProductMap, Scheme.Hom.opensRange_comp_of_isIso,
      Scheme.Opens.opensRange_ι]
    ext t
    change ((boundaryGraphTarget q z ≫ pullback.fst q (z ≫ q)) t ∈
      boundaryBaseSourceOpen q U V) ↔ (z ≫ q) t ∈ V
    simp only [boundaryGraphTarget, pullback.lift_fst]
    change (z t ∈ U ∧ (z ≫ q) t ∈ V) ↔ (z ≫ q) t ∈ V
    exact ⟨And.right, fun ht => ⟨h t ht, ht⟩⟩
end AlgebraicGeometry.Scheme.Hom
