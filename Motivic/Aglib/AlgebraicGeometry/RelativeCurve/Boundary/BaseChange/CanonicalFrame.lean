module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.Product
/-! # A constructed graph frame after the actual common base and source shrink -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X Z : Scheme.{u}} (q : X ⟶ S) (z : Z ⟶ X)
  (U : X.Opens) (V : S.Opens)
  (h : ∀ t : Z, (z ≫ q) t ∈ V → z t ∈ U)
  (e : (idealModule (boundaryGraphTarget q z)).restrict
    ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).ι ≅
    SheafOfModules.unit ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).toScheme.ringCatSheaf)

/-- Transport of the same chosen frame, through the original product comparison. -/
def boundaryBasePulledFrame :
    SheafOfModules.unit
      (pullback (boundaryBaseSourceProjection q U V)
        (boundaryBaseLift q z U V h ≫ boundaryBaseSourceProjection q U V)).ringCatSheaf ≅
    (Modules.pullback (boundaryBaseProductMap q z U V h)).obj
      (idealModule (boundaryGraphTarget q z)) := by
  let W := (pullback.fst q (z ≫ q)) ⁻¹ᵁ boundaryBaseSourceOpen q U V
  let e' := restrictUnitIsoOfLE (idealModule (boundaryGraphTarget q z))
    (show W ≤ (pullback.fst q (z ≫ q)) ⁻¹ᵁ U from fun _ hx => hx.1) e
  let P := boundaryBaseProductIso q z U V h
  exact (pullbackUnitIso P.hom).symm ≪≫
    (Modules.pullback P.hom).mapIso e'.symm ≪≫
    (Modules.pullback P.hom).mapIso
      ((restrictFunctorIsoPullback W.ι).app (idealModule (boundaryGraphTarget q z))) ≪≫
    (Modules.pullbackComp P.hom W.ι).app (idealModule (boundaryGraphTarget q z))

variable [IsSeparated q] [SmoothOfRelativeDimension 1 q]

/-- The frame is on the literal canonical graph ideal of the simultaneously shrunk curve. -/
def boundaryBaseCanonicalFrame :
    SheafOfModules.unit
      (pullback (boundaryBaseSourceProjection q U V)
        (boundaryBaseLift q z U V h ≫ boundaryBaseSourceProjection q U V)).ringCatSheaf ≅
    idealModule (boundaryGraphTarget (boundaryBaseSourceProjection q U V)
      (boundaryBaseLift q z U V h)) := by
  have := relativeBoundaryGraph_closed q z
  have : (idealModule (boundaryGraphTarget q z)).IsQuasicoherent := by
    have := finiteLocallyFree_of_isLocallyRankOne (relativeBoundaryGraphLine q z).val
      (relativeBoundaryGraphLine q z).property
    exact inferInstanceAs ((relativeBoundaryGraphLine q z).val.IsQuasicoherent)
  let H := boundaryBaseGraph_isPullback q z U V h
  have : IsClosedImmersion (boundaryGraphTarget (boundaryBaseSourceProjection q U V)
      (boundaryBaseLift q z U V h)) := MorphismProperty.of_isPullback H inferInstance
  let v := idealPullbackMap (boundaryGraphTarget q z)
    (boundaryGraphTarget (boundaryBaseSourceProjection q U V) (boundaryBaseLift q z U V h))
    (boundaryBaseProductMap q z U V h) (boundaryBaseClosedOpen q z V).ι H.w
  have : IsIso v := idealPullbackMap_isIso_of_flat_ambient _ _ _ _ _ H
  exact boundaryBasePulledFrame q z U V h e ≪≫ asIso v

@[reassoc]
theorem boundaryBaseCanonicalFrame_inclusion :
    (boundaryBaseCanonicalFrame q z U V h e).hom ≫
      idealInclusion (boundaryGraphTarget (boundaryBaseSourceProjection q U V)
        (boundaryBaseLift q z U V h)) =
    (boundaryBasePulledFrame q z U V h e).hom ≫
      Modules.Hom.pullbackToUnit (idealInclusion (boundaryGraphTarget q z))
        (boundaryBaseProductMap q z U V h) := by
  simp only [boundaryBaseCanonicalFrame, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [idealPullbackMap_inclusion]
  rfl

/-- Both opens and the actual canonical graph frame are constructed. The full original
boundary is retained over the chosen affine base neighborhood. -/
theorem exists_affine_boundaryBaseCanonicalFrame [IsAffine X] [IsAffine S]
    [IsFinite (z ≫ q)] (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
    ∃ V : S.Opens, IsAffineOpen V ∧ q x ∈ V ∧
    ∃ h : ∀ t : Z, (z ≫ q) t ∈ V → z t ∈ U,
      IsAffineOpen (boundaryBaseSourceOpen q U V) ∧
      Nonempty (SheafOfModules.unit
        (pullback (boundaryBaseSourceProjection q U V)
          (boundaryBaseLift q z U V h ≫ boundaryBaseSourceProjection q U V)).ringCatSheaf ≅
        idealModule (boundaryGraphTarget (boundaryBaseSourceProjection q U V)
          (boundaryBaseLift q z U V h))) := by
  obtain ⟨U, hU, hx, V, hy, hz, ⟨e⟩⟩ :=
    exists_affine_relativeBoundaryFrame_over_base_neighborhood q z x
  obtain ⟨V', hV', hy', hV⟩ := exists_isAffineOpen_mem_and_subset hy
  let h : ∀ t : Z, (z ≫ q) t ∈ V' → z t ∈ U := fun t ht => hz t (hV ht)
  exact ⟨U, hU, hx, V', hV', hy', h, boundaryBaseSourceOpen_affine q U V' hU hV',
    ⟨boundaryBaseCanonicalFrame q z U V' h e⟩⟩
end AlgebraicGeometry.Scheme.Hom
