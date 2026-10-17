module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.RestrictedBoundaryFrame
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryFramePullback
/-! # The actual restricted frame on the original source product -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X Z : Scheme.{u}} (q : X ⟶ S) (U : X.Opens) (z : Z ⟶ X)

/-- Two literal pullback squares identify the source product with the open restriction. -/
def openBoundaryProductIso : pullback (U.ι ≫ q) (z ≫ q) ≅
    ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).toScheme :=
  (boundaryProductMap_isPullback q U.ι z).isoPullback ≪≫
    (isPullback_morphismRestrict (pullback.fst q (z ≫ q)) U).isoPullback.symm

@[reassoc]
theorem openBoundaryProductIso_hom_ι :
    (openBoundaryProductIso q U z).hom ≫ ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).ι =
      boundaryProductMap q U.ι z := by
  simp only [openBoundaryProductIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    IsPullback.isoPullback_inv_snd, IsPullback.isoPullback_hom_snd]

/-- Pull back the original chosen open frame through the canonical product comparison. -/
def openBoundaryPulledFrame
    (e : (idealModule (boundaryGraphTarget q z)).restrict
      ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).ι ≅
      SheafOfModules.unit ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).toScheme.ringCatSheaf) :
    SheafOfModules.unit (pullback (U.ι ≫ q) (z ≫ q)).ringCatSheaf ≅
      (Modules.pullback (boundaryProductMap q U.ι z)).obj
        (idealModule (boundaryGraphTarget q z)) :=
  (pullbackUnitIso (openBoundaryProductIso q U z).hom).symm ≪≫
    (Modules.pullback (openBoundaryProductIso q U z).hom).mapIso e.symm ≪≫
    (Modules.pullback (openBoundaryProductIso q U z).hom).mapIso
      ((restrictFunctorIsoPullback ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).ι).app
        (idealModule (boundaryGraphTarget q z))) ≪≫
    ((Modules.pullbackComp (openBoundaryProductIso q U z).hom
      ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).ι ≪≫
      Modules.pullbackCongr (openBoundaryProductIso_hom_ι q U z)).app
        (idealModule (boundaryGraphTarget q z)))

variable (s : Z ⟶ U.toScheme) (hs : s ≫ U.ι = z)

include hs in
/-- The full boundary lift through an actual open is Cartesian, including nilpotents. -/
theorem openBoundaryLift_isPullback : IsPullback s (𝟙 Z) U.ι z :=
  IsPullback.of_vert_isIso_mono ⟨by simpa using hs⟩

variable [IsSeparated q] [SmoothOfRelativeDimension 1 q]

/-- The local finite-boundary frame is now a frame of the original open-source graph ideal. -/
def openSourceBoundaryFrame
    (e : (idealModule (boundaryGraphTarget q z)).restrict
      ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).ι ≅
      SheafOfModules.unit ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).toScheme.ringCatSheaf) :
    SheafOfModules.unit (pullback (U.ι ≫ q) (z ≫ q)).ringCatSheaf ≅
      idealModule (boundaryGraphSource q U.ι z s hs) := by
  have := relativeBoundaryGraph_closed q z
  have : (idealModule (boundaryGraphTarget q z)).IsQuasicoherent := by
    have := finiteLocallyFree_of_isLocallyRankOne (relativeBoundaryGraphLine q z).val
      (relativeBoundaryGraphLine q z).property
    exact inferInstanceAs ((relativeBoundaryGraphLine q z).val.IsQuasicoherent)
  let H := boundaryGraph_isPullback q U.ι z s hs (openBoundaryLift_isPullback U z s hs)
  have : IsClosedImmersion (boundaryGraphSource q U.ι z s hs) :=
    MorphismProperty.of_isPullback H inferInstance
  let v := idealPullbackMap (boundaryGraphTarget q z) (boundaryGraphSource q U.ι z s hs)
    (boundaryProductMap q U.ι z) (𝟙 Z) H.w
  have : IsIso v := idealPullbackMap_isIso_of_flat_ambient _ _ _ _ _ H
  exact openBoundaryPulledFrame q U z e ≪≫ asIso v

@[reassoc]
theorem openSourceBoundaryFrame_inclusion
    (e : (idealModule (boundaryGraphTarget q z)).restrict
      ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).ι ≅
      SheafOfModules.unit ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).toScheme.ringCatSheaf) :
    (openSourceBoundaryFrame q U z s hs e).hom ≫
      idealInclusion (boundaryGraphSource q U.ι z s hs) =
    (openBoundaryPulledFrame q U z e).hom ≫
      Modules.Hom.pullbackToUnit (idealInclusion (boundaryGraphTarget q z))
        (boundaryProductMap q U.ι z) := by
  simp only [openSourceBoundaryFrame, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [idealPullbackMap_inclusion]
  rfl
/-- The actual product reassociation identifies the open-source graph with the
canonical boundary graph for the restricted curve and the unchanged full boundary. -/
def openCanonicalBoundaryProductIso : pullback (U.ι ≫ q) (z ≫ q) ≅
    pullback (U.ι ≫ q) (s ≫ (U.ι ≫ q)) :=
  pullback.congrHom rfl (by rw [← Category.assoc, hs])

/-- The local frame is now on precisely the canonical graph ideal expected by the
relative Serre pencil, not an abstract isomorphic line-bundle class. -/
def openCanonicalBoundaryFrame
    (e : (idealModule (boundaryGraphTarget q z)).restrict
      ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).ι ≅
      SheafOfModules.unit ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).toScheme.ringCatSheaf) :
    SheafOfModules.unit (pullback (U.ι ≫ q) (s ≫ (U.ι ≫ q))).ringCatSheaf ≅
      idealModule (boundaryGraphTarget (U.ι ≫ q) s) := by
  let P := openCanonicalBoundaryProductIso q U z s hs
  have he : (𝟙 Z) ≫ boundaryGraphSource q U.ι z s hs =
      boundaryGraphTarget (U.ι ≫ q) s ≫ P.inv := by
    apply (cancel_mono P.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply pullback.hom_ext <;>
      simp [P, openCanonicalBoundaryProductIso, boundaryGraphSource,
        boundaryGraphTarget, pullback.congrHom]
  let v := idealPullbackMap (boundaryGraphSource q U.ι z s hs)
    (boundaryGraphTarget (U.ι ≫ q) s) P.inv (𝟙 Z) he
  have : IsIso v := idealPullbackMap_isIso_of_iso_square _ _ _ _ _
  exact (pullbackUnitIso P.inv).symm ≪≫
    (Modules.pullback P.inv).mapIso (openSourceBoundaryFrame q U z s hs e) ≪≫ asIso v

/-- The canonical inclusion is transported through the literal original product
isomorphism, keeping the coefficient needed by both sides of the pencil. -/
@[reassoc]
theorem openCanonicalBoundaryFrame_inclusion
    (e : (idealModule (boundaryGraphTarget q z)).restrict
      ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).ι ≅
      SheafOfModules.unit ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).toScheme.ringCatSheaf) :
    (openCanonicalBoundaryFrame q U z s hs e).hom ≫
      idealInclusion (boundaryGraphTarget (U.ι ≫ q) s) =
    unitEndomorphismPullback (openCanonicalBoundaryProductIso q U z s hs).inv
      ((openSourceBoundaryFrame q U z s hs e).hom ≫
        idealInclusion (boundaryGraphSource q U.ι z s hs)) := by
  simp only [openCanonicalBoundaryFrame, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, asIso_hom, Category.assoc, unitEndomorphismPullback,
    Functor.map_comp]
  rw [idealPullbackMap_inclusion]
  rfl
end AlgebraicGeometry.Scheme.Hom
