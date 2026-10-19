/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Diagonal.OpenProductNeighborhoods
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.Tor

/-!
# Actual restricted support products in open factor neighborhoods

The restricted supports are genuine pullbacks of the original closed
inclusions. They are not declared to be finite-correspondence generators.
Their product retains the exact ambient inclusion and open comparison with
the original support product.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme.Products

open _root_.AlgebraicGeometry.Scheme.Products.OpenNeighborhoods

variable {S X Y Z X' Y' Z' : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (uX : X' ⟶ X) (uY : Y' ⟶ Y) (uZ : Z' ⟶ Z)

/-- The actual closed support restricted to an adjacent factor rectangle. -/
abbrev openSupport : Scheme.{u} := pullback (productMap f g uX uY) F.inclusion

/-- The restricted support's actual local closed immersion. -/
abbrev openSupportInclusion : F.openSupport uX uY ⟶ pullback (uX ≫ f) (uY ≫ g) :=
  pullback.fst (productMap f g uX uY) F.inclusion

/-- The actual open restriction map to the original support. -/
abbrev openSupportMap : F.openSupport uX uY ⟶ F.scheme :=
  pullback.snd (productMap f g uX uY) F.inclusion

instance : IsClosedImmersion (F.openSupportInclusion uX uY) := inferInstanceAs
  (IsClosedImmersion (pullback.fst (productMap f g uX uY) F.inclusion))

instance [IsOpenImmersion uX] [IsOpenImmersion uY] :
    IsOpenImmersion (F.openSupportMap uX uY) := inferInstanceAs
  (IsOpenImmersion (pullback.snd (productMap f g uX uY) F.inclusion))

/-- The support restriction is the literal pullback square. -/
@[reassoc] theorem openSupport_square :
    F.openSupportInclusion uX uY ≫ productMap f g uX uY =
      F.openSupportMap uX uY ≫ F.inclusion := pullback.condition

/-- The first restricted-support coordinate retains the original source projection. -/
@[reassoc] theorem openSupportInclusion_fst :
    F.openSupportInclusion uX uY ≫ pullback.fst (uX ≫ f) (uY ≫ g) ≫ uX =
      F.openSupportMap uX uY ≫ F.projection := by
  rw [← productMap_fst, ← Category.assoc, F.openSupport_square]
  rfl

/-- The second restricted-support coordinate retains the original target projection. -/
@[reassoc] theorem openSupportInclusion_snd :
    F.openSupportInclusion uX uY ≫ pullback.snd (uX ≫ f) (uY ≫ g) ≫ uY =
      F.openSupportMap uX uY ≫ F.targetProjection := by
  rw [← productMap_snd, ← Category.assoc, F.openSupport_square]
  rfl

/-- The genuine product of restricted supports over the unchanged base. -/
abbrev openSupportProduct : Scheme.{u} :=
  pullback
    (F.openSupportInclusion uX uY ≫ pullback.snd (uX ≫ f) (uY ≫ g) ≫ uY ≫ g)
    (G.openSupportInclusion uY uZ ≫ pullback.fst (uY ≫ g) (uZ ≫ h) ≫ uY ≫ g)

/-- The local support-product inclusion into the actual local ambient product. -/
def openSupportProductInclusion : F.openSupportProduct G uX uY uZ ⟶
    correspondenceIntersectionAmbient (uX ≫ f) (uY ≫ g) (uZ ≫ h) :=
  pullback.map _ _ _ _ (F.openSupportInclusion uX uY)
    (G.openSupportInclusion uY uZ) (𝟙 S) (by simp) (by simp)

/-- The actual comparison to the original support product. -/
def openSupportProductMap : F.openSupportProduct G uX uY uZ ⟶ F.supportProduct G :=
  pullback.map _ _ _ _ (F.openSupportMap uX uY) (G.openSupportMap uY uZ) (𝟙 S)
    (by simp only [Category.comp_id, F.openSupportInclusion_snd_assoc,
      targetProjection, Category.assoc])
    (by simp only [Category.comp_id, G.openSupportInclusion_fst_assoc])

instance [IsOpenImmersion uX] [IsOpenImmersion uY] [IsOpenImmersion uZ] :
    IsOpenImmersion (F.openSupportProductMap G uX uY uZ) := by
  unfold openSupportProductMap
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance : IsClosedImmersion (F.openSupportProductInclusion G uX uY uZ) := by
  unfold openSupportProductInclusion
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstanceAs (IsClosedImmersion (F.openSupportInclusion uX uY)))
    (inferInstanceAs (IsClosedImmersion (G.openSupportInclusion uY uZ))) rfl rfl

/-- The actual coefficient support square commutes with the ambient neighborhood map. -/
@[reassoc] theorem openSupportProduct_square :
    F.openSupportProductMap G uX uY uZ ≫ F.supportProductInclusion G =
      F.openSupportProductInclusion G uX uY uZ ≫ ambientMap f g h uX uY uZ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, supportProductInclusion_fst,
      openSupportProductMap, openSupportProductInclusion, ambientMap_fst, pullback.map,
      pullback.lift_fst_assoc, openSupport_square]
  · simp only [Category.assoc, supportProductInclusion_snd,
      openSupportProductMap, openSupportProductInclusion, ambientMap_snd, pullback.map,
      pullback.lift_snd_assoc, openSupport_square]

/-- Every original incidence point in a triple rectangle lifts to the genuine
restricted support product, with the exact common local ambient point. -/
theorem exists_openSupportProductPoint
    [IsOpenImmersion uX] [IsOpenImmersion uY] [IsOpenImmersion uZ]
    (w : F.incidence G)
    (q : correspondenceTripleProduct (uX ≫ f) (uY ≫ g) (uZ ≫ h))
    (hq : tripleMap f g h uX uY uZ q = F.incidenceInclusion G w) :
    ∃ t : F.openSupportProduct G uX uY uZ,
      F.openSupportProductMap G uX uY uZ t = F.incidenceToSupportProduct G w ∧
      correspondenceTripleInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) q =
        F.openSupportProductInclusion G uX uY uZ t := by
  have hrect : F.incidenceInclusion G w ∈ Set.range (tripleMap f g h uX uY uZ) := ⟨q, hq⟩
  rw [range_tripleMap] at hrect
  have hl : F.incidenceFst G w ∈ Set.range (F.openSupportMap uX uY) := by
    rw [openSupportMap, Scheme.Pullback.range_snd]
    change F.inclusion (F.incidenceFst G w) ∈ Set.range (productMap f g uX uY)
    simpa only [Set.mem_preimage, ← Scheme.Hom.comp_apply, incidenceInclusion_fst] using hrect.1
  have hr : F.incidenceSnd G w ∈ Set.range (G.openSupportMap uY uZ) := by
    rw [openSupportMap, Scheme.Pullback.range_snd]
    change G.inclusion (F.incidenceSnd G w) ∈ Set.range (productMap g h uY uZ)
    simpa only [Set.mem_preimage, ← Scheme.Hom.comp_apply, incidenceInclusion_snd] using hrect.2
  have ht : F.incidenceToSupportProduct G w ∈
      Set.range (F.openSupportProductMap G uX uY uZ) := by
    unfold openSupportProductMap
    rw [Scheme.Pullback.range_map]
    simpa only [Set.mem_inter_iff, Set.mem_preimage, ← Scheme.Hom.comp_apply,
      incidenceToSupportProduct_fst, incidenceToSupportProduct_snd] using And.intro hl hr
  obtain ⟨t, ht⟩ := ht
  refine ⟨t, ht, ?_⟩
  apply (ambientMap f g h uX uY uZ).isOpenEmbedding.injective
  calc
    ambientMap f g h uX uY uZ
        (correspondenceTripleInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) q) =
      correspondenceTripleInclusion f g h (tripleMap f g h uX uY uZ q) :=
        (congrArg (fun m ↦ m q) (tripleMap_inclusion f g h uX uY uZ)).symm
    _ = correspondenceTripleInclusion f g h (F.incidenceInclusion G w) := by rw [hq]
    _ = F.supportProductInclusion G (F.incidenceToSupportProduct G w) :=
      congrArg (fun m ↦ m w) (F.incidence_ambient_comm G)
    _ = F.supportProductInclusion G (F.openSupportProductMap G uX uY uZ t) := by rw [ht]
    _ = ambientMap f g h uX uY uZ (F.openSupportProductInclusion G uX uY uZ t) :=
      congrArg (fun m ↦ m t) (F.openSupportProduct_square G uX uY uZ)

open _root_.AlgebraicGeometry.Scheme.Intersection

/-- Actual local Tor with the genuinely restricted support product as coefficient. -/
def openIncidenceStalkTor
    (q : correspondenceTripleProduct (uX ≫ f) (uY ≫ g) (uZ ≫ h))
    (t : F.openSupportProduct G uX uY uZ)
    (hp : correspondenceTripleInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) q =
      F.openSupportProductInclusion G uX uY uZ t) (n : ℕ) :
    ModuleCat (ambientStalk (correspondenceTripleInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h)) q) :=
  ((Tor (ModuleCat
    (ambientStalk (correspondenceTripleInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h)) q)) n).obj
    (coefficientStalkModule (correspondenceTripleInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h)) q
      (F.openSupportProductInclusion G uX uY uZ) t hp)).obj
    (sourceStalkModule (correspondenceTripleInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h)) q)

variable [IsOpenImmersion uX] [IsOpenImmersion uY] [IsOpenImmersion uZ]
  (w : F.incidence G)
  (q : correspondenceTripleProduct (uX ≫ f) (uY ≫ g) (uZ ≫ h))
  (t : F.openSupportProduct G uX uY uZ)
  (hq : tripleMap f g h uX uY uZ q = F.incidenceInclusion G w)
  (ht : F.openSupportProductMap G uX uY uZ t = F.incidenceToSupportProduct G w)
  (hp : correspondenceTripleInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) q =
    F.openSupportProductInclusion G uX uY uZ t)

/-- The actual ambient stalk equivalence of this product neighborhood. -/
def openIncidenceAmbientStalkEquiv : F.incidenceAmbientStalk G w ≃+*
    ambientStalk (correspondenceTripleInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h)) q :=
  neighborhoodAmbientStalkEquiv (correspondenceTripleInclusion f g h)
    (F.incidenceInclusion G w)
    (correspondenceTripleInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h)) q
    (tripleMap f g h uX uY uZ) (ambientMap f g h uX uY uZ)
    (tripleMap_inclusion f g h uX uY uZ) hq.symm

/-- Actual incidence Tor is carried to the genuinely restricted coefficient support
with the literal product-neighborhood ambient scalar map. -/
def openIncidenceStalkTorIso (n : ℕ) :
    F.incidenceTor G w n ≅
      (ModuleCat.restrictScalars
        (F.openIncidenceAmbientStalkEquiv G uX uY uZ w q hq).toRingHom).obj
        (F.openIncidenceStalkTor G uX uY uZ q t hp n) :=
  neighborhoodStalkTorIso (correspondenceTripleInclusion f g h)
    (F.incidenceInclusion G w) (F.supportProductInclusion G)
    (F.incidenceToSupportProduct G w)
    (point_eq _ _ _ _ (F.incidence_ambient_isPullback G) w)
    (correspondenceTripleInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h)) q
    (F.openSupportProductInclusion G uX uY uZ) t hp
    (tripleMap f g h uX uY uZ) (F.openSupportProductMap G uX uY uZ)
    (ambientMap f g h uX uY uZ) (tripleMap_inclusion f g h uX uY uZ)
    (F.openSupportProduct_square G uX uY uZ) hq.symm ht.symm n

include hq ht in
/-- Actual local lengths agree in every degree, without any finite-length assumption. -/
theorem openIncidenceStalkTor_length (n : ℕ) :
    Module.length (F.incidenceAmbientStalk G w) (F.incidenceTor G w n) =
      Module.length
        (ambientStalk (correspondenceTripleInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h)) q)
        (F.openIncidenceStalkTor G uX uY uZ q t hp n) :=
  (F.openIncidenceStalkTorIso G uX uY uZ w q t hq ht hp n).toLinearEquiv.length_eq.trans
    (_root_.ModuleCat.length_restrictScalars_of_surjective
      (F.openIncidenceAmbientStalkEquiv G uX uY uZ w q hq).toRingHom
      (F.openIncidenceAmbientStalkEquiv G uX uY uZ w q hq).surjective _)

end Motivic.FiniteCorrespondenceGenerator
