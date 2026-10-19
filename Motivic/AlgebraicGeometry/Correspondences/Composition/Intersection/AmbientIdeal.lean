/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.Kernel
public import Motivic.Aglib.AlgebraicGeometry.Products.Diagonal.IntersectionIdeal

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Intersection.Ambient

/-!
# The scheme-theoretic ambient intersection of correspondence supports

The incidence scheme is the actual pullback of the support product and the
middle diagonal inside the four-factor ambient product. When the middle
structure map is separated, the actual kernel ideal of the incidence closed
immersion is exactly the sum of those two ideals. This identifies the full
scheme structure and preserves nilpotents, without defining an intersection
cycle or asserting a Tor-vanishing property.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic

namespace FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme.Hom _root_.AlgebraicGeometry.Scheme.Products

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)

/-- The actual incidence scheme is the Cartesian intersection in the ambient product. -/
theorem incidence_ambient_isPullback :
    IsPullback (A.incidenceInclusion B) (A.incidenceToSupportProduct B)
      (correspondenceTripleInclusion f g h) (A.supportProductInclusion B) where
  w := A.incidence_ambient_comm B
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun s ↦ by
    have ha := congrArg
      (fun k => k ≫ pullback.fst (pullback.snd f g ≫ g) (pullback.fst g h ≫ g))
      s.condition
    have hb := congrArg
      (fun k => k ≫ pullback.snd (pullback.snd f g ≫ g) (pullback.fst g h ≫ g))
      s.condition
    simp only [Category.assoc, correspondenceTripleInclusion_fst,
      supportProductInclusion_fst] at ha
    simp only [Category.assoc, correspondenceTripleInclusion_snd,
      supportProductInclusion_snd] at hb
    have hab :
        (s.snd ≫ pullback.fst (A.targetProjection ≫ g) (B.projection ≫ g)) ≫
          A.targetProjection =
        (s.snd ≫ pullback.snd (A.targetProjection ≫ g) (B.projection ≫ g)) ≫
          B.projection := by
      change (s.snd ≫ pullback.fst _ _) ≫ (A.inclusion ≫ pullback.snd f g) =
        (s.snd ≫ pullback.snd _ _) ≫ (B.inclusion ≫ pullback.fst g h)
      simp only [Category.assoc]
      calc
        _ = s.fst ≫ pullback.fst (pullback.snd f g) (pullback.fst g h) ≫
            pullback.snd f g := by
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ pullback.snd f g) ha.symm
        _ = s.fst ≫ pullback.snd (pullback.snd f g) (pullback.fst g h) ≫
            pullback.fst g h := by rw [pullback.condition]
        _ = _ := by
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ pullback.fst g h) hb
    let w : s.pt ⟶ A.incidence B := pullback.lift
      (s.snd ≫ pullback.fst _ _) (s.snd ≫ pullback.snd _ _) hab
    have hw₁ : w ≫ A.incidenceInclusion B = s.fst := by
      apply pullback.hom_ext
      · simpa only [w, Category.assoc, incidenceInclusion_fst, incidenceFst,
          pullback.lift_fst_assoc] using ha.symm
      · simpa only [w, Category.assoc, incidenceInclusion_snd, incidenceSnd,
          pullback.lift_snd_assoc] using hb.symm
    have hw₂ : w ≫ A.incidenceToSupportProduct B = s.snd := by
      apply pullback.hom_ext
      · rw [Category.assoc, incidenceToSupportProduct_fst]
        exact pullback.lift_fst _ _ _
      · rw [Category.assoc, incidenceToSupportProduct_snd]
        exact pullback.lift_snd _ _ _
    refine ⟨w, hw₁, hw₂, ?_⟩
    intro m hm _
    exact (cancel_mono (A.incidenceInclusion B)).mp (hm.trans hw₁.symm))⟩

/-- The actual map from incidence to the four-factor ambient product. -/
noncomputable abbrev incidenceAmbientInclusion :
    A.incidence B ⟶ correspondenceIntersectionAmbient f g h :=
  A.incidenceInclusion B ≫ correspondenceTripleInclusion f g h

instance [IsSeparated g] : IsClosedImmersion (A.incidenceAmbientInclusion B) :=
  inferInstanceAs (IsClosedImmersion
    (A.incidenceInclusion B ≫ correspondenceTripleInclusion f g h))

/-- The actual incidence ideal in the ambient product is the sum of the diagonal
pullback ideal and the support-product ideal. -/
theorem ker_incidenceAmbientInclusion [IsSeparated g] :
    (A.incidenceAmbientInclusion B).ker =
      (correspondenceTripleInclusion f g h).ker ⊔ (A.supportProductInclusion B).ker :=
  ker_comp_eq_sup_of_isPullback _ _ _ _ (A.incidence_ambient_isPullback B)

/-- Inside the support product, incidence is cut out by the actual ambient
triple-product ideal, without any coefficient regularity assumption. -/
theorem ker_incidenceToSupportProduct [IsSeparated g] :
    (A.incidenceToSupportProduct B).ker =
      (correspondenceTripleInclusion f g h).ker.comap (A.supportProductInclusion B) :=
  ker_eq_comap_of_isPullback _ _ _ _ (A.incidence_ambient_isPullback B).flip

/-- The ambient incidence ideal is the pulled-back middle-diagonal ideal plus
the ideal of the literal product of support schemes. -/
theorem ker_incidenceAmbientInclusion_eq_diagonal_sup [IsSeparated g] :
    (A.incidenceAmbientInclusion B).ker =
      (pullback.diagonal g).ker.comap (correspondenceMiddlePair f g h) ⊔
        (A.supportProductInclusion B).ker := by
  rw [A.ker_incidenceAmbientInclusion B, ker_correspondenceTripleInclusion]

/-- The full incidence scheme is the subscheme cut out by the sum of the two
actual ambient ideals, including its nilpotents. -/
noncomputable def incidenceAmbientIntersectionIso [IsSeparated g] :
    A.incidence B ≅
      ((correspondenceTripleInclusion f g h).ker ⊔ (A.supportProductInclusion B).ker).subscheme :=
  asIso (A.incidenceAmbientInclusion B).toImage ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.subscheme (A.ker_incidenceAmbientInclusion B))

end FiniteCorrespondenceGenerator

end Motivic
