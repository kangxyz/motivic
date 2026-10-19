/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Support.Basic

/-!
# The actual common triple incidence scheme

Three genuine correspondence supports have two parenthesized incidence schemes.
Their explicit pullback isomorphism respects all three support projections and
the common source-target map. The left projection and the final output map are
finite. No finiteness of the projection to the right pair incidence is asserted.
No scheme is replaced by its reduction or by a component cycle.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g)
  (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- The left-parenthesized incidence of three actual support schemes. -/
abbrev tripleIncidence : Scheme.{u} := pullback (F.incidenceTarget G) H.projection

/-- The right-parenthesized incidence of the same three support schemes. -/
abbrev rightTripleIncidence : Scheme.{u} := pullback F.targetProjection (G.incidenceSource H)

/-- The projection to the first pair incidence, which is a finite base change. -/
abbrev tripleIncidenceFst : F.tripleIncidence G H ⟶ F.incidence G :=
  pullback.fst (F.incidenceTarget G) H.projection

/-- The projection to the third support. -/
abbrev tripleIncidenceSnd : F.tripleIncidence G H ⟶ H.scheme :=
  pullback.snd (F.incidenceTarget G) H.projection

instance : IsFinite (F.tripleIncidenceFst G H) :=
  inferInstanceAs (IsFinite (pullback.fst (F.incidenceTarget G) H.projection))

/-- The actual map from the common incidence to its original source. -/
abbrev tripleIncidenceSource : F.tripleIncidence G H ⟶ X :=
  F.tripleIncidenceFst G H ≫ F.incidenceSource G

/-- The actual map from the common incidence to its final target. -/
abbrev tripleIncidenceTarget : F.tripleIncidence G H ⟶ W :=
  F.tripleIncidenceSnd G H ≫ H.targetProjection

instance : IsFinite (F.tripleIncidenceSource G H) :=
  inferInstanceAs (IsFinite (F.tripleIncidenceFst G H ≫ F.incidenceSource G))

/-- Both outer projections lie over the same base point. -/
@[reassoc] theorem tripleIncidence_base :
    F.tripleIncidenceSource G H ≫ f = F.tripleIncidenceTarget G H ≫ i := by
  calc
    _ = F.tripleIncidenceFst G H ≫ (F.incidenceSource G ≫ f) := Category.assoc _ _ _
    _ = F.tripleIncidenceFst G H ≫ (F.incidenceTarget G ≫ h) :=
      congrArg (F.tripleIncidenceFst G H ≫ ·) (F.incidence_base G)
    _ = F.tripleIncidenceSnd G H ≫ (H.projection ≫ h) := by
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ h) (pullback.condition (f := F.incidenceTarget G) (g := H.projection))
    _ = F.tripleIncidenceSnd G H ≫ (H.targetProjection ≫ i) :=
      congrArg (F.tripleIncidenceSnd G H ≫ ·) H.projection_base
    _ = _ := (Category.assoc _ _ _).symm

/-- The actual projection to the second pair incidence; it is not assumed finite. -/
def tripleIncidenceToRightPair : F.tripleIncidence G H ⟶ G.incidence H :=
  pullback.lift (F.tripleIncidenceFst G H ≫ F.incidenceSnd G)
    (F.tripleIncidenceSnd G H) (by
      simpa only [incidenceTarget, Category.assoc] using
        (pullback.condition (f := F.incidenceTarget G) (g := H.projection)))

/-- The second support projection of the right pair is the original middle support map. -/
@[reassoc (attr := simp)] theorem tripleIncidenceToRightPair_fst :
    F.tripleIncidenceToRightPair G H ≫ G.incidenceFst H =
      F.tripleIncidenceFst G H ≫ F.incidenceSnd G := pullback.lift_fst _ _ _

/-- The third support projection of the right pair is the original last support map. -/
@[reassoc (attr := simp)] theorem tripleIncidenceToRightPair_snd :
    F.tripleIncidenceToRightPair G H ≫ G.incidenceSnd H =
      F.tripleIncidenceSnd G H := pullback.lift_snd _ _ _

/-- The right-parenthesized incidence maps to the first pair incidence. -/
def rightTripleIncidenceToLeftPair : F.rightTripleIncidence G H ⟶ F.incidence G :=
  pullback.lift (pullback.fst F.targetProjection (G.incidenceSource H))
    (pullback.snd F.targetProjection (G.incidenceSource H) ≫ G.incidenceFst H) (by
      simpa only [incidenceSource, Category.assoc] using
        (pullback.condition (f := F.targetProjection) (g := G.incidenceSource H)))

/-- The associator's forward map is assembled from the three actual support projections. -/
def tripleIncidenceAssocHom : F.tripleIncidence G H ⟶ F.rightTripleIncidence G H :=
  pullback.lift (F.tripleIncidenceFst G H ≫ F.incidenceFst G)
    (F.tripleIncidenceToRightPair G H) (by
      simp only [incidenceSource, tripleIncidenceToRightPair_fst_assoc, Category.assoc]
      exact congrArg (F.tripleIncidenceFst G H ≫ ·) (F.incidence_condition G))

/-- The inverse associator is assembled from the same actual support projections. -/
def tripleIncidenceAssocInv : F.rightTripleIncidence G H ⟶ F.tripleIncidence G H :=
  pullback.lift (F.rightTripleIncidenceToLeftPair G H)
    (pullback.snd F.targetProjection (G.incidenceSource H) ≫ G.incidenceSnd H) (by
      simp only [incidenceTarget, rightTripleIncidenceToLeftPair, pullback.lift_snd_assoc,
        Category.assoc]
      exact congrArg (pullback.snd F.targetProjection (G.incidenceSource H) ≫ ·)
        (G.incidence_condition H))

/-- The actual pullback associator, without reducing any incidence scheme. -/
def tripleIncidenceAssoc : F.tripleIncidence G H ≅ F.rightTripleIncidence G H where
  hom := F.tripleIncidenceAssocHom G H
  inv := F.tripleIncidenceAssocInv G H
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext <;>
        simp [tripleIncidenceAssocHom, tripleIncidenceAssocInv,
          rightTripleIncidenceToLeftPair, tripleIncidenceToRightPair, Category.assoc,
          pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc]
    · simp [tripleIncidenceAssocHom, tripleIncidenceAssocInv,
        tripleIncidenceToRightPair, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp [tripleIncidenceAssocHom, tripleIncidenceAssocInv,
        rightTripleIncidenceToLeftPair, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · apply pullback.hom_ext <;>
        simp [tripleIncidenceAssocHom, tripleIncidenceAssocInv,
          rightTripleIncidenceToLeftPair, tripleIncidenceToRightPair, Category.assoc,
          pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc]

/-- The associator preserves the first support projection. -/
@[reassoc (attr := simp)] theorem tripleIncidenceAssoc_fst :
    (F.tripleIncidenceAssoc G H).hom ≫
      pullback.fst F.targetProjection (G.incidenceSource H) =
      F.tripleIncidenceFst G H ≫ F.incidenceFst G := pullback.lift_fst _ _ _

/-- The associator preserves the actual right-pair incidence projection. -/
@[reassoc (attr := simp)] theorem tripleIncidenceAssoc_snd :
    (F.tripleIncidenceAssoc G H).hom ≫
      pullback.snd F.targetProjection (G.incidenceSource H) =
      F.tripleIncidenceToRightPair G H := pullback.lift_snd _ _ _

/-- The actual common map to the original source and final target product. -/
def tripleIncidenceMap : F.tripleIncidence G H ⟶ pullback f i :=
  pullback.lift (F.tripleIncidenceSource G H) (F.tripleIncidenceTarget G H)
    (F.tripleIncidence_base G H)

/-- The output map has the finite original-source projection. -/
@[reassoc (attr := simp)] theorem tripleIncidenceMap_fst :
    F.tripleIncidenceMap G H ≫ pullback.fst f i = F.tripleIncidenceSource G H :=
  pullback.lift_fst _ _ _

/-- The output map has the prescribed final-target projection. -/
@[reassoc (attr := simp)] theorem tripleIncidenceMap_snd :
    F.tripleIncidenceMap G H ≫ pullback.snd f i = F.tripleIncidenceTarget G H :=
  pullback.lift_snd _ _ _

instance [IsSeparated i] : IsFinite (F.tripleIncidenceMap G H) := by
  have : IsFinite (F.tripleIncidenceMap G H ≫ pullback.fst f i) := by
    simpa using (inferInstance : IsFinite (F.tripleIncidenceSource G H))
  exact IsFinite.of_comp (F.tripleIncidenceMap G H) (pullback.fst f i)

/-- The right-parenthesized output uses the inverse of the actual associator. -/
def rightTripleIncidenceMap : F.rightTripleIncidence G H ⟶ pullback f i :=
  (F.tripleIncidenceAssoc G H).inv ≫ F.tripleIncidenceMap G H

/-- Both parenthesizations have literally the same source-target map. -/
@[reassoc (attr := simp)] theorem tripleIncidenceAssoc_map :
    (F.tripleIncidenceAssoc G H).hom ≫ F.rightTripleIncidenceMap G H =
      F.tripleIncidenceMap G H := by
  simp [rightTripleIncidenceMap]

/-- The right-parenthesized output has the actual first-support source projection. -/
@[reassoc (attr := simp)] theorem rightTripleIncidenceMap_fst :
    F.rightTripleIncidenceMap G H ≫ pullback.fst f i =
      pullback.fst F.targetProjection (G.incidenceSource H) ≫ F.projection := by
  apply (cancel_epi (F.tripleIncidenceAssoc G H).hom).mp
  simp only [tripleIncidenceAssoc_map_assoc, tripleIncidenceMap_fst,
    tripleIncidenceAssoc_fst_assoc]

/-- The right-parenthesized output has the actual last-support target projection. -/
@[reassoc (attr := simp)] theorem rightTripleIncidenceMap_snd :
    F.rightTripleIncidenceMap G H ≫ pullback.snd f i =
      pullback.snd F.targetProjection (G.incidenceSource H) ≫ G.incidenceTarget H := by
  apply (cancel_epi (F.tripleIncidenceAssoc G H).hom).mp
  simp only [tripleIncidenceAssoc_map_assoc, tripleIncidenceMap_snd,
    tripleIncidenceAssoc_snd_assoc]
  change _ = F.tripleIncidenceToRightPair G H ≫ G.incidenceSnd H ≫ H.targetProjection
  rw [tripleIncidenceToRightPair_snd_assoc]

instance [IsSeparated i] : IsFinite (F.rightTripleIncidenceMap G H) :=
  inferInstanceAs (IsFinite ((F.tripleIncidenceAssoc G H).inv ≫ F.tripleIncidenceMap G H))

end Motivic.FiniteCorrespondenceGenerator
