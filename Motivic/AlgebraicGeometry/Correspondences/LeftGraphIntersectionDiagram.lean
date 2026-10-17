/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.GraphIntersectionDiagram

/-!
# The actual transposed graph diagram for left incidence

When the first support has isomorphic target projection, swapping the support
factors identifies its product with the graph ambient product of the second
source projection. The actual middle pair is the graph pair followed by the
symmetry of the middle self-product. These are actual scheme morphisms and
isomorphisms; no Tor symmetry or coefficient regularity is assumed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic

variable {S U Y : Scheme.{u}} (φ : U ⟶ Y) (g : Y ⟶ S)

/-- The transposed actual graph pair, retaining the original middle-coordinate order. -/
noncomputable def leftGraphMiddlePair : pullback (φ ≫ g) g ⟶ pullback g g :=
  graphMiddlePair φ g ≫ (pullbackSymmetry g g).hom

@[reassoc (attr := simp)]
theorem leftGraphMiddlePair_fst :
    leftGraphMiddlePair φ g ≫ pullback.fst g g = pullback.snd (φ ≫ g) g := by
  simp [leftGraphMiddlePair]

@[reassoc (attr := simp)]
theorem leftGraphMiddlePair_snd :
    leftGraphMiddlePair φ g ≫ pullback.snd g g = pullback.fst (φ ≫ g) g ≫ φ := by
  simp [leftGraphMiddlePair]

/-- The actual diagonal is fixed by the actual pullback symmetry. -/
@[reassoc (attr := simp)]
theorem diagonal_symmetry :
    pullback.diagonal g ≫ (pullbackSymmetry g g).hom = pullback.diagonal g := by
  apply pullback.hom_ext <;> simp

/-- A graph maps to the same diagonal after transposing the two middle coordinates. -/
@[reassoc]
theorem correspondenceGraph_leftMiddlePair :
    correspondenceGraph φ g ≫ leftGraphMiddlePair φ g = φ ≫ pullback.diagonal g := by
  apply pullback.hom_ext <;> simp

/-- The actual integral diagonal support also projects isomorphically by its target. -/
instance identityGenerator_targetProjection_isIso
    {X : Scheme.{u}} {f : X ⟶ S} [IsIntegral X] [IsSeparated f] :
    IsIso (identityGenerator f).targetProjection := by
  rw [identityGenerator_targetProjection]
  infer_instance

namespace FiniteCorrespondenceGenerator

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)

/-- Swap support factors and use the first target projection as the graph's second factor. -/
noncomputable def supportProductToLeftGraphProduct :
    A.supportProduct B ⟶ pullback (B.projection ≫ g) g :=
  (pullbackSymmetry (A.targetProjection ≫ g) (B.projection ≫ g)).hom ≫
    pullback.map (B.projection ≫ g) (A.targetProjection ≫ g)
      (B.projection ≫ g) g (𝟙 B.scheme) A.targetProjection (𝟙 S) (by simp) (by simp)

instance [IsIso A.targetProjection] : IsIso (A.supportProductToLeftGraphProduct B) := by
  unfold supportProductToLeftGraphProduct
  infer_instance

@[reassoc (attr := simp)]
theorem supportProductToLeftGraphProduct_fst :
    A.supportProductToLeftGraphProduct B ≫ pullback.fst (B.projection ≫ g) g =
      pullback.snd (A.targetProjection ≫ g) (B.projection ≫ g) := by
  simp [supportProductToLeftGraphProduct, pullback.map, Category.assoc, pullback.lift_fst]

@[reassoc (attr := simp)]
theorem supportProductToLeftGraphProduct_snd :
    A.supportProductToLeftGraphProduct B ≫ pullback.snd (B.projection ≫ g) g =
      pullback.fst (A.targetProjection ≫ g) (B.projection ≫ g) ≫ A.targetProjection := by
  simp [supportProductToLeftGraphProduct, pullback.map, Category.assoc, pullback.lift_snd]

/-- The actual support product is the actual transposed graph ambient product. -/
noncomputable def supportProductLeftGraphIso [IsIso A.targetProjection] :
    A.supportProduct B ≅ pullback (B.projection ≫ g) g :=
  asIso (A.supportProductToLeftGraphProduct B)

/-- The actual incidence embedding becomes the graph of the second source projection. -/
@[reassoc]
theorem incidenceToSupportProduct_leftGraph :
    A.incidenceToSupportProduct B ≫ A.supportProductToLeftGraphProduct B =
      A.incidenceSnd B ≫ correspondenceGraph B.projection g := by
  apply pullback.hom_ext
  · simp
  · simp only [Category.assoc, supportProductToLeftGraphProduct_snd,
      incidenceToSupportProduct_fst_assoc, correspondenceGraph_snd]
    exact A.incidence_condition B

/-- The four-factor middle pair agrees with the transposed graph pair on the actual support. -/
@[reassoc]
theorem supportProductInclusion_leftMiddlePair :
    A.supportProductInclusion B ≫ correspondenceMiddlePair f g h =
      A.supportProductToLeftGraphProduct B ≫ leftGraphMiddlePair B.projection g := by
  apply pullback.hom_ext
  · simp only [Category.assoc, correspondenceMiddlePair_fst,
      supportProductInclusion_fst_assoc, leftGraphMiddlePair_fst,
      supportProductToLeftGraphProduct_snd]
  · simp only [Category.assoc, correspondenceMiddlePair_snd,
      supportProductInclusion_snd_assoc, leftGraphMiddlePair_snd,
      supportProductToLeftGraphProduct_fst_assoc]
    rfl

end FiniteCorrespondenceGenerator

end Motivic
