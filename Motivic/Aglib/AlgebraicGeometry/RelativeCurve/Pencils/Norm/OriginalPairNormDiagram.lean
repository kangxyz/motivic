/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalNormParameterChart
public import Motivic.Aglib.Data.Fin.TwoCases
/-! # The actual original two-pair norm comparison diagram

The parameter is an actual component K mapping to the original cover Y. The source pair stays
      on Y × C, while
the target pair on X × P is pulled by the original Y → X. The second finite
map is the identity of Y × P, not a norm along the parameter map. These native
maps are the arguments of the original two-pair norm/action consumer.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalPairNormDiagram`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Norm.OriginalPairNormSectionData`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.RelativeCurvePencil
universe u
namespace AlgebraicGeometry.Scheme.Hom

variable {S C P X Y K : Scheme.{u}} (π : P ⟶ S) (f : C ⟶ P)
  (jB : Y ⟶ C) (α : K ⟶ Y) (jA : X ⟶ P) (p : Y ⟶ X) (hret : jB ≫ f = p ≫ jA)

/-- The exact cover parameter before any component inclusion. -/
abbrev originalNormPairBase := jB ≫ f ≫ π

/-- The actual component changes only the first parameter. -/
abbrev originalNormPairComponentBase := α ≫ originalNormPairBase π f jB

/-- The actual composite parameter equation, retained as a public proof. -/
theorem originalNormPairComponentBase_eq (hret : jB ≫ f = p ≫ jA) :
    originalNormPairComponentBase π f jB α = (α ≫ p) ≫ (jA ≫ π) := by
  simpa only [originalNormPairComponentBase, originalNormPairBase, Category.assoc] using
    congrArg (fun l => α ≫ l ≫ π) hret

/-- The two original parameter schemes. -/
def originalNormPairParameter (Y X : Scheme.{u}) : Fin 2 → Scheme.{u} := ![Y, X]

/-- The parameter maps are the actual component inclusion and its composite with p. -/
def originalNormPairParameterMap : ∀ i, K ⟶ originalNormPairParameter Y X i :=
  Fin.twoCases α (α ≫ p)

/-- The two original compact curves retain their distinct original parameters. -/
def originalNormPairCompact : Fin 2 → Scheme.{u} :=
  ![pullback (originalNormPairBase π f jB) (f ≫ π), pullback (jA ≫ π) π]

/-- The compact curves after the single original parameter change. -/
def originalNormPairChangedCompact : Fin 2 → Scheme.{u} :=
  ![pullback (originalNormPairComponentBase π f jB α) (f ≫ π),
      pullback (originalNormPairComponentBase π f jB α) π]

/-- Both original pairs are pulled along their actual first-parameter maps. -/
def originalNormPairCompactMap :
    ∀ i, originalNormPairChangedCompact π f jB α i ⟶ originalNormPairCompact π f jB jA i :=
  Fin.twoCases (constantSourceMapOfEq α (originalNormPairBase π f jB) (f ≫ π)
      (originalNormPairComponentBase π f jB α) rfl) (retainedNormParameterMap π
        (originalNormPairComponentBase π f jB α) jA
      (α ≫ p) (originalNormPairComponentBase_eq π f jB α jA p hret))

/-- The actual finite comparison is the second-factor map and the identity. -/
def originalNormPairFiniteMap : ∀ i, originalNormPairChangedCompact π f jB α i ⟶
    pullback (originalNormPairComponentBase π f jB α) π :=
  Fin.twoCases (normProductMap π f (originalNormPairComponentBase π f jB α)) (𝟙 _)

instance [IsFinite f] (i : Fin 2) : IsFinite (originalNormPairFiniteMap π f jB α i) := by
  fin_cases i
  · change IsFinite (normProductMap π f (originalNormPairComponentBase π f jB α))
    infer_instance
  · change IsFinite (𝟙 (pullback (originalNormPairComponentBase π f jB α) π : Scheme))
    infer_instance

instance [Flat α] [Flat p] (i : Fin 2) : Flat (originalNormPairCompactMap π f jB α jA p hret i)
      := by
  fin_cases i <;> simp only [Fin.twoCases_mk_zero, Fin.twoCases_mk_one,
      originalNormPairCompactMap] <;> infer_instance

/-- The actual original retained curves, before changing the parameter. -/
def originalNormPairRetained : Fin 2 → Scheme.{u} :=
  ![retainedProduct (originalNormPairBase π f jB) (f ≫ π) jB,
    retainedProduct (jA ≫ π) π jA]

/-- The same retained second factors over the common cover parameter. -/
def originalNormPairChangedRetained : Fin 2 → Scheme.{u} :=
  ![retainedProduct (originalNormPairComponentBase π f jB α) (f ≫ π) jB,
    retainedProduct (originalNormPairComponentBase π f jB α) π jA]

/-- The original retained inclusions into the two original compactifications. -/
def originalNormPairRetainedInclusion : ∀ i, originalNormPairRetained π f jB jA i ⟶
    originalNormPairCompact π f jB jA i :=
  Fin.twoCases (retainedProductInclusion (originalNormPairBase π f jB) (f ≫ π) jB)
      (retainedProductInclusion (jA ≫ π) π jA)

/-- Retained inclusions after the same first-parameter change. -/
def originalNormPairChangedInclusion : ∀ i, originalNormPairChangedRetained π f jB α jA i ⟶
    originalNormPairChangedCompact π f jB α i :=
  Fin.twoCases (retainedProductInclusion (originalNormPairComponentBase π f jB α) (f ≫ π)
      jB) (retainedProductInclusion (originalNormPairComponentBase π f jB α) π jA)

/-- The original first-parameter map on the retained curves. -/
def originalNormPairRetainedMap :
    ∀ i, originalNormPairChangedRetained π f jB α jA i ⟶ originalNormPairRetained π f jB jA i :=
  Fin.twoCases (retainedParameterChangeMap (f ≫ π) (originalNormPairComponentBase π f jB α)
      (originalNormPairBase π f jB) α rfl jB) (retainedParameterChangeMap π
        (originalNormPairComponentBase π f jB α)
      (jA ≫ π) (α ≫ p) (originalNormPairComponentBase_eq π f jB α jA p hret) jA)

/-- The original retained finite-map squares commute; no Cartesianity is claimed. -/
def originalNormPairRetainedFiniteMap : ∀ i, originalNormPairChangedRetained π f jB α jA i ⟶
    retainedProduct (originalNormPairComponentBase π f jB α) π jA :=
  Fin.twoCases (retainedNormProductMap π f (originalNormPairComponentBase π f jB α) jA jB
      p hret) (𝟙 _)

/-- Exact compactification compatibility of the original retained parameter change. -/
theorem originalNormPairRetainedMap_inclusion (i : Fin 2) :
    originalNormPairRetainedMap π f jB α jA p hret i ≫
        originalNormPairRetainedInclusion π f jB jA i =
      originalNormPairChangedInclusion π f jB α jA i ≫
        originalNormPairCompactMap π f jB α jA p hret i := by
  fin_cases i
  · exact retainedParameterChangeMap_inclusion (f ≫ π)
      (originalNormPairComponentBase π f jB α) (originalNormPairBase π f jB) α rfl jB
  · exact retainedParameterChangeMap_inclusion π (originalNormPairComponentBase π f jB α)
      (jA ≫ π) (α ≫ p) (originalNormPairComponentBase_eq π f jB α jA p hret) jA

/-- Exact retained second-factor commutation for the finite norm comparison. -/
theorem originalNormPairRetainedFiniteMap_inclusion (i : Fin 2) :
    originalNormPairChangedInclusion π f jB α jA i ≫ originalNormPairFiniteMap π f jB α i =
      originalNormPairRetainedFiniteMap π f jB α jA p hret i ≫
        retainedProductInclusion (originalNormPairComponentBase π f jB α) π jA := by
  fin_cases i
  · exact retainedNormProductMap_inclusion π f (originalNormPairComponentBase π f jB α) jA jB p hret
  · simp [
      originalNormPairChangedInclusion, originalNormPairFiniteMap,
      originalNormPairRetainedFiniteMap]

/-- The original compact curve projections. -/
def originalNormPairProjection : ∀ i, originalNormPairCompact π f jB jA i ⟶
    originalNormPairParameter Y X i :=
  Fin.twoCases (pullback.fst (originalNormPairBase π f jB) (f ≫ π)) (pullback.fst (jA ≫ π) π)

instance [IsFinite f] [IsProper π] (i : Fin 2) :
    IsProper (originalNormPairProjection π f jB jA i) := by
  fin_cases i <;> simp only [Fin.twoCases_mk_zero, Fin.twoCases_mk_one,
      originalNormPairProjection] <;> infer_instance

instance [IsOpenImmersion jB] [IsOpenImmersion jA] (i : Fin 2) :
    IsOpenImmersion (originalNormPairRetainedInclusion π f jB jA i) := by
  fin_cases i <;> simp only [Fin.twoCases_mk_zero, Fin.twoCases_mk_one,
      originalNormPairRetainedInclusion] <;> infer_instance

instance [IsOpenImmersion jB] [IsOpenImmersion jA] (i : Fin 2) :
    IsOpenImmersion (originalNormPairChangedInclusion π f jB α jA i) := by
  fin_cases i <;> simp only [Fin.twoCases_mk_zero, Fin.twoCases_mk_one,
      originalNormPairChangedInclusion] <;> infer_instance

/-- Affineness belongs to the actual retained products, not the finite source. -/
instance [IsAffine S] [IsAffine X] [IsAffine Y] (i : Fin 2) :
    IsAffine (originalNormPairRetained π f jB jA i) := by
  fin_cases i
  · exact retainedProduct_affine (originalNormPairBase π f jB) (f ≫ π) jB
  · exact retainedProduct_affine (jA ≫ π) π jA

instance [IsAffine S] [IsAffine X] [IsAffine Y] [IsAffine K] (i : Fin 2) :
    IsAffine (originalNormPairChangedRetained π f jB α jA i) := by
  fin_cases i
  · exact retainedProduct_affine (originalNormPairComponentBase π f jB α) (f ≫ π) jB
  · exact retainedProduct_affine (originalNormPairComponentBase π f jB α) π jA

/-- Relative dimension one is inherited from the original retained curves. -/
instance [SmoothOfRelativeDimension 1 (jB ≫ (f ≫ π))]
    [SmoothOfRelativeDimension 1 (jA ≫ π)] (i : Fin 2) :
    SmoothOfRelativeDimension 1
      (originalNormPairRetainedInclusion π f jB jA i ≫
        originalNormPairProjection π f jB jA i) := by
  fin_cases i
  · exact retainedProduct_smooth (originalNormPairBase π f jB) (f ≫ π) jB
  · exact retainedProduct_smooth (jA ≫ π) π jA

/-- The changed retained products have the same relative dimension over the actual component K. -/
instance [SmoothOfRelativeDimension 1 (jB ≫ (f ≫ π))]
    [SmoothOfRelativeDimension 1 (jA ≫ π)] (i : Fin 2) :
    SmoothOfRelativeDimension 1
      (originalNormPairChangedInclusion π f jB α jA i ≫
        (originalNormPairFiniteMap π f jB α i ≫
          pullback.fst (originalNormPairComponentBase π f jB α) π)) := by
  fin_cases i
  · simpa only [Fin.twoCases_mk_zero, Fin.twoCases_mk_one,
      originalNormPairChangedInclusion, originalNormPairFiniteMap,
       normProductMap_fst] using
      (retainedProduct_smooth (originalNormPairComponentBase π f jB α) (f ≫ π) jB)
  · change SmoothOfRelativeDimension 1
      (retainedProductInclusion (originalNormPairComponentBase π f jB α) π jA ≫
        (𝟙 _ ≫ pullback.fst (originalNormPairComponentBase π f jB α) π))
    simpa only [Category.id_comp] using
      (retainedProduct_smooth (originalNormPairComponentBase π f jB α) π jA)

/-- These, and only these, are the Cartesian first-parameter squares needed by
left graph composition in the norm comparison. -/
theorem originalNormPairRetainedMap_isPullback (i : Fin 2) :
    IsPullback (originalNormPairRetainedMap π f jB α jA p hret i)
      (originalNormPairChangedInclusion π f jB α jA i ≫
        originalNormPairFiniteMap π f jB α i ≫ pullback.fst (originalNormPairComponentBase π f
          jB α) π)
      (originalNormPairRetainedInclusion π f jB jA i ≫ originalNormPairProjection π f jB jA i)
      (originalNormPairParameterMap α p i) := by
  fin_cases i
  · simpa only [Fin.twoCases_mk_zero, Fin.twoCases_mk_one, originalNormPairRetainedMap,
      originalNormPairChangedInclusion,
      originalNormPairFiniteMap, originalNormPairRetainedInclusion,
      originalNormPairProjection, originalNormPairParameterMap,
      Category.assoc, normProductMap_fst, retainedProductInclusion_fst] using
      (retainedParameterChangeMap_isPullback (f ≫ π)
        (originalNormPairComponentBase π f jB α) (originalNormPairBase π f jB) α rfl jB)
  · change IsPullback
      (retainedParameterChangeMap π (originalNormPairComponentBase π f jB α)
        (jA ≫ π) (α ≫ p) (originalNormPairComponentBase_eq π f jB α jA p hret) jA)
      (retainedProductInclusion (originalNormPairComponentBase π f jB α) π jA ≫
        (𝟙 _ ≫ pullback.fst (originalNormPairComponentBase π f jB α) π))
      (retainedProductInclusion (jA ≫ π) π jA ≫ pullback.fst (jA ≫ π) π) (α ≫ p)
    simpa only [Category.id_comp, retainedProductInclusion_fst] using
      (retainedParameterChangeMap_isPullback π (originalNormPairComponentBase π f jB α)
        (jA ≫ π) (α ≫ p) (originalNormPairComponentBase_eq π f jB α jA p hret) jA)

/-- The original graph sections in the two compactifications. -/
def originalNormPairGraph : ∀ i, originalNormPairParameter Y X i ⟶
    originalNormPairCompact π f jB jA i :=
  Fin.twoCases (compactificationGraph (f ≫ π) jB) (compactificationGraph π jA)

/-- Both original graphs factor through their unchanged retained curve. -/
def originalNormPairRetainedGraph : ∀ i, originalNormPairParameter Y X i ⟶
    originalNormPairRetained π f jB jA i :=
  Fin.twoCases (pullback.lift (𝟙 Y) (𝟙 Y) (by simp [originalNormPairBase])) (pullback.lift
      (𝟙 X) (𝟙 X) (by simp))

/-- The graph pole is the literal original graph, not a cycle-level surrogate. -/
theorem originalNormPairRetainedGraph_inclusion (i : Fin 2) :
    originalNormPairRetainedGraph π f jB jA i ≫
        originalNormPairRetainedInclusion π f jB jA i =
      originalNormPairGraph π f jB jA i := by
  fin_cases i <;> apply pullback.hom_ext <;>
    simp only [originalNormPairRetainedGraph, originalNormPairRetainedInclusion,
      originalNormPairGraph, compactificationGraph, Fin.twoCases_mk_zero,
      Fin.twoCases_mk_one, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_snd_assoc,
      retainedProductInclusion_fst, retainedProductInclusion_snd]
  all_goals exact Category.id_comp _

/-- Each original graph is a section of its original parameter projection. -/
theorem originalNormPairGraph_projection (i : Fin 2) :
    originalNormPairGraph π f jB jA i ≫ originalNormPairProjection π f jB jA i =
      𝟙 (originalNormPairParameter Y X i) := by
  fin_cases i <;> simp [ originalNormPairGraph, originalNormPairProjection,
      originalNormPairParameter,
    compactificationGraph]

/-- The large target maps are the actual original map p and the unchanged target. -/
def originalNormPairTargetMap : ∀ i, originalNormPairRetained π f jB jA i ⟶ X :=
  Fin.twoCases (pullback.snd (originalNormPairBase π f jB) (jB ≫ (f ≫ π)) ≫ p)
      (pullback.snd (jA ≫ π) (jA ≫ π))

/-- The graph target maps that must cancel in E3 are p and identity. -/
def originalNormPairGraphTarget : ∀ i, originalNormPairParameter Y X i ⟶ X :=
  Fin.twoCases p (𝟙 X)

/-- Literal graph target identification for both original pairs. -/
theorem originalNormPairRetainedGraph_target (i : Fin 2) :
    originalNormPairRetainedGraph π f jB jA i ≫ originalNormPairTargetMap π f jB jA p i =
      originalNormPairGraphTarget p i := by
  fin_cases i
  · change (pullback.lift (𝟙 Y) (𝟙 Y) _ ≫ pullback.snd _ _) ≫ p = p
    rw [pullback.lift_snd]
    exact Category.id_comp _
  · change pullback.lift (𝟙 X) (𝟙 X) _ ≫ pullback.snd _ _ = 𝟙 X
    exact pullback.lift_snd _ _ _

/-- Graph cancellation comes from equality of actual maps, not cancellation of
presheaf restriction or étale actions. -/
theorem originalNormPair_graphs :
    originalNormPairParameterMap α p 0 ≫ originalNormPairGraphTarget p 0 =
      originalNormPairParameterMap α p 1 ≫ originalNormPairGraphTarget p 1 := by
  change α ≫ p = (α ≫ p) ≫ 𝟙 X
  exact (Category.comp_id _).symm

/-- The original parameter and finite maps preserve the SAME large target map. -/
theorem originalNormPairRetainedMap_target (i : Fin 2) :
    originalNormPairRetainedMap π f jB α jA p hret i ≫ originalNormPairTargetMap π f jB jA p i =
      originalNormPairRetainedFiniteMap π f jB α jA p hret i ≫
        pullback.snd (originalNormPairComponentBase π f jB α) (jA ≫ π) := by
  fin_cases i
  · simp [
      originalNormPairRetainedMap, originalNormPairTargetMap,
      originalNormPairRetainedFiniteMap, retainedParameterChangeMap]
  · simp [
      originalNormPairRetainedMap, originalNormPairTargetMap,
      originalNormPairRetainedFiniteMap, retainedParameterChangeMap]

variable {DB DA : Scheme.{u}} (dB : DB ⟶ C) (dA : DA ⟶ P)

/-- The original two whole infinity schemes, with all their nilpotents. -/
def originalNormPairInfinity : Fin 2 → Scheme.{u} :=
  ![pullback (pullback.snd (originalNormPairBase π f jB) (f ≫ π)) dB,
    pullback (pullback.snd (jA ≫ π) π) dA]

/-- The same infinity schemes after the actual first-parameter change. -/
def originalNormPairChangedInfinity : Fin 2 → Scheme.{u} :=
  ![pullback (pullback.snd (originalNormPairComponentBase π f jB α) (f ≫ π)) dB,
    pullback (pullback.snd (originalNormPairComponentBase π f jB α) π) dA]

/-- The original unmarked-boundary inclusions used by the large-target comparison. -/
def originalNormPairInfinityInclusion : ∀ i, originalNormPairInfinity π f jB jA dB dA i ⟶
    originalNormPairCompact π f jB jA i :=
  Fin.twoCases (pullback.fst _ dB) (pullback.fst _ dA)

/-- The unmarked boundary after the same first-parameter change. -/
def originalNormPairChangedInfinityInclusion :
    ∀ i, originalNormPairChangedInfinity π f jB α dB dA i ⟶
      originalNormPairChangedCompact π f jB α i :=
  Fin.twoCases (pullback.fst _ dB) (pullback.fst _ dA)

/-- Actual parameter transport of the original infinity, not a chosen replacement. -/
def originalNormPairInfinityMap :
    ∀ i, originalNormPairChangedInfinity π f jB α dB dA i ⟶
      originalNormPairInfinity π f jB jA dB dA i :=
  Fin.twoCases (constantInfinitySourceMap α (originalNormPairBase π f jB) (f ≫ π)
      (originalNormPairComponentBase π f jB α) rfl dB) (constantInfinitySourceMap (α ≫ p) (jA ≫ π) π
      (originalNormPairComponentBase π f jB α)
      (originalNormPairComponentBase_eq π f jB α jA p hret) dA)

/-- Both source-boundary units can be transported using this literal equality. -/
theorem originalNormPairInfinityMap_inclusion (i : Fin 2) :
    originalNormPairInfinityMap π f jB α jA p hret dB dA i ≫
        originalNormPairInfinityInclusion π f jB jA dB dA i =
      originalNormPairChangedInfinityInclusion π f jB α dB dA i ≫
        originalNormPairCompactMap π f jB α jA p hret i := by
  fin_cases i
  · exact constantInfinitySourceMap_fst α (originalNormPairBase π f jB) (f ≫ π)
      (originalNormPairComponentBase π f jB α) rfl dB
  · exact constantInfinitySourceMap_fst (α ≫ p) (jA ≫ π) π
      (originalNormPairComponentBase π f jB α)
      (originalNormPairComponentBase_eq π f jB α jA p hret) dA

section SmallRetained

variable {A B : Scheme.{u}} (a : A ⟶ X) (vB : B ⟶ Y) (bA : B ⟶ A)
  (hsmall : vB ≫ p = bA ≫ a)

/-- The smaller original retained products use the actual B and A, never a
fabricated map from A to the source cover. -/
def originalNormPairSmallRetained : Fin 2 → Scheme.{u} :=
  ![retainedProduct (originalNormPairBase π f jB) (jB ≫ (f ≫ π)) vB,
    retainedProduct (jA ≫ π) (jA ≫ π) a]

/-- The genuine restrictions from smaller to larger original retained curves. -/
def originalNormPairSmallMap : ∀ i, originalNormPairSmallRetained π f jB jA a vB i ⟶
    originalNormPairRetained π f jB jA i :=
  Fin.twoCases (retainedProductInclusion (originalNormPairBase π f jB) (jB ≫ (f ≫ π)) vB)
      (retainedProductInclusion (jA ≫ π) (jA ≫ π) a)

/-- The small original compactification inclusions are literal composites. -/
def originalNormPairSmallInclusion : ∀ i,
    originalNormPairSmallRetained π f jB jA a vB i ⟶ originalNormPairCompact π f jB jA i :=
  fun i => originalNormPairSmallMap π f jB jA a vB i ≫
    originalNormPairRetainedInclusion π f jB jA i

/-- The small target maps are the original B→A and the second projection. -/
def originalNormPairSmallTargetMap : ∀ i,
    originalNormPairSmallRetained π f jB jA a vB i ⟶ A :=
  Fin.twoCases (pullback.snd (originalNormPairBase π f jB) (vB ≫ (jB ≫ (f ≫ π))) ≫ bA)
      (pullback.snd (jA ≫ π) (a ≫ (jA ≫ π)))

include hsmall in
/-- This is the original small-to-large target commutation required by E3. -/
theorem originalNormPairSmallTargetMap_comp (i : Fin 2) :
    originalNormPairSmallTargetMap π f jB jA a vB bA i ≫ a =
      originalNormPairSmallMap π f jB jA a vB i ≫
        originalNormPairTargetMap π f jB jA p i := by
  fin_cases i
  · simpa only [Fin.twoCases_mk_zero, Fin.twoCases_mk_one, originalNormPairSmallTargetMap,
      originalNormPairSmallMap,
      originalNormPairTargetMap,  Category.assoc,
      retainedProductInclusion_snd_assoc] using
      congrArg (fun m => pullback.snd (originalNormPairBase π f jB)
        (vB ≫ (jB ≫ (f ≫ π))) ≫ m) hsmall.symm
  · simp [
      originalNormPairSmallTargetMap, originalNormPairSmallMap,
      originalNormPairTargetMap]

instance [IsOpenImmersion a] [IsOpenImmersion vB] (i : Fin 2) :
    IsOpenImmersion (originalNormPairSmallMap π f jB jA a vB i) := by
  fin_cases i <;> simp only [Fin.twoCases_mk_zero, Fin.twoCases_mk_one,
      originalNormPairSmallMap] <;> infer_instance

instance [IsOpenImmersion a] [IsOpenImmersion vB]
    [IsOpenImmersion jB] [IsOpenImmersion jA] (i : Fin 2) :
    IsOpenImmersion (originalNormPairSmallInclusion π f jB jA a vB i) := by
  dsimp [
      originalNormPairSmallInclusion]
  infer_instance

/-- The smaller original products are affine under the actual affine overlap hypotheses. -/
instance [IsAffine S] [IsAffine X] [IsAffine Y] [IsAffine A] [IsAffine B]
    (i : Fin 2) : IsAffine (originalNormPairSmallRetained π f jB jA a vB i) := by
  fin_cases i
  · exact retainedProduct_affine (originalNormPairBase π f jB) (jB ≫ (f ≫ π)) vB
  · exact retainedProduct_affine (jA ≫ π) (jA ≫ π) a

/-- Smoothness of the original smaller retained products is base change of
smoothness of B and A over the unchanged common base. -/
instance [SmoothOfRelativeDimension 1 (vB ≫ (jB ≫ (f ≫ π)))]
    [SmoothOfRelativeDimension 1 (a ≫ (jA ≫ π))] (i : Fin 2) :
    SmoothOfRelativeDimension 1
      (originalNormPairSmallInclusion π f jB jA a vB i ≫
        originalNormPairProjection π f jB jA i) := by
  fin_cases i
  · simpa only [Fin.twoCases_mk_zero, Fin.twoCases_mk_one, originalNormPairSmallInclusion,
      originalNormPairSmallMap,
      originalNormPairRetainedInclusion, originalNormPairProjection,
       Category.assoc, retainedProductInclusion_fst] using
      (retainedProduct_smooth (originalNormPairBase π f jB) (jB ≫ (f ≫ π)) vB)
  · simpa only [Fin.twoCases_mk_zero, Fin.twoCases_mk_one, originalNormPairSmallInclusion,
      originalNormPairSmallMap,
      originalNormPairRetainedInclusion, originalNormPairProjection,
       Category.assoc, retainedProductInclusion_fst] using
      (retainedProduct_smooth (jA ≫ π) (jA ≫ π) a)

end SmallRetained

end AlgebraicGeometry.Scheme.Hom
