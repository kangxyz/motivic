/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.CurveGeometry
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Flat.FreeCartesianOpen
public import Motivic.Aglib.AlgebraicGeometry.Graph.Frames.FreeProductCharts
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.RetainedParameterGraph
/-! # Original norm maps with an arbitrary parameter

The compactified second-factor square and the first-parameter square are
Cartesian. The square between the retained source and retained target is only
commuting: the retained source need not be the full inverse image. In particular,
the correction parameter needs a map to the original target, not to its cover.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalRetainedNormMaps`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Correction.OriginalCorrectionNormDiagram`, `Norm.OriginalNormBoundaryRange`,
`Norm.OriginalNormMarkedChart`, `Norm.OriginalNormParameterChart`,
`Norm.OriginalNormParameterTargetMap`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteSchemeNormBaseChange
open AlgebraicGeometry.Scheme.RelativeCurvePencil
universe u
namespace AlgebraicGeometry.Scheme.Hom

variable {S C P T : Scheme.{u}} (π : P ⟶ S) (f : C ⟶ P) (b : T ⟶ S)

/-- The finite map on the second factor for an arbitrary actual parameter. -/
def normProductMap : pullback b (f ≫ π) ⟶ pullback b π :=
  (pullbackLeftPullbackSndIso b π f).inv ≫ pullback.fst (pullback.snd b π) f

@[reassoc (attr := simp)]
theorem normProductMap_fst :
    normProductMap π f b ≫ pullback.fst b π = pullback.fst b (f ≫ π) := by
  simp [normProductMap]

@[reassoc (attr := simp)]
theorem normProductMap_snd :
    normProductMap π f b ≫ pullback.snd b π = pullback.snd b (f ≫ π) ≫ f := by
  simp [normProductMap]

instance [IsFinite f] : IsFinite (normProductMap π f b) := by
  unfold normProductMap
  infer_instance

/-- This square uses the whole compactification, not the retained source. -/
theorem normProductMap_isPullback :
    IsPullback (pullback.snd b (f ≫ π)) (normProductMap π f b)
      f (pullback.snd b π) := by
  apply IsPullback.flip
  apply IsPullback.of_iso_pullback ⟨normProductMap_snd π f b⟩
    (pullbackLeftPullbackSndIso b π f).symm
  · rfl
  · simp

/-- The cover-parameter specialization is the existing original graph product. -/
theorem normProductMap_graph (j : T ⟶ C) :
    normProductMap π f (j ≫ f ≫ π) = graphProductMap π f j := rfl

/-- Free affine charts come from the original finite map for every parameter. -/
theorem normProductMap_exists_free_affine_neighborhood [IsFinite f]
    {ι : Type u} (A : ι → CommRingCat.{u}) (w : ∀ i, Spec (A i) ⟶ P)
    [∀ i, IsOpenImmersion (w i)]
    (hcover : ∀ x : P, ∃ i, x ∈ Set.range (w i))
    (hfree : ∀ i,
      let : Algebra (A i) Γ(pullback f (w i), ⊤) :=
        (scalarMap (pullback.snd f (w i))).toAlgebra
      Module.Free (A i) Γ(pullback f (w i), ⊤))
    (x : (pullback b π : Scheme.{u})) :
    ∃ (U : (pullback b π).Opens) (hU : IsAffineOpen U), x ∈ U ∧
      (let : Algebra Γ(pullback b π, U)
          Γ(pullback (normProductMap π f b) hU.fromSpec, ⊤) :=
        (scalarMap (pullback.snd (normProductMap π f b) hU.fromSpec)).toAlgebra
       Module.Free Γ(pullback b π, U)
         Γ(pullback (normProductMap π f b) hU.fromSpec, ⊤)) :=
  exists_free_affine_neighborhood_of_isPullback f (normProductMap π f b)
    (pullback.snd b (f ≫ π)) (pullback.snd b π)
    (normProductMap_isPullback π f b) A w hcover hfree x

/-- The same original free charts refine inside the constructed good open. -/
theorem normProductMap_exists_free_affine_neighborhood_subset [IsFinite f]
    {ι : Type u} (A : ι → CommRingCat.{u}) (w : ∀ i, Spec (A i) ⟶ P)
    [∀ i, IsOpenImmersion (w i)]
    (hcover : ∀ x : P, ∃ i, x ∈ Set.range (w i))
    (hfree : ∀ i,
      let : Algebra (A i) Γ(pullback f (w i), ⊤) :=
        (scalarMap (pullback.snd f (w i))).toAlgebra
      Module.Free (A i) Γ(pullback f (w i), ⊤))
    (V : (pullback b π).Opens) (x : (pullback b π : Scheme.{u})) (hx : x ∈ V) :
    ∃ (U : (pullback b π).Opens) (hU : IsAffineOpen U), x ∈ U ∧ U ≤ V ∧
      (let : Algebra Γ(pullback b π, U)
          Γ(pullback (normProductMap π f b) hU.fromSpec, ⊤) :=
        (scalarMap (pullback.snd (normProductMap π f b) hU.fromSpec)).toAlgebra
       Module.Free Γ(pullback b π, U)
         Γ(pullback (normProductMap π f b) hU.fromSpec, ⊤)) :=
  exists_free_affine_neighborhood_subset_of_isPullback f (normProductMap π f b)
    (pullback.snd b (f ≫ π)) (pullback.snd b π)
    (normProductMap_isPullback π f b) A w hcover hfree V x hx

/-- First-parameter change keeps the retained second factor unchanged. -/
abbrev retainedParameterChangeMap {X V : Scheme.{u}} (q : X ⟶ S)
    (a : T ⟶ X) (ha : b = a ≫ q) (v : V ⟶ P) :
    retainedProduct b π v ⟶ retainedProduct q π v :=
  constantSourceMapOfEq a q (v ≫ π) b ha

/-- This is the first-parameter Cartesian square used by the original pairs. -/
theorem retainedParameterChangeMap_isPullback {X V : Scheme.{u}} (q : X ⟶ S)
    (a : T ⟶ X) (ha : b = a ≫ q) (v : V ⟶ P) :
    IsPullback (retainedParameterChangeMap π b q a ha v)
      (pullback.fst b (v ≫ π)) (pullback.fst q (v ≫ π)) a :=
  constantSourceMapOfEq_isPullback a q (v ≫ π) b ha

/-- The parameter change and the original retained inclusions commute literally. -/
theorem retainedParameterChangeMap_inclusion {X V : Scheme.{u}} (q : X ⟶ S)
    (a : T ⟶ X) (ha : b = a ≫ q) (v : V ⟶ P) :
    retainedParameterChangeMap π b q a ha v ≫ retainedProductInclusion q π v =
      retainedProductInclusion b π v ≫ constantSourceMapOfEq a q π b ha := by
  apply pullback.hom_ext <;> simp [retainedParameterChangeMap, Category.assoc]

variable {X V : Scheme.{u}} (x : X ⟶ P) (v : V ⟶ C)
  (p : V ⟶ X) (h : v ≫ f = p ≫ x)

/-- The actual target parameter map; no lift of the parameter to C is used. -/
abbrev retainedNormParameterMap (a : T ⟶ X) (ha : b = a ≫ (x ≫ π)) :
    pullback b π ⟶ pullback (x ≫ π) π :=
  constantSourceMapOfEq a (x ≫ π) π b ha

/-- First-parameter change is genuinely Cartesian. -/
theorem retainedNormParameterMap_isPullback (a : T ⟶ X) (ha : b = a ≫ (x ≫ π)) :
    IsPullback (retainedNormParameterMap π b x a ha) (pullback.fst b π)
      (pullback.fst (x ≫ π) π) a :=
  constantSourceMapOfEq_isPullback a (x ≫ π) π b ha

instance (a : T ⟶ X) (ha : b = a ≫ (x ≫ π)) [Flat a] :
    Flat (retainedNormParameterMap π b x a ha) :=
  MorphismProperty.of_isPullback (retainedNormParameterMap_isPullback π b x a ha).flip
    inferInstance

/-- The cover-parameter instance is the original retained parameter map. -/
theorem retainedNormParameterMap_original {Y : Scheme.{u}} (j : Y ⟶ C)
    (a : Y ⟶ X) (ha : j ≫ f = a ≫ x) :
    retainedNormParameterMap π (j ≫ f ≫ π) x a
        (by simpa only [Category.assoc] using congrArg (fun l => l ≫ π) ha) =
      retainedParameterProductMap π f j x a ha := by
  apply pullback.hom_ext <;>
    simp [retainedNormParameterMap, retainedParameterProductMap,
      retainedParameterProductIso, Category.assoc]

/-- The original map on the retained second factors. -/
def retainedNormProductMap : retainedProduct b (f ≫ π) v ⟶ retainedProduct b π x :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ p) (by
    rw [Category.assoc, ← Category.assoc p x π, ← h, Category.assoc]
    exact pullback.condition)

@[reassoc (attr := simp)]
theorem retainedNormProductMap_fst :
    retainedNormProductMap π f b x v p h ≫ pullback.fst b (x ≫ π) =
      pullback.fst b (v ≫ (f ≫ π)) := by
  simp [retainedNormProductMap]

@[reassoc (attr := simp)]
theorem retainedNormProductMap_snd :
    retainedNormProductMap π f b x v p h ≫ pullback.snd b (x ≫ π) =
      pullback.snd b (v ≫ (f ≫ π)) ≫ p := by
  simp [retainedNormProductMap]

/-- Only commutation is asserted here, never a Cartesian retained square. -/
theorem retainedNormProductMap_inclusion :
    retainedProductInclusion b (f ≫ π) v ≫ normProductMap π f b =
      retainedNormProductMap π f b x v p h ≫ retainedProductInclusion b π x := by
  apply pullback.hom_ext
  · simp
  · simp only [Category.assoc, normProductMap_snd, retainedProductInclusion_snd_assoc,
      retainedProductInclusion_snd, retainedNormProductMap_snd_assoc]
    simp only [← h]

end AlgebraicGeometry.Scheme.Hom
