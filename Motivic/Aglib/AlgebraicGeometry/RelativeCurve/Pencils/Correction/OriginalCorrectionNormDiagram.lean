/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalRetainedNormMaps
public import Motivic.Aglib.Data.Fin.TwoCases
/-! # The actual punctured-parameter correction norm diagram

The target pair changes its first parameter by the original puncture A → X.
The correction pair already lives over A and is not changed. The base is the
literal original a ≫ q, using the given equality jA ≫ π = q only in the target
parameter map. The finite maps
are the identity and the actual second-factor finite map, respectively.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.OriginalCorrectionNormDiagram`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Correction.OriginalCorrectionActionGeometry`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.RelativeCurvePencil
universe u
namespace AlgebraicGeometry.Scheme.Hom

variable {S C P X Y A : Scheme.{u}} (q : X ⟶ S) (π : P ⟶ S) (f : C ⟶ P)
  (jB : Y ⟶ C) (jA : X ⟶ P) (p : Y ⟶ X) (hret : jB ≫ f = p ≫ jA)
  (hA : jA ≫ π = q) (a : A ⟶ X)

/-- The original punctured parameter structure map. -/
abbrev originalCorrectionPairBase := a ≫ q

/-- The target keeps parameter X, whereas the correction already has parameter A. -/
def originalCorrectionPairParameter (X A : Scheme.{u}) : Fin 2 → Scheme.{u} := ![X, A]

/-- There is no map from A to the original étale cover in this diagram. -/
def originalCorrectionPairParameterMap : ∀ i, A ⟶ originalCorrectionPairParameter X A i :=
  Fin.twoCases a (𝟙 A)

/-- The two original compact products carrying the fixed sections. -/
def originalCorrectionPairCompact : Fin 2 → Scheme.{u} :=
  ![pullback (jA ≫ π) π, pullback (originalCorrectionPairBase q a) (f ≫ π)]

/-- The compact products after the sole target first-parameter change. -/
def originalCorrectionPairChangedCompact : Fin 2 → Scheme.{u} :=
  ![pullback (originalCorrectionPairBase q a) π,
    pullback (originalCorrectionPairBase q a) (f ≫ π)]

/-- Compactification maps are the actual first-parameter map and identity. -/
def originalCorrectionPairCompactMap : ∀ i,
    originalCorrectionPairChangedCompact q π f a i ⟶
      originalCorrectionPairCompact q π f jA a i :=
  Fin.twoCases (retainedNormParameterMap π (originalCorrectionPairBase q a) jA a
    (congrArg (fun k => a ≫ k) hA.symm)) (𝟙 _)

/-- The finite norm comparison maps are identity and the actual product map. -/
def originalCorrectionPairFiniteMap : ∀ i,
    originalCorrectionPairChangedCompact q π f a i ⟶
      pullback (originalCorrectionPairBase q a) π :=
  Fin.twoCases (𝟙 _) (normProductMap π f (originalCorrectionPairBase q a))

instance [IsFinite f] (i : Fin 2) : IsFinite (originalCorrectionPairFiniteMap q π f a i) := by
  fin_cases i
  · change IsFinite (𝟙 (pullback (a ≫ q) π : Scheme.{u}))
    infer_instance
  · exact inferInstanceAs (IsFinite (normProductMap π f (a ≫ q)))

instance [Flat a] (i : Fin 2) : Flat (originalCorrectionPairCompactMap q π f jA hA a i) := by
  fin_cases i
  · exact inferInstanceAs (Flat (retainedNormParameterMap π (a ≫ q) jA a
      (congrArg (fun k => a ≫ k) hA.symm)))
  · change Flat (𝟙 (pullback (a ≫ q) (f ≫ π) : Scheme.{u}))
    infer_instance

/-- The original retained products are unchanged in their second factors. -/
def originalCorrectionPairRetained : Fin 2 → Scheme.{u} :=
  ![retainedProduct (jA ≫ π) π jA,
    retainedProduct (originalCorrectionPairBase q a) (f ≫ π) jB]

/-- The same retained second factors over the actual punctured parameter. -/
def originalCorrectionPairChangedRetained : Fin 2 → Scheme.{u} :=
  ![retainedProduct (originalCorrectionPairBase q a) π jA,
    retainedProduct (originalCorrectionPairBase q a) (f ≫ π) jB]

/-- The two literal original retained inclusions. -/
def originalCorrectionPairRetainedInclusion : ∀ i,
    originalCorrectionPairRetained q π f jB jA a i ⟶ originalCorrectionPairCompact q π f jA a i :=
  Fin.twoCases (retainedProductInclusion (jA ≫ π) π jA)
    (retainedProductInclusion (originalCorrectionPairBase q a) (f ≫ π) jB)

/-- The retained inclusions after the sole target parameter change. -/
def originalCorrectionPairChangedInclusion : ∀ i,
    originalCorrectionPairChangedRetained q π f jB jA a i ⟶
      originalCorrectionPairChangedCompact q π f a i :=
  Fin.twoCases (retainedProductInclusion (originalCorrectionPairBase q a) π jA)
    (retainedProductInclusion (originalCorrectionPairBase q a) (f ≫ π) jB)

/-- Only the original target retained curve changes its first parameter. -/
def originalCorrectionPairRetainedMap : ∀ i,
    originalCorrectionPairChangedRetained q π f jB jA a i ⟶
      originalCorrectionPairRetained q π f jB jA a i :=
  Fin.twoCases (retainedParameterChangeMap π (originalCorrectionPairBase q a)
    (jA ≫ π) a (congrArg (fun k => a ≫ k) hA.symm) jA) (𝟙 _)

/-- The retained finite comparison is identity and the actual second-factor map. -/
def originalCorrectionPairRetainedFiniteMap : ∀ i,
    originalCorrectionPairChangedRetained q π f jB jA a i ⟶
      retainedProduct (originalCorrectionPairBase q a) π jA :=
  Fin.twoCases (𝟙 _) (retainedNormProductMap π f (originalCorrectionPairBase q a) jA jB p hret)

/-- The native first-parameter change commutes with compactification. -/
theorem originalCorrectionPairRetainedMap_inclusion (i : Fin 2) :
    originalCorrectionPairRetainedMap q π f jB jA hA a i ≫
        originalCorrectionPairRetainedInclusion q π f jB jA a i =
      originalCorrectionPairChangedInclusion q π f jB jA a i ≫
        originalCorrectionPairCompactMap q π f jA hA a i := by
  fin_cases i
  · exact retainedParameterChangeMap_inclusion π (originalCorrectionPairBase q a)
      (jA ≫ π) a (congrArg (fun k => a ≫ k) hA.symm) jA
  · simp [originalCorrectionPairRetainedMap, originalCorrectionPairRetainedInclusion,
      originalCorrectionPairChangedInclusion, originalCorrectionPairCompactMap]

/-- The actual retained second-factor comparison commutes with the norm maps. -/
theorem originalCorrectionPairRetainedFiniteMap_inclusion (i : Fin 2) :
    originalCorrectionPairChangedInclusion q π f jB jA a i ≫
        originalCorrectionPairFiniteMap q π f a i =
      originalCorrectionPairRetainedFiniteMap q π f jB jA p hret a i ≫
        retainedProductInclusion (originalCorrectionPairBase q a) π jA := by
  fin_cases i
  · simp [originalCorrectionPairChangedInclusion, originalCorrectionPairFiniteMap,
      originalCorrectionPairRetainedFiniteMap]
  · exact retainedNormProductMap_inclusion π f (originalCorrectionPairBase q a)
      jA jB p hret

/-- The original compact structure maps to their own original parameters. -/
def originalCorrectionPairProjection : ∀ i,
    originalCorrectionPairCompact q π f jA a i ⟶ originalCorrectionPairParameter X A i :=
  Fin.twoCases (pullback.fst (jA ≫ π) π)
    (pullback.fst (originalCorrectionPairBase q a) (f ≫ π))

instance [IsFinite f] [IsProper π] (i : Fin 2) :
    IsProper (originalCorrectionPairProjection q π f jA a i) := by
  fin_cases i <;>
    simp only [originalCorrectionPairProjection, Fin.twoCases_mk_zero,
      Fin.twoCases_mk_one] <;>
    infer_instance

instance [IsOpenImmersion jB] [IsOpenImmersion jA] (i : Fin 2) :
    IsOpenImmersion (originalCorrectionPairRetainedInclusion q π f jB jA a i) := by
  fin_cases i <;>
    simp only [originalCorrectionPairRetainedInclusion, Fin.twoCases_mk_zero,
      Fin.twoCases_mk_one] <;>
    infer_instance

instance [IsOpenImmersion jB] [IsOpenImmersion jA] (i : Fin 2) :
    IsOpenImmersion (originalCorrectionPairChangedInclusion q π f jB jA a i) := by
  fin_cases i <;>
    simp only [originalCorrectionPairChangedInclusion, Fin.twoCases_mk_zero,
      Fin.twoCases_mk_one] <;>
    infer_instance

instance [IsAffine S] [IsAffine X] [IsAffine Y] [IsAffine A] (i : Fin 2) :
    IsAffine (originalCorrectionPairRetained q π f jB jA a i) := by
  fin_cases i
  · exact retainedProduct_affine (jA ≫ π) π jA
  · exact retainedProduct_affine (originalCorrectionPairBase q a) (f ≫ π) jB

instance [IsAffine S] [IsAffine X] [IsAffine Y] [IsAffine A] (i : Fin 2) :
    IsAffine (originalCorrectionPairChangedRetained q π f jB jA a i) := by
  fin_cases i
  · exact retainedProduct_affine (originalCorrectionPairBase q a) π jA
  · exact retainedProduct_affine (originalCorrectionPairBase q a) (f ≫ π) jB

instance [SmoothOfRelativeDimension 1 (jB ≫ (f ≫ π))]
    [SmoothOfRelativeDimension 1 (jA ≫ π)] (i : Fin 2) :
    SmoothOfRelativeDimension 1
      (originalCorrectionPairRetainedInclusion q π f jB jA a i ≫
        originalCorrectionPairProjection q π f jA a i) := by
  fin_cases i
  · exact retainedProduct_smooth (jA ≫ π) π jA
  · exact retainedProduct_smooth (originalCorrectionPairBase q a) (f ≫ π) jB

instance [SmoothOfRelativeDimension 1 (jB ≫ (f ≫ π))]
    [SmoothOfRelativeDimension 1 (jA ≫ π)] (i : Fin 2) :
    SmoothOfRelativeDimension 1
      (originalCorrectionPairChangedInclusion q π f jB jA a i ≫
        (originalCorrectionPairFiniteMap q π f a i ≫
          pullback.fst (originalCorrectionPairBase q a) π)) := by
  fin_cases i
  · change SmoothOfRelativeDimension 1
      (retainedProductInclusion (a ≫ q) π jA ≫
        (𝟙 (pullback (a ≫ q) π : Scheme.{u}) ≫ pullback.fst (a ≫ q) π))
    rw [Category.id_comp]
    exact retainedProduct_smooth (a ≫ q) π jA
  · simpa only [originalCorrectionPairChangedInclusion, originalCorrectionPairFiniteMap,
      Fin.twoCases_mk_zero, Fin.twoCases_mk_one, normProductMap_fst] using
      (retainedProduct_smooth (originalCorrectionPairBase q a) (f ≫ π) jB)

/-- These are the actual Cartesian squares for left graph composition. -/
theorem originalCorrectionPairRetainedMap_isPullback (i : Fin 2) :
    IsPullback (originalCorrectionPairRetainedMap q π f jB jA hA a i)
      (originalCorrectionPairChangedInclusion q π f jB jA a i ≫
        originalCorrectionPairFiniteMap q π f a i ≫
          pullback.fst (originalCorrectionPairBase q a) π)
      (originalCorrectionPairRetainedInclusion q π f jB jA a i ≫
        originalCorrectionPairProjection q π f jA a i)
      (originalCorrectionPairParameterMap a i) := by
  fin_cases i
  · change IsPullback
      (retainedParameterChangeMap π (a ≫ q) (jA ≫ π) a
        (congrArg (fun k => a ≫ k) hA.symm) jA)
      (retainedProductInclusion (a ≫ q) π jA ≫
        𝟙 (pullback (a ≫ q) π : Scheme.{u}) ≫ pullback.fst (a ≫ q) π)
      (retainedProductInclusion (jA ≫ π) π jA ≫ pullback.fst (jA ≫ π) π) a
    simp only [Category.id_comp, retainedProductInclusion_fst]
    exact retainedParameterChangeMap_isPullback π (a ≫ q)
      (jA ≫ π) a (congrArg (fun k => a ≫ k) hA.symm) jA
  · change IsPullback (𝟙 (retainedProduct (a ≫ q) (f ≫ π) jB))
      (retainedProductInclusion (a ≫ q) (f ≫ π) jB ≫
        normProductMap π f (a ≫ q) ≫ pullback.fst (a ≫ q) π)
      (retainedProductInclusion (a ≫ q) (f ≫ π) jB ≫
        pullback.fst (a ≫ q) (f ≫ π)) (𝟙 A)
    simp only [normProductMap_fst, retainedProductInclusion_fst]
    exact IsPullback.id_horiz (pullback.fst (a ≫ q) (jB ≫ (f ≫ π)))

end AlgebraicGeometry.Scheme.Hom
