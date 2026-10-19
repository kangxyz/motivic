/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Components
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Generalizing.Components
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.QuasiFinite.GenericFiber
public import Motivic.Aglib.AlgebraicGeometry.Cycles.FundamentalSupport

/-!
# Generic points of base-changed finite-flat components

Over a Noetherian base with normal domain stalks, the base change of each
actual reduced component of a finite-flat family is generalizing over the
test scheme. Its generic points therefore map to generic points of the whole
base change. The whole family and both pullbacks may be nonreduced and
disconnected. No flatness of the reduced component is asserted.

The current proof reuses the project's component-generalization API; this
module is not yet a standalone upstream Aglib import.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RelativeFiniteFlat

variable {P B A : Scheme.{u}} (f : P ⟶ B) (e : A ⟶ B)
  (z : genericPoints P)

/-- The literal inclusion of an original reduced generic component. -/
abbrev componentInclusion :=
    (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure z.val).val.subschemeι

/-- The original component pullback maps to the entire original family pullback. -/
def componentBaseChangeMap : pullback e (componentInclusion z ≫ f) ⟶ pullback e f :=
  pullback.map e (componentInclusion z ≫ f) e f (𝟙 A) (componentInclusion z) (𝟙 B)
    (by simp) (by simp)

@[reassoc (attr := simp)]
theorem componentBaseChangeMap_fst :
    componentBaseChangeMap f e z ≫ pullback.fst e f =
      pullback.fst e (componentInclusion z ≫ f) := by
  simp [componentBaseChangeMap, pullback.map]

@[reassoc (attr := simp)]
theorem componentBaseChangeMap_snd :
    componentBaseChangeMap f e z ≫ pullback.snd e f =
      pullback.snd e (componentInclusion z ≫ f) ≫ componentInclusion z := by
  simp [componentBaseChangeMap, pullback.map]

/-- The component map is the actual base change of its original closed inclusion. -/
theorem componentBaseChangeMap_isPullback :
    IsPullback (componentBaseChangeMap f e z)
      (pullback.snd e (componentInclusion z ≫ f)) (pullback.snd e f)
      (componentInclusion z) := by
  apply IsPullback.of_right (t := IsPullback.of_hasPullback e f)
  · simpa only [componentBaseChangeMap_fst] using
      IsPullback.of_hasPullback e (componentInclusion z ≫ f)
  · exact componentBaseChangeMap_snd f e z

instance componentBaseChangeMap_isClosedImmersion :
    IsClosedImmersion (componentBaseChangeMap f e z) :=
  MorphismProperty.of_isPullback (componentBaseChangeMap_isPullback f e z).flip
    (inferInstanceAs (IsClosedImmersion (componentInclusion z)))

variable [IsFinite f] [Flat f]

/-- Finite-flat dominance identifies the component's actual image in the base. -/
theorem range_component_mem :
    Set.range (componentInclusion z ≫ f) ∈ irreducibleComponents B := by
  change Set.range (f ∘ componentInclusion z) ∈ _
  rw [Set.range_comp, Scheme.IdealSheafData.range_subschemeι]
  exact f.image_closure_mem_irreducibleComponents_of_finite_flat z.val z.property

variable [IsNoetherian B] [LocallyOfFiniteType e]
  (hB : ∀ b : B, IsDomain (B.presheaf.stalk b) ∧
    IsIntegrallyClosed (B.presheaf.stalk b))

include hB

/-- The component pullback projection is generalizing by the actual normal
component theorem, without any component-flatness hypothesis. -/
theorem componentBaseChange_generalizing :
    GeneralizingMap (pullback.fst e (componentInclusion z ≫ f)) :=
  _root_.AlgebraicGeometry.Scheme.Products.generalizingMap_of_isPullback_component _ _ _ _
      (.of_hasPullback _ _)
    (range_component_mem f z) hB

/-- Every generic point of a reduced component's actual base change maps to a
generic point of the whole, possibly nonreduced, finite-flat base change. -/
theorem componentBaseChangeMap_mem_genericPoints
    (x : pullback (C := Scheme.{u}) e (componentInclusion z ≫ f))
    (hx : x ∈ genericPoints (pullback (C := Scheme.{u}) e (componentInclusion z ≫ f))) :
    componentBaseChangeMap f e z x ∈ genericPoints (pullback (C := Scheme.{u}) e f) := by
  apply _root_.AlgebraicGeometry.Scheme.Hom.mem_genericPoints_of_image_generic (pullback.fst e f)
  have h := _root_.AlgebraicGeometry.Scheme.Hom.mem_genericPoints_of_generalizing _
    (componentBaseChange_generalizing f e z hB) x hx
  have heq := congrArg (fun q ↦ q x) (componentBaseChangeMap_fst f e z)
  change pullback.fst e f (componentBaseChangeMap f e z x) =
    pullback.fst e (componentInclusion z ≫ f) x at heq
  rwa [heq]

end AlgebraicGeometry.RelativeFiniteFlat
