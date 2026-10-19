/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Limits

/-! # The whole residual component of an actual marked fiber

The marked component is both open and closed. Its complement is the original
open subscheme of the full fiber, retaining every nilpotent. In particular its
map into the compactification is not factored through a reduced infinity scheme.


Intended upstream module: `Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.ResidualFiber`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.ResidualFiberPullback`,
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.MarkedFiber`,
`Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.ThickenedBoundary`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme
variable {C X Y Z : Scheme.{u}} (f : C ⟶ X) [IsFinite f]
  (j : Y ⟶ C) [IsOpenImmersion j] (z : Z ⟶ X) [IsClosedImmersion z]
  (s : Z ⟶ Y) (hs : (s ≫ j) ≫ f = z)

/-- The actual marked section of the full finite pullback. -/
def markedFiberSection : Z ⟶ pullback f z :=
  pullback.lift (s ≫ j) (𝟙 Z) (by simpa using hs)

omit [IsFinite f] [IsOpenImmersion j] [IsClosedImmersion z] in
@[reassoc (attr := simp)] theorem markedFiberSection_fst :
    markedFiberSection f j z s hs ≫ pullback.fst f z = s ≫ j :=
  pullback.lift_fst _ _ _

omit [IsFinite f] [IsOpenImmersion j] [IsClosedImmersion z] in
@[reassoc (attr := simp)] theorem markedFiberSection_snd :
    markedFiberSection f j z s hs ≫ pullback.snd f z = 𝟙 Z :=
  pullback.lift_snd _ _ _

/-- The marked component is a closed section of the finite, separated projection. -/
instance markedFiberSection_closed : IsClosedImmersion (markedFiberSection f j z s hs) := by
  have : IsClosedImmersion (markedFiberSection f j z s hs ≫ pullback.snd f z) := by
    rw [markedFiberSection_snd]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.snd f z)

variable (H : IsPullback s (𝟙 Z) (j ≫ f) z)

omit [IsFinite f] [IsOpenImmersion j] [IsClosedImmersion z] in
include H in
/-- The original whole marked square identifies exactly the intersection with Y. -/
theorem markedFiberSection_isPullback :
    IsPullback s (markedFiberSection f j z s hs) j (pullback.fst f z) := by
  have H' : IsPullback s (markedFiberSection f j z s hs ≫ pullback.snd f z)
      (j ≫ f) z := by simpa only [markedFiberSection_snd] using H
  exact H'.of_bot (by simp) (IsPullback.of_hasPullback f z)

omit [IsFinite f] [IsClosedImmersion z] in
include H in
/-- The marked component is open by base change of the original retained open. -/
theorem markedFiberSection_open : IsOpenImmersion (markedFiberSection f j z s hs) :=
  MorphismProperty.of_isPullback (markedFiberSection_isPullback f j z s hs H) inferInstance

/-- The complementary open carries the full residual fiber scheme structure. -/
def residualMarkedFiberOpen : (pullback f z).Opens :=
  ⟨(Set.range (markedFiberSection f j z s hs))ᶜ,
    (markedFiberSection f j z s hs).isClosedMap.isClosed_range.isOpen_compl⟩

/-- The residual component's original map into the compactification. -/
def residualMarkedFiberMap : (residualMarkedFiberOpen f j z s hs).toScheme ⟶ C :=
  (residualMarkedFiberOpen f j z s hs).ι ≫ pullback.fst f z

omit [IsClosedImmersion z] in
include H in
/-- The complementary open immersion is closed as well. -/
theorem residualMarkedFiberInclusion_closed :
    IsClosedImmersion (residualMarkedFiberOpen f j z s hs).ι := by
  have := markedFiberSection_open f j z s hs H
  apply IsClosedImmersion.of_isPreimmersion
  rw [Scheme.Opens.range_ι]
  exact (markedFiberSection f j z s hs).isOpenEmbedding.isOpen_range.isClosed_compl

omit [IsClosedImmersion z] in
include H in
/-- The original residual component maps finitely to the full marked scheme. -/
theorem residualMarkedFiber_finite :
    IsFinite ((residualMarkedFiberOpen f j z s hs).ι ≫ pullback.snd f z) := by
  have := residualMarkedFiberInclusion_closed f j z s hs H
  infer_instance

include H in
/-- Its original compactification map is closed, not merely supported on a closed set. -/
theorem residualMarkedFiberMap_closed : IsClosedImmersion (residualMarkedFiberMap f j z s hs) := by
  have := residualMarkedFiberInclusion_closed f j z s hs H
  dsimp only [residualMarkedFiberMap]
  infer_instance

omit [IsOpenImmersion j] [IsClosedImmersion z] in
include H in
/-- Every residual point lies outside the unchanged retained open. -/
theorem residualMarkedFiberMap_disjoint :
    Disjoint (Set.range j) (Set.range (residualMarkedFiberMap f j z s hs)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨y, rfl⟩ ⟨e, he⟩
  obtain ⟨w, _, hw⟩ := Scheme.exists_preimage_of_isPullback
    (markedFiberSection_isPullback f j z s hs H) y e.val he.symm
  exact e.property ⟨w, hw⟩

/-- The original marked and residual immersions form a coproduct cocone. -/
def markedResidualFiberIsColimit :
    IsColimit (BinaryCofan.mk (markedFiberSection f j z s hs)
      (residualMarkedFiberOpen f j z s hs).ι) := by
  have := markedFiberSection_open f j z s hs H
  let m := markedFiberSection f j z s hs
  let E := residualMarkedFiberOpen f j z s hs
  have hc : IsCompl m.opensRange E.ι.opensRange := by
    have hr : IsCompl (Set.range m) (Set.range E.ι) := by
      rw [Scheme.Opens.range_ι]
      exact isCompl_compl
    convert! hr
    simp only [isCompl_iff, disjoint_iff, codisjoint_iff, ← TopologicalSpace.Opens.coe_inj]
    rfl
  exact (AlgebraicGeometry.nonempty_isColimit_binaryCofanMk_of_isCompl m E.ι hc).some

/-- The literal complementary components give the original entire fiber. -/
def markedResidualFiberIso :
    Z ⨿ (residualMarkedFiberOpen f j z s hs).toScheme ≅ pullback f z :=
  (coprodIsCoprod Z (residualMarkedFiberOpen f j z s hs).toScheme).coconePointUniqueUpToIso
    (markedResidualFiberIsColimit f j z s hs H)

omit [IsClosedImmersion z] in
@[reassoc (attr := simp)] theorem markedResidualFiberIso_inl :
    coprod.inl ≫ (markedResidualFiberIso f j z s hs H).hom = markedFiberSection f j z s hs := by
  dsimp only [markedResidualFiberIso]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom _
    (markedResidualFiberIsColimit f j z s hs H) (Discrete.mk WalkingPair.left)

omit [IsClosedImmersion z] in
@[reassoc (attr := simp)] theorem markedResidualFiberIso_inr :
    coprod.inr ≫ (markedResidualFiberIso f j z s hs H).hom =
      (residualMarkedFiberOpen f j z s hs).ι := by
  dsimp only [markedResidualFiberIso]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom _
    (markedResidualFiberIsColimit f j z s hs H) (Discrete.mk WalkingPair.right)

end AlgebraicGeometry.Scheme
