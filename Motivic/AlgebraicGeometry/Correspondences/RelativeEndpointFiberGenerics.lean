/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeFiniteFlatFiberGenerics
public import Motivic.AlgebraicGeometry.Correspondences.RelativeEndpointDiagram
public import Motivic.AlgebraicGeometry.SmoothSiteProducts

/-!
# Generic support in the whole relative endpoint fiber

The base change by the literal endpoint of `X × A¹` is identified with the
whole parameter fiber, including nilpotents. The original component fiber map
preserves generic points when the family is finite-flat and `X` is smooth.
No component-flatness or global integrality hypothesis is used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.RelativeEndpointDiagram

variable {k : Type u} [Field k] {X P : Scheme.{u}} (b : X ⟶ Spec (.of k))
  (f : P ⟶ relativeLine b) (a : k)

/-- The actual parameter of the original relative family. -/
abbrev familyParameter : P ⟶ Spec (.of (Polynomial k)) :=
  f ≫ pullback.snd b (FiniteFlatCurveFamily.line k).hom

/-- The relative endpoint square pastes to the original whole parameter fiber. -/
theorem relativeFiber_isPullback :
    IsPullback (pullback.fst (endpoint b a) f ≫ b)
      (pullback.snd (endpoint b a) f) (FiniteFlatCurve.endpoint a)
      (familyParameter b f) :=
  (IsPullback.of_hasPullback (endpoint b a) f).paste_horiz (endpoint_isPullback b a)

/-- The literal isomorphism between the two whole endpoint-fiber models. -/
def relativeFiberIso : pullback (endpoint b a) f ≅ FiniteFlatCurve.fiber
    (familyParameter b f) a := (relativeFiber_isPullback b f a).isoPullback

@[reassoc (attr := simp)]
theorem relativeFiberIso_hom_inclusion :
    (relativeFiberIso b f a).hom ≫ FiniteFlatCurve.fiberInclusion (familyParameter b f) a =
      pullback.snd (endpoint b a) f := (relativeFiber_isPullback b f a).isoPullback_hom_snd

variable (z : genericPoints P)

/-- Reassociation is transported by the canonical pullback isomorphism, so
this component fiber has exactly the original parameter-map expression. -/
def componentRelativeFiberIso :
    pullback (endpoint b a) (RelativeFiniteFlat.componentInclusion z ≫ f) ≅
      FiniteFlatCurve.fiber (RelativeFiniteFlat.componentInclusion z ≫
        familyParameter b f) a :=
  relativeFiberIso b (RelativeFiniteFlat.componentInclusion z ≫ f) a ≪≫
    pullback.congrHom rfl (Category.assoc _ _ _)

@[reassoc (attr := simp)]
theorem componentRelativeFiberIso_hom_inclusion :
    (componentRelativeFiberIso b f a z).hom ≫
      FiniteFlatCurve.fiberInclusion (RelativeFiniteFlat.componentInclusion z ≫
        familyParameter b f) a =
      pullback.snd (endpoint b a) (RelativeFiniteFlat.componentInclusion z ≫ f) := by
  simp only [componentRelativeFiberIso, Iso.trans_hom, Category.assoc,
    pullback.congrHom_hom, pullback.map, FiniteFlatCurve.fiberInclusion,
    pullback.lift_snd, Category.comp_id]
  exact relativeFiberIso_hom_inclusion b (RelativeFiniteFlat.componentInclusion z ≫ f) a

/-- The two canonical component maps agree under the actual fiber isomorphisms. -/
@[reassoc]
theorem relativeFiberIso_componentMap :
    RelativeFiniteFlat.componentBaseChangeMap f (endpoint b a) z ≫
        (relativeFiberIso b f a).hom =
      (componentRelativeFiberIso b f a z).hom ≫
        FiniteFlatCurve.fiberMap (familyParameter b f) a
          (RelativeFiniteFlat.componentInclusion z) := by
  apply (cancel_mono (FiniteFlatCurve.fiberInclusion (familyParameter b f) a)).mp
  simp only [Category.assoc, relativeFiberIso_hom_inclusion,
    RelativeFiniteFlat.componentBaseChangeMap_snd, FiniteFlatCurve.fiberMap_inclusion,
    componentRelativeFiberIso_hom_inclusion_assoc]

/-- Generic support transport in the literal parameter-fiber model over an
explicit normal relative base. All whole fibers retain their scheme structure. -/
theorem componentFiberMap_mem_genericPoints
    [IsFinite f] [Flat f] [IsNoetherian (relativeLine b)]
    (hB : ∀ v : relativeLine b, IsDomain ((relativeLine b).presheaf.stalk v) ∧
      IsIntegrallyClosed ((relativeLine b).presheaf.stalk v))
    (x : FiniteFlatCurve.fiber (RelativeFiniteFlat.componentInclusion z ≫
      familyParameter b f) a)
    (hx : x ∈ genericPoints (FiniteFlatCurve.fiber
      (RelativeFiniteFlat.componentInclusion z ≫ familyParameter b f) a)) :
    FiniteFlatCurve.fiberMap (familyParameter b f) a
      (RelativeFiniteFlat.componentInclusion z) x ∈
        genericPoints (FiniteFlatCurve.fiber (familyParameter b f) a) := by
  let e := componentRelativeFiberIso b f a z
  have hx' := mem_genericPoints_of_generalizing e.inv (Flat.generalizingMap e.inv) x hx
  have hy := RelativeFiniteFlat.componentBaseChangeMap_mem_genericPoints f (endpoint b a) z
    hB (e.inv x) hx'
  have hz := mem_genericPoints_of_generalizing (relativeFiberIso b f a).hom
    (Flat.generalizingMap _) _ hy
  have heq := congrArg (fun q ↦ q (e.inv x)) (relativeFiberIso_componentMap b f a z)
  change (relativeFiberIso b f a).hom
      (RelativeFiniteFlat.componentBaseChangeMap f (endpoint b a) z (e.inv x)) =
    FiniteFlatCurve.fiberMap (familyParameter b f) a
      (RelativeFiniteFlat.componentInclusion z) (e.hom (e.inv x)) at heq
  have hinv : e.hom (e.inv x) = x := by
    change (e.inv ≫ e.hom) x = x
    rw [e.inv_hom_id]
    rfl
  rw [hinv] at heq
  rwa [← heq]

/-- Smoothness supplies normal domain stalks componentwise, even for a
disconnected source. This is the actual finite-flat relative endpoint input. -/
theorem componentFiberMap_mem_genericPoints_smooth
    (X : SmoothSite (Spec (.of k))) {P : Scheme.{u}}
    (f : P ⟶ relativeLine X.hom) [IsFinite f] [Flat f] (a : k)
    (z : genericPoints P)
    (x : FiniteFlatCurve.fiber (RelativeFiniteFlat.componentInclusion z ≫
      familyParameter X.hom f) a)
    (hx : x ∈ genericPoints (FiniteFlatCurve.fiber
      (RelativeFiniteFlat.componentInclusion z ≫ familyParameter X.hom f) a)) :
    FiniteFlatCurve.fiberMap (familyParameter X.hom f) a
      (RelativeFiniteFlat.componentInclusion z) x ∈
        genericPoints (FiniteFlatCurve.fiber (familyParameter X.hom f) a) := by
  have : IsNoetherian (relativeLine X.hom) :=
    inferInstanceAs (IsNoetherian (SmoothSite.product X (FiniteFlatCurveFamily.line k)).left)
  exact componentFiberMap_mem_genericPoints X.hom f a z
    (fun v ↦ ⟨SmoothSite.isDomain_stalk k
      (SmoothSite.product X (FiniteFlatCurveFamily.line k)) v,
      SmoothSite.isIntegrallyClosed_stalk k
        (SmoothSite.product X (FiniteFlatCurveFamily.line k)) v⟩) x hx

end Motivic.RelativeEndpointDiagram
