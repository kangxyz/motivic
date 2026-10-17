/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.FiniteFlatCurveSpecialization
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Whole endpoint fibers under restriction of scalars

The literal polynomial coefficient map carries the endpoint at `a` to the
endpoint at its image. Its Cartesian square identifies the whole endpoint
fiber of a scheme over the larger affine line with its endpoint fiber after
composition to the smaller affine line. The original inclusion and scalar
projection are retained, as are every nilpotent and local multiplicity.

The geometric comparison needs neither finiteness nor separability, and it
does not require the scheme to be smooth over either field.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Motivic
open scoped Polynomial

universe u

namespace AlgebraicGeometry.ScalarExtensionEndpointFiber

section Rings

variable {R S : Type u} [CommRing R] [CommRing S] (c : R →+* S) (a : R)

/-- Evaluation commutes with the actual coefficient homomorphism. -/
theorem evaluation_square :
    CommRingCat.ofHom (Polynomial.mapRingHom c) ≫
        CommRingCat.ofHom (Polynomial.evalRingHom (c a)) =
      CommRingCat.ofHom (Polynomial.evalRingHom a) ≫ CommRingCat.ofHom c := by
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun p => Polynomial.eval_map_apply c a)

/-- The literal evaluation square is a pushout, without assumptions on the
coefficient homomorphism. -/
theorem evaluation_isPushout :
    IsPushout (CommRingCat.ofHom (Polynomial.mapRingHom c))
      (CommRingCat.ofHom (Polynomial.evalRingHom a))
      (CommRingCat.ofHom (Polynomial.evalRingHom (c a))) (CommRingCat.ofHom c) := by
  apply IsPushout.of_isColimit
    (c := PushoutCocone.mk _ _ (evaluation_square c a))
  apply PushoutCocone.isColimitAux'
  intro s
  let d : CommRingCat.of S ⟶ s.pt :=
    CommRingCat.ofHom (s.inl.hom.comp Polynomial.C)
  refine ⟨d, ?_, ?_, ?_⟩
  · apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro r
      simp [d]
    · have hX := congrArg (fun f => f Polynomial.X) s.condition
      have hC := congrArg (fun f => f (Polynomial.C a)) s.condition
      change s.inl (Polynomial.map c Polynomial.X) =
        s.inr (Polynomial.eval a Polynomial.X) at hX
      change s.inl (Polynomial.map c (Polynomial.C a)) =
        s.inr (Polynomial.eval a (Polynomial.C a)) at hC
      simp only [Polynomial.map_X, Polynomial.eval_X] at hX
      simp only [Polynomial.map_C, Polynomial.eval_C] at hC
      simpa [d] using hC.trans hX.symm
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    have h := congrArg (fun f => f (Polynomial.C r)) s.condition
    simpa [d] using h
  · intro h hl _
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    have hc := congrArg (fun f => f (Polynomial.C r)) hl
    simpa [d] using hc

end Rings

open FiniteFlatCurve

variable {k E : Type u} [Field k] [Field E] (c : k →+* E)

/-- The actual scalar morphism between affine lines. -/
abbrev coefficientMap : Spec (.of E[X]) ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom c))

/-- The full closed endpoint square is Cartesian. -/
theorem endpoint_isPullback (a : k) :
    IsPullback (endpoint (c a)) (Spec.map (CommRingCat.ofHom c))
      (coefficientMap c) (endpoint a) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (evaluation_isPushout c a)

variable {C : Scheme.{u}} (f : C ⟶ Spec (.of E[X])) (a : k)

/-- Pasting with the original fiber square retains its original projection
to the source scheme. -/
theorem fiber_isPullback :
    IsPullback
      (pullback.fst (endpoint (c a)) f ≫ Spec.map (CommRingCat.ofHom c))
      (fiberInclusion f (c a)) (endpoint a) (f ≫ coefficientMap c) :=
  (IsPullback.of_hasPullback (endpoint (c a)) f).paste_horiz
    (endpoint_isPullback c a).flip

/-- The entire fiber after restriction of scalars is the original entire
fiber at the image endpoint, with no reduction. -/
def fiberIso : fiber (f ≫ coefficientMap c) a ≅ fiber f (c a) :=
  (fiber_isPullback c f a).isoPullback.symm

/-- The forward comparison retains the original source inclusion. -/
@[reassoc (attr := simp)]
theorem fiberIso_hom_inclusion :
    (fiberIso c f a).hom ≫ fiberInclusion f (c a) =
      fiberInclusion (f ≫ coefficientMap c) a :=
  (fiber_isPullback c f a).isoPullback_inv_snd

/-- The reverse comparison retains the same source inclusion. -/
@[reassoc (attr := simp)]
theorem fiberIso_inv_inclusion :
    (fiberIso c f a).inv ≫ fiberInclusion (f ≫ coefficientMap c) a =
      fiberInclusion f (c a) :=
  (fiber_isPullback c f a).isoPullback_hom_snd

/-- The field projection is the actual original field map. -/
@[reassoc (attr := simp)]
theorem fiberIso_inv_scalar :
    (fiberIso c f a).inv ≫ pullback.fst (endpoint a) (f ≫ coefficientMap c) =
      pullback.fst (endpoint (c a)) f ≫ Spec.map (CommRingCat.ofHom c) :=
  (fiber_isPullback c f a).isoPullback_hom_fst

/-- The forward comparison gives the same literal scalar square. -/
@[reassoc (attr := simp)]
theorem fiberIso_hom_scalar :
    (fiberIso c f a).hom ≫ pullback.fst (endpoint (c a)) f ≫
        Spec.map (CommRingCat.ofHom c) =
      pullback.fst (endpoint a) (f ≫ coefficientMap c) :=
  (fiber_isPullback c f a).isoPullback_inv_fst

/-- The whole fundamental cycle, including all original local lengths, is
preserved by the literal endpoint comparison. -/
theorem finitePushforward_fiberIso [IsNoetherian C] :
    IntegralCycle.finitePushforward (fiberIso c f a).hom
        (fundamentalCycle (fiber (f ≫ coefficientMap c) a)) =
      fundamentalCycle (fiber f (c a)) :=
  finitePushforward_fundamentalCycle (fiberIso c f a).hom

/-- Transport into any fixed finite target keeps the original source map. -/
theorem finitePushforward_fiberInclusion [IsNoetherian C]
    {T : Scheme.{u}} (g : C ⟶ T) [IsFinite g] :
    IntegralCycle.finitePushforward (fiberInclusion (f ≫ coefficientMap c) a ≫ g)
        (fundamentalCycle (fiber (f ≫ coefficientMap c) a)) =
      IntegralCycle.finitePushforward (fiberInclusion f (c a) ≫ g)
        (fundamentalCycle (fiber f (c a))) := by
  have h : IntegralCycle.finitePushforward
      ((fiberIso c f a).hom ≫ fiberInclusion f (c a) ≫ g)
      (fundamentalCycle (fiber (f ≫ coefficientMap c) a)) =
      IntegralCycle.finitePushforward (fiberInclusion f (c a) ≫ g)
        (fundamentalCycle (fiber f (c a))) := by
    rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
      finitePushforward_fiberIso]
  simpa only [fiberIso_hom_inclusion_assoc] using h

end AlgebraicGeometry.ScalarExtensionEndpointFiber
