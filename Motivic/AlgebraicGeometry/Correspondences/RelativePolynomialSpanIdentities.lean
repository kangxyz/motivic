/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.AlgebraicGeometry.Correspondences.RelativePolynomialOpenSpans
public import Motivic.AlgebraicGeometry.Correspondences.PolynomialOpenSpanIdentities
/-! # Relative polynomial identities in the original k-correspondence group -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient
universe u
namespace Motivic.RelativePolynomialOpenSpans
variable {k R A : Type u} [Field k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra.Smooth k R] [Algebra R A] [Algebra k A]
    [IsScalarTower k R A] [Algebra.Smooth k A]

/-- The same relative ambient closed immersion, with the literal k-site structural maps. -/
def ambient : Spec (.of A[X]) ⟶
    pullback (sourceSite (k := k) (A := A)).hom (lineSite (k := k) (R := R)).hom :=
  ambientChangeBase (algebraMap R A) (Spec.map (CommRingCat.ofHom (algebraMap k R))) ≫
    (pullback.congrHom (coefficient_base (k := k) (R := R) (A := A)) rfl).hom

instance ambient_closed : IsClosedImmersion (ambient (k := k) (R := R) (A := A)) := by
  dsimp [ambient]
  infer_instance

theorem joint_eq (p : A[X]) :
    pullback.lift (source p) (target (algebraMap R A) p) (affine_base (k := k) p) =
      inclusion p ≫ ambient (k := k) (R := R) (A := A) := by
  apply pullback.hom_ext <;> simp [ambient, target, pullback.congrHom]

instance joint_closed (p : A[X]) : IsClosedImmersion
    (pullback.lift (source p) (target (algebraMap R A) p) (affine_base (k := k) p)) := by
  rw [joint_eq]
  infer_instance

variable [IsNoetherianRing A]

theorem affineCycle_toIntegralCycle (p : A[X]) (hp : p.Monic) :
    FiniteCorrespondence.toIntegralCycle
      (f := (sourceSite (k := k) (A := A)).hom)
      (g := (lineSite (k := k) (R := R)).hom) (affineCycle (k := k) (R := R) p hp) =
      IntegralCycle.finitePushforward (ambient (k := k) (R := R)) (quotientCycle p hp) := by
  let : IsFinite (source p) := source_finite p hp
  let : Flat (source p) := source_flat p hp
  rw [affineCycle, Cor.toIntegralCycle_ofFiniteFlatSpan]
  change IntegralCycle.finitePushforward
    (pullback.lift (source p) (target (algebraMap R A) p) (affine_base (k := k) p))
    (fundamentalCycle (Spec (.of (AdjoinRoot p)))) = _
  simp only [joint_eq, IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]
  rfl

/-- Product multiplicities are retained before any open restriction. -/
theorem affineCycle_mul [IsDomain A] (p q : A[X]) (hp : p.Monic) (hq : q.Monic) :
    affineCycle (k := k) (R := R) (p * q) (hp.mul hq) =
      affineCycle (k := k) (R := R) p hp + affineCycle (k := k) (R := R) q hq := by
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [map_add, affineCycle_toIntegralCycle, affineCycle_toIntegralCycle,
    affineCycle_toIntegralCycle, quotientCycle_mul, map_add]

/-- Product multiplicities are unchanged in the actual relative open target. -/
theorem cycle_mul [IsDomain A] (p q : A[X]) (hp : p.Monic) (hq : q.Monic) (f : R[X])
    (hpf : IsUnit (AdjoinRoot.mk p (f.map (algebraMap R A))))
    (hqf : IsUnit (AdjoinRoot.mk q (f.map (algebraMap R A))))
    (hpqf : IsUnit (AdjoinRoot.mk (p * q) (f.map (algebraMap R A)))) :
    cycle (k := k) (p * q) (hp.mul hq) f hpqf =
      cycle (k := k) p hp f hpf + cycle (k := k) q hq f hqf := by
  let : IsOpenImmersion (openInclusion (k := k) f).left := inferInstanceAs
    (IsOpenImmersion (principalOpen f).ι)
  apply Cor.comp_open_graph_injective (openInclusion (k := k) f)
  dsimp only
  erw [Preadditive.add_comp, cycle_comp_inclusion, cycle_comp_inclusion, cycle_comp_inclusion]
  exact affineCycle_mul p q hp hq

end Motivic.RelativePolynomialOpenSpans
