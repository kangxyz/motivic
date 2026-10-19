/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Polynomial.Open.Spans
public import Motivic.AlgebraicGeometry.Correspondences.Support.OpenTargetFaithfulness
public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialQuotient.PolynomialQuotientCoordinates
public import Motivic.Aglib.AlgebraicGeometry.Cycles.PolynomialQuotient.Product
public import Motivic.AlgebraicGeometry.Correspondences.Composition.DiagonalZeroCycle
/-! # Actual product and linear-graph identities for monic open-target spans -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient
universe u
namespace Motivic.PolynomialOpenSpans
open _root_.AlgebraicGeometry.Scheme
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]

/-- The whole quotient correspondence before retaining its open target. -/
def affineCycle (p : R[X]) (hp : p.Monic) :
    Cor.mk (affineSite (k := k) (R := R)) ⟶ Cor.mk (SmoothSite.affineLine (.of k)) := by
  let : IsFinite (source p) := source_finite p hp
  let : Flat (source p) := source_flat p hp
  exact Cor.ofFiniteFlatSpan (source p) (target (algebraMap k R) p)
    (target_base (algebraMap k R) p).symm

variable [IsNoetherianRing R]

theorem affineCycle_toIntegralCycle (p : R[X]) (hp : p.Monic) :
    FiniteCorrespondence.toIntegralCycle
      (f := (affineSite (k := k) (R := R)).hom)
      (g := (SmoothSite.affineLine (.of k)).hom) (affineCycle (k := k) (R := R) p hp) =
      IntegralCycle.finitePushforward (ambientIso (algebraMap k R)).hom (quotientCycle p hp) := by
  let : IsFinite (source p) := source_finite p hp
  let : Flat (source p) := source_flat p hp
  rw [affineCycle, Cor.toIntegralCycle_ofFiniteFlatSpan]
  change IntegralCycle.finitePushforward
    (pullback.lift (source p) (target (algebraMap k R) p)
      (target_base (algebraMap k R) p).symm)
    (fundamentalCycle (Spec (.of (AdjoinRoot p)))) = _
  simp only [joint_eq, IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]
  rfl

/-- Repeated factors retain their full multiplicities in the actual correspondence group. -/
theorem affineCycle_mul [IsDomain R] (p q : R[X]) (hp : p.Monic) (hq : q.Monic) :
    affineCycle (k := k) (p * q) (hp.mul hq) = affineCycle p hp + affineCycle q hq := by
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [map_add, affineCycle_toIntegralCycle, affineCycle_toIntegralCycle,
    affineCycle_toIntegralCycle, quotientCycle_mul, map_add]

/-- The product identity remains in the original open-target correspondence group. -/
theorem cycle_mul [IsDomain R] (p q : R[X]) (hp : p.Monic) (hq : q.Monic) (f : k[X])
    (hpf : IsUnit (AdjoinRoot.mk p (f.map (algebraMap k R))))
    (hqf : IsUnit (AdjoinRoot.mk q (f.map (algebraMap k R))))
    (hpqf : IsUnit (AdjoinRoot.mk (p * q) (f.map (algebraMap k R)))) :
    cycle (p * q) (hp.mul hq) f hpqf = cycle p hp f hpf + cycle q hq f hqf := by
  let : IsOpenImmersion (openInclusion f).left := inferInstanceAs
    (IsOpenImmersion (principalOpen f).ι)
  apply Cor.comp_open_graph_injective (openInclusion f)
  dsimp only
  erw [Preadditive.add_comp, cycle_comp_inclusion, cycle_comp_inclusion, cycle_comp_inclusion]
  exact affineCycle_mul p q hp hq

end Motivic.PolynomialOpenSpans
