/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Polynomial.Interpolation.TwoUnitFamily
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Endpoints.FiniteFlatCurveSpecialization
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Retaining the root in a finite polynomial family

The parameter and the adjoined root generate the entire quotient algebra.
Keeping both coordinates therefore gives a closed immersion, even when the
additional coordinates identify points or erase nilpotent structure. All
fibers below are the original scheme-theoretic fibers.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open Polynomial.TwoUnitPolynomialFamily

universe u

namespace AlgebraicGeometry.FiniteTwoUnitPolynomialFamily

variable {k : Type u} [Field k]

/-- The full polynomial quotient, without reduction or localization. -/
abbrev familyScheme (f : k[X][X]) : Scheme.{u} := Spec (.of (AdjoinRoot f))

/-- The literal affine parameter projection. -/
def projection (f : k[X][X]) : familyScheme f ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (AdjoinRoot.of f))

/-- The original constant-field map. -/
def constantMap (f : k[X][X]) : k →+* AdjoinRoot f := (AdjoinRoot.of f).comp C

/-- The retained affine root coordinate. -/
def rootMap (f : k[X][X]) : familyScheme f ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (eval₂RingHom (constantMap f) (AdjoinRoot.root f)))

@[reassoc (attr := simp)] theorem rootMap_structure (f : k[X][X]) :
    rootMap f ≫ Spec.map (CommRingCat.ofHom (C : k →+* k[X])) =
      Spec.map (CommRingCat.ofHom (constantMap f)) := by
  rw [rootMap, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change eval₂ (constantMap f) (AdjoinRoot.root f) (C r) = constantMap f r
  simp only [eval₂_C]

/-- Monicity gives finiteness of the original projection. -/
theorem projection_finite {f : k[X][X]} (hf : f.Monic) : IsFinite (projection f) := by
  let : Module.Finite k[X] (AdjoinRoot f) := hf.finite_adjoinRoot
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- Monicity gives flatness, with all nilpotents retained. -/
theorem projection_flat {f : k[X][X]} (hf : f.Monic) : Flat (projection f) := by
  let : Module.Free k[X] (AdjoinRoot f) := hf.free_adjoinRoot
  apply Flat.SpecMap_iff.mpr
  change (AdjoinRoot.of f).Flat
  rw [← AdjoinRoot.algebraMap_eq]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

private def affinePullback {R : Type u} [CommRing R] {W : Scheme.{u}}
    (f : W ⟶ Spec (.of R)) : R →+* Γ(W, ⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom

private theorem affinePullback_comp {R S : Type u} [CommRing R] [CommRing S]
    {W : Scheme.{u}} (f : W ⟶ Spec (.of S)) (g : R →+* S) :
    affinePullback (f ≫ Spec.map (CommRingCat.ofHom g)) =
      (affinePullback f).comp g := by
  apply RingHom.ext
  intro r
  change f.appTop ((Spec.map (CommRingCat.ofHom g)).appTop
      ((Scheme.ΓSpecIso (.of R)).inv r)) =
    f.appTop ((Scheme.ΓSpecIso (.of S)).inv (g r))
  congr 1
  exact ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g)).symm r

/-- The parameter and retained root determine every map into the full quotient. -/
theorem family_hom_ext (f : k[X][X]) {W : Scheme.{u}} {r s : W ⟶ familyScheme f}
    (ht : r ≫ projection f = s ≫ projection f)
    (hz : r ≫ rootMap f = s ≫ rootMap f) : r = s := by
  have ht' : (affinePullback r).comp (AdjoinRoot.of f) =
      (affinePullback s).comp (AdjoinRoot.of f) := by
    simpa only [projection, affinePullback_comp] using congrArg affinePullback ht
  have hz' := congrArg affinePullback hz
  simp only [rootMap, affinePullback_comp] at hz'
  have hc := RingHom.congr_fun hz' X
  simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X] at hc
  have he := AdjoinRoot.ringHom_ext ht' hc
  apply ext_of_isAffine
  apply (cancel_epi (Scheme.ΓSpecIso (.of (AdjoinRoot f))).inv).mp
  exact CommRingCat.hom_ext he

/-- Any separated ambient map retaining parameter and root is a closed immersion.
No injectivity hypothesis on any additional coordinates is needed. -/
theorem closedImmersion_of_coordinates {f : k[X][X]} (hf : f.Monic)
    {Q : Scheme.{u}} (j : familyScheme f ⟶ Q)
    (t z : Q ⟶ Spec (.of k[X])) [IsSeparated t]
    (ht : j ≫ t = projection f) (hz : j ≫ z = rootMap f) :
    IsClosedImmersion j := by
  have : IsFinite (projection f) := projection_finite hf
  have : IsFinite (j ≫ t) := by rw [ht]; infer_instance
  have : IsFinite j := IsFinite.of_comp j t
  apply (IsClosedImmersion.iff_isFinite_and_mono j).mpr
  refine ⟨inferInstance, ⟨?_⟩⟩
  intro W r s h
  apply family_hom_ext f
  · simpa only [Category.assoc, ht] using congrArg (fun q => q ≫ t) h
  · simpa only [Category.assoc, hz] using congrArg (fun q => q ≫ z) h

/-- The full scheme-theoretic scalar fiber. -/
abbrev fiber (f : k[X][X]) (s : k) : Scheme.{u} :=
  FiniteFlatCurve.fiber (projection f) s

/-- The whole fiber's tensor-product presentation. -/
def fiberSchemeIso (f : k[X][X]) (s : k) :
    fiber f s ≅ Spec (.of (Algebra.PolynomialFiber.Fiber (AdjoinRoot f) s)) := by
  letI : Algebra k[X] k := Algebra.PolynomialFiber.evaluationAlgebra s
  exact pullbackSpecIso k[X] k (AdjoinRoot f)

@[reassoc (attr := simp)] theorem fiberSchemeIso_inv_fst (f : k[X][X]) (s : k) :
    (fiberSchemeIso f s).inv ≫ pullback.fst (FiniteFlatCurve.endpoint s) (projection f) =
      Spec.map (CommRingCat.ofHom
        (algebraMap k (Algebra.PolynomialFiber.Fiber (AdjoinRoot f) s))) := by
  let : Algebra k[X] k := Algebra.PolynomialFiber.evaluationAlgebra s
  exact pullbackSpecIso_inv_fst' k[X] k (AdjoinRoot f)

@[reassoc (attr := simp)] theorem fiberSchemeIso_inv_snd (f : k[X][X]) (s : k) :
    (fiberSchemeIso f s).inv ≫ pullback.snd (FiniteFlatCurve.endpoint s) (projection f) =
      Spec.map (CommRingCat.ofHom (Algebra.PolynomialFiber.specialize (AdjoinRoot f) s)) := by
  let : Algebra k[X] k := Algebra.PolynomialFiber.evaluationAlgebra s
  exact pullbackSpecIso_inv_snd k[X] k (AdjoinRoot f)

/-- The entire fiber is its literal specialized polynomial quotient. -/
def fiberPolynomialSchemeIso (f : k[X][X]) (s : k) (p : k[X])
    (hp : f.map (evalRingHom s) = p) : fiber f s ≅ Spec (.of (AdjoinRoot p)) :=
  fiberSchemeIso f s ≪≫
    Scheme.Spec.mapIso (endpointFiberEquiv f s p hp).symm.toRingEquiv.toCommRingCatIso.op

@[reassoc (attr := simp)] theorem fiberPolynomialSchemeIso_inv_fst
    (f : k[X][X]) (s : k) (p : k[X]) (hp : f.map (evalRingHom s) = p) :
    (fiberPolynomialSchemeIso f s p hp).inv ≫
        pullback.fst (FiniteFlatCurve.endpoint s) (projection f) =
      Spec.map (CommRingCat.ofHom (AdjoinRoot.of p)) := by
  rw [fiberPolynomialSchemeIso, Iso.trans_inv, Category.assoc, fiberSchemeIso_inv_fst]
  change Spec.map (CommRingCat.ofHom (endpointFiberEquiv f s p hp).toRingHom) ≫
    Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (endpointFiberEquiv f s p hp).commutes

@[reassoc (attr := simp)] theorem fiberPolynomialSchemeIso_inv_snd
    (f : k[X][X]) (s : k) (p : k[X]) (hp : f.map (evalRingHom s) = p) :
    (fiberPolynomialSchemeIso f s p hp).inv ≫
        pullback.snd (FiniteFlatCurve.endpoint s) (projection f) =
      Spec.map (CommRingCat.ofHom (endpoint f s p hp)) := by
  rw [fiberPolynomialSchemeIso, Iso.trans_inv, Category.assoc, fiberSchemeIso_inv_snd]
  change Spec.map (CommRingCat.ofHom (endpointFiberEquiv f s p hp).toRingHom) ≫
    Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro r
    exact (endpointFiberEquiv_of f s p hp r).trans (endpoint_of f s p hp r).symm
  · exact (endpointFiberEquiv_root f s p hp).trans (endpoint_root f s p hp).symm

end AlgebraicGeometry.FiniteTwoUnitPolynomialFamily
