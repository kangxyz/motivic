/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.FiniteCurve.Faces.FiniteDominantFaceCoordinates
public import Motivic.Aglib.AlgebraicGeometry.Stalk.GenericFiber.FiniteSupportCoheight
public import Motivic.Aglib.AlgebraicGeometry.Scheme.FunctionField.NonzeroAffineFraction
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Restriction.Open

/-!
# Original endpoint support in the retained smooth curve

The whole evaluation face of a finite dominant integral family is retained.
Its component generic points lie over the generic base point by going down.
The native generic-fibre stalk equivalence then computes their coheight in the
original smooth curve. Nonzero pushed coefficients retain an actual point and
an actual affine fraction chart; no flatness or reduced face is substituted.


Intended upstream module:
`Aglib.AlgebraicGeometry.Cycles.FiniteCurve.Faces.FiniteDominantFaceCurvePlacement`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Endpoints.ComponentFacePlacement`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Order
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme.FiniteDominantFace

variable {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  {S E V : Scheme.{u}} [IsIntegral S]
  (f : S ⟶ Spec (.of A[X])) [IsFinite f] [IsDominant f]
  (e : E ⟶ S) (b : E ⟶ Spec (.of A)) (a : A)
  (hsq : IsPullback e b f (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))))
  (q : V ⟶ Spec (.of A)) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (i : E ⟶ V) [IsClosedImmersion i] (hi : i ≫ q = b)

include hsq hi in
/-- Every original component generic of the whole face has coheight one in the
retained curve. The intermediate lift is along the original generic-fibre map. -/
theorem original_face_curve_coheight (x : E) (hx : x ∈ genericPoints E) :
    coheight (i x) = 1 := by
  let F := FractionRing A
  have : IsFinite b := MorphismProperty.of_isPullback hsq inferInstance
  have : IsFinite (i ≫ q) := by rw [hi]; infer_instance
  have hzero : q (i x) = (⊥ : PrimeSpectrum A) := by
    rw [← Scheme.Hom.comp_apply, hi]
    exact original_face_generic_over_zero f e b a hsq x hx
  have hfield : LocalRing.GenericFiber.baseMap A F (⊥ : PrimeSpectrum F) =
      (⊥ : PrimeSpectrum A) := by
    apply PrimeSpectrum.ext
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective A F)
  obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback q (LocalRing.GenericFiber.baseMap A F))
    (i x) (⊥ : PrimeSpectrum F) (hzero.trans hfield.symm)
  obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback i (LocalRing.GenericFiber.projection A F q)) x z hz.symm
  have hp : LocalRing.GenericFiber.projection A F q
      (LocalRing.GenericFiber.supportInclusion A F q i y) = i x := by
    have h := congrArg (fun g : LocalRing.GenericFiber.support A F q i ⟶ V => g y)
      (pullback.condition (f := i) (g := LocalRing.GenericFiber.projection A F q))
    simpa only [Scheme.Hom.comp_apply, hy] using h.symm
  simpa only [hp] using LocalRing.GenericFiber.support_image_coheight A F q i y

include hsq hi in
/-- Every nonzero coefficient of the original pushed whole face is supported at
coheight one. Source multiplicities remain its native fundamental cycle. -/
theorem original_face_coefficient_coheight [IsNoetherian E] (y : V)
    (hy : _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward i
          (_root_.AlgebraicGeometry.Scheme.fundamentalCycle E)) y ≠ 0) :
    coheight y = 1 := by
  classical
  rw [_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_finitePushforward_apply,
    _root_.AlgebraicGeometry.Scheme.toPoints_fundamentalCycle,
    _root_.AlgebraicGeometry.Scheme.residuePushforward_eq_mapDomain_of_surjectiveOnStalks] at hy
  have hm : y ∈ i '' (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle E).support := by
    by_contra hn
    exact hy (Finsupp.mapDomain_of_not_mem_image_support hn)
  obtain ⟨x, hx, rfl⟩ := hm
  exact original_face_curve_coheight f e b a hsq q i hi x
    ((_root_.AlgebraicGeometry.Scheme.mem_support_fundamentalPointCycle x).mp hx)

include hsq hi in
/-- At every nonzero original endpoint coefficient, a specified nonzero rational
function has an actual affine numerator and denominator on the retained curve. -/
theorem original_face_coefficient_affine_fraction [IsNoetherian E] [IsIntegral V]
    (r : V.functionField) (hr : r ≠ 0) (y : V)
    (hy : _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward i
          (_root_.AlgebraicGeometry.Scheme.fundamentalCycle E)) y ≠ 0) :
    coheight y = 1 ∧ ∃ (U : V.Opens) (_ : IsAffineOpen U) (hyU : y ∈ U)
      (n d : Γ(V, U)),
        (∀ (z : V) (hz : z ∈ U),
          V.presheaf.germ U z hz n ≠ 0 ∧ V.presheaf.germ U z hz d ≠ 0) ∧
        (letI : Nonempty U := ⟨⟨y, hyU⟩⟩
         V.germToFunctionField U n / V.germToFunctionField U d = r) := by
  refine ⟨original_face_coefficient_coheight f e b a hsq q i hi y hy, ?_⟩
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ (⊤ : V.Opens) from trivial)
  let : Nonempty U := ⟨⟨y, hyU⟩⟩
  obtain ⟨n, d, hn, hnd⟩ := V.exists_nonzero_affine_fraction U hU r hr
  exact ⟨U, hU, hyU, n, d, hn, hnd⟩

end AlgebraicGeometry.Scheme.FiniteDominantFace
