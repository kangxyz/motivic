/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.Multiplicity.ClosedImmersionKoszulEuler
public import Motivic.Aglib.AlgebraicGeometry.IdealSheaf.Stalk.FlatPolynomialRegularity
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.FiniteFlat.Components
public import Motivic.Aglib.AlgebraicGeometry.Modules.Pushforward.Finite.Injective
public import Motivic.Aglib.RingTheory.Multiplicity.Cartier.CutLength
public import Motivic.Aglib.AlgebraicGeometry.Cycles.GenericCoefficients
public import Motivic.Aglib.AlgebraicGeometry.Diagonal.FlatBaseChange
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.QuasiFinite.GenericFiber
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Fundamental.ClosedSubscheme
public import Mathlib.RingTheory.Polynomial.Ideal

/-!
# Specialization of actual finite-flat curve cycles

The endpoint is a Cartier cut, not a flat base-change map. All fiber schemes
and all their lengths retain their original, possibly nonreduced structure.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits _root_.HomologicalComplex.ModuleLengthEuler
open scoped BigOperators Polynomial

universe u

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme

/-- The original fundamental cycle is the weighted sum of its reduced supports. -/
theorem fundamentalCycle_eq_sum_closed_components (P : Scheme.{u}) [IsNoetherian P] :
    letI := IntegralCycle.genericPointFintype P
    fundamentalCycle P =
      ∑ z : genericPoints P, (genericMultiplicity z : ℤ) •
        IntegralCycle.finitePushforward (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι
          (fundamentalCycle (IntegralClosedSubscheme.pointClosure z.1).val.subscheme) := by
  classical
  let := IntegralCycle.genericPointFintype P
  rw [← IntegralCycle.ofGenericCoefficients_genericMultiplicity,
    IntegralCycle.ofGenericCoefficients_eq_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [← closedFundamentalCycle, closedFundamentalCycle_of_isIntegral]
  simp only [Finsupp.smul_single, zsmul_eq_mul, Int.cast_id, mul_one]
  rfl

/-- At a closed zero-dimensional source, every pushed coefficient is an actual
ambient quotient length, also at ambient points which are not generic. -/
theorem closedImmersion_fundamentalCoefficient_eq_length_of_all_generic
    {E P : Scheme.{u}} (j : E ⟶ P) [IsClosedImmersion j] [IsNoetherian E]
    (hE : ∀ x : E, x ∈ genericPoints E) (x : P) :
    IntegralCycle.toPoints (IntegralCycle.finitePushforward j (fundamentalCycle E)) x =
      ((Module.length (P.presheaf.stalk x)
        ((P.presheaf.stalk x) ⧸ j.ker.stalk x)).toNat : ℤ) := by
  classical
  rw [IntegralCycle.toPoints_finitePushforward_apply, toPoints_fundamentalCycle,
    residuePushforward_eq_mapDomain_of_surjectiveOnStalks]
  change Finsupp.mapDomain j (fundamentalPointCycle E) x = _
  by_cases hx : x ∈ Set.range j
  · obtain ⟨y, rfl⟩ := hx
    rw [Finsupp.mapDomain_apply_of_injective j.isEmbedding.injective,
      fundamentalPointCycle_apply, dite_eq_left (hE y), j.ker_stalk]
    have hlength : Module.length (P.presheaf.stalk (j y))
        ((P.presheaf.stalk (j y)) ⧸ RingHom.ker (j.stalkMap y).hom) =
        Module.length (E.presheaf.stalk y) (E.presheaf.stalk y) :=
      (Module.length_eq_of_surjective
        (Ideal.Quotient.mk_surjective (I := RingHom.ker (j.stalkMap y).hom))).trans
          (ringLength_eq_of_ringEquiv (stalkQuotientKerEquiv j y))
    rw [hlength]
    rfl
  · rw [Finsupp.mapDomain_of_notMem_range _ _ hx]
    have : Subsingleton ((P.presheaf.stalk x) ⧸ j.ker.stalk x) :=
      Ideal.Quotient.subsingleton_iff.mpr
          (_root_.AlgebraicGeometry.Scheme.Hom.closedImmersion_ker_stalk_eq_top j hx)
    simp only [Module.length_eq_zero, ENat.toNat_zero, Nat.cast_zero]

namespace FiniteFlatCurve

variable {k : Type u} [Field k]

/-- The actual closed endpoint morphism. -/
abbrev endpoint (a : k) : Spec (.of k) ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))

instance endpoint_isClosedImmersion (a : k) : IsClosedImmersion (endpoint a) :=
  IsClosedImmersion.spec_of_surjective _ (Polynomial.eval_surjective a)

/-- The endpoint's ideal on the entire affine line is its literal equation. -/
theorem endpoint_ideal (a : k) :
    (endpoint a).ker.ideal ⟨⊤, isAffineOpen_top _⟩ =
      (Ideal.span {Polynomial.X - Polynomial.C a}).map
        (Scheme.ΓSpecIso (.of k[X])).inv.hom := by
  rw [Scheme.Hom.ker_apply, ← Polynomial.ker_evalRingHom]
  change RingHom.ker (endpoint a).appTop.hom = _
  rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv]
  change RingHom.ker ((Scheme.ΓSpecIso (.of k)).hom.hom.comp (endpoint a).appTop.hom) = _
  rw [← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality]
  rw [CommRingCat.hom_comp, ← RingHom.comap_ker]
  exact (Ideal.map_symm (Scheme.ΓSpecIso (.of k[X])).commRingCatIsoToRingEquiv).symm

/-- The original endpoint equation in the actual affine-line stalk. -/
def endpointScalar (a : k) (x : Spec (.of k[X])) :
    (Spec (.of k[X])).presheaf.stalk x :=
  (Spec (.of k[X])).presheaf.germ ⊤ x trivial
    ((Scheme.ΓSpecIso (.of k[X])).inv (Polynomial.X - Polynomial.C a))

/-- The same singleton equation generates the endpoint ideal in each original stalk. -/
theorem endpoint_stalk (a : k) (x : Spec (.of k[X])) :
    (endpoint a).ker.stalk x = Ideal.ofList [endpointScalar a x] := by
  rw [Scheme.IdealSheafData.stalk_eq_map _ ⟨⊤, isAffineOpen_top _⟩ trivial,
    endpoint_ideal, Ideal.map_map, Ideal.map_span]
  simp [endpointScalar, Ideal.ofList]

/-- The affine stalk is a localization, so the original nonzero equation stays regular. -/
theorem endpointScalar_regular (a : k) (x : Spec (.of k[X])) :
    IsSMulRegular ((Spec (.of k[X])).presheaf.stalk x) (endpointScalar a x) := by
  let : Algebra k[X] ((Spec (.of k[X])).presheaf.stalk x) :=
    (StructureSheaf.toStalk k[X] x).hom.toAlgebra
  have : IsLocalization.AtPrime ((Spec (.of k[X])).presheaf.stalk x) x.asIdeal :=
    inferInstanceAs (IsLocalization.AtPrime ((Spec.structureSheaf k[X]).presheaf.stalk x)
      x.asIdeal)
  let : Module.Flat k[X] ((Spec (.of k[X])).presheaf.stalk x) :=
    IsLocalization.flat _ x.asIdeal.primeCompl
  exact (IsSMulRegular.of_ne_zero (M := k[X]) (Polynomial.X_sub_C_ne_zero a)).of_flat

variable {P : Scheme.{u}} (f : P ⟶ Spec (.of k[X])) (a : k)

/-- The full actual endpoint fiber. -/
abbrev fiber : Scheme.{u} := pullback (endpoint a) f

/-- The actual closed endpoint-fiber inclusion. -/
abbrev fiberInclusion : fiber f a ⟶ P := pullback.snd (endpoint a) f

/-- The original single endpoint equation in the ambient stalk. -/
def scalar (x : P) : P.presheaf.stalk x :=
  f.stalkMap x (endpointScalar a (f x))

/-- The full endpoint fiber has the literal singleton stalk ideal. -/
theorem fiberInclusion_stalk (x : P) :
    (fiberInclusion f a).ker.stalk x = Ideal.ofList [scalar f a x] := by
  have hker : (fiberInclusion f a).ker = (endpoint a).ker.comap f :=
    _root_.AlgebraicGeometry.Scheme.Hom.ker_eq_comap_of_isPullback _ _ _ _
        (IsPullback.of_hasPullback (endpoint a) f).flip
  rw [hker, Scheme.IdealSheafData.stalk_comap, endpoint_stalk, Ideal.map_ofList]
  rfl

/-- Flatness is used on the family, never on the closed endpoint map. -/
theorem scalar_regular [Flat f] (x : P) :
    IsSMulRegular (P.presheaf.stalk x) (scalar f a x) := by
  let := (f.stalkMap x).hom.toAlgebra
  have : Module.Flat ((Spec (.of k[X])).presheaf.stalk (f x)) (P.presheaf.stalk x) :=
    Flat.stalkMap f x
  exact (endpointScalar_regular a (f x)).of_flat

instance fiber_isNoetherian [IsNoetherian P] : IsNoetherian (fiber f a) :=
  isNoetherian_of_finiteType (fiberInclusion f a)

/-- All points of a finite scheme over the endpoint field are actual generic points. -/
theorem fiber_all_generic [IsFinite f] (x : fiber f a) : x ∈ genericPoints (fiber f a) := by
  apply _root_.AlgebraicGeometry.Scheme.Hom.mem_genericPoints_of_image_generic (pullback.fst
      (endpoint a) f) x
  have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using
    (Subsingleton.elim ((pullback.fst (endpoint a) f) x) (genericPoint (Spec (.of k))))

/-- At an actual fiber point the singleton cut is Artinian with its full multiplicity. -/
theorem scalar_cut_isArtinian [IsFinite f] [IsNoetherian P] (x : fiber f a) :
    IsArtinianRing ((P.presheaf.stalk (fiberInclusion f a x)) ⧸
      (Ideal.ofList [scalar f a (fiberInclusion f a x)] ⊔ ⊥)) := by
  rw [sup_bot_eq, ← fiberInclusion_stalk, Scheme.Hom.ker_stalk]
  exact stalk_quotient_ker_isArtinian (fiberInclusion f a) x (fiber_all_generic f a x)

/-- The endpoint scalar belongs to the actual maximal ideal at every fiber point. -/
theorem scalar_mem_maximalIdeal (x : fiber f a) :
    scalar f a (fiberInclusion f a x) ∈
      IsLocalRing.maximalIdeal (P.presheaf.stalk (fiberInclusion f a x)) := by
  have hle := IsLocalRing.le_maximalIdeal
    (RingHom.ker_ne_top ((fiberInclusion f a).stalkMap x).hom)
  rw [← Scheme.Hom.ker_stalk, fiberInclusion_stalk] at hle
  exact hle (Ideal.subset_span (by simp))

variable {E : Scheme.{u}} (j : E ⟶ P)

/-- The canonical map of actual fibers induced by a closed support inclusion. -/
def fiberMap : fiber (j ≫ f) a ⟶ fiber f a :=
  pullback.map _ _ _ _ (𝟙 _) j (𝟙 _) (by simp) (by simp)

@[reassoc (attr := simp)] theorem fiberMap_inclusion :
    fiberMap f a j ≫ fiberInclusion f a = fiberInclusion (j ≫ f) a ≫ j := by
  simp [fiberMap, fiberInclusion]

/-- The actual component fiber is Cartesian over its original support. -/
theorem fiberMap_isPullback :
    IsPullback (fiberMap f a j) (fiberInclusion (j ≫ f) a) (fiberInclusion f a) j := by
  apply IsPullback.of_right (t := IsPullback.of_hasPullback (endpoint a) f)
  · simpa [fiberMap] using IsPullback.of_hasPullback (endpoint a) (j ≫ f)
  · exact fiberMap_inclusion f a j

instance fiberMap_isClosedImmersion [IsClosedImmersion j] :
    IsClosedImmersion (fiberMap f a j) :=
  MorphismProperty.of_isPullback (fiberMap_isPullback f a j).flip
    (inferInstanceAs (IsClosedImmersion j))

/-- Intersection retains the sum of the two actual closed stalk ideals. -/
theorem fiberMap_composite_stalk [IsClosedImmersion j] (x : P) :
    (fiberMap f a j ≫ fiberInclusion f a).ker.stalk x =
      Ideal.ofList [scalar f a x] ⊔ j.ker.stalk x := by
  rw [_root_.AlgebraicGeometry.Scheme.Hom.ker_comp_eq_sup_of_isPullback _ _ _ _
      (fiberMap_isPullback f a j),
    Scheme.IdealSheafData.stalk_sup, fiberInclusion_stalk]

omit j in
/-- A fixed singleton Euler test specializes the original component sum into
the full actual fiber. The regularity premise concerns the original support
quotients; it will be derived from finite-flat curve geometry below. -/
theorem fundamentalCycle_specialization_of_quotient_regular
    [IsFinite f] [Flat f] [IsNoetherian P]
    (hregular : ∀ (z : genericPoints P) (x : P),
      IsSMulRegular ((P.presheaf.stalk x) ⧸
        (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι.ker.stalk x)
        (scalar f a x)) :
    let := IntegralCycle.genericPointFintype P
    fundamentalCycle (fiber f a) =
      ∑ z : genericPoints P, (genericMultiplicity z : ℤ) •
        IntegralCycle.finitePushforward
          (fiberMap f a (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι)
          (fundamentalCycle
            (fiber ((IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫ f) a)) := by
  classical
  let := IntegralCycle.genericPointFintype P
  apply IntegralCycle.finitePushforward_injective_of_isClosedImmersion (fiberInclusion f a)
  rw [map_sum]
  simp_rw [map_zsmul]
  have hcomp (z : genericPoints P) :
      IntegralCycle.finitePushforward (fiberInclusion f a)
          (IntegralCycle.finitePushforward
            (fiberMap f a (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι)
            (fundamentalCycle
              (fiber ((IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫ f) a))) =
        IntegralCycle.finitePushforward
          (fiberMap f a (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫
            fiberInclusion f a)
          (fundamentalCycle
            (fiber ((IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫ f) a)) := by
    rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]
  simp_rw [hcomp]
  apply IntegralCycle.toPoints_injective
  ext x
  simp only [map_sum, map_zsmul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    zsmul_eq_mul, Int.cast_id]
  rw [closedImmersion_fundamentalCoefficient_eq_length_of_all_generic
    (fiberInclusion f a) (fiber_all_generic f a)]
  have hcoeff (z : genericPoints P) :
      IntegralCycle.toPoints (IntegralCycle.finitePushforward
          (fiberMap f a (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫
            fiberInclusion f a)
          (fundamentalCycle
            (fiber ((IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫ f) a))) x =
        ((Module.length (P.presheaf.stalk x)
          ((P.presheaf.stalk x) ⧸ (Ideal.ofList [scalar f a x] ⊔
            (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι.ker.stalk x))).toNat :
              ℤ) := by
    rw [closedImmersion_fundamentalCoefficient_eq_length_of_all_generic _
      (fiber_all_generic ((IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫ f) a),
      fiberMap_composite_stalk]
  simp_rw [hcoeff]
  by_cases hx : x ∈ Set.range (fiberInclusion f a)
  · obtain ⟨y, rfl⟩ := hx
    let := scalar_cut_isArtinian f a y
    have hEuler := chainEuler_eq_sum_of_fundamentalCycle_eq
      (fun z : genericPoints P => (IntegralClosedSubscheme.pointClosure z.1).val.subscheme)
      (fun z : genericPoints P => (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι)
      (fun z : genericPoints P => (genericMultiplicity z : ℤ))
      (fundamentalCycle_eq_sum_closed_components P)
      (fiberInclusion f a y) [scalar f a (fiberInclusion f a y)]
      (by intro r hr; simpa only [List.mem_singleton.mp hr] using scalar_mem_maximalIdeal f a y)
    rw [_root_.ChainComplex.Koszul.singleton_chainEuler_eq_ring_quotient_length
      _ (scalar_regular f a _)] at hEuler
    simp_rw [_root_.ChainComplex.Koszul.singleton_chainEuler_eq_quotient_length
      _ _ (hregular _ _)] at hEuler
    rw [fiberInclusion_stalk f a (fiberInclusion f a y)]
    exact hEuler
  · have htop := _root_.AlgebraicGeometry.Scheme.Hom.closedImmersion_ker_stalk_eq_top
      (fiberInclusion f a) hx
    have hscalar : Ideal.ofList [scalar f a x] = ⊤ :=
      (fiberInclusion_stalk f a x).symm.trans htop
    have : Subsingleton ((P.presheaf.stalk x) ⧸ (⊤ : Ideal (P.presheaf.stalk x))) :=
      Ideal.Quotient.subsingleton_iff.mpr rfl
    trans 0
    · rw [htop]
      simp only [Module.length_eq_zero, ENat.toNat_zero, Nat.cast_zero]
    · symm
      apply Finset.sum_eq_zero
      intro z _
      rw [hscalar, top_sup_eq]
      simp only [Module.length_eq_zero, ENat.toNat_zero, Nat.cast_zero, mul_zero]

end FiniteFlatCurve

/-- The full fundamental cycle of a finite-flat curve fiber is the sum of the
full fibers of its original reduced components, weighted by the original
generic local lengths. The endpoint morphism is not assumed flat. -/
theorem finiteFlatCurve_fundamentalCycle_specialization
    {k : Type u} [Field k] {P : Scheme.{u}}
    (f : P ⟶ Spec (.of k[X])) [IsFinite f] [Flat f] [IsNoetherian P] (a : k) :
    let := IntegralCycle.genericPointFintype P
    fundamentalCycle (FiniteFlatCurve.fiber f a) =
      ∑ z : genericPoints P, (genericMultiplicity z : ℤ) •
        IntegralCycle.finitePushforward
          (FiniteFlatCurve.fiberMap f a (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι)
          (fundamentalCycle (FiniteFlatCurve.fiber
            ((IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫ f) a)) := by
  apply FiniteFlatCurve.fundamentalCycle_specialization_of_quotient_regular f a
  intro z x
  let j := (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι
  have : Flat (j ≫ f) := _root_.AlgebraicGeometry.Scheme.Hom.finiteFlatCurve_component_flat f z
  change IsSMulRegular ((P.presheaf.stalk x) ⧸ j.ker.stalk x) (FiniteFlatCurve.scalar f a x)
  by_cases hx : x ∈ Set.range j
  · obtain ⟨c, rfl⟩ := hx
    exact closedImmersion_polynomial_fiber_isSMulRegular f j a c
  · have : Subsingleton ((P.presheaf.stalk x) ⧸ j.ker.stalk x) :=
      Ideal.Quotient.subsingleton_iff.mpr
          (_root_.AlgebraicGeometry.Scheme.Hom.closedImmersion_ker_stalk_eq_top j hx)
    exact fun _ _ _ => Subsingleton.elim _ _

end AlgebraicGeometry
