/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.FinitePoint.Equality
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.FiniteFlat.IntegralCartierBalance
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.QuasiFinite.GenericFiber


/-!
# Original finite-image endpoint length balance

At an actual generic point of the whole generator endpoint, the target cut is
Artinian and the scalar is nonzero by component dominance. The original finite
support-to-image map then gives the complete residue-weighted local length sum.
This does not assert that every source endpoint component maps generically.
-/

open _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
  (rightSupport_endpointScalar_regular)

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve
open _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
open scoped BigOperators

universe u

namespace Motivic.RelativeEndpointDiagram

variable {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k)))

local instance : IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)

/-- A genuine finite dominant map to an original generator has the full
Cartier length balance at each generic point of its actual endpoint. The
Artinian quotient and scalar regularity are proved, not supplied. -/
theorem generator_endpoint_original_length_balance
    (G : FiniteCorrespondenceGenerator
        (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineHom X.hom)
        Y.hom)
    {C : Scheme.{u}} [IsIntegral C] (j : C ⟶ G.scheme)
    [IsFinite j] [IsDominant j] (a : k)
    (y : fiber (G.inclusion ≫
        _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter X.hom
        Y.hom) a)
    (hy : y ∈ genericPoints (fiber (G.inclusion ≫
        _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter X.hom
        Y.hom) a)) :
    (∑ᶠ x : {x : C // j x = fiberInclusion
        (G.inclusion ≫
            _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter X.hom
            Y.hom) a y},
      (j.residueDegree x.1 : ℤ) *
        ((Module.length (C.presheaf.stalk x.1)
          ((C.presheaf.stalk x.1) ⧸ Ideal.ofList
            [scalar (j ≫ G.inclusion ≫
                _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter
                X.hom Y.hom) a x.1])).toNat : ℤ)) =
      (j.residueDegree (genericPoint C) : ℤ) *
        ((Module.length ((fiber (G.inclusion ≫
            _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter X.hom
            Y.hom) a).presheaf.stalk y)
          ((fiber (G.inclusion ≫
              _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter
              X.hom Y.hom) a).presheaf.stalk y)).toNat :
          ℤ) := by
  let : IsNoetherian (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLine
      X.hom) :=
    inferInstanceAs (IsNoetherian
        (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X).left)
  let : IsNoetherian G.scheme := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType
      G.projection
  let f := G.inclusion ≫
      _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter X.hom Y.hom
  let z := fiberInclusion f a y
  have hcut : IsArtinianRing ((G.scheme.presheaf.stalk z) ⧸
      Ideal.ofList [scalar f a z]) := by
    rw [← fiberInclusion_stalk, Scheme.Hom.ker_stalk]
    exact _root_.AlgebraicGeometry.Scheme.stalk_quotient_ker_isArtinian (fiberInclusion f a) y hy
  let := hcut
  have hz : scalar f a z ≠ 0 := by
    intro hz
    have hr := rightSupport_endpointScalar_regular X Y a G z
    have he : (1 : G.scheme.presheaf.stalk z) = 0 := hr (by simp [f, hz])
    exact one_ne_zero he
  obtain ⟨U, hU, p, hp⟩ := _root_.AlgebraicGeometry.Scheme.Hom.FiniteAffineChart.exists_targetChart
      z
  let : Nonempty U := ⟨⟨hU.fromSpec p, by
    change hU.fromSpec p ∈ (U : Set G.scheme)
    rw [← hU.range_fromSpec]
    exact ⟨p, rfl⟩⟩⟩
  have : IsArtinianRing ((G.scheme.presheaf.stalk (hU.fromSpec p)) ⧸
      Ideal.ofList [scalar f a (hU.fromSpec p)]) := by
    rw [hp]
    exact hcut
  have hm : scalar f a (hU.fromSpec p) ∈
      IsLocalRing.maximalIdeal (G.scheme.presheaf.stalk (hU.fromSpec p)) := by
    rw [hp]
    exact scalar_mem_maximalIdeal f a y
  have h := originalCartierLength_sum_of_integral f a j hU p (by rw [hp]; exact hz) hm
  rw [hp, ← fiber_stalk_length] at h
  exact h

end Motivic.RelativeEndpointDiagram

namespace Motivic.FinitePointCycleCorrespondence

variable {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k)))
  {C V : Scheme.{u}} (q : C ⟶
      _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLine X.hom) (j : V ⟶
      C) [IsOpenImmersion j]
  (c : _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle C)
  (hretained : ∀ x : c.support,
    Set.range (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
        x.val).val.subschemeι ⊆ Set.range j)
  (hfinite : ∀ x : c.support,
    IsFinite ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
        x.val).val.subschemeι ≫ q))
  (hdominant : ∀ x : c.support,
    Set.range ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
        x.val).val.subschemeι ≫ q) ∈
      irreducibleComponents
          (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLine X.hom))
  (g : V ⟶ Y.left) (hbase : j ≫ q ≫
      _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineHom X.hom = g ≫
      Y.hom)

/-- The actual point-cycle support-to-image factorization satisfies the native
endpoint balance, retaining the original product-map generic degree. -/
theorem original_support_endpoint_length_balance (x : c.support) (a : k) :
    let e := productMap (X :=
        _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X) (Y :=
        Y) q j c hretained g hbase x
    let G := generator (X :=
        _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X) (Y :=
        Y)
      q j c hretained hfinite hdominant g hbase x
    let f := G.inclusion ≫
        _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter X.hom
        Y.hom
    ∀ (y : fiber f a), y ∈ genericPoints (fiber f a) →
      (∑ᶠ z : {z : supportScheme c x // e.toImage z = fiberInclusion f a y},
        (e.toImage.residueDegree z.1 : ℤ) *
          ((Module.length ((supportScheme c x).presheaf.stalk z.1)
            (((supportScheme c x).presheaf.stalk z.1) ⧸
              Ideal.ofList [scalar (e.toImage ≫ f) a z.1])).toNat : ℤ)) =
        (e.residueDegree (genericPoint (supportScheme c x)) : ℤ) *
          ((Module.length ((fiber f a).presheaf.stalk y)
            ((fiber f a).presheaf.stalk y)).toNat : ℤ) := by
  dsimp only
  let e := productMap (X :=
      _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X) (Y := Y)
      q j c hretained g hbase x
  let G := generator (X :=
      _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X) (Y := Y)
      q j c hretained hfinite hdominant g hbase x
  let : IsFinite e := productMap_isFinite (X :=
      _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X) (Y := Y)
    q j c hretained hfinite g hbase x
  let : IsFinite e.toImage := _root_.AlgebraicGeometry.Scheme.Hom.isFinite_toImage e
  intro y hy
  have h :=
    _root_.Motivic.RelativeEndpointDiagram.generator_endpoint_original_length_balance
      X Y G e.toImage a y hy
  have hd : e.toImage.residueDegree (genericPoint (supportScheme c x)) =
      e.residueDegree (genericPoint (supportScheme c x)) := by
    have he := _root_.AlgebraicGeometry.Scheme.Hom.residueDegree_comp e.toImage e.imageι
        (genericPoint (supportScheme c x))
    simpa only [Scheme.Hom.toImage_imageι,
        _root_.AlgebraicGeometry.Scheme.Hom.residueDegree_of_surjectiveOnStalks,
      one_mul, mul_one] using he.symm
  rw [hd] at h
  convert h using 1

end Motivic.FinitePointCycleCorrespondence
