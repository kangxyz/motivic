/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.AlgebraicGeometry.Correspondences.OneSidedMovingEndpoints
public import Motivic.Aglib.AlgebraicGeometry.Moving.OneSidedRetainedFactors
/-! # Actual Serre sections give the one-sided moving correspondence

The family targets the original larger X. Only its two moving endpoint divisors
factor through V. In particular X is never replaced by V near the diagonal.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible Scheme.Moving
open Scheme.Modules.Invertible.PolynomialBoundaryPencil
open Motivic.SignedProductPencilEndpoints
universe u
namespace Motivic.OneSidedMovingEndpoints

/-- Both desired correspondences are constructed from the actual Serre sections.
No endpoint, correspondence, support lift, or family-finiteness premise is added. -/
theorem exists_moving_endpoints_of_sections {k : Type u} [Field k]
    {S X V : SmoothSite (Spec (.of k))} [IsAffine S.left]
    {C D G B W : Scheme.{u}} (q : C ⟶ S.left) [IsProper q]
    (z : B ⟶ C) (i : W ⟶ B)
    (j : D ⟶ C) [IsOpenImmersion j] [D.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    [Smooth ((j ≫ q) ≫ S.hom)] [IsSeparated ((j ≫ q) ≫ S.hom)]
    [QuasiCompact ((j ≫ q) ≫ S.hom)]
    (w : G ⟶ D) [IsOpenImmersion w]
    (hcover : ∀ x : C, x ∈ Set.range j ∨ x ∈ Set.range z)
    (δ : S.left ⟶ C) [IsClosedImmersion δ] (γ : S.left ⟶ D)
    (hγ : γ ≫ j = δ) (hγq : γ ≫ (j ≫ q) = 𝟙 _)
    (hI : IsLocallyRankOne C (Scheme.Hom.idealModule δ)) (T : LineBundle C)
    (E : (Scheme.Modules.pullback z).obj
      (dualLineBundle C ⟨Scheme.Hom.idealModule δ, hI⟩).val ≅
        SheafOfModules.unit B.ringCatSheaf)
    (s : OneSidedSections S.hom q z i j (w ≫ j) ⟨Scheme.Hom.idealModule δ, hI⟩ T
      (Scheme.Hom.idealInclusion δ) E)
    (g : D ⟶ X.left) (gV : G ⟶ V.left) (v : V ⟶ X) [IsOpenImmersion v.left]
    (hv : w ≫ g = gV ≫ v.left)
    (φ : S ⟶ X) (hγg : γ ≫ g = φ.left)
    (hbase : (j ≫ q) ≫ S.hom = g ≫ X.hom) :
    HasMovingEndpoints φ v := by
  let I : LineBundle C := ⟨Scheme.Hom.idealModule δ, hI⟩
  let A := tensorLineBundle C T (dualLineBundle C I)
  let J : LineBundle D := ⟨Scheme.Hom.idealModule γ, openGraph_locallyRankOne j δ γ hγ hI⟩
  let M := pullbackLineBundle j (dualLineBundle C T)
  let e := openGraphPencilLineIso j δ γ hγ hI T
  let b := Hom.pullbackToUnit (sectionDualFunctional C T s.denominator) j
  let a0 := Hom.pullbackToUnit (sectionDualFunctional C A s.numerator) j
  let a := e.hom ≫ a0
  have : IsClosedImmersion γ := MorphismProperty.of_isPullback
    (openGraph_isPullback j δ γ hγ) inferInstance
  have : IsAffine ((𝟭 Scheme).obj S.left) := inferInstanceAs (IsAffine S.left)
  have hb := s.denominator_on_target S.hom q z i j (w ≫ j) I T
    (Scheme.Hom.idealInclusion δ) E hcover
  have hbfin : IsFinite (Hom.zeroInclusion b ≫ (j ≫ q)) := hb.2.2.2.1
  have hbmono : Mono b := hb.2.2.2.2.1
  have hbflat : Flat (Hom.zeroInclusion b ≫ (j ≫ q)) := hb.2.2.2.2.2
  have hf := s.graph_family_finite_flat S.hom q z i j (w ≫ j) δ γ hγ hI T E
  let := hf.1
  let := hf.2
  have hs := s.retained_supports S.hom q z i j w I T
    (Scheme.Hom.idealInclusion δ) E e
  have haW : Set.range (Hom.zeroInclusion a) ⊆ Set.range w := hs.1
  have hbW : Set.range (Hom.zeroInclusion b) ⊆ Set.range w := hs.2
  have lift_range {Z : Scheme.{u}} (u : Z ⟶ D)
      (hu : Set.range u ⊆ Set.range w) : Set.range (u ≫ g) ⊆ Set.range v.left := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hu ⟨x, rfl⟩
    refine ⟨gV y, ?_⟩
    change v.left (gV y) = g (u x)
    rw [← hy]
    exact (congrArg (fun f => f y) hv).symm
  exact exists_moving_endpoints (j ≫ q) γ hγq J.property M b a g φ hγg hbase v
    (lift_range _ haW) (lift_range _ hbW)

end Motivic.OneSidedMovingEndpoints
