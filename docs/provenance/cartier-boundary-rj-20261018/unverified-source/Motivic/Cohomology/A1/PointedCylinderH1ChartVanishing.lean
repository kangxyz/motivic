/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.ContractionBoundaryProjectionExcision
public import Motivic.Cohomology.A1.DenseOpenRestrictionMono
public import Motivic.Cohomology.A1.PointedCylinderLocalEffacement
public import Motivic.AlgebraicGeometry.SmoothSiteContractionDensity
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleOriginalMapRecognition
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleOrdinaryEdgeWindow
public import Motivic.Cohomology.SheafCohomologyLocalTriviality

/-! # The degree-one localization sequence on an actual pointed base chart

The actual model/chart projection supplies a quotient lift after a marked BASE
refinement. The existing image-sieve localization-sequence theorem kills the
original ordinary class on the whole homotopy cylinder. Its comparison with
the unchanged original cylinder germ is the existing natural comparison.

Only the genuine canonical contraction-to-boundary Epi inputs remain here.
Coefficient restriction Mono is proved from the actual dense puncture.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite

variable {k : Type u} [Field k] [Infinite k]
  (X : SmoothSite (Spec (.of k))) {E U : SmoothSite (Spec (.of k))}
  (b : E ⟶ SmoothSite.a1Cylinder (.of k) X) [Etale b.left]
  (F : SheafWithTransfers.{u + 1} k)
  (j : U ⟶ E) [IsOpenImmersion j.left]
  (q : U ⟶ SmoothSite.torusCylinder (.of k) X)
  (hpb : IsPullback q j (SmoothSite.contractionOpen (.of k) X) b)
  (hF : F.obj.IsA1Invariant)
  (hE₀ : Epi (contractionToBoundary X F hF))
  (hE₁ : Epi (contractionToBoundary (SmoothSite.a1Cylinder (.of k) X) F hF))

local notation "G" => (SheafWithTransfers.toSheaf k).obj F
local notation "E₁" => SmoothSite.a1Cylinder (.of k) E
local notation "U₁" => SmoothSite.a1Cylinder (.of k) U
local notation "πE" => SmoothSite.a1Projection (.of k) E
local notation "j₁" => SmoothSite.a1Map (.of k) j

include hpb hF in
/-- The coefficient restriction in the actual product-chart localization
sequence is monic by dense-open detection. It is not an additional premise. -/
theorem chartProduct_restrictionToDirectImage_mono :
    Mono (restrictionToDirectImage G j₁) := by
  let b₁ := SmoothSite.contractionChartProduct (.of k) X b
  let q₁ := SmoothSite.contractionChartPunctureProduct (.of k) X q
  have hpb₁ := SmoothSite.contractionChartPunctureProduct_isPullback
    (.of k) X b j q hpb
  let : IsOpenImmersion (j₁).left :=
    MorphismProperty.of_isPullback
      ((SmoothSite.forgetScheme (Spec (.of k))).map_isPullback hpb₁).flip inferInstance
  exact restrictionToDirectImage_mono_of_dense j₁ F hF
    (SmoothSite.contractionChartOpen_denseRange (.of k)
      (SmoothSite.a1Cylinder (.of k) X) b₁ j₁ q₁ hpb₁)

local instance (S : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

include hpb hF hE₀ hE₁ in
/-- A class in the kernel of the actual coefficient map is killed by a
full-marked BASE refinement. The proof uses the original short exact sequence,
its actual Ext connecting class and a genuine image-sieve witness. -/
theorem exists_pointed_chart_H1_coefficient_kernel_restriction_zero
    (Φ : (nisnevichTopology E.left).Point.{u + 1}) (V : Φ.fiber.Elements)
    (x : SheafCohomology.H.{u + 1, u + 1, u, u + 1} (nisnevichTopology (E₁).left)
      ((restrict E₁ AddCommGrpCat).obj G) 1 ((baseChange (πE).left).obj V.obj))
    (hx : x.comp (Ext.mk₀ (restrictionToDirectImage G j₁)) (add_zero 1) = 0) :
    ∃ (W : Φ.fiber.Elements) (a : W ⟶ V),
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (nisnevichTopology (E₁).left) ((restrict E₁ AddCommGrpCat).obj G) 1).map
          ((baseChange (πE).left).map a.hom).op x = 0 := by
  let J := nisnevichTopology (E₁).left
  let r := restrictionToDirectImage G j₁
  let := chartProduct_restrictionToDirectImage_mono X b F j q hpb hF
  let S := ShortComplex.mk r (cokernel.π r) (cokernel.condition r)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
  let V₁ := (baseChange (πE).left).obj V.obj
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
    (Hypercohomology.freeAbelianSheaf J V₁) hS x hx rfl
  let c₁ := SheafCohomology.zeroSections J S.X₃ V₁ y
  obtain ⟨W, a, w, t, ha, ht⟩ :=
    exists_pointed_a1_product_quotient_lift_of_chart
      X b F j q hpb hF hE₀ hE₁ Φ V.obj V.val c₁
  let M : Φ.fiber.Elements := Functor.elementsMk _ W w
  let f : M ⟶ V := Functor.Elements.homMk a ha
  refine ⟨M, f, ?_⟩
  have hz := SheafCohomology.boundary_restriction_eq_zero_of_imageSieve J hS y
    ((baseChange (πE).left).map a)
    ⟨(a1PuncturedProjectionMap j G).hom.app (op W) t, ht⟩
  rwa [hy] at hz

variable [HasExt.{u + 1}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

include hpb hF hE₀ hE₁ in
/-- The actual chart localization sequence kills the original cylinder germ
in degree one. The supplied class equation is the kernel of the literal
coefficient restriction, not an assumed cohomological puncture Mono. -/
theorem pointedCylinder_H1_germ_zero_of_chart_coefficient_kernel
    (Φ : (nisnevichTopology E.left).Point.{u + 1}) (V : Φ.fiber.Elements)
    (s : (pointedCylinderValues (.of k) Φ
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) G 1)
      (pointedBase (.of k) Φ)).obj (op V))
    (hs : ((pointedCylinderOrdinaryIso (.of k) E Φ G 1).hom.app (op V) s).comp
      (Ext.mk₀ (restrictionToDirectImage G j₁)) (add_zero 1) = 0) :
    colimit.ι (pointedCylinderValues (.of k) Φ
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) G 1)
      (pointedBase (.of k) Φ)) (op V) s = 0 := by
  obtain ⟨W, a, ha⟩ := exists_pointed_chart_H1_coefficient_kernel_restriction_zero
    X b F j q hpb hF hE₀ hE₁ Φ V
      ((pointedCylinderOrdinaryIso (.of k) E Φ G 1).hom.app (op V) s) hs
  exact pointedCylinder_germ_eq_zero_of_ordinary_base_refinement
    (.of k) E Φ G 1 a s ha

include hpb hF hE₀ hE₁ in
/-- In degree one the genuine open-image edge is injective without any positive
higher-image premise. The actual geometric puncture triangle therefore turns
an original puncture-zero representative into the coefficient kernel used by
the localization sequence. -/
theorem pointedCylinder_H1_germ_zero_of_chart_puncture_restriction_zero
    (Φ : (nisnevichTopology E.left).Point.{u + 1}) (V : Φ.fiber.Elements)
    (s : (pointedCylinderValues (.of k) Φ
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) G 1)
      (pointedBase (.of k) Φ)).obj (op V))
    (hs : (pointedCylinderRestriction (.of k) j Φ
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) G 1)).app (op V) s = 0) :
    colimit.ι (pointedCylinderValues (.of k) Φ
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) G 1)
      (pointedBase (.of k) Φ)) (op V) s = 0 := by
  let P := SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k))) G 1
  let V₁ := (baseChange (πE).left).obj V.obj
  let t := P.map (a1BaseChangeIso (.of k) E V.obj).hom.op s
  have ht : P.map ((restrictionProjection j₁).app V₁).op t = 0 := by
    change P.map ((restrictionProjection j₁).app V₁).op
      (P.map (a1BaseChangeIso (.of k) E V.obj).hom.op s) = 0
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      a1PunctureProjectionBaseChangeIso_restriction]
    change P.map (SmoothSite.a1Map (.of k) ((restrictionProjection j).app V.obj)).op s = 0
      at hs
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hs, map_zero]
  let x := cohomologyRestrictionEquiv E₁ G 1 V₁ t
  have hx : x.comp (Ext.mk₀ (restrictionToDirectImage G j₁)) (add_zero 1) = 0 := by
    apply ordinaryEdgeMap_injective_of_rightDerived_window (j₁).left V₁
      ((restrict U₁ AddCommGrpCat).obj G) 1 (by intro n hn hlt; omega)
    rw [map_zero]
    have he := ordinaryEdgeMap_restrictionToDirectImage j₁ G 1 V₁ t
    simpa only [ht, map_zero] using he
  apply pointedCylinder_H1_germ_zero_of_chart_coefficient_kernel
    X b F j q hpb hF hE₀ hE₁ Φ V s
  exact hx

include hpb hF hE₀ hE₁ in
/-- The original degree-one cylinder-to-puncture map is monic on every actual
point of a displayed etale contraction chart. The only unproved mathematical
inputs here are the two genuine canonical boundary epimorphisms. -/
theorem pointedCylinderRestriction_H1_colimit_mono_of_chart
    (Φ : (nisnevichTopology E.left).Point.{u + 1}) :
    Mono (colim.map (pointedCylinderRestriction (.of k) j Φ
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) G 1))) := by
  let P := SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k))) G 1
  let D := pointedCylinderValues (.of k) Φ P (pointedBase (.of k) Φ)
  let T := pointedCylinderValues (.of k) Φ P (pointedPuncture (.of k) j Φ)
  let r := pointedCylinderRestriction (.of k) j Φ P
  apply (AddCommGrpCat.mono_iff_injective _).mpr
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨V, v, s, rfl⟩ := Φ.toPresheafFiber_jointly_surjective
    (P := (toSmoothSite E ⋙ SmoothSite.parameterProduct (SmoothSite.affineLine (.of k))).op ⋙ P) z
  let N : Φ.fiber.Elements := Functor.elementsMk _ V v
  have he : colimit.ι T (op N) (r.app (op N) s) = colimit.ι T (op N) 0 := by
    rw [map_zero]
    have h := ConcreteCategory.congr_hom (colimit.ι_map r (op N)) s
    exact h.symm.trans hz
  obtain ⟨W, a, ha⟩ := ((colimit.isColimit T).eq_iff' (r.app (op N) s) 0).mp he
  have hlocal : r.app W (D.map a s) = 0 := by
    rw [NatTrans.naturality_apply]
    simpa only [map_zero] using ha
  have hzero := pointedCylinder_H1_germ_zero_of_chart_puncture_restriction_zero
    X b F j q hpb hF hE₀ hE₁ Φ W.unop (D.map a s) hlocal
  have hw := ConcreteCategory.congr_hom (colimit.w D a) s
  exact hw.symm.trans hzero

end Motivic.FiniteEtaleSite
