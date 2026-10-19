/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Boundary.Contraction.Inputs
public import Motivic.Cohomology.A1.Boundary.Contraction.ProjectionExcision
public import Motivic.Cohomology.A1.LocalVanishing.Cylinder.LocalEffacement
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Cartier.ContractionDensity
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Original.MapRecognition
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Ordinary.EdgeWindow
public import Motivic.Aglib.CategoryTheory.Sites.SheafCohomology.Large.LocalTriviality
public import Motivic.Cohomology.A1.LocalVanishing.Cylinder.EtaleRestriction
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Cartier.CylinderComparison
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Cartier.PunctureComparison
public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Lifting.DistinguishedSquare

/-! # Full-marked H1 restriction from original coefficient inputs

Only original integral-affine local zero and the exact boundary Epi maps are
assumed. The degree-one edge window is empty. The construction reuses the
original quotient-lift and full-mark transport; no H1 HI or finite-field
producer is asserted here.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite.CoefficientInputs
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.CategoryTheory.Sheaf

variable {k : Type u} [Field k]
  (hD : PresheafWithTransfers.IntegralAffineLocalZero k)
  (X : SmoothSite (Spec (.of k))) {E U : SmoothSite (Spec (.of k))}
  (b : E ⟶ SmoothSite.a1Cylinder (.of k) X) [Etale b.left]
  (F : SheafWithTransfers.{u + 1} k)
  (j : U ⟶ E) [IsOpenImmersion j.left]
  (q : U ⟶ SmoothSite.torusCylinder (.of k) X)
  (hpb : IsPullback q j (SmoothSite.contractionOpen (.of k) X) b)
  (hF : F.obj.IsA1Invariant)
  (hE₀ : Epi (contractionToBoundary X F hF))
  (hE₁ : Epi (contractionToBoundary (SmoothSite.a1Cylinder (.of k) X) F hF))

local notation "G" => Functor.obj (SheafWithTransfers.toSheaf k) F
local notation "E₁" => SmoothSite.a1Cylinder (CommRingCat.of k) E
local notation "U₁" => SmoothSite.a1Cylinder (CommRingCat.of k) U
local notation "πE" => SmoothSite.a1Projection (CommRingCat.of k) E
local notation "j₁" => SmoothSite.a1Map (CommRingCat.of k) j

include hD hpb hF in
omit [IsOpenImmersion j.left] in
/-- The actual product-chart coefficient restriction is monic from the
original integral-affine local-zero input. -/
theorem chartProduct_restrictionToDirectImage_mono :
    Mono (restrictionToDirectImage G j₁) := by
  let b₁ := SmoothSite.contractionChartProduct (.of k) X b
  let q₁ := SmoothSite.contractionChartPunctureProduct (.of k) X q
  have hpb₁ := SmoothSite.contractionChartPunctureProduct_isPullback
    (.of k) X b j q hpb
  let : IsOpenImmersion (j₁).left :=
    MorphismProperty.of_isPullback
      ((SmoothSite.forgetScheme (Spec (.of k))).map_isPullback hpb₁)
      (inferInstanceAs (IsOpenImmersion (SmoothSite.contractionOpen (.of k)
        (SmoothSite.a1Cylinder (.of k) X)).left))
  exact restrictionToDirectImage_mono_of_dense_of_integralAffineLocalZero hD j₁ F hF
    (SmoothSite.contractionChartOpen_denseRange (.of k)
      (SmoothSite.a1Cylinder (.of k) X) b₁ j₁ q₁ hpb₁)

local instance (S : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

include hD hpb hF hE₀ hE₁ in
/-- A class in the kernel of the actual coefficient map is killed by a
full-marked BASE refinement. The proof uses the original short exact sequence,
its actual Ext connecting class and a genuine image-sieve witness. -/
theorem exists_pointed_chart_H1_coefficient_kernel_restriction_zero
    (Φ : (nisnevichTopology E.left).Point.{u + 1}) (V : Φ.fiber.Elements)
    (x : LargeCohomology.H.{u + 1, u + 1, u, u + 1} (nisnevichTopology (E₁).left)
      ((restrict E₁ AddCommGrpCat).obj G) 1 ((baseChange (πE).left).obj V.obj))
    (hx : x.comp (Ext.mk₀ (restrictionToDirectImage G j₁)) (add_zero 1) = 0) :
    ∃ (W : Φ.fiber.Elements) (a : W ⟶ V),
      (LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (nisnevichTopology (E₁).left) ((restrict E₁ AddCommGrpCat).obj G) 1).map
          ((baseChange (πE).left).map a.hom).op x = 0 := by
  let J := nisnevichTopology (E₁).left
  let r := restrictionToDirectImage G j₁
  let := chartProduct_restrictionToDirectImage_mono hD X b F j q hpb hF
  let S := ShortComplex.mk r (cokernel.π r) (cokernel.condition r)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
  let V₁ := (baseChange (πE).left).obj V.obj
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
    (Hypercohomology.freeAbelianSheaf J V₁) hS x hx rfl
  let c₁ := LargeCohomology.zeroSections J S.X₃ V₁ y
  obtain ⟨W, a, w, t, ha, ht⟩ :=
    exists_pointed_a1_product_quotient_lift_of_chart
      X b F j q hpb hF hE₀ hE₁ Φ V.obj V.val c₁
  let M : Φ.fiber.Elements := Functor.elementsMk _ W w
  let f : M ⟶ V := Functor.Elements.homMk a ha
  refine ⟨M, f, ?_⟩
  have hz := LargeCohomology.boundary_restriction_eq_zero_of_imageSieve J hS y
    ((baseChange (πE).left).map a)
    ⟨(a1PuncturedProjectionMap j G).hom.app (op W) t, ht⟩
  rwa [hy] at hz

variable [HasExt.{u + 1}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

include hD hpb hF hE₀ hE₁ in
/-- The actual chart localization sequence kills the original cylinder germ
in degree one. The supplied class equation is the kernel of the literal
coefficient restriction, not an assumed cohomological puncture Mono. -/
theorem pointedCylinder_H1_germ_zero_of_chart_coefficient_kernel
    (Φ : (nisnevichTopology E.left).Point.{u + 1}) (V : Φ.fiber.Elements)
    (s : (pointedCylinderValues (.of k) Φ
      (LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) G 1)
      (pointedBase (.of k) Φ)).obj (op V))
    (hs : ((pointedCylinderOrdinaryIso (.of k) E Φ G 1).hom.app (op V) s).comp
      (Ext.mk₀ (restrictionToDirectImage G j₁)) (add_zero 1) = 0) :
    colimit.ι (pointedCylinderValues (.of k) Φ
      (LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) G 1)
      (pointedBase (.of k) Φ)) (op V) s = 0 := by
  obtain ⟨W, a, ha⟩ := exists_pointed_chart_H1_coefficient_kernel_restriction_zero
    hD X b F j q hpb hF hE₀ hE₁ Φ V
      ((pointedCylinderOrdinaryIso (.of k) E Φ G 1).hom.app (op V) s) hs
  exact pointedCylinder_germ_eq_zero_of_ordinary_base_refinement
    (.of k) E Φ G 1 a s ha

include hD hpb hF hE₀ hE₁ in
/-- In degree one the genuine open-image edge is injective without any positive
higher-image premise. The actual geometric puncture triangle therefore turns
an original puncture-zero representative into the coefficient kernel used by
the localization sequence. -/
theorem pointedCylinder_H1_germ_zero_of_chart_puncture_restriction_zero
    (Φ : (nisnevichTopology E.left).Point.{u + 1}) (V : Φ.fiber.Elements)
    (s : (pointedCylinderValues (.of k) Φ
      (LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) G 1)
      (pointedBase (.of k) Φ)).obj (op V))
    (hs : (pointedCylinderRestriction (.of k) j Φ
      (LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) G 1)).app (op V) s = 0) :
    colimit.ι (pointedCylinderValues (.of k) Φ
      (LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) G 1)
      (pointedBase (.of k) Φ)) (op V) s = 0 := by
  let P := LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
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
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    erw [hs]
    simp only [map_zero]
  let x := cohomologyRestrictionEquiv E₁ G 1 V₁ t
  have hx : x.comp (Ext.mk₀ (restrictionToDirectImage G j₁)) (add_zero 1) = 0 := by
    apply ordinaryEdgeMap_injective_of_rightDerived_window (j₁).left V₁
      ((restrict U₁ AddCommGrpCat).obj G) 1 (by intro n hn hlt; omega)
    rw [map_zero]
    have he := ordinaryEdgeMap_restrictionToDirectImage j₁ G 1 V₁ t
    change ordinaryEdgeMap (j₁).left V₁ ((restrict U₁ AddCommGrpCat).obj G) 1
        (x.comp (Ext.mk₀ (restrictionToDirectImage G j₁)) (add_zero 1)) =
      cohomologyRestrictionEquiv U₁ G 1 ((baseChange (j₁).left).obj V₁)
        (P.map ((restrictionProjection j₁).app V₁).op t) at he
    rw [ht, map_zero] at he
    exact he
  apply pointedCylinder_H1_germ_zero_of_chart_coefficient_kernel
    hD X b F j q hpb hF hE₀ hE₁ Φ V s
  exact hx

include hD hpb hF hE₀ hE₁ in
/-- The original degree-one cylinder-to-puncture map is monic on every actual
point of a displayed etale contraction chart. The original local-zero input and
two genuine canonical boundary epimorphisms remain explicit mathematical inputs. -/
theorem pointedCylinderRestriction_H1_colimit_mono_of_chart
    (Φ : (nisnevichTopology E.left).Point.{u + 1}) :
    Mono (colim.map (pointedCylinderRestriction (.of k) j Φ
      (LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) G 1))) := by
  let P := LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
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
    hD X b F j q hpb hF hE₀ hE₁ Φ W.unop (D.map a s) hlocal
  have hw := ConcreteCategory.congr_hom (colimit.w D a) s
  exact hw.symm.trans hzero

end Motivic.FiniteEtaleSite.CoefficientInputs

namespace Motivic.FiniteEtaleSite.CoefficientInputs
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.CategoryTheory.Sheaf
open Scheme.Modules Scheme.Modules.Invertible

/-- At any complete field-valued mark on a smooth Cartier divisor, the actual
degree-one cylinder-to-puncture colimit map is monic, conditional on original local
zero and the genuine canonical boundary epimorphisms. The marking field is unchanged. -/
theorem pointedCylinderRestriction_H1_mono_of_cartier_of_boundary_epi
    {k : Type u} [Field k]
    (hD : PresheafWithTransfers.IntegralAffineLocalZero k)
    [HasExt.{u + 1}
      (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
    (Y : SmoothSite (Spec (.of k))) (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant)
    (hE : ∀ X : SmoothSite (Spec (.of k)), Epi (contractionToBoundary X F hF))
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) [IsClosedImmersion i] [Smooth (i ≫ Y.hom)]
    (hI : IsLocallyRankOne Y.left (Scheme.Hom.idealModule i))
    {U : SmoothSite (Spec (.of k))} (j : U ⟶ Y) [IsOpenImmersion j.left]
    (hcomp : Set.range i = (Set.range j.left)ᶜ)
    (K : Type u) [Field K] (b : Spec (.of K) ⟶ Y.left) (s : Spec (.of K))
    (hb : b s ∈ Set.range i) :
    Mono (colim.map (pointedCylinderRestriction (.of k) j
      (relativeFieldPoint b K (𝟙 _))
      (LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) 1))) := by
  let P := LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1
  have hs : (IsLocalRing.closedPoint K : PrimeSpectrum K) = s := Subsingleton.elim _ _
  obtain ⟨cZ, hcZ⟩ := Scheme.exists_field_lift_of_mem_range i b
    (by simpa only [hs] using hb)
  obtain ⟨O, hO, E, a, q, d, ha, hq, hpa, hpq⟩ :=
    SmoothSite.exists_cartier_cylinder_comparison Y i hI (cZ s)
  let D := SmoothSite.closedOpenSite (Y := Y) i O
  let c := openFieldPointLift K cZ s O hO
  let bE := c ≫ d.left
  have hc : c ≫ O.ι = cZ := openFieldPointLift_ι K cZ s O hO
  have hbE : bE ≫ a.left = b := by
    change (c ≫ d.left) ≫ a.left = b
    rw [Category.assoc, hpa.w, ← Category.assoc, hc]
    exact hcZ
  let : Etale a.left := ha
  let : Etale q.left := hq
  obtain ⟨hA, t, hB⟩ := SmoothSite.exists_cartier_puncture_comparison
    (.of k) j a q d i O.ι hpa hpq hcomp
  let w := SmoothSite.etalePullbackSnd j a
  let qU := SmoothSite.etalePullbackFst j a
  let : IsOpenImmersion w.left :=
    inferInstanceAs (IsOpenImmersion (pullback.snd j.left a.left))
  let : Mono (colim.map (pointedCylinderRestriction (.of k) w
      (relativeFieldPoint bE K (𝟙 _)) P)) :=
    pointedCylinderRestriction_H1_colimit_mono_of_chart
      hD D q F w t hB hF (hE D) (hE (SmoothSite.a1Cylinder (.of k) D))
      (relativeFieldPoint bE K (𝟙 _))
  have h := fieldPoint_cylinderRestriction_mono_of_etale
    (.of k) P j a w qU hA K bE
  let M (c : Spec (.of K) ⟶ Y.left) : Prop :=
    Mono (colim.map (pointedCylinderRestriction (.of k) j
      (relativeFieldPoint c K (𝟙 _)) P))
  change M b
  exact Eq.mp (congrArg M hbE) (show M (bE ≫ a.left) from h)

end Motivic.FiniteEtaleSite.CoefficientInputs
