/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.DiagonalBoundary
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.GlobalBoundary

/-! # The actual canonical section zero scheme and its graph correspondence -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u

namespace Motivic.DiagonalZeroCycle
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Hom
open _root_.AlgebraicGeometry.Scheme.IdealSheafData

/-- The zero scheme of the original ideal inclusion is the original closed
subscheme itself, not a reduction of it. -/
def zeroIdealInclusionIso {D C : Scheme.{u}} (j : D ⟶ C) [IsClosedImmersion j]
    [(Scheme.Hom.idealModule j).IsQuasicoherent] :
    Hom.zeroScheme (Scheme.Hom.idealInclusion j) ≅ D :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme
    (Scheme.Hom.imageIdealData_idealInclusion j)) ≪≫ (asIso j.toImage).symm

@[reassoc (attr := simp)]
theorem zeroIdealInclusionIso_hom_inclusion {D C : Scheme.{u}}
    (j : D ⟶ C) [IsClosedImmersion j] [(Scheme.Hom.idealModule j).IsQuasicoherent] :
    (zeroIdealInclusionIso j).hom ≫ j = Hom.zeroInclusion (Scheme.Hom.idealInclusion j) := by
  have ht (I J : C.IdealSheafData) (h : I = J) :
      eqToHom (congrArg Scheme.IdealSheafData.subscheme h) ≫ J.subschemeι = I.subschemeι := by
    subst J
    simp
  have hi : (asIso j.toImage).inv ≫ j = j.imageι := by
    calc
      (asIso j.toImage).inv ≫ j = (asIso j.toImage).inv ≫ (j.toImage ≫ j.imageι) :=
        congrArg (fun z => (asIso j.toImage).inv ≫ z) j.toImage_imageι.symm
      _ = j.imageι := Iso.inv_hom_id_assoc (asIso j.toImage) j.imageι
  simpa only [zeroIdealInclusionIso, Iso.trans_hom, Iso.symm_hom, eqToIso.hom,
    Category.assoc, hi, Hom.zeroScheme, Hom.zeroInclusion, Scheme.Hom.imageι] using
    ht _ _ (Scheme.Hom.imageIdealData_idealInclusion j)

/-- The original component graph has the pushed fundamental cycle, including
all disconnected components of the reduced source. -/
theorem graphCycle_fundamental {S X Y : Scheme.{u}} [IsNoetherian X] [IsReduced X]
    (φ : X ⟶ Y) (g : Y ⟶ S) [IsSeparated g] :
    FiniteCorrespondence.toIntegralCycle (componentGraphCycle φ g) =
      IntegralCycle.finitePushforward (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph φ
        g) (fundamentalCycle X) := by
  classical
  let := IntegralCycle.genericPointFintype X
  let := (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)).fintype
  have hs : componentGraphCycle φ g =
      ∑ x : genericPoints X, (componentGraphGenerator φ g (closure {x.1}) x.2).cycle := by
    have hcomp : componentGraphCycle φ g = ∑ C : irreducibleComponents X,
        (componentGraphGenerator φ g C.1 C.2).cycle := by
      rw [componentGraphCycle]
      rw [Finset.sum_subtype (p := fun C => C ∈ irreducibleComponents X) _
        (fun C => Set.Finite.mem_toFinset _)]
      apply Finset.sum_congr rfl
      intro C _
      rw [dite_eq_left C.2]
    rw [hcomp]
    exact (Fintype.sum_equiv (genericPoints.equiv (α := X)) _ _ (fun _ => rfl)).symm
  rw [hs, map_sum, ← IntegralCycle.ofGenericCoefficients_genericMultiplicity,
    IntegralCycle.ofGenericCoefficients_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [genericMultiplicity_eq_one, Nat.cast_one, IntegralCycle.finitePushforward_single,
    residueDegree_of_surjectiveOnStalks, Nat.cast_one, mul_one]
  rw [FiniteCorrespondenceGenerator.cycle, FiniteCorrespondence.toIntegralCycle_single]
  congr 1
  apply Subtype.ext
  have he : (IntegralClosedSubscheme.pointClosure x.1).val =
      X.irreducibleComponentIdeal (closure {x.1}) x.2 := by
    let : IsReduced (X.irreducibleComponentIdeal (closure {x.1}) x.2).subscheme :=
      inferInstanceAs (IsReduced (X.irreducibleComponent (closure {x.1}) x.2))
    apply idealSheaf_eq_of_support_eq
    apply SetLike.coe_injective
    rfl
  change (X.irreducibleComponentι (closure {x.1}) x.2 ≫
    _root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph φ g).ker =
    ((IntegralClosedSubscheme.pointClosure x.1).val.subschemeι ≫
      _root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph φ g).ker
  rw [he]
  rfl

/-- The full identity-source span is exactly the existing graph functor. -/
theorem ofFiniteFlatSpan_id {k : Type u} [Field k]
    {X Y : SmoothSite (Spec (.of k))} (φ : X ⟶ Y) :
    Cor.ofFiniteFlatSpan (X := X) (Y := Y) (𝟙 X.left) φ.left
      (by simp [MorphismProperty.Over.w φ]) = (Cor.graphFunctor k).map φ := by
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [Cor.toIntegralCycle_ofFiniteFlatSpan, Cor.graphFunctor_map]
  have hg {S A B : Scheme.{u}} [IsNoetherian A] [IsReduced A]
      {f : A ⟶ S} (g : B ⟶ S) [IsSeparated g] (q : A ⟶ B) (w : q ≫ g = f) :
      FiniteCorrespondence.toIntegralCycle (componentGraphCycleOver q w) =
        letI : IsFinite (pullback.lift (𝟙 A) q ((Category.id_comp f).trans w.symm)) :=
          FiniteFlatCorrespondence.isFinite_productMap (𝟙 A) _ (pullback.lift_fst _ _ _)
        IntegralCycle.finitePushforward (pullback.lift (𝟙 A) q ((Category.id_comp f).trans w.symm))
          (fundamentalCycle A) := by
    subst f
    exact graphCycle_fundamental q g
  exact (hg Y.hom φ.left (MorphismProperty.Over.w φ)).symm

/-- The original section projection identifies the full canonical zero scheme
with the base, proving finite flatness without an additional geometric premise. -/
theorem zeroIdealInclusion_finite_flat {D C : Scheme.{u}} (j : D ⟶ C)
    [IsClosedImmersion j] [(Scheme.Hom.idealModule j).IsQuasicoherent]
    (p : C ⟶ D) (hp : j ≫ p = 𝟙 D) :
    IsFinite (Hom.zeroInclusion (Scheme.Hom.idealInclusion j) ≫ p) ∧
      Flat (Hom.zeroInclusion (Scheme.Hom.idealInclusion j) ≫ p) := by
  have he : Hom.zeroInclusion (Scheme.Hom.idealInclusion j) ≫ p =
      (zeroIdealInclusionIso j).hom := by
    rw [← zeroIdealInclusionIso_hom_inclusion j, Category.assoc, hp, Category.comp_id]
  rw [he]
  exact ⟨inferInstance, inferInstance⟩

/-- The zero correspondence of the canonical section of an actual graph divisor
is exactly that graph, including disconnected or empty smooth bases. -/
theorem canonicalSection_zero_graph {k : Type u} [Field k]
    {X Y : SmoothSite (Spec (.of k))} {C : Scheme.{u}}
    (j : X.left ⟶ C) [IsClosedImmersion j]
    [(Scheme.Hom.idealModule j).IsQuasicoherent]
    (p : C ⟶ X.left) (hp : j ≫ p = 𝟙 X.left)
    (g : C ⟶ Y.left) (φ : X ⟶ Y) (hg : j ≫ g = φ.left)
    (h : p ≫ X.hom = g ≫ Y.hom) :
    letI := (zeroIdealInclusion_finite_flat j p hp).1
    letI := (zeroIdealInclusion_finite_flat j p hp).2
    Cor.ofFiniteFlatSpan (X := X) (Y := Y)
      (Hom.zeroInclusion (Scheme.Hom.idealInclusion j) ≫ p)
      (Hom.zeroInclusion (Scheme.Hom.idealInclusion j) ≫ g)
      (by simpa only [Category.assoc] using
        congrArg (fun z => Hom.zeroInclusion (Scheme.Hom.idealInclusion j) ≫ z) h) =
        (Cor.graphFunctor k).map φ := by
  let := (zeroIdealInclusion_finite_flat j p hp).1
  let := (zeroIdealInclusion_finite_flat j p hp).2
  have hsource : Hom.zeroInclusion (Scheme.Hom.idealInclusion j) ≫ p =
      (zeroIdealInclusionIso j).hom ≫ 𝟙 X.left := by
    rw [← zeroIdealInclusionIso_hom_inclusion j, Category.assoc, hp]
  have htarget : Hom.zeroInclusion (Scheme.Hom.idealInclusion j) ≫ g =
      (zeroIdealInclusionIso j).hom ≫ φ.left := by
    rw [← zeroIdealInclusionIso_hom_inclusion j, Category.assoc, hg]
  have hs := GlobalBoundaryPencil.ofFiniteFlatSpan_precompIso
    (X := X) (Y := Y) (zeroIdealInclusionIso j) (𝟙 X.left) φ.left
    (by simp [MorphismProperty.Over.w φ])
  rw [ofFiniteFlatSpan_id] at hs
  simpa only [← hsource, ← htarget] using hs

end Motivic.DiagonalZeroCycle
