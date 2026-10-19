/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.BoundaryRatio
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.ThickBoundaryBaseChange

/-! # Actual chart factors for the original correction norm

The correction parameter is the original disjoint open, not the source curve.
Both boundary factors are constructed from the same finite chart square. The
residual retains its actual map to the entire supplied infinity scheme.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.ChartMarkedNorm`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.FunctionalChartMarkedNorm`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.TargetMarkedCoordinate`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S X Y A Z C D K T V Q B : Scheme.{u}}
  (q : X ⟶ S) (π : C ⟶ S) (j : Y ⟶ C) (p : Y ⟶ X)
  (hq : j ≫ π = p ≫ q) (a : A ⟶ X) (z : Z ⟶ X)
  (s : Z ⟶ Y) (hs : s ≫ p = z)
  (k : V ⟶ T) (σ : Q ⟶ V) (u : T ⟶ C) (m : Q ⟶ Z)
  (hj : m ≫ (s ≫ j) = (σ ≫ k) ≫ u)
  (w : T ⟶ pullback (a ≫ q) π) (hw : w ≫ pullback.snd (a ≫ q) π = u)

/-- The original correction parameter and actual marked point define this factor. -/
def correctionChartMarkedFactor : Q ⟶ pullback (a ≫ q) (z ≫ q) :=
  pullback.lift ((σ ≫ k) ≫ w ≫ pullback.fst (a ≫ q) π) m (by
    calc
      ((σ ≫ k) ≫ w ≫ pullback.fst (a ≫ q) π) ≫ (a ≫ q) =
          (σ ≫ k) ≫ w ≫ pullback.snd (a ≫ q) π ≫ π := by
            simp only [Category.assoc, pullback.condition]
      _ = m ≫ s ≫ j ≫ π := by
        rw [← Category.assoc w, hw]
        simpa only [Category.assoc] using congrArg (fun l => l ≫ π) hj.symm
      _ = m ≫ (z ≫ q) := by rw [hq, ← Category.assoc s, hs])

/-- The marked factor is over the literal original correction ambient point. -/
@[reassoc] theorem correctionChartMarkedFactor_ambient :
    correctionChartMarkedFactor q π j p hq a z s hs k σ u m hj w hw ≫
      psiZeroInclusion q π j p hq a z s hs = (σ ≫ k) ≫ w := by
  apply pullback.hom_ext
  · simp [correctionChartMarkedFactor, psiZeroInclusion]
  · simpa only [correctionChartMarkedFactor, psiZeroInclusion,
      Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hw] using hj

variable (f : C ⟶ K) [IsFinite f] (zK : Z ⟶ K) (hsK : (s ≫ j) ≫ f = zK)
  (n : T ⟶ B) [IsFinite n] (z' : Q ⟶ B) (hn : (σ ≫ k) ≫ n = z')
  (t : B ⟶ K) (Hf : IsPullback u n f t) (hz : z' ≫ t = m ≫ zK)
  (d : D ⟶ C) (bE : (Scheme.residualMarkedFiberOpen f j zK s hsK).toScheme ⟶ D)
  (hbE : bE ≫ d = Scheme.residualMarkedFiberMap f j zK s hsK)

/-- Actual residual base change yields the full infinity factor for the correction. -/
def correctionChartResidualFactor :
    (Scheme.residualMarkedFiberOpen n k z' σ hn).toScheme ⟶
      pullback (pullback.snd (a ≫ q) π) d :=
  pullback.lift (Scheme.residualMarkedFiberMap n k z' σ hn ≫ w)
    (Scheme.residualBaseChangeMap f j zK s hsK n k z' σ hn u t Hf m hz hj ≫ bE) (by
      rw [Category.assoc, hw]
      exact (Scheme.residualBaseChangeMap_boundary f j zK s hsK n k z' σ hn
        u t Hf m hz hj d bE hbE).symm)

/-- All nilpotents and the literal correction ambient map are retained. -/
@[reassoc] theorem correctionChartResidualFactor_ambient :
    correctionChartResidualFactor q π j a s k σ u m hj w hw f zK hsK n z' hn
      t Hf hz d bE hbE ≫ pullback.fst (pullback.snd (a ≫ q) π) d =
        Scheme.residualMarkedFiberMap n k z' σ hn ≫ w :=
  pullback.lift_fst _ _ _

include hbE in
/-- The correction norm uses internally constructed marked and residual factors
from the original finite square. Only the original total chart is assumed free. -/
theorem correctionChart_norm_marked_value
    [IsSeparated q] [Flat a]
    (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
      Hom.idealModule (Hom.boundaryGraphTarget q z))
    (ha : Disjoint (Set.range a) (Set.range z))
    (N : LineBundle (pullback (a ≫ q) π))
    (nS dS : SheafOfModules.unit (pullback (a ≫ q) π).ringCatSheaf ⟶ N.val)
    (hN : pullbackSectionMap (psiBoundaryInclusion q π j p hq a z s hs d) nS =
      (fixedProductBoundaryFrame q π a z e ha d).hom ≫
        pullbackSectionMap (psiBoundaryInclusion q π j p hq a z s hs d) dS)
    {R Q₀ : Type u} [CommRing R] [CommRing Q₀]
    (n : T ⟶ Spec (.of R)) [IsFinite n] (φ : R →+* Q₀)
    (k : V ⟶ T) [IsOpenImmersion k] (σ : Spec (.of Q₀) ⟶ V)
    (hn : (σ ≫ k) ≫ n = Spec.map (CommRingCat.ofHom φ))
    (HN : IsPullback σ (𝟙 _) (k ≫ n) (Spec.map (CommRingCat.ofHom φ)))
    (t : Spec (.of R) ⟶ K) (Hf : IsPullback u n f t)
    (m : Spec (.of Q₀) ⟶ Z)
    (hz : Spec.map (CommRingCat.ofHom φ) ≫ t = m ≫ zK)
    (hj : m ≫ (s ≫ j) = (σ ≫ k) ≫ u)
    [IsIso (pullbackSectionMap w dS)] :
    let b : Γ(T, ⊤) := Modules.Hom.app
      (pullbackSectionMap w nS ≫ inv (pullbackSectionMap w dS)) ⊤ (1 : Γ(T, ⊤))
    let μ := correctionChartMarkedFactor q π j p hq a z s hs k σ u m hj w hw
    let c : Γ(Spec (.of Q₀), ⊤) := Modules.Hom.app (Hom.unitEndomorphismPullback
      (μ ≫ Hom.boundaryProductMap q a z)
      (e.hom ≫ Hom.idealInclusion (Hom.boundaryGraphTarget q z))) ⊤
        (1 : Γ(Spec (.of Q₀), ⊤))
    let : Algebra R Γ(T, ⊤) := (FiniteSchemeNormBaseChange.scalarMap n).toAlgebra
    ∀ [Module.Free R Γ(T, ⊤)], φ (Algebra.norm R b) = (Scheme.ΓSpecIso (.of Q₀)).hom c := by
  let : Algebra R Γ(T, ⊤) := (FiniteSchemeNormBaseChange.scalarMap n).toAlgebra
  dsimp only
  intro hfree
  let := hfree
  let μ := correctionChartMarkedFactor q π j p hq a z s hs k σ u m hj w hw
  let ρ := correctionChartResidualFactor q π j a s k σ u m hj w hw f zK hsK n
    (Spec.map (CommRingCat.ofHom φ)) hn t Hf hz d bE hbE
  exact correctionRatio_norm_marked_value q π j p hq a z s hs e ha d N nS dS hN
    n φ k σ hn HN w μ
    (correctionChartMarkedFactor_ambient q π j p hq a z s hs k σ u m hj w hw).symm
    ρ (correctionChartResidualFactor_ambient q π j a s k σ u m hj w hw f zK hsK n
      (Spec.map (CommRingCat.ofHom φ)) hn t Hf hz d bE hbE).symm

end AlgebraicGeometry.Scheme.RelativeCurvePencil
