/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.FiniteCoefficientsCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Exactness of the coefficient Bockstein

The actual mapping-cone coefficient triangle gives an exact sequence on
cohomology. Its middle three terms identify the kernel of the positive
Bockstein with the integral cohomology modulo multiplication by the level.
The Bockstein factors through the kernel of multiplication by the level on
the next integral cohomology object. These statements hold at every natural
level, including one and composite levels, in every abelian category.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Preadditive CochainComplex HomologicalComplex
open CategoryTheory.ComposableArrows

universe u v

namespace Motivic.finiteCoefficients

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : CochainComplex C ℤ) (n : ℕ)

/-- The integral-to-finite coefficient map on actual cohomology objects. -/
noncomputable def integralHomology (i : ℤ) :
    K.homology i ⟶ (finiteCoefficients K n).homology i :=
  homologyMap (integral K n) i

/-- The five consecutive cohomology objects in the coefficient sequence. -/
noncomputable def cohomologySequence (i : ℤ) : ComposableArrows C 4 :=
  mk₄ (n • 𝟙 (K.homology i)) (integralHomology K n i)
    (bocksteinHomology K n i) (n • 𝟙 (K.homology (i + 1)))

/-- Exactness is inherited from the actual distinguished mapping-cone triangle. -/
theorem cohomologySequence_exact (i : ℤ) : (cohomologySequence K n i).Exact := by
  let F := HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0
  let e := HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ)
  let S := (F.homologySequenceComposableArrows₅
    (mappingCone.triangleh (n • 𝟙 K)) i (i + 1) rfl).δlast
  have hS : S.Exact :=
    (F.homologySequenceComposableArrows₅_exact _
      (HomotopyCategory.mappingCone_triangleh_distinguished (n • 𝟙 K)) i (i + 1) rfl).δlast
  let φ : S ≅ cohomologySequence K n i :=
    isoMk₄ ((e i).app K) ((e i).app K)
      ((e i).app (finiteCoefficients K n))
      ((e (i + 1)).app K) ((e (i + 1)).app K)
      (by
        change (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) i).map
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (n • 𝟙 K)) ≫
            (e i).hom.app K = (e i).hom.app K ≫ (n • 𝟙 _)
        simp only [Functor.map_smul, CategoryTheory.Functor.map_id, Linear.smul_comp, id_comp,
          Functor.comp_obj, Linear.comp_smul]
        exact congrArg (fun f => n • f) (comp_id ((e i).hom.app K)).symm)
      (by
        dsimp [S, F, cohomologySequence, integralHomology, integral]
        exact (e i).hom.naturality (mappingCone.inr (n • 𝟙 K)))
      (by
        change F.homologySequenceδ (mappingCone.triangleh (n • 𝟙 K)) i (i + 1) rfl ≫
          (e (i + 1)).hom.app K =
            (e i).hom.app (finiteCoefficients K n) ≫ bocksteinHomology K n i
        erw [CochainComplex.homologySequenceδ_quotient_mapTriangle_obj]
        dsimp only [e, bocksteinHomology, bockstein, triangle, Functor.shiftMap,
          mappingCone.triangle]
        simp only [Functor.mapTriangle_obj, Pretriangulated.Triangle.mk_obj₃,
          Pretriangulated.Triangle.mk_obj₁, Functor.comp_obj, assoc,
          Iso.inv_hom_id_app]
        change _ ≫ _ ≫ _ ≫ 𝟙 _ = _
        simp only [comp_id]
        rfl)
      (by
        change (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) (i + 1)).map
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (n • 𝟙 K)) ≫
            (e (i + 1)).hom.app K = (e (i + 1)).hom.app K ≫ (n • 𝟙 _)
        simp only [Functor.map_smul, CategoryTheory.Functor.map_id, Linear.smul_comp, id_comp,
          Functor.comp_obj, Linear.comp_smul]
        exact congrArg (fun f => n • f) (comp_id ((e (i + 1)).hom.app K)).symm)
  exact ComposableArrows.exact_of_iso φ hS

/-- Multiplication by the coefficient level followed by reduction vanishes. -/
@[reassoc]
theorem mul_integralHomology (i : ℤ) :
    (n • 𝟙 (K.homology i)) ≫ integralHomology K n i = 0 :=
  (cohomologySequence_exact K n i).zero 0

/-- The reduction map is annihilated by the coefficient level, in simp-normal form. -/
@[simp]
theorem nsmul_integralHomology (i : ℤ) : n • integralHomology K n i = 0 := by
  simpa only [Linear.smul_comp, id_comp] using mul_integralHomology K n i

/-- Every postcomposition of integral reduction is annihilated by the level. -/
@[simp]
theorem nsmul_integralHomology_comp (i : ℤ) {X : C}
    (f : (finiteCoefficients K n).homology i ⟶ X) :
    n • (integralHomology K n i ≫ f) = 0 := by
  rw [← Linear.smul_comp, nsmul_integralHomology, zero_comp]

/-- The Bockstein vanishes on integral classes. -/
@[reassoc (attr := simp)]
theorem integralHomology_bocksteinHomology (i : ℤ) :
    integralHomology K n i ≫ bocksteinHomology K n i = 0 :=
  (cohomologySequence_exact K n i).zero 1

/-- Every Bockstein class is annihilated by the coefficient level. -/
@[reassoc]
theorem bocksteinHomology_mul (i : ℤ) :
    bocksteinHomology K n i ≫ (n • 𝟙 (K.homology (i + 1))) = 0 :=
  (cohomologySequence_exact K n i).zero 2

/-- The Bockstein morphism is annihilated by the level, in simp-normal form. -/
@[simp]
theorem nsmul_bocksteinHomology_map (i : ℤ) : n • bocksteinHomology K n i = 0 := by
  simpa only [Linear.comp_smul, comp_id] using bocksteinHomology_mul K n i

/-- Every postcomposition of the positive Bockstein is annihilated by the level. -/
@[simp]
theorem nsmul_bocksteinHomology_comp (i : ℤ) {X : C}
    (f : K.homology (i + 1) ⟶ X) : n • (bocksteinHomology K n i ≫ f) = 0 := by
  rw [← Linear.smul_comp, nsmul_bocksteinHomology_map, zero_comp]

/-- Reduction has kernel precisely the image of multiplication by the level. -/
theorem exact_mul_integralHomology (i : ℤ) :
    (ShortComplex.mk _ _ (mul_integralHomology K n i)).Exact :=
  (cohomologySequence_exact K n i).exact 0

/-- The kernel of the positive Bockstein is precisely the image of integral classes. -/
theorem exact_integralHomology_bocksteinHomology (i : ℤ) :
    (ShortComplex.mk _ _ (integralHomology_bocksteinHomology K n i)).Exact :=
  (cohomologySequence_exact K n i).exact 1

/-- The image of the positive Bockstein is precisely the level torsion. -/
theorem exact_bocksteinHomology_mul (i : ℤ) :
    (ShortComplex.mk _ _ (bocksteinHomology_mul K n i)).Exact :=
  (cohomologySequence_exact K n i).exact 2

/-- The canonical inclusion of integral cohomology modulo the coefficient level. -/
noncomputable def integralQuotient (i : ℤ) :
    cokernel (n • 𝟙 (K.homology i)) ⟶ (finiteCoefficients K n).homology i :=
  cokernel.desc _ (integralHomology K n i) (mul_integralHomology K n i)

/-- The positive Bockstein with codomain restricted to level torsion. -/
noncomputable def bocksteinTorsion (i : ℤ) :
    (finiteCoefficients K n).homology i ⟶ kernel (n • 𝟙 (K.homology (i + 1))) :=
  kernel.lift _ (bocksteinHomology K n i) (bocksteinHomology_mul K n i)

@[reassoc (attr := simp)]
theorem quotientπ_integralQuotient (i : ℤ) :
    cokernel.π (n • 𝟙 (K.homology i)) ≫ integralQuotient K n i =
      integralHomology K n i := by
  simp [integralQuotient]

@[reassoc (attr := simp)]
theorem bocksteinTorsion_kernelι (i : ℤ) :
    bocksteinTorsion K n i ≫ kernel.ι (n • 𝟙 (K.homology (i + 1))) =
      bocksteinHomology K n i := by
  simp [bocksteinTorsion]

instance mono_integralQuotient (i : ℤ) : Mono (integralQuotient K n i) :=
  (exact_mul_integralHomology K n i).mono_cokernelDesc

instance epi_bocksteinTorsion (i : ℤ) : Epi (bocksteinTorsion K n i) :=
  (exact_bocksteinHomology_mul K n i).epi_kernelLift

@[reassoc (attr := simp)]
theorem integralQuotient_bocksteinHomology (i : ℤ) :
    integralQuotient K n i ≫ bocksteinHomology K n i = 0 := by
  rw [← cancel_epi (cokernel.π (n • 𝟙 (K.homology i))),
    quotientπ_integralQuotient_assoc, integralHomology_bocksteinHomology, comp_zero]

@[reassoc (attr := simp)]
theorem integralQuotient_bocksteinTorsion (i : ℤ) :
    integralQuotient K n i ≫ bocksteinTorsion K n i = 0 := by
  rw [← cancel_mono (kernel.ι (n • 𝟙 (K.homology (i + 1)))),
    assoc, bocksteinTorsion_kernelι, integralQuotient_bocksteinHomology, zero_comp]

/-- The canonical coefficient short complex `Hⁱ(K)/n → Hⁱ(K/n) → Hⁱ⁺¹(K)[n]`. -/
noncomputable def cohomologyShortComplex (i : ℤ) : ShortComplex C :=
  ShortComplex.mk (integralQuotient K n i) (bocksteinTorsion K n i)
    (integralQuotient_bocksteinTorsion K n i)

/-- The coefficient short complex is short exact with its canonical maps. -/
theorem cohomologyShortComplex_shortExact (i : ℤ) :
    (cohomologyShortComplex K n i).ShortExact where
  exact := by
    let S := ShortComplex.mk _ _ (integralHomology_bocksteinHomology K n i)
    let T := ShortComplex.mk _ _ (integralQuotient_bocksteinHomology K n i)
    let φ : S ⟶ T :=
      { τ₁ := cokernel.π (n • 𝟙 (K.homology i))
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by simp [S, T]
        comm₂₃ := by simp [S, T] }
    have hT : T.Exact :=
      (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
        (exact_integralHomology_bocksteinHomology K n i)
    let ψ : cohomologyShortComplex K n i ⟶ T :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := kernel.ι (n • 𝟙 (K.homology (i + 1)))
        comm₁₂ := by simp [cohomologyShortComplex, T]
        comm₂₃ := by simp [cohomologyShortComplex, T] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).2 hT
  mono_f := mono_integralQuotient K n i
  epi_g := epi_bocksteinTorsion K n i

section Modules

variable {R : Type u} [Ring R] (K : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℕ)

/-- On modules, the kernel of the positive Bockstein is the range of integral reduction. -/
theorem range_integralHomology_eq_ker_bocksteinHomology (i : ℤ) :
    LinearMap.range (integralHomology K n i).hom =
      LinearMap.ker (bocksteinHomology K n i).hom :=
  (exact_integralHomology_bocksteinHomology K n i).moduleCat_range_eq_ker

/-- A finite class has zero Bockstein exactly when it lifts to an integral class. -/
theorem bocksteinHomology_eq_zero_iff (i : ℤ)
    (x : (finiteCoefficients K n).homology i) :
    bocksteinHomology K n i x = 0 ↔
      ∃ y : K.homology i, integralHomology K n i y = x :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (exact_integralHomology_bocksteinHomology K n i) x

/-- The positive Bockstein of every class is annihilated by `n`. -/
@[simp]
theorem nsmul_bocksteinHomology (i : ℤ)
    (x : (finiteCoefficients K n).homology i) :
    n • bocksteinHomology K n i x = 0 := by
  exact congrArg (fun f : (finiteCoefficients K n).homology i ⟶
    K.homology (i + 1) => f x) (nsmul_bocksteinHomology_map K n i)

/-- Every integral class annihilated by `n` is the positive Bockstein of a finite class. -/
theorem exists_bocksteinHomology_eq (i : ℤ) (y : K.homology (i + 1))
    (hy : n • y = 0) :
    ∃ x : (finiteCoefficients K n).homology i, bocksteinHomology K n i x = y := by
  apply (ShortComplex.moduleCat_exact_iff _).1 (exact_bocksteinHomology_mul K n i) y
  simpa using hy

/-- The usual quotient module of integral cohomology by the multiples of `n`. -/
noncomputable def integralModulo (i : ℤ) :
    ModuleCat.of R (K.homology i ⧸ LinearMap.range (n • 𝟙 (K.homology i)).hom) ⟶
      (finiteCoefficients K n).homology i :=
  (ModuleCat.cokernelIsoRangeQuotient (n • 𝟙 (K.homology i))).inv ≫
    integralQuotient K n i

/-- The Bockstein landing in the usual kernel submodule, that is, the `n`-torsion. -/
noncomputable def bocksteinNTorsion (i : ℤ) :
    (finiteCoefficients K n).homology i ⟶
      ModuleCat.of R (LinearMap.ker (n • 𝟙 (K.homology (i + 1))).hom) :=
  bocksteinTorsion K n i ≫
    (ModuleCat.kernelIsoKer (n • 𝟙 (K.homology (i + 1)))).hom

/-- The kernel submodule used by `bocksteinNTorsion` is exactly the `n`-torsion. -/
theorem mem_nTorsion_iff (i : ℤ) (y : K.homology (i + 1)) :
    y ∈ LinearMap.ker (n • 𝟙 (K.homology (i + 1))).hom ↔ n • y = 0 := by
  simp

/-- The usual quotient map followed by `integralModulo` is integral reduction. -/
@[reassoc (attr := simp)]
theorem mkQ_integralModulo (i : ℤ) :
    (ModuleCat.ofHom
      (LinearMap.range (n • (LinearMap.id : K.homology i →ₗ[R] K.homology i))).mkQ :
        K.homology i ⟶ _) ≫ integralModulo K n i = integralHomology K n i := by
  change ModuleCat.ofHom (LinearMap.range (n • 𝟙 (K.homology i)).hom).mkQ ≫
    integralModulo K n i = integralHomology K n i
  dsimp only [integralModulo]
  rw [← assoc, ModuleCat.range_mkQ_cokernelIsoRangeQuotient_inv,
    quotientπ_integralQuotient]

/-- Forgetting the torsion condition recovers the actual positive Bockstein. -/
@[reassoc (attr := simp)]
theorem bocksteinNTorsion_subtype (i : ℤ) :
    bocksteinNTorsion K n i ≫
      (ModuleCat.ofHom (LinearMap.ker
        (n • (LinearMap.id : K.homology (i + 1) →ₗ[R] K.homology (i + 1)))).subtype :
          _ ⟶ K.homology (i + 1)) =
        bocksteinHomology K n i := by
  change bocksteinNTorsion K n i ≫
    ModuleCat.ofHom (LinearMap.ker (n • 𝟙 (K.homology (i + 1))).hom).subtype =
      bocksteinHomology K n i
  dsimp only [bocksteinNTorsion]
  rw [assoc, ModuleCat.kernelIsoKer_hom_ker_subtype, bocksteinTorsion_kernelι]

instance mono_integralModulo (i : ℤ) : Mono (integralModulo K n i) := by
  dsimp [integralModulo]
  infer_instance

instance epi_bocksteinNTorsion (i : ℤ) : Epi (bocksteinNTorsion K n i) := by
  dsimp [bocksteinNTorsion]
  infer_instance

/-- The quotient and torsion interpretation of the canonical coefficient short complex. -/
noncomputable def moduleCohomologyShortComplex (i : ℤ) : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk (integralModulo K n i) (bocksteinNTorsion K n i)
    (by simp [integralModulo, bocksteinNTorsion])

/-- The concrete module sequence `0 → Hⁱ(K)/n → Hⁱ(K/n) → Hⁱ⁺¹(K)[n] → 0` is exact. -/
theorem moduleCohomologyShortComplex_shortExact (i : ℤ) :
    (moduleCohomologyShortComplex K n i).ShortExact := by
  apply ShortComplex.shortExact_of_iso _ (cohomologyShortComplex_shortExact K n i)
  exact ShortComplex.isoMk (ModuleCat.cokernelIsoRangeQuotient _) (Iso.refl _)
    (ModuleCat.kernelIsoKer _) (by simp [cohomologyShortComplex,
      moduleCohomologyShortComplex, integralModulo])
    (by simp [cohomologyShortComplex, moduleCohomologyShortComplex, bocksteinNTorsion])

end Modules

end Motivic.finiteCoefficients
