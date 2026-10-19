/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.Pair.Euler
public import Motivic.Aglib.Algebra.Homology.LengthEuler.Chain
public import Motivic.Aglib.RingTheory.LocalLength.KoszulPairFiniteLength
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Additivity of the two-equation local Euler multiplicity

A coefficient map induces the literal chain map with components `f`,
`f × f`, `f`, and zero. A short exact coefficient sequence therefore induces
an actual short exact sequence of Koszul complexes. The homology long exact
sequence, with its genuine connecting homomorphisms, proves additivity of
the full local Euler integer. Neither equation is assumed regular.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open _root_.HomologicalComplex.ModuleLengthEuler
open scoped ZeroObject

universe u v

namespace Module.KoszulPair

variable {R : Type u} [CommRing R]
variable {U V W : Type v}
variable [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]
variable (a b : R)

/-- The coefficient map in each literal Koszul degree. -/
noncomputable def coefficientMapX (f : U →ₗ[R] V) :
    (n : ℕ) → (chainComplex U a b).X n ⟶ (chainComplex V a b).X n
  | 0 => ModuleCat.ofHom f
  | 1 => ModuleCat.ofHom (f.prodMap f)
  | 2 => ModuleCat.ofHom f
  | _ + 3 => 0

/-- A coefficient map gives an actual chain map on the two-equation Koszul complex. -/
noncomputable def coefficientMap (f : U →ₗ[R] V) :
    chainComplex U a b ⟶ chainComplex V a b :=
  ChainComplex.ofHom (coefficientMapX a b f) (by
    intro n
    obtain (_ | _ | n) := n
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change U × U at x
      change d₁ V a b (f x.1, f x.2) = f (d₁ U a b x)
      change a • f x.1 + b • f x.2 = f (a • x.1 + b • x.2)
      simp
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change U at x
      change d₂ V a b (f x) = (f (d₂ U a b x).1, f (d₂ U a b x).2)
      change (-(b • f x), a • f x) = (f (-(b • x)), f (a • x))
      exact Prod.ext (by rw [f.map_neg, f.map_smul]) (f.map_smul a x).symm
    · change coefficientMapX a b f (n + 3) ≫
          (chainComplex V a b).d (n + 3) (n + 2) =
        (chainComplex U a b).d (n + 3) (n + 2) ≫ coefficientMapX a b f (n + 2)
      rw [chainComplex_d_add_three, chainComplex_d_add_three, comp_zero, zero_comp])

/-- Zero composites of coefficient maps remain zero as chain maps. -/
theorem coefficientMap_comp_eq_zero (f : U →ₗ[R] V) (g : V →ₗ[R] W)
    (h : g.comp f = 0) : coefficientMap a b f ≫ coefficientMap a b g = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  obtain (_ | _ | _ | n) := n
  · exact ModuleCat.hom_ext h
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (g (f x.1), g (f x.2)) = (0, 0)
    have hx := LinearMap.congr_fun h x.1
    have hy := LinearMap.congr_fun h x.2
    exact Prod.ext hx hy
  · exact ModuleCat.hom_ext h
  · exact zero_comp

/-- The actual short complex of Koszul complexes induced by a coefficient sequence. -/
noncomputable def coefficientShortComplex (f : U →ₗ[R] V) (g : V →ₗ[R] W)
    (h : g.comp f = 0) : ShortComplex (ChainComplex (ModuleCat.{v} R) ℕ) :=
  ShortComplex.mk (coefficientMap a b f) (coefficientMap a b g)
    (coefficientMap_comp_eq_zero a b f g h)

/-- Exactness of a coefficient sequence is preserved in the doubled degree-one term. -/
theorem exact_prodMap (f : U →ₗ[R] V) (g : V →ₗ[R] W)
    (hex : Function.Exact f g) : Function.Exact (f.prodMap f) (g.prodMap g) := by
  intro x
  constructor
  · intro hx
    obtain ⟨u, hu⟩ := (hex x.1).mp (congrArg Prod.fst hx)
    obtain ⟨v, hv⟩ := (hex x.2).mp (congrArg Prod.snd hx)
    exact ⟨(u, v), Prod.ext hu hv⟩
  · rintro ⟨y, rfl⟩
    exact Prod.ext (hex.apply_apply_eq_zero y.1) (hex.apply_apply_eq_zero y.2)

/-- A short exact sequence of coefficients produces a genuine short exact sequence
of the actual two-equation Koszul chain complexes. -/
theorem coefficientShortComplex_shortExact (f : U →ₗ[R] V) (g : V →ₗ[R] W)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g) :
    (coefficientShortComplex a b f g hex.linearMap_comp_eq_zero).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  obtain (_ | _ | _ | n) := n
  · exact {
      exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr hex
      mono_f := (ModuleCat.mono_iff_injective _).mpr hf
      epi_g := (ModuleCat.epi_iff_surjective _).mpr hg }
  · refine {
      exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
        (exact_prodMap f g hex)
      mono_f := (ModuleCat.mono_iff_injective _).mpr ?_
      epi_g := (ModuleCat.epi_iff_surjective _).mpr ?_ }
    · intro x y hxy
      exact Prod.ext (hf (congrArg Prod.fst hxy)) (hf (congrArg Prod.snd hxy))
    · intro x
      obtain ⟨u, hu⟩ := hg x.1
      obtain ⟨v, hv⟩ := hg x.2
      exact ⟨(u, v), Prod.ext hu hv⟩
  · exact {
      exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr hex
      mono_f := (ModuleCat.mono_iff_injective _).mpr hf
      epi_g := (ModuleCat.epi_iff_surjective _).mpr hg }
  · refine {
      exact := ShortComplex.exact_of_isZero_X₂ _ (isZero_zero _)
      mono_f := (ModuleCat.mono_iff_injective _).mpr ?_
      epi_g := (ModuleCat.epi_iff_surjective _).mpr ?_ }
    · change Function.Injective (0 : (0 : ModuleCat.{v} R) ⟶ 0)
      have : Subsingleton (0 : ModuleCat.{v} R) :=
        ModuleCat.isZero_iff_subsingleton.mp (isZero_zero _)
      intro x y _
      exact Subsingleton.elim x y
    · change Function.Surjective (0 : (0 : ModuleCat.{v} R) ⟶ 0)
      have : Subsingleton (0 : ModuleCat.{v} R) :=
        ModuleCat.isZero_iff_subsingleton.mp (isZero_zero _)
      intro x
      exact ⟨0, Subsingleton.elim _ _⟩

/-- Full local two-equation Euler multiplicity is additive in short exact coefficient
sequences with finite homology. No scalar-regularity hypothesis is needed. -/
theorem eulerMultiplicity_add_of_exact (f : U →ₗ[R] V) (g : V →ₗ[R] W)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g)
    (hU : HasFiniteHomology U a b) (hV : HasFiniteHomology V a b)
    (hW : HasFiniteHomology W a b) :
    eulerMultiplicity V a b hV = eulerMultiplicity U a b hU + eulerMultiplicity W a b hW := by
  have hh := chainEuler_add_of_shortExact
    (coefficientShortComplex a b f g hex.linearMap_comp_eq_zero)
    (coefficientShortComplex_shortExact a b f g hf hg hex)
    (finiteHomology_chainComplex U a b hU) (finiteHomology_chainComplex V a b hV)
    (finiteHomology_chainComplex W a b hW)
  change chainEuler (chainComplex V a b) _ =
    chainEuler (chainComplex U a b) _ + chainEuler (chainComplex W a b) _ at hh
  rw [chainEuler_eq_eulerMultiplicity V a b hV,
    chainEuler_eq_eulerMultiplicity U a b hU,
    chainEuler_eq_eulerMultiplicity W a b hW] at hh
  exact hh

/-- For finite modules over a Noetherian ring, an Artinian equation quotient
supplies all finite-length hypotheses in the local Euler additive law. -/
theorem eulerMultiplicity_add_of_artinian_quotient [IsNoetherianRing R]
    [Module.Finite R U] [Module.Finite R V] [Module.Finite R W]
    [IsArtinianRing (R ⧸ Ideal.span ({a, b} : Set R))]
    (f : U →ₗ[R] V) (g : V →ₗ[R] W)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g) :
    eulerMultiplicity V a b (hasFiniteHomology_of_artinian_quotient V a b) =
      eulerMultiplicity U a b (hasFiniteHomology_of_artinian_quotient U a b) +
        eulerMultiplicity W a b (hasFiniteHomology_of_artinian_quotient W a b) :=
  eulerMultiplicity_add_of_exact a b f g hf hg hex _ _ _

end Module.KoszulPair
