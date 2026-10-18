/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulExteriorCoefficientComparison
public import Motivic.Algebra.Homology.TorComparison.QuotientCoefficientExtension
public import Motivic.Algebra.Homology.TorComparison.AmbientLength
public import Mathlib.RingTheory.LocalRing.Length

/-!
# Literal flat local multiplicity of coefficient Koszul homology

A flat local map on the actual coefficient rings transports the same equation
list and every homology degree. Surjective ambient actions can then be removed
without changing length. The actual local closed fiber remains a factor;
regularity, genericity, finite length and reducedness are not hypotheses of the
extended-natural length identity.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace Motivic.Koszul

variable {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]

/-- Extension of the literal regular module is the target regular module. -/
def extendScalarsRegularIso (g : A →+* B) :
    (ModuleCat.extendScalars g).obj (ModuleCat.of A A) ≅ ModuleCat.of B B := by
  letI := g.toAlgebra
  exact TorComparison.extendScalarsTensorIso g (ModuleCat.of A A) ≪≫
    (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso

/-- Flat extension carries actual regular-coefficient homology to the homology
of the literal image list, with its target coefficient-ring action. -/
def regularCoefficientFlatHomologyIso (g : A →+* B) (hg : g.Flat)
    (s : List A) (n : ℕ) :
    (ModuleCat.extendScalars g).obj
        ((coefficientComplex (ModuleCat.of A A) s).homology n) ≅
      (coefficientComplex (ModuleCat.of B B) (s.map g)).homology n :=
  TorComparison.flatExtendHomologyIso g hg _ n ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat B) (ComplexShape.down ℕ) n).mapIso
      (coefficientExtendIso g (ModuleCat.of A A) s ≪≫
        (coefficientFunctor (s.map g)).mapIso (extendScalarsRegularIso g))

/-- A literal surjective coefficient action preserves actual homology length. -/
theorem coordinateHomology_length (σ : R →+* A) (hσ : Function.Surjective σ)
    (s : List R) (n : ℕ) :
    Module.length R ((coefficientComplex
        ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A)) s).homology n) =
      Module.length A ((coefficientComplex (ModuleCat.of A A) (s.map σ)).homology n) :=
  (coefficientRestrictHomologyIso σ (ModuleCat.of A A) s n).toLinearEquiv.length_eq.trans
    (TorComparison.length_restrictScalars_of_surjective σ hσ _)

/-- The actual closed fiber of the specified local coefficient-ring map. -/
abbrev coefficientClosedFiber (g : A →+* B) [IsLocalRing A] :=
  B ⧸ (IsLocalRing.maximalIdeal A).map g

/-- Flat local base change multiplies each actual homology length by the
length of its actual, possibly nonreduced, closed fiber. -/
theorem regularCoefficientFlat_length [IsLocalRing A] [IsLocalRing B]
    (g : A →+* B) [IsLocalHom g] (hg : g.Flat) (s : List A) (n : ℕ) :
    Module.length B ((coefficientComplex (ModuleCat.of B B) (s.map g)).homology n) =
      Module.length A ((coefficientComplex (ModuleCat.of A A) s).homology n) *
        Module.length B (coefficientClosedFiber g) := by
  let := g.toAlgebra
  have : Module.Flat A B := hg
  rw [← (regularCoefficientFlatHomologyIso g hg s n).toLinearEquiv.length_eq,
    (TorComparison.extendScalarsTensorIso g _).toLinearEquiv.length_eq]
  exact IsLocalRing.length_baseChange A B _

/-- The two literal ambient presentations use a proved common coefficient
list. Their all-degree length comparison retains the actual local fiber. -/
theorem coordinateFlatLocalHomology_length [IsLocalRing A] [IsLocalRing B]
    (σ : R →+* A) (hσ : Function.Surjective σ)
    (τ : S →+* B) (hτ : Function.Surjective τ)
    (g : A →+* B) [IsLocalHom g] (hg : g.Flat)
    (s : List R) (t : List S) (hst : t.map τ = (s.map σ).map g) (n : ℕ) :
    Module.length S ((coefficientComplex
        ((ModuleCat.restrictScalars τ).obj (ModuleCat.of B B)) t).homology n) =
      Module.length R ((coefficientComplex
        ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A)) s).homology n) *
          Module.length B (coefficientClosedFiber g) := by
  rw [coordinateHomology_length τ hτ, coordinateHomology_length σ hσ, hst]
  exact regularCoefficientFlat_length g hg (s.map σ) n

end Motivic.Koszul


namespace Module

variable {A B R S : Type u} [CommRing A] [CommRing B] [CommRing R] [CommRing S]
  [IsLocalRing A] [IsLocalRing R]
  (σ : A →+* R) (hσ : Function.Surjective σ)
  (τ : B →+* S) (hτ : Function.Surjective τ)
  (g : A →+* B) (f : R →+* S) (hcomm : f.comp σ = τ.comp g)
  (hker : RingHom.ker τ = (RingHom.ker σ).map g)

include hσ hcomm in
/-- A Cartesian quotient square sends the actual coefficient closed-fiber
ideal onto the actual support closed-fiber ideal. -/
theorem closedFiberIdeal_map :
    ((IsLocalRing.maximalIdeal A).map g).map τ =
      (IsLocalRing.maximalIdeal R).map f := by
  rw [← IsLocalRing.map_maximalIdeal_of_surjective σ hσ, Ideal.map_map,
    Ideal.map_map, hcomm]

include hσ hτ hcomm hker in
/-- The complete coefficient closed-fiber ideal is the inverse image of the
support closed-fiber ideal, using the literal Cartesian kernel equality. -/
theorem closedFiberIdeal_comap :
    ((IsLocalRing.maximalIdeal R).map f).comap τ =
      (IsLocalRing.maximalIdeal A).map g := by
  rw [← closedFiberIdeal_map σ hσ τ g f hcomm,
    Ideal.comap_map_of_surjective τ hτ, ← RingHom.ker_eq_comap_bot,
    sup_eq_left, hker]
  exact Ideal.map_mono (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top σ))

/-- The actual two closed fibers are compared by the literal quotient map
induced by the support-stalk quotient, retaining all nilpotents. -/
def closedFiberQuotientEquiv :
    Motivic.Koszul.coefficientClosedFiber g ≃+* Motivic.Koszul.coefficientClosedFiber f :=
  RingEquiv.ofBijective
    (Ideal.quotientMap ((IsLocalRing.maximalIdeal R).map f) τ
      (closedFiberIdeal_comap σ hσ τ hτ g f hcomm hker).ge)
    ⟨Ideal.quotientMap_injective'
      (closedFiberIdeal_comap σ hσ τ hτ g f hcomm hker).le,
      Ideal.quotientMap_surjective hτ⟩

/-- The ring comparison is induced by the original support quotient on numerators. -/
@[simp] theorem closedFiberQuotientEquiv_mk (b : B) :
    closedFiberQuotientEquiv σ hσ τ hτ g f hcomm hker
      (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ (τ b) := rfl

/-- The closed-fiber comparison preserves the actual coefficient-ring scalar
map, not merely the abstract quotient rings. -/
def closedFiberQuotientModuleIso :
    ModuleCat.of B (Motivic.Koszul.coefficientClosedFiber g) ≅
      (ModuleCat.restrictScalars τ).obj
        (ModuleCat.of S (Motivic.Koszul.coefficientClosedFiber f)) := by
  let e := closedFiberQuotientEquiv σ hσ τ hτ g f hcomm hker
  let N := (ModuleCat.restrictScalars τ).obj
    (ModuleCat.of S (Motivic.Koszul.coefficientClosedFiber f))
  let l : ModuleCat.of B (Motivic.Koszul.coefficientClosedFiber g) ≃ₗ[B] N :=
    { e.toAddEquiv with
      map_smul' := by
        intro b x
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
        change e (Ideal.Quotient.mk _ (b * c)) =
          Ideal.Quotient.mk _ (τ b * τ c)
        simp only [e, closedFiberQuotientEquiv_mk, map_mul] }
  exact l.toModuleIso

include hσ hτ hcomm hker in
/-- Closed-fiber lengths agree under the actual Cartesian quotient square;
surjectivity compares their different original scalar rings. -/
theorem closedFiberQuotient_length :
    Module.length B (Motivic.Koszul.coefficientClosedFiber g) =
      Module.length S (Motivic.Koszul.coefficientClosedFiber f) :=
  (closedFiberQuotientModuleIso σ hσ τ hτ g f hcomm hker).toLinearEquiv.length_eq.trans
    (Motivic.TorComparison.length_restrictScalars_of_surjective τ hτ _)

end Module
