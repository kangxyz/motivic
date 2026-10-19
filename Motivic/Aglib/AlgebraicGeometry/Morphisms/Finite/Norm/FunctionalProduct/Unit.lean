/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.FunctionalProduct.UnitDomain
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.RetainedUnitDomain
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberFunctionalNormProduct
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Flat.FreeCartesianOpen
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.RationalUnitGluing
/-! # Original functional norm products on the exact good open

Local units are computed from the original functionals. The required inverses
are consequences of membership in the fixed good open, not additional chart
hypotheses. The whole finite source is used in every chart.

Intended upstream module:
`Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.FunctionalProduct.Unit`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Correction.NormalizedUnit`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme

variable {C T : Scheme.{u}} (f : C ⟶ T) [IsFinite f]
  (N : LineBundle C) (n d : N.val ⟶ SheafOfModules.unit C.ringCatSheaf)
  (L : LineBundle T) (a c : L.val ⟶ SheafOfModules.unit T.ringCatSheaf)

/-- The original retained triangle and full marked square prove boundary
containment in V from the original boundary-unit sections. No full-inverse
support condition is added as an independent normalization hypothesis. -/
theorem range_subset_functionalNormProductUnitDomain_of_retainedBoundary
    {E Y D Z I W : Scheme.{u}} (j : Y ⟶ C) (d₀ : D ⟶ C)
    (hd₀ : Set.range d₀ = (Set.range j)ᶜ)
    (z : Z ⟶ T) (s : Z ⟶ Y)
    (H : IsPullback s (𝟙 Z) (j ≫ f) z)
    (i : I ⟶ T) (p : Y ⟶ W) (k : W ⟶ T)
    (hp : p ≫ k = j ≫ f) (hi : Disjoint (Set.range k) (Set.range i))
    (b : E ⟶ T) (hb : Set.range b ⊆ Set.range i ∪ Set.range z)
    [IsIso ((Modules.pullback b).map a)] [IsIso ((Modules.pullback b).map c)]
    [IsIso ((Modules.pullback d₀).map n)]
    [IsIso ((Modules.pullback (s ≫ j)).map n)]
    [IsIso ((Modules.pullback d₀).map d)]
    [IsIso ((Modules.pullback (s ≫ j)).map d)] :
    Set.range b ⊆ (functionalNormProductUnitDomain f N N n d L L a c : Set T) := by
  apply range_subset_functionalNormProductUnitDomain f N N n d L L a c b
  · intro x hx
    rcases preimage_fullBoundary_subset_retainedBoundary f j d₀ hd₀ z s H i p k hp hi
      (hb hx) with hx | hx
    · exact range_subset_zeroSupportUnitOpen_of_pullback_isIso N n d₀ hx
    · exact range_subset_zeroSupportUnitOpen_of_pullback_isIso N n (s ≫ j) hx
  · intro x hx
    rcases preimage_fullBoundary_subset_retainedBoundary f j d₀ hd₀ z s H i p k hp hi
      (hb hx) with hx | hx
    · exact range_subset_zeroSupportUnitOpen_of_pullback_isIso N d d₀ hx
    · exact range_subset_zeroSupportUnitOpen_of_pullback_isIso N d (s ≫ j) hx

/-- The literal target quotient times the whole source norm on a chart of V. -/
def functionalNormProductChart (U : T.Opens) (hU : IsAffineOpen U)
    (hUV : U ≤ functionalNormProductUnitDomain f N N n d L L a c) : Γ(T, U) := by
  have ht := functionalNormProductUnitDomain_target_isIso f N N n d L L a c U.ι
    (by rw [Opens.range_ι]; exact fun _ hx => hUV hx)
  have hs := functionalNormProductUnitDomain_source_isIso f N N n d L L a c hU.fromSpec
    (by rw [hU.range_fromSpec]; exact hUV)
  letI := ht.1
  letI := ht.2
  letI := hs.1
  letI := hs.2
  letI : Algebra Γ(T, U) Γ(pullback f hU.fromSpec, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f hU.fromSpec)).toAlgebra
  exact U.topIso.hom (Modules.Hom.app
    (inv (pullbackUnitMap U.ι c) ≫ pullbackUnitMap U.ι a) ⊤ (1 : Γ(U.toScheme, ⊤))) *
      Algebra.norm Γ(T, U) (show Γ(pullback f hU.fromSpec, ⊤) from Modules.Hom.app
        (inv (pullbackUnitMap (pullback.fst f hU.fromSpec) d) ≫
          pullbackUnitMap (pullback.fst f hU.fromSpec) n) ⊤
          (1 : Γ(pullback f hU.fromSpec, ⊤)))

/-- No chart-unit or germ identity is assumed: both follow for the literal product. -/
theorem functionalNormProductChart_unit_and_germ
    [IsIntegral T] [Mono n] [Mono d] [Mono a] [Mono c]
    (U : T.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hUV : U ≤ functionalNormProductUnitDomain f N N n d L L a c) :
    let : Algebra Γ(T, U) Γ(pullback f hU.fromSpec, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f hU.fromSpec)).toAlgebra
    ∀ [Module.Free Γ(T, U) Γ(pullback f hU.fromSpec, ⊤)],
      IsUnit (functionalNormProductChart f N n d L a c U hU hUV) ∧
      T.germToFunctionField U (functionalNormProductChart f N n d L a c U hU hUV) =
        genericFiberLineRatioNorm (𝟙 T) L a c * genericFiberLineRatioNorm f N n d := by
  have ht := functionalNormProductUnitDomain_target_isIso f N N n d L L a c U.ι
    (by rw [Opens.range_ι]; exact fun _ hx => hUV hx)
  have hs := functionalNormProductUnitDomain_source_isIso f N N n d L L a c hU.fromSpec
    (by rw [hU.range_fromSpec]; exact hUV)
  let := ht.1
  let := ht.2
  let := hs.1
  let := hs.2
  let : Algebra Γ(T, U) Γ(pullback f hU.fromSpec, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f hU.fromSpec)).toAlgebra
  dsimp only
  intro hfree
  let := hfree
  exact genericFiberFunctionalNormProduct_unit_and_germ f N n d L a c U hU

/-- A global representative of the original germ restricts to the literal product
on every nonempty free chart in the same good open. -/
theorem functionalNormProductUnit_restrict
    [IsIntegral T] [Mono n] [Mono d] [Mono a] [Mono c]
    [Nonempty (functionalNormProductUnitDomain f N N n d L L a c)]
    (r : Γ(T, functionalNormProductUnitDomain f N N n d L L a c))
    (hr : T.germToFunctionField (functionalNormProductUnitDomain f N N n d L L a c) r =
      genericFiberLineRatioNorm (𝟙 T) L a c * genericFiberLineRatioNorm f N n d)
    (U : T.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hUV : U ≤ functionalNormProductUnitDomain f N N n d L L a c) :
    let : Algebra Γ(T, U) Γ(pullback f hU.fromSpec, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f hU.fromSpec)).toAlgebra
    ∀ [Module.Free Γ(T, U) Γ(pullback f hU.fromSpec, ⊤)],
      T.presheaf.map (homOfLE hUV).op r =
        functionalNormProductChart f N n d L a c U hU hUV := by
  let : Algebra Γ(T, U) Γ(pullback f hU.fromSpec, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f hU.fromSpec)).toAlgebra
  dsimp only
  intro hfree
  let := hfree
  apply T.germToFunctionField_injective U
  have hg := (functionalNormProductChart_unit_and_germ f N n d L a c U hU hUV).2
  change T.presheaf.germ _ _ _ (T.presheaf.map _ r) = _
  rw [T.presheaf.germ_res_apply]
  exact hr.trans hg.symm

/-- Original free charts produce a global unit on the exact good open. This
statement does not yet assert the correction boundary value: that is a separate
scheme-level calculation, not an assumption used to manufacture the unit. -/
theorem exists_functionalNormProductUnit_of_free_charts
    [IsIntegral T] [Mono n] [Mono d] [Mono a] [Mono c]
    {C₀ T₀ : Scheme.{u}} (f₀ : C₀ ⟶ T₀) [IsFinite f₀]
    (v : C ⟶ C₀) (b : T ⟶ T₀) (H : IsPullback v f f₀ b)
    {ι : Type u} (A : ι → CommRingCat.{u}) (w : ∀ i, Spec (A i) ⟶ T₀)
    [∀ i, IsOpenImmersion (w i)]
    (hcover : ∀ t : T₀, ∃ i, t ∈ Set.range (w i))
    (hfree : ∀ i,
      let : Algebra (A i) Γ(pullback f₀ (w i), ⊤) :=
        (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f₀ (w i))).toAlgebra
      Module.Free (A i) Γ(pullback f₀ (w i), ⊤))
    [Nonempty (functionalNormProductUnitDomain f N N n d L L a c)] :
    ∃ r : Γ(T, functionalNormProductUnitDomain f N N n d L L a c), IsUnit r ∧
      T.germToFunctionField (functionalNormProductUnitDomain f N N n d L L a c) r =
        genericFiberLineRatioNorm (𝟙 T) L a c * genericFiberLineRatioNorm f N n d := by
  let V := functionalNormProductUnitDomain f N N n d L L a c
  choose U hU hxU hUV hfreeU using fun x : V =>
    FiniteSchemeNormBaseChange.exists_free_affine_neighborhood_subset_of_isPullback
      f₀ f v b H A w hcover hfree V x.1 x.2
  have hunion : iSup U = V := by
    apply le_antisymm
    · exact iSup_le hUV
    · intro x hx
      exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  let (x : V) : Nonempty (U x) := ⟨⟨x.1, hxU x⟩⟩
  let s (x : V) := functionalNormProductChart f N n d L a c (U x) (hU x) (hUV x)
  let R := genericFiberLineRatioNorm (𝟙 T) L a c * genericFiberLineRatioNorm f N n d
  have hs (x : V) : IsUnit (s x) ∧ T.germToFunctionField (U x) (s x) = R := by
    let : Algebra Γ(T, U x) Γ(pullback f (hU x).fromSpec, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f (hU x).fromSpec)).toAlgebra
    let := hfreeU x
    exact functionalNormProductChart_unit_and_germ f N n d L a c (U x) (hU x) (hUV x)
  have : Nonempty (iSup U : T.Opens) := hunion.symm ▸ (inferInstance : Nonempty V)
  obtain ⟨r, _, _, hunit, hrat, _, _⟩ :=
    exists_rationalUnit_boundary_gluing (Scheme.emptyTo T) U R s
      (fun x => (hs x).1) (fun x => (hs x).2)
      (fun _ => Subsingleton.elim _ _)
      (by rintro _ ⟨x, _⟩; exact isEmptyElim x)
  change ∃ r : Γ(T, V), IsUnit r ∧ T.germToFunctionField V r = R
  have result : ∀ W : T.Opens, W = iSup U → ∀ [Nonempty W],
      ∃ r : Γ(T, W), IsUnit r ∧ T.germToFunctionField W r = R := by
    rintro W rfl hW
    exact ⟨r, hunit, hrat⟩
  exact result V hunion.symm

end AlgebraicGeometry.Scheme
