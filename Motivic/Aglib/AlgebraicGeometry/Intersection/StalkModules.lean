/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.FiniteSupport.Euler
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# The actual two stalk modules of a closed intersection

For two closed immersions and points with the same ambient image, the source
and coefficient objects below are the actual stalks, with scalars induced by
the literal stalk maps. Equality of the two ambient points supplies only the
necessary stalk transport. Surjectivity proves finite generation, and the
coefficient annihilator is proved equal to its actual stalk-map kernel.
A regular list for the first literal kernel computes categorical Tor of these
two actual modules by the already constructed finite Koszul resolution.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace AlgebraicGeometry.Scheme.Intersection

variable {D T P : Scheme.{u}} (i : D ⟶ P) (d : D)

/-- The actual ambient local ring at the image of the first source point. -/
abbrev ambientStalk := P.presheaf.stalk (i d)

/-- The actual first source stalk, acted on by the actual ambient stalk map. -/
def sourceStalkModule : ModuleCat (ambientStalk i d) :=
  let := (i.stalkMap d).hom.toAlgebra
  ModuleCat.of (ambientStalk i d) (D.presheaf.stalk d)

variable (j : T ⟶ P) (t : T) (hp : i d = j t)

/-- The actual second stalk map, transported between the equal ambient points. -/
def coefficientStalkMap : ambientStalk i d ⟶ T.presheaf.stalk t :=
  (P.presheaf.stalkCongr (.of_eq hp)).hom ≫ j.stalkMap t

/-- The actual coefficient stalk with scalars through its transported stalk map. -/
def coefficientStalkModule : ModuleCat (ambientStalk i d) :=
  let := (coefficientStalkMap i d j t hp).hom.toAlgebra
  ModuleCat.of (ambientStalk i d) (T.presheaf.stalk t)

/-- The coefficient annihilator is exactly the literal transported stalk-map kernel. -/
theorem coefficientStalkModule_annihilator :
    Module.annihilator (ambientStalk i d) (coefficientStalkModule i d j t hp) =
      RingHom.ker (coefficientStalkMap i d j t hp).hom := by
  let := (coefficientStalkMap i d j t hp).hom.toAlgebra
  change Module.annihilator (ambientStalk i d) (T.presheaf.stalk t) = _
  ext r
  rw [Module.mem_annihilator, RingHom.mem_ker]
  change (∀ m : T.presheaf.stalk t, (coefficientStalkMap i d j t hp) r * m = 0) ↔ _
  constructor
  · intro hr
    simpa using hr 1
  · intro hr m
    rw [hr, zero_mul]

section CoefficientClosed

variable [IsClosedImmersion j]

/-- Closed-stalk surjectivity survives the equality transport of ambient points. -/
theorem coefficientStalkMap_surjective :
    Function.Surjective (coefficientStalkMap i d j t hp) :=
  (j.stalkMap_surjective t).comp
    (ConcreteCategory.bijective_of_isIso (P.presheaf.stalkCongr (.of_eq hp)).hom).2

/-- The actual coefficient stalk is a finite ambient module by closed-stalk surjectivity. -/
instance coefficientStalkModule_finite :
    Module.Finite (ambientStalk i d) (coefficientStalkModule i d j t hp) := by
  let := (coefficientStalkMap i d j t hp).hom.toAlgebra
  exact Module.Finite.of_surjective (Algebra.linearMap (ambientStalk i d) (T.presheaf.stalk t))
    (coefficientStalkMap_surjective i d j t hp)

end CoefficientClosed

variable [IsClosedImmersion i]

/-- The actual first source stalk is a finite ambient module. -/
instance sourceStalkModule_finite : Module.Finite (ambientStalk i d) (sourceStalkModule i d) := by
  let := (i.stalkMap d).hom.toAlgebra
  exact Module.Finite.of_surjective (Algebra.linearMap (ambientStalk i d) (D.presheaf.stalk d))
    (i.stalkMap_surjective d)

variable (s : List (ambientStalk i d))
  (hker : RingHom.ker (i.stalkMap d).hom = Ideal.ofList s)

set_option backward.isDefEq.respectTransparency false in
/-- The quotient by equations for the literal kernel is the actual first source stalk module. -/
def quotientStalkIso :
    ModuleCat.of (ambientStalk i d) ((ambientStalk i d) ⧸ Ideal.ofList s) ≅
      sourceStalkModule i d := by
  let := (i.stalkMap d).hom.toAlgebra
  let μ : ambientStalk i d →ₐ[ambientStalk i d] D.presheaf.stalk d := Algebra.ofId _ _
  have hμ : Function.Surjective μ := i.stalkMap_surjective d
  have hk : Ideal.ofList s = RingHom.ker μ := hker.symm
  exact ((Ideal.quotientEquivAlgOfEq (ambientStalk i d) hk).trans
    (Ideal.quotientKerAlgEquivOfSurjective hμ)).toLinearEquiv.toModuleIso

/-- The quotient comparison is induced by the actual source stalk map. -/
@[simp]
theorem quotientStalkIso_mk (r : ambientStalk i d) :
    (quotientStalkIso i d s hker).hom (Ideal.Quotient.mk (Ideal.ofList s) r) =
      i.stalkMap d r := rfl

variable (hs : IsRegular (ambientStalk i d) s)

/-- Categorical Tor of the actual two stalk modules is coefficient Koszul homology. -/
def torIsoHomology (n : ℕ) :
    ((Tor (ModuleCat (ambientStalk i d)) n).obj (coefficientStalkModule i d j t hp)).obj
        (sourceStalkModule i d) ≅
      (_root_.ChainComplex.Koszul.coefficientComplex (coefficientStalkModule i d j t hp) s).homology
          n :=
  ((Tor (ModuleCat (ambientStalk i d)) n).obj (coefficientStalkModule i d j t hp)).mapIso
      (quotientStalkIso i d s hker).symm ≪≫
    _root_.ChainComplex.Koszul.finiteTorIsoHomology (coefficientStalkModule i d j t hp) s
        hs.toIsWeaklyRegular n

include hker hs in
/-- All genuine higher Tor above the ambient regular-list length vanish. -/
theorem isZero_tor_above_length (n : ℕ) (hn : s.length < n) :
    IsZero (((Tor (ModuleCat (ambientStalk i d)) n).obj
      (coefficientStalkModule i d j t hp)).obj (sourceStalkModule i d)) :=
  (HomologicalComplex.ExactAt.of_isZero
    (_root_.ChainComplex.Koszul.coefficient_isZero_X (coefficientStalkModule i d j t hp) s n
        hn)).isZero_homology.of_iso
      (torIsoHomology i d j t hp s hker hs n)

include hker hs in
/-- Both actual closed-stalk kernels annihilate every categorical Tor degree. -/
theorem support_le_annihilator_tor (n : ℕ) :
    RingHom.ker (i.stalkMap d).hom ⊔ RingHom.ker (coefficientStalkMap i d j t hp).hom ≤
      Module.annihilator (ambientStalk i d)
        (((Tor (ModuleCat (ambientStalk i d)) n).obj
          (coefficientStalkModule i d j t hp)).obj (sourceStalkModule i d)) := by
  rw [hker, ← coefficientStalkModule_annihilator i d j t hp]
  exact (_root_.ChainComplex.Koszul.support_le_annihilator_coefficient_homology
    (coefficientStalkModule i d j t hp) s n).trans
    ((torIsoHomology i d j t hp s hker hs n).hom.hom.annihilator_le_of_injective
      ((ModuleCat.mono_iff_injective _).mp inferInstance))

end AlgebraicGeometry.Scheme.Intersection
