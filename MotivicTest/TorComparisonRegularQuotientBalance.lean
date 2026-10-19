/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.RegularQuotientBalance
public import Motivic.Aglib.AlgebraicGeometry.Intersection.StalkModules

/-! Consumers of the genuine regular-quotient balancing theorem and its two augmentations. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open _root_.ChainComplex.Koszul _root_.ModuleCat.TorComparison

universe u

namespace Motivic.MotivicTest.TorComparisonRegularQuotientBalance
open _root_.AlgebraicGeometry.Scheme

variable {R : Type u} [CommRing R]

/-- Both sides are the actual one-sided categorical Tor, in opposite argument orders. -/
def arbitraryCoefficient (M : ModuleCat.{u} R) (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (n : ℕ) :
    ((Tor (ModuleCat R) n).obj M).obj (ModuleCat.of R (R ⧸ Ideal.ofList s)) ≅
      ((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ Ideal.ofList s))).obj M :=
  regularQuotientTorIso M s hs n

/-- The other support ideal has no regularity or flatness hypothesis. -/
def arbitrarySupportIdeal (I : Ideal R) (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (n : ℕ) :
    ((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ I))).obj
        (ModuleCat.of R (R ⧸ Ideal.ofList s)) ≅
      ((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ Ideal.ofList s))).obj
        (ModuleCat.of R (R ⧸ I)) :=
  regularQuotientTorIso _ s hs n

/-- The empty regular list is covered without a nonempty-list assumption. -/
def emptyList (M : ModuleCat.{u} R) (n : ℕ) :
    ((Tor (ModuleCat R) n).obj M).obj (ModuleCat.of R (R ⧸ Ideal.ofList ([] : List R))) ≅
      ((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ Ideal.ofList ([] : List R)))).obj M :=
  regularQuotientTorIso M [] (RingTheory.Sequence.IsWeaklyRegular.nil R R) n

/-- No bound on the coefficient's genuine projective resolution is supplied. -/
theorem actualResolutionAugmentation (M : ModuleCat.{u} R)
    (P : ProjectiveResolution M) (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) :
    QuasiIso (koszulResolutionTensor s P.complex) :=
  projectiveResolutionTensor_quasiIso M P s hs

/-- The augmentation target is the actual quotient-ring tensor complex. -/
def actualResolutionHomology (M : ModuleCat.{u} R)
    (P : ProjectiveResolution M) (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (n : ℕ) :
    (HomologicalComplex.tensorObj (chainComplex s) P.complex).homology n ≅
      (mappedComplex ((tensoringLeft (ModuleCat R)).obj
        (ModuleCat.of R (R ⧸ Ideal.ofList s))) P.complex).homology n :=
  projectiveResolutionTensorHomologyIso M P s hs n

/-- Flat-module regularity is proved on the full successive ideal quotients. -/
theorem flatTerms (M : ModuleCat.{u} R) [Module.Flat R M] (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) :
    RingTheory.Sequence.IsWeaklyRegular M s :=
  weaklyRegular_of_flat_module M s hs

/-- Literal closed-stalk scalar actions are retained when the regular source
stalk is moved from the resolved argument to the coefficient argument. -/
def actualClosedStalks {D T P : AlgebraicGeometry.Scheme.{u}}
    (i : D ⟶ P) (d : D) (j : T ⟶ P) (t : T) (hp : i d = j t)
    [AlgebraicGeometry.IsClosedImmersion i]
    (s : List (Intersection.ambientStalk i d))
    (hker : RingHom.ker (i.stalkMap d).hom = Ideal.ofList s)
    (hs : RingTheory.Sequence.IsWeaklyRegular (Intersection.ambientStalk i d) s) (n : ℕ) :
    ((Tor (ModuleCat (Intersection.ambientStalk i d)) n).obj
      (Intersection.coefficientStalkModule i d j t hp)).obj (Intersection.sourceStalkModule i d) ≅
    ((Tor (ModuleCat (Intersection.ambientStalk i d)) n).obj
      (Intersection.sourceStalkModule i d)).obj (Intersection.coefficientStalkModule i d j t hp) :=
  ((Tor (ModuleCat (Intersection.ambientStalk i d)) n).obj
      (Intersection.coefficientStalkModule i d j t hp)).mapIso
      (Intersection.quotientStalkIso i d s hker).symm ≪≫
    regularQuotientTorIso (Intersection.coefficientStalkModule i d j t hp) s hs n ≪≫
    ((Tor (ModuleCat (Intersection.ambientStalk i d)) n).mapIso
      (Intersection.quotientStalkIso i d s hker)).app
        (Intersection.coefficientStalkModule i d j t hp)

end Motivic.MotivicTest.TorComparisonRegularQuotientBalance
