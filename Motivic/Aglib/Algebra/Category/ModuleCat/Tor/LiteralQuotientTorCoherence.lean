/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.FlatBaseChangeIdentity
public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.QuotientCoefficientCoherence

/-!
# Canonical flat Tor coherence for literal quotient coefficients

The canonical all-degree flat Tor comparison, followed by the actual quotient
coefficient identifications, respects scalar extension and image-ideal
associators. This is the ambient-linear equation underlying support restriction.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace ModuleCat.TorComparison

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- Actual categorical Tor functoriality in both coefficients, in coefficient-first order. -/
def torMapPair (n : ℕ) {M M' N N' : ModuleCat.{u} R} (a : M ⟶ M') (b : N ⟶ N') :
    (((Tor (ModuleCat R) n).obj M).obj N) ⟶ (((Tor (ModuleCat R) n).obj M').obj N') :=
  ((Tor (ModuleCat R) n).map a).app N ≫ ((Tor (ModuleCat R) n).obj M').map b

/-- The two-variable actual Tor map preserves composition. -/
@[reassoc] theorem torMapPair_comp (n : ℕ) {M M' M'' N N' N'' : ModuleCat.{u} R}
    (a : M ⟶ M') (a' : M' ⟶ M'') (b : N ⟶ N') (b' : N' ⟶ N'') :
    torMapPair n (a ≫ a') (b ≫ b') = torMapPair n a b ≫ torMapPair n a' b' := by
  simp only [torMapPair, Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [← NatTrans.naturality_assoc]

/-- The two-variable actual Tor map preserves identities. -/
@[simp] theorem torMapPair_id (n : ℕ) (M N : ModuleCat.{u} R) :
    torMapPair n (𝟙 M) (𝟙 N) = 𝟙 _ := by
  simp only [torMapPair, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

/-- The existing canonical flat Tor comparison is natural simultaneously in both modules. -/
@[reassoc] theorem flatBaseChangeTorIso_hom_naturality_pair (f : R →+* S) (hf : f.Flat)
    (n : ℕ) {M M' N N' : ModuleCat.{u} R} (a : M ⟶ M') (b : N ⟶ N') :
    (ModuleCat.extendScalars f).map (torMapPair n a b) ≫
        (flatBaseChangeTorIso f hf M' N' n).hom =
      (flatBaseChangeTorIso f hf M N n).hom ≫
        torMapPair n ((ModuleCat.extendScalars f).map a) ((ModuleCat.extendScalars f).map b) := by
  simp only [torMapPair, Functor.map_comp, Category.assoc]
  rw [flatBaseChangeTorIso_hom_naturality_right,
    flatBaseChangeTorIso_hom_naturality_left_assoc]

/-- Canonical flat Tor base change with both target coefficients identified literally. -/
def flatBaseChangeLiteralTorIso (f : R →+* S) (hf : f.Flat) (J K : Ideal R) (n : ℕ) :
    (ModuleCat.extendScalars f).obj
      (((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ K))).obj (ModuleCat.of R (R ⧸ J))) ≅
    (((Tor (ModuleCat S) n).obj (ModuleCat.of S (S ⧸ K.map f))).obj
      (ModuleCat.of S (S ⧸ J.map f))) :=
  flatBaseChangeTorIso f hf _ _ n ≪≫ extendedQuotientsTorIso f J K n

/-- Literal target Tor transport along the two actual composite-image quotient isomorphisms. -/
def mappedQuotientsTorCompIso (f : R →+* S) (g : S →+* T) (J K : Ideal R) (n : ℕ) :
    (((Tor (ModuleCat T) n).obj (ModuleCat.of T (T ⧸ (K.map f).map g))).obj
      (ModuleCat.of T (T ⧸ (J.map f).map g))) ≅
    (((Tor (ModuleCat T) n).obj (ModuleCat.of T (T ⧸ K.map (g.comp f)))).obj
      (ModuleCat.of T (T ⧸ J.map (g.comp f)))) :=
  ((Tor (ModuleCat T) n).mapIso (mappedQuotientCompIso f g K)).app _ ≪≫
    ((Tor (ModuleCat T) n).obj (ModuleCat.of T (T ⧸ K.map (g.comp f)))).mapIso
      (mappedQuotientCompIso f g J)

/-- Literal target Tor transport along the two actual identity-image quotient isomorphisms. -/
def mappedQuotientsTorIdIso (J K : Ideal R) (n : ℕ) :
    (((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ K.map (RingHom.id R)))).obj
      (ModuleCat.of R (R ⧸ J.map (RingHom.id R)))) ≅
    (((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ K))).obj (ModuleCat.of R (R ⧸ J))) :=
  ((Tor (ModuleCat R) n).mapIso (mappedQuotientIdIso K)).app _ ≪≫
    ((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ K))).mapIso (mappedQuotientIdIso J)

/-- The literal coefficient isomorphism is precisely the two-variable Tor map. -/
theorem extendedQuotientsTorIso_hom (f : R →+* S) (J K : Ideal R) (n : ℕ) :
    (extendedQuotientsTorIso f J K n).hom =
      torMapPair n (extendedIdealQuotientIso f K).hom (extendedIdealQuotientIso f J).hom := rfl

/-- The actual image-ideal composition transport is precisely the two-variable Tor map. -/
theorem mappedQuotientsTorCompIso_hom (f : R →+* S) (g : S →+* T)
    (J K : Ideal R) (n : ℕ) :
    (mappedQuotientsTorCompIso f g J K n).hom =
      torMapPair n (mappedQuotientCompIso f g K).hom (mappedQuotientCompIso f g J).hom := rfl

/-- The actual image-ideal identity transport is precisely the two-variable Tor map. -/
theorem mappedQuotientsTorIdIso_hom (J K : Ideal R) (n : ℕ) :
    (mappedQuotientsTorIdIso J K n).hom =
      torMapPair n (mappedQuotientIdIso K).hom (mappedQuotientIdIso J).hom := rfl

/-- The proven canonical composition law, bundled in two-variable Tor notation. -/
@[reassoc] theorem flatBaseChangeTorIso_hom_comp_pair (f : R →+* S) (g : S →+* T)
    (hf : f.Flat) (hg : g.Flat) (M N : ModuleCat.{u} R) (n : ℕ) :
    (ModuleCat.extendScalarsComp f g).hom.app (((Tor (ModuleCat R) n).obj M).obj N) ≫
        (ModuleCat.extendScalars g).map (flatBaseChangeTorIso f hf M N n).hom ≫
        (flatBaseChangeTorIso g hg ((ModuleCat.extendScalars f).obj M)
          ((ModuleCat.extendScalars f).obj N) n).hom =
      (flatBaseChangeTorIso (g.comp f) (hf.comp hg) M N n).hom ≫
        torMapPair n ((ModuleCat.extendScalarsComp f g).hom.app M)
          ((ModuleCat.extendScalarsComp f g).hom.app N) :=
  flatBaseChangeTorIso_hom_comp f g hf hg M N n

/-- Canonical flat Tor with literal quotient coefficients obeys the scalar composition law. -/
theorem flatBaseChangeLiteralTorIso_hom_comp (f : R →+* S) (g : S →+* T)
    (hf : f.Flat) (hg : g.Flat) (J K : Ideal R) (n : ℕ) :
    (ModuleCat.extendScalarsComp f g).hom.app
        (((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ K))).obj
          (ModuleCat.of R (R ⧸ J))) ≫
      (ModuleCat.extendScalars g).map (flatBaseChangeLiteralTorIso f hf J K n).hom ≫
      (flatBaseChangeLiteralTorIso g hg (J.map f) (K.map f) n).hom ≫
      (mappedQuotientsTorCompIso f g J K n).hom =
    (flatBaseChangeLiteralTorIso (g.comp f) (hf.comp hg) J K n).hom := by
  simp only [flatBaseChangeLiteralTorIso, Iso.trans_hom, extendedQuotientsTorIso_hom,
    mappedQuotientsTorCompIso_hom, Functor.map_comp, Category.assoc]
  rw [flatBaseChangeTorIso_hom_naturality_pair_assoc,
    flatBaseChangeTorIso_hom_comp_pair_assoc]
  rw [← torMapPair_comp, ← torMapPair_comp, ← torMapPair_comp]
  simp only [extendedIdealQuotientIso_hom_comp]

/-- Canonical flat Tor with literal quotient coefficients obeys the scalar identity law. -/
theorem flatBaseChangeLiteralTorIso_hom_id (J K : Ideal R) (n : ℕ) :
    (flatBaseChangeLiteralTorIso (RingHom.id R) (RingHom.Flat.id R) J K n).hom ≫
      (mappedQuotientsTorIdIso J K n).hom =
    (ModuleCat.extendScalarsId R).hom.app
      (((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ K))).obj
        (ModuleCat.of R (R ⧸ J))) := by
  simp only [flatBaseChangeLiteralTorIso, Iso.trans_hom, extendedQuotientsTorIso_hom,
    mappedQuotientsTorIdIso_hom, Category.assoc]
  rw [← torMapPair_comp, extendedIdealQuotientIso_hom_id, extendedIdealQuotientIso_hom_id]
  exact flatBaseChangeTorIso_hom_id _ _ _

end ModuleCat.TorComparison
