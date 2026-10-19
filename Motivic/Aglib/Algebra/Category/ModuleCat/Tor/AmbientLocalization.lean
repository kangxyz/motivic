/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.Ambient
public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.SurjectiveLocalization

/-!
# The actual prime-local ambient Tor comparison

Localization of the constructed ambient Tor comparison yields an isomorphism
of modules over the actual ambient local ring. For a surjective ambient map,
restriction of scalars commutes with localization of every coefficient module.
The restricted action uses the literal `Localization.localRingHom`. Only the
two factor maps are flat; neither the ambient quotient nor either input module
is assumed flat. A second formulation computes both sides using local Tor.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace ModuleCat.TorComparison

variable {k U V Q : Type u} [Field k] [CommRing U] [CommRing V] [CommRing Q]
  [Algebra k U] [Algebra k V]

/-- The actual ambient Tor comparison localized at corresponding primes,
with the full ambient local-ring action on both sides. -/
def primeLocalizedAmbientTorIso (μ : U ⊗[k] V →+* Q)
    (hμ : Function.Surjective μ)
    (hleft : (MixedBase.leftMap k U V Q μ).Flat)
    (hright : (MixedBase.rightMap k U V Q μ).Flat)
    (P : Ideal (U ⊗[k] V)) [P.IsPrime] (q : Ideal Q) [q.IsPrime]
    (hPq : P = q.comap μ) (M : ModuleCat.{u} U) (N : ModuleCat.{u} V) (n : ℕ) :
    ModuleCat.of (Localization.AtPrime P)
      (LocalizedModule P.primeCompl
        (((Tor (ModuleCat (U ⊗[k] V)) n).obj (ExteriorModule.obj k U V M N)).obj
          ((ModuleCat.restrictScalars μ).obj (ModuleCat.of Q Q)))) ≅
      (ModuleCat.restrictScalars (Localization.localRingHom P q μ hPq)).obj
        (ModuleCat.of (Localization.AtPrime q)
          (LocalizedModule q.primeCompl
            (((Tor (ModuleCat Q) n).obj
              ((ModuleCat.extendScalars (MixedBase.leftMap k U V Q μ)).obj M)).obj
                ((ModuleCat.extendScalars (MixedBase.rightMap k U V Q μ)).obj N)))) :=
  localizedModuleExtendScalarsIso P.primeCompl _ ≪≫
    (ModuleCat.extendScalars (algebraMap (U ⊗[k] V) (Localization.AtPrime P))).mapIso
      (ambientTorIso μ hleft hright M N n) ≪≫
    (localizedModuleExtendScalarsIso P.primeCompl _).symm ≪≫
    surjectivePrimeLocalizedModuleIso μ hμ P q hPq _

/-- Computing the comparison with actual local Tor modules on both sides.
The quotient local-ring restriction is constructed rather than hypothesized. -/
def ambientPrimeTorIso (μ : U ⊗[k] V →+* Q)
    (hμ : Function.Surjective μ)
    (hleft : (MixedBase.leftMap k U V Q μ).Flat)
    (hright : (MixedBase.rightMap k U V Q μ).Flat)
    (P : Ideal (U ⊗[k] V)) [P.IsPrime] (q : Ideal Q) [q.IsPrime]
    (hPq : P = q.comap μ) (M : ModuleCat.{u} U) (N : ModuleCat.{u} V) (n : ℕ) :
    ((Tor (ModuleCat (Localization.AtPrime P)) n).obj
      (ModuleCat.of (Localization.AtPrime P)
        (LocalizedModule P.primeCompl (ExteriorModule.obj k U V M N)))).obj
      (ModuleCat.of (Localization.AtPrime P)
        (LocalizedModule P.primeCompl
          ((ModuleCat.restrictScalars μ).obj (ModuleCat.of Q Q)))) ≅
      (ModuleCat.restrictScalars (Localization.localRingHom P q μ hPq)).obj
        (((Tor (ModuleCat (Localization.AtPrime q)) n).obj
          (ModuleCat.of (Localization.AtPrime q)
            (LocalizedModule q.primeCompl
              ((ModuleCat.extendScalars (MixedBase.leftMap k U V Q μ)).obj M)))).obj
          (ModuleCat.of (Localization.AtPrime q)
            (LocalizedModule q.primeCompl
              ((ModuleCat.extendScalars (MixedBase.rightMap k U V Q μ)).obj N)))) :=
  (primeLocalizedTorIso P _ _ n).symm ≪≫
    primeLocalizedAmbientTorIso μ hμ hleft hright P q hPq M N n ≪≫
    (ModuleCat.restrictScalars (Localization.localRingHom P q μ hPq)).mapIso
      (primeLocalizedTorIso q _ _ n)

end ModuleCat.TorComparison
