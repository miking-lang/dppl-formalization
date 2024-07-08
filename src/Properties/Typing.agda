module Properties.Typing (ℝ : Set) where

-- Lemmas purely about typing

open import Lib.Prelude
open import Lib.Unfinite
open import Lib.oc-Sets
open import Lib.LocalClosedness
open import Lib.Freshness
open import Lib.FunExt
open import Lib.BindingSignature

open import Function using (_$_ ; const ; flip)
open import Data.List using (_++_)

open import Syntax ℝ
open import Typing ℝ
open import Properties.Util

infixl 5 _&_
_&_ : TyEnv → TyEnv → TyEnv
_&_ = flip _++_

sub-refl : ∀ {T} → T <: T
sub-refl {treal c} = sreal ≤refl
sub-refl {T ⇒[ x ] T₁} = sarr sub-refl sub-refl ≤refl
sub-refl {ttup ts} = stup (λ i → sub-refl)
sub-refl {tdist T} = sdist sub-refl

well-typed-lc
  : ∀ {Γ t e T}
  → Γ ⊢ t :[ e ] T
  → --------------
    0 ≻ t
well-typed-lc = {!!}

open Subst {TermSig}

substitution-pres-typing
  : ∀ {Γ′ Γ₀ Γ t T₁ e T₂} x u
  → Γ₀ ⊢ t :[ e ] T₂
  → Γ  ⊢ u :[ e ] T₁
  → Γ₀ ≡ Γ , x ∶ T₁ & Γ′ 
  → -----------------------------
    Γ & Γ′ ⊢ (x => u) t :[ e ] T₂
substitution-pres-typing x u tvar Hu Heq = {!!}
substitution-pres-typing {Γ′} {Γ₀} x u (tabs {t = t} Habs) Hu Heq rewrite Heq =
  let Иi As Hcof = Habs in
  tabs $ Иi ([ x ] ∪ As) λ { y {{∉∪ {{∉x}}}} →
    let Htype = substitution-pres-typing x u (Hcof y) (tsub Hu 0≤ sub-refl) refl
        Heq   = subst-open-comm t (∉[]₁ ∉x) (well-typed-lc Hu)
    in
    subst (λ x → _ ⊢ x :[ _ ] _) Heq Htype
  }
substitution-pres-typing x u (tapp Htype Htype₁) Hu Heq = {!!}
substitution-pres-typing x u (tprim Hϕ Htypes) Hu Heq = {!!}
substitution-pres-typing x u (treal {r}) Hu Heq =
  let foo : x ∉ fv (real r)
      foo = ∉Ø
  in
  {!!}
  -- tweaken
  --   (subst (λ x → [] ⊢ x :[ det ] treal cc) Heq′ treal)
  --   {!!}
  --   {!!}
substitution-pres-typing x u (ttup Htypes) Hu Heq = {!!}
substitution-pres-typing x u (tproj i Htype) Hu Heq = {!!}
substitution-pres-typing x u (tif Htype Htype₁ Htype₂) Hu Heq = {!!}
substitution-pres-typing x u (tdiff _ Htype Htype₁) Hu Heq = {!!}
substitution-pres-typing x u (tsolve Htype Htype₁ Htype₂) Hu Heq = {!!}
substitution-pres-typing x u (tdist _ Htypes) Hu Heq = {!!}
substitution-pres-typing x u (tassume Htype) Hu Heq = {!!}
substitution-pres-typing x u (tweight Htype) Hu Heq = {!!}
substitution-pres-typing x u (texpect Htype) Hu Heq = {!!}
substitution-pres-typing x u (tinfer Htype) Hu Heq = {!!}
substitution-pres-typing x u (tweaken Htype _ _) Hu Heq = {!!}
substitution-pres-typing x u (tsub Htype _ _) Hu Heq = {!!}
substitution-pres-typing x u (tpromote Htype _) Hu Heq = {!!}
