open import Data.Finset.Base hiding (_∷_)
open import Data.Fin.Base hiding (_≤_)
open import Data.Power using (singleton)

open import Jacana.Regularity

open import Lib.LocallyNameless.BindingSignature
open import Lib.LocallyNameless.Unfinite
open import Lib.Syntax.Substitution
open import Lib.Syntax.EvalCtx
open import Lib.Algebra.Reals
open import Lib.Data.Finset
open import Lib.Data.Vector
open import Lib.Syntax.Env
open import Lib.Prelude

module Jacana.Properties.Preservation (R : Reals₀) where

open import Jacana.Properties.Typing R
open import Jacana.SmallStep R
open import Jacana.Syntax R
open import Jacana.Typing R

open FinsetSyntax
open VectorSyntax
open SyntaxVars
open TypingVars

updateAt-type :
  {Γs : TyEnv ^ n}
  {Ts : Ty ^ n}
  {ts : Tm ^ n}
  (j : Fin n)
  (_ : ∀ i → Γs i ⊢ ts i ∶ Ts i)
  (_ : Γs j ⊢ t ∶ Ts j)
  → -----------------------------------
  ∀ i → Γs i ⊢ updateAt ts j t i ∶ Ts i
updateAt-type {t = t} {ts = ts} j Htypes Htype i with (i ≡ᵢ? j)
... | yes reflᵢ = subst (_ ⊢_∶ _) (sym $ updateAt-updates ts j t) Htype
... | no H≠     =
  subst (_ ⊢_∶ _) (sym $ updateAt-minimal ts j t i (H≠ ∘ Id≃path.from ∘ sym))
    $ Htypes i

preservation-ctx :
  {E : Tm → Tm}
  {t₁ t₂ : Tm}
  (_ : DetCtx E)
  (_ : ∀ {T} → ε ⊢ t₁ ∶ T → ε ⊢ t₂ ∶ T)
  (_ : ε ⊢ E t₁ ∶ T)
  → ------------------
  ε ⊢ E t₂ ∶ T
preservation-ctx {t₁ = t₁} {t₂} (ectx {o} {j = j} {ts} _) Ht₁₂ Hty =
  let i = ord {o = o} j

      H₁ : ∀ {T} → ε ⊢ updateAt ts i t₁ i ∶ T → ε ⊢ t₂ ∶ T
      H₁ = Ht₁₂ ∘ subst (_ ⊢_∶ _) (updateAt-updates ts i _)

      H₂ : ε ⊢ o ▸ updateAt (updateAt ts i t₁) i t₂ ∶ _
      H₂ = go Hty j H₁

      H₃ : ε ⊢ o ▸ updateAt ts i t₂ ∶ _
      H₃ = subst (λ ts → _ ⊢ o ▸ ts ∶ _) (funext $ updateAt-updateAt ts i _ _) H₂

  in  H₃
  where
    go : 
      {o : TmOp}
      {ts : Vector Tm (length (TmAr o))}
      (_ : ε ⊢ o ▸ ts ∶ T)
      (j : Fin (len {o = o}))
      (_ : ∀ {T} → ε ⊢ ts (ord {o = o} j) ∶ T → ε ⊢ t ∶ T)
      → ----------------------------------------------------------------
      ε ⊢ o ▸ updateAt ts (ord {o = o} j) t ∶ T
    go (tsub Hty H<:) = λ j Ht → tsub (go Hty j Ht) H<:
    go (tpromote Hty H≤ H~ H⊆)
      rewrite Id≃path.from (env-sub-dom-eq H⊆ ∈Ø-elim) = λ j Ht →
      tpromote (go Hty j Ht) H≤ H~ sub-nil
    go (tapp Hty Hty₁) =
      Fin-cases (λ Ht → tapp (Ht Hty) Hty₁)
      $ Fin-cases (λ Ht → tapp Hty (Ht Hty₁)) λ ()
    go (tprim Hϕ Hty)           = Fin-cases (λ Ht → tprim Hϕ (Ht Hty)) λ ()
    go (ttup Htys)              = λ j Ht → ttup (updateAt-type j Htys (Ht (Htys j)))
    go (tproj i Hty)            = Fin-cases (λ Ht → tproj i (Ht Hty)) λ ()
    go (tif Hty Hty₁ Hty₂ H≤)   = Fin-cases (λ Ht → tif (Ht Hty) Hty₁ Hty₂ H≤) λ ()
    go (tdiff Hty Hty₁ Hty₂ Hc) =
      Fin-cases (λ Ht → tdiff (Ht Hty) Hty₁ Hty₂ Hc)
      $ Fin-cases (λ Ht → tdiff Hty (Ht Hty₁) Hty₂ Hc)
      $ Fin-cases (λ Ht → tdiff Hty Hty₁ (Ht Hty₂) Hc) λ ()
    go (tsolve Hty Hty₁ Hty₂ Hc) =
      Fin-cases (λ Ht → tsolve (Ht Hty) Hty₁ Hty₂ Hc)
      $ Fin-cases (λ Ht → tsolve Hty (Ht Hty₁) Hty₂ Hc)
      $ Fin-cases (λ Ht → tsolve Hty Hty₁ (Ht Hty₂) Hc) λ ()

module _ (Ax : EvalAssumptions) where
  open Eval Ax
  open EvalAssumptions Ax

  record PresAssumptions : Type where
    field
      DiffPres :
        {t₀ t₁ t₂ : Tm}
        (_ : Γ ⊢ t₀ ∶ treals m (make c) ⇒[ singleton P ] treals n (make c))
        (_ : Γ ⊢ t₁ ∶ treals m (make c))
        (_ : Γ ⊢ t₂ ∶ treals m (make A↓))
        (_ : c ≡ A↓ ⊎ c ≡ P↓)
        (v₀ : is-value t₀) (v₁ : is-value t₁) (v₂ : is-value t₂)
        → -------------------------------------------------------------------
        Γ ⊢ Diff (_ , v₀) (_ , v₁) (_ , v₂) .fst ∶ treals n (make A↓)

      SolvePres :
        {t₀ t₁ t₂ : Tm}
        (_ : Γ ⊢ t₀ ∶ treals (1 + n) (c ∷ make A↓) ⇒[ singleton C ] treals n (make A↓))
        (_ : Γ ⊢ t₁ ∶ treals (1 + n) (c ∷ make A↓))
        (_ : Γ ⊢ t₂ ∶ treal (c Reg↓-lat.∩ PC↓))
        (_ : c ≡ A↓ ⊎ c ≡ C↓)
        (v₀ : is-value t₀) (v₁ : is-value t₁) (v₂ : is-value t₂)
        → -----------------------------------------------------------------------
        Γ ⊢ Solve (_ , v₀) (_ , v₁) (_ , v₂) .fst ∶ treals (1 + n) (make A↓)

  module Preservation (PAx : PresAssumptions) where
    open PresAssumptions PAx

    preservation-step :
      (_ : ε ⊢ t ∶ T)
      (_ : t →ᵈ t')
      → ------------------
      ε ⊢ t' ∶ T
    preservation-step (tsub Hty H<:) Hstep =
      tsub (preservation-step Hty Hstep) H<:
    preservation-step (tpromote {Γ = Γ} Hty H≤ H~ H⊆) Hstep
      rewrite Id≃path.from (env-sub-dom-eq H⊆ ∈Ø-elim) = tpromote
      (preservation-step Hty Hstep)
      (λ H∈ → ∈Ø-elim _ (env-sub→dom-sub H∈ _ hereₛ))
      H~
      sub-nil
    preservation-step (tapp Hty Hty₁) (eapp {t = t} Heq Hv) =
      let
        T' , H<: , Иi As Hty' = tlam-inv (subst (_ ⊢_∶ _) Heq Hty) reflᵢ
        x , H∉ = fresh{𝔸} (As ∪ fv (t ₀))
      in
      subst (_ ⊢_∶ _) (sym $ subst-intro (t ₀) (∉∪₂ As H∉))
        $ subst-pres-typing reflᵢ (tsub Hty₁ H<:) (Hty' x ⦃ ∉∪₁ H∉ ⦄)
    preservation-step (tprim {ϕ} {c} H∈ Hty) (eprim {rs = rs} Heq) = treal
    preservation-step (tproj i Hty) (eproj .i Heq Hv) =
      ttup-inv (subst (_ ⊢_∶ _) Heq Hty) reflᵢ i
    preservation-step (tif Hty Hty₁ Hty₂ H≤) (eif {r} Heq) with is-pos r
    ... | true  = Hty₁
    ... | false = Hty₂
    preservation-step (tdiff Hty Hty₁ Hty₂ Hc) (ediff Hv₀ Hv₁ Hv₂) =
      DiffPres Hty Hty₁ Hty₂ Hc Hv₀ Hv₁ Hv₂
    preservation-step (tsolve Hty Hty₁ Hty₂ Hc) (esolve Hv₀ Hv₁ Hv₂) =
      SolvePres Hty Hty₁ Hty₂ Hc Hv₀ Hv₁ Hv₂

    preservation : 
      (_ : ε ⊢ t ∶ T)
      (_ : t →det t')
      → -------------------
      ε ⊢ t' ∶ T
    preservation Htype (estep Hstep) = preservation-step Htype Hstep
    preservation Htype (econg Hctx Hstep) =
      preservation-ctx Hctx (λ Ht₁ → preservation Ht₁ Hstep) Htype
