open import Data.Finset.Base

open import Lib.Syntax.EvalCtx
open import Lib.Algebra.Reals
open import Lib.Data.Finset
open import Lib.Syntax.Env
open import Lib.Data.Fin
open import Lib.Prelude

module Jacana.Properties.Progress (R : Reals₀) where

-- Proof of progress for the Jacana semantics

open import Jacana.Properties.SmallStep R
open import Jacana.Properties.Typing R
open import Jacana.SmallStep R
open import Jacana.Syntax R
open import Jacana.Typing R

open SyntaxVars

module Progress (Ax : EvalAssumptions) where
  open Eval Ax
  open Step Ax

  progress :
    ε ⊢ t ∶ T
    → --------------------------------
    is-value t ⊎ Σ[ t' ∈ Tm ] t →det t'

  progress (tlam _)                = inl vlam
  progress treal                   = inl vreal
  progress (tvar H∈)               = absurd (¬mem-[] (env-sub→dom-sub H∈ _ hereₛ))
  progress (tapp Hty Hty₁)         = inr $ case (progress Hty) of λ where
    (inr (t' , Hstep)) → _ , cong-stepᵈ (λ _ ()) Hstep
    (inl Hv) → case (progress Hty₁) of λ where
      (inr (t' , Hstep)) → _ , cong-stepᵈ (Fin-cases (λ _ → Hv) λ _ ()) Hstep
      (inl Hv₁) →
        let _ , t , Heq = canonical-⇒ Hty Hv reflᵢ
        in  _ , estep (eapp Heq Hv₁)
  progress (tprim Hϕ Hty) = inr $ case (progress Hty) of λ where
    (inr (t' , Hstep)) → _ , cong-stepᵈ (λ _ ()) Hstep
    (inl Hv) →
      let _ , Heq , Hvs = canonical-tup Hty Hv reflᵢ
          Htys          = ttup-inv (subst (_ ⊢_∶ _) Heq Hty) reflᵢ
          Hreals i      = canonical-real (Htys i) (Hvs i) reflᵢ .snd
      in _ , estep (eprim (Heq ∙ ap (tup _ ▸_) (funext Hreals)))
  progress (ttup Htys) with Fin-search-⊎ (progress ∘ Htys)
  ... | inr (j , (t' , Hstep) , Hvs) = inr $ _ , cong-stepᵈ Hvs Hstep
  ... | inl Hvs                      = inl $ vtup Hvs
  progress (tproj i Hty) = inr $ case (progress Hty) of λ where
    (inr (t' , Hstep)) → _ , cong-stepᵈ (λ _ ()) Hstep
    (inl Hv) →
      let _ , Heq , Hvs = canonical-tup Hty Hv reflᵢ
      in  _ , estep (eproj i Heq Hvs)
  progress (tif Hty Hty₁ Hty₂ _) = inr $ case (progress Hty) of λ where
    (inr (t' , Hstep)) → _ , cong-stepᵈ {n = fzero} (λ _ ()) Hstep
    (inl Hv) →
      let _ , Heq = canonical-real Hty Hv reflᵢ
      in  _ , estep (eif Heq)
  progress (tdiff Hty Hty₁ Hty₂ _) = inr $ case (progress Hty) of λ where
    (inr (t' , Hstep)) → _ , cong-stepᵈ (λ _ ()) Hstep
    (inl Hv) → case (progress Hty₁) of λ where
      (inr (t' , Hstep)) → _ , cong-stepᵈ (Fin-cases (λ _ → Hv) λ _ ()) Hstep
      (inl Hv₁) → case (progress Hty₂) of λ where
        (inr (t' , Hstep)) →
          _ , cong-stepᵈ (Fin-cases (λ _ → Hv) $ Fin-cases (λ _ → Hv₁) λ _ ()) Hstep
        (inl Hv₂) → _ , estep (ediff Hv Hv₁ Hv₂)
  progress (tsolve Hty Hty₁ Hty₂ _) = inr $ case (progress Hty) of λ where
    (inr (t' , Hstep)) → _ , cong-stepᵈ (λ _ ()) Hstep
    (inl Hv) → case (progress Hty₁) of λ where
      (inr (t' , Hstep)) → _ , cong-stepᵈ (Fin-cases (λ _ → Hv) λ _ ()) Hstep
      (inl Hv₁) → case (progress Hty₂) of λ where
        (inr (t' , Hstep)) →
          _ , cong-stepᵈ (Fin-cases (λ _ → Hv) $ Fin-cases (λ _ → Hv₁) λ _ ()) Hstep
        (inl Hv₂) → _ , estep (esolve Hv Hv₁ Hv₂)
  progress (tsub Hty _) = progress Hty
  progress (tpromote {Γ} Hty _ _ H⊆)
    rewrite Id≃path.from (env-sub-dom-eq H⊆ ∈Ø-elim) = progress Hty
