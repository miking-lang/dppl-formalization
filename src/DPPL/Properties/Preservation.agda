open import Lib.Algebra.Reals

module DPPL.Properties.Preservation (R : Reals₀) where

open import DPPL.Regularity
open import DPPL.Syntax R
open import DPPL.SmallStep R
open import DPPL.Typing R
open import DPPL.Properties.Typing R
open import DPPL.Properties.SmallStep R

open import Lib.Prelude
open import Lib.Data.Finset
open import Lib.Data.Vector
open import Lib.LocallyNameless.Unfinite
open import Lib.LocallyNameless.BindingSignature
open import Lib.Syntax.Env
open import Lib.Syntax.EvalCtx
open import Lib.Syntax.Substitution

open import Data.Bool.Order using (lift)
open import Data.Finset.Base hiding (_∷_)
open import Data.Fin.Base hiding (_≤_)
open import Order.Lattice

open SyntaxVars
open TypingVars
open EvalVars
open is-lattice Reg↓-lattice hiding (_∪_)
open Reg↓≤
open FinsetSyntax
open VectorSyntax

ctx-type-inv :
  {E : Tm → Tm}
  (_ : DetCtx E)
  (_ : Γ ⊢ E t :[ e ] T)
  → ------------------------------------------
  Σ[ (e' , T') ∈ Eff × Ty ] (Γ ⊢ t :[ e' ] T')
ctx-type-inv (ectx {o} {j = j} _) Hty =
  let (e , T) , Hty' = go Hty j
  in  _ , subst (λ t → _ ⊢ t :[ e ] T) (updateAt-updates _ (ord {o = o} j) _) Hty'
  where
    go :
      {o : TmOp}
      {ts : Vector Tm (length (TmAr o))}
      (_ : Γ ⊢ op (o , ts) :[ e ] T)
      (j : Fin (len {o = o}))
      → -----------------------------------------------------------
      Σ[ (e' , T') ∈ Eff × Ty ] (Γ ⊢ ts (ord {o = o} j) :[ e' ] T')
    go (tsub Hty x x₁)                      = go Hty
    go (tpromote {T = T} {c = c} Hty H≤ H⊆) = λ j →
      let (e' , T') , Hty' = go Hty j
      in  (e' , c ∩ᵗ T') , tpromote Hty' H≤ H⊆
    go (tapp Hty Hty₁)           = Fin-cases (_ , Hty) $ Fin-cases (_ , Hty₁) λ ()
    go (tprim _ Hty)             = Fin-cases (_ , Hty) λ ()
    go (ttup Htys)               = λ j → _ , Htys j
    go (tproj i Hty)             = Fin-cases (_ , Hty) λ ()
    go (tif Hty Hty₁ Hty₂ H≤)    = Fin-cases (_ , Hty) λ ()
    go (tsample Hty)             = Fin-cases (_ , Hty) λ ()
    go (tweight Hty)             = Fin-cases (_ , Hty) λ ()
    go (tinfer Hty)              = Fin-cases (_ , Hty) λ ()
    go (tdiff Hty Hty₁ Hty₂ Hc)  =
      Fin-cases (_ , Hty) $ Fin-cases (_ , Hty₁) $ Fin-cases (_ , Hty₂) λ ()
    go (tsolve Hty Hty₁ Hty₂ Hc) =
      Fin-cases (_ , Hty) $ Fin-cases (_ , Hty₁) $ Fin-cases (_ , Hty₂) λ ()

updateAt-type :
  {Γs : TyEnv ^ n}
  {es : Eff ^ n}
  {Ts : Ty ^ n}
  {ts : Tm ^ n}
  (j : Fin n)
  (_ : ∀ i → Γs i ⊢ ts i :[ es i ] Ts i)
  (_ : Γs j ⊢ t :[ es j ] Ts j)
  → ---------------------------------------------------
  (∀ i → Γs i ⊢ updateAt ts j t i :[ es i ] Ts i)
updateAt-type {t = t} {ts = ts} j Htypes Htype i with (i ≡ᵢ? j)
... | yes reflᵢ = subst (_ ⊢_:[ _ ] _) (sym $ updateAt-updates ts j t) Htype
... | no H≠     =
  subst (_ ⊢_:[ _ ] _) (sym $ updateAt-minimal ts j t i (H≠ ∘ Id≃path.from ∘ sym))
    $ Htypes i

preservation-ctx :
  {E : Tm → Tm}
  {t₁ t₂ : Tm}
  (_ : DetCtx E)
  (_ : ∀ {e T} → ε ⊢ t₁ :[ e ] T → ε ⊢ t₂ :[ e ] T)
  (_ : ε ⊢ E t₁ :[ e ] T)
  → ------------------
  ε ⊢ E t₂ :[ e ] T
preservation-ctx {t₁ = t₁} {t₂} (ectx {o} {j = j} {ts} _) Ht₁₂ Hty =
  let i = ord {o = o} j

      H₁ : ∀ {e T} → ε ⊢ updateAt ts i t₁ i :[ e ] T → ε ⊢ t₂ :[ e ] T
      H₁ = Ht₁₂ ∘ subst (_ ⊢_:[ _ ] _) (updateAt-updates ts i _)

      H₂ : ε ⊢ o ▸ updateAt (updateAt ts i t₁) i t₂ :[ _ ] _
      H₂ = go Hty j H₁

      H₃ : ε ⊢ o ▸ updateAt ts i t₂ :[ _ ] _
      H₃ = subst (λ ts → _ ⊢ o ▸ ts :[ _ ] _) (funext $ updateAt-updateAt ts i _ _) H₂

  in  H₃
  where
    go : 
      {o : TmOp}
      {ts : Vector Tm (length (TmAr o))}
      (_ : ε ⊢ o ▸ ts :[ e ] T)
      (j : Fin (len {o = o}))
      (_ : ∀ {e T} → ε ⊢ ts (ord {o = o} j) :[ e ] T → ε ⊢ t :[ e ] T)
      → ----------------------------------------------------------------
      ε ⊢ o ▸ updateAt ts (ord {o = o} j) t :[ e ] T
    go (tsub Hty H≤ H<:) = λ j Ht → tsub (go Hty j Ht) H≤ H<:
    go (tpromote Hty H≤ H⊆)
      rewrite Id≃path.from (env-sub-dom-eq H⊆ ∈Ø-elim) = λ j Ht →
      tpromote (go Hty j Ht) H≤ sub-nil
    go (tapp Hty Hty₁) =
      Fin-cases (λ Ht → tapp (Ht Hty) Hty₁)
      $ Fin-cases (λ Ht → tapp Hty (Ht Hty₁)) λ ()
    go (tprim Hϕ Hty)           = Fin-cases (λ Ht → tprim Hϕ (Ht Hty)) λ ()
    go (ttup Htys)              = λ j Ht → ttup (updateAt-type j Htys (Ht (Htys j)))
    go (tproj i Hty)            = Fin-cases (λ Ht → tproj i (Ht Hty)) λ ()
    go (tif Hty Hty₁ Hty₂ H≤)   = Fin-cases (λ Ht → tif (Ht Hty) Hty₁ Hty₂ H≤) λ ()
    go (tsample Hty)            = Fin-cases (λ Ht → tsample (Ht Hty)) λ ()
    go (tweight Hty)            = Fin-cases (λ Ht → tweight (Ht Hty)) λ ()
    go (tinfer Hty)             = Fin-cases (λ Ht → tinfer (Ht Hty)) λ ()
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
        (_ : Γ ⊢ t₀ :[ e ] treals m (make c) ⇒[ P↓ , det ] treals n (make c))
        (_ : Γ ⊢ t₁ :[ e ] treals m (make c))
        (_ : Γ ⊢ t₂ :[ e ] treals m (make A↓))
        (_ : c ≡ A↓ ⊎ c ≡ P↓)
        (v₀ : IsValue t₀) (v₁ : IsValue t₁) (v₂ : IsValue t₂)
        → -------------------------------------------------------------------
        Γ ⊢ Diff (_ , v₀) (_ , v₁) (_ , v₂) .fst :[ e ] treals n (make A↓)

      SolvePres :
        {t₀ t₁ t₂ : Tm}
        (_ : Γ ⊢ t₀ :[ e ] treals (1 + n) (c ∷ make A↓) ⇒[ C↓ , det ] treals n (make A↓))
        (_ : Γ ⊢ t₁ :[ e ] treals (1 + n) (c ∷ make A↓))
        (_ : Γ ⊢ t₂ :[ e ] treal (c ∩ PC↓))
        (_ : c ≡ A↓ ⊎ c ≡ C↓)
        (v₀ : IsValue t₀) (v₁ : IsValue t₁) (v₂ : IsValue t₂)
        → -----------------------------------------------------------------------
        Γ ⊢ Solve (_ , v₀) (_ , v₁) (_ , v₂) .fst :[ e ] treals (1 + n) (make A↓)

      InferPres :
        (_ : Γ ⊢ t :[ e ] tunit ⇒[ M↓ , rnd ] T)
        (v : IsValue t)
        → --------------------------------------
        Γ ⊢ Infer (_ , v) p .fst :[ e ] T

  module Preservation (PAx : PresAssumptions) where
    open PresAssumptions PAx

    preservation-det-step :
      (_ : ε ⊢ t :[ e ] T)
      (_ : t →ᵈ t')
      → ------------------
      ε ⊢ t' :[ e ] T
    preservation-det-step (tsub Hty H≤ H<:) Hstep =
      tsub (preservation-det-step Hty Hstep) H≤ H<:
    preservation-det-step (tpromote {Γ = Γ} Hty H≤ H⊆) Hstep
      rewrite Id≃path.from (env-sub-dom-eq H⊆ ∈Ø-elim) = tpromote
      (preservation-det-step Hty Hstep)
      (λ H∈ → ∈Ø-elim _ (env-sub→dom-sub H∈ _ hereₛ))
      sub-nil
    preservation-det-step (tapp Hty Hty₁) (eapp {t = t} Heq Hv) =
      let Иi As Hty' = tlam-inv (subst (_ ⊢_:[ _ ] _) Heq Hty) reflᵢ
          x , H∉     = fresh{𝔸} (As ∪ fv (t ₀))
      in  subst (_ ⊢_:[ _ ] _) (sym $ subst-intro (t ₀) (∉∪₂ As H∉))
          $ subst-pres-typing
            (Id≃path.from (sym $ &-idl _))
            (val-type-det Hty₁ Hv)
            (Hty' x ⦃ ∉∪₁ H∉ ⦄)
    preservation-det-step (tprim {ϕ} {c} {e = e} H∈ Hty) (eprim {rs = rs} Heq) =
      subst (ε ⊢ real (PrimEv ϕ rs) :[ e ]_)
        (ap treal (order→∩ (subst (c ≤_) A↓-is-top !)))
        $ tpromote {Γ = ε}
          (tsub treal (lift tt) (sreal ≤-refl))
          (λ H∈ → ∈Ø-elim _ (env-sub→dom-sub H∈ _ hereₛ))
          env-sub-refl
    preservation-det-step (tproj i Hty) (eproj .i Heq Hv) =
      ttup-inv (subst (_ ⊢_:[ _ ] _) Heq Hty) reflᵢ i
    preservation-det-step (tif Hty Hty₁ Hty₂ H≤) (eif {r} Heq) with is-pos r
    ... | true  = Hty₁
    ... | false = Hty₂
    preservation-det-step (tdiff Hty Hty₁ Hty₂ Hc) (ediff Hv₀ Hv₁ Hv₂) =
      DiffPres Hty Hty₁ Hty₂ Hc Hv₀ Hv₁ Hv₂
    preservation-det-step (tsolve Hty Hty₁ Hty₂ Hc) (esolve Hv₀ Hv₁ Hv₂) =
      SolvePres Hty Hty₁ Hty₂ Hc Hv₀ Hv₁ Hv₂

    preservation-det : 
      (_ : ε ⊢ t :[ e ] T)
      (_ : t →det t')
      → -------------------
      ε ⊢ t' :[ e ] T
    preservation-det Htype (estep Hstep) = preservation-det-step Htype Hstep
    preservation-det Htype (econg Hctx Hstep) =
      let _ , Htype' = ctx-type-inv Hctx Htype in
      preservation-ctx Hctx (λ Ht₁ → preservation-det Ht₁ Hstep) Htype

    preservation-rnd-step :
      (_ : ε ⊢ t :[ e ] T)
      (_ : (t , w , s) →ʳ (t' , w' , s'))
      → ---------------------------------
      ε ⊢ t' :[ e ] T
    preservation-rnd-step (tsub Hty H≤ H<:) Hstep =
      tsub (preservation-rnd-step Hty Hstep) H≤ H<:
    preservation-rnd-step (tpromote {Γ = Γ} Hty H≤ H⊆) Hstep
      rewrite Id≃path.from (env-sub-dom-eq H⊆ ∈Ø-elim) = tpromote
      (preservation-rnd-step Hty Hstep)
      (λ H∈ → ∈Ø-elim _ (env-sub→dom-sub H∈ _ hereₛ))
      sub-nil
    preservation-rnd-step Hty (edet Hstep) = preservation-det-step Hty Hstep
    preservation-rnd-step (tweight Hty) (eweight Heq) = ttup λ ()
    preservation-rnd-step tuniform (euniform {p = p}) =
      subst (ε ⊢ real (p .fst) :[ rnd ]_)
        (ap treal (order→∩ (subst (M↓ ≤_) A↓-is-top !)))
        $ tpromote {Γ = ε}
          (tsub treal (lift tt) (sreal ≤-refl))
          (λ H∈ → ∈Ø-elim _ (env-sub→dom-sub H∈ _ hereₛ))
          env-sub-refl
    preservation-rnd-step (tsample Hty) (esample Heq Hv) =
      InferPres (tinfer-inv (subst (_ ⊢_:[ _ ] _) Heq Hty) reflᵢ) Hv

    preservation-rnd :
      (_ : ε ⊢ t :[ e ] T)
      (_ : (t , w , s) →rnd (t' , w' , s'))
      → -----------------------------------
      ε ⊢ t' :[ e ] T
    preservation-rnd Htype (estep Hstep) = preservation-rnd-step Htype Hstep
    preservation-rnd Htype (econg (E , Hctx , reflᵢ) Hstep) =
      let _ , Htype' = ctx-type-inv Hctx Htype in
      preservation-ctx Hctx (λ Ht₁ → preservation-rnd Ht₁ Hstep) Htype
