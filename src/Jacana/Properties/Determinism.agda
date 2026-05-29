open import Data.Nat.Base using (Nat-is-set)

open import Lib.LocallyNameless.BindingSignature
open import Lib.Syntax.Substitution
open import Lib.Syntax.EvalCtx
open import Lib.Algebra.Reals
open import Lib.Data.Vector
open import Lib.Prelude hiding (_*_)

module Jacana.Properties.Determinism (R : Reals₀) where

open import Jacana.Properties.SmallStep R
open import Jacana.SmallStep R
open import Jacana.Syntax R

open Reals R

module _ (Ax : EvalAssumptions) where
  open EvalAssumptions Ax
  open Eval Ax
  open Step Ax

  →ᵈ-deterministic : Deterministic _→ᵈ_
  →ᵈ-deterministic (eapp Heq Hv) (eapp Heq' Hv') =
    ap (λ t → (0 ≈> _) (t ₀)) $ is-set→cast-pathp {q = refl} (Tm ^_) Nat-is-set
      (ap snd (op-inj (sym Heq ∙ Heq')))
  →ᵈ-deterministic (eprim {ϕ = ϕ} Heq) (eprim Heq') =
    ap (real ∘ PrimEv ϕ) (ext λ i → real-inj $ op-inj' (sym Heq ∙ Heq') $ₚ i)
  →ᵈ-deterministic (eproj _ Heq _) (eproj _ Heq' _) = op-inj' (sym Heq ∙ Heq') $ₚ _
  →ᵈ-deterministic (eif Heq) (eif Heq') =
    ap (λ r → if is-pos r then _ else _) (real-inj $ sym Heq ∙ Heq')
  →ᵈ-deterministic (ediff Hv₀ Hv₁ Hv₂) (ediff Hv₀' Hv₁' Hv₂') i =
    Diff
      (_ , is-value-is-prop Hv₀ Hv₀' i)
      (_ , is-value-is-prop Hv₁ Hv₁' i)
      (_ , is-value-is-prop Hv₂ Hv₂' i)
      .fst
  →ᵈ-deterministic (esolve Hv₀ Hv₁ Hv₂) (esolve Hv₀' Hv₁' Hv₂') i =
    Solve
      (_ , is-value-is-prop Hv₀ Hv₀' i)
      (_ , is-value-is-prop Hv₁ Hv₁' i)
      (_ , is-value-is-prop Hv₂ Hv₂' i)
      .fst

  DetCtx-cannot-step :
    {E : Tm → Tm}
    {t u : Tm}
    (_ : DetCtx E)
    (_ : ¬ is-value t)
    → ---------------
    ¬ E t →ᵈ u
  DetCtx-cannot-step (ectx {j = j} _) Ht (eapp Heq Hv) with fin-view j
  ... | zero                         = Ht (subst is-value (sym Heq) vlam)
  ... | suc i with zero ← fin-view i = Ht Hv
  DetCtx-cannot-step (ectx {j = j} _) Ht (eprim Heq) with zero ← fin-view j =
    Ht (subst is-value (sym Heq) (vtup (λ _ → vreal)))
  DetCtx-cannot-step (ectx {j = j} _) Ht (eproj i Heq Hvs) with zero ← fin-view j =
    Ht (subst is-value (sym Heq) (vtup Hvs))
  DetCtx-cannot-step (ectx {j = j} _) Ht (eif Heq) with zero ← fin-view j =
    Ht (subst is-value (sym Heq) vreal)
  DetCtx-cannot-step (ectx {j = j} _) Ht (ediff Hv₀ Hv₁ Hv₂) with fin-view j
  ... | zero                         = Ht Hv₀
  ... | suc i with fin-view i
  ... | zero                         = Ht Hv₁
  ... | suc i with zero ← fin-view i = Ht Hv₂
  DetCtx-cannot-step (ectx {j = j} _) Ht (esolve Hv₀ Hv₁ Hv₂) with fin-view j
  ... | zero = Ht Hv₀
  ... | suc i with fin-view i
  ... | zero                         = Ht Hv₁
  ... | suc i with zero ← fin-view i = Ht Hv₂

  →det-deterministic : Deterministic _→det_
  →det-deterministic =
    CongCls-deterministic →ᵈ-deterministic
      (λ Hctx1 Hctx2 Ht Hu Heq →
        EvalCtx-unique is-value Hctx1 Hctx2
          (λ Hv → value-cannot-step Hv Ht)
          (λ Hv → value-cannot-step Hv Hu)
          Heq)
      (λ Hctx Ht →
        DetCtx-cannot-step Hctx
          (λ Hv → value-cannot-step Hv Ht))
