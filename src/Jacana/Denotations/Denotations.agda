open import 1Lab.Type.Sigma

open import Cat.Diagram.Exponential
open import Cat.Displayed.Total
open import Cat.Prelude hiding (_∨_)

open import Jacana.Denotations.Regularity
open import Jacana.Regularity

open import Data.Sum.Base
open import Data.Power using (singleton)

open import Lib.Algebra.Reals
open import Lib.Homotopy.Join renaming (_∗_ to _∨_)
open import Lib.Cat.Concrete
open import Lib.Data.Vector

open import Order.Base

import Jacana.Denotations.Domain as Domain
import Jacana.Denotations.Model as Model
import Jacana.Syntax as Syntax
import Jacana.Typing as Typing

module Jacana.Denotations.Denotations (R : Reals₀) (Ax : RegAssumptions R) where

open Conc-psh.CPSh-on
open RegAssumptions Ax
open VectorSyntax
open Domain R Ax
open Syntax R
open SyntaxVars
open Typing R
open Model R
open Cartesian-closed 𝔇-closed using () renaming ([_,_] to _⇒_)
open Precategory 𝔇
open Reals R using (ℝ)
open Reg≤

⟨_⟩-sec : Reg↓ → (U : Nat × Reg) → (ℝ ^ U .fst → ℝ) → Type
⟨ c ⟩-sec (m , r) f = (r ∈ c × f' ∈ ⟨ r ⟩-reg) ∨ (f' ∈ is-const) where
  f' : ℝ ^ m → ℝ ^ 1
  f' = make {n = 1} ⊙ f

⟨_⟩-sec' : Reg↓ ^ n → (U : Nat × Reg) → (ℝ ^ U .fst → ℝ ^ n) → Type
⟨ cs ⟩-sec' U g = ∀ i → π[ i ] ⊙ g ∈ ⟨ π[ i ] cs ⟩-sec U

⟨_∥_⟩-reg : Reg↓ ^ m → Reg↓ ^ n → (ℝ ^ m → ℝ ^ n) → Type
⟨_∥_⟩-reg {m = m} cs cs' f =
  ∀ {U} (g : ℝ ^ U .fst → ℝ ^ m) → g ∈ ⟨ cs ⟩-sec' U → f ⊙ g ∈ ⟨ cs' ⟩-sec' U

⟨_∣_∣_⟩-hom-sec
  : (cs : Reg↓ ^ m) (X : Reg⊆) (cs' : Reg↓ ^ n) (U : Nat × Reg)
  → (ℝ ^ U .fst → ∫ₚ ⟨ cs ∥ cs' ⟩-reg) → Type
⟨_∣_∣_⟩-hom-sec cs X cs' U f =
  □ (Σ[ V ∈ Nat × Reg ] V .snd ∈ X × U .snd ≤ V .snd ×
     Σ[ g ∈ (ℝ ^ U .fst → ℝ ^ V .fst) ]
     Σ[ f' ∈ (ℝ ^ V .fst → ∫ₚ ⟨ cs ∥ cs' ⟩-reg) ]
       f ≡ f' ⊙ g
     × g ∈ ⟨ U .snd ⟩-reg
     × ∀ {W} {h₁} {h₂}
       → h₁ ∈ ⟨ W .snd ∣ V .snd ⟩-reg
       → h₂ ∈ ⟨ cs ⟩-sec' W
       → uncurry (fst ⊙ f') ⊙ ⟨ h₁ , h₂ ⟩ ∈ ⟨ cs' ⟩-sec' W)
  ∨ (f ∈ is-const)

record DenotAssumptions : Type where
  -- TODO: Split Prim-reg into explicit cases
  -- TODO: Try to lay out the regularity assumptions in more concrete terms?

  field
    Prim-denot : (ϕ : Prim) → ℝ ^ PrimAr ϕ → ℝ
    Prim-reg
      : ∀ {cs} (Hϕ : PrimTy ϕ ≡ (cs , c)) {U} {gs}
      → gs ∈ ⟨ cs ⟩-sec' U
      → Prim-denot ϕ ⊙ gs ∈ ⟨ c ⟩-sec U

    cond-denot : ℝ × ℝ ^ n × ℝ ^ n → ℝ ^ n
    cond-reg
      : ∀ (cs : Reg↓ ^ n) (Hc : ∀ i → P↓ ⊆ cs i) {U g₁ g₂ g₃}
      → g₁ ∈ ⟨ P↓ ⟩-sec U
      → g₂ ∈ ⟨ cs ⟩-sec' U
      → g₃ ∈ ⟨ cs ⟩-sec' U
      → cond-denot ⊙ ⟨ g₁ , ⟨ g₂ , g₃ ⟩ ⟩ ∈ ⟨ cs ⟩-sec' U

    diff-denot
      : ∀ m n → c ≡ A↓ ⊎ c ≡ P↓
      → ∫ₚ ⟨ make {n = m} c ∥ make {n = n} c ⟩-reg × ℝ ^ m × ℝ ^ m
      → ℝ ^ n

    diff-reg
      : ∀ m n (Hc : c ≡ A↓ ⊎ c ≡ P↓) {U g₁ g₂ g₃}
      → g₁ ∈ ⟨ make c ∣ singleton P ∣ make c ⟩-hom-sec U
      → g₂ ∈ ⟨ make c ⟩-sec' U
      → g₃ ∈ ⟨ make A↓ ⟩-sec' U
      → diff-denot m n Hc ⊙ ⟨ g₁ , ⟨ g₂ , g₃ ⟩ ⟩ ∈ ⟨ make A↓ ⟩-sec' U

    solve-denot
      : ∀ n → c ≡ A↓ ⊎ c ≡ C↓
      → ∫ₚ ⟨ c ∷ make {n = n} A↓ ∥ make {n = n} A↓ ⟩-reg × ℝ ^ (1 + n) × ℝ
      → ℝ ^ (1 + n)

    solve-reg
      : ∀ n (Hc : c ≡ A↓ ⊎ c ≡ C↓) {U g₁ g₂ g₃}
      → g₁ ∈ ⟨ c ∷ make A↓ ∣ singleton C ∣ make A↓ ⟩-hom-sec U
      → g₂ ∈ ⟨ c ∷ make A↓ ⟩-sec' U
      → g₃ ∈ ⟨ c Reg↓-lat.∩ PC↓ ⟩-sec U
      → solve-denot n Hc ⊙ ⟨ g₁ , ⟨ g₂ , g₃ ⟩ ⟩ ∈ ⟨ make A↓ ⟩-sec' U

mk-hom-sec
  : ∀ (cs : Reg↓ ^ m) X (cs' : Reg↓ ^ n) {U f}
  → f ∈ □⟨ X ⟩₀ (𝔇ℝ'[ cs ] ⇒ 𝔇ℝ'[ cs' ]) .snd .is-sec U
  → f ∈ ⟨ cs ∣ X ∣ cs' ⟩-hom-sec U
mk-hom-sec cs X cs' Hf₀ = case Hf₀ of λ where
  (inr H⋆) → inr H⋆
  (inl Hf) → flip (□-elim (λ _ → hlevel 1)) Hf
    λ (W , HW , H≤ , (g , Hg) , (f' , Hf₀') , p) → case Hf₀' of λ Hf' →
    let fac = W , HW , H≤ , g , f' , p , Hg , λ Hh Hh' →
              Hf' _ (inc ((_ , Hh) , refl) , Hh')
    in
    inl (inc fac)


module _ (Ax' : DenotAssumptions) where
  open DenotAssumptions Ax'

  model : Jacana-model _ _
  model .fst = 𝔇
  model .snd = record
    { 𝔇-cartesian = 𝔇-cartesian
    ; 𝔇-closed    = 𝔇-closed
    ; 𝔇-ip        = 𝔇-ip
    ; □⟨_⟩        = □⟨_⟩
    ; □-counit    = □-counit
    ; □-comult    = □-comult-≅
    ; □-⊆         = □-⊆
    ; □-top       = □-top
    ; □-prod      = □-prod-≅
    ; □⟨⊤⟩-Id     = □⟨⊤⟩-Id
    ; 𝔇ℝ[_]       = 𝔇ℝ[_]
    ; □-𝔇ℝ        = □-𝔇ℝ
    ; 𝔇-sub       = 𝔇ℝ-≤
    ; 𝔇-real      = 𝔇ℝ-const
    ; 𝔇-prim      = λ {ϕ} Hϕ → ∫hom (Prim-denot ϕ) λ _ Hg → Prim-reg Hϕ Hg
    ; 𝔇-cond      = λ cs H≤ →
      ∫hom cond-denot λ _ (Hg₁ , Hg₂ , Hg₃) → cond-reg cs H≤ Hg₁ Hg₂ Hg₃
    ; 𝔇-diff = λ {c} m n Hc → ∫hom (diff-denot m n Hc) λ g (Hg₁ , Hg₂ , Hg₃) →
      diff-reg m n Hc
        (mk-hom-sec (make c) (singleton P) (make c) Hg₁)
        Hg₂
        Hg₃
    ; 𝔇-solve = λ {c} n Hc → ∫hom (solve-denot n Hc) λ g (Hg₁ , Hg₂ , Hg₃) →
      solve-reg n Hc
        (mk-hom-sec (c ∷ make A↓) (singleton C) (make A↓) Hg₁)
        Hg₂
        Hg₃
    }

  open Denotations model public
