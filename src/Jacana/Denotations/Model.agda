open import Cat.Diagram.Product.Indexed
open import Cat.Diagram.Exponential
open import Cat.Functor.Naturality
open import Cat.Functor.Base
open import Cat.Cartesian
open import Cat.Prelude

open import Data.Fin.Base
open import Data.Sum.Base
open import Data.Power using (singleton ; _∪_)

open import Jacana.Regularity

open import Lib.LocallyNameless.Unfinite
open import Lib.Algebra.Reals
open import Lib.Cat.Product
open import Lib.Data.Finset
open import Lib.Data.Vector
open import Lib.Syntax.Env

open import Order.Base

import Jacana.Properties.Syntax as SyntaxProperties
import Jacana.Syntax as Syntax
import Jacana.Typing as Typing

module Jacana.Denotations.Model (R : Reals₀) where

open SyntaxProperties R
open FinsetSyntax renaming (_∪_ to _∪ᶠ_)
open VectorSyntax
open Syntax R
open Typing R
open SyntaxVars
open TypingVars
open Reg⊆-lat hiding (! ; top ; _∪_)
open Functor
open Reals R using (ℝ)
open _=>_

record is-Jacana-model {o ℓ} (𝔇 : Precategory o ℓ) : Type (o ⊔ ℓ) where
  field
    𝔇-cartesian : Cartesian-category 𝔇
    𝔇-closed    : Cartesian-closed 𝔇 𝔇-cartesian
    𝔇-ip        : ∀ {n} → has-products-indexed-by 𝔇 (Fin n)

  open Cartesian-category 𝔇-cartesian public
  open Cartesian-closed   𝔇-closed public renaming ([_,_] to infixr 4 _⇒_)
  open ProdIso 𝔇-cartesian public
  open IndexedProdIso 𝔇-ip public

  module 𝔇-ip {n} (F : Fin n → Ob) = Indexed-product (𝔇-ip F)

  field
    □⟨_⟩     : Reg⊆ → Functor 𝔇 𝔇
    □-counit : □⟨ X ⟩ => Id
    □-comult : X ~ʳ X' → □⟨ X ∩ X' ⟩ ≅ⁿ □⟨ X ⟩ F∘ □⟨ X' ⟩
    □-⊆      : X ⊆ X' → □⟨ X ⟩ => □⟨ X' ⟩
    □-top    : □⟨ X ⟩ .F₀ top ≅ top
    □-prod
      : is-meet-closed X
      → ∀ {A B} → □⟨ X ⟩ .F₀ (A ⊗₀ B) ≅ (□⟨ X ⟩ .F₀ A ⊗₀ □⟨ X ⟩ .F₀ B)
    □⟨⊤⟩-Id : Id => □⟨ Reg⊆-lat.top ⟩

    𝔇ℝ[_] : Reg↓ → Ob
    □-𝔇ℝ : □⟨ X ⟩ .F₀ 𝔇ℝ[ c ] ≅ 𝔇ℝ[ Close-downward · (X ∩ c .hom) ]

  𝔇ℝ'[_] : Reg↓ ^ n → Ob
  𝔇ℝ'[ cs ] = 𝔇-ip.ΠF (𝔇ℝ[_] ⊙ cs)

  field
    𝔇-sub  : c ⊆ c' → Hom 𝔇ℝ[ c ] 𝔇ℝ[ c' ]
    𝔇-real : ℝ → Hom top 𝔇ℝ[ c ]
    𝔇-prim
      : {cs : Reg↓ ^ PrimAr ϕ} → PrimTy ϕ ≡ (cs , c)
      → Hom 𝔇ℝ'[ cs ] 𝔇ℝ[ c ]
    𝔇-cond
      : (cs : Reg↓ ^ n) (_ : ∀ i → P↓ ⊆ cs i)
      → Hom (𝔇ℝ[ P↓ ] ⊗₀ 𝔇ℝ'[ cs ] ⊗₀ 𝔇ℝ'[ cs ]) 𝔇ℝ'[ cs ]
    𝔇-diff
      : ∀ m n
      → ((c ≡ A↓ × X ≡ singleton S ∪ singleton A)
      ⊎ (c ≡ S↓ × X ≡ singleton S)
      ⊎ (c ≡ P↓ × X ≡ singleton P))
      → Hom
        (□⟨ singleton P ⟩ .F₀ (𝔇ℝ'[ make {n = m} c ] ⇒ 𝔇ℝ'[ make {n = n} c ]) ⊗₀ 𝔇ℝ'[ make {n = m} c ] ⊗₀ 𝔇ℝ'[ make {n = m} A↓ ])
        𝔇ℝ'[ make {n = n} A↓ ]
    𝔇-solve
      : ∀ n
      → ((c ≡ A↓ × c' ≡ A↓ × X ≡ singleton C ∪ singleton S ∪ singleton A)
       ⊎ (c ≡ C↓ × c' ≡ S↓ × X ≡ singleton S)
       ⊎ (c ≡ C↓ × c' ≡ L↓ × X ≡ singleton C))
      → Hom
        (□⟨ X ⟩ .F₀ (𝔇ℝ[ c ] ⇒ □⟨ X ⟩ .F₀ (𝔇ℝ'[ make {n = n} c' ] ⇒ 𝔇ℝ'[ make {n = n} c' ]))
         ⊗₀ 𝔇ℝ'[ c ∷ make {n = n} c' ]
         ⊗₀ 𝔇ℝ[ c Reg↓-lat.∩ PL↓ ])
        𝔇ℝ'[ make {n = 1 + n} A↓ ]

  □-ip
    : is-meet-closed X
    → (F : Fin n → Ob) → □⟨ X ⟩ .F₀ (𝔇-ip.ΠF F) ≅ 𝔇-ip.ΠF λ i → □⟨ X ⟩ .F₀ (F i)
  □-ip {X} {zero} HX F  = F-map-iso □⟨ X ⟩ Π-0 ∙Iso □-top ∙Iso Π-0 Iso⁻¹
  □-ip {X} {suc n} HX F =
         F-map-iso □⟨ X ⟩ (Π-cons F)
    ∙Iso □-prod HX
    ∙Iso (id-iso ⊗Iso □-ip HX (tail F))
    ∙Iso Π-cons (λ i → □⟨ X ⟩ .F₀ (F i)) Iso⁻¹

Jacana-model : ∀ o ℓ → Type (lsuc (o ⊔ ℓ))
Jacana-model o ℓ = Σ (Precategory o ℓ) is-Jacana-model

module Denotations {o} {ℓ} (model : Jacana-model o ℓ) where
  open is-Jacana-model (model .snd)

  Ty-denot : Ty → Ob
  Ty-denot (treal c)      = 𝔇ℝ[ c ]
  Ty-denot (T₁ ⇒[ X ] T₂) = □⟨ X ⟩ .F₀ (Ty-denot T₁ ⇒ Ty-denot T₂)
  Ty-denot (ttup n Ts)    = 𝔇-ip.ΠF λ i → Ty-denot (Ts i)

  instance
    ⟦⟧-Ty : ⟦⟧-notation Ty
    ⟦⟧-Ty = brackets _ Ty-denot

  open EnvDenot 𝔇-cartesian Ty-denot

  Sub-denot : T <: T' → Hom ⟦ T ⟧ ⟦ T' ⟧
  Sub-denot (sreal H⊆) = 𝔇-sub H⊆
  Sub-denot (stup H<:) = 𝔇-ip.tuple _ λ i → Sub-denot (H<: i) ∘ 𝔇-ip.π _ i
  Sub-denot (sarr {X = X} {T₁' = T₁'} {T₂' = T₂'} H<: H⊆ H<:₁) =
      □-⊆ {X = X} H⊆ .η (⟦ T₁' ⟧ ⇒ ⟦ T₂' ⟧)
    ∘ □⟨ X ⟩ .F₁ ([-,-]₁ _ _ 𝔇-closed (Sub-denot H<:₁) (Sub-denot H<:))

  ∩ᵗ-is-□ : ∀ T → X ~ᵗ T → □⟨ X ⟩ .F₀ ⟦ T ⟧ ≅ ⟦ X ∩ᵗ T ⟧
  ∩ᵗ-is-□ (treal c) HX       = □-𝔇ℝ
  ∩ᵗ-is-□ (T ⇒[ _ ] T₁) HX   = isoⁿ→iso (□-comult HX) _ Iso⁻¹
  ∩ᵗ-is-□ {X} (ttup n Ts) HX =
    □-ip (Reg⊆-is-meet-closed X) _ ∙Iso ΠIso (λ i → ∩ᵗ-is-□ (Ts i) (HX i))

  env-≤-□ : Γ ≤ᵉ X → □⟨ X ⟩ .F₀ ⟦ Γ ⟧ ≅ ⟦ Γ ⟧
  env-≤-□ {ε} H≤                    = □-top
  env-≤-□ {Γ ▸ a , T [ H∉ ]} {X} H≤ =
    let p : X ∩ᵗ T ≡ T
        p = ≤ᵗ→∩ᵗ (H≤ (sub-cons sub-nil'))
        Hl : □⟨ X ⟩ .F₀ (Env-denot Γ) ≅ Env-denot Γ
        Hl = env-≤-□ λ H∈ → H≤ (sub-consr H∈)
        HT : □⟨ X ⟩ .F₀ (Ty-denot T) ≅ Ty-denot T
        HT = ∩ᵗ-is-□ T (≤ᵗ→~ᵗ (H≤ (sub-cons sub-nil'))) ∙Iso path→iso (ap Ty-denot p)
    in
    □-prod (Reg⊆-is-meet-closed X) ∙Iso (Hl ⊗Iso HT)

  Tm-denot : Γ ⊢ t ∶ T → Hom ⟦ Γ ⟧ ⟦ T ⟧
  Tm-denot (tsub Hty H<:) = Sub-denot H<: ∘ Tm-denot Hty
  Tm-denot (tpromote {T = T} {X} Hty H≤ H~ H⊆) =
    ∩ᵗ-is-□ T H~ .to ∘ □⟨ X ⟩ .F₁ (Tm-denot Hty) ∘ env-≤-□ H≤ .from ∘ env-proj H⊆
  Tm-denot (tvar H∈) = π₂ ∘ env-proj H∈
  Tm-denot {Γ} (tlam {T = T} {T'} (Иi As Hty))
    with (a , H∉) ← fresh{𝔸} (As ∪ᶠ dom Γ) = □⟨⊤⟩-Id .η _ ∘ ƛ body
    where
      body = subst (λ Γ → Hom ⟦ Γ ⟧ _) (cons-∉ {Γ = Γ} (∉∪₂ As H∉))
        (Tm-denot (Hty a ⦃ ∉∪₁ H∉ ⦄))
  Tm-denot (tapp Hty Hty₁) = ev ∘ ⟨ □-counit .η _ ∘ Tm-denot Hty , Tm-denot Hty₁ ⟩
  Tm-denot (tprim Hϕ Hty)  = 𝔇-prim Hϕ ∘ Tm-denot Hty
  Tm-denot (treal {r = r}) = 𝔇-real r ∘ !
  Tm-denot (ttup Htys)     = 𝔇-ip.tuple _ λ i → Tm-denot (Htys i)
  Tm-denot (tproj i Hty)   = 𝔇-ip.π _ i ∘ Tm-denot Hty
  Tm-denot (tif {cs = cs} Hty Hty₁ Hty₂ H≤) =
    𝔇-cond cs H≤ ∘ ⟨ Tm-denot Hty , ⟨ Tm-denot Hty₁ , Tm-denot Hty₂ ⟩ ⟩
  Tm-denot (tdiff {m = m} {n = n} Hty Hty₁ Hty₂ Hc) =
    𝔇-diff m n Hc ∘ ⟨ Tm-denot Hty , ⟨ Tm-denot Hty₁ , Tm-denot Hty₂ ⟩ ⟩
  Tm-denot (tsolve {n = n} Hty Hty₁ Hty₂ Hc) =
    𝔇-solve n Hc ∘ ⟨ Tm-denot Hty , ⟨ Tm-denot Hty₁ , Tm-denot Hty₂ ⟩ ⟩
