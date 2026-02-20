open import Lib.Algebra.Reals

module DPPL.Denotations.Model (R : Reals₀) where

open import DPPL.Regularity
open import DPPL.Syntax R
open import DPPL.Typing R
open import DPPL.Properties.Syntax R

open import Lib.Cat.Product
open import Lib.Data.Finset
open import Lib.Data.Vector
open import Lib.LocallyNameless.Unfinite
open import Lib.Syntax.Env

open import Cat.Prelude
open import Cat.Cartesian
open import Cat.Diagram.Exponential
open import Cat.Diagram.Product.Finite
open import Cat.Diagram.Product.Indexed
open import Cat.Functor.Base
open import Cat.Functor.Naturality
open import Data.Fin.Base hiding (_≤_)
open import Data.List.Base hiding (_++_ ; head ; tail)
open import Data.Power hiding (_∪_ ; _∩_)
open import Data.Sum using (_⊎_)
open import Order.Base
open import Order.Lattice
import Cat.Reasoning as Cr

open Reals R using (ℝ)
open SyntaxVars
open VectorSyntax using () renaming (_∷_ to _∷ᵛ_)

open Reg↓≤ using (_≤_)
open is-lattice Reg↓-lattice hiding (! ; top ; _∪_)

open Functor
open _=>_

record is-DPPL-model {o ℓ} (𝔇 : Precategory o ℓ) : Type (o ⊔ ℓ) where
  field
    𝔇-cartesian : Cartesian-category 𝔇
    𝔇-closed : Cartesian-closed 𝔇 𝔇-cartesian

  open Cartesian-category 𝔇-cartesian public
  open Cartesian-closed   𝔇-closed public renaming ([_,_] to infixr 4 _⇒_)
  open ProdIso 𝔇-cartesian public

  module 𝔇-ip {n} (F : Fin n → Ob) =
    Indexed-product (Cartesian→standard-finite-products terminal products F)

  field
    □⟨_⟩        : Coeff → Functor 𝔇 𝔇
    □-pres-top  : □⟨ c ⟩ .F₀ top ≅ top
    □-pres-prod : ∀ X Y → □⟨ c ⟩ .F₀ (X ⊗₀ Y) ≅ (□⟨ c ⟩ .F₀ X ⊗₀ □⟨ c ⟩ .F₀ Y)
    □-≤         : c ≤ c' → □⟨ c ⟩ => □⟨ c' ⟩
    □-comult    : □⟨ c ⟩ F∘ □⟨ c' ⟩ ≅ⁿ □⟨ c ∩ c' ⟩
    □⟨A⟩-Id     : □⟨ A↓ ⟩ ≅ⁿ Id

    𝔇ℝ[_] : Nat × Coeff → Ob
    □-𝔇ℝ : □⟨ c ⟩ .F₀ 𝔇ℝ[ n , c' ] ≅ 𝔇ℝ[ n , c ∩ c' ]

  𝔇ℝ1[_] : Coeff → Ob
  𝔇ℝ1[ c ] = 𝔇ℝ[ 1 , c ]

  𝔇ℝ'[_] : Coeff ^ n → Ob
  𝔇ℝ'[ cs ] = 𝔇-ip.ΠF (𝔇ℝ1[_] ⊙ cs)

  field
    𝔇-sub : c ≤ c' → Hom 𝔇ℝ[ n , c ] 𝔇ℝ[ n , c' ]
    𝔇-real : ℝ → ∀ {c} → Hom top 𝔇ℝ[ c ]
    𝔇-prim
      : {cs : Reg↓ ^ PrimAr ϕ} → PrimTy ϕ ≡ (cs , c)
      → Hom 𝔇ℝ'[ cs ] 𝔇ℝ[ 1 , c ]
    𝔇-cond
      : (cs : Coeff ^ n) (_ : ∀ i → P↓ ≤ cs i)
      → Hom 𝔇ℝ'[ make {n = 1} P↓ ++ (cs ++ cs) ] 𝔇ℝ'[ cs ]
    𝔇-diff
      : ∀ m n → c ≡ A↓ ⊎ c ≡ P↓ → Hom
        (□⟨ P↓ ⟩ .F₀ (𝔇ℝ'[ make {n = m} c ] ⇒ 𝔇ℝ'[ make {n = n} c ]) ⊗₀ 𝔇ℝ'[ make {n = m} c ] ⊗₀ 𝔇ℝ'[ make {n = m} A↓ ])
        𝔇ℝ'[ make {n = n} A↓ ]
    𝔇-solve
      : ∀ n → c ≡ A↓ ⊎ c ≡ C↓ → Hom
        (□⟨ C↓ ⟩ .F₀ (𝔇ℝ'[ c ∷ᵛ make {n = n} A↓ ] ⇒ 𝔇ℝ'[ make {n = n} A↓ ])
         ⊗₀ 𝔇ℝ'[ c ∷ᵛ make {n = n} A↓ ]
         ⊗₀ 𝔇ℝ[ 1 , c ∩ PC↓ ])
        𝔇ℝ'[ make {n = 1 + n} A↓ ]

  □-pres-ip
    : ∀ (F : Fin n → Ob) → □⟨ c ⟩ .F₀ (𝔇-ip.ΠF F) ≅ 𝔇-ip.ΠF λ i → □⟨ c ⟩ .F₀ (F i)
  □-pres-ip {n = zero} F                = □-pres-top
  □-pres-ip {n = suc zero} F            = id-iso
  □-pres-ip {n = suc (suc n)} {c = c} F = □-pres-prod (F fzero) (𝔇-ip.ΠF (F ⊙ fsuc))
    ∙Iso (id-iso {□⟨ c ⟩ .F₀ (F fzero)} ⊗Iso □-pres-ip (F ⊙ fsuc))

  𝔇ℝ'-⊗
    : (cs : Coeff ^ m) (cs' : Coeff ^ n)
    → (𝔇ℝ'[ cs ] ⊗₀ 𝔇ℝ'[ cs' ]) ≅ 𝔇ℝ'[ cs ++ cs' ]
  𝔇ℝ'-⊗ cs cs' =
    Π-++ (𝔇ℝ1[_] ⊙ cs) (𝔇ℝ1[_] ⊙ cs') ∙Iso
    path→iso (ap 𝔇-ip.ΠF (sym (++-map cs cs' 𝔇ℝ1[_])))


DPPL-model : ∀ o ℓ → Type (lsuc (o ⊔ ℓ))
DPPL-model o ℓ = Σ (Precategory o ℓ) is-DPPL-model

module Denotations {o} {l} (model : DPPL-model o l) where
  open is-DPPL-model (model .snd)
  open Cr._≅_

  Ty-denot : Ty → Ob
  Ty-denot (treal c)            = 𝔇ℝ[ 1 , c ]
  Ty-denot (T₁ ⇒[ c , det ] T₂) = □⟨ c ⟩ .F₀ (Ty-denot T₁ ⇒ Ty-denot T₂)
  Ty-denot (ttup n Ts)          = 𝔇-ip.ΠF λ i → Ty-denot (Ts i)
  -- Distributions are interpreted trivially for the time being.
  Ty-denot (tdist _)          = top
  Ty-denot (_ ⇒[ _ , rnd ] _) = top

  instance
    ⟦⟧-Ty : ⟦⟧-notation Ty
    ⟦⟧-Ty = brackets _ Ty-denot

  open EnvDenot 𝔇-cartesian Ty-denot
  open TypingVars
  open FinsetSyntax

  Sub-denot : T <: T' → Hom ⟦ T ⟧ ⟦ T' ⟧
  Sub-denot (sreal H≤)             = 𝔇-sub H≤
  Sub-denot (stup {Ts' = Ts'} H<:) =
    𝔇-ip.tuple _ λ i → Sub-denot (H<: i) ∘ 𝔇-ip.π _ i
  Sub-denot (sarr {c = c} {e = det} {det} {T₁' = T₁'} {T₂' = T₂'} H<: H<:' H≤c H≤e) =
    □-≤ H≤c .η (⟦ T₁' ⟧ ⇒ ⟦ T₂' ⟧) ∘
    □⟨ c ⟩ .F₁ ([-,-]₁ _ _ 𝔇-closed (Sub-denot H<:') (Sub-denot H<:))
  Sub-denot (sarr {e' = rnd} H<: H<:' H≤c H≤e) = !
  Sub-denot (sdist H<:)                        = !

  ∩ᵗ-is-□ : ∀ T → □⟨ c ⟩ .F₀ ⟦ T ⟧ ≅ ⟦ c ∩ᵗ T ⟧
  ∩ᵗ-is-□ (treal c')          = □-𝔇ℝ
  ∩ᵗ-is-□ (T ⇒[ _ , det ] T₁) = isoⁿ→iso □-comult (Ty-denot T ⇒ Ty-denot T₁)
  ∩ᵗ-is-□ (ttup n Ts)         =
    □-pres-ip (λ i → Ty-denot (Ts i)) ∙Iso ΠIso (λ i → ∩ᵗ-is-□ (Ts i))
  ∩ᵗ-is-□ (tdist _)          = □-pres-top
  ∩ᵗ-is-□ (_ ⇒[ _ , rnd ] _) = □-pres-top

  env-≤-□ : {Γ : Env Ty} → Γ ≤ᵉ c → □⟨ c ⟩ .F₀ ⟦ Γ ⟧ ≅ ⟦ Γ ⟧
  env-≤-□ {Γ = ε} H≤                               = □-pres-top
  env-≤-□ {c} {Γ ▸ a , T [ H∉ ]} H≤ =
    let p : c ∩ᵗ T ≡ T
        p = ≤ᵗ→∩ᵗ (H≤ (sub-cons sub-nil'))
        Hl : □⟨ c ⟩ .F₀ (Env-denot Γ) ≅ Env-denot Γ
        Hl = env-≤-□ λ H∈ → H≤ (sub-consr H∈)
        HT : □⟨ c ⟩ .F₀ (Ty-denot T) ≅ Ty-denot T
        HT = ∩ᵗ-is-□ T ∙Iso path→iso (ap Ty-denot p)
    in
    □-pres-prod (Env-denot Γ) (Ty-denot T) ∙Iso (Hl ⊗Iso HT)

  Tm-denot : Γ ⊢ t :[ det ] T → Hom ⟦ Γ ⟧ ⟦ T ⟧
  Tm-denot (tsub {e = det} Hty _ H<:)       = Sub-denot H<: ∘ Tm-denot Hty
  Tm-denot (tpromote {T = T} {c} Hty H≤ H⊆) =
    ∩ᵗ-is-□ T .to ∘ □⟨ c ⟩ .F₁ (Tm-denot Hty) ∘ env-≤-□ H≤ .from ∘ env-proj H⊆
  Tm-denot (tvar H∈)             = π₂ ∘ env-proj H∈
  Tm-denot (tlam {e = rnd} Hlam) = !
  Tm-denot {Γ} (tlam {T = T} {e = det} {T'} (Иi As Hty))
    with (a , H∉) ← fresh{𝔸} (As ∪ dom Γ) = □⟨A⟩-Id .from .η _ ∘ ƛ body
    where
      body = subst (λ Γ → Hom ⟦ Γ ⟧ _) (cons-∉ {Γ = Γ} (∉∪₂ As H∉))
        (Tm-denot (Hty a ⦃ ∉∪₁ H∉ ⦄))
  Tm-denot (tapp {T = T} {T' = T'} Hty Hty₁) =
    ev ∘ ⟨ □⟨A⟩-Id .to .η _ ∘ Tm-denot Hty , Tm-denot Hty₁ ⟩
  Tm-denot (tprim {ϕ = ϕ} Hϕ Hty)           = 𝔇-prim Hϕ ∘ Tm-denot Hty
  Tm-denot (treal {r = r})                  = 𝔇-real r ∘ !
  Tm-denot (ttup Htys)                      = 𝔇-ip.tuple _ λ i → Tm-denot (Htys i)
  Tm-denot (tproj i Hty)                    = 𝔇-ip.π _ i ∘ Tm-denot Hty
  Tm-denot (tif {cs = cs} Hty Hty₁ Hty₂ H≤) =
    𝔇-cond cs H≤ ∘ if-distr ∘ ⟨ Tm-denot Hty , ⟨ Tm-denot Hty₁ , Tm-denot Hty₂ ⟩ ⟩
    where
      if-distr = 𝔇ℝ'-⊗ (make {n = 1} P↓) (cs ++ cs) .to ∘ id ⊗₁ 𝔇ℝ'-⊗ cs cs .to
  Tm-denot (tinfer _)                               = !
  Tm-denot (tdiff {m = m} {n = n} Hty Hty₁ Hty₂ Hc) =
    𝔇-diff m n Hc ∘ ⟨ Tm-denot Hty , ⟨ Tm-denot Hty₁ , Tm-denot Hty₂ ⟩ ⟩
  Tm-denot (tsolve {n = n} Hty Hty₁ Hty₂ Hc) =
    𝔇-solve n Hc ∘ ⟨ Tm-denot Hty , ⟨ Tm-denot Hty₁ , Tm-denot Hty₂ ⟩ ⟩

