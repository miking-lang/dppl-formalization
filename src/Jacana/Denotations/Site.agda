open import Cat.Functor.Properties
open import Cat.Prelude

open import Data.Nat.Base using (H-Level-≤)

open import Jacana.Denotations.Regularity
open import Jacana.Regularity

open import Lib.Algebra.Reals
open import Lib.Homotopy.Join
open import Lib.Cat.Concrete
open import Lib.Data.Vector

open import Order.Base

module Jacana.Denotations.Site (R : Reals₀) (Ax : RegAssumptions R) where

open RegAssumptions Ax
open RegProperties R Ax
open Reals R using (ℝ)

open Reg≤

ℛ : Precategory lzero lzero
ℛ .Precategory.Ob                    = Nat × Reg
ℛ .Precategory.Hom (m , c) (n , d)   = ∫ₚ (⟨ c ∣ d ⟩-reg {m} {n})
ℛ .Precategory.Hom-set _ _ _ _       = hlevel 1
ℛ .Precategory.id {m , c}            = (λ x → x) , id-reg' ≤-refl
ℛ .Precategory._∘_ (f , Hf) (g , Hg) = f ⊙ g , ∘-reg' Hf Hg
ℛ .Precategory.idr f                 = refl ,ₚ prop!
ℛ .Precategory.idl g                 = refl ,ₚ prop!
ℛ .Precategory.assoc f g h           = refl ,ₚ prop!

module ℛ = Precategory ℛ

ℛ-underlying : Functor ℛ (Sets _)
ℛ-underlying .Functor.F₀ (n , _) = el! (ℝ ^ n)
ℛ-underlying .Functor.F₁ f       = f .fst
ℛ-underlying .Functor.F-id       = refl
ℛ-underlying .Functor.F-∘ _ _    = refl

ℛ-faithful : is-faithful ℛ-underlying
ℛ-faithful p = p ,ₚ prop!

ℛ-conc : Conc-category _ ℛ
ℛ-conc .Conc-category.underlying          = ℛ-underlying
ℛ-conc .Conc-category.underlying-faithful = ℛ-faithful

open Conc-category ℛ-conc

ℛ-id≤ : ∀ {c c' m} → c ≤ c' → ℛ.Hom (m , c) (m , c')
ℛ-id≤ H≤ = (λ x → x) , id-reg' H≤

ℛ-const : ∀ {n m c c'} → ℝ ^ n → ℛ.Hom (m , c) (n , c')
ℛ-const x = (λ _ → x) , const-reg' x
