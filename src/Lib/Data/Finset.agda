module Lib.Data.Finset where

open import 1Lab.Prelude hiding (_≠_ ; _∉_)

open import Lib.Data.Dec
open import Lib.Data.Vector hiding (_++_)
open import Data.Finset.Base
open import Data.Finset.Properties

open import Order.Base using (Poset)
open import Order.Diagram.Join using (Join)
open import Order.Instances.Nat using (Nat-poset; Nat-joins; Nat-bottom)
open import Order.Semilattice.Join using (is-join-semilattice)
open import Data.Dec.Base using (Discrete)
open import Data.Fin.Base using (Fin ; fzero ; fsuc ; fin-view ; suc ; zero)
open import Data.List.Base using (List ; _++_)
open import Data.List.Membership using (++-memberₗ ; ++-memberᵣ ; member-++-view)
open import Data.Nat.Base using (max)
open import Data.Nat.Order using (¬sucx≤x)
open import Data.Sum.Base using (_⊎_ ; inr ; inl)
open import Data.Sum.Properties using (Discrete-⊎)

private variable
  ℓ ℓ' : Level
  A : Type ℓ
  B : Type ℓ'

module FinsetSyntax where
  infix 1 [_]
  infixr 8 _∪_

  pattern Ø = []
  pattern [_] a = a ∷ []

  _∪_ : Finset A → Finset A → Finset A
  _∪_ = _<>_

∈Ø-elim : {B : A → Type ℓ'} (a : A) → a ∈ᶠˢ [] → B a
∈Ø-elim _ H∈ = absurd (¬mem-[] H∈)

∷≠[] : ∀ {x : A} {xs} → ¬ x ∷ xs ≡ []
∷≠[] {A = A} p = subst (λ x → ∣ distinguish x ∣) p tt where
  distinguish : Finset A → Prop lzero
  distinguish []                   = el! ⊥
  distinguish (x ∷ xs)             = el! ⊤
  distinguish (∷-dup x xs i)       = el! ⊤
  distinguish (∷-swap x y xs i)    = el! ⊤
  distinguish (squash x y p q i j) =
    n-Type-is-hlevel 1
      (distinguish x) (distinguish y)
      (λ i → distinguish (p i)) (λ i → distinguish (q i)) i j

module _ {o ℓ : Level} {P : Poset o ℓ} ⦃ joins : is-join-semilattice P ⦄ where
  open Poset P
  open is-join-semilattice joins

  fold : Finset ⌞ P ⌟ → ⌞ P ⌟
  fold [] = bot
  fold (x ∷ xs) = x ∪ fold xs
  fold (∷-dup x xs i) =
    (∪-assoc {x} ∙ ap (_∪ fold xs) ∪-idem) i
  fold (∷-swap x y xs i) =
    (∪-assoc {x} {y} ∙ ap (_∪ fold xs) ∪-comm ∙ sym ∪-assoc) i
  fold (squash x y p q i j) =
    Poset.Ob-is-set P _ _ (λ k → fold (p k)) (λ k → fold (q k)) i j

  ≤fold : ∀{x xs} → x ∈ xs → x ≤ fold xs
  ≤fold {x} {xs} H∈ =
    ∈ᶠˢ-elim (λ xs _ → x ≤ fold xs)
      (λ {_} → l≤∪)
      (λ q z → ≤-trans z r≤∪)
      xs H∈

private instance
  Nat-is-join-semilattice : is-join-semilattice Nat-poset
  Nat-is-join-semilattice = record
    { _∪_ = max
    ; ∪-joins = λ x y → Join.has-join (Nat-joins x y)
    ; has-bottom = Nat-bottom
    }

-- Maximum of a finite set of numbers
maxfs : Finset Nat → Nat
maxfs = fold

maxfs+1∉ : (xs : Finset Nat) → suc (maxfs xs) ∉ xs
maxfs+1∉ xs = ¬∈→∉ {ℙA = Finset Nat} λ H∈ → ¬sucx≤x _ (≤fold H∈)

open FinsetSyntax

from-list-++
  : ∀ {ℓ} {X : Type ℓ} (l1 l2 : List X)
  → from-list (l1 ++ l2) ≡ from-list l1 ∪ from-list l2
from-list-++ l1 l2 = finset-ext
  (λ x H∈ →
    case ∈ᶠˢ-from-list H∈ of λ H∈++ →
    case member-++-view l1 l2 H∈++ of λ where
      (inl (H∈l , _)) → unionl-∈ᶠˢ _ _ _ (from-list-∈ᶠˢ H∈l)
      (inr (H∈r , _)) → unionr-∈ᶠˢ _ (from-list l1) _ (from-list-∈ᶠˢ H∈r))
  (λ x H∈ →
    case ∈ᶠˢ-union _ (from-list l1) (from-list l2) H∈ of λ where
      (inl H∈l) → case ∈ᶠˢ-from-list H∈l of λ H∈l' → from-list-∈ᶠˢ (++-memberₗ H∈l')
      (inr H∈r) → case ∈ᶠˢ-from-list H∈r of λ H∈r' → from-list-∈ᶠˢ (++-memberᵣ H∈r'))

-- Finite union of finite subsets
⋃ : {n : Nat} → Vector (Finset A) n → Finset A
⋃ = foldr _∪_ Ø

inr⁻¹ : Finset (A ⊎ B) → Finset B
inr⁻¹ = _>>= λ
  { (inl _) → []
  ; (inr y) → y ∷ []
  }

thereₛ-inr⁻¹
  : {y : B} {y' : A ⊎ B} {xs : Finset (A ⊎ B)}
  → y ∈ᶠˢ inr⁻¹ xs → y ∈ᶠˢ inr⁻¹ (y' ∷ xs)
thereₛ-inr⁻¹ {y' = inl x} H∈ = H∈
thereₛ-inr⁻¹ {y' = inr x} H∈ = thereₛ H∈

∉inr⁻¹→inr∉ :
  ⦃ _ : Discrete A ⦄
  ⦃ _ : Discrete B ⦄
  (zs : Finset (A ⊎ B))
  (y : B)
  → -----------------------
  y ∉ inr⁻¹ zs → inr y ∉ zs
∉inr⁻¹→inr∉ {A = A} {B = B} zs y H∉ =
  ¬∈→∉ {ℙA = Finset (A ⊎ B)} λ H∈ → ∉→¬∈ {ℙA = Finset B} H∉ $
  ∈ᶠˢ-elim (λ zs _ → y ∈ inr⁻¹ zs)
    hereₛ
    (λ {y' xs} _ → thereₛ-inr⁻¹ {y' = y'} {xs})
    zs H∈

module _ {ℓ : Level} {A : Type ℓ} ⦃ _ : Discrete A ⦄ where

  -- Subtract an element
  infix 6 _-[_]
  _-[_] :
    (xs : Finset A)
    (x : A)
    → ----------------
    Finset A
  xs -[ x ] = filter (¬_ ∘ (_≡ x)) xs

  ∉∷₁ :
    {x y : A}
    {ys : Finset A}
    (_ : x ∉ (y ∷ ys))
    → ----------------
    x ≠ y
  ∉∷₁ p = ¬≡→≠ λ H≡ → ∉→¬∈ {ℙA = Finset A} p (hereₛ' (Id≃path.from H≡))

  ∉∷₂ :
    {x y : A}
    {ys : Finset A}
    (_ : x ∉ (y ∷ ys))
    → ----------------
    x ∉ ys
  ∉∷₂ p = ¬∈→∉ {ℙA = Finset A} λ H∈ → ∉→¬∈ {ℙA = Finset A} p (thereₛ H∈)

  ∉∷ :
    {x y : A}
    {ys : Finset A}
    (_ : x ≠ y)
    (_ : x ∉ ys)
    → -------------
    x ∉ (y ∷ ys)
  ∉∷ H≠ H∉ = ¬∈→∉ {ℙA = Finset A} λ H∈ →
    ∈ᶠˢ-case H∈
      (λ p → ≠→¬≡ H≠ (Id≃path.to p))
      (λ q → ∉→¬∈ {ℙA = Finset A} H∉ q)

  ∉∪₁ :
    {x : A}
    {xs ys : Finset A}
    (_ : x ∉ (xs ∪ ys))
    → ---------------------
    x ∉ xs
  ∉∪₁ p = ¬∈→∉ {ℙA = Finset A} λ H∈ →
    ∉→¬∈ {ℙA = Finset A} p (unionl-∈ᶠˢ _ _ _ H∈)

  ∉∪₂ :
    {x : A}
    (xs : Finset A)
    {ys : Finset A}
    (_ : x ∉ (xs ∪ ys))
    → ---------------------
    x ∉ ys
  ∉∪₂ xs p = ¬∈→∉ {ℙA = Finset A} λ H∈ →
    ∉→¬∈ {ℙA = Finset A} p (unionr-∈ᶠˢ _ xs _ H∈)

  ∉∪ :
    {x : A}
    {xs ys : Finset A}
    (_ : x ∉ xs)
    (_ : x ∉ ys)
    → ---------------------
    x ∉ (xs ∪ ys)
  ∉∪ p q = ¬∈→∉ {ℙA = Finset A} λ H∈ →
    ∥-∥-rec
     (hlevel 1)
     (λ { (inl ∈xs) → ∉→¬∈ {ℙA = Finset A} p ∈xs
        ; (inr ∈ys) → ∉→¬∈ {ℙA = Finset A} q ∈ys
        })
     (∈ᶠˢ-union _ _ _ H∈)

  minus-∉ :
    {xs : Finset A}
    {x y : A}
    (_ : y ∉ (xs -[ x ]))
    (_ : ¬ y ≡ x)
    → -----------------
    y ∉ xs
  minus-∉ H∉ H≠ = ¬∈→∉ {ℙA = Finset A} λ H∈ →
    ∉→¬∈ {ℙA = Finset A} H∉ (filter-∈ᶠˢ _ H∈ H≠)

  ∉-minus :
    (xs : Finset A)
    {x : A}
    → ----------------
    x ∉ (xs -[ x ])
  ∉-minus xs = ¬∈→∉ {ℙA = Finset A} λ H∈ →
    ∥-∥-rec (hlevel 1) (_$ refl) (snd (∈ᶠˢ-filter xs H∈))

  ∉⋃ :
    {n : Nat}
    (f : Vector (Finset A) n)
    {x : A}
    (k : Fin n)
    ⦃ p : x ∉ ⋃ f ⦄
    → ------------------
    x ∉ f k
  ∉⋃ f k ⦃ p ⦄ with fin-view k
  ... | zero  = ∉∪₁ p
  ... | suc k = ∉⋃ (tail f) k ⦃ ∉∪₂ (head f) p ⦄

  ∉⋃' :
    {n : Nat}
    (f : Vector (Finset A) n)
    {x : A}
    (g : (k : Fin n) → x ∉ f k)
    → -------------------------
    x ∉ ⋃ f
  ∉⋃' {n = zero}  f g = tt
  ∉⋃' {n = suc n} f g = ∉∪ (g fzero) (∉⋃' (tail f) (g ∘ fsuc))

  map-∉ :
    ⦃ _ : Discrete B ⦄
    {f : A → B}
    {x : A}
    {xs : Finset A}
    ⦃ p : f x ∉ map f xs ⦄
    → --------------------
    x ∉ xs
  map-∉ {B = B} ⦃ p = p ⦄ =
    ¬∈→∉ {ℙA = Finset A} λ q → ∉→¬∈ {ℙA = Finset B} p (map-∈ᶠˢ _ _ q)
