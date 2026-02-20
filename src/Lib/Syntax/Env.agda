module Lib.Syntax.Env where

open import Lib.Prelude hiding (⟨_,_⟩)
open import Lib.Data.Dec
open import Lib.Data.Finset
open import Lib.LocallyNameless.Unfinite

open import Cat.Base
open import Cat.Cartesian

open import Data.Dec.Base
open import Data.Finset.Base
open import Data.Finset.Properties

open FinsetSyntax

private variable
  ℓ : Level
  X Y : Type ℓ
  a : 𝔸
  T : X

data Env (X : Type ℓ) : Type ℓ
dom : Env X → Finset 𝔸

data Env X where
  ε      : Env X
  _▸_[_] : (Γ : Env X) (x : 𝔸 × X) (H∉ : fst x ∉ dom Γ) → Env X

dom ε              = Ø
dom (Γ ▸ x [ H∉ ]) = [ fst x ] ∪ dom Γ

private variable
  Γ Γ' : Env X

_,_∶_ : Env X → 𝔸 → X → Env X
_,_∶_ {X = X} Γ a T = caseᵈ (a ∈ dom Γ) of cons module Cons where
  cons : Dec (a ∈ dom Γ) → Env X
  cons (yes _) = Γ
  cons (no H∉) = Γ ▸ (a , T) [ false→is-no H∉ ]

_&_ : Env X → Env X → Env X
Γ & ε                    = Γ
Γ & (Γ' ▸ (a , T) [ _ ]) = (Γ & Γ') , a ∶ T

infixr 8 _&_

pattern [_∶_] a T = ε ▸ a , T [ tt ]

data env-sub {X : Type ℓ} : Env X → Env X → Type ℓ where
  sub-nil : env-sub ε ε
  sub-cons
    : {x : 𝔸 × X} {H∉ : fst x ∉ dom Γ} {H∉' : fst x ∉ dom Γ'}
    → env-sub Γ Γ' → env-sub (Γ ▸ x [ H∉ ]) (Γ' ▸ x [ H∉' ])
  sub-consr
    : {x : 𝔸 × X} {H∉' : fst x ∉ dom Γ'}
    → env-sub Γ Γ' → env-sub Γ (Γ' ▸ x [ H∉' ])

instance
  Inclusion-Env : {X : Type ℓ} → Inclusion (Env X) ℓ
  Inclusion-Env = record { _⊆_ = env-sub }

instance
  Membership-Env : {X : Type ℓ} → Membership (𝔸 × X) (Env X) ℓ
  Membership-Env = record { _∈_ = λ (x , T) Γ → [ x ∶ T ] ⊆ Γ }

infixl 5 _∶_∈_
_∶_∈_ : {X : Type ℓ} → 𝔸 → X → Env X → Type ℓ
a ∶ T ∈ Γ = (a , T) ∈ Γ

dom-cons : (Γ : Env X) → dom (Γ , a ∶ T) ≡ [ a ] ∪ dom Γ
dom-cons {a = a} Γ with holds? (a ∈ dom Γ)
... | yes H∈ = uncons a (dom Γ) H∈
... | no  _  = refl

dom-& : (Γ Γ' : Env X) → dom (Γ & Γ') ≡ dom Γ ∪ dom Γ'
dom-& Γ ε               = sym $ union-idr _
dom-& Γ (Γ' ▸ x [ H∉ ]) =
  dom ((Γ & Γ') , fst x ∶ snd x) ≡⟨ dom-cons (Γ & Γ') ∙ ap ([ fst x ] ∪_) (dom-& Γ Γ') ⟩
  [ fst x ] ∪ dom Γ ∪ dom Γ'     ≡⟨ union-comm [ fst x ] _ ∙ sym (union-assoc (dom Γ) _ _) ∙ ap (dom Γ ∪_) (union-comm (dom Γ') _) ⟩
  dom Γ ∪ [ fst x ] ∪ dom Γ'     ∎

dom-empty→is-nil : dom Γ ⊆ Ø → Γ ≡ ε
dom-empty→is-nil {Γ = ε} H⊆           = refl
dom-empty→is-nil {Γ = _ ▸ _ [ _ ]} H⊆ = absurd (¬mem-[] (H⊆ _ hereₛ))

cons-∈ : (H∉ : a ∈ dom Γ) → Γ , a ∶ T ≡ Γ
cons-∈ {a = a} {Γ = Γ} H∈ with yes _ ← holds? (a ∈ dom Γ)
  | _ ← true→is-yes {d = holds? (a ∈ dom Γ)} H∈ = refl

cons-∉
  : {X : Type ℓ} {Γ : Env X} {T : X} (H∉ : a ∉ dom Γ)
  → Γ , a ∶ T ≡ Γ ▸ a , T [ H∉ ]
cons-∉ {a = a} {Γ = Γ} {T} = unfold where
  unfold : {d : Dec (a ∈ dom Γ)} (H∉ : a ∉ dom Γ) → Cons.cons Γ a T d ≡ Γ ▸ a , T [ H∉ ]
  unfold {yes H∈} H∉   = absurd (is-no→false H∉ H∈)
  unfold {no H∉'} H∉ i =
    Γ ▸ a , T [ is-yes-is-prop (false→is-no H∉') H∉ i ]

&-cons-distr : (Γ & Γ') , a ∶ T ≡ Γ & (Γ' , a ∶ T)
&-cons-distr {Γ = Γ} {Γ'} {a} with holds? (a ∈ dom Γ')
... | yes H∈ = cons-∈ (subst (_ ∈ᶠˢ_) (sym (dom-& Γ Γ')) (unionr-∈ᶠˢ _ (dom Γ) _ H∈))
... | no  _  = refl

&-idl : (Γ : Env X) → ε & Γ ≡ Γ
&-idl ε                  = refl
&-idl (Γ ▸ a , T [ H∉ ]) = ap (_, a ∶ T) (&-idl Γ) ∙ cons-∉ H∉

env-sub→dom-sub : Γ ⊆ Γ' → dom Γ ⊆ dom Γ'
env-sub→dom-sub sub-nil _ H∈                            = absurd (¬mem-[] H∈)
env-sub→dom-sub (sub-cons {Γ = Γ} {Γ'} {x = x} H⊆) a H∈ =
 case ∈ᶠˢ-union _ [ fst x ] (dom Γ) H∈ of λ where
   (inl H∈') → unionl-∈ᶠˢ _ _ (dom Γ') H∈'
   (inr H∈') → thereₛ (env-sub→dom-sub H⊆ a H∈')
env-sub→dom-sub (sub-consr {Γ' = Γ'} {x = x} H⊆) a H∈ =
  thereₛ (env-sub→dom-sub H⊆ a H∈)

sub-nil' : ε ⊆ Γ
sub-nil' {Γ = ε}           = sub-nil
sub-nil' {Γ = _ ▸ _ [ _ ]} = sub-consr sub-nil'

sub-▸-cons
  : {X : Type ℓ} {Γ Γ' : Env X} {T : X} {H∉ : a ∉ dom Γ}
  → a ∉ dom Γ' → Γ ⊆ Γ' → (Γ ▸ (a , T) [ H∉ ]) ⊆ (Γ' , a ∶ T)
sub-▸-cons {a = a} {Γ' = Γ'} H∉ H⊆ with no _ ← holds? (a ∈ dom Γ') = sub-cons H⊆

sub-consr' : Γ ⊆ Γ' → Γ ⊆ (Γ' , a ∶ T)
sub-consr' {Γ' = Γ'} {a} H⊆ with holds? (a ∈ dom Γ')
... | yes _ = H⊆
... | no  _ = sub-consr H⊆

sub-cons' : a ∉ dom Γ' → Γ ⊆ Γ' → (Γ , a ∶ T) ⊆ (Γ' , a ∶ T)
sub-cons' {a} {Γ' = Γ'} {Γ} H∉ H⊆ with holds? (a ∈ dom Γ)
... | yes _ = sub-consr' H⊆
... | no  _ = sub-▸-cons H∉ H⊆

env-sub-refl : Γ ⊆ Γ
env-sub-refl {Γ = ε}           = sub-nil
env-sub-refl {Γ = _ ▸ _ [ _ ]} = sub-cons env-sub-refl

env-sub-trans : {Γ₁ Γ₂ Γ₃ : Env X} → Γ₁ ⊆ Γ₂ → Γ₂ ⊆ Γ₃ → Γ₁ ⊆ Γ₃
env-sub-trans H⊆ sub-nil                    = H⊆
env-sub-trans (sub-cons H⊆) (sub-cons H⊆')  = sub-cons (env-sub-trans H⊆ H⊆')
env-sub-trans (sub-consr H⊆) (sub-cons H⊆') = env-sub-trans H⊆ (sub-consr H⊆')
env-sub-trans H⊆ (sub-consr H⊆')            = sub-consr (env-sub-trans H⊆ H⊆')

env-sub-dom-eq : Γ ⊆ Γ' → dom Γ' ⊆ dom Γ → Γ ≡ Γ'
env-sub-dom-eq sub-nil Hdom                                    = refl
env-sub-dom-eq (sub-cons {Γ = Γ} {Γ'} {H∉ = H∉} {H∉'} H⊆) Hdom =
  let Hdom' : dom Γ' ⊆ dom Γ
      Hdom' a H∈ = ∈ᶠˢ-split (λ where reflᵢ → absurd $ᵢ is-no→false H∉' H∈) id
        (Hdom a (thereₛ H∈))
  in
  sym (cons-∉ H∉) ∙ ap (_, _ ∶ _) (env-sub-dom-eq H⊆ Hdom') ∙ cons-∉ H∉'
env-sub-dom-eq (sub-consr {H∉' = H∉'} H⊆) Hdom =
  absurd $ᵢ is-no→false H∉' $ env-sub→dom-sub H⊆ _ (Hdom _ hereₛ)

env-sub-&
  : {Γ₁ Γ₁' Γ₂ Γ₂' : Env X} → Γ₁ ⊆ Γ₁' → Γ₂ ⊆ Γ₂'
  → (∀ a → a ∈ᶠˢ dom Γ₂ → a ∉ dom Γ₁') → (Γ₁ & Γ₂) ⊆ (Γ₁' & Γ₂')
env-sub-& H⊆₁ sub-nil Hdisj = H⊆₁
env-sub-& {Γ₁' = Γ₁'} {Γ₂ ▸ _ [ _ ]} {Γ₂' ▸ x [ H∉₂ ]} H⊆₁ (sub-cons H⊆₂) Hdisj =
  sub-cons'
    (subst (_ ∉_) (sym $ dom-& Γ₁' Γ₂') (∉∪ (Hdisj _ hereₛ) H∉₂))
    (env-sub-& H⊆₁ H⊆₂ (λ _ H∈ → Hdisj _ (thereₛ H∈)))
env-sub-& H⊆₁ (sub-consr H⊆₂) Hdisj =
  sub-consr' (env-sub-& H⊆₁ H⊆₂ Hdisj)

env-sub-&-inv
  : {X : Type ℓ} {Γ Γ₁' Γ₂' : Env X} → Γ ⊆ (Γ₁' & Γ₂')
  → Σ[ Γ₁ ∈ Env X ] Σ[ Γ₂ ∈ Env X ] Γ ≡ Γ₁ & Γ₂ × Γ₁ ⊆ Γ₁' × Γ₂ ⊆ Γ₂'
  × (∀ a → a ∈ᶠˢ dom Γ₂ → a ∉ dom Γ₁')
env-sub-&-inv {Γ = Γ} {Γ₂' = ε} H⊆ = Γ , ε , refl , H⊆ , sub-nil , ∈Ø-elim
env-sub-&-inv {Γ₁' = Γ₁'} {Γ₂' ▸ a , T [ H∉ ]} H⊆ with holds? (a ∈ dom (Γ₁' & Γ₂'))
... | yes _ =
  let Γ₁ , Γ₂ , p , H⊆₁ , H⊆₂ , Hdisj = env-sub-&-inv H⊆ in
  Γ₁ , Γ₂ , p , H⊆₁ , sub-consr H⊆₂ , Hdisj
... | no H∉a with H⊆
... | sub-cons {H∉ = H∉₁} H⊆₁ =
  let Γ₁ , Γ₂ , p , H⊆₁ , H⊆₂ , Hdisj = env-sub-&-inv {Γ₁' = Γ₁'} {Γ₂'} H⊆₁
      a∉Γ' : ¬ a ∈ (dom Γ₁' ∪ dom Γ₂')
      a∉Γ' = subst (λ xs → ¬ _ ∈ xs) (dom-& Γ₁' Γ₂') H∉a
      a∉Γ₂ : a ∉ dom Γ₂
      a∉Γ₂ = false→is-no λ H∈ → a∉Γ' (unionr-∈ᶠˢ _ (dom Γ₁') _ (env-sub→dom-sub H⊆₂ _ H∈))
  in
  Γ₁ , (Γ₂ , a ∶ T) ,
    sym (cons-∉ H∉₁) ∙ ap (_, a ∶ T) p ∙ &-cons-distr {Γ' = Γ₂} ,
    H⊆₁ ,
    subst (λ Γ → env-sub Γ _) (sym $ cons-∉ a∉Γ₂) (sub-cons H⊆₂) ,
    λ a' H∈ → ∈ᶠˢ-split {P = λ _ → a' ∉ dom Γ₁'} ⦃ hlevel-instance is-yes-is-prop ⦄
      (λ p → subst (_∉ dom Γ₁') (sym $ Id≃path.to p) $ ∉∪₁ (false→is-no a∉Γ'))
      (λ H∈' → Hdisj _ H∈')
      (subst (_ ∈ᶠˢ_) (dom-cons Γ₂) H∈)
... | sub-consr H⊆₁ =
  let Γ₁ , Γ₂ , p , H⊆₁ , H⊆₂ , Hdisj = env-sub-&-inv H⊆₁ in
  Γ₁ , Γ₂ , p , H⊆₁ , sub-consr H⊆₂ , Hdisj

env-sub-weakenr : {Γ Γ₁' Γ₂' : Env X} → Γ ⊆ Γ₁' → Γ ⊆ (Γ₁' & Γ₂')
env-sub-weakenr {Γ₂' = Γ₂'} H⊆ = env-sub-& {Γ₂' = Γ₂'} H⊆ sub-nil' ∈Ø-elim

env-sub-weakenl
  : {Γ Γ₁' Γ₂' : Env X} → Γ ⊆ Γ₂'
  → (∀ a → a ∈ᶠˢ dom Γ → a ∉ dom Γ₁') → Γ ⊆ (Γ₁' & Γ₂')
env-sub-weakenl {Γ = Γ} H⊆ Hdisj =
  subst (λ Γ → env-sub Γ _) (&-idl Γ) (env-sub-& sub-nil' H⊆ Hdisj)

env-sub-strengthenr
  : {Γ Γ₁' Γ₂' : Env X} → Γ ⊆ (Γ₁' & Γ₂')
  → dom Γ ⊆ dom Γ₁' → Γ ⊆ Γ₁'
env-sub-strengthenr {Γ₂' = Γ₂'} H⊆ Hcont =
  let Γ₁ , Γ₂ , p , H⊆₁ , H⊆₂ , Hdisj = env-sub-&-inv {Γ₂' = Γ₂'} H⊆
      q : Γ₂ ≡ ε
      q = dom-empty→is-nil λ _ H∈ → absurd $ᵢ is-no→false
        (Hdisj _ H∈)
        (Hcont _ $
          subst (_ ∈ᶠˢ_) (sym $ ap dom p ∙ dom-& Γ₁ Γ₂) (unionr-∈ᶠˢ _ (dom Γ₁) _ H∈))
  in subst (λ Γ → env-sub Γ _) (sym $ p ∙ ap (Γ₁ &_) q) H⊆₁

env-sub-strengthenl
  : {Γ Γ₁' Γ₂' : Env X} → Γ ⊆ (Γ₁' & Γ₂')
  → (∀ a → a ∈ᶠˢ dom Γ → a ∉ dom Γ₁') → Γ ⊆ Γ₂'
env-sub-strengthenl {Γ₂' = Γ₂'} H⊆ Hdisj =
  let Γ₁ , Γ₂ , p , H⊆₁ , H⊆₂ , _ = env-sub-&-inv {Γ₂' = Γ₂'} H⊆
      q : Γ₁ ≡ ε
      q = dom-empty→is-nil λ _ H∈ → absurd $ᵢ is-no→false
        (Hdisj _ $
          subst (_ ∈ᶠˢ_) (sym $ ap dom p ∙ dom-& Γ₁ Γ₂) (unionl-∈ᶠˢ _ _ (dom Γ₂) H∈))
        (env-sub→dom-sub H⊆₁ _ H∈)
  in subst (λ Γ → env-sub Γ _) (sym $ p ∙ ap (_& Γ₂) q ∙ &-idl Γ₂) H⊆₂

env-sub-&-diffl
  : {X : Type ℓ} {Γ Γ₁' Γ₂' : Env X} → dom Γ₁' ⊆ dom Γ → Γ ⊆ (Γ₁' & Γ₂')
  → Σ[ Γ' ∈ Env X ] Γ ≡ (Γ₁' & Γ') × Γ' ⊆ Γ₂' × (∀ a → a ∈ᶠˢ dom Γ' → a ∉ dom Γ₁')
env-sub-&-diffl {Γ₁' = Γ₁'} {Γ₂'} Hcont H⊆ =
  let Γ₁ , Γ₂ , p , H⊆₁ , H⊆₂ , Hdisj = env-sub-&-inv {Γ₂' = Γ₂'} H⊆
      q : Γ₁ ≡ Γ₁'
      q = env-sub-dom-eq H⊆₁ λ a H∈ →
        let H∈Γ : a ∈ᶠˢ (dom Γ₁ ∪ dom Γ₂)
            H∈Γ = subst (_ ∈ᶠˢ_) (ap dom p ∙ dom-& Γ₁ Γ₂) (Hcont a H∈)
        in case ∈ᶠˢ-union _ _ _ H∈Γ of λ where
          (inl H∈') → H∈'
          (inr H∈') → absurd $ᵢ is-no→false (Hdisj _ H∈') H∈
  in
  Γ₂ , p ∙ ap (_& Γ₂) q , H⊆₂ , Hdisj

module EnvDenot
  {o ℓ} {C : Precategory o ℓ} (cart : Cartesian-category C)
  (X-denot : X → Precategory.Ob C) where
  private module C = Cartesian-category cart
  open C

  Env-denot : Env X → Ob
  Env-denot ε                   = top
  Env-denot (Γ ▸ (_ , T) [ _ ]) = Env-denot Γ ⊗₀ X-denot T

  instance
    ⟦⟧-RawEnv : ⟦⟧-notation (Env X)
    ⟦⟧-RawEnv = brackets _ Env-denot

  env-proj : {Γ Γ' : Env X} → Γ ⊆ Γ' → Hom ⟦ Γ' ⟧ ⟦ Γ ⟧
  env-proj sub-nil        = C.id
  env-proj (sub-cons H⊆)  = ⟨ env-proj H⊆ C.∘ π₁ , π₂ ⟩
  env-proj (sub-consr H⊆) = env-proj H⊆ C.∘ π₁

