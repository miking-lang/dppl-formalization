open import Cat.Diagram.Product.Indexed
open import Cat.Diagram.Exponential
open import Cat.Functor.Properties
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Displayed.Total
open import Cat.Cartesian
open import Cat.Prelude

open import Lib.Cat.Thin

open import Data.Fin.Base
open import Data.Power

module Lib.Cat.Concrete where

-- We give an explicit definition of concrete presheaves and show that the category
-- of concrete presheaves is cartesian closed.

record Conc-category {o ℓ} κ (C : Precategory o ℓ) : Type (o ⊔ ℓ ⊔ lsuc κ) where
  no-eta-equality
  open Precategory C

  field
    underlying          : Functor C (Sets κ)
    underlying-faithful : is-faithful underlying

  module underlying = Functor underlying

  ∣_∣ₒ : Ob → Type κ
  ∣ c ∣ₒ = underlying ʻ c

  open underlying public using () renaming (F₁ to ∣_∣ₕ)

  is-conc-hom : (U V : Ob) → (∣ U ∣ₒ → ∣ V ∣ₒ) → Type (ℓ ⊔ κ)
  is-conc-hom U V f = fibre ∣_∣ₕ f

  is-conc-hom-prop : (U V : Ob) (f : ∣ U ∣ₒ → ∣ V ∣ₒ) → is-prop (is-conc-hom U V f)
  is-conc-hom-prop U V f (g , p) (h , q) = underlying-faithful (p ∙ sym q) ,ₚ prop!

  hom≃conc-hom : {U V : Ob} → Hom U V ≃ ∫ₚ (is-conc-hom U V)
  hom≃conc-hom .fst = λ f → ∣ f ∣ₕ , f , refl
  hom≃conc-hom .snd = is-iso→is-equiv $
    iso (λ (_ , f , _) → f)
      (λ (f , g , p) → p ,ₚ refl ,ₚ prop!)
      (λ _ → refl)

module Conc-psh {κ h} {C : Precategory κ h} (Cc : Conc-category κ C) where

  private
    module C = Precategory C
    open Conc-category Cc
    open ∫Hom

  -- This definition is as presented in e.g., Matache et al. 2022.  It's equivalent
  -- to the standard definition when C's underlying sets are represented by a
  -- terminal object, as is traditionally assumed (and as in our applications).
  record CPSh-on (X : Type κ) : Type (κ ⊔ h) where
    no-eta-equality
    field
      is-sec : ∀ U → ℙ (∣ U ∣ₒ → X)
      is-sec-∘
        : ∀ {U V} (g : ∣ V ∣ₒ → X) (h : C.Hom U V)
        → ∣ is-sec V g ∣ → ∣ is-sec U (g ⊙ ∣ h ∣ₕ) ∣
      pt-sec : ∀ {U} (x : X) → ∣ is-sec U (λ _ → x) ∣

  open CPSh-on

  is-cpsh-hom
    : {X Y : Type κ} (f : X → Y) (A : CPSh-on X) (B : CPSh-on Y) → Prop _
  is-cpsh-hom {X} f A B =
    el! $ ∀ {U} (g : ∣ U ∣ₒ → X) → ∣ A .is-sec U g ∣ → ∣ B .is-sec U (f ⊙ g) ∣

  CPSh-structure : Thin-structure _ CPSh-on
  CPSh-structure .Thin-structure.is-hom                  = is-cpsh-hom
  CPSh-structure .Thin-structure.id-is-hom g Hg          = Hg
  CPSh-structure .Thin-structure.∘-is-hom f g Hf Hg h Hh = Hf (g ⊙ h) (Hg h Hh)

  CPSh : Precategory _ _
  CPSh = Structured-objects CPSh-structure

  const-sec : ∀ (A : ⌞ CPSh ⌟) {U f x} → f ≡ (λ _ → x) → ∣ A .snd .is-sec U f ∣
  const-sec A {U} {x = x} p =
    subst (λ f → ∣ A .snd .is-sec U f ∣) (sym p) (A .snd .pt-sec x)

  ⊤CPSh : CPSh-on (Lift _ ⊤)
  ⊤CPSh .is-sec _ _ = ⊤Ω
  ⊤CPSh .is-sec-∘   = _
  ⊤CPSh .pt-sec     = _

  CPSh-terminal : Terminal CPSh
  CPSh-terminal .Terminal.top    = el! _ , ⊤CPSh
  CPSh-terminal .Terminal.has⊤ X =
    contr (∫hom (λ _ → lift tt) _) λ _ → ext λ _ → refl

  _×CPSh_ : {X Y : Type κ} → CPSh-on X → CPSh-on Y → CPSh-on (X × Y)
  (A ×CPSh B) .is-sec U f .∣_∣ =
    ∣ A .is-sec U (fst ⊙ f) ∣ × ∣ B .is-sec U (snd ⊙ f) ∣
  (A ×CPSh B) .is-sec U f .is-tr = hlevel 1
  (A ×CPSh B) .is-sec-∘ g h Hg   =
    A .is-sec-∘ (fst ⊙ g) h (Hg .fst) , B .is-sec-∘ (snd ⊙ g) h (Hg .snd)
  (A ×CPSh B) .pt-sec x = A .pt-sec (fst x) , B .pt-sec (snd x)

  CPSh-products : (A B : ⌞ CPSh ⌟) → Product CPSh A B
  CPSh-products A B = prod where
    open Product
    open is-product
    prod : Product CPSh A B
    prod .apex = el! _ , A .snd ×CPSh B .snd
    prod .π₁ = ∫hom fst λ _ → fst
    prod .π₂ = ∫hom snd λ _ → snd
    prod .has-is-product .⟨_,_⟩ f g =
      ∫hom (λ z → f .fst z , g .fst z) λ h z → f .snd h z , g .snd h z
    prod .has-is-product .π₁∘⟨⟩ = ext λ _ → refl
    prod .has-is-product .π₂∘⟨⟩ = ext λ _ → refl
    prod .has-is-product .unique p q = ext λ _ → ap fst p $ₚ _ ,ₚ ap fst q $ₚ _

  CPSh-cartesian : Cartesian-category CPSh
  CPSh-cartesian .Cartesian-category.terminal = CPSh-terminal
  CPSh-cartesian .Cartesian-category.products = CPSh-products

  ΠCPSh : ∀ {n} {F : Fin n → Type κ} (As : ∀ i → CPSh-on (F i)) → CPSh-on (∀ i → F i)
  ΠCPSh As .is-sec U f .∣_∣   = ∀ i → ∣ As i .is-sec U (λ z → f z i) ∣
  ΠCPSh As .is-sec U f .is-tr = hlevel 1
  ΠCPSh As .is-sec-∘ g h Hg   = λ i → As i .is-sec-∘ (λ z → g z i) h (Hg i)
  ΠCPSh As .pt-sec x          = λ i → As i .pt-sec (x i)

  CPSh-ip : ∀ {n} (F : Fin n → ⌞ CPSh ⌟) → Indexed-product CPSh F
  CPSh-ip F = ip where
    open Indexed-product
    open is-indexed-product
    ip : Indexed-product CPSh F
    ip .ΠF                 = el! _ , ΠCPSh (snd ⊙ F)
    ip .π i                = ∫hom (λ z → z i) (λ _ z → z i)
    ip .has-is-ip .tuple f = ∫hom (λ z i → f i .fst z) λ g z i → f i .snd g z
    ip .has-is-ip .commute    = ext λ _ → refl
    ip .has-is-ip .unique f p = ext λ x i → ap fst (p i) $ₚ x

  module Repr-conc
    (const : ∀ {U V} (x : ∣ V ∣ₒ) → is-conc-hom U V (λ _ → x))
    where

    repr₀ : (U : C.Ob) → CPSh-on ∣ U ∣ₒ
    repr₀ U .is-sec V f      = elΩ (is-conc-hom V U f)
    repr₀ U .is-sec-∘ g h Hg = case Hg of λ g' Hg' →
      inc (g' C.∘ h , underlying.F-∘ _ _ ∙ ap (_⊙ _) Hg')
    repr₀ U .pt-sec {V} x = inc (const {V} {U} x)

    repr : Functor C CPSh
    repr .Functor.F₀ U = underlying.F₀ U , repr₀ U
    repr .Functor.F₁ f = ∫hom ∣ f ∣ₕ λ g Hg → case Hg of λ g' Hg' →
      inc (f C.∘ g' , underlying.F-∘ _ _ ∙ ap (∣ f ∣ₕ ⊙_) Hg')
    repr .Functor.F-id    = ext λ _ → underlying.F-id $ₚ _
    repr .Functor.F-∘ f g = ext λ _ → underlying.F-∘ _ _ $ₚ _

    _⇒CPSh_
      : {X Y : Type κ} (A : CPSh-on X) (B : CPSh-on Y)
      → CPSh-on (∫ₚ (λ f → is-cpsh-hom f A B))
    (A ⇒CPSh B) .is-sec U f =
      elΩ ∣ is-cpsh-hom (uncurry (fst ⊙ f)) (repr₀ U ×CPSh A) B ∣
    (A ⇒CPSh B) .is-sec-∘ g h Hg = inc λ f Hf → case Hf .fst of λ f' Hf' →
      □-out! Hg _ $ inc (h C.∘ f' , underlying.F-∘ _ _ ∙ ap (∣ h ∣ₕ ⊙_) Hf') , snd Hf
    (A ⇒CPSh B) .pt-sec f = inc λ g Hg → f .snd (snd ⊙ g) (snd Hg)

    CPSh-closed : Cartesian-closed CPSh CPSh-cartesian
    CPSh-closed .Cartesian-closed.has-exp A B = exp where
      open Exponential
      open is-exponential
      exp : Exponential CPSh CPSh-cartesian A B
      exp .B^A = el! _ , A .snd ⇒CPSh B .snd
      exp .ev  = ∫hom (λ (f , x) → f · x) λ g Hg →
        □-out! (Hg .fst) _ (inc (C.id , underlying.F-id) , Hg .snd)
      exp .has-is-exp .ƛ {X , Γ} (∫hom f Hf) = ∫hom
        (λ x → (λ z → f (x , z)) , λ g Hg → Hf _ (Γ .pt-sec x , Hg))
        λ g Hg → inc λ h Hh → case Hh .fst of λ h' Hh' → Hf _ $
          ( subst (λ z → ∣ Γ .is-sec _ z ∣) (ap (g ⊙_) Hh') (Γ .is-sec-∘ g h' Hg)
          , Hh .snd
          )
      exp .has-is-exp .commutes m = ext λ _ _ → refl
      exp .has-is-exp .unique _ p = ext λ _ → ext (λ _ → ap fst p $ₚ _) ,ₚ prop!
