open import Cat.Functor.Properties
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Morphism as Cm

module Lib.Cat.Thin where

-- We define a version of Cat.Displayed.Univalence.Thin without univalence

private variable
  o o' h h' : Level

module _ {B : Precategory o h} (E : Displayed B o' h') where

  private module B = Precategory B
  open Displayed E

  is-thinly-displayed : Type (o ⊔ h ⊔ o' ⊔ h')
  is-thinly-displayed = ∀ {a b} {f : B.Hom a b} {x y} → is-prop (Hom[ f ] x y)

  thin→πᶠ-faithful : is-thinly-displayed → is-faithful (πᶠ E)
  thin→πᶠ-faithful thin p = ∫Hom-path E p (to-pathp (thin _ _))

record
  Thin-structure {ℓ o'} ℓ' (S : Type ℓ → Type o')
    : Type (lsuc ℓ ⊔ o' ⊔ lsuc ℓ') where
  no-eta-equality
  field
    is-hom    : ∀ {x y} → (x → y) → S x → S y → Prop ℓ'
    id-is-hom : ∀ {x} {s : S x} → ∣ is-hom (λ x → x) s s ∣

    ∘-is-hom  :
      ∀ {x y z} {s t u} (f : y → z) (g : x → y)
      → (α : ∣ is-hom f t u ∣) (β : ∣ is-hom g s t ∣)
      → ∣ is-hom (λ x → f (g x)) s u ∣

open Thin-structure

module _ {S : Type o → Type o'} (spec : Thin-structure h' S) where
  Thin-structure→displayed : Displayed (Sets o) o' h'
  Thin-structure→displayed = with-thin-display record where
    Ob[_]      x = S ∣ x ∣
    Hom[_] f x y = ∣ spec .is-hom f x y ∣

    id'      = spec .id-is-hom
    _∘'_ f g = spec .∘-is-hom _ _ f g

  Structured-objects : Precategory _ _
  Structured-objects = ∫ Thin-structure→displayed

  Forget-structure : Functor Structured-objects (Sets o)
  Forget-structure = πᶠ Thin-structure→displayed

  Structured-hom-path : is-faithful Forget-structure
  Structured-hom-path = thin→πᶠ-faithful _ (hlevel 1)

module _ {S : Type o → Type o'} {spec : Thin-structure h' S} where
  private
    module So = Precategory (Structured-objects spec)
    module Som = Cm (Structured-objects spec)

  instance
    Extensional-Hom
      : ∀ {a b ℓr} ⦃ sa : Extensional (⌞ a ⌟ → ⌞ b ⌟) ℓr ⦄
      → Extensional (So.Hom a b) ℓr
    Extensional-Hom ⦃ sa ⦄ = injection→extensional!
      (Structured-hom-path spec) sa

  Homomorphism-monic
    : ∀ {x y} (f : So.Hom x y)
    → (∀ {x y} (p : f · x ≡ f · y) → x ≡ y)
    → Som.is-monic f
  Homomorphism-monic f wit g h p = ext λ x → wit (ap ∫Hom.fst p $ₚ x)
