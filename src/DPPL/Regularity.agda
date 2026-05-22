open import 1Lab.Prelude

open import Data.Nat.Base using (H-Level-≤)

open import Lib.Homotopy.Join
open import Lib.Order.Meet

open import Order.Instances.Pointwise.Diagrams
open import Order.Instances.Pointwise
open import Order.Instances.Product
open import Order.Semilattice.Join
open import Order.Semilattice.Meet
open import Order.Instances.Lower renaming (↓ to ↓ˡ)
open import Order.Instances.Nat
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Lattice
open import Order.Base

module DPPL.Regularity where

data Reg : Type where
  C L S P A : Reg

opaque
  Reg-ord : Reg → Nat × Nat
  Reg-ord C = 0 , 3
  Reg-ord L = 0 , 2
  Reg-ord S = 0 , 1
  Reg-ord P = 1 , 0
  Reg-ord A = 0 , 0

  Reg-ord-injective : injective Reg-ord
  Reg-ord-injective p = go (Id≃path.from p) where
    go : {x y : Reg} → Reg-ord x ≡ᵢ Reg-ord y → x ≡ y
    go {C} {C} p = refl
    go {L} {L} p = refl
    go {S} {S} p = refl
    go {P} {P} p = refl
    go {A} {A} p = refl

private
  module NN = Poset (Nat-poset ×ᵖ Nat-poset)

Reg-poset : Poset lzero lzero
Reg-poset .Poset.Ob               = Reg
Reg-poset .Poset._≤_ a b          = Reg-ord b NN.≤ Reg-ord a
Reg-poset .Poset.≤-thin           = hlevel 1
Reg-poset .Poset.≤-refl           = NN.≤-refl
Reg-poset .Poset.≤-trans H≤ H≤'   = NN.≤-trans H≤' H≤
Reg-poset .Poset.≤-antisym H≤ H≤' = Reg-ord-injective (NN.≤-antisym H≤' H≤)

module Reg≤ = Poset Reg-poset

open Reg≤

Reg↓-poset : Poset lzero lzero
Reg↓-poset = Lower-sets Reg-poset

module Reg↓ = Poset Reg↓-poset

Reg↓ : Type
Reg↓ = ⌞ Reg↓-poset ⌟

Reg⊆-poset : Poset lzero lzero
Reg⊆-poset = Subsets Reg

module Reg⊆ = Poset Reg⊆-poset

Reg⊆ : Type
Reg⊆ = ⌞ Reg⊆-poset ⌟

Reg↓-lat : is-lattice Reg↓-poset
Reg↓-lat .is-lattice._∩_ a b     = Meet.glb (Lower-sets-meets Reg-poset a b)
Reg↓-lat .is-lattice.∩-meets a b = Meet.has-meet (Lower-sets-meets Reg-poset a b)
Reg↓-lat .is-lattice._∪_ a b     = Join.lub (Lower-sets-joins Reg-poset a b)
Reg↓-lat .is-lattice.∪-joins a b = Join.has-join (Lower-sets-joins Reg-poset a b)
Reg↓-lat .is-lattice.has-top     = Lower-sets-top Reg-poset
Reg↓-lat .is-lattice.has-bottom  = Lower-sets-bottom Reg-poset

module Reg↓-lat = is-lattice Reg↓-lat

Reg⊆-lat : is-lattice Reg⊆-poset
Reg⊆-lat = record
  { is-meet-semilattice Subsets-is-meet-slat
  ; is-join-semilattice Subsets-is-join-slat
  }

module Reg⊆-lat = is-lattice Reg⊆-lat

open Reg↓-lat

Forget-closure : Monotone Reg↓-poset Reg⊆-poset
Forget-closure .hom f     = f .hom
Forget-closure .pres-≤ Hf = Hf

Close-downward : Monotone Reg⊆-poset Reg↓-poset
Close-downward .hom f .hom x       = elΩ (Σ[ y ∈ Reg ] x ≤ y × ∣ f y ∣)
Close-downward .hom f .pres-≤ H≤ p = do
  (y , H≤' , Hy) ← p
  inc (y , ≤-trans H≤ H≤' , Hy)
Close-downward .pres-≤ H⊆ x p = do
  (y , H≤ , Hy) ← p
  inc (y , H≤ , H⊆ y Hy)

↓ : Reg → Reg↓
↓ = ↓ˡ Reg-poset

Ø↓ C↓ L↓ S↓ P↓ PC↓ PL↓ PS↓ A↓ : Reg↓.Ob
Ø↓  = bot
C↓  = ↓ C
L↓  = ↓ L
S↓  = ↓ S
P↓  = ↓ P
PC↓ = P↓ ∪ C↓
PL↓ = P↓ ∪ L↓
PS↓ = P↓ ∪ S↓
A↓  = ↓ A

_~ʳ_ : Reg⊆ → Reg⊆ → Type
X ~ʳ Y =
  (x : ∫ₚ X) (y : ∫ₚ Y) → x .fst ≤ y .fst →
  ∃[ z ∈ ∫ₚ (X Reg⊆-lat.∩ Y) ] x .fst ≤ z .fst × z .fst ≤ y .fst

is-meet-closed : Reg⊆ → Type
is-meet-closed X = (x x' : ∫ₚ X) →
    (∀ z → z ≤ x .fst → ¬ z ≤ x' .fst)
  ∗ (Σ[ m ∈ Meet Reg-poset (x .fst) (x' .fst) ] Meet.glb m ∈ X)

opaque
  unfolding Reg-ord

  Reg⊆-is-meet-closed : ∀ X → is-meet-closed X
  Reg⊆-is-meet-closed X (x , Hx) (A , Hx') =
    inr (record { glb = x ; has-meet = le→is-meet _ } , Hx)
  Reg⊆-is-meet-closed X (A , Hx) (x' , Hx') =
    inr (record { glb = x' ; has-meet = is-meet-sym (le→is-meet _) } , Hx')
  Reg⊆-is-meet-closed X (C , Hx) (C , Hx') =
    inr (record { glb = C ; has-meet = le→is-meet _ } , Hx)
  Reg⊆-is-meet-closed X (C , Hx) (L , Hx') =
    inr (record { glb = C ; has-meet = le→is-meet _ } , Hx)
  Reg⊆-is-meet-closed X (C , Hx) (S , Hx') =
    inr (record { glb = C ; has-meet = le→is-meet _ } , Hx)
  Reg⊆-is-meet-closed X (C , Hx) (P , Hx') = inl λ where C _ ()
  Reg⊆-is-meet-closed X (L , Hx) (C , Hx') =
    inr (record { glb = C ; has-meet = is-meet-sym (le→is-meet _) } , Hx')
  Reg⊆-is-meet-closed X (L , Hx) (L , Hx') =
    inr (record { glb = L ; has-meet = le→is-meet _ } , Hx)
  Reg⊆-is-meet-closed X (L , Hx) (S , Hx') =
    inr (record { glb = L ; has-meet = le→is-meet _ } , Hx)
  Reg⊆-is-meet-closed X (L , Hx) (P , Hx') = inl λ where C _ ()
  Reg⊆-is-meet-closed X (S , Hx) (C , Hx') =
    inr (record { glb = C ; has-meet = is-meet-sym (le→is-meet _) } , Hx')
  Reg⊆-is-meet-closed X (S , Hx) (L , Hx') =
    inr (record { glb = L ; has-meet = is-meet-sym (le→is-meet _) } , Hx')
  Reg⊆-is-meet-closed X (S , Hx) (S , Hx') =
    inr (record { glb = S ; has-meet = le→is-meet _ } , Hx)
  Reg⊆-is-meet-closed X (S , Hx) (P , Hx') = inl λ where C _ ()
  Reg⊆-is-meet-closed X (P , Hx) (C , Hx') = inl λ where C () _
  Reg⊆-is-meet-closed X (P , Hx) (L , Hx') = inl λ where C () _
  Reg⊆-is-meet-closed X (P , Hx) (S , Hx') = inl λ where C () _
  Reg⊆-is-meet-closed X (P , Hx) (P , Hx') =
    inr (record { glb = P ; has-meet = le→is-meet _ } , Hx)
