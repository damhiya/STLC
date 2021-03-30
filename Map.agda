open import Level
open import Data.Empty
open import Data.Product as Product
open import Data.Maybe as Maybe
open import Data.List hiding (lookup)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.Definitions

module Map {c} (K : Set c) (_≟_ : DecidableEquality K) where

private
  variable
    a : Level
    A : Set a
  
Map : Set a → Set (c ⊔ a)
Map A = List (K × A)

∅ : Map A
∅ = []

infixl 5 _+:_
_+:_ : Map A → K × A → Map A
M +: k:x = k:x ∷ M
  
infix 4 _∈_
data _∈_ {a} {A : Set a} : K × A → Map A → Set (c ⊔ a) where
  ∈-head : ∀ {M k x} → (k , x) ∈ M +: (k , x)
  ∈-cons : ∀ {M k k' x x'} → k ≢ k' → (k , x) ∈ M → (k , x) ∈ M +: (k' , x') 

k:x∉∅ : ∀ {k : K} {x : A} → (k , x) ∈ ∅ → ⊥
k:x∉∅ ()

∈-unique : ∀ {M : Map A} {k x₁ x₂} → (k , x₁) ∈ M → (k , x₂) ∈ M → x₁ ≡ x₂
∈-unique ∈-head ∈-head = refl
∈-unique (∈-cons k≢k _) ∈-head = ⊥-elim (k≢k refl)
∈-unique ∈-head (∈-cons k≢k _) = ⊥-elim (k≢k refl)
∈-unique (∈-cons _ ∈₁) (∈-cons _ ∈₂) = ∈-unique ∈₁ ∈₂

-- ∈-shadow : ∀ {M : Map A} {k k₁ x x₁ x₂} → (k , x) ∈ (M +: (k₁ , x₂)) → (k , x) ∈ (M +: (k₁ , x₁) +: (k₁ , x₂))
-- ∈-shadow ∈-head = ∈-head
-- ∈-shadow (∈-cons k≢k₁ x) = ∈-cons k≢k₁ (∈-cons k≢k₁ x)
  
lookup : (k : K) → (M : Map A) → Dec (∃[ x ] (k , x) ∈ M)
lookup k [] = no (λ (x , k:x∈∅) → k:x∉∅ k:x∈∅)
lookup k ((k' , x') ∷ M) with k ≟ k'
... | yes refl = yes (x' , ∈-head)
... | no  k≢k' with lookup k M
...   | yes (x , k:x∈M) = yes (x , ∈-cons k≢k' k:x∈M)
...   | no  ∄x[k:x∉M] = no λ where
  (x , ∈-head) → k≢k' refl
  (x , ∈-cons k≢k'₂ k:x∈M) → ∄x[k:x∉M] (x , k:x∈M)
  
