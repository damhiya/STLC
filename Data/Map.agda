open import Relation.Binary.Definitions using (DecidableEquality)

module Data.Map {c} (K : Set c) (_≟_ : DecidableEquality K) where

open import Level
open import Function.Base
open import Data.Empty
open import Data.Product
open import Data.List
open import Data.List.Relation.Unary.First
open import Data.List.Relation.Unary.First.Properties
open import Relation.Binary.PropositionalEquality.Core

private
  variable
    a : Level
    A : Set a

Map : Set a → Set (c ⊔ a)
Map A = List (K × A)

pattern ∅ = []
pattern _∷[_∶_] M k x = (k , x) ∷ M

_∈_ : K → Map A → Set _
k ∈ M = First (_≢_ k ∘ proj₁) (_≡_ k ∘ proj₁) M

_∉_ : K → Map A → Set _
k ∉ M = k ∈ M → ⊥

_⟨_⟩ : ∀ {k} (M : Map A) → k ∈ M → A
M ⟨ k∈M ⟩ = (proj₂ ∘ lookup M ∘ index) k∈M

⟨⟩-unique : ∀ {M : Map A} {k} (k∈M₁ k∈M₂ : k ∈ M) → M ⟨ k∈M₁ ⟩ ≡ M ⟨ k∈M₂ ⟩
⟨⟩-unique {M = M} k∈M₁ k∈M₂ = cong (proj₂ ∘ lookup M) (unique-index id k∈M₁ k∈M₂)

module _ {a p} {A : Set a} where
  open import Relation.Unary
  import Data.Sum as Sum

  first?′ : ∀ {P : Pred A p} → Decidable P → Decidable (First (∁ P) P)
  first?′ P? xs = Sum.toDec
                $ Sum.map₂ (All⇒¬First id)
                $ first (Sum.swap ∘ Sum.fromDec ∘ P?) xs

open import Relation.Binary.Definitions
_∈?_ : ∀ {A : Set a} → Decidable (_∈_ {A = A})
k ∈? M = first?′ (_≟_ k ∘ proj₁) M
