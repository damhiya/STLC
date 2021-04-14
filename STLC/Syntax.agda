module STLC.Syntax where

open import Level
open import Relation.Nullary
open import Relation.Binary.Definitions
open import Relation.Binary.Structures
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality.Properties

open import STLC.Variable using (Var)

infixr 5 _⟶_
data Type : Set where
  base : Type
  _⟶_ : Type → Type → Type

infix 4 _≟_
_≟_ : Decidable {A = Type} _≡_
base ≟ base = yes refl
σ₁ ⟶ τ₁ ≟ σ₂ ⟶ τ₂ with σ₁ ≟ σ₂ | τ₁ ≟ τ₂
... | yes refl | yes refl = yes refl
... | no σ₁≢σ₂ | yes refl = no λ {refl → σ₁≢σ₂ refl}
... | no σ₁≢σ₂ | no τ₁≢τ₂ = no λ {refl → σ₁≢σ₂ refl}
... | yes refl | no τ₁≢τ₂ = no λ {refl → τ₁≢τ₂ refl}
base ≟ σ ⟶ τ = no λ ()
σ ⟶ τ ≟ base = no λ ()

≡-isDecEquivalence : IsDecEquivalence (_≡_ {A = Type})
≡-isDecEquivalence = record
  { isEquivalence = isEquivalence
  ; _≟_ = _≟_
  }

≡-decSetoid : DecSetoid 0ℓ 0ℓ
≡-decSetoid = record
  { Carrier = Type
  ; _≈_ = _≡_
  ; isDecEquivalence = ≡-isDecEquivalence
  }

data Term : Set where
  var : Var → Term
  lam : Var → Type → Term → Term
  app : Term → Term → Term
