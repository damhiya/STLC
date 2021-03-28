module STLC where

open import Data.Product as P
open import Data.Maybe as M
open import Data.List hiding (lookup)
open import Data.Nat.Base renaming (ℕ to Name)
import Data.Nat.Properties as Name
open import Relation.Nullary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality.Core

data Type : Set where
  Base : Type
  Arr : Type → Type → Type

infix 4 _≟_
_≟_ : Decidable {A = Type} _≡_
Base ≟ Base = yes refl
Arr σ₁ τ₁ ≟ Arr σ₂ τ₂ with σ₁ ≟ σ₂ | τ₁ ≟ τ₂
... | yes refl | yes refl = yes refl
... | no σ₁≢σ₂ | _ = no (λ {refl → σ₁≢σ₂ refl})
... | _ | no τ₁≢τ₂ = no (λ {refl → τ₁≢τ₂ refl})
Base ≟ Arr σ τ = no (λ ())
Arr σ τ ≟ Base = no (λ ())
  
data Term : Set where
  Var : Name → Term
  Abs : Name → Type → Term → Term
  App : Term → Term → Term

data Value : Term → Set where
  VAbs : ∀ {x t σ} → Value (Abs x σ t)

Context : Set
Context = List (Name × Type)

infix 5 _+:_
_+:_ : Context → Name × Type → Context
Γ +: x:σ = x:σ ∷ Γ

infix 3 _∈_
data _∈_ : Name × Type → Context → Set where
  ∈-head : ∀ {Γ x σ} → (x , σ) ∈ Γ +: (x , σ) 
  ∈-cons : ∀ {Γ x₁ x₂ σ₁ σ₂} → x₁ ≢ x₂ → (x₁ , σ₁) ∈ Γ → (x₁ , σ₁) ∈ Γ +: (x₂ , σ₂)

lookup : (Γ : Context) → (x : Name) → Maybe (∃[ σ ] (x , σ) ∈ Γ)
lookup [] x = nothing
lookup ((x₂ , σ) ∷ xs) x₁ with x₁ Name.≟ x₂
... | yes refl = just (σ , ∈-head)
... | no x₁≢x₂ = M.map (map₂ (∈-cons x₁≢x₂)) (lookup xs x₁)

data TypeCheck (Γ : Context) : Term → Type → Set where
  TCVar : ∀ {x σ} → (x , σ) ∈ Γ → TypeCheck Γ (Var x) σ
  TCAbs : ∀ {x t σ τ} → TypeCheck (Γ +: (x , σ)) t τ → TypeCheck Γ (Abs x σ t) (Arr σ τ)
  TCApp : ∀ {t₁ t₂ σ τ} → TypeCheck Γ t₁ (Arr σ τ) → TypeCheck Γ t₂ σ → TypeCheck Γ (App t₁ t₂) τ

type-check : (Γ : Context) → (t : Term) → Maybe (∃[ τ ] TypeCheck Γ t τ)
type-check Γ (Var x) = M.map (P.map₂ TCVar) (lookup Γ x)
type-check Γ (Abs x σ t) = M.map (P.map (λ τ → Arr σ τ) TCAbs) (type-check (Γ +: (x , σ)) t)
type-check Γ (App t₁ t₂) = type-check Γ t₁ >>= λ where
    (Base     , tc₁) → nothing
    (Arr σ₁ τ , tc₁) → type-check Γ t₂ >>= λ {(σ₂ , tc₂) → app σ₁ σ₂ τ tc₁ tc₂}
  where
    app : ∀ σ₁ σ₂ τ → TypeCheck Γ t₁ (Arr σ₁ τ) → TypeCheck Γ t₂ σ₂ → Maybe (∃[ τ ] TypeCheck Γ (App t₁ t₂) τ)
    app σ₁ σ₂ with σ₁ ≟ σ₂
    ... | yes refl = λ τ tc₁ tc₂ → just (τ , TCApp tc₁ tc₂)
    ... | no σ₁≢σ₂ = λ τ tc₁ tc₂ → nothing
