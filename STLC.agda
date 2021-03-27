module STLC where

open import Data.Product
open import Data.Maybe
open import Data.List
open import Data.Nat.Base renaming (ℕ to Name)

data Type : Set where
  Base : Type
  Arr : Type → Type → Type
  
data Term : Set where
  Var : Name → Term
  Abs : Name → Type → Term → Term
  App : Term → Term → Term

data Value : Term → Set where
  VAbs : ∀ {x ty tm} → Value (Abs x ty tm)

Context : Set
Context = List (Name × Type)

data _∈_ {A : Set} : A → List A → Set where
  ∈-head : ∀ {x xs} → x ∈ (x ∷ xs)
  ∈-cons : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)
  
data TypeCheck (Γ : Context) : Term → Type → Set where
  TCVar : ∀ {x σ} → (x , σ) ∈ Γ → TypeCheck Γ (Var x) σ
  TCAbs : ∀ {x e σ τ} → TypeCheck ((x , σ) ∷ Γ) e τ → TypeCheck Γ (Abs x σ e) (Arr σ τ)
  TCApp : ∀ {e₁ e₂ σ τ} → TypeCheck Γ e₁ (Arr σ τ) → TypeCheck Γ e₂ σ → TypeCheck Γ (App e₁ e₂) τ

type-check : (Γ : Context) → (e : Term) → Maybe (∃[ τ ] TypeCheck Γ e τ)
type-check = {!!}
