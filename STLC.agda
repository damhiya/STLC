module STLC where

open import Data.List hiding (lookup)
  
open import Function.Base
open import Data.Empty
open import Data.Product as P
open import Data.Maybe as M
open import Relation.Nullary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality.Core hiding (subst)

import Data.Nat.Base as Nat
import Data.Nat.Properties as Name

Name : Set
Name = Nat.ℕ

_name≟_ : DecidableEquality Name
_name≟_ = Name._≟_

import Map
open Map Name _name≟_
  
data Type : Set where
  Base : Type
  Arr : Type → Type → Type

infix 4 _≟_
_≟_ : Decidable {A = Type} _≡_
Base ≟ Base = yes refl
Arr σ₁ τ₁ ≟ Arr σ₂ τ₂ with σ₁ ≟ σ₂ | τ₁ ≟ τ₂
... | yes refl | yes refl = yes refl
... | no σ₁≢σ₂ | _ = no λ {refl → σ₁≢σ₂ refl}
... | _ | no τ₁≢τ₂ = no λ {refl → τ₁≢τ₂ refl}
Base ≟ Arr σ τ = no λ ()
Arr σ τ ≟ Base = no λ ()

data Term : Set where
  Var : Name → Term
  Abs : Name → Type → Term → Term
  App : Term → Term → Term

data Value : Term → Set where
  VAbs : ∀ {x t σ} → Value (Abs x σ t)

Context : Set
Context = Map Type

infix 5 _⊢_
data _⊢_ (Γ : Context) : (Term × Type) → Set where
  TCVar : ∀ {x σ} → (x , σ) ∈ Γ → Γ ⊢ (Var x , σ)
  TCAbs : ∀ {x t σ τ} → (Γ +: (x , σ)) ⊢ (t , τ) → Γ ⊢ (Abs x σ t , Arr σ τ)
  TCApp : ∀ {t₁ t₂ σ τ} → Γ ⊢ (t₁ , Arr σ τ) → Γ ⊢ (t₂ , σ) → Γ ⊢ (App t₁ t₂ , τ)

Base≢σ→τ : ∀ {σ τ} → Base ≡ Arr σ τ → ⊥
Base≢σ→τ ()
  
type-unique : ∀ {Γ t τ₁ τ₂} → Γ ⊢ (t , τ₁) → Γ ⊢ (t , τ₂) → τ₁ ≡ τ₂
type-unique {t = Var x} (TCVar x:τ₁∈Γ) (TCVar x:τ₂∈Γ) = ∈-unique x:τ₁∈Γ x:τ₂∈Γ
type-unique {t = Abs x σ t} (TCAbs tc₁) (TCAbs tc₂) = cong (Arr σ) (type-unique tc₁ tc₂)
type-unique {t = App t₁ t₂} (TCApp tc₁ _) (TCApp tc₂ _) with type-unique tc₁ tc₂
... | refl = refl

type-check : (Γ : Context) → (t : Term) → Dec (∃[ τ ] Γ ⊢ (t , τ))
type-check Γ (Var x) with lookup x Γ
... | yes (σ , x:σ∈Γ) = yes (σ , TCVar x:σ∈Γ) 
... | no ∄σ[x:σ∈Γ] = no λ where (τ , TCVar x:τ∈Γ) → ∄σ[x:σ∈Γ] (τ , x:τ∈Γ)
type-check Γ (Abs x σ t) with type-check (Γ +: (x , σ)) t
... | yes (τ , Γ,x:σ⊢t:τ) = yes (Arr σ τ , TCAbs Γ,x:σ⊢t:τ)
... | no ∄τ[Γ,x:σ⊢t:τ] = no λ where (Arr σ τ , TCAbs Γ,x:σ⊢t:τ) → ∄τ[Γ,x:σ⊢t:τ] (τ , Γ,x:σ⊢t:τ)
type-check Γ (App t₁ t₂) with type-check Γ t₁
... | no ∄σ[Γ⊢t₁:σ] = no λ where (τ , TCApp {σ = σ} Γ⊢t₁:σ→τ tc) → ∄σ[Γ⊢t₁:σ] (Arr σ τ , Γ⊢t₁:σ→τ)
... | yes (Base , Γ⊢t₁:Base) = no λ where (τ , TCApp {σ = σ} Γ⊢t₁:σ→τ _) → (⊥-elim ∘ Base≢σ→τ) (type-unique Γ⊢t₁:Base Γ⊢t₁:σ→τ)
... | yes (Arr σ₁ τ , Γ⊢t₁:σ₁→τ) with type-check Γ t₂
...   | no ∄σ[Γ⊢t₂:σ] = no λ where (τ , TCApp {σ = σ} _ Γ⊢t₂:σ) → ∄σ[Γ⊢t₂:σ] (σ , Γ⊢t₂:σ)
...   | yes (σ₂ , Γ⊢t₂:σ₂) with σ₁ ≟ σ₂
...     | yes refl = yes (τ , TCApp Γ⊢t₁:σ₁→τ Γ⊢t₂:σ₂) 
...     | no σ₁≢σ₂ = no λ where
  (τ , TCApp {σ = σ} Γ⊢t₁:σ→τ Γ⊢t₂:σ) → case (type-unique Γ⊢t₁:σ₁→τ Γ⊢t₁:σ→τ , type-unique Γ⊢t₂:σ₂ Γ⊢t₂:σ) of λ where
    (refl , refl) → σ₁≢σ₂ refl

-- strict fresh variable
data _#'_ : Name → Term → Set where
  #'-Var : ∀ {x x'} → x ≢ x' → x #' Var x'
  #'-Abs : ∀ {x x' t σ} → x ≢ x' → x #' t → x #' Abs x' σ t
  #'-App : ∀ {x t₁ t₂} → x #' t₁ → x #' t₂ → x #' App t₁ t₂

data Lift (x : Name) : Context → Context → Set where
  LiftOne : ∀ {Γ σ} → Lift x Γ (Γ +: (x , σ))
  LiftCons : ∀ {Γ₁ Γ₂ x' σ'} → Lift x Γ₁ Γ₂ → Lift x (Γ₁ +: (x' , σ')) (Γ₂ +: (x' , σ'))

lift-var : ∀ {Γ₁ Γ₂ x x' σ'} → x ≢ x' → Lift x Γ₁ Γ₂ → (x' , σ') ∈ Γ₁ → (x' , σ') ∈ Γ₂
lift-var neq LiftOne a = ∈-cons (≢-sym neq) a
lift-var neq (LiftCons lf) ∈-head = ∈-head
lift-var neq (LiftCons lf) (∈-cons x≢x₁ a) = ∈-cons x≢x₁ (lift-var neq lf a)

lift : ∀ {Γ₁ Γ₂ x t τ} → x #' t → Lift x Γ₁ Γ₂ → Γ₁ ⊢ (t , τ) → Γ₂ ⊢ (t , τ)
lift {Γ₁} {Γ₂} {x} {t} {τ} (#'-Var x≢x') lf (TCVar a) = TCVar (lift-var x≢x' lf a)
lift {Γ₁} {Γ₂} {x} {Abs x₁ σ₁ t₁} {Arr σ₁ τ₁} (#'-Abs _ x#'t₁) lf (TCAbs Γ,x₁:σ₁⊢t₁:τ₁) = TCAbs (lift x#'t₁ (LiftCons lf) Γ,x₁:σ₁⊢t₁:τ₁)
lift {Γ₁} {Γ₂} {x} {t} {τ} (#'-App #₁ #₂) lf (TCApp a b) = TCApp (lift #₁ lf a) (lift #₂ lf b)

grow-context : ∀ {Γ x t σ τ} → x #' t → Γ ⊢ (t , τ) → (Γ +: (x , σ)) ⊢ (t , τ)
grow-context x#'t Γ⊢t:τ = lift x#'t LiftOne Γ⊢t:τ
