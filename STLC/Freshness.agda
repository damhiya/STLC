module STLC.Freshness where

open import Relation.Binary.PropositionalEquality.Core hiding (subst)

open import STLC.Variable
open import STLC.Syntax
open import STLC.Typing

data _#_ : Var → Term → Set where
  #-var : ∀ {x y} → x ≢ y → x # var y
  #-lam₁ : ∀ {x t σ} → x # lam x σ t
  #-lam₂ : ∀ {x y t σ} → x ≢ y → x # t → x # lam y σ t
  #-app : ∀ {x t₁ t₂} → x # t₁ → x # t₂ → x # app t₁ t₂


