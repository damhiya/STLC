module STLC.Normalization where

open import Function.Base
open import Induction.WellFounded

open import STLC.Syntax
open import STLC.Typing
open import STLC.Substitution

data _⟶ᵦ_ : Term → Term → Set where
  β : ∀ {Γ x t₁ t₂ σ τ}
      ([Γ,x∶σ]⊢t₁∶τ : [ Γ , x ∶ σ ] ⊢ t₁ ∶ τ)
      (Γ⊢t₂∶σ : Γ ⊢ t₂ ∶ σ) →
      app (lam x σ t₁) t₂ ⟶ᵦ subst₁ [Γ,x∶σ]⊢t₁∶τ Γ⊢t₂∶σ
  β-appˡ : ∀ {t₁ t₁′ t₂} → t₁ ⟶ᵦ t₁′ → app t₁ t₂ ⟶ᵦ app t₁′ t₂
  β-appʳ : ∀ {t₁ t₂ t₂′} → t₂ ⟶ᵦ t₂′ → app t₁ t₂ ⟶ᵦ app t₁ t₂′
  β-lam : ∀ {x σ t t′} → t ⟶ᵦ t′ → lam x σ t ⟶ᵦ lam x σ t′

sn : Term → Set
sn = Acc (flip _⟶ᵦ_)
