module STLC.Typing where

open import Function.Base
open import Data.Product
open import Data.Bool
open import Data.Maybe as Maybe
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.Core

open import STLC.Variable as Variable
open import STLC.Syntax as Syntax
open import Data.Map Var Variable._≟_ public

Context : Set
Context = Map Type

infix 3 _⊢_∶_
data _⊢_∶_ (Γ : Context) : Term → Type → Set where
  ⊢var : ∀ {x} → (x∈Γ : x ∈ Γ) → Γ ⊢ var x ∶ Γ ⟨ x∈Γ ⟩
  ⊢lam : ∀ {x t σ τ} → [ Γ , x ∶ σ ] ⊢ t ∶ τ → Γ ⊢ lam x σ t ∶ σ ⟶ τ
  ⊢app : ∀ {t₁ t₂ σ τ} → Γ ⊢ t₁ ∶ σ ⟶ τ → Γ ⊢ t₂ ∶ σ → Γ ⊢ app t₁ t₂ ∶ τ

⊢check : (Γ : Context) → (t : Term) → Maybe (∃[ τ ] Γ ⊢ t ∶ τ)
⊢check Γ (var x) = (Maybe.map (λ x∈Γ → Γ ⟨ x∈Γ ⟩ , ⊢var x∈Γ) ∘ decToMaybe) (x ∈? Γ)
⊢check Γ (lam x σ t) = Maybe.map
  (λ where (τ , [Γ,x∶σ]⊢t∶τ) → (σ ⟶ τ , ⊢lam [Γ,x∶σ]⊢t∶τ))
  (⊢check ([ Γ , x ∶ σ ]) t)
⊢check Γ (app t₁ t₂) = Maybe.zip (⊢check Γ t₁) (⊢check Γ t₂) >>= λ
  { ((base , _) , _) → nothing
  ; ((σ₁ ⟶ τ , Γ⊢t₁∶σ₁→τ) , (σ₂ , Γ⊢t₂∶σ₂)) → case (σ₁ Syntax.≟ σ₂) of λ
    { (yes σ₁≡σ₂) → just (τ , ⊢app (subst _ σ₁≡σ₂ Γ⊢t₁∶σ₁→τ) Γ⊢t₂∶σ₂)
    ; (no  σ₁≢σ₂) → nothing
    }
  }

⊢check-does : (Γ : Context) → (t : Term) → Bool
⊢check-does Γ t = is-just (⊢check Γ t)

≡-domain : ∀ {σ₁ σ₂ τ₁ τ₂} → σ₁ ⟶ τ₁ ≡ σ₂ ⟶ τ₂ → σ₁ ≡ σ₂
≡-domain refl = refl

≡-codomain : ∀ {σ₁ σ₂ τ₁ τ₂} → σ₁ ⟶ τ₁ ≡ σ₂ ⟶ τ₂ → τ₁ ≡ τ₂
≡-codomain refl = refl

⊢! : ∀ {Γ t τ₁ τ₂} → Γ ⊢ t ∶ τ₁ → Γ ⊢ t ∶ τ₂ → τ₁ ≡ τ₂
⊢! {t = var x} (⊢var x∈Γ₁) (⊢var x∈Γ₂) = ⟨⟩-unique x∈Γ₁ x∈Γ₂
⊢! {t = lam x σ t} (⊢lam ⊢₁) (⊢lam ⊢₂) = cong (σ ⟶_) (⊢! ⊢₁ ⊢₂)
⊢! {t = app t₁ t₂} (⊢app ⊢₁ _) (⊢app ⊢₂ _) = ≡-codomain (⊢! ⊢₁ ⊢₂)

base≢σ→τ : ∀ {σ τ} → base ≢ σ ⟶ τ
base≢σ→τ ()

⊢check-reflects : (Γ : Context) (t : Term) → Reflects (∃[ τ ] Γ ⊢ t ∶ τ) (⊢check-does Γ t)
⊢check-reflects Γ (var x) with x ∈? Γ
... | yes x∈Γ = ofʸ (Γ ⟨ x∈Γ ⟩ , ⊢var x∈Γ)
... | no  x∉Γ = ofⁿ λ where (_ , ⊢var x∈Γ) → x∉Γ x∈Γ
⊢check-reflects Γ (lam x σ t) with ⊢check [ Γ , x ∶ σ ] t | ⊢check-reflects [ Γ , x ∶ σ ] t
... | just _  | ofʸ (τ , [Γ,x∶σ]⊢t∶τ) = ofʸ (σ ⟶ τ , ⊢lam [Γ,x∶σ]⊢t∶τ)
... | nothing | ofⁿ ∄τ[[Γ,x∶σ]⊢t∶τ] = ofⁿ λ where (_ , ⊢lam [Γ,x∶σ]⊢t∶τ) → ∄τ[[Γ,x∶σ]⊢t∶τ] (_ , [Γ,x∶σ]⊢t∶τ)
⊢check-reflects Γ (app t₁ t₂) with ⊢check Γ t₁ | ⊢check Γ t₂ | ⊢check-reflects Γ t₁ | ⊢check-reflects Γ t₂
... | nothing | _ | ofⁿ ∄τ[Γ⊢t₁∶τ] | _ = ofⁿ λ where (_ , ⊢app Γ⊢t₁∶σ→τ _) → ∄τ[Γ⊢t₁∶τ] (_ , Γ⊢t₁∶σ→τ)
... | just _  | nothing | ofʸ _ | ofⁿ ∄τ[Γ⊢t₂∶τ] = ofⁿ λ where (_ , ⊢app _ Γ⊢t₂∶τ) → ∄τ[Γ⊢t₂∶τ] (_ , Γ⊢t₂∶τ)
... | just (_ , Γ⊢t₁∶τ₁) | just (_ , Γ⊢t₂∶σ₁)
    | ofʸ (_ , Γ⊢t₁∶τ₂)  | ofʸ (_ , Γ⊢t₂∶σ₂) with ⊢! Γ⊢t₁∶τ₁ Γ⊢t₁∶τ₂ | ⊢! Γ⊢t₂∶σ₁ Γ⊢t₂∶σ₂
⊢check-reflects Γ (app t₁ t₂)
  | just (base , _)        | just (σ , _)
  | ofʸ (base , Γ⊢t₁∶base) | ofʸ (σ , _) | refl | refl = ofⁿ λ where
  (_ , ⊢app Γ⊢t₁∶σ→τ _) → base≢σ→τ (⊢! Γ⊢t₁∶base Γ⊢t₁∶σ→τ)
⊢check-reflects Γ (app t₁ t₂)
  | just (σ₁ ⟶ τ , _)        | just (σ₂ , _)
  | ofʸ (σ₁ ⟶ τ , Γ⊢t₁∶σ₁→τ) | ofʸ (σ₂ , Γ⊢t₂∶σ₂) | refl | refl with σ₁ Syntax.≟ σ₂
... | yes refl = ofʸ (τ , ⊢app Γ⊢t₁∶σ₁→τ Γ⊢t₂∶σ₂)
... | no σ₁≢σ₂ = ofⁿ λ where
  (_ , ⊢app {σ = σ} Γ⊢t₁∶σ→τ Γ⊢t₂∶σ) → σ₁≢σ₂ $ trans (≡-domain (⊢! Γ⊢t₁∶σ₁→τ Γ⊢t₁∶σ→τ)) ( ⊢! Γ⊢t₂∶σ Γ⊢t₂∶σ₂)
