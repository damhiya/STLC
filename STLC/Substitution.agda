module STLC.Substitution where

open import Data.Product
open import Relation.Binary.PropositionalEquality.Core

open import STLC.Variable
open import STLC.Syntax
open import STLC.Typing

data Weakening : Context → Context → Set where
  weak-base : ∀ {Γ z σ} → z ∉ Γ → Weakening Γ [ Γ , z ∶ σ ]
  weak-ind : ∀ {Γ Δ z σ} → Weakening Γ Δ → Weakening [ Γ , z ∶ σ ] [ Δ , z ∶ σ ]

weakening-var : ∀ {Γ Δ x} → Weakening Γ Δ → x ∈ Γ → x ∈ Δ
weakening-var (weak-base z∉Γ) x∈Γ = (λ x≡z → z∉Γ (subst _ x≡z x∈Γ)) ∷ x∈Γ
weakening-var (weak-ind Γ⇒Δ) [ refl ] = [ refl ]
weakening-var (weak-ind Γ⇒Δ) (x≢y ∷ x∈Γ) = x≢y ∷ weakening-var Γ⇒Δ x∈Γ

weakening-var-⟨⟩ : ∀ {Γ Δ x} → (Γ⇒Δ : Weakening Γ Δ) → (x∈Γ : x ∈ Γ) → Δ ⟨ weakening-var Γ⇒Δ x∈Γ ⟩ ≡ Γ ⟨ x∈Γ ⟩
weakening-var-⟨⟩ (weak-base z∉Γ) x∈Γ = refl
weakening-var-⟨⟩ (weak-ind Γ⇒Δ) [ refl ] = refl
weakening-var-⟨⟩ (weak-ind Γ⇒Δ) (x≢y ∷ x∈Γ) = weakening-var-⟨⟩ Γ⇒Δ x∈Γ
  
weakening : ∀ {Γ Δ t τ} → Weakening Γ Δ → Γ ⊢ t ∶ τ → Δ ⊢ t ∶ τ
weakening {Δ = Δ} {t = t} {τ = τ} Γ⇒Δ (⊢var x∈Γ) = subst (λ τ → Δ ⊢ t ∶ τ) (weakening-var-⟨⟩ Γ⇒Δ x∈Γ) (⊢var (weakening-var Γ⇒Δ x∈Γ))
weakening Γ⇒Δ (⊢lam [Γ,x∶σ]⊢t∶τ) = ⊢lam (weakening (weak-ind Γ⇒Δ) [Γ,x∶σ]⊢t∶τ)
weakening Γ⇒Δ (⊢app ⊢₁ ⊢₂) = ⊢app (weakening Γ⇒Δ ⊢₁) (weakening Γ⇒Δ ⊢₂)
  
weakening₁ : ∀ {Γ z t σ τ} → z ∉ Γ → Γ ⊢ t ∶ τ → [ Γ , z ∶ σ ] ⊢ t ∶ τ
weakening₁ z∉Γ = weakening (weak-base z∉Γ)

data Subst : Context → Context → Set where
  subst₁ : ∀ {Γ} x t τ → Γ ⊢ t ∶ τ → Subst [ Γ , x ∶ τ ] Γ
  rebind : ∀ {Γ Δ} x z σ → z ∉ Δ → Subst Γ Δ → Subst [ Γ , x ∶ σ ] [ Δ , z ∶ σ ]

module _ where
  open import Function.Base
  open import Data.Nat.Base
  open import Data.Nat.Properties as ℕ
  open import Data.List as List
  open import Data.List.Extrema ℕ.≤-totalOrder
  open import Data.List.Relation.Unary.All as All
  open import Data.List.Relation.Unary.First.Properties
  
  χ : Context → Var
  χ ∅ = zero
  χ [ Γ , x ∶ σ ] = (suc ∘ proj₁ ∘ argmax proj₁ (x , σ)) Γ
  
  χ-∉ : ∀ {Γ} → χ Γ ∉ Γ
  χ-∉ {∅} ()
  χ-∉ {Γ@([ Δ , x ∶ σ ])} [ χ[Γ]≡x ] = χ[Γ]≢x χ[Γ]≡x
    where
      χ[Γ]≢x : χ Γ ≢ x
      χ[Γ]≢x = (≢-sym ∘ <⇒≢ ∘ s≤s) (f[⊥]≤f[argmax] {f = proj₁} (x , σ) Δ)
  χ-∉ {Γ@([ Δ , x ∶ σ ])} (y ∷ x∈Δ) = All⇒¬First id all-≢ x∈Δ
    where
      all-≢ : All (λ x → χ Γ ≢ proj₁ x ) Δ
      all-≢ = All.map (≢-sym ∘ <⇒≢ ∘ s≤s) (f[xs]≤f[argmax] {f = proj₁} (x , σ) Δ)

subst-var : ∀ {Γ Δ x} → Subst Γ Δ → x ∈ Γ → Term
subst-var {[ Γ , x ∶ σ ]} {x = x} (subst₁ x t σ Γ⊢t∶τ) [ refl ] = t
subst-var {[ Γ , y ∶ σ ]} {x = x} (subst₁ y t τ Γ⊢t∶τ) (x≢y ∷ x∈Γ) = var x
subst-var {[ Γ , x ∶ σ ]} {x = x} (rebind x z σ z∉Δ Γ⇒Δ) [ refl ] = var z
subst-var {[ Γ , y ∶ σ ]} {x = x} (rebind y z σ z∉Δ Γ⇒Δ) (x≢y ∷ x∈Γ) = subst-var Γ⇒Δ x∈Γ

subst-var-⟨⟩ : ∀ {Γ Δ x} (s : Subst Γ Δ) (x∈Γ : x ∈ Γ) → Δ ⊢ subst-var s x∈Γ ∶ Γ ⟨ x∈Γ ⟩
subst-var-⟨⟩ {[ Γ , x ∶ σ ]} {x = x} (subst₁ x t σ Γ⊢t∶τ) [ refl ] = Γ⊢t∶τ
subst-var-⟨⟩ {[ Γ , y ∶ σ ]} {x = x} (subst₁ y t τ Γ⊢t∶τ) (x≢y ∷ x∈Γ) = ⊢var x∈Γ
subst-var-⟨⟩ {[ Γ , x ∶ σ ]} {x = x} (rebind x z σ z∉Δ s) [ refl ] = ⊢var [ refl ]
subst-var-⟨⟩ {[ Γ , y ∶ σ ]} {x = x} (rebind y z σ z∉Δ s) (x≢y ∷ x∈Γ) = weakening₁ z∉Δ (subst-var-⟨⟩ s x∈Γ)

apply-subst : ∀ {Γ Δ τ} → Subst Γ Δ → ∃[ t ] Γ ⊢ t ∶ τ → ∃[ t ] Δ ⊢ t ∶ τ
apply-subst Γ⇒Δ (var x , ⊢var x∈Γ) = subst-var Γ⇒Δ x∈Γ , subst-var-⟨⟩ Γ⇒Δ x∈Γ
apply-subst {Δ = Δ} Γ⇒Δ (lam x σ t , ⊢lam ⊢₁) = map (lam _ σ) ⊢lam (apply-subst (rebind x (χ Δ) σ χ-∉ Γ⇒Δ) (t , ⊢₁))
apply-subst Γ⇒Δ (app t₁ t₂ , ⊢app ⊢₁ ⊢₂) = zip app ⊢app (apply-subst Γ⇒Δ (t₁ , ⊢₁)) (apply-subst Γ⇒Δ (t₂ , ⊢₂))
