module start where

open import Relation.Binary.PropositionalEquality
open import Data.Product


injective : {A B : Set} → (f : A → B) → Set
injective f = ∀ a₁ a₂ → f a₁ ≡ f a₂ → a₁ ≡ a₂

surjective : {A B : Set} → (f : A → B) → Set
surjective f = ∀ b → ∃ (λ a → f a ≡ b)

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ


lemma-suc-inj : ∀ {a₁ a₂} → suc a₁ ≡ suc a₂ → a₁ ≡ a₂
lemma-suc-inj refl = refl

suc-injective : injective suc
suc-injective a₁ a₂ x = lemma-suc-inj x

id : {A : Set} → A → A
id x = x

lemma-idℕ-surj : ∀ (b : ℕ) → ∃ (λ a → id a ≡ b)
lemma-idℕ-surj b = b , refl

idℕ-surjective : surjective (id {ℕ})
idℕ-surjective = lemma-idℕ-surj
