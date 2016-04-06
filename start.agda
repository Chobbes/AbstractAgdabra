module start where

open import Relation.Binary.PropositionalEquality
open import Data.Product


injective : {A B : Set} → (f : A → B) → Set
injective f = ∀ a₁ a₂ → f a₁ ≡ f a₂ → a₁ ≡ a₂

surjective : {A B : Set} → (f : A → B) → Set
surjective f = ∀ b → ∃ (λ a → f a ≡ b)

bijective : {A B : Set} → (f : A → B) → Set
bijective f = injective f × surjective f

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ


lemma-suc-inj : ∀ {a₁ a₂} → suc a₁ ≡ suc a₂ → a₁ ≡ a₂
lemma-suc-inj refl = refl

suc-injective : injective suc
suc-injective a₁ a₂ = lemma-suc-inj

id : {A : Set} → A → A
id x = x

lemma-id-inj : ∀ {A} {a₁ a₂ : A} → id a₁ ≡ id a₂ → a₁ ≡ a₂
lemma-id-inj refl = refl

id-injective : ∀ {A} → injective (id {A})
id-injective a₁ a₂ = lemma-id-inj

lemma-id-surj : ∀ {A} (b : A) → ∃ (λ a → id a ≡ b)
lemma-id-surj b = b , refl

id-surjective : ∀ {A} → surjective (id {A})
id-surjective = lemma-id-surj

bijective→injective : ∀ {A B} {f : A → B} → bijective f → injective f
bijective→injective b = proj₁ b

bijective→surjective : ∀ {A B} {f : A → B} → bijective f → surjective f
bijective→surjective b = proj₂ b

