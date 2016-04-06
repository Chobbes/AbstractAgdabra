module start where

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Function hiding (id)


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

left-inverse : ∀ {A B} → (f : A → B) → Set
left-inverse f = ∃ (λ g → g ∘ f ≡ id)

right-inverse : ∀ {A B} → (f : A → B) → Set
right-inverse f = ∃ (λ g → f ∘ g ≡ id)

lemma-comp : ∀ {A B : Set} {a : A} {g : B → A} {f : A → B} → ((λ x → g x) ∘ f) a ≡ g (f a)
lemma-comp = refl

infix 5 _s~_
_s~_ : {A : Set} {a b c : A} → a ≡ b → a ≡ c → c ≡ b
_s~_ refl refl = refl

infix 5 _~_
_~_ : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
_~_ = trans


lemma-left-id₁ : ∀ {A B : Set} {a : A} {g : B → A} {f : A → B} → g ∘ f ≡ id → g (f a) ≡ a
lemma-left-id₁ {A} {B} {a} {g} {f} idcomp = cong (λ f₁ → f₁ a) idcomp s~ (lemma-comp {A} {B} {a} {g} {f})

lemma-left-id : ∀ {A B : Set} {a₁ a₂ : A} {g : B → A} {f : A → B} → g ∘ f ≡ id → g (f a₁) ≡ g (f a₂) → a₁ ≡ a₂
lemma-left-id {A} {B} {a₁} {a₂} {g} {f} idcomp comp = (comp ~ lemma-left-id₁ {A} {B} {a₂} {g} {f} idcomp) s~ lemma-left-id₁ {A} {B} {a₁} {g} {f} idcomp

lemma-left-inj : ∀ {A B : Set} {a₁ a₂ : A} → (f : A → B) → ∃ (λ g → g ∘ f ≡ id) → f a₁ ≡ f a₂ → a₁ ≡ a₂
lemma-left-inj {A} {B} {a₁} {a₂} f (g , idcomp) eq = lemma-left-id {A} {B} {a₁} {a₂} {g} {f} idcomp (cong (λ x → g x) eq)

left-inverse→injective : ∀ {A B} (f : A → B) → left-inverse f → injective f
left-inverse→injective f left-inv a₁ a₂ fas = lemma-left-inj f left-inv fas
