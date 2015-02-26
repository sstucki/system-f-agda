------------------------------------------------------------------------
-- Polymorphic and iso-recursive types
------------------------------------------------------------------------

module SystemF.Type where

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Nat using (ℕ; _+_)
open import Data.Star using (Star; ε; _◅_)
open import Data.Vec using (Vec; []; _∷_; lookup; map)
open import Relation.Binary.PropositionalEquality as PropEq
  using (refl; _≡_; cong; cong₂; sym)
open PropEq.≡-Reasoning

------------------------------------------------------------------------
-- Polymorphic and iso-recursive types

infixr 7 _→'_

-- Types with up to n free type variables
data Type (n : ℕ) : Set where
  var  : Fin n           → Type n   -- type variable
  _→'_ : Type n → Type n → Type n   -- arrow/function type
  ∀'   : Type (1 + n)    → Type n   -- universal type
  μ    : Type (1 + n)    → Type n   -- recursive type


------------------------------------------------------------------------
-- Substitutions in types

module TypeSubst where
  module TypeApp {T} (l : Lift T Type) where
    open Lift l hiding (var)

    infixl 8 _/_

    -- Apply a substitution to a type
    _/_ : ∀ {m n} → Type m → Sub T m n → Type n
    var x    / σ = lift (lookup x σ)
    (a →' b) / σ = (a / σ) →' (b / σ)
    ∀' a     / σ = ∀' (a / σ ↑)
    μ a      / σ = μ (a / σ ↑)

    open Application (record { _/_ = _/_ }) using (_/✶_)

    -- Helper lemmas relating application of simple substitutions (_/_)
    -- to application of sequences of substititions (_/✶_).  These are
    -- used to derive other (more general) lemmas below.

    →'-/✶-↑✶ : ∀ k {m n a b} (ρs : Subs T m n) →
               (a →' b) /✶ ρs ↑✶ k ≡ (a /✶ ρs ↑✶ k) →' (b /✶ ρs ↑✶ k)
    →'-/✶-↑✶ k ε        = refl
    →'-/✶-↑✶ k (ρ ◅ ρs) = cong₂ _/_ (→'-/✶-↑✶ k ρs) refl

    ∀'-/✶-↑✶ : ∀ k {m n a} (ρs : Subs T m n) →
               (∀' a) /✶ ρs ↑✶ k ≡ ∀' (a /✶ ρs ↑✶ (1 + k))
    ∀'-/✶-↑✶ k ε        = refl
    ∀'-/✶-↑✶ k (ρ ◅ ρs) = cong₂ _/_ (∀'-/✶-↑✶ k ρs) refl

    μT-/✶-↑✶ : ∀ k {m n a} (ρs : Subs T m n) →
               (μ a) /✶ ρs ↑✶ k ≡ μ (a /✶ ρs ↑✶ (1 + k))
    μT-/✶-↑✶ k ε        = refl
    μT-/✶-↑✶ k (ρ ◅ ρs) = cong₂ _/_ (μT-/✶-↑✶ k ρs) refl

  -- Defining the abstract members var and _/_ in
  -- Data.Fin.Substitution.TermSubst for T = Type gives us access to a
  -- number of (generic) substitution functions out-of-the-box.
  typeSubst : TermSubst Type
  typeSubst = record { var = var; app = TypeApp._/_ }

  open TermSubst typeSubst public hiding (var)

  weaken↑ : ∀ {n} → Type (1 + n) → Type (2 + n)
  weaken↑ a = a / wk ↑

  infix 8 _[/_]

  -- Shorthand for single-variable type substitutions
  _[/_] : ∀ {n} → Type (1 + n) → Type n → Type n
  a [/ b ] = a / sub b


-- Substitution lemmas.
module TypeLemmas where

  -- FIXME: The following lemmas are generic and should go somewhere
  -- else.
  module AdditionalLemmas {T} (lemmas : TermLemmas T) where
    open TermLemmas lemmas

    -- Weakening commutes with single-variable substitution
    weaken-sub : ∀ {n} (a : T (1 + n)) (b : T n) →
                 weaken (a / sub b) ≡ a / wk ↑ / sub (weaken b)
    weaken-sub a b = begin
      weaken (a / sub b)        ≡⟨ sym (/-wk′ (a / sub b)) ⟩
      a / sub b / wk            ≡⟨ sub-commutes a ⟩
      a / wk ↑ / sub (b / wk)   ≡⟨ cong (λ c → a / wk ↑ / sub c) (/-wk′ b) ⟩
      a / wk ↑ / sub (weaken b) ∎
      where /-wk′ : ∀ {n} (a : T n) → a / wk ≡ weaken a
            /-wk′ a = /-wk {t = a}

    -- Weakening commutes with reverse composition of substitutions.
    map-weaken-⊙ : ∀ {m n k} (σ₁ : Sub T m n) (σ₂ : Sub T n k) →
                   map weaken (σ₁ ⊙ σ₂) ≡ (map weaken σ₁) ⊙ (σ₂ ↑)
    map-weaken-⊙ σ₁ σ₂ = begin
      map weaken (σ₁ ⊙ σ₂)     ≡⟨ map-weaken ⟩
      (σ₁ ⊙ σ₂) ⊙ wk           ≡⟨ sym ⊙-assoc ⟩
      σ₁ ⊙ (σ₂ ⊙ wk)           ≡⟨ cong (λ σ₂ → σ₁ ⊙ σ₂) ⊙-wk ⟩
      σ₁ ⊙ (wk ⊙ (σ₂ ↑))       ≡⟨ ⊙-assoc ⟩
      (σ₁ ⊙ wk) ⊙ (σ₂ ↑)       ≡⟨ cong (λ σ₁ → σ₁ ⊙ (σ₂ ↑)) (sym map-weaken) ⟩
      (map weaken σ₁) ⊙ (σ₂ ↑) ∎

  -- Giving concrete definitions (i.e. proofs) for the abstract members
  -- (i.e. lemmas) in Data.Fin.Substitution.Lemmas.TermLemmas for T =
  -- Type gives us access to a number of (generic) substitutions lemmas
  -- out-of-the-box.
  typeLemmas : TermLemmas Type
  typeLemmas = record
    { termSubst = TypeSubst.typeSubst
    ; app-var   = refl
    ; /✶-↑✶     = Lemma./✶-↑✶
    }
    where
    module Lemma {T₁ T₂} {lift₁ : Lift T₁ Type} {lift₂ : Lift T₂ Type} where

      open TypeSubst
      open Lifted lift₁ using () renaming (_↑✶_ to _↑✶₁_; _/✶_ to _/✶₁_)
      open Lifted lift₂ using () renaming (_↑✶_ to _↑✶₂_; _/✶_ to _/✶₂_)

      /✶-↑✶ : ∀ {m n} (ρs₁ : Subs T₁ m n) (ρs₂ : Subs T₂ m n) →
              (∀ k x → var x /✶₁ ρs₁ ↑✶₁ k ≡ var x /✶₂ ρs₂ ↑✶₂ k) →
               ∀ k t → t     /✶₁ ρs₁ ↑✶₁ k ≡ t     /✶₂ ρs₂ ↑✶₂ k
      /✶-↑✶ ρs₁ ρs₂ hyp k (var x) = hyp k x
      /✶-↑✶ ρs₁ ρs₂ hyp k (a →' b) = begin
          (a →' b) /✶₁ ρs₁ ↑✶₁ k
        ≡⟨ TypeApp.→'-/✶-↑✶ _ k ρs₁ ⟩
          (a /✶₁ ρs₁ ↑✶₁ k) →' (b /✶₁ ρs₁ ↑✶₁ k)
        ≡⟨ cong₂ _→'_ (/✶-↑✶ ρs₁ ρs₂ hyp k a) (/✶-↑✶ ρs₁ ρs₂ hyp k b) ⟩
          (a /✶₂ ρs₂ ↑✶₂ k) →' (b /✶₂ ρs₂ ↑✶₂ k)
        ≡⟨ sym (TypeApp.→'-/✶-↑✶ _ k ρs₂) ⟩
          (a →' b) /✶₂ ρs₂ ↑✶₂ k
        ∎
      /✶-↑✶ ρs₁ ρs₂ hyp k (∀' a) = begin
        (∀' a) /✶₁ ρs₁ ↑✶₁ k        ≡⟨ TypeApp.∀'-/✶-↑✶ _ k ρs₁ ⟩
        ∀' (a /✶₁ ρs₁ ↑✶₁ (1 + k))  ≡⟨ cong ∀' (/✶-↑✶ ρs₁ ρs₂ hyp (1 + k) a) ⟩
        ∀' (a /✶₂ ρs₂ ↑✶₂ (1 + k))  ≡⟨ sym (TypeApp.∀'-/✶-↑✶ _ k ρs₂) ⟩
        (∀' a) /✶₂ ρs₂ ↑✶₂ k        ∎
      /✶-↑✶ ρs₁ ρs₂ hyp k (μ a) = begin
        (μ a) /✶₁ ρs₁ ↑✶₁ k         ≡⟨ TypeApp.μT-/✶-↑✶ _ k ρs₁ ⟩
        μ (a /✶₁ ρs₁ ↑✶₁ (1 + k))   ≡⟨ cong μ (/✶-↑✶ ρs₁ ρs₂ hyp (1 + k) a) ⟩
        μ (a /✶₂ ρs₂ ↑✶₂ (1 + k))   ≡⟨ sym (TypeApp.μT-/✶-↑✶ _ k ρs₂) ⟩
        (μ a) /✶₂ ρs₂ ↑✶₂ k         ∎

  open TermLemmas typeLemmas public hiding (var)
  open TypeSubst public using (_[/_]; _/Var_; weaken↑; module Lifted)

  -- The above lemma /✶-↑✶ specialized to single substitutions
  /-↑⋆ : ∀ {T₁ T₂} {lift₁ : Lift T₁ Type} {lift₂ : Lift T₂ Type} →
         let open Lifted lift₁ using () renaming (_↑⋆_ to _↑⋆₁_; _/_ to _/₁_)
             open Lifted lift₂ using () renaming (_↑⋆_ to _↑⋆₂_; _/_ to _/₂_)
         in
         ∀ {n k} (ρ₁ : Sub T₁ n k) (ρ₂ : Sub T₂ n k) →
         (∀ i x → var x /₁ ρ₁ ↑⋆₁ i ≡ var x /₂ ρ₂ ↑⋆₂ i) →
          ∀ i a → a /₁ ρ₁ ↑⋆₁ i ≡ a /₂ ρ₂ ↑⋆₂ i
  /-↑⋆ ρ₁ ρ₂ hyp i a = /✶-↑✶ (ρ₁ ◅ ε) (ρ₂ ◅ ε) hyp i a

  open AdditionalLemmas typeLemmas public


------------------------------------------------------------------------
-- Encoding/translation of additional type operators

module TypeOperators where
  open TypeLemmas hiding (id)

  -- Type of the polymorphic identity
  id : ∀ {n} → Type n
  id = ∀' ((var zero) →' (var zero))

  -- Bottom/initial/zero type
  ⊥ : ∀ {n} → Type n
  ⊥ = ∀' (var zero)

  -- Top/terminal/unit type
  ⊤ : ∀ {n} → Type n
  ⊤ = id

  -- Existential type
  ∃ : ∀ {n} → Type (1 + n) → Type n
  ∃ a = ∀' (∀' (weaken↑ a →' var (suc zero)) →' var zero)

  infixr 7 _→ⁿ_

  -- n-ary function type
  _→ⁿ_ : ∀ {n k} → Vec (Type n) k → Type n → Type n
  []       →ⁿ z = z
  (a ∷ as) →ⁿ z = as →ⁿ a →' z

  -- Record/finite tuple
  rec : ∀ {n k} → Vec (Type n) k → Type n
  rec []       = ⊤
  rec (a ∷ as) = ∀' ((map weaken (a ∷ as) →ⁿ var zero) →' var zero)


------------------------------------------------------------------------
-- Lemmas about encoded type operators

module TypeOperatorLemmas where
  open TypeOperators
  open TypeLemmas hiding (_/_; id)

  module TypeOperatorAppLemmas {T} (l : Lift T Type) where
    open TypeSubst.TypeApp l

    -- Type substitution commutes with the translation of of n-ary
    -- function types
    /-→ⁿ : ∀ {m n k} (as : Vec (Type m) k) (b : Type m) (σ : Sub T m n) →
           (as →ⁿ b) / σ ≡ map (λ a → a / σ) as →ⁿ b / σ
    /-→ⁿ []       _ _ = refl
    /-→ⁿ (a ∷ as) b σ = /-→ⁿ as (a →' b) σ

    -- FIXME: Write similar lemmas for the remaining type operators

  private
    module WeakeningLemmas where
      open TypeOperatorAppLemmas TypeSubst.varLift

      -- Weakening commutes with the translation of of n-ary function
      -- types
      weaken-→ⁿ : ∀ {n k} (as : Vec (Type n) k) (b : Type n) →
                  weaken (as →ⁿ b) ≡ map weaken as →ⁿ weaken b
      weaken-→ⁿ as b = /-→ⁿ as b VarSubst.wk

      -- FIXME: Write similar lemmas for the remaining type operators

  open TypeOperatorAppLemmas TypeSubst.termLift public
  open WeakeningLemmas public
