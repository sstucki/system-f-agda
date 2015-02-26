----------------------------------------------------------------------
-- Functional big-step evaluation of terms in the partiality monad
-- (alternative version not productivity checker workarounds)
----------------------------------------------------------------------

module SystemF.Eval.NoWorkarounds where

open import Coinduction using (∞; ♯_; ♭)
open import Category.Monad
open import Category.Monad.Partiality.All
open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe as Maybe using (just; nothing)
open import Data.Nat using (_+_)
open import Data.Vec using ([])
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary

open import PartialityAndFailure as PF
open PF.Equality hiding (fail)
private
  open module M {f} = RawMonad (PF.monad {f}) using (return; _>>=_)

open import SystemF.Type
open import SystemF.Term
open import SystemF.WtTerm

open TypeSubst       using () renaming (_[/_]  to _[/tp_])
open TermTypeSubst   using () renaming (_[/_]  to _[/tmTp_])
open TermTermSubst   using () renaming (_[/_]  to _[/tmTm_])
open WtTermTypeSubst using () renaming (_[/_]′ to _[/⊢tmTp_])
open WtTermTermSubst using () renaming (_[/_]  to _[/⊢tmTm_])

open import SystemF.Eval as E
  using (Comp; _⊢comp_∈_; does-not-fail)


----------------------------------------------------------------------
-- Functional big-step semantics (alternative version)
--
-- The evaluation function _⇓ given below differs from that in
-- SystemF.Eval in that it evaluates terms directly in the
-- partiality-and-failure monad (rather than first evaluating them in
-- PartialityAndFailure.Workaround._?⊥P and subsequently interpreting
-- the result in PartialityAndFailure._?⊥).  This is achieved by
-- manually expanding and inlining every application of the monadic
-- bind operation.
--
-- We give a separate type soundness proof formulated with respect to
-- the alternative semantics, as well as a proof that the two
-- semantics are equivalent (i.e. the two evaluations of any given
-- term are bisimilar).
--
-- The definition of the alternative semantics is more verbose and
-- arguably less readable.  However the associated type soundness
-- proof is simpler in that it requires no additional compositionality
-- lemmas.

module _ where
  open M

  mutual

    infix 7 _⇓ _[_]⇓ _·⇓_

    -- Evaluation of untyped (open) terms.
    _⇓ : ∀ {m n} → Term m n → Comp m n
    var x ⇓      = fail
    Λ t ⇓        = return (Λ t)
    λ' a t ⇓     = return (λ' a t)
    μ a t ⇓      = later (♯ (t [/tmTm μ a t ] ⇓))
    (t [ a ]) ⇓  with t ⇓
    ... | c      = c [ a ]⇓
    (s · t) ⇓    with s ⇓ | t ⇓
    ... | f | c  = f ·⇓ c
    fold a t ⇓   with t ⇓
    ... | c      = fold⇓ a c
    unfold a t ⇓ with t ⇓
    ... | c      = unfold⇓ a c

    -- Evaluation of type application.
    _[_]⇓ : ∀ {m n} → Comp m n → Type n → Comp m n
    now (just (Λ t)) [ a ]⇓ = later (♯ (t [/tmTp a ] ⇓))
    now (just _)     [ _ ]⇓ = fail
    now nothing      [ _ ]⇓ = fail
    later c          [ a ]⇓ = later (♯ ((♭ c) [ a ]⇓))

    -- Evaluation of term application.
    _·⇓_ : ∀ {m n} → Comp m n → Comp m n → Comp m n
    now (just (λ' _ t)) ·⇓ now (just v) = later (♯ (t [/tmTm ⌜ v ⌝ ] ⇓))
    now (just _)        ·⇓ now _        = fail
    now nothing         ·⇓ _            = fail
    now f               ·⇓ later c      = later (♯ (now f ·⇓ (♭ c)))
    later f             ·⇓ c            = later (♯ ((♭ f) ·⇓ c))

    -- Evaluation of recursive type folding.
    fold⇓ : ∀ {m n} → Type (1 + n) → Comp m n → Comp m n
    fold⇓ a (now (just v)) = now (just (fold a v))
    fold⇓ _ (now nothing)  = fail
    fold⇓ a (later c)      = later (♯ fold⇓ a (♭ c))

    -- Evaluation of recursive type unfolding.
    unfold⇓ : ∀ {m n} → Type (1 + n) → Comp m n → Comp m n
    unfold⇓ _ (now (just (fold _ v))) = now (just v)
    unfold⇓ a (now (just _))          = fail
    unfold⇓ a (now nothing)           = fail
    unfold⇓ a (later c)               = later (♯ unfold⇓ a (♭ c))


----------------------------------------------------------------------
-- Type soundness wrt. to the alternative semantics

infix 4 ⊢comp_∈_

-- Short hand for closed well-typed computations.
⊢comp_∈_ : Comp 0 0 → Type 0 → Set
⊢comp c ∈ a = [] ⊢comp c ∈ a

mutual

  infix 7 ⊢_⇓ ⊢_[_]⇓ ⊢_·⇓_

  -- Evaluation of closed terms preserves well-typedness.
  ⊢_⇓ : ∀ {t a} → [] ⊢ t ∈ a → ⊢comp t ⇓ ∈ a
  ⊢ var ()      ⇓
  ⊢ Λ ⊢t        ⇓ = now (just (Λ ⊢t))
  ⊢ λ' a ⊢t     ⇓ = now (just (λ' a ⊢t))
  ⊢ μ a ⊢t      ⇓ = later (♯ ⊢ ⊢t [/⊢tmTm μ a ⊢t ] ⇓)
  ⊢ ⊢t [ a ]    ⇓ with ⊢ ⊢t ⇓
  ... | ⊢c        = ⊢ ⊢c [ a ]⇓
  ⊢ ⊢s · ⊢t     ⇓ with ⊢ ⊢s ⇓ | ⊢ ⊢t ⇓
  ... | ⊢f | ⊢c   = ⊢ ⊢f ·⇓ ⊢c
  ⊢ fold a ⊢t   ⇓ with ⊢ ⊢t ⇓
  ... | ⊢c        = ⊢fold⇓ a ⊢c
  ⊢ unfold a ⊢t ⇓ with ⊢ ⊢t ⇓
  ... | ⊢c        = ⊢unfold⇓ a ⊢c

  -- Evaluation of type application preserves well-typedness.
  ⊢_[_]⇓ : ∀ {c a} → ⊢comp c ∈ ∀' a → ∀ b → ⊢comp c [ b ]⇓ ∈ a [/tp b ]
  ⊢ now (just (Λ ⊢t)) [ a ]⇓ = later (♯ ⊢ ⊢t [/⊢tmTp a ] ⇓)
  ⊢ later ⊢c          [ a ]⇓ = later (♯ ⊢ (♭ ⊢c) [ a ]⇓)

  -- Evaluation of term application preserves well-typedness.
  ⊢_·⇓_ : ∀ {f c a b} → ⊢comp f ∈ a →' b → ⊢comp c ∈ a → ⊢comp f ·⇓ c ∈ b
  ⊢ now (just (λ' a ⊢t)) ·⇓ now (just ⊢v) =
    later (♯ (⊢ ⊢t [/⊢tmTm ⊢⌜ ⊢v ⌝ ] ⇓))
  ⊢ now (just (λ' a ⊢t)) ·⇓ later ⊢c =
    later (♯ (⊢ now (just (λ' a ⊢t)) ·⇓ ♭ ⊢c))
  ⊢ later ⊢f ·⇓ ⊢c = later (♯ (⊢ ♭ ⊢f ·⇓ ⊢c))

  -- Evaluation of recursive type folding preserves well-typedness.
  ⊢fold⇓ : ∀ {c} a → ⊢comp c ∈ a [/tp μ a ] → ⊢comp fold⇓ a c ∈ μ a
  ⊢fold⇓ a (now (just ⊢v)) = now (just (fold a ⊢v))
  ⊢fold⇓ a (later ⊢c)      = later (♯ ⊢fold⇓ a (♭ ⊢c))

  -- Evaluation of recursive type unfolding preserves well-typedness.
  ⊢unfold⇓ : ∀ {c} a → ⊢comp c ∈ μ a → ⊢comp unfold⇓ a c ∈ a [/tp μ a ]
  ⊢unfold⇓ _ (now (just (fold ._ ⊢v))) = now (just ⊢v)
  ⊢unfold⇓ a (later ⊢c)                = later (♯ ⊢unfold⇓ a (♭ ⊢c))

-- Type soundness: evaluation of well-typed terms does not fail.
type-soundness : ∀ {t a} → [] ⊢ t ∈ a → ¬ t ⇓ ≈ fail
type-soundness ⊢t = does-not-fail ⊢ ⊢t ⇓


----------------------------------------------------------------------
-- Equivalence (bisimilarity) of big-step semantics

open PF.Workaround using (⟦_⟧P)
open PF.Equivalence hiding (sym)
open PF.AlternativeEquality
  renaming (return to returnP; fail to failP; _>>=_ to _>>=P_)

-- Bind-expanded variants of the various helpers of of _⇓.

_[_]⇓′ : ∀ {m n} → Comp m n → Type n → Comp m n
c [ a ]⇓′ = c >>= λ v → (return v) [ a ]⇓

_·⇓′_ : ∀ {m n} → Comp m n → Comp m n → Comp m n
c ·⇓′ d = c >>= λ f → d >>= λ v → (return f) ·⇓ (return v)

fold⇓′ : ∀ {m n} → Type (1 + n) → Comp m n → Comp m n
fold⇓′ a c = c >>= λ v → fold⇓ a (return v)

unfold⇓′ : ∀ {m n} → Type (1 + n) → Comp m n → Comp m n
unfold⇓′ a c = c >>= λ v → unfold⇓ a (return v)

-- The two variants of _[_]⇓ are strongly bisimilar.
_[_]⇓≅ : ∀ {m n} (c : Comp m n) (a : Type n) → c [ a ]⇓ ≅ c [ a ]⇓′
now (just _) [ _ ]⇓≅ = refl P.refl
now nothing  [ _ ]⇓≅ = now P.refl
later c      [ a ]⇓≅ = later (♯ ((♭ c) [ a ]⇓≅))

-- The two variants of _·⇓_ are strongly bisimilar.
_·⇓≅_ : ∀ {m n} (c : Comp m n) (d : Comp m n) → c ·⇓ d ≅ c ·⇓′ d
now (just _)          ·⇓≅ now (just _) = refl P.refl
now (just (Λ t))      ·⇓≅ now nothing  = now P.refl
now (just (λ' a t))   ·⇓≅ now nothing  = now P.refl
now (just (fold a t)) ·⇓≅ now nothing  = now P.refl
now nothing           ·⇓≅ now v   = now P.refl
now (just (Λ t))      ·⇓≅ later d = later (♯ (now (just (Λ t))      ·⇓≅ ♭ d))
now (just (λ' a t))   ·⇓≅ later d = later (♯ (now (just (λ' a t))   ·⇓≅ ♭ d))
now (just (fold a t)) ·⇓≅ later d = later (♯ (now (just (fold a t)) ·⇓≅ ♭ d))
now nothing           ·⇓≅ later d = now P.refl
later c               ·⇓≅ d       = later (♯ ((♭ c) ·⇓≅ d))

-- The two variants of fold⇓ are strongly bisimilar.
fold⇓≅ : ∀ {m n} (a : Type (1 + n)) (c : Comp m n) → fold⇓ a c ≅ fold⇓′ a c
fold⇓≅ a (now (just v)) = now P.refl
fold⇓≅ a (now nothing)  = now P.refl
fold⇓≅ a (later c)      = later (♯ fold⇓≅ a (♭ c))

-- The two variants of unfold⇓ are strongly bisimilar.
unfold⇓≅ : ∀ {m n} (a : Type (1 + n)) (c : Comp m n) →
           unfold⇓ a c ≅ unfold⇓′ a c
unfold⇓≅ a (now (just v)) = refl P.refl
unfold⇓≅ a (now nothing)  = now P.refl
unfold⇓≅ a (later c)      = later (♯ unfold⇓≅ a (♭ c))

mutual

  -- Helper lemma relating the two semantics of type application.
  []-E⇓≅⇓′ : ∀ {m n} (v : Val m n) (a : Type n) →
             ⟦ v E.[ a ]′ ⟧P ≅P (return v) [ a ]⇓
  []-E⇓≅⇓′ (Λ t)      a = later (♯ E⇓≅⇓′ (t [/tmTp a ] ))
  []-E⇓≅⇓′ (λ' _ _)   _ = failP
  []-E⇓≅⇓′ (fold _ _) _ = failP

  -- Helper lemma relating the two semantics of term application.
  ·-E⇓≅⇓′ : ∀ {m n} (f : Val m n) (v : Val m n) →
            ⟦ f E.·′ v ⟧P ≅P (return f) ·⇓ (return v)
  ·-E⇓≅⇓′ (Λ _)      _ = failP
  ·-E⇓≅⇓′ (λ' a t)   v = later (♯ E⇓≅⇓′ (t [/tmTm ⌜ v ⌝ ]))
  ·-E⇓≅⇓′ (fold _ _) _ = failP

  -- Helper lemma relating the two semantics of recursive type
  -- unfolding.
  unfold-E⇓≅⇓′ : ∀ {m n} (a : Type (1 + n)) (v : Val m n) →
                 ⟦ E.unfold′ a v ⟧P ≅P unfold⇓ a (return v)
  unfold-E⇓≅⇓′ _ (Λ _)      = failP
  unfold-E⇓≅⇓′ _ (λ' _ _)   = failP
  unfold-E⇓≅⇓′ _ (fold _ _) = returnP P.refl

  -- The two semantics are ≅P-equivalent.
  E⇓≅⇓′ : ∀ {m n} (t : Term m n) → t E.⇓ ≅P t ⇓
  E⇓≅⇓′ (var x)           = failP
  E⇓≅⇓′ (Λ t)             = returnP P.refl
  E⇓≅⇓′ (λ' a t)          = returnP P.refl
  E⇓≅⇓′ (μ a t)           = later (♯ E⇓≅⇓′ (t [/tmTm μ a t ]))
  E⇓≅⇓′ (t [ a ])         =
    t [ a ] E.⇓           ≅⟨ complete (E.[]-comp t a) ⟩
    (t E.⇓) E.[ a ]⇓      ≅⟨ (E⇓≅⇓′ t >>=P λ v → []-E⇓≅⇓′ v a) ⟩
    (t ⇓) [ a ]⇓′         ≅⟨ sym (complete ((t ⇓) [ a ]⇓≅)) ⟩
    t [ a ] ⇓             ∎
  E⇓≅⇓′ (s · t)           =
    s · t E.⇓             ≅⟨ complete (E.·-comp s t) ⟩
    (s E.⇓) E.·⇓ (t E.⇓)  ≅⟨ (E⇓≅⇓′ s >>=P λ f → E⇓≅⇓′ t >>=P λ v →
                              ·-E⇓≅⇓′ f v) ⟩
    (s ⇓) ·⇓′ (t ⇓)       ≅⟨ sym (complete ((s ⇓) ·⇓≅ (t ⇓))) ⟩
    s · t ⇓               ∎
  E⇓≅⇓′ (fold a t)        =
    fold a t E.⇓          ≅⟨ complete (E.fold-comp a t) ⟩
    E.fold⇓ a (t E.⇓)     ≅⟨ (E⇓≅⇓′ t >>=P λ v → return (fold a v) ∎) ⟩
    fold⇓′ a (t ⇓)        ≅⟨ sym (complete (fold⇓≅ a (t ⇓))) ⟩
    fold a t ⇓            ∎
  E⇓≅⇓′ (unfold a t)      =
    unfold a t E.⇓        ≅⟨ complete (E.unfold-comp a t) ⟩
    E.unfold⇓ a (t E.⇓)   ≅⟨ (E⇓≅⇓′ t >>=P λ v → unfold-E⇓≅⇓′ a v) ⟩
    unfold⇓′ a (t ⇓)      ≅⟨ sym (complete (unfold⇓≅ a (t ⇓))) ⟩
    unfold a t ⇓          ∎

-- The two big-step semantics are strongly bisimliar.
E⇓≅⇓ : ∀ {m n} (t : Term m n) → t E.⇓ ≅ t ⇓
E⇓≅⇓ t = sound (E⇓≅⇓′ t)
