----------------------------------------------------------------------
-- Functional big-step evaluation of terms in the partiality monad
----------------------------------------------------------------------

module SystemF.Eval where

open import Codata.Musical.Notation
open import Category.Monad
open import Category.Monad.Partiality.All as All using (All; now; later)
open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe as Maybe using (just; nothing)
open import Data.Maybe.Relation.Unary.Any as MaybeAny using (just)
open import Data.Nat using (_+_)
open import Data.Vec using ([])
open import Function
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary

open import PartialityAndFailure as PF hiding (fail)
open PF.Equality hiding (fail)
open PF.Equivalence
private module M {f} = RawMonad (PF.monad {f})

open import SystemF.Type
open import SystemF.Term
open import SystemF.WtTerm

open TypeSubst       using () renaming (_[/_]  to _[/tp_])
open TermTypeSubst   using () renaming (_[/_]  to _[/tmTp_])
open TermTermSubst   using () renaming (_[/_]  to _[/tmTm_])
open WtTermTypeSubst using () renaming (_[/_]′ to _[/⊢tmTp_])
open WtTermTermSubst using () renaming (_[/_]  to _[/⊢tmTm_])

----------------------------------------------------------------------
-- Functional call-by-value big-step semantics

-- The functional presentation of the big-step semantics below is
-- heavily inspired by Danielsson's ICFP'12 paper "Operational
-- Semantics Using the Partiality Monad".  While the paper describes a
-- closure-based semantics, the semantics given below is
-- substitution-based.  This simplifies the evaluation of recursive
-- terms, i.e those involving fixpoint combinators, which would
-- otherwise have to be evaluated in a cyclic evironment, i.e. one
-- already containing the value of the recursive term being evaluated.
--
-- NB: while it is not described in detail in the paper, Danielsson
-- actually provides an alternative, substitution-based implementation
-- in the accompanying code, which can be found at
--
--   http://www.cse.chalmers.se/~nad/publications/danielsson-semantics-partiality-monad.tgz
--
-- As pointed out in Danielsson's paper, the functional presentation
-- of the big-step semantics feels rather natural in that it follows
-- the form of an interpreter, and it has the added advantage of
-- proving that the semantics are deterministic and computable "for
-- free".
--
-- For more information about Danielson's paper see
--
--   http://www.cse.chalmers.se/~nad/publications/danielsson-semantics-partiality-monad.html


----------------------------------------------------------------------
-- Semantic domain and evaluation

-- Computations with potential failure and partiality effects.
Comp : ∀ m n → Set
Comp m n = (Val m n) ?⊥

-- Following Danielsson's approach, we formulate the evaluation
-- function _⇓′ in an "embedded language" to work around the
-- limitations of Agda's guarded coinduction.  The function _⇓′
-- returns "programs", i.e. instances of the type _?⊥P which
-- internalizes the monadic bind operation as a constructor.  In a
-- second step, these programs are interpreted in the
-- partiality-and-failure monad by the function _⇓.
--
-- For details about this technique, see e.g. Danielsson's PAR'10
-- paper "Beating the Productivity Checker Using Embedded Languages".
--
-- SystemF.Eval.NoWorkarounds contains an alternative version of the
-- semantics which does not use the above-mentioned workaround.  The
-- alternative definition, while (provably) equivalent to the one
-- given below, is more verbose and arguably less readable.  However
-- the associated type soundness proof is simpler in that it requires
-- no additional compositionality lemmas.
module _ where
  open PF.Workaround

  -- Computation "programs".
  CompP : ∀ m n → Set₁
  CompP m n = (Val m n) ?⊥P

  mutual

    infix 7 _⇓′ _[_]′ _·′_

    -- Evaluation of untyped (open) terms in _?⊥P.
    _⇓′ : ∀ {m n} → Term m n → CompP m n
    var x ⇓′      = fail
    Λ t ⇓′        = return (Λ t)
    λ' a t ⇓′     = return (λ' a t)
    μ a t ⇓′      = later (♯ (t [/tmTm μ a t ] ⇓′))
    (t [ a ]) ⇓′  = t ⇓′ >>= λ v → v [ a ]′
    (s · t) ⇓′    = s ⇓′ >>= λ f → t ⇓′ >>= λ v → f ·′ v
    fold a t ⇓′   = t ⇓′ >>= λ v → return (fold a v)
    unfold a t ⇓′ = t ⇓′ >>= λ v → unfold′ a v

    -- Call-by-value evaluation of type application in _?⊥P.
    _[_]′ : ∀ {m n} → Val m n → Type n → CompP m n
    (Λ t) [ a ]′ = later (♯ (t [/tmTp a ] ⇓′))
    _     [ _ ]′ = fail

    -- Call-by-value Evaluation of term application in _?⊥P.
    _·′_ : ∀ {m n} → Val m n → Val m n → CompP m n
    (λ' _ t) ·′ v = later (♯ (t [/tmTm ⌜ v ⌝ ] ⇓′))
    _        ·′ _ = fail

    -- Evaluation of recursive type unfolding in _?⊥P.
    unfold′ : ∀ {m n} → Type (1 + n) → Val m n → CompP m n
    unfold′ _ (fold _ v) = return v
    unfold′ a _          = fail

  infix 7 _⇓

  -- Evaluation of untyped (open) terms in the partiality monad.
  _⇓ : ∀ {m n} → Term m n → Comp m n
  t ⇓ = ⟦ t ⇓′ ⟧P


----------------------------------------------------------------------
-- The semantics _⇓ is compositional

module _ where
  open M
  open PF.Reasoning
  open PF.Workaround using (⟦_⟧P) renaming (_>>=_ to _>>=P_)
  open PF.Workaround.Correct

  infix 7 _[_]⇓ _·⇓_

  -- Short hands for relating the semantics of composite terms to the
  -- semantics of their subterms.

  _[_]⇓ : ∀ {m n} → Comp m n → Type n → Comp m n
  c [ a ]⇓ = c >>= λ v → ⟦ v [ a ]′ ⟧P

  _·⇓_ : ∀ {m n} → Comp m n → Comp m n → Comp m n
  c ·⇓ d = c >>= λ f → d >>= λ v → ⟦ f ·′ v ⟧P

  fold⇓ : ∀ {m n} → Type (1 + n) → Comp m n → Comp m n
  fold⇓ a c = c >>= λ v → return (fold a v)

  unfold⇓ : ∀ {m n} → Type (1 + n) → Comp m n → Comp m n
  unfold⇓ a c = c >>= λ v → ⟦ unfold′ a v ⟧P

  -- The semantics of type application is compositional.
  []-comp : ∀ {m n} (t : Term m n) (a : Type n) → t [ a ] ⇓ ≅ (t ⇓) [ a ]⇓
  []-comp t a = >>=-hom (t ⇓′) _

  -- The semantics of term application is compositional.
  ·-comp : ∀ {m n} (s t : Term m n) → s · t ⇓ ≅ (s ⇓) ·⇓ (t ⇓)
  ·-comp s t =
      s · t ⇓
    ≅⟨ >>=-hom (s ⇓′) _ ⟩
      (s ⇓ >>= λ f → ⟦ t ⇓′ >>=P (λ v → f ·′ v) ⟧P)
    ≅⟨ (s ⇓ ∎ >>=-cong λ _ → >>=-hom (t ⇓′) _) ⟩
      (s ⇓) ·⇓ (t ⇓)
    ∎

  -- The semantics of recursive type folding is compositional.
  fold-comp : ∀ {m n} (a : Type (1 + n)) (t : Term m n) →
              fold a t ⇓ ≅ fold⇓ a (t ⇓)
  fold-comp a t = >>=-hom (t ⇓′) _

  -- The semantics of recursive type unfolding is compositional.
  unfold-comp : ∀ {m n} (a : Type (1 + n)) (t : Term m n) →
                unfold a t ⇓ ≅ unfold⇓ a (t ⇓)
  unfold-comp a t = >>=-hom (t ⇓′) _


----------------------------------------------------------------------
-- Type soundness

open PF using (fail)

infix 4 _⊢comp_∈_

-- A computation is well-typed if it is a well-typed value or it takes
-- a step towards a well-typed computation.  Note that we exclude the
-- case of failing well-typed computations through the use of
-- Maybe.Any.
_⊢comp_∈_ : ∀ {m n} → Ctx m n → Comp m n → Type n → Set
Γ ⊢comp c ∈ a = All (MaybeAny.Any (λ v → Γ ⊢val v ∈ a)) c

-- Well-typed computations do not fail.
does-not-fail : ∀ {m n} {Γ : Ctx m n} {c a} → Γ ⊢comp c ∈ a → ¬ c ≈ fail
does-not-fail (now (MaybeAny.just _)) (now ())
does-not-fail (later ⊢c)     (laterˡ c-fails) = does-not-fail (♭ ⊢c) c-fails

-- It remains to prove that well-typed terms evaluate to well-typed
-- computations.  The proof ⊢_⇓ follows the same structure as _⇓ and
-- uses an analogous workaround to deal with guarded coinduction.  It
-- is formulated in the language AllP of of Partiality.All "programs"
-- defined in All.Alternative.
open All.Alternative
open PF.Workaround using (⟦_⟧P)

infix 4 ⊢compP_∈_ ⊢val_∈_

-- Closed well-typed computation "programs".
⊢compP_∈_ : Comp 0 0 → Type 0 → Set₁
⊢compP c ∈ a = AllP (MaybeAny.Any (λ v → [] ⊢val v ∈ a)) c

-- A short hand for closed well-typed values.
⊢val_∈_ : Val 0 0 → Type 0 → Set
⊢val v ∈ a = [] ⊢val v ∈ a

mutual

  infix 7 ⊢_⇓′ ⊢_[_]′ ⊢_·′_

  -- Evaluation of closed terms preserves well-typedness in AllP.
  ⊢_⇓′ : ∀ {t a} → [] ⊢ t ∈ a → ⊢compP t ⇓ ∈ a
  ⊢ var ()      ⇓′
  ⊢ Λ ⊢t        ⇓′   = now (just (Λ ⊢t))
  ⊢ λ' a ⊢t     ⇓′   = now (just (λ' a ⊢t))
  ⊢ μ a ⊢t      ⇓′   = later (♯ ⊢ ⊢t [/⊢tmTm μ a ⊢t ] ⇓′)
  ⊢_⇓′ {t [ a ]} (⊢t [ .a ] ) =
    t [ a ] ⇓        ≅⟨ []-comp t a ⟩P
    (t ⇓) [ a ]⇓      ⟨  ⊢ ⊢t ⇓′ >>=-congP (λ { .{_} (just ⊢v) →
                         ⊢ ⊢v [ a ]′ }) ⟩P
  ⊢_⇓′ {s · t} (⊢s · ⊢t) =
    s · t ⇓          ≅⟨ ·-comp s t ⟩P
    (s ⇓) ·⇓ (t ⇓)    ⟨ (⊢ ⊢s ⇓′ >>=-congP λ { .{_} (just ⊢f) →
                         ⊢ ⊢t ⇓′ >>=-congP λ { .{_} (just ⊢v) →
                         ⊢ ⊢f ·′ ⊢v }}) ⟩P
  ⊢_⇓′ {fold a t} (fold .a ⊢t) =
    fold a t ⇓       ≅⟨ fold-comp a t ⟩P
    fold⇓ a (t ⇓)     ⟨ (⊢ ⊢t ⇓′ >>=-congP λ { .{_} (just ⊢v) →
                         now (just (fold a ⊢v)) }) ⟩P
  ⊢_⇓′ {unfold a t} (unfold .a ⊢t) =
    unfold a t ⇓     ≅⟨ unfold-comp a t ⟩P
    unfold⇓ a (t ⇓)   ⟨ (⊢ ⊢t ⇓′ >>=-congP λ { .{_} (just ⊢v) →
                         ⊢unfold′ a ⊢v }) ⟩P

  -- Evaluation of type application preserves well-typedness in AllP.
  ⊢_[_]′ : ∀ {v a} → ⊢val v ∈ ∀' a → ∀ b → ⊢compP ⟦ v [ b ]′ ⟧P ∈ a [/tp b ]
  ⊢ Λ ⊢t [ a ]′ = later (♯ ⊢ ⊢t [/⊢tmTp a ] ⇓′)

  -- Evaluation of term application preserves well-typedness in AllP.
  ⊢_·′_ : ∀ {f v a b} → ⊢val f ∈ a →' b → ⊢val v ∈ a → ⊢compP ⟦ f ·′ v ⟧P ∈ b
  ⊢ λ' a ⊢t ·′ ⊢v = later (♯ ⊢ ⊢t [/⊢tmTm ⊢⌜ ⊢v ⌝ ] ⇓′)

  -- Evaluation of recursive type unfolding preserves well-typedness in AllP.
  ⊢unfold′ : ∀ {v} a → ⊢val v ∈ μ a → ⊢compP ⟦ unfold′ a v ⟧P ∈ a [/tp μ a ]
  ⊢unfold′ _ (fold ._ ⊢v) = now (just ⊢v)

infix 7 ⊢_⇓

-- Evaluation of closed terms preserves well-typedness.
⊢_⇓ : ∀ {t a} → [] ⊢ t ∈ a → [] ⊢comp t ⇓ ∈ a
⊢_⇓ = sound ∘ ⊢_⇓′

-- Type soundness: evaluation of well-typed terms does not fail.
type-soundness : ∀ {t a} → [] ⊢ t ∈ a → ¬ t ⇓ ≈ fail
type-soundness ⊢t = does-not-fail ⊢ ⊢t ⇓
