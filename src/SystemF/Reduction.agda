----------------------------------------------------------------------
-- Functional small-step semantics
----------------------------------------------------------------------

module SystemF.Reduction where

open import Codata.Musical.Notation
open import Category.Monad
open import Category.Monad.Partiality.All
open import Data.Maybe as Maybe using (Maybe; just; nothing; map)
open import Data.Maybe.Relation.Unary.All as MaybeAll using (nothing; just)
open import Data.Maybe.Relation.Unary.Any as MaybeAny using (just)
open import Data.Nat using (ℕ; _+_)
open import Data.Unit using (tt)
open import Data.Vec using ([])
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_)
open import Relation.Nullary

open import PartialityAndFailure as PF
open PF.Equality hiding (fail)
open PF.Equivalence
private
  open module M {f} = RawMonad (PF.monad {f}) using (_>>=_; return)

open import SystemF.Type
open import SystemF.Term
open import SystemF.WtTerm
open import SystemF.Eval hiding (type-soundness)

open TypeSubst       using () renaming (_[/_]  to _[/tp_])
open TermTypeSubst   using () renaming (_[/_]  to _[/tmTp_])
open TermTermSubst   using () renaming (_[/_]  to _[/tmTm_])
open WtTermTypeSubst using () renaming (_[/_]′ to _[/⊢tmTp_])
open WtTermTermSubst using () renaming (_[/_]  to _[/⊢tmTm_])

----------------------------------------------------------------------
-- Functional call-by-value small-step semantics in the partiality
-- monad

-- The functional presentation of the small-step semantics below is
-- heavily inspired by Danielsson's ICFP'12 paper "Operational
-- Semantics Using the Partiality Monad".  Whereas the paper
-- illustrates the technique to give a functional abstract machine
-- semantics (i.e. the semantics of a "VM"), we skip the compilation
-- step and directly reduce terms, which results in a (functional)
-- structural operational semantics (SOS).  We adopt many of the
-- conventions used in the accompanying code, which can be found at
--
--   http://www.cse.chalmers.se/~nad/publications/danielsson-semantics-partiality-monad.tgz
--
-- As pointed out in Danielsson's paper, the functional presentation
-- of the semantics feels rather natural in that it follows the form
-- of an interpreter, and it has the added advantage of proving that
-- the semantics are deterministic and computable "for free".
--
-- For more information about Danielson's paper see
--
--   http://www.cse.chalmers.se/~nad/publications/danielsson-semantics-partiality-monad.html


----------------------------------------------------------------------
-- Small-step call-by-value reduction

-- Results of reduction steps
data Result (m n : ℕ) : Set where
  continue : (t : Term m n) → Result m n  -- further reducible term
  done     : (v : Val m n)  → Result m n  -- irreducible value

-- Take a single reduction step (if possible).
step : ∀ {m n} → Term m n → Maybe (Result m n)
step (var x)                 = nothing
step (Λ t)                   = just (done (Λ t))
step (λ' a t)                = just (done (λ' a t))
step (μ a t)                 = just (continue (t [/tmTm μ a t ]))
step (t [ a ])               with step t
... | just (continue t′)     = just (continue (t′ [ a ]))
... | just (done (Λ t′))     = just (continue (t′ [/tmTp a ]))
... | just (done _)          = nothing
... | nothing                = nothing
step {m} {n} (s · t)         with step s
... | just (continue s′)     = just (continue (s′ · t))
... | just (done v)          = nested v
  where -- Call-by-value: only reduce (s · t) if s is a value.
    nested : Val m n → Maybe (Result m n)
    nested v with step t
    nested v         | (just (continue t′)) = just (continue (⌜ v ⌝ · t′))
    nested (λ' _ s′) | (just (done v)) = just (continue (s′ [/tmTm ⌜ v ⌝ ]))
    nested _         | (just (done _)) = nothing
    nested _         | nothing         = nothing
... | nothing                = nothing
step (fold a t)              with step t
... | just (continue t′)     = just (continue (fold a t′))
... | just (done v)          = just (done (fold a v))
... | nothing                = nothing
step (unfold a t)            with step t
... | just (continue t′)     = just (continue (unfold a t′))
... | just (done (fold _ v)) = just (done v)
... | just (done _)          = nothing
... | nothing                = nothing


----------------------------------------------------------------------
-- Type soundness

infix 4 _⊢res_∈_ _⊢res?_∈_

-- Well-typedness lifted to results of reduction steps.
data _⊢res_∈_ {m n} (Γ : Ctx m n) : Result m n → Type n → Set where
  ⊢continue : ∀ {t a} → Γ ⊢    t ∈ a → Γ ⊢res continue t ∈ a
  ⊢done     : ∀ {v a} → Γ ⊢val v ∈ a → Γ ⊢res done v     ∈ a

-- Well-typedness lifted to possibly undefined reduction steps.
_⊢res?_∈_ : ∀ {m n} → Ctx m n → Maybe (Result m n) → Type n → Set
Γ ⊢res? r? ∈ a = MaybeAll.All (λ r → Γ ⊢res r ∈ a) r?

-- Preservation of well-typedness: a well-typed term reduces in one
-- step to a result of the same type or fails to reduce.
⊢step : ∀ {m n} {Γ : Ctx m n} {t a} → Γ ⊢ t ∈ a → Γ ⊢res? step t ∈ a
⊢step (var x)   = nothing
⊢step (Λ ⊢t)    = just (⊢done (Λ ⊢t))
⊢step (λ' a ⊢t) = just (⊢done (λ' a ⊢t))
⊢step (μ a ⊢t)  = just (⊢continue (⊢t [/⊢tmTm μ a ⊢t ]))
⊢step {t = t [ a ]} (⊢t [ .a ]) with step t | ⊢step ⊢t
... | just ._ | just (⊢continue ⊢t′) = just (⊢continue (⊢t′ [ a ]))
... | just ._ | just (⊢done (Λ ⊢t′)) = just (⊢continue (⊢t′ [/⊢tmTp a ]))
... | nothing | nothing              = nothing
⊢step {m} {n} {Γ} {s · t} {b} (⊢s · ⊢t) with step s | ⊢step ⊢s
... | just ._ | just (⊢continue ⊢s′) = just (⊢continue (⊢s′ · ⊢t))
... | just (done (λ' a s′)) | just (⊢done (λ' .a ⊢s′)) = nested
  where
    nested : Γ ⊢res? step ((λ' a s′) · t) ∈ b
    nested with step t | ⊢step ⊢t
    ... | just ._ | just (⊢continue ⊢t′) = just (⊢continue ((λ' a ⊢s′) · ⊢t′))
    ... | just ._ | just (⊢done v) = just (⊢continue (⊢s′ [/⊢tmTm ⊢⌜ v ⌝ ]))
    ... | nothing | nothing        = nothing
... | nothing | nothing = nothing
⊢step {t = fold a t} (fold .a ⊢t) with step t | ⊢step ⊢t
... | just ._ | just (⊢continue ⊢t′) = just (⊢continue (fold a ⊢t′))
... | just ._ | just (⊢done ⊢v)      = just (⊢done (fold a ⊢v))
... | nothing | nothing              = nothing
⊢step {t = unfold a t} (unfold .a ⊢t) with step t | ⊢step ⊢t
... | just ._ | just (⊢continue ⊢t′)      = just (⊢continue (unfold a ⊢t′))
... | just ._ | just (⊢done (fold .a ⊢v)) = just (⊢done ⊢v)
... | nothing | nothing                   = nothing

-- Progress: reduction of well-typed closed terms does not fail.
progress : ∀ {t} {a : Type 0} → [] ⊢ t ∈ a → Maybe.Is-just (step t)
progress (var ())
progress (Λ t) = just tt
progress (λ' a t) = just tt
progress (μ a t) = just tt
progress {t [ a ]} (⊢t [ .a ]) with step t | ⊢step ⊢t | progress ⊢t
... | just ._ | just (⊢continue _) | just tt = just tt
... | just ._ | just (⊢done (Λ _)) | just tt = just tt
progress {s · t} (⊢s · ⊢t) with step s | ⊢step ⊢s | progress ⊢s
... | just ._               | just (⊢continue _)     | just tt = just tt
... | just (done (λ' a s′)) | just (⊢done (λ' .a _)) | just tt = nested
  where
    nested : Maybe.Is-just (step ((λ' a s′) · t))
    nested with step t | ⊢step ⊢t | progress ⊢t
    ... | just ._ | just (⊢continue _) | just tt = just tt
    ... | just ._ | just (⊢done _)     | just tt = just tt
progress {fold a t} (fold .a ⊢t) with step t | ⊢step ⊢t | progress ⊢t
... | just ._ | just (⊢continue _) | just tt = just tt
... | just ._ | just (⊢done _)     | just tt = just tt
progress {unfold a t} (unfold .a ⊢t) with step t | ⊢step ⊢t | progress ⊢t
... | just ._ | just (⊢continue _)       | just tt = just tt
... | just ._ | just (⊢done (fold .a _)) | just tt = just tt

infix 7 _↓ ⊢_↓

-- Evaluation of untyped (open) terms in the partiality monad via
-- repeated reduction.
_↓ : ∀ {m n} → Term m n → Comp m n
t ↓ with step t
... | just (continue t′) = later (♯ (t′ ↓))
... | just (done v)      = return v
... | nothing            = fail

-- Evaluation of closed terms preserves well-typedness.
⊢_↓ : ∀ {t a} → [] ⊢ t ∈ a → [] ⊢comp t ↓ ∈ a
⊢_↓ {t} ⊢t with step t | ⊢step ⊢t | progress ⊢t
... | just (continue t′) | just (⊢continue ⊢t′) | just tt = later (♯ ⊢ ⊢t′ ↓)
... | just (done v)      | just (⊢done ⊢v)      | just tt = now (just ⊢v)
... | nothing            | _                    | ()

-- Type soundness: evaluation of well-typed terms does not fail.
type-soundness : ∀ {t a} → [] ⊢ t ∈ a → ¬ t ↓ ≈ fail
type-soundness ⊢t = does-not-fail ⊢ ⊢t ↓


----------------------------------------------------------------------
-- Strong bisimilarity of big-step and small-step semantics

open PF.AlternativeEquality
  renaming (return to returnP; fail to failP; _>>=_ to _>>=P_)

-- Lemma: values don't reduce.
step-val : ∀ {m n} (v : Val m n) → step ⌜ v ⌝ ≡ just (done v)
step-val (Λ a)      = P.refl
step-val (λ' a t)   = P.refl
step-val (fold a v) with step ⌜ v ⌝ | step-val v
... | just (continue t) | ()
... | just (done w) | w≡v = P.cong (map (lower a)) w≡v
  where lower : ∀ {m n} → Type (1 + n) → Result m n → Result m n
        lower a (done v)     = done (fold a v)
        lower a (continue t) = continue t
... | nothing | ()

-- Lemma: _↓ "preserves" values.
↓-val : ∀ {m n} (v : Val m n) → ⌜ v ⌝ ↓ ≡ return v
↓-val v with step ⌜ v ⌝ | step-val v
↓-val v | just (continue t) | ()
↓-val v | just (done w) | w≡v = P.cong toComp w≡v
  where toComp : ∀ {m n} → Maybe (Result m n) → Comp m n
        toComp (just (continue t′)) = later (♯ (t′ ↓))
        toComp (just (done v))      = return v
        toComp nothing              = fail
↓-val v | nothing | ()

mutual
  infix 7 _[_]⇓≅↓′ _·⇓≅↓′_

  -- A helper lemma relating reduction and evaluation of type
  -- application.
  _[_]⇓≅↓′ : ∀ {m n} (t : Term m n) (a : Type n) →
             (t ↓) [ a ]⇓ ≅P (t [ a ]) ↓
  t [ a ]⇓≅↓′ with step t
  ... | just (continue t′)     = later (♯ (t′ [ a ]⇓≅↓′))
  ... | just (done (Λ t′))     = later (♯ ⇓≅↓′ (t′ [/tmTp a ]) )
  ... | just (done (λ' _ _))   = failP
  ... | just (done (fold _ _)) = failP
  ... | nothing                = failP

  -- A helper lemma relating reduction and evaluation of term
  -- application.
  _·⇓≅↓′_ : ∀ {m n} (s : Term m n) (t : Term m n) →
            (s ↓) ·⇓ (t ↓) ≅P (s · t) ↓
  s ·⇓≅↓′ t with step s
  s ·⇓≅↓′ t | just (continue s′)     = later (♯ (s′ ·⇓≅↓′ t))
  s ·⇓≅↓′ t | just (done v)          with step t
  s ·⇓≅↓′ t | just (done v)          | just (continue t′) = later (♯ subst v)
    where
      subst : ∀ v → (return v) ·⇓ (t′ ↓) ≅P (⌜ v ⌝ · t′) ↓
      subst v with ⌜ v ⌝ ↓ | ↓-val v | ⌜ v ⌝ ·⇓≅↓′ t′
      subst v | now (just .v) | P.refl | v≅t′ = v≅t′
      subst _ | now nothing   | ()     | _
      subst _ | later x₁      | ()     | _
  s ·⇓≅↓′ t | just (done (Λ s′))     | just (done w) = failP
  s ·⇓≅↓′ t | just (done (λ' a s′))  | just (done w) =
    later (♯ ⇓≅↓′ (s′ [/tmTm ⌜ w ⌝ ]))
  s ·⇓≅↓′ t | just (done (fold x v)) | just (done w) = failP
  s ·⇓≅↓′ t | just (done v)          | nothing       = failP
  s ·⇓≅↓′ t | nothing                                = failP

  -- A helper lemma relating reduction and evaluation of recursive
  -- type folding.
  fold⇓≅↓′ : ∀ {m n} (a : Type (1 + n)) (t : Term m n) →
             fold⇓ a (t ↓) ≅P (fold a t) ↓
  fold⇓≅↓′ a t with step t
  ... | just (continue t′) = later (♯ fold⇓≅↓′ a t′)
  ... | just (done v)      = returnP P.refl
  ... | nothing            = failP

  -- A helper lemma relating reduction and evaluation of recursive
  -- type unfolding.
  unfold⇓≅↓′ : ∀ {m n} (a : Type (1 + n)) (t : Term m n) →
               unfold⇓ a (t ↓) ≅P (unfold a t) ↓
  unfold⇓≅↓′ a t with step t
  ... | just (continue t′) = later (♯ unfold⇓≅↓′ a t′)
  ... | just (done (Λ _))      = failP
  ... | just (done (λ' _ _))   = failP
  ... | just (done (fold _ v)) = returnP P.refl
  ... | nothing                = failP

  -- Big-step evaluation and small-step reduction are strongly bisimliar.
  ⇓≅↓′ : ∀ {m n} (t : Term m n) → t ⇓ ≅P t ↓
  ⇓≅↓′ (var x)        = failP
  ⇓≅↓′ (Λ t)          = returnP P.refl
  ⇓≅↓′ (λ' a t)       = returnP P.refl
  ⇓≅↓′ (μ a t)        = later (♯ ⇓≅↓′ (t [/tmTm μ a t ]))
  ⇓≅↓′ (t [ a ])      =
    (t [ a ]) ⇓       ≅⟨ complete ([]-comp t a) ⟩
    (t ⇓) [ a ]⇓      ≅⟨ (⇓≅↓′ t) >>=P (λ v → (_ ∎)) ⟩
    (t ↓) [ a ]⇓      ≅⟨ t [ a ]⇓≅↓′ ⟩
    (t [ a ]) ↓       ∎
  ⇓≅↓′ (s · t)        =
    (s · t) ⇓         ≅⟨ complete (·-comp s t) ⟩
    (s ⇓) ·⇓ (t ⇓)    ≅⟨ (⇓≅↓′ s >>=P λ v → ⇓≅↓′ t >>=P λ w → (_ ∎)) ⟩
    (s ↓) ·⇓ (t ↓)    ≅⟨ s ·⇓≅↓′ t ⟩
    (s · t) ↓         ∎
  ⇓≅↓′ (fold a t)     =
    (fold a t) ⇓      ≅⟨ complete (fold-comp a t) ⟩
    fold⇓ a (t ⇓)     ≅⟨ (⇓≅↓′ t) >>=P (λ v → (_ ∎)) ⟩
    fold⇓ a (t ↓)     ≅⟨ fold⇓≅↓′ a t ⟩
    (fold a t) ↓      ∎
  ⇓≅↓′ (unfold a t)   =
    (unfold a t) ⇓    ≅⟨ complete (unfold-comp a t) ⟩
    unfold⇓ a (t ⇓)   ≅⟨ (⇓≅↓′ t) >>=P (λ v → (_ ∎)) ⟩
    unfold⇓ a (t ↓)   ≅⟨ unfold⇓≅↓′ a t ⟩
    (unfold a t) ↓    ∎

-- Big-step evaluation and small-step reduction are strongly bisimliar.
⇓≅↓ : ∀ {m n} (t : Term m n) → t ⇓ ≅ t ↓
⇓≅↓ t = sound (⇓≅↓′ t)
