------------------------------------------------------------------------
-- Type checing of polymorphic and iso-recursive lambda terms
------------------------------------------------------------------------

module SystemF.TypeCheck where

open import Data.Fin using (Fin; suc; zero; pred)
open import Data.Nat as Nat using (ℕ; _+_)
open import Data.Product
open import Data.Vec using (_∷_; []; lookup)
open import Function
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

open import SystemF.Type
open import SystemF.Term
open import SystemF.WtTerm

open TypeSubst using () renaming (_[/_]  to _[/tp_])
open CtxSubst  using () renaming (weaken to weakenCtx)

------------------------------------------------------------------------
-- Decision procedures for equality of variable names and types

-- This module contains two decision procedures for type checking:
--
--  * the function typeOf synthesizes a type a for a given (untyped)
--    term t and typing environment Γ, if possible;
--
--  * the function check_⊢_∈_ checks whether a given triple Γ, t, a is
--    in the well-typedness relation.
--
-- The two functions correspond to a synthetic resp. analytic view of
-- type-checking.  Both produce evidence in the form of a typing
-- derivation if type checking succeeds or a proof that no such
-- derivation exists otherwise.


infix 4 _≟n_ _≡tp_ _≟_

-- Equal successors have equal predecessors.
≡suc : ∀ {n} {x y : Fin n} → suc x ≡ suc y → x ≡ y
≡suc refl = refl

-- A decision procedure for equality of variable names.
_≟n_ : ∀ {n} → Decidable {A = Fin n} _≡_
zero  ≟n zero   = yes refl
suc x ≟n suc y  with x ≟n y
... | yes x≡y   = yes (cong suc x≡y)
... | no  x≢y   = no (x≢y ∘ ≡suc)
zero  ≟n suc y  = no λ()
suc x ≟n zero   = no λ()

-- A shorthand for (syntactic) type equality.
_≡tp_ : ∀ {n} → Type n → Type n → Set
a ≡tp b = a ≡ b

-- Equal type variables have equal names.
≡var : ∀ {n} {x y : Fin n} → var x ≡tp var y → x ≡ y
≡var refl = refl

-- Equal function types have equal domains.
≡dom→ : ∀ {n} {a a′ b b′ : Type n} → a →' b ≡tp a′ →' b′ → a ≡ a′
≡dom→ refl = refl

-- Equal function types have equal codomains.
≡cod→ : ∀ {n} {a a′ b b′ : Type n} → a →' b ≡tp a′ →' b′ → b ≡ b′
≡cod→ refl = refl

-- Equal univeral types have equal bodies.
≡∀ : ∀ {n} {a a′ : Type (1 + n)} → ∀' a ≡tp ∀' a′ → a ≡ a′
≡∀ refl = refl

-- Equal recursive types have equal bodies.
≡μ : ∀ {n} {a a′ : Type (1 + n)} → μ a ≡tp μ a′ → a ≡ a′
≡μ refl = refl

-- A decision procedure for (syntactic) type equality
_≟_ : ∀ {n} → Decidable {A = Type n} _≡_
var x  ≟ var  y    with x ≟n y
var x  ≟ var .x    | yes refl = yes refl
var x  ≟ var  y    | no  x≢y  = no (x≢y ∘ ≡var)
var _  ≟ _ →' _    = no λ()
var _  ≟ ∀' _      = no λ()
var _  ≟ μ _       = no λ()
a →' b ≟ var x     = no λ()
a →' b ≟  a′ →' b′ with a ≟ a′ | b ≟ b′
a →' b ≟ .a →' .b  | yes refl  | yes refl = yes refl
a →' b ≟  a′ →' b′ | yes _     | no  b≢b′ = no (b≢b′ ∘ ≡cod→)
a →' b ≟  a′ →' b′ | no  a≢a′  | _        = no (a≢a′ ∘ ≡dom→)
a →' b ≟ ∀' _      = no λ()
a →' b ≟ μ _       = no λ()
∀' _   ≟ var _     = no λ()
∀' _   ≟ _ →' _    = no λ()
∀' a   ≟ ∀'  a′    with a ≟ a′
∀' a   ≟ ∀' .a     | yes refl = yes refl
∀' a   ≟ ∀'  a′    | no  a≢a′ = no (a≢a′ ∘ ≡∀)
∀' _   ≟ μ _       = no λ()
μ _    ≟ var _     = no λ()
μ _    ≟ _ →' _    = no λ()
μ _    ≟ ∀' _      = no λ()
μ a    ≟ μ  a′     with a ≟ a′
μ a    ≟ μ .a      | yes refl = yes refl
μ a    ≟ μ  a′     | no  a≢a′ = no (a≢a′ ∘ ≡μ)


------------------------------------------------------------------------
-- Inversion and functionality of the well-typedness relation

-- Inversion of type application typing.
Λ-inversion : ∀ {m n} {Γ : Ctx m n} {t a} →
              Γ ⊢ Λ t ∈ a → ∃ λ a′ → (a ≡ ∀' a′) × (weakenCtx Γ ⊢ t ∈ a′)
Λ-inversion {a = ∀' a′} (Λ t∈a) = a′ , (refl , t∈a)

-- Inversion of term application typing.
λ'-inversion : ∀ {m n} {Γ : Ctx m n} {t a a→b} →
               Γ ⊢ λ' a t ∈ a→b → ∃ λ b → (a→b ≡ a →' b) × (a ∷ Γ ⊢ t ∈ b)
λ'-inversion {a→b = a →' b} (λ' .a t∈b) = b , (refl , t∈b)

-- Inversion of recursive term typing.
μ-inversion : ∀ {m n} {Γ : Ctx m n} {t a a′} →
              Γ ⊢ μ a t ∈ a′ → (a ≡ a′) × (a ∷ Γ ⊢ t ∈ a)
μ-inversion (μ a t∈b) = refl , t∈b

-- Inversion of type application.
[]-inversion : ∀ {m n} {Γ : Ctx m n} {t b a[/b]} → Γ ⊢ t [ b ] ∈ a[/b] →
               ∃ λ a → (a[/b] ≡ a [/tp b ]) × (Γ ⊢ t ∈ ∀' a)
[]-inversion (_[_] {a = a} t∈∀a b) = a , (refl , t∈∀a)

-- Inversion of term application.
·-inversion : ∀ {m n} {Γ : Ctx m n} {s t b} → Γ ⊢ s · t ∈ b →
              ∃ λ a → (Γ ⊢ s ∈ a →' b) × (Γ ⊢ t ∈ a)
·-inversion (_·_ {a = a} s∈a→b t∈a) = a , (s∈a→b , t∈a)

-- Inversion of recursive type folding.
fold-inversion : ∀ {m n} {Γ : Ctx m n} {t a μa} → Γ ⊢ fold a t ∈ μa →
                 (μa ≡ μ a) × (Γ ⊢ t ∈ a [/tp μ a ])
fold-inversion (fold a t∈a[/μa]) = refl , t∈a[/μa]

-- Inversion of recursive type unfolding.
unfold-inversion : ∀ {m n} {Γ : Ctx m n} {t a a[/μa]} →
                   Γ ⊢ unfold a t ∈ a[/μa] →
                   (a[/μa] ≡ a [/tp μ a ]) × (Γ ⊢ t ∈ μ a)
unfold-inversion (unfold a t∈μa) = refl , t∈μa

-- The relation _⊢_∈_ is functional in its last argument.
functional : ∀ {m n} {Γ : Ctx m n} {t a a′} → Γ ⊢ t ∈ a → Γ ⊢ t ∈ a′ → a ≡ a′
functional (var x)       (var .x)        = refl
functional (Λ t∈a)       (Λ t∈a′)        = cong ∀' (functional t∈a t∈a′)
functional (λ' a t∈b)    (λ' .a t∈b′)    = cong (_→'_ a) (functional t∈b t∈b′)
functional (μ a t∈a)     (μ .a t∈a′)     = functional t∈a t∈a′
functional (t∈∀a [ b ])  (t∈∀a′ [ .b ])  =
  cong (λ{ (∀' a)   → a [/tp b ] ; a → a }) (functional t∈∀a t∈∀a′)
functional (s∈a→b · _)   (s∈a→b′ · _)    =
  cong (λ{ (a →' b) → b          ; a → a }) (functional s∈a→b s∈a→b′)
functional (fold a t∈)   (fold .a t∈′)   = refl
functional (unfold a t∈) (unfold .a t∈′) = refl

-- A variant of functionality.
functional′ : ∀ {m n} {Γ : Ctx m n} {t a a′} → Γ ⊢ t ∈ a → a ≢ a′ → Γ ⊢ t ∉ a′
functional′ t∈a = contraposition (functional t∈a)


------------------------------------------------------------------------
-- Type checking

infix 5 check_⊢_∈_

-- A predicate for typable terms
HasType : ∀ {m n} → Ctx m n → Term m n → Set
HasType Γ t = ∃ λ a → Γ ⊢ t ∈ a

-- Type checking viewed as a decision procedure for the existence of
-- typings (i.e. type synthesis).  Note that together with
-- functionality, this proves that the well-typedness relation is a
-- decidable partial function.
typeOf : ∀ {m n} (Γ : Ctx m n) t → Dec (HasType Γ t)
typeOf Γ (var x)      = yes (lookup x Γ , var x)
typeOf Γ (Λ t)        with typeOf (weakenCtx Γ) t
... | yes (a , t∈a)   = yes (∀' a , Λ t∈a)
... | no ∄a           = no (∄a ∘ map id proj₂ ∘ Λ-inversion ∘ proj₂)
typeOf Γ (λ' a t)     with typeOf (a ∷ Γ) t
... | yes (b , t∈b)   = yes (a →' b , λ' a t∈b)
... | no ∄b           = no (∄b ∘ map id proj₂ ∘ λ'-inversion ∘ proj₂)
typeOf Γ (μ a t)      with typeOf (a ∷ Γ) t
typeOf Γ (μ a t)      | yes ( a′ , t∈a′) with a′ ≟ a
typeOf Γ (μ a t)      | yes (.a  , t∈a′) | yes refl = yes (a , μ a t∈a′)
... | no  a′≢a = no (a′≢a ∘ functional t∈a′ ∘ proj₂ ∘ μ-inversion ∘ proj₂)
typeOf Γ (μ a t)      | no ∄a′ =
  no (∄a′ ∘ map id (uncurry ⊢substTp ∘ μ-inversion))
typeOf Γ (t [ b ])    with typeOf Γ t
typeOf Γ (t [ b ])    | yes (var _  , t∈x   ) =
  no ((functional′ t∈x λ()) ∘ proj₂ ∘ proj₂ ∘ []-inversion ∘ proj₂)
typeOf Γ (t [ b ])    | yes (_ →' _ , t∈a→b ) =
  no ((functional′ t∈a→b λ()) ∘ proj₂ ∘ proj₂ ∘ []-inversion ∘ proj₂)
typeOf Γ (t [ b ])    | yes (∀' a   , t∈∀a  ) = yes (a [/tp b ] , t∈∀a [ b ])
typeOf Γ (t [ b ])    | yes (μ _    , t∈μa  ) =
  no ((functional′ t∈μa λ()) ∘ proj₂ ∘ proj₂ ∘ []-inversion ∘ proj₂)
typeOf Γ (t [ b ])    | no  ∄a = no (∄a ∘ map ∀' proj₂ ∘ []-inversion ∘ proj₂)
typeOf Γ (s · t)      with typeOf Γ s | typeOf Γ t
typeOf Γ (s · t)      | yes (var _  , s∈x  ) | _ =
  no ((functional′ s∈x λ()) ∘ proj₁ ∘ proj₂ ∘ ·-inversion ∘ proj₂)
typeOf Γ (s · t) | yes (a →' b , s∈a→b) | yes ( a′ , t∈a) with a′ ≟ a
typeOf Γ (s · t) | yes (a →' b , s∈a→b) | yes (.a  , t∈a) | yes refl =
  yes (b , s∈a→b · t∈a)
typeOf Γ (s · t) | yes (a →' b , s∈a→b) | yes ( a′ , t∈a) | no  a′≢a =
  no (a′≢a ∘ helper)
  where
    helper : HasType Γ (s · t) → a′ ≡ a
    helper (b , s·t∈b) with ·-inversion s·t∈b
    ... | c , s∈c→b , t∈c = begin
      a′ ≡⟨ functional t∈a t∈c ⟩
      c  ≡⟨ ≡dom→ (functional s∈c→b s∈a→b) ⟩
      a  ∎
typeOf Γ (s · t) | yes (a →' b , s∈a→b) | no  ∄a′ =
  no (∄a′ ∘ map id proj₂ ∘ ·-inversion ∘ proj₂)
typeOf Γ (s · t) | yes (∀' _   , s∈∀a ) | _ =
  no ((functional′ s∈∀a λ()) ∘ proj₁ ∘ proj₂ ∘ ·-inversion ∘ proj₂)
typeOf Γ (s · t) | yes (μ  _   , s∈μa ) | _ =
  no ((functional′ s∈μa λ()) ∘ proj₁ ∘ proj₂ ∘ ·-inversion ∘ proj₂)
typeOf Γ (s · t) | no  ∄a               | _ = no (∄a ∘ helper)
  where
    helper : HasType Γ (s · t) → HasType Γ s
    helper (b , s·t∈b) with ·-inversion s·t∈b
    ... | a , s∈a→b , _ = a →' b , s∈a→b
typeOf Γ (fold a t)   with typeOf Γ t
typeOf Γ (fold a t)   | yes (a′ , t∈a′) with a′ ≟ a [/tp μ a ]
typeOf Γ (fold a t)   | yes (._ , t∈a′) | yes refl = yes (μ a , fold a t∈a′)
typeOf Γ (fold a t)   | yes (a′ , t∈a′) | no a′≢a[/μa] =
  no (a′≢a[/μa] ∘ functional t∈a′ ∘ proj₂ ∘ fold-inversion ∘ proj₂)
typeOf Γ (fold a t)   | no  ∄a′ =
  no (∄a′ ∘ map (const (a [/tp μ a ])) id ∘ fold-inversion ∘ proj₂)
typeOf Γ (unfold a t) with typeOf Γ t
typeOf Γ (unfold a t) | yes (a′ , t∈a′) with a′ ≟ μ a
typeOf Γ (unfold a t) | yes (._ , t∈a′) | yes refl =
  yes (a [/tp μ a ] , unfold a t∈a′)
typeOf Γ (unfold a t) | yes (a′ , t∈a′) | no a′≢μa =
  no (a′≢μa ∘ functional t∈a′ ∘ proj₂ ∘ unfold-inversion ∘ proj₂)
typeOf Γ (unfold a t) | no  ∄a′ =
  no (∄a′ ∘ map (const (μ a)) id ∘ unfold-inversion ∘ proj₂)

-- Type checking as a decision procedure for the well-typedness
-- relation.
check_⊢_∈_ : ∀ {m n} (Γ : Ctx m n) t a → Dec (Γ ⊢ t ∈ a)
check Γ ⊢ t ∈ a with typeOf Γ t
check Γ ⊢ t ∈ a | yes ( a′ , t∈a′) with a′ ≟ a
check Γ ⊢ t ∈ a | yes (.a  , t∈a ) | yes refl = yes t∈a
check Γ ⊢ t ∈ a | yes ( a′ , t∈a′) | no  a′≢a = no (a′≢a ∘ functional t∈a′)
check Γ ⊢ t ∈ a | no   ∄a′                    = no (∄a′ ∘ helper)
  where
    helper : ∀ {m n} {Γ : Ctx m n} {t a} → Γ ⊢ t ∈ a → HasType Γ t
    helper {a = a} t∈a = a , t∈a


------------------------------------------------------------------------
-- Some simple test cases

private
  module TpOp = TypeOperators
  module TmOp = TermOperators
  module WtOp = WtTermOperators

-- Test: synthesize the type of the polymorphic identity.
test-typeOf-id : typeOf [] (TmOp.id {n = 0}) ≡ yes (TpOp.id , WtOp.id)
test-typeOf-id = refl

-- Test: check the type of the polymorphic identity.
test-check-id : check [] ⊢ TmOp.id {n = 0} ∈ TpOp.id ≡ yes WtOp.id
test-check-id = refl

-- Using the agda2-mode one can also run the above decision procedures
-- interactively in GNU/Emacs by typing C-x C-n <expression>.
-- E.g. typing
--
--   C-x C-n typeOf [] (Λ (λ' (var zero) (var zero)))
--
-- should return
--
--   yes (∀' (var zero →' var zero) , Λ (λ' (var zero) (var zero)))


------------------------------------------------------------------------
-- Uniqueness of typing derivations

-- There is at most one typing derivation for each triple Γ, t, a.
-- I.e. if there is an x : Γ ⊢ t ∈ a, it is unique.
unique : ∀ {m n} {Γ : Ctx m n} {t a} (t∈a t∈a′ : Γ ⊢ t ∈ a) → t∈a ≡ t∈a′
unique (var x)    (var .x)     = refl
unique (Λ t∈a)    (Λ t∈a′)     = cong Λ (unique t∈a t∈a′)
unique (λ' a t∈a) (λ' .a t∈a′) = cong (λ' a) (unique t∈a t∈a′)
unique (μ  a t∈a) (μ  .a t∈a′) = cong (μ  a) (unique t∈a t∈a′)
unique {Γ = Γ} {t [ b ]} (_[_] {a = a } t∈a .b) t∈a′[b] = helper t∈a′[b] refl
  where
    helper : ∀ {a′[/b]} (t∈a′[b] : Γ ⊢ t [ b ] ∈ a′[/b])
             (a[/b]≡a′[/b] : a [/tp b ] ≡ a′[/b]) →
             ⊢substTp a[/b]≡a′[/b] (t∈a [ b ]) ≡ t∈a′[b]
    helper (_[_] {a = a′} t∈a′ .b) _ with functional t∈a t∈a′
    helper (t∈a′ [ .b ]) refl | refl = cong _ (unique t∈a t∈a′)
unique (_·_ {a = a} s∈a→b t∈a) (_·_ {a = a′} s∈a′→b t∈a′) with
  functional s∈a→b s∈a′→b
unique (s∈a→b · t∈a) (s∈a′→b · t∈a′) | refl =
  cong₂ _·_ (unique s∈a→b s∈a′→b) (unique t∈a t∈a′)
unique (fold   a t∈a) (fold   .a t∈a′) = cong (fold   a) (unique t∈a t∈a′)
unique (unfold a t∈a) (unfold .a t∈a′) = cong (unfold a) (unique t∈a t∈a′)
