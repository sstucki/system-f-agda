------------------------------------------------------------------------
-- Polymorphic and iso-recursive lambda terms
------------------------------------------------------------------------

module SystemF.Term where

open import Data.Fin using (Fin; zero; suc; inject+)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Nat using (ℕ; suc; _+_; _∸_)
open import Data.Product using (Σ; _,_)
open import Data.Vec using (Vec; []; _∷_; lookup; map)
open import Function as Fun hiding (id)
open import Relation.Binary.PropositionalEquality as PropEq
  using (refl; _≡_; cong; cong₂; sym)
open PropEq.≡-Reasoning

open import SystemF.Type

------------------------------------------------------------------------
-- Untyped terms and values

infixl 9 _[_] _·_

-- Untyped terms with up to m free term variables and up to n free
-- type variables
data Term (m n : ℕ) : Set where
  var     : (x : Fin m)                   → Term m n  -- term variable
  Λ       : Term m (1 + n)                → Term m n  -- type abstraction
  λ'      : Type n       → Term (1 + m) n → Term m n  -- term abstraction
  μ       : Type n       → Term (1 + m) n → Term m n  -- recursive term
  _[_]    : Term m n     → Type n         → Term m n  -- type application
  _·_     : Term m n     → Term m n       → Term m n  -- term application
  fold    : Type (1 + n) → Term m n       → Term m n  -- fold recursive type
  unfold  : Type (1 + n) → Term m n       → Term m n  -- unfold recursive type

-- Untyped values with up to m free term variables and up to n free
-- type variables
data Val (m n : ℕ) : Set where
  Λ       : Term m (1 + n)                → Val m n   -- type abstraction
  λ'      : Type n       → Term (1 + m) n → Val m n   -- term abstraction
  fold    : Type (1 + n) → Val m n        → Val m n   -- fold recursive type

-- Conversion from values to terms
⌜_⌝  : ∀ {m n} → Val m n → Term m n
⌜ Λ x      ⌝ = Λ x
⌜ λ' a t   ⌝ = λ' a t
⌜ fold a t ⌝ = fold a ⌜ t ⌝


------------------------------------------------------------------------
-- Substitutions in terms

-- Type substitutions in terms
module TermTypeSubst where

  module TermTypeApp {T} (l : Lift T Type) where
    open Lift l hiding (var)
    open TypeSubst.TypeApp l renaming (_/_ to _/tp_)

    infixl 8 _/_

    -- Apply a type substitution to a term
    _/_ : ∀ {m n k} → Term m n → Sub T n k → Term m k
    var x      / σ = var x
    Λ t        / σ = Λ (t / σ ↑)
    λ' a t     / σ = λ' (a /tp σ) (t / σ)
    μ a t      / σ = μ (a /tp σ) (t / σ)
    t [ a ]    / σ = (t / σ) [ a /tp σ ]
    s · t      / σ = (s / σ) · (t / σ)
    fold a t   / σ = fold (a /tp σ ↑) (t / σ)
    unfold a t / σ = unfold (a /tp σ ↑) (t / σ)

  open TypeSubst using (varLift; termLift; sub)

  module Lifted {T} (lift : Lift T Type) {m} where
    application : Application (Term m) T
    application = record { _/_ = TermTypeApp._/_ lift {m = m} }

    open Application application public

  open Lifted termLift public

  -- Apply a type variable substitution (renaming) to a term
  _/Var_ : ∀ {m n k} → Term m n → Sub Fin n k → Term m k
  _/Var_ = TermTypeApp._/_ varLift

  -- Weaken a term with an additional type variable
  weaken : ∀ {m n} → Term m n → Term m (suc n)
  weaken t = t /Var VarSubst.wk

  infix 8 _[/_]

  -- Shorthand for single-variable type substitutions in terms
  _[/_] : ∀ {m n} → Term m (1 + n) → Type n → Term m n
  t [/ b ] = t / sub b


-- Lemmas about type substitutions in terms.
module TermTypeLemmas where
  open TermTypeSubst public

  private module T = TypeLemmas
  private module V = VarLemmas

  /-↑⋆ :
    ∀ {T₁ T₂} {lift₁ : Lift T₁ Type} {lift₂ : Lift T₂ Type} →
    let open T.Lifted lift₁ using () renaming (_↑⋆_ to _↑⋆₁_; _/_ to _/tp₁_)
        open   Lifted lift₁ using () renaming (_/_  to _/₁_)
        open T.Lifted lift₂ using () renaming (_↑⋆_ to _↑⋆₂_; _/_ to _/tp₂_)
        open   Lifted lift₂ using () renaming (_/_  to _/₂_)
    in
    ∀ {n k} (ρ₁ : Sub T₁ n k) (ρ₂ : Sub T₂ n k) →
    (∀ i x → Type.var x /tp₁ ρ₁ ↑⋆₁ i ≡ Type.var x /tp₂ ρ₂ ↑⋆₂ i) →
     ∀ i {m} (t : Term m (i + n))  → t /₁ ρ₁ ↑⋆₁ i ≡ t /₂ ρ₂ ↑⋆₂ i
  /-↑⋆ ρ₁ ρ₂ hyp i (var x)      = refl
  /-↑⋆ ρ₁ ρ₂ hyp i (Λ t)        = cong Λ      (/-↑⋆ ρ₁ ρ₂ hyp (1 + i) t)
  /-↑⋆ ρ₁ ρ₂ hyp i (λ' a t)     =
    cong₂ λ'     (T./-↑⋆ ρ₁ ρ₂ hyp i a)       (/-↑⋆ ρ₁ ρ₂ hyp i t)
  /-↑⋆ ρ₁ ρ₂ hyp i (μ a t)      =
    cong₂ μ      (T./-↑⋆ ρ₁ ρ₂ hyp i a)       (/-↑⋆ ρ₁ ρ₂ hyp i t)
  /-↑⋆ ρ₁ ρ₂ hyp i (t [ b ])    =
    cong₂ _[_]     (/-↑⋆ ρ₁ ρ₂ hyp i t)     (T./-↑⋆ ρ₁ ρ₂ hyp i b)
  /-↑⋆ ρ₁ ρ₂ hyp i (s · t)      =
    cong₂ _·_      (/-↑⋆ ρ₁ ρ₂ hyp i s)       (/-↑⋆ ρ₁ ρ₂ hyp i t)
  /-↑⋆ ρ₁ ρ₂ hyp i (fold a t)   =
    cong₂ fold   (T./-↑⋆ ρ₁ ρ₂ hyp (1 + i) a) (/-↑⋆ ρ₁ ρ₂ hyp i t)
  /-↑⋆ ρ₁ ρ₂ hyp i (unfold a t) =
    cong₂ unfold (T./-↑⋆ ρ₁ ρ₂ hyp (1 + i) a) (/-↑⋆ ρ₁ ρ₂ hyp i t)

  /-wk : ∀ {m n} (t : Term m n) → t / TypeSubst.wk ≡ weaken t
  /-wk t = /-↑⋆ TypeSubst.wk VarSubst.wk (λ k x → begin
    tpVar x T./ T.wk T.↑⋆ k         ≡⟨ T.var-/-wk-↑⋆ k x ⟩
    tpVar (Data.Fin.lift k suc x)   ≡⟨ cong tpVar (sym (V.var-/-wk-↑⋆ k x)) ⟩
    tpVar (lookup x (V.wk V.↑⋆ k))  ≡⟨ refl ⟩
    tpVar x T./Var V.wk V.↑⋆ k      ∎) 0 t
      where open Type using () renaming (var to tpVar)


-- Term substitutions in terms
module TermTermSubst where

  -- Substitutions of terms in terms
  --
  -- A TermSub T m n k is a substitution which, when applied to a term
  -- with at most m free term variables and n free type variables,
  -- yields a term with at most k free term variables and n free type
  -- variables.
  TermSub : (ℕ → ℕ → Set) → ℕ → ℕ → ℕ → Set
  TermSub T m n k = Sub (flip T n) m k

  record TermLift (T : ℕ → ℕ → Set) : Set where
    infix 10 _↑tm _↑tp
    field
      lift : ∀ {m n} → T m n → Term m n
      _↑tm : ∀ {m n k} → TermSub T m n k → TermSub T (suc m) n (suc k)
      _↑tp : ∀ {m n k} → TermSub T m n k → TermSub T m (suc n) k

  module TermTermApp {T} (l : TermLift T) where
    open TermLift l

    infixl 8 _/_

    -- Apply a term substitution to a term
    _/_ : ∀ {m n k} → Term m n → TermSub T m n k → Term k n
    var x      / ρ = lift (lookup x ρ)
    Λ t        / ρ = Λ (t / ρ ↑tp)
    λ' a t     / ρ = λ' a (t / ρ ↑tm)
    μ a t      / ρ = μ a (t / ρ ↑tm)
    t [ a ]    / ρ = (t / ρ) [ a ]
    s · t      / ρ = (s / ρ) · (t / ρ)
    fold a t   / ρ = fold a (t / ρ)
    unfold a t / ρ = unfold a (t / ρ)

  Fin′ : ℕ → ℕ → Set
  Fin′ m _ = Fin m

  varLift : TermLift Fin′
  varLift = record { lift = var; _↑tm = VarSubst._↑; _↑tp = Fun.id }

  infixl 8 _/Var_

  _/Var_ : ∀ {m n k} → Term m n → Sub Fin m k → Term k n
  _/Var_ = TermTermApp._/_ varLift

  Term′ : ℕ → ℕ → Set
  Term′ = flip Term

  private
    module ExpandSimple {n : ℕ} where
      simple : Simple (Term′ n)
      simple = record { var = var; weaken = λ t → t /Var VarSubst.wk }

      open Simple simple public

  open ExpandSimple  using (_↑; simple)
  open TermTypeSubst using () renaming (weaken to weakenTp)

  termLift : TermLift Term
  termLift = record
    { lift = Fun.id; _↑tm = _↑ ; _↑tp = λ ρ → map weakenTp ρ }

  private
    module ExpandSubst {n : ℕ} where
      app : Application (Term′ n) (Term′ n)
      app = record { _/_ = TermTermApp._/_ termLift {n = n} }

      subst : Subst (flip Term n)
      subst = record
        { simple      = simple
        ; application = app
        }

      open Subst subst public

  open ExpandSubst public hiding (var; simple)

  infix 8 _[/_]

  -- Shorthand for single-variable term substitutions in terms
  _[/_] : ∀ {m n} → Term (1 + m) n → Term m n → Term m n
  s [/ t ] = s / sub t


open TermTypeSubst renaming (weaken to weakenTmTp)
open TermTermSubst renaming (weaken to weakenTmTm) hiding (id)
open TypeSubst     renaming (weaken to weakenTp; weaken↑ to weakenTp↑)
                   hiding (id)


------------------------------------------------------------------------
-- Encoding of additional term operators
--
-- NOTE: These encoded operators require more type information than
-- their "classic" untyped counterparts.  The additional types are
-- required by the underlying (untyped) abstractions and type
-- applications.  Cf. TAPL sec. 24.3, pp. 377-379.
module TermOperators where

  open TypeOperators using (⊤; ⊥; _→ⁿ_)

  -- Polymorphic identity function
  id : {m n : ℕ} → Term m n
  id = Λ (λ' (var zero) (var zero))

  -- Bottom elimination/univeral property of the initial type
  ⊥-elim : ∀ {m n} → Type n → Term m n
  ⊥-elim a = λ' ⊥ ((var zero) [ a ])

  -- Unit value
  tt = id

  -- Top introduction/universal property of the terminal type
  ⊤-intro : ∀ {m n} → Type n → Term m n
  ⊤-intro a = λ' a id

  -- Packing existential types
  as-∃_pack_,_ : ∀ {m n} → Type (1 + n) → Type n → Term m n → Term m n
  as-∃ a pack b , t =
    Λ (λ' (∀' (weakenTp↑ a →' var (suc zero)))
          ((var zero [ weakenTp b ]) · weakenTmTm (weakenTmTp t)))

  -- Unpacking existential types
  unpack_in'_ : ∀ {m n} → Term m n → Term (1 + m) (1 + n) →
                {a : Type (1 + n)} {b : Type n} → Term m n
  unpack_in'_ s t {a} {b} = (s [ b ]) · (Λ (λ' a t))

  -- n-ary term abstraction
  λⁿ : ∀ {m n k} → Vec (Type n) k → Term (k + m) n → Term m n
  λⁿ []       t = t
  λⁿ (a ∷ as) t = λⁿ as (λ' a t)

  infixl 9 _·ⁿ_

  -- n-ary term application
  _·ⁿ_ : ∀ {m n k} → Term m n → Vec (Term m n) k → Term m n
  s ·ⁿ []       = s
  s ·ⁿ (t ∷ ts) = s ·ⁿ ts · t

  -- Record/tuple constructor
  new : ∀ {m n k} → Vec (Term m n) k → {as : Vec (Type n) k} → Term m n
  new []                = tt
  new (t ∷ ts) {a ∷ as} =
    Λ (λ' (map weakenTp (a ∷ as) →ⁿ var zero)
          (var zero ·ⁿ map weakenTmTm (map weakenTmTp (t ∷ ts))))

  -- Field access/projection
  π : ∀ {m n k} → Fin k → Term m n → {as : Vec (Type n) k} → Term m n
  π     () t {[]}
  π {m} x  t {a ∷ as} =
    (t [ lookup x (a ∷ as) ]) · (λⁿ (a ∷ as) (var (inject+ m x)))
