------------------------------------------------------------------------
-- Well-typed polymorphic and iso-recursive lambda terms
------------------------------------------------------------------------

module SystemF.WtTerm where

open import Data.Fin using (Fin; zero; suc; inject+)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.List using (List; _∷_)
open import Data.List.All using (All; []; _∷_)
open import Data.Nat using (zero; suc; ℕ; _+_)
open import Data.Product using (_,_)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; toList; zip)
open import Data.Vec.Properties
  using (map-∘; map-cong; lookup-map; lookup-++-inject+)
open import Function as Fun using (_∘_)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; cong; cong₂; subst; sym)
open PropEq.≡-Reasoning
open import Relation.Nullary using (¬_)

open import SystemF.Type
open import SystemF.Term

------------------------------------------------------------------------
-- Typing derivations for polymorphic and iso-recursive lambda terms

-- Typing contexts mapping free (term) variables to types.  A context
-- of type Ctx m n maps m free variables to types containing up to n
-- free type variables each.
Ctx : ℕ → ℕ → Set
Ctx m n = Vec (Type n) m

-- Type and variable substitutions lifted to typing contexts
module CtxSubst where

  infixl 8 _/_ _/Var_

  -- Type substitution lifted to typing contexts
  _/_ : ∀ {m n k} → Ctx m n → Sub Type n k → Ctx m k
  Γ / σ = Γ TypeSubst.⊙ σ

  -- Weakening of typing contexts with additional type variables
  weaken : ∀ {m n} → Ctx m n → Ctx m (1 + n)
  weaken Γ = map TypeSubst.weaken Γ

  -- Variable substitution (renaming) lifted to typing contexts
  _/Var_ : ∀ {m n k} → Sub Fin m k → Ctx k n → Ctx m n
  σ /Var Γ = map (λ x → lookup x Γ) σ

open TypeSubst using () renaming (_[/_]  to _[/tp_])
open CtxSubst  using () renaming (weaken to weakenCtx)

infix  4 _⊢_∈_ _⊢_∉_ _⊢val_∈_ _⊢ⁿ_∈_
infixl 9 _·_ _[_]

-- Typing derivations for well-typed terms
data _⊢_∈_ {m n} (Γ : Ctx m n) : Term m n → Type n → Set where
  var    : (x : Fin m) → Γ ⊢ var x ∈ lookup x Γ
  Λ      : ∀ {t a} → (weakenCtx Γ) ⊢ t ∈ a → Γ ⊢ Λ t ∈ ∀' a
  λ'     : ∀ {t b} → (a : Type n) → a ∷ Γ ⊢ t ∈ b → Γ ⊢ λ' a t ∈ a →' b
  μ      : ∀ {t} → (a : Type n) → a ∷ Γ ⊢ t ∈ a → Γ ⊢ μ a t ∈ a
  _[_]   : ∀ {t a} → Γ ⊢ t ∈ ∀' a → (b : Type n) → Γ ⊢ t [ b ] ∈ a [/tp b ]
  _·_    : ∀ {s t a b} → Γ ⊢ s ∈ a →' b → Γ ⊢ t ∈ a → Γ ⊢ s · t ∈ b
  fold   : ∀ {t} → (a : Type (1 + n)) → Γ ⊢ t ∈ a [/tp μ a ] →
           Γ ⊢ fold a t ∈ μ a
  unfold : ∀ {t} → (a : Type (1 + n)) → Γ ⊢ t ∈ μ a →
           Γ ⊢ unfold a t ∈ a [/tp μ a ]

-- Negation of well-typedness.
_⊢_∉_ : ∀ {m n} → Ctx m n → Term m n → Type n → Set
Γ ⊢ t ∉ a = ¬ Γ ⊢ t ∈ a

-- Typing derivations for well-typed values.
data _⊢val_∈_ {m n} (Γ : Ctx m n) : Val m n → Type n → Set where
  Λ    : ∀ {t a} → (weakenCtx Γ) ⊢ t ∈ a → Γ ⊢val Λ t ∈ ∀' a
  λ'   : ∀ {t b} → (a : Type n) → a ∷ Γ ⊢ t ∈ b → Γ ⊢val λ' a t ∈ a →' b
  fold : ∀ {v} → (a : Type (1 + n)) → Γ ⊢val v ∈ a [/tp μ a ] →
         Γ ⊢val fold a v ∈ μ a

-- Conversion from well-typed values to well-typed terms.
⊢⌜_⌝ : ∀ {m n} {Γ : Ctx m n} {v a} → Γ ⊢val v ∈ a → Γ ⊢ ⌜ v ⌝ ∈ a
⊢⌜ Λ x      ⌝ = Λ x
⊢⌜ λ' a t   ⌝ = λ' a t
⊢⌜ fold a t ⌝ = fold a ⊢⌜ t ⌝

-- Collections of typing derivations for well-typed terms.
data _⊢ⁿ_∈_ {m n} (Γ : Ctx m n) :
  ∀ {k} → Vec (Term m n) k → Vec (Type n) k → Set where
    []  : Γ ⊢ⁿ [] ∈ []
    _∷_ : ∀ {t a k} {ts : Vec (Term m n) k} {as : Vec (Type n) k} →
          Γ ⊢ t ∈ a → Γ ⊢ⁿ ts ∈ as → Γ ⊢ⁿ t ∷ ts ∈ a ∷ as

-- Lookup a well-typed term in a collection thereof.
lookup-⊢ : ∀ {m n k} {Γ : Ctx m n} {ts : Vec (Term m n) k}
             {as : Vec (Type n) k} →
           (x : Fin k) → Γ ⊢ⁿ ts ∈ as → Γ ⊢ lookup x ts ∈ lookup x as
lookup-⊢ zero    (⊢t ∷ ⊢ts) = ⊢t
lookup-⊢ (suc x) (⊢t ∷ ⊢ts) = lookup-⊢ x ⊢ts


------------------------------------------------------------------------
-- Lemmas about type and variable substitutions (renaming) lifted to
-- typing contexts

module CtxLemmas where
  open CtxSubst public

  private module Tp  = TypeLemmas
  private module Var = VarSubst

  -- Term variable substitution (renaming) commutes with type
  -- substitution.
  /Var-/ : ∀ {m n k l} (ρ : Sub Fin m k) (Γ : Ctx k n) (σ : Sub Type n l) →
           (ρ /Var Γ) / σ ≡ ρ /Var (Γ / σ)
  /Var-/ ρ Γ σ = begin
      (ρ /Var Γ) / σ
    ≡⟨ sym (map-∘ _ _ ρ) ⟩
      map (λ x → (lookup x Γ) Tp./ σ) ρ
    ≡⟨ map-cong (λ x → sym (Tp.lookup-⊙ x)) ρ ⟩
      map (λ x → lookup x (Γ / σ)) ρ
    ∎

  -- Term variable substitution (renaming) commutes with weakening of
  -- typing contexts with an additional type variable.
  /Var-weaken : ∀ {m n k} (ρ : Sub Fin m k) (Γ : Ctx k n) →
                weaken (ρ /Var Γ) ≡ ρ /Var (weaken Γ)
  /Var-weaken ρ Γ = begin
    weaken (ρ /Var Γ)    ≡⟨ Tp.map-weaken ⟩
    (ρ /Var Γ) / Tp.wk   ≡⟨ /Var-/ ρ Γ Tp.wk ⟩
    ρ /Var (Γ / Tp.wk)   ≡⟨ sym (cong (_/Var_ ρ) Tp.map-weaken) ⟩
    ρ /Var (weaken Γ)    ∎

  -- Term variable substitution (renaming) commutes with term variable
  -- lookup in typing context.
  /Var-lookup : ∀ {m n k} (x : Fin m) (ρ : Sub Fin m k) (Γ : Ctx k n) →
                lookup x (ρ /Var Γ) ≡ lookup (lookup x ρ) Γ
  /Var-lookup x ρ Γ = lookup-map x _ _

  -- Term variable substitution (renaming) commutes with weakening of
  -- typing contexts with an additional term variable.
  /Var-∷ : ∀ {m n k} (a : Type n) (ρ : Sub Fin m k) (Γ : Ctx k n) →
           a ∷ (ρ /Var Γ) ≡ (ρ Var.↑) /Var (a ∷ Γ)
  /Var-∷ a []      Γ = refl
  /Var-∷ a (x ∷ ρ) Γ = cong (_∷_ a) (cong (_∷_ (lookup x Γ)) (begin
    map (λ x → lookup x Γ) ρ                   ≡⟨ refl ⟩
    map (λ x → lookup (suc x) (a ∷ Γ)) ρ       ≡⟨ map-∘ _ _ ρ ⟩
    map (λ x → lookup x (a ∷ Γ)) (map suc ρ)   ∎))

  -- Invariants of term variable substitution (renaming)
  idVar-/Var   : ∀ {m n} (Γ : Ctx m n) → Γ ≡ (Var.id /Var Γ)
  wkVar-/Var-∷ : ∀ {m n} (Γ : Ctx m n) (a : Type n) → Γ ≡ (Var.wk /Var (a ∷ Γ))

  idVar-/Var []      = refl
  idVar-/Var (a ∷ Γ) = cong (_∷_ a) (wkVar-/Var-∷ Γ a)

  wkVar-/Var-∷ Γ a = begin
    Γ                    ≡⟨ idVar-/Var Γ ⟩
    Var.id /Var Γ         ≡⟨ map-∘ _ _ VarSubst.id ⟩
    Var.wk /Var (a ∷ Γ)   ∎


------------------------------------------------------------------------
-- Substitutions in well-typed terms

-- Helper lemmas for applying type and term equalities in typing
-- derivations
⊢subst : ∀ {m n} {Γ₁ Γ₂ : Ctx m n} {t₁ t₂ : Term m n} {a₁ a₂ : Type n} →
  Γ₁ ≡ Γ₂ → t₁ ≡ t₂ → a₁ ≡ a₂ → Γ₁ ⊢ t₁ ∈ a₁ → Γ₂ ⊢ t₂ ∈ a₂
⊢subst refl refl refl hyp = hyp

⊢substCtx : ∀ {m n} {Γ₁ Γ₂ : Ctx m n} {t : Term m n} {a : Type n} →
  Γ₁ ≡ Γ₂ → Γ₁ ⊢ t ∈ a → Γ₂ ⊢ t ∈ a
⊢substCtx refl hyp = hyp

⊢substTp : ∀ {m n} {Γ : Ctx m n} {t : Term m n} {a₁ a₂ : Type n} →
  a₁ ≡ a₂ → Γ ⊢ t ∈ a₁ → Γ ⊢ t ∈ a₂
⊢substTp refl hyp = hyp


-- Type substitutions lifted to well-typed terms
module WtTermTypeSubst where
  open TypeLemmas hiding (_/_; _[/_]; weaken)
  private
    module Tp = TypeLemmas
    module Tm = TermTypeLemmas
    module C  = CtxSubst

  infixl 8 _/_

  -- Type substitutions lifted to well-typed terms
  _/_ : ∀ {m n k} {Γ : Ctx m n} {t : Term m n} {a : Type n} →
        Γ ⊢ t ∈ a → (σ : Sub Type n k) → Γ C./ σ ⊢ t Tm./ σ ∈ a Tp./ σ
  var x             / σ = ⊢substTp (lookup-⊙ x) (var x)
  _/_ {Γ = Γ} (Λ ⊢t)  σ =
    Λ (⊢substCtx (sym (map-weaken-⊙ Γ σ)) (⊢t / σ ↑))
  λ' a ⊢t           / σ = λ' (a Tp./ σ) (⊢t / σ)
  μ a ⊢t            / σ = μ  (a Tp./ σ) (⊢t / σ)
  _[_] {a = a} ⊢t b / σ =
    ⊢substTp (sym (sub-commutes a)) ((⊢t / σ) [ b Tp./ σ ])
  ⊢s · ⊢t           / σ = (⊢s / σ) · (⊢t / σ)
  fold a ⊢t         / σ =
    fold (a Tp./ σ ↑) (⊢substTp (sub-commutes a) (⊢t / σ))
  unfold a ⊢t       / σ =
    ⊢substTp (sym (sub-commutes a)) (unfold (a Tp./ σ ↑) (⊢t / σ))

  -- Weakening of terms with additional type variables lifted to
  -- well-typed terms.
  weaken : ∀ {m n} {Γ : Ctx m n} {t : Term m n} {a : Type n} →
           Γ ⊢ t ∈ a → C.weaken Γ ⊢ Tm.weaken t ∈ Tp.weaken a
  weaken {t = t} {a = a} ⊢t =
    ⊢subst (sym map-weaken) (Tm./-wk t) (/-wk {t = a}) (⊢t / wk)

  -- Weakening of terms with additional type variables lifted to
  -- collections of well-typed terms.
  weakenAll : ∀ {m n k} {Γ : Ctx m n} {ts : Vec (Term m n) k}
                {as : Vec (Type n) k} → Γ ⊢ⁿ ts ∈ as →
                C.weaken Γ ⊢ⁿ map Tm.weaken ts ∈ map Tp.weaken as
  weakenAll {ts = []}    {[]}    []         = []
  weakenAll {ts = _ ∷ _} {_ ∷ _} (⊢t ∷ ⊢ts) = weaken ⊢t ∷ weakenAll ⊢ts

  -- Shorthand for single-variable type substitutions in well-typed
  -- terms.
  _[/_] : ∀ {m n} {Γ : Ctx m (1 + n)} {t a} →
          Γ ⊢ t ∈ a → (b : Type n) → Γ C./ sub b ⊢ t Tm./ sub b ∈ a Tp./ sub b
  ⊢t [/ b ] = ⊢t / sub b

  -- A weakened version of the shorthand for single-variable type
  -- substitutions that fits well with well-typed type application.
  _[/_]′ : ∀ {m n} {Γ : Ctx m n} {t a} → C.weaken Γ ⊢ t ∈ a →
           (b : Type n) → Γ ⊢ t Tm./ sub b ∈ a Tp./ sub b
  ⊢t [/ b ]′ = ⊢substCtx Tp.map-weaken-⊙-sub (⊢t / sub b)


-- Term substitutions lifted to well-typed terms
module WtTermTermSubst where
  private
    module Tp  = TermTypeSubst
    module Tm  = TermTermSubst
    module Var = VarSubst
    module C   = CtxLemmas
    TmSub = Tm.TermSub Term

  infix 4 _⇒_⊢_

  -- Well-typed term substitutions are collections of well-typed terms.
  _⇒_⊢_ : ∀ {m n k} → Ctx m n → Ctx k n → TmSub m n k → Set
  Γ ⇒ Δ ⊢ ρ = Δ ⊢ⁿ ρ ∈ Γ

  infixl 8  _/_ _/Var_
  infix  10 _↑

  -- Application of term variable substitutions (renaming) lifted to
  -- well-typed terms.
  _/Var_ : ∀ {m n k} {Γ : Ctx k n} {t : Term m n} {a : Type n}
             (ρ : Sub Fin m k) → ρ C./Var Γ ⊢ t ∈ a → Γ ⊢ t Tm./Var ρ ∈ a
  _/Var_ {Γ = Γ} ρ (var x)   =
    ⊢substTp (sym (C./Var-lookup x ρ Γ)) (var (lookup x ρ))
  _/Var_ {Γ = Γ} ρ (Λ ⊢t)    =
    Λ    (ρ      /Var ⊢substCtx (C./Var-weaken ρ Γ) ⊢t)
  _/Var_ {Γ = Γ} ρ (λ' a ⊢t) =
    λ' a (ρ Var.↑ /Var ⊢substCtx (C./Var-∷ a ρ Γ) ⊢t)
  _/Var_ {Γ = Γ} ρ (μ a ⊢t)  =
    μ  a (ρ Var.↑ /Var ⊢substCtx (C./Var-∷ a ρ Γ) ⊢t)
  ρ /Var (⊢t [ b ])          = (ρ /Var ⊢t) [ b ]
  ρ /Var (⊢s · ⊢t)           = (ρ /Var ⊢s) · (ρ /Var ⊢t)
  ρ /Var (fold a ⊢t)         = fold   a (ρ /Var ⊢t)
  ρ /Var (unfold a ⊢t)       = unfold a (ρ /Var ⊢t)

  -- Weakening of terms with additional term variables lifted to
  -- well-typed terms.
  weaken : ∀ {m n} {Γ : Ctx m n} {t : Term m n} {a b : Type n} →
           Γ ⊢ t ∈ a → b ∷ Γ ⊢ Tm.weaken t ∈ a
  weaken {Γ = Γ} {b = b} ⊢t =
    Var.wk /Var ⊢substCtx (C.wkVar-/Var-∷ Γ b) ⊢t

  -- Weakening of terms with additional term variables lifted to
  -- collections of well-typed terms.
  weakenAll : ∀ {m n k} {Γ : Ctx m n} {ts : Vec (Term m n) k}
                {as : Vec (Type n) k} {b : Type n} →
              Γ ⊢ⁿ ts ∈ as → b ∷ Γ ⊢ⁿ map Tm.weaken ts ∈ as
  weakenAll {ts = []}    {[]}    []         = []
  weakenAll {ts = _ ∷ _} {_ ∷ _} (⊢t ∷ ⊢ts) = weaken ⊢t ∷ weakenAll ⊢ts

  -- Lifting of well-typed term substitutions.
  _↑ : ∀ {m n k} {Γ : Ctx m n} {Δ : Ctx k n} {ρ b} →
       Γ ⇒ Δ ⊢ ρ → b ∷ Γ ⇒ b ∷ Δ ⊢ ρ Tm.↑
  ⊢ρ ↑ = var zero ∷ weakenAll ⊢ρ

  -- The well-typed identity substitution.
  id : ∀ {m n} {Γ : Ctx m n} → Γ ⇒ Γ ⊢ Tm.id
  id {zero}  {Γ = []}    = []
  id {suc m} {Γ = a ∷ Γ} = id ↑

  -- Well-typed weakening (as a substitution).
  wk : ∀ {m n} {Γ : Ctx m n} {a} → Γ ⇒ a ∷ Γ ⊢ Tm.wk
  wk = weakenAll id

  -- A well-typed substitution which only replaces the first variable.
  sub : ∀ {m n} {Γ : Ctx m n} {t a} → Γ ⊢ t ∈ a → a ∷ Γ ⇒ Γ ⊢ Tm.sub t
  sub ⊢t = ⊢t ∷ id

  -- Application of term substitutions lifted to well-typed terms
  _/_ : ∀ {m n k} {Γ : Ctx m n} {Δ : Ctx k n} {t a ρ} →
        Γ ⊢ t ∈ a → Γ ⇒ Δ ⊢ ρ → Δ ⊢ t Tm./ ρ ∈ a
  var x       / ⊢ρ = lookup-⊢ x ⊢ρ
  Λ ⊢t        / ⊢ρ = Λ (⊢t / (WtTermTypeSubst.weakenAll ⊢ρ))
  λ' a ⊢t     / ⊢ρ = λ' a (⊢t / ⊢ρ ↑)
  μ a ⊢t      / ⊢ρ = μ a (⊢t / ⊢ρ ↑)
  (⊢t [ a ])  / ⊢ρ = (⊢t / ⊢ρ) [ a ]
  (⊢s · ⊢t)   / ⊢ρ = (⊢s / ⊢ρ) · (⊢t / ⊢ρ)
  fold a ⊢t   / ⊢ρ = fold a (⊢t / ⊢ρ)
  unfold a ⊢t / ⊢ρ = unfold a (⊢t / ⊢ρ)

  -- Shorthand for well-typed single-variable term substitutions.
  _[/_] : ∀ {m n} {Γ : Ctx m n} {s t a b} →
          b ∷ Γ ⊢ s ∈ a → Γ ⊢ t ∈ b → Γ ⊢ s Tm./ Tm.sub t ∈ a
  ⊢s [/ ⊢t ] = ⊢s / sub ⊢t


------------------------------------------------------------------------
-- Encoding of additional well-typed term operators
--
-- These correspond to admissible typing rules for the asscociated
-- term operators.

module WtTermOperators where
  open TypeOperators renaming (id to idTp)
  open TypeOperatorLemmas
  open TypeLemmas hiding (id)
  private
    module Ut   = TermOperators
    module ⊢Tp  = WtTermTypeSubst
    module ⊢Tm  = WtTermTermSubst

  -- Polymorphic identity function
  id : ∀ {m n} {Γ : Ctx m n} → Γ ⊢ Ut.id ∈ idTp
  id = Λ (λ' (var (zero)) (var zero))

  -- Bottom elimination/univeral property of the initial type
  ⊥-elim : ∀ {m n} {Γ : Ctx m n} (a : Type n) → Γ ⊢ Ut.⊥-elim a ∈ ⊥ →' a
  ⊥-elim a = λ' ⊥ ((var zero) [ a ])

  -- Unit value
  tt : ∀ {m n} {Γ : Ctx m n} → Γ ⊢ Ut.tt ∈ ⊤
  tt = id

  -- Top introduction/universal property of the terminal type
  ⊤-intro : ∀ {m n} {Γ : Ctx m n} → (a : Type n) → Γ ⊢ Ut.⊤-intro a ∈ a →' ⊤
  ⊤-intro {n = n} a = λ' a (id {n = n})

  -- Packing existential types
  as-∃_pack_,_ : ∀ {m n} {Γ : Ctx m n}
                   (a : Type (1 + n)) (b : Type n) {t : Term m n} →
                 Γ ⊢ t ∈ a [/tp b ] → Γ ⊢ Ut.as-∃ a pack b , t ∈ ∃ a
  as-∃ a pack b , ⊢t =
    Λ (λ' (∀' (weaken↑ a →' var (suc zero))) ((var zero [ weaken b ]) · ⊢t′))
    where ⊢t′ = ⊢Tm.weaken (⊢substTp (weaken-sub a b) (⊢Tp.weaken ⊢t))

  -- Unpacking existential types
  unpack_in'_ : ∀ {m n} {Γ : Ctx m n} {s : Term m n}
                  {t : Term (1 + m) (1 + n)} {a : Type (1 + n)} {b : Type n} →
                Γ ⊢ s ∈ ∃ a → a ∷ weakenCtx Γ ⊢ t ∈ weaken b →
                Γ ⊢ Ut.unpack_in'_ s t {a} {b} ∈ b
  unpack_in'_ {a = a} {b = b} ⊢s ⊢t = (⊢s [ b ]) · Λ (⊢substTp a≡ (λ' a ⊢t))
    where
      a≡ : a →' weaken b ≡ weaken↑ a / (sub b) ↑ →' weaken b
      a≡ = cong (λ a → a →' weaken b) (begin
        a                       ≡⟨ sym (id-vanishes a) ⟩
        a / TypeLemmas.id       ≡⟨ cong (λ σ → a / σ) (sym (id-↑⋆ 1)) ⟩
        a / (TypeLemmas.id) ↑   ≡⟨ cong (λ σ → a / σ ↑) (sym wk-⊙-sub) ⟩
        a / (wk ⊙ sub b) ↑      ≡⟨ cong (λ σ → a / σ) (↑⋆-distrib 1) ⟩
        a / wk ↑ ⊙ (sub b) ↑    ≡⟨ /-⊙ a ⟩
        a / wk ↑ / (sub b) ↑    ∎)

  -- n-ary term abstraction
  λⁿ : ∀ {m n k} {Γ : Ctx m n} (as : Vec (Type n) k) {b : Type n}
       {t : Term (k + m) n} → as ++ Γ ⊢ t ∈ b → Γ ⊢ Ut.λⁿ as t ∈ as →ⁿ b
  λⁿ []       ⊢t = ⊢t
  λⁿ (a ∷ as) ⊢t = λⁿ as (λ' a ⊢t)

  infixl 9 _·ⁿ_

  -- n-ary term application
  _·ⁿ_ : ∀ {m n k} {Γ : Ctx m n} {s : Term m n} {ts : Vec (Term m n) k}
           {as : Vec (Type n) k} {b : Type n} →
         Γ ⊢ s ∈ as →ⁿ b → Γ ⊢ⁿ ts ∈ as → Γ ⊢ s Ut.·ⁿ ts ∈ b
  _·ⁿ_ {ts = []}    {[]}    ⊢s []         = ⊢s
  _·ⁿ_ {ts = _ ∷ _} {_ ∷ _} ⊢s (⊢t ∷ ⊢ts) = ⊢s ·ⁿ ⊢ts · ⊢t

  -- Record/tuple constructor
  new : ∀ {m n k} {Γ : Ctx m n} {ts : Vec (Term m n) k} {as : Vec (Type n) k} →
        Γ ⊢ⁿ ts ∈ as → Γ ⊢ Ut.new ts {as} ∈ rec as
  new {ts = []}    {[]}     []         = tt
  new {ts = _ ∷ _} {a ∷ as} (⊢t ∷ ⊢ts) =
    Λ (λ' (map weaken (a ∷ as) →ⁿ var zero)
          (var zero ·ⁿ ⊢Tm.weakenAll (⊢Tp.weakenAll (⊢t ∷ ⊢ts))))

  -- Field access/projection
  π : ∀ {m n k} {Γ : Ctx m n} (x : Fin k) {t : Term m n}
        {as : Vec (Type n) k} →
      Γ ⊢ t ∈ rec as → Γ ⊢ Ut.π x t {as} ∈ lookup x as
  π             () {as = []}     ⊢t
  π {m} {Γ = Γ} x  {as = a ∷ as} ⊢t =
    (⊢t [ b ]) · ⊢substTp as′→ⁿb′≡ (λⁿ as′ (var x′))
    where
      as′ = a ∷ as
      x′  = inject+ m x
      b   = lookup x   as′
      b′  = lookup x′ (as′ ++ Γ)
      as′→ⁿb′≡ : as′ →ⁿ b′ ≡ (map weaken as′ →ⁿ var zero) [/tp b ]
      as′→ⁿb′≡ = begin
          as′ →ⁿ b′
        ≡⟨ cong (λ b → as′ →ⁿ b) (lookup-++-inject+ as′ Γ x) ⟩
          as′ →ⁿ b
        ≡⟨ cong (λ as′ → as′ →ⁿ b) (sym (map-weaken-⊙-sub {ρ = as′})) ⟩
          map weaken as′ ⊙ sub b →ⁿ b
        ≡⟨ sym (/-→ⁿ (map weaken as′) (var zero) (sub b)) ⟩
          (map weaken as′ →ⁿ var zero) [/tp b ]
        ∎
