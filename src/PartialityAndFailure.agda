----------------------------------------------------------------------
-- A monad with partiality and failure
----------------------------------------------------------------------

module PartialityAndFailure where

open import Coinduction using (∞; ♯_; ♭)
open import Category.Monad
open import Category.Monad.Partiality as Partiality using (_⊥)
open import Data.Maybe as Maybe using (Maybe; just; nothing; maybe)
open import Level using (_⊔_)
open import Function
open import Relation.Binary as B hiding (Rel)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

------------------------------------------------------------------------
-- Danielsson's partiality-and-failure monad.

-- The definitions below are slightly modified versions of those given
-- in the code accompanying Danielsson's ICFP'12 paper "Operational
-- Semantics Using the Partiality Monad".  The original version along
-- with additional explanations can be found at
--
--   http://www.cse.chalmers.se/~nad/publications/danielsson-semantics-partiality-monad.html

_?⊥ : ∀ {a} → Set a → Set a
A ?⊥ = Maybe A ⊥

monad : ∀ {f} → RawMonad {f = f} (_⊥ ∘ Maybe)
monad = Maybe.monadT Partiality.monad

private module M {f} = RawMonad (monad {f})

-- Re-export constructors and kinds of relations.
open Partiality public
  using (now; later; Kind; OtherKind; geq; weak; strong; other)

-- Failure.
private
  -- This module encapsulates fail so we can define/overload it as a
  -- constructor of _?⊥P and RelP in the Workaround and
  -- AlternativeEquality modules below.  Its definitions will be
  -- re-exported at the global scope later.
  module Failure {a} where

    fail : ∀ {A : Set a} → A ?⊥
    fail = now nothing

    infix 7 _or-fail

    _or-fail : ∀ {A B : Set a} → (A → B ?⊥) → Maybe A → B ?⊥
    f or-fail = maybe f fail


------------------------------------------------------------------------
-- Equality/ordering

-- The default equality for the partiality monad (bisimilarity)
-- specialized to include failure and with the underlying equality
-- fixed to "syntactic" equality (_≡_).

module Equality {a} {A : Set a} where
  open M using (_>>=_)
  private module E = Partiality.Equality (_≡_ {A = Maybe A})
  open E public using (now; later; laterʳ; laterˡ)

  infix 4 _≅_ _≳_ _≲_ _≈_

  -- The three relations specialized to include failure and with the
  -- underlying equality fixed to "syntactic" equality (_≡_).
  Rel : Kind → A ?⊥ → A ?⊥ → Set _
  Rel k x y = E.Rel k x y

  _≅_ = Rel strong
  _≳_ = Rel (other geq)
  _≲_ = flip _≳_
  _≈_ = Rel (other weak)

  fail : ∀ {k} → Rel k (Failure.fail) (Failure.fail)
  fail = now P.refl


------------------------------------------------------------------------
-- The (specialized) relations are equivalences or partial orders
-- for the chosen underlying "syntactic" equality (_≡_)

module Equivalence {a} {A : Set a} where
  open Partiality.Equivalence {A = Maybe A} {_∼_ = _≡_} public

-- Equational reasoning with the underlying equality fixed to
-- "syntactic" equality (_≡_).
module Reasoning {a} {A : Set a} where
  open Partiality.Reasoning (P.isEquivalence {A = Maybe A}) public


------------------------------------------------------------------------
-- Laws related to bind

module _ {a} {A B : Set a} where
  open Failure
  open Equality
  open M using (_>>=_)

  infixl 1 _>>=-cong_

  -- Bind preserves all the relations.
  _>>=-cong_ : ∀ {k} {x₁ x₂} {f₁ f₂ : A → B ?⊥} →
               Rel k x₁ x₂ → (∀ x → Rel k (f₁ x) (f₂ x)) →
               Rel k (x₁ >>= f₁) (x₂ >>= f₂)
  _>>=-cong_ {k} {f₁ = f₁} {f₂} x₁≈x₂ f₁≈f₂ =
    x₁≈x₂ Partiality.>>=-cong helper
    where
      helper : ∀ {x y} → x ≡ y → Rel k ((f₁ or-fail) x) ((f₂ or-fail) y)
      helper {x = nothing} P.refl = now P.refl
      helper {x = just x}  P.refl = f₁≈f₂ x


------------------------------------------------------------------------
-- Productivity checker workaround

-- Just like the partiality monad, the partiality-and-fail monad
-- suffers from the limitations of guarded coinduction.  Luckily there
-- is a (limited) workaround for this problem, namely to extend the
-- datatype _?⊥ with a _>>=_ constructor, yielding an embedded
-- language _?⊥P (of _?⊥ "programs") which internalizes the monadic
-- bind operation.  When writing corecursive functions in _?⊥P, one
-- may use _>>=_ without guarding it with other constructors.  By
-- interpreting the resulting programs in _?⊥, one recovers the
-- desired corecursive function.  For details, see e.g. Danielsson's
-- PAR'10 paper "Beating the Productivity Checker Using Embedded
-- Languages".

module Workaround {a} where
  private module W = Partiality.Workaround {a}

  infixl 1 _>>=_

  -- The language of _?⊥ "programs" internalizing _>>=_.
  data _?⊥P : Set a → Set (Level.suc a) where
    return : ∀ {A}   (x : A)                     → A ?⊥P
    later  : ∀ {A}   (x : ∞ (A ?⊥P))             → A ?⊥P
    fail   : ∀ {A}                               → A ?⊥P
    _>>=_  : ∀ {A B} (x : A ?⊥P) (f : A → B ?⊥P) → B ?⊥P

  private

    mutual

      -- Translation of _?⊥ programs to _⊥ programs.
      ⟦_⟧P′ : ∀ {A} → A ?⊥P → (Maybe A) W.⊥P
      ⟦ return x          ⟧P′ = W.now (just x)
      ⟦ later x           ⟧P′ = W.later (♯ ⟦ (♭ x) ⟧P′)
      ⟦ fail              ⟧P′ = W.now nothing
      ⟦ _>>=_ {A} {B} x f ⟧P′ = ⟦ x ⟧P′ W.>>= ⟦>>=⟧-helper f

      ⟦>>=⟧-helper : ∀ {A B : Set a} → (A → B ?⊥P) → Maybe A → (Maybe B) W.⊥P
      ⟦>>=⟧-helper f (just y) = ⟦ f y ⟧P′
      ⟦>>=⟧-helper _ nothing  = W.now nothing

  -- Interpretation of _?⊥ programs in _?⊥.
  ⟦_⟧P : ∀ {A} → A ?⊥P → A ?⊥
  ⟦_⟧P = W.⟦_⟧P ∘ ⟦_⟧P′


  -- The definitions above make sense. ⟦_⟧P is homomorphic with
  -- respect to now, later, fail and _>>=_.
  module Correct where
    open Equality {a} hiding (fail)
    open Reasoning {a}
    private
      module F      = Failure {a}
      module PM {f} = RawMonad (Partiality.monad {f})

    return-hom : ∀ {A} (x : A) → ⟦ return x ⟧P ≅ M.return x
    return-hom x = M.return x ∎

    later-hom : ∀ {A} (x : ∞ (A ?⊥P)) → ⟦ later x ⟧P ≅ later (♯ ⟦ ♭ x ⟧P)
    later-hom x = later (♯ (⟦ ♭ x ⟧P ∎) )

    fail-hom : ∀ {A} → ⟦ fail {A} ⟧P ≅ F.fail {A}
    fail-hom {A} = F.fail {A} ∎

    >>=-hom : ∀ {A B} (x : A ?⊥P) (f : A → B ?⊥P) →
              ⟦ x >>= f ⟧P ≅ (⟦ x ⟧P M.>>= λ y → ⟦ f y ⟧P)
    >>=-hom {A} {B} x f =
        W.⟦ ⟦ x ⟧P′ W.>>= (⟦>>=⟧-helper f) ⟧P
      ≅⟨ W.Correct.>>=-hom ⟦ x ⟧P′ _ ⟩
        (⟦ x ⟧P PM.>>= λ y → W.⟦ ⟦>>=⟧-helper f y ⟧P)
      ≅⟨ (⟦ x ⟧P ∎) Partiality.≡->>=-cong helper ⟩
        (⟦ x ⟧P PM.>>= maybe (⟦_⟧P ∘ f) F.fail)
      ∎
      where
        helper : ∀ y → W.⟦ ⟦>>=⟧-helper f y ⟧P ≅ maybe (⟦_⟧P ∘ f) F.fail y
        helper (just y) = ⟦ f y ⟧P ∎
        helper nothing  = F.fail ∎


------------------------------------------------------------------------
-- An alternative, but equivalent, formulation of equality/ordering

-- This version of equality works around some limitations of guarded
-- corecursion and is therefore easier to use in corecursive proofs.
-- However, it does not admit unrestricted use of transitivity.  For a
-- discussion of the technique and the related issues, see e.g.
--
--  * "Operational Semantics Using the Partiality Monad", Danielsson,
--    ICFP'12
--
--  * "Beating the Productivity Checker Using Embedded Languages",
--    Danielsson, PAR'10
--
--  * "Subtyping, Declaratively -- An Exercise in Mixed Induction and
--    Coinduction", Danielsson and Altenkirch, MPC'10
--
-- All of the above can be found at
--   http://www.cse.chalmers.se/~nad/publications/

module AlternativeEquality {a} where
  open Equality {a} hiding (fail)
  private
    open module F = Failure {a} hiding (fail)
    module AE = Partiality.AlternativeEquality {a}

  mutual
    -- Proof "programs" with the underlying equality fixed to
    -- "syntactic" equality (_≡_) and extended to include failure.

    infix  4 _≅P_ _≳P_ _≈P_
    infix  2 _∎
    infixr 2 _≡⟨_⟩_ _≅⟨_⟩_ _≳⟨_⟩_ _≳⟨_⟩≅_ _≳⟨_⟩≈_ _≈⟨_⟩≅_ _≈⟨_⟩≲_
    infixl 1 _>>=_

    _≅P_ : ∀ {A} → B.Rel (A ?⊥) _
    _≅P_ = RelP strong

    _≳P_ : ∀ {A} → B.Rel (A ?⊥) _
    _≳P_ = RelP (other geq)

    _≈P_ : ∀ {A} → B.Rel (A ?⊥) _
    _≈P_ = RelP (other weak)

    data RelP {A : Set a} : Kind → B.Rel (A ?⊥) (Level.suc a) where

      -- Congruences.

      return : ∀ {k x y} (x≡y : x ≡ y) →
               RelP k (M.return x) (M.return y)
      later  : ∀ {k x y} (x∼y : ∞ (RelP k (♭ x) (♭ y))) →
               RelP k (later x) (later y)
      fail   : ∀ {k} → RelP k (F.fail) (F.fail)
      _>>=_  : ∀ {B : Set a} {k x₁ x₂} {f₁ f₂ : B → A ?⊥} →
               let open M in
               (x₁≡x₂ : RelP k x₁ x₂)
               (f₁∼f₂ : ∀ x → RelP k (f₁ x) (f₂ x)) →
               RelP k (x₁ >>= f₁) (x₂ >>= f₂)

      -- Ordering/weak equality.

      laterʳ : ∀ {x y} (x≈y : RelP (other weak) x (♭ y)) →
               RelP (other weak) x (later y)
      laterˡ : ∀ {k x y} (x∼y : RelP (other k) (♭ x) y) →
               RelP (other k) (later x) y

      -- Equational reasoning. Note that including full transitivity
      -- for weak equality would make _≈P_ trivial; a similar problem
      -- applies to _≳P_ (never ≳P now x would be provable). Instead
      -- the definition of RelP includes limited notions of
      -- transitivity, similar to weak bisimulation up-to various
      -- things.

      _∎      : ∀ {k} x → RelP k x x
      sym     : ∀ {k x y} {eq : Partiality.Equality k} (x∼y : RelP k x y) →
                RelP k y x
      _≡⟨_⟩_  : ∀ {k} x {y z} (x≡y : x ≡ y)  (y∼z : RelP k y z) → RelP k x z
      _≅⟨_⟩_  : ∀ {k} x {y z} (x≅y : x ≅P y) (y∼z : RelP k y z) → RelP k x z
      _≳⟨_⟩_  : ∀     x {y z} (x≳y : x ≳  y) (y≳z : y ≳P z) → x ≳P z
      _≳⟨_⟩≅_ : ∀     x {y z} (x≳y : x ≳P y) (y≅z : y ≅P z) → x ≳P z
      _≳⟨_⟩≈_ : ∀     x {y z} (x≳y : x ≳P y) (y≈z : y ≈P z) → x ≈P z
      _≈⟨_⟩≅_ : ∀     x {y z} (x≈y : x ≈P y) (y≅z : y ≅P z) → x ≈P z
      _≈⟨_⟩≲_ : ∀     x {y z} (x≈y : x ≈P y) (y≲z : z ≳P y) → x ≈P z

      -- If any of the following transitivity-like rules were added to
      -- RelP, then RelP and Rel would no longer be equivalent:
      --
      --   x ≳P y → y ≳P z → x ≳P z
      --   x ≳P y → y ≳  z → x ≳P z
      --   x ≲P y → y ≈P z → x ≈P z
      --   x ≈P y → y ≳P z → x ≈P z
      --   x ≲  y → y ≈P z → x ≈P z
      --   x ≈P y → y ≳  z → x ≈P z
      --   x ≈P y → y ≈P z → x ≈P z
      --   x ≈P y → y ≈  z → x ≈P z
      --   x ≈  y → y ≈P z → x ≈P z
      --
      -- The reason is that any of these rules would make it possible
      -- to derive that never and now x are related.

  -- RelP is complete with respect to Rel.
  complete : ∀ {A k} {x y : A ?⊥} → Rel k x y → RelP k x y
  complete {x = now (just x)} {now (just .x)} (now P.refl) = return P.refl
  complete {x = now (just x)} {now nothing}   (now ())
  complete {x = now nothing}  {now (just _)}  (now ())
  complete {x = now nothing}  {now nothing}   (now P.refl) = fail
  complete (later  x∼y) = later (♯ complete (♭ x∼y))
  complete (laterʳ x≈y) = laterʳ  (complete    x≈y)
  complete (laterˡ x∼y) = laterˡ  (complete    x∼y)

  private
    AE-RelP : ∀ {A : Set a} → Kind → B.Rel (A ?⊥) _
    AE-RelP {A} = AE.RelP (P.setoid (Maybe A))

    -- RelP is sound with respect to the alternative equality of the
    -- partiality monad.
    sound′ : ∀ {A k} {x y : A ?⊥} → RelP k x y → AE-RelP k x y
    sound′ (return x≡y)      = AE.now (P.cong just x≡y)
    sound′ (later x∼y)       = AE.later (♯ sound′ (♭ x∼y))
    sound′ fail              = AE.now P.refl
    sound′ {A} {k} (_>>=_ {B} {f₁ = f₁} {f₂} x f₁∼f₂) =
      sound′ x AE.>>= helper
      where
        helper : ∀ {x y} → x ≡ y → AE-RelP k ((f₁ or-fail) x) ((f₂ or-fail) y)
        helper {x = nothing} P.refl = AE.now P.refl
        helper {x = just x}  P.refl = sound′ (f₁∼f₂ x)
    sound′ (laterʳ x)        = AE.laterʳ (sound′ x)
    sound′ (laterˡ x)        = AE.laterˡ (sound′ x)
    sound′ (x ∎)             = x AE.∎
    sound′ (sym {eq = eq} x) = AE.sym {eq = eq} (sound′ x)
    sound′ (x ≡⟨ x≡y ⟩ y≡z)  = AE._≡⟨_⟩_  x x≡y          (sound′ y≡z)
    sound′ (x ≅⟨ x≅y ⟩ y≅z)  = AE._≅⟨_⟩_  x (sound′ x≅y) (sound′ y≅z)
    sound′ (x ≳⟨ x≳y ⟩ y≳z)  = AE._≳⟨_⟩_  x x≳y          (sound′ y≳z)
    sound′ (x ≳⟨ x≳y ⟩≅ y≅z) = AE._≳⟨_⟩≅_ x (sound′ x≳y) (sound′ y≅z)
    sound′ (x ≳⟨ x≳y ⟩≈ y≈z) = AE._≳⟨_⟩≈_ x (sound′ x≳y) (sound′ y≈z)
    sound′ (x ≈⟨ x≈y ⟩≅ y≅z) = AE._≈⟨_⟩≅_ x (sound′ x≈y) (sound′ y≅z)
    sound′ (x ≈⟨ x≈y ⟩≲ y≲z) = AE._≈⟨_⟩≲_ x (sound′ x≈y) (sound′ y≲z)

  -- RelP is sound with respect to Rel.
  sound : ∀ {A k} {x y : A ?⊥} → RelP k x y → Rel k x y
  sound = AE.sound ∘ sound′

open Failure public
