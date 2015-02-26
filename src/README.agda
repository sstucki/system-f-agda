------------------------------------------------------------------------
-- A formalization of the polymorphic lambda calculus extended with
-- iso-recursive types
------------------------------------------------------------------------

-- Author: Sandro Stucki
-- Copyright (c) 2015 EPFL

-- The code in this directory contains an Agda formalization of the
-- Girard-Reynolds polymorphic lambda calculus (System F) extended
-- with iso-recursive types.
--
-- The code makes heavy use of the Agda standard library, which is
-- freely available from
--
--   https://agda.github.io/agda-stdlib


module README where

------------------------------------------------------------------------
-- Module overview

-- The formalization is organized in the following modules.

-- Syntax for terms and types along with support for term/type
-- substitutions.  These modules also contain church/CPS encodings for
-- some other forms, such as existential types or tuples.
open import SystemF.Term
open import SystemF.Type

-- Typing derivations along with substitution/weakening lemmas.
open import SystemF.WtTerm

-- A (functional) call-by-value small-step semantics.  This module
-- also contains a type soundness proof with respect to to said
-- semantics as well as a proof of its equivalence (strong
-- bisimilarity) to the big-step semantics mentioned below.  The type
-- soundness proof uses the common progress & preservation
-- (i.e. subject reduction) structure.
open import SystemF.Reduction

-- Two equivalent versions of a (functional) call-by-value big-step
-- semantics along with corresponding type soundness proofs.  The
-- second version is formulated without the use of productivity
-- checker workarounds.  The latter module also contains an
-- equivalence proof of the two semantics.
open import SystemF.Eval
open import SystemF.Eval.NoWorkarounds

-- Decision procedures for type checking and a uniqueness proof for
-- typing derivations.
open import SystemF.TypeCheck

-- Danielsson's partiality-and-failure monad.  This monad provides the
-- domain in which functional operational semantics are formulated.
open import PartialityAndFailure
