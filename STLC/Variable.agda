module STLC.Variable where

open import Data.Nat.Base
import Data.Nat.Properties as Nat
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality.Core

Var : Set
Var = ℕ

_≟_ : Decidable {A = Var} _≡_
_≟_ = Nat._≟_
