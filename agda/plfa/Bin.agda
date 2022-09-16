module Bin where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Nat.Tactic.RingSolver

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc (b O) = b I
inc (b I) = (inc b) O
inc ⟨⟩ = ⟨⟩ I

to : ℕ → Bin
to 0 = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0
from (b O) = (from b) + (from b)
from (b I) = (from b) + (from b) + 1

{-
  I would like to use the ring solver directly, but it seems to require free variables
  It would be nice to have a way for instance to pass (from b) that evaluates to a Nat
  This was helpful: https://gist.github.com/andrejbauer/358722620c26c09d6be218bcd95ee654
-}
  
+-succ-succ : ∀ (m n : ℕ) → suc m + suc n ≡ suc(m + n + 1)
+-succ-succ = solve-∀

+1-eq-suc : ∀ (m n : ℕ) → m + n + 1 ≡ suc(m + n)
+1-eq-suc = solve-∀

inc-eq-suc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
inc-eq-suc ⟨⟩ = refl 
inc-eq-suc (b O) 
  rewrite 
    +1-eq-suc (from b) (from b) 
    = refl
inc-eq-suc (b I)
  rewrite 
      inc-eq-suc b 
    | +-succ-succ (from b) (from b) 
    = refl

from-to : ∀ (n : ℕ) → from (to n) ≡ n
from-to zero = refl    
from-to (suc n) 
  rewrite 
      inc-eq-suc (to n) 
    | from-to n 
  = refl