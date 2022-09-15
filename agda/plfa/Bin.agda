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
from (⟨⟩ O) = 0
from (b O) = (from b) + (from b)
from (b I) = (from b) + (from b) + 1

-- I don't understand why I need these to be separate definitions if they all just use refl

back-bin : ∀ ( b : Bin ) → (from b) + (from b) ≡ from (b O)
back-bin ⟨⟩ = refl                   
back-bin (b O) = refl
back-bin (b I) = refl 

help-from-inc : ∀ ( b : Bin) → from ((inc b) O) ≡ from (inc b) + from (inc b)
help-from-inc ⟨⟩ = refl         
help-from-inc (b O) = refl
help-from-inc (b I) = refl

{-
  I would like to use the ring solver directly, but it seems to require free variables
  It would be nice to have a way for instance to pass (from b) that evaluates to a Nat
  This was helpful: https://gist.github.com/andrejbauer/358722620c26c09d6be218bcd95ee654
-}
  
+-succ-succ : ∀ (m n : ℕ) → suc m + suc n ≡ suc(m + n + 1)
+-succ-succ = solve-∀

inc-eq-suc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
inc-eq-suc ⟨⟩ = refl
inc-eq-suc (b O) = 
    begin
        from (inc (b O))         ≡⟨⟩
        from b + from b     + 1  ≡⟨ cong (_+ 1) (back-bin b) ⟩
            from (b O)      + 1  ≡⟨ +-suc _ zero ⟩
        suc(from (b O)      + 0) ≡⟨ cong suc (+-identityʳ (_)) ⟩ 
        suc(from (b O))
    ∎
inc-eq-suc (b I) =
    begin
        from (inc (b I))            ≡⟨⟩
        from ((inc b) O)            ≡⟨ help-from-inc b ⟩
        from (inc b) + from (inc b) ≡⟨ cong (_+ from (inc b)) (inc-eq-suc b) ⟩
        suc (from b) + from (inc b) ≡⟨ cong (suc (from b) +_) (inc-eq-suc b) ⟩
        suc (from b) + suc (from b) ≡⟨ +-succ-succ _ _ ⟩
        suc (from b + from b + 1)
    ∎    

from-to : ∀ (n : ℕ) → from (to n) ≡ n
from-to zero = refl    
from-to (suc n) = 
  begin
    from (to (suc n))  ≡⟨⟩
    from (inc (to n))  ≡⟨ inc-eq-suc (     to n) ⟩
    suc (from (to n))  ≡⟨ cong   suc (from-to n) ⟩
    suc n
  ∎     