module Bin where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-comm; ≤-refl; +-mono-≤)
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

+1-eq-suc` : ∀ (n : ℕ) → n + 1 ≡ suc(n)
+1-eq-suc` = solve-∀

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

data One : Bin → Set where
  b1 :
    One (⟨⟩ I)
  _I : ∀ {b : Bin}
    → One b 
    → One (b I)
  _O : ∀ {b : Bin}
    → One b 
    → One (b O)

one-inc : ∀{b : Bin} → One b → One (inc b)
one-inc b1 = b1 O
one-inc (x O) = x I
one-inc (x I) = (one-inc x) O

1-≤-one : ∀ {b : Bin} → One b → 1 ≤ (from b) 
1-≤-one b1 = ≤-refl {1} -- the same as s≤s z≤n
1-≤-one {b O} (x O) = +-mono-≤ (1-≤-one {b} x) (z≤n {from b})
1-≤-one {b I} (x I) = +-mono-≤ (z≤n {from b + from b}) (s≤s z≤n)

data Can : Bin → Set where
  c0 :
    Can (⟨⟩ O)
  cl : ∀{b : Bin}
    → One b
    → Can b

can-inc : ∀{b : Bin} → Can b → Can (inc b)
can-inc c0 = cl b1
can-inc (cl x) = cl (one-inc x) 

to-can : ∀(n : ℕ) → Can (to n)
to-can zero    = c0
to-can (suc n) = can-inc (to-can n)

to-suc : ∀(n : ℕ) → to(n + 1) ≡ inc(to n) 
to-suc zero = refl
to-suc (suc n) = 
  begin
    inc(to (n + 1)) ≡⟨ cong inc (cong to (+1-eq-suc` n)) ⟩
    inc(to (suc n)) ≡⟨⟩
    inc(inc (to n))
  ∎

{-
  This took me some time to figure out, I had some confusion at first with the way Agda unwraps definitions
  The crucial piece is (s≤s (z≤n {n})), allowing recursion to the {suc n} case
-}

can-shift : ∀ {n : ℕ} → 1 ≤ n → to(n + n) ≡ (to n) O
can-shift {suc zero} (s≤s x) = refl
can-shift {suc(suc n)} x = 
  begin
    inc(to (suc n + suc(suc n)))   ≡⟨ cong inc (cong to (+-comm (suc n) (suc (suc n)))) ⟩
    inc (inc (to (suc n + suc n))) ≡⟨ cong inc (cong inc (can-shift {suc n} (s≤s (z≤n {n})))) ⟩ 
    to (suc (suc n)) O
  ∎

can-to-from : ∀{b : Bin} → Can b → to (from b) ≡ b
can-to-from c0 = refl
can-to-from (cl b1) = refl
can-to-from (cl {b O} (x O))
  rewrite 
      can-shift (1-≤-one x)
    | can-to-from (cl x)
    = refl
can-to-from (cl {b I} (x I))
  rewrite
      to-suc (from b + from b)
    | can-shift (1-≤-one x)
    | can-to-from (cl x)
    = refl  

open import plfa.part1.Isomorphism using (_≲_; _≃_)

ℕ≲Bin : ℕ ≲ Bin
ℕ≲Bin = record
  { to = to
  ; from = from
  ; from∘to = from-to
  }

{-
  These first two proofs are interesting. They show that for any b : Bin, there is only one proof that b
  has a leading one or is cannonical. This is explicit in constructing that proof. 
-}

≡One : ∀ {b : Bin} (o o′ : One b) → o ≡ o′
≡One b1 b1        = refl
≡One (o I) (o′ I) = cong _I (≡One o o′)
≡One (o O) (o′ O) = cong _O (≡One o o′)

{-
  Note that the below can be shorter by using the case:
    ≡Can (cl o) (cl o′) = cong cl (≡One o o′)
  
  I thought it more instructive to show that this was also exhaustive. 
  Interestingly, this eliminates one absurd pattern
-}

≡Can : ∀ {b : Bin} (cb cb′ : Can b) → cb ≡ cb′
≡Can c0 (cl (() O)) -- absurd pattern, as ≡Can c0 (cl x) gives a goal of c0 ≡ cl One(⟨⟩ O) 
≡Can c0 c0 = refl
≡Can (cl b1) (cl b1) = refl
≡Can (cl (cb O)) (cl (cb` O)) = cong cl (≡One (cb O) (cb` O))
≡Can (cl (cb I)) (cl (cb` I)) = cong cl (≡One (cb I) (cb` I))

open import Data.Product using (proj₁; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)

{-
  Intuitively, this is saying that if I have two binary numbers that are equivalent:
    b  : ⟨⟩ I O I
    b′ : ⟨⟩ I O I

  then their sum types are equivalent:

    cb  : ⟨ ⟨⟩ I O I , Can(One(⟨⟩ I O I))⟩ 
    cb′ : ⟨ ⟨⟩ I O I , Can(One(⟨⟩ I O I))⟩

    Note that if we said this about proj₂, this would be false:

    cb  : ⟨ ⟨⟩       I O I , Can(One(⟨⟩ I O I))⟩ 
    cb′ : ⟨ ⟨⟩ O O O I O I , Can(One(⟨⟩ I O I))⟩

-}

proj₁≡→Can≡ : {cb cb′ : ∃[ b ] Can b} → proj₁ cb ≡ proj₁ cb′ → cb ≡ cb′
proj₁≡→Can≡ {⟨ b , cb ⟩} {⟨ b , cb′ ⟩} refl = cong (λ{ x → ⟨ b , x ⟩ }) (≡Can cb cb′)

{-
  It is interesting how this isomorphism feels different from others, because it forces us to confront
  the existential as its own type, not just syntax. 

  The type ∃[ b ] (Can b) is restricting Bin to exclude non-unique binary numbers introduced by 
  leading zeroes, as described by Can.
 
  The type of Can here is crucial, in that its constructors are applied to (b : Bin) to "refine" it.

  The existential's inhabitants are those where both (b: Bin) and (Can b) can (depending on definition) 
  be placed into a record type where Can b is constructed from b using proj₁ or satisfy:
     
        (b : Bin) → (Can : Bin → Set) b →  ∑ Bin Can
                                        →  Σ[ b ∈ Bin ] Can
                                        →  ∃[ b ] Can

  The last syntax is most familiar at first, but once I really think of this in terms of types, the former seem more intuitive! 
  
  It's important to note how to was written such that it always "picks" the cannonical binary, as evidenced by (to-can b).

  When we go the other way around, there is only one Nat we could pick i.e. it's a "smaller", non-sum type with ℕ≲Bin

  For from∘to, we don't need this extra information from the sum type, as this is really true for all Bin and we 
  would "drop" this information in the middle:

      Nat → ⟨ Bin , Can b ⟩ → Nat 

  However with to∘from we use proj₂ for the evidence that we are starting and ending with a cannonical binary:

    ⟨ Bin , Can b ⟩ → Nat → ⟨ Bin , Can b ⟩      
-}

ℕ≃∃Can : ℕ ≃ (∃[ b ] (Can b))
ℕ≃∃Can = record
  { to      = λ{ n → ⟨ to n , to-can n ⟩ }
  ; from    = λ{ ⟨ b , cb ⟩ → from b }
  ; from∘to = from-to
  ; to∘from = λ{ ⟨ b , cb ⟩ → proj₁≡→Can≡ (can-to-from cb) }
  }