#lang pie

; definition of addition

(claim +
  (→ Nat Nat
    Nat))

(define +
  (λ(a b)
    (iter-Nat a
      b
      (λ(x)
        (add1 x)))))

; ∀a, a+0=a
; note the order matters here

(claim add_zero
  (Π((a Nat))
    (= Nat a (+ a 0))))

(define add_zero
  (λ(a)
    (ind-Nat a
      (λ(x) (= Nat x (+ x 0))) ; This is the motive, the type for each step of induction. Note how it "abstracts" the Π type
      (same 0)                 ; base case
      (λ(n-1 prev)             ; increment the "from" and "to" of the equality `prev` from the previous induction step
        (cong prev (+ 1))))))


; from Chapter 9
; ∀a,b → 1+(a+b) = a+(1+b)
; note the carful order of variables in some places

(claim add1+=+add1
  (Π((a Nat)
     (b Nat))
    (= Nat
       (add1 (+ a b))
       (+ a (add1 b)))))

(claim mot-add1+=+add1
  (→ Nat Nat U))

(define mot-add1+=+add1
  (λ(b a)
    (= Nat
      (add1 (+ a b))
      (+ a (add1 b)))))

(claim step-add1+=+add1
  (Π((a Nat)(n-1 Nat))
    (→ (mot-add1+=+add1 a       n-1)
       (mot-add1+=+add1 a (add1 n-1)))))

(define step-add1+=+add1
  (λ(a n-1 prev)
    (cong prev (+ 1))))

(define add1+=+add1
  (λ(a b)
    (ind-Nat a
      (mot-add1+=+add1 b)
      (same (add1 b))
      (step-add1+=+add1 b))))

; ∀a,b → a+b=b+a
; did this all by myself!

(claim add_comm
  (Π((a Nat)
     (b Nat))
    (= Nat
       (+ a b)
       (+ b a))))

(define add_comm
  (λ(a b)
    (ind-Nat b
      (λ(x)
        (= Nat
          (+ a x)
          (+ x a)))
      (replace       ; here the base case a=a is replaced with a+0=a
        (add_zero a)
        (λ(x)
          (= Nat x a))
        (same a))
      (λ(n-1 prev)   ; for the step, we note that using cong gets us close to our goal
        (replace     ; to move an add1 up, we replace that piece using add1+=+add1
          (add1+=+add1 a n-1)
          (λ(x)
            (= Nat x (add1 (+ n-1 a))))
          (cong prev (+ 1)))))))