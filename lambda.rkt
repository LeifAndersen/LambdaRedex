#lang racket

(require redex)
(require redex/tut-subst)
(require pict)

; Based off of http://redex.racket-lang.org/lam-v.html

(define-language λv
  (e (e e ...)
     (if e e e)
     (if0 e e e)
     lam x v)
  (lam (λ (x ...) e) + * =)
  (v number boolean)
  (x variable-not-otherwise-mentioned))

(define-extended-language λesk λv
  (E (v ... E e ...)
     (if E e e)
     (if0 E e e)
     hole)
  (v .... closure)
  (closure (clo e ρ))
  (addr v)
  (state (ς E ρ σ κ))
  (ρ ((x addr) ...))
  (σ ((addr val) ...))
  (κ (letk x e ρ κ)
      halt))

(define red
  (reduction-relation
   λesk
   (--> e
        (ς e () () halt)
        "inject"
        (side-condition (not (v? (term e)))))
   (--> (ς v ρ σ halt)
        v
        "halt")
   (--> (ς (in-hole E x) ρ σ κ)
        (ς (in-hole E (ρσ-lookup ρ σ x)) ρ σ κ)
        "lookup"
        (side-condition (term (in-ρ ρ x))))
   (--> (ς (in-hole E ((clo (λ (x ..._1) e) ρ_1) v ..._1)) ρ_2 σ κ)
        (ς (in-hole E (subst (x v) ... e)) ρ_2 σ κ)
        "βv")
   (--> (ς (in-hole E (λ (x ...) e)) ρ σ κ)
        (ς (in-hole E (clo (λ (x ...) e) ρ)) ρ σ κ))
   (==> (+ number ...)
        (Σ number ...)
        "+")
   (==> (* number ...)
        (Π number ...)
        "*")
   (==> (= number_1 number_2)
        (== number_1 number_2)
        "=")
   (==> (if0 0 e_1 e_2)
        e_1
        "if0t")
   (==> (if0 v e_1 e_2)
        e_2
        "if0f"
        (side-condition (term (different v 0))))
   (==> (if #t e_1 e_2)
        e_1
        "ift")
   (==> (if #f e_1 e_2)
        e_2
        "iff")

   ; Preventing Invalid programs
   (--> (ς (in-hole E x) ρ σ κ)
        (ς (in-hole E (ρσ-lookup ρ σ x)) ρ σ κ)
        "lookup-fell"
        (side-condition (not (term (in-ρ ρ x)))))

   with
   [(--> (ς (in-hole E a) ρ σ κ)
         (ς (in-hole E b) ρ σ κ))
    (==> a b)]))

(define-metafunction λesk
  [(different v_1 v_1) #f]
  [(different v_1 v_2) #t])

(define-metafunction λesk
  Σ : number ... -> number
  [(Σ number ...) ,(apply + (term (number ...)))])

(define-metafunction λesk
  Π : number ... -> number
  [(Π number ...) ,(apply * (term (number ...)))])

(define-metafunction λesk
  == : number number -> boolean
  [(== number_1 number_2) ,(= (term number_1) (term number_2))])

(define-metafunction λesk
  [(in-ρ ρ x) ,(not (equal? #f (assq (term x) (term ρ))))])

(define-metafunction λesk
  ρ-lookup : ρ x -> addr
  [(ρ-lookup ρ x) ,(second (assq (term x) (term ρ)))])

(define-metafunction λesk
  ρ-extend : ρ x addr -> ρ
  [(ρ-extend ρ x addr) (term ,(cons (cons (term x) (term addr)) (term ρ)))])

(define-metafunction λesk
  σ-lookup : σ addr -> v
  [(σ-lookup σ addr) ,(second (assq (term addr) (term σ)))])

(define-metafunction λesk
  σ-extend : σ addr v -> σ
  [(σ-extend σ addr v) (term ,(cons (cons (term x) (term addr)) (term ρ)))])

(define-metafunction λesk
  ρσ-lookup : ρ σ x -> v
  [(ρσ-lookup ρ σ x) (σ-lookup σ (ρ-lookup ρ x))])

(define-metafunction λesk
  alloc : v -> addr
  [(alloc v) v])

(define-metafunction λesk
  apply-κ : κ v σ -> state
  [(apply-κ halt v σ)
   (ς v () ())]
  [(apply-κ (letk x e ρ) v σ)
   (ς e (ρ-extend ρ x a) (σ-extend σ a v))
   (where a (alloc v))])

(define-metafunction λesk
  subst : (x v) ... e -> e
  [(subst (x v) ... e)
   ,(subst/proc x?
                (term (x ...))
                (term (v ...))
                (term e))])

(define κ? (redex-match λesk κ))

(define x? (redex-match λesk x))

(define v? (redex-match λesk v))

(define (single-step? e)
  (or (= (length (apply-reduction-relation red e))
         1)
      (let ([step (apply-reduction-relation red e)])
        (ormap (λ (x) (equal? (term error)
                              (car x)))
                step))))

(define (progress-holds? e)
  (or (v? e) (reduces? e)))

(define (reduces? e)
  (not (null? (apply-reduction-relation red (term (,e))))))

(define (test-suite)
  (test-->> red #:cycles-ok
            (term ((λ (n) (n n)) (λ (n) (n n)))))
  (test-->> red #:cycles-ok
            (term ((λ (n) (if0 n 1 ((λ (x) (x x)) (λ (x) (x x))))) (+ 2 2))))
  (test-->> red
            (term ((λ (x) (x x)) (λ (x) x)))
            (term (clo (λ (x) x) ())))
  (test-->> red
            (term ((λ (x) (if (= x 0) 5 9)) 0))
            (term 5))
  (test-->> red
            (term (if (= 0 0) 5 9))
            (term 5))
  (test-->> red
            (term ((λ (x y) (+ x y)) 3 4))
            (term 7))

  (redex-check λesk e (or (v? (term e))
                          (single-step? (term e))))

  (test-results))

(test-suite)
