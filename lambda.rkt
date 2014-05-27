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
  (v .... lam closure)
  (closure (clo e ρ))
  (addr number)
  (state (ς E ρ σ))
  (ρ ((x addr) ...))
  (σ ((addr val) ...)))

(define red
  (reduction-relation
   λesk
   (--> e
        (ς e () ())
        "inject"
        (side-condition (not (v? (term e)))))
   (--> (ς v ρ σ)
        v
        "halt")
   (--> (ς (in-hole E x) ρ σ)
        (ς (in-hole E (ρσ-lookup ρ σ x)) ρ σ)
        "lookup"
        (side-condition (term (in-ρ ρ x))))
   (--> (ς (in-hole E (+ number ...)) ρ σ)
        (ς (in-hole E (Σ number ...)) ρ σ)
        "+")
   (--> (ς (in-hole E (* number ...)) ρ σ)
        (ς (in-hole E (Π number ...)) ρ σ)
        "*")
   (--> (ς (in-hole E (= number_1 number_2)) ρ σ)
        (ς (in-hole E (== number_1 number_2)) ρ σ)
        "=")
   (--> (ς (in-hole E (if0 0 e_1 e_2)) ρ σ)
        (ς (in-hole E e_1) ρ σ)
        "if0t")
   (--> (ς (in-hole E (if0 v e_1 e_2)) ρ σ)
        (ς (in-hole E e_2) ρ σ)
        "if0f"
        (side-condition (term (different v 0))))
   (--> (ς (in-hole E (if #t e_1 e_2)) ρ σ)
        (ς (in-hole E e_1) ρ σ)
        "ift")
   (--> (ς (in-hole E (if #f e_1 e_2)) ρ σ)
        (ς (in-hole E e_2) ρ σ)
        "iff")
   (--> (ς (in-hole E ((λ (x ..._1) e) v ..._1)) ρ σ)
        (ς (in-hole E (subst (x v) ... e)) ρ σ)
        "βv")

   ; Preventing Invalid programs
   (--> (ς (in-hole E x) ρ σ)
        (ς (in-hole E (ρσ-lookup ρ σ x)) ρ σ)
        "lookup-fil"
        (side-condition (not (term (in-ρ ρ x)))))
   (--> (in-hole E (number any_1 ...))
        (error "invalid application"))
   (--> (in-hole E (boolean any_1 ...))
        (error "invalid application"))
   (--> (in-hole E (if any_1 any_2 any_3))
        (error "invalid use of if")
        (side-condition (and (not (boolean? (term any_1)))
                             (not (reduces? (term any_1))))))
   (--> (in-hole E (+ any_1 ...))
        (error "invalid use of +")
        (side-condition (not (andmap (λ (x) (number? x)) (term (any_1 ...))))))
   (--> (in-hole E (* any_1 ...))
        (error "invalid use of *")
        (side-condition (not (andmap (λ (x) (number? x)) (term (any_1 ...))))))
   (--> (in-hole E (= any_1 ...))
        (error "invalid use of =")
        (side-condition (not (and (andmap (λ (x) (number? x)) (term (any_1 ...)))
                                 (= 2 (length (term (any_1 ...))))))))
   (--> (in-hole E ((λ (x ...) e) v ...))
        (error "argument count mismatch")
        (side-condition (not (= (length (term (x ...)))
                                (length (term (v ...)))))))
   ))

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
  σ-lookup : σ addr -> v
  [(σ-lookup σ addr) ,(second (assq (term addr) (term σ)))])

(define-metafunction λesk
  ρσ-lookup : ρ σ x -> v
  [(ρσ-lookup ρ σ x) (σ-lookup σ (ρ-lookup ρ x))])

(define-metafunction λesk
  subst : (x v) ... e -> e
  [(subst (x v) ... e)
   ,(subst/proc x?
                (term (x ...))
                (term (v ...))
                (term e))])

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
            (term (λ (x) x)))
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
