#lang racket

(require redex)
(require redex/tut-subst)

; Based off of http://redex.racket-lang.org/lam-v.html

(define-language λv
  (e (e e ...) (if e e e) (if0 e e e) x v)
  (v (λ (x ...) e) number + * = boolean)
  (E (v ... E e ...) (if E e e) (if0 E e e) hole)
  (x variable-not-otherwise-mentioned))

;(define-extend-langauge λenv
;  (a number)
;  (ρ · (x : a))
;  (σ · (a : v)))

(define red
  (reduction-relation
   λv
   (--> (in-hole E (+ number_1 ...))
        (in-hole E ,(apply + (term (number_1 ...))))
        "+")
   (--> (in-hole E (* number_1 ...))
        (in-hole E ,(apply * (term (number_1 ...))))
        "*")
   (--> (in-hole E (= number_1 number_2))
        (in-hole E ,(= (term number_1) (term number_2)))
        "=")
   (--> (in-hole E (if0 0 e_1 e_2))
        (in-hole E e_1)
        "if0t")
   (--> (in-hole E (if0 number_1 e_1 e_2))
        (in-hole E e_2)
        "if0f"
        (side-condition (not (= 0 (term number_1)))))
   (--> (in-hole E (if #t e_1 e_2))
        (in-hole E e_1)
        "ift")
   (--> (in-hole E (if #f e_1 e_2))
        (in-hole E e_2)
        "iff")
   (--> (in-hole E (if e_1 e_2 e_3))
        (in-hole E (if #t e_2 e_3))
        (side-condition (not (boolean? (term e_1)))))
   (--> (in-hole E ((λ (x ..._1) e) v ..._1))
        (in-hole E (subst (x v) ... e))
        "βv")

   ; Preventing Invalid programs
   (--> (in-hole E x)
        (error "free var"))
   (--> (in-hole E (number any_1 ...))
        (error "invalid application"))
   (--> (in-hole E (boolean any_1 ...))
        (error "invalid application"))
   (--> (in-hole E (if0 any_1 any_2 any_3))
        (error "invalid use of if0")
        (side-condition (not (number? (term any_1)))))
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

(define x? (redex-match λv x))

(define-metafunction λv
  subst : (x v) ... e -> e
  [(subst (x v) ... e)
   ,(subst/proc x?
                (term (x ...))
                (term (v ...))
                (term e))])


(define value? (redex-match λv v))

(define (single-step? e)
  (or (= (length (apply-reduction-relation red e))
         1)
      (let ([step (apply-reduction-relation red e)])
        (ormap (λ (x) (equal? (term error)
                              (car x)))
                step))))

(define (progress-holds? e)
  (or (v? e) (reduces? e)))

(define v? (redex-match λv v))

(define (reduces? e)
  (not (null? (apply-reduction-relation red (term (,e))))))

(test-->> red #:cycles-ok
          (term ((λ (n) (n n)) (λ (n)  (n n)))))
(test-->> red #:cycles-ok
          (term ((λ (n) (if0 n 1 ((λ (x) (x x)) (λ (x) (x x))))) (+ 2 2))))
(test-->> red
          (term ((λ (x) (if (= x 0) 5 9)) 0))
          (term 5))
(test-->> red
          (term (if (= 0 0) 5 9))
          (term 5))

(redex-check λv e (or (value? (term e))
                      (single-step? (term e))))

(test-results)
