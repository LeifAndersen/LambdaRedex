#lang racket

(require redex)

; Based off of http://redex.racket-lang.org/lam-v.html

(define-language λv
  (e (e e ...) x v)
  (v (λ (x ...) e))
  (E (v ... E e ...) hole)
  (x (variable-except λ)))

(define red
  (reduction-relation
   λv
   (--> (in-hole E ((λ (x ..._1) e) v ..._1))
        (in-hole E (subst-n (x v) ... e))
        "βv")))

(define-metafunction λv
  subst-n : (x any) ... any -> any
  [(subst-n (x_1 any_1) (x_2 any_2) ... any_3)
   (subst x_1 any_1 (subst-n (x_2 any_2) ... any_3))]
  [(subst-n any_3) any_3])

(define-metafunction λv
  subst : x any any -> any
  ; Avoid capture avoiding subst
  [(subst x_1 any_1 (λ (x_2 ... x_1 x_3 ...) any_2))
   (λ (x_2 ... x_1 x_3 ...) any_2)
   (side-condition (not (member (term x_1) (term (x_2 ...)))))]

  ; subst without capture avoiding subst
  [(subst x_1 any_1 (λ (x_2 ...) any_3))
   (λ (x_new ...)
      (subst x_1 any_1
             (sbust-vars (x_2 x_new) ... any_2)))
   (where (x_new ...)
          ,(variables-not-in
            (term (x_1 any_1 any_2))
            (term (x_2 ...))))]
  [(subst x_1 any_1 x_1) any_1]
  [(subst x_1 any_1 x_2) x_2]
  [(subst x_1 any_1 (any_2 ...)) ((subst x_1 any_1 any_2) ...)]
  [(subst x_1 any_1 any_2) any_2])

(define-metafunction λv
  subst-vars : (x any) ... any -> any
  [(subst-vars (x_1 any_1) x_1) any_1]
  [(subst-vars (x_1 any_1) (any_2 ...))
   ((subst-vars (x_1 any_1) any_2) ...)]
  [(subst-vars (x_1 any_1) any_2) any_2]
  [(subst-vars (x_1 any_1) (x_2 any_2) ... any_3)
   (subst-vars (x_1 any_1) (subst-vars (x_2 any_2) ... any_3))]
  [(subst-vars any) any])
