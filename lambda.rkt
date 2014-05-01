#lang racket

(require redex)

(define-language λv
  (e (e e ...) x v)
  (v (λ (x ...) e))
  (x (variable-except λ)))
