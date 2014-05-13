#lang racket

; Based off the amb tutorial: http://docs.racket-lang.org/redex/tutorial.html?q=define-language

(require redex)

(define-language amb
  (e (e e)
     (λ (x t) e)
     x
     (amb e ...)
     number
     (+ e ...)
     (if0 e e e)
     (fix e))
  (t (→ t t) num)
  (x variable-not-otherwise-mentioned))

(define-extend-language amb+Γ amb
  (Γ · (x : t Γ)))


