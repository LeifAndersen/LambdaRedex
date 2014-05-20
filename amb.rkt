#lang racket

; Based off the amb tutorial: http://docs.racket-lang.org/redex/tutorial.html?q=define-language

(require redex)
(require redex/tut-subst)
(require pict)

(define-language amb
  (e (e e ...)
     (λ (x t) e)
     (λ ((x t) ...) e)
     x
     (amb e ...)
     number
     (+ e ...)
     (if0 e e e)
     (fix e))
  (t (→ t ... t) num)
  (x variable-not-otherwise-mentioned))

(define-extended-language amb+Γ amb
  (Γ · (x : t Γ)))

(define-judgment-form
  amb+Γ
  #:mode (types I I O)
  #:contract (types Γ e t)
  [(types Γ e_1 (→ t_2 t_3))
   (types Γ e_2 t_2)
   -------------------------
   (types Γ (e_1 e_2) t_3)]

  [(types (x : t_1 Γ) e t_2)
   -----------------------------------
   (types Γ (λ (x t_1) e) (→ t_1 t_2))]

  [(types (build-Γ (x t_1) ... Γ_1) e t_2)
   -----------------------------------
   (types Γ_1 (λ ((x t_1) ...) e) (→ t_1 ... t_2))]

  [(types Γ e (→ (→ t_1 t_2) (→ t_1 t_2)))
   ---------------------------------------
   (types Γ (fix e) (→ t_1 t_2))]

  [---------------------
   (types (x : t Γ) x t)]

  [(types Γ x_1 t_1)
   (side-condition (different x_1 x_2))
   ------------------------------------
   (types (x_2 : t_2 Γ) x_1 t_1)]

  [(types Γ e num) ...
   -----------------------
   (types Γ (+ e ...) num)]

  [--------------------
   (types Γ number num)]

  [(types Γ e_1 num)
   (types Γ e_2 t)
   (types Γ e_3 t)
   -----------------------------
   (types Γ (if0 e_1 e_2 e_3) t)]

  [(types Γ e t_1) ...
   (side-condition (same-n t_1 ...))
   (where t_2 ,(car (term (t_1 ...))))
   -----------------------------------
   (types Γ (amb e ...) t_2)])

(define-metafunction amb+Γ
  [(different x_1 x_1) #f]
  [(different x_1 x_2) #t])

(define-metafunction amb+Γ
  [(out Γ) ,(write (term Γ))])

(define-metafunction amb+Γ
  build-Γ : (x t) ... Γ -> Γ
  [(build-Γ (x_1 t_1) (x_2 t_2) ... Γ)
   (build-Γ (x_2 t_2) ... (x_1 : t_1 Γ))]
  [(build-Γ Γ) Γ])

(define-metafunction amb+Γ
  [(same-n t_1 t_1 t_3 ...) (same-n t_1 t_3 ...)]
  [(same-n t_1)             #t]
  [(same-n)                 #t]
  [(same-n t_1 t_2 ...)     #f])

(define-extended-language Ev amb+Γ
  (p (e ...))
  (P (e ... E e ...))
  (E (v E)
     (E e)
     (+ v ... E e ...)
     (if0 E e e)
     (fix E)
     hole)
  (v (λ (x t) e)
     (λ ((x t) ...) e)
     (fix v)
     number))

(define-metafunction Ev
  Σ : number ... -> number
  [(Σ number ...) ,(apply + (term (number ...)))])

(define-metafunction Ev
  subst : (x v) ... e -> e
  [(subst (x v) ... e)
   ,(subst/proc x?
                (term (x ...))
                (term (v ...))
                (term e))])

(define x? (redex-match Ev x))

(define red
  (reduction-relation
   Ev
   #:domain p
   (--> (in-hole P (if0 0 e_1 e_2))
        (in-hole P e_1)
        "if0t")
   (--> (in-hole P (if0 v e_1 e_2))
        (in-hole P e_2)
        (side-condition (not (equal? 0 (term v))))
        "if0f")
   (--> (in-hole P ((fix (λ (x t) e)) v))
        (in-hole P (((λ (x t) e) (fix (λ (x t) e))) v))
        "fix")
   (--> (in-hole P ((λ (x t) e) v))
        (in-hole P (subst (x v) e))
        "βvs")
   (--> (in-hole P ((λ ((x t) ..._1) e) v ..._1))
        (in-hole P (subst (x v) ... e))
        "βv")
   (--> (in-hole P (+ number ...))
        (in-hole P (Σ number ...))
        "+")
   (--> (e_1 ... (in-hole E (amb e_2 ...)) e_3 ...)
        (e_1 ... (in-hole E e_2) ... e_3 ...)
        "amb")))

(define (trace-amb+)
         (traces red
                 (term ((+ (amb 1 2)
                           (amb 10 20))))))

(define (trace-ambfix)
  (traces red
          (term (((fix (λ (f (→ num num))
                          (λ (n num) (if0 n
                                          0
                                          (amb n (f (+ n -1)))))))
                  10)))))

(define (trace-multiarg)
  (traces red (term (((λ ((x num) (y num)) (+ x y)) 3 4)))))

(define (trace-singlearg)
  (traces red (term (((λ ((x num)) (+ x 3)) 3)))))

(define (trace-noarg)
  (traces red (term ((+ 3 ((λ () 4)))))))

