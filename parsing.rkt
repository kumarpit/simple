#lang plai

(print-only-errors #t)
(require "simple.rkt")


;; This file defines the parser for the Simple language

;; Simple-focused-sexp (SFS) is one of:
;; - ,identifier
;; - { λ {,identifier} ,SFS }
;; - { ,SFS ,SFS }
;; - true
;; - false
;; - { if ,SFS ,SFS ,SFS }
;; - "any other s-expression"
;; where identifier is any symbol except λ

#;
(define (fn-for-sfs sexp)
  (match sexp
    [`,i #:when (identifier? i) (... i)]
    [`true (...)]
    [`false (...)]
    [`{ if ,p ,c ,a } (... (fn-for-sfs p)
                           (fn-for-sfs c)
                           (fn-for-sfs a))]
    [`{ λ { ,i } ,sfs } (... i
                             (fn-for-sfs sfs))]
    [`{ ,sexp1 ,sexp2 } (... (fn-for-sfs sexp1)
                             (fn-for-sfs sexp2))]
    [otherwise (...)]))

;; SFS -> Simple
;; produce Simple corresponding to the given SFS expression
;; EFFECT: signals an error if no representation possible
(define (parse/simple sexp)
  (match sexp
    [`true (bool #t)]
    [`false (bool #f)]
    [`,i #:when (identifier? i) (var i)]
    [`{ if ,p ,c ,a } (_if (parse/simple p)
                           (parse/simple c)
                           (parse/simple a))]
    [`{ λ {,i} ,sfs } (fun i
                           (parse/simple sfs))]
    [`{ ,sexp1 ,sexp2 } (app (parse/simple sexp1)
                             (parse/simple sexp2))]
    [otherwise (error 'parse/simple "bad simple: ~a" sexp)]))

(test (parse/simple `{λ {x} x})
      (fun 'x (var 'x)))
(test (parse/simple `{λ {F} {λ {x} (F x)}})
      (fun 'F (fun 'x (app (var 'F) (var 'x)))))
;; fixed-point combinator
(test (parse/simple `((λ (f) ((λ (x) (f (x x))) (λ (x) (f (x x))))) (λ (x) x)))
      (app (fun 'f (app (fun 'x (app (var 'f) (app (var 'x) (var 'x))))
                        (fun 'x (app (var 'f) (app (var 'x) (var 'x))))))
           (fun 'x (var 'x))))
(test (parse/simple `true) (bool #t))
(test (parse/simple `false) (bool #f))
(test (parse/simple `{ if true
                          {λ {x} x}
                          {λ {F} {λ {x} (F x)}}})
      (_if (bool #t) (fun 'x (var 'x)) (fun 'F (fun 'x (app (var 'F) (var 'x))))))
(test (parse/simple `{ if ((λ {x} x) true)
                          true
                          false})
      (_if (app (fun 'x (var 'x)) (bool #t)) (bool #t) (bool #f)))

;; the following example is expected to diverge
#;
(test/exn (interp/simple
           (parse/simple `((λ (f) ((λ (x) (f (x x))) (λ (x) (f (x x))))) (λ (x) x)))) "")
