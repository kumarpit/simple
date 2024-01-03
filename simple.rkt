#lang plai

(require "env.rkt")
(print-only-errors #t)

;; Simple - an implementation of the Simply-typed Lambda Calculus

;; This file defines the interpreter for the Simple language

;; Identifier is Symbol
;; INVARIANT: cannot be equal to any Simple keyword
;; interp. variable name in Simple
(define (identifier? s)
  (and (symbol? s)
       (not (equal? s "λ"))))

(define ID1 'F)
(define ID2 'x)

;; No template, atmoic data

(define-type Simple
  [var (v identifier?)]
  [fun (i identifier?) (body Simple?)]
  [app (ratr Simple?) (rand Simple?)])

;; interp. expressions in the Simple language
;; Its syntax is defined by the following BNF:
;; <Simple> ::=
;; (IDENTIFIERS)
;;          <id>
;; (FUNCTIONS
;;        | {λ {<id>} <Simple>}  --> these are the only canonicals in Simple
;;        | {<Simple> <Simple>}

#;
(define (fn-for-simple s)
  (type-case Simple s
    [var (v) (... v)]
    [fun (i body) (... i
                       (fn-for-simple body))]
    [app (rator rand) (... (fn-for-simple rator)
                           (fn-for-simple rand))]))
    

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpretation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type Value
  [funV (param symbol?) (body Simple?)])
;; interp. Simple runtime value

;; We restrict Simple to **closed** expressions so we don't need to
;; worry about variable capture

;; Simple -> Boolean
;; produces true if every identifier reference in Simple is bound,
;; otherwise false
(define (closed-simple? s)
  ;; Accumulator: bounds is listof Symbol
  ;; Invariant: list of identifiers bound in the surrounding context
  (local [;; Simple (listof Symbol) -> Boolean
          (define (closed-simple?--bounds s bounds)
            (type-case Simple s
              [var (v) (if (member v bounds) #t #f)]
              [fun (i body) (closed-simple?--bounds body (cons i bounds))]
              [app (rator rand) (and (closed-simple?--bounds rator bounds)
                                     (closed-simple?--bounds rand bounds))]))]
    (closed-simple?--bounds s empty)))

(test (closed-simple? (fun 'x (var 'x))) #t)
(test (closed-simple? (fun 'F (fun 'x (app (var 'F) (var 'x))))) #t)
(test (closed-simple? (app (fun 'x (var 'x)) (var 'y))) #f)

;; Simple -> Value
;; consumes a Simple program and produces the corresponding Value
(define (interp/simple s)
  (local [(define (interp/simple-env s env)
            (type-case Simple s
              [var (v) (lookup-env env v)]  ;; guranteed to exist
              [fun (i body) (funV i body)]   ;; already a value
              [app (rator rand) (let ([ratorv (interp/simple-env rator env)]
                                      [randv (interp/simple-env rand env)])
                                  (interp/simple-env (funV-body ratorv)
                                                     (extend-env
                                                      env
                                                      (funV-param ratorv)
                                                      randv)))]))]
    (begin
      (unless (closed-simple? s)
        (error 'interp/simple "not a valid Simple expression: ~a" s))
      (interp/simple-env s empty-env))))

(test (interp/simple (fun 'x (var 'x))) (funV 'x (var 'x)))
(test (interp/simple (app (fun 'x (var 'x)) (fun 'x (var 'x))))
      (funV 'x (var 'x)))