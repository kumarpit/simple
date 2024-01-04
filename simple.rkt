#lang plai

(require "env.rkt")
(print-only-errors #t)

;; Simple - an implementation of the Simply-typed Lambda Calculus

;; This file defines the interpreter for the Simple language

;; Identifier is Symbol
;; INVARIANT: cannot be equal to any Simple keyword
;; interp. variable name in Simple
(define (identifier? s)
  (local [(define RESERVED '(λ true false if :))]
    (and (symbol? s)
         (not (memq s RESERVED)))))

(define ID1 'F)
(define ID2 'x)

;; No template, atmoic data

(define-type Simple
  [var (v identifier?)]
  [bool (b boolean?)]
  [sif (pred Simple?) (conseq Simple?) (altern Simple?)]  ;; if is a Racket keyword
  [fun (i identifier?) (body Simple?)]
  [app (ratr Simple?) (rand Simple?)])

;; interp. expressions in the Simple language
;; Its syntax is defined by the following BNF:
;; <Simple> ::=
;; (IDENTIFIERS)
;;          <id>
;; (CONDITIONALS)
;;          <bool>
;;        | {if <Simple> <Simple> <Simple>}
;; (FUNCTIONS
;;        | {λ {<id>} <Simple>}
;;        | {<Simple> <Simple>}
;; where <bool> = true | false
;;   and <id> is any identifier satisfying (identifier?)

#;
(define (fn-for-simple s)
  (type-case Simple s
    [var (v) (... v)]
    [bool (b) (... b)]
    [_if (p c a) (... (fn-for-simple p)
                      (fn-for-simple c)
                      (fn-for-simple a))]
    [fun (i body) (... i
                       (fn-for-simple body))]
    [app (rator rand) (... (fn-for-simple rator)
                           (fn-for-simple rand))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Typing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type Type
  [boolType]
  [funType (domain Type?) (range Type?)])
;; <Type> ::= boolean | <Type> -> <Type>

;; Tenv is (envof Type)
;; interp. The type associated to each identifier in the surrounding context
(define Tenv? (envof? Type?))

(define-type Simple/wt
  ;; [var/wt]
  ;; ----------------------
  ;;    tenv ⊢ v : type
  ;; CHECK: (lookup-env tenv v) = type
  [var/wt (tenv Tenv?) (v identifier?)]

  ;; [bool/wt]
  ;; ----------------------
  ;;   tenv ⊢ b : boolean
  [bool/wt (tenv Tenv?) (b boolean?)]

  ;; [sif/wt]  tenv1 ⊢ p : type1
  ;;           tenv2 ⊢ c : type2  tenv3 ⊢ a : type3
  ;; ------------------------------------------------------------
  ;;          tenv1 ⊢ {if p c a} : type2
  ;; CHECK: tenv1 = tenv2 = tenv3
  ;; CHECK: type1 = boolean
  ;; CHECK: type2 = type3
  [sif/wt (p Simple/wt?) (c Simple/wt?) (a Simple/wt?)]

  ;; [fun/wt]  tenv2 ⊢ body : type1  
  ;; ------------------------------------------------------------
  ;;           tenv1 ⊢ {λ {x : type0} body} : type2
  ;; CHECK: tenv2 = (extend-env tenv1
  ;;                            (list x)
  ;;                            (list type0))
  ;; CHECK: type2 = type0 -> type1
  [fun/wt (i identifier?) (body Simple/wt?)]

  ;; [app/wt]  tenv1 ⊢ rator : type1   tenv2 ⊢ rand : type2
  ;; ------------------------------------------------------------
  ;;           tenv1 ⊢ {rator rand} : type3
  ;; CHECK: tenv1 = tenv2
  ;; CHECK: type1 = type2 -> type3
  [app/wt (rator Simple/wt?) (rand Simple/wt?)])

;; TODO
;; 1) Define selector functions
;; 2) Check derivation tree
;; 3) Add type-checking to the interpreter


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpretation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type Value
  [boolV (b boolean?)]
  [funV (param symbol?) (body Simple?)])
;; interp. Simple runtime values

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
              [bool (b) #t]
              [sif (p c a) (and (closed-simple?--bounds p bounds)
                                (closed-simple?--bounds c bounds)
                                (closed-simple?--bounds a bounds))]
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
              [var (v) (lookup-env env v)]
              [bool (b) (boolV b)]
              [sif (p c a) (let ([pv (interp/simple p)])
                             (type-case Value pv
                               [funV (p body) (error 'interp/simple)]
                               [boolV (b) (if b
                                              (interp/simple c)
                                              (interp/simple a))]))]
              [fun (i body) (funV i body)]
              [app (rator rand) (let ([ratorv (interp/simple-env rator env)]
                                      [randv (interp/simple-env rand env)])
                                  (type-case Value ratorv
                                    [boolV (b) (error 'interp/simple)]
                                    [funV (p body)
                                          (interp/simple-env (funV-body ratorv)
                                                             (extend-env
                                                              env
                                                              (list (funV-param ratorv))
                                                              (list randv)))]))]))]
    (begin
      (unless (closed-simple? s)
        (error 'interp/simple "not a valid Simple expression: ~a" s))
      (interp/simple-env s empty-env))))

(test (interp/simple (fun 'x (var 'x))) (funV 'x (var 'x)))
(test (interp/simple (app (fun 'x (var 'x)) (fun 'x (var 'x))))
      (funV 'x (var 'x)))
(test (interp/simple (bool #t)) (boolV #t))
(test (interp/simple (bool #f)) (boolV #f))
(test (interp/simple (sif (bool #t)
                          (fun 'x (var 'x))
                          (fun 'F (fun 'x (app (var 'F) (var 'x))))))
      (funV 'x (var 'x)))
(test (interp/simple (sif (app (fun 'x (var 'x)) (bool #t)) (bool #t) (bool #f)))
      (boolV #t))
(test/exn (interp/simple (app (bool #t) (bool #f))) "")
