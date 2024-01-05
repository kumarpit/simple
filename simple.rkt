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
  [fun (argType Type?) (i identifier?) (body Simple?)]
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
  [var/wt (tenv Tenv?) (v identifier?)]
  [bool/wt (tenv Tenv?) (b boolean?)]
  [sif/wt (p Simple/wt?) (c Simple/wt?) (a Simple/wt?)]
  [fun/wt (argType Type?) (i identifier?) (body Simple/wt?)]
  [app/wt (rator Simple/wt?) (rand Simple/wt?)])

#;
(define (fn-for-simple/wt simple/wt)
  (type-case Simple/wt simple/wt
    [var/wt (tenv v) (... tenv v)]
    [bool/wt (tenv b) (... tenv b)]
    [sif/wt (p c a) (... (fn-for-simple/wt p)
                         (fn-for-simple/wt c)
                         (fn-for-simple/wt a))]
    [fun/wt (argType i body) (... i
                                  (fn-for-simple/wt body))]
    [app/wt (rator rand) (... (fn-for-simple/wt rator)
                              (fn-for-simple/wt rand))]))


;; Selectors

;; Simple/wt -> Tenv
;; produce the type environment associated with the given derivation
(define (simple/wt-tenv simple/wt)
  (type-case Simple/wt simple/wt
    [var/wt (tenv v) tenv]
    [bool/wt (tenv b) tenv]
    [sif/wt (p c a) (simple/wt-tenv p)]
    [fun/wt (argType i body) (shrink-env (simple/wt-tenv body)
                                         (list i))]
    [app/wt (rator rand) (simple/wt-tenv rator)]))


;; Simple/wt -> Simple
;; produce the Simple expression associated with the given Simple/wt
(define (simple/wt-simple simple/wt)
  (type-case Simple/wt simple/wt
    [var/wt (tenv v) (var v)]
    [bool/wt (tenv b) (bool b)]
    [sif/wt (p c a) (sif (simple/wt-simple p)
                         (simple/wt-simple c)
                         (simple/wt-simple a))]
    [fun/wt (argType i body) (fun i
                                  (simple/wt-simple body))]
    [app/wt (rator rand) (app (simple/wt-simple rator)
                              (simple/wt-simple rand))]))

;; Simple/wt -> Type
;; produce the type associated with the given expression
(define (simple/wt-type simple/wt)
  (type-case Simple/wt simple/wt
    [var/wt (tenv v) (lookup-env tenv v)]
    [bool/wt (tenv b) (boolType)]
    [sif/wt (p c a) (simple/wt-type c)]
    [fun/wt (argType i body) (funType argType
                                      (simple/wt-type body))]
    [app/wt (rator rand) (funType-range (simple/wt-type rator))]))


;; Type -> string
;; produce a string corresponding to a given type
(define (type-string type)
  (type-case Type type
    [boolType () "(boolean)"]
    [funType (domain range) (string-append "("
                                           (type-string domain)
                                           "->"
                                           (type-string range)
                                           ")")]))

;; Simple/wt -> void
;; given a well-formed Simple/wt, produce void
;; Effect: signal an error if the given Simple/wt derivation is ill-formed.
(define (check-simple/wt simple/wt)
  (local [;; Tenv Tenv -> void
          (define (check-simple/wt-tenvs simple/wt1 simple/wt2)
            (unless (equal? (simple/wt-tenv simple/wt1)
                            (simple/wt-tenv simple/wt2))
              (error 'check "mismatched envs, ~a ≠ ~a"
                     (simple/wt-tenv simple/wt1)
                     (simple/wt-tenv simple/wt2))))

          ;; Simple/wt Type -> void
          (define (check-simple/wt-type simple/wt type)
            (begin
              (check-simple/wt simple/wt)
              (unless (equal? (simple/wt-type simple/wt) type)
                (error 'check "~a has type ~a: expected ~a"
                       (simple/wt-simple simple/wt)
                       (type-string (simple/wt-type simple/wt))
                       (type-string type)))))

          ;; Type -> funType
          (define (to-funType type)
            (match type
              [(funType param-type result-type) type]
              [else (error 'check-simple/wt "Unexpected non-function type ~a"
                           (type-string type))]))

          ;; Tenv identifier Type -> void
          (define (check-env-binding tenv x expected-type)
            (let ([env-type (lookup-env tenv x)])
              (unless (equal? env-type expected-type)
                (error 'check-simple/wt
                       "unexpected type binding for ~a:\nexpected ~a\ngot ~a"
                       x
                       env-type
                       expected-type))))]
    (type-case Simple/wt simple/wt
      
      ;; [var/wt]
      ;; ----------------------
      ;;    tenv ⊢ v : type
      ;; CHECK: (lookup-env tenv v) = type
      [var/wt (tenv v)
              (cond
                [(assoc v tenv) (void)]
                [else
                 (error 'check-simple/wt "var ~a not bound in tenv ~a" v tenv)])]

      ;; [bool/wt]
      ;; ----------------------
      ;;   tenv ⊢ b : boolean
      [bool/wt (tenv b) (void)]

      ;; [sif/wt]  tenv1 ⊢ p : type1
      ;;           tenv2 ⊢ c : type2  tenv3 ⊢ a : type3
      ;; ------------------------------------------------------------
      ;;          tenv1 ⊢ {if p c a} : type2
      ;; CHECK: tenv1 = tenv2 = tenv3
      ;; CHECK: type1 = boolean
      ;; CHECK: type2 = type3
      [sif/wt (p c a)
              (begin
                (check-simple/wt-type p (boolType))
                (check-simple/wt-type c (simple/wt-type a))
                (check-simple/wt-tenvs p c)
                (check-simple/wt-tenvs c a)
                (check-simple/wt-tenvs p a))]

      ;; [fun/wt]  tenv2 ⊢ body : type1  
      ;; ------------------------------------------------------------
      ;;           tenv1 ⊢ {λ {x : type0} body} : type2
      ;; CHECK: tenv2 = (extend-env tenv1
      ;;                            (list x)
      ;;                            (list type0))
      ;; CHECK: type2 = type0 -> type1
      [fun/wt (argType i body)
              (check-env-binding (simple/wt-tenv body) i argType)]
      
      ;; [app/wt]  tenv1 ⊢ rator : type1   tenv2 ⊢ rand : type2
      ;; ------------------------------------------------------------
      ;;           tenv1 ⊢ {rator rand} : type3
      ;; CHECK: tenv1 = tenv2
      ;; CHECK: type1 = type2 -> type3
      [app/wt (rator rand)
              (begin
                (check-simple/wt-tenvs rator rand)
                (to-funType (simple/wt-type rator))
                (check-simple/wt-type rand (funType-domain (simple/wt-type rator))))])))


(define simple1 (app
                 (fun (funType (boolType) (boolType)) 'x (var 'x))
                 (fun (boolType) 'y (var 'y))))
(define deriv1 (app/wt
                (fun/wt 
                 (funType (boolType) (boolType))
                 'x
                 (var/wt `((x ,(funType (boolType) (boolType)))) 'x))
                (fun/wt (boolType) 'y (var/wt `((y ,(boolType))) 'y))))


;; Make sure the typing derivation is well-formed
(test (check-simple/wt deriv1) (void))
;; Make sure the typing derivation is for the empty environment
(test (simple/wt-tenv deriv1) '())
;; Make sure the type of the derivation is Num -> Num
(test (simple/wt-type deriv1) (funType (boolType) (boolType)))



;; Simple Tenv -> Simple/wt
;; produce the type derivation tree for the given Simple expression
;; Accumulator: tenv is Tenv
;; Invariant: tenv associates identifiers with the types of doru expressions
;;            to which they are bound in the surrounding context.
(define (simple->simple/wt simple tenv)
  (local [(define (synth&check simple tenv type)
            (let ([simple/wt (simple->simple/wt simple tenv)])
              (begin
                (unless (equal? (simple/wt-type simple/wt) type)
                  (error 'simple->simple/wt "type mismatch: expected ~a got ~a"
                         type
                         (simple/wt-type simple/wt)))
                simple/wt)))]
    (type-case Simple simple
      [var (v) (begin
                 (unless (in-env? tenv v)
                   (error 'simple->simple/wt "~s ∉ ~s" v tenv))
                 (var/wt tenv v))]
      [bool (b) (bool/wt tenv b)]
      [sif (p c a) (let ([p/wt (synth&check p tenv (boolType))] 
                         [c/wt (simple->simple/wt c tenv)]
                         [a/wt (simple->simple/wt a tenv)])
                     (unless
                         (equal? (simple/wt-type c/wt)
                                 (simple/wt-type a/wt))
                       (error 'simple->simple/wt "type mismatch: ~a ≠ ~a"
                              (simple/wt-type c/wt)
                              (simple/wt-type a/wt))
                       (sif/wt p/wt c/wt a/wt)))]
      [fun (argType i body) (fun/wt argType
                                    i
                                    (simple->simple/wt
                                     body (extend-env tenv
                                                      (list i)
                                                      (list argType))))]
      [app (rator rand) (app/wt (simple->simple/wt rator tenv)
                                (simple->simple/wt rand tenv))])))

;; Simple -> Simple
;; reproduce simple if simple is a well-typed program (i.e `() ⊢ simple : type)
;; EFFECT: signal an error if not
(define (typecheck-simple simple)
  (let ([simple/wt (simple->simple/wt simple '())])
        (begin
          (unless (and (equal? (simple/wt-tenv simple/wt) '())
                       (equal? (simple/wt-simple simple/wt) simple))
            (error 'typecheck
               "Liar Liar Pants on Fire!\n I wanted: ~a\nYou gave me: ~a.\n"
               (format "'() ⊢ ~s : type for some type" simple)
               (format "~a ⊢ ~a : ~a"
                       (simple/wt-tenv simple/wt)
                       (simple/wt-simple simple/wt)
                       (type-string (simple/wt-type simple/wt)))))
          (check-simple/wt simple/wt)
          simple)))

(test/exn (typecheck-simple (sif (fun (boolType) 'x (var 'x)) (bool #t) (bool #f))) "")
(test/exn (typecheck-simple (app (bool #t) (bool #t))) "")
        

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpretation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type Value
  [boolV (b boolean?)]
  [funV (param symbol?) (body Simple?)])
;; interp. Simple runtime values

;; We restrict Simple to **closed** expressions so we don't need to
;; worry about variable capture


;; no longer need closed-simpled?

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
              [fun (_ i body) (closed-simple?--bounds body (cons i bounds))]
              [app (rator rand) (and (closed-simple?--bounds rator bounds)
                                     (closed-simple?--bounds rand bounds))]))]
    (closed-simple?--bounds s empty)))

(test (closed-simple? (fun (boolType) 'x (var 'x))) #t)
(test (closed-simple? (fun (funType (boolType) (boolType)) 'F
                           (fun (boolType) 'x (app (var 'F) (var 'x))))) #t)
(test (closed-simple? (app (fun (boolType) 'x (var 'x)) (var 'y))) #f)

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
              [fun (_ i body) (funV i body)]
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
      (typecheck-simple s)
      (interp/simple-env s empty-env))))

;; all my tests are now broken :)
#;{
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
   }
