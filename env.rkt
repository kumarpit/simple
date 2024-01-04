#lang plai

(print-only-errors #t)

;; Taken from CPSC 311 course materials
;; Authored by Ron Garcia

;; (envof X) is (listof (list symbol X))

;; any -> boolean
;; produce true if the given object is an (envof X)
(define ((envof? X?) x)
  (match x
    [(list `(,x ,v) ...) #:when (and (andmap symbol? x)
                                     (andmap X? v)) #t]
    [else #f]))

;; (listof symbol) -> boolean
;; produce true if each symbol in x* appears only once
(define (unique? lox)
  (cond
    [(empty? lox) #t]
    [else ;; (cons? lox)
     (and (not (member (first lox) (rest lox)))
          (unique? (rest lox)))]))

(test (unique? '()) #t)
(test (unique? '(a)) #t)
(test (unique? '(a b c d)) #t)
(test (unique? '(a b c b)) #f)
(test (unique? '(a a c d)) #f)

;; empty-env : Env
(define empty-env '())

;; extend-env : (envof X) (listof symbol) (listof X) -> (envof X)
;; Produce an environment that binds distinct symbols in x* to values in v*.
;; ASSUME: (= (length x*) (length v*))
;; ASSUME: (unique? x*) 

(define (extend-env env x* v*)
  (append (map list x* v*) env))

(test (extend-env empty-env '(x y z) '(5 6 7)) '((x 5)
                                                 (y 6)
                                                 (z 7)))
(test (extend-env
       (extend-env empty-env '(x y z) '(5 6 7))
       '(a x c) '(5 6 7))
      '((a 5)
        (x 6)
        (c 7)
        (x 5)
        (y 6)
        (z 7)))

;; lookup-env : (envof X) symbol -> X
;; Produce the binding for the given symbol.
;; Effect: Signals an error if no binding is found.
(define (lookup-env env x)
  (cond [(empty? env) (error 'lookup-env "unbound identifier: ~a" x)]
        [else (if (symbol=? x (car (first env)))
                  (cadr (first env))
                  (lookup-env (rest env) x))]))

(test (lookup-env (extend-env
                   (extend-env empty-env '(x y z) '(5 6 7))
                   '(a x c) '(5 6 7))
                  'z)
      7)

;; (envof X) Symbol -> Boolean
;; produce true if the environment binds x, otherwise false
(define (in-env? env x)
  (cond [(assoc x env) #t]
        [else #f]))

(test (in-env? (extend-env
                (extend-env empty-env '(x y z) '(5 6 7))
                '(a x c) '(5 6 7))
               'z)
      #t)

(test (in-env? (extend-env
                (extend-env empty-env '(x y z) '(5 6 7))
                '(a x c) '(5 6 7))
               'q)
      #f)

;; (envof X) (listof identifier) -> (envof X)
;; remove the initial bindings of env indicated by loid
(define (shrink-env env loid)
  (cond
    [(empty? loid) env]
    [else ; (cons? loid)
     (if (symbol=? (caar env) (first loid))
         (shrink-env (rest env) (rest loid))
         (error 'shrink-env "Binding mismatch: ~a ∈ ~a"  (first loid) env))]))


(test (shrink-env empty-env empty) empty-env)

(test (shrink-env (extend-env empty-env (list 'x 'y) (list 7 8))
                  (list 'x))
      (extend-env empty-env (list 'y) (list 8)))

(test (shrink-env (extend-env empty-env (list 'x 'y) (list 7 8))
                  (list 'x 'y)) empty-env)

(test/exn (shrink-env (extend-env empty-env (list 'x 'y) (list 7 8))
                      (list 'y)) "mismatch")

;; (envof X) (listof symbol) (listof X) -> boolean
;; Produce true if environment env0 begins with mapping of identifers
;; in x* to values in v*.
;; ASSUME: (= (length x*) (length v*))
;; ASSUME: (unique? x*)
(define (extends-env? env0 x*0 v*0)
  (let loop ([x* x*0] [v* v*0] [env env0])
    (cond [(empty? x*) #t]
          [else (match env0
                  [(cons (list x^ v^)  env^)                    
                   (and (equal? (first x*) x^)
                        (equal? (first v*) v^)
                        (loop (rest x*) (rest v*) (rest env)))]
                  [else #f])])))
