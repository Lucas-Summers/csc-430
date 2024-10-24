; Full project implemented
; Muzart Tuman (mtuman) and Lucas Summers (lsumme01)
#lang typed/racket
(require typed/rackunit)

; defines a lexical environment
(define-type Env (Listof Binding))

; defines an environment binding
(struct Binding ([name : Symbol] [val : Value]) #:transparent)
(define mt-env '()) ; empty environment
(define extend-env cons) ; addas to environment list (for easier readability)

; defines a value type
(define-type Value (U NumV BoolV StringV PrimV ClosV))

; defines a number value
(struct NumV ([n : Real]) #:transparent)
; defines a string value
(struct StringV ([s : String]) #:transparent)
; defines a boolean value
(struct BoolV ([b : Boolean]) #:transparent)
; defines a primitive operator value
(struct PrimV ([op : Symbol]) #:transparent)
; defines a closure
(struct ClosV ([args : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)

; defines an expression type
(define-type ExprC (U Value IdC AppC LamC IfC)) ; remove Value?

; defines an identifier
(struct IdC ([s : Symbol]) #:transparent)
; defines a function application
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
; defines a lambda function
(struct LamC ([args : (Listof Symbol)] [body : ExprC]) #:transparent)
; defines an if statement
(struct IfC ([test : ExprC] [then : ExprC] [else : ExprC]) #:transparent)

; the top-level environment installed with primitive operations and true/false
(define top-env
  (list
   (Binding 'false (PrimV 'false))
   (Binding 'true (PrimV 'true))
   (Binding '+ (PrimV '+))
   (Binding '* (PrimV '*))
   (Binding '- (PrimV '-))
   (Binding '/ (PrimV '/))
   (Binding '<= (PrimV '<=))
   (Binding 'equal? (PrimV 'equal?))
   (Binding 'error (PrimV 'error))))

; given an s-expression, combine parsing and evaluation to produced a result
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env)))

(define (parse [s : Sexp]) : ExprC
  (match s
    [(? real? n) (NumV n)]
    [(? symbol? sym) (IdC (valid-id? sym))]
    [(? string? str) (StringV str)]
    [(list 'if test then else) (IfC (parse test) (parse then) (parse else))]
    [(list 'bind (list (? symbol? a) '= b) ... c) (AppC (LamC (check-args (cast a (Listof Symbol)))
                                                              (parse c))
                                                        (map parse (cast b (Listof Sexp))))]
    [(list (list (? symbol? a) ...) '=> b) (LamC (check-args (cast a (Listof Symbol)))
                                                 (parse b))]
    [(list f a ...) (AppC (parse f) (map parse a))]
    [other (error 'parse "[AAQZ] syntax error: ~e" other)]))


(define (interp [expr : ExprC] [env : Env]) : Value
  (match expr
    [(NumV n) (NumV n)]
    [(IdC s) (lookup s env)]
    [(StringV s) (StringV s)]
    [(LamC a b) (ClosV a b env)]
    [(IfC test then else) (match (interp test env)
                            [(BoolV #t) (interp then env)]
                            [(BoolV #f) (interp else env)]
                            [other (error 'interp "[AAQZ] non-Boolean test in if statement: ~e"
                                           (serialize other))])]
    [(AppC f a) (match (interp f env)
                  [(ClosV args body cenv)
                   (if (equal? (length args) (length a))
                       (interp body
                               (foldl (lambda ([param : Symbol] [arg : ExprC] [acc-env : Env])
                                        (extend-env (bind param (interp arg env)) acc-env))
                                      cenv args a))
                       (error 'interp "[AAQZ] wrong arity: ~e" f))]
                  [(PrimV op) (handle-prims op (map (lambda ([e : ExprC]) (interp e env))
                                                    a))]
                  [other (error 'interp "[AAQZ] application of a non-closure: ~e"
                                (serialize other))])]))

(define (handle-prims [op : Symbol] [args : (Listof Value)]) : Value
  (match (cons op args)
    [(cons 'true '()) (BoolV #t)]
    [(cons 'false '()) (BoolV #f)]
    [(cons 'error (? StringV? s))
     (error 'interp "[AAQZ] user-error: ~e" (serialize s))]
    [(cons 'equal? (list x y))
     (match (cons x y)
       [(cons (PrimV v1) (PrimV v2)) (BoolV (symbol=? v1 v2))]
       [(cons (or (? PrimV?) (? ClosV?)) (or (? PrimV?) (? ClosV?))) (BoolV #f)]
       [other (BoolV (equal? x y))])]
    [(cons arith (list x y))
     (match (cons x y)
       [(cons (NumV x) (NumV y))
        (match arith
          ['+ (NumV (+ x y))]
          ['- (NumV (- x y))]
          ['* (NumV (* x y))]
          ['/ (NumV (if (positive? y)
                        (/ x y)
                        (error 'interp "[AAQZ] division by zero")))]
          ['<= (BoolV (<= x y))])]
       [other (error 'interp "[AAQZ] arithmetic operation with non-number: ~e" arith)])]
    [other (error 'interp "[AAQZ] wrong arity for operation: ~e" op)]))

(define (serialize [val : Value]) : String
  (match val
    [(NumV n) (format "~v" n)]
    [(BoolV #f) "false"]
    [(BoolV #t) "true"]
    [(StringV s) (format "~a" s)]
    [(? ClosV?) "#<procedure>"]
    [(? PrimV?) "#<primop>"]))

(define (bind [n : Symbol] [v : Value]) : Binding
  (Binding n v))

(define (lookup [for : Symbol] [env : Env]) : Value
  (match env
    ['() (error 'lookup "[AAQZ] id out of bounds: ~e" for)]
    [(cons (Binding name val) r) (if (symbol=? for name)
                                     val
                                     (lookup for r))]))

; check if the given symbol is a valid id under the AAQZ4 language
; if it is, return the symbol, else throw an error
(define (valid-id? [s : Symbol]) : Symbol
  (if (member s '(if => bind =))
      (error 'valid-id? "[AAQZ] id not permitted: ~e" s)
      s))

; given a list of arg symbols, return the list if all symbols are unique and are also valid ids
; else, throw an error
(define (check-args [args : (Listof Symbol)]) : (Listof Symbol)
  (match args
    ['() '()]
    [(cons f r) (if (member (valid-id? f) r)
                    (error 'parse "[AAQZ] duplicate argument names: ~e" f)
                    (cons f (check-args r)))]))

; TEST CASES
(serialize (interp (AppC (IdC '+) (list (NumV 10) (NumV 15))) top-env))
(serialize (interp (AppC
                    (LamC '(a b)
                          (AppC (IdC '+) (list (IdC 'a) (IdC 'b))))
                    (list (NumV 10) (NumV 15))) top-env))

(top-interp '{bind [f = {(x) => {+ x 1}}]
      [y = 7]
      {f y}})

(top-interp '{bind [fact = {(self n) => {if {<= n 0}
                               1
                               {* n {self self {- n 1}}}}}]
      {fact fact 4}})

;(serialize (interp (IfC (IdC 'true) (NumV 1) (NumV 0)) top-env))
; interp: [AAQZ] non-Boolean test in if statement: "#<primop>"

(serialize (interp (AppC (IdC '-) (list (NumV 20) (NumV 5))) top-env))

(serialize (interp (AppC (IdC '*) (list (NumV 3) (NumV 4))) top-env))

#;(serialize (interp (AppC (LamC '(x y) (AppC (IdC '+) (list (IdC 'x) (IdC 'y))))
                        (list (NumV 1))) top-env))
; Expected: Error for wrong arity, works but errors out lol

;(serialize (interp (AppC (IdC 'equal?) (list (NumV 5) (BoolV #true))) top-env))
; message:  match: no matching clause for (BoolV #t)

(top-interp '{bind [double = {(x) => {* x 2}}]
      [y = 6]
      {double y}})

;(serialize (interp (IfC (NumV 1) (NumV 5) (NumV 10)) top-env))
; Expected: Error for non-Boolean test in if statement works but errors out

(check-equal? (serialize (interp (parse 'true) top-env)) "#<primop>")

(check-equal? (serialize (interp (parse 'false) top-env)) "#<primop>")

(check-equal? (serialize (interp (parse "\"Hello\"") top-env)) "\"Hello\"")

(check-equal? (serialize (interp (AppC (IdC 'equal?) (list (IdC 'true) (IdC 'true))) top-env)) "true")

(check-equal? (serialize (interp (AppC (IdC 'equal?) (list (IdC 'true) (IdC 'false))) top-env)) "false")

(check-equal? (serialize (interp (AppC (IdC 'equal?) (list (StringV "abc") (StringV "abc"))) top-env)) "true")

(check-equal? (serialize (interp (AppC (IdC 'equal?) (list (StringV "abc") (StringV "xyz"))) top-env)) "false")

(check-equal? (serialize (interp (AppC (IdC '/) (list (NumV 10) (NumV 2))) top-env)) "5")

(check-equal? (serialize
               (interp (AppC (LamC '(x)
                                  (AppC (IdC '+) (list (IdC 'x) (NumV 5))))
                             (list (NumV 10))) top-env))
              "15")

(check-equal? (serialize (ClosV '(x) (AppC (IdC '+) (list (IdC 'x) (NumV 5))) '())) "#<procedure>")

(check-equal? (serialize (PrimV '+)) "#<primop>")

;Handle-prims
(check-equal? (handle-prims 'true '()) (BoolV #t))

(check-equal? (handle-prims 'false '()) (BoolV #f))

(check-equal? (handle-prims 'equal? (list (PrimV '+) (PrimV '+))) (BoolV #t))

(check-equal? (handle-prims 'equal? (list (PrimV '+) (PrimV '-))) (BoolV #f))

(check-equal? (handle-prims 'equal? (list (ClosV '(x) (IdC 'x) '()) (ClosV '(x) (IdC 'x) '()))) (BoolV #f))

; Error tests
(check-exn exn:fail?
           (lambda ()
             (parse 'bind)))

(check-exn exn:fail?
           (lambda ()
             (parse '(bind [f = {(x x) => {+ x 1}}]))))

(check-exn exn:fail?
           (lambda ()
             (interp (AppC (LamC '(x y) (AppC (IdC '+) (list (IdC 'x) (IdC 'y))))
                           (list (NumV 1))) top-env)))

(check-exn exn:fail?
           (lambda ()
             (interp (IfC (NumV 1) (NumV 5) (NumV 10)) top-env)))

(check-exn exn:fail?
           (lambda ()
             (interp (AppC (NumV 5) (list (NumV 10))) top-env)))

(check-exn exn:fail?
           (lambda ()
             (interp (AppC (IdC '+) (list (StringV "hello") (NumV 5))) top-env)))

(check-exn exn:fail?
           (lambda ()
             (interp (AppC (IdC '/) (list (NumV 10) (NumV 0))) top-env)))

(check-exn exn:fail?
           (lambda ()
             (interp (AppC (IdC '+) (list (NumV 1))) top-env)))

(check-exn exn:fail?
           (lambda ()
             (lookup 'nonexistent-symbol top-env)))

(check-exn exn:fail?
           (lambda ()
             (check-args '(x x))))




