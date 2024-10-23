; Full project implemented
; Muzart Tuman (mtuman) and Lucas Summers (lsumme01)
#lang typed/racket
(require typed/rackunit)

; defines a lexical environment as a list of bindings
(define-type Env (Listof Binding))
; defines an environment binding
(struct Binding ([name : Symbol] [val : Value]) #:transparent)
(define mt-env '()) ; empty environment
(define extend-env cons) ; addas to environment list (for easier readability)

; defines a value type
(define-type Value (U NumV BoolV StringV PrimV ClosV))
; defines a number value
(struct NumV ([n : Real]) #:transparent)
; defines a boolean value
(struct BoolV ([b : Boolean]) #:transparent)
; defines a string value
(struct StringV ([s : String]) #:transparent)
; supports both unary (only error) and binary operators
; defines a primitive operator value
; NOTE: using struct instead of define-type gives access to PrimV? predicate
(struct PrimV () #:transparent)
; defines binary primitive operators (+, -, *, /, equal?, <=)
(struct BinaryP PrimV ([op : (-> Value Value Value)]) #:transparent)
; defines unary primitive operators (just error for now)
(struct UnaryP PrimV ([op : (-> Value Value)]) #:transparent)
; defines a closure
(struct ClosV ([args : (Listof Symbol)] [body : ExprC] [env : Env]))

; defines an expression type
(define-type ExprC (U Value IdC AppC LamC)) ; remove Value?
; defines an identifier
(struct IdC ([s : Symbol]) #:transparent)
; defines a function application
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
; defines a lambda function
(struct LamC ([args : (Listof Symbol)] [body : ExprC]))

(define (binop [s : Symbol] [l : Value] [r : Value]) : Value
  (cond
    [(and (NumV? l) (NumV? r)) 
      (match s
        ['+ (NumV (+ (NumV-n l) (NumV-n r)))]
        ['- (NumV (- (NumV-n l) (NumV-n r)))]
        ['* (NumV (* (NumV-n l) (NumV-n r)))]
        ['/ (NumV (/ (NumV-n l) (NumV-n r)))]
        ['<= (BoolV (<= (NumV-n l) (NumV-n r)))])]
    [(symbol=? s 'equal?) (if (or (or (PrimV? l) (ClosV? l)) (or (PrimV? r) (ClosV? r))) ;confused here - muzart
                              (error 'arith "[AAQZ]: cannot compare closures or primitives")
                              (BoolV (equal? l r)))]
    [else (error 'arith "[AAQZ] at least on argument was not a number")]))

; the top-level environment installed with primitive operations and true/false
(define top-env
  (list
   (Binding 'false (BoolV false))
   (Binding 'true (BoolV true))
   (Binding '+ (BinaryP (lambda ([a : Value] [b : Value]) : Value (binop '+ a b))))
   (Binding '* (BinaryP (lambda ([a : Value] [b : Value]) : Value (binop '* a b))))
   (Binding '- (BinaryP (lambda ([a : Value] [b : Value]) : Value (binop '- a b))))
   (Binding '/ (BinaryP (lambda ([a : Value] [b : Value]) : Value (binop '/ a b))))
   (Binding '<= (BinaryP (lambda ([a : Value] [b : Value]) : Value (binop '<= a b))))
   (Binding 'equal? (BinaryP (lambda ([a : Value] [b : Value]) : Value (binop 'equal? a b))))
   (Binding 'error (UnaryP (lambda ([a : Value]) (error "[AAQZ] user-error: ~e" (serialize a)))))))

; given an s-expression, combine parsing and evaluation to produced a result
;(define (top-interp [s : Sexp]) : String
;  (serialize (interp (parse s) top-env)))

; TODO parse to the new setup
; parse an s-expression into an ExprC
;(define (parse [s : Sexp]) : ExprC
;  (match s
;    [(? real? n) (NumV n)]
;    [(? symbol? s) (IdC (valid-id? s))]
;    [(list (? symbol? f) a ...) (AppC (valid-id? f) (map parse a))]
;    [other (error 'parse "[AAQZ] syntax error: ~e" other)]))
#;(define (parse [s : Sexp]) : ExprC
  (match s
    [(? real? n) (NumV n)] ; Numbers become NumV
    [(? symbol? sym) (IdC (valid-id? sym))] ; Symbols become IdC
    [(list (? symbol? f) a ...) ; Function application
     (match f
       ['lambda 
        (match a
          [(list args body) 
           (LamC (check-args args) (parse body))] ; Lambda function
          [other (error 'parse "[AAQZ] invalid lambda syntax: ~e" other)])]
       [else (AppC (IdC (valid-id? f)) (map parse a))])] ; Function application
    [other (error 'parse "[AAQZ] syntax error: ~e" other)]))
; my take on parse

(define (bind [n : Symbol] [v : Value]) : Binding
  (Binding n v))

(define (serialize [val : Value]) : String
  (match val
    [(NumV n) (format "~v" n)]
    [(BoolV #f) "false"]
    [(BoolV #t) "true"]
    [(StringV s) (format "\"~v\"" s)]
    [(? ClosV?) "#<procedure>"]
    [(? PrimV?) "#<primop>"]))


(define (interp [expr : ExprC] [env : Env]) : Value
  (match expr
    [(NumV n) (NumV n)]
    [(IdC s) (lookup s env)]
    [(LamC a b) (ClosV a b env)]
    [(AppC f a) (define f-val (interp f env))
                (match f-val
                  [(ClosV args body env)
                   (if (equal? (length (ClosV-args f-val)) (length a))
                       (interp (ClosV-body f-val)
                               (foldl (lambda ([param : Symbol] [arg : ExprC] [e : Env])
                                        (extend-env (bind param (interp arg e))
                                                    e))
                                      (ClosV-env f-val) (ClosV-args f-val) a))
                       (error 'interp "[AAQZ] wrong arity: ~e" f))]
                  [(? PrimV? (BinaryP op))
                   (op (interp (first a) env) (interp (second a) env))]
                  [(? PrimV? (UnaryP op))
                   (op (interp (first a) env))])]))

(define (lookup [for : Symbol] [env : Env]) : Value
  (match env
    ['() (error 'lookup "[AAQZ] binding not found: ~e" for)]
    [(cons (Binding name val) r) (if (symbol=? for name) val (lookup for r))]))

; TODO change to match new specification and add to parse function
; check if the given symbol is a valid id under the AAQZ language
; if it is, return the symbol, else throw an error
(define (valid-id? [s : Symbol]) : Symbol
  (if (member s '(* + - / def ifleq0? =>))
      (error 'valid-id? "[AAQZ] id ~e not permitted" s)
      s))

; TODO add to interp
; given a list of args, return the list if all arg Symbols are unique and valid ids
; else, throw an error
(define (check-args [args : (Listof Symbol)]) : (Listof Symbol)
  (match args
    ['() '()]
    [(cons f r) (if (member (valid-id? f) r)
                    (error 'parse-fundef "[AAQZ] duplicate argument names: ~e" f)
                    (cons f (check-args r)))]))


; TEST CASES
(serialize (interp (AppC (IdC '+) (list (NumV 10) (NumV 15))) top-env))
(serialize (interp (AppC
                    (LamC '(a b)
                          (AppC (IdC '+) (list (IdC 'a) (IdC 'b))))
                    (list (NumV 10) (NumV 15))) top-env))