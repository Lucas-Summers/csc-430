; Full project implemented
; Muzart Tuman (mtuman) and Lucas Summers (lsumme01)
#lang typed/racket
(require typed/rackunit)

; defines an environment
(define-type Env (Listof Binding))
; defines a binding within an evironment
(struct Binding ([name : Symbol] [loc : Integer]) #:transparent)
(define mt-env '()) ; empty environment
(define extend-env cons) ; add a binding to an environment

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
(define-type ExprC (U IdC AppC LamC IfC RecC Value))
; defines an identifier
(struct IdC ([s : Symbol]) #:transparent)
; defines a function application
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
; defines a lambda function
(struct LamC ([args : (Listof TBinding)] [body : ExprC]) #:transparent)
; defines an if statement
(struct IfC ([test : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
; defines a recursive expression
(struct RecC ([t : TBinding] [body : ExprC] [use : ExprC]))

; defines a type environment
(define-type TEnv (Listof TBinding))
; define a type binding in a TEnv
(struct TBinding ([name : Symbol] [t : Ty]) #:transparent)
(define extend-type-env cons) ; add a type binding to a type environment
; defines a Type type
(define-type Ty (U NumT StringT BoolT LamT))
; defines a number type
(struct NumT () #:transparent)
; defines a number type
(struct BoolT () #:transparent)
; defines a string type
(struct StringT () #:transparent)
; defines a lambda type
(struct LamT ([args : (Listof Ty)] [ret : Ty]) #:transparent)

; a version of make-vector that only makes Value vectors (for the store)
(define make-value-vector (inst make-vector Value))

; the list of AAQZ7 primitives, each listed as a list of Symbol, Value and Type
(define prims
  (list
   (list 'false (BoolV #f) (BoolT))
   (list 'true (BoolV #t) (BoolT))
   (list '+ (PrimV '+) (LamT (list (NumT) (NumT)) (NumT)))
   (list '* (PrimV '*) (LamT (list (NumT) (NumT)) (NumT)))
   (list '- (PrimV '-) (LamT (list (NumT) (NumT)) (NumT)))
   (list '/ (PrimV '/) (LamT (list (NumT) (NumT)) (NumT)))
   (list '<= (PrimV '<=) (LamT (list (NumT) (NumT)) (BoolT)))
   (list 'num-eq? (PrimV 'num-eq?) (LamT (list (NumT) (NumT)) (BoolT)))
   (list 'str-eq? (PrimV 'str-eq?) (LamT (list (StringT) (StringT)) (BoolT)))))

; the base type environment installed with primitives
(define base-tenv (foldl (lambda ([p : (List Symbol Value Ty)] [acc-tenv : TEnv])
                           (extend-type-env (TBinding (car p) (caddr p)) acc-tenv))
                         mt-env prims))

; given an s-expression, combines parsing, type-checking, evaluation, and serialization
; of AAQZ7 to produce a result as a string
(define (top-interp [s : Sexp]) : String
  (let* ([store (make-initial-store 2000)]
        [env (install-prims prims store)]
        [expr (parse s)])
    (type-check expr base-tenv)
    (serialize (interp expr env store))))

; checks that the given AAQZ7 AST is of the correct type according to the given type environment
(define (type-check [expr : ExprC] [tenv : TEnv]) : Ty
  (match expr
    [(NumV _) (NumT)]
    [(StringV _) (StringT)]
    [(BoolV _) (BoolT)]
    [(IdC s) (lookup-type s tenv)]
    [(IfC test then else)
     (begin
       (unless (BoolT? (type-check test tenv))
         (error 'type-check "[AAQZ] if condition must evaluate to type bool"))
       (let ([then-type (type-check then tenv)]
             [else-type (type-check else tenv)])
         (if (equal? then-type else-type)
             then-type
             (error 'type-check "[AAQZ] branches of if must have the same type"))))]
    [(LamC a b) (LamT (map (lambda ([tbind : TBinding]) (TBinding-t tbind)) a)
                      (type-check b (foldl (lambda ([tb : TBinding] [acc-tenv : TEnv])
                                             (extend-type-env tb acc-tenv))
                                           tenv a)))]
    [(RecC t f u) (let ([extended-env (extend-type-env t tenv)])
                    (cond
                      [(not (equal? (TBinding-t t) (type-check f extended-env)))
                       (error 'type-check "[AAQZ] wrong type for recbind ~e" (TBinding-name t))]
                      [else (type-check u extended-env)]))]
    [(AppC f a) (match (type-check f tenv)
                  [(LamT args ret)
                   (if (= (length args) (length a))
                       (begin
                         (for-each (lambda ([arg : ExprC] [arg-type : Ty])
                                     (unless (equal? (type-check arg tenv) arg-type)
                                       (error 'type-check "[AAQZ] type mismatch, expected ~e got ~e"
                                              arg-type
                                              (type-check arg tenv))))
                                   a args)
                         ret)
                       (error 'type-check "[AAQZ] wrong number of arguments in function call ~e" f))]
                  [other (error 'type-check "[AAQZ] trying to call a non-function ~e" f)])]))

; parses an s-expression into an AAQZ7 AST that can be interpreted
(define (parse [s : Sexp]) : ExprC
  (match s
    [(? real? n) (NumV n)]
    [(? symbol? sym) (IdC (valid-id? sym))]
    [(? string? str) (StringV str)]
    [(list 'if test then else) (IfC (parse test) (parse then) (parse else))]
    ; casts must succeed...
    [(list 'bind (list (? symbol? a) ': t '= b) ... c)
     (AppC (LamC (map (lambda ([arg : Symbol] [ty : Sexp])
                        (TBinding arg (parse-type ty)))
                      (check-args (cast a (Listof Symbol)))
                      (cast t (Listof Sexp)))
                 (parse c))
           (map parse (cast b (Listof Sexp))))]
    [(list 'recbind (list (? symbol? n) ': t '= f) u) (RecC (TBinding (valid-id? n) (parse-type t))
                                                             (parse f)
                                                             (parse u))]
    ; cast must succeed...
    [(list (list (list (? symbol? a) ': t) ...) '=> b)
     (LamC (map (lambda ([arg : Symbol] [ty : Sexp])
                  (TBinding arg (parse-type ty)))
                (check-args (cast a (Listof Symbol))) (cast t (Listof Sexp)))
           (parse b))]
    [(list f a ...) (AppC (parse f) (map parse a))]
    [other (error 'parse "[AAQZ] syntax error: ~e" other)]))

; parses an s-expression in AAQZ7 type sytax into a Type
(define (parse-type [s : Sexp]) : Ty
  (match s
    ['num (NumT)]
    ['str (StringT)]
    ['bool (BoolT)]
    ; cast must succeed
    [(list args ... '-> ret) (LamT (map parse-type (cast args (Listof Sexp))) (parse-type ret))]
    [other (error 'parse "[AAQZ] invalid type ~e" s)]))

; interprets an AAQZ7 AST given an environment and store to produce a Value
(define (interp [expr : ExprC] [env : Env] [store : (Vectorof Value)]) : Value
  (match expr
    [(NumV n) (NumV n)]
    [(StringV s) (StringV s)]
    [(IdC s) (lookup s env store)]
    [(LamC a b) (ClosV (map TBinding-name a) b env)]
    [(IfC test then else) (match (interp test env store)
                            [(BoolV #t) (interp then env store)]
                            [(BoolV #f) (interp else env store)]
                            [other (error 'interp "[AAQZ] non-Boolean test in if statement: ~e"
                                          (serialize other))])]
    [(AppC f a) (match (interp f env store)
                  [(ClosV args body cenv)
                   (if (equal? (length args) (length a))
                       (interp body
                               (foldl (lambda ([param : Symbol] [arg : ExprC] [acc-env : Env])
                                        (add-to-store acc-env store (cons param
                                                                          (interp arg env store))))
                                      cenv args a)
                               store)
                       (error 'interp "[AAQZ] wrong arity: ~e" f))]
                  [(PrimV op) (handle-prims op
                                            (map (lambda ([e : ExprC]) (interp e env store)) a)
                                            store)]
                  [other (error 'interp "[AAQZ] application of a non-closure: ~e"
                                (serialize other))])]
    [(RecC (TBinding n t) f u) (let* ([extended-env (add-to-store env store (cons n (NumV 0)))]
                                      [v (interp f extended-env store)])
                                 (vector-set! store (lookup-index n extended-env) v)
                                 (interp u extended-env store))]))

; performs the AAQZ7 primitive operation corresponding to the given symbol on the
; given list of Values, returning the result as a Value
(define (handle-prims [op : Symbol] [args : (Listof Value)] [store : (Vectorof Value)]) : Value
  (match (cons op args)
    [(cons 'num-eq? (list (NumV x) (NumV y)))
     (BoolV (equal? x y))]
    [(cons 'str-eq? (list (StringV x) (StringV y)))
     (BoolV (equal? x y))]
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

; adds a given Value to the given store,
; then creating a binding in the given environment with its location in the store
(define (add-to-store [env : Env]
                      [store : (Vectorof Value)]
                      [new : (Pairof Symbol Value)]) : Env
  (let* ([sym (car new)]
         [val (cdr new)]
         [loc (allocate store (list val))])
    (extend-env (Binding sym loc) env)))

; allocates the given Values in the next available area of the store, returning the base location
; throw error if the store does not have enough space for all the given Values
(define (allocate [store : (Vectorof Value)] [vals : (Listof Value)]) : Integer
  (let* ([loc (cast (NumV-n (cast (vector-ref store 0) NumV)) Integer)] ; casts must succeed...
         [len (length vals)])
    (when (< (vector-length store) (+ loc len))
      (error 'allocate "[AAQZ] ran out of memory"))
    (for ([i (in-range (length vals))])
      (vector-set! store (+ i loc) (list-ref vals i)))
    (vector-set! store (ann 0 Natural) (NumV (+ loc len)))
    loc))

; given the list of primatives (Symbol, Value, Type), allocates each primative on the given store,
; binding their locations in the store in a new top-level environment
(define (install-prims [prims : (Listof (List Symbol Value Ty))] [store : (Vectorof Value)]) : Env
  (foldl (lambda ([p : (List Symbol Value Ty)] [acc-env : Env])
           (add-to-store acc-env store (cons (car p) (cadr p))))
         mt-env prims))

; creates a store vector of the given size (with added room for primatives)
(define (make-initial-store [memsize : Integer]) : (Vectorof Value)
  (let ([s (make-value-vector (+ memsize (length prims)) (NumV 0))])
    (vector-set! s (ann 0 Natural) (NumV 1))
    s))

; returns a string that is a readable form of the given AAQZ6 Value
(define (serialize [val : Value]) : String
  (match val
    [(NumV n) (format "~v" n)]
    [(BoolV #f) "false"]
    [(BoolV #t) "true"]
    [(StringV s) (format "~v" s)]
    [(? ClosV?) "#<procedure>"]
    [(? PrimV?) "#<primop>"]))

; for the given environment, finds the Binding with the name corresponding to the given symbol
; and returns the Value corresponding to the Bindings location in the store,
; else throws an error if not found
(define (lookup [for : Symbol] [env : Env] [store : (Vectorof Value)]) : Value
  (match env
    ['() (error 'lookup "[AAQZ] id not bound: ~e" for)]
    [(cons (Binding name loc) r) (if (symbol=? for name)
                                     (vector-ref store loc)
                                     (lookup for r store))]))

; for the given environment, finds the Binding with the name corresponding to the given symbol
; and returns the binding's location in the store, else throws an error if not found
(define (lookup-index [for : Symbol] [env : Env]) : Integer
  (match env
    ['() (error 'lookup-index "[AAQZ] id not bound: ~e" for)]
    [(cons (Binding name loc) r) (if (symbol=? for name)
                                     loc
                                     (lookup-index for r))]))

; for the given type environment, finds the binding corresponding to the given symbol
; returning the type associated with that binding
(define (lookup-type [for : Symbol] [tenv : TEnv]) : Ty
  (match tenv
    ['() (error 'lookup-type "[AAQZ] id not bound: ~e" for)]
    [(cons (TBinding name t) r) (if (symbol=? for name)
                                    t
                                    (lookup-type for r))]))

; check if the given symbol is a valid id under the AAQZ7 language
; if it is, returns the symbol, else throws an error
(define (valid-id? [s : Symbol]) : Symbol
  (if (member s '(if => bind recbind = :))
      (error 'valid-id? "[AAQZ] id not permitted: ~e" s)
      s))

; given a list of function arg symbols, returns the list if all symbols are unique
; and are also valid ids under AAQZ7, else throws an error
(define (check-args [args : (Listof Symbol)]) : (Listof Symbol)
  (match args
    ['() '()]
    [(cons f r) (if (member (valid-id? f) r)
                    (error 'parse "[AAQZ] duplicate argument names: ~e" f)
                    (cons f (check-args r)))]))

; TEST CASES
(check-equal? (top-interp '{{([x : str] [y : str]) => {str-eq? x y}} "test" "test"}) "true")
; from assignment
(check-equal? (top-interp '{recbind [square-helper
                       : {num -> num}
                       = {([n : num]) => {if {<= n 0} 0 {+ n {square-helper {- n 2}}}}}]
                      {bind [square
                             : {num -> num}
                             = {([n : num]) => {square-helper {- {* 2 n} 1}}}]
                            {square 13}}}) "169")
(check-equal? (top-interp '{{([x : bool]) => x} true}) "true")
(check-equal? (type-check (BoolV #t) '()) (BoolT))

;error tests
(check-exn exn:fail? (lambda () (top-interp '{if 42 true false})))
(check-exn exn:fail? (lambda () (top-interp '{if true 42 "hello"})))
(check-exn exn:fail? (lambda ()
                       (top-interp '{recbind [f : {num -> num} = {([x : num]) => "wrong"}] 42})))
(check-exn exn:fail? (lambda () (top-interp '{{([x : num]) => x} "string"})))
(check-exn exn:fail? (lambda () (top-interp '{{([x : num] [y : num]) => x} 42})))
(check-exn exn:fail? (lambda () (top-interp '{42 1})))
(check-exn exn:fail? (lambda () (top-interp '(bind [x : num]))))

(check-exn exn:fail? (lambda () (top-interp '(()))))
(check-exn exn:fail? (lambda () (top-interp '(bind (x : invalid = 1) x))))
(check-exn exn:fail? (lambda () (top-interp '(/ 1 0))))
(check-exn exn:fail? (lambda () (top-interp '(/ 1 (- 1 1)))))
;
(check-exn exn:fail? (lambda () (top-interp '((([x : num] [x : num]) => 1) 1 2))))
(check-exn exn:fail? (lambda () (top-interp '((([x : num] [y : num] [x : num]) => 1) 1 2 3))))

(check-exn exn:fail? (lambda () (top-interp '(IdC 'x))))
(check-exn exn:fail? (lambda () (lookup-index 'z '())))


(check-exn exn:fail?
           (lambda ()
             (lookup 'undefined-id '() (vector))))
(check-exn exn:fail?
           (lambda ()
             (lookup-index 'undefined-id '())))
(check-exn exn:fail?
           (lambda ()
             (valid-id? 'if)))
(check-exn exn:fail?
           (lambda ()
             (check-args '(x x))))
(check-exn exn:fail?
           (lambda ()
             (check-args '(if x))))

(check-equal? (handle-prims '/ (list (NumV 10) (NumV 2)) (make-vector 10 (NumV 0))) (NumV 5))
(check-exn exn:fail? (lambda () (handle-prims '+ (list (NumV 5)) (make-vector 10 (NumV 0)))))
(check-exn exn:fail? (lambda () (handle-prims '+ (list (NumV 5) (StringV "not-a-number"))
                                              (make-vector 10 (NumV 0)))))
(check-equal? (handle-prims 'num-eq? (list (NumV 5) (NumV 5)) (make-vector 10 (NumV 0))) (BoolV #t))
(check-exn exn:fail? (lambda () (allocate (make-initial-store 10) (make-list 1000 (NumV 1)))))
(check-equal? (lookup-index 'y (cons (Binding 'x 1) (cons (Binding 'y 2) '()))) 2)

; interp error tests
(check-exn exn:fail? (lambda ()
                       (interp (IfC (NumV 1) (NumV 2) (NumV 3)) '() (make-initial-store 10))))
(check-exn exn:fail? (lambda ()
                       (interp (AppC (NumV 10) (list (NumV 1))) '() (make-initial-store 10))))
(check-exn exn:fail? (lambda ()
                       (interp (AppC (LamC (list (TBinding 'x (NumT))) (NumV 42))
                                     (list (NumV 1) (NumV 2))) '() (make-initial-store 10))))

;serialize tests
(check-equal? (serialize (NumV 42)) "42")
(check-equal? (serialize (BoolV #f)) "false")
(check-equal? (serialize (BoolV #t)) "true")
(check-equal? (serialize (StringV "Hello")) "\"Hello\"")
(check-equal? (serialize (ClosV '() (NumV 42) '())) "#<procedure>")
(check-equal? (serialize (PrimV 'add)) "#<primop>")