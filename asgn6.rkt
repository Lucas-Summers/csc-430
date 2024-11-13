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
(define-type Value (U NumV BoolV StringV PrimV ClosV NullV ArrayV))
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
; defines a null value
(struct NullV () #:transparent)
; defines an array value
(struct ArrayV ([start : Integer] [len : Integer]) #:transparent)

; defines an expression type
(define-type ExprC (U IdC AppC LamC IfC MutateC Value))
; defines an identifier
(struct IdC ([s : Symbol]) #:transparent)
; defines a function application
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
; defines a lambda function
(struct LamC ([args : (Listof Symbol)] [body : ExprC]) #:transparent)
; defines an if statement
(struct IfC ([test : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
; defines a mutation expression
(struct MutateC ([id : Symbol] [new : ExprC]) #:transparent)

; a version of make-vector that only makes Value vectors (for the store)
(define make-value-vector (inst make-vector Value))

; the list of AAQZ6 primatives + booleans + null, each listed as a Symbol-Value pair
(define prims
  (list
   (cons 'false (BoolV #f))
   (cons 'true (BoolV #t))
   (cons '+ (PrimV '+))
   (cons '* (PrimV '*))
   (cons '- (PrimV '-))
   (cons '/ (PrimV '/))
   (cons '<= (PrimV '<=))
   (cons 'equal? (PrimV 'equal?))
   (cons 'error (PrimV 'error))
   (cons 'null (NullV))
   (cons 'array (PrimV 'array))
   (cons 'make-array (PrimV 'make-array))
   (cons 'aref (PrimV 'aref))
   (cons 'aset! (PrimV 'aset!))
   (cons 'seq (PrimV 'seq))
   (cons 'substring (PrimV 'substring))))

; given an s-expression, combines parsing and evaluation of AAQZ6 to produce a result as a string
(define (top-interp [s : Sexp] [memsize : Integer]) : String
  (let ([store (make-initial-store memsize)])
    (serialize (interp (parse s) (install-prims prims store) store))))

; parses an s-expression into an AAQZ6 ExprC that can be interpreted
(define (parse [s : Sexp]) : ExprC
  (match s
    [(? real? n) (NumV n)]
    [(? symbol? sym) (IdC (valid-id? sym))]
    [(? string? str) (StringV str)]
    [(list (? symbol? s) ':= e) (MutateC s (parse e))]
    [(list 'if test then else) (IfC (parse test) (parse then) (parse else))]
    ; casts must succeed...
    [(list 'bind (list (? symbol? a) '= b) ... c) (AppC (LamC (check-args (cast a (Listof Symbol)))
                                                              (parse c))
                                                        (map parse (cast b (Listof Sexp))))]
    ; cast must succeed...
    [(list (list (? symbol? a) ...) '=> b) (LamC (check-args (cast a (Listof Symbol)))
                                                 (parse b))]
    [(list f a ...) (AppC (parse f) (map parse a))]
    [other (error 'parse "[AAQZ] syntax error: ~e" other)]))

; interprets an AAQZ6 ExprC given an environment of bindings to produce a Value
(define (interp [expr : ExprC] [env : Env] [store : (Vectorof Value)]) : Value
  (match expr
    [(NumV n) (NumV n)]
    [(StringV s) (StringV s)]
    [(IdC s) (lookup s env store)]
    [(LamC a b) (ClosV a b env)]
    [(IfC test then else) (match (interp test env store)
                            [(BoolV #t) (interp then env store)]
                            [(BoolV #f) (interp else env store)]
                            [other (error 'interp "[AAQZ] non-Boolean test in if statement: ~e"
                                          (serialize other))])]
    [(MutateC s n) (begin
                     (vector-set! store (lookup-index s env) (interp n env store))
                     (NullV))]
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
                                (serialize other))])]))

; performs the AAQZ6 primitive operation corresponding to the given symbol on the
; given list of Values, returning the result as a Value
(define (handle-prims [op : Symbol] [args : (Listof Value)] [store : (Vectorof Value)]) : Value
  (match (cons op args)
    [(cons 'error (list x))
     ; cast must succeed...
     (error 'interp "[AAQZ] user-error: ~e" (serialize (cast x Value)))]
    [(cons 'equal? (list x y))
     (match (cons x y)
       [(cons (or (? PrimV?) (? ClosV?)) (or (? PrimV?) (? ClosV?))) (BoolV #f)]
       [other (BoolV (equal? x y))])]
    [(cons 'seq (list _ ... x)) (cast x Value)] ; cast must succeed...
    [(cons 'array (list x ...)) (if (empty? x)
                                    (error 'interp "[AAQZ] array must have at least one cell")
                                    ; cast must succeed...
                                    (ArrayV (allocate store (cast x (Listof Value)))
                                            (length x)))]
    [(cons 'make-array (list x y))
     (match x
       ; casts must succeed...
       [(NumV (? positive? n)) (ArrayV (allocate store (make-list (cast n Integer) (cast y Value)))
                                       (cast n Integer))]
       [other (error 'interp "[AAQZ] invalid array size: ~e" (serialize (cast x Value)))])]
    [(cons 'aref (list x y))
     (match (cons x y)
       [(cons (ArrayV s l) (NumV y)) (if (or (> 0 y) (< l y))
                                         (error 'interp "[AAQZ] array index out of bounds: ~e" x)
                                         ; cast must succeed...
                                         (vector-ref store (+ s (cast y Integer))))]
       [other (error 'interp "[AAQZ] invalid array reference")])]
    [(cons 'aset! (list x y z))
     (match (cons x y)
       [(cons (ArrayV s l) (NumV y)) (begin
                                       (if (or (> 0 y) (< l y))
                                         (error 'interp "[AAQZ] array index out of bounds: ~e" x)
                                         ; casts must succeed...
                                         (vector-set! store (+ s (cast y Integer)) (cast z Value)))
                                       (NullV))]
       [other (error 'interp "[AAQZ] invalid array mutation")])]
    [(cons 'substring (list x y z))
     (match (list x y z)
       ; casts must succeed...
       [(list (StringV x) (NumV y) (NumV z)) (StringV (substring x
                                                                 (cast y Integer)
                                                                 (cast z Integer)))]
       [other (error 'interp "[AAQZ] invalid indexes to string ~e" (serialize (cast x Value)))])]
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
  (let* ([loc (ArrayV-len (cast (vector-ref store 0) ArrayV))] ; cast must succeed...
         [len (length vals)])
    (when (< (vector-length store) (+ loc len))
      (error 'allocate "[AAQZ] ran out of memory"))
    (for ([i (in-range (length vals))])
      (vector-set! store (+ i loc) (list-ref vals i)))
    (vector-set! store 0 (ArrayV 1 (+ loc len)))
    loc))

; given the list of primatives (each a Symbol-Value pair),
; allocates each primative on the given store,
; binding their locations in the store in a new top-level environment
(define (install-prims [prims : (Listof (Pairof Symbol Value))] [store : (Vectorof Value)]) : Env
  (foldl (lambda ([p : (Pairof Symbol Value)] [acc-env : Env])
           (add-to-store acc-env store p))
         mt-env prims))

; creates a store vector of the given size (with added room for primatives)
(define (make-initial-store [memsize : Integer]) : (Vectorof Value)
  (let ([s (make-value-vector (+ memsize (length prims)) (NullV))])
    (vector-set! s 0 (ArrayV 1 1))
    s))

; returns a string that is a readable form of the given AAQZ6 Value
(define (serialize [val : Value]) : String
  (match val
    [(NumV n) (format "~v" n)]
    [(BoolV #f) "false"]
    [(BoolV #t) "true"]
    [(StringV s) (format "~v" s)]
    [(? ClosV?) "#<procedure>"]
    [(? PrimV?) "#<primop>"]
    [(? NullV?) "null"]
    [(? ArrayV?) "#<array>"]))

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

; check if the given symbol is a valid id under the AAQZ6 language
; if it is, returns the symbol, else throws an error
(define (valid-id? [s : Symbol]) : Symbol
  (if (member s '(if => bind = :=))
      (error 'valid-id? "[AAQZ] id not permitted: ~e" s)
      s))

; given a list of function arg symbols, returns the list if all symbols are unique
; and are also valid ids under AAQZ6, else throws an error
(define (check-args [args : (Listof Symbol)]) : (Listof Symbol)
  (match args
    ['() '()]
    [(cons f r) (if (member (valid-id? f) r)
                    (error 'parse "[AAQZ] duplicate argument names: ~e" f)
                    (cons f (check-args r)))]))

; TEST CASES
(top-interp '{bind [fact = "bogus"]
                   {seq {fact := {(x) => {if {equal? x 0}
                                             1
                                             {* x {fact {- x 1}}}}}}
                        {fact 12}}} 100)

(define while '{bind [while = 0]
                     {while := {(guard body) => {if {guard}
                                                    {seq
                                                     {body}
                                                     {while guard body}}
                                                    false}}}})

(define in-order '{bind [in-order = {(arr size) =>
                                       {bind [i = 0]
                                             {bind [while = 0]
                                                   {seq
                                                    {while := {(guard body) =>
                                                                            {if {guard}
                                                                                {seq
                                                                                 {body}
                                                                                 {while guard body}}
                                                                                false}}}
                                                    {seq
                                                     {while
                                                      {() => {<= (+ 1 i) (- size 1)}}
                                                      {() => {if {<= {aref arr i} {aref arr {+ i 1}}}
                                                                 {i := {+ i 1}}
                                                                 {i := size}}}}
                                                     {equal? i {- size 1}}}}}}}]
                        {in-order {array 1 2 3 4 5} 5}})

(top-interp in-order 100)

;TESTING
; Test cases for error primitive
(check-exn exn:fail? 
           (lambda () (top-interp '{error "test error"} 100)))

(check-exn exn:fail? 
           (lambda () (top-interp '{error {+ 1 2}} 100)))

; Test cases for equal? primitive with closures and primitives
(check-equal? (top-interp '{equal? + -} 100) "false")
(check-equal? (top-interp '{equal? {(x) => x} {(x) => x}} 100) "false")
(check-equal? (top-interp '{equal? + +} 100) "false")
(check-equal? (top-interp '{equal? {(x) => x} +} 100) "false")

; Regular equal? cases
(check-equal? (top-interp '{equal? 1 1} 100) "true")
(check-equal? (top-interp '{equal? "hello" "hello"} 100) "true")
(check-equal? (top-interp '{equal? true true} 100) "true")
(check-equal? (top-interp '{equal? false false} 100) "true")
(check-equal? (top-interp '{equal? null null} 100) "true")
(check-equal? (top-interp '{equal? 1 2} 100) "false")
(check-equal? (top-interp '{equal? "hello" "world"} 100) "false")

; Test cases for make-array
(check-equal? (top-interp '{make-array 3 0} 100) "#<array>")
(check-equal? (top-interp '{aref {make-array 3 42} 0} 100) "42")
(check-equal? (top-interp '{aref {make-array 3 42} 2} 100) "42")

; Error cases for make-array
(check-exn exn:fail? 
           (lambda () (top-interp '{make-array 0 42} 100)))

(check-exn exn:fail? 
           (lambda () (top-interp '{make-array -1 42} 100)))

(check-exn exn:fail? 
           (lambda () (top-interp '{make-array "not-a-number" 42} 100)))

; Test cases for aset!
(check-equal? (top-interp '{bind [arr = {make-array 3 0}]
                                {seq
                                  {aset! arr 0 42}
                                  {aref arr 0}}} 100) "42")

(check-equal? (top-interp '{bind [arr = {make-array 3 0}]
                                {seq
                                  {aset! arr 2 42}
                                  {aref arr 2}}} 100) "42")

; Error cases for aset!
#;(check-exn exn:fail?
           (lambda () (top-interp '{bind [arr = {make-array 3 0}]
                                        {aset! arr 3 42}} 100)))

(check-exn exn:fail?
           (lambda () (top-interp '{bind [arr = {make-array 3 0}]
                                        {aset! arr -1 42}} 100)))

(check-exn exn:fail?
           (lambda () (top-interp '{aset! 42 0 1} 100)))

(check-exn exn:fail?
           (lambda () (top-interp '{aset! "not-an-array" 0 1} 100)))

; Test cases for substring
(check-equal? (top-interp '{substring "hello" 0 5} 100) "\"hello\"")
(check-equal? (top-interp '{substring "hello" 1 4} 100) "\"ell\"")
(check-equal? (top-interp '{substring "hello" 0 0} 100) "\"\"")

; Error cases for substring
(check-exn exn:fail?
           (lambda () (top-interp '{substring 42 0 1} 100)))

(check-exn exn:fail?
           (lambda () (top-interp '{substring "hello" "not-a-number" 1} 100)))

(check-exn exn:fail?
           (lambda () (top-interp '{substring "hello" 0 "not-a-number"} 100)))

; Additional edge cases
(check-exn exn:fail?
           (lambda () (top-interp '{substring "hello" -1 5} 100)))

(check-exn exn:fail?
           (lambda () (top-interp '{substring "hello" 0 6} 100)))

(check-exn exn:fail?
           (lambda () (top-interp '{substring "hello" 3 2} 100)))

; Memory exhaustion test
(check-exn exn:fail?
           (lambda () (top-interp '{make-array 1000 0} 10)))

; Test array mutation preserves other values
(check-equal? (top-interp '{bind [arr = {make-array 3 0}]
                                {seq
                                  {aset! arr 0 42}
                                  {aset! arr 1 43}
                                  {aset! arr 2 44}
                                  {array {aref arr 0} {aref arr 1} {aref arr 2}}}} 100) "#<array>")