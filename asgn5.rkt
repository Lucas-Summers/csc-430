; Full project implemented
; Muzart Tuman (mtuman) and Lucas Summers (lsumme01)
#lang typed/racket
(require typed/rackunit)

; defines an environment
(define-type Env (Listof Binding))
; defines a binding within an evironment
(struct Binding ([name : Symbol] [val : Value]) #:transparent)
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
(define-type ExprC (U IdC AppC LamC IfC Value))
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
   (Binding 'false (BoolV #f))
   (Binding 'true (BoolV #t))
   (Binding '+ (PrimV '+))
   (Binding '* (PrimV '*))
   (Binding '- (PrimV '-))
   (Binding '/ (PrimV '/))
   (Binding '<= (PrimV '<=))
   (Binding 'equal? (PrimV 'equal?))
   (Binding 'error (PrimV 'error))
   (Binding 'println (PrimV 'println))
   (Binding 'read-num (PrimV 'read-num))
   (Binding 'read-str (PrimV 'read-str))
   (Binding 'seq (PrimV 'seq))
   (Binding '++ (PrimV '++))))

; given an s-expression, combines parsing and evaluation of AAQZ4 to produce a result as a string
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env)))

; parses an s-expression into an AAQZ4 ExprC that can be interpreted
(define (parse [s : Sexp]) : ExprC
  (match s
    [(? real? n) (NumV n)]
    [(? symbol? sym) (IdC (valid-id? sym))]
    [(? string? str) (StringV str)]
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

; interprets an AAQZ4 ExprC given an environment of bindings to produce a Value
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

; performs the AAQZ4 primitive operation corresponding to the given symbol on the
; given list of Values, returning the result as a Value
(define (handle-prims [op : Symbol] [args : (Listof Value)]) : Value
  (match (cons op args)
    [(cons 'true '()) (BoolV #t)]
    [(cons 'false '()) (BoolV #f)]
    [(cons 'error (list x))
     ; cast must succeed...
     (error 'interp "[AAQZ] user-error: ~e" (serialize (cast x Value)))]
    [(cons 'equal? (list x y))
     (match (cons x y)
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

    [(cons 'println (list (StringV s)))
     (begin
       (displayln s)
       (BoolV #t))]

    [(cons 'read-str '())
  (let ([input (read-line)])
    (match input
      [(? string?) (StringV input)]
      [EOF (error 'interp "[AAQZ] unexpected end of input for read-str")]))]

    [(cons 'read-num '())
     (let ([input (read-line)])
       (match input
         [(? string?) 
          (match (string->number input)
            [(and (? real?) num) (NumV num)]
            [else (error 'interp "[AAQZ] invalid input for read-num")])]
         [EOF (error 'interp "[AAQZ] unexpected end of input for read-num")]))]

    [(cons 'seq (list _ ... x))
  (if (null? x)
      (error 'interp "[AAQZ] seq returning a last value which is null")
      (cast x Value))]

    [(cons '++ args)
     (StringV (apply string-append (map serialize (cast args (Listof Value)))))]

    ;; Default case for unsupported operations or arity mismatches
    [other (error 'interp "[AAQZ] wrong arity or unsupported operation: ~e" op)]))


; returns a string that is a readable form of the given Value
(define (serialize [val : Value]) : String
  (match val
    [(NumV n) (format "~v" n)]
    [(BoolV #f) "false"]
    [(BoolV #t) "true"]
    [(StringV s) (format "~v" s)]
    [(? ClosV?) "#<procedure>"]
    [(? PrimV?) "#<primop>"]))

; given a symbol and a Value, creates a Binding to be inserted into an environment
(define (bind [n : Symbol] [v : Value]) : Binding
  (Binding n v))

; for the given environment, finds the Binding with the name corresponding to the given symbol
; and returns the binding's Value, else throws an error
(define (lookup [for : Symbol] [env : Env]) : Value
  (match env
    ['() (error 'lookup "[AAQZ] id out of bounds: ~e" for)]
    [(cons (Binding name val) r) (if (symbol=? for name)
                                     val
                                     (lookup for r))]))

; check if the given symbol is a valid id under the AAQZ4 language
; if it is, returns the symbol, else throws an error
(define (valid-id? [s : Symbol]) : Symbol
  (if (member s '(if => bind =))
      (error 'valid-id? "[AAQZ] id not permitted: ~e" s)
      s))

; given a list of function arg symbols, returns the list if all symbols are unique
; and are also valid ids under AAQZ4, else throws an error
(define (check-args [args : (Listof Symbol)]) : (Listof Symbol)
  (match args
    ['() '()]
    [(cons f r) (if (member (valid-id? f) r)
                    (error 'parse "[AAQZ] duplicate argument names: ~e" f)
                    (cons f (check-args r)))]))

; TEST CASES
; General
(check-equal? (serialize (interp (AppC
                    (LamC '(a b)
                          (AppC (IdC '+) (list (IdC 'a) (IdC 'b))))
                    (list (NumV 10) (NumV 15))) top-env)) "25")

(check-equal? (top-interp '{bind [f = {(x) => {+ x 1}}]
      [y = 7]
      {f y}}) "8")

; recursive test from in class
(check-equal? (top-interp '{bind [fact = {(self n) => {if {<= n 0}
                               1
                               {* n {self self {- n 1}}}}}]
      {fact fact 4}}) "24")

(check-equal? (top-interp '{bind [double = {(x) => {* x 2}}]
      [y = 6]
      {double y}}) "12")

(check-equal? (serialize
               (interp (AppC (LamC '(x)
                                  (AppC (IdC '+) (list (IdC 'x) (NumV 5))))
                             (list (NumV 10))) top-env))
              "15")

(check-equal? (serialize (interp (AppC (IdC '-) (list (NumV 20) (NumV 5))) top-env)) "15")
(check-equal? (serialize (interp (AppC (IdC '*) (list (NumV 3) (NumV 4))) top-env)) "12")
(check-equal? (serialize (interp (parse 'true) top-env)) "true")
(check-equal? (serialize (interp (parse 'false) top-env)) "false")
(check-equal? (serialize (interp (parse "Hello") top-env)) "\"Hello\"")
(check-equal? (serialize (interp (AppC (IdC 'equal?)
                                       (list (IdC 'true) (IdC 'true))) top-env)) "true")
(check-equal? (serialize (interp (AppC (IdC 'equal?)
                                       (list (IdC 'true) (IdC 'false))) top-env)) "false")
(check-equal? (serialize (interp (AppC (IdC 'equal?)
                                       (list (StringV "abc") (StringV "abc"))) top-env)) "true")
(check-equal? (serialize (interp (AppC (IdC 'equal?)
                                       (list (StringV "abc") (StringV "xyz"))) top-env)) "false")
(check-equal? (serialize (interp (AppC (IdC '/) (list (NumV 10) (NumV 2))) top-env)) "5")
(check-equal? (serialize (interp (IfC (IdC 'true) (NumV 1) (NumV 0)) top-env)) "1")
(check-equal? (serialize (ClosV '(x) (AppC (IdC '+) (list (IdC 'x) (NumV 5))) '())) "#<procedure>")
(check-equal? (serialize (PrimV '+)) "#<primop>")

; Handlng primitives
(check-equal? (handle-prims 'true '()) (BoolV #t))
(check-equal? (handle-prims 'false '()) (BoolV #f))
(check-equal? (handle-prims 'equal? (list (NumV 1) (PrimV '-))) (BoolV #f))
(check-equal? (handle-prims 'equal? (list (ClosV '(x) (IdC 'x) '())
                                          (ClosV '(x) (IdC 'x) '()))) (BoolV #f))

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
(check-exn exn:fail? (lambda ()
                       (parse '{"not" 10 #f})))
(check-exn exn:fail? (lambda ()
                       (interp (AppC (IdC 'error) (list (StringV "something wrong"))) top-env)))
(check-exn exn:fail? (lambda () (top-interp '(((e) => (e e)) error))))

; 5, hangman game
#;(define hangman
  '{seq
     {println "Welcome to Hangman!"}
     {define word "racket master"}
     {define guessed-letters {list}}
     {define attempts 6}

     {println {string-append "The word has " (int->string (length word)) " letters."}}
     
     {define all-letters-guessed?
       {lambda (w gl)
         {if (null? w)
             true
             {if (member (car w) gl)
                 {all-letters-guessed? (cdr w) gl}
                 false}}}}
     {define display-word
       {lambda (w gl)
         {if (null? w)
             ""
             {string-append
               (if (member (car w) gl)
                   (car w)
                   "_")
               " "
               {display-word (cdr w) gl}}}}}

     {while (and (> attempts 0)
                 (not {all-letters-guessed? (string->list word) guessed-letters}))
       {seq
         {println "Current word:"}
         {println {display-word (string->list word) guessed-letters}}
         {println "Guess a letter:"}
         {define guess {read-char}}

         {if {member guess guessed-letters}
             {println "You already guessed that letter!"}
             {if {member guess (string->list word)}
                 {seq
                   {println "Good guess!"}
                   {set! guessed-letters (cons guess guessed-letters)}}
                 {seq
                   {println "Incorrect guess."}
                   {set! attempts (- attempts 1)}
                   {println {string-append "You have " (int->string attempts) " attempts left."}}}}}}}

     {if {all-letters-guessed? (string->list word) guessed-letters}
         {println "Congratulations! You've guessed the word!"}
         {println {string-append "Game over! The word was '" word "'."}}})


