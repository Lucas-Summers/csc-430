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
    
    [(cons 'println (list (StringV s)))
     (begin
       (displayln s)
       (BoolV #t))]

    [(cons 'read-str '())
     (begin
       (printf "> ")
       (match (read-line)
         [(? string? s) (StringV s)]
         [EOF (error 'interp "[AAQZ] unexpected EOF for read-str")]))]

    [(cons 'read-num '())
       (begin
         (printf "> ")
         (match (read-line)
           [(? string? in) 
            (match (string->number in)
              [(? real? n) (NumV n)]
              [else (error 'interp "[AAQZ] invalid input for read-num")])]
           [EOF (error 'interp "[AAQZ] unexpected EOF for read-num")]))]

    [(cons 'seq (list _ ... x)) (cast x Value)] ; cast must succeed...

    [(cons '++ (list x y ...))
     (StringV (apply string-append
                     (map convert-to-str
                          (cast (cons x y) (Listof Value)))))] ; cast must succeed...
    
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
    
    [other (error 'interp "[AAQZ] wrong arity or unsupported operation: ~e" op)]))

(define (convert-to-str [v : Value]) : String
  (match v
    [(NumV n) (number->string n)]
    [(StringV s) s]
    [(BoolV b) (match b
                 [#f "false"]
                 [#t "true"])]))

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

; Example program: Hangman in AAQZ5
(define example-program
  '{bind
    [empty = 0]
    {bind
     [empty? = {(x) => {equal? x empty}}]
     [cons = {(f r)
              =>
              {(key)
               =>
               {if {equal? key 0}
                   f
                   r}}}]
     [first = {(pair) => {pair 0}}]
     [rest =  {(pair) => {pair 1}}]
     {bind
      [member? = {(self l x)
                  =>
                  {if {empty? l}
                      false
                      {if {equal? x {first l}}
                          true
                          {self self {rest l} x}}}}]
      [print = {(self l delim)
                =>
                {if {empty? l}
                    ""
                    {++ {first l} delim {self self {rest l} delim} delim}}}]
      {bind 
       [word = {cons "r" {cons "a" {cons "c" {cons "k" {cons "e" {cons "t" empty}}}}}}] 
       [max-attempts = 10]
       [display-word = {(self g w)
                        =>
                        {if {empty? w}
                            ""
                            {if {member? member? g {first w}}
                                {++ {first w} {self self g {rest w}}}
                                {++ "_" {self self g {rest w}}}}}}]
       [guess = {(self new g)
                 =>
                 {if {member? member? g new}
                     {seq
                      {println {++ "You already guessed the letter: " new}}
                      {println {++ "Guessed Letters: " (print print g " ")}}
                      {println "Enter a new letter:"}
                      {self self {read-str} g}}
                     {cons new g}}}]
       {bind
        [play = {(self attempts guessed)
                 =>
                 {if {equal? attempts max-attempts}
                     {println {++ "Ran out of attempts! The word was: " (print print word "")}}
                     {if {equal? (display-word display-word guessed word) (print print word "")}
                         {println {++ "Congrats! You guessed the word: " (print print word "")}}
                         {seq
                          {println {++ "Attempts Remaining: " {- max-attempts attempts}}}
                          {println {++ "Current Word: " (display-word display-word guessed word)}}
                          {println {++ "Guessed Letters: " (print print guessed " ")}}
                          {println "Enter a new letter:"}
                          {self self {+ 1 attempts} {guess guess {read-str} guessed}}
                          }}}}]
        {seq
         {println "Let's play HANGMAN!"}
         {play play 0 empty}}
        }}}}})

; Sample run:
(top-interp example-program)

#|
Let's play HANGMAN!
Attempts Remaining: 10
Current Word: ______
Guessed Letters: 
Enter a new letter:
r
Attempts Remaining: 9
Current Word: r_____
Guessed Letters: r  
Enter a new letter:
a
Attempts Remaining: 8
Current Word: ra____
Guessed Letters: a r   
Enter a new letter:
t
Attempts Remaining: 7
Current Word: ra___t
Guessed Letters: t a r    
Enter a new letter:
f
Attempts Remaining: 6
Current Word: ra___t
Guessed Letters: f t a r     
Enter a new letter:
t
You already guessed the letter: t
Guessed Letters: f t a r     
Enter a new letter:
e
Attempts Remaining: 5
Current Word: ra__et
Guessed Letters: e f t a r      
Enter a new letter:
c
Attempts Remaining: 4
Current Word: rac_et
Guessed Letters: c e f t a r       
Enter a new letter:
r
You already guessed the letter: r
Guessed Letters: c e f t a r       
Enter a new letter:
x
Attempts Remaining: 3
Current Word: rac_et
Guessed Letters: x c e f t a r        
Enter a new letter:
z
Attempts Remaining: 2
Current Word: rac_et
Guessed Letters: z x c e f t a r         
Enter a new letter:
k
Congrats! You guessed the word: racket
|#