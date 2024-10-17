; Full project implemented
; Muzart Tuman (mtuman) and Lucas Summers (lsumme01)
#lang typed/racket
(require typed/rackunit)

; defines an expression type
(define-type ExprC (U NumC BinopC Ifleq0?C IdC AppC))
; defines a number (real number)
(struct NumC ([n : Real]) #:transparent)
; defines a binary operator (which uses rackets implementation of +, -, *, and /)
(struct BinopC ([op : Symbol] [l : ExprC] [r : ExprC]) #:transparent)
(define ops (make-immutable-hash
             (list
              (cons '+ +)
              (cons '* *)
              (cons '/ /)
              (cons '- -))))
; defines an "if less than or equal to 0" conditional
(struct Ifleq0?C ([test : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
; defines an identifier
(struct IdC ([s : Symbol]) #:transparent)
; defines a function application
(struct AppC ([fun : Symbol] [args : (Listof ExprC)]) #:transparent)
; defines a function definition
(struct FundefC ([name : Symbol] [args : (Listof Symbol)] [body : ExprC]) #:transparent)

; given an s-expression, combine parsing and evaluation to produced a real number result
(define (top-interp [fun-sexps : Sexp]) : Real
  (interp-fns (parse-prog fun-sexps)))

; given a list of function defs, interpret the function named main
; if main function def isn't provided, throw an error
(define (interp-fns [funs : (Listof FundefC)]) : Real
  (define mainf (filter (lambda ([f : FundefC]) (equal? (FundefC-name f) 'main)) funs))
  (if (empty? mainf)
      (error 'interp-fns "[AAQZ] no main function provided")
      (interp (FundefC-body (first mainf)) funs)))

; parse an s-expression into a list of function defs
(define (parse-prog [s : Sexp]) : (Listof FundefC)
  (match s
    ['() '()]
    [(cons (list f ...) rst) (cons (parse-fundef f) (parse-prog rst))]
    [other (error 'parse-prog "[AAQZ] not a function definition: ~e" other)]))

; parse an s-expression into a function def
(define (parse-fundef [s : Sexp]) : FundefC
  (match s
    [(list 'def (? symbol? name) (list (list (? symbol? args) ...) '=> (list body ...)))
     (FundefC name (check-args (cast args (Listof Symbol))) (parse body))]
    [(list 'def (? symbol? name) (list (list (? symbol? args) ...) '=> body))
     (FundefC name (check-args (cast args (Listof Symbol))) (parse body))]
    [other (error 'parse-fundef "[AAQZ] invalid function definition: ~e" other)]))

; parse an s-expression into an ExprC
(define (parse [s : Sexp]) : ExprC
  (match s
    [(? real? n) (NumC n)]
    [(list (? symbol? op) l r) (cond
                                 [(hash-has-key? ops op) (BinopC op (parse l) (parse r))]
                                 [else (AppC op (list (parse l) (parse r)))])]
    [(list 'ifleq0? test then else) (Ifleq0?C (parse test) (parse then) (parse else))]
    [(? symbol? s) (IdC s)]
    [(list (? symbol? f) a ...) (AppC f (map parse a))]
    [other (error 'parse "[AAQZ] syntax error: ~e" other)]))

; interpret an ExprC using the list of function defs to resolve applications
(define (interp [expr : ExprC] [funs : (Listof FundefC)]) : Real
  (match expr
    [(NumC n) n]
    [(BinopC op l r) ((hash-ref ops op (lambda () (error 'interp "[AAQZ] undefined operator: ~e" op)))
                                       (interp l funs) (interp r funs))]
    [(Ifleq0?C test then else) (if (<= (interp test funs) 0)
                                   (interp then funs)
                                   (interp else funs))]
    [(IdC s) (error 'interp "[AAQZ] unbound identifier: ~e" s)]
    [(AppC f a) (define fd (get-fundef f funs))
                (if (equal? (length (FundefC-args fd)) (length a))
                    (interp (foldl (lambda ([param : Symbol] [arg : ExprC] [body : ExprC])
                                           (subst (NumC (interp arg funs)) param body))
                                   (FundefC-body fd) (FundefC-args fd) a)
                            funs)
                    (error 'interp "[AAQZ] wrong arity: ~e" f))]))

; recursively replaces symbol 'for' in the ExprC 'in' with the ExprC 'what'
(define (subst [what : ExprC] [for : Symbol] [in : ExprC]) : ExprC
  (match in
    [(NumC n) in]
    [(IdC s) (cond
               [(symbol=? s for) what]
               [else in])]
    [(AppC f a) (AppC f (map (lambda ([exp : ExprC]) (subst what for exp)) a))]
    [(BinopC op l r) (BinopC op (subst what for l)
                                (subst what for r))]
    [(Ifleq0?C test then else) (Ifleq0?C (subst what for test)
                                         (subst what for then)
                                         (subst what for else))]))

; given a list of args, return the list of all arg Symbols are unique, else throw an error
(define (check-args [args : (Listof Symbol)]) : (Listof Symbol)
  (match args
    ['() '()]
    [(cons f r) (if (member f r)
                    (error 'parse-fundef "[AAQZ] duplicate argument names: ~e" f)
                    (cons f (check-args r)))]))

; given a symbol n and a list of function defs, return the def whose name matches n
; else, throw an error
(define (get-fundef [n : Symbol] [funs : (Listof FundefC)]) : FundefC
  (match funs
    ['() (error 'interp "[AAQZ] reference to undefined function: ~e" n)]
    [(cons f r) (if (equal? n (FundefC-name f)) f (get-fundef n r))]))


; TEST CASES (need more)
(check-equal? (top-interp '{{def f {(x y) => {+ x y}}}
                            {def main {() => {f (+ 1 2) 2}}}})
              5)
(check-equal? (top-interp '{{def f {() => 5}}
                            {def main {() => {+ {f} {f}}}}})
              10)
(check-equal? (top-interp '{{def f {(x) => x}}
                            {def main {() => {ifleq0? {f -1} {* 1 2} {f {/ 1 2}}}}}})
              2)
(check-equal? (top-interp '{{def r {(b) => b}}
                            {def f {(x) => (r {+ x 1})}}
                            {def main {() => {+ {f 1} {f 1}}}}})
              4)
; Tests for NumC and BinopC
(check-equal? (top-interp '{{def main {() => {+ 2 3}}}}) 5)
(check-equal? (top-interp '{{def main {() => {* 3 4}}}}) 12)
(check-equal? (top-interp '{{def main {() => {/ 6 2}}}}) 3)
(check-equal? (top-interp '{{def main {() => {- 10 3}}}}) 7)

; Tests for AppC
(check-equal? (top-interp '{{def f {(x) => {+ x 1}}}
                           {def main {() => {f 5}}}}) 6)
(check-equal? (top-interp '{{def f {(x y) => {* x y}}}
                           {def main {() => {f 3 4}}}}) 12)

; Tests for parse-fundef
(check-equal? (parse-fundef '(def f ((x y) => (+ x y))))
              (FundefC 'f (list 'x 'y) (BinopC '+ (IdC 'x) (IdC 'y))))
(check-equal? (parse-fundef '(def f ((x) => (* x x))))
              (FundefC 'f (list 'x) (BinopC '* (IdC 'x) (IdC 'x))))
(check-equal? (parse-fundef '(def f (() => 42)))
              (FundefC 'f '() (NumC 42)))
(check-equal? (parse-fundef '(def f ((x) => (list x (+ x 1)))))
              (FundefC 'f (list 'x) (AppC 'list (list (IdC 'x) (BinopC '+ (IdC 'x) (NumC 1))))))
(check-exn exn:fail?
           (lambda ()
             (parse-fundef '(def f ((x x) => (+ x y))))))
(check-exn exn:fail?
           (lambda ()
             (parse-fundef '(def f => (+ x y)))))

; Tests for subst
(check-equal? (subst (NumC 10) 'x (IdC 'x))
              (NumC 10))
(check-equal? (subst (NumC 10) 'x (BinopC '+ (IdC 'x) (NumC 5)))
              (BinopC '+ (NumC 10) (NumC 5)))
(check-equal? (subst (NumC 10) 'y (IdC 'x))
              (IdC 'x))
(check-equal? (subst (NumC 10) 'x (Ifleq0?C (IdC 'x) (NumC 1) (NumC 2)))
              (Ifleq0?C (NumC 10) (NumC 1) (NumC 2)))

; Tests for get-fundef
(define funs (list (FundefC 'f '() (NumC 5)) (FundefC 'g '() (NumC 10))))
(define funs2 (list (FundefC 'a '() (NumC 1)) (FundefC 'b '() (NumC 2))))
(check-equal? (get-fundef 'f funs)(FundefC 'f '() (NumC 5)))
(check-equal? (get-fundef 'g funs)(FundefC 'g '() (NumC 10)))
(check-equal? (get-fundef 'a funs2)(FundefC 'a '() (NumC 1)))

; Tests for Ifleq0?C
(check-equal? (top-interp '{{def main {() => {ifleq0? -1 10 5}}}}) 10)
(check-equal? (top-interp '{{def main {() => {ifleq0? 1 10 5}}}}) 5)
(check-equal? (top-interp '{{def main {() => {ifleq0? 1 10 5}}}}) 5)

; Error tests
(check-exn exn:fail?
           (lambda ()
             (top-interp '{{def main {() => {@ 1 2}}}})))
(check-exn exn:fail?
           (lambda ()
             (top-interp '{{def f {(x) => x}}
                          {def main {() => {f 1 2}}}})))
(check-exn exn:fail?
           (lambda ()
             (top-interp '{{def main {() => {+ x 1}}}})))
(check-exn exn:fail?
           (lambda ()
             (parse-prog '((1 2 3)))))
(check-exn exn:fail?
           (lambda ()
             (parse-prog '(+ 1 2))))
(check-exn exn:fail?
           (lambda ()
             (parse '(1 2 3) )))
(check-exn exn:fail?
           (lambda ()
             (interp (BinopC '^ (NumC 2) (NumC 3)) '())))
(check-exn exn:fail?
           (lambda ()
             (interp-fns (list (FundefC 'f '() (NumC 5))))))