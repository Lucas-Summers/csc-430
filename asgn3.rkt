; Full project implemented

#lang typed/racket
(require typed/rackunit)

(define-type ExprC (U NumC BinopC Ifleq0?C IdC AppC))
(struct FundefC ([name : Symbol] [args : (Listof Symbol)] [body : ExprC]) #:transparent)
(struct NumC ([n : Real]) #:transparent)
(struct BinopC ([op : Symbol] [l : ExprC] [r : ExprC]) #:transparent)
(define ops (make-immutable-hash
             (list
              (cons '+ +)
              (cons '* *)
              (cons '/ /)
              (cons '- -))))
(struct Ifleq0?C ([test : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct IdC ([s : Symbol]) #:transparent)
(struct AppC ([fun : Symbol] [args : (Listof ExprC)]) #:transparent)

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

; given a list of args, return the list of all arg Symbols are unique, else throw an error
(define (check-args [args : (Listof Symbol)]) : (Listof Symbol)
  (match args
    ['() '()]
    [(cons f r) (if (member f r)
                    (error 'parse-fundef "[AAQZ] duplicate argument names: ~e" f)
                    (cons f (check-args r)))]))

; parse an s-expression into a function def
(define (parse-fundef [s : Sexp]) : FundefC
  (match s
    [(list 'def (? symbol? name) (list (list (? symbol? args) ...) '=> (list body ...)))
     (FundefC name (check-args (cast args (Listof Symbol))) (parse body))]
    [(list 'def (? symbol? name) (list (list (? symbol? args) ...) '=> body))
     (FundefC name (check-args (cast args (Listof Symbol))) (parse body))]
    [(list 'def (? symbol? name) (list '() '=> (list body ...)))
     (FundefC name '() (parse body))]
    [(list 'def (? symbol? name) (list '() '=> body))
     (FundefC name '() (parse body))]
    [other (error 'parse-fundef "[AAQZ] invalid function definition: ~e" other)]))

; parse an s-expression into a list of function defs
(define (parse-prog [s : Sexp]) : (Listof FundefC)
  (match s
    ['() '()]
    [(cons (list f ...) rst) (cons (parse-fundef f) (parse-prog rst))]
    [other (error 'parse-prog "[AAQZ] not a function definition: ~e" other)]))

; replaces the ExprC 'what' with the ExprC 'for' in the ExprC 'in'
(define (subst [what : ExprC] [for : Symbol] [in : ExprC]) : ExprC
  (match in
    [(NumC n) in]
    [(IdC s) (cond
               [(symbol=? s for) what]
               [else in])]
    [(AppC f a) (AppC f (map (lambda ([exp : ExprC]) subst what for exp) a))]
    [(BinopC op l r) (BinopC op (subst what for l)
                                (subst what for r))]
    [(Ifleq0?C test then else) (Ifleq0?C (subst what for test)
                                         (subst what for then)
                                         (subst what for else))]))

; given a symbol n and a list of function defs, return the def whose name matches n
; else, throw an error
(define (get-fundef [n : Symbol] [funs : (Listof FundefC)]) : FundefC
  (match funs
    ['() (error 'interp "[AAQZ] reference to undefined function: ~e" n)]
    [(cons f r) (if (equal? n (FundefC-name f)) f (get-fundef n r))]))

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
                    (interp (foldl (lambda ([arg : Symbol] [param : ExprC] [body : ExprC])
                                             (subst param arg body))
                                           (FundefC-body fd) (FundefC-args fd) a) funs)
                    (error 'interp "[AAQZ] wrong arity: ~e" (FundefC-name fd)))]))

; given a list of function defs, interpret the function named main
; if main function def isn't found, throw an error
(define (interp-fns [funs : (Listof FundefC)]) : Real
  (define main
    (first (filter (lambda ([f : FundefC]) (equal? (FundefC-name f) 'main)) funs)))
  (if (empty? main)
      (error 'interp-fns "[AAQZ] no main function provided")
      (interp (FundefC-body main) funs)))

; given an s-expression, combine parsing and evaluation
(define (top-interp [fun-sexps : Sexp]) : Real
  (interp-fns (parse-prog fun-sexps)))

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
;(check-exn exn:fail?
;          (lambda ()
;            (parse-fundef '(def f ((x) => (x 1))))))
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
; uncomment to test for [(AppC f a) (AppC f (map (lambda ([exp : ExprC]) subst what for exp) a))]
;;(check-equal? (subst (NumC 10) 'x (AppC 'f (list (IdC 'x))))
;;              (AppC 'f (list (NumC 10))))

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
