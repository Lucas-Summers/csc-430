#lang typed/racket
(require typed/rackunit)

(define-type ExprC (U NumC BinopC IdC AppC))

(struct NumC ([n : Real]) #:transparent)
(struct BinopC ([op : Symbol] [l : ExprC] [r : ExprC]) #:transparent)
(define ops (make-immutable-hash
             (list
              (cons '+ +)
              (cons '* *)
              (cons '/ /)
              (cons '- -))))
(struct IdC ([s : Symbol]) #:transparent)
(struct AppC ([fun : Symbol] [args : (Listof ExprC)]) #:transparent)

(struct FundefC ([name : Symbol] [args : (Listof Symbol)] [body : ExprC]) #:transparent)

; parse the given program into an AST
(define (parse [s : Sexp]) : ExprC
  (match s
    [(? real? n) (NumC n)]
    [(list (? symbol? op) l r) (cond
                     [(hash-has-key? ops op) (BinopC op (parse l) (parse r))]
                     [else (AppC op (list (parse l) (parse r)))])]
    [(? symbol? s) (IdC s)]
    [(list (? symbol? f) a ...) (AppC f (map parse a))]
    [other (error 'parse "AAQZ: syntax error, got ~e" other)]))

(define (parse-fundef [s : Sexp]) : FundefC
  (match s
    [(list 'def (? symbol? name) (list (list (? symbol? args) ...) '=> (list body ...)))
     (FundefC name (cast args (Listof Symbol)) (parse body))]
    [other (error 'parse-fundef "AAQZ: invalid function definition ~e" other)]))

(define (parse-prog [s : Sexp]) : (Listof FundefC)
  (match s
    ['() '()]
    [(cons (list f ...) rst) (cons (parse-fundef f) (parse-prog rst))]
    [other (error 'parse-prog "AAQZ: not a function definition ~e" other)]))

(define (subst [what : ExprC] [for : Symbol] [in : ExprC]) : ExprC
  (match in
    [(NumC n) in]
    [(IdC s) (cond
               [(symbol=? s for) what]
               [else in])]
    [(AppC f a) (AppC f (subst what for a))]
    [(BinopC op l r) (BinopC op (subst what for l) (subst what for r))]))

(define (get-fundef [n : Symbol] [funs : (Listof FundefC)]) : FundefC
  (match funs
    ['() (error 'get-fundef "AAQZ: reference to undefined function ~e" n)]
    [(cons f r) (if (equal? n (FundefC-name f)) f (get-fundef n r))]))

(define (interp [expr : ExprC] [funs : (Listof FundefC)]) : Real
  (match expr
    [(NumC n) n]
    [(BinopC op l r) ((hash-ref ops op (lambda () (error 'interp "AAQZ: undefined operator ~e" op)))
                       (interp l funs) (interp r funs))]
    [(IdC s) (error 'interp "AAQZ: unbound identifier ~e" s)]
    [(AppC f a) (define fd (get-fundef f funs))
                (define substituted (foldl (lambda ([arg : Symbol] [body : ExprC])
                                             (subst a arg body))
                                             (FundefC-body fd) (FundefC-args fd)))
                (interp substituted funs)]))

;(interp (parse '{double 2}) (list (parse-fundef '{def double {(x) => {+ x x}}})))
(interp (parse '{sum 2 3 4}) (list (parse-fundef '{def sum {(x y z) => {+ x {+ y z}}}})))
    
(define (interp-fns [funs : (Listof FundefC)]) : Real
  (define out
    (for ([f funs] #:when (equal? (FundefC-name f) 'main))
      (interp (FundefC-body f) funs)))
  (if (real? out) out (error 'interp-fns "AAQZ: no main function provided")))

(define (top-interp [fun-sexps : Sexp]) : Real
  (interp-fns (parse-prog fun-sexps)))