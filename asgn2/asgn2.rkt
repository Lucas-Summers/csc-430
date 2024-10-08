#lang typed/racket
(require typed/rackunit)

; 2.1
; given the number of attendees at a show, return how much income the attendees produce
(define (total-profit [num_attend : Real]) : Real
  (- (* 5 num_attend) (+ 20 (* 0.5 num_attend))))

; given the radius and height of a cylinder, return the surface area of that cylinder
(define (area-cylinder [r : Real] [h : Real]) : Real
  (* (* r (* 2 pi)) (+ r h)))

; 2.2
; represents a food
(define-type Food (U Blueberry Bread Banana))
; Represents a blueberry with blueness in blue-units and count amount of taste
(struct Blueberry ([blueness : Nonnegative-Real] [count : Nonnegative-Integer])
   #:transparent)
; Represents bread with hydration ratio
(struct Bread ([hydration : Nonnegative-Real])
   #:transparent)
; Represents a banana with grams weight
(struct Banana ([grams : Nonnegative-Real])
   #:transparent)

; return true if the given food is determined to be delicious, otherwise false
(define (delicious? [f : Food]) : Boolean
  (match f
    [(Blueberry blueness count) (if (and (> blueness 5) (>= count 100)) #t #f)]
    [(Bread hydration) (if (and (>= hydration 0.7) (<= hydration 0.9)) #t #f)]
    [(Banana _) #t]))

; 2.3
; returns the result of plugging in the given value x for the variable in the given polynomial
(define-type Polynomial (U Linear Quadratic))
(struct Linear ([A : Real] [B : Real]) #:transparent)
(struct Quadratic ([A : Real] [B : Real] [C : Real]) #:transparent)

(define (interp [poly : Polynomial] [x : Real]) : Real
  (match poly
    [(Linear A B) (+ (* A x) B)]
    [(Quadratic A B C) (+ (* A (* x x)) (* B x) C)]))

; 2.4
; returns a new polynomial that represents the given polynomial's derivative
(define (derivative [poly : Polynomial]) : Polynomial
  (match poly
    [(Quadratic A B C) (Linear (* 2 A) B)]
    [(Linear A B) (Linear 0 A)]))

; 2.5
; represents a binary tree
(define-type BTree (U Node Leaf))
; represents an internal node of a binary tree
(struct Node ([v : Symbol] [l : BTree] [r : BTree]) #:transparent)
; represents a leaf node of a binary tree
(struct Leaf () #:transparent)

; 2.6
; returns a new BTree that is the left-right mirror image of the given BTree
(define (mirror [tree : BTree]) : BTree
  (match tree
    [(? Leaf?) (Leaf)]
    [(Node v l r) (Node v (mirror r) (mirror l))]))

; 2.7
; returns a new BTree that only has the "left spine" of the given BTree
; and each right branch is just a leaf
(define (left-spine [tree : BTree]) : BTree
  (match tree
    [(? Leaf?) (Leaf)]
    [(Node v l r) (Node v (left-spine l) (Leaf))]))

; 2.8
; returns true if the given symbol is found in at least one of the nodes in the given BTree
(define (contains? [tree : BTree] [s : Symbol]) : Boolean
  (match tree
    [(? Leaf?) #f]
    [(Node v l r) (if (equal? v s) #t (or (contains? l s) (contains? r s)))]))

; 2.9
; returns a number indicating how many nodes in the given BTree have the given symbol as their value
(define (occurrences [tree : BTree] [s : Symbol]) : Real
  (match tree
    [(? Leaf?) 0]
    [(Node v l r) (+ (if (equal? v s) 1 0) (occurrences l s) (occurrences r s))]))

; 2.10
; accepts a source BTree, a symbol, and a replacement BTree, and returns a new BTree
; where every node of the source tree containing the given symbol is replaced by the replacement tree
(define (subst [src : BTree] [s : Symbol] [replace : BTree]) : BTree
  (match src
    [(? Leaf?) (Leaf)]
    [(Node v l r) (if (equal? v s) replace (Node v (subst l s replace) (subst r s replace)))]))

; 2.11
; returns a list containing the lengths of all the paths from the root to each leaf in the given BTree
(define (all-path-lengths [tree : BTree]) : (Listof Real)
  (define (all-path-lengths-helper [t : BTree] [curr-len : Real]) : (Listof Real)
    (match t
      [(? Leaf?) (list curr-len)]
      [(Node v l r) (append (all-path-lengths-helper l (+ 1 curr-len))
                            (all-path-lengths-helper r (+ 1 curr-len)))]))
  ; apply the recursive helper to the root of the tree with initial path length 0
  (all-path-lengths-helper tree 0))


; ALL TESTS
; 2.1
(check-equal? (total-profit 0) -20)
(check-equal? (total-profit 5) 2.5)
(check-equal? (total-profit 10) 25.0)
(check-equal? (total-profit 100) 430.0)
(check-equal? (area-cylinder 2 0) (* 8 pi))
(check-equal? (area-cylinder 0 2) 0)
(check-equal? (area-cylinder 3 4) (* 42 pi))
(check-equal? (area-cylinder 1 1) (* 4 pi))

; 2.2
(check-false (delicious? (Blueberry 5 100)))
(check-true (delicious? (Blueberry 6 100)))
(check-false (delicious? (Blueberry 6 99)))
(check-false (delicious? (Bread 0.6)))
(check-true (delicious? (Bread 0.7)))
(check-true (delicious? (Bread 0.9)))
(check-false (delicious? (Bread 1)))
(check-true (delicious? (Banana 5)))
(check-true (delicious? (Banana 0)))

; 2.3
(check-equal? (interp (Quadratic 1 3 0) 0) 0)
(check-equal? (interp (Quadratic 2 1 1) 2) 11)
(check-equal? (interp (Quadratic -2 2 -1) 2) -5)
(check-equal? (interp (Linear 0 0) 2) 0)
(check-equal? (interp (Linear 1 0) 0) 0)
(check-equal? (interp (Linear 2 1) 2) 5)
(check-equal? (interp (Linear -2 -1) 1) -3)

; 2.4
(check-equal? (derivative (Quadratic 0 8 1)) (Linear 0 8))
(check-equal? (derivative (Quadratic 4 2 1)) (Linear 8 2))
(check-equal? (derivative (Linear 0 3)) (Linear 0 0))
(check-equal? (derivative (Linear 4 0)) (Linear 0 4))

; BTree examples used for testing
(define t0 (Leaf))
(define t1 (Node 'a (Leaf) (Leaf)))
(define t2 (Node 'a
                 (Node 'b (Leaf) (Leaf))
                 (Node 'c (Leaf) (Leaf))))
(define t3 (Node 'a
                 (Node 'b
                       (Node 'c (Leaf) (Leaf))
                       (Node 'd (Leaf) (Leaf)))
                 (Node 'e
                       (Node 'b (Leaf) (Leaf))
                       (Node 'g (Leaf) (Leaf)))))
; 2.6
(check-equal? (mirror t0) t0)
(check-equal? (mirror t1) t1)
(check-equal? (mirror t2) (Node 'a
                                (Node 'c (Leaf) (Leaf))
                                (Node 'b (Leaf) (Leaf))))
(check-equal? (mirror t3) (Node 'a
                                (Node 'e
                                      (Node 'g (Leaf) (Leaf))
                                      (Node 'b (Leaf) (Leaf)))
                                (Node 'b
                                      (Node 'd (Leaf) (Leaf))
                                      (Node 'c (Leaf) (Leaf)))))
; 2.7
(check-equal? (left-spine t0) t0)
(check-equal? (left-spine t1) t1)
(check-equal? (left-spine t2) (Node 'a (Node 'b (Leaf) (Leaf)) (Leaf)))
(check-equal? (left-spine t3) (Node 'a (Node 'b (Node 'c (Leaf) (Leaf)) (Leaf)) (Leaf)))

; 2.8
(check-false (contains? t0 'a))
(check-true (contains? t1 'a))
(check-false (contains? t1 'b))
(check-true (contains? t2 'a))
(check-false (contains? t2 'd))
(check-true (contains? t3 'e))
(check-false (contains? t3 'h))

; 2.9
(check-equal? (occurrences t0 'a) 0)
(check-equal? (occurrences t1 'a) 1)
(check-equal? (occurrences t1 'b) 0)
(check-equal? (occurrences t3 'b) 2)

; 2.10
(check-equal? (subst t0 'a t1) t0)
(check-equal? (subst t1 'a t2) t2)
(check-equal? (subst t1 'b t2) t1)
(check-equal? (subst t2 'b t1) (Node 'a (Node 'a (Leaf) (Leaf)) (Node 'c (Leaf) (Leaf))))

; 2.11
(check-equal? (all-path-lengths t0) '(0))
(check-equal? (all-path-lengths t1) '(1 1))
(check-equal? (all-path-lengths t2) '(2 2 2 2))
(check-equal? (all-path-lengths t3) '(3 3 3 3 3 3 3 3))