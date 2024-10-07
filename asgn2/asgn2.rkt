; CSC 430 Assignment 2
; By: lsumme01 and mtuman

#lang typed/racket
(require typed/rackunit)

; 2.1
; given the number of attendees at a show, return how much income the attendees produce
(define (total-profit [num_attend : Real]) : Real
  (- (* 5 num_attend) (+ 20 (* 0.5 num_attend))))

(check-equal? (total-profit 0) -20)
(check-equal? (total-profit 5) 2.5)
(check-equal? (total-profit 10) 25.0)
(check-equal? (total-profit 100) 430.0)

; given the radius and height of a cylinder, return the surface area of that cylinder
(define (area-cylinder [r : Real] [h : Real]) : Real
  (* (* r (* 2 pi)) (+ r h)))

(check-equal? (area-cylinder 2 0) (* 8 pi))
(check-equal? (area-cylinder 0 2) 0)
(check-equal? (area-cylinder 3 4) (* 42 pi))
(check-equal? (area-cylinder 1 1) (* 4 pi))

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

; given a food, return true if the food is determined to be delicious
(define (delicious? [f : Food]) : Boolean
  (match f
    [(Blueberry blueness count) (if (and (> blueness 5) (>= count 100)) #t #f)]
    [(Bread hydration) (if (and (>= hydration 0.7) (<= hydration 0.9)) #t #f)]
    [(Banana _) #t]))

(check-false (delicious? (Blueberry 5 100)))
(check-true (delicious? (Blueberry 6 100)))
(check-false (delicious? (Blueberry 6 99)))
(check-false (delicious? (Bread 0.6)))
(check-true (delicious? (Bread 0.7)))
(check-true (delicious? (Bread 0.9)))
(check-false (delicious? (Bread 1)))
(check-true (delicious? (Banana 5)))
(check-true (delicious? (Banana 0)))

; 2.5
; represents a binary tree
(define-type BTree (U Node Leaf))
; represents an internal node of a binary tree
(struct Node ([v : Symbol] [l : BTree] [r : BTree]) #:transparent)
; represents a leaf node of a binary tree
(struct Leaf ([v : Symbol]) #:transparent)

; BTree examples used for testing
(define t1 (Leaf 'a))
(define t2 (Node 'a (Leaf 'b) (Leaf 'c)))
(define t3 (Node 'a (Node 'b (Leaf 'c) (Leaf 'd)) (Node 'e (Leaf 'f) (Leaf 'g))))

; 2.6
; returns a BTree that is the left-right mirror image of the given BTree
(define (mirror [tree : BTree]) : BTree
  (match tree
    [(Leaf v) (Leaf v)]
    [(Node v l r) (Node v (mirror r) (mirror l))]))

(check-equal? (mirror t1) (Leaf 'a))
(check-equal? (mirror t2) (Node 'a (Leaf 'c) (Leaf 'b)))
(check-equal? (mirror t3) (Node 'a (Node 'e (Leaf 'g) (Leaf 'f)) (Node 'b (Leaf 'd) (Leaf 'c))))

; 2.7
; returns a BTree the has only the "left spine" (each right branch is a leaf) of the given BTree
(define (left-spine [tree : BTree]) : BTree
  (match tree
    [(Leaf v) (Leaf v)]
    [(Node v l (Node rv _ _)) (Node v (left-spine l) (Leaf rv))]
    [(Node v l (Leaf rv)) (Node v (left-spine l) (Leaf rv))]))

(check-equal? (left-spine t1) (Leaf 'a))
(check-equal? (left-spine t2) (Node 'a (Leaf 'b) (Leaf 'c)))
(check-equal? (left-spine t3) (Node 'a (Node 'b (Leaf 'c) (Leaf 'd)) (Leaf 'e)))

; 2.8
; returns true if the given symbol is found in at least one of the nodes in the BTree
(define (contains? [tree : BTree] [s : Symbol]) : Boolean
  (match tree
    [(Leaf v) (if (equal? v s) #t #f)]
    [(Node v l r) (if (equal? v s) #t (or (contains? l s) (contains? r s)))]))

(check-true (contains? t1 'a))
(check-false (contains? t1 'b))
(check-true (contains? t2 'a))
(check-false (contains? t2 'd))
(check-true (contains? t3 'e))
(check-true (contains? t3 'f))
(check-false (contains? t3 'h))