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

(define (area-cylinder [r : Real] [h : Real]) : Real
  (* (* r (* 2 pi)) (+ r h)))

(check-equal? (area-cylinder 2 0) (* 8 pi))
(check-equal? (area-cylinder 0 2) 0)
(check-equal? (area-cylinder 3 4) (* 42 pi))
(check-equal? (area-cylinder 1 1) (* 4 pi))


; 2.2

