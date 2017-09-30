#lang racket
(require "core.rkt")
(require rackunit)

(define-syntax-rule (show x)
  (let ([p (open-output-string)])
    (write x p)
    (get-output-string p)))

(define-syntax-rule (e x y) (check-equal? (ceval (quote x)) y (show (quote x))))

(e ((+ 1) 2) 3)
(e (map (+ 1) '(1 2 3)) '(2 3 4))
(e (if true 0 not-a-value) 0)
(e (= (record x 0 y x) (record y x x 0)) true)
(e (open (record x 1 y x) (+ x y)) 2)
(e (record x 1 y z z x) #hasheq((x . 1) (y . 1) (z . 1)))
(e (record x 1 y (: _< x)) #hasheq((x . 1) (y . 1)))
