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