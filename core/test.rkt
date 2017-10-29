#lang racket
;;  Copyright (C) 2017  Zaoqi

;;  This program is free software: you can redistribute it and/or modify
;;  it under the terms of the GNU Affero General Public License as published
;;  by the Free Software Foundation, either version 3 of the License, or
;;  (at your option) any later version.

;;  This program is distributed in the hope that it will be useful,
;;  but WITHOUT ANY WARRANTY; without even the implied warranty of
;;  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;;  GNU Affero General Public License for more details.

;;  You should have received a copy of the GNU Affero General Public License
;;  along with this program.  If not, see <http://www.gnu.org/licenses/>.
(require "core.rkt")
(require rackunit)

(define-syntax-rule (show x)
  (let ([p (open-output-string)])
    (write x p)
    (get-output-string p)))

(define-syntax-rule (e x y) (check-equal? (call-with-exception-handler (λ (v) (writeln v) v) (λ () (core (quote x)))) y (show (quote x))))

(e ((cons 1) 2) (cons 1 2))
(e 'cons 'cons)
(e ((if #t 0) 1) 0)
(e (open (record a 0 c (cons a b) b 1) (car c)) 0)
(e (: (record b a a 0) b) 0)
(e (record-has? (record b b) b) #t)
(e (: (record-set (record b b) b 1) b) 1)
(e (=/2 (record b 0 a 1) (record a 1 b 0)) #t)
(e ((λ x x) (cons 'a 'b)) (cons 'a 'b))
(e (((λ... xs) xs) 0 1 2 3) (list 0 1 2 3))
(e (cond
     false 0
     false 2
     else 1) 1)
(e (choice2 (: (record a a) a) 0 (λ x (λ y x))) 0)
