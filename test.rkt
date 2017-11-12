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

(define-syntax-rule (e x y)
  (check-equal?
   (call-with-exception-handler (λ (v) (writeln v) v) (λ () (core (quote x))))
   y
   (show (quote x))))

(e true #t)
(e (cons 0 1) '(0 . 1))
(e ((cons 0) 1) '(0 . 1))
(e (pair? ((cons 1) 2)) #t)
(e ((! λ1 x x) 0) 0)
(e (list 1 2 45 7) '(1 2 45 7))
(e (! open (! record x (! quote a) y x) y) 'a)
(e (! : (! record x (! quote a) y x) y) 'a)
(e (! record-has? (! record x 0) x) #t)
(e (! : (! record-set (! record) x 0) x) 0)
(e (! : (! record-set (! record x 1) x 0) x) 0)
(e (choice2 (! : (! record x x) x) 0 (! λ1 x (! λ1 y x))) 0)
(e (! (! f... env xs xs) a b) '(a b))
(e (! (! macro (x) (list (! quote !) (! quote quote) x)) a) 'a)
(check-equal? (mustread "{record x 0}") '(! record x 0))
(check-equal? (mustread "'a") '(! quote a))
(check-equal? (mustread "( 1 2 3        4      )") '(1 2 3 4))
(check-equal? (mustread "#\\a") #\a)
