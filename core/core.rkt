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
(define-syntax-rule (delay-force x) (delay (force x)))
(define (with-exception-handler handler thunk)
  (with-handlers ([(λ (x) #t) handler]) (thunk)))
(module s racket
  (provide (rename-out [structt struct]))
  (define-syntax-rule (structt x ...)
    (struct x ... #:transparent)))
(require 's)

(struct undefined (t id x))
(struct UnDeF ())
(define UNDEF (UnDeF))
(define UNDEF? UnDeF?)

(define (unlazy u x f)
  (cond
   [(promise? x)
    (if (promise-forced? x)
        (unlazy u (force x) f)
        (delay (unlazy u (force x) f)))]
   [(undefined? x) (undefined (undefined-t x) (undefined-id x) (u (undefined-x x)))]
   [else (f x)]))
(define (unlazy2list xs u f)
  (unlazy
   xs
   u
   (λ (xs)
     (if (null? xs)
         (f '())
         (unlazy2list
          (cdr xs)
          (λ (d) (u (cons (car xs) d)))
          (λ (d) (f (cons (car xs) d))))))))
(define (unlazy2pairs xs u f) ; u接近[Any] -> Any, f : [Pairof NotPromise Any] -> Any
  (unlazy
   xs
   u
   (λ (xs)
     (if (null? xs)
         (f '())
         (unlazy
          (car xs)
          (λ (a) (u (cons a (cdr xs))))
          (λ (a)
            (unlazy
             (cdr xs)
             (λ (d) (u (cons a d)))
             (λ (d)
               (unlazy2pairs
                (cdr d)
                (λ (dd) (u (cons a (cons (car d) dd))))
                (λ (ps) (f (cons (cons a (car d)) ps))))))))))))