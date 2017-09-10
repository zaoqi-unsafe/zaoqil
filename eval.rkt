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

#| Env = Hash Symbol Any |#

#| Symbol → Exp → Func |#
(struct func (arg body env))

#| Func → Macro |#
(struct macro (v))

#| (a ... → b) → Primitive  |#
(struct eprimitive (v))

(define (eeval env code) (delay (%eval env code)))

(define rlist-nil (λ (rs) rs))
(define (rlist-cons x xs) (λ (rs) (xs (cons x rs))))
(define (run-rlist xs) (xs '()))

(define ((lazyf f) . args)
  (let loop ([xs args] [rs rlist-nil])
    (cond
      [(null? xs) (apply f (run-rlist rs))]
      [(promise? (car xs)) (delay (loop (cons (force (car xs)) (cdr xs)) rs))]
      [else (loop (cdr xs)) (rlist-cons (car xs) rs)])))

(define-syntax-rule (define-lazy (f arg ...) body ...)
  (define f (lazyf (λ (arg ...) body ...))))

(define (unlazy x f)
  (if (promise? x)
      (delay (unlazy (force x) f))
      (f x)))

(define-lazy (%lazymap f xs)
  (if (null? xs)
      '()
      (unlazy xs (λ (xs)
                   (cons (f (car xs)) (%lazymap f (cdr xs)))))))

(define (lazymap f xs) (%lazymap (lazyf f) xs))

(define (eapply env f args)
  (unlazy f (λ (f)
  (cond
    [(eprimitive? f) ((eprimitive-v f) env args)]
    [(macro? f) (eeval (eapply env (macro-v f) (lazymap (λ (x) (cons 'quote x)) args)))]
    [else
     (let ([arg (func-arg f)] [body (func-body f)] [e (func-env f)])
       (unlazy args
               (λ (as)
                 (let ([v (eeval
                           (hash-set e arg (eeval env (car as)))
                           body)])
                   (unlazy (cdr as)
                           (λ (d)
                             (if (null? d)
                                 v
                                 (eapply env v d))))))))]))))

(define (%eval) (error))
