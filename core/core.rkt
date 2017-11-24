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
(define (zsplit-at xs n) (let-values ([(h t) (split-at xs n)]) (cons h t)))

(define (succ x) (+ 1 x))
(define (pred x) (- x 1))

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

(define newenv hasheq)
(define env-set hash-set)
(define env-get hash-ref)
(define-syntax-rule (_!_) (error "_|_")) ; BUG

; e = 表达式, f : [Any] -> Any, n : Nat
(struct λn (e n f))
; f : [Any] -> [Any] -> Any, n : PosInt
(struct λn... (e n f))
; f : Env -> [Exp] -> Any, n : Nat
(struct Fn (e n f))
; f : Env -> [Exp] -> [Exp] -> Any, n : PosInt
(struct Fn... (e n f))

(define (EVAL env x)
  (unlazy
   x
   (λ (x) (list '! '(! _G chenv) env x))
   (λ (x)
     (cond
      [(pair? x)
       (unlazy2list
        x
        (λ (xs) (list '! '(! _G chenv) env xs))
        (λ (xs)
          (unlazy
           (car xs)
           (λ (a) (list '! '(! _G chenv) env (cons a (cdr xs))))
           (λ (a)
             (cond
               [(eq? a '!) (APPLYmacro env (EVAL env (cadr xs)) (cddr xs))]
               [else (APPLY (EVAL env a) (map (λ (x) (EVAL env x)) (cdr xs)))])))))]
      [(symbol? x) (if (eq? x '_G)
                       (env-get genv '_G)
                       (env-get env x))]
      [(string? x) (string->list x)]
      [else x]))))
(define (APPLYmacro env f xs)
  (unlazy
   f
   (λ (f) (list '! '(! _G chenv) env (cons '! (cons f xs))))
   (λ (f)
     (cond
       [(Fn? f) (let ([sr (zsplit-at xs (Fn-n f))])
                  (if (null? (cdr sr))
                  ((Fn-f f) env (car sr))
                  (_!_)))]
       [(Fn...? f) (let ([sr (zsplit-at xs (Fn...-n f))])
                     ((Fn...-f f) env (car sr) (cdr sr)))]
       [else (_!_)]))))
(define (QUOTE x) (list '! '(! _G quote) x))
(define (APPLY f xs)
  (unlazy
   f
   (λ (f) (list '! '(! _G chenv) env (cons f (map QUOTE xs))))
   (λ (f)
     (cond
       [(λn? f) (let ([sr (zsplit-at xs (λn-n f))])
                  (if (null? (cdr sr))
                  ((λn-f f) (car sr))
                  (_!_)))]
       [(λn...? f) (let ([sr (zsplit-at xs (λn...-n f))])
                     ((λn...-f f) (car sr) (cdr sr)))]
       [else (_!_)]))))
(define genv
  (newenv
   'true #t
   'false #f
   ))
  
