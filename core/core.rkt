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
(define (memorize1eq f)
  (let ([m (make-weak-hasheq)])
    (λ (x) (hash-ref m x
                     (λ ()
                       (let ([v (f x)])
                         (hash-set! m x v)
                         v))))))
(define (memroizeeq f)
  (let ([t (memorize1eq (λ (xs) (apply f xs)))])
    (λ xs (t xs))))
(define-syntax-rule (delay-force x) (delay (force x)))
(define (with-exception-handler handler thunk)
  (with-handlers ([(λ (x) #t) handler]) (thunk)))
(module s racket
  (provide (rename-out [structt struct]))
  (define-syntax-rule (structt x ...)
    (struct x ... #:transparent)))
(require 's)

(define (succ x) (+ 1 x))
(define (pred x) (- x 1))
(define (force+ x)
  (if (promise? x)
      (force+ (force x))
      x))
(define (unlazy x f)
  (if (promise? x)
      (if (promise-forced? x)
          (unlazy (force x) f)
          (delay (unlazy (force x) f)))
      (f x)))
(define (lmap f xs)
  (unlazy
   xs
   (λ (xs)
     (if (null? xs)
         '()
         (cons (f (car xs)) (lmap f (cdr xs)))))))
(define (unlazy* xs f)
  (if (null? xs)
      (f '())
      (unlazy
       (car xs)
       (λ (x)
         (unlazy*
          (cdr xs)
          (λ (d)
            (f (cons x d))))))))
;(define (unlazylist xs f)
;  (unlazy
;   xs
;   (λ (xs)
;     (if (null? xs)
;         (f '())
;         (unlazylist
;          (cdr xs)
;          (λ (d)
;            (f (cons (car xs) d))))))))
;(define (%unlazyn n xs f)
;  (if (zero? n)
;      (f '())
;      (unlazy
;       xs
;       (λ (xs)
;         (%unlazyn
;          (pred n)
;          (cdr xs)
;          (λ (d)
;            (f (cons (car xs) d))))))))
;(define (unlazyn* n xs f) (%unlazyn n xs (λ (xs) (λ (xs) (apply f xs)))))
;(define (unlazyn* n xs f) (%unlazyn n xs (λ (xs) (unlazy* xs (λ (xs) (apply f xs))))))

; U 'undefined 'syntax -> Symbol -> [Env * Exp] -> CompileErr
(struct compile-error (t f xs))
(define undefined 'undefined)
(define syntaxerr 'syntax)
(define (err t f xs) (raise (compile-error t f xs)))

; Env -> String -> Symbol -> [Any] -> String -> TypeError
(struct type-error (env at f parm i))

(struct left (x))
; Nothing = Left ()
; False = Nothing

; String → Nat → [U Symbol (Promise Record)] → At
(struct at (file line ss))
(define (at+ x s) (at (at-file x) (at-line x) (cons s (at-ss x))))

(struct env (at x))
(define (newenv . xs)
  (env (at "" 0 '()) (apply hasheq xs)))
(define (env-set e s x) (env (env-at e) (hash-set (env-x e) s x)))
(define (env-get e s f) (hash-ref (env-x e) s f))
(define (env-at+ e x) (env (at+ (env-at e) x) (env-x e)))

(struct func (exp f))
(struct func... (exp f))
(struct f (exp f))
(struct f... (exp f))

(define (lam? x) (or (func? x) (f? x)))
(define (lam...? x) (or (func...? x) (f...? x)))
(define (apply-lam env f x)
  (if (func? f)
      ((func-f f) (EVAL env x))
      ((f-f f) env x)))
(define (apply-lam... env f xs)
  (if (func...? f)
      ((func...-f f) (lmap (λ (v) (EVAL env v)) xs))
      ((f...-f f) env xs)))

(define (EVAL env x)
  (delay
    (unlazy
     x
     (λ (x)
       (cond
         [(pair? x) (APPLY env (EVAL env (car x)) (cdr x))]
         [(symbol? x)
          (env-get env x
                   (λ () (raise (compile-error undefined 'eval (list (cons env x))))))]
         [(string? x) (string->list x)]
         [else x])))))

(define (APPLY env f xs)
  (unlazy
   f
   (λ (f)
     (cond
       [(lam? f)
        (unlazy
         xs
         (λ (xs)
           (if (pair? xs)
               (unlazy
                (cdr xs)
                (λ (d)
                  (if (null? d)
                      (apply-lam env f (car xs))
                      (APPLY env (apply-lam env f (car xs)) d))))
               (raise (type-error env "" 'apply (list f xs) "参数太少")))))]
       [(lam...? f) (apply-lam... env f xs)]
       [else (raise (type-error env "" 'apply (list f xs) "不是函数"))]))))

(define (%prim exp n f)
  (if (zero? n)
      (f '())
      (func exp
            (λ (x)
              (%prim (list exp (list 'quote x))
                     (pred n)
                     (λ (xs)
                       (f (cons x xs))))))))
(define (prim s n f) (%prim s n (λ (xs) (apply f xs))))
(define (prim* s n f) (%prim s n (λ (xs) (unlazy* xs (λ (xs) (apply f xs))))))

(define genv
  (newenv
   'pair? (prim* 'pair? 1 pair?)
   'cons (prim 'cons 2 cons)
   'car (prim* 'car 1 car)
   'cdr (prim* 'cdr 1 cdr)
   ))

(define (to-racket x)
  (let ([x (force+ x)])
    (cond
      [(pair? x) (cons (to-racket (car x)) (to-racket (cdr x)))]
      [else x])))

(define (core x)
  (with-exception-handler
      (λ (x) x)
    (λ () (to-racket (EVAL genv x)))))
