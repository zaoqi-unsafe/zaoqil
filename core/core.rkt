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
(define (with-exception-handler handler thunk)
  (with-handlers ([(λ (x) #t) handler]) (thunk)))
(module s racket
  (provide (rename-out [structt struct]))
  (define-syntax-rule (structt x ...)
    (struct x ... #:transparent)))
(require 's)
(define-syntax-rule (delay-force x) (delay (force x)))

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
(define (unlazylist xs f)
  (unlazy
   xs
   (λ (xs)
     (if (null? xs)
         (f '())
         (unlazylist
          (cdr xs)
          (λ (d)
            (f (cons (car xs) d))))))))


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

(struct func (env s exp))
; Symbol -> (Any -> Any) -> Prim
(struct prim (s f))
(struct func... (env s exp))
(struct prim... (s f))
(struct f (env s es exp))
(struct pri (s f))
(struct f... (env s es exp))
; Symbol -> (Env -> [Exp] -> Any) -> Pri...
(struct pri... (s f))

(define (func*? x) (or (func? x) (prim? x)))
(define (apply-func* f x)
  (if (func? f)
      (EVAL (env-set (func-env f) (func-s f) x) (func-exp f))
      ((prim-f f) x)))
(define (func...*? x) (or (func...? x) (prim...? x)))
(define (apply-func...* f xs)
  (if (func...? f)
      (EVAL (env-set (func...-env f) (func...-s f) xs) (func...-exp f))
      ((prim...-f f) xs)))
(define (f*? x) (or (f? x) (pri? x)))
(define (apply-f* f env x)
  (if (f? f)
      (EVAL (env-set (env-set (f-env f) (f-s f) x) (f-es f) env)
            (f-exp f))
      ((pri-f f) env x)))
(define (f...*? x) (or (f...? x) (pri...? x)))
(define (apply-f...* f env x)
  (if (f...? f)
      (EVAL (env-set (env-set (f...-env f) (f...-s f) x) (f...-es f) env)
            (f...-exp f))
      ((pri...-f f) env x)))

(define (f-? x) (or (f*? x) (func*? x)))
(define (apply-f- f env x)
  (if (func*? f)
      (apply-func* f (EVAL env x))
      (apply-f* f env x)))
(define (f...-? x) (or (func...*? x) (f...*? x)))
(define (apply-f...- f env xs)
  (if (func...*? f)
      (apply-func...* f (lmap (λ (x) (EVAL env x)) xs))
      (apply-f...* f env xs)))

(define EVAL
  (memroizeeq
   (λ (env x)
     (delay
       (unlazy
        x
        (λ (x)
          (cond
            [(pair? x) (APPLY env (EVAL env (car x)) (cdr x))]
            [(symbol? x)
             (env-get env x
                      (λ () (raise (compile-error undefined 'eval (list (cons env x))))))]
            [else x])))))))
(define (APPLY env f xs)
  (unlazy
   f
   (λ (f)
     (cond
       [(f-? f)
        (unlazy
         xs
         (λ (xs)
           (if (pair? xs)
               (unlazy
                (cdr xs)
                (λ (d)
                  (if (null? d)
                      (apply-f- f env (car xs))
                      (APPLY env (apply-f- f env (car xs)) d))))
               (raise (type-error env "" 'apply (list f xs) "参数太少")))))]
       [(f...-? f) (apply-f...- f env xs)]
       [else (raise (type-error env "" 'apply (list f xs) "不是函数"))]))))

(define (prim1 s f) (prim s (λ (x) (unlazy x f))))

(define null-env (newenv))

(define (%funcpack n f)
  (if (zero? n)
      (f '())
      (let ([s (gensym)])
        (list 'λ s (%funcpack (pred n) (λ (xs) (f (cons s xs))))))))
(define (funcpack n x)
  (delay-force (EVAL genv (%funcpack n (λ (xs) (cons x xs))))))
(define (prim...+ s f)
  (prim... s (λ (xs) (unlazylist xs f))))
(define (primn n s f) (funcpack n (prim...+ s (λ (xs) (apply f xs)))))

(define genv
  (newenv
   'pair? (prim 'pair? (λ (x) (unlazy x pair?)))
   'cons (primn 2 'cons cons)
   'car (prim1 'car car)
   'cdr (prim1 'cdr cdr)
   'λ (pri... 'λ
              (λ (env xs)
                (unlazylist xs
                            (λ (xs)
                              (apply (λ (s x)
                                       (func env s x)) xs)))))
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
