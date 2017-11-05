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
(provide core)
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
(define (force* x)
  (let ([x (force+ x)])
    (cond
      [(pair? x) (cons (force* (car x)) (force* (cdr x)))]
      [else x])))
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
(define (unlazyn n less xs f)
  (if (zero? n)
      (f xs '())
      (unlazy
       xs
       (λ (xs)
         (if (null? xs)
             (less)
             (unlazyn
              n
              less
              (cdr xs)
              (λ (more d)
                (f more (cons (car xs) d)))))))))

; U 'undefined 'syntax -> Symbol -> [Env * Exp] -> CompileErr
(struct compile-error (t f xs))
(define undefined 'undefined)
(define syntaxerr 'syntax)
(define (err t f xs) (raise (compile-error t f xs)))

; Env -> String -> Stream Any -> String -> TypeError
(struct type-error (env at f parm i))

; String → Nat → [U Symbol (Promise Hash) Hash] → At
(struct at (file line ss))
(define (at+ x s) (at (at-file x) (at-line x) (cons s (at-ss x))))

(struct env (at x))
(define (hash->env h) (env (at "" 0 (list h)) h))
(define (newenv . xs) (hash->env (apply hasheq xs)))
(define (env-set e s x) (env (env-at e) (hash-set (env-x e) s x)))
(define (env-get e s f) (hash-ref (env-x e) s f))
(define (env-at+ e x) (env (at+ (env-at e) x) (env-x e)))

; f : Any -> Any
(struct lam1 (exp f))
; f : Stream Any -> Any
(struct lam... (exp f))
; n : Nat
; f : Env -> Exp -> ... -> Any
(struct f-n (exp n f))
; f : Env -> Stream Exp -> Any
(struct f... (exp f))

(define (EVAL env x)
  (delay
    (unlazy
     x
     (λ (x)
       (cond
         [(pair? x)
          (unlazy
           (car x)
           (λ (xa)
             (cond
               [(eq? xa 'G)
                (unlazy
                 (cdr x)
                 (λ (xd)
                   (EVAL genv (car xd))))]
               [(eq? xa '!)
                (unlazy
                 (cdr x)
                 (λ (xd)
                   (APPLYmacro env (car xd) (cdr xd))))]
               [else (APPLY (EVAL env xa) (lmap (λ (x) (EVAL env x)) (cdr x)))])))]
         [(symbol? x)
          (env-get env x
                   (λ () (raise (compile-error undefined 'eval (list (cons env x))))))]
         [(string? x) (string->list x)]
         [else x])))))

(define (APPLY f xs) (%APPLY f xs (cons f xs)))
(define (%APPLY f xs parm)
  (unlazy
   f
   (λ (f)
     (cond
       [(lam1? f)
        (unlazy
         xs
         (λ (xs)
           (if (pair? xs)
               (unlazy
                ((lam1-f f) (car xs))
                (λ (r)
                  (if (lam...? r)
                      (%APPLY r (cdr xs) parm)
                      (unlazy
                       (cdr xs)
                       (λ (xsd)
                         (cond
                           [(null? xsd) r]
                           [(lam1? r) (%APPLY r xsd parm)]
                           [else
                            (raise (type-error (env-at+ genv 'apply) "" parm "参数太多"))]))))))
               (raise (type-error (env-at+ genv 'apply) "" parm "参数太少")))))]
       [(lam...? f) ((lam...-f f) xs)]
       [else (raise (type-error (env-at+ genv 'apply) "" parm "不是函数"))]))))
(define (APPLYmacro env f xs) (%APPLYmacro env f xs (cons env (cons f xs))))
(define (%APPLYmacro env f xs parm)
  (unlazy
   f
   (λ (f)
     (cond
       [(f-n? f)
        (unlazyn
         (f-n-n f)
         (λ () (raise (type-error (env-at+ genv '!) "" parm "参数太少")))
         xs
         (λ (more xs)
           (if (null? more)
               (apply (f-n-f f) (cons env xs))
               (APPLY (apply (f-n-f f) (cons env xs)) more))))] ; BUG APPLY raise内容不正确
       [(f...? f) ((f...-f f) env xs)]
       [else (raise (type-error (env-at+ genv '!) "" parm "不是宏"))]))))

(define (prim-f-n s n f) (f-n (list 'G s) n f))
(define (prim-f... s f) (f... (list 'G s) f))
(define (%prim-n exp n f)
  (if (zero? n)
      (f '())
      (lam1 exp
            (λ (x)
              (%prim-n (list exp (list 'quote x))
                       (pred n)
                       (λ (xs) (f (cons x xs))))))))
(define (prim-n s n f)
  (%prim-n (list 'G s)
           n
           (λ (xs) (apply f xs))))

(define genv
  (newenv
   'true #t
   'false #f
   'cons (prim-n 'cons 2 cons)
   ))

(define (torkt x)
  (let ([x (force* x)])
    (cond
      [(and (pair? x) (list? x) (andmap char? x)) (list->string x)]
      [else x])))
(define (core x) (torkt (EVAL genv x)))
