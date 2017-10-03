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

(define prelude-sexp
  '(record
    module record
    id (λ x x)
    or (λ x (λ y (choice2 x y (λ x (λ y (if x #t y))))))
    and (λ x (λ y (choice2 x y (λ x (λ y (if x y #f))))))
    list? (λ xs (or (null? xs) (list? (cdr xs))))
    map (λ f (λ xs
               (if (null? xs)
                   ()
                   (cons (f (car xs)) (map f (cdr xs))))))
    filter (λ f (λ xs
                  (if (null? xs)
                      ()
                      (if (f (car xs))
                          (cons (car xs) (filter f (cdr xs)))
                          (filter f (cdr xs))))))
    succ (+ 1)
    pred (- 1)
    prelude/io (require io
                        (module
                            >> (λ x (λ y (>>= x (λ (i) y))))
                          putstrln (λ s (>> (: io putstr s) (: io newline)))))
    ))

(define (succ x) (+ 1 x))
(define (pred x) (- x 1))

(define (unlazy x f)
  (if (promise? x)
      (delay (unlazy (force x) f))
      (f x)))

; U undefined notfunction → Symbol → Exp → Env
(struct compile-error (t f x e) #:transparent)
(define undefined 'undefined)
(define notfunction 'notfunction)
(define noarg 'noarg)
(define toomanyarg 'toomanyarg)
(struct left (x))
; Nothing = Left ()
(define (err t f x e) (raise (compile-error t f x e)))

; Hash Symbol Any → [U (File : String) Symbol (Line : Nat)] → Envr
(struct envr (x at))
(define (newenv . xs) (envr (apply hasheq xs) '('_)))
(define (env-set e s x) (envr (hash-set (envr-x e) s x) (envr-at e)))
(define (env-has? e s) (hash-has-key? (envr-x e) s))
(define (env-ref e s t) (hash-ref (envr-x e) s t))

; Env → Exp → Any
(struct func (v))
; Env → Stream Exp → Any
(struct func... (v))

(define (eeval env x)
  (delay
    (unlazy
     x
     (λ (x)
       (cond
         [(symbol? x) (env-ref env x (λ () (err undefined 'eval x env)))]
         [(pair? x) (aapply env (eeval env (car x)) (cdr x))]
         [else x])))))
; Env → Any → Stream Exp → Any
(define (aapply env f xs)
  (unlazy
   f
   (λ (f)
     (cond
       [(func? f)
        (unlazy
         xs
         (λ (xs)
           (if (pair? xs)
               (unlazy
                ((func-v f) env (car xs))
                (λ (r)
                  (if (func...? r)
                      (aapply env r (cdr xs))
                      (unlazy
                       (cdr xs)
                       (λ (d)
                         (cond
                           [(null? d) r]
                           [(func? r) (aapply env r d)]
                           [else (err toomanyarg 'apply (list f (cons (car xs) d)) env)]))))))
               (err noarg 'apply (list f xs) env))))]
       [(func...? f) ((func...-v f) env xs)]
       [else (err notfunction 'apply (list f xs))]))))


(define (force+ x)
  (if (promise? x)
      (force+ (force x))
      x))

(define (from-racket-value x)
  (cond
    [(promise? x) (delay (from-racket-value (force x)))]
    ;[(procedure? x) (to-func x)]
    ;[(hash? x) (record x)];需修复: 可能不是Hash Symbol Any
    [else x]))

(define (to-racket-value x)
  (let ([x (force+ x)])
    (cond
      [(pair? x) (cons (to-racket-value (car x)) (to-racket-value (cdr x)))]
      ;[(func? x) (from-func x)]
      ;[(func...? x) (from-func... x)]
      ;[(record? x)
      ; (make-immutable-hasheq
      ;  (map (λ (p) (cons (car p) (to-racket-value (cdr p))))
      ;       (hash->list (record-v x))))]
      ;[(io? x) (force+ (runio x to-racket-value))]
      [else x])))

(define (core x) (to-racket-value (eeval genv x)))

(define (makefunc n f)
  (if (zero? n)
      (f '())
      (func (λ (env x)
              (makefunc (pred n) (λ (xs)
                                   (f (cons env (cons x xs)))))))))
(define (pmacro n f) (makefunc n (λ (xs) (apply f xs))))

(define genv
  (newenv
   'true #t
   'false #f
   'quote (pmacro 1 (λ (env x) x))))
