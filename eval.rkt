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

(provide ceval)

#| Env → Symbol → Any → Env |#
(define env-set hash-set)

#| Env → Symbol → Any |#
(define env-ref hash-ref)

#| Env = Hash Symbol Any |#

#| Symbol → Exp → Env → Func |#
(struct func (arg body env))

#| Env → Exp → DelayE |#
(struct delaye ([env #:mutable] exp))

#| U Any DelayE → DelayE+ |#
(struct delaye+ ([v #:mutable]))

(define (forcee x)
  (let ([v (delaye+-v x)])
    (if (delaye? v)
        (let ([v1 (eeval (delaye-env v) (delaye-exp v))])
          (set-delaye+-v! x v1)
          v1)
        v)))

#| Func → Macro |#
(struct macro (v))

#| (Env → Exp → b) → Primitive  |#
(struct eprimitive (v))

(define (eeval env code) (delay (%eval env code)))

(define rlist-nil (λ (rs) rs))
(define (rlist-cons x xs) (λ (rs) (xs (cons x rs))))
(define (run-rlist xs) (xs '()))

(define (force+ x)
  (if (promise? x)
      (force+ (force x))
      x))

(define (unlazy-list xs f)
  (let loop ([xs xs] [rs rlist-nil])
    (cond
      [(promise? xs) (delay (unlazy-list (force xs) f))]
      [(null? xs) (f (run-rlist rs))]
      [else (loop (cdr xs) (rlist-cons (car xs) rs))])))

(define (unlazy x f)
  (if (promise? x)
      (delay (unlazy (force x) f))
      (f x)))

(define (lazymap f xs)
  (unlazy
   xs
   (λ (xs)
     (if (null? xs)
         '()
         (cons (f (car xs)) (lazymap f (cdr xs)))))))

(define (eapply env f args)
  (delay
    (unlazy
     f
     (λ (f)
       (cond
         [(eprimitive? f) ((eprimitive-v f) env args)]
         [(macro? f) (eeval (eapply env (macro-v f) (lazymap (λ (x) (list 'quote x)) args)))]
         [else
          (let ([arg (func-arg f)] [body (func-body f)] [e (func-env f)])
            (unlazy args
                    (λ (as)
                      (let ([v (eeval
                                (env-set e arg (eeval env (car as)))
                                body)])
                        (unlazy (cdr as)
                                (λ (d)
                                  (if (null? d)
                                      v
                                      (eapply env v d))))))))])))))

(define (%eval env code)
  (unlazy
   code
   (λ (e)
     (cond
       [(symbol? e)
        (let ([x (env-ref env e)])
          (cond
            [(delaye+? x) (forcee x)]
            [else x]))]
       [(pair? e) (eapply env (%eval env (car e)) (cdr e))]
       [(delaye+? e) (forcee e)]
       [else e]))))

(define global-env (hasheq))

(define (global-env-define s x)
  (set! global-env (env-set global-env s x)))

(define-syntax-rule (define-primitive (f env args) body)
  (global-env-define
   (quote f)
   (λprimitive env args body)))

(define-syntax-rule (λprimitive env args body)
  (eprimitive
   (λ (env args0)
     (unlazy-list
      args0
      (λ (args)
        body)))))

(define-primitive (quote env args)
  (car args))

(define (mp xs)
  (let loop ([xs xs] [ps '()])
    (if (null? xs)
        ps
        (unlazy
         (car xs)
         (λ (s)
           (loop (cddr xs) (cons (cons s (cadr xs)) ps)))))))

(define self '_<)

#| Env → [(Symbol,Exp)] → Env |#
(define (%mkenv env ps)
  (if (null? ps)
      env
      (let ([p (car ps)])
        (%mkenv (env-set env (car p) (delaye+ (delaye 0 (cdr p)))) (cdr ps)))))
(define (mkenv env ps)
  (let ([e (env-set (%mkenv env ps) self (delaye+ (void)))])
    (for ([p ps])
      (set-delaye-env! (delaye+-v (env-ref e (car p))) e))
    e))

#| Set Symbol → Env → Record |#
(struct record (ss env))

(define-primitive (λ env args)
  (func (car args) (cadr args) env))

(define-primitive (record env args)
  (let ([ps (mp args)])
    (let ([ss (list->seteq (map car ps))] [e (mkenv env ps)])
      (let ([r (record ss e)])
        (set-delaye+-v! (env-ref e self) r)
        r))))

(define record-hide (seteq self))

#| Env → Record → Env |#
(define (open env rv)
  (let ([re (record-env rv)] [ss (set->list (record-ss rv))])
    (let loop ([e env] [ss ss])
      (if (null? ss)
          e
          (let ([s (car ss)])
            (if (set-member? record-hide s)
                (loop e (cdr ss))
                (loop (env-set e s (eeval re s)) (cdr ss))))))))

(define-primitive (open env args)
  (let ([r (car args)] [exp (second args)])
    (unlazy
     (eeval env r)
     (λ (rv)
       (eeval (open env rv) exp)))))

(define-primitive (macro env args)
  (macro (eeval env (car args))))

(define-primitive (: env args)
  (let ([r (car args)])
    (unlazy* ([s (second args)] [rv (eeval env r)])
             (let ([re (record-env rv)] [ss (record-ss rv)])
               (if (set-member? ss s)
                   (eeval re s)
                   (error "undefined"))))))

(define-primitive (eval env args)
  (eeval env (eeval env (car args))))

(define-syntax unlazy*
  (syntax-rules ()
    [(_ () e) e]
    [(_ ([x v] y ...) e) (unlazy v (λ (x) (unlazy* (y ...) e)))]))

(define-primitive (car env args)
  (unlazy* ([p (eeval env (car args))])
           (car p)))

(define-primitive (cdr env args)
  (unlazy* ([p (eeval env (car args))])
           (cdr p)))

(define-syntax-rule (define-primitive-f (f x ...) e)
  (global-env-define
   (quote f)
   (eeval
    global-env
    (%define-primitive-f (x ...) (x ...) e))))

(define-syntax %define-primitive-f
  (syntax-rules ()
    [(_ () (x ...) e)
     (list (λprimitive
            env
            args
            (unify (x ...) args
                   (let ([x (eeval env x)] ...)
                     e))) (quote x) ...)]
    [(_ (s0 s ...) xs e)
     (list 'λ (quote s0) (%define-primitive-f (s ...) xs e))]))

(define-syntax unify
  (syntax-rules ()
    [(_ () nil e) e]
    [(_ (x0 x ...) ys e)
     (let ([x0 (car ys)])
       (unify (x ...) (cdr ys) e))]))

(define-primitive-f (cons a d) (cons a d))

(define-syntax-rule (define-primitive-f-unlazy (f x ...) e)
  (define-primitive-f (f x ...)
    (unlazy* ([x x] ...) e)))

(define-syntax-rule (prim (f x ...))
  (define-primitive-f-unlazy (f x ...) (f x ...)))

(define (load f)
  (set!
   global-env
   (open
    global-env
    (ceval (read (open-input-file f))))))

(define (force* x)
  (let ([v (force+ x)])
    (cond
      [(pair? v) (cons (force+ (car v)) (force+ (cdr v)))]
      [else v])))

(define (ceval x) (force* (eeval global-env x)))

(global-env-define 't #t)
(global-env-define 'f #f)
(define-primitive-f (if b x y) (unlazy* ([b b]) (if b x y)))
(prim (boolean? x))
(prim (null? x))
(prim (char? x))
(prim (pair? x))
(prim (symbol? x))
(prim (record? x))
(prim (+ x y))
(prim (- x y))
(prim (* x y))
(prim (/ x y))
(prim (not x))
(prim (< x y))
(prim (> x y))
(prim (>= x y))
(define-primitive-f-unlazy (=< x y) (<= x y))
(define-primitive-f-unlazy (= x y) (equal? x y))

(load "prelude.core")
