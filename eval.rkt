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

#| Symbol → (Env → Exp → b) → Void |#
(define (%define-primitive s x)
  (set! global-env (env-set global-env s (eprimitive x))))

(define-syntax-rule (define-primitive (f env args) body ...)
  (%define-primitive
   (quote f)
   (λ (env args0)
     (unlazy-list
      args0
      (λ (args)
        body ...)))))

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

(define-primitive (open env args)
  (let ([r (car args)] [exp (second args)])
    (unlazy
     (eeval env r)
     (λ (rv)
       (let ([re (record-env rv)] [ss (set->list (record-ss rv))])
         (let loop ([e env] [ss ss])
           (if (null? ss)
               (eeval e exp)
               (let ([s (car ss)])
                 (loop (env-set e s (eeval re s)) (cdr ss))))))))))

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

(define (load f)
  (set!
   global-env
   (record-env
    (force+
     (eeval global-env
            (read (open-input-file f)))))))

(load "prelude.core")
