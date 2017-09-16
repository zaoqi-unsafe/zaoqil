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

#| Symbol → Exp → Env → Func |#
(struct func (arg body env))

#| Env → Exp → DelayE |#
(struct delaye ([env #:mutable] exp))

(define forceem (make-weak-hasheq))

(define (forcee x)
  (hash-ref forceem x
            (λ ()
              (let ([v (%forcee x)])
                (hash-set! forceem x v)
                v))))

(define (%forcee x) (eeval (delaye-env x) (delaye-exp x)))

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
                                (hash-set e arg (eeval env (car as)))
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
       [(symbol? e) (hash-ref env e)]
       [(pair? e) (eapply env (%eval env (car e)) (cdr e))]
       [(delaye? e) (forcee e)]
       [else e]))))

(define global-env (hash))

#| Symbol → (Env → Exp → b) → Void |#
(define (%define-primitive s x)
  (set! global-env (hash-set global-env s (eprimitive x))))

(define-syntax-rule (define-primitive (f env args) body ...)
  (%define-primitive (quote f)
                     (λ (env args)
                       body ...)))

(define-primitive (quote env args)
  (unlazy
   args
   (λ (args)
     (car args))))

(define (mp xs)
  (let loop ([xs xs] [ps '()])
    (if (null? xs)
        ps
        (loop (cddr xs) (cons (cons (car xs) (cadr xs)) ps)))))

#| Env → [(Symbol,Exp)] → Env |#
(define (%mkenv env ps)
  (if (null? ps)
      env
      (let ([p (car ps)])
        (%mkenv (hash-set env (car p) (delaye 0 (cdr p))) (cdr ps)))))
(define (mkenv env ps)
  (let ([e (%mkenv env ps)])
    (for ([p ps])
      (set-delaye-env! (hash-ref e (car p)) e))
    e))

#| Set Symbol → Env → Record |#
(struct record (ss env))

(define-primitive (λ env args)
  (unlazy-list
   args
   (λ (args)
     (func (car args) (cadr args) env))))

(define-primitive (record env args)
  (unlazy-list
   args
   (λ (args)
     (let ([ps (mp args)])
       (let ([ss (map car ps)] [e (mkenv env ps)])
         (record ss e))))))

(define-syntax-rule (define-primitive-f (f env args) body ...)
  (define-primitive (f env a)
    (let ([a2 (lazymap (λ (x) (eeval env x)) a)])
      (unlazy-list
       a2
       (λ (args)
         body ...)))))

(define-primitive-f (open env args) (error))
