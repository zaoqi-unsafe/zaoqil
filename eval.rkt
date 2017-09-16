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

(define (%forcee x)
  (unlazy
   (eeval (delaye-env x) (delaye-exp x))
   (λ (x)
     (if (delaye? x)
         (%forcee x)
         x))))

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
       [(symbol? e)
        (let ([x (hash-ref env e)])
          (cond
            [(delaye? x) (forcee x)]
            [else x]))]
       [(pair? e) (eapply env (%eval env (car e)) (cdr e))]
       [(delaye? e) (forcee e)]
       [else e]))))

(define global-env (hasheq))

#| Symbol → (Env → Exp → b) → Void |#
(define (%define-primitive s x)
  (set! global-env (hash-set global-env s (eprimitive x))))

(define-syntax-rule (define-primitive (f env args) body ...)
  (%define-primitive
   (quote f)
   (λ (env args0)
     (unlazy
      args0
      (λ (args)
        body ...)))))

(define-primitive (quote env args)
  (car args))

(define (mp xs)
  (let loop ([xs xs] [ps '()])
    (unlazy* ([xs xs])
             (if (null? xs)
                 ps
                 (unlazy* ([s (car xs)] [d (cdr xs)] [v (car d)] [xs1 (cdr d)])
                          (loop xs1 (cons (cons s v) ps)))))))

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
  (func (car args) (cadr args) env))

(define-primitive (record env args)
  (unlazy* ([ps (mp args)])
    (let ([ss (list->seteq (map car ps))] [e (mkenv env ps)])
      (record ss e))))

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
                 (loop (hash-set e s (eeval re s)) (cdr ss))))))))))

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
