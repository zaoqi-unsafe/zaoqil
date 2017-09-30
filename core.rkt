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

(define-syntax-rule (file->sexp f)
  (include/reader
   f
   (λ (source-name in)
     (let ([x (read in)])
       (if (eof-object? x)
           eof
           (datum->syntax #f (list 'quote x)))))))
(define true #t)
(define false #f)

(define (succ x) (+ 1 x))
(define (pred x) (- x 1))

(define (_!_) (error '_!_))

(define (force+ x)
  (if (promise? x)
      (force+ (force x))
      x))

(define (unlazy x f)
  (if (promise? x)
      (delay (unlazy (force x) f))
      (f x)))

(define (unlazy* n xs f)
  (unlazy
   xs
   (λ (xs)
     (if (zero? n)
         (f '() xs)
         (if (pair? xs)
             (unlazy*
              (pred n)
              (cdr xs)
              (λ (d rs)
                (f (cons (car xs) d) rs)))
             (_!_))))))

(define (unlazy... xs f)
  (if (null? xs)
      (f '())
      (unlazy
       (car xs)
       (λ (a)
         (unlazy...
          (cdr xs)
          (λ (d)
            (f (cons a d))))))))

(define env hasheq)
(define envset hash-set)
(define envget hash-ref)

; Nat → (Env → [Exp] → Any) → Prim
(struct prim (n f))
(define (prim-apply f env xs g)
  (unlazy* (prim-n f) xs (λ (xs rs) (g rs ((prim-f f) env xs)))))
(define (primm n f) (prim n (λ (env xs) (apply f (cons env xs)))))
(define (primf n f) (prim n (λ (env xs) (apply f (map (λ (x) (eeval env x)) xs)))))
(define (primp n f)
  (prim
   n
   (λ (env xs)
     (unlazy...
      (map (λ (x) (eeval env x)) xs)
      (λ (as)
        (apply f as))))))

; (Any → Any) → Func
(struct func (v))
; Func → Macro
(struct macro (v))

(define (from-racket-value x)
  (cond
    [(promise? x) (delay (from-racket-value (force x)))]
    ;需Fix
    [else x]))

(define (to-racket-value x)
  (let ([x (force+ x)])
    (cond
      [(pair? x) (cons (to-racket-value (car x)) (to-racket-value (cdr x)))]
      [(func? x) (λ (v) (to-racket-value ((func-v x) (from-racket-value v))))];需Fix
      [else x])))

(define (f? x) (or (func? x) (macro? x) (prim? x)))

; Env → Exp → Any
(define (eeval env x) (delay (%eval env x)))
(define (%eval env x)
  (unlazy
   x
   (λ (x)
     (cond
       [(symbol? x) (envget env x (λ () (_!_)))]
       [(pair? x) (aapply env (eeval env (car x)) (cdr x))]
       [else x]))))
; Env → Any → Exp → Any
(define (aapply env f xs)
  (unlazy
   f
   (λ (f)
     (unlazy
      xs
      (λ (xs)
        (cond
          [(func? f)
           (if (pair? xs)
               (unlazy
                ((func-v f) (eeval env (car xs)))
                (λ (r)
                  (if (f? r)
                      (aapply env r (cdr xs))
                      (unlazy
                       (cdr xs)
                       (λ (d)
                         (if (null? d)
                             r
                             (_!_)))))))
               (_!_))]
          [(prim? f)
           (prim-apply f env xs
                       (λ (rs r)
                         (unlazy
                          rs
                          (λ (rs)
                            (if (null? rs)
                                r
                                (aapply env r rs))))))]
          [else (_!_)]))))))

(define genv
  (env 'λ (primm
           2
           (λ (env s v)
             (unlazy
              s
              (λ (s)
                (if (symbol? s)
                    (func (λ (x) (eeval (envset env s x) v)))
                    (_!_))))))
       'cons (primf 2 cons)
       'car (primp 2 car)
       'cdr (primp 2 cdr)
       'true true
       'false false
       'boolean? (primp 1 boolean?)
       'pair? (primp 1 pair?)
       'symbol? (primp 1 symbol?)
       '+ (primp 2 +)
       '- (primp 2 -)
       '* (primp 2 *)
       '/ (primp 2 /)
       '> (primp 2 >)
       '< (primp 2 <)
       '>= (primp 2 >=)
       '=< (primp 2 <=)
       '= (primp 2 =)))

(define (ceval x) (to-racket-value (eeval genv x)))
