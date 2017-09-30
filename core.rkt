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

(define env hasheq)
(define envset hash-set)
(define envget hash-ref)

; Nat → (Env → ... → Any) → Prim
(struct prim (n f))
(define (prim-apply f env xs g)
  (unlazy* (prim-n f) xs (λ (xs rs) (g rs (apply (prim-f f) (cons env xs))))))
; (Any → Any) → Func
(struct func (v))
; Func → Macro
(struct macro (v))

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
                  (if (func? r)
                      (aapply env r (cdr xs))
                      r)))
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
