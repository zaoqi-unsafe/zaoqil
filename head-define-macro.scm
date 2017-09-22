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

(define true #t)
(define false #f)

(define-macro (unlazy* ps e)
  (if (null? ps)
      e
      `(unlazy ,(cadar ps) (λ (,(caar ps)) (unlazy* ,(cdr ps) ,e)))))

(define-macro (λprimitive env args body)
  `(eprimitive
   (λ (,env args0)
     (unlazy-list
      args0
      (λ (,args)
        ,body))))

(define-macro (define-primitive fea body)
  `(global-env-define
   (quote ,(car fea))
   (λprimitive ,(cadr fea) ,(caddr fea) ,body)))

(define-macro (define-primitive-f fxs e)
  `(global-env-define
   (quote ,(car fxs))
   (eeval
    global-env
    (%define-primitive-f ,(cdr fxs) ,(cdr fxs) ,e))))

(define-macro (%define-primitive-f ss xs e)
  (if (null? ss)
      `(list (λprimitive
            env
            args
            (unify ,xs args
                   (let ,(map (λ (x) `[,x (eeval env ,x)]) xs)
                     ,e))) ,@(map (λ (x) `(quote ,x)) xs))
      `(list 'λ (quote ,(car ss)) (%define-primitive-f ,(cdr ss) ,xs ,e))))

(define-macro (unify xs ys e)
  (if (null? xs)
      e
      `(let ([,(car xs) (car ,ys)])
         (unify ,(cdr xs) (cdr ,ys) ,e))))

(define-macro (define-primitive-f-unlazy fxs e)
  `(define-primitive-f ,fxs
    (unlazy* ,(map (λ (x) (list x x)) (cdr fxs)) ,e)))

(define-macro (prim fxs)
  `(define-primitive-f-unlazy ,fxs ,fxs))

(define (readfile f) (read (open-input-file f)))

