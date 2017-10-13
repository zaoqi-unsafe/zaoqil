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
(require "zaoqil-core.rkt")
(require rackunit)

(define-syntax-rule (show x)
  (let ([p (open-output-string)])
    (write x p)
    (get-output-string p)))

(define-syntax-rule (e x y) (check-equal? (core (quote x)) y (show (quote x))))

(e 'true 'true)
(e true #t)
(e (cons 0 0) (cons 0 0))
(e (car ((cons 'a) 'b)) 'a)
(e (list ((+ 1) 2) 0) '(3 0))
(e (: (record x (+ 0 0)) x) 0)
(e (: (record f (λ... xs xs)) f 'a) '(a))
(e (((open (record f (λ... xs xs))) f) 'a) '(a))
(e (or #t #f) #t)
(e (and #f (: (record x x) x)) #f)
(e (and (: (record x x) x) #f) #f)
(e (= (record x 0 y x) (record y x x 0)) true)
(e (require io (open io (return 'a))) 'a)
(e (require prelude/io (open prelude/io (>> (putstrln "hello") (putstrln "world")))) '())
(e ((λ...macro xs (list 'quote xs)) (+ 1 1) (+ 2 2)) '((+ 1 1) (+ 2 2)))
(e (list? "str") #t)
(e (let (x 0 y x) (+ y 1)) 1)
(e (car (: listmonad mplus (: (record x x) x) (list 0))) 0)

(load-file 'mk "mk.core")
(e (open mk ((call/fresh (λ v1 (call/fresh (λ v2 (== v1 v2))))) empty-state)) 0)
