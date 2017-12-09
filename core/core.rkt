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
(module s racket
  (provide (rename-out [structt struct]))
  (define-syntax-rule (structt x ...)
    (struct x ... #:transparent)))
(require 's)
;--------------------------racket部分结束--------------------------
(provide mayberead mustread)
(struct reads (x r))
(define (mayberead s)
  (let ([x (readc (string->list s))])
    (and
     x
     (null? (reads-r x))
     (list (reads-x x)))))
(define (mustread s) (car (mayberead s)))
(define (readc xs)
  (or (read-comment xs)
      (read-boolean xs)
      (read-macro xs)
      (read-list xs)
      (read-char xs)
      ;(read-str xs)
      (read-quote xs)
      (read-space xs)
      (read-number xs)
      (read-symbol xs)))
(define (read-comment xs)
  (and (eq? (car xs) #\;)
       (%read-comment (cdr xs))))
(define (%read-comment xs)
  (if (eq? (car xs) #\newline)
      (readc (cdr xs))
      (%read-comment (cdr xs))))
(define (read-boolean xs)
  (and (eq? (car xs) #\#)
       (let ([nxs (cdr xs)])
         (or (and (eq? (car nxs) #\t) (reads #t (cdr nxs)))
             (and (eq? (car nxs) #\f) (reads #f (cdr nxs)))))))
(define (mk-read-xs b e f)
  (define (readxs xs)
    (and (eq? (car xs) b)
         (let ([x (%readxs (cdr xs))])
           (and x (reads (f (reads-x x)) (reads-r x))))))
  (define (%readxs xs)
    (if (eq? (car xs) e)
        (reads '() (cdr xs))
        (let ([x (readc xs)])
          (and x (let ([rs (skip-space (reads-r x) %readxs)])
                   (and rs
                        (reads (cons (reads-x x) (reads-x rs)) (reads-r rs))))))))
  readxs)
(define read-list (mk-read-xs #\( #\) (λ (xs) xs)))
(define read-macro (mk-read-xs #\{ #\} (λ (xs) (cons '! xs))))
(define (read-char xs)
  (and (eq? (car xs) #\#)
       (let ([nxs (cdr xs)])
         (and (eq? (car nxs) #\\)
              (let ([nnxs (cdr nxs)])
                (reads (car nnxs) (cdr nnxs)))))))
(define (read-quote xs)
  (and (eq? (car xs) #\')
       (let ([x (readc (cdr xs))])
         (and x (reads (list '! 'quote (reads-x x)) (reads-r x))))))
(define (space? x)
  (or (eq? x #\space) (eq? x #\tab) (eq? x #\return) (eq? x #\newline)))
(define (delimiters? x)
  (or (space? x) (eq? x #\#) (eq? x #\() (eq? x #\)) (eq? x #\{) (eq? x #\}) (eq? x #\") (eq? x #\,) (eq? x #\') (eq? x #\`) (eq? x #\;)))
(define (read-space xs)
  (let ([x (car xs)])
    (and (space? x)
         (readc (cdr xs)))))
(define (skip-space xs f)
  (let ([x (car xs)])
    (if (space? x)
        (skip-space (cdr xs) f)
        (f xs))))
(define (read-symbol xs)
  (let ([x (%read-symbol xs)])
    (and x
         (reads (string->symbol (list->string (reads-x x))) (reads-r x)))))
(define (%read-symbol xs)
  (and
   (not (null? xs))
   (not (delimiters? (car xs)))
   (let ([n (%read-symbol (cdr xs))])
     (if n
         (reads (cons (car xs) (reads-x n)) (reads-r n))
         (reads (list (car xs)) (cdr xs))))))
(define (n? x)
  (or (eq? x #\0) (eq? x #\1) (eq? x #\2) (eq? x #\3) (eq? x #\4) (eq? x #\5) (eq? x #\6) (eq? x #\7) (eq? x #\8) (eq? x #\9)))
(define (read-number xs)
  (let ([x (%read-number xs)])
    (and x
         (reads (string->number (list->string (reads-x x))) (reads-r x)))))
(define (%read-number xs)
  (if (eq? (car xs) #\.)
      (let ([x (%%read-number (cdr xs))])
        (and x
             (reads (cons (car xs) (reads-x x)) (reads-r x))))
      (and (n? (car xs))
           (let ([n (%read-number (cdr xs))])
             (if n
                 (reads (cons (car xs) (reads-x n)) (reads-r n))
                 (reads (list (car xs)) (cdr xs)))))))
(define (%%read-number xs)
  (and (n? (car xs))
       (let ([n (%%read-number (cdr xs))])
         (if n
             (reads (cons (car xs) (reads-x n)) (reads-r n))
             (reads (list (car xs)) (cdr xs))))))

;----------read结束-----------------------------------------------

(define (succ x) (+ 1 x))
(define (pred x) (- x 1))
(define (undelay x f)
  (cond
    [(delay+src? x) (undelay (delay+src-d x) f)]
    [(promise? x) (if (promise-forced? x)
                      (undelay (force x) f)
                      (delay (undelay (force x) f)))]
    [else (f x)]))
(define (delay-map f xs)
  (undelay
   xs
   (λ (xs)
     (if (null? xs)
         '()
         (cons (f (car xs)) (delay-map f (cdr xs)))))))
(define (undelay-list xs f)
  (if (null? xs)
      (f '())
      (undelay
       (car xs)
       (λ (x)
         (undelay-list
          (cdr xs)
          (λ (d)
            (f (cons x d))))))))
(define (unstream xs f)
  (undelay
   xs
   (λ (xs)
     (if (null? xs)
         (f '())
         (unstream
          (cdr xs)
          (λ (d)
            (f (cons (car xs) d))))))))
(define (unlazy++ xs f) (unstream xs (λ (xs) (undelay-list xs f))))
(define (undelayN n less xs f)
  (if (zero? n)
      (f '() xs)
      (undelay
       xs
       (λ (xs)
         (if (null? xs)
             (less)
             (undelayN
              (pred n)
              less
              (cdr xs)
              (λ (d more)
                (f (cons (car xs) d) more))))))))
(define (force+ x)
  (if (promise? x)
      (force+ (force x))
      x))
(define (force* x)
  (let ([x (force+ x)])
    (cond
      [(pair? x) (cons (force* (car x)) (force* (cdr x)))]
      [else x])))

; f : [Any] -> Any ; n : Nat
(struct λn (exp n f))
; f : [Any] * Stream Any -> Any ; n : Pos
(struct λ... (exp n f))
; f : Env * [Exp] -> Any ; n : Nat
(struct macro-n (exp n f))
; f : Env * [Any] * Stream Any -> Any ; n : Pos
(struct macro... (exp n f))

(struct data (xs))
(struct delay+src (env x d))

(define newenv hasheq)
(define env-set hash-set)
(define (env-get e s f) (hash-ref e s f))

; U 'undefined 'syntax * Any * [Exp * Map] * CompileErr
(struct compile-error (t f xs))
(define undefinederr 'undefined)
(define syntaxerr 'syntax)

; Any * Any * Stream Any * String -> TypeError
(struct type-error (f at parm i))

(define (_!_) (error "!!!")) ; 临时

(define (EVAL env x)
  (delay
    (undelay
     x
     (λ (x)
       (delay+src
        env x
        (cond
          [(pair? x)
           (undelay
            (car x)
            (λ (a)
              (cond
                [(eq? a '!)
                 (undelay
                  (cdr x)
                  (λ (d)
                    (APPLYmacro env (EVAL env (car d)) (cdr d))))]
                [else (APPLY (EVAL env a) (delay-map (λ (x) (EVAL env x)) (cdr x)))])))]
          [(symbol? x)
           (if (eq? x '_G)
               (env-get genv '_G
                        (_!_))
               (env-get env x
                        (λ () (raise (compile-error undefined 'eval (list (cons x env)))))))]
          [else x]))))))
(define (APPLY f xs)
  (undelay
   f
   (λ (f)
     (cond
       [(λn? f)
        (undelayN (λn-n f) _!_ xs
                  (λ (xs more)
                    (undelay
                     more
                     (λ (m)
                       (if (null? m)
                           ((λn-f f) xs)
                           (_!_))))))]
       [(λ...? f)
        (undelayN (λ...-n f) _!_ xs
                  (λ (xs more)
                    ((λ...-f f) xs more)))]
       [else (_!_)]))))
(define (APPLYmacro env m xs)
  (undelay
   f
   (λ (f)
     (cond
       [(macro-n? f)
        (undelayN (macro-n-n f) _!_ xs
                  (λ (xs more)
                    (undelay
                     more
                     (λ (m)
                       (if (null? m)
                           ((macro-n-f f) env xs)
                           (_!_))))))]
       [(macro...? f)
        (undelayN (macro...-n f) _!_ xs
                  (λ (xs more)
                    ((macro...-f f) env xs more)))]
       [else (_!_)]))))