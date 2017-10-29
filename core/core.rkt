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
(define (memorize1eq f)
  (let ([m (make-weak-hasheq)])
    (λ (x) (hash-ref m x
                     (λ ()
                       (let ([v (f x)])
                         (hash-set! m x v)
                         v))))))
(define (memroizeeq f)
  (let ([t (memorize1eq (λ (xs) (apply f xs)))])
    (λ xs (t xs))))
(define-syntax-rule (delay-force x) (delay (force x)))
(define (with-exception-handler handler thunk)
  (with-handlers ([(λ (x) #t) handler]) (thunk)))
(module s racket
  (provide (rename-out [structt struct]))
  (define-syntax-rule (structt x ...)
    (struct x ... #:transparent)))
(require 's)

(define (succ x) (+ 1 x))
(define (pred x) (- x 1))
(define (force+ x)
  (if (promise? x)
      (force+ (force x))
      x))
(define (unlazy x f)
  (if (promise? x)
      (if (promise-forced? x)
          (unlazy (force x) f)
          (delay (unlazy (force x) f)))
      (f x)))
(define (lmap f xs)
  (unlazy
   xs
   (λ (xs)
     (if (null? xs)
         '()
         (cons (f (car xs)) (lmap f (cdr xs)))))))
(define (unlazy* xs f)
  (if (null? xs)
      (f '())
      (unlazy
       (car xs)
       (λ (x)
         (unlazy*
          (cdr xs)
          (λ (d)
            (f (cons x d))))))))
(define (unlazylist xs f)
  (unlazy
   xs
   (λ (xs)
     (if (null? xs)
         (f '())
         (unlazylist
          (cdr xs)
          (λ (d)
            (f (cons (car xs) d))))))))
;(define (%unlazyn n xs f)
;  (if (zero? n)
;      (f '())
;      (unlazy
;       xs
;       (λ (xs)
;         (%unlazyn
;          (pred n)
;          (cdr xs)
;          (λ (d)
;            (f (cons (car xs) d))))))))
;(define (unlazyn* n xs f) (%unlazyn n xs (λ (xs) (λ (xs) (apply f xs)))))
;(define (unlazyn* n xs f) (%unlazyn n xs (λ (xs) (unlazy* xs (λ (xs) (apply f xs))))))

; U 'undefined 'syntax -> Symbol -> [Env * Exp] -> CompileErr
(struct compile-error (t f xs))
(define undefined 'undefined)
(define syntaxerr 'syntax)
(define (err t f xs) (raise (compile-error t f xs)))

; Env -> String -> Symbol -> [Any] -> String -> TypeError
(struct type-error (env at f parm i))

; String → Nat → [U Symbol (Promise Hash)] → At
(struct at (file line ss))
(define (at+ x s) (at (at-file x) (at-line x) (cons s (at-ss x))))

(struct env (at x))
(define (newenv . xs)
  (letrec ([r (env (at "" 0 (list (delay r))) (apply hasheq xs))])
    r))
(define (env-set e s x) (env (env-at e) (hash-set (env-x e) s x)))
(define (env-get e s f) (hash-ref (env-x e) s f))
(define (env-at+ e x) (env (at+ (env-at e) x) (env-x e)))

(struct func (exp f))
(struct func... (exp f))
(struct f (exp f))
(struct f... (exp f))

(define (lam? x) (or (func? x) (f? x)))
(define (lam...? x) (or (func...? x) (f...? x)))
(define (apply-lam env f x)
  (if (func? f)
      ((func-f f) (EVAL env x))
      ((f-f f) env x)))
(define (apply-lam... env f xs)
  (if (func...? f)
      ((func...-f f) (lmap (λ (v) (EVAL env v)) xs))
      ((f...-f f) env xs)))

(define (EVAL env x)
  (delay
    (unlazy
     x
     (λ (x)
       (cond
         [(pair? x) (APPLY env (EVAL env (car x)) (cdr x))]
         [(symbol? x)
          (if (eq? x '_G_)
              (env-get genv 'eval (λ () (error "eval")))
              (env-get env x
                       (λ () (raise (compile-error undefined 'eval (list (cons env x)))))))]
         [(string? x) (string->list x)]
         [else x])))))

(define (APPLY env f xs)
  (unlazy
   f
   (λ (f)
     (cond
       [(lam? f)
        (unlazy
         xs
         (λ (xs)
           (if (pair? xs)
               (unlazy
                (cdr xs)
                (λ (d)
                  (if (null? d)
                      (apply-lam env f (car xs))
                      (APPLY env (apply-lam env f (car xs)) d))))
               (raise (type-error env "" 'apply (list f xs) "参数太少")))))]
       [(lam...? f) (apply-lam... env f xs)]
       [else (raise (type-error env "" 'apply (list f xs) "不是函数"))]))))

(define (%prim exp n f)
  (if (zero? n)
      (f '())
      (func exp
            (λ (x)
              (%prim (list exp (list 'quote x))
                     (pred n)
                     (λ (xs)
                       (f (cons x xs))))))))
(define (%primf exp n t)
  (if (zero? n)
      (t '())
      (f exp
         (λ (env x)
           (%primf (list '(_G_ 'chenv) env (list exp x))
                   (pred n)
                   (λ (xs)
                     (t (cons env (cons x xs)))))))))
(define (prim s n f) (%prim (list '_G_ (list 'quote s)) n (λ (xs) (apply f xs))))
(define (prim* s n f) (%prim (list '_G_ (list 'quote s)) n (λ (xs) (unlazy* xs (λ (xs) (apply f xs))))))
(define (p1 s f) (prim* s 1 f))
(define (p2 s f) (prim* s 2 f))
(define (primf s n f) (%primf (list '_G_ (list 'quote s)) n (λ (xs) (apply f xs))))
(define (primf... s f) (f... (list '_G_ (list 'quote s)) f))

(define (mkpair xs f)
  (unlazy
   xs
   (λ (xs)
     (if (null? xs)
         (f '())
         (unlazy
          (car xs)
          (λ (s)
            (unlazy
             (cdr xs)
             (λ (dd)
               (mkpair (cdr dd)
                       (λ (d)
                         (f (cons (cons s (car dd)) d))))))))))))
(define (env-append env ps)
  (foldl (λ (p env) (env-set env (car p) (cdr p))) env ps))

(define (andl x y)
  (if (promise? x)
      (delay (andl y (force x)))
      (if x
          y
          #f)))
(define (EQ? x y)
  (cond
    [(equal? x y) #t]
    [(promise? x) (delay (EQ? y (force x)))]
    [(promise? y) (delay (EQ? x (force y)))]
    [(pair? x)
     (and (pair? y)
          (andl
           (EQ? (car x) (car y))
           (EQ? (cdr x) (cdr y))))]
    [(hash? x) (and (hash? y) (EQ? (hash->list x) (hash->list y)))] ; BUG hash->list 可能顺序不一样
    [else #f]))

(define genv
  (newenv
   'eval (prim 'eval 1 (λ (x) (EVAL genv x)))
   'quote (primf 'quote 1 (λ (env x) x))

   'null? (p1 'null? null?)
   'pair? (p1 'pair? pair?)
   'cons (prim 'cons 2 cons)
   'car (p1 'car car)
   'cdr (p1 'cdr cdr)

   'boolean? (p1 'boolean? boolean?)
   'true #t
   'false #f
   'if (prim 'if 3 (λ (b x y) (unlazy b (λ (b) (if b x y)))))

   'record? (p1 'record? hash?)
   'record
   (primf...
    'record
    (λ (env xs)
      (letrec
          ([rc
            (delay
              (mkpair
               xs
               (λ (ps)
                 (map (λ (p)
                        (let ([s (car p)])
                          (cons s (delay-force (EVAL (env-at+ (force newenv) s) (cdr p))))))
                      ps))))]
           [newenv
            (delay
              (env-at+ (env-set (env-append env (force+ rc)) '_< rec) newenv))]
           [rec (unlazy rc make-immutable-hasheq)])
        rec)))
   'open (primf 'open 2 (λ (envr r envx x)
                          (unlazy
                           (EVAL envr r)
                           (λ (rec)
                             (EVAL (env-append envx (hash->list rec)) x)))))
   ': (primf ': 2
             (λ (envr r envx x)
               (unlazy
                (EVAL envr r)
                (λ (rec)
                  (unlazy
                   x
                   (λ (x)
                     (hash-ref rec x (λ () (raise (compile-error undefined ': (list (cons envr r) (cons envx x))))))))))))
   'record-has? (primf 'record-has? 2
                       (λ (envr r envx x)
                         (unlazy
                          (EVAL envr r)
                          (λ (rec)
                            (unlazy
                             x
                             (λ (x)
                               (hash-has-key? rec x)))))))
   'record-set (primf 'record-set 3
                      (λ (envr r envk k envx x)
                        (unlazy
                         (EVAL envr r)
                         (λ (rec)
                           (unlazy
                            k
                            (λ (k)
                              (hash-set rec k (EVAL envx x))))))))
   'record->list (p1 'record->list hash->list)

   '+/2 (p2 '+/2 +)
   '-/2 (p2 '-/2 -)
   '*/2 (p2 '*/2 *)
   '//2 (p2 '//2 /)
   '=/2 (prim '=/2 2 EQ?)
   '</2 (p2 '</2 <)
   '>/2 (p2 '>/2 >)
   '=</2 (p2 '=</2 <=)
   '>=/2 (p2 '>=/2 >=)

   'λ (primf 'λ 2
             (λ (envs s envx x)
               (unlazy
                s
                (λ (s)
                  (func (list '(_G_ 'chenv) envx (list '_G_ (list 'λ s x)))
                        (λ (v)
                          (EVAL (env-set envx s v)
                                x)))))))
   ))

(define (to-racket x)
  (let ([x (force+ x)])
    (cond
      [(pair? x) (cons (to-racket (car x)) (to-racket (cdr x)))]
      [(hash? x)
       (make-immutable-hasheq
        (map
         (λ (p)
           (cons (car p) (to-racket (cdr p))))
         (hash->list x)))]
      [else x])))

(define (core x)
  (with-exception-handler
      (λ (x) x)
    (λ () (to-racket (EVAL genv x)))))

; ----------------------------------------------------------------------------------------------------------------------------

(struct reads (x r))
(define (readst s) (readc (string->list s)))
(define (readc xs)
  (or (read-comment xs)
      (read-boolean xs)
      (read-list xs)
      (read-char xs)
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
(define (read-list xs)
  (and (eq? (car xs) #\()
       (%read-list (cdr xs))))
(define (%read-list xs)
  (if (eq? (car xs) #\))
      (reads '() (cdr xs))
      (let ([x (readc xs)])
        (and x (let ([rs (%read-list (reads-r x))])
                 (and rs
                      (reads (cons (reads-x x) (reads-x rs)) (reads-r rs))))))))
(define (read-char xs)
  (and (eq? (car xs) #\#)
       (let ([nxs (cdr xs)])
         (and (eq? (car xs) #\\)
              (let ([nnxs (cdr nxs)])
                (reads (car nnxs) (cdr nnxs)))))))
(define (read-quote xs)
  (and (eq? (car xs) #\')
       (let ([x (readc (cdr xs))])
         (and x (reads (list 'quote (reads-x x)) (reads-r x))))))
(define (space? x)
  (or (eq? x #\space) (eq? x #\tab) (eq? x #\return) (eq? x #\newline)))
(define (delimiters? x)
  (or (space? x) (eq? x #\() (eq? x #\)) (eq? x #\[) (eq? x #\]) (eq? x #\") (eq? x #\,) (eq? x #\') (eq? x #\`) (eq? x #\;)))
(define (read-space xs)
  (let ([x (car xs)])
    (and (space? x)
         (readc (cdr xs)))))
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
