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
(define-syntax-rule (deft (f x ...) v)
  (define (f x ...)
    (writeln (list (quote f) (force+ x) ...))
    (let ([r v])
      (let ([rf (force+ r)])
        (write (list (quote f) (force+ x) ...))
        (display " => ")
        (writeln rf)
        r))))

(define prelude-sexp
  '(record
    module record
    id (λ x x)
    or (λ x (λ y (choice2 x y (λ x (λ y (if x #t y))))))
    and (λ x (λ y (choice2 x y (λ x (λ y (if x y #f))))))
    list? (λ xs (or (null? xs) (list? (cdr xs))))
    map (λ f (λ xs
               (if (null? xs)
                   ()
                   (cons (f (car xs)) (map f (cdr xs))))))
    filter (λ f (λ xs
                  (if (null? xs)
                      ()
                      (if (f (car xs))
                          (cons (car xs) (filter f (cdr xs)))
                          (filter f (cdr xs))))))
    succ (+ 1)
    pred (- 1)
    prelude/io (require io
                        (module
                            >> (λ x (λ y (>>= x (λ (i) y))))
                          putstrln (λ s (>> (: io putstr s) (: io newline)))))
    ))
(define fold foldl)

(define (succ x) (+ 1 x))
(define (pred x) (- x 1))

(define (unlazy x f)
  (if (promise? x)
      (delay (unlazy (force x) f))
      (f x)))

; U undefined notfunction → Symbol → Exp → [Env] → CompileErr
(struct compile-error (t f x e) #:transparent)
(define undefined 'undefined)
(define notfunction 'notfunction)
(define noarg 'noarg)
(define toomanyarg 'toomanyarg)
(define syntaxerr 'syntax)
(struct left (x))
; Nothing = Left ()
(define (err t f x e) (raise (compile-error t f x e)))

; String → Nat → [U Symbol (Promise+ Record)] → U Symbol (Promise+ Record) → At
(struct at (file line s x))
(define (at+ x s) (at (at-file x) (at-line x) (cons (at-x x) (at-s x)) s))
; Hash Symbol Any → At → Envr
(struct envr (x at))
(define (newenv . xs)
  (let ([x (apply hasheq xs)])
    (envr x (at "" 0 '() x))))
(define (env-set e s x) (envr (hash-set (envr-x e) s x) (envr-at e)))
(define (env-has? e s) (hash-has-key? (envr-x e) s))
(define (env-ref e s t) (hash-ref (envr-x e) s t))
(define (env-at+ e x) (envr (envr-x e) (at+ (envr-at e) x)))

; Env → Exp → Any
(struct func (v) #:transparent)
; Env → Stream Exp → Any
(struct func... (v) #:transparent)

(define (eeval env x)
  (delay
    (unlazy
     x
     (λ (x)
       (cond
         [(symbol? x) (env-ref env x (λ () (err undefined 'eval x env)))]
         [(pair? x) (aapply env (eeval env (car x)) (cdr x))]
         [else x])))))
; Env → Any → Stream Exp → Any
(define (aapply env f xs)
  (unlazy
   f
   (λ (f)
     (cond
       [(func? f)
        (unlazy
         xs
         (λ (xs)
           (if (pair? xs)
               (unlazy
                ((func-v f) env (car xs))
                (λ (r)
                  (unlazy
                   (cdr xs)
                   (λ (d)
                     (cond
                       [(null? d) r]
                       [(or (func...? r) (func? r)) (aapply env r d)]
                       [else (err toomanyarg 'apply (list f (cons (car xs) d)) env)])))))
               (err noarg 'apply (list f xs) env))))]
       [(func...? f) ((func...-v f) env xs)]
       [else (err notfunction 'apply (list f xs) env)]))))


(define (force+ x)
  (if (promise? x)
      (force+ (force x))
      x))
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
(define (unlazystream xs f)
  (unlazy
   xs
   (λ (xs)
     (if (null? xs)
         (f '())
         (unlazystream
          (cdr xs)
          (λ (d)
            (f (cons (car xs) d))))))))
(define (lmap f xs)
  (unlazy
   xs
   (λ (xs)
     (if (null? xs)
         '()
         (cons (f (car xs)) (lmap f (cdr xs)))))))

(define (from-racket-value x)
  (cond
    [(promise? x) (delay (from-racket-value (force x)))]
    ;[(procedure? x) (to-func x)]
    ;[(hash? x) (record x)];需修复: 可能不是Hash Symbol Any
    [else x]))
(define (to-racket-value x)
  (let ([x (force+ x)])
    (cond
      [(pair? x) (cons (to-racket-value (car x)) (to-racket-value (cdr x)))]
      ;[(func? x) (from-func x)]
      ;[(func...? x) (from-func... x)]
      ;[(record? x)
      ; (make-immutable-hasheq
      ;  (map (λ (p) (cons (car p) (to-racket-value (cdr p))))
      ;       (hash->list (record-v x))))]
      ;[(io? x) (force+ (runio x to-racket-value))]
      [else x])))

(define (core x) (to-racket-value (eeval genv x)))

(define (makefunc n f)
  (if (zero? n)
      (f '())
      (func (λ (env x)
              (makefunc (pred n) (λ (xs)
                                   (f (cons env (cons x xs)))))))))
(define (makef n f)
  (if (zero? n)
      (f '())
      (func (λ (env x)
              (makef (pred n) (λ (xs)
                                (f (cons (eeval env x) xs))))))))
(define (pm n f) (makefunc n (λ (xs) (apply f xs))))
(define pm... func...)
(define (pf n f) (makef n (λ (xs) (apply f xs))))
(define (pf... f) (func... (λ (env xs) (unlazystream xs (λ (xs) (f (map (λ (x) (eeval env x)) xs)))))))
(define (p n f) (makef n (λ (xs) (unlazy... xs (λ (xs) (apply f xs))))))

(define (ceq? x y c)
  (unlazy
   x
   (λ (x)
     (unlazy
      y
      (λ (y)
        (cond
          [(pair? x) (and (pair? y)
                          (ceq? (car x) (car y)
                                (λ ()
                                  (ceq? (cdr x) (cdr y)
                                        c))))]
          ;[(record? x) (and (record? y)
          ;                  (ceq? (hash->list (record-v x)) (hash->list (record-v y)) c))]
          [(number? x) (and (number? y) (= x y) (c))]
          [else (and (equal? x y) (c))]))))))

; Hash Symbol Any → Record
(struct record (v))
(define (mkpair xs f)
  (if (null? xs)
      (f '())
      (unlazy
       (car xs)
       (λ (s)
         (mkpair (cddr xs)
                 (λ (d)
                   (f (cons (cons s (cadr xs)) d))))))))
(define (env-append env ps)
  (fold (λ (p env) (env-set env (car p) (cdr p))) env ps))
(define (env+record env r)
  (env-append env (hash->list (record-v r))))

(define genv
  (newenv
   'λ (pm 2 (λ (envs s envx x)
              (unlazy
               s
               (λ (s)
                 (if (symbol? s)
                     (func (λ (env a)
                             (eeval (env-set envx s (eeval env a)) x)))
                     (err syntaxerr 'λ (list s x) (list envs envx)))))))
   'λ... (pm 2 (λ (envs s envx x)
                 (unlazy
                  s
                  (λ (s)
                    (if (symbol? s)
                        (func... (λ (env as)
                                   (eeval (env-set envx s (lmap (λ (x) (eeval env x)) as)) x)))
                        (err syntaxerr 'λ... (list s x) (list envs envx)))))))
   'true #t
   'false #f
   'quote (pm 1 (λ (env x) x))
   'cons (pf 2 cons)
   'car (p 1 car)
   'cdr (p 1 cdr)
   '+ (p 2 +)
   '- (p 2 -)
   '* (p 2 *)
   '/ (p 2 /)
   '< (p 2 <)
   '> (p 2 >)
   '=< (p 2 <=)
   '>= (p 2 >=)
   '= (pf 2 (λ (x y) (ceq? x y (λ () true))))
   '=/= (pf 2 (λ (x y) (unlazy (ceq? x y (λ () true)) not)))
   'not (p 1 not)
   'list (pf... (λ (xs) xs))
   'record (pm... (λ (env xs)
                    (define newenv
                      (delay
                        (env-set (env-append env (force+ rc)) '_< rec)))
                    (define newenv+
                      (delay
                        (env-at+ (force newenv) recf)))
                    (define rc
                      (delay
                        (mkpair
                         xs
                         (λ (ps)
                           (map (λ (p)
                                  (let ([s (car p)])
                                    (if (symbol? s)
                                        (cons s (delay (eeval (env-at+ (force newenv+) s) (cdr p))))
                                        (err syntaxerr 'record xs env)))) ps)))))
                    (define rec
                      (unlazy
                       rc
                       (λ (rc)
                         (record (make-immutable-hasheq rc)))))
                    (define recf (delay (force+ rec)))
                    rec))
   'open (pm 2 (λ (envr r envx x)
                 (unlazy
                  (eeval envr r)
                  (λ (r)
                    (eeval (env+record envx r) x)))))
   ': (pm 2 (λ (envr r envx x)
              (unlazy
               (eeval envr r)
               (λ (r)
                 (unlazy
                  x
                  (λ (s)
                    (hash-ref (record-v r) s (λ () (err undefined ': (list r s) (list envr envx))))))))))
   ))
