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

(define prelude
  '(record
    module record
    list (λ... xs xs)
    id (λ x x)
    or (λ x (λ y (choice2 x y (λ x (λ y (if x true y))))))
    and (λ x (λ y (choice2 x y (λ x (λ y (if x y false))))))
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
                            >> (λ x (λ y (: io >>= x (λ i y))))
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
;(define-syntax-rule (err t f x e) (error 'err))
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
    [(procedure? x)
     (let ([n (procedure-arity x)])
       (if (number? n)
           (p n x)
           (p... x)))]
    [(hash? x) (record x)];需修复: 可能不是Hash Symbol Any
    [else x]))
(define (to-racket-value x)
  (let ([x (force+ x)])
    (cond
      [(pair? x) (cons (to-racket-value (car x)) (to-racket-value (cdr x)))]
      ;[(func? x) (from-func x)]
      ;[(func...? x) (from-func... x)]
      [(record? x)
       (make-immutable-hasheq
        (map (λ (p) (cons (car p) (to-racket-value (cdr p))))
             (hash->list (record-v x))))]
      [(io? x) (force+ (runio x to-racket-value))]
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
(define (p... f) (pf... (λ (xs) (unlazy... xs f))))

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
          [(record? x) (and (record? y)
                            (ceq? (hash->list (record-v x)) (hash->list (record-v y)) c))]
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
(define (cload e env) (env+record env (force+ (eeval env e))))

(define (capply f xs) (aapply genv f (lmap (λ (x) (list 'quote x)) xs)))

(define genv
  (cload
   prelude
   (newenv
    'eval (pm 1 (λ (env x) (eeval env (eeval env x))))
    'apply (pf 1 capply)
    'λ (pm 2 (λ (envs s envx x)
               (unlazy
                s
                (λ (s)
                  (if (symbol? s)
                      (func (λ (env a)
                              (eeval (env-set envx s (eeval env a)) x)))
                      (err syntaxerr 'λ (list s x) (list envs envx)))))))
    'λmacro (pm 2 (λ (envs s envx x)
               (unlazy
                s
                (λ (s)
                  (if (symbol? s)
                      (func (λ (env a)
                              (eeval env (eeval (env-set envx s a) x))))
                      (err syntaxerr 'λ (list s x) (list envs envx)))))))
    'λ... (pm 2 (λ (envs s envx x)
                  (unlazy
                   s
                   (λ (s)
                     (if (symbol? s)
                         (func... (λ (env as)
                                    (eeval (env-set envx s (lmap (λ (x) (eeval env x)) as)) x)))
                         (err syntaxerr 'λ... (list s x) (list envs envx)))))))
    'λ...macro (pm 2 (λ (envs s envx x)
                  (unlazy
                   s
                   (λ (s)
                     (if (symbol? s)
                         (func... (λ (env as)
                                    (eeval env (eeval (env-set envx s as) x))))
                         (err syntaxerr 'λ... (list s x) (list envs envx)))))))
    'λ? (p 1 func?)
    'λ...? (p 1 func...?)
    'true #t
    'false #f
    'quote (pm 1 (λ (env x) x))
    'cons (pf 2 cons)
    'car (p 1 car)
    'cdr (p 1 cdr)
    'null? (p 1 null?)
    'number? (p 1 number?)
    'pair? (p 1 pair?)
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
    'choice2 (pf 3 (λ (x y f)
                     (choice2 x y (λ (x y) (capply f (list x y))))))
    'if (pf 3 (λ (c t f) (unlazy c (λ (c) (if c t f)))))
    'require (pm 2 (λ (envm m envx x)
                     (unlazy
                      m
                      (λ (m)
                        (cond
                          [(env-has? envm m) (eeval (env-set envx m (env-ref envm m (λ () (error '!)))) x)]
                          [(eq? m 'io) (eeval (env-set envx 'io io) x)]
                          [else (err syntaxerr 'require (list m x) (list envm envx))])))))
    )))

(struct choice2-_!_ (v))
(define (choice2 x y f)
  (if (promise? x)
      (delay (let ([nx (with-handlers ([(λ (x) true) choice2-_!_])
                         (force x))])
               (if (choice2-_!_? nx)
                   (f y (delay (raise (choice2-_!_-v nx))))
                   (choice2 y nx f))))
      (f x y)))

(struct reads (x r) #:transparent)
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

(struct ioret (v))
(struct iocall/ccv (id x))
(struct iocall/cc (id x))
(struct iobind (x f))
(struct ioputstr (x))
(struct ionewline ())
(struct ioread-line ())
(define (io? x) (or (ioret? x) (iocall/ccv? x) (iocall/cc? x) (iobind? x) (ioputstr? x) (ionewline? x) (ioread-line? x)))
(define id!
  (let ([idc 0])
    (λ ()
      (set! idc (succ idc))
      idc)))
(define (runio x f)
  (unlazy
   x
   (λ (x)
     (cond
       [(ioret? x) (f (ioret-v x))]
       [(iobind? x)
        (runio (iobind-x x) (λ (r) (unlazy
                                    (iobind-f x)
                                    (λ (x)
                                      (runio (capply x (list r)) f)))))]
       [(ioputstr? x) (unlazy (ioputstr-x x) (λ (s) (display s) (f '())))]
       [(ionewline? x) (newline) (f '())]
       [(iocall/ccv? x) x]
       [(iocall/cc? x) (runio (iocall/cc-x x)
                              (λ (r)
                                (if (equal? (iocall/ccv-id r) (iocall/cc-id x))
                                    (f (iocall/ccv-x r))
                                    (err syntaxerr 'runio (list x f) '()))))]
       [(ioread-line? x) (f (read-line))]
       [else (err syntaxerr 'runio (list x f) '())]))))
(define io
  (record (hasheq 'return (pf 1 ioret)
                  '>>= (pf 2 iobind)
                  'putstr (pf 1 ioputstr)
                  'newline (ionewline)
                  'readline (ioread-line)
                  'call/cc (pf
                            1
                            (λ (f)
                              (let ([id (id!)])
                                (iocall/cc id (capply f (list (pf 1 (λ (x) (iocall/ccv id x))))))))))))
