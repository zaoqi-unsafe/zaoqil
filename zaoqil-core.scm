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
(define prelude
  '(record
    λ (f e0 s (f env v (f argenv arg (eval+env (env-set env s (eval+env argenv arg)) v))))
    λmacro (f e0 s (f env v (f argenv arg (eval+env argenv (eval+env (env-set env s arg) v)))))
    λ...macro (f e0 s (f env v (f... argenv arg (eval+env argenv (eval+env (env-set env s arg) v)))))
    ;λ... (f e0 s (f env v (f... argenv arg (eval+env (env-set env s (map (eval+env argenv) arg)) v))))
    module record
    list (λ... xs xs)
    id (λ x x)
    or (λ2 x y (if x true y))
    and (λ2 x y (if x y false))
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
    record+ (λ r
              (λ...macro x
                         (list 'record-append r (cons 'record x))))
    module+ record+
    io (import primio
               (module+ primio
                 putstrln (λ s (>>= (putstr s) (λ i newline)))))
    import (λmacro m (λmacro x
                             (list 'require m
                                   (list 'open m
                                         x))))
    string? (λ x
              (and (pair? x)
                   (and (char? (car x))
                        (or (null? (cdr x))
                            (string? (cdr x))))))
    let (f xsenv xs
           (λmacro x
                   (list 'open (eval+env xsenv (cons 'record xs))
                         x)))
    λ2 (λmacro s1 (λmacro s2 (λmacro x  ;非pair?，不会eval
                                     (list 'λ s1
                                           (list 'λ s2
                                                 (list 'choice2 s1 s2
                                                       (list 'λ s1
                                                             (list 'λ s2
                                                                   x))))))))
    listmonad (module
                  return (λ x (list x))
                >>= (λ xs (λ f (bind f xs)))
                bind (λ f (λ xs
                            (if (null? xs)
                                '()
                                (mplus (f (car xs)) (bind f (cdr xs))))))
                mplus (λ2 xs ys (if (null? xs) ys (cons (car xs) (mplus ys (cdr xs))))))
    struct (λ...macro xs
                      (gensym
                       (λ x
                         (list (list 'λ x
                                     (cons 'record
                                           (cons '_:
                                                 (cons (list 'cons x (list 'quote (car xs)))
                                                       (cdr xs))))) '_<))))
    struct? (λmacro s
                    (gensym
                     (λ x
                       (list 'λ x
                             (list '= (list '_:? x) (list 'cons '_< (list 'quote s)))))))
    do (let (%do (λ bind (λ xs
                 (if (null? (cdr xs))
                     (car xs)
                     (if (= (car (cdr xs)) '<-)
                         (list bind
                               (car (cdr (cdr xs)))
                               (list 'λ (car xs)
                                     (%do bind (cdr (cdr (cdr xs))))))
                         (gensym (λ i
                                   (list bind (car xs)
                                         (list 'λ i
                                               (%do bind (cdr xs)))))))))))
         (λ...macro xs
                    (list 'open (car xs)
                          (%do '>>= (cdr xs)))))
    ))

(define (succ x) (+ 1 x))
(define (pred x) (- x 1))

(define (unlazy x f)
  (if (promise? x)
      (if (promise-forced? x)
          (unlazy (force x) f)
          (delay (unlazy (force x) f)))
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

; String → Nat → [U Symbol (Promise Record)] → At
(struct at (file line s) #:transparent)
(define (at+ x s) (at (at-file x) (at-line x) (cons s (at-s x))))
; Hash Symbol Any → At → Envr
(struct envr (at x) #:transparent)
(define (newenv . xs)
  (let ([x (apply hasheq xs)])
    (envr (at "" 0 '()) x)))
(define (env-set e s x) (envr (envr-at e) (hash-set (envr-x e) s x)))
(define (env-has? e s) (hash-has-key? (envr-x e) s))
(define (env-ref e s t) (hash-ref (envr-x e) s t))
(define (env-at+ e x) (envr (at+ (envr-at e) x) (envr-x e)))

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
         [(string? x) (string->list x)]
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
(define (unlazy* xs f)
  (unlazystream xs (λ (xs) (unlazy... xs f))))

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
             (filter-not (λ (p) (eq? (car p) '_:))
                         (hash->list (record-v x)))))]
      [(io? x) (force+ (runio x to-racket-value))]
      [(str2rkt? x) => (λ (r) r)]
      [else x])))
(define (str2rkt? x)
  (let ([r (%str2rkt? x)])
    (and
     r
     (not (null? r))
     (list->string r))))
(define (%str2rkt? x)
  (let ([x (force+ x)])
    (if (null? x)
        '()
        (and (pair? x)
             (char? (car x))
             (cons (car x) (%str2rkt? (cdr x)))))))

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
          [(equal? x y) (c)]
          [(pair? x) (and (pair? y)
                          (ceq? (car x) (car y)
                                (λ ()
                                  (ceq? (cdr x) (cdr y)
                                        c))))]
          [(record? x) (and (record? y)
                            (ceq? (hash->list (record-v x)) (hash->list (record-v y)) c))]
          [(number? x) (and (number? y) (= x y) (c))]
          [else false]))))))

; Hash Symbol Any → Record
(struct record (v) #:transparent)
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
(define (env+record env r)
  (env-append env (hash->list (record-v r))))
(define (cload e env) (env+record env (force+ (eeval env e))))

(define (capply f xs) (aapply genv f (lmap (λ (x) (list 'quote x)) xs)))

(define genv
  (cload
   prelude
   (newenv
    'eval (pm 1 (λ (env x) (eeval env (eeval env x))))
    'eval+env (pf 2 (λ (env x) (unlazy env (λ (env) (eeval env x)))))
    'env-set (pf 3 (λ (env s x) (unlazy env (λ (env) (unlazy s (λ (s) (env-set env s x)))))))
    'apply (pf 1 capply)
    'f (pm 3 (λ (e0 envs e1 s envx x)
               (unlazy
                s
                (λ (s)
                  (if (symbol? s)
                      (func (λ (env a)
                              (eeval (env-set (env-set envx s a) envs env) x)))
                      (err syntaxerr 'f (list envs s x) (list e0 e1 envx)))))))
    'λ... (pm 2 (λ (envs s envx x)
                  (unlazy
                   s
                   (λ (s)
                     (if (symbol? s)
                         (func... (λ (env as)
                                    (eeval (env-set envx s (lmap (λ (x) (eeval env x)) as)) x)))
                         (err syntaxerr 'λ... (list s x) (list envs envx)))))))
    'f... (pm 3 (λ (e0 envs e1 s envx x)
                  (unlazy
                   s
                   (λ (s)
                     (if (symbol? s)
                         (func... (λ (env as)
                                    (eeval (env-set (env-set envx s as) envs env) x)))
                         (err syntaxerr 'f... (list envs s x) (list e0 e1 envx)))))))
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
    'record? (p 1 record?)
    'env? (p 1 envr?)
    'char? (p 1 char?)
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
                     (letrec
                         ([newenv (delay
                                    (env-set (env-append env (force+ rc)) '_< rec))]
                          [newenv+ (delay
                                     (env-at+ (force newenv) recf))]
                          [rc (delay
                                (mkpair
                                 xs
                                 (λ (ps)
                                   (map (λ (p)
                                          (let ([s (car p)])
                                            (if (symbol? s)
                                                (cons s (delay (eeval (env-at+ (force newenv+) s) (cdr p))))
                                                (err syntaxerr 'record xs env)))) ps))))]
                          [rec (unlazy
                                rc
                                (λ (rc)
                                  (record (make-immutable-hasheq rc))))]
                          [recf (delay (force+ rec))])
                       rec)))
    'record-append (p 2 (λ (r1 r2) (record (hash-union (record-v r1) (record-v r2)))))
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
                          [(eq? m 'primio) (eeval (env-set envx 'primio io) x)]
                          [else (err syntaxerr 'require (list m x) (list envm envx))])))))
    'record->list (p 1 (λ (r) (hash->list (record-v r))))
    'gensym (p 1 (memorize1 (λ (f) (capply f (list (gensym)))))) ;尽量类似纯函数，所以最好不提供symbol->string
    '_:? (p 1 (λ (r) (and (record? r) (hash-ref (record-v r) '_: false))))
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
       [(ioputstr? x) (unlazy* (ioputstr-x x) (λ (s) (display (list->string s)) (f '())))]
       [(ionewline? x) (newline) (f '())]
       [(iocall/ccv? x) x]
       [(iocall/cc? x) (runio (iocall/cc-x x)
                              (λ (r)
                                (if (and (iocall/ccv? r) (equal? (iocall/ccv-id r) (iocall/cc-id x)))
                                    (f (iocall/ccv-x r))
                                    (f r))))]
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
