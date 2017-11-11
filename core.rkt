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
(provide core coreread mustread)
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
(define (force* x)
  (let ([x (force+ x)])
    (cond
      [(pair? x) (cons (force* (car x)) (force* (cdr x)))]
      [else x])))
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
(define (unlazyn n less xs f)
  (if (zero? n)
      (f xs '())
      (unlazy
       xs
       (λ (xs)
         (if (null? xs)
             (less)
             (unlazyn
              (pred n)
              less
              (cdr xs)
              (λ (more d)
                (f more (cons (car xs) d)))))))))

; U 'undefined 'syntax -> Symbol -> [(U Hash Env) * Exp] -> CompileErr
(struct compile-error (t f xs))
(define undefined 'undefined)
(define syntaxerr 'syntax)
(define (err t f xs) (raise (compile-error t f xs)))

; Env -> String -> Stream Any -> String -> TypeError
(struct type-error (env at parm i))

; String → Nat → [U Symbol (Promise Hash) Hash Env (Promise Env)] → At
(struct at (file line ss))
(define (at+ x s) (at (at-file x) (at-line x) (cons s (at-ss x))))

(struct env (at x))
(define (hash->env h) (env (at "" 0 (list h)) h))
(define (newenv . xs) (hash->env (apply hasheq xs)))
(define (env-set e s x) (env (env-at e) (hash-set (env-x e) s x)))
(define (env-get e s f) (hash-ref (env-x e) s f))
(define (env-at+ e x) (env (at+ (env-at e) x) (env-x e)))

; f : Any -> Any
(struct lam1 (exp f))
; f : Stream Any -> Any
(struct lam... (exp f))
; n : Nat
; f : Env -> [Exp] -> Any
(struct f-n (exp n f))
; f : Env -> Stream Exp -> Any
(struct f... (exp f))

(define (EVAL env x)
  (delay
    (unlazy
     x
     (λ (x)
       (cond
         [(pair? x)
          (unlazy
           (car x)
           (λ (xa)
             (cond
               [(eq? xa 'G)
                (unlazy
                 (cdr x)
                 (λ (xd)
                   (EVAL genv (car xd))))]
               [(eq? xa '!)
                (unlazy
                 (cdr x)
                 (λ (xd)
                   (APPLYmacro env (EVAL env (car xd)) (cdr xd))))]
               [else (APPLY (EVAL env xa) (lmap (λ (x) (EVAL env x)) (cdr x)))])))]
         [(symbol? x)
          (env-get env x
                   (λ () (raise (compile-error undefined 'eval (list (cons env x))))))]
         [(string? x) (string->list x)]
         [else x])))))

(define (APPLY f xs) (%APPLY f xs (cons f xs)))
(define (%APPLY f xs parm)
  (unlazy
   f
   (λ (f)
     (cond
       [(lam1? f)
        (unlazy
         xs
         (λ (xs)
           (if (pair? xs)
               (unlazy
                ((lam1-f f) (car xs))
                (λ (r)
                  (if (lam...? r)
                      (%APPLY r (cdr xs) parm)
                      (unlazy
                       (cdr xs)
                       (λ (xsd)
                         (cond
                           [(null? xsd) r]
                           [(lam1? r) (%APPLY r xsd parm)]
                           [else
                            (raise (type-error (env-at+ genv 'apply) "" parm "参数太多"))]))))))
               (raise (type-error (env-at+ genv 'apply) "" parm "参数太少")))))]
       [(lam...? f) ((lam...-f f) xs)]
       [else (raise (type-error (env-at+ genv 'apply) "" parm "不是函数"))]))))
(define (APPLYmacro env f xs) (%APPLYmacro env f xs (cons env (cons f xs))))
(define (%APPLYmacro env f xs parm)
  (unlazy
   f
   (λ (f)
     (cond
       [(f-n? f)
        (unlazyn
         (f-n-n f)
         (λ () (raise (type-error (env-at+ genv '!) "" parm "参数太少")))
         xs
         (λ (more xs)
           (if (null? more)
               ((f-n-f f) env xs)
               (APPLY ((f-n-f f) env xs) more))))] ; BUG APPLY raise内容不正确
       [(f...? f) ((f...-f f) env xs)]
       [else (raise (type-error (env-at+ genv '!) "" parm "不是宏"))]))))

(define (prim-f-n s n f) (f-n (list 'G s) n (λ (env xs) (apply f (cons env xs)))))
(define (prim-f... s f) (f... (list 'G s) f))
(define (%prim-n exp n f)
  (if (zero? n)
      (f '())
      (lam1 exp
            (λ (x)
              (%prim-n (list exp (list 'quote x))
                       (pred n)
                       (λ (xs) (f (cons x xs))))))))
(define (prim-n s n f)
  (%prim-n (list 'G s)
           n
           (λ (xs) (apply f xs))))
(define (?-prim s f)
  (lam1 (list 'G s)
        (λ (x)
          (unlazy x f))))

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
(define (env+record env rec) (env-append env (hash->list rec)))

(define genv
  (newenv
   'true #t
   'false #f
   'boolean? (?-prim 'boolean? boolean?)
   'cons (prim-n 'cons 2 cons)
   'pair? (?-prim 'pair? pair?)
   'if (prim-n 'if 3 (λ (b x y) (unlazy b (λ (b) (if b x y)))))
   'quote (prim-f-n 'quote 1 (λ (env x) x))

   'λ1 (prim-f-n 'λ1 2 (λ (env s x)
                         (lam1 (list 'chenv env (list '! '(G λ1) s x))
                               (λ (p)
                                 (EVAL (env-set env s p) x)))))
   'λ1? (?-prim 'λ1? lam1?)
   'λ...? (?-prim 'λ...? lam...?)
   'λ... (prim-f-n 'λ... 2 (λ (env s x)
                             (lam... (list 'chenv env (list '! '(G λ...) s x))
                                     (λ (p)
                                       (EVAL (env-set env s p) x)))))

   'record (prim-f...
            'record
            (λ (env parms)
              (letrec
                  ([rc (delay
                         (mkpair
                          parms
                          (λ (ps)
                            (map (λ (p)
                                   (let ([s (car p)])
                                     (cons s (delay-force (EVAL (env-at+ (force newenv) s) (cdr p))))))
                                 ps))))]
                   [newenv
                    (delay
                      (env-at+ (env-append env (force+ rc)) newenv))]
                   [rec (unlazy rc make-immutable-hasheq)])
                rec)))
   'record? (?-prim 'record? hash?)
   'open (prim-f-n 'open 2 (λ (env rec v)
                             (unlazy
                              (EVAL env rec)
                              (λ (rec) (EVAL (env+record env rec) v)))))
   ': (prim-f-n
       ': 2
       (λ (env rec v)
         (unlazy
          (EVAL env rec)
          (λ (rec)
            (unlazy
             v
             (λ (v)
               (hash-ref rec v
                         (λ () (raise (compile-error undefined ': (list (cons rec v))))))))))))
   'record-has? (prim-f-n
                 'record-has? 2
                 (λ (env rec s)
                   (unlazy
                    (EVAL env rec)
                    (λ (rec)
                      (unlazy
                       s
                       (λ (s)
                         (hash-has-key? rec s)))))))
   'record-set (prim-f-n
                'record-set 3
                (λ (env rec s x)
                  (unlazy
                   (EVAL env rec)
                   (λ (rec)
                     (unlazy
                      (EVAL env x)
                      (λ (x)
                        (unlazy
                         s
                         (λ (s)
                           (hash-set rec s x)))))))))
   ))

(define (torkt x)
  (let ([x (force* x)])
    (cond
      [(and (pair? x) (list? x) (andmap char? x)) (list->string x)]
      [(hash? x)
       (make-immutable-hasheq
        (map
         (λ (p)
           (cons (car p) (torkt (cdr p))))
         (hash->list x)))]
      [else x])))
(define (core x) (torkt (EVAL genv x)))

(struct reads (x r))
(define (coreread s)
  (let ([x (readc (string->list s))])
    (and
     x
     (null? (reads-r x))
     (list (reads-x x)))))
(define (mustread s) (car (coreread s)))
(define (readc xs)
  (or (read-comment xs)
      (read-boolean xs)
      (read-macro xs)
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


; ----------------------------------------------------------------------------------------------------------------------------
; 暂时未使用

(define (choice2 x y f)
  (if (promise? x)
      (delay (choice2 y (force x) f))
      (f x y)))
;wip
;(define (%choice* ps xs rs)
;  (if (pair? ps)
;      (%choice* (cdr ps) (cons (car ps) xs) rs)
;      (if (null? ps)
;          (%choice*- xs rs)
;          (if (null? xs)
;              (if (null? rs)
;                  (unlazy ps (λ (ps) (%choice* ps '() '())))
;                  (%choice* ps rs '()))
;              (if (promise? (car xs))
;                  (delay
;                    (delay
;                      (%choice* (force ps) (cdr xs) (cons (force (car xs)) rs))))
;                  (cons (car xs) (%choice* ps (cdr xs) rs)))))))


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
; old
;(define (runio x f)
;  (unlazy
;   x
;   (λ (x)
;     (cond
;       [(ioret? x) (f (ioret-v x))]
;       [(iobind? x)
;        (runio (iobind-x x) (λ (r) (unlazy
;                                    (iobind-f x)
;                                    (λ (x)
;                                      (runio (capply x (list r)) f)))))]
;       [(ioputstr? x) (unlazy* (ioputstr-x x) (λ (s) (display (list->string s)) (f '())))]
;       [(ionewline? x) (newline) (f '())]
;       [(iocall/ccv? x) x]
;       [(iocall/cc? x) (runio (iocall/cc-x x)
;                              (λ (r)
;                                (if (and (iocall/ccv? r) (equal? (iocall/ccv-id r) (iocall/cc-id x)))
;                                    (f (iocall/ccv-x r))
;                                    (f r))))]
;       [(ioread-line? x) (f (read-line))]
;       [else (err syntaxerr 'runio (list x f) '())]))))
;(define io
;  (record (hasheq 'return (pf 1 ioret)
;                  '>>= (pf 2 iobind)
;                  'putstr (pf 1 ioputstr)
;                  'newline (ionewline)
;                  'readline (ioread-line)
;                  'call/cc (pf
;                            1
;                            (λ (f)
;                              (let ([id (id!)])
;                                (iocall/cc id (capply f (list (pf 1 (λ (x) (iocall/ccv id x))))))))))))
