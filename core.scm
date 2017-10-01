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
(define prelude-sexp
  '(record
    module record
    id (λ x x)
    or (λ x (λ y (if x t y)))
    and (λ x (λ y (if x y f)))
    list? (λ xs (or (null? xs) (list? (cdr xs))))
    map (λ f (λ xs
               (if (null? xs)
                   ()
                   (cons (f (car xs)) (map f (cdr xs))))))
    succ (+ 1)
    pred (- 1)
    ))

(define (succ x) (+ 1 x))
(define (pred x) (- x 1))

(define (_!_) (raise (compile-error "")))

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
(define (unlazy** xs f)
  (unlazy
   xs
   (λ (xs)
     (cond
       [(null? xs) (f '())]
       [(pair? xs)
        (unlazy**
         (cdr xs)
         (λ (d)
           (f (cons (car xs) d))))]
       [else (_!_)]))))
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
(define (unlazy*+ n xs f)
  (if (zero? n)
      (unlazy** xs (λ (rs) (f rs '())))
      (unlazy* n xs f)))

(define (lmap f xs)
  (unlazy
   xs
   (λ (xs)
     (if (null? xs)
         '()
         (cons (f (car xs)) (lmap f (cdr xs)))))))

(define env hasheq)
(define envset hash-set)
(define envget hash-ref)

(define (capply f xs) (aapply genv f (lmap (λ (x) (list 'quote x)) xs)))

; Prim → Func
(define (pack n p)
  (if (zero? n)
      p
      (%pack n (λ (xs) (capply p xs)))))
(define (%pack n g)
  (if (zero? n)
      (g '())
      (func
       (λ (x) (%pack (pred n) (λ (xs) (g (cons x xs))))))))

; Nat → (Env → [Exp] → Any) → Prim
(struct prim (n f))
(define (prim-apply f env xs g)
  (unlazy*+ (prim-n f) xs (λ (xs rs) (g rs ((prim-f f) env xs)))))
(define (primm n f) (prim n (λ (env xs) (apply f (cons env xs)))))
(define (primf n f) (pack n (prim n (λ (env xs) (apply f (map (λ (x) (eeval env x)) xs))))))
(define (primp n f)
  (pack n (prim
           n
           (λ (env xs)
             (unlazy...
              (map (λ (x) (eeval env x)) xs)
              (λ (as)
                (apply f as)))))))

; (Any → Any) → Func
(struct func (v))
; (Stream Any → Any) → Func...
(struct func... (v))
; F → Macro
(struct macro (v))
; Hash Symbol Any → Record
(struct record (v))
(struct nothing (v))
(struct compile-error (v))

(define (to-func x) (%to-func (curry x)))
(define (%to-func x)
  (if (procedure? x)
      (func (λ (v) (%to-func (x (to-racket-value v)))))
      (from-racket-value x)))

(define (from-f x)
  (λ as
    (to-racket-value (capply x (map (λ (a) (from-racket-value a)) as)))))

(define (from-racket-value x)
  (cond
    [(promise? x) (delay (from-racket-value (force x)))]
    [(procedure? x) (to-func x)]
    [(hash? x) (record x)];需修复： 可能不是Hash Symbol Any
    [else x]))

(define (to-racket-value x)
  (let ([x (force+ x)])
    (cond
      [(pair? x) (cons (to-racket-value (car x)) (to-racket-value (cdr x)))]
      [(f? x) (from-f x)]
      [(record? x)
       (make-immutable-hasheq
        (map (λ (p) (cons (car p) (to-racket-value (cdr p))))
             (hash->list (record-v x))))]
      [(io? x) (force+ (runio x to-racket-value))]
      [else x])))

(define (ceval x) (to-racket-value (eeval genv x)))

(define (f? x) (or (func? x) (macro? x) (prim? x) (func...? x)))

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
                  (unlazy
                   (cdr xs)
                   (λ (d)
                     (if (null? d)
                         (if (func...? r)
                             (aapply env r '())
                             r)
                         (if (f? r)
                             (aapply env r (cdr xs))
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
          [(func...? f)
           (aapply env (func (func...-v f)) (list (cons 'list xs)))]
          [(macro? f)
           (unlazy
            (aapply env (macro-v f) (lmap (λ (x) (list 'quote x)) xs))
            (λ (r)
              (if (f? r)
                  (macro r)
                  (eeval env r))))]
          [else (_!_)]))))))

(define fold foldl)

(define (env-append env ps)
  (fold (λ (p env) (envset env (car p) (cdr p))) env ps))

(define (env+record env r)
  (env-append env (hash->list (record-v r))))

; Exp → Env → Env
(define (cload e env) (env+record env (force+ (eeval env e))))

(define (mkpair xs f)
  (if (null? xs)
      (f '())
      (unlazy
       (car xs)
       (λ (s)
         (mkpair (cddr xs)
                 (λ (d)
                   (f (cons (cons s (cadr xs)) d))))))))

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

(define (catch-nothing x f)
  (with-handlers ([nothing? f])
    (if (promise? x)
        (delay (catch-nothing (with-handlers ([nothing? f]) (force x)) f))
        x)))

(define genv
  (cload prelude-sexp
         (env
          'quote (primm
                  1
                  (λ (env x)
                    x))
          'λ (primm
              2
              (λ (env s v)
                (unlazy
                 s
                 (λ (s)
                   (if (symbol? s)
                       (func (λ (x) (eeval (envset env s x) v)))
                       (_!_))))))
          'λ... (primm
                 2
                 (λ (env s v)
                   (unlazy
                    s
                    (λ (s)
                      (if (symbol? s)
                          (func... (λ (x) (eeval (envset env s x) v)))
                          (_!_))))))
          'λ? (primp 1 func?)
          'macro (primp 1 (λ (f) (if (func? f) (macro f) (_!_))))
          'macro? (primp 1 macro?)
          'pair? (primp 1 pair?)
          'cons (primf 2 cons)
          'car (primp 1 car)
          'cdr (primp 1 cdr)
          'null? (primp 1 null?)
          'list (primf 0 (λ xs xs))
          'true true
          'false false
          'boolean? (primp 1 boolean?)
          'if (primf 3 (λ (c t f)
                         (unlazy c (λ (c) (if c t f)))))
          'symbol? (primp 1 symbol?)
          '+ (primp 2 +)
          '- (primp 2 -)
          '* (primp 2 *)
          '/ (primp 2 /)
          '> (primp 2 >)
          '< (primp 2 <)
          '>= (primp 2 >=)
          '=< (primp 2 <=)
          'record (primm
                   0
                   (λ (env . xs)
                     (define newenv
                       (delay
                         (envset (env-append env (force+ rc)) '_< rec)))
                     (define rc
                       (delay
                         (mkpair
                          xs
                          (λ (ps)
                            (map (λ (p)
                                   (if (symbol? (car p))
                                       (cons (car p) (delay (eeval (force newenv) (cdr p))))
                                       (_!_))) ps)))))
                     (define rec
                       (unlazy
                        rc
                        (λ (rc)
                          (record (make-immutable-hasheq rc)))))
                     rec))
          'open (primm
                 2
                 (λ (env r x)
                   (unlazy
                    (eeval env r)
                    (λ (r)
                      (eeval (env+record env r) x)))))
          ': (primm
              2
              (λ (env r x)
                (unlazy
                 (eeval env r)
                 (λ (r)
                   (unlazy
                    x
                    (λ (s)
                      (hash-ref (record-v r) s)))))))
          '= (primf 2 (λ (x y) (ceq? x y (λ () true))))
          'nothing (delay (raise (nothing "")))
          'left (primf 1 (λ (x) (raise (nothing x))))
          'catch-nothing (primf
                          2
                          (λ (f x)
                            (catch-nothing x (λ (n) (capply f (list (nothing-v n)))))))
          'require (primm 2 (λ (env m x) (crequire env m (λ (nenv) (eeval nenv x)))))
          'apply (primf 2 (λ (f xs) (capply f xs)))
          'eval (primm 1 (λ (env x) (eeval env (eeval env x))))
          )))

(struct ioret (v))
(struct iocall/ccv (id x))
(struct iocall/cc (id x))
(struct iobind (x f))
(struct ioputstr (x))
(struct ioread-line ())

(define (io? x) (or (ioret? x) (iocall/ccv? x) (iocall/cc? x) (iobind? x) (ioputstr? x) (ioread-line? x)))

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
                                      (runio ((func-v x) r) f)))))]
       [(ioputstr? x) (unlazy (ioputstr-x x) (λ (s) (display s) (f '())))]
       [(iocall/ccv? x) x]
       [(iocall/cc? x) (runio (iocall/cc-x x)
                              (λ (r)
                                (if (equal? (iocall/ccv-id r) (iocall/cc-id x))
                                    (f (iocall/ccv-x r))
                                    (_!_))))]
       [(ioread-line? x) (f (read-line))]
       [else (_!_)]))))

(define io
  (record (hasheq 'return (primf 1 ioret)
                  '>>= (primf 2 iobind)
                  'putstr (primf 1 ioputstr)
                  'readline (ioread-line)
                  'call/cc (primf
                            1
                            (λ (f)
                              (let ([id (id!)])
                                (iocall/cc id (capply f (list (primf 1 (λ (x) (iocall/ccv id x))))))))))))

(define (crequire env m g)
  (unlazy
   m
   (λ (m)
     (cond
       [(eq? m 'io) (g (envset env 'io io))]
       [else (_!_)]))))
