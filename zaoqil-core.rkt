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
(provide core load-file)
(define-syntax-rule (deft (f x ...) v)
  (define (f x ...)
    (writeln (list (quote f) (force+ x) ...))
    (let ([r v])
      (let ([rf (force+ r)])
        (write (list (quote f) (force+ x) ...))
        (display " => ")
        (writeln rf)
        r))))

(define (read-file f) (read (open-input-file f)))
(define (load-file s f)
  (set! genv (env-set genv s (eeval genv (read-file f)))))

(include "zaoqil-core.scm")
