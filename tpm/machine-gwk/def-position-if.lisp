; ACL2 TPM  Model
; Copyright (C) 2013 Battelle Memorial Institute
;
; Contact:
;  David Rager, ragerdl@cs.utexas.edu
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original authors: David Rager <ragerdl@cs.utexas.edu> and
;                   Greg Kulczycki

(in-package "ACL2")

(defmacro def-position-if (function-name comparison-expr
                                         &key guard)
; When using position-if, we have to know that X and LST are the names of
; variables chosen to represent the element against which to compare, and the
; list.
  (let ((declaration (if guard 
                         `((declare (xargs :guard ,guard)))
                       nil)))
    `(progn
       (defun ,function-name (x lst)
         ,@declaration
         (cond ((atom lst)
                -1)
               (,comparison-expr 
                0)
               (t
                (+ 1 (,function-name x (cdr lst))))))
       (defthm nth-of-function-name ; need to explode-atom
         (implies ,guard
                  (let ((index 

))
#|
(def-position-if position-car (equal (caar lst) x))

(position-car 3 '( ( 1 . 2) ( 3 . 4) ( 5 . 6)))


(def-position-if position-invalid-session
 (equal (tpm-session-data->session-type (car lst))
        :tpmx-st-invalid))

(position-invalid-session ...)
|#
