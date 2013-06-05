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
; Original author: David Rager <ragerdl@cs.utexas.edu>

(in-package "ACL2")

(include-book "tools/bstar" :dir :system)

(program)

(defun times-eight-no-error-checking (x)
  (let* ((double-x (+ x x))
         (quadruple-x (+ double-x double-x)))
    (+ quadruple-x quadruple-x)))

(times-eight-no-error-checking 1)

(defun times-eight-with-error-checking (x)
  (b* (((when (not (integerp x))) 
        'error)
       (double-x (+ x x))
       ((when (not 'always-non-nil))
        'error-too)
       (quadruple-x (+ double-x double-x)))
    (+ quadruple-x quadruple-x)))
  
(times-eight-with-error-checking 1)

(times-eight-with-error-checking "hi")
