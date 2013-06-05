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

(include-book "tpm-structures")
(include-book "defenum-plus")
(include-book "tpm-objects")

(defenum+ tpm-input-p

; A tpm-input includes both an instruction to execute and the arguments to that
; instruction.  Below, we list the instructions we support and the predicates
; that their arguments must satisfy.  We use this predicate to specify the
; guard for the tpm-step function of the tpm.

  ((:tpm-owner-install booleanp tpmx-internal-data-p)
   (:tpm-owner-set-disable booleanp tpmx-auth-info-p tpmx-internal-data-p)
   (:tpm-physical-enable tpmx-internal-data-p)
   (:tpm-physical-disable tpmx-internal-data-p))

; ...

  )




(defun tpm-input->command (x)

; This definition could be part of defenum+ in the future.

  (declare (xargs :guard (tpm-input-p x)))
  (cond ((atom x)
         x)
        (t (car x))))

(defun tpm-input->arg1 (x)
  (declare (xargs :guard (tpm-input-p x)))
  (cond ((atom x)

; (er hard? ...) causes an error when run but logically returns nil

         (er hard? 'tpm-input->arg1 
             "tpm-input->arg1 ~x0 does not have an argument"
             x))
        ((atom (cdr x))
         (er hard? 'tpm-input->arg1 
             "tpm-input->arg1 ~x0 does not have an argument"
             x))
        (t (cadr x))))

(defun tpm-input->arg2 (x)
  (declare (xargs :guard (tpm-input-p x)))
  (cond ((atom x)

; (er hard? ...) causes an error when run but logically returns nil

         (er hard? 'tpm-input->arg2
             "tpm-input->arg2 ~x0 does not have a second argument"
             x))
        ((atom (cdr x))
         (er hard? 'tpm-input->arg2 
             "tpm-input->arg2 ~x0 does not have a second argument"
             x))
        ((atom (cddr x))
         (er hard? 'tpm-input->arg2
             "tpm-input->arg2 ~x0 does not have a second argument"
             x))
        (t (caddr x))))

(defun tpm-input->arg3 (x)
  (declare (xargs :guard (tpm-input-p x)))
  (cond ((atom x)

; (er hard? ...) causes an error when run but logically returns nil

         (er hard? 'tpm-input->arg3
             "tpm-input->arg3 ~x0 does not have a third argument"
             x))
        ((atom (cdr x))
         (er hard? 'tpm-input->arg3 
             "tpm-input->arg3 ~x0 does not have a third argument"
             x))
        ((atom (cddr x))
         (er hard? 'tpm-input->arg3
             "tpm-input->arg3 ~x0 does not have a third argument"
             x))
        ((atom (cdddr x))
         (er hard? 'tpm-input->arg3
             "tpm-input->arg3 ~x0 does not have a third argument"
             x))

        (t (cadddr x))))
