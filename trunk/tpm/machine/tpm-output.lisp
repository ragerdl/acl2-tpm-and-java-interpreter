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
(include-book "tpm-structures-fixup")
(include-book "defenum-plus")

(defenum+ tpm-output-p

; A tpm-input includes both an instruction to execute and the arguments to that
; instruction.  Below, we list the instructions we support and the predicates
; that their arguments must satisfy.  We use this predicate to specify the
; guard for the tpm-step function of the tpm.

  ((:tpm-owner-install tpmx-internal-data-p)
   (:tpm-owner-set-disable tpmx-internal-data-p)
   (:tpm-physical-enable tpmx-internal-data-p)
   (:tpm-physical-disable tpmx-internal-data-p)

; ...

   (:tpm-get-test-result byte-list-p tpmx-internal-data-p)

   ))
