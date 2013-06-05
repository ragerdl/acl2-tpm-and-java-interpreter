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

#|
(include-book "tpm-input")
(include-book "tools/bstar" :dir :system)

(define tpm-step
  ((instruction-and-args tpm-input-p "Instruction to execute.  E.g., :tpm-startup,
                                      :tpm-save-state"))
  :returns (tpm-output tpm-output-p "Output of the TPM, includes tpmx-internal-data-p")
  (b* ((cmd (tpm-input->command instruction-and-args))
       (arg1 (if (<= 1 (tpm-input->arg-count instruction-and-args))
                 (tpm-input->arg1 instruction-and-args)
               nil))
       (arg2 (if (<= 2 (tpm-input->arg-count instruction-and-args))
                 (tpm-input->arg2 instruction-and-args)
               nil))
       (arg3 (if (<= 3 (tpm-input->arg-count instruction-and-args))
                 (tpm-input->arg3 instruction-and-args)
               nil))
       (arg4 (if (<= 4 (tpm-input->arg-count instruction-and-args))
                 (tpm-input->arg4 instruction-and-args)
               nil))
       (arg5 (if (<= 5 (tpm-input->arg-count instruction-and-args))
                 (tpm-input->arg5 instruction-and-args)
               nil))
       (tpm-output 
        (mv-list
         (case cmd
           (:tpm-owner-install (tpm-owner-install 
    
    
|#
