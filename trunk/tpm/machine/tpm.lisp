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

(include-book "xdoc/top" :dir :system)

(include-book "tpmx-constants")
(include-book "tpm-structures")
(include-book "tpmx-objects")
(include-book "tpm-commands")

(defxdoc tpm
  :short "An ACL2 model for the Trusted Platform Module (TPM)"
  :long "We are modeling the TPM in ACL2.

         There is a section for tpm commands that we have finished implementing
         @(see tpm-finished), and a section for those which only have a partial
         implementation @(see tpm-unfinished).")

(defxdoc tpm-commands
  :parents (tpm)
  :short "Topic for collecting the TPM commands")

(defxdoc tpmx-commands
  :parents (tpm)
  :short "Topic for collecting subcommands that we write to implement the tpm
  commands.  The \"x\" is short for \"extension\".")

(defxdoc tpm-structures
  :parents (tpm)
  :short "Topic for collecting the TPM structures, mostly as derived from the
  TCG spec.")

(defxdoc tpmx-objects
  :parents (tpm)
  :short "Topic for collecting objects that we write to implement the tpm
  commands.  The \"x\" is short for \"extension\".  We have a separate notion
  of an object, because objects can also have commands defined upon them.")

;; (defxdoc tpmx-object-commands
;;   :parents (tpmx-objects)
;;   :short "Topic for collecting commands that operate upon tpmx
;;   commands.  The \"x\" is short for \"extension\".")


(defxdoc tpm-finished
  :parents (tpm)
  :short "Topic for collecting the TPM components that we think we have finished
          modeling.")
  
(defxdoc tpm-unfinished
  :parents (tpm)
  :short "Topic for collecting the TPM components that we have not finished
          modeling.")

(defxdoc tpm-oddly-finished
  :parents (tpm)
  :short "Topic for collecting the TPM components that we have finished, but in an
          odd way that needs review.")
