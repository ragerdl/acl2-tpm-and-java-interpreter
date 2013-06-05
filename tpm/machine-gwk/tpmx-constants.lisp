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

(include-book "misc/assert" :dir :system)

;; See SHA-1 commands 13.1 - 13.4
;; This must be a multiple of 64
;; BerliOS uses 2048
;; We use 64 because we are simulation SHA-1 by keeping only the first byte of input data
(defconst *tpmx-sha1-max-bytes* 64)
(assert! (equal (mod *tpmx-sha1-max-bytes* 64) 0))

;; Used in TPM_PERMANENT_DATA pcrAttrib (7.4) and TPM_STCLEAR_DATA PCR (7.5)
;; PC Client TIS requires a minimum of 24 PCRs
(defconst *tpmx-num-pcrs* 24)
(assert! (>= *tpmx-num-pcrs* 24))

;; Used in TPM_STANY_DATA sessions (7.6)
;; TCG spec requires min of 3
;; BerliOS uses 4
(defconst *tpmx-max-sessions* 3)
(assert! (>= *tpmx-max-sessions* 3))

;; Used in TPM_STANY_DATA context list (7.6)
;; TCG spec requires min of 16
;; BerliOS uses 16
(defconst *tpmx-max-session-list* 16)
(assert! (>= *tpmx-max-session-list* 16))

;; GWK: It is not clear yet whether we will use this in our implementation
;; Used in TPM_STANY_DATA sessions daa [in place of daa session (22.7)]
;; Berlios creates sessions daa as an array so handles can be treated
;; consistently as array indexes
;; As there is only one session, this number is 1
;; (defconst *tpmx-max-sessions-daa* 1)
;; (assert! (>= *tpmx-max-sessions-daa* 1))

;; 
