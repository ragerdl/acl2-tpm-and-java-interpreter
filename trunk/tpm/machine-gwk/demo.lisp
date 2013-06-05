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

(include-book "tpm")

(defconst *default-tpmx-internal-data*
  (make-tpmx-internal-data))

(defconst *64-byte-list*
  '(1 2 3 4 5 6 7 8 9 
    10 11 12 13 14 15 16 17 18 19 
    20 21 22 23 24 25 26 27 28 29 
    30 31 32 33 34 35 36 37 38 39 
    40 41 42 43 44 45 46 47 48 49 
    50 51 52 53 54 55 56 57 58 59 
    60 61 62 63 64))

(mv-let (tpm-data return-code1 max-num-bytes)
  (tpm-sha1-start *default-tpmx-internal-data*)
  (assert$ (and (equal return-code1 :tpm-success)
                (equal max-num-bytes *tpmx-sha1-max-bytes*))
    (mv-let (tpm-data return-code2)
      (tpm-sha1-update tpm-data 
                       *64-byte-list*)
      (assert$ (and (equal return-code2 :tpm-success)
                    ;; some property about internal hash value
                    )
        (mv-let (tpm-data return-code3 hash-value)
          (tpm-sha1-complete tpm-data 
                             *64-byte-list*)
          (assert$ (and (equal return-code3 :tpm-success)
                        (equal (tpm-digest->value hash-value)
                               1335441244180744576605065311518458060268273638140682576462189443234290070969642913723260848524035534865541346463041953262997891104436750586970625702775419651212084355287395490435203028498610257))
            "Basic test passed!"))))))


(thm
 (mv-let (tpm-data return-code1 max-num-bytes)
  (tpm-sha1-start *default-tpmx-internal-data*)
    (mv-let (tpm-data return-code2)
      (tpm-sha1-update tpm-data 
                       *64-byte-list*)
      (mv-let (tpm-data return-code3 hash-value)
        (tpm-sha1-complete tpm-data *64-byte-list*)
        (and (equal return-code1 :tpm-success)
             (equal max-num-bytes *tpmx-sha1-max-bytes*)
             (equal return-code2 :tpm-success)
             (equal return-code3 :tpm-success)
             (equal (tpm-digest->value hash-value)
                    1335441244180744576605065311518458060268273638140682576462189443234290070969642913723260848524035534865541346463041953262997891104436750586970625702775419651212084355287395490435203028498610257)
             )))))
                        
