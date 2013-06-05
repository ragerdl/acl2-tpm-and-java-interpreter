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

(include-book "cutil/define" :dir :system)
(include-book "cutil/defenum" :dir :system)
(include-book "tpm-structures")
(include-book "tools/bstar" :dir :system)
(include-book "tpm-modeling-choices")

;; ctrl+meta+q s-expression to align

(cutil::define tpm-key->check
 ((key-input tpm-key-p "Tpm-key to check"))
 :returns (result tpm-result-p)
; body
 (b* (
      ((tpm-key key) key-input) ; ((tpm-key tpm-key) tpm-key)
      (alg-parms-input key.algorithm-parms)
      ((tpm-key-parms alg-parms) alg-parms-input) ; ((tpm-key-parms alg-parms) alg-parms)
      (enc alg-parms.enc-scheme)
      (sig alg-parms.sig-scheme))
     (case key.key-usage
       (:tpm-key-signing
        (if (or (not (equal enc :tpm-es-none))
                (and (not (equal sig :tpm-ss-rsassapkcs1v15-der))
                     (not (equal sig :tpm-ss-rsassapkcs1v15-info))
                     (not (equal sig :tpm-ss-rsassapkcs1v15-sha1))))
            :tpm-bad-key-property
          :tpm-success))
       ((:tpm-key-storage :tpm-key-migrate :tpm-key-authchange)
        (if (or (not (equal enc :tpm-es-rsaesoaep-sha1-mgf1))
                (not (equal sig :tpm-ss-none)))
            :tpm-bad-key-property
          :tpm-success))
       (:tpm-key-identity
        (if (or (not (equal enc :tpm-es-none))
                (not (equal sig :tpm-ss-rsassapkcs1v15-sha1)))
            :tpm-bad-key-property
          :tpm-success))
       (:tpm-key-bind
        (if (or (and (not (equal enc :tpm-es-rsaesoaep-sha1-mgf1))
                     (not (equal enc :tpm-es-rsaespkcsv15))
                     (not (equal sig :tpm-ss-none))))
            :tpm-bad-key-property
          :tpm-success))
       (:tpm-key-legacy
        (if (or (and (not (equal enc :tpm-es-rsaesoaep-sha1-mgf1))
                     (not (equal enc :tpm-es-rsaespkcsv15)))
                (and (not (equal sig :tpm-ss-rsassapkcs1v15-sha1))
                     (not (equal sig :tpm-ss-rsassapkcs1v15-sha1))))
            :tpm-bad-key-property
          :tpm-success))
       (otherwise :tpm-bad-key-property))))

(program)

(cutil::define tpm-key->check-make-identity
 ((key-input tpm-key-p "Key to check")
  (tpm-data-input tpmx-internal-data-p "Tpm internal data"))
 :returns (result tpm-result-p)
; body
 (b* (
      ((tpm-key key) key-input)
      ((tpmx-internal-data tpm-data) tpm-data-input)
      ((tpm-key-parms alg-parms) key.algorithm-parms)
      ((tpm-rsa-key-parms rsa) alg-parms.rsa)
      ((tpm-permanent-flags perm-flags) tpm-data.permanent-flags)
      ((tpm-key-flags key-flags) key.key-flags))
     ((when (not (equal (tpm-key->check key) :tpm-success)))
	(tpm-key->check key))
     (cond
      ;; 4. Verify that idKeyParams -> keyUsage is TPM_KEY_IDENTITY. If it is not, return TPM_INVALID_KEYUSAGE
      ((not (equal key.key-usage :tpm-key-identity))
       :tpm-invalid-keyusage)
      ;; 1. Validate the idKeyParams parameters for the key description
      ;; 1.a. If the algorithm type is RSA, the key length MUST be a minimum of 2048 and MUST use the default exponent. For interoperability the key length SHOULD be 2048.
      ;; 1.b. If the algorithm type is other than RSA the strength provided by the key MUST be comparable to RSA 2048
      ;; 1.c. If the TPM is not designed to create a key of the requested type, return the error code TPM_BAD_KEY_PROPERTY
      ;; TPMX: Only RSA with 2048-bit key, 2 primes, and 0 exponent supported
      ((or (not (equal alg-parms.algorithm-id :tpm-alg-rsa))
	   (not (equal rsa.key-length 2048))
	   (not (equal rsa.num-primes 2))
	   (not (equal rsa.exponent 0)))
       :tpm-bad-key-property)
      ;; 1.d. If TPM_PERMANENT_FLAGS -> FIPS is TRUE then
      ;; 1.d.i. If authDataUsage specifies TPM_AUTH_NEVER return TPM_NOTFIPS
      ((and perm-flags.fips
	    (equal key.auth-data-usage :tpm-auth-never)) 
       :tpm-notfips)
      ;; 5. Verify that idKeyParams -> keyFlags -> migratable is FALSE. If it is not, return TPM_INVALID_KEYUSAGE
      ((not key-flags.migratable)
       :tpm-invalid-keyusage)
      (t
       :tpm-success))))

(cutil::define tpm-key->check-create-wrap-key
 ((key tpm-key-p "Primary key to check")
  (parent tpm-key-p "Parent key to check")
  (tpm-data tpmx-internal-data-p "Tpm internal data"))
 :returns (result tpm-result-p)
; body
 (b* (
      ((tpm-key key) key)
      ((tpm-key parent) parent)
      ((tpmx-internal-data tpm-data) tpm-data)

      ((tpm-key-parms alg-parms) key.algorithm-parms)
      ((tpm-rsa-key-parms rsa) alg-parms.rsa)
      ((tpm-permanent-flags perm-flags) tpm-data.permanent-flags)
      ((tpm-key-flags key-flags) key.key-flags))
     ((when (not (equal (tpm-key->check key) :tpm-success)))
	(tpm-key->check key))
     ((when (not (equal (tpm-key->check parent) :tpm-success)))
	(tpm-key->check parent))
     (case
      ;; 4. Verify that parentHandle -> keyUsage equals TPM_KEY_STORAGE
      ;; 5. If parentHandle -> keyFlags -> migratable is TRUE and keyInfo -> keyFlags -> migratable is FALSE then return TPM_INVALID_KEYUSAGE
      ;; 6. Validate key parameters
      ;; 6.a. keyInfo -> keyUsage MUST NOT be TPM_KEY_IDENTITY or TPM_KEY_AUTHCHANGE. If it is, return TPM_INVALID_KEYUSAGE
      ;; 6.b. If keyInfo -> keyFlags -> migrateAuthority is TRUE then return TPM_INVALID_KEYUSAGE
      ((or (not (equal parent.key-usage :tpm-key-storage))
	   (and parent-flags.tpm-key-flag-migratable
		(not key-flags.tpm-key-flag-migratable))
	   (equal key.key-usage :tpm-key-identity)
	   (equal key.key-usage :tpm-key-authchange)
	   key-flags.migrate-authority)
       :tpm-invalid-keyusage)
      ;; 7. If TPM_PERMANENT_FLAGS -> FIPS is TRUE then
      ;; 7.a. If keyInfo -> keySize is less than 1024 return TPM_NOTFIPS
      ;; 7.b. If keyInfo -> authDataUsage specifies TPM_AUTH_NEVER return TPM_NOTFIPS
      ;; 7.c. If keyInfo -> keyUsage specifies TPM_KEY_LEGACY return TPM_NOTFIPS
      ((and tpmData.permanent.flags.FIPS
	    (or (< rsa.key-length 1024)
		(equal key.auth-data-usage :tpm-auth-never)
		(equal key.key-usage :tpm-key-legacy)))
       :tpm-notfips)
      ;; 8. If keyInfo -> keyUsage equals TPM_KEY_STORAGE or TPM_KEY_MIGRATE
      ;; 8.i. algorithmID MUST be TPM_ALG_RSA
      ;; 8.ii. encScheme MUST be TPM_ES_RSAESOAEP_SHA1_MGF1 [TPMX: part of default tpm-key check]
      ;; 8.iii. sigScheme MUST be TPM_SS_NONE [TPMX: part of default tpm-key check]
      ;; 8.iv. key size MUST be 2048
      ;; 8.v. exponentSize MUST be 0
      ((and (or (equal key.key-usage :tpm-key-storage)
		(equal key.key-usage :tpm-key-migrate))
	    (or (not (equal alg-parms.algorithm-id :tpm-alg-rsa))
		(not (equal rsa.key-length 2048))))
       :tpm-bad-key-property)
      ;; 3. If the TPM is not designed to create a key of the type requested in keyInfo, return the error code TPM_BAD_KEY_PROPERTY
      ((or (not (equal alg-parms.algorithm-id :tpm-alg-rsa))
	   (< rsa.key-length 512)
	   (not (equal rsa.num-primes 2))
	   (not (equal rsa.exponent-size 0)))
       :tpm-bad-key-property)
      (t
       :tpm-success))))

