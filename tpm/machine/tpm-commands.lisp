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
(include-book "tools/bstar" :dir :system)
;(include-book "tpm-modeling-choices")
(include-book "tpm-structures")
(include-book "tpmx-constants")
(include-book "tpmx-objects")

(program)

;; 3.1 TPM_Init
(cutil::define tpm-init
  ((tpm-data-in tpmx-internal-data-p "TPM data"))
  :returns (mv (tpm-data-out tpmx-internal-data-p "TPM data" :hyp :fguard)
               (return-code tpm-result-p "The return code of the operation."
                            :hyp :fguard))
  :parents (tpm-commands)
  ;; Function Body
  (b* (((tpmx-internal-data tpm-data) tpm-data-in))
    (mv (change-tpmx-internal-data tpm-data-in
                                   :stany-flags
                                   (change-tpm-stany-flags tpm-data.stany-flags
                                                           :post-initialise t))
        :tpm-success)))

; (set-ignore-ok t)

; (program)

#|
;; The following definition motivates our need to have better constructors.

;; 3.2 TPM_Startup
(cutil::define tpm-startup
  ((tpm-data-in tpmx-internal-data-p "TPM data")
   (startup-type tpm-startup-type-p "Type of startup that is occurring"))
  :returns (mv (tpm-data-out tpmx-internal-data-p "TPM data" :hyp :fguard) 
               (return-code tpm-result-p "The return code of the operation." :hyp :fguard))
  (b* (((when (not (tpm-stany-flags->post-initialise ; spelling
                    (tpmx-internal-data->stany-flags tpm-data-in))))
        ;(tpmx-internal-data->stany-flags->post-initialise tpm-data-in)
        (mv tpm-data-in :tpm-invalid-postinit))
       (tpm-data-in
        (if (equal startup-type :tpm-st-clear)
            (b* ((tpm-data-in
                    (change-tpmx-internal-data :stany-data
                                               (make-tpm-stany-data)
                                               tpm-data-in)))
                tpm-data-in)
          tpm-data-in))
; set tpm-data-in->stany-data to whatever is returned by
; (make-tpm-stany-data)
                  
       )


; so we can admit function
      (mv tpm-data-in :tpm-success)))
|#


;; 3.3 TPM_SaveState
(cutil::define tpm-save-state
  ((tpm-data tpmx-internal-data-p "TPM data"))
  :returns (mv (tpm-data tpmx-internal-data-p "TPM data" :hyp :fguard)
               (return-code tpm-result-p "The return code of the operation."
                            :hyp :fguard))
  :parents (tpm-commands tpm-unfinished#|tpm-oddly-finished|#)
  ;; Disregarding the specification that the tpm may declare all preserved values
  ;; invalid in response to any command other than tpm-init.
  (b* (((tpmx-internal-data tpm-data) tpm-data))
    (mv #|(change-tpmx-internal-data tpm-data
                                   :saved-data
                                   (make-tpmx-internal-saved-data
                                    :permanent-flags tpm-data.permanent-flags
                                    :stclear-flags tpm-data.stclear-flags
                                    :stany-flags tpm-data.stany-flags
                                    :permanent-data tpm-data.permanent-data
                                    :stclear-data tpm-data.stclear-data
                                    :stany-data tpm-data.stany-data))|#
        tpm-data
        :TPM-SUCCESS)))




;; 6.4 TPM_DisableOwnerClear
(cutil::define tpmx-verify-auth
  ((auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-result tpm-result-p)
               (auth1 tpmx-auth-info-p :hyp :fguard))
  :parents (tpm-commands tpm-unfinished)
  :short "Check that the authorization data is valid"
  :long "Can use OIAP, OSAP, or DASP to authenticate."
  (mv :tpm-success auth1))

(cutil::define tpm-disable-owner-clear
  ((tpm-data tpmx-internal-data-p "TPM data")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "TPM data" :hyp :fguard)
               (return-code tpm-result-p "The return code of the operation." :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents (tpmx-commands tpm-oddly-finished)
  (b* (

; Setup class accessors
       
       ((tpmx-internal-data tpm-data) tpm-data)
       ((tpm-permanent-flags flags) tpm-data.permanent-flags)
       ((mv tpm-result auth1)
        (tpmx-verify-auth auth1))

       ((when (not (equal tpm-result :tpm-success)))
; Unclear whether :tpm-authfail is the right call
        (mv tpm-data tpm-result auth1))
       
       (tpm-data
        (change-tpmx-internal-data tpm-data
                                   :permanent-flags 
                                   (change-tpm-permanent-flags tpm-data.permanent-flags
                                                               :disable-owner-clear
                                                               t))))
    (mv tpm-data :tpm-success auth1)))

;; 6.5 TPM_DisableForceClear
(cutil::define tpm-disable-force-clear
  ((tpm-data-in tpmx-internal-data-p "TPM data"))
  :returns (mv (tpm-data-out tpmx-internal-data-p "TPM data" :hyp :fguard)
               (return-code tpm-result-p "The return code of the operation." :hyp :fguard))
  :parents (tpm-commands tpm-finished)
  :short "Disable the force clear flag of the tpm"

  (b* (

; Setup class accessors
       
       ((tpmx-internal-data tpm-data) tpm-data-in) ; would like to name tpm-data instead of tpm-data
       ((tpm-stclear-flags flags) tpm-data.stclear-flags)
       (tpm-data
        (change-tpmx-internal-data tpm-data-in
                                   :stclear-flags 
                                   (change-tpm-stclear-flags tpm-data.stclear-flags
                                                             :disable-force-clear
                                                             t))))
    (mv tpm-data :tpm-success)))


;; 6.7 TPM_ResetEstablishmentBit
(cutil::define tpm-reset-establishment-bit
  ((tpm-data tpmx-internal-data-p "TPM data"))
  :returns (mv (tpm-data tpmx-internal-data-p "TPM data" :hyp :fguard)
               (return-code tpm-result-p "The return code of the operation." :hyp :fguard))
  :parents (tpm-commands tpm-finished)
  (b* (((tpmx-internal-data tpm-data) tpm-data))
    (mv (change-tpmx-internal-data tpm-data
                                   :permanent-flags
                                   (change-tpm-permanent-flags tpm-data.permanent-flags
                                                               :tpm-established
                                                               t))
        :tpm-success)))


;; 7.3 TPM_GetCapabilityOwner
(include-book "centaur/misc/arith-equivs" :dir :system)
(include-book "ihs/logops-definitions" :dir :system)

(in-theory (disable logapp)) ; should probably be disabled already

(cutil::define tpmx-marshall-permament-flags 
  ((perm-flags tpm-permanent-flags-p "TPM permament flags"))
  :returns (marshalled-perm-flags integerp "Marshalled version of permament
                                             flags")
  :parents (tpm-finished tpm-get-capability-owner)
  :long "We skip marshalling the tpm-structure-tag-p"
  (b* (((tpm-permanent-flags flags) perm-flags))
    (make-word-from-bits (bool->bit flags.disable)
                         (bool->bit flags.ownership)
                         (bool->bit flags.deactivated)
                         (bool->bit flags.read-pubek)
                         (bool->bit flags.disable-owner-clear)
                         (bool->bit flags.allow-maintenance)
                         (bool->bit flags.physical-presence-lifetime-lock)
                         (bool->bit flags.physical-presence-hw-enable)
                         (bool->bit flags.physical-presence-cmd-enable)
                         (bool->bit flags.cekp-used)
                         (bool->bit flags.tp-mpost)
                         (bool->bit flags.tp-mpost-lock)
                         (bool->bit flags.fips)
                         (bool->bit flags.operator)
                         (bool->bit flags.enable-revoke-ek)
                         (bool->bit flags.nv-locked)
                         (bool->bit flags.read-srk-pub)
                         (bool->bit flags.tpm-established)
                         (bool->bit flags.maintenance-done)
                         (bool->bit flags.disable-full-da-logic-info))))

(cutil::define tpmx-marshall-stclear-flags 
  ((stclear-flags tpm-stclear-flags-p "TPM permament flags"))
  :returns (marshalled-stclear-flags integerp "Marshalled version of stclear
                                               flags")
  :parents (tpm-finished tpm-get-capability-owner)
  :long "We skip marshalling the tpm-structure-tag-p"
  (b* (((tpm-stclear-flags flags) stclear-flags))
    (make-word-from-bits (bool->bit flags.deactivated)
                         (bool->bit flags.disable-force-clear)
                         (bool->bit flags.physical-presence)
                         (bool->bit flags.physical-presence-lock)
                         (bool->bit flags.b-global-lock))))



   
#|
(cutil::define tpm-get-capability-owner
  ((tpm-data-in tpmx-internal-data-p "TPM data")
   (auth1-in tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data-out tpmx-internal-data-p "TPM data" :hyp :fguard)
               (return-code tpm-result-p "The return code of the operation." :hyp :fguard)
               (version tpm-version-p "A properly filled out version structure." :hyp :fguard)
               (non-volatile-flags uint32-p "The current state of the non-volatile flags." :hyp :fguard)
               (volatile-flags uint32-p "The current state of the volatile flags." :hyp :fguard)
               (auth1-out tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  ;; Function Body
  nil)
|#

(logic)

;; 13.1 TPM_SHA1Start
(cutil::define tpm-sha1-start
  ((tpm-data tpmx-internal-data-p "Internal TPM data"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (max-num-bytes integerp "Maximum number of bytes that can be sent to TPM_SHA1Update. Must be a multiple of 64 bytes." :hyp :fguard))
  :parents (tpm-commands)
  ;; Function Body
  
  ;; Description
  ;; 1. This capability prepares the TPM for a subsequent TPM_SHA1Update, TPM_SHA1Complete or TPM_SHA1CompleteExtend command. The capability SHALL open a thread that calculates a SHA-1 digest.
  ;; 2. After receipt of TPM_SHA1Start, and prior to the receipt of TPM_SHA1Complete or TPM_SHA1CompleteExtend, receipt of any command other than TPM_SHA1Update invalidates the SHA-1 session.
  ;; 2.a. If the command received is TPM_ExecuteTransport, the SHA-1 session invalidation is based on the wrapped command, not the TPM_ExecuteTransport ordinal.
  ;; 2.b. A SHA-1 thread (start, update, complete) MUST take place either completely outside a transport session or completely within a single transport session.
  ;; 
  ;; Actions (none)

  (b* (
       ;; new tpm-data
       ((tpmx-internal-data tpm-data) tpm-data)

       ;; if thread is already active, return error
       ;; ((when tpmx-sha1-thread->active tpm-data.sha1-thread) (mv tpm-data
       ;;                                                           :sha1-thread
       ;;                                                           *tpmx-sha1-max-bytes*))

       ;; don't need if returning error when thread is active
       (sha1-thread (if (tpmx-sha1-thread->active tpm-data.sha1-thread) ;; if active
                        (make-tpmx-sha1-thread) ;; reset thread
                        tpm-data.sha1-thread))  ;; use current thread
       (sha1-thread (tpmx-sha1-thread->start sha1-thread)) ;; start thread
       (tpm-data (change-tpmx-internal-data tpm-data
                                            :sha1-thread sha1-thread)) ;; new tpm-data
       )
      (mv tpm-data
          :tpm-success
          *tpmx-sha1-max-bytes*)))

; On 4/30/2013 Greg and Rager had a discussion concerning whether we will allow
; one tpm spec function to call another tpm spec function so it can fulfill its
; implementation obligation.  We agreed upon the following four ideas to guide
; us:
;
; (1) It is okay for a tpm spec function to call another tpm spec function.
;     For example, tpm-sha1-complete can call tpm-sha1-update.  We will refer
;     to the calling function (e.g., tpm-sha1-complete) as foo and the called
;     function (e.g., tpm-sha1-update) as bar.
;
; (2) We are obliged to place corresponding postconditions that we place upon
;     the called function (e.g., tpm-sha1-update) also upon the postconditions
;     of the calling function (e.g., tpm-sha1-complete) (probably via a
;     copy+paste).  For example, if tpm-sha1-update makes a statement about the
;     resulting thread's active property, tpm-sha1-complete should also attempt
;     to make a statement about the resulting thread's active property (even
;     though it might be the opposite statement).
;
; (3) When reasoning about the calling function (e.g., tpm-sha1-complete), it
;     is okay to enable the called function (e.g., tpm-sha1-update).
;
; (4) We might use the reasoning about the calling function to help discover
;     preconditions that we wish to place upon the called function.  This would
;     probably only work if we left the called function disabled (which is a
;     contradiction of (3), above).  Figuring out how often we want to enable
;     or disable the called function when reasoning about the calling function
;     is an open question for our work.

;; 13.2 TPM_SHA1Update
(cutil::define tpm-sha1-update
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (hash-data byte-list-p "Bytes to be hashed"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard))
  :parents(tpm-commands)

  :long ; I thought about putting the description in a :short section, as shown above
  "<h1>Description</h1> 

   <p>This command SHALL incorporate complete blocks of data into the digest of
      an existing SHA-1 thread. Only integral numbers of complete blocks (64
      bytes each) can be processed.</p>

   <h2>Actions</h2>
   <ol>
     <li>If there is no existing SHA-1 thread, return TPM_SHA_THREAD</li>
     <li>If numBytes is not a multiple of 64
       <ul>
         <li>Return TPM_SHA_ERROR</li>
         <li>The TPM MAY terminate the SHA-1 thread</li>
       </ul>
      </li>
      <li>If numBytes is greater than maxNumBytes returned by TPM_SHA1Start
        <ul>
          <li>Return TPM_SHA_ERROR</li>
          <li>The TPM MAY terminate the SHA-1 thread</li>
       </ul>
      </li>
      <li>Incorporate hashData into the digest of the existing SHA-1 thread.</li>
    </ol>"

  ;; Function Body

  ;; Description
  ;; This command SHALL incorporate complete blocks of data into the digest of an existing SHA-1 thread. Only integral numbers of complete blocks (64 bytes each) can be processed.
  ;;
  ;; Actions
  ;; 1. If there is no existing SHA-1 thread, return TPM_SHA_THREAD
  ;; 2. If numBytes is not a multiple of 64
  ;; 2.a. Return TPM_SHA_ERROR
  ;; 2.b. The TPM MAY terminate the SHA-1 thread
  ;; 3. If numBytes is greater than maxNumBytes returned by TPM_SHA1Start
  ;; 3.a. Return TPM_SHA_ERROR
  ;; 3.b. The TPM MAY terminate the SHA-1 thread
  ;; 4. Incorporate hashData into the digest of the existing SHA-1 thread.

  (b* (
       ;; field access for defaggregate params
       ((tpmx-internal-data tpm-data) tpm-data)
       (sha1-thread tpm-data.sha1-thread)
       ((tpmx-sha1-thread sha1-thread) sha1-thread)

       ;; on error, TPM resets the sha1-thread
       (tpm-data-stop (change-tpmx-internal-data tpm-data
						 :sha1-thread (make-tpmx-sha1-thread)))
       
       ;; return error code
       ((when (not sha1-thread.active))
	      (mv tpm-data-stop :tpm-sha-thread))
       ((when sha1-thread.complete) ;; TODO: eventually, prove this can never occur
              (mv tpm-data-stop :tpmx-error))
       ((when (or (not (equal (length hash-data) 64))
		  (> (length hash-data) *tpmx-sha1-max-bytes*)))
	      (mv tpm-data-stop :tpm-sha-error))

       ;; new tpm-data
       (sha1-thread (tpmx-sha1-thread->update sha1-thread hash-data))
       (tpm-data (change-tpmx-internal-data tpm-data
                                            :sha1-thread sha1-thread))
      )
      (mv tpm-data :tpm-success))

  ///
  (defthm tpm-sha1-update-post-conditions
    (implies (and (tpmx-internal-data-p tpm-data-in)
                  (byte-list-p hash-data-in))
             (b* (
                  ((mv tpm-data-out return-code) (tpm-sha1-update tpm-data-in hash-data-in))
                  ((tpmx-internal-data tpm-data-out) tpm-data-out)
                 )
                 (implies (equal return-code :tpm-success)
                          (and (tpmx-sha1-thread->active tpm-data-out.sha1-thread)
                               (not (tpmx-sha1-thread->complete tpm-data-out.sha1-thread)))))))
)

;; 13.3 TPM_SHA1Complete
(cutil::define tpm-sha1-complete
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (hash-data byte-list-p "Final bytes to be hashed"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               ;; :hints(("Goal" :in-theory (enable tpmx-sha1-thread->update))))
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (hash-value tpm-digest-p "The output of the SHA-1 hash." :hyp
                           :fguard))
  ;; GWK: We can enable tpm-sha1-update (for all guards) instead of writing a post-condition for it
  ;; :guard-hints (("Goal" :in-theory (enable tpm-sha1-update)))
  ;; :guard-debug t
  :parents(tpm-commands)
  ;; Function Body

  ;; Description
  ;; This command SHALL incorporate a partial or complete block of data into the digest of an existing SHA-1 thread, and terminate that thread.
  ;; hashDataSize MAY have values in the range of 0 through 64, inclusive.
  ;; If the SHA-1 thread has received no bytes the TPM SHALL calculate the SHA-1 of the empty buffer.        

  (b* (
       ((mv tpm-data return-code) (tpm-sha1-update tpm-data hash-data)) ;; Call TPM_Sha1Update
       ((when (not (equal return-code :tpm-success)))
        (mv tpm-data
            return-code
            (make-tpm-digest :value 0))) 
       ((tpmx-internal-data tpm-data) tpm-data)

       ;; We need a theorem here to prove that 'update' leaves the thread in a
       ;; state that is active but not complete (guard of tpmx-sha1-thread->stop)
       ;; GWK: Is it possible to enable tpmx-sha1-thread->update to prove the
       ;; guards of tpmx-sha1-thread->stop?
       (sha1-thread (tpmx-sha1-thread->stop tpm-data.sha1-thread))
       
       ((tpmx-sha1-thread sha1-thread) sha1-thread)
      )
      (mv tpm-data
          :tpm-success
          (make-tpm-digest :value sha1-thread.value))))

;; 16.1 TPM_Extend
(cutil::define tpm-extend
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (pcr-num tpm-pcrindex-p "The PCR to be updated.")
   (in-digest tpm-digest-p "The 160 bit value representing the event to be recorded."))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (out-digest tpm-pcrvalue-p "The PCR value after execution of the command." :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body

  ;; Description
  ;; Add a measurement value to a PCR
  ;;
  ;; Actions
  ;; 1. Validate that pcrNum represents a legal PCR number. On error, return TPM_BADINDEX.
  ;; 2. Map L1 to TPM_STANY_FLAGS -> localityModifier
  ;; 3. Map P1 to TPM_PERMANENT_DATA -> pcrAttrib [pcrNum]. pcrExtendLocal
  ;; 4. If, for the value of L1, the corresponding bit is not set in the bit map P1, return TPM_BAD_LOCALITY
  ;; 5. Create c1 by concatenating (TPM_STCLEAR_DATA -> PCR[pcrNum] || inDigest). This takes the current PCR value and concatenates the inDigest parameter.
  ;; 6. Create h1 by performing a SHA-1 digest of c1.
  ;; 7. Store h1 to TPM_STCLEAR_DATA -> PCR[pcrNum]
  ;; 8. If TPM_PERMANENT_FLAGS -> disable is TRUE or TPM_STCLEAR_FLAGS -> deactivated is TRUE
  ;; 8.a. Set outDigest to 20 bytes of 0x00
  ;; 9. Else
  ;; 9.a. Set outDigest to h1

  (b* (
       ;; check pcr-num
       ((when (or (< pcr-num 0)
                  (>= pcr-num *tpmx-num-pcrs*)))
        (mv tpm-data :tpm-badindex (make-tpm-pcrvalue :value 0)))

       ;; enable dot notation for tpm data and fields
       ((tpmx-internal-data tpm-data) tpm-data)
       ((tpm-permanent-data permanent-data) tpm-data.permanent-data)
       ((tpm-stclear-data stclear-data) tpm-data.stclear-data)
       ((tpm-permanent-flags permanent-flags) tpm-data.permanent-flags)
       ((tpm-stclear-flags stclear-flags) tpm-data.stclear-flags)
       ((tpm-stany-flags stany-flags) tpm-data.stany-flags)
       ((tpmx-sha1-thread sha1-thread) tpm-data.sha1-thread)

       ;; bind the pcr attribute for pcr-num, enable dot notation, and get localities
       (nth-pcr-attrib (nth pcr-num permanent-data.pcr-attrib))
       ((tpm-pcr-attributes nth-pcr-attrib) nth-pcr-attrib)
       ((tpm-locality-selection pcr-extend-local) nth-pcr-attrib.pcr-extend-local)

       ;; if the stany flags locality is a locality accepted by the PCR, all is good
       (good-locality (case stany-flags.locality-modifier
                            (0 pcr-extend-local.tpm-loc-zero)
                            (1 pcr-extend-local.tpm-loc-one)
                            (2 pcr-extend-local.tpm-loc-two)
                            (3 pcr-extend-local.tpm-loc-three)
                            (4 pcr-extend-local.tpm-loc-four)
                            (t nil)))

       ;; otherwise, return with an error
       ((when (not good-locality)) (mv tpm-data :tpm-bad-locality (make-tpm-pcrvalue :value 0)))

       ;; get the pcrvalue and enable dot notation (for its integer value)
       (pcrvalue (nth pcr-num stclear-data.pcr))
       ((tpm-pcrvalue pcrvalue) pcrvalue)
       ((tpm-digest in-digest) in-digest)

       ;; ensure tpm's sha1 thread is not currently active
       (sha1-thread (if (tpmx-sha1-thread->active tpm-data.sha1-thread) ;; if active
                        (make-tpmx-sha1-thread) ;; reset thread
                        tpm-data.sha1-thread))  ;; use current thread
       ;; start a sha-1 thread, extend the pcrvalue with the digest and stop the thread
       (sha1-thread (tpmx-sha1-thread->start-extend-stop sha1-thread
                                                         pcrvalue.value
                                                         in-digest.value))

       ;; update the tpm-data with the completed sha-1 thread, put the thread's value in h1
       (tpm-data (change-tpmx-internal-data tpm-data :sha1-thread sha1-thread))
       (h1 (make-tpm-pcrvalue :value sha1-thread.value))

       (new-pcr (update-nth pcr-num h1 stclear-data.pcr))

       ;; update the tpm's pcr value
       (stclear-data (change-tpm-stclear-data tpm-data.stclear-data
                                              :pcr new-pcr))
       (tpm-data (change-tpmx-internal-data tpm-data
                                            :stclear-data stclear-data))

       ;; set the out digest (note: may be different from updated PCR value)
       ;; NOTE: In BerliOS implementation, PCR and outDigest are always the same
       (out-digest (if (or permanent-flags.disable
                           stclear-flags.deactivated)
                       (make-tpm-pcrvalue :value 0)
                       h1))
      )
      (mv tpm-data :tpm-success out-digest)))

;; 13.4 TPM_SHA1CompleteExtend
(cutil::define tpm-sha1-complete-extend
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (pcr-num tpm-pcrindex-p "Index of the PCR to be modified")
   (hash-data byte-list-p "Final bytes to be hashed"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (hash-value tpm-digest-p "The output of the SHA-1 hash." :hyp :fguard)
               (out-digest tpm-pcrvalue-p "The PCR value after execution of the command." :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body

  ;; Description
  ;; This command SHALL incorporate a partial or complete block of data into the digest of an existing SHA-1 thread, EXTEND the resultant digest into a PCR, and terminate the SHA-1 session.
  ;; hashDataSize MAY have values in the range of 0 through 64, inclusive.
  ;; The SHA-1 session MUST terminate even if the command returns an error, e.g. TPM_BAD_LOCALITY.
  ;;
  ;; Actions
  ;; 5. Validate that pcrNum represents a legal PCR number. On error, return TPM_BADINDEX.
  ;; 6. Map V1 to TPM_STANY_DATA
  ;; 7. Map L1 to V1 -> localityModifier
  ;; 8. If the current locality, held in L1, is not selected in TPM_PERMANENT_DATA -> pcrAttrib [pcrNum]. pcrExtendLocal, return TPM_BAD_LOCALITY
  ;; 9. Create H1 the TPM_DIGEST of the SHA-1 session ensuring that hashData, if any, is added to the SHA-1 session
  ;; 10. Perform the actions of TPM_Extend using H1 as the data and pcrNum as the PCR to extend

  (b* (
       ;; Call TPM_Sha1Complete
       ((mv tpm-data return-code hash-value)
        (tpm-sha1-complete tpm-data hash-data))
       ;; return on error
       ((when (not (equal return-code :tpm-success)))
        (mv tpm-data return-code hash-value (make-tpm-pcrvalue :value 0)))
       ;; Call TPM_Extend, return on error
       ((mv tpm-data return-code out-digest)
        (tpm-extend tpm-data pcr-num hash-value))
      )
      ;; return result, regardless of error or success
      (mv tpm-data return-code hash-value out-digest)))
