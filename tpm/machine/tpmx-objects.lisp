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

(include-book "cutil/deflist" :dir :system)
(include-book "cutil/defaggregate" :dir :system)
(include-book "cutil/defenum" :dir :system)
(include-book "cutil/define" :dir :system)
(include-book "defprimitive")
(include-book "tpm-structures")
(include-book "tpmx-constants")
(include-book "misc/assert" :dir :system)

;; TPMX_AUTH_INFO
(cutil::defaggregate tpmx-auth-info
  ((auth-handle tpm-authhandle-p ""
     :default (make-tpm-authhandle))
   (nonce-even tpm-nonce-p ""
     :default (make-tpm-nonce))
   (nonce-odd tpm-nonce-p ""
     :default (make-tpm-nonce))
   (continue-auth-session booleanp ""
     :default nil)
   (auth-data tpm-authdata-p ""
     :default (make-tpm-authdata))
  )
  :parents(tpm-structures))

;; TPMX_SHA1_THREAD
(cutil::defaggregate tpmx-sha1-thread
  ((active booleanp "When the SHA-1 thread is active, TPM commands are limited to SHA-1 commands. (see TPM_Sha1Start)"
     :default nil)
   (complete booleanp "Indicates that the SHA-1 hash has completed"
     :default nil)
   (value integerp "The current value of the SHA-1 hash (in progress if not completed)"
     :default 0 :rule-classes (:type-prescription :rewrite))
  )
  :parents(tpmx-objects))

;; TPMX_SHA1_THREAD START
(cutil::define tpmx-sha1-thread->start
  ((sha1-thread tpmx-sha1-thread-p "SHA-1 thread"))
  ;; sha1-thread-input should not be active
  ;; If we interpret the spec (see TPM_Sha1Start) to mean that the current
  ;; thread is invalidated and this new thread will take its place then we
  ;; may want to change this here OR in the TPM commands that call this.
  :guard
  (not (tpmx-sha1-thread->active sha1-thread))
  :returns
  (sha1-thread (and (tpmx-sha1-thread-p sha1-thread)
                    (tpmx-sha1-thread->active sha1-thread)
                    (not (tpmx-sha1-thread->complete sha1-thread)))

               "SHA-1 thread" :hyp :fguard)
  :parents (tpmx-sha1-thread)
; body
  (declare (ignore sha1-thread))
  (make-tpmx-sha1-thread :active t
                         :complete nil
                         :value 17)

  ;; GWK: Instead of writing our 'postconditions' in the :retruns section,
  ;; we could have written the following theorem inside the body.
  ;; (Note that the three slashes are mandatory)
  ;;
  ;; ///
  ;; (defthm tpmx-sha1-thread->start-post-conditions
  ;;   (implies (tpmx-sha1-thread-p sha1-thread)
  ;;            (b* ((sha1-thread (tpmx-sha1-thread->start sha1-thread))
  ;;                 ((tpmx-sha1-thread sha1-thread) sha1-thread))
  ;;                (and sha1-thread.active
  ;;                     (not sha1-thread.complete)))))

  ;; GWK: Here is another way to write the theorem using a 'let'
  ;;
  ;; ///
  ;; (defthm tpmx-sha1-thread->start-post-conditions
  ;;   (implies (tpmx-sha1-thread-p sha1-thread)
  ;;            (let ((sha1-thread (tpmx-sha1-thread->start sha1-thread)))
  ;;              (and (tpmx-sha1-thread->active sha1-thread)
  ;;                   (not (tpmx-sha1-thread->complete sha1-thread))))))

  )

;; GWK: If we wrote the theorem outside of the body, we would need to 'enable'
;; the implimentation in a :hint
;;
;; (defthm tpmx-sha1-thread->start-post-conditions
;;   (implies (tpmx-sha1-thread-p sha1-thread)
;;            (b* ((sha1-thread (tpmx-sha1-thread->start sha1-thread))
;;                 ((tpmx-sha1-thread sha1-thread) sha1-thread))
;;                (and sha1-thread.active
;;                     (not sha1-thread.complete))))
;;   :hints (("Goal" :in-theory (enable tpmx-sha1-thread->start))))

;; TPMX_SHA1_THREAD STOP
(cutil::define tpmx-sha1-thread->stop
  ((sha1-thread tpmx-sha1-thread-p "SHA-1 thread"))
  ;; sha1-thread-input should be active and not complete
  :guard
  (and (tpmx-sha1-thread->active sha1-thread)
       (not (tpmx-sha1-thread->complete sha1-thread)))
  :returns
  (sha1-thread (and (tpmx-sha1-thread-p sha1-thread)
                    (not (tpmx-sha1-thread->active sha1-thread))
                    (tpmx-sha1-thread->complete sha1-thread))
                    "SHA-1 thread" :hyp :fguard)
  :parents (tpmx-sha1-thread)
; body
  (change-tpmx-sha1-thread sha1-thread
                           :active nil
                           :complete t))

;; TPMX_SHA1_THREAD INTEGER_UPDATE
(cutil::define tpmx-sha1-thread->integer-update
  ((sha1-thread tpmx-sha1-thread-p "SHA-1 thread")
   (data integerp "integer data to add to SHA-1 calculation"))
  :guard
  (and (tpmx-sha1-thread->active sha1-thread)
       (not (tpmx-sha1-thread->complete sha1-thread)))
  :parents (tpmx-sha1-thread)

  ;; If error output is required, use this instead
  ;; :guard (and (or (tpmx-sha1-thread->active sha1-thread)
  ;;                 (er hard? 'tpmx-sha1-thread->integer-update
  ;;                     "sha1-thread not active; should be active"))
  ;;             (or (not (tpmx-sha1-thread->complete sha1-thread))
  ;;                 (er hard? 'tpmx-sha1-thread
  ;;                     "sha1-thread complete; should be incomplete")))
  ;; :guard-debug t

  :returns
  (sha1-thread (and (tpmx-sha1-thread-p sha1-thread)
                    (tpmx-sha1-thread->active sha1-thread)
                    (not (tpmx-sha1-thread->complete sha1-thread)))
                    "SHA-1 thread" :hyp :fguard)
; body
  (b* (
       ((tpmx-sha1-thread sha1-thread) sha1-thread)
      )
      (change-tpmx-sha1-thread sha1-thread
                               :value
                               (+ (* 31 sha1-thread.value) data))))

;; TPMX_SHA1_THREAD HASH_LIST (private: used by UPDATE)
(cutil::define tpmx-sha1-thread->hash-list
  ((data byte-list-p)
   (value-so-far integerp))
  :returns
  (ans integerp :hyp :fguard)
  :parents (tpmx-sha1-thread)
; body
  ;; Recursively add the bytes to the hash value according to our simple
  ;; Java-like hash algorithm: 17 + rem, where rem = 31 * rem + c, for each new
  ;; element c. If the byte-list has no data, nothing is added to the value.
  (cond ((endp data)
         value-so-far)
        (t (tpmx-sha1-thread->hash-list
            (cdr data)
            (+ (* 31 value-so-far) (car data))))))

;; TPMX_SHA1_THREAD UPDATE
(cutil::define tpmx-sha1-thread->update
  ((sha1-thread tpmx-sha1-thread-p "SHA-1 thread")
   (data byte-list-p "byte-list data to add to SHA-1 calculation"))
  ;; sha1-thread-input should be active and not complete
  :guard
  (and (tpmx-sha1-thread->active sha1-thread)
       (not (tpmx-sha1-thread->complete sha1-thread)))
  :returns
  (sha1-thread (and (tpmx-sha1-thread-p sha1-thread)
                    (tpmx-sha1-thread->active sha1-thread)
                    (not (tpmx-sha1-thread->complete sha1-thread)))
                    "SHA-1 thread" :hyp :fguard)
  :parents (tpmx-sha1-thread)
; body
  ;; Technically, if the list is empty, a SHA-1 hash is taken of the 'empty
  ;; buffer' (see TPM_Sha1Complete)
  (b* (
       ((tpmx-sha1-thread sha1-thread) sha1-thread)
       ;; If empty (nil) list is passed, no changes will be made
       ;; (data (if (endp data) (cons 0 (make-byte-list)) data))
      )
      (change-tpmx-sha1-thread sha1-thread
                               :value
                               (tpmx-sha1-thread->hash-list data sha1-thread.value))))

;; TPMX_SHA1_THREAD START_STOP (test method)
(cutil::define tpmx-sha1-thread->start-stop
  ((sha1-thread tpmx-sha1-thread-p "SHA-1 thread"))
  ;; sha1-thread should not be active
  :guard
  (not (tpmx-sha1-thread->active sha1-thread))
  :returns
  (sha1-thread (and (tpmx-sha1-thread-p sha1-thread)
                    (not (tpmx-sha1-thread->active sha1-thread))
                    (tpmx-sha1-thread->complete sha1-thread))
                    "SHA-1 thread" :hyp :fguard
                    ;; GWK: If you don't have postconditions, you can try enabling
                    ;; implementations as follows, but you do so at your own peril.
                    ;; :hints (("Goal" :in-theory (enable tpmx-sha1-thread->start)))
                    )
  :parents (tpmx-sha1-thread)
; body
  (b* (
       ;; modify sha1-thread
       (sha1-thread (tpmx-sha1-thread->start sha1-thread))
       (sha1-thread (tpmx-sha1-thread->stop sha1-thread))
      )
      sha1-thread)
)

;; TPMX_SHA1_THREAD START_UPDATE_STOP (convenience method)
(cutil::define tpmx-sha1-thread->start-update-stop
  ((sha1-thread tpmx-sha1-thread-p "SHA-1 thread")
   (data integerp "integer data to hash"))
  ;; sha1-thread should not be active
  :guard
  (not (tpmx-sha1-thread->active sha1-thread))
  :returns
  (sha1-thread (and (tpmx-sha1-thread-p sha1-thread)
                    (not (tpmx-sha1-thread->active sha1-thread))
                    (tpmx-sha1-thread->complete sha1-thread))
                    "SHA-1 thread" :hyp :fguard)
  :parents (tpmx-sha1-thread)
; body
  (b* (
       ;; modify sha1-thread
       (sha1-thread (tpmx-sha1-thread->start sha1-thread))
       (sha1-thread (tpmx-sha1-thread->integer-update sha1-thread data))
       (sha1-thread (tpmx-sha1-thread->stop sha1-thread))
      )
      sha1-thread)
)

;; TPMX_SHA1_THREAD START_EXTEND_STOP (convenience method)
(cutil::define tpmx-sha1-thread->start-extend-stop
  ((sha1-thread tpmx-sha1-thread-p "SHA-1 thread")
   (data integerp "initial integer data for SHA-1 calculation")
   (ext integerp "additional integer data for SHA-1 calculation"))
  ;; sha1-thread should not be active
  :guard
  (not (tpmx-sha1-thread->active sha1-thread))
  :returns
  (sha1-thread (and (tpmx-sha1-thread-p sha1-thread)
                    (not (tpmx-sha1-thread->active sha1-thread))
                    (tpmx-sha1-thread->complete sha1-thread))
                    "SHA-1 thread" :hyp :fguard)
  :parents (tpmx-sha1-thread)
; body
  (b* (
       (sha1-thread (tpmx-sha1-thread->start sha1-thread))
       (sha1-thread (tpmx-sha1-thread->integer-update sha1-thread data))
       (sha1-thread (tpmx-sha1-thread->integer-update sha1-thread ext))
       (sha1-thread (tpmx-sha1-thread->stop sha1-thread))
      )
      sha1-thread))

;; TPMX_INTERNAL_DATA
(cutil::defaggregate tpmx-internal-data
  ((permanent-flags tpm-permanent-flags-p "These flags maintain state information for the TPM. The values are not affected by any TPM_Startup command."
     :default (make-tpm-permanent-flags))
   (stclear-flags tpm-stclear-flags-p "These flags maintain state that is reset on each TPM_Startup(ST_CLEAR) command. The values are not affected by TPM_Startup(ST_STATE) commands."
     :default (make-tpm-stclear-flags))
   (stany-flags tpm-stany-flags-p "These flags reset on any TPM_Startup command."
     :default (make-tpm-stany-flags))
   (permanent-data tpm-permanent-data-p "This structure contains the data fields that are permanently held in the TPM and not affected by TPM_Startup(any)."
     :default (make-tpm-permanent-data))
   (stclear-data tpm-stclear-data-p "Most of the data in this structure resets on TPM_Startup(ST_CLEAR)."
     :default (make-tpm-stclear-data))
   (stany-data tpm-stany-data-p "Most of the data in this structure resets on TPM_Startup(ST_STATE)."
     :default (make-tpm-stany-data))
   (sha1-thread tpmx-sha1-thread-p "Thread is active when calculating SHA-1 values."
     :default (make-tpmx-sha1-thread))
  )
  :parents(tpm-structures))

