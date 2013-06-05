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
(include-book "cutil/defprojection" :dir :system)
(include-book "defposition-if")
(include-book "defprimitive")
(include-book "tpm-structures")
(include-book "tpmx-constants")
(include-book "misc/assert" :dir :system)


;; ===============================================================
;; TPMX_AUTH_INFO
;; ===============================================================

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

;; ===============================================================
;; TPMX_SHA1_THREAD
;; ===============================================================

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

;; ===============================================================
;; TPMX_INTERNAL_DATA
;; ===============================================================

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
   (last-random-value natp "Last randomly generated value.  Acts as seed for
                            next randomly generated value."
                      :default 0)
  )
  :parents(tpm-structures))

;; ===============================================================
;; TPMX HANDLE MANAGEMENT FUNCTIONS
;; ===============================================================

(cutil::define handle->get-key-handle-from-index
  ((index (and (integerp index)
               (< index 100))))
  :returns (handle integerp :hyp :fguard)
  (+ index 100))

(cutil::define handle->get-auth-handle-from-index
  ((index (and (natp index)
               (< index 100))))
  :returns (handle tpm-authhandle-p :hyp :fguard
                   :hints (("Goal" :in-theory (enable tpm-authhandle-p uint32-p))))
  (+ index 200))

(cutil::define handle->get-trans-handle-from-index
  ((index (and (integerp index)
               (< index 100))))
  :returns (handle integerp :hyp :fguard)
  (+ index 300))

(cutil::define handle->get-counter-handle-from-index
  ((index (and (integerp index)
               (< index 100))))
  :returns (handle integerp :hyp :fguard)
  (+ index 400))

(cutil::define handle->get-daa-handle-from-index
  ((index (and (integerp index)
               (< index 100))))
  :returns (handle integerp :hyp :fguard)
  (+ index 500))

(cutil::define handle->get-index-from-handle
  ((handle integerp))
  :returns (index integerp :hyp :fguard)
  (mod handle 100))

(cutil::define handle->get-resource-type-from-handle
  ((handle integerp))
  :returns (rt tpm-resource-type-p :hyp :fguard)
  (let ((q (floor handle 100)))
    (case q
      (1 :tpm-rt-key)
      (2 :tpm-rt-auth)
      (3 :tpm-rt-trans)
      (4 :tpm-rt-counter)
      (5 :tpm-rt-daa-tpm)
      (t :tpmx-default-enum-value))))

(defthm hack
  (implies (tpmx-session-data-list-p x)
           (tpm-session-data-list-p x))
  :hints (("Goal" :in-theory (enable tpmx-session-data-list-p)))
  :rule-classes (#|:forward-chaining|# :rewrite))

(defun invalid-session (x)
  (declare (xargs :guard (tpm-session-data-p x)))
  (equal (tpm-session-data->session-type x)
         :tpmx-st-invalid))

(defposition-if 
  position-invalid-session
  invalid-session
  :guard (tpm-session-data-list-p lst))
  
(defthm type-of-position-invalid-session-ac
  (implies (natp acc)
           (or (not (position-invalid-session-ac lst acc))
               (natp (position-invalid-session-ac lst acc))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable position-invalid-session-ac))))

(defthm type-of-position-invalid-session
  (or (not (position-invalid-session lst))
      (natp (position-invalid-session lst)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable position-invalid-session))))

(defthm nth-of-position-invalid-session-ac
  (implies (and (position-invalid-session-ac lst acc)
                (natp acc))
           (invalid-session (nth (- (position-invalid-session-ac lst acc)
                                    acc)
                                 lst)))
  :hints (("goal" :in-theory (enable position-invalid-session-ac)
           :do-not '(generalize fertilize)
           :induct (position-invalid-session-ac lst acc))))

(defthm limit-of-position-invalid-session-ac
  (implies (and (natp ac)
                (equal (len lst) *tpmx-max-sessions*))
           (< (position-invalid-session-ac lst ac)
              (+ *tpmx-max-sessions* ac)))
    :hints (("goal" :in-theory (enable position-invalid-session-ac)
             :do-not '(generalize fertilize)
             ;;:induct (position-invalid-session-ac lst ac)
           )))

(defthm limit-of-position-invalid-session
  (implies (and (position-invalid-session lst)
                (equal (len lst) *tpmx-max-sessions*))
           (< (position-invalid-session lst) *tpmx-max-sessions*))
  :hints (("Goal" 
           :use ((:instance limit-of-position-invalid-session-ac
                            (ac 0)))
           :in-theory (enable position-invalid-session))))

(cutil::define handle->get-free-session-index
  ((tpm-data tpmx-internal-data-p))
  :returns (index (implies index (natp index))
                  :hyp :fguard)
                  ;:hints (("Goal" :in-theory (enable position-invalid-session))))
  :long "Searches tpm-data.stany-data.sessions array for a session
         whose session-type is :tpm-invalid-session and returns its
         index. If no such sessions are found, <tt>nil</tt> is 
         returned."
  (b* (
       ;; field access for defaggregate params
       ((tpmx-internal-data tpm-data) tpm-data)
       (stany-data tpm-data.stany-data)
       ((tpm-stany-data stany-data) stany-data)
       )
      (position-invalid-session stany-data.sessions))
  ///
  (defthm handle->get-free-session-index-post-condition-1
    (implies 
     (tpmx-internal-data-p tpm-data-in)
     (b* (
          (index (handle->get-free-session-index tpm-data-in))
          ((tpmx-internal-data tpm-data-in) tpm-data-in)
          ((tpm-stany-data stany-data) tpm-data-in.stany-data)
          )
         (implies index
                  (b* (
                       (nth-session (nth index stany-data.sessions))
                       ((tpm-session-data nth-session) nth-session)
                       )
                      (invalid-session nth-session)))))
    :hints (("Goal" :use 
             ((:instance nth-of-position-invalid-session
                         (lst (tpm-stany-data->sessions
                               (tpmx-internal-data->stany-data tpm-data-in)))))
             :in-theory (disable nth-of-position-invalid-session))))

  (local
   (defthm handle->get-free-session-index-post-condition-2-lemma
     (implies
      (and
       (tpmx-internal-data-p tpm-data-in)
       (tpmx-session-data-list-p (tpm-stany-data->sessions
                                  (tpmx-internal-data->stany-data tpm-data-in)))
    
       (position-invalid-session
        (tpm-stany-data->sessions (tpmx-internal-data->stany-data tpm-data-in))))
      (< (position-invalid-session
          (tpm-stany-data->sessions (tpmx-internal-data->stany-data tpm-data-in)))
         3))
     :hints (("Goal" :in-theory (enable tpmx-session-data-list-p)))))

  (defthm handle->get-free-session-index-post-condition-2
    (implies 
     (tpmx-internal-data-p tpm-data-in)
     (let ((index (handle->get-free-session-index tpm-data-in)))
       (implies index
                (< index *tpmx-max-sessions*))))
    :rule-classes (:rewrite :linear)))

;; ===============================================================
;; TPMX MATH FUNCTIONS
;; ===============================================================

(cutil::define math->generate-random-number
  ((tpm-data tpmx-internal-data-p))
  :returns (mv (number natp "Pseudo-random number that isn't really random at
                             all.  It is important for this function to 
                             remain disabled"                
                       :hyp :fguard)
               (tpm-data tpmx-internal-data-p :hyp :fguard))
  (b* (((tpmx-internal-data tpm-data) tpm-data)
       (next-random-value (1+ tpm-data.last-random-value))
       (tpm-data (change-tpmx-internal-data tpm-data
                                            :last-random-value
                                            next-random-value)))
      (mv next-random-value tpm-data)))

(in-theory (disable math->generate-random-number ; rewrite rule
                    (math->generate-random-number))) ; executable counterpart
