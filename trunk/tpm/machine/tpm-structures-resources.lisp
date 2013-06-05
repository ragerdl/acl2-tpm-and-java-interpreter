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
(include-book "defprimitive")

; ===============================================================
; primitive structures (integers and byte arrays)
; ===============================================================

(defprimitive byte (x)
  (and (integerp x)
       (<= 0 x)
       (<= x 255))
  :default 0
  :parents(tpm-structures))

(defprimitive uint16 (x)
  (and (integerp x)
       (<= 0 x)
       (<= x (- (expt 2 16) 1)))
  :default 0
  :parents(tpm-structures))

(defprimitive uint32 (x)
  (and (integerp x)
       (<= 0 x)
       (<= x (- (expt 2 32) 1)))
  :default 0
  :parents(tpm-structures))

(defprimitive uint64 (x)
  (and (integerp x)
       (<= 0 x)
       (<= x (- (expt 2 64) 1)))
  :default 0
  :parents(tpm-structures))

(cutil::deflist byte-list-p (x)
  (byte-p x)
  :elementp-of-nil nil
  :true-listp t
  :parents(tpm-structures))

(defnd make-byte-list ()
  nil)

(cutil::deflist uint32-list-p (x)
  (uint32-p x)
  :elementp-of-nil nil
  :true-listp t
  :parents(tpm-structures))

(defnd make-uint32-list ()
  nil)

(defprimitive 4-byte-list (x)
  (and (byte-list-p x)
       (equal (len x) 4))
  :default (make-list 4 :initial-element (make-byte))
  :parents(tpm-structures))

(defprimitive 16-byte-list (x)
  (and (byte-list-p x)
       (equal (len x) 16))
  :default (make-list 16 :initial-element (make-byte))
  :parents(tpm-structures))

(defprimitive 20-byte-list (x)
  (and (byte-list-p x)
       (equal (len x) 20))
  :default (make-list 20 :initial-element (make-byte))
  :parents(tpm-structures))

(defprimitive 26-byte-list (x)
  (and (byte-list-p x)
       (equal (len x) 26))
  :default (make-list 26 :initial-element (make-byte))
  :parents(tpm-structures))

(defprimitive 128-byte-list (x)
  (and (byte-list-p x)
       (equal (len x) 128))
  :default (make-list 128 :initial-element (make-byte))
  :parents(tpm-structures))

(defprimitive 256-byte-list (x)
  (and (byte-list-p x)
       (equal (len x) 256))
  :default (make-list 256 :initial-element (make-byte))
  :parents(tpm-structures))

; ===============================================================
; Level 0 Wrappers
; ===============================================================

;; 2.2 TPM_ACTUAL_COUNT
;; The actual number of a counter.
(defprimitive tpm-actual-count (x)
  (uint32-p x)
  :default (make-uint32)
  :parents(tpm-structures))

;; 2.2 TPM_AUTHHANDLE
;; Handle to an authorization session
(defprimitive tpm-authhandle (x)
  (uint32-p x)
  :default (make-uint32)
  :parents(tpm-structures))

;; 2.2 TPM_CAPABILITY_AREA
;; Identifies a TPM capability area.
(defprimitive tpm-capability-area (x)
  (uint32-p x)
  :default (make-uint32)
  :parents(tpm-structures))

;; 2.2 TPM_COUNT_ID
;; The ID value of a monotonic counter
(defprimitive tpm-count-id (x)
  (uint32-p x)
  :default (make-uint32)
  :parents(tpm-structures))

;; 2.2 TPM_DELEGATE_INDEX
;; The index value for the delegate NV table
(defprimitive tpm-delegate-index (x)
  (uint32-p x)
  :default (make-uint32)
  :parents(tpm-structures))

;; 2.2 TPM_DIRINDEX
;; Index to a DIR register
(defprimitive tpm-dirindex (x)
  (uint32-p x)
  :default (make-uint32)
  :parents(tpm-structures))

;; 2.2 TPM_FAMILY_ID
;; The family ID. Families ID's are automatically assigned a sequence number by the TPM. A trusted process can set the FamilyID value in an individual row to zero, which invalidates that row. The family  ...
(defprimitive tpm-family-id (x)
  (uint32-p x)
  :default (make-uint32)
  :parents(tpm-structures))

;; 2.2 TPM_FAMILY_VERIFICATION
;; A value used as a label for the most recent verification of this family. Set to zero when not in use.
(defprimitive tpm-family-verification (x)
  (uint32-p x)
  :default (make-uint32)
  :parents(tpm-structures))

;; 2.2 TPM_MODIFIER_INDICATOR
;; The locality modifier
(defprimitive tpm-modifier-indicator (x)
  (uint32-p x)
  :default (make-uint32)
  :parents(tpm-structures))

;; 2.2 TPM_PCRINDEX
;; Index to a PCR register
(defprimitive tpm-pcrindex (x)
  (uint32-p x)
  :default (make-uint32)
  :parents(tpm-structures))

;; 2.2 TPM_REDIT_COMMAND
;; A command to execute
(defprimitive tpm-redit-command (x)
  (uint32-p x)
  :default (make-uint32)
  :parents(tpm-structures))

;; 2.2 TPM_STRUCTURE_TAG
;; The tag for the structure
(defprimitive tpm-structure-tag (x)
  (uint16-p x)
  :default (make-uint16)
  :parents(tpm-structures))

;; 2.2 TPM_SYM_MODE
;; The mode of a symmetric encryption
(defprimitive tpm-sym-mode (x)
  (uint32-p x)
  :default (make-uint32)
  :parents(tpm-structures))

;; 2.2 TPM_TRANSHANDLE
;; A transport session handle
(defprimitive tpm-transhandle (x)
  (uint32-p x)
  :default (make-uint32)
  :parents(tpm-structures))

;; 2.2 TPM_TRANSPORT_ATTRIBUTES
;; Attributes that define what options are in use for a transport session
(defprimitive tpm-transport-attributes (x)
  (uint32-p x)
  :default (make-uint32)
  :parents(tpm-structures))

;; 4.3 TPM_ENTITY_TYPE
;; Indicates the types of entity that are supported by the TPM.
(defprimitive tpm-entity-type (x)
  (uint16-p x)
  :default (make-uint16)
  :parents(tpm-structures))

;; 4.4 TPM_HANDLE
;; A generic handle could be key, transport etc.
(defprimitive tpm-handle (x)
  (uint32-p x)
  :default (make-uint32)
  :parents(tpm-structures))

;; 5.2 TPM_VERSION_BYTE
;; The version info breakdown
(defprimitive tpm-version-byte (x)
  (byte-p x)
  :default (make-byte)
  :parents(tpm-structures))

;; 5.6 TPM_AUTHDATA()
(defprimitive tpm-authdata (x)
  (20-byte-list-p x)
  :default (make-20-byte-list)
  :parents(tpm-structures))

;; 17.0 TPM_COMMAND_CODE
;; The command ordinal.
(defprimitive tpm-command-code (x)
  (uint32-p x)
  :default (make-uint32)
  :parents(tpm-structures))

;; 21.4 TPM_CAPABILITY_AREA_set()
(defprimitive tpm-capability-area-set (x)
  (uint32-p x)
  :default (make-uint32)
  :parents(tpm-structures))

;; 23.1 TPM_REDIR_COMMAND
;; See section 23.1
(defprimitive tpm-redir-command (x)
  (uint32-p x)
  :default (make-uint32)
  :parents(tpm-structures))

; ===============================================================
; Level 0 Flags
; ===============================================================

;; 4.6 TPM_STARTUP_EFFECTS
;; How the TPM handles var
(cutil::defaggregate tpm-startup-effects
  ((bit8 booleanp :default nil) ;; TPM_RT_DAA_TPM resources are initialized by TPM_Startup(ST_STATE)
   (bit7 booleanp :default nil) ;; TPM_Startup has no effect on auditDigest
   (bit6 booleanp :default nil) ;; auditDigest is set to all zeros on TPM_Startup(ST_CLEAR) but not on other types of TPM_Startup
   (bit5 booleanp :default nil) ;; auditDigest is set to all zeros on TPM_Startup(any)
   (bit4 booleanp :default nil) ;; Deprecated, as the meaning was subject to interpretation. (Was:TPM_RT_KEY resources are initialized by TPM_Startup(ST_ANY))
   (bit3 booleanp :default nil) ;; TPM_RT_AUTH resources are initialized by TPM_Startup(ST_STATE)
   (bit2 booleanp :default nil) ;; TPM_RT_HASH resources are initialized by TPM_Startup(ST_STATE)
   (bit1 booleanp :default nil) ;; TPM_RT_TRANS resources are initialized by TPM_Startup(ST_STATE)
   (bit0 booleanp :default nil) ;; TPM_RT_CONTEXT session (but not key) resources are initialized by TPM_Startup(ST_STATE)
  )
  :parents(tpm-structures))

;; 5.10 TPM_KEY_FLAGS
;; Indicates information regarding a key.
(cutil::defaggregate tpm-key-flags
  ((redirection booleanp :default nil)      ;; This mask value SHALL indicate the use of redirected output.
   (migratable booleanp :default nil)       ;; This mask value SHALL indicate that the key is migratable.
   (isvolatile booleanp :default nil)       ;; This mask value SHALL indicate that the key MUST be unloaded upon execution of the TPM_Startup(ST_Clear). This does not indicate that a nonvolatile key will remain loaded across TPM_Startup(ST_Clear)  ...
   (pcrignoredonread booleanp :default nil) ;; When TRUE the TPM MUST NOT check digestAtRelease or localityAtRelease for commands that read the public portion of the key (e.g., TPM_GetPubKey) and MAY NOT check digestAtRelease or localityAtRelease  ...
   (migrateauthority booleanp :default nil) ;; When set indicates that the key is under control of a migration authority. The TPM MUST only allow the creation of a key with this flag in TPM_CMK_CreateKey
  )
  :parents(tpm-structures))

;; 5.17 TPM_CMK_DELEGATE
;; The restrictions placed on delegation of CMK commands
(cutil::defaggregate tpm-cmk-delegate
  ((tpm-cmk-delegate-signing booleanp :default nil) ;; When set to 1, this bit SHALL indicate that a delegated command may manipulate a CMK of TPM_KEY_USAGE == TPM_KEY_SIGNING
   (tpm-cmk-delegate-storage booleanp :default nil) ;; When set to 1, this bit SHALL indicate that a delegated command may manipulate a CMK of TPM_KEY_USAGE == TPM_KEY_STORAGE
   (tpm-cmk-delegate-bind booleanp :default nil)    ;; When set to 1, this bit SHALL indicate that a delegated command may manipulate a CMK of TPM_KEY_USAGE == TPM_KEY_BIND
   (tpm-cmk-delegate-legacy booleanp :default nil)  ;; When set to 1, this bit SHALL indicate that a delegated command may manipulate a CMK of TPM_KEY_USAGE == TPM_KEY_LEGACY
   (tpm-cmk-delegate-migrate booleanp :default nil) ;; When set to 1, this bit SHALL indicate that a delegated command may manipulate a CMK of TPM_KEY_USAGE == TPM_KEY_MIGRATE
  )
  :parents(tpm-structures))

;; 8.6 TPM_LOCALITY_SELECTION()
(cutil::defaggregate tpm-locality-selection
  ((tpm-loc-four booleanp :default nil)  ;; Locality 4
   (tpm-loc-three booleanp :default nil) ;; Locality 3
   (tpm-loc-two booleanp :default nil)   ;; Locality 2
   (tpm-loc-one booleanp :default nil)   ;; Locality 1
   (tpm-loc-zero booleanp :default nil)  ;; Locality 0. This is the same as the legacy interface.
  )
  :parents(tpm-structures))

;; 10.9 TPM_KEY_CONTROL
;; Allows for controlling of the key when loaded and how to handle TPM_Startup issues
(cutil::defaggregate tpm-key-control
  ((tpm-key-control-owner-evict booleanp :default nil) ;; Owner controls when the key is evicted from the TPM. When set the TPM MUST preserve key the key across all TPM_Init invocations.
  )
  :parents(tpm-structures))

;; 20.3 TPM_FAMILY_FLAGS
;; The family flags
(cutil::defaggregate tpm-family-flags
  ((tpm-delegate-admin-lock booleanp :default nil) ;; TRUE: Some TPM_Delegate_XXX commands are locked and return TPM_DELEGATE_LOCK; FALSE: TPM_Delegate_XXX commands are available; Default is FALSE
   (tpm-famflag-enabled booleanp :default nil)     ;; When TRUE the table is enabled. The default value is FALSE.
  )
  :parents(tpm-structures))

; ===============================================================
; Level 0 Enumerations
; ===============================================================

;; 4.1 TPM_RESOURCE_TYPE
;; The types of resources that a TPM may have using internal resources
(cutil::defenum tpm-resource-type-p
  (:tpmx-default-enum-value
   :tpm-rt-key      ;; The handle is a key handle and is the result of a LoadKey type operation
   :tpm-rt-auth     ;; The handle is an authorization handle. Auth handles come from TPM_OIAP, TPM_OSAP and TPM_DSAP
   :tpm-rt-hash     ;; Reserved for hashes
   :tpm-rt-trans    ;; The handle is for a transport session. Transport handles come from TPM_EstablishTransport
   :tpm-rt-context  ;; Resource wrapped and held outside the TPM using the context save/restore commands
   :tpm-rt-counter  ;; Reserved for counters
   :tpm-rt-delegate ;; The handle is for a delegate row. These are the internal rows held in NV storage by the TPM
   :tpm-rt-daa-tpm  ;; The value is a DAA TPM specific blob
   :tpm-rt-daa-v0   ;; The value is a DAA V0 parameter
   :tpm-rt-daa-v1   ;; The value is a DAA V1 parameter
  )
  :parents(tpm-structures))

(defnd make-tpm-resource-type ()
  :tpmx-default-enum-value)

;; 4.2 TPM_PAYLOAD_TYPE
;; The information as to what the payload is in an encrypted structure
(cutil::defenum tpm-payload-type-p
  (:tpmx-default-enum-value
   :tpm-pt-asym               ;; The entity is an asymmetric key
   :tpm-pt-bind               ;; The entity is bound data
   :tpm-pt-migrate            ;; The entity is a migration blob
   :tpm-pt-maint              ;; The entity is a maintenance blob
   :tpm-pt-seal               ;; The entity is sealed data
   :tpm-pt-migrate-restricted ;; The entity is a restricted-migration asymmetric key
   :tpm-pt-migrate-external   ;; The entity is a external migratable key
   :tpm-pt-cmk-migrate        ;; The entity is a CMK migratable blob
  )
  :parents(tpm-structures))

(defnd make-tpm-payload-type ()
  :tpmx-default-enum-value)

;; 4.4 TPM_KEY_HANDLE
;; The area where a key is held assigned by the TPM.
(cutil::defenum tpm-key-handle-p
  (:tpmx-default-enum-value
   :tpm-kh-srk       ;; The handle points to the SRK
   :tpm-kh-owner     ;; The handle points to the TPM Owner
   :tpm-kh-revoke    ;; The handle points to the RevokeTrust value
   :tpm-kh-transport ;; The handle points to the TPM_EstablishTransport static authorization
   :tpm-kh-operator  ;; The handle points to the Operator auth
   :tpm-kh-admin     ;; The handle points to the delegation administration auth
   :tpm-kh-ek        ;; The handle points to the PUBEK, only usable with TPM_OwnerReadInternalPub
  )
  :parents(tpm-structures))

(defnd make-tpm-key-handle ()
  :tpmx-default-enum-value)

;; 4.5 TPM_STARTUP_TYPE
;; Indicates the start state.
(cutil::defenum tpm-startup-type-p
  (:tpmx-default-enum-value
   :tpm-st-clear       ;; The TPM is starting up from a clean state
   :tpm-st-state       ;; The TPM is starting up from a saved state
   :tpm-st-deactivated ;; The TPM is to startup and set the deactivated flag to TRUE
  )
  :parents(tpm-structures))

(defnd make-tpm-startup-type ()
  :tpmx-default-enum-value)

;; 4.7 TPM_PROTOCOL_ID
;; The protocol in use.
(cutil::defenum tpm-protocol-id-p
  (:tpmx-default-enum-value
   :tpm-pid-oiap      ;; The OIAP protocol.
   :tpm-pid-osap      ;; The OSAP protocol.
   :tpm-pid-adip      ;; The ADIP protocol.
   :tpm-pid-adcp      ;; The ADCP protocol.
   :tpm-pid-owner     ;; The protocol for taking ownership of a TPM.
   :tpm-pid-dsap      ;; The DSAP protocol
   :tpm-pid-transport ;; The transport protocol
  )
  :parents(tpm-structures))

(defnd make-tpm-protocol-id ()
  :tpmx-default-enum-value)

;; 4.8 TPM_ALGORITHM_ID
;; Indicates the type of algorithm.
(cutil::defenum tpm-algorithm-id-p
  (:tpmx-default-enum-value
   :tpm-alg-rsa    ;; The RSA algorithm.
   ;; reserved     ;; (was the DES algorithm)
   ;; reserved     ;; (was the 3DES algorithm in EDE mode)
   :tpm-alg-sha    ;; The SHA1 algorithm
   :tpm-alg-hmac   ;; The RFC 2104 HMAC algorithm
   :tpm-alg-aes128 ;; The AES algorithm, key size 128
   :tpm-alg-mgf1   ;; The XOR algorithm using MGF1 to create a string the size of the encrypted block
   :tpm-alg-aes192 ;; AES, key size 192
   :tpm-alg-aes256 ;; AES, key size 256
   :tpm-alg-xor    ;; XOR using the rolling nonces
  )
  :parents(tpm-structures))

(defnd make-tpm-algorithm-id ()
  :tpmx-default-enum-value)

;; 4.9 TPM_PHYSICAL_PRESENCE
;; Sets the state of the physical presence mechanism.
(cutil::defenum tpm-physical-presence-p
  (:tpmx-default-enum-value
   :tpm-physical-presence-hw-disable    ;; Sets the physicalPresenceHWEnable to FALSE
   :tpm-physical-presence-cmd-disable   ;; Sets the physicalPresenceCMDEnable to FALSE
   :tpm-physical-presence-lifetime-lock ;; Sets the physicalPresenceLifetimeLock to TRUE
   :tpm-physical-presence-hw-enable     ;; Sets the physicalPresenceHWEnable to TRUE
   :tpm-physical-presence-cmd-enable    ;; Sets the physicalPresenceCMDEnable to TRUE
   :tpm-physical-presence-notpresent    ;; Sets PhysicalPresence = FALSE
   :tpm-physical-presence-present       ;; Sets PhysicalPresence = TRUE
   :tpm-physical-presence-lock          ;; Sets PhysicalPresenceLock = TRUE
  )
  :parents(tpm-structures))

(defnd make-tpm-physical-presence ()
  :tpmx-default-enum-value)

;; 4.10 TPM_MIGRATE_SCHEME
;; The definition of the migration scheme
(cutil::defenum tpm-migrate-scheme-p
  (:tpmx-default-enum-value
   :tpm-ms-migrate          ;; A public key that can be used with all TPM migration commands other than 'ReWrap' mode.
   :tpm-ms-rewrap           ;; A public key that can be used for the ReWrap mode of TPM_CreateMigrationBlob.
   :tpm-ms-maint            ;; A public key that can be used for the Maintenance commands
   :tpm-ms-restrict-migrate ;; The key is to be migrated to a Migration Authority.
   :tpm-ms-restrict-approve ;; The key is to be migrated to an entity approved by a Migration Authority using double wrapping
  )
  :parents(tpm-structures))

(defnd make-tpm-migrate-scheme ()
  :tpmx-default-enum-value)

;; 4.11 TPM_EK_TYPE
;; The type of asymmetric encrypted structure in use by the endorsement key
(cutil::defenum tpm-ek-type-p
  (:tpmx-default-enum-value
   :tpm-ek-type-activate ;; The blob MUST be TPM_EK_BLOB_ACTIVATE
   :tpm-ek-type-auth     ;; The blob MUST be TPM_EK_BLOB_AUTH
  )
  :parents(tpm-structures))

(defnd make-tpm-ek-type ()
  :tpmx-default-enum-value)

;; 4.12 TPM_PLATFORM_SPECIFIC
;; The platform specific spec to which the information relates to
(cutil::defenum tpm-platform-specific-p
  (:tpmx-default-enum-value
   :tpm-ps-pc-11     ;; PC Specific version 1.1
   :tpm-ps-pc-12     ;; PC Specific version 1.2
   :tpm-ps-pda-12    ;; PDA Specific version 1.2
   :tpm-ps-server-12 ;; Server Specific version 1.2
   :tpm-ps-mobile-12 ;; Mobil Specific version 1.2
  )
  :parents(tpm-structures))

(defnd make-tpm-platform-specific ()
  :tpmx-default-enum-value)

;; 5.8 TPM_ENC_SCHEME
;; The definition of the encryption scheme.
(cutil::defenum tpm-enc-scheme-p
  (:tpmx-default-enum-value
   :tpm-es-none                ;; See section 5.8
   :tpm-es-rsaespkcsv15        ;; See section 5.8
   :tpm-es-rsaesoaep-sha1-mgf1 ;; See section 5.8
   :tpm-es-sym-ctr             ;; See section 5.8
   :tpm-es-sym-ofb             ;; See section 5.8
  )
  :parents(tpm-structures))

(defnd make-tpm-enc-scheme ()
  :tpmx-default-enum-value)

;; 5.8 TPM_KEY_USAGE
;; Indicates the permitted usage of the key.
(cutil::defenum tpm-key-usage-p
  (:tpmx-default-enum-value
   :tpm-key-signing    ;; This SHALL indicate a signing key. The [private] key SHALL be used for signing operations, only. This means that it MUST be a leaf of the Protected Storage key hierarchy. ...
   :tpm-key-storage    ;; This SHALL indicate a storage key. The key SHALL be used to wrap and unwrap other keys in the Protected Storage hierarchy
   :tpm-key-identity   ;; This SHALL indicate an identity key. The key SHALL be used for operations that require a TPM identity, only.
   :tpm-key-authchange ;; This SHALL indicate an ephemeral key that is in use during the ChangeAuthAsym process, only.
   :tpm-key-bind       ;; This SHALL indicate a key that can be used for TPM_Bind and TPM_UnBind operations only.
   :tpm-key-legacy     ;; This SHALL indicate a key that can perform signing and binding operations. The key MAY be used for both signing and binding operations. The TPM_KEY_LEGACY key type is to allow for use by applications  ...
   :tpm-key-migrate    ;; This SHALL indicate a key in use for TPM_MigrateKey
  )
  :parents(tpm-structures))

(defnd make-tpm-key-usage ()
  :tpmx-default-enum-value)

;; 5.8 TPM_SIG_SCHEME
;; The definition of the signature scheme.
(cutil::defenum tpm-sig-scheme-p
  (:tpmx-default-enum-value
   :tpm-ss-none                ;; See section 5.8
   :tpm-ss-rsassapkcs1v15-sha1 ;; See section 5.8
   :tpm-ss-rsassapkcs1v15-der  ;; See section 5.8
   :tpm-ss-rsassapkcs1v15-info ;; See section 5.8
  )
  :parents(tpm-structures))

(defnd make-tpm-sig-scheme ()
  :tpmx-default-enum-value)

;; 5.9 TPM_AUTH_DATA_USAGE
;; Indicates the conditions where it is required that authorization be presented.
(cutil::defenum tpm-auth-data-usage-p
  (:tpmx-default-enum-value
   :tpm-auth-never          ;; This SHALL indicate that usage of the key without authorization is permitted.
   :tpm-auth-always         ;; This SHALL indicate that on each usage of the key the authorization MUST be performed.
   :tpm-no-read-pubkey-auth ;; This SHALL indicate that on commands that require the TPM to use the the key, the authorization MUST be performed. For commands that cause the TPM to read the public portion of the key, but not to use ...
  )
  :parents(tpm-structures))

(defnd make-tpm-auth-data-usage ()
  :tpmx-default-enum-value)

;; 6.0 TPM_TAG
;; The request or response authorization type.
(cutil::defenum tpm-tag-p
  (:tpmx-default-enum-value
   :tpm-tag-rqu-command       ;; A command with no authentication.
   :tpm-tag-rqu-auth1-command ;; An authenticated command with one authentication handle
   :tpm-tag-rqu-auth2-command ;; An authenticated command with two authentication handles
   :tpm-tag-rsp-command       ;; A response from a command with no authentication
   :tpm-tag-rsp-auth1-command ;; An authenticated response with one authentication handle
   :tpm-tag-rsp-auth2-command ;; An authenticated response with two authentication handles
  )
  :parents(tpm-structures))

(defnd make-tpm-tag ()
  :tpmx-default-enum-value)

;; 16.0 TPM_RESULT
;; The return code from a function
(cutil::defenum tpm-result-p
  (:tpmx-default-enum-value
   :tpm-success                ;; Successful completion of the operation.
   :tpm-authfail               ;; Authentication failed.
   :tpm-badindex               ;; The index to a PCR, DIR or other register is incorrect.
   :tpm-bad-parameter          ;; One or more parameter is bad.
   :tpm-auditfailure           ;; An operation completed successfully but the auditing of that operation failed.
   :tpm-clear-disabled         ;; The clear disable flag is set and all clear operations now require physical access.
   :tpm-deactivated            ;; The TPM is deactivated.
   :tpm-disabled               ;; The TPM is disabled.
   :tpm-disabled-cmd           ;; The target command has been disabled.
   :tpm-fail                   ;; The operation failed.
   :tpm-bad-ordinal            ;; The ordinal was unknown or inconsistent.
   :tpm-install-disabled       ;; The ability to install an owner is disabled.
   :tpm-invalid-keyhandle      ;; The key handle can not be interpreted.
   :tpm-keynotfound            ;; The key handle points to an invalid key.
   :tpm-inappropriate-enc      ;; Unacceptable encryption scheme.
   :tpm-migratefail            ;; Migration authorization failed.
   :tpm-invalid-pcr-info       ;; PCR information could not be interpreted.
   :tpm-nospace                ;; No room to load key.
   :tpm-nosrk                  ;; There is no SRK set.
   :tpm-notsealed-blob         ;; An encrypted blob is invalid or was not created by this TPM.
   :tpm-owner-set              ;; There is already an Owner.
   :tpm-resources              ;; The TPM has insufficient internal resources to perform the requested action.
   :tpm-shortrandom            ;; A random string was too short.
   :tpm-size                   ;; The TPM does not have the space to perform the operation.
   :tpm-wrongpcrval            ;; The named PCR value does not match the current PCR value.
   :tpm-bad-param-size         ;; The paramSize argument to the command has the incorrect value.
   :tpm-sha-thread             ;; There is no existing SHA-1 thread.
   :tpm-sha-error              ;; The calculation is unable to proceed because the existing SHA-1 thread has already encountered an error.
   :tpm-failedselftest         ;; Self-test has failed and the TPM has shutdown.
   :tpm-auth2fail              ;; The authorization for the second key in a 2 key function failed authorization.
   :tpm-badtag                 ;; The tag value sent to for a command is invalid.
   :tpm-ioerror                ;; An IO error occurred transmitting information to the TPM.
   :tpm-encrypt-error          ;; The encryption process had a problem.
   :tpm-decrypt-error          ;; The decryption process did not complete.
   :tpm-invalid-authhandle     ;; An invalid handle was used.
   :tpm-no-endorsement         ;; The TPM does not a EK installed.
   :tpm-invalid-keyusage       ;; The usage of a key is not allowed.
   :tpm-wrong-entitytype       ;; The submitted entity type is not allowed.
   :tpm-invalid-postinit       ;; The command was received in the wrong sequence relative to TPM_Init and a subsequent TPM_Startup.
   :tpm-inappropriate-sig      ;; Signed data cannot include additional DER information.
   :tpm-bad-key-property       ;; The key properties in TPM_KEY_PARMs are not supported by this TPM.
   :tpm-bad-migration          ;; The migration properties of this key are incorrect.
   :tpm-bad-scheme             ;; The signature or encryption scheme for this key is incorrect or not permitted in this situation.
   :tpm-bad-datasize           ;; The size of the data or blob parameter is bad or inconsistent with the referenced key.
   :tpm-bad-mode               ;; A mode parameter is bad, such as capArea or subCapArea for TPM_GetCapability, physicalPresence parameter for TPM_PhysicalPresence, or migrationType for TPM_CreateMigrationBlob.
   :tpm-bad-presence           ;; Either the physicalPresence or physicalPresenceLock bits have the wrong value.
   :tpm-bad-version            ;; The TPM cannot perform this version of the capability.
   :tpm-no-wrap-transport      ;; The TPM does not allow for wrapped transport sessions.
   :tpm-auditfail-unsuccessful ;; TPM audit construction failed and the underlying command was returning a failure code also.
   :tpm-auditfail-successful   ;; TPM audit construction failed and the underlying command was returning success.
   :tpm-notresetable           ;; Attempt to reset a PCR register that does not have the resettable attribute.
   :tpm-notlocal               ;; Attempt to reset a PCR register that requires locality and locality modifier not part of command transport.
   :tpm-bad-type               ;; Make identity blob not properly typed.
   :tpm-invalid-resource       ;; When saving context identified resource type does not match actual resource.
   :tpm-notfips                ;; The TPM is attempting to execute a command only available when in FIPS mode.
   :tpm-invalid-family         ;; The command is attempting to use an invalid family ID.
   :tpm-no-nv-permission       ;; The permission to manipulate the NV storage is not available.
   :tpm-requires-sign          ;; The operation requires a signed command.
   :tpm-key-notsupported       ;; Wrong operation to load an NV key.
   :tpm-auth-conflict          ;; NV_LoadKey blob requires both owner and blob authorization.
   :tpm-area-locked            ;; The NV area is locked and not writable.
   :tpm-bad-locality           ;; The locality is incorrect for the attempted operation.
   :tpm-read-only              ;; The NV area is read only and can't be written to.
   :tpm-per-nowrite            ;; There is no protection on the write to the NV area.
   :tpm-familycount            ;; The family count value does not match.
   :tpm-write-locked           ;; The NV area has already been written to.
   :tpm-bad-attributes         ;; The NV area attributes conflict.
   :tpm-invalid-structure      ;; The structure tag and version are invalid or inconsistent.
   :tpm-key-owner-control      ;; The key is under control of the TPM Owner and can only be evicted by the TPM Owner.
   :tpm-bad-counter            ;; The counter handle is incorrect.
   :tpm-not-fullwrite          ;; The write is not a complete write of the area.
   :tpm-context-gap            ;; The gap between saved context counts is too large.
   :tpm-maxnvwrites            ;; The maximum number of NV writes without an owner has been exceeded.
   :tpm-nooperator             ;; No operator AuthData value is set.
   :tpm-resourcemissing        ;; The resource pointed to by context is not loaded.
   :tpm-delegate-lock          ;; The delegate administration is locked.
   :tpm-delegate-family        ;; Attempt to manage a family other then the delegated family.
   :tpm-delegate-admin         ;; Delegation table management not enabled.
   :tpm-transport-notexclusive ;; There was a command executed outside of an exclusive transport session.
   :tpm-owner-control          ;; Attempt to context save a owner evict controlled key.
   :tpm-daa-resources          ;; The DAA command has no resources available to execute the command.
   :tpm-daa-input-data0        ;; The consistency check on DAA parameter inputData0 has failed.
   :tpm-daa-input-data1        ;; The consistency check on DAA parameter inputData1 has failed.
   :tpm-daa-issuer-settings    ;; The consistency check on DAA_issuerSettings has failed.
   :tpm-daa-tpm-settings       ;; The consistency check on DAA_tpmSpecific has failed.
   :tpm-daa-stage              ;; The atomic process indicated by the submitted DAA command is not the expected process.
   :tpm-daa-issuer-validity    ;; The issuer's validity check has detected an inconsistency.
   :tpm-daa-wrong-w            ;; The consistency check on w has failed.
   :tpm-bad-handle             ;; The handle is incorrect.
   :tpm-bad-delegate           ;; Delegation is not correct.
   :tpm-badcontext             ;; The context blob is invalid.
   :tpm-toomanycontexts        ;; Too many contexts held by the TPM.
   :tpm-ma-ticket-signature    ;; Migration authority signature validation failure.
   :tpm-ma-destination         ;; Migration destination not authenticated.
   :tpm-ma-source              ;; Migration source incorrect.
   :tpm-ma-authority           ;; Incorrect migration authority.
   :tpm-permanentek            ;; Attempt to revoke the EK and the EK is not revocable.
   :tpm-bad-signature          ;; Bad signature of CMK ticket.
   :tpm-nocontextspace         ;; There is no room in the context list for additional contexts.
   :tpm-retry                  ;; The TPM is too busy to respond to the command immediately, but the command could be resubmitted at a later time.
   :tpm-needs-selftest         ;; --
   :tpm-doing-selftest         ;; --
   :tpm-defend-lock-running    ;; --
  )
  :parents(tpm-structures))

(defnd make-tpm-result ()
  :tpmx-default-enum-value)

;; 19.1 TPM_NV_INDEX
;; The index into the NV storage area
(cutil::defenum tpm-nv-index-p
  (:tpmx-default-enum-value
   :tpm-nv-index-lock         ;; (required) This value turns on the NV authorization protections. Once executed all NV areas us the protections as defined. This value never resets. Attempting to execute TPM_NV_DefineSpace on this val ...
   :tpm-nv-index0             ;; (required) This value allows for the setting of the bGlobalLock flag, which is only reset on TPM_Startup(ST_Clear). Attempting to execute TPM_NV_WriteValue with a size other than zero MAY result in th ...
   :tpm-nv-index-dir          ;; (required) Size MUST be 20. This index points to the deprecated DIR command area from 1.1. The TPM MUST map this reserved space to be the area operated on by the 1.1 DIR commands. As the DIR commands  ...
   :tpm-nv-index-tpm          ;; Reserved for TPM use
   :tpm-nv-index-ekcert       ;; The Endorsement credential
   :tpm-nv-index-tpm-cc       ;; The TPM Conformance credential
   :tpm-nv-index-platformcert ;; The platform credential
   :tpm-nv-index-platform-cc  ;; The Platform conformance credential
   :tpm-nv-index-trial        ;; To try TPM_NV_DefineSpace without actually allocating NV space
   :tpm-nv-index-pc           ;; Reserved for PC Client use
   :tpm-nv-index-gpio-xx      ;; Reserved for GPIO pins
   :tpm-nv-index-pda          ;; Reserved for PDA use
   :tpm-nv-index-mobile       ;; Reserved for mobile use
   :tpm-nv-index-server       ;; Reserved for Server use
   :tpm-nv-index-peripheral   ;; Reserved for peripheral use
   :tpm-nv-index-tss          ;; Reserved for TSS use
   :tpm-nv-index-group-resv   ;; Reserved for TCG WG's
  )
  :parents(tpm-structures))

(defnd make-tpm-nv-index ()
  :tpmx-default-enum-value)

;; 20.14 TPM_FAMILY_OPERATION
;; What operation is happening
(cutil::defenum tpm-family-operation-p
  (:tpmx-default-enum-value
   :tpm-family-create     ;; Create a new family
   :tpm-family-enable     ;; Set or reset the enable flag for this family.
   :tpm-family-admin      ;; Prevent administration of this family.
   :tpm-family-invalidate ;; Invalidate a specific family row.
  )
  :parents(tpm-structures))

(defnd make-tpm-family-operation ()
  :tpmx-default-enum-value)

;; 21.1 TPM_CAPABILITY_AREA_get()
(cutil::defenum tpm-capability-area-get-p
  (:tpmx-default-enum-value
   :tpm-cap-ord          ;; Boolean value. TRUE indicates that the TPM supports the ordinal. FALSE indicates that the TPM does not support the ordinal. Unimplemented optional ordinals and unused (unassigned) ordinals return FALS ...
   :tpm-cap-alg          ;; Boolean value. TRUE means that the TPM supports the asymmetric algorithm for TPM_Sign, TPM_Seal, TPM_UnSeal and TPM_UnBind and related commands. FALSE indicates that the asymmetric algorithm is not su ...
   :tpm-cap-pid          ;; Boolean value. TRUE indicates that the TPM supports the protocol, FALSE indicates that the TPM does not support the protocol. Unassigned protocol IDs return FALSE. ...
   :tpm-cap-flag         ;; See TPM_CAP_FLAG_SUBCAPS
   :tpm-cap-property     ;; See TPM_CAP_PROPERTY_SUBCAPS
   :tpm-cap-version      ;; TPM_STRUCT_VER structure. The major and minor version MUST indicate 1.1. The firmware revision MUST indicate 0.0. The use of this value is deprecated, new software SHOULD use TPM_CAP_VERSION_VAL to ob ...
   :tpm-cap-key-handle   ;; A TPM_KEY_HANDLE_LIST structure that enumerates all key handles loaded on the TPM. The list only contains the number of handles that an external manager can operate with and does not include the EK or ...
   :tpm-cap-check-loaded ;; A Boolean value. TRUE indicates that the TPM supports and has enough memory available to load a key of the type specified by the TPM_KEY_PARMS structure. FALSE indicates that the TPM does not support  ...
   :tpm-cap-sym-mode     ;; A Boolean value. TRUE indicates that the TPM supports the TPM_SYM_MODE, FALSE indicates the TPM does not support the mode. Unassigned modes return FALSE.
   ;; Unused             ;; --
   ;; Unused             ;; --
   :tpm-cap-key-status   ;; Boolean value of ownerEvict. The handle MUST point to a valid key handle. Return TPM_INVALID_KEYHANDLE for an unvalid handle.
   :tpm-cap-nv-list      ;; A list of TPM_NV_INDEX values that are currently allocated NV storage through TPM_NV_DefineSpace.
   ;; Unused             ;; --
   ;; Unused             ;; --
   :tpm-cap-mfr          ;; Manufacturer specific. The manufacturer may provide any additional information regarding the TPM and the TPM state but MUST not expose any sensitive information.
   :tpm-cap-nv-index     ;; A TPM_NV_DATA_PUBLIC structure that indicates the values for the TPM_NV_INDEX. Returns TPM_BADINDEX if the index is not in the TPM_CAP_NV_LIST list.
   :tpm-cap-trans-alg    ;; Boolean value. TRUE means that the TPM supports the algorithm for TPM_EstablishTransport, TPM_ExecuteTransport and TPM_ReleaseTransportSigned. FALSE indicates that for these three commands the algorit ...
   ;; Unused             ;; --
   :tpm-cap-handle       ;; A TPM_KEY_HANDLE_LIST structure that enumerates all handles currently loaded in the TPM for the given resource type. When describing keys the handle list only contains the number of handles that an ex ...
   :tpm-cap-trans-es     ;; Boolean value. TRUE means the TPM supports the encryption scheme in a transport session for at least one algorithm. Unassigned schemes return FALSE.
   ;; Unused             ;; --
   :tpm-cap-auth-encrypt ;; Boolean value. TRUE indicates that the TPM supports the encryption algorithm in OSAP encryption of AuthData values. Unassigned algorithm IDs return FALSE.
   :tpm-cap-select-size  ;; Boolean value. TRUE indicates that the TPM supports reqSize in TPM_PCR_SELECTION -> sizeOfSelect for the given version. For instance a request could ask for version 1.1 size 2 and the TPM would indica ...
   :tpm-cap-da-logic     ;; (OPTIONAL) A TPM_DA_INFO or TPM_DA_INFO_LIMITED structure that returns data according to the selected entity type (e.g., TPM_ET_KEYHANDLE, TPM_ET_OWNER, TPM_ET_SRK, TPM_ET_COUNTER, TPM_ET_OPERATOR, et ...
   :tpm-cap-version-val  ;; TPM_CAP_VERSION_INFO structure. The TPM fills in the structure and returns the information indicating what the TPM currently supports.
  )
  :parents(tpm-structures))

(defnd make-tpm-capability-area-get ()
  :tpmx-default-enum-value)

;; 21.1 TPM_CAP_FLAG_SUBCAPS()
(cutil::defenum tpm-cap-flag-subcaps-p
  (:tpmx-default-enum-value
   :tpm-cap-flag-permanent ;; Return the TPM_PERMANENT_FLAGS structure. Each flag in the structure returns as a byte.
   :tpm-cap-flag-volatile  ;; Return the TPM_STCLEAR_FLAGS structure. Each flag in the structure returns as a byte.
  )
  :parents(tpm-structures))

(defnd make-tpm-cap-flag-subcaps ()
  :tpmx-default-enum-value)

;; 21.2 TPM_CAP_PROPERTY_SUBCAPS()
(cutil::defenum tpm-cap-property-subcaps-p
  (:tpmx-default-enum-value
   :tpm-cap-prop-pcr              ;; UINT32 value. Returns the number of PCR registers supported by the TPM
   :tpm-cap-prop-dir              ;; UNIT32. Deprecated. Returns the number of DIR, which is now fixed at 1
   :tpm-cap-prop-manufacturer     ;; UINT32 value. Returns the vendor ID unique to each TPM manufacturer.
   :tpm-cap-prop-keys             ;; UINT32 value. Returns the number of 2048-bit RSA keys that can be loaded. This may vary with time and circumstances.
   :tpm-cap-prop-min-counter      ;; UINT32. The minimum amount of time in 10ths of a second that must pass between invocations of incrementing the monotonic counter.
   :tpm-cap-prop-authsess         ;; UINT32. The number of available authorization sessions. This may vary with time and circumstances.
   :tpm-cap-prop-transess         ;; UINT32. The number of available transport sessions. This may vary with time and circumstances
   :tpm-cap-prop-counters         ;; UINT32. The number of available monotonic counters. This may vary with time and circumstances.
   :tpm-cap-prop-max-authsess     ;; UINT32. The maximum number of loaded authorization sessions the TPM supports.
   :tpm-cap-prop-max-transess     ;; UINT32. The maximum number of loaded transport sessions the TPM supports.
   :tpm-cap-prop-max-counters     ;; UINT32. The maximum number of monotonic counters under control of TPM_CreateCounter
   :tpm-cap-prop-max-keys         ;; UINT32. The maximum number of 2048 RSA keys that the TPM can support. The number does not include the EK or SRK.
   :tpm-cap-prop-owner            ;; BOOL. A value of TRUE indicates that the TPM has successfully installed an owner.
   :tpm-cap-prop-context          ;; UINT32. The number of available saved session slots. This may vary with time and circumstances.
   :tpm-cap-prop-max-context      ;; UINT32. The maximum number of saved session slots.
   :tpm-cap-prop-familyrows       ;; UINT32. The maximum number of rows in the family table
   :tpm-cap-prop-tis-timeout      ;; A 4 element array of UINT32 values each denoting the timeout value in microseconds for the following in this order: TIMEOUT_A, TIMEOUT_B, TIMEOUT_C, TIMEOUT_D. Where these timeouts are to be used is d ...
   :tpm-cap-prop-startup-effect   ;; The TPM_STARTUP_EFFECTS structure
   :tpm-cap-prop-delegate-row     ;; UINT32. The maximum size of the delegate table in rows.
   ;; open                        ;; --
   :tpm-cap-prop-max-daasess      ;; UINT32. The maximum number of loaded DAA sessions (join or sign) that the TPM supports.
   :tpm-cap-prop-daasess          ;; UINT32. The number of available DAA sessions. This may vary with time and circumstances
   :tpm-cap-prop-context-dist     ;; UINT32. The maximum distance between context count values. This MUST be at least 2^16-1
   :tpm-cap-prop-daa-interrupt    ;; BOOL. A value of TRUE indicates that the TPM will accept ANY command while executing a DAA Join or Sign. A value of FALSE indicates that the TPM will invalidate the DAA Join or Sign upon the receipt o ...
   :tpm-cap-prop-sessions         ;; UNIT32. The number of available authorization and transport sessions from the pool. This may vary with time and circumstances.
   :tpm-cap-prop-max-sessions     ;; UINT32. The maximum number of sessions the TPM supports.
   :tpm-cap-prop-cmk-restriction  ;; UINT32 TPM_Permanent_Data -> restrictDelegate
   :tpm-cap-prop-duration         ;; A 3 element array of UINT32 values each denoting the duration value in microseconds of the duration of the three classes of commands: Small, Medium and Long in the following in this order: SMALL_DURAT ...
   ;; open                        ;; --
   :tpm-cap-prop-active-counter   ;; TPM_COUNT_ID. The id of the current counter. 0xff..ff if no counter is active, either because no counter has been set active or because the active counter has been released. ...
   :tpm-cap-prop-max-nv-available ;; UINT32. Deprecated. The maximum number of NV space that can be allocated, MAY vary with time and circumstances. This capability was not implemented consistently, and is replaced by TPM_NV_INDEX_TRIAL. ...
   :tpm-cap-prop-input-buffer     ;; UINT32. The maximum size of the TPM input buffer or output buffers in bytes.
   ;; XX                          ;; Next number
  )
  :parents(tpm-structures))

(defnd make-tpm-cap-property-subcaps ()
  :tpmx-default-enum-value)

;; 21.9 TPM_DA_STATE
;; The state of the dictionary attack mitigation logic
(cutil::defenum tpm-da-state-p
  (:tpmx-default-enum-value
   :tpm-da-state-inactive ;; The dictionary attack mitigation logic is currently inactive
   :tpm-da-state-active   ;; The dictionary attack mitigation logic is active. TPM_DA_ACTION_TYPE (21.10) is in progress.
  )
  :parents(tpm-structures))

(defnd make-tpm-da-state ()
  :tpmx-default-enum-value)

; ===============================================================
; Level 0 Records
; ===============================================================

;; 5.1 TPM_STRUCT_VER()
(cutil::defaggregate tpm-struct-ver
  ((major byte-p "This SHALL indicate the major version of the structure. MUST be 0x01"
     :default (make-byte))
   (minor byte-p "This SHALL indicate the minor version of the structure. MUST be 0x01"
     :default (make-byte))
   (rev-major byte-p "This MUST be 0x00 on output, ignored on input"
     :default (make-byte))
   (rev-minor byte-p "This MUST be 0x00 on output, ignored on input"
     :default (make-byte))
  )
  :parents(tpm-structures))

;; 5.4 TPM_DIGEST()
(cutil::defaggregate tpm-digest
  ((digest byte-list-p "This SHALL be the actual digest information"
     :default (make-byte-list))
  )
  :parents(tpm-structures))

(cutil::deflist tpm-digest-list-p (x)
  (tpm-digest-p x)
  :elementp-of-nil nil
  :true-listp t
  :parents(tpm-structures))

(defnd make-tpm-digest-list ()
  nil)

;; 5.5 TPM_NONCE()
(cutil::defaggregate tpm-nonce
  ((nonce 20-byte-list-p "This SHALL be the 20 bytes of random data. When created by the TPM the value MUST be the next 20 bytes from the RNG."
     :default (make-20-byte-list))
  )
  :parents(tpm-structures))

;; 5.7 TPM_KEY_HANDLE_LIST()
(cutil::defaggregate tpm-key-handle-list
  ((loaded uint16-p "The number of keys currently loaded in the TPM."
     :default (make-uint16))
   (handle uint32-p "An array of handles, one for each key currently loaded in the TPM"
     :default (make-uint32))
  )
  :parents(tpm-structures))

;; 5.18 TPM_SELECT_SIZE()
(cutil::defaggregate tpm-select-size
  ((major byte-p "This SHALL indicate the major version of the TPM. This MUST be 0x01"
     :default (make-byte))
   (minor byte-p "This SHALL indicate the minor version of the TPM. This MAY be 0x01 or 0x02"
     :default (make-byte))
   (req-size uint16-p "This SHALL indicate the value for a sizeOfSelect field in the TPM_SELECTION structure"
     :default (make-uint16))
  )
  :parents(tpm-structures))

;; 7.6 TPM_SESSION_DATA()
(cutil::defaggregate tpm-session-data
  ((place-holder booleanp "Vendor specific"
     :default nil)
  )
  :parents(tpm-structures))

(cutil::deflist tpm-session-data-list-p (x)
  (tpm-session-data-p x)
  :elementp-of-nil nil
  :true-listp t
  :parents(tpm-structures))

(defnd make-tpm-session-data-list ()
  nil)

;; 8.1 TPM_PCR_SELECTION()
(cutil::defaggregate tpm-pcr-selection
  ((size-of-select uint16-p "The size in bytes of the pcrSelect structure"
     :default (make-uint16))
   (pcr-select byte-list-p "This SHALL be a bit map that indicates if a PCR is active or not"
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 10.1 TPM_RSA_KEY_PARMS()
(cutil::defaggregate tpm-rsa-key-parms
  ((key-length uint32-p "This specifies the size of the RSA key in bits"
     :default (make-uint32))
   (num-primes uint32-p "This specifies the number of prime factors used by this RSA key."
     :default (make-uint32))
   (exponent-size uint32-p "This SHALL be the size of the exponent. If the key is using the default exponent then the exponentSize MUST be 0."
     :default (make-uint32))
   (exponent byte-list-p "The public exponent of this key"
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 10.1 TPM_SYMMETRIC_KEY_PARMS()
(cutil::defaggregate tpm-symmetric-key-parms
  ((key-length uint32-p "This SHALL indicate the length of the key in bits"
     :default (make-uint32))
   (block-size uint32-p "This SHALL indicate the block size of the algorithm"
     :default (make-uint32))
   (iv-size uint32-p "This SHALL indicate the size of the IV"
     :default (make-uint32))
   (iv byte-list-p "The initialization vector"
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 10.4 TPM_STORE_PUBKEY()
(cutil::defaggregate tpm-store-pubkey
  ((key-length uint32-p "This SHALL be the length of the key field."
     :default (make-uint32))
   (key byte-list-p "This SHALL be a structure interpreted according to the algorithm Id in the corresponding TPM_KEY_PARMS structure."
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 10.7 TPM_STORE_PRIVKEY()
(cutil::defaggregate tpm-store-privkey
  ((key-length uint32-p "This SHALL be the length of the key field."
     :default (make-uint32))
   (key byte-list-p "This SHALL be a structure interpreted according to the algorithm Id in the corresponding TPM_KEY structure."
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 20.4 TPM_FAMILY_LABEL()
(cutil::defaggregate tpm-family-label
  ((label byte-p "A sequence number that software can map to a string of bytes that can be displayed or used by the applications. This MUST not contain sensitive information."
     :default (make-byte))
  )
  :parents(tpm-structures))

;; 20.7 TPM_DELEGATE_LABEL()
(cutil::defaggregate tpm-delegate-label
  ((label byte-p "A byte that can be displayed or used by the applications. This MUST not contain sensitive information."
     :default (make-byte))
  )
  :parents(tpm-structures))

; ===============================================================
; Level 1 Wrappers
; ===============================================================

;; 5.4 TPM_AUDITDIGEST
;; This SHALL be the value of the current internal audit state
(defprimitive tpm-auditdigest (x)
  (tpm-digest-p x)
  :default (make-tpm-digest)
  :parents(tpm-structures))

;; 5.4 TPM_CHOSENID_HASH
;; This SHALL be the digest of the chosen identityLabel and privacyCA for a new TPM identity.
(defprimitive tpm-chosenid-hash (x)
  (tpm-digest-p x)
  :default (make-tpm-digest)
  :parents(tpm-structures))

;; 5.4 TPM_COMPOSITE_HASH
;; This SHALL be the hash of a list of PCR indexes and PCR values that a key or data is bound to.
(defprimitive tpm-composite-hash (x)
  (tpm-digest-p x)
  :default (make-tpm-digest)
  :parents(tpm-structures))

;; 5.4 TPM_DIRVALUE
;; This SHALL be the value of a DIR register
(defprimitive tpm-dirvalue (x)
  (tpm-digest-p x)
  :default (make-tpm-digest)
  :parents(tpm-structures))

(cutil::deflist tpm-dirvalue-list-p (x)
  (tpm-dirvalue-p x)
  :elementp-of-nil nil
  :true-listp t
  :parents(tpm-structures))

(defnd make-tpm-dirvalue-list ()
  nil)

;; 5.4 TPM_HMAC
;; This shall be the output of the HMAC algorithm
(defprimitive tpm-hmac (x)
  (tpm-digest-p x)
  :default (make-tpm-digest)
  :parents(tpm-structures))

;; 5.4 TPM_PCRVALUE
;; The value inside of the PCR
(defprimitive tpm-pcrvalue (x)
  (tpm-digest-p x)
  :default (make-tpm-digest)
  :parents(tpm-structures))

(cutil::deflist tpm-pcrvalue-list-p (x)
  (tpm-pcrvalue-p x)
  :elementp-of-nil nil
  :true-listp t
  :parents(tpm-structures))

(defnd make-tpm-pcrvalue-list ()
  nil)

;; 5.5 TPM_DAA_CONTEXT_SEED
;; This SHALL be a random value
(defprimitive tpm-daa-context-seed (x)
  (tpm-nonce-p x)
  :default (make-tpm-nonce)
  :parents(tpm-structures))

;; 5.5 TPM_DAA_TPM_SEED
;; This SHALL be a random value generated by a TPM immediately after the EK is installed in that TPM, whenever an EK is installed in that TPM
(defprimitive tpm-daa-tpm-seed (x)
  (tpm-nonce-p x)
  :default (make-tpm-nonce)
  :parents(tpm-structures))

;; 5.6 TPM_ENCAUTH
;; A ciphertext (encrypted) version of AuthData data. The encryption mechanism depends on the context.
(defprimitive tpm-encauth (x)
  (tpm-authdata-p x)
  :default (make-tpm-authdata)
  :parents(tpm-structures))

;; 5.6 TPM_SECRET
;; A secret plaintext value used in the authorization process.
(defprimitive tpm-secret (x)
  (tpm-authdata-p x)
  :default (make-tpm-authdata)
  :parents(tpm-structures))

; ===============================================================
; Level 1 Records
; ===============================================================

;;  TPMX_AUTH_INFO()
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

;; 5.3 TPM_VERSION()
(cutil::defaggregate tpm-version
  ((major tpm-version-byte-p "This SHALL indicate the major version of the TPM, mostSigVer MUST be 0x01, leastSigVer MUST be 0x00"
     :default (make-tpm-version-byte))
   (minor tpm-version-byte-p "This SHALL indicate the minor version of the TPM, mostSigVer MUST be 0x01 or 0x02, leastSigVer MUST be 0x00"
     :default (make-tpm-version-byte))
   (rev-major byte-p "This SHALL be the value of the TPM_PERMANENT_DATA -> revMajor"
     :default (make-byte))
   (rev-minor byte-p "This SHALL be the value of the TPM_PERMANENT_DATA -> revMinor"
     :default (make-byte))
  )
  :parents(tpm-structures))

;; 5.13 TPM_COUNTER_VALUE()
(cutil::defaggregate tpm-counter-value
  ((tag tpm-structure-tag-p "TPM_TAG_COUNTER_VALUE"
     :default (make-tpm-structure-tag))
   (label 4-byte-list-p "The label for the counter"
     :default (make-4-byte-list))
   (counter tpm-actual-count-p "The 32-bit counter value."
     :default (make-tpm-actual-count))
  )
  :parents(tpm-structures))

(cutil::deflist tpm-counter-value-list-p (x)
  (tpm-counter-value-p x)
  :elementp-of-nil nil
  :true-listp t
  :parents(tpm-structures))

(defnd make-tpm-counter-value-list ()
  nil)

;; 5.14 TPM_SIGN_INFO()
(cutil::defaggregate tpm-sign-info
  ((tag tpm-structure-tag-p "Set to TPM_TAG_SIGNINFO"
     :default (make-tpm-structure-tag))
   (fixed 4-byte-list-p "The ASCII text that identifies what function was performing the signing operation"
     :default (make-4-byte-list))
   (replay tpm-nonce-p "Nonce provided by caller to prevent replay attacks"
     :default (make-tpm-nonce))
   (data-len uint32-p "The length of the data area"
     :default (make-uint32))
   (data byte-list-p "The data that is being signed"
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 5.15 TPM_MSA_COMPOSITE()
(cutil::defaggregate tpm-msa-composite
  ((ms-alist uint32-p "The number of migAuthDigests. MSAlist MUST be one (1) or greater."
     :default (make-uint32))
   (mig-auth-digest tpm-digest-list-p "An arbitrary number of digests of public keys belonging to Migration Authorities."
     :default (make-tpm-digest-list))
  )
  :parents(tpm-structures))

;; 5.16 TPM_CMK_AUTH()
(cutil::defaggregate tpm-cmk-auth
  ((migration-authority-digest tpm-digest-p "The digest of a public key belonging to a Migration Authority"
     :default (make-tpm-digest))
   (destination-key-digest tpm-digest-p "The digest of a TPM_PUBKEY structure that is an approved destination key for the private key associated with 'sourceKey'"
     :default (make-tpm-digest))
   (source-key-digest tpm-digest-p "The digest of a TPM_PUBKEY structure whose corresponding private key is approved by a Migration Authority to be migrated as a child to the destinationKey."
     :default (make-tpm-digest))
  )
  :parents(tpm-structures))

;; 5.19 TPM_CMK_MIGAUTH()
(cutil::defaggregate tpm-cmk-migauth
  ((tag tpm-structure-tag-p "Set to TPM_TAG_CMK_MIGAUTH"
     :default (make-tpm-structure-tag))
   (msa-digest tpm-digest-p "The digest of a TPM_MSA_COMPOSITE structure containing the migration authority public key and parameters."
     :default (make-tpm-digest))
   (pub-key-digest tpm-digest-p "The hash of the associated public key"
     :default (make-tpm-digest))
  )
  :parents(tpm-structures))

;; 5.20 TPM_CMK_SIGTICKET()
(cutil::defaggregate tpm-cmk-sigticket
  ((tag tpm-structure-tag-p "Set to TPM_TAG_CMK_SIGTICKET"
     :default (make-tpm-structure-tag))
   (ver-key-digest tpm-digest-p "The hash of a TPM_PUBKEY structure containing the public key and parameters of the key that can verify the ticket"
     :default (make-tpm-digest))
   (signed-data tpm-digest-p "The ticket data"
     :default (make-tpm-digest))
  )
  :parents(tpm-structures))

;; 5.21 TPM_CMK_MA_APPROVAL()
(cutil::defaggregate tpm-cmk-ma-approval
  ((tag tpm-structure-tag-p "Set to TPM_TAG_CMK_MA_APPROVAL"
     :default (make-tpm-structure-tag))
   (migration-authority-digest tpm-digest-p "The hash of a TPM_MSA_COMPOSITE structure containing the hash of one or more migration authority public keys and parameters."
     :default (make-tpm-digest))
  )
  :parents(tpm-structures))

;; 7.1 TPM_PERMANENT_FLAGS()
(cutil::defaggregate tpm-permanent-flags
  ((tag tpm-structure-tag-p "TPM_TAG_PERMANENT_FLAGS"
     :default (make-tpm-structure-tag))
   (disable booleanp "The state of the disable flag. The default state is TRUE"
     :default nil)
   (ownership booleanp "The ability to install an owner. The default state is TRUE."
     :default nil)
   (deactivated booleanp "The state of the inactive flag. The default state is TRUE."
     :default nil)
   (read-pubek booleanp "The ability to read the PUBEK without owner AuthData. The default state is TRUE."
     :default nil)
   (disable-owner-clear booleanp "Whether the owner authorized clear commands are active. The default state is FALSE."
     :default nil)
   (allow-maintenance booleanp "Whether the TPM Owner may create a maintenance archive. The default state is TRUE if maintenance is implemented, vendor specific if maintenance is not implemented. ..."
     :default nil)
   (physical-presence-lifetime-lock booleanp "This bit can only be set to TRUE; it cannot be set to FALSE except during the manufacturing process. FALSE: The state of either physicalPresenceHWEnable or physicalPresenceCMDEnable MAY be changed. (D ..."
     :default nil)
   (physical-presence-hw-enable booleanp "FALSE: Disable the hardware signal indicating physical presence. (DEFAULT) TRUE: Enables the hardware signal indicating physical presence."
     :default nil)
   (physical-presence-cmd-enable booleanp "FALSE: Disable the command indicating physical presence. (DEFAULT) TRUE: Enables the command indicating physical presence."
     :default nil)
   (cekp-used booleanp "TRUE: The PRIVEK and PUBEK were created using TPM_CreateEndorsementKeyPair. FALSE: The PRIVEK and PUBEK were created using a manufacturer's process. NOTE: This flag has no default value as the key pai ..."
     :default nil)
   (tp-mpost booleanp "The meaning of this bit clarified in rev87. While actual use does not match the name, for backwards compatibility there is no change to the name. TRUE: After TPM_Startup, if there is a call to TPM_Con ..."
     :default nil)
   (tp-mpost-lock booleanp "With the clarification of TPMPost TPMpostLock is now unnecessary. This flag is now deprecated"
     :default nil)
   (fips booleanp "TRUE: This TPM operates in FIPS mode FALSE: This TPM does NOT operate in FIPS mode"
     :default nil)
   (operator booleanp "TRUE: The operator AuthData value is valid FALSE: the operator AuthData value is not set (DEFAULT)"
     :default nil)
   (enable-revoke-ek booleanp "TRUE: The TPM_RevokeTrust command is active FALSE: the TPM RevokeTrust command is disabled"
     :default nil)
   (nv-locked booleanp "TRUE: All NV area authorization checks are active FALSE: No NV area checks are performed, except for maxNVWrites. FALSE is the default value"
     :default nil)
   (read-srk-pub booleanp "TRUE: GetPubKey will return the SRK pub key FALSE: GetPubKey will not return the SRK pub key Default SHOULD be FALSE. See the informative."
     :default nil)
   (tpm-established booleanp "TRUE: TPM_HASH_START has been executed at some time FALSE: TPM_HASH_START has not been executed at any time Default is FALSE. Reset to FALSE using TSC_ResetEstablishmentBit ..."
     :default nil)
   (maintenance-done booleanp "TRUE: A maintenance archive has been created for the current SRK"
     :default nil)
   (disable-full-da-logic-info booleanp "TRUE: The full dictionary attack TPM_GetCapability info is deactivated. The returned structure is TPM_DA_INFO_LIMITED. FALSE: The full dictionary attack TPM_GetCapability info is activated. The return ..."
     :default nil)
  )
  :parents(tpm-structures))

;; 7.2 TPM_STCLEAR_FLAGS()
(cutil::defaggregate tpm-stclear-flags
  ((tag tpm-structure-tag-p "TPM_TAG_STCLEAR_FLAGS"
     :default (make-tpm-structure-tag))
   (deactivated booleanp "Prevents the operation of most capabilities. There is no default state. It is initialized by TPM_Startup to the same value as TPM_PERMANENT_FLAGS -> deactivated or a set value depending on the type of ..."
     :default nil)
   (disable-force-clear booleanp "Prevents the operation of TPM_ForceClear when TRUE. The default state is FALSE. TPM_DisableForceClear sets it to TRUE."
     :default nil)
   (physical-presence booleanp "Command assertion of physical presence. The default state is FALSE. This flag is affected by the TSC_PhysicalPresence command but not by the hardware signal."
     :default nil)
   (physical-presence-lock booleanp "Indicates whether changes to the TPM_STCLEAR_FLAGS -> physicalPresence flag are permitted. TPM_Startup(ST_CLEAR) sets PhysicalPresenceLock to its default state of FALSE (allow changes to the physicalP ..."
     :default nil)
   (b-global-lock booleanp "Set to FALSE on each TPM_Startup(ST_CLEAR). Set to TRUE when a write to NV_Index =0 is successful"
     :default nil)
  )
  :parents(tpm-structures))

;; 7.3 TPM_STANY_FLAGS()
(cutil::defaggregate tpm-stany-flags
  ((tag tpm-structure-tag-p "TPM_TAG_STANY_FLAGS"
     :default (make-tpm-structure-tag))
   (post-initialise booleanp "Prevents the operation of most capabilities. There is no default state. It is initialized by TPM_Init to TRUE. TPM_Startup sets it to FALSE."
     :default nil)
   (locality-modifier tpm-modifier-indicator-p "This SHALL indicate for each command the presence of a locality modifier for the command. It MUST be always ensured that the value during usage reflects the currently active locality. ..."
     :default (make-tpm-modifier-indicator))
   (transport-exclusive booleanp "Defaults to FALSE. TRUE when there is an exclusive transport session active. Execution of ANY command other than TPM_ExecuteTransport targeting the exclusive transport session MUST invalidate the excl ..."
     :default nil)
   (tos-present booleanp "Defaults to FALSE Set to TRUE on TPM_HASH_START set to FALSE using setCapability"
     :default nil)
  )
  :parents(tpm-structures))

;; 8.8 TPM_PCR_ATTRIBUTES()
(cutil::defaggregate tpm-pcr-attributes
  ((pcr-reset booleanp "A value of TRUE SHALL indicate that the PCR register can be reset using the TPM_PCR_Reset command. If pcrReset is: FALSE- Default value of the PCR MUST be 0x00..00 Reset on TPM_Startup(ST_Clear) only  ..."
     :default nil)
   (pcr-reset-local tpm-locality-selection-p "An indication of which localities can reset the PCR"
     :default (make-tpm-locality-selection))
   (pcr-extend-local tpm-locality-selection-p "An indication of which localities can perform extends on the PCR."
     :default (make-tpm-locality-selection))
  )
  :parents(tpm-structures))

(cutil::deflist tpm-pcr-attributes-list-p (x)
  (tpm-pcr-attributes-p x)
  :elementp-of-nil nil
  :true-listp t
  :parents(tpm-structures))

(defnd make-tpm-pcr-attributes-list ()
  nil)

;; 9.1 TPM_STORED_DATA()
(cutil::defaggregate tpm-stored-data
  ((ver tpm-struct-ver-p "This MUST be 1.1.0.0"
     :default (make-tpm-struct-ver))
   (seal-info-size uint32-p "Size of the sealInfo parameter"
     :default (make-uint32))
   (seal-info byte-list-p "This SHALL be a structure of type TPM_PCR_INFO or a 0 length array if the data is not bound to PCRs."
     :default (make-byte-list))
   (enc-data-size uint32-p "This SHALL be the size of the encData parameter"
     :default (make-uint32))
   (enc-data byte-list-p "This shall be an encrypted TPM_SEALED_DATA structure containing the confidential part of the data."
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 9.2 TPM_STORED_DATA12()
(cutil::defaggregate tpm-stored-data12
  ((tag tpm-structure-tag-p "This SHALL be TPM_TAG_STORED_DATA12"
     :default (make-tpm-structure-tag))
   (et tpm-entity-type-p "The type of blob"
     :default (make-tpm-entity-type))
   (seal-info-size uint32-p "Size of the sealInfo parameter"
     :default (make-uint32))
   (seal-info byte-list-p "This SHALL be a structure of type TPM_PCR_INFO_LONG"
     :default (make-byte-list))
   (enc-data-size uint32-p "This SHALL be the size of the encData parameter"
     :default (make-uint32))
   (enc-data byte-list-p "This shall be an encrypted TPM_SEALED_DATA structure containing the confidential part of the data."
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 9.4 TPM_SYMMETRIC_KEY()
(cutil::defaggregate tpm-symmetric-key
  ((alg-id tpm-algorithm-id-p "This SHALL be the algorithm identifier of the symmetric key."
     :default (make-tpm-algorithm-id))
   (enc-scheme tpm-enc-scheme-p "This SHALL fully identify the manner in which the key will be used for encryption operations."
     :default (make-tpm-enc-scheme))
   (size uint16-p "This SHALL be the size of the data parameter in bytes"
     :default (make-uint16))
   (data byte-list-p "This SHALL be the symmetric key data"
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 9.5 TPM_BOUND_DATA()
(cutil::defaggregate tpm-bound-data
  ((ver tpm-struct-ver-p "This MUST be 1.1.0.0"
     :default (make-tpm-struct-ver))
   (payload tpm-payload-type-p "This SHALL be the value TPM_PT_BIND"
     :default (make-tpm-payload-type))
   (payload-data byte-list-p "The bound data"
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 10.1 TPM_KEY_PARMS()
(cutil::defaggregate tpm-key-parms
  ((algorithm-id tpm-algorithm-id-p "This SHALL be the key algorithm in use"
     :default (make-tpm-algorithm-id))
   (enc-scheme tpm-enc-scheme-p "This SHALL be the encryption scheme that the key uses to encrypt information"
     :default (make-tpm-enc-scheme))
   (sig-scheme tpm-sig-scheme-p "This SHALL be the signature scheme that the key uses to perform digital signatures"
     :default (make-tpm-sig-scheme))
   (parm-size uint32-p "This SHALL be the size of the parms field in bytes"
     :default (make-uint32))
   (parms byte-list-p "This SHALL be the parameter information dependant upon the key algorithm."
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 12.1 TPM_EK_BLOB()
(cutil::defaggregate tpm-ek-blob
  ((tag tpm-structure-tag-p "TPM_TAG_EK_BLOB"
     :default (make-tpm-structure-tag))
   (ek-type tpm-ek-type-p "This SHALL be set to reflect the type of blob in use"
     :default (make-tpm-ek-type))
   (blob-size uint32-p "The size of the blob field"
     :default (make-uint32))
   (blob byte-list-p "The blob of information depending on the type"
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 13.1 TPM_TRANSPORT_PUBLIC()
(cutil::defaggregate tpm-transport-public
  ((tag tpm-structure-tag-p "TPM_TAG_TRANSPORT_PUBLIC"
     :default (make-tpm-structure-tag))
   (trans-attributes tpm-transport-attributes-p "The attributes of this session"
     :default (make-tpm-transport-attributes))
   (alg-id tpm-algorithm-id-p "This SHALL be the algorithm identifier of the symmetric key."
     :default (make-tpm-algorithm-id))
   (enc-scheme tpm-enc-scheme-p "This SHALL fully identify the manner in which the key will be used for encryption operations."
     :default (make-tpm-enc-scheme))
  )
  :parents(tpm-structures))

;; 13.3 TPM_TRANSPORT_LOG_IN()
(cutil::defaggregate tpm-transport-log-in
  ((tag tpm-structure-tag-p "TPM_TAG_TRANSPORT_LOG_IN"
     :default (make-tpm-structure-tag))
   (parameters tpm-digest-p "The actual parameters contained in the digest are subject to the rules of the command using this structure. To find the exact calculation refer to the actions in the command using this structure. ..."
     :default (make-tpm-digest))
   (pub-key-hash tpm-digest-p "The hash of any keys in the transport command"
     :default (make-tpm-digest))
  )
  :parents(tpm-structures))

;; 13.5 TPM_TRANSPORT_AUTH()
(cutil::defaggregate tpm-transport-auth
  ((tag tpm-structure-tag-p "TPM_TAG_TRANSPORT_AUTH"
     :default (make-tpm-structure-tag))
   (auth-data tpm-authdata-p "The AuthData value"
     :default (make-tpm-authdata))
  )
  :parents(tpm-structures))

;; 15.1 TPM_CURRENT_TICKS()
(cutil::defaggregate tpm-current-ticks
  ((tag tpm-structure-tag-p "TPM_TAG_CURRENT_TICKS"
     :default (make-tpm-structure-tag))
   (current-ticks uint64-p "The number of ticks since the start of this tick session"
     :default (make-uint64))
   (tick-rate uint16-p "The number of microseconds per tick. The maximum resolution of the TPM tick counter is thus 1 microsecond. The minimum resolution SHOULD be 1 millisecond."
     :default (make-uint16))
   (tick-nonce tpm-nonce-p "The nonce created by the TPM when resetting the currentTicks to 0. This indicates the beginning of a time session. This value MUST be valid before the first use of TPM_CURRENT_TICKS. The value can be  ..."
     :default (make-tpm-nonce))
  )
  :parents(tpm-structures))

;; 18.1 TPM_CONTEXT_BLOB()
(cutil::defaggregate tpm-context-blob
  ((tag tpm-structure-tag-p "MUST be TPM_TAG_CONTEXTBLOB"
     :default (make-tpm-structure-tag))
   (resource-type tpm-resource-type-p "The resource type"
     :default (make-tpm-resource-type))
   (handle tpm-handle-p "Previous handle of the resource"
     :default (make-tpm-handle))
   (label 16-byte-list-p "Label for identification of the blob. Free format area."
     :default (make-16-byte-list))
   (context-count uint32-p "MUST be TPM_STANY_DATA -> contextCount when creating the structure. This value is ignored for context blobs that reference a key."
     :default (make-uint32))
   (integrity-digest tpm-digest-p "The integrity of the entire blob including the sensitive area. This is a HMAC calculation with the entire structure (including sensitiveData) being the hash and tpmProof is the secret ..."
     :default (make-tpm-digest))
   (additional-size uint32-p "The size of additionalData"
     :default (make-uint32))
   (additional-data byte-list-p "Additional information set by the TPM that helps define and reload the context. The information held in this area MUST NOT expose any information held in shielded locations. This should include any IV ..."
     :default (make-byte-list))
   (sensitive-size uint32-p "The size of sensitiveData"
     :default (make-uint32))
   (sensitive-data byte-list-p "The normal information for the resource that can be exported"
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 18.2 TPM_CONTEXT_SENSITIVE()
(cutil::defaggregate tpm-context-sensitive
  ((tag tpm-structure-tag-p "MUST be TPM_TAG_CONTEXT_SENSITIVE"
     :default (make-tpm-structure-tag))
   (context-nonce tpm-nonce-p "On context blobs other than keys this MUST be TPM_STANY_DATA -> contextNonceSession For keys the value is TPM_STCLEAR_DATA -> contextNonceKey"
     :default (make-tpm-nonce))
   (internal-size uint32-p "The size of the internalData area"
     :default (make-uint32))
   (internal-data byte-list-p "The internal data area"
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 19.2 TPM_NV_ATTRIBUTES()
(cutil::defaggregate tpm-nv-attributes
  ((tag tpm-structure-tag-p "TPM_TAG_NV_ATTRIBUTES"
     :default (make-tpm-structure-tag))
   (attributes uint32-p "The attribute area"
     :default (make-uint32))
  )
  :parents(tpm-structures))

;; 19.3 TPM_NV_DATA_PUBLIC()
(cutil::defaggregate tpm-nv-data-public
  ((tag tpm-structure-tag-p "TPM_TAG_NV_ATTRIBUTES"
     :default (make-tpm-structure-tag))
   (attributes uint32-p "The attribute area"
     :default (make-uint32))
  )
  :parents(tpm-structures))

;; 20.2 TPM_DELEGATIONS()
(cutil::defaggregate tpm-delegations
  ((tag tpm-structure-tag-p "This SHALL be TPM_TAG_DELEGATIONS"
     :default (make-tpm-structure-tag))
   (delegate-type uint32-p "Owner or key"
     :default (make-uint32))
   (per1 uint32-p "The first block of permissions"
     :default (make-uint32))
   (per2 uint32-p "The second block of permissions"
     :default (make-uint32))
  )
  :parents(tpm-structures))

;; 20.5 TPM_FAMILY_TABLE_ENTRY()
(cutil::defaggregate tpm-family-table-entry
  ((tag tpm-structure-tag-p "This SHALL be TPM_TAG_FAMILY_TABLE_ENTRY"
     :default (make-tpm-structure-tag))
   (family-label tpm-family-label-p "A sequence number that software can map to a string of bytes that can be displayed or used by the applications. This MUST not contain sensitive information."
     :default (make-tpm-family-label))
   (family-id tpm-family-id-p "The family ID in use to tie values together. This is not a sensitive value."
     :default (make-tpm-family-id))
   (verification-count tpm-family-verification-p "The value inserted into delegation rows to indicate that they are the current generation of rows. Used to identify when a row in the delegate table was last verified. This is not a sensitive value. ..."
     :default (make-tpm-family-verification))
   (flags tpm-family-flags-p "See section on TPM_FAMILY_FLAGS."
     :default (make-tpm-family-flags))
  )
  :parents(tpm-structures))

;; 21.10 TPM_DA_ACTION_TYPE()
(cutil::defaggregate tpm-da-action-type
  ((tag tpm-structure-tag-p "MUST be TPM_TAG_DA_ACTION_TYPE"
     :default (make-tpm-structure-tag))
   (actions uint32-p "The action taken when TPM_DA_STATE is TPM_DA_STATE_ACTIVE."
     :default (make-uint32))
  )
  :parents(tpm-structures))

;; 22.3 TPM_DAA_ISSUER()
(cutil::defaggregate tpm-daa-issuer
  ((tag tpm-structure-tag-p "MUST be TPM_TAG_DAA_ISSUER"
     :default (make-tpm-structure-tag))
   (daa-digest-r0 tpm-digest-p "A digest of the parameter 'R0', which is not secret and may be common to many TPMs."
     :default (make-tpm-digest))
   (daa-digest-r1 tpm-digest-p "A digest of the parameter 'R1', which is not secret and may be common to many TPMs."
     :default (make-tpm-digest))
   (daa-digest-s0 tpm-digest-p "A digest of the parameter 'S0', which is not secret and may be common to many TPMs."
     :default (make-tpm-digest))
   (daa-digest-s1 tpm-digest-p "A digest of the parameter 'S1', which is not secret and may be common to many TPMs."
     :default (make-tpm-digest))
   (daa-digest-n tpm-digest-p "A digest of the parameter 'n', which is not secret and may be common to many TPMs."
     :default (make-tpm-digest))
   (daa-digest-gamma tpm-digest-p "A digest of the parameter 'gamma', which is not secret and may be common to many TPMs."
     :default (make-tpm-digest))
   (daa-generic-q 26-byte-list-p "The parameter q, which is not secret and may be common to many TPMs. Note that q is slightly larger than a digest, but is stored in its native form to simplify the TPM_DAA_join command. Otherwise, JOI ..."
     :default (make-26-byte-list))
  )
  :parents(tpm-structures))

;; 22.4 TPM_DAA_TPM()
(cutil::defaggregate tpm-daa-tpm
  ((tag tpm-structure-tag-p "MUST be TPM_TAG_DAA_TPM"
     :default (make-tpm-structure-tag))
   (daa-digestissuer tpm-digest-p "A digest of a TPM_DAA_ISSUER structure that contains the parameters used to generate this TPM_DAA_TPM structure."
     :default (make-tpm-digest))
   (daa-digest-v0 tpm-digest-p "A digest of the parameter 'v0', which is secret and specific to this TPM. 'v0' is generated during a JOIN phase."
     :default (make-tpm-digest))
   (daa-digest-v1 tpm-digest-p "A digest of the parameter 'v1', which is secret and specific to this TPM. 'v1' is generated during a JOIN phase."
     :default (make-tpm-digest))
   (daa-rekey tpm-digest-p "A digest related to the rekeying process, which is not secret but is specific to this TPM, and must be consistent across JOIN/SIGN sessions. 'rekey' is generated during a JOIN phase. ..."
     :default (make-tpm-digest))
   (daa-count uint32-p "The parameter 'count', which is not secret but must be consistent across JOIN/SIGN sessions. 'count' is an input to the TPM from the host system."
     :default (make-uint32))
  )
  :parents(tpm-structures))

;; 22.6 TPM_DAA_JOINDATA()
(cutil::defaggregate tpm-daa-joindata
  ((daa-join-u0 128-byte-list-p "A TPM-specific secret 'u0', used during the JOIN phase, and discarded afterwards."
     :default (make-128-byte-list))
   (daa-join-u1 128-byte-list-p "A TPM-specific secret 'u1', used during the JOIN phase, and discarded afterwards."
     :default (make-128-byte-list))
   (daa-digest-n0 tpm-digest-p "A digest of the parameter 'n0', which is an RSA public key with exponent 2^16 +1"
     :default (make-tpm-digest))
  )
  :parents(tpm-structures))

;; 22.8 TPM_DAA_BLOB()
(cutil::defaggregate tpm-daa-blob
  ((tag tpm-structure-tag-p "MUST be TPM_TAG_DAA_BLOB"
     :default (make-tpm-structure-tag))
   (resource-type tpm-resource-type-p "The resource type: enc(DAA_tpmSpecific) or enc(v0) or enc(v1)"
     :default (make-tpm-resource-type))
   (label 16-byte-list-p "Label for identification of the blob. Free format area."
     :default (make-16-byte-list))
   (blob-integrity tpm-digest-p "The integrity of the entire blob including the sensitive area. This is a HMAC calculation with the entire structure (including sensitiveData) being the hash and daaProof is the secret ..."
     :default (make-tpm-digest))
   (additional-size uint32-p "The size of additionalData"
     :default (make-uint32))
   (additional-data byte-list-p "Additional information set by the TPM that helps define and reload the context. The information held in this area MUST NOT expose any information held in shielded locations. This should include any IV ..."
     :default (make-byte-list))
   (sensitive-size uint32-p "The size of sensitiveData"
     :default (make-uint32))
   (sensitive-data byte-list-p "A TPM_DAA_SENSITIVE structure"
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 22.9 TPM_DAA_SENSITIVE()
(cutil::defaggregate tpm-daa-sensitive
  ((tag tpm-structure-tag-p "MUST be TPM_TAG_DAA_SENSITIVE"
     :default (make-tpm-structure-tag))
   (internal-size uint32-p "The size of the internalData area"
     :default (make-uint32))
   (internal-data byte-list-p "DAA_tpmSpecific or DAA_private_v0 or DAA_private_v1"
     :default (make-byte-list))
  )
  :parents(tpm-structures))

; ===============================================================
; Level 2 Records
; ===============================================================

;; 5.11 TPM_CHANGEAUTH_VALIDATE()
(cutil::defaggregate tpm-changeauth-validate
  ((new-auth-secret tpm-secret-p "This SHALL be the new AuthData data for the target entity"
     :default (make-tpm-secret))
   (n1 tpm-nonce-p "This SHOULD be a nonce, to enable the caller to verify that the target TPM is on-line."
     :default (make-tpm-nonce))
  )
  :parents(tpm-structures))

;; 7.5 TPM_STCLEAR_DATA()
(cutil::defaggregate tpm-stclear-data
  ((tag tpm-structure-tag-p "TPM_TAG_STCLEAR_DATA"
     :default (make-tpm-structure-tag))
   (context-nonce-key tpm-nonce-p "This is the nonce in use to properly identify saved key context blobs This SHALL be set to all zeros on each TPM_Startup (ST_Clear)."
     :default (make-tpm-nonce))
   (count-id tpm-count-id-p "This is the handle for the current monotonic counter. This SHALL be set to zero on each TPM_Startup(ST_Clear)."
     :default (make-tpm-count-id))
   (owner-reference uint32-p "Points to where to obtain the owner secret in OIAP and OSAP commands. This allows a TSS to manage 1.1 applications on a 1.2 TPM where delegation is in operation. Default value is TPM_KH_OWNER. ..."
     :default (make-uint32))
   (disable-reset-lock booleanp "Disables TPM_ResetLockValue upon authorization failure. The value remains TRUE for the timeout period. Default is FALSE. The value is in the STCLEAR_DATA structure as the implementation of this flag i ..."
     :default nil)
   (pcr tpm-pcrvalue-list-p "Platform configuration registers"
     :default (make-tpm-pcrvalue-list))
   (deferred-physical-presence uint32-p "The value can save the assertion of physicalPresence. Individual bits indicate to its ordinal that physicalPresence was previously asserted when the software state is such that it can no longer be ass ..."
     :default (make-uint32))
  )
  :parents(tpm-structures))

;; 8.2 TPM_PCR_COMPOSITE()
(cutil::defaggregate tpm-pcr-composite
  ((select tpm-pcr-selection-p "This SHALL be the indication of which PCR values are active"
     :default (make-tpm-pcr-selection))
   (value-size uint32-p "This SHALL be the size of the pcrValue field (not the number of PCR's)"
     :default (make-uint32))
   (pcr-value tpm-pcrvalue-list-p "This SHALL be an array of TPM_PCRVALUE structures. The values come in the order specified by the select parameter and are concatenated into a single blob"
     :default (make-tpm-pcrvalue-list))
  )
  :parents(tpm-structures))

;; 8.3 TPM_PCR_INFO()
(cutil::defaggregate tpm-pcr-info
  ((pcr-selection tpm-pcr-selection-p "This SHALL be the selection of PCRs to which the data or key is bound."
     :default (make-tpm-pcr-selection))
   (digest-at-release tpm-composite-hash-p "This SHALL be the digest of the PCR indices and PCR values to verify when revealing Sealed Data or using a key that was wrapped to PCRs."
     :default (make-tpm-composite-hash))
   (digest-at-creation tpm-composite-hash-p "This SHALL be the composite digest value of the PCR values, at the time when the sealing is performed."
     :default (make-tpm-composite-hash))
  )
  :parents(tpm-structures))

;; 8.4 TPM_PCR_INFO_LONG()
(cutil::defaggregate tpm-pcr-info-long
  ((tag tpm-structure-tag-p "This SHALL be TPM_TAG_PCR_INFO_LONG"
     :default (make-tpm-structure-tag))
   (locality-at-creation tpm-locality-selection-p "This SHALL be the locality modifier when the blob is created"
     :default (make-tpm-locality-selection))
   (locality-at-release tpm-locality-selection-p "This SHALL be the locality modifier required to reveal Sealed Data or use a key that was wrapped to PCRs This value MUST not be zero (0)."
     :default (make-tpm-locality-selection))
   (creation-pcr-selection tpm-pcr-selection-p "This SHALL be the selection of PCRs active when the blob is created"
     :default (make-tpm-pcr-selection))
   (release-pcr-selection tpm-pcr-selection-p "This SHALL be the selection of PCRs to which the data or key is bound."
     :default (make-tpm-pcr-selection))
   (digest-at-creation tpm-composite-hash-p "This SHALL be the composite digest value of the PCR values, when the blob is created"
     :default (make-tpm-composite-hash))
   (digest-at-release tpm-composite-hash-p "This SHALL be the digest of the PCR indices and PCR values to verify when revealing Sealed Data or using a key that was wrapped to PCRs."
     :default (make-tpm-composite-hash))
  )
  :parents(tpm-structures))

;; 8.5 TPM_PCR_INFO_SHORT()
(cutil::defaggregate tpm-pcr-info-short
  ((pcr-selection tpm-pcr-selection-p "This SHALL be the selection of PCRs that specifies the digestAtRelease"
     :default (make-tpm-pcr-selection))
   (locality-at-release tpm-locality-selection-p "This SHALL be the locality modifier required to release the information. This value must not be zero (0)."
     :default (make-tpm-locality-selection))
   (digest-at-release tpm-composite-hash-p "This SHALL be the digest of the PCR indices and PCR values to verify when revealing auth data"
     :default (make-tpm-composite-hash))
  )
  :parents(tpm-structures))

;; 9.3 TPM_SEALED_DATA()
(cutil::defaggregate tpm-sealed-data
  ((payload tpm-payload-type-p "This SHALL indicate the payload type of TPM_PT_SEAL"
     :default (make-tpm-payload-type))
   (auth-data tpm-secret-p "This SHALL be the AuthData data for this value"
     :default (make-tpm-secret))
   (tpm-proof tpm-secret-p "This SHALL be a copy of TPM_PERMANENT_DATA -> tpmProof"
     :default (make-tpm-secret))
   (stored-digest tpm-digest-p "This SHALL be a digest of the TPM_STORED_DATA structure, excluding the fields TPM_STORED_DATA -> encDataSize and TPM_STORED_DATA -> encData."
     :default (make-tpm-digest))
   (data-size uint32-p "This SHALL be the size of the data parameter"
     :default (make-uint32))
   (data byte-list-p "This SHALL be the data to be sealed"
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 10.2 TPM_KEY()
(cutil::defaggregate tpm-key
  ((ver tpm-struct-ver-p "This MUST be 1.1.0.0"
     :default (make-tpm-struct-ver))
   (key-usage tpm-key-usage-p "This SHALL be the TPM key usage that determines the operations permitted with this key"
     :default (make-tpm-key-usage))
   (key-flags tpm-key-flags-p "This SHALL be the indication of migration, redirection etc."
     :default (make-tpm-key-flags))
   (auth-data-usage tpm-auth-data-usage-p "This SHALL Indicate the conditions where it is required that authorization be presented."
     :default (make-tpm-auth-data-usage))
   (algorithm-parms tpm-key-parms-p "This SHALL be the information regarding the algorithm for this key"
     :default (make-tpm-key-parms))
   (pcr-info-size uint32-p "This SHALL be the length of the pcrInfo parameter. If the key is not bound to a PCR this value SHOULD be 0."
     :default (make-uint32))
   (pcr-info byte-list-p "This SHALL be a structure of type TPM_PCR_INFO, or an empty array if the key is not bound to PCRs."
     :default (make-byte-list))
   (pub-key tpm-store-pubkey-p "This SHALL be the public portion of the key"
     :default (make-tpm-store-pubkey))
   (enc-data-size uint32-p "This SHALL be the size of the encData parameter."
     :default (make-uint32))
   (enc-data byte-list-p "This SHALL be an encrypted TPM_STORE_ASYMKEY structure or TPM_MIGRATE_ASYMKEY structure"
     :default (make-byte-list))
  )
  :parents(tpm-structures))

(cutil::deflist tpm-key-list-p (x)
  (tpm-key-p x)
  :elementp-of-nil nil
  :true-listp t
  :parents(tpm-structures))

(defnd make-tpm-key-list ()
  nil)

;; 10.3 TPM_KEY12()
(cutil::defaggregate tpm-key12
  ((tag tpm-structure-tag-p "MUST be TPM_TAG_KEY12"
     :default (make-tpm-structure-tag))
   (tpm-fill uint16-p "MUST be 0x0000"
     :default (make-uint16))
   (key-usage tpm-key-usage-p "This SHALL be the TPM key usage that determines the operations permitted with this key"
     :default (make-tpm-key-usage))
   (key-flags tpm-key-flags-p "This SHALL be the indication of migration, redirection etc."
     :default (make-tpm-key-flags))
   (auth-data-usage tpm-auth-data-usage-p "This SHALL Indicate the conditions where it is required that authorization be presented."
     :default (make-tpm-auth-data-usage))
   (algorithm-parms tpm-key-parms-p "This SHALL be the information regarding the algorithm for this key"
     :default (make-tpm-key-parms))
   (pcr-info-size uint32-p "This SHALL be the length of the pcrInfo parameter. If the key is not bound to a PCR this value SHOULD be 0."
     :default (make-uint32))
   (pcr-info byte-list-p "This SHALL be a structure of type TPM_PCR_INFO_LONG,"
     :default (make-byte-list))
   (pub-key tpm-store-pubkey-p "This SHALL be the public portion of the key"
     :default (make-tpm-store-pubkey))
   (enc-data-size uint32-p "This SHALL be the size of the encData parameter."
     :default (make-uint32))
   (enc-data byte-list-p "This SHALL be an encrypted TPM_STORE_ASYMKEY structure TPM_MIGRATE_ASYMKEY structure"
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 10.5 TPM_PUBKEY()
(cutil::defaggregate tpm-pubkey
  ((algorithm-parms tpm-key-parms-p "This SHALL be the information regarding this key"
     :default (make-tpm-key-parms))
   (pub-key tpm-store-pubkey-p "This SHALL be the public key information"
     :default (make-tpm-store-pubkey))
  )
  :parents(tpm-structures))

;; 10.6 TPM_STORE_ASYMKEY()
(cutil::defaggregate tpm-store-asymkey
  ((payload tpm-payload-type-p "This SHALL set to TPM_PT_ASYM to indicate an asymmetric key. If used in TPM_CMK_ConvertMigration the value SHALL be TPM_PT_MIGRATE_EXTERNAL If used in TPM_CMK_CreateKey the value SHALL be TPM_PT_MIGRA ..."
     :default (make-tpm-payload-type))
   (usage-auth tpm-secret-p "This SHALL be the AuthData data necessary to authorize the use of this value"
     :default (make-tpm-secret))
   (migration-auth tpm-secret-p "This SHALL be the migration AuthData data for a migratable key, or the TPM secret value tpmProof for a non-migratable key created by the TPM. If the TPM sets this parameter to the value tpmProof, then ..."
     :default (make-tpm-secret))
   (pub-data-digest tpm-digest-p "This SHALL be the digest of the corresponding TPM_KEY structure, excluding the fields TPM_KEY.encSize and TPM_KEY.encData. When TPM_KEY -> pcrInfoSize is 0 then the digest calculation has no input fro ..."
     :default (make-tpm-digest))
   (priv-key tpm-store-privkey-p "This SHALL be the private key data. The privKey can be a variable length which allows for differences in the key format. The maximum size of the area would be 151 bytes. ..."
     :default (make-tpm-store-privkey))
  )
  :parents(tpm-structures))

;; 10.8 TPM_MIGRATE_ASYMKEY()
(cutil::defaggregate tpm-migrate-asymkey
  ((payload tpm-payload-type-p "This SHALL set to TPM_PT_MIGRATE or TPM_PT_CMK_MIGRATE to indicate an migrating asymmetric key or TPM_PT_MAINT to indicate a maintenance key."
     :default (make-tpm-payload-type))
   (usage-auth tpm-secret-p "This SHALL be a copy of the usageAuth from the TPM_STORE_ASYMKEY structure."
     :default (make-tpm-secret))
   (pub-data-digest tpm-digest-p "This SHALL be a copy of the pubDataDigest from the TPM_STORE_ASYMKEY structure."
     :default (make-tpm-digest))
   (part-priv-key-len uint32-p "This SHALL be the size of the partPrivKey field"
     :default (make-uint32))
   (part-priv-key byte-list-p "This SHALL be the k2 area as described in TPM_CreateMigrationBlob"
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 11.1 TPM_CERTIFY_INFO()
(cutil::defaggregate tpm-certify-info
  ((version tpm-struct-ver-p "This MUST be 1.1.0.0"
     :default (make-tpm-struct-ver))
   (key-usage tpm-key-usage-p "This SHALL be the same value that would be set in a TPM_KEY representation of the key to be certified. The upper byte MUST be zero."
     :default (make-tpm-key-usage))
   (key-flags tpm-key-flags-p "This SHALL be set to the same value as the corresponding parameter in the TPM_KEY structure that describes the public key that is being certified. The upper byte MUST be zero. ..."
     :default (make-tpm-key-flags))
   (auth-data-usage tpm-auth-data-usage-p "This SHALL be the same value that would be set in a TPM_KEY representation of the key to be certified"
     :default (make-tpm-auth-data-usage))
   (algorithm-parms tpm-key-parms-p "This SHALL be the same value that would be set in a TPM_KEY representation of the key to be certified"
     :default (make-tpm-key-parms))
   (pub-key-digest tpm-digest-p "This SHALL be a digest of the value TPM_KEY -> pubKey -> key in a TPM_KEY representation of the key to be certified"
     :default (make-tpm-digest))
   (data tpm-nonce-p "This SHALL be externally provided data."
     :default (make-tpm-nonce))
   (parent-pcr-status booleanp "This SHALL indicate if any parent key was wrapped to a PCR"
     :default nil)
   (pcr-info-size uint32-p "This SHALL be the size of the pcrInfo parameter. A value of zero indicates that the key is not wrapped to a PCR"
     :default (make-uint32))
   (pcr-info byte-list-p "This SHALL be the TPM_PCR_INFO structure."
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 11.2 TPM_CERTIFY_INFO2()
(cutil::defaggregate tpm-certify-info2
  ((tag tpm-structure-tag-p "MUST be TPM_TAG_CERTIFY_INFO2"
     :default (make-tpm-structure-tag))
   (tpm-fill byte-p "MUST be 0x00"
     :default (make-byte))
   (payload-type tpm-payload-type-p "This SHALL be the same value that would be set in a TPM_KEY representation of the key to be certified"
     :default (make-tpm-payload-type))
   (key-usage tpm-key-usage-p "This SHALL be the same value that would be set in a TPM_KEY representation of the key to be certified. The upper byte MUST be zero."
     :default (make-tpm-key-usage))
   (key-flags tpm-key-flags-p "This SHALL be set to the same value as the corresponding parameter in the TPM_KEY structure that describes the public key that is being certified. The upper byte MUST be zero. ..."
     :default (make-tpm-key-flags))
   (auth-data-usage tpm-auth-data-usage-p "This SHALL be the same value that would be set in a TPM_KEY representation of the key to be certified"
     :default (make-tpm-auth-data-usage))
   (algorithm-parms tpm-key-parms-p "This SHALL be the same value that would be set in a TPM_KEY representation of the key to be certified"
     :default (make-tpm-key-parms))
   (pub-key-digest tpm-digest-p "This SHALL be a digest of the value TPM_KEY -> pubKey -> key in a TPM_KEY representation of the key to be certified"
     :default (make-tpm-digest))
   (data tpm-nonce-p "This SHALL be externally provided data."
     :default (make-tpm-nonce))
   (parent-pcr-status booleanp "This SHALL indicate if any parent key was wrapped to a PCR"
     :default nil)
   (pcr-info-size uint32-p "This SHALL be the size of the pcrInfo parameter."
     :default (make-uint32))
   (pcr-info byte-list-p "This SHALL be the TPM_PCR_INFO_SHORT structure."
     :default (make-byte-list))
   (migration-authority-size uint32-p "This SHALL be the size of migrationAuthority"
     :default (make-uint32))
   (migration-authority byte-list-p "If the key to be certified has [payload == TPM_PT_MIGRATE_RESTRICTED or payload == TPM_PT_MIGRATE_EXTERNAL], migrationAuthority is the digest of the TPM_MSA_COMPOSITE and has TYPE == TPM_DIGEST. Other ..."
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 11.3 TPM_QUOTE_INFO()
(cutil::defaggregate tpm-quote-info
  ((version tpm-struct-ver-p "This MUST be 1.1.0.0"
     :default (make-tpm-struct-ver))
   (fixed 4-byte-list-p "This SHALL always be the string 'QUOT'"
     :default (make-4-byte-list))
   (digest-value tpm-composite-hash-p "This SHALL be the result of the composite hash algorithm using the current values of the requested PCR indices."
     :default (make-tpm-composite-hash))
   (external-data tpm-nonce-p "160 bits of externally supplied data"
     :default (make-tpm-nonce))
  )
  :parents(tpm-structures))

;; 12.3 TPM_EK_BLOB_AUTH()
(cutil::defaggregate tpm-ek-blob-auth
  ((tag tpm-structure-tag-p "TPM_TAG_EK_BLOB_AUTH"
     :default (make-tpm-structure-tag))
   (auth-value tpm-secret-p "This SHALL be the AuthData value"
     :default (make-tpm-secret))
  )
  :parents(tpm-structures))

;; 12.6 TPM_IDENTITY_REQ()
(cutil::defaggregate tpm-identity-req
  ((asym-size uint32-p "This SHALL be the size of the asymmetric encrypted area created by TSS_CollateIdentityRequest"
     :default (make-uint32))
   (sym-size uint32-p "This SHALL be the size of the symmetric encrypted area created by TSS_CollateIdentityRequest"
     :default (make-uint32))
   (asym-algorithm tpm-key-parms-p "This SHALL be the parameters for the asymmetric algorithm used to create the asymBlob"
     :default (make-tpm-key-parms))
   (sym-algorithm tpm-key-parms-p "This SHALL be the parameters for the symmetric algorithm used to create the symBlob"
     :default (make-tpm-key-parms))
   (asym-blob byte-list-p "This SHALL be the asymmetric encrypted area from TSS_CollateIdentityRequest"
     :default (make-byte-list))
   (sym-blob byte-list-p "This SHALL be the symmetric encrypted area from TSS_CollateIdentityRequest"
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 12.8 TPM_ASYM_CA_CONTENTS()
(cutil::defaggregate tpm-asym-ca-contents
  ((session-key tpm-symmetric-key-p "This SHALL be the session key used by the CA to encrypt the TPM_IDENTITY_CREDENTIAL"
     :default (make-tpm-symmetric-key))
   (id-digest tpm-digest-p "This SHALL be the digest of the TPM_PUBKEY of the key that is being certified by the CA"
     :default (make-tpm-digest))
  )
  :parents(tpm-structures))

;; 12.9 TPM_SYM_CA_ATTESTATION()
(cutil::defaggregate tpm-sym-ca-attestation
  ((cred-size uint32-p "This SHALL be the size of the credential parameter"
     :default (make-uint32))
   (algorithm tpm-key-parms-p "This SHALL be the indicator and parameters for the symmetric algorithm"
     :default (make-tpm-key-parms))
   (credential byte-list-p "This is the result of encrypting TPM_IDENTITY_CREDENTIAL using the session_key and the algorithm indicated 'algorithm'"
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 13.2 TPM_TRANSPORT_INTERNAL()
(cutil::defaggregate tpm-transport-internal
  ((tag tpm-structure-tag-p "TPM_TAG_TRANSPORT_INTERNAL"
     :default (make-tpm-structure-tag))
   (auth-data tpm-authdata-p "The shared secret for this session"
     :default (make-tpm-authdata))
   (trans-public tpm-transport-public-p "The public information of this session"
     :default (make-tpm-transport-public))
   (trans-handle tpm-transhandle-p "The handle for this session"
     :default (make-tpm-transhandle))
   (trans-nonce-even tpm-nonce-p "The even nonce for the rolling protocol"
     :default (make-tpm-nonce))
   (trans-digest tpm-digest-p "The log of transport events"
     :default (make-tpm-digest))
  )
  :parents(tpm-structures))

;; 13.4 TPM_TRANSPORT_LOG_OUT()
(cutil::defaggregate tpm-transport-log-out
  ((tag tpm-structure-tag-p "TPM_TAG_TRANSPORT_LOG_OUT"
     :default (make-tpm-structure-tag))
   (current-ticks tpm-current-ticks-p "The current tick count. This SHALL be the value of the current TPM tick counter."
     :default (make-tpm-current-ticks))
   (parameters tpm-digest-p "The actual parameters contained in the digest are subject to the rules of the command using this structure. To find the exact calculation refer to the actions in the command using this structure. ..."
     :default (make-tpm-digest))
   (locality tpm-modifier-indicator-p "The locality that called TPM_ExecuteTransport"
     :default (make-tpm-modifier-indicator))
  )
  :parents(tpm-structures))

;; 14.1 TPM_AUDIT_EVENT_IN()
(cutil::defaggregate tpm-audit-event-in
  ((tag tpm-structure-tag-p "TPM_TAG_AUDIT_EVENT_IN"
     :default (make-tpm-structure-tag))
   (input-parms tpm-digest-p "Digest value according to the HMAC digest rules of the 'above the line' parameters (i.e. the first HMAC digest calculation). When there are no HMAC rules, the input digest includes all parameters incl ..."
     :default (make-tpm-digest))
   (audit-count tpm-counter-value-p "The current value of the audit monotonic counter"
     :default (make-tpm-counter-value))
  )
  :parents(tpm-structures))

;; 14.2 TPM_AUDIT_EVENT_OUT()
(cutil::defaggregate tpm-audit-event-out
  ((tag tpm-structure-tag-p "TPM_TAG_AUDIT_EVENT_OUT"
     :default (make-tpm-structure-tag))
   (output-parms tpm-digest-p "Digest value according to the HMAC digest rules of the 'above the line' parameters (i.e. the first HMAC digest calculation). When there are no HMAC rules, the output digest includes the return code, t ..."
     :default (make-tpm-digest))
   (audit-count tpm-counter-value-p "The current value of the audit monotonic counter"
     :default (make-tpm-counter-value))
  )
  :parents(tpm-structures))

;; 19.4 TPM_NV_DATA_SENSITIVE()
(cutil::defaggregate tpm-nv-data-sensitive
  ((tag tpm-structure-tag-p "This SHALL be TPM_TAG_NV_DATA_SENSITIVE"
     :default (make-tpm-structure-tag))
   (pub-info tpm-nv-data-public-p "The public information regarding this area"
     :default (make-tpm-nv-data-public))
   (auth-value tpm-authdata-p "The AuthData value to manipulate the value"
     :default (make-tpm-authdata))
   (data byte-list-p "The data area. This MUST not contain any sensitive information as the TPM does not provide any confidentiality on the data."
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 20.6 TPM_FAMILY_TABLE()
(cutil::defaggregate tpm-family-table
  ((fam-table-row tpm-family-table-entry-p "The array of family table entries"
     :default (make-tpm-family-table-entry))
  )
  :parents(tpm-structures))

;; 20.11 TPM_DELEGATE_SENSITIVE()
(cutil::defaggregate tpm-delegate-sensitive
  ((tag tpm-structure-tag-p "This MUST be TPM_TAG_DELEGATE_SENSITIVE"
     :default (make-tpm-structure-tag))
   (auth-value tpm-secret-p "AuthData value"
     :default (make-tpm-secret))
  )
  :parents(tpm-structures))

;; 21.6 TPM_CAP_VERSION_INFO()
(cutil::defaggregate tpm-cap-version-info
  ((tag tpm-structure-tag-p "MUST be TPM_TAG_CAP_VERSION_INFO"
     :default (make-tpm-structure-tag))
   (version tpm-version-p "The version and revision"
     :default (make-tpm-version))
   (spec-level uint16-p "A number indicating the level of ordinals supported"
     :default (make-uint16))
   (errata-rev byte-p "A number indicating the errata version of the specification"
     :default (make-byte))
   (tpm-vendor-id 4-byte-list-p "The vendor ID unique to each TPM manufacturer."
     :default (make-4-byte-list))
   (vendor-specific-size uint16-p "The size of the vendor specific area"
     :default (make-uint16))
   (vendor-specific byte-list-p "Vendor specific information"
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 21.7 TPM_DA_INFO()
(cutil::defaggregate tpm-da-info
  ((tag tpm-structure-tag-p "MUST be TPM_TAG_DA_INFO"
     :default (make-tpm-structure-tag))
   (tpm-state tpm-da-state-p "Dynamic. The actual state of the dictionary attack mitigation logic. See 21.9."
     :default (make-tpm-da-state))
   (current-count uint16-p "Dynamic. The actual count of the authorization failure counter for the selected entity type"
     :default (make-uint16))
   (threshold-count uint16-p "Static. Dictionary attack mitigation threshold count for the selected entity type"
     :default (make-uint16))
   (action-at-threshold tpm-da-action-type-p "Static Action of the TPM when currentCount passes thresholdCount. See 21.10."
     :default (make-tpm-da-action-type))
   (action-depend-value uint32-p "Dynamic. Action being taken when the dictionary attack mitigation logic is active. E.g., when actionAtThreshold is TPM_DA_ACTION_TIMEOUT, this is the lockout time remaining in seconds. ..."
     :default (make-uint32))
   (vendor-data-size uint32-p "Size of vendor specific data field"
     :default (make-uint32))
   (vendor-data byte-list-p "Vendor specific data field"
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 21.8 TPM_DA_INFO_LIMITED()
(cutil::defaggregate tpm-da-info-limited
  ((tag tpm-structure-tag-p "MUST be TPM_TAG_DA_INFO_LIMITED"
     :default (make-tpm-structure-tag))
   (tpm-state tpm-da-state-p "Dynamic. The actual state of the dictionary attack mitigation logic. See 21.9."
     :default (make-tpm-da-state))
   (current-count uint16-p "Dynamic. The actual count of the authorization failure counter for the selected entity type"
     :default (make-uint16))
   (threshold-count uint16-p "Static. Dictionary attack mitigation threshold count for the selected entity type"
     :default (make-uint16))
   (action-at-threshold tpm-da-action-type-p "Static Action of the TPM when currentCount passes thresholdCount. See 21.10."
     :default (make-tpm-da-action-type))
   (action-depend-value uint32-p "Dynamic. Action being taken when the dictionary attack mitigation logic is active. E.g., when actionAtThreshold is TPM_DA_ACTION_TIMEOUT, this is the lockout time remaining in seconds. ..."
     :default (make-uint32))
   (vendor-data-size uint32-p "Size of vendor specific data field"
     :default (make-uint32))
   (vendor-data byte-list-p "Vendor specific data field"
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 22.5 TPM_DAA_CONTEXT()
(cutil::defaggregate tpm-daa-context
  ((tag tpm-structure-tag-p "MUST be TPM_TAG_DAA_CONTEXT"
     :default (make-tpm-structure-tag))
   (daa-digestcontext tpm-digest-p "A digest of parameters used to generate this structure. The parameters vary, depending on whether the session is a JOIN session or a SIGN session."
     :default (make-tpm-digest))
   (daa-digest tpm-digest-p "A running digest of certain parameters generated during DAA computation; operationally the same as a PCR (which holds a running digest of integrity metrics)."
     :default (make-tpm-digest))
   (daa-contextseed tpm-daa-context-seed-p "The seed used to generate other DAA session parameters"
     :default (make-tpm-daa-context-seed))
   (daa-scratch 256-byte-list-p "Memory used to hold different parameters at different times of DAA computation, but only one parameter at a time. The maximum size of this field is 256 bytes"
     :default (make-256-byte-list))
   (daa-stage byte-p "A counter, indicating the stage of DAA computation that was most recently completed. The value of the counter is zero if the TPM currently contains no DAA context. When set to zero (0) the TPM MUST cl ..."
     :default (make-byte))
  )
  :parents(tpm-structures))

; ===============================================================
; Level 3 Records
; ===============================================================

;;  TPMX_INTERNAL_SAVE_DATA()
(cutil::defaggregate tpmx-internal-save-data
  ((pcr tpm-pcrvalue-list-p "Unresetable PCRs"
     :default (make-tpm-pcrvalue-list))
   (audit-digest tpm-digest-p "Audit digest (optional)"
     :default (make-tpm-digest))
   (stclear-data tpm-stclear-data-p "Most of the data in this structure resets on TPM_Startup(ST_CLEAR)."
     :default (make-tpm-stclear-data))
   (stclear-flags tpm-stclear-flags-p "These flags maintain state that is reset on each TPM_Startup(ST_CLEAR) command. The values are not affected by TPM_Startup(ST_STATE) commands."
     :default (make-tpm-stclear-flags))
   (loaded-keys tpm-key-list-p "Loaded key where parentPCRstatus == true (mandatory); other loaded keys (optional)"
     :default (make-tpm-key-list))
   (owner-evict-keys tpm-key-list-p "Any key where TPM_KEY_CONTROL_EVICT == true."
     :default (make-tpm-key-list))
   (sessions tpm-session-data-list-p "Any session (optional)"
     :default (make-tpm-session-data-list))
  )
  :parents(tpm-structures))

;; 5.12 TPM_MIGRATIONKEYAUTH()
(cutil::defaggregate tpm-migrationkeyauth
  ((migration-key tpm-pubkey-p "This SHALL be the public key of the migration facility"
     :default (make-tpm-pubkey))
   (migration-scheme tpm-migrate-scheme-p "This shall be the type of migration operation."
     :default (make-tpm-migrate-scheme))
   (digest tpm-digest-p "This SHALL be the digest value of the concatenation of migration key, migration scheme and tpmProof"
     :default (make-tpm-digest))
  )
  :parents(tpm-structures))

;; 11.4 TPM_QUOTE_INFO2()
(cutil::defaggregate tpm-quote-info2
  ((tag tpm-structure-tag-p "This SHALL be TPM_TAG_QUOTE_INFO2"
     :default (make-tpm-structure-tag))
   (fixed 4-byte-list-p "This SHALL always be the string 'QUT2'"
     :default (make-4-byte-list))
   (external-data tpm-nonce-p "160 bits of externally supplied data"
     :default (make-tpm-nonce))
   (info-short tpm-pcr-info-short-p "the quoted PCR registers"
     :default (make-tpm-pcr-info-short))
  )
  :parents(tpm-structures))

;; 12.2 TPM_EK_BLOB_ACTIVATE()
(cutil::defaggregate tpm-ek-blob-activate
  ((tag tpm-structure-tag-p "TPM_TAG_EK_BLOB_ACTIVATE"
     :default (make-tpm-structure-tag))
   (session-key tpm-symmetric-key-p "This SHALL be the session key used by the CA to encrypt the TPM_IDENTITY_CREDENTIAL"
     :default (make-tpm-symmetric-key))
   (id-digest tpm-digest-p "This SHALL be the digest of the TPM_PUBKEY that is being certified by the CA"
     :default (make-tpm-digest))
   (pcr-info tpm-pcr-info-short-p "This SHALL indicate the PCR's and localities"
     :default (make-tpm-pcr-info-short))
  )
  :parents(tpm-structures))

;; 12.5 TPM_IDENTITY_CONTENTS()
(cutil::defaggregate tpm-identity-contents
  ((ver tpm-struct-ver-p "This MUST be 1.1.0.0. This is the version information for this structure and not the underlying key."
     :default (make-tpm-struct-ver))
   (ordinal uint32-p "This SHALL be the ordinal of the TPM_MakeIdentity command."
     :default (make-uint32))
   (label-priv-ca-digest tpm-chosenid-hash-p "This SHALL be the result of hashing the chosen identityLabel and privacyCA for the new TPM identity"
     :default (make-tpm-chosenid-hash))
   (identity-pub-key tpm-pubkey-p "This SHALL be the public key structure of the identity key"
     :default (make-tpm-pubkey))
  )
  :parents(tpm-structures))

;; 12.7 TPM_IDENTITY_PROOF()
(cutil::defaggregate tpm-identity-proof
  ((ver tpm-struct-ver-p "This MUST be 1.1.0.0"
     :default (make-tpm-struct-ver))
   (label-size uint32-p "This SHALL be the size of the label area"
     :default (make-uint32))
   (identity-binding-size uint32-p "This SHALL be the size of the identitybinding area"
     :default (make-uint32))
   (endorsement-size uint32-p "This SHALL be the size of the endorsement credential"
     :default (make-uint32))
   (platform-size uint32-p "This SHALL be the size of the platform credential"
     :default (make-uint32))
   (conformance-size uint32-p "This SHALL be the size of the conformance credential"
     :default (make-uint32))
   (identity-key tpm-pubkey-p "This SHALL be the public key of the new identity"
     :default (make-tpm-pubkey))
   (label-area byte-list-p "This SHALL be the text label for the new identity"
     :default (make-byte-list))
   (identity-binding byte-list-p "This SHALL be the signature value of TPM_IDENTITY_CONTENTS structure from the TPM_MakeIdentity command"
     :default (make-byte-list))
   (endorsement-credential byte-list-p "This SHALL be the TPM endorsement credential"
     :default (make-byte-list))
   (platform-credential byte-list-p "This SHALL be the TPM platform credential"
     :default (make-byte-list))
   (conformance-credential byte-list-p "This SHALL be the TPM conformance credential"
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 20.8 TPM_DELEGATE_PUBLIC()
(cutil::defaggregate tpm-delegate-public
  ((tag tpm-structure-tag-p "This SHALL be TPM_TAG_DELEGATE_PUBLIC"
     :default (make-tpm-structure-tag))
   (rowlabel tpm-delegate-label-p "This SHALL be the label for the row. It MUST not contain any sensitive information."
     :default (make-tpm-delegate-label))
   (pcr-info tpm-pcr-info-short-p "This SHALL be the designation of the process that can use the permission. This is a not sensitive value. PCR_SELECTION may be NULL. If selected the pcrInfo MUST be checked on each use of the delegatio ..."
     :default (make-tpm-pcr-info-short))
   (permissions tpm-delegations-p "This SHALL be the permissions that are allowed to the indicated process. This is not a sensitive value."
     :default (make-tpm-delegations))
   (family-id tpm-family-id-p "This SHALL be the family ID that identifies which family the row belongs to. This is not a sensitive value."
     :default (make-tpm-family-id))
   (verification-count tpm-family-verification-p "A copy of verificationCount from the associated family table. This is not a sensitive value."
     :default (make-tpm-family-verification))
  )
  :parents(tpm-structures))

;; 22.7 TPM_STANY_DATA()
(cutil::defaggregate tpm-stany-data
  ((daa-issuersettings tpm-daa-issuer-p "A set of DAA issuer parameters controlling a DAA session."
     :default (make-tpm-daa-issuer))
   (daa-tpmspecific tpm-daa-tpm-p "A set of DAA parameters associated with a specific TPM."
     :default (make-tpm-daa-tpm))
   (daa-session tpm-daa-context-p "A set of DAA parameters associated with a DAA session."
     :default (make-tpm-daa-context))
   (daa-joinsession tpm-daa-joindata-p "A set of DAA parameters used only during the JOIN phase of a DAA session, and generated by the TPM."
     :default (make-tpm-daa-joindata))
  )
  :parents(tpm-structures))

; ===============================================================
; Level 4 Records
; ===============================================================

;; 20.9 TPM_DELEGATE_TABLE_ROW()
(cutil::defaggregate tpm-delegate-table-row
  ((tag tpm-structure-tag-p "This SHALL be TPM_TAG_DELEGATE_TABLE_ROW"
     :default (make-tpm-structure-tag))
   (pub tpm-delegate-public-p "This SHALL be the public information for a table row."
     :default (make-tpm-delegate-public))
   (auth-value tpm-secret-p "This SHALL be the AuthData value that can use the permissions. This is a sensitive value."
     :default (make-tpm-secret))
  )
  :parents(tpm-structures))

;; 20.12 TPM_DELEGATE_OWNER_BLOB()
(cutil::defaggregate tpm-delegate-owner-blob
  ((tag tpm-structure-tag-p "This MUST be TPM_TAG_DELEGATE_OWNER_BLOB"
     :default (make-tpm-structure-tag))
   (pub tpm-delegate-public-p "The public information for this blob"
     :default (make-tpm-delegate-public))
   (integrity-digest tpm-digest-p "The HMAC to guarantee the integrity of the entire structure"
     :default (make-tpm-digest))
   (additional-size uint32-p "The size of additionalArea"
     :default (make-uint32))
   (additional-area byte-list-p "An area that the TPM can add to the blob which MUST NOT contain any sensitive information. This would include any IV material for symmetric encryption"
     :default (make-byte-list))
   (sensitive-size uint32-p "The size of the sensitive area"
     :default (make-uint32))
   (sensitive-area byte-list-p "The area that contains the encrypted TPM_DELEGATE_SENSITIVE"
     :default (make-byte-list))
  )
  :parents(tpm-structures))

;; 20.13 TPM_DELEGATE_KEY_BLOB()
(cutil::defaggregate tpm-delegate-key-blob
  ((tag tpm-structure-tag-p "This MUST be TPM_TAG_DELG_KEY_BLOB"
     :default (make-tpm-structure-tag))
   (pub tpm-delegate-public-p "The public information for this blob"
     :default (make-tpm-delegate-public))
   (integrity-digest tpm-digest-p "The HMAC to guarantee the integrity of the entire structure"
     :default (make-tpm-digest))
   (pub-key-digest tpm-digest-p "The digest, that uniquely identifies the key for which this usage delegation applies. This is a hash of the TPM_STORE_PUBKEY structure."
     :default (make-tpm-digest))
   (additional-size uint32-p "The size of the integrity area"
     :default (make-uint32))
   (additional-area byte-list-p "An area that the TPM can add to the blob which MUST NOT contain any sensitive information. This would include any IV material for symmetric encryption"
     :default (make-byte-list))
   (sensitive-size uint32-p "The size of the sensitive area"
     :default (make-uint32))
   (sensitive-area byte-list-p "The area that contains the encrypted TPM_DELEGATE_SENSITIVE"
     :default (make-byte-list))
  )
  :parents(tpm-structures))

; ===============================================================
; Level 5 Records
; ===============================================================

;; 20.10 TPM_DELEGATE_TABLE()
(cutil::defaggregate tpm-delegate-table
  ((del-row tpm-delegate-table-row-p "The array of delegations"
     :default (make-tpm-delegate-table-row))
  )
  :parents(tpm-structures))

; ===============================================================
; Level 6 Records
; ===============================================================

;; 7.4 TPM_PERMANENT_DATA()
(cutil::defaggregate tpm-permanent-data
  ((tag tpm-structure-tag-p "TPM_TAG_PERMANENT_DATA"
     :default (make-tpm-structure-tag))
   (rev-major byte-p "This is the TPM major revision indicator. This SHALL be set by the TPME, only. The default value is manufacturer-specific."
     :default (make-byte))
   (rev-minor byte-p "This is the TPM minor revision indicator. This SHALL be set by the TPME, only. The default value is manufacturer-specific."
     :default (make-byte))
   (tpm-proof tpm-secret-p "This is a random number that each TPM maintains to validate blobs in the SEAL and other processes. The default value is manufacturer-specific."
     :default (make-tpm-secret))
   (owner-auth tpm-secret-p "This is the TPM-Owner's AuthData data. The default value is manufacturer-specific."
     :default (make-tpm-secret))
   (operator-auth tpm-secret-p "The value that allows the execution of the TPM_SetTempDeactivated command"
     :default (make-tpm-secret))
   (manu-maint-pub tpm-pubkey-p "This is the manufacturer's public key to use in the maintenance operations. The default value is manufacturer-specific."
     :default (make-tpm-pubkey))
   (endorsement-key tpm-key-p "This is the TPM's endorsement key pair."
     :default (make-tpm-key))
   (srk tpm-key-p "This is the TPM's StorageRootKey."
     :default (make-tpm-key))
   (delegate-key tpm-key-p "This key encrypts delegate rows that are stored outside the TPM. The key MAY be symmetric or asymmetric. The key size for the algorithm SHOULD be equivalent to 128-bit AES key. The TPM MAY set this va ..."
     :default (make-tpm-key))
   (context-key tpm-key-p "This is the key in use to perform context saves. The key may be symmetric or asymmetric. The key size is predicated by the algorithm in use. This value MUST be reset when the TPM Owner changes. This k ..."
     :default (make-tpm-key))
   (audit-monotonic-counter tpm-counter-value-p "This SHALL be the audit monotonic counter for the TPM. This value starts at 0 and increments according to the rules of auditing. The label SHALL be fixed at 4 bytes of 0x00. ..."
     :default (make-tpm-counter-value))
   (monotonic-counter tpm-counter-value-list-p "This SHALL be the monotonic counters for the TPM. The individual counters start and increment according to the rules of monotonic counters."
     :default (make-tpm-counter-value-list))
   (pcr-attrib tpm-pcr-attributes-list-p "The attributes for all of the PCR registers supported by the TPM."
     :default (make-tpm-pcr-attributes-list))
   (ordinal-audit-status byte-list-p "Table indicating which ordinals are being audited."
     :default (make-byte-list))
   (auth-dir tpm-dirvalue-list-p "The array of TPM Owner authorized DIR. Points to the same location as the NV index value."
     :default (make-tpm-dirvalue-list))
   (rng-state byte-list-p "State information describing the random number generator."
     :default (make-byte-list))
   (family-table tpm-family-table-p "The family table in use for delegations"
     :default (make-tpm-family-table))
   (delegate-table tpm-delegate-table-p "The delegate table"
     :default (make-tpm-delegate-table))
   (ek-reset tpm-nonce-p "Nonce held by TPM to validate TPM_RevokeTrust. This value is set as the next 20 bytes from the TPM RNG when the EK is set"
     :default (make-tpm-nonce))
   (last-family-id uint32-p "--"
     :default (make-uint32))
   (no-owner-nv-write uint32-p "--"
     :default (make-uint32))
   (restrict-delegate tpm-cmk-delegate-p "--"
     :default (make-tpm-cmk-delegate))
   (tpm-daa-seed tpm-daa-tpm-seed-p "--"
     :default (make-tpm-daa-tpm-seed))
   (daa-proof tpm-nonce-p "--"
     :default (make-tpm-nonce))
   (daa-blob-key tpm-key-p "--"
     :default (make-tpm-key))
  )
  :parents(tpm-structures))

; ===============================================================
; Level 7 Records
; ===============================================================

;;  TPMX_INTERNAL_DATA()
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
   (save-data tpmx-internal-save-data-p "Data saved from TPM_SaveState command."
     :default (make-tpmx-internal-save-data))
   (keys tpm-key-list-p "All TPM keys"
     :default (make-tpm-key-list))
   (loaded-keys tpm-key-list-p "Loaded keys."
     :default (make-tpm-key-list))
  )
  :parents(tpm-structures))
