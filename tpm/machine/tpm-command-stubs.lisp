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
(include-book "tpm-structures")

(program)

(set-ignore-ok t)

;; 3.1 TPM_Init
(cutil::define tpm-init
  ((tpm-data-in tpmx-internal-data-p "TPM data"))
  :returns ((tpm-data-out tpmx-internal-data-p "TPM data" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 3.2 TPM_Startup
(cutil::define tpm-startup
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (startup-type tpm-startup-type-p "Type of startup that is occurring"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 3.3 TPM_SaveState
(cutil::define tpm-save-state
  ((tpm-data tpmx-internal-data-p "Internal TPM data"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 4.1 TPM_SelfTestFull
(cutil::define tpm-self-test-full
  ((tpm-data tpmx-internal-data-p "Internal TPM data"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 4.2 TPM_ContinueSelfTest
(cutil::define tpm-continue-self-test
  ((tpm-data tpmx-internal-data-p "Internal TPM data"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 4.3 TPM_GetTestResult
(cutil::define tpm-get-test-result
  ((tpm-data tpmx-internal-data-p "Internal TPM data"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (out-data byte-list-p "The outData this is manufacturer specific" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 5.1 TPM_SetOwnerInstall
(cutil::define tpm-set-owner-install
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (tpm-state booleanp "State to which ownership flag is to be set."))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 5.2 TPM_OwnerSetDisable
(cutil::define tpm-owner-set-disable
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (disable-state booleanp "Value for disable state")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 5.3 TPM_PhysicalEnable
(cutil::define tpm-physical-enable
  ((tpm-data tpmx-internal-data-p "Internal TPM data"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 5.4 TPM_PhysicalDisable
(cutil::define tpm-physical-disable
  ((tpm-data tpmx-internal-data-p "Internal TPM data"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 5.5 TPM_PhysicalSetDeactivated
(cutil::define tpm-physical-set-deactivated
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (tpm-state booleanp "State to which deactivated flag is to be set."))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 5.6 TPM_SetTempDeactivated
(cutil::define tpm-set-temp-deactivated
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 5.7 TPM_SetOperatorAuth
(cutil::define tpm-set-operator-auth
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (operator-auth tpm-secret-p "The operator AuthData"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 6.1 TPM_TakeOwnership
(cutil::define tpm-take-ownership
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (protocol-id tpm-protocol-id-p "The ownership protocol in use.")
   (enc-owner-auth byte-list-p "The owner AuthData encrypted with PUBEK")
   (enc-srk-auth byte-list-p "The SRK AuthData encrypted with PUBEK")
   (srk-params tpm-key-p "Structure containing all parameters of new SRK. pubKey.keyLength and encSize are both 0. This structure MAY be TPM_KEY12.")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (srk-pub tpm-key-p "Structure containing all parameters of new SRK. srkPub.encData is set to 0. This structure MAY be TPM_KEY12." :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 6.2 TPM_OwnerClear
(cutil::define tpm-owner-clear
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 6.3 TPM_ForceClear
(cutil::define tpm-force-clear
  ((tpm-data tpmx-internal-data-p "Internal TPM data"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 6.4 TPM_DisableOwnerClear
(cutil::define tpm-disable-owner-clear
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 6.5 TPM_DisableForceClear
(cutil::define tpm-disable-force-clear
  ((tpm-data tpmx-internal-data-p "Internal TPM data"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 6.6 TPM_PhysicalPresence
(cutil::define tpm-physical-presence
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (physical-presence tpm-physical-presence-p "The state to set the TPM's Physical Presence flags."))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 6.7 TPM_ResetEstablishmentBit
(cutil::define tpm-reset-establishment-bit
  ((tpm-data tpmx-internal-data-p "Internal TPM data"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 7.1 TPM_GetCapability
(cutil::define tpm-get-capability
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (cap-area tpm-capability-area-p "Partition of capabilities to be interrogated")
   (sub-cap byte-list-p "Further definition of information"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (resp byte-list-p "The capability response" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 7.2 TPM_SetCapability
(cutil::define tpm-set-capability
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (cap-area tpm-capability-area-p "Partition of capabilities to be set")
   (sub-cap byte-list-p "Further definition of information")
   (set-value byte-list-p "The value to set")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 7.3 TPM_GetCapabilityOwner
(cutil::define tpm-get-capability-owner
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (version tpm-version-p "A properly filled out version structure." :hyp :fguard)
               (non-volatile-flags uint32-p "The current state of the non-volatile flags." :hyp :fguard)
               (volatile-flags uint32-p "The current state of the volatile flags." :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 8.3 TPM_GetAuditDigest
(cutil::define tpm-get-audit-digest
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (start-ordinal uint32-p "The starting ordinal for the list of audited ordinals"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (counter-value tpm-counter-value-p "The current value of the audit monotonic counter" :hyp :fguard)
               (audit-digest tpm-digest-p "Log of all audited events" :hyp :fguard)
               (more booleanp "TRUE if the output does not contain a full list of audited ordinals" :hyp :fguard)
               (ord-list uint32-list-p "List of ordinals that are audited." :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 8.4 TPM_GetAuditDigestSigned
(cutil::define tpm-get-audit-digest-signed
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (key-handle tpm-key-handle-p "The handle of a loaded key that can perform digital signatures.")
   (close-audit booleanp "Indication if audit session should be closed")
   (anti-replay tpm-nonce-p "A nonce to prevent replay attacks")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (counter-value tpm-counter-value-p "The value of the audit monotonic counter" :hyp :fguard)
               (audit-digest tpm-digest-p "Log of all audited events" :hyp :fguard)
               (ordinal-digest tpm-digest-p "Digest of all audited ordinals" :hyp :fguard)
               (sig byte-list-p "The signature of the area" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 8.5 TPM_SetOrdinalAuditStatus
(cutil::define tpm-set-ordinal-audit-status
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (ordinal-to-audit tpm-command-code-p "The ordinal whose audit flag is to be set")
   (audit-state booleanp "Value for audit flag")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 9.2 TPM_SetRedirection
(cutil::define tpm-set-redirection
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (key-handle tpm-key-handle-p "The keyHandle identifier of a loaded key that can implement redirection.")
   (redir-cmd tpm-redir-command-p "The command to execute")
   (input-data byte-p "Manufacturer parameter")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 9.3 TPM_ResetLockValue
(cutil::define tpm-reset-lock-value
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 10.1 TPM_Seal
(cutil::define tpm-seal
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (key-handle tpm-key-handle-p "Handle of a loaded key that can perform seal operations.")
   (enc-auth tpm-encauth-p "The encrypted AuthData for the sealed data.")
   (pcr-info tpm-pcr-info-p "The PCR selection information. The caller MAY use TPM_PCR_INFO_LONG.")
   (in-data byte-list-p "The data to be sealed to the platform and any specified PCRs")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (sealed-data tpm-stored-data-p "Encrypted, integrity-protected data object that is the result of the TPM_Seal operation." :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 10.2 TPM_Unseal
(cutil::define tpm-unseal
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (parent-handle tpm-key-handle-p "Handle of a loaded key that can unseal the data.")
   (in-data tpm-stored-data-p "The encrypted data generated by TPM_Seal.")
   (auth1 tpmx-auth-info-p "Auth Info object")
   (auth2 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (secret byte-list-p "Decrypted data that had been sealed" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard)
               (auth2 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 10.3 TPM_UnBind
(cutil::define tpm-un-bind
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (key-handle tpm-key-handle-p "The keyHandle identifier of a loaded key that can perform UnBind operations.")
   (in-data byte-list-p "Encrypted blob to be decrypted")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (out-data byte-list-p "The resulting decrypted data." :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 10.4 TPM_CreateWrapKey
(cutil::define tpm-create-wrap-key
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (parent-handle tpm-key-handle-p "Handle of a loaded key that can perform key wrapping.")
   (data-usage-auth tpm-encauth-p "Encrypted usage AuthData for the key.")
   (data-migration-auth tpm-encauth-p "Encrypted migration AuthData for the key.")
   (key-info tpm-key-p "Information about key to be created, pubkey.keyLength and keyInfo.encData elements are 0. MAY be TPM_KEY12")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (wrapped-key tpm-key-p "The TPM_KEY structure which includes the public and encrypted private key. MAY be TPM_KEY12" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 10.5 TPM_LoadKey2
(cutil::define tpm-load-key2
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (parent-handle tpm-key-handle-p "TPM handle of parent key.")
   (in-key tpm-key-p "Incoming key structure, both encrypted private and clear public portions. MAY be TPM_KEY12")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (inkey-handle tpm-key-handle-p "Internal TPM handle where decrypted key was loaded." :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 10.6 TPM_GetPubKey
(cutil::define tpm-get-pub-key
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (key-handle tpm-key-handle-p "TPM handle of key.")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (pub-key tpm-pubkey-p "Public portion of key in keyHandle." :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 10.7 TPM_Sealx
(cutil::define tpm-sealx
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (key-handle tpm-key-handle-p "Handle of a loaded key that can perform seal operations.")
   (enc-auth tpm-encauth-p "The encrypted AuthData for the sealed data.")
   (pcr-info tpm-pcr-info-p "MUST use TPM_PCR_INFO_LONG.")
   (in-data byte-list-p "The data to be sealed to the platform and any specified PCRs")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (sealed-data tpm-stored-data-p "Encrypted, integrity-protected data object that is the result of the TPM_Sealx operation." :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 11.1 TPM_CreateMigrationBlob
(cutil::define tpm-create-migration-blob
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (parent-handle tpm-key-handle-p "Handle of the parent key that can decrypt encData.")
   (migration-type tpm-migrate-scheme-p "The migration type, either MIGRATE or REWRAP")
   (migration-key-auth tpm-migrationkeyauth-p "Migration public key and its authorization session digest.")
   (enc-data byte-list-p "The encrypted entity that is to be modified.")
   (auth1 tpmx-auth-info-p "Auth Info object")
   (auth2 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (random byte-list-p "String used for xor encryption" :hyp :fguard)
               (out-data byte-list-p "The modified, encrypted entity." :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard)
               (auth2 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 11.2 TPM_ConvertMigrationBlob
(cutil::define tpm-convert-migration-blob
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (parent-handle tpm-key-handle-p "Handle of a loaded key that can decrypt keys.")
   (in-data byte-list-p "The XOR'd and encrypted key")
   (random byte-list-p "Random value used to hide key data.")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (out-data byte-list-p "The encrypted private key that can be loaded with TPM_LoadKey" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 11.3 TPM_AuthorizeMigrationKey
(cutil::define tpm-authorize-migration-key
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (migration-scheme tpm-migrate-scheme-p "Type of migration operation that is to be permitted for this key.")
   (migration-key tpm-pubkey-p "The public key to be authorized.")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (out-data tpm-migrationkeyauth-p "Returned public key and authorization session digest." :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 11.4 TPM_MigrateKey
(cutil::define tpm-migrate-key
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (ma-key-handle tpm-key-handle-p "Handle of the key to be used to migrate the key.")
   (pub-key tpm-pubkey-p "Public key to which the blob is to be migrated")
   (in-data byte-list-p "The input blob")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (out-data byte-list-p "The re-encrypted blob" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 11.5 TPM_CMK_SetRestrictions
(cutil::define tpm-cmk_-set-restrictions
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (restriction tpm-cmk-delegate-p "The bit mask of how to set the restrictions on CMK keys")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 11.6 TPM_CMK_ApproveMA
(cutil::define tpm-cmk_-approve-ma
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (migration-authority-digest tpm-digest-p "A digest of a TPM_MSA_COMPOSITE structure (itself one or more digests of public keys belonging to migration authorities)")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (out-data tpm-hmac-p "HMAC of migrationAuthorityDigest" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 11.7 TPM_CMK_CreateKey
(cutil::define tpm-cmk_-create-key
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (parent-handle tpm-key-handle-p "Handle of a loaded key that can perform key wrapping.")
   (data-usage-auth tpm-encauth-p "Encrypted usage AuthData for the key.")
   (key-info tpm-key12-p "Information about key to be created, pubkey.keyLength and keyInfo.encData elements are 0. MUST be TPM_KEY12")
   (migration-authority-approval tpm-hmac-p "A ticket, created by the TPM Owner using TPM_CMK_ApproveMA, approving a TPM_MSA_COMPOSITE structure")
   (migration-authority-digest tpm-digest-p "The digest of a TPM_MSA_COMPOSITE structure")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (wrapped-key tpm-key12-p "The TPM_KEY structure which includes the public and encrypted private key. MUST be TPM_KEY12" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 11.8 TPM_CMK_CreateTicket
(cutil::define tpm-cmk_-create-ticket
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (verification-key tpm-pubkey-p "The public key to be used to check signatureValue")
   (signed-data tpm-digest-p "The data to be verified")
   (signature-value byte-list-p "The signatureValue to be verified")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (sig-ticket tpm-hmac-p "Ticket that proves digest created on this TPM" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 11.9 TPM_CMK_CreateBlob
(cutil::define tpm-cmk_-create-blob
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (parent-handle tpm-key-handle-p "Handle of the parent key that can decrypt encData.")
   (migration-type tpm-migrate-scheme-p "The migration type, either TPM_MS_RESTRICT_MIGRATE or TPM_MS_RESTRICT_APPROVE")
   (migration-key-auth tpm-migrationkeyauth-p "Migration public key and its authorization session digest.")
   (pub-source-key-digest tpm-digest-p "The digest of the TPM_PUBKEY of the entity to be migrated")
   (msa-list tpm-msa-composite-p "One or more digests of public keys belonging to migration authorities")
   (restrict-ticket byte-list-p "If migrationType is TPM_MS_RESTRICT_APPROVE, a TPM_CMK_AUTH structure, containing the digests of the public keys belonging to the Migration Authority, the destination parent key and the key-to-be-migr ...")
   (sig-ticket byte-list-p "If migrationType is TPM_MS_RESTRICT_APPROVE, a TPM_HMAC structure, generated by the TPM, signaling a valid signature over restrictTicket")
   (enc-data byte-list-p "The encrypted entity that is to be modified.")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (random byte-list-p "String used for xor encryption" :hyp :fguard)
               (out-data byte-list-p "The modified, encrypted entity." :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 11.10 TPM_CMK_ConvertMigration
(cutil::define tpm-cmk_-convert-migration
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (parent-handle tpm-key-handle-p "Handle of a loaded key that can decrypt keys.")
   (restrict-ticket tpm-cmk-auth-p "The digests of public keys belonging to the Migration Authority, the destination parent key and the key-to-be-migrated.")
   (sig-ticket tpm-hmac-p "A signature ticket, generated by the TPM, signaling a valid signature over restrictTicket")
   (migrated-key tpm-key12-p "The public key of the key-to-be-migrated. The private portion MUST be TPM_MIGRATE_ASYMKEY properly XOR'd")
   (msa-list tpm-msa-composite-p "One or more digests of public keys belonging to migration authorities")
   (random byte-list-p "Random value used to hide key data.")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (out-data byte-list-p "The encrypted private key that can be loaded with TPM_LoadKey" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 12.1 TPM_CreateMaintenanceArchive
(cutil::define tpm-create-maintenance-archive
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (generate-random booleanp "Use RNG or Owner auth to generate 'random'.")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (random byte-list-p "Random data to XOR with result." :hyp :fguard)
               (archive byte-list-p "Encrypted key archive." :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 12.2 TPM_LoadMaintenanceArchive
(cutil::define tpm-load-maintenance-archive
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (archive byte-list-p "Encrypted key archive")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 12.3 TPM_KillMaintenanceFeature
(cutil::define tpm-kill-maintenance-feature
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 12.4 TPM_LoadManuMaintPub
(cutil::define tpm-load-manu-maint-pub
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (anti-replay tpm-nonce-p "AntiReplay and validation nonce")
   (pub-key tpm-pubkey-p "The public key of the manufacturer to be in use for maintenance"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (checksum tpm-digest-p "Digest of pubKey and antiReplay" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 12.5 TPM_ReadManuMaintPub
(cutil::define tpm-read-manu-maint-pub
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (anti-replay tpm-nonce-p "AntiReplay and validation nonce"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (checksum tpm-digest-p "Digest of pubKey and antiReplay" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 13.1 TPM_SHA1Start
(cutil::define tpm-sha1-start
  ((tpm-data tpmx-internal-data-p "Internal TPM data"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (max-num-bytes uint32-p "Maximum number of bytes that can be sent to TPM_SHA1Update. Must be a multiple of 64 bytes." :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 13.2 TPM_SHA1Update
(cutil::define tpm-sha1-update
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (hash-data byte-list-p "Bytes to be hashed"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 13.3 TPM_SHA1Complete
(cutil::define tpm-sha1-complete
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (hash-data byte-list-p "Final bytes to be hashed"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (hash-value tpm-digest-p "The output of the SHA-1 hash." :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

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
  nil)

;; 13.5 TPM_Sign
(cutil::define tpm-sign
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (key-handle tpm-key-handle-p "The keyHandle identifier of a loaded key that can perform digital signatures.")
   (area-to-sign byte-list-p "The value to sign")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (sig byte-list-p "The resulting digital signature." :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 13.6 TPM_GetRandom
(cutil::define tpm-get-random
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (bytes-requested uint32-p "Number of bytes to return"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (random-bytes byte-list-p "The returned bytes" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 13.7 TPM_StirRandom
(cutil::define tpm-stir-random
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (in-data byte-list-p "Data to add entropy to RNG state"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 13.8 TPM_CertifyKey
(cutil::define tpm-certify-key
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (cert-handle tpm-key-handle-p "Handle of the key to be used to certify the key.")
   (key-handle tpm-key-handle-p "Handle of the key to be certified.")
   (anti-replay tpm-nonce-p "160 bits of externally supplied data (typically a nonce provided to prevent replay-attacks)")
   (auth1 tpmx-auth-info-p "Auth Info object")
   (auth2 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (certify-info tpm-certify-info-p "TPM_CERTIFY_INFO or TPM_CERTIFY_INFO2 structure that provides information relative to keyhandle" :hyp :fguard)
               (out-data byte-list-p "The signature of certifyInfo" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard)
               (auth2 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 13.9 TPM_CertifyKey2
(cutil::define tpm-certify-key2
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (key-handle tpm-key-handle-p "Handle of the key to be certified.")
   (cert-handle tpm-key-handle-p "Handle of the key to be used to certify the key.")
   (migration-pub-digest tpm-digest-p "The digest of a TPM_MSA_COMPOSITE structure, containing at least one public key of a Migration Authority")
   (anti-replay tpm-nonce-p "160 bits of externally supplied data (typically a nonce provided to prevent replay-attacks)")
   (auth1 tpmx-auth-info-p "Auth Info object")
   (auth2 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (certify-info tpm-certify-info2-p "TPM_CERTIFY_INFO2 relative to keyHandle" :hyp :fguard)
               (out-data byte-list-p "The signed public key." :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard)
               (auth2 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 14.1 TPM_CreateEndorsementKeyPair
(cutil::define tpm-create-endorsement-key-pair
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (anti-replay tpm-nonce-p "Arbitrary data")
   (key-info tpm-key-parms-p "Information about key to be created, this includes all algorithm parameters"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (pub-endorsement-key tpm-pubkey-p "The public endorsement key" :hyp :fguard)
               (checksum tpm-digest-p "Hash of pubEndorsementKey and antiReplay" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 14.2 TPM_CreateRevocableEK
(cutil::define tpm-create-revocable-ek
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (anti-replay tpm-nonce-p "Arbitrary data")
   (key-info tpm-key-parms-p "Information about key to be created, this includes all algorithm parameters")
   (generate-reset booleanp "If TRUE use TPM RNG to generate EKreset. If FALSE use the passed value inputEKreset")
   (input-e-kreset tpm-nonce-p "The authorization value to be used with TPM_RevokeTrust if generateReset==FALSE, else the parameter is present but ignored"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (pub-endorsement-key tpm-pubkey-p "The public endorsement key" :hyp :fguard)
               (checksum tpm-digest-p "Hash of pubEndorsementKey and antiReplay" :hyp :fguard)
               (output-e-kreset tpm-nonce-p "The AuthData value to use TPM_RevokeTrust" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 14.3 TPM_RevokeTrust
(cutil::define tpm-revoke-trust
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (ek-reset tpm-nonce-p "The value that will be matched to EK Reset"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 14.4 TPM_ReadPubek
(cutil::define tpm-read-pubek
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (anti-replay tpm-nonce-p "Arbitrary data"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (pub-endorsement-key tpm-pubkey-p "The public endorsement key" :hyp :fguard)
               (checksum tpm-digest-p "Hash of pubEndorsementKey and antiReplay" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 14.5 TPM_OwnerReadInternalPub
(cutil::define tpm-owner-read-internal-pub
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (key-handle tpm-key-handle-p "Handle for either PUBEK or SRK")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (public-portion tpm-pubkey-p "The public portion of the requested key" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 15.1 TPM_MakeIdentity
(cutil::define tpm-make-identity
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (identity-auth tpm-encauth-p "Encrypted usage AuthData for the new identity")
   (label-priv-ca-digest tpm-chosenid-hash-p "The digest of the identity label and privacy CA chosen for the AIK")
   (id-key-params tpm-key-p "Structure containing all parameters of new identity key. pubKey.keyLength and idKeyParams.encData are both 0 MAY be TPM_KEY12")
   (auth1 tpmx-auth-info-p "Auth Info object")
   (auth2 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (id-key tpm-key-p "The newly created identity key. MAY be TPM_KEY12" :hyp :fguard)
               (identity-binding byte-list-p "Signature of TPM_IDENTITY_CONTENTS using idKey.private." :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard)
               (auth2 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 15.2 TPM_ActivateIdentity
(cutil::define tpm-activate-identity
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (id-key-handle tpm-key-handle-p "Identity key to be activated")
   (blob byte-list-p "The encrypted ASYM_CA_CONTENTS or TPM_EK_BLOB")
   (auth1 tpmx-auth-info-p "Auth Info object")
   (auth2 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (symmetric-key tpm-symmetric-key-p "The decrypted symmetric key." :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard)
               (auth2 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

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
  nil)

;; 16.2 TPM_PCRRead
(cutil::define tpm-pcr-read
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (pcr-index tpm-pcrindex-p "Index of the PCR to be read"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (out-digest tpm-pcrvalue-p "The current contents of the named PCR" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 16.3 TPM_Quote
(cutil::define tpm-quote
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (key-handle tpm-key-handle-p "The keyHandle identifier of a loaded key that can sign the PCR values.")
   (external-data tpm-nonce-p "160 bits of externally supplied data (typically a nonce provided by a server to prevent replay-attacks)")
   (target-pcr tpm-pcr-selection-p "The indices of the PCRs that are to be reported.")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (pcr-data tpm-pcr-composite-p "A structure containing the same indices as targetPCR, plus the corresponding current PCR values." :hyp :fguard)
               (sig byte-list-p "The signed data blob." :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 16.4 TPM_PCR_Reset
(cutil::define tpm-pcr_-reset
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (pcr-selection tpm-pcr-selection-p "The PCR's to reset"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 16.5 TPM_Quote2
(cutil::define tpm-quote2
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (key-handle tpm-key-handle-p "The keyHandle identifier of a loaded key that can sign the PCR values.")
   (external-data tpm-nonce-p "160 bits of externally supplied data (typically a nonce provided by a server to prevent replay-attacks)")
   (target-pcr tpm-pcr-selection-p "The indices of the PCRs that are to be reported.")
   (add-version booleanp "When TRUE add TPM_CAP_VERSION_INFO to the output")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (pcr-data tpm-pcr-info-short-p "The value created and signed for the quote" :hyp :fguard)
               (version-info tpm-cap-version-info-p "The version info" :hyp :fguard)
               (sig byte-list-p "The signed data blob." :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 17.1 TPM_ChangeAuth
(cutil::define tpm-change-auth
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (parent-handle tpm-key-handle-p "Handle of the parent key to the entity.")
   (protocol-id tpm-protocol-id-p "The protocol in use.")
   (new-auth tpm-encauth-p "The encrypted new AuthData for the entity")
   (entity-type tpm-entity-type-p "The type of entity to be modified")
   (enc-data byte-list-p "The encrypted entity that is to be modified.")
   (auth1 tpmx-auth-info-p "Auth Info object")
   (auth2 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (out-data byte-list-p "The modified, encrypted entity." :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard)
               (auth2 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 17.2 TPM_ChangeAuthOwner
(cutil::define tpm-change-auth-owner
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (protocol-id tpm-protocol-id-p "The protocol in use.")
   (new-auth tpm-encauth-p "The encrypted new AuthData for the entity")
   (entity-type tpm-entity-type-p "The type of entity to be modified")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 18.1 TPM_OIAP
(cutil::define tpm-oiap
  ((tpm-data tpmx-internal-data-p "Internal TPM data"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (auth-handle tpm-authhandle-p "Handle that TPM creates that points to the authorization state." :hyp :fguard)
               (nonce-even tpm-nonce-p "Nonce generated by TPM and associated with session." :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 18.2 TPM_OSAP
(cutil::define tpm-osap
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (entity-type tpm-entity-type-p "The type of entity in use")
   (entity-value uint32-p "The selection value based on entityType, e.g. a keyHandle #")
   (nonce-odd-osap tpm-nonce-p "The nonce generated by the caller associated with the shared secret."))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (auth-handle tpm-authhandle-p "Handle that TPM creates that points to the authorization state." :hyp :fguard)
               (nonce-even tpm-nonce-p "Nonce generated by TPM and associated with session." :hyp :fguard)
               (nonce-even-osap tpm-nonce-p "Nonce generated by TPM and associated with shared secret." :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 18.3 TPM_DSAP
(cutil::define tpm-dsap
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (entity-type tpm-entity-type-p "The type of delegation information to use")
   (key-handle tpm-key-handle-p "Key for which delegated authority corresponds, or 0 if delegated owner activity. Only relevant if entityValue equals TPM_DELEGATE_KEY_BLOB")
   (nonce-odd-dsap tpm-nonce-p "The nonce generated by the caller associated with the shared secret.")
   (entity-value byte-list-p "TPM_DELEGATE_KEY_BLOB or TPM_DELEGATE_OWNER_BLOB or index MUST not be empty If entityType is TPM_ET_DEL_ROW then entityValue is a TPM_DELEGATE_INDEX"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (auth-handle tpm-authhandle-p "Handle that TPM creates that points to the authorization state." :hyp :fguard)
               (nonce-even tpm-nonce-p "Nonce generated by TPM and associated with session." :hyp :fguard)
               (nonce-even-dsap tpm-nonce-p "Nonce generated by TPM and associated with shared secret." :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 18.4 TPM_SetOwnerPointer
(cutil::define tpm-set-owner-pointer
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (entity-type tpm-entity-type-p "The type of entity in use")
   (entity-value uint32-p "The selection value based on entityType"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 19.1 TPM_Delegate_Manage
(cutil::define tpm-delegate_-manage
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (family-id tpm-family-id-p "The familyID that is to be managed")
   (op-code tpm-family-operation-p "Operation to be performed by this command.")
   (op-data byte-list-p "Data necessary to implement opCode")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (ret-data byte-list-p "Returned data" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 19.2 TPM_Delegate_CreateKeyDelegation
(cutil::define tpm-delegate_-create-key-delegation
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (key-handle tpm-key-handle-p "The keyHandle identifier of a loaded key.")
   (public-info tpm-delegate-public-p "The public information necessary to fill in the blob")
   (del-auth tpm-encauth-p "The encrypted new AuthData for the blob. The encryption key is the shared secret from the authorization session protocol.")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (blob tpm-delegate-key-blob-p "The partially encrypted delegation information." :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 19.3 TPM_Delegate_CreateOwnerDelegation
(cutil::define tpm-delegate_-create-owner-delegation
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (increment booleanp "Flag dictates whether verificationCount will be incremented")
   (public-info tpm-delegate-public-p "The public parameters for the blob")
   (del-auth tpm-encauth-p "The encrypted new AuthData for the blob. The encryption key is the shared secret from the OSAP protocol.")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (blob tpm-delegate-owner-blob-p "The partially encrypted delegation information." :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 19.4 TPM_Delegate_LoadOwnerDelegation
(cutil::define tpm-delegate_-load-owner-delegation
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (index tpm-delegate-index-p "The index of the delegate row to be written")
   (blob tpm-delegate-owner-blob-p "Delegation information, including encrypted portions as appropriate")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 19.5 TPM_Delegate_ReadTable
(cutil::define tpm-delegate_-read-table
  ((tpm-data tpmx-internal-data-p "Internal TPM data"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (family-table byte-list-p "Array of TPM_FAMILY_TABLE_ENTRY elements" :hyp :fguard)
               (delegate-table byte-list-p "Array of TPM_DELEGATE_INDEX and TPM_DELEGATE_PUBLIC elements" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 19.6 TPM_Delegate_UpdateVerification
(cutil::define tpm-delegate_-update-verification
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (input-data byte-p "TPM_DELEGATE_KEY_BLOB or TPM_DELEGATE_OWNER_BLOB or TPM_DELEGATE_INDEX")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (output-data byte-p "TPM_DELEGATE_KEY_BLOB or TPM_DELEGATE_OWNER_BLOB" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 19.7 TPM_Delegate_VerifyDelegation
(cutil::define tpm-delegate_-verify-delegation
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (delegation byte-list-p "TPM_DELEGATE_KEY_BLOB or TPM_DELEGATE_OWNER_BLOB"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 20.1 TPM_NV_DefineSpace
(cutil::define tpm-nv_-define-space
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (pub-info tpm-nv-data-public-p "The public parameters of the NV area")
   (enc-auth tpm-encauth-p "The encrypted AuthData, only valid if the attributes require subsequent authorization")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 20.2 TPM_NV_WriteValue
(cutil::define tpm-nv_-write-value
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (nv-index tpm-nv-index-p "The index of the area to set")
   (offset uint32-p "The offset into the NV Area")
   (data byte-p "The data to set the area to")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;;  TPM_NV_WriteValueAuth
(cutil::define tpm-nv_-write-value-auth
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (nv-index tpm-nv-index-p "The index of the area to set")
   (offset uint32-p "The offset into the chunk")
   (data byte-p "The data to set the area to")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;;  TPM_NV_ReadValue
(cutil::define tpm-nv_-read-value
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (nv-index tpm-nv-index-p "The index of the area to set")
   (offset uint32-p "The offset into the area")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (data byte-p "The data to set the area to" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 20.5 TPM_NV_ReadValueAuth
(cutil::define tpm-nv_-read-value-auth
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (nv-index tpm-nv-index-p "The index of the area to set")
   (offset uint32-p "The offset from the data area")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (data byte-p "The data" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 21.1 TPM_KeyControlOwner
(cutil::define tpm-key-control-owner
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (key-handle tpm-key-handle-p "The handle of a loaded key.")
   (pub-key tpm-pubkey-p "The public key associated with the loaded key")
   (bit-name tpm-key-control-p "The name of the bit to be modified")
   (bit-value booleanp "The value to set the bit to")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 21.3 TPM_SaveContext
(cutil::define tpm-save-context
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (handle tpm-handle-p "Handle of the resource being saved.")
   (resource-type tpm-resource-type-p "The type of resource that is being saved")
   (label 16-byte-list-p "Label for identification purposes"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (context-blob tpm-context-blob-p "The context blob" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 21.3 TPM_LoadContext
(cutil::define tpm-load-context
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (entity-handle tpm-handle-p "The handle the TPM MUST use to locate the entity tied to the OSAP/DSAP session")
   (keep-handle booleanp "Indication if the handle MUST be preserved")
   (context-blob tpm-context-blob-p "The context blob"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (handle tpm-handle-p "The handle assigned to the resource after it has been successfully loaded." :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 22.1 TPM_FlushSpecific
(cutil::define tpm-flush-specific
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (handle tpm-handle-p "The handle of the item to flush")
   (resource-type tpm-resource-type-p "The type of resource that is being flushed"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 23.1 TPM_GetTicks
(cutil::define tpm-get-ticks
  ((tpm-data tpmx-internal-data-p "Internal TPM data"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (current-time tpm-current-ticks-p "The current time held in the TPM" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 23.2 TPM_TickStampBlob
(cutil::define tpm-tick-stamp-blob
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (key-handle tpm-key-handle-p "The keyHandle identifier of a loaded key that can perform digital signatures.")
   (anti-replay tpm-nonce-p "Anti replay value added to signature")
   (digest-to-stamp tpm-digest-p "The digest to perform the tick stamp on")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (current-ticks tpm-current-ticks-p "The current time according to the TPM" :hyp :fguard)
               (sig byte-list-p "The resulting digital signature." :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 24.1 TPM_EstablishTransport
(cutil::define tpm-establish-transport
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (enc-handle tpm-key-handle-p "The handle to the key that encrypted the blob")
   (trans-public tpm-transport-public-p "The public information describing the transport session")
   (secret byte-list-p "The encrypted secret area")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (trans-handle tpm-transhandle-p "The handle for the transport session" :hyp :fguard)
               (locality tpm-modifier-indicator-p "The locality that called this command" :hyp :fguard)
               (current-ticks tpm-current-ticks-p "The current tick count" :hyp :fguard)
               (trans-nonce-even tpm-nonce-p "The even nonce in use for subsequent execute transport" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 24.2 TPM_ExecuteTransport
(cutil::define tpm-execute-transport
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (wrapped-cmd byte-list-p "The wrapped command")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (current-ticks uint64-p "The current ticks when the command was executed" :hyp :fguard)
               (locality tpm-modifier-indicator-p "The locality that called this command" :hyp :fguard)
               (wrapped-rsp byte-list-p "The wrapped response" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 24.3 TPM_ReleaseTransportSigned
(cutil::define tpm-release-transport-signed
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (key-handle tpm-key-handle-p "Handle of a loaded key that will perform the signing")
   (anti-replay tpm-nonce-p "Value provided by caller for anti-replay protection")
   (auth1 tpmx-auth-info-p "Auth Info object")
   (auth2 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (locality tpm-modifier-indicator-p "The locality that called this command" :hyp :fguard)
               (current-ticks tpm-current-ticks-p "The current ticks when the command executed" :hyp :fguard)
               (signature byte-list-p "The signature of the digest" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard)
               (auth2 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 25.1 TPM_CreateCounter
(cutil::define tpm-create-counter
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (enc-auth tpm-encauth-p "The encrypted auth data for the new counter")
   (label byte-p "Label to associate with counter")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (count-id tpm-count-id-p "The handle for the counter" :hyp :fguard)
               (counter-value tpm-counter-value-p "The starting counter value" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 25.2 TPM_IncrementCounter
(cutil::define tpm-increment-counter
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (count-id tpm-count-id-p "The handle of a valid counter")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (count tpm-counter-value-p "The counter value" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 25.3 TPM_ReadCounter
(cutil::define tpm-read-counter
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (count-id tpm-count-id-p "ID value of the counter"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (count tpm-counter-value-p "The counter value" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 25.4 TPM_ReleaseCounter
(cutil::define tpm-release-counter
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (count-id tpm-count-id-p "ID value of the counter")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 25.5 TPM_ReleaseCounterOwner
(cutil::define tpm-release-counter-owner
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (count-id tpm-count-id-p "ID value of the counter")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 26.1 TPM_DAA_Join
(cutil::define tpm-daa_-join
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (handle tpm-handle-p "Session handle")
   (stage byte-p "Processing stage of join")
   (input-size0 uint32-p "Size of inputData0 for this stage of JOIN")
   (input-data0 byte-list-p "Data to be used by this capability")
   (input-size1 uint32-p "Size of inputData1 for this stage of JOIN")
   (input-data1 byte-list-p "Data to be used by this capability")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (output-data byte-list-p "Data produced by this capability" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)

;; 26.2 TPM_DAA_Sign
(cutil::define tpm-daa_-sign
  ((tpm-data tpmx-internal-data-p "Internal TPM data")
   (handle tpm-handle-p "Handle to the sign session")
   (stage byte-p "Stage of the sign process")
   (input-size0 uint32-p "Size of inputData0 for this stage of DAA_Sign")
   (input-data0 byte-list-p "Data to be used by this capability")
   (input-size1 uint32-p "Size of inputData1 for this stage of DAA_Sign")
   (input-data1 byte-list-p "Data to be used by this capability")
   (auth1 tpmx-auth-info-p "Auth Info object"))
  :returns (mv (tpm-data tpmx-internal-data-p "Internal TPM data" :hyp :fguard)
               (return-code tpm-result-p "Return code" :hyp :fguard)
               (output-data byte-list-p "Data produced by this capability" :hyp :fguard)
               (auth1 tpmx-auth-info-p "Auth Info object" :hyp :fguard))
  :parents(tpm-commands)
  ;; Function Body
  nil)
