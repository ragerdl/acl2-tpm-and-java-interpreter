; ACL2 Interpreter for Java
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

; We load this here now so we can import their symbols into JI as desired.
(ld "cutil/package.lsp" :dir :system)

(defpkg "JI"
  (set-difference-eq
   (union-eq cutil::*cutil-exports*
    (union-eq ;sets::*sets-exports*
              '(defxdoc defsection xdoc xdoc! b* patbind-when-match
                 assert!) 
              (union-eq *acl2-exports*
                        *common-lisp-symbols-from-main-lisp-package*)))
   '(method method-p make-method
     member member-p make-member
     class class-p make-class
            )))
