; ACL2 Parser for Java
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

(include-book "cutil/defaggregate" :dir :system)
(include-book "cutil/deflist" :dir :system)

(mutual-recursion
 (DEFUND FOO-P (X)
   (DECLARE (XARGS :GUARD T))
   (AND (CONSP X)
        (EQ (CAR X) :FOO)
        (ALISTP (CDR X))
        (CONSP (CDR X))
        (LET ((BAR (CDR (ASSOC 'BAR (CDR X)))))
             (DECLARE (IGNORABLE BAR))
             (AND (FOO-LIST-P BAR)))))

 (DEFUND FOO-LIST-P (X)
   (DECLARE (XARGS :GUARD T
                   :NORMALIZE NIL
                   :VERIFY-GUARDS T
                   :GUARD-DEBUG NIL
                   :GUARD-HINTS NIL))
   (IF (CONSP X)
       (AND (FOO-P (CAR X))
            (FOO-LIST-P (CDR X)))
       (NULL X))))

(set-ld-redefinition-action '(:warn! . :overwrite)
                            state)

(cutil::defaggregate foo
  (bar)
  :require ((foo-list-p-of-foo->bar
             (foo-list-p bar)))
  :tag :foo)

(cutil::deflist foo-list-p (x)
  (foo-p x)
  :elementp-of-nil nil
  :true-listp t)

(set-ld-redefinition-action nil state)
