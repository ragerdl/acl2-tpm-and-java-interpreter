#!/bin/bash

# ACL2 TPM  Model
# Copyright (C) 2013 Battelle Memorial Institute
#
# Contact:
#  David Rager, ragerdl@cs.utexas.edu
#
# This program is free software; you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free Software
# Foundation; either version 2 of the License, or (at your option) any later
# version.  This program is distributed in the hope that it will be useful but
# WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
# more details.  You should have received a copy of the GNU General Public
# License along with this program; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
#
# Original author: David Rager <ragerdl@cs.utexas.edu>

wd=`pwd`

len=`expr length $wd`
len=`expr $len - 7`
LASTDIRPART=${wd:$len:7}
if [ $LASTDIRPART != "machine" ]; then
  echo "Run from the wrong directory.  Need to run from tpm-tcg/acl2/machine directory."
  exit
fi

./cert.pl doc --acl2 /home/ragerd/r/acl2-devel/ccl-saved_acl2hp -j 32 --keep-going


echo '(include-book "doc")' > workxxx.make-doc
echo '(xdoc::save "../../xdoc")' >> workxxx.make-doc
echo '(quit)' >> workxxx.make-doc

time acl2hp < workxxx.make-doc

rm workxxx.make-doc

pushd ../../xdoc

echo "About to add TPM documentation to version control from `pwd`"

svn add xml/* --quiet

echo "Done making TPM documentation.  The following command will commit the documentation:"

echo 'pushd ../../xdoc; svn commit -m "FMMC-14 Committing new version of TPM documentation"; popd'
