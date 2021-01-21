#!/usr/bin/env bash

set -euo pipefail

cd "$(dirname "$0")"

curl -fsSL http://speleotrove.com/decimal/decNumber-icu-368.zip > decnumber.zip

rm -rf decnumber-sys/decnumber
unzip decnumber.zip
mv decNumber decnumber-sys/decnumber
rm decnumber-sys/decnumber/example{1,2,3,4,5,6,7,8}.c decnumber-sys/decnumber/decnumber.pdf
rm decnumber.zip

(
    cd decnumber-sys/decnumber

    for f in *; do
        dos2unix "$f"
    done

    for p in ../patch/*; do
        patch -sp1 -i "$p"
    done
    find . -name '*.orig' -delete
)

curl -fsSL http://speleotrove.com/decimal/dectest.zip > dectest.zip
rm -rf testdata
mkdir testdata
(
    cd testdata

    unzip ../dectest.zip

    for f in *; do
        dos2unix "$f"
    done

    patch -p1 <<EOF
diff --git a/testall.decTest b/testall.decTest
index 294d367..d632c2c 100644
--- a/testall.decTest
+++ b/testall.decTest
@@ -74,13 +74,6 @@ dectest: tointegralx
 dectest: trim
 dectest: xor

--- The next are for the Strawman 4d concrete representations and
--- tests at those sizes [including dsEncode, ddEncode, and dqEncode,
--- which replace decimal32, decimal64, and decimal128]
-dectest: decSingle
-dectest: decDouble
-dectest: decQuad
-
 -- General 31->33-digit boundary tests
 dectest: randombound32
EOF
)
rm dectest.zip
