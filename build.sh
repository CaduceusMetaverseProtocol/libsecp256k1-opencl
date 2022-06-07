#!/bin/bash 
BASE=$PWD
BUILD=$BASE/.build

# build secp256k1
mkdir -p $BUILD
./autogen.sh
./configure --prefix=$BUILD  --with-field=32bit --with-scalar=32bit --enable-module-recovery

make && make install

gcc -g -c oclsp/oclsp.c -I $BUILD/include -I $BASE/src -o oclsp/oclsp.o
ar x  $BUILD/lib/libsecp256k1.a
ar rs $BUILD/lib/liboclsp.a oclsp/oclsp.o libsecp256k1_la-secp256k1.o
cp oclsp/oclsp.h $BUILD/include/

rm oclsp/oclsp.o libsecp256k1_la-secp256k1.o 
echo "generate $BUILD/lib/liboclsp.a"
