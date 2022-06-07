#!/bin/bash 
pwd=$PWD
BASE=$pwd/../
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$BASE/.libs

gcc test.c -g -I $BASE/include -I ./ -L $BASE/.libs -lsecp256k1 -o test && ./test
