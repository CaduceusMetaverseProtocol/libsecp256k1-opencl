#!/bin/bash 
HOME=$HOME
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$HOME/usr/lib

gcc test.c -g -I $HOME/usr/include -I ./ -L $HOME/usr/lib -lsecp256k1 -o test && ./test
