#!/bin/bash 
LIBDIR=$PWD/../.build/lib

gcc -g testocl.c -o testocl -I. -L${LIBDIR} -loclsp -lOpenCL
./testocl ./data/eth_rsh.txt ./data/eth_v.txt ./data/eth_xy.txt
#gdb ./testocl 
