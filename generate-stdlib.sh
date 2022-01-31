#!/bin/bash

mkdir std-out
i=0
cd agda-stdlib/src
find . -name "*.agda" | sort |
    while read file;
    do
        echo $i;
        i=$(($i+1));
        stack exec -- Agda2Dedukti-exe --dk "$file" --outDir=../../std-out/ ;
    done
