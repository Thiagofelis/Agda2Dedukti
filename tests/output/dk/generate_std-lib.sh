#!/bin/bash

mkdir std-out
i=0
cd agda-stdlib/src
find . -name "*.agda" | sort |
    while read file;
    do
        if (("$NB" == "$i"))
        then
            break
        fi;
        echo $i;
	echo $file;
        i=$(($i+1));
        stack exec -- Agda2Dedukti-exe --dk "$file" --outDir=../../std-out;
    done
