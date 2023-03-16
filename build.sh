#!bin/bash

# ToDo: Check queries for -DARCH64

DEFS_SEQ=" -ffast-math -DEXTRA"
DEFS_MEM=" -ffast-math -DEXTRA -DMALLOC_COUNT"

g++ -O3 -c bit_array.cpp

echo "Compiling sequential algorithm ..."
g++ -O3 -o st_seq $DEFS_SEQ main.cpp util.cpp bit_array.o   lookup_tables.cpp -lrt -lm


echo "Compiling sequential algorithm (Working space) ..."
#g++ -c malloc_count.cpp
#g++ -O2 -std=gnu99 -o st_mem $DEFS_MEM main.cpp util.cpp bit_array.o malloc_count.o \
#succinct_tree.cpp lookup_tables.cpp -lrt -lm -ldl
