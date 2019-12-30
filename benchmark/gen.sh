#!/bin/sh

cd inputs

LISTS=`ls  | grep -E "[^n]$"`

mkdir -p ../lists
rm -f ../lists/all

for l in $LISTS
do
    find $l -depth 1 | grep -E ".*in$" > ../lists/$l
    find $l -depth 1 | grep -E ".*in$" >> ../lists/all
done

cd ../
# adhoc
mv lists/Burn_POPL18 lists/burn
mv lists/Burn_POPL18_2 lists/burn2
mv lists/higher_nonterminating lists/nonterminating
cat lists/mochi lists/mochi2 > lists/mochis
