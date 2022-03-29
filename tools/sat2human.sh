#!/bin/sh

if [ $# -le 1 ]; then
    echo "Usage: $0 <CNF-file> <SAT-file>"
    exit 1
fi

CNF_FILE="$1"
if [ "$(head -n1 $CNF_FILE)" != "c cksystemsgroup.github.io/unicorn" ]; then
    echo "First input doesn't look like a Unicorn CNF file!"
    exit 1
fi

SAT_FILE="$2"
if [ "$(head -n1 $SAT_FILE)" != "SAT" ]; then
    echo "Second input doesn't look like a SAT file!"
    exit 1
fi

grep "c   " $CNF_FILE | while read line; do
    varc=$(echo $line | cut -d' ' -f2 -)
    name=$(echo $line | cut -d' ' -f3 -)
    assignment=$(grep -o " -\?${varc::-1} " $SAT_FILE)
    [[ $assignment -lt 0 ]] && val=0 || val=1
    echo "#$varc $val $name"
done
