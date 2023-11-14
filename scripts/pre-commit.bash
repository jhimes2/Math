#!/usr/bin/bash

echo "$(dirname "$0")"

##clean
# find "$(dirname "$0")"/.. -type f -name "*\.agdai" -exec rm {} \;

echo "Running pre-commit hook"
git ls-files | grep -E "*\.agda" 2> /dev/null | while read line
do
    agda $line

    STATUS=$?

    if [ $STATUS -ne 0 ]; then
     echo "Pre-commit test failed for $line"
     exit $STATUS
    fi
done
