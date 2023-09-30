#!/usr/bin/env bash

echo "Running pre-commit hook"
echo $(git ls-files $(git rev-parse --show-toplevel)) \
     | tr ' ' '\n' \
     | grep "\.agda" \
     | grep -v "unfinishedProofs.agda" \
     | while read line
do
    agda $line

    STATUS=$?

    if [ $STATUS -ne 0 ]; then
     echo "Pre-commit test failed for $line"
     exit $STATUS
    fi
done
