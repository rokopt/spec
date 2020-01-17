#!/bin/sh

set -e

rm -f *.ibc

files=$(ls *.idr)
for file in ${files[@]}; do
  echo "Typechecking $file..."
  output=$(idris --noprelude --check $file)
  if [ -z "$output" ]; then
    echo "OK!"
  else
    echo "$output"
    exit 1
  fi
done
