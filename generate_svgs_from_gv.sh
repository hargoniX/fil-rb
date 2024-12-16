#!/bin/sh
set -xe

for f in examples/*.gv; do
  file_name_wo_suffix=$(basename -s .gv $f)
  dot -Tsvg $f -o examples/${file_name_wo_suffix}.svg
done
