#!/usr/bin/env bash
# Run every test of a manifest in its own process, so one that hangs or overflows is a failure and not the end of the run.
# usage: ./run-suite.sh <tests-dir> <manifest> [seconds]
set -u
cd "$(dirname "$0")"
dir=$1; manifest=$2; secs=${3:-10}
bin=.lake/build/bin/jsonld_suite
pass=0; fail=0
for id in $(grep -o '"@id": *"#[^"]*"' "$manifest" | sed 's/.*"\(#[^"]*\)"/\1/'); do
  out=$(perl -e 'alarm shift; exec @ARGV' "$secs" "$bin" "$dir" "$manifest" "$id" 2>&1); rc=$?
  case "$out" in
    *"1 pass, 0 fail"*) pass=$((pass+1));;
    *"0 pass, 0 fail, 1 skipped"*) ;;
    *) fail=$((fail+1)); echo "FAIL $id: $(echo "$out" | head -1 | cut -c1-160) [rc $rc]";;
  esac
done
echo "$pass pass, $fail fail"
