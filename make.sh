#!/usr/bin/env bash
# Build the library and run the checks on the files in tests/.
set -euo pipefail
cd "$(dirname "$0")"
lake build YamlLd yamlld_witness yamlld_conform
.lake/build/bin/yamlld_witness tests/*.yamlld
