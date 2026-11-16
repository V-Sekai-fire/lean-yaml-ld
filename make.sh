#!/usr/bin/env bash
# Build the library and run the checks on the files in tests/.
set -euo pipefail
cd "$(dirname "$0")"
lake build YamlLd JsonLd HtmlScripts yamlld_witness jsonld_suite
.lake/build/bin/yamlld_witness tests/*.yamlld
