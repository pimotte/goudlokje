#!/bin/sh
set -e
lake build
lake test
e2e/run.sh
