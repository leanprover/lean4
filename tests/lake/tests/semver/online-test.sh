#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test an exact version
test_out 'using version `2.0.0`' -R -KdepVer="=2.0.0" update --keep-toolchain

# Test an approximate version
test_out 'using version `2.1.0`' -R -KdepVer="~2" update --keep-toolchain

# Test a complex version
test_out 'using version `2.0.0`' -R -KdepVer="1.*.* || 2.x.x, !=2.1.0" update --keep-toolchain

# Test TOML versions
test_out 'using version `2.1.0`' -R -f version.toml update --keep-toolchain

