#!/usr/bin/env bash
TAPLO_URL=https://github.com/tamasfe/taplo/releases/latest/download/taplo-linux-x86_64.gz
PROJECT_ROOT=$(realpath $(pwd)/../../../..)

curl -fsSL $TAPLO_URL | gzip -d - > taplo
chmod +x taplo

for file in ./valid/*.toml; do
    echo Test: $file should be marked valid by Taplo
    ./taplo lint --schema file://$PROJECT_ROOT/src/lake/schemas/lakefile-toml-schema.json $file
done

for file in ./invalid/*.toml; do
    echo Test: $file should be marked invalid by Taplo
    ! ./taplo lint --schema file://$PROJECT_ROOT/src/lake/schemas/lakefile-toml-schema.json $file
done