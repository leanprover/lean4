set -ex
${LAKE:-../../build/bin/lake} build-lib
${LAKE:-../../build/bin/lake} build-bin
