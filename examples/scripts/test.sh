set -ex
${LAKE:-../../build/bin/lake} run greet
${LAKE:-../../build/bin/lake} run greet -- me
