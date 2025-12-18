set -ex

${LAKE:-./.lake/build/bin/lake} --version
${LAKE:-./.lake/build/bin/lake} self-check
