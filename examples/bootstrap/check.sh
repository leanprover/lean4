set -ex

${LAKE:-./build/bin/lake} --version
${LAKE:-./build/bin/lake} self-check
