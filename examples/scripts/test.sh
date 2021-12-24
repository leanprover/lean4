set -ex
${LAKE:-../../build/bin/lake} script list
${LAKE:-../../build/bin/lake} script run scripts/greet
${LAKE:-../../build/bin/lake} script run greet me
${LAKE:-../../build/bin/lake} script doc greet
${LAKE:-../../build/bin/lake} script run nonexistant && false || true
${LAKE:-../../build/bin/lake} script doc nonexistant && false || true
