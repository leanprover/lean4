#!/usr/bin/env bash
set -euo pipefail

echo "Setting up Lean 4 development environment..."

# Set stack size limit to match test suite
ulimit -s 8192

# Install elan (Lean version manager) without default toolchain
if ! command -v elan &> /dev/null; then
    echo "Installing elan..."
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- --default-toolchain none -y
fi

# Add elan to PATH for this session
export PATH="$HOME/.elan/bin:$PATH"

# Create directory structure for toolchain links
echo "Creating build directory structure..."
mkdir -p /workspace/lean4/build/release/stage0/bin
mkdir -p /workspace/lean4/build/release/stage1/bin

# Create placeholder lean executables for elan
# These will be replaced by actual builds later
echo '#!/bin/bash' > /workspace/lean4/build/release/stage0/bin/lean
echo 'echo "Stage 0 lean placeholder - run make to build"' >> /workspace/lean4/build/release/stage0/bin/lean
chmod +x /workspace/lean4/build/release/stage0/bin/lean

echo '#!/bin/bash' > /workspace/lean4/build/release/stage1/bin/lean
echo 'echo "Stage 1 lean placeholder - run make to build"' >> /workspace/lean4/build/release/stage1/bin/lean
chmod +x /workspace/lean4/build/release/stage1/bin/lean

# Link toolchains - these will be used based on lean-toolchain files in each directory
echo "Setting up elan toolchains..."
elan toolchain link lean4-stage0 /workspace/lean4/build/release/stage0 || true
elan toolchain link lean4 /workspace/lean4/build/release/stage1 || true

# Install both toolchains so they're available
# This ensures seamless switching based on directory context
echo "Installing linked toolchains..."
elan toolchain install lean4-stage0 || true
elan toolchain install lean4 || true

# Set up ccache
echo "Configuring ccache..."
ccache --set-config=max_size=5G
ccache --set-config=compiler_check=content
ccache --set-config=hash_dir=false

# Configure git to handle lean4 directory
git config --global --add safe.directory /workspace/lean4

# Initial cmake configuration
echo "Running initial cmake configuration..."
cd /workspace/lean4
cmake --preset release || true

echo "Development environment setup complete!"
echo ""
echo "To build Lean 4, run:"
echo "  make -C build/release -j\$(nproc)"
echo ""
echo "To run tests, run:"
echo "  make -C build/release test"