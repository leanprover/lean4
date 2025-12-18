# You can find the new timestamped tags here: https://hub.docker.com/r/gitpod/workspace-full/tags
FROM gitpod/workspace-full

USER root
RUN apt-get update && apt-get install git libgmp-dev libuv1-dev cmake ccache clang -y && apt-get clean

USER gitpod

# Install and configure elan
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
ENV PATH="/home/gitpod/.elan/bin:${PATH}"
# Create a dummy toolchain so that we can pre-register it with elan
RUN mkdir -p /workspace/lean4/build/release/stage1/bin && touch /workspace/lean4/build/release/stage1/bin/lean && elan toolchain link lean4 /workspace/lean4/build/release/stage1
RUN mkdir -p /workspace/lean4/build/release/stage0/bin && touch /workspace/lean4/build/release/stage0/bin/lean && elan toolchain link lean4-stage0 /workspace/lean4/build/release/stage0
