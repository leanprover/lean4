# You can find the new timestamped tags here: https://hub.docker.com/r/gitpod/workspace-full/tags
FROM gitpod/workspace-full

USER root
RUN apt-get update && apt-get install git libgmp-dev libuv1-dev cmake ccache clang -y && apt-get clean

USER gitpod

# Install and configure elan
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- --default-toolchain none
ENV PATH="/home/gitpod/.elan/bin:${PATH}"
RUN elan toolchain link lean4 build/release/stage1
RUN elan toolchain link lean4-stage0 build/release/stage0
