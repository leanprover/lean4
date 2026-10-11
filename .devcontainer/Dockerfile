FROM mcr.microsoft.com/devcontainers/cpp:1-ubuntu-24.04

ARG REINSTALL_CMAKE_VERSION_FROM_SOURCE="3.22.2"

RUN apt-get update && export DEBIAN_FRONTEND=noninteractive \
    && apt-get -y install --no-install-recommends git libgmp-dev libuv1-dev cmake ccache clang pkgconf

COPY ./reinstall-cmake.sh /tmp/

# We require a custom CMake version: the default (3.18) does not come with presetes
RUN chmod +x /tmp/reinstall-cmake.sh && /tmp/reinstall-cmake.sh ${REINSTALL_CMAKE_VERSION_FROM_SOURCE} \
    && rm -f /tmp/reinstall-cmake.sh

USER vscode

# Modified from .gitpod.Dockerfile: Install and configure elan
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
ENV PATH="$PATH:/home/vscode/.elan/bin"
# Create a dummy toolchain so that we can pre-register it with elan
USER root
RUN mkdir -p /workspaces/lean4/build/release/stage1/bin && touch /workspaces/lean4/build/release/stage1/bin/lean && elan toolchain link lean4 /workspaces/lean4/build/release/stage1
RUN mkdir -p /workspaces/lean4/build/release/stage0/bin && touch /workspaces/lean4/build/release/stage0/bin/lean && elan toolchain link lean4-stage0 /workspaces/lean4/build/release/stage0
