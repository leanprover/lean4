FROM mcr.microsoft.com/devcontainers/base:ubuntu-22.04

# Install build dependencies as specified in doc/make/ubuntu.md
# Plus additional developer tools for better experience
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
        git \
        libgmp-dev \
        libuv1-dev \
        cmake \
        ccache \
        clang \
        pkgconf \
        build-essential \
        ca-certificates \
        curl \
        python3 \
        python3-pip \
        gdb \
        rr \
        valgrind \
        time \
        bash-completion \
        htop \
        ripgrep \
        fd-find \
        && rm -rf /var/lib/apt/lists/*

# Create vscode user if it doesn't exist
RUN if ! id -u vscode > /dev/null 2>&1; then \
        useradd -m -s /bin/bash vscode && \
        echo "vscode ALL=(ALL) NOPASSWD:ALL" >> /etc/sudoers; \
    fi

# Switch to vscode user
USER vscode

# Set up workspace directory
RUN sudo mkdir -p /workspace/lean4 && \
    sudo chown -R vscode:vscode /workspace

# Pre-create elan directory
RUN mkdir -p /home/vscode/.elan

# Create symlinks for tools with different names on Ubuntu
RUN sudo ln -s /usr/bin/fdfind /usr/local/bin/fd && \
    sudo ln -s /usr/bin/rg /usr/local/bin/rg

# Set working directory
WORKDIR /workspace/lean4

# Keep container running
CMD ["/bin/bash"]