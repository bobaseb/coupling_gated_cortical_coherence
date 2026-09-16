FROM python:3.11-bookworm

ENV DEBIAN_FRONTEND=noninteractive

# Install system dependencies: Git, curl, TeX Live for LaTeX, and build tools for Lean
RUN apt-get update && apt-get install -y \
    curl \
    git \
    build-essential \
    texlive \
    texlive-latex-extra \
    texlive-fonts-recommended \
    texlive-science \
    && rm -rf /var/lib/apt/lists/*

# Install uv (Python package manager)
ENV UV_LINK_MODE=copy
RUN curl -LsSf https://astral.sh/uv/install.sh | env UV_UNMANAGED_INSTALL="/usr/local/bin" sh

# Install elan (Lean version manager)
ENV ELAN_HOME=/usr/local/elan
ENV PATH="${ELAN_HOME}/bin:${PATH}"
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none

WORKDIR /workspace

# Pre-install the Lean toolchain to speed up first builds
COPY lean-toolchain ./
RUN elan toolchain install $(cat lean-toolchain) && \
    elan default $(cat lean-toolchain)

# Copy the repository code
COPY . /workspace/

# Default command
CMD ["bash"]
