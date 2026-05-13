FROM mcr.microsoft.com/devcontainers/base:trixie
RUN apt update
RUN apt install -y nodejs npm plocate file git ripgrep
RUN npm install -g @anthropic-ai/claude-code   # Need to install via the devcontainer feature, so it patches the question asking.

USER vscode

# Install elan
RUN curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y
ENV PATH="/home/vscode/.elan/bin:/home/vscode/.local/bin:${PATH}"
ENV ELAN_HOME="/home/vscode/.elan"

# Install uv
RUN curl -LsSf https://astral.sh/uv/install.sh | sh

# Install correct lean version (so that it's cached)
COPY lean-toolchain /tmp/lean-toolchain
RUN elan toolchain install "$(cat /tmp/lean-toolchain)"

RUN sudo updatedb

RUN ln -s ~/.claude/link-me-claude.json ~/.claude.json

COPY init.sh /home/vscode

