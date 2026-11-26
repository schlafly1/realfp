# Dev container for realfp (GitHub Codespaces, or VS Code "Reopen in Container").
# Ubuntu + a C compiler (realfp compiles a small C runtime) + elan (Lean's installer).
FROM mcr.microsoft.com/devcontainers/base:ubuntu

RUN apt-get update \
 && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends build-essential \
 && rm -rf /var/lib/apt/lists/*

USER vscode
WORKDIR /home/vscode
RUN curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
ENV PATH="/home/vscode/.elan/bin:${PATH}"
