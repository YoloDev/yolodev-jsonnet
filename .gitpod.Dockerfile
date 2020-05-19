FROM gitpod/workspace-full

USER gitpod

RUN rustup self update \
  && rustup toolchain install nightly --allow-downgrade --component clippy --component rustfmt --no-self-update \
  && rustup default nightly

# Install custom tools, runtime, etc. using apt-get
# For example, the command below would install "bastet" - a command line tetris clone:
#
# RUN sudo apt-get -q update && #     sudo apt-get install -yq bastet && #     sudo rm -rf /var/lib/apt/lists/*
#
# More information: https://www.gitpod.io/docs/config-docker/
