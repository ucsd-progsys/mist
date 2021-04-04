FROM fpco/stack-build:lts-14.0

# install deps
RUN DEBIAN_FRONTEND=noninteractive \
    apt-get -y update && \
    apt-get -y install z3 git-core curl build-essential time libgmp-dev locales && \
    update-locale LANG=C.UTF-8 && \
    apt-get -y clean autoclean && \
    rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/*

# set shell to bash
RUN ln -sf /bin/bash /bin/sh

# set utf8 locale
ENV LANG C.UTF-8

# force https on github instead of ssh
RUN git config --system url."https://github.com/".insteadOf "git@github.com:"

# add ecoop21 user
RUN useradd -m ecoop21
USER ecoop21

# build mist
WORKDIR /home/ecoop21
RUN git clone -b ecoop21 --recursive https://github.com/ucsd-progsys/mist.git
WORKDIR /home/ecoop21/mist
ENV PATH "/home/ecoop21/.local/bin:${PATH}"
RUN stack install
RUN stack build
RUN stack build --test --no-run-tests

# The version of z3 that the stack image comes with segfaults on the mist tests.
# We add a newer version of z3 to the $PATH
# However, one must be careful! MoCHi will depend on yet another version of z3.
WORKDIR /home/ecoop21
RUN wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.10/z3-4.8.10-x64-ubuntu-18.04.zip
RUN unzip z3-4.8.10-x64-ubuntu-18.04.zip
RUN cp z3-4.8.10-x64-ubuntu-18.04/bin/z3 ~/.local/bin/

# Set things up nicely for the user
WORKDIR /home/ecoop21/mist
RUN git pull
RUN stack test
CMD /bin/bash
