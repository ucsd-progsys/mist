FROM fpco/stack-build:lts-14.0

# install deps
RUN export DEBIAN_FRONTEND=noninteractive
RUN apt-get -qq update
RUN apt-get install -y software-properties-common
RUN add-apt-repository -y ppa:avsm/ppa # for opam 2
RUN apt-get -qq update
# Mist deps
RUN apt-get -y install z3 git-core curl build-essential time libgmp-dev locales
# FStar deps
RUN apt-get -y install libssl-dev libsqlite3-dev g++ gcc m4 make opam pkg-config python libgmp3-dev unzip cmake
RUN update-locale LANG=C.UTF-8
RUN apt-get -y clean autoclean
RUN rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/*

# set shell to bash
RUN ln -sf /bin/bash /bin/sh

# set utf8 locale
ENV LANG C.UTF-8

# force https on github instead of ssh
RUN git config --system url."https://github.com/".insteadOf "git@github.com:"

# add ecoop21 user
RUN useradd -m ecoop21
RUN echo "ecoop21 ALL=(ALL:ALL) NOPASSWD:ALL" >> /etc/sudoers
USER ecoop21

# build mist
WORKDIR /home/ecoop21
RUN git clone -b ecoop21 --recursive https://github.com/ucsd-progsys/mist.git
WORKDIR /home/ecoop21/mist
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

# Prepare and build OPAM and OCaml
RUN opam init -y --disable-sandboxing
RUN opam update
RUN opam install -y ocamlbuild ocamlfind batteries stdint zarith yojson fileutils pprint menhir sedlex ppx_deriving ppx_deriving_yojson process pprint visitors fix wasm ppxlib=0.22.0

# Of course, Fstar requires its own version of z3....
ENV z3=z3-4.8.5-x64-debian-8.11
ADD https://github.com/FStarLang/binaries/raw/master/z3-tested/${z3}.zip .
RUN sudo unzip ${z3}.zip
ENV PATH=/home/ecoop21/${z3}/bin:${PATH}
WORKDIR /home/ecoop21

# Prepare and build F*
ADD update-fstar.sh .
RUN git clone https://github.com/FStarLang/FStar.git --depth=1
ENV FSTAR_HOME=/home/ecoop21/FStar
WORKDIR $FSTAR_HOME
RUN opam config exec -- make
WORKDIR /home/ecoop21

# Set things up nicely for the user
ENV PATH "/home/ecoop21/.local/bin:${PATH}"
WORKDIR /home/ecoop21/mist
RUN git pull
CMD stack test && cd ~ && /bin/bash
