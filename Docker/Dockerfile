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
# MoCHi deps
RUN apt-get install -y git make gcc m4 opam libgmp-dev libmpfr-dev libglpk-dev autoconf cpanminus
RUN update-locale LANG=C.UTF-8
#RUN apt-get -y clean autoclean
#RUN rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/*

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
# We add a newer version of z3 to what will be in the $PATH
WORKDIR /home/ecoop21
RUN wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.10/z3-4.8.10-x64-ubuntu-18.04.zip
RUN unzip z3-4.8.10-x64-ubuntu-18.04.zip
RUN cp z3-4.8.10-x64-ubuntu-18.04/bin/z3 ~/.local/bin/

# Prepare and build OPAM and OCaml
ARG ocaml_ver=4.09.1
RUN opam init -y --comp=$ocaml_ver --disable-sandboxing && \
    eval `opam config env`
# FStar deps
RUN opam install -y ocamlbuild ocamlfind batteries stdint zarith yojson fileutils pprint menhir sedlex ppx_deriving ppx_deriving_yojson process pprint visitors fix wasm ppxlib=0.22.0

# Of course, Fstar requires its own version of z3...
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

# Build mochi
RUN cpanm --sudo String::ShellQuote
RUN opam install -y z3 camlp5 ocamlfind zarith apron batteries yojson ppx_deriving dune menhir
RUN git clone https://github.com/hopv/MoCHi mochi
COPY --chown=ecoop21:ecoop21 horsat2 mochi

ENV OCAMLFIND_IGNORE_DUPS_IN /home/mochi/.opam/$ocaml_ver/lib/ocaml/compiler-libs

WORKDIR /home/ecoop21/mochi
RUN eval $(opam env) && \
    autoconf && \
    touch trecs && chmod +x trecs && \
    ./configure && \
    make install-lib && \
    make && \
    LD_LIBRARY_PATH=/home/mochi/.opam/$ocaml_ver/lib/z3 ./src/mochi.exe -v

# Set things up nicely for the user
RUN cp src/mochi.exe /home/ecoop21/.local/bin/mochi
RUN echo PATH=/home/ecoop21/z3-4.8.5-x64-debian-8.11/bin:/root/.local/bin:/usr/local/cuda-10.0/bin:/home/stackage/.stack/programs/x86_64-linux/ghc-8.6.5/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin /home/ecoop21/FStar/bin/fstar.exe '$@' > /home/ecoop21/.local/bin/fstar
RUN chmod +x /home/ecoop21/.local/bin/fstar
ENV PATH "/home/ecoop21/.local/bin:${PATH}"
WORKDIR /home/ecoop21/mist
RUN git pull
CMD stack test && /bin/bash
