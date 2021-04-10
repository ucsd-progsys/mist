% `mist` Artifact
% Anish Tondwalkar, Matt Kolosick, Ranjit Jhala

`mist` is a tiny language for teaching and experimenting with refinement types, in the style of
[LiquidHaskell](https://github.com/ucsd-progsys/liquidhaskell). We use it as
a platform for experimenting with and as a demonstration of implicit refinement
types as presented in the ECOOP21 paper _Refinements of Futures Past:
Higher-Order Specification with Implicit Refinement Types_. We start with the
parser and AST we use to teach our undergradute compilers class, and layer
upon it a refinement type checker directly translated from the typing rules
presented in that paper, which produces constraints that are solved the
`liquid-fixpoint` horn clause solver.

We present source code and binaries for `mist` in a container image that
includes installations of the competing tools we compare to: FStar and MoCHi.


# Initial Build, Install, and Running All Tests

You can use the Docker image or install `mist` manually. The
Docker image also includes Fstar and MoCHi, the other tools we compare against
in our paper

## Using `docker`

> (Windows and Mac users: make sure your docker container has at least 4GB of RAM)

The following command will download an image containing `mist`, `fstar`,
and `mochi`, run the full `mist` test suite, and then drop you into an
interactive shell at the root of the `mist` code repository.

    $ docker run -it atondwal/mist

If you want to skip the test suite, instead run

    $ docker run -it atondwal/mist /bin/bash

You can then (re)run all of the tests in the `tests/` directory (perhaps after
editing some) at any time by running

    $ stack test

### Juggling containers

You can use `docker ps` to see the running container and open another shell to
it using `docker exec`, e.g.:

    $ docker ps
    CONTAINER ID      IMAGE             STATUS            NAMES
    696b2221e3ad      atondwal/mist     Up 45 seconds     vibrant_leavitt
    $ docker exec -it vibrant_leavitt bash
    ecoop21@696b2221e3ad:~/mist$

You can use `docker start` to restart exited containers

    $ docker ps -a
    CONTAINER ID      IMAGE             STATUS                     NAMES
    696b2221e3ad      atondwal/mist     Exited (137) 5 seconds ago vibrant_leavitt
    $ docker start vibrant_leavitt
    vibrant_leavitt
    $ docker exec -it vibrant_leavitt bash
    ecoop21@696b2221e3ad:~/mist$

## Manually

You'll need git, [z3 version 4.8.10](https://github.com/Z3Prover/z3/releases), and [stack](https://docs.haskellstack.org/en/stable/README/).

    $ git clone -b ecoop21 --recursive https://github.com/uscd-progsys/mist
    $ cd mist
    $ stack install

You can then run the full `mist` test suite (which is located in the `tests/` directory).

    $ stack test

# Running specific tests

You can run a specific test by calling mist on the test file, e.g.

    $ mist tests/pos/incrState.hs

If you're using the docker image, you can also run tests for `fstar` and `mochi`:

    $ mochi mochi-tests/incrState.ml
    $ fstar fstar-tests/incrState.fst

# Benchmarks from the paper

Here's a table of where you can find each of the tests described in the paper:


| Name          | Mist test (tests/pos/)                                   | Mochi (mochi-tests/)                     | Fstar (fstar-tests/)                               |
| ------------- | ----------------------                                   | --------------------                     | --------------------                               |
| incr          | [incr00.hs](tests/pos/incr00.hs)                         | [incr00.ml](mochi-tests/incr00.ml)       | [incr.fst](fstar-tests/incr.fst)                   |
| sum           | [sum.hs](tests/pos/sum.hs)                               | [sum.ml](mochi-tests/sum.ml)             | [sum.fst](fstar-tests/sum.fst)                     |
| repeat        | [repeat.hs](tests/pos/repeat.hs)                         | [repeat.ml](mochi-tests/repeat.ml)       | x                                                  |
| d2            | [mochi-app-lin-ord2.hs](tests/pos/mochi-app-lin-ord2.hs) | [d2.ml](mochi-tests/d2.ml)               | [mochi-d2.fst](fstar-tests/mochi-d2.fst)           |
|               |                                                          |                                          |                                                    |
| incrState     | [incrStatePoly.hs](tests/pos/incrStatePoly.hs)           | [incrState.ml](mochi-tests/incrState.ml) | [incrState.fst](fstar-tests/incrState.fst)         |
| accessControl | [acl.hs](tests/pos/acl.hs)                               | [acl.ml](mochi-tests/acl.ml)             | [accessControl.fst](fstar-tests/accessControl.fst) |
| tick          | [tick-append.hs](tests/pos/tick-append.hs)               | x                                        | [tick.fst](fstar-tests/tick.fst)                   |
| linearDSL     | [linearTypes.hs](tests/pos/linearTypes.hs)               | x                                        | [linearDSL.fst](fstar-tests/linearDSL.fst)         |
|               |                                                          |                                          |                                                    |
| pagination    | [paginationTokens.hs](tests/pos/paginationTokens.hs)     | x                                        | x                                                  |
| login         | [idr_login.hs](tests/pos/idr_login.hs)                   | x                                        | x                                                  |
| twophase      | [twoPhaseCommit.hs](tests/pos/twoPhaseCommit.hs)         | x                                        | x                                                  |
| ticktock      | [ticktock3.hs](tests/pos/ticktock3.hs)                   | x                                        | x                                                  |
| tcp           | [tcp_client.hs](tests/pos/tcp_client.hs)                 | x                                        | x                                                  |

As in the paper, an `x` indicates that the specification cannot be directly expressed with that tool.

N.B. We use the latest version of mochi, to give it the best chance of passing
the above case studies. However, while the latest version of mochi fails the
`d2.ml` test, the version of mochi from the mochi paper passes it, so we
still mark it as passing in the paper.

# Writing Mist

(TODO)
