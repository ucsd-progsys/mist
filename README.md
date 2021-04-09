# `mist` ECOOP 21 Artifact

# Initial Build, Install, and Running All Tests

You can use the Docker image (recommended) or install `mist` manually. The
Docker image also includes Fstar and MoCHi, the other tools we compare against.

## With `docker`

The following command will download an image containing `mist`, `fstar`,
and `mochi`, run the full `mist` test suite, and then drop you into an
interactive shell at the root of the `mist` code repository.

    $ docker run -it atondwal/mist

If you want to skip the test suite, instead run

    $ docker run -it atondwal/mist /bin/bash

You can then (re)run all of the tests in the `tests/` directory (perhaps after
editing some) at any time by running

    $ stack test

You can use `docker ps` to see the running container and open another shell to
it using `docker exec`, e.g.:

    $ docker ps
    CONTAINER ID        IMAGE               COMMAND                  CREATED             STATUS              PORTS               NAMES
    696b2221e3ad        atondwal/mist       "/usr/local/sbin/pid…"   9 minutes ago       Up 45 seconds                           vibrant_leavitt
    $ docker exec -it vibrant_leavitt bash
    ecoop21@696b2221e3ad:~/mist$ 

You can use `docker start` to restart exited containers

    $ docker ps -a
    CONTAINER ID        IMAGE               COMMAND                  CREATED             STATUS                       PORTS               NAMES
    696b2221e3ad        atondwal/mist       "/usr/local/sbin/pid…"   13 minutes ago      Exited (137) 5 seconds ago                       vibrant_leavitt
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

| Name          | Mist test                       | Mochi test               | Fstar test                    |
| ------------- | -------------------------       | -------                  | ----------                    |
| incr          | tests/pos/incr00.hs             | mochi-tests/incr00.ml    | fstar-tests/incr.fst          |
| sum           | tests/pos/sum.hs                | mochi-tests/sum.ml       | fstar-tests/sum.fst           |
| repeat        | tests/pos/repeat.hs             | mochi-tests/repeat.ml    | x                             |
| d2            | tests/pos/mochi-app-lin-ord2.hs | mochi-tests/d2.ml        | fstar-tests/mochi-d2.fst      |
|               |                                 |                          |                               |
| incrState     | tests/pos/incrStatePoly.hs      | mochi-tests/incrState.ml | fstar-tests/incrState.fst     |
| accessControl | tests/pos/acl.hs                | mochi-tests/acl.ml       | fstar-tests/accessControl.fst |
| tick          | tests/pos/tick-append.hs        | x                        | fstar-tests/tick.fst          |
| linearDSL     | tests/pos/linearTypes.hs        | x                        | fstar-tests/linearDSL.fst     |
|               |                                 |                          |                               |
| pagination    | tests/pos/paginationTokens.hs   | x                        | x                             |
| login         | tests/pos/idr_login.hs          | x                        | x                             |
| twophase      | tests/pos/twoPhaseCommit.hs     | x                        | x                             |
| ticktock      | tests/pos/ticktock3.hs          | x                        | x                             |
| tcp           | tests/pos/tcp_client.hs         | x                        | x                             |

As in the paper, an `x` indicates that the specification cannot be directly expressed with that tool.

N.B. We use the latest version of mochi, to give it the best chance of passing
the above case studies. However, while the latest version of mochi fails the
`d2.ml` test, while the version of mochi from the mochi paper passes it, so we
still mark it as passing in the paper.

# Writing Mist

(TODO)
