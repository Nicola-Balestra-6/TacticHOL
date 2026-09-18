# The environment of the README, built once: Ubuntu 22.04, HOL Light at
# the named commit with its local opam switch (OCaml 5.2.0, Camlp5
# 8.03.06), and the three opam packages TacticHOL needs. The image holds
# HOL Light in /root/hol-light; devcontainer.json mounts this directory
# at /root/hol-light/TacticHOL, where the scripts expect it. The corpus
# is not built here: see README, "1. Build the corpus".

FROM ubuntu:22.04
ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y \
    bubblewrap build-essential ca-certificates curl git libgmp-dev \
    libpcre2-dev m4 opam patch pkg-config python3 rsync unzip

ARG HOL_LIGHT_COMMIT=157c99b7
WORKDIR /root
RUN git clone https://github.com/jrh13/hol-light.git \
 && cd hol-light && git checkout "$HOL_LIGHT_COMMIT"

# The switch must be active when make runs: make copies the
# update_database.ml variant of the OCaml it finds and does not rebuild
# it. The last line checks that the OCaml 5 variant was taken.
WORKDIR /root/hol-light
RUN opam init --disable-sandboxing -y \
 && OPAMCONFIRMLEVEL=unsafe-yes make switch-5 \
 && eval "$(opam env)" \
 && make \
 && test "$(sha1sum update_database.ml | cut -c1-8)" = 1dc116fc \
 && opam install -y dune yojson menhir

WORKDIR /root/hol-light/TacticHOL
