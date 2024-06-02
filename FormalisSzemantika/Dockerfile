FROM ubuntu:latest

ARG OCAML_VERSION=4.14.2
ARG COQ_VERSION=8.18.0

RUN apt-get update -y \
    && DEBIAN_FRONTEND=noninteractive apt-get install -y ocaml opam libgmp-dev \
    && yes | opam init --disable-sandboxing --bare

RUN opam switch create ${OCAML_VERSION} --yes

RUN eval $(opam env) \
    opam repo add coq-released https://coq.inria.fr/opam/released \
    && opam pin add coq ${COQ_VERSION} --yes \
    && opam install vscoq-language-server --yes




