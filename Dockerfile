FROM ubuntu:latest as lib-base
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update && \
    apt-get -y --no-install-recommends install \
        cmake \
        make \
        clang \
        g++ \
        git \
        patch \
        libgmp3-dev \
        libeigen3-dev \
        libboost-all-dev \
        ca-certificates

FROM lib-base as builder
COPY . /smtrat-src/
WORKDIR /smtrat-src/build/
RUN cmake -D USE_MIMALLOC=ON ..
RUN make mimalloc-EP
RUN make smtrat-static
WORKDIR /smtrat-src/

FROM builder as smtrat
ENV LD_PRELOAD=/smtrat-src/resources/lib/mimalloc-1.6/libmimalloc.so
ENTRYPOINT [ "/smtrat-src/build/smtrat-static" ]