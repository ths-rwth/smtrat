FROM ubuntu:24.04 AS base
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update && \
    apt-get -y --no-install-recommends install \
        cmake \
        make \
        g++-12 \
        git \
        patch \
        libgmp3-dev \
        libeigen3-dev \
        libboost-all-dev \
        ca-certificates \
        libtool \
        python3 \
        build-essential \
        wget \
        unzip \
        time

# Stage for building all variants
FROM base AS build-smtrat
RUN wget https://zenodo.org/records/15464618/files/ths-rwth/carl-25.04.zip \
    && unzip carl-25.04.zip \
    && mv ths-rwth-carl-0aa6abe /carl
WORKDIR /carl/build
RUN cmake -D CMAKE_CXX_COMPILER=g++-12 .. && make libs

WORKDIR /
COPY . /smtrat
WORKDIR /smtrat/build/

RUN mkdir /tools
RUN for s in "Default" "OptQE" "OptPlus"; do \
        cmake -D CMAKE_CXX_COMPILER=g++-12 -D SMTRAT_DEVOPTION_Statistics=ON -D SMTRAT_Strategy=CoveringNG/$s .. && \
        make smtrat-static && \
        mv smtrat-static /tools/$s; \
        done
RUN mv /tools/Default /tools/CAlC-Opt \
    && mv /tools/OptQE /tools/CAlC-QE \
    && mv /tools/OptPlus /tools/CAlC-Opt-Plus

# Final stage
FROM ubuntu:24.04
WORKDIR /
ARG DEBIAN_FRONTEND=noninteractive
COPY --from=build-smtrat /tools .