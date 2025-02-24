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
RUN wget https://zenodo.org/records/14900072/files/ths-rwth/carl-25.02.zip \
    && unzip carl-25.02.zip \
    && mv ths-rwth-carl-2156a73 /carl
WORKDIR /carl/build
RUN cmake -D CMAKE_CXX_COMPILER=g++-12 .. && make libs

WORKDIR /
COPY . /smtrat
WORKDIR /smtrat/build/
RUN mkdir /tools
RUN for s in "Baseline" "Simple3" "Simple4" "Simple5" "Simple6" "Dynamic" "PWL2" "PWL4" "PWL6" "Taylor" "Outside"; do \
        cmake -D CMAKE_CXX_COMPILER=g++-12 -D SMTRAT_DEVOPTION_Statistics=ON -D SMTRAT_Strategy=Approximation/$s .. && \
        make smtrat-static && \
        mv smtrat-static /tools/$s; \
        done
RUN mv /tools/Simple3 /tools/Simple-3 \
    && mv /tools/Simple4 /tools/Simple-4 \
    && mv /tools/Simple5 /tools/Simple-5 \
    && mv /tools/Simple6 /tools/Simple-6 \
    && mv /tools/PWL2 /tools/PWL-2 \
    && mv /tools/PWL4 /tools/PWL-4 \
    && mv /tools/PWL6 /tools/PWL-6 

# Final stage
FROM ubuntu:24.04
WORKDIR /
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update && \
    apt-get -y --no-install-recommends install \
        python3 \
        python3-pandas \
        unzip \
        time
COPY artifact /artifact
COPY --from=build-smtrat /tools /artifact/tools
WORKDIR /artifact/
RUN unzip QF_NRA.zip