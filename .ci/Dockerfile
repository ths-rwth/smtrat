FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update -y ; apt-get install -y make texinfo time uuid-dev libboost-all-dev cmake flex bison ghostscript graphviz libclang-dev lmodern texinfo texlive texlive-font-utils texlive-latex-extra texlive-plain-generic python3-pip python3-setuptools doxygen doxygen-latex
RUN apt-get update -y ; apt-get install -y git libtool libgmp-dev python3 
RUN apt-get update -y ; apt-get install -y clang-14 clang-13 clang-12 clang-11 g++-12 g++-11 g++-10 g++-9 gcc-12 gcc-11 gcc-10 gcc-9
RUN apt-get update -y ; apt-get install -y imagemagick curl

RUN git config --global user.email "runner@ths.rwth-aachen.de"