FROM ubuntu:20.04

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update -y ; apt-get install -y make texinfo time uuid-dev libboost-all-dev cmake flex bison ghostscript graphviz libclang-7-dev lmodern texinfo texlive texlive-font-utils texlive-latex-extra texlive-plain-generic python3-pip python3-setuptools gcc-10 gcc-9 gcc-8 doxygen doxygen-latex
RUN apt-get update -y ; apt-get install -y git libtool libgmp-dev python3 
RUN apt-get update -y ; apt-get install -y clang-11 clang-10 clang-9 g++-10 g++-9 g++-8
RUN apt-get update -y ; apt-get install -y imagemagick curl

RUN git config --global user.email "runner@ths.rwth-aachen.de"