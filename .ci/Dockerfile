FROM ubuntu:latest

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update -y ; apt-get install -y make texinfo time uuid-dev libboost-all-dev cmake flex bison ghostscript libclang-13-dev lmodern texinfo texlive texlive-font-utils texlive-latex-extra texlive-plain-generic python3-pip python3-setuptools
RUN apt-get update -y ; apt-get install -y git libtool libgmp-dev python3 
RUN apt-get update -y ; apt-get install -y clang-14 clang-13 g++-12 g++-11 libc++-dev
RUN apt-get update -y ; apt-get install -y imagemagick curl libgtest-dev
RUN apt-get update -y ; apt-get install -y doxygen doxygen-doc doxygen-gui graphviz doxygen-latex libiconv-hook-dev doxygen-latex doxygen-doc doxygen-gui xapian-tools

RUN git config --global user.email "runner@ths.rwth-aachen.de"