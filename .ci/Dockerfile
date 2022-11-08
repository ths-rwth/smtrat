FROM ubuntu:latest

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update -y ; apt-get install -y make texinfo time uuid-dev libboost-all-dev cmake flex bison ghostscript libclang-13-dev lmodern texinfo texlive texlive-font-utils texlive-latex-extra texlive-plain-generic python3-pip python3-setuptools
RUN apt-get update -y ; apt-get install -y git libtool libgmp-dev python3 
RUN apt-get update -y ; apt-get install -y clang-13 clang-12 g++-12 g++-11
RUN apt-get update -y ; apt-get install -y imagemagick curl
RUN apt-get update -y ; apt-get install -y doxygen doxygen-doc doxygen-gui graphviz doxygen-latex libiconv-hook-dev doxygen-latex doxygen-doc doxygen-gui xapian-tools

RUN git config --global user.email "runner@ths.rwth-aachen.de"