FROM openjdk:8

MAINTAINER Phillip van Heerden <vanheerden.phillip@gmail.com>

# Update the system
RUN apt update -y
RUN apt upgrade -y

# Install ant, libgomp1 (GCC OpenMP support library), vim, patchelf, and tmux.
# These should be available on the NARGA machines.
RUN apt install ant -y
RUN apt install vim -y
RUN apt install tmux -y
RUN apt install patchelf -y
RUN apt install libgomp1

# Clone down the GreenSolver repository
RUN git clone https://github.com/FloraJuliane/green

# Download and extract Z3
RUN mkdir z3
WORKDIR z3
RUN wget https://github.com/Z3Prover/z3/releases/download/z3-4.7.1/z3-4.7.1-x64-ubuntu-16.04.zip
RUN unzip z3-4.7.1-x64-ubuntu-16.04.zip

# Fix the link time error with libz3java.so
WORKDIR /z3/z3-4.7.1-x64-ubuntu-16.04/bin
RUN patchelf --set-rpath '.:$ORIGIN' libz3java.so

# Make the z3 path a bit easier for sed
WORKDIR /z3/
RUN mv z3-4.7.1-x64-ubuntu-16.04/ z3/

# Update the build.properties file with the new z3 paths
WORKDIR /green/
RUN sed -i '16s/.*/z3path = \/z3\/z3\/bin\/z3/' build.properties
RUN sed -i '17s/.*/z3lib = \/z3\/z3\/bin/' build.properties
