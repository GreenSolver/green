---
title: Installation
permalink: /userguide/installation/
---

Green itself is relatively easy to install and use, but since it relies on external tools, it is often necessary to install additional software.

## Requirements

- [Java 8](https://www.oracle.com/technetwork/java/javase/downloads/jre8-downloads-2133155.html) or later JRE
- [Z3](#z3) (Optional)
- [LattE](#latte) (Optional)
- [barvinok](#barvinok) (Optional)

## Download Green

Download the ```green.jar``` file for the latest release of Green:

- [https://github.com/GreenSolver/green/releases/latest](https://github.com/GreenSolver/green/releases/latest)

Earlier releases are available at:

- [https://github.com/GreenSolver/green/releases](https://github.com/GreenSolver/green/releases)

Store the ```green.jar``` file in the Java class path of your application.

### Configuration

Green is set up by default to look for external applications in standard paths.  Each instance of Green can be configured as desired during its creation.  However, it may be convenient to pin down some settings that are not expected to change.  To do so, create a directory ```$HOME/.green``` and set the following properties in ```$HOME/.green/green.properties```:

~~~
green.latte.path = /usr/local/latte/bin/count
green.latte.args = --triangulation=cddlib

green.z3.path = /usr/local/bin/z3
green.z3.args = -smt2 -in
green.z3.lib = /usr/local/lib/

green.barvinok.path = /usr/local/barvinok/bin/barvinok_count
green.barvinok.args = 
~~~ 

More information about these and other settings can be found in [Configuration settings]({{ '//userguide/configuration/' | relative_url }}).
 
### Download with gradle

To build with Gradle, add the repository and dependency listed below to your ```build.gradle``` file.

~~~
repositories {
    maven { url 'http://repo.jacogeld.org:8081/artifactory/gradle-dev-local/' }
}

dependencies {
    compile group: 'za.ac.sun.cs', name: 'green', version: '0.1.5-SNAPSHOT'
}
~~~

## Additional tools

### barvinok

barvinok is a library for counting the number of integer points in parametric and non-parametric polytopes.

  - [```http://barvinok.gforge.inria.fr/```](http://barvinok.gforge.inria.fr/)

### LattE

LattE (Lattice point Enumeration) is a computer software dedicated to the problems of counting lattice points and integration inside convex polytopes.

  - [```https://www.math.ucdavis.edu/~latte/```](https://www.math.ucdavis.edu/~latte/)
  - [```https://github.com/latte-int/latte```](https://github.com/latte-int/latte)

For the latest information, consult the repository.  As of July 2019, the following instructions work on Linux:

~~~
$ wget https://github.com/latte-int/latte/releases/latest/download/latte-integrale-1.7.5.tar.gz
$ tar xf latte-integrale-1.7.5.tar.gz
$ cd latte-integrale-1.7.5/
$ ./configure --prefix=/usr/local
$ sudo make
~~~

### Z3

Z3 is an efficient SMT (Satisfiability Modulo Theories) solver with specialized algorithms for solving background theories.

  - [```https://github.com/Z3Prover/z3```](https://github.com/Z3Prover/z3)

For the latest information, consult the repository.  As of July 2019, the following instructions work on Linux:

~~~
$ git clone https://github.com/Z3Prover/z3.git
$ cd z3
$ python scripts/mk_make.py --java
$ cd build
$ make
$ sudo make install
~~~
