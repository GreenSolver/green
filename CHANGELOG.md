# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added
- ...

### Changed
- ...

### Deprecated
- ...

### Removed
- ...

### Fixed
- ...


## [0.1.6] - 2018.12.16

### Added
- Support for 64-bit integer constants and variables [fc2b03b](https://github.com/GreenSolver/green/commit/fc2b03bbb3b1e40f5c934644dc3f4b113f0519f4)


## [0.1.5] - 2018.12.12

### Added
- Support for real variables and constants in SMTLIB


## [0.1.4] - 2018.12.05

### Added
- The log level is now read from the configuration
- More timing information is collected and displayed (SATService, SATCanonizerService, SATFactorizerService, RedisStore)
- New in-memory store
- New redis client that operates asynchronously

### Fixed
- Z3 processes are now killed after the complete their work


## [0.1.3] - 2018.07.17

### Added
- Model-only command-line Z3 service



## [0.1.2] - 2018.07.17

### Fixed
- gradle.properties problem that preventer maven publication.



## [0.1.1] - 2018.07.17

### Fixed
- Maven publication needed a group name in the build.gradle.



## [0.1.0] - 2018.07.17

First version after switching to gradle and publishing on github.

### Added
- New tests for CNF factoriser
- Added Travis support (probably broken after merge of pull request)
- More support for OR operator

### Changed
- Merge pull request from JHTaljaard to switch to gradle
