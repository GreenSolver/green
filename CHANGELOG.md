# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added
- Identity service
  [7e76bd0](https://github.com/GreenSolver/green/commit/7e76bd0d9c979ed134ecbdcd75a9f688049d0305)
- Logging & tests
  [bcf2d41](https://github.com/GreenSolver/green/commit/bcf2d41ae04cdfca5932e954a2465e71c972bde5)
  [598251d](https://github.com/GreenSolver/green/commit/598251d6066dd5faae56d5f79879d8aaec010447)
  [66da1cf](https://github.com/GreenSolver/green/commit/66da1cf8349cdb6b7df9906404e1e8bc6fb3f5f5)
  [9e12088](https://github.com/GreenSolver/green/commit/9e120880a790d75bf0e37310a0cf1e62c27c2bb9)

### Changed
- Counting of invocations for some services
  [b5d675a](https://github.com/GreenSolver/green/commit/b5d675ace072ea81b65db6af29b185c958fe24e1)

### Deprecated
- ...

### Removed
- Defunct factorization code
  [c110699](https://github.com/GreenSolver/green/commit/c11069962bfb183752548d1ca4adc7cd8972a1ca)

### Fixed
- Choco translation, [Issue #27](https://github.com/GreenSolver/green/issues/27)
  [6124445](https://github.com/GreenSolver/green/commit/61244457a9360ad87e9a28ae6ba3fa827b523333)
  [bcf2d41](https://github.com/GreenSolver/green/commit/bcf2d41ae04cdfca5932e954a2465e71c972bde5)
- Factorization for newer model / model-core return values
  [c110699](https://github.com/GreenSolver/green/commit/c11069962bfb183752548d1ca4adc7cd8972a1ca)

## [0.2.0] - 2019.07.12

### Added
- Grulia service.  This includes limited support for bitvectors.
  [aa0ca72](https://github.com/GreenSolver/green/commit/aa0ca72b842dc270c10d4fdc2ef5aa2aecffd1f2)
  [d69c1fb](https://github.com/GreenSolver/green/commit/d69c1fbbf9ccb92d3766c4efd1b9777053e531cb)
  [5c3de1f](https://github.com/GreenSolver/green/commit/5c3de1f1418ccbcba3a6fa8a3baa678da9979438)
  [916c4a4](https://github.com/GreenSolver/green/commit/916c4a4a8d14005023cdea35200a7fdf2772ea05)
  [9b07c16](https://github.com/GreenSolver/green/commit/9b07c162ddf783d1a55d4757a692012610ffcfbc)
  [b476770](https://github.com/GreenSolver/green/commit/b476770d5cecccb554b8e45e58053e2c02425dcc)
  [2a0099d](https://github.com/GreenSolver/green/commit/2a0099da943aeca6e59ae18e176a34fda8cf9979)
  [d69cb26](https://github.com/GreenSolver/green/commit/d69cb2614bd278c518b05f6b7ea5b89841cd16e5)
  [fa1e810](https://github.com/GreenSolver/green/commit/fa1e81082c1924dfff5424299c0ca33fc4d0bb46)
  [643db1c](https://github.com/GreenSolver/green/commit/643db1cd04754fa1f11e1597ffbd2f711818ba76)
  [8086cba](https://github.com/GreenSolver/green/commit/8086cbaa647213f62ad5535edbbc0f5e4eb784ed)
  [454c73a](https://github.com/GreenSolver/green/commit/454c73ac6e39699ca814fcf4ca4d40c17727a0a3)
  [048f9ff](https://github.com/GreenSolver/green/commit/048f9ffec4833563a7df05a842666eb4792f5192)
  [c515a70](https://github.com/GreenSolver/green/commit/c515a70aae91b0bed6bfb157ebf24f37318bc128)
  [4fe7cf1](https://github.com/GreenSolver/green/commit/4fe7cf1e4c0308d126e04e2622b806523948274f)
  [e23054a](https://github.com/GreenSolver/green/commit/e23054ae92021c8f2359b57fffa9f13d798ae04c)
  [0eed58c](https://github.com/GreenSolver/green/commit/0eed58c74e8abdbe8523f7e0109fe3817dc586d3)
  [659a5d4](https://github.com/GreenSolver/green/commit/659a5d451f8601696fb37a25c7c9c54ce4847fbc)
  [0308ea5](https://github.com/GreenSolver/green/commit/0308ea5fee95974a166f9bb997bca864fac58ff2)
  [2e5ff9b](https://github.com/GreenSolver/green/commit/2e5ff9b86242d72a06a57c41efff81c5cc109556)
  [75c3690](https://github.com/GreenSolver/green/commit/75c36904bb983c7453d7502837490a8feff53c21)
  [e807e53](https://github.com/GreenSolver/green/commit/e807e53e0d2b039cd1b72a328b9c094fe8b93ad7)
  [b4feb5d](https://github.com/GreenSolver/green/commit/b4feb5d4d3beb357c1b6b9ed619ae503df56a49b)
  [73be4b3](https://github.com/GreenSolver/green/commit/73be4b3e29efdb8e8bf27cb5e7fde1f421d76bb2)
  [0dc704b](https://github.com/GreenSolver/green/commit/0dc704b0a6b1d26fbbce3faf2f5d5a6ada6e3258)
  [f7471c1](https://github.com/GreenSolver/green/commit/f7471c1a3ef776c5d8e23e9efd326c4c048428d9)
  [7ecb37a](https://github.com/GreenSolver/green/commit/7ecb37a032eac792885760eb92e3847dca1fe440)
  [f9c6e74](https://github.com/GreenSolver/green/commit/f9c6e740155df088581f6a50aac08cf6460fe9e8)
  [42efce9](https://github.com/GreenSolver/green/commit/42efce9ac576bde5ec3d6400853b9d056a5faa3d)
  [99ae46b](https://github.com/GreenSolver/green/commit/99ae46b09e682df9b84bdd317875d3c475d54ed7)
  [9e3f213](https://github.com/GreenSolver/green/commit/9e3f213e00b9fe8d2470c82966fbd3948de4d052)
  [4caa21d](https://github.com/GreenSolver/green/commit/4caa21d41c071f051fb87f364d012780f2adfc1c)
  [7fe1dcf](https://github.com/GreenSolver/green/commit/7fe1dcf76cc6d567ea89f8ce963d4dc237293fe7)
  [aa547b0](https://github.com/GreenSolver/green/commit/aa547b041bdba0e972857bb2e1ab80c33a48db93)
- Add checkstyle to check code style
  [39ac95d](https://github.com/GreenSolver/green/commit/39ac95dec5f4aebe285f291bb6834838b4783cea)
- Barvinok service
  [bb68816](https://github.com/GreenSolver/green/commit/bb688162f3167bd09eb486905b4ea928cd61c5ad)
  [775fa1c](https://github.com/GreenSolver/green/commit/775fa1c47f20d0d3add1debc063157e5ec679931)
  [6505fb8](https://github.com/GreenSolver/green/commit/6505fb882762936ec52604e428e5aa2755b653a8)
  [fb6de5b](https://github.com/GreenSolver/green/commit/fb6de5bd9a5ed539008d545fdd0aa420397fd2b8)
  [886ec19](https://github.com/GreenSolver/green/commit/886ec19a236887d5bcfc4d9633f1108feb456398)
  [f678298](https://github.com/GreenSolver/green/commit/f678298a807c2f4ce36a524f066bac64437af308)
  [303928e](https://github.com/GreenSolver/green/commit/303928ed5f9e4f54b7a42dfe1c205da28a536101)
  [c8825e0](https://github.com/GreenSolver/green/commit/c8825e0687642a8dc99d4984c7106dc10a5c8f67)
  [490ed79](https://github.com/GreenSolver/green/commit/490ed7989e4075bad25d7ef1ff9a637c5f9b1463)
  [33a1d50](https://github.com/GreenSolver/green/commit/33a1d50b8557d84087f25e93419ff40ffa104ac0)
  [96ff55f](https://github.com/GreenSolver/green/commit/96ff55f23e7e24bd92d6f47d23c58618dc89f066)
- Memory store
  [e268c84](https://github.com/GreenSolver/green/commit/e268c84fee2d6fccad2fa3e5d037c524f6740079)
  [1090678](https://github.com/GreenSolver/green/commit/1090678ce04d2c845e7af83a9513335691b1e81e)
  [2395a85](https://github.com/GreenSolver/green/commit/2395a85cb64f2bc70e3794d691dd76eae851a8d8)
  [a745e92](https://github.com/GreenSolver/green/commit/a745e923c581243cb05414df0deab85681f9c001)
  [97efc9c](https://github.com/GreenSolver/green/commit/97efc9c463db86a10c28e60791ea4214ab9a171a)
  [d4d1e92](https://github.com/GreenSolver/green/commit/d4d1e92f8ce40707aeb2bd3c64148398fb17151e)
- Caching of ```toString()''' computations
- Add coverage measurement for tests
  [7fa2fe2](https://github.com/GreenSolver/green/commit/7fa2fe251e7983afd8b1d7d213d616efbe3933b9)

### Changed
- Gradle now releases successfully on the maven central repository.
  [2d381c6](https://github.com/GreenSolver/green/commit/2d381c625188517f359a443c17753e05e7d519d6)
  [c3968fa](https://github.com/GreenSolver/green/commit/c3968fa633142c1f7d843c80f122b5694f176bb0)
  [ce44175](https://github.com/GreenSolver/green/commit/ce441755a7dab7448176ac79fae99d4469c3da99)
  [e0ffab4](https://github.com/GreenSolver/green/commit/e0ffab491b72a1539acf86753618aa8022490410)
  [fcde541](https://github.com/GreenSolver/green/commit/fcde54173f31a5f6b73784d4e7608125a3aba25b)
- Cleanup Z3 services
  [826ac0e](https://github.com/GreenSolver/green/commit/826ac0e252cfa625efabed1160179c9eb4cce8f5)
  [bd66789](https://github.com/GreenSolver/green/commit/bd667890b84a95837988af3f1a3f399270152fda)
  [633c2e2](https://github.com/GreenSolver/green/commit/633c2e249e2a0b5a11416080d8990953632c8dbd)
  [c6567fd](https://github.com/GreenSolver/green/commit/c6567fdd09555f3036d5cbf2f24da069fca2a627)
  [ead5dae](https://github.com/GreenSolver/green/commit/ead5daecc63c36a149c33f7e56031c830e163f19)
  [c9f080d](https://github.com/GreenSolver/green/commit/c9f080d2a381307da8e85b9512c02884c049b784)
  [8cce0a1](https://github.com/GreenSolver/green/commit/8cce0a1a9208821cb2978eba3fc1c87189b7a7fa)
  [e627241](https://github.com/GreenSolver/green/commit/e6272413cfd81f5064ac6626d1d68cbe43f3efc9)
  [47c31da](https://github.com/GreenSolver/green/commit/47c31da9dd1b2317265fc66e21dbef07b0375e78)
  [d15c8c6](https://github.com/GreenSolver/green/commit/d15c8c602f9d285f1dcb56b81b35692e65066917)
  [ef0e2c1](https://github.com/GreenSolver/green/commit/ef0e2c18e3f32229345d40edb73fe3f766d9ae80)
- Reporting infrastructures
  [36305c8](https://github.com/GreenSolver/green/commit/36305c8c4b21d9c1dd7447d49ca6a198e7950f5f)
  [662e7fb](https://github.com/GreenSolver/green/commit/662e7fbe95d3a36e97a13e4b15fb8e4faafb0e99)
  [8980fbf](https://github.com/GreenSolver/green/commit/8980fbf4b7b9ae4184ff03a8777a37856ea9772a)
  [c28fcc2](https://github.com/GreenSolver/green/commit/c28fcc2993df1db352c915a7bfa244210df89e11)
  [d56e569](https://github.com/GreenSolver/green/commit/d56e5697449d30bbbbd47509ec6cec09d2dbbb4a)
  [a669d41](https://github.com/GreenSolver/green/commit/a669d41733817590f53ab22e9b918f1c4fe2a47d)
  [f8d3d18](https://github.com/GreenSolver/green/commit/f8d3d18fa3c244504215288903ef40b9ff04526f)
  [001589d](https://github.com/GreenSolver/green/commit/001589df7f16bb44751720e4fd976b1522b1d024)
  [eddcdeb](https://github.com/GreenSolver/green/commit/eddcdebb45e2856efbf7d4612c38e74cb6c2df49)
  [6e97786](https://github.com/GreenSolver/green/commit/6e97786ec12b570182448fa4f4a73bfa2820bc69)
  [df3f634](https://github.com/GreenSolver/green/commit/df3f6346fbadbc098c6201e20ab4b37fa6659fdd)
- Improve logging
  [d3836f4](https://github.com/GreenSolver/green/commit/d3836f4c9f1fd5ad3d5f32e5d1141e71f8eb3053)
- Improve factorizer
  [a834985](https://github.com/GreenSolver/green/commit/a834985ccfe8636afbd86d2c3118c2faa13417e8)
  [2aafe47](https://github.com/GreenSolver/green/commit/2aafe47fc3e55f447f0a5f1cda07bff5ed596fda)
  [bf04149](https://github.com/GreenSolver/green/commit/bf04149aa6df79b218bf587b1f36a6d351d0b1b2)
- Improved renaming service
  [428313f](https://github.com/GreenSolver/green/commit/428313fb2a085cf6f8f01e207bbd7ef61ed8ea67)
- Comments
  [b5f327d](https://github.com/GreenSolver/green/commit/b5f327df02cf24d6095ea61fc1011f92c872283a)
  [d783e9a](https://github.com/GreenSolver/green/commit/d783e9aa563885914fa7822036df18f066469e26)
- Reorganization of build properties
- Improve Dockerfile for testing (continuous integration)
  [dae9a38](https://github.com/GreenSolver/green/commit/dae9a38209e664e97c6c6936b9c42ae5532dcbcb)
  [5fc5731](https://github.com/GreenSolver/green/commit/5fc5731625d51c29d695d17531cce4655ec72bda)
  [358628d](https://github.com/GreenSolver/green/commit/358628d43175f61aebd383012560b05d93a20653)
  [277a48e](https://github.com/GreenSolver/green/commit/277a48e57138a0eed9bc25bc692c474c3a5edd17)
  [6af5436](https://github.com/GreenSolver/green/commit/6af5436b566468e9765cdbb20a4cd767e06eccdb)
  [55ba810](https://github.com/GreenSolver/green/commit/55ba81016f8976c962fd2ec67ee6d13d76bc518b)
  [8515c61](https://github.com/GreenSolver/green/commit/8515c61f8d9f74336c5d9c53c27a07f73f6ab7ad)
  [fb825f1](https://github.com/GreenSolver/green/commit/fb825f11b0f7aed5e0a4a13a7bbcea121b0fad16)
  [1eab491](https://github.com/GreenSolver/green/commit/1eab491ff19d28e0b1dda00675ba7ac90a0b702c)
  [9faef9c](https://github.com/GreenSolver/green/commit/9faef9cbb8b9922a86884d8a78c3f3b9622afc85)
  [c7780bd](https://github.com/GreenSolver/green/commit/c7780bd1b1dd0bffe46836e1fa86f078a6eacda1)
  [ac8190f](https://github.com/GreenSolver/green/commit/ac8190fa286d615d220ac3064b48fdc5f74904e1)
  [59c4572](https://github.com/GreenSolver/green/commit/59c45727afbab9dfca457ebb9191874f57b889fd)
  [e68e64c](https://github.com/GreenSolver/green/commit/e68e64c0467fcda6e1b16dba531653b47c83611b)
  [4b645c4](https://github.com/GreenSolver/green/commit/4b645c4c902bba0ce45e01f594321530920f9111)
  [ea9ac39](https://github.com/GreenSolver/green/commit/ea9ac39ef49794d926d5734e8953070b3b235011)
  [842778a](https://github.com/GreenSolver/green/commit/842778a5ff375413148e87568e1d231c1396f83c)
  [5bb6b79](https://github.com/GreenSolver/green/commit/5bb6b79bda49f4b09ed95427728467ea161e4fb4)
  [92795f4](https://github.com/GreenSolver/green/commit/92795f41ac462fbe9c2d82f2d64a783bd6973f54)
  [79fc507](https://github.com/GreenSolver/green/commit/79fc5079360fd7abf05adda8b75428580d4c4394)
  [272eb7f](https://github.com/GreenSolver/green/commit/272eb7f29fd234d4dde27e8a3e7712d270d7cea9)
  [810afd5](https://github.com/GreenSolver/green/commit/810afd51590aa0cbd5541faf232ab1e185e2dada)
  [f2f1a15](https://github.com/GreenSolver/green/commit/f2f1a15d47c9296fd9a740fe6110cf5de98ee516)
  [7ba3dc2](https://github.com/GreenSolver/green/commit/7ba3dc2a7e4d2788c16fee7e189b4739797ba9e8)

### Fixed
- Style errors
  [4c30610](https://github.com/GreenSolver/green/commit/4c306106c848694fc237d9ea4ef84a2b630d3859)
- Fix some broken test code
  [497e6fa](https://github.com/GreenSolver/green/commit/497e6fa4cf8a2ff931d1c93400bf2c557047bd60)
  [de1f2f5](https://github.com/GreenSolver/green/commit/de1f2f5f523ef1c7832262959212809912deafa1)
- ```hashCode()''' bug
  [3c7afae](https://github.com/GreenSolver/green/commit/3c7afae9b993d6c20adffff13104299c64fe0f96)


## [0.1.7] - 2018.12.17

### Changed
- Improved support for real constraints [371ec58](https://github.com/GreenSolver/green/commit/371ec58ec7149ace312007b9fe1f9bb6b7b73787)


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
