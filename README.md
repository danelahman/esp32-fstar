# Examples of ESP32 applications written and verified in F\*, and extracted to C

This repository contains examples of simple [ESP32
SoC](https://www.espressif.com/en/products/socs/esp32) applications
written and verified (currently, for memory safety and functional
correctness) in the [Low*](http://dx.doi.org/10.1145/3110261) subset
of the dependently typed language [F\*](http://fstar-lang.org), and
then extracted to C code, and compiled and flashed to ESP32.

The purpose of these examples is to demonstrate how one can use the
F\* language to *incrementally* develop, specify, verify, extract, and
compile low-level embedded code. In particular, we are only importing
(via specifying corresponding F\* interfaces) those parts of the ESP32
development framework that are needed for writing specific examples.

**Note:** These examples are programmed against the [SparkFun ESP32
Thing](https://www.sparkfun.com/products/13907) development board, and
its pin layout for buttons and LEDs. For other ESP32 boards, you might
need to change which pins are used for specific buttons, LEDs, etc.

## Prerequisites

To verify, extract, compile, and flash the examples in this
repository, you need to install the following software:

* [F\* language](https://github.com/FStarLang/FStar)

  Tested with Github commit version 9086005cb5129dc6d5667214586f2df902bddddd (tag v2022.07.13)
  
  *Note:* For building F\* v2022.07.13, the `opam` package `ppxlib`
  package cannot be newer than version 0.25.1, see also [this
  issue](https://github.com/FStarLang/FStar/issues/2681).

* Emacs and [fstar-mode](https://github.com/FStarLang/fstar-mode.el)

  Tested with Github commit version 60489e75c6f26417068bf861b6db2935e72c38fe (version 20220725.2139)

* [KaRaMeL F\* to C extraction tool](https://github.com/FStarLang/karamel)

  Tested with Github commit version 6dd219f468907553b65cda0cdb094eae849cf773 (Nov 2 2022)

* [Espressif IoT Development Framework](https://github.com/espressif/esp-idf)

  Tested with Github commit version 63091bdf8d118f0e0c4e4424ee7a90f3d58ac6e5 (tag v4.3.4)

* [FTDI Drivers](https://learn.sparkfun.com/tutorials/how-to-install-ftdi-drivers)

  Tested with v1.5.0 for Mac OS X10.15 and macOS 11/12.

## User-specific settings

Once you have installed all the above-mentioned software (using the
tested versions) as per the corresponding instructions, the only
user-specific settings you should need to set are the `ESP_IDF` and
`ESP_PORT` paths in the top-level `Makefile.include` file.

Also, pay attention that both F\* and KaRaMeL binaries are your path,
and that the `FSTAR_HOME` and `KRML_HOME` environment variables are
set and pointing to the F\* and KaRaMeL directories, respectively.

## Structure of the repository

This repository contains two top-level directories:

* `examples/`: contains example applications in separate sub-directories

* `lib/`: contains (F\* and C) library files used across the examples

  * `lib/c/`: contains manually written C code for the F\* code we do
    not extract (mostly assumed interfaces concerning the existing ESP
    and GPIO libraries, and libraries for features such as void pointers)

Each example application has the following general directory structure:

* `dist/`: output of extracting F\* code to C code

* `esp/`: build directory for the esp-idf framework

  * `esp/main/`: directory to where we copy all the C source code for
    compilation

    * `esp/main/CMakeLists.txt`: list of C source files for esp-idf to
      compile

  * `esp/CMakeLists.txt`: esp-idf project configuration

  * `esp/Makefile`: esp-idf project makefile

* `src/`: F\* source code directory

  * `src/c/`: manually written C code specific to each individual
    example application

  * `src/Makefile`: makefile including the paths used by F\* Emacs mode

* `Makefile`: project's top-level main makefile (includes targets
  `extract`, `compile`, `flash`, and `clean`)

* `Makefile.include`: makefile including the paths used by F\* Emacs mode

## Typechecking, extracting, and compiling the examples

In the root folder of the each example (`examples/foo`), you can type

* `make extract` to typecheck the example in F* and extract it to C
* `make compile` to compile the extracted C code into ESP32 binary
* `make flash` to flash the compiled code onto an ESP32 SoC
* `make` to do all the above

In the root folder of the repository, you can type

* `make` to execute `make extract` and `make compile` for each example
  
## F\*'s Emacs mode configuration

To make F\*'s Emacs mode pick up the include paths from makefiles, add the
following code to your `~/.emacs` configuration file: 

```
(defun my-fstar-compute-prover-args-using-make ()
 "Construct arguments to pass to F* by calling make."
 (with-demoted-errors "Error when constructing arg string: %S"
   (let* ((fname (file-name-nondirectory buffer-file-name))
          (target (concat fname "-in"))
          (argstr (condition-case nil
                      (car (process-lines "make" "--quiet" target))
                    (error "--use_hints"))))
     (split-string argstr))))

(setq fstar-subp-prover-args #'my-fstar-compute-prover-args-using-make)
```
