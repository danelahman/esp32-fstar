# Examples of ESP32 applications written and verified in F\*, and extracted to C

This repository contains examples of ESP32 microcontroller applications
written and verified (for memory safety and functional correctness) in 
the Low* subset of the F\* language, which are then extracted to low-level
C code, and compiled and flashed to ESP32.

## Prerequisites

To verify, extract, compile, and flash the examples in this repository, 
you need the following software:

* [F\* language](https://github.com/FStarLang/FStar)

  Tested with Github commit version a21ad970d2d2aad8d6b2c455cab97b8f71c18285

* [fstar-mode](https://github.com/FStarLang/fstar-mode.el)

  Tested with Github commit version 3afbf04e4eb21af950cfdb727d8b808164fd9415

* [KreMLin F\* to C extraction tool](https://github.com/FStarLang/kremlin)

  Tested with Github commit version c113d20b84a55dd1ba60c86c1502f2c49459b645

* [Espressif IoT Development Framework](https://github.com/espressif/esp-idf)

  Tested with version v4.3-dev-1901-g178b122c1

* [FTDI Drivers](https://learn.sparkfun.com/tutorials/how-to-install-ftdi-drivers)

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

  * `esp/main/`: directory to where we copy all the C source code for compilation

    * `esp/main/CMakeLists.txt`: list of C source files for esp-idf to compile

  * `esp/CMakeLists.txt`: esp-idf project configuration

  * `esp/Makefile`: esp-idf project makefile

* `src/`: F\* source code directory

  * `src/c/`: manually written C code specific to each individual example application

  * `src/Makefile`: makefile including the paths used by F\* Emacs mode

* `Makefile`: project's top-level main makefile (includes targets `extract`, `compile`, `flash`, and `clean`)

* `Makefile.include`: makefile including the paths used by F\* Emacs mode

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