## Finding and Reporting Bugs {#bugs}

This page is meant as a guide for the case that you find a bug or any unexpected behaviour.
We consider any of the following events a (potential) bug:
- SMT-RAT crashes.
- A library used through SMT-RAT crashes.
- SMT-RAT gives incorrect results.
- SMT-RAT does not terminate (for reasonably sized inputs).
- SMT-RAT does not provide a method or functionality that should be available according to this documentation.
- SMT-RAT does not provide a method or functionality that you consider crucial or trivial for some of the datastructures.
- Compiling SMT-RAT fails.
- Compiling your code using SMT-RAT fails and you are pretty sure that you use SMT-RAT according to this documentation.

In any of the above cases, make sure that:
- You have installed all necessary @ref dependencies in the required versions.
- You work on something that is similar to a system listed as supported platform at @ref getting_started.
- You can (somewhat reliably) reproduce the error with a (somewhat) clean build of SMT-RAT. (i.e., you did not screw up the CMake flags, see @ref build_cmake for more information)
- You compile either with `CMAKE_BUILD_TYPE=DEBUG` or `DEVELOPER=ON`. This will give additional warnings during compilation and enable assertions during runtime. This will slow down SMT-RAT significantly, but detect errors before an actual crash happens and give a meaningful error message in many cases.

If you are unable to solve issue yourself or you find the issue to be an actual bug in SMT-RAT, please do not hesitate to contact us.
You can either contact us via email (if you suspect a configuration or usage issue on your side) or create a ticket in our bug tracker (if you suspect an error that is to be fixed by us).
The bug tracker is available at https://github.com/ths-rwth/smtrat/issues.

When sending us a mail or creating a ticket, please provide us with:
- Your system specifications, including versions of compilers and libraries listed in the dependencies.
- The SMT-RAT version (release version of git commit id).
- A minimal working example.
- A description of what you would expect to happen.
- A description of what actually happens.
