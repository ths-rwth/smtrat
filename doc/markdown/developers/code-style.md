## Code style {#code-style}

### Code formatting

[ClangFormat](https://clang.llvm.org/docs/ClangFormat.html) allows to define code style rules and format source files automatically.
A `.clang-format` file is provided with the repository. Please use this file to format all sources.

### Naming conventions

For all new code, the following rules apply.

* type names and template parameter: `CamelCase`
* variable and function names: `snake_case`
* compiler macros and defines: `ALL_UPPERCASE`
* enum values: `UPPERCASE`
* (private) class members: start with `m_` respectively `mp_` for pointers and `mr_ ` for references 

### Headers and namespaces 

The following conventions apply for new modules added to SMT-RAT and CArL. When adding code to existing structures, be consistent with existing code.

* Every file should represent a *module*.
* Every (sub-)folder has its own namespace.
* Namespaces and modules have names in `camel_case`.

### C++ features

* As of now, please stick to C++17 features.
* Use `enum class` instead of `enum`.