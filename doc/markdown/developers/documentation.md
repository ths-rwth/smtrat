## Documentation {#documentation}

For SMT-RAT, there are two sources of documentation: the in-source API documentation and the more manual-like documentation (you are reading right now).
While the in-source API documentation is generated based on the doxygen comments from the actual source files, the manual is generated from the markdown files in `doc/markdown/`.

### Writing documentation

Note that some of the documentation may be incomplete or rendered incorrectly, especially if you use an old version of doxygen. Here is a list of known problems:
- Comments in code blocks (see below) may not work correctly (e.g. with doxygen 1.8.1.2). See [here](http://doxygen.10944.n7.nabble.com/Including-doc-comments-in-code-blocks-in-markdown-td5592.html) for a workaround. This will however look ugly for newer doxygen versions, hence we do not use it.
- Files with `static_assert` statements will be incomplete. A [patch](https://bugzilla.gnome.org/show_bug.cgi?id=737172) is pending and will hopefully make it into doxygen 1.8.9.
- Member groups (usually used to group operators) may or may not work. There still seem to be a few cases where doxygen [messes up](https://bugzilla.gnome.org/show_bug.cgi?id=737112).
- Documenting unnamed parameters is not possible. A corresponding [ticket](https://bugzilla.gnome.org/show_bug.cgi?id=152990) exists for several years.

### Literature references

Literature references should be provided when appropriate by citing references from the bibtex database located at `doc/literature.bib` using the `@cite` command. The labels are the last name of the first author and the four-digit year. In case of duplicates, we append lowercase letters.

These references can be used with `@cite label`, for example like this:
@code
/**
 * Checks whether the polynomial is unit normal
 * @see @cite GCL92, page 39
 * @return If polynomial is normal.
 */
bool isNormal() const;
@endcode 

## Code comments


### File headers

	/**
	 * @file <filename>
	 * @ingroup <groupid1>
	 * @ingroup <groupid2>
	 * @author <author1>
	 * @author <author2>
	 * 
	 * [ Short description ]
	 */

Descriptions may be omitted when the file contains a single class, either implementation or declaration.


### Namespaces
Namespaces are documented in a separate file, found at '/doc/markdown/codedocs/namespaces.dox'

### Class headers

	/**
	 * @ingroup <groupid>
	 * [ Description ]
	 * @see <reference>
	 * @see <OtherClass>
	 */

### Method headers

	/**
	 * [ Usage Description ]
	 * @param <p1> [ Short description for first parameter ] 
	 * @param <p2> [ Short description for second parameter ]
	 * @return [ Short description of return value ]
	 * @see <reference>
	 * @see <otherMethod>
	 */

These method headers are written directly above the method declaration. 
Comments about the implementation are written above the or inside the implementation. 

The `see` command is used likewise as for classes.

### Method groups

There are some cases when documenting each method is tedious and meaningless, for example operators.
In this case, we use doxygen method groups.

For member operators (for example `operator+=`), this works as follows:

	/// @name In-place addition operators
	/// @{
	/**
	 * Add something to this polynomial and return the changed polynomial.
	 * @param rhs Right hand side.
	 * @return Changed polynomial.
	 */
	MultivariatePolynomial& operator+=(const MultivariatePolynomial& rhs);
	MultivariatePolynomial& operator+=(const Term<Coeff>& rhs);
	MultivariatePolynomial& operator+=(const Monomial& rhs);
	MultivariatePolynomial& operator+=(Variable::Arg rhs);
	MultivariatePolynomial& operator+=(const Coeff& rhs);
	/// @}

## Writing out-of-source documentation

Documentation not directly related to the source code is written in Markdown format, and is located in
`/doc/markdown/`.
