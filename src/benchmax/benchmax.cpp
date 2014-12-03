/*
 *  SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
 *
 * This file is part of SMT-RAT.
 *
 * SMT-RAT is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMT-RAT is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *
 */


/**
 * @file benchmax.cpp
 *
 * @author Sebastian Junges
 * @author Ulrich Loup
 *
 * @since 2012-02-01
 * @version 2013-04-23
 */

#include <iostream>
#include <boost/filesystem/path.hpp>
#include <signal.h>

#include "logging.h"
#include "Benchmark.h"
#include "Tool.h"
#include "Node.h"
#include "Settings.h"

#include "carl/formula/Formula.h"

#ifdef USE_BOOST_REGEX
#include <boost/regex.hpp>
using boost::regex;
using boost::regex_match;
#else
#include <regex>
using std::regex;
using std::regex_match;
#endif

namespace po = boost:: program_options;

using std::endl;
using std::stringstream;
using std::string;
using std::pair;
using std::map;
using std::set;
using std::vector;
using std::ios;

const string COPYRIGHT =
	"Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Sebastian Junges, Erika Abraham\r\nThis program comes with ABSOLUTELY NO WARRANTY.\r\nThis is free software, and you are welcome to redistribute it \r\nunder certain conditions; use the command line argument --disclaimer in order to get the conditions and warranty disclaimer.";
const string WARRANTY =
	"THERE IS NO WARRANTY FOR THE PROGRAM, TO THE EXTENT PERMITTED BY APPLICABLE LAW. EXCEPT WHEN OTHERWISE STATED IN WRITING THE COPYRIGHT HOLDERS AND/OR OTHER PARTIES PROVIDE THE PROGRAM “AS IS” WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESSED OR IMPLIED, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE. THE ENTIRE RISK AS TO THE QUALITY AND PERFORMANCE OF THE PROGRAM IS WITH YOU. SHOULD THE PROGRAM PROVE DEFECTIVE, YOU ASSUME THE COST OF ALL NECESSARY SERVICING, REPAIR OR CORRECTION.";
const string CONDITIONS =
	"					GNU GENERAL PUBLIC LICENSE\r\n					   Version 3, 29 June 2007\r\n\r\n Copyright (C) 2007 Free Software Foundation, Inc. <http://fsf.org/>\r\n Everyone is permitted to copy and distribute verbatim copies\r\n of this license document, but changing it is not allowed.\r\n\r\n							Preamble\r\n\r\n  The GNU General Public License is a free, copyleft license for\r\nsoftware and other kinds of works.\r\n\r\n  The licenses for most software and other practical works are designed\r\nto take away your freedom to share and change the works.  By contrast,\r\nthe GNU General Public License is intended to guarantee your freedom to\r\nshare and change all versions of a program--to make sure it remains free\r\nsoftware for all its users.  We, the Free Software Foundation, use the\r\nGNU General Public License for most of our software; it applies also to\r\nany other work released this way by its authors.  You can apply it to\r\nyour programs, too.\r\n\r\n  When we speak of free software, we are referring to freedom, not\r\nprice.  Our General Public Licenses are designed to make sure that you\r\nhave the freedom to distribute copies of free software (and charge for\r\nthem if you wish), that you receive source code or can get it if you\r\nwant it, that you can change the software or use pieces of it in new\r\nfree programs, and that you know you can do these things.\r\n\r\n  To protect your rights, we need to prevent others from denying you\r\nthese rights or asking you to surrender the rights.  Therefore, you have\r\ncertain responsibilities if you distribute copies of the software, or if\r\nyou modify it: responsibilities to respect the freedom of others.\r\n\r\n  For example, if you distribute copies of such a program, whether\r\ngratis or for a fee, you must pass on to the recipients the same\r\nfreedoms that you received.  You must make sure that they, too, receive\r\nor can get the source code.  And you must show them these terms so they\r\nknow their rights.\r\n\r\n  Developers that use the GNU GPL protect your rights with two steps:\r\n(1) assert copyright on the software, and (2) offer you this License\r\ngiving you legal permission to copy, distribute and/or modify it.\r\n\r\n  For the developers\' and authors\' protection, the GPL clearly explains\r\nthat there is no warranty for this free software.  For both users\' and\r\nauthors\' sake, the GPL requires that modified versions be marked as\r\nchanged, so that their problems will not be attributed erroneously to\r\nauthors of previous versions.\r\n\r\n  Some devices are designed to deny users access to install or run\r\nmodified versions of the software inside them, although the manufacturer\r\ncan do so.  This is fundamentally incompatible with the aim of\r\nprotecting users\' freedom to change the software.  The systematic\r\npattern of such abuse occurs in the area of products for individuals to\r\nuse, which is precisely where it is most unacceptable.  Therefore, we\r\nhave designed this version of the GPL to prohibit the practice for those\r\nproducts.  If such problems arise substantially in other domains, we\r\nstand ready to extend this provision to those domains in future versions\r\nof the GPL, as needed to protect the freedom of users.\r\n\r\n  Finally, every program is threatened constantly by software patents.\r\nStates should not allow patents to restrict development and use of\r\nsoftware on general-purpose computers, but in those that do, we wish to\r\navoid the special danger that patents applied to a free program could\r\nmake it effectively proprietary.  To prevent this, the GPL assures that\r\npatents cannot be used to render the program non-free.\r\n\r\n  The precise terms and conditions for copying, distribution and\r\nmodification follow.\r\n\r\n					   TERMS AND CONDITIONS\r\n\r\n  0. Definitions.\r\n\r\n  \"This License\" refers to version 3 of the GNU General Public License.\r\n\r\n  \"Copyright\" also means copyright-like laws that apply to other kinds of\r\nworks, such as semiconductor masks.\r\n\r\n  \"The Program\" refers to any copyrightable work licensed under this\r\nLicense.  Each licensee is addressed as \"you\".  \"Licensees\" and\r\n\"recipients\" may be individuals or organizations.\r\n\r\n  To \"modify\" a work means to copy from or adapt all or part of the work\r\nin a fashion requiring copyright permission, other than the making of an\r\nexact copy.  The resulting work is called a \"modified version\" of the\r\nearlier work or a work \"based on\" the earlier work.\r\n\r\n  A \"covered work\" means either the unmodified Program or a work based\r\non the Program.\r\n\r\n  To \"propagate\" a work means to do anything with it that, without\r\npermission, would make you directly or secondarily liable for\r\ninfringement under applicable copyright law, except executing it on a\r\ncomputer or modifying a private copy.  Propagation includes copying,\r\ndistribution (with or without modification), making available to the\r\npublic, and in some countries other activities as well.\r\n\r\n  To \"convey\" a work means any kind of propagation that enables other\r\nparties to make or receive copies.  Mere interaction with a user through\r\na computer network, with no transfer of a copy, is not conveying.\r\n\r\n  An interactive user interface displays \"Appropriate Legal Notices\"\r\nto the extent that it includes a convenient and prominently visible\r\nfeature that (1) displays an appropriate copyright notice, and (2)\r\ntells the user that there is no warranty for the work (except to the\r\nextent that warranties are provided), that licensees may convey the\r\nwork under this License, and how to view a copy of this License.  If\r\nthe interface presents a list of user COMMANDS or options, such as a\r\nmenu, a prominent item in the list meets this criterion.\r\n\r\n  1. Source Code.\r\n\r\n  The \"source code\" for a work means the preferred form of the work\r\nfor making modifications to it.  \"Object code\" means any non-source\r\nform of a work.\r\n\r\n  A \"Standard Interface\" means an interface that either is an official\r\nstandard defined by a recognized standards body, or, in the case of\r\ninterfaces specified for a particular programming language, one that\r\nis widely used among developers working in that language.\r\n\r\n  The \"System Libraries\" of an executable work include anything, other\r\nthan the work as a whole, that (a) is included in the normal form of\r\npackaging a Major Component, but which is not part of that Major\r\nComponent, and (b) serves only to enable use of the work with that\r\nMajor Component, or to implement a Standard Interface for which an\r\nimplementation is available to the public in source code form.  A\r\n\"Major Component\", in this context, means a major essential component\r\n(kernel, window system, and so on) of the specific operating system\r\n(if any) on which the executable work runs, or a compiler used to\r\nproduce the work, or an object code interpreter used to run it.\r\n\r\n  The \"Corresponding Source\" for a work in object code form means all\r\nthe source code needed to generate, install, and (for an executable\r\nwork) run the object code and to modify the work, including scripts to\r\ncontrol those activities.  However, it does not include the work\'s\r\nSystem Libraries, or general-purpose tools or generally available free\r\nprograms which are used unmodified in performing those activities but\r\nwhich are not part of the work.  For example, Corresponding Source\r\nincludes interface definition files associated with source files for\r\nthe work, and the source code for shared libraries and dynamically\r\nlinked subprograms that the work is specifically designed to require,\r\nsuch as by intimate data communication or control flow between those\r\nsubprograms and other parts of the work.\r\n\r\n  The Corresponding Source need not include anything that users\r\ncan regenerate automatically from other parts of the Corresponding\r\nSource.\r\n\r\n  The Corresponding Source for a work in source code form is that\r\nsame work.\r\n\r\n  2. Basic Permissions.\r\n\r\n  All rights granted under this License are granted for the term of\r\ncopyright on the Program, and are irrevocable provided the stated\r\nconditions are met.  This License explicitly affirms your unlimited\r\npermission to run the unmodified Program.  The output from running a\r\ncovered work is covered by this License only if the output, given its\r\ncontent, constitutes a covered work.  This License acknowledges your\r\nrights of fair use or other equivalent, as provided by copyright law.\r\n\r\n  You may make, run and propagate covered works that you do not\r\nconvey, without conditions so long as your license otherwise remains\r\nin force.  You may convey covered works to others for the sole purpose\r\nof having them make modifications exclusively for you, or provide you\r\nwith facilities for running those works, provided that you comply with\r\nthe terms of this License in conveying all material for which you do\r\nnot control copyright.  Those thus making or running the covered works\r\nfor you must do so exclusively on your behalf, under your direction\r\nand control, on terms that prohibit them from making any copies of\r\nyour copyrighted material outside their relationship with you.\r\n\r\n  Conveying under any other circumstances is permitted solely under\r\nthe conditions stated below.  Sublicensing is not allowed; section 10\r\nmakes it unnecessary.\r\n\r\n  3. Protecting Users\' Legal Rights From Anti-Circumvention Law.\r\n\r\n  No covered work shall be deemed part of an effective technological\r\nmeasure under any applicable law fulfilling obligations under article\r\n11 of the WIPO copyright treaty adopted on 20 December 1996, or\r\nsimilar laws prohibiting or restricting circumvention of such\r\nmeasures.\r\n\r\n  When you convey a covered work, you waive any legal power to forbid\r\ncircumvention of technological measures to the extent such circumvention\r\nis effected by exercising rights under this License with respect to\r\nthe covered work, and you disclaim any intention to limit operation or\r\nmodification of the work as a means of enforcing, against the work\'s\r\nusers, your or third parties\' legal rights to forbid circumvention of\r\ntechnological measures.\r\n\r\n  4. Conveying Verbatim Copies.\r\n\r\n  You may convey verbatim copies of the Program\'s source code as you\r\nreceive it, in any medium, provided that you conspicuously and\r\nappropriately publish on each copy an appropriate copyright notice;\r\nkeep intact all notices stating that this License and any\r\nnon-permissive terms added in accord with section 7 apply to the code;\r\nkeep intact all notices of the absence of any warranty; and give all\r\nrecipients a copy of this License along with the Program.\r\n\r\n  You may charge any price or no price for each copy that you convey,\r\nand you may offer support or warranty protection for a fee.\r\n\r\n  5. Conveying Modified Source Versions.\r\n\r\n  You may convey a work based on the Program, or the modifications to\r\nproduce it from the Program, in the form of source code under the\r\nterms of section 4, provided that you also meet all of these conditions:\r\n\r\n	a) The work must carry prominent notices stating that you modified\r\n	it, and giving a relevant date.\r\n\r\n	b) The work must carry prominent notices stating that it is\r\n	released under this License and any conditions added under section\r\n	7.  This requirement modifies the requirement in section 4 to\r\n	\"keep intact all notices\".\r\n\r\n	c) You must license the entire work, as a whole, under this\r\n	License to anyone who comes into possession of a copy.  This\r\n	License will therefore apply, along with any applicable section 7\r\n	additional terms, to the whole of the work, and all its parts,\r\n	regardless of how they are packaged.  This License gives no\r\n	permission to license the work in any other way, but it does not\r\n	invalidate such permission if you have separately received it.\r\n\r\n	d) If the work has interactive user interfaces, each must display\r\n	Appropriate Legal Notices; however, if the Program has interactive\r\n	interfaces that do not display Appropriate Legal Notices, your\r\n	work need not make them do so.\r\n\r\n  A compilation of a covered work with other separate and independent\r\nworks, which are not by their nature extensions of the covered work,\r\nand which are not combined with it such as to form a larger program,\r\nin or on a volume of a storage or distribution medium, is called an\r\n\"aggregate\" if the compilation and its resulting copyright are not\r\nused to limit the access or legal rights of the compilation\'s users\r\nbeyond what the individual works permit.  Inclusion of a covered work\r\nin an aggregate does not cause this License to apply to the other\r\nparts of the aggregate.\r\n\r\n  6. Conveying Non-Source Forms.\r\n\r\n  You may convey a covered work in object code form under the terms\r\nof sections 4 and 5, provided that you also convey the\r\nmachine-readable Corresponding Source under the terms of this License,\r\nin one of these ways:\r\n\r\n	a) Convey the object code in, or embodied in, a physical product\r\n	(including a physical distribution medium), accompanied by the\r\n	Corresponding Source fixed on a durable physical medium\r\n	customarily used for software interchange.\r\n\r\n	b) Convey the object code in, or embodied in, a physical product\r\n	(including a physical distribution medium), accompanied by a\r\n	written offer, valid for at least three years and valid for as\r\n	long as you offer spare parts or customer support for that product\r\n	model, to give anyone who possesses the object code either (1) a\r\n	copy of the Corresponding Source for all the software in the\r\n	product that is covered by this License, on a durable physical\r\n	medium customarily used for software interchange, for a price no\r\n	more than your reasonable cost of physically performing this\r\n	conveying of source, or (2) access to copy the\r\n	Corresponding Source from a network server at no charge.\r\n\r\n	c) Convey individual copies of the object code with a copy of the\r\n	written offer to provide the Corresponding Source.  This\r\n	alternative is allowed only occasionally and noncommercially, and\r\n	only if you received the object code with such an offer, in accord\r\n	with subsection 6b.\r\n\r\n	d) Convey the object code by offering access from a designated\r\n	place (gratis or for a charge), and offer equivalent access to the\r\n	Corresponding Source in the same way through the same place at no\r\n	further charge.  You need not require recipients to copy the\r\n	Corresponding Source along with the object code.  If the place to\r\n	copy the object code is a network server, the Corresponding Source\r\n	may be on a different server (operated by you or a third party)\r\n	that supports equivalent copying facilities, provided you maintain\r\n	clear directions next to the object code saying where to find the\r\n	Corresponding Source.  Regardless of what server hosts the\r\n	Corresponding Source, you remain obligated to ensure that it is\r\n	available for as long as needed to satisfy these requirements.\r\n\r\n	e) Convey the object code using peer-to-peer transmission, provided\r\n	you inform other peers where the object code and Corresponding\r\n	Source of the work are being offered to the general public at no\r\n	charge under subsection 6d.\r\n\r\n  A separable portion of the object code, whose source code is excluded\r\nfrom the Corresponding Source as a System Library, need not be\r\nincluded in conveying the object code work.\r\n\r\n  A \"User Product\" is either (1) a \"consumer product\", which means any\r\ntangible personal property which is normally used for personal, family,\r\nor household purposes, or (2) anything designed or sold for incorporation\r\ninto a dwelling.  In determining whether a product is a consumer product,\r\ndoubtful cases shall be resolved in favor of coverage.  For a particular\r\nproduct received by a particular user, \"normally used\" refers to a\r\ntypical or common use of that class of product, regardless of the status\r\nof the particular user or of the way in which the particular user\r\nactually uses, or expects or is expected to use, the product.  A product\r\nis a consumer product regardless of whether the product has substantial\r\ncommercial, industrial or non-consumer uses, unless such uses represent\r\nthe only significant mode of use of the product.\r\n\r\n  \"Installation Information\" for a User Product means any methods,\r\nprocedures, authorization keys, or other information required to install\r\nand execute modified versions of a covered work in that User Product from\r\na modified version of its Corresponding Source.  The information must\r\nsuffice to ensure that the continued functioning of the modified object\r\ncode is in no case prevented or interfered with solely because\r\nmodification has been made.\r\n\r\n  If you convey an object code work under this section in, or with, or\r\nspecifically for use in, a User Product, and the conveying occurs as\r\npart of a transaction in which the right of possession and use of the\r\nUser Product is transferred to the recipient in perpetuity or for a\r\nfixed term (regardless of how the transaction is characterized), the\r\nCorresponding Source conveyed under this section must be accompanied\r\nby the Installation Information.  But this requirement does not apply\r\nif neither you nor any third party retains the ability to install\r\nmodified object code on the User Product (for example, the work has\r\nbeen installed in ROM).\r\n\r\n  The requirement to provide Installation Information does not include a\r\nrequirement to continue to provide support service, warranty, or updates\r\nfor a work that has been modified or installed by the recipient, or for\r\nthe User Product in which it has been modified or installed.  Access to a\r\nnetwork may be denied when the modification itself materially and\r\nadversely affects the operation of the network or violates the rules and\r\nprotocols for communication across the network.\r\n\r\n  Corresponding Source conveyed, and Installation Information provided,\r\nin accord with this section must be in a format that is publicly\r\ndocumented (and with an implementation available to the public in\r\nsource code form), and must require no special password or key for\r\nunpacking, reading or copying.\r\n\r\n  7. Additional Terms.\r\n\r\n  \"Additional permissions\" are terms that supplement the terms of this\r\nLicense by making exceptions from one or more of its conditions.\r\nAdditional permissions that are applicable to the entire Program shall\r\nbe treated as though they were included in this License, to the extent\r\nthat they are valid under applicable law.  If additional permissions\r\napply only to part of the Program, that part may be used separately\r\nunder those permissions, but the entire Program remains governed by\r\nthis License without regard to the additional permissions.\r\n\r\n  When you convey a copy of a covered work, you may at your option\r\nremove any additional permissions from that copy, or from any part of\r\nit.  (Additional permissions may be written to require their own\r\nremoval in certain cases when you modify the work.)  You may place\r\nadditional permissions on material, added by you to a covered work,\r\nfor which you have or can give appropriate copyright permission.\r\n\r\n  Notwithstanding any other provision of this License, for material you\r\nadd to a covered work, you may (if authorized by the copyright holders of\r\nthat material) supplement the terms of this License with terms:\r\n\r\n	a) Disclaiming warranty or limiting liability differently from the\r\n	terms of sections 15 and 16 of this License; or\r\n\r\n	b) Requiring preservation of specified reasonable legal notices or\r\n	author attributions in that material or in the Appropriate Legal\r\n	Notices displayed by works containing it; or\r\n\r\n	c) Prohibiting misrepresentation of the origin of that material, or\r\n	requiring that modified versions of such material be marked in\r\n	reasonable ways as different from the original version; or\r\n\r\n	d) Limiting the use for publicity purposes of names of licensors or\r\n	authors of the material; or\r\n\r\n	e) Declining to grant rights under trademark law for use of some\r\n	trade names, trademarks, or service marks; or\r\n\r\n	f) Requiring indemnification of licensors and authors of that\r\n	material by anyone who conveys the material (or modified versions of\r\n	it) with contractual assumptions of liability to the recipient, for\r\n	any liability that these contractual assumptions directly impose on\r\n	those licensors and authors.\r\n\r\n  All other non-permissive additional terms are considered \"further\r\nrestrictions\" within the meaning of section 10.  If the Program as you\r\nreceived it, or any part of it, contains a notice stating that it is\r\ngoverned by this License along with a term that is a further\r\nrestriction, you may remove that term.  If a license document contains\r\na further restriction but permits relicensing or conveying under this\r\nLicense, you may add to a covered work material governed by the terms\r\nof that license document, provided that the further restriction does\r\nnot survive such relicensing or conveying.\r\n\r\n  If you add terms to a covered work in accord with this section, you\r\nmust place, in the relevant source files, a statement of the\r\nadditional terms that apply to those files, or a notice indicating\r\nwhere to find the applicable terms.\r\n\r\n  Additional terms, permissive or non-permissive, may be stated in the\r\nform of a separately written license, or stated as exceptions;\r\nthe above requirements apply either way.\r\n\r\n  8. Termination.\r\n\r\n  You may not propagate or modify a covered work except as expressly\r\nprovided under this License.  Any attempt otherwise to propagate or\r\nmodify it is void, and will automatically terminate your rights under\r\nthis License (including any patent licenses granted under the third\r\nparagraph of section 11).\r\n\r\n  However, if you cease all violation of this License, then your\r\nlicense from a particular copyright holder is reinstated (a)\r\nprovisionally, unless and until the copyright holder explicitly and\r\nfinally terminates your license, and (b) permanently, if the copyright\r\nholder fails to notify you of the violation by some reasonable means\r\nprior to 60 days after the cessation.\r\n\r\n  Moreover, your license from a particular copyright holder is\r\nreinstated permanently if the copyright holder notifies you of the\r\nviolation by some reasonable means, this is the first time you have\r\nreceived notice of violation of this License (for any work) from that\r\ncopyright holder, and you cure the violation prior to 30 days after\r\nyour receipt of the notice.\r\n\r\n  Termination of your rights under this section does not terminate the\r\nlicenses of parties who have received copies or rights from you under\r\nthis License.  If your rights have been terminated and not permanently\r\nreinstated, you do not qualify to receive new licenses for the same\r\nmaterial under section 10.\r\n\r\n  9. Acceptance Not Required for Having Copies.\r\n\r\n  You are not required to accept this License in order to receive or\r\nrun a copy of the Program.  Ancillary propagation of a covered work\r\noccurring solely as a consequence of using peer-to-peer transmission\r\nto receive a copy likewise does not require acceptance.  However,\r\nnothing other than this License grants you permission to propagate or\r\nmodify any covered work.  These actions infringe copyright if you do\r\nnot accept this License.  Therefore, by modifying or propagating a\r\ncovered work, you indicate your acceptance of this License to do so.\r\n\r\n  10. Automatic Licensing of Downstream Recipients.\r\n\r\n  Each time you convey a covered work, the recipient automatically\r\nreceives a license from the original licensors, to run, modify and\r\npropagate that work, subject to this License.  You are not responsible\r\nfor enforcing compliance by third parties with this License.\r\n\r\n  An \"entity transaction\" is a transaction transferring control of an\r\norganization, or substantially all assets of one, or subdividing an\r\norganization, or merging organizations.  If propagation of a covered\r\nwork results from an entity transaction, each party to that\r\ntransaction who receives a copy of the work also receives whatever\r\nlicenses to the work the party\'s predecessor in interest had or could\r\ngive under the previous paragraph, plus a right to possession of the\r\nCorresponding Source of the work from the predecessor in interest, if\r\nthe predecessor has it or can get it with reasonable efforts.\r\n\r\n  You may not impose any further restrictions on the exercise of the\r\nrights granted or affirmed under this License.  For example, you may\r\nnot impose a license fee, royalty, or other charge for exercise of\r\nrights granted under this License, and you may not initiate litigation\r\n(including a cross-claim or counterclaim in a lawsuit) alleging that\r\nany patent claim is infringed by making, using, selling, offering for\r\nsale, or importing the Program or any portion of it.\r\n\r\n  11. Patents.\r\n\r\n  A \"contributor\" is a copyright holder who authorizes use under this\r\nLicense of the Program or a work on which the Program is based.  The\r\nwork thus licensed is called the contributor\'s \"contributor version\".\r\n\r\n  A contributor\'s \"essential patent claims\" are all patent claims\r\nowned or controlled by the contributor, whether already acquired or\r\nhereafter acquired, that would be infringed by some manner, permitted\r\nby this License, of making, using, or selling its contributor version,\r\nbut do not include claims that would be infringed only as a\r\nconsequence of further modification of the contributor version.  For\r\npurposes of this definition, \"control\" includes the right to grant\r\npatent sublicenses in a manner consistent with the requirements of\r\nthis License.\r\n\r\n  Each contributor grants you a non-exclusive, worldwide, royalty-free\r\npatent license under the contributor\'s essential patent claims, to\r\nmake, use, sell, offer for sale, import and otherwise run, modify and\r\npropagate the contents of its contributor version.\r\n\r\n  In the following three paragraphs, a \"patent license\" is any express\r\nagreement or commitment, however denominated, not to enforce a patent\r\n(such as an express permission to practice a patent or covenant not to\r\nsue for patent infringement).  To \"grant\" such a patent license to a\r\nparty means to make such an agreement or commitment not to enforce a\r\npatent against the party.\r\n\r\n  If you convey a covered work, knowingly relying on a patent license,\r\nand the Corresponding Source of the work is not available for anyone\r\nto copy, free of charge and under the terms of this License, through a\r\npublicly available network server or other readily accessible means,\r\nthen you must either (1) cause the Corresponding Source to be so\r\navailable, or (2) arrange to deprive yourself of the benefit of the\r\npatent license for this particular work, or (3) arrange, in a manner\r\nconsistent with the requirements of this License, to extend the patent\r\nlicense to downstream recipients.  \"Knowingly relying\" means you have\r\nactual knowledge that, but for the patent license, your conveying the\r\ncovered work in a country, or your recipient\'s use of the covered work\r\nin a country, would infringe one or more identifiable patents in that\r\ncountry that you have reason to believe are valid.\r\n\r\n  If, pursuant to or in connection with a single transaction or\r\narrangement, you convey, or propagate by procuring conveyance of, a\r\ncovered work, and grant a patent license to some of the parties\r\nreceiving the covered work authorizing them to use, propagate, modify\r\nor convey a specific copy of the covered work, then the patent license\r\nyou grant is automatically extended to all recipients of the covered\r\nwork and works based on it.\r\n\r\n  A patent license is \"discriminatory\" if it does not include within\r\nthe scope of its coverage, prohibits the exercise of, or is\r\nconditioned on the non-exercise of one or more of the rights that are\r\nspecifically granted under this License.  You may not convey a covered\r\nwork if you are a party to an arrangement with a third party that is\r\nin the business of distributing software, under which you make payment\r\nto the third party based on the extent of your activity of conveying\r\nthe work, and under which the third party grants, to any of the\r\nparties who would receive the covered work from you, a discriminatory\r\npatent license (a) in connection with copies of the covered work\r\nconveyed by you (or copies made from those copies), or (b) primarily\r\nfor and in connection with specific products or compilations that\r\ncontain the covered work, unless you entered into that arrangement,\r\nor that patent license was granted, prior to 28 March 2007.\r\n\r\n  Nothing in this License shall be construed as excluding or limiting\r\nany implied license or other defenses to infringement that may\r\notherwise be available to you under applicable patent law.\r\n\r\n  12. No Surrender of Others\' Freedom.\r\n\r\n  If conditions are imposed on you (whether by court order, agreement or\r\notherwise) that contradict the conditions of this License, they do not\r\nexcuse you from the conditions of this License.  If you cannot convey a\r\ncovered work so as to satisfy simultaneously your obligations under this\r\nLicense and any other pertinent obligations, then as a consequence you may\r\nnot convey it at all.  For example, if you agree to terms that obligate you\r\nto collect a royalty for further conveying from those to whom you convey\r\nthe Program, the only way you could satisfy both those terms and this\r\nLicense would be to refrain entirely from conveying the Program.\r\n\r\n  13. Use with the GNU Affero General Public License.\r\n\r\n  Notwithstanding any other provision of this License, you have\r\npermission to link or combine any covered work with a work licensed\r\nunder version 3 of the GNU Affero General Public License into a single\r\ncombined work, and to convey the resulting work.  The terms of this\r\nLicense will continue to apply to the part which is the covered work,\r\nbut the special requirements of the GNU Affero General Public License,\r\nsection 13, concerning interaction through a network will apply to the\r\ncombination as such.\r\n\r\n  14. Revised Versions of this License.\r\n\r\n  The Free Software Foundation may publish revised and/or new versions of\r\nthe GNU General Public License from time to time.  Such new versions will\r\nbe similar in spirit to the present version, but may differ in detail to\r\naddress new problems or concerns.\r\n\r\n  Each version is given a distinguishing version number.  If the\r\nProgram specifies that a certain numbered version of the GNU General\r\nPublic License \"or any later version\" applies to it, you have the\r\noption of following the terms and conditions either of that numbered\r\nversion or of any later version published by the Free Software\r\nFoundation.  If the Program does not specify a version number of the\r\nGNU General Public License, you may choose any version ever published\r\nby the Free Software Foundation.\r\n\r\n  If the Program specifies that a proxy can decide which future\r\nversions of the GNU General Public License can be used, that proxy\'s\r\npublic statement of acceptance of a version permanently authorizes you\r\nto choose that version for the Program.\r\n\r\n  Later license versions may give you additional or different\r\npermissions.  However, no additional obligations are imposed on any\r\nauthor or copyright holder as a result of your choosing to follow a\r\nlater version.\r\n\r\n  15. Disclaimer of Warranty.\r\n\r\n  THERE IS NO WARRANTY FOR THE PROGRAM, TO THE EXTENT PERMITTED BY\r\nAPPLICABLE LAW.  EXCEPT WHEN OTHERWISE STATED IN WRITING THE COPYRIGHT\r\nHOLDERS AND/OR OTHER PARTIES PROVIDE THE PROGRAM \"AS IS\" WITHOUT WARRANTY\r\nOF ANY KIND, EITHER EXPRESSED OR IMPLIED, INCLUDING, BUT NOT LIMITED TO,\r\nTHE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR\r\nPURPOSE.  THE ENTIRE RISK AS TO THE QUALITY AND PERFORMANCE OF THE PROGRAM\r\nIS WITH YOU.  SHOULD THE PROGRAM PROVE DEFECTIVE, YOU ASSUME THE COST OF\r\nALL NECESSARY SERVICING, REPAIR OR CORRECTION.\r\n\r\n  16. Limitation of Liability.\r\n\r\n  IN NO EVENT UNLESS REQUIRED BY APPLICABLE LAW OR AGREED TO IN WRITING\r\nWILL ANY COPYRIGHT HOLDER, OR ANY OTHER PARTY WHO MODIFIES AND/OR CONVEYS\r\nTHE PROGRAM AS PERMITTED ABOVE, BE LIABLE TO YOU FOR DAMAGES, INCLUDING ANY\r\nGENERAL, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES ARISING OUT OF THE\r\nUSE OR INABILITY TO USE THE PROGRAM (INCLUDING BUT NOT LIMITED TO LOSS OF\r\nDATA OR DATA BEING RENDERED INACCURATE OR LOSSES SUSTAINED BY YOU OR THIRD\r\nPARTIES OR A FAILURE OF THE PROGRAM TO OPERATE WITH ANY OTHER PROGRAMS),\r\nEVEN IF SUCH HOLDER OR OTHER PARTY HAS BEEN ADVISED OF THE POSSIBILITY OF\r\nSUCH DAMAGES.\r\n\r\n  17. Interpretation of Sections 15 and 16.\r\n\r\n  If the disclaimer of warranty and limitation of liability provided\r\nabove cannot be given local legal effect according to their terms,\r\nreviewing courts shall apply local law that most closely approximates\r\nan absolute waiver of all civil liability in connection with the\r\nProgram, unless a warranty or assumption of liability accompanies a\r\ncopy of the Program in return for a fee.\r\n";
const unsigned NUMBER_OF_EXAMPLES_TO_SOLVE = 6;

void printWelcome()
{
	BenchmarkTool::OStream << endl;
	BenchmarkTool::OStream << "   SMT-LIB 2.0 Benchmark Tool " << endl << endl;
	BenchmarkTool::OStream << COPYRIGHT << endl << endl;
	BenchmarkTool::OStream << "Support: Florian Corzilius <florian.corzilius@rwth-aachen.de> and Ulrich Loup <loup@cs.rwth-aachen.de>" << endl
						   << endl;
	BenchmarkTool::OStream << "Usage: Start the tool with the command line argument --help to get further information." << endl;
	BenchmarkTool::OStream << "Examples: ./benchmax -T 90 -D smtlib/qf_nra/etcs/ -D smtlib/qf_nra/bouncing_ball/ -S smtratSolver" << endl << endl;
	BenchmarkTool::OStream << "		  ./benchmax -T 90 -D smtlib/qf_nra/etcs/ -D smtlib/qf_nra/bouncing_ball/ -Z z3" << endl << endl;
	BenchmarkTool::OStream << "		  ./benchmax -T 90 -D smtlib/qf_nra/etcs/ -D smtlib/qf_nra/bouncing_ball/ --redlog_rlqe /usr/bin/redcsl"
						   << endl << endl;
}

void printDisclaimer()
{
	BenchmarkTool::OStream << CONDITIONS << endl << endl;
	BenchmarkTool::OStream << WARRANTY << endl << endl;
}

void printConnectionError(const string& _nodeAsString)
{
	BenchmarkTool::OStream << "Error,   \"" << _nodeAsString << "\"   is not a well defined node connection." << endl;
	BenchmarkTool::OStream << "It must be of the form " << endl << endl;
	BenchmarkTool::OStream << "			server[:port]@[numberOfCores]@user@password" << endl << endl;
	BenchmarkTool::OStream << "where server must be a well defined ip address, port a valid port" << endl;
	BenchmarkTool::OStream << "number (1 to 65535) and numberOfCores an integer > 0." << endl;
}

void printSolverExecutionError(const string& _nodeAsString)
{
	BenchmarkTool::OStream << "Error,   \"" << _nodeAsString << "\"   is not a well defined solver execution." << endl;
	BenchmarkTool::OStream << "Every space must be replaced by an @." << endl;
	BenchmarkTool::OStream << "Example:  The solver execution	   /pathToSolver -arg1 --arg2 10 --arg3 abc" << endl;
	BenchmarkTool::OStream << "		  must be written as		 /pathToSolver@-arg1@--arg2@10@--arg3@abc" << endl;
}

/* void exportToLatexTable( std::ostream& BenchmarkTool::OStream )
 * {
		boost::posix_time::ptime pt = boost::posix_time::second_clock::universal_time();
		string name = "results.tex";
		fs::ofstream file;
		file.open(name);
		BenchmarkTool::OStream << "Print LaTeX table representation of the results:" << endl << endl;
		file << "\\begin{tabular}{lllll}" << endl;
		BOOST_FOREACH( doublestring res, results)
		{	// benchmarks
			file << res.first;
			file << " & $" << res.second << "$";
			file << "\\\\" << endl;
		}
		file << "\\end{tabular}" << endl;
		file.close();

	}
 * */

void addToTools(const std::vector<std::string>& pathes, ToolInterface interface, std::vector<Tool*>& tools)
{
	for (const auto& p: pathes) {
		regex r("([^ ]+)(?: ([^ ]+))*");
		std::smatch matches;
		if (regex_match(p, matches, r)) {
			fs::path path(matches[1]);
			fs::file_status status = fs::status(path);
			if (status.type() != fs::file_type::regular_file) {
				std::cout << "The tool " << path << " does not seem to be a file. We skip it." << std::endl;
				continue;
			}
			if ((status.permissions() & (fs::others_exe | fs::group_exe | fs::owner_exe)) == 0) {
				std::cout << "The tool " << path << " does not seem to be executable. We skip it." << std::endl;
				continue;
			}
			tools.push_back(createTool(interface, matches[1]));
			for (std::size_t i = 2; i < matches.size(); i++) {
				tools.back()->addArgument(matches[i]);
			}
		}
	}
}

/**
 * Parses a node identifier of the format `server[:port]@[numberOfCores]@user@password`
 * @param _nodeAsString
 * @return 
 */
Node* getNode(const string& _nodeAsString)
{
	regex noderegex("([^:]+):([^@]+)@([^:@]+)(?::(\\d+))?(?:@(\\d+))?");
	std::smatch matches;
	if (regex_match(_nodeAsString, matches, noderegex)) {
		std::string username = matches[1];
		std::string password = matches[2];
		std::string hostname = matches[3];
		unsigned long port = 22;
		unsigned long cores = 1;
		try {
			if (matches[4] != "") port = std::stoul(matches[4]);
			if (matches[5] != "") cores = std::stoul(matches[5]);
		} catch (std::out_of_range) {
			std::cerr << "Value for port or number of cores is out of range." << std::endl;
			std::cerr << "\tPort: " << matches[4] << std::endl;
			std::cerr << "\tCores: " << matches[5] << std::endl;
		}
		return new Node(hostname, username, password, (unsigned short)cores, (unsigned short)port);
	} else {
		std::cerr << "Invalid format for node specification. Use the following format:" << std::endl;
		std::cerr << "\t<user>:<password>@<hostname>[:<port = 22>][@<cores = 1>]" << std::endl;
		return nullptr;
	}
}

void checkPathCorrectness(std::string& _path)
{
	if(!_path.empty())
	{
		if(_path.at(_path.size() - 1) != '/')
			_path += "/";
	}
}

bool initApplication(int argc, char** argv, vector<Benchmark*>& _benchmarks, Stats*& _stats, vector<Tool*>& _tools)
{
	benchmax::Settings s(argc, argv);

	// add the remote nodes
	for (const auto& node: s.nodes) {
		BenchmarkTool::Nodes->push_back(getNode(node));
	}
	
	BenchmarkTool::PathOfBenchmarkTool = fs::system_complete(fs::path(argv[0])).native();

	if(s.has("help")) {
		BenchmarkTool::OStream << s;
		return false;
	}
	if(s.has("disclaimer")) {
		printDisclaimer();
		return false;
	}
	if(s.has("compose")) {
		Stats::composeStats(s.composeFiles);
		return false;
	}
	else if(BenchmarkTool::ProduceLatex)
	{
		Stats::createStatsCompose(BenchmarkTool::OutputDirectory + "latexCompose.xsl");
		system(
		std::string("xsltproc -o " + BenchmarkTool::OutputDirectory + "results.tex " + BenchmarkTool::OutputDirectory + "latexCompose.xsl "
					+ BenchmarkTool::StatsXMLFile).c_str());
		fs::remove(fs::path(BenchmarkTool::OutputDirectory + "latexCompose.xsl"));
	}

	if(s.validationtool != "")
	{
		BenchmarkTool::ValidationTool = createTool(TI_Z3, s.validationtool);
	}

	if(s.outputDir != "")
	{
		fs::path oloc = fs::path(s.outputDir);
		if(!fs::exists(oloc) ||!fs::is_directory(oloc))
		{
			BenchmarkTool::OStream << "Error: Output directory does not exist." << endl;
			exit(0);
		}
		BenchmarkTool::OutputDirectory = s.outputDir;
	}

	if(s.wrongResultsDir == "")
	{
		BenchmarkTool::WrongResultPath = BenchmarkTool::OutputDirectory + "wrong_results/";
	}
	
	if(s.statsXMLFile != "")
	{
		BenchmarkTool::StatsXMLFile = s.statsXMLFile;
	}
	if (!s.mute) {
		printWelcome();
	}

	// Check the correctness of the given paths and correct them if necessary
	checkPathCorrectness(BenchmarkTool::WrongResultPath);
	checkPathCorrectness(BenchmarkTool::OutputDirectory);

	// add the different applications to the list of tools, with the appropriate interface.
	addToTools(s.smtratapps, TI_SMTRAT, _tools);
	addToTools(s.z3apps, TI_Z3, _tools);
	addToTools(s.isatapps, TI_ISAT, _tools);
	addToTools(s.redlog_rlqeapps, TI_REDLOG_RLQE, _tools);
	addToTools(s.redlog_rlcadapps, TI_REDLOG_RLCAD, _tools);
	addToTools(s.qepcadapps, TI_QEPCAD, _tools);

	// Collect all used solvers in the statisticsfile.
	_stats = new Stats(BenchmarkTool::OutputDirectory + BenchmarkTool::StatsXMLFile,
					   (!BenchmarkTool::Nodes->empty() ? Stats::STATS_COLLECTION : Stats::BENCHMARK_RESULT));
	if(BenchmarkTool::Nodes->empty())
	{
		for (const auto& tool: _tools) {
			_stats->addSolver(fs::path(tool->path()).filename().generic_string());
		}
	}

	// For each path, and each tool, we add a benchmark to be computed.
	for (const auto& p: s.pathes) {
		fs::path path(p);
		if(fs::exists(path))
		{
			for (const auto& tool: _tools) {
				_benchmarks.push_back(
				new Benchmark(path.generic_string(), tool, BenchmarkTool::Timeout, BenchmarkTool::Memout, s.verbose, s.quiet, s.mute,
							  BenchmarkTool::ProduceLatex, _stats));
			}
		}
	}
	return true;
}

/**
 *
 * @param _signal
 */
void handleSignal(int)
{
	BENCHMAX_LOG_WARN("benchmax", "User abort!");
	while(!BenchmarkTool::Nodes->empty())
	{
		Node* toDelete = BenchmarkTool::Nodes->back();
		toDelete->cancel();
		BenchmarkTool::Nodes->pop_back();
		delete toDelete;
	}
	exit(-1);
}

/**
 * Main program.
 */
int main(int argc, char** argv)
{
	// init benchmarks
	std::vector<Benchmark*> benchmarks;
	Stats* stats = NULL;
	std::vector<Tool*> tools;
	if (!initApplication(argc, argv, benchmarks, stats, tools)) {
		return 0;
	}

	std::signal(SIGINT, &handleSignal);

	if(benchmarks.empty()) {
		BENCHMAX_LOG_FATAL("benchmax", "No benchmarks were found.");
		return 0;
	}
	
	// run benchmarks
	std::map<std::pair<std::string, std::string>, Benchmark*> table;	// table mapping <benchmark,solver> -> result
	std::set<std::string> benchmarkSet, solverSet;

	if(!BenchmarkTool::Nodes->empty()) {
		// libssh is needed.
		int rc = libssh2_init(0);
		if (rc != 0) {
			std::cout << "Failed to initialize libssh2 (return code " << rc << ")" << std::endl;
			exit(1);
		}
	}

	/*
	 * Main loop.
	 */
	if(BenchmarkTool::Nodes->empty())
	{
		for (const auto& benchmark: benchmarks)
		{
			benchmark->printSettings();
			benchmark->run();
			BenchmarkTool::OStream << "Benchmark done!" << std::endl;
			benchmark->printResults();
			if(benchmark->produceLaTeX())
			{
				string benchmarkString = benchmark->benchmarkName() + " (" + boost::lexical_cast<string>(benchmark->benchmarkCount()) + ")";
				table[pair<string, string>(benchmarkString, benchmark->solverName())] = benchmark;
				benchmarkSet.insert(benchmarkString);
				solverSet.insert(benchmark->solverName());
			}
		}

		if(BenchmarkTool::ValidationTool != NULL)
		{
			std::string wrongResultPath = BenchmarkTool::WrongResultPath.substr(0, BenchmarkTool::WrongResultPath.size() - 1);
			fs::path path(wrongResultPath);
			if(fs::exists(path))
			{
				std::string tarCall = std::string("tar zcfP " + wrongResultPath + ".tgz " + wrongResultPath);
				system(tarCall.c_str());
				fs::remove_all(fs::path(BenchmarkTool::WrongResultPath));
			}
		}
	}
	else
	{
		int						  nrOfCalls		= 0;
		vector<Benchmark*>::iterator currentBenchmark = benchmarks.begin();
		vector<Node*>::iterator	  currentNode	  = BenchmarkTool::Nodes->begin();
		if(currentBenchmark != benchmarks.end())
			(*currentBenchmark)->printSettings();
		while(currentBenchmark != benchmarks.end())
		{
			if((*currentBenchmark)->done())
			{
				++currentBenchmark;
				if(currentBenchmark == benchmarks.end())
					break;
				(*currentBenchmark)->printSettings();
			}
			if(currentNode == BenchmarkTool::Nodes->end())
				currentNode = BenchmarkTool::Nodes->begin();
			if(!(*currentNode)->connected())
			{
				(*currentNode)->createSSHconnection();
			}

			(*currentNode)->updateResponses();

			if((*currentNode)->freeCores() > 0)
			{
				stringstream tmpStream;
				tmpStream << ++nrOfCalls;
				(*currentNode)->assignAndExecuteBenchmarks(**currentBenchmark, NUMBER_OF_EXAMPLES_TO_SOLVE, tmpStream.str());
			}
			++currentNode;
			usleep(100000);	// 100 milliseconds (0.1 seconds);
		}

		BenchmarkTool::OStream << "Benchmark done!" << std::endl;

		unsigned waitedTime = 0;
		//		unsigned numberOfTries = 0;
		// Wait until all nodes have finished.
		BenchmarkTool::OStream << "All scheduled!" << std::endl;
		bool allNodesEntirelyIdle = false;
		BenchmarkTool::OStream << "Waiting for calls!" << std::endl << std::endl;
		while(!allNodesEntirelyIdle)
		{
			allNodesEntirelyIdle = true;
			vector<Node*>::iterator currentNode = BenchmarkTool::Nodes->begin();
			while(currentNode != BenchmarkTool::Nodes->end())
			{
				(*currentNode)->updateResponses();
				if(!(*currentNode)->idle())
				{
					allNodesEntirelyIdle = false;
					if(waitedTime > (BenchmarkTool::Timeout * NUMBER_OF_EXAMPLES_TO_SOLVE))
					{
						BenchmarkTool::OStream << "Waiting for call:" << std::endl << std::endl;
						(*currentNode)->sshConnection().printActiveRemoteCalls(BenchmarkTool::OStream, "   ");
						waitedTime = 0;
					}
					break;
				}
				++currentNode;
			}
			sleep(1);
			++waitedTime;
		}

		// Download files.
		for(std::vector<Node*>::const_iterator currentNode = BenchmarkTool::Nodes->begin(); currentNode != BenchmarkTool::Nodes->end(); ++currentNode)
		{
			for(std::vector<std::string>::const_iterator jobId = (*currentNode)->jobIds().begin(); jobId != (*currentNode)->jobIds().end(); ++jobId)
			{
				std::stringstream out;
				out << *jobId;
				(*currentNode)->downloadFile(
				BenchmarkTool::RemoteOutputDirectory + "stats_" + *jobId + ".xml", BenchmarkTool::OutputDirectory + "stats_" + *jobId + ".xml");
				if(BenchmarkTool::ValidationTool != NULL)
				{
					fs::path newloc = fs::path(BenchmarkTool::WrongResultPath);
					if(!fs::is_directory(newloc))
					{
						fs::create_directories(newloc);
					}
					(*currentNode)->downloadFile(
					BenchmarkTool::RemoteOutputDirectory + "wrong_results_" + *jobId + ".tgz",
					BenchmarkTool::WrongResultPath + "wrong_results_" + *jobId + ".tgz");
				}
				fs::path newloc = fs::path(BenchmarkTool::OutputDirectory + "benchmark_output/");
				if(!fs::is_directory(newloc))
				{
					fs::create_directories(newloc);
				}
				(*currentNode)->downloadFile(
				BenchmarkTool::RemoteOutputDirectory + "benchmark_" + *jobId + ".out",
				BenchmarkTool::OutputDirectory + "benchmark_output/benchmark_" + *jobId + ".out");
				stats->addStat("stats_" + *jobId + ".xml");

			}
		}
	}

	if(!BenchmarkTool::Nodes->empty())
	{
		stats->createStatsCompose(BenchmarkTool::OutputDirectory + "statsCompose.xsl");
		delete stats;
		Stats::callComposeProcessor();
	}
	else
	{
		delete stats;
	}

	// Delete everything and finish.
	while(!benchmarks.empty())
	{
		Benchmark* toDelete = benchmarks.back();
		benchmarks.pop_back();
		delete toDelete;
	}
	while(!tools.empty())
	{
		Tool* toDelete = tools.back();
		tools.pop_back();
		delete toDelete;
	}
	while(!BenchmarkTool::Nodes->empty())
	{
		Node* toDelete = BenchmarkTool::Nodes->back();
		BenchmarkTool::Nodes->pop_back();
		delete toDelete;
	}

	// Necessary output message (DO NOT REMOVE IT)
	std::cout << BenchmarkTool::ExitMessage << std::endl;
	if(!BenchmarkTool::Nodes->empty())
	{
		libssh2_exit();
	}
	return 0;
}
