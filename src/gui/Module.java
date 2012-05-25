/* SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
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
 *
 * @author Ulrich Loup
 * @since 2012-02-13
 * @version 2012-03-08
 */
class Module
{
    /// template of a module name
    private static final String MODULE_NAME = "MyModule";
    /// template of a module name
    private static final String MODULE_CONDITIONNAME = "MyCondition";
    /// template of a module header file
    private static final String MODULE_HEADER = "/*\r\n * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox\r\n * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges\r\n *\r\n * This file is part of SMT-RAT.\r\n *\r\n * SMT-RAT is free software: you can redistribute it and/or modify\r\n * it under the terms of the GNU General Public License as published by\r\n * the Free Software Foundation, either version 3 of the License, or\r\n * (at your option) any later version.\r\n *\r\n * SMT-RAT is distributed in the hope that it will be useful,\r\n * but WITHOUT ANY WARRANTY; without even the implied warranty of\r\n * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the\r\n * GNU General Public License for more details.\r\n *\r\n * You should have received a copy of the GNU General Public License\r\n * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.\r\n *\r\n */\r\n\r\n\r\n/**\r\n * @file "+MODULE_NAME+".h\r\n *\r\n */\r\n#ifndef SMTRAT_"+MODULE_NAME.toUpperCase()+"_H\r\n#define SMTRAT_"+MODULE_NAME.toLowerCase()+"_H\r\n\r\n#include \"../Module.h\"\r\n\r\nnamespace smtrat\r\n{\r\n/**\r\n * Module description.\r\n *\r\n * @author \r\n * @since \r\n * @version \r\n *\r\n */\r\nclass "+MODULE_NAME+": public Module\r\n{\r\npublic:\r\n    "+MODULE_NAME+"( Manager* const _tsManager );\r\n    virtual ~"+MODULE_NAME+"();\r\n\r\n    virtual bool inform( const Constraint* const );\r\n    virtual bool addConstraint( const Constraint* const );\r\n    virtual Answer isConsistent();\r\n    virtual void pushBacktrackPoint();    virtual void popBacktrackPoint();\r\n};\r\n\r\n}    // namespace smtrat\r\n#endif   /** SMTRAT_"+MODULE_NAME.toUpperCase()+"_H */\r\n";
    /// template of a module implementation file
    private static final String MODULE_IMPLEMENTATION = "/*\r\n * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox\r\n * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges\r\n *\r\n * This file is part of SMT-RAT.\r\n *\r\n * SMT-RAT is free software: you can redistribute it and/or modify\r\n * it under the terms of the GNU General Public License as published by\r\n * the Free Software Foundation, either version 3 of the License, or\r\n * (at your option) any later version.\r\n *\r\n * SMT-RAT is distributed in the hope that it will be useful,\r\n * but WITHOUT ANY WARRANTY; without even the implied warranty of\r\n * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the\r\n * GNU General Public License for more details.\r\n *\r\n * You should have received a copy of the GNU General Public License\r\n * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.\r\n *\r\n */\r\n\r\n\r\n/**\r\n * @file MyModule.cpp\r\n *\r\n */\r\n\r\n#include \""+MODULE_NAME+".h\"\r\n\r\nnamespace smtrat\r\n{\r\n    "+MODULE_NAME+"::"+MODULE_NAME+"( Manager* const _tsManager ) : Module( _tsManager )\r\n    {\r\n        mModuleType = "+MODULE_CONDITIONNAME+";\r\n    }\r\n\n    "+MODULE_NAME+"::~"+MODULE_NAME+"() {}\r\n\r\n    bool "+MODULE_NAME+"::inform( const Constraint* const _constraint )\r\n    {\r\n        // write your implementation here\r\n    }\r\n\n    bool "+MODULE_NAME+"::addConstraint( const Constraint* const _constraint )\r\n    {\r\n        Module::addConstraint( _constraint );\r\n        // write your implementation here\r\n    }\r\n\n    Answer "+MODULE_NAME+"::isConsistent()\r\n    {\r\n        // write your implementation here\r\n    }\r\n\n    void "+MODULE_NAME+"::pushBacktrackPoint()\r\n    {\r\n        Module::pushBacktrackPoint();\r\n        // write your implementation here\r\n    }\r\n\n    void "+MODULE_NAME+"::popBacktrackPoint()\r\n    {\r\n        // write your implementation here\r\n        "+MODULE_NAME+"::popBacktrackPoint();\r\n    }\r\n\n}    // namespace smtrat\r\n";
    /// the standard prefix of module type strings
    private static final String MODULETYPE_PREFIX = "MT_";
    /// the name string of this Module
    private String name;
    /// the type string of this Module
    private String type;

    /**
     * Constructs a module with name and type.
     * @param type
     */
    public Module( String name, String type )
    {
        if( !name.endsWith( "Module" ) ) // the module name should end with "Module"
            name = name + "Module";
        this.name = name;
        this.type = type;
    }

    /**
     * Constructs a module with name = type.
     * @param name
     */
    public Module( String name )
    {
        if( !name.endsWith( "Module" ) ) // the module name should end with "Module"
            name = name + "Module";
        this.name = name;
        this.type = MODULETYPE_PREFIX + name;
    }

    /**
     * This method returns the type, which is more an internal data field. The name is returned by toString().
     * @return type of this string
     */
    public String type()
    {
        return this.type;
    }

    /**
     * Generate the contents of a header file implementing this module.
     * @return string representing the contents of a header file implementing this module
     */
    public String generateHeader()
    {
        return MODULE_HEADER.replaceAll( MODULE_NAME, this.name ).replaceAll( MODULE_NAME.toUpperCase(), this.name.toUpperCase() );
    }

    /**
     * Generate the contents of a cpp file implementing this module.
     * @return string representing the contents of a cpp file implementing this module
     */
    public String generateImplementation()
    {
        return MODULE_IMPLEMENTATION.replaceAll( MODULE_NAME, this.name ).replaceAll( MODULE_NAME.toUpperCase(), this.name.toUpperCase() ).replaceAll( MODULE_CONDITIONNAME, this.type );
    }

    public String toString()
    {
        return this.name;
    }

    public boolean equals( Object o )
    {
        if( !(o instanceof Module) )
            return false;
        return this.type == ((Module) o).type;
    }
}