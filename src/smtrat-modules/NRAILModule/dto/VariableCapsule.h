#pragma once

#include <carl/core/Variable.h>

namespace smtrat
{

    class VariableCapsule {

    public:
        VariableCapsule(const carl::Variable &xVariable, const carl::Variable &yVariable,
                        const carl::Variable &zVariable);
        carl::Variable xVariable;
        carl::Variable yVariable;
        carl::Variable zVariable;
        const carl::Variable &getXVariable() const;
        const carl::Variable &getYVariable() const;
        const carl::Variable &getZVariable() const;

    };
}