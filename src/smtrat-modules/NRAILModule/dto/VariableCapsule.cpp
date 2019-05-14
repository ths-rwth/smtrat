#include "VariableCapsule.h"

namespace smtrat {

    VariableCapsule::VariableCapsule(const carl::Variable &xVariable, const carl::Variable &yVariable,
                                     const carl::Variable &zVariable) : xVariable(xVariable), yVariable(yVariable),
                                                                        zVariable(zVariable) {}

    const carl::Variable &VariableCapsule::getXVariable() const {
        return xVariable;
    }

    const carl::Variable &VariableCapsule::getYVariable() const {
        return yVariable;
    }

    const carl::Variable &VariableCapsule::getZVariable() const {
        return zVariable;
    }
}