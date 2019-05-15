#include "RationalCapsule.h"

namespace smtrat {

    RationalCapsule::RationalCapsule(const Rational &aRational, const Rational &bRational,
                                     const Rational &cRational) : aRational(aRational), bRational(bRational),
                                                                  cRational(cRational) {}

    const smtrat::Rational &smtrat::RationalCapsule::getARational() const {
        return aRational;
    }

    const smtrat::Rational &smtrat::RationalCapsule::getBRational() const {
        return bRational;
    }

    const smtrat::Rational &smtrat::RationalCapsule::getCRational() const {
        return cRational;
    }
}