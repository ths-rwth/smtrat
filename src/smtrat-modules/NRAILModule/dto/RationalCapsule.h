#pragma once

#include <smtrat-common/smtrat-common.h>

namespace smtrat {

    class RationalCapsule {
    public:
        RationalCapsule(const Rational &aRational, const Rational &bRational,
                        const Rational &cRational);
        Rational aRational = aRational;
        Rational bRational = bRational;
        Rational cRational = cRational;

        const Rational &getARational() const;

        const Rational &getBRational() const;

        const Rational &getCRational() const;

    };

}
