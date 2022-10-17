#pragma once

#include "Tableau.h"
#include <smtrat-common/smtrat-common.h>

class Level {
    public:
        Level(){}

    private:
        Tableau m_tableau;
        carl::Bitset m_tried_rows;
        carl::Bitset m_open_rows;
};