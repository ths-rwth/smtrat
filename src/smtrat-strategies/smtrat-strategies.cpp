#include "smtrat-strategies.h"

#include "strategies/MCSATFMVSNL.h"

namespace smtrat {

void load_configured_strategy(Manager& m) {
	strategies::MCSATFMVSNL(m);
}

}