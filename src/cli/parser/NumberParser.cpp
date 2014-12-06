#include "NumberParser.h"

#include <boost/spirit/include/phoenix_bind.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_object.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>

namespace smtrat {
namespace parser {

	IntegralParser::IntegralParser() : IntegralParser::base_type(integral, "integral") {   
		integral = ("#b" > binary) | numeral | ("#x" > hexadecimal);
		integral.name("integral number");
	}
 

}
}