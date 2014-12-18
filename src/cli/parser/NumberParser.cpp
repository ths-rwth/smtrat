#include "NumberParser.h"

namespace smtrat {
namespace parser {

	IntegralParser::IntegralParser() : IntegralParser::base_type(integral, "integral") {   
		integral = ("#b" > binary) | numeral | ("#x" > hexadecimal);
		integral.name("integral number");
	}
 

}
}