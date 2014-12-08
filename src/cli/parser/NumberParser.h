#pragma once

#define BOOST_SPIRIT_USE_PHOENIX_V3
#include <boost/spirit/include/qi.hpp>

#include "Common.h"
#include "ParserTypes.h"

namespace smtrat {
namespace parser {

namespace spirit = boost::spirit;
namespace qi = boost::spirit::qi;
namespace px = boost::phoenix;

struct RationalPolicies : qi::ureal_policies<smtrat::Rational> {
    template <typename It, typename Attr>
    static bool parse_nan(It&, It const&, Attr&) { return false; }
    template <typename It, typename Attr>
    static bool parse_inf(It&, It const&, Attr&) { return false; }
};

struct IntegralParser : public qi::grammar<Iterator, Rational(), Skipper> {
    IntegralParser();
    qi::rule<Iterator, Rational(), Skipper> integral;
    qi::uint_parser<Rational,2,1,-1> binary;
    qi::uint_parser<Rational,10,1,-1> numeral;
    qi::uint_parser<Rational,16,1,-1> hexadecimal;
};
  
struct DecimalParser : qi::real_parser<Rational, RationalPolicies> {};

}
}

namespace boost { namespace spirit { namespace traits {
    template<> inline void scale(int exp, smtrat::Rational& r) {
        if (exp >= 0)
            r *= carl::pow(smtrat::Rational(10), (unsigned)exp);
        else
            r /= carl::pow(smtrat::Rational(10), (unsigned)(-exp));
    }
    template<> inline bool is_equal_to_one(const smtrat::Rational& value) {
        return value == 1;
    }
}}}