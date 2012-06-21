/* 
 * File:   GBSettings.h
 * Author: square
 *
 * Created on June 18, 2012, 7:50 PM
 */

#include <ginacra/MultivariatePolynomialMR.h>

#ifndef GBSETTINGS_H
#define	GBSETTINGS_H

namespace smtrat {
	
	struct GBSettings {
		typedef GiNaCRA::GradedLexicgraphic Order;
		typedef GiNaCRA::MultivariatePolynomialMR<Order> Polynomial;
		typedef GiNaCRA::MultivariateIdeal<Order> MultivariateIdeal;
		typedef GiNaCRA::BaseReductor<Order> Reductor;
	};
}

#endif	/* GBSETTINGS_H */

