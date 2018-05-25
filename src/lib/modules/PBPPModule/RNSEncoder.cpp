#include "RNSEncoder.h"

#include <carl/numbers/PrimeFactory.h>

namespace smtrat {

	boost::optional<FormulaT> RNSEncoder::doEncode(const ConstraintT& constraint) {
		std::vector<Integer> base = calculateRNSBase(constraint);
		if(base.size() != 0 && isNonRedundant(base, constraint)){
			std::vector<FormulaT> subformulas;
			for(auto i : base){
				subformulas.push_back(rnsTransformation(constraint, i));
			}
			auto res = FormulaT(carl::FormulaType::AND, std::move(subformulas));
			SMTRAT_LOG_INFO("smtrat.pbc", constraint << " -> " << res);
			return res;
		}

		return {};
	}

	bool RNSEncoder::isNonRedundant(const std::vector<Integer>& base, const ConstraintT& formula) {
		const auto& cLHS = formula.lhs();
		Rational max = INT_MIN;
		Rational sum = 0;
		Rational product = 1;
		carl::PrimeFactory<Integer> pFactory;


		for(auto it : cLHS){
			if(it.coeff() > max){
				max = it.coeff();
			}
			sum += it.coeff();
		}

		for(auto it : base){
			if(it >= max){
				return false;
			}
		}

		for(Rational i = 0; i < max; i++){
			product *= pFactory.nextPrime();
		}

		if(sum > product){
			return false;
		}

		return true;
	}

	FormulaT RNSEncoder::rnsTransformation(const ConstraintT& formula, const Integer& prime) {
		const auto& cLHS = formula.lhs();
		assert(carl::isInteger(formula.constantPart()));
		Integer cRHS = carl::getNum(formula.constantPart());
		Poly newLHS;
		Rational newRHS = carl::mod(cRHS, prime);


		for(const auto& it : cLHS){
			// TODO actually, we only modify the coefficient. Is it enough to modify the coefficient?
			assert(carl::isInteger(it.coeff()));
			Integer newCoeff = carl::mod(carl::getNum(it.coeff()), prime);
			if(newCoeff != 0){
				newLHS += TermT(newCoeff, it.getSingleVariable(), 1);
			}
		}

		if(newLHS.size() == 0 && newRHS > 0){
			return FormulaT(carl::FormulaType::FALSE);
		}else if(newLHS.size() == 0 && newRHS == 0){
			return FormulaT(carl::FormulaType::TRUE);
		}

		Rational t = 0;
		for(const auto& it : newLHS){
			t += it.coeff();
		}
		t = carl::floor((t - newRHS) / prime );

		for(int i = 0; i < t; i++){
			// newLHS.push_back(std::pair<Rational, carl::Variable>(-t, carl::freshVariable(carl::VariableType::VT_BOOL)));
			newLHS += TermT(-t, carl::freshBooleanVariable(), 1);
		}

		ConstraintT newConstraint(newLHS - newRHS, carl::Relation::EQ);
		// TODO checkFormulaType is not our job, here
		// return checkFormulaType(FormulaT(newConstraint));
		return FormulaT(newConstraint);
	}

	std::vector<Integer> RNSEncoder::calculateRNSBase(const ConstraintT& formula) {
		const auto& cLHS = formula.lhs();
		std::vector<std::pair<int, Integer>> freq;
		Rational sum = 0;
		Rational product = 1;
		std::vector<Integer> base;

		for(auto it : cLHS){
			assert(carl::isInteger(it.coeff()));
			sum += carl::getNum(it.coeff());
		}

		for(auto it : cLHS){
			assert(carl::isInteger(it.coeff()));
			std::vector<Integer> v = integerFactorization(carl::getNum(it.coeff()));
			std::sort(v.begin(), v.end());
			v.erase( unique( v.begin(), v.end() ), v.end() );

			for(auto i : v){
				auto elem = std::find_if(freq.begin(), freq.end(),
						[&] (const pair<int, Integer>& elem){
						return elem.second == i;
						});
				if(elem != freq.end()){
					auto distance = std::distance(freq.begin(), elem);
					freq[(unsigned long) distance].first = freq[(unsigned long) distance].first + 1;
				}else{
					freq.push_back(std::pair<int, Integer>(1, i));
				}
			}
		}

		std::sort(freq.begin(), freq.end(),
				[&](const pair<int, Integer> &p1, const pair<int, Integer> &p2)
				{
				if(p1.first == p2.first){
				return (p1.second < p2.second);
				}else{
				return(p1.first > p2.first);
				}
				});


		for(auto it : freq){
			if(it.second != 0){
				product *= it.second;
				if(product <= sum){
					base.push_back(it.second);
				}else{
					base.push_back(it.second);
					break;
				}
			}

		}

		for(std::size_t i = 0; i < base.size(); i++){
			if(base[i] == 1 || base[i] == 0){
				base.erase(base.begin() +  (long) i);
			}
		}
		return base;
	}

	std::vector<Integer> RNSEncoder::integerFactorization(const Integer& coeff) {
		if(coeff <= 100){
			return mPrimesTable[carl::toInt<carl::uint>(coeff)];
		}

		std::vector<Integer> primes;
		Integer x = carl::ceil(carl::sqrt(coeff));
		Integer y = (x * x) - coeff;
		Integer r = carl::floor(carl::sqrt(y));

		if(coeff % 2 == 0){
			primes.emplace_back((carl::uint) 2);
			if(coeff / 2 > 2){
				std::vector<Integer> v = integerFactorization(coeff / 2);
				primes.insert(primes.end(), v.begin(), v.end());
			}
		}else{
			while(y >  r * r){
				x++;
				y = (x * x) - coeff;
				r = carl::floor(carl::sqrt(y));
			}

			Integer first = x + r;
			Integer second  = x - r;

			if(first > 1){
				if(first <= 100){
					std::vector<Integer> v = mPrimesTable[carl::toInt<carl::uint>(first)];
					primes.insert(primes.end(), v.begin(), v.end());

				}else{
					carl::PrimeFactory<Integer> pFactory;
					Integer prime = pFactory[24];
					while(prime < first){
						prime = pFactory.nextPrime();
					}
					if(prime == first){
						//first is a big prime number
						primes.push_back(first);
					}else{
						//first is not a prime number
						std::vector<Integer> v = integerFactorization(first);
						primes.insert(primes.end(), v.begin(), v.end());
					}
				}
			}

			if(second > 1){
				if(second <= 100){
					std::vector<Integer> v = mPrimesTable[carl::toInt<carl::uint>(second)];
					primes.insert(primes.end(), v.begin(), v.end());
				}else{
					carl::PrimeFactory<Integer> pFactory;
					Integer prime = pFactory[24];
					while(prime < second){
						prime = pFactory.nextPrime();
					}
					if(prime == second){
						//second is a big prime number
						primes.push_back(second);
					}else{
						//second is not a prime number
						std::vector<Integer> v = integerFactorization(second);
						primes.insert(primes.end(), v.begin(), v.end());
					}
				}
			}
		}
		return primes;
	}

	std::vector<std::vector<Integer>> RNSEncoder::primesTable() {
		//The 0 and 1 MUST be here in order to pick the right factorization!
		return {{0}, {1}, {2}, {3}, {2, 2}, {5}, {2, 3}, {7}, {2, 2, 2}, {3, 3}, {2, 5}, {11}, {2, 2, 3},
			{13}, {2, 7}, {3, 5}, {2, 2, 2, 2}, {17}, {2, 3, 3}, {19}, {2, 2, 5}, {3, 7}, {2, 11},
			{23}, {2, 2, 2, 3}, {5, 5}, {2, 13}, {3, 3, 3}, {2, 2, 7}, {29}, {2, 3, 5}, {31},
			{2, 2, 2, 2, 2}, {3, 11}, {2, 17}, {5, 7}, {2, 2, 3, 3}, {37}, {2, 19}, {3, 13}, {2, 2, 2, 5},
			{41}, {2, 3, 7}, {43}, {2, 2, 11}, {3, 3, 5}, {2, 23}, {47}, {2, 2, 2, 2, 3}, {7 ,7}, {2, 5, 5},
			{3, 17}, {2, 2, 13}, {53}, {2, 3, 3, 3}, {5, 11}, {2, 2, 2, 7}, {3, 19}, {2, 29}, {59},
			{2, 2, 3, 5}, {61}, {2, 31}, {3, 3, 7}, {2, 2, 2, 2, 2, 2}, {5, 13}, {2, 3, 11}, {67},
			{2, 2, 17}, {3, 23}, {2, 5, 7}, {71}, {2, 2, 2, 3, 3}, {73}, {2, 37}, {3, 5, 5}, {2, 2, 19},
			{7, 11}, {2, 3, 13}, {79}, {2, 2, 2, 2, 5}, {3, 3, 3, 3}, {2, 41}, {83}, {2, 2, 3, 7}, {5, 17},
			{2, 43}, {3, 29}, {2, 2, 2, 11}, {89}, {2, 3, 3, 5}, {7, 13}, {2, 2, 23}, {3, 31}, {2, 47},
			{5, 19}, {2, 2, 2, 2, 2, 3}, {97}, {2, 7, 7}, {3, 3, 11}, {2, 2, 5, 5}};
	}
}
