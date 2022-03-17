/**
* @file FMPlexModule.cpp
* @author Svenja Stein <svenja.stein@rwth-aachen.de>
*
* @version 2022-03-15
* Created on 2022-03-15.
*/

#include "FMPlexModule.h"

namespace smtrat {
	template<class Settings>
	FMPlexModule<Settings>::FMPlexModule(const ModuleInput* _formula, Conditionals& _foundAnswer, uint_fast64_t _varNumber, uint_fast64_t _constrNumber, Manager* _manager) :
	  Module(_formula, _foundAnswer, _manager), mVarNumber(_varNumber), mConstrNumber(_constrNumber){
		// Intentionally empty for now
	}

	template<typename Settings>
	bool FMPlexModule<Settings>::addCore(ModuleInput::const_iterator formula) {
		// TODO Implement
	}

	template<typename Settings>
	void FMPlexModule<Settings>::removeCore(ModuleInput::const_iterator formula) {
		// TODO Implement
	}

	template<typename Settings>
	Answer FMPlexModule<Settings>::checkCore() {
		// TODO Implement
	}

	template<typename Settings>
	void FMPlexModule<Settings>::updateModel() const {
		// TODO Implement
	}

	template<typename Settings>
	std::list<typename FMPlexModule<Settings>::ConstraintWithInfo> FMPlexModule<Settings>::fmplexCombine(boost::optional<carl::Variable> var, FMPlexModule::ConstraintWithInfo eliminator, std::list<ConstraintWithInfo>* sameBounds, std::list<ConstraintWithInfo>* oppositeBounds) {
		// TODO implement
	}

	template<typename Settings>
	void FMPlexModule<Settings>::resetBelow(typename std::list<FMPlexModule<Settings>::FmplexLvl>::iterator lvl) {
		mFMPlexBranch.erase(lvl, mFMPlexBranch.end());
	}

	/*** Nested Class FMPlexLvl Function Implementations ***/
	template<typename Settings>
	FMPlexModule<Settings>::FmplexLvl::FmplexLvl(std::list<ConstraintWithInfo> notUsed) : notUsed(notUsed){
		chooseVarAndDirection();
	}
	template<typename Settings>
	void FMPlexModule<Settings>::FmplexLvl::chooseVarAndDirection() {
		// TODO implement choice of different heuristics here based on settings
		baseHeuristicVarDir();
	}
	template<typename Settings>
	void FMPlexModule<Settings>::FmplexLvl::baseHeuristicVarDir() {
		// TODO implement: choose variable and direction, then set according class attributes.
	}
	template<typename Settings>
	void FMPlexModule<Settings>::FmplexLvl::chooseNextConstraint() {
		// TODO implement choice of different heuristics here based on settings
		baseHeuristicNextConstraint();
	}
	template<typename Settings>
	void FMPlexModule<Settings>::FmplexLvl::baseHeuristicNextConstraint() {
		assert(!todoConstraints.empty());
		// TODO implement: choose variable and direction, then set according class attributes.
	}
	}