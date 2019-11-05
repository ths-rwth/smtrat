#include"TotalizerEncoder.h"

namespace smtrat {
	boost::optional<FormulaT> TotalizerEncoder::doEncode(const ConstraintT& constraint) {
		assert(canEncode(constraint) && "Input must be <=-cardinality constraint.");

		auto treeIt = mTreeCache.find(constraint.variables().underlyingVariableSet());
		if (treeIt == mTreeCache.end()) {
			TotalizerTree* tree = new TotalizerTree(constraint.variables().underlyingVariableSet());
			mTreeCache.insert(std::map<carl::Variables, TotalizerTree*>::value_type(constraint.variables().underlyingVariableSet(), tree));
			mSumPropagationFormulaCache.insert(std::map<carl::Variables, FormulaT>::value_type(constraint.variables().underlyingVariableSet(), encodeSumPropagation(*tree)));
		}

		TotalizerTree* tree = mTreeCache[constraint.variables().underlyingVariableSet()];

		// traverse non-leaf nodes and construct formula
		FormulaT sumPropagation = mSumPropagationFormulaCache[constraint.variables().underlyingVariableSet()];
		FormulaT cardinalityRestriction = encodeCardinalityRestriction(*tree, carl::abs(constraint.constantPart()));

		return FormulaT(carl::FormulaType::AND, sumPropagation, cardinalityRestriction);
	}

	FormulaT TotalizerEncoder::encodeSumPropagation(TotalizerTree& tree) {
		if (tree.isLeaf()) return FormulaT(carl::FormulaType::TRUE);

		// build sums for current non-leaf
		std::vector<carl::Variable> leftVars = tree.left().variables();
		std::vector<carl::Variable> rightVars = tree.right().variables();

		SMTRAT_LOG_TRACE("smtrat.pbpp.total", "Having rootVars = " << tree.variables() << ", leftVars = " << leftVars << ", rightVars = " << rightVars);

		FormulasT encoding;
		for (size_t alpha = 0; alpha <= leftVars.size(); alpha++) {
			for (size_t beta = 0; beta <= rightVars.size(); beta++) {
				size_t sigma = alpha + beta;
				FormulaT leftNode;
				FormulaT rightNode;
				FormulaT rootNode;

				if (alpha != 0) {
					leftNode = !FormulaT(leftVars[alpha - 1]);
				}

				if (beta != 0) {
					rightNode = !FormulaT(rightVars[beta - 1]);
				}

				if (sigma == 0) {
					rootNode = FormulaT(carl::FormulaType::TRUE);
				} else {
					rootNode = FormulaT(tree.variables().at(sigma - 1));
				}

				FormulaT nodeSum = FormulaT(carl::FormulaType::OR, leftNode, rightNode, rootNode);
				SMTRAT_LOG_TRACE("smtrat.pbpp.total", "Adding for alpha =" << alpha << ", beta = " << beta << ", sigma = " << sigma << ": " << nodeSum);
				encoding.push_back(nodeSum);
			}
		}

		encoding.push_back(encodeSumPropagation(tree.left()));
		encoding.push_back(encodeSumPropagation(tree.right()));

		return FormulaT(carl::FormulaType::AND, encoding);

	}

	FormulaT TotalizerEncoder::encodeCardinalityRestriction(TotalizerTree& root, Rational constantPart) {
		std::vector<carl::Variable> vars = root.variables();

		SMTRAT_LOG_TRACE("smtrat.pbpp.total", "Restricting to " << constantPart << ": " << vars);

		FormulasT encoding;
		for (size_t i = vars.size() - 1; i >= 0; i--) { 
			if (Rational(i) < constantPart) break; // abort when we reach constantPart var
			SMTRAT_LOG_TRACE("smtrat.pbpp.total", "Forcing variable " << vars[i]  << " at index " << i << " to false");
			encoding.push_back(!FormulaT(vars[i]));

			if (i == 0) break; // underflow protection
		}

		SMTRAT_LOG_TRACE("smtrat.pbpp.total", "Those literals are added to assure cardinality: " << encoding);
		return FormulaT(carl::FormulaType::AND, encoding);
	}

	bool TotalizerEncoder::canEncode(const ConstraintT& constraint) {
		bool encodable = true;
		bool allCoeffPositive = true;
		bool allCoeffNegative = true;

		for (const auto& it : constraint.lhs()) {
			if (it.isConstant()) continue;

			encodable = encodable && (it.coeff() == 1 || it.coeff() == -1);
			if (it.coeff() < 0) allCoeffPositive = false;
			if (it.coeff() > 0) allCoeffNegative = false;
		}

		encodable = encodable && allCoeffNegative != allCoeffPositive;
		encodable = encodable && constraint.relation() == carl::Relation::LEQ;

		return encodable;
	}

	Rational TotalizerEncoder::encodingSize(const ConstraintT& constraint) {
		std::size_t nVars = constraint.variables().size();

		return carl::log(Rational(nVars)) * nVars;
	}

	TotalizerTree::TotalizerTree(const std::set<carl::Variable>& variables) {
		if (variables.size() == 1) {
			// just keep the variable
			SMTRAT_LOG_TRACE("smtrat.pbpp.total", "Adding leaf " << *(variables.begin()) );
			mNodeVariables.push_back(*(variables.begin()));
			return;
		}

		// create size() many new variables save it to this node
		for (size_t i = 0; i < variables.size(); i++) {
			mNodeVariables.push_back(carl::freshBooleanVariable());
		}

		SMTRAT_LOG_TRACE("smtrat.pbpp.total", "Partitioning node variables " << mNodeVariables);

		// partition variables
		std::set<carl::Variable> leftVariables;
		std::set<carl::Variable> rightVariables;

		std::vector<carl::Variable> varVector(variables.begin(), variables.end());
		int i = -1;
		auto separator = std::partition(varVector.begin(), varVector.end(), [&](const carl::Variable&){ 
			i++;
			return i % 2 == 0; 
		});

		for (auto it = varVector.begin(); it != separator; it++) {
			rightVariables.insert(*it);
		}

		for (auto it = separator; it != varVector.end(); it++) {
			leftVariables.insert(*it);
		}

		assert(leftVariables.size() != 0);
		assert(rightVariables.size() != 0);

		// create children recursively
		SMTRAT_LOG_TRACE("smtrat.pbpp.total", "Adding child left " << leftVariables);
		SMTRAT_LOG_TRACE("smtrat.pbpp.total", "Adding child right " << rightVariables);
		mLeft = new TotalizerTree(leftVariables);
		mRight = new TotalizerTree(rightVariables);

	}

	TotalizerEncoder::~TotalizerEncoder() {
		for (const auto& it : mTreeCache) {
			delete it.second;
		}
	}
}

