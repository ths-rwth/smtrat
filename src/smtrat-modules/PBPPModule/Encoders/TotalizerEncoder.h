#pragma once

#include "PseudoBoolEncoder.h"
#include "PseudoBoolNormalizer.h"

namespace smtrat {
	// forward declaration
	class TotalizerTree;

	/**
	 * TotalizerEncoder implements the Totalizer encoding as described in "Incremental Cardinality Constraints for MaxSAT" by Martins et al
	 * https://doi.org/10.1007/978-3-319-10428-7_39 
	 */
	class TotalizerEncoder : public PseudoBoolEncoder {
		public:
			TotalizerEncoder() : PseudoBoolEncoder () {}
			~TotalizerEncoder();


			bool canEncode(const ConstraintT& constraint);
			Rational encodingSize(const ConstraintT& constraint);

			string name() { return "TotalizerEncoder"; }


		protected:
			boost::optional<FormulaT> doEncode(const ConstraintT& constraint);

		private:
			// we need this cache because with recurring calls we might produce a tree multiple times although the set
			// of variables is identical, introducing a load of redundant variables.
			std::map<carl::Variables, TotalizerTree*> mTreeCache;
			map<carl::Variables, FormulaT> mSumPropagationFormulaCache;

			TotalizerTree buildTree(const std::set<carl::Variable>& variables);
			FormulaT encodeSumPropagation(TotalizerTree& tree);
			FormulaT encodeCardinalityRestriction(TotalizerTree& tree, Rational constantPart);

	};

	class TotalizerTree {
	public:
		TotalizerTree(const std::set<carl::Variable>& variables);

		~TotalizerTree() {
			if (mLeft) delete mLeft;
			if (mRight) delete mRight;
		}

		bool isLeaf() { return !(mLeft && mRight); }

		TotalizerTree& left() { 
			assert(mLeft != nullptr);
			return *mLeft; 
		}

		TotalizerTree& right() { 
			assert(mRight != nullptr);
			return *mRight; 
		}

		std::vector<carl::Variable> variables() { return mNodeVariables; }


	private:
		std::vector<carl::Variable> mNodeVariables;
		TotalizerTree* mLeft = nullptr;
		TotalizerTree* mRight = nullptr;
	};
}
