#pragma once

#include "PseudoBoolEncoder.h"
#include "PseudoBoolNormalizer.h"

namespace smtrat {
	// forward declaration
	class TotalizerTree;

	class TotalizerEncoder : public PseudoBoolEncoder {
		public:
			TotalizerEncoder() : PseudoBoolEncoder () {}

			bool canEncode(const ConstraintT& constraint);
			Rational encodingSize(const ConstraintT& constraint);

			string name() { return "TotalizerEncoder"; }


		protected:
			boost::optional<FormulaT> doEncode(const ConstraintT& constraint);

		private:
			
			PseudoBoolNormalizer mNormalizer;


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
