#ifndef SRC_LIB_MODULES_EQPREPROCESSINGMODULE_NNFREWRITER_H_
#define SRC_LIB_MODULES_EQPREPROCESSINGMODULE_NNFREWRITER_H_

#include <smtrat-common/smtrat-common.h>
#include <vector>

namespace smtrat {
	// to prepare for NNF transformation, replace all (except for xor for which this can drastically increase formula size)
	// formulas that contain "implicit" negations (=>, ITE, <=>) by their definition
	struct NNFPreparation {
		FormulaT rewrite_implication(const FormulaT&, FormulaT&& premise, FormulaT&& conclusion) {
			// A => B ----> (!A v B)
			return FormulaT(carl::OR, {FormulaT(carl::NOT, std::move(premise)), std::move(conclusion)});
		}

		FormulaT rewrite_ite(const FormulaT&, FormulaT&& condition, FormulaT&& trueCase, FormulaT&& falseCase) {
			// if(A) then B else C ----> (!A v B) & (A v C)
			return FormulaT(
				carl::AND,
				{FormulaT(carl::OR, {FormulaT(carl::NOT, std::move(condition)), std::move(trueCase)}),
				FormulaT(carl::OR, {std::move(condition), std::move(falseCase)})}
			);
		}

		FormulaT rewrite_iff(const FormulaT&, FormulaSetT&& subformulas) {
			// A <=> B <=> ... ----> (A & B & ...) v (!A & !B & ...)
			FormulaSetT negs;

			for(const FormulaT& formula : subformulas) {
				negs.emplace(carl::NOT, formula);
			}

			return FormulaT(
				carl::OR,
				{FormulaT(carl::AND, std::move(subformulas)),
				FormulaT(carl::AND, std::move(negs))}
			);
		}

		FormulaT rewrite_xor(const FormulaT&, FormulasMultiT&& subformulas) {
			// rewrite empty XORs to FALSE, this is probably not strictly required, but the NNFRewriter relies on XORs not being empty
			if(subformulas.empty()) {
				return FormulaT(carl::FALSE);
			} else {
				return FormulaT(carl::XOR, std::move(subformulas));
			}
		}
	};

	class NNFRewriter {
		public:
			// checks whether we are currently leaving the topmost first XOR-argument that we are below of in the AST
			struct remove_xor_first_arg {
				public:
					remove_xor_first_arg(NNFRewriter& r_, const FormulaT& f_) :
						r(r_), f(f_)
					{}

					~remove_xor_first_arg() {
						if(!r.xorFirstArgs.empty() && r.xorFirstArgs.back() == f) {
							r.xorFirstArgs.pop_back();
							--r.notCount;
						}
					}

				private:
					NNFRewriter& r;
					const FormulaT& f;
			};

			NNFRewriter() :
				notCount(0)
			{}

			void enter_not(const FormulaT&) {
				++notCount;
			}

			FormulaT rewrite_not(const FormulaT& formula, FormulaT&& subformula) {
				remove_xor_first_arg remover(*this, formula);
				--notCount;
				return std::move(subformula);
			}

			FormulaT rewrite_leaf(const FormulaT& formula) {
				remove_xor_first_arg remover(*this, formula);

				if(notCount % 2) {
					return FormulaT(carl::NOT, formula);
				} else {
					return formula;
				}
			}

			// normalize all inequalities to be (not (= x y)), distinct can cause (!= x y) which causes errors in CNF/SAT module and preprocessing
			FormulaT rewrite_ueq(const FormulaT& formula) {
				remove_xor_first_arg remove(*this, formula);
				const carl::UEquality& ueq = formula.uequality();

				if((notCount + (ueq.negated() ? 1 : 0)) % 2) {
					return FormulaT(carl::NOT, FormulaT(ueq.lhs(), ueq.rhs(), false));
				} else {
					return FormulaT(ueq.lhs(), ueq.rhs(), false);
				}
			}

			FormulaT rewrite_quantified(const FormulaT& formula, FormulaT&& subformula) {
				remove_xor_first_arg remover(*this, formula);

				if(notCount % 2) {
					return FormulaT(formula.type() == carl::EXISTS ? carl::FORALL : carl::EXISTS, formula.quantifiedVariables(), std::move(subformula));
				} else {
					return FormulaT(formula.type(), formula.quantifiedVariables(), std::move(subformula));
				}
			}

			FormulaT rewrite_or(const FormulaT& formula, FormulaSetT&& subformulas) {
				remove_xor_first_arg remover(*this, formula);

				if(notCount % 2) {
					return FormulaT(carl::AND, std::move(subformulas));
				} else {
					return FormulaT(carl::OR, std::move(subformulas));
				}
			}

			FormulaT rewrite_and(const FormulaT& formula, FormulaSetT&& subformulas) {
				remove_xor_first_arg remover(*this, formula);

				if(notCount % 2) {
					return FormulaT(carl::OR, std::move(subformulas));
				} else {
					return FormulaT(carl::AND, std::move(subformulas));
				}
			}

			// the only non-trivial case is XOR because it introduces an implicit negation that is not nice to remove in the preparation step;
			// keep a stack of all first arguments to an xor we are currently below of in the AST, and increment/decrement the not counter accordingly
			void enter_xor(const FormulaT& formula) {
				assert(!formula.subformulas().empty());
				xorFirstArgs.push_back(*formula.subformulas().begin());
				++notCount;
			}

			// (a ^ b ^ ...) ----> (!a ^ b ^ ...)
			FormulaT rewrite_xor(const FormulaT& formula, FormulasMultiT&& subformulas) {
				remove_xor_first_arg remover(*this, formula);
				return FormulaT(carl::XOR, std::move(subformulas));
			}

		private:
			std::vector<FormulaT> xorFirstArgs;
			std::size_t notCount;
	};
}

#endif /* SRC_LIB_MODULES_EQPREPROCESSINGMODULE_NNFREWRITER_H_ */
