#ifndef SRC_LIB_MODULES_EQPREPROCESSINGMODULE_FORMULAVISITOR_HPP_
#define SRC_LIB_MODULES_EQPREPROCESSINGMODULE_FORMULAVISITOR_HPP_

#include <smtrat-common/smtrat-common.h>

#include <utility>
#include <type_traits>

namespace smtrat {
// helper macro to determine whether a type T declares a member
// with the name given as argument. This is determined at compile-time using SFINAE.
#define SMTRAT_HAS_DECL(name) \
	template<typename T> struct has_decl_##name {\
		private:\
			template<typename C> static std::true_type check(decltype(&C::name));\
			template<typename C> static std::false_type check(...);\
		\
		public:\
			constexpr static bool value = decltype(check<T>(nullptr))::value;\
			typedef decltype(check<T>(nullptr)) type;\
	}

	template<typename T> struct default_compare {
		typedef std::less<T> type;
	};

	template<> struct default_compare<void> {
		typedef void type;
	};

	template<typename T> struct default_allocator {
		typedef std::allocator<T> type;
	};

	template<> struct default_allocator<void> {
		typedef void type;
	};

	template<
		typename ConcreteType,
		typename ResultType,
		typename Compare = typename default_compare<ResultType>::type,
		typename Allocator = typename default_allocator<ResultType>::type
	> class formula_visitor {
		public:
			typedef ResultType result_type;
			typedef Compare compare_type;
			typedef Allocator allocator_type;

			typedef std::set<result_type, compare_type, allocator_type> set_type;
			//typedef std::multiset<result_type, compare_type, allocator_type> multiset_type;
			typedef FormulasMultiT multiset_type;

			ResultType apply(const FormulaT& formula) {
				return P_dispatch(formula);
			}

		protected:
			formula_visitor() = default;
			~formula_visitor() = default;

		private:
			#define SMTRAT_DISP_TAG(name) (typename has_decl_##name<ConcreteType>::type{})

			// the ConcreteType deriving from this formula_visitor template
			// class can declare any subset of methods with the names visit_*.
			// these methods will then be called on any formula passed into the apply method
			// and all of its subformulas. There also are visit_default (all otherwise untreated formulas),
			// visit_leaf (all leafs of the AST) and visit_quantified methods to handle more than one type at once.
			// this occurs recursively, starting with the leaf nodes of the formula AST,
			// and the result of all child nodes of the AST is passed into the visit method.
			// for an example, look at the formula_rewriter class template.
			SMTRAT_HAS_DECL(visit_default);
			SMTRAT_HAS_DECL(visit_or);
			SMTRAT_HAS_DECL(visit_and);
			SMTRAT_HAS_DECL(visit_xor);
			SMTRAT_HAS_DECL(visit_iff);
			SMTRAT_HAS_DECL(visit_ite);
			SMTRAT_HAS_DECL(visit_implication);
			SMTRAT_HAS_DECL(visit_not);
			SMTRAT_HAS_DECL(visit_bool);
			SMTRAT_HAS_DECL(visit_constraint);
			SMTRAT_HAS_DECL(visit_true);
			SMTRAT_HAS_DECL(visit_false);
			SMTRAT_HAS_DECL(visit_ueq);
			SMTRAT_HAS_DECL(visit_forall);
			SMTRAT_HAS_DECL(visit_exists);
			SMTRAT_HAS_DECL(visit_quantified);
			SMTRAT_HAS_DECL(visit_leaf);

			// the enter methods are only called if they are available
			// any result they compute is discarded, but they can be used to
			// alter the visitors state (keep a stack of predecessor nodes, ...)
			SMTRAT_HAS_DECL(enter_default);
			SMTRAT_HAS_DECL(enter_or);
			SMTRAT_HAS_DECL(enter_and);
			SMTRAT_HAS_DECL(enter_xor);
			SMTRAT_HAS_DECL(enter_iff);
			SMTRAT_HAS_DECL(enter_ite);
			SMTRAT_HAS_DECL(enter_implication);
			SMTRAT_HAS_DECL(enter_not);
			SMTRAT_HAS_DECL(enter_bool);
			SMTRAT_HAS_DECL(enter_constraint);
			SMTRAT_HAS_DECL(enter_true);
			SMTRAT_HAS_DECL(enter_false);
			SMTRAT_HAS_DECL(enter_ueq);
			SMTRAT_HAS_DECL(enter_forall);
			SMTRAT_HAS_DECL(enter_exists);
			SMTRAT_HAS_DECL(enter_quantified);
			SMTRAT_HAS_DECL(enter_leaf);

			// these methods are "seamless" templates to ensure only the right overload is ever instantiated;
			// instantiating the wrong overload may cause compile-time errors due to calling non-existing methods
			template<typename = void> result_type P_visit_default(const FormulaT& formula, std::true_type) {
				return static_cast<ConcreteType*>(this)->visit_default(formula);
			}

			template<typename = void> result_type P_visit_default(const FormulaT&, std::false_type) {
				return result_type{};
			}

			result_type P_visit_default(const FormulaT& formula) {
				return P_visit_default(formula, SMTRAT_DISP_TAG(visit_default));
			}

			template<typename = void> result_type P_visit_or(const FormulaT& formula, set_type&& child_results, std::true_type) {
				return static_cast<ConcreteType*>(this)->visit_or(formula, std::move(child_results));
			}

			template<typename = void> result_type P_visit_or(const FormulaT& formula, set_type&&, std::false_type) {
				return P_visit_default(formula);
			}

			template<typename = void> result_type P_visit_xor(const FormulaT& formula, multiset_type&& child_results, std::true_type) {
				return static_cast<ConcreteType*>(this)->visit_xor(formula, std::move(child_results));
			}

			template<typename = void> result_type P_visit_xor(const FormulaT& formula, multiset_type&&, std::false_type) {
				return P_visit_default(formula);
			}

			template<typename = void> result_type P_visit_and(const FormulaT& formula, set_type&& child_results, std::true_type) {
				return static_cast<ConcreteType*>(this)->visit_and(formula, std::move(child_results));
			}

			template<typename = void> result_type P_visit_and(const FormulaT& formula, set_type&&, std::false_type) {
				return P_visit_default(formula);
			}

			template<typename = void> result_type P_visit_iff(const FormulaT& formula, set_type&& child_results, std::true_type) {
				return static_cast<ConcreteType*>(this)->visit_iff(formula, std::move(child_results));
			}

			template<typename = void> result_type P_visit_iff(const FormulaT& formula, set_type&&, std::false_type) {
				return P_visit_default(formula);
			}

			template<typename = void> result_type P_visit_not(const FormulaT& formula, result_type&& child_result, std::true_type) {
				return static_cast<ConcreteType*>(this)->visit_not(formula, std::move(child_result));
			}

			template<typename = void> result_type P_visit_not(const FormulaT& formula, result_type&&, std::false_type) {
				return P_visit_default(formula);
			}

			template<typename = void> result_type P_visit_exists(const FormulaT& formula, result_type&& child_result, std::true_type) {
				return static_cast<ConcreteType*>(this)->visit_exists(formula, std::move(child_result));
			}

			template<typename = void> result_type P_visit_exists(const FormulaT& formula, result_type&& child_result, std::false_type) {
				return P_visit_quantified(formula, std::move(child_result), SMTRAT_DISP_TAG(visit_quantified));
			}

			template<typename = void> result_type P_visit_forall(const FormulaT& formula, result_type&& child_result, std::true_type) {
				return static_cast<ConcreteType*>(this)->visit_forall(formula, std::move(child_result));
			}

			template<typename = void> result_type P_visit_forall(const FormulaT& formula, result_type&& child_result, std::false_type) {
				return P_visit_quantified(formula, std::move(child_result), SMTRAT_DISP_TAG(visit_quantified));
			}

			template<typename = void> result_type P_visit_quantified(const FormulaT& formula, result_type&& child_result, std::true_type) {
				return static_cast<ConcreteType*>(this)->visit_quantified(formula, std::move(child_result));
			}

			template<typename = void> result_type P_visit_quantified(const FormulaT& formula, result_type&&, std::false_type) {
				return P_visit_default(formula);
			}

			template<typename = void> result_type P_visit_leaf(const FormulaT& formula, std::true_type) {
				return static_cast<ConcreteType*>(this)->visit_leaf(formula);
			}

			template<typename = void> result_type P_visit_leaf(const FormulaT& formula, std::false_type) {
				return P_visit_default(formula);
			}

			result_type P_visit_leaf(const FormulaT& formula) {
				return P_visit_leaf(formula, SMTRAT_DISP_TAG(visit_leaf));
			}

			template<typename = void> result_type P_visit_true(const FormulaT& formula, std::true_type) {
				return static_cast<ConcreteType*>(this)->visit_true(formula);
			}

			template<typename = void> result_type P_visit_true(const FormulaT& formula, std::false_type) {
				return P_visit_leaf(formula);
			}

			template<typename = void> result_type P_visit_false(const FormulaT& formula, std::true_type) {
				return static_cast<ConcreteType*>(this)->visit_false(formula);
			}

			template<typename = void> result_type P_visit_false(const FormulaT& formula, std::false_type) {
				return P_visit_leaf(formula);
			}

			template<typename = void> result_type P_visit_ueq(const FormulaT& formula, std::true_type) {
				return static_cast<ConcreteType*>(this)->visit_ueq(formula);
			}

			template<typename = void> result_type P_visit_ueq(const FormulaT& formula, std::false_type) {
				return P_visit_leaf(formula);
			}

			template<typename = void> result_type P_visit_constraint(const FormulaT& formula, std::true_type) {
				return static_cast<ConcreteType*>(this)->visit_constraint(formula);
			}

			template<typename = void> result_type P_visit_constraint(const FormulaT& formula, std::false_type) {
				return P_visit_leaf(formula);
			}

			template<typename = void> result_type P_visit_bool(const FormulaT& formula, std::true_type) {
				return static_cast<ConcreteType*>(this)->visit_bool(formula);
			}

			template<typename = void> result_type P_visit_bool(const FormulaT& formula, std::false_type) {
				return P_visit_leaf(formula);
			}

			template<typename = void> result_type P_visit_implication(const FormulaT& formula, result_type&& premise_result, result_type&& conclusion_result, std::true_type) {
				return static_cast<ConcreteType*>(this)->visit_implication(formula, std::move(premise_result), std::move(conclusion_result));
			}

			template<typename = void> result_type P_visit_implication(const FormulaT& formula, result_type&&, result_type&&, std::false_type) {
				return P_visit_default(formula);
			}

			template<typename = void> result_type P_visit_ite(const FormulaT& formula, result_type&& condition_result, result_type&& true_case_result, result_type&& false_case_result, std::true_type) {
				return static_cast<ConcreteType*>(this)->visit_ite(formula, std::move(condition_result), std::move(true_case_result), std::move(false_case_result));
			}

			template<typename = void> result_type P_visit_ite(const FormulaT& formula, result_type&&, result_type&&, result_type&&, std::false_type) {
				return P_visit_default(formula);
			}

			template<typename = void> void P_enter_default(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_default(formula);
			}

			template<typename = void> void P_enter_default(const FormulaT&, std::false_type) {}

			void P_enter_default(const FormulaT& formula) {
				P_enter_default(formula, SMTRAT_DISP_TAG(enter_default));
			}

			template<typename = void> void P_enter_or(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_or(formula);
			}

			template<typename = void> void P_enter_or(const FormulaT& formula, std::false_type) { P_enter_default(formula); }

			template<typename = void> void P_enter_and(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_and(formula);
			}

			template<typename = void> void P_enter_and(const FormulaT& formula, std::false_type) {  P_enter_default(formula); }

			template<typename = void> void P_enter_xor(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_xor(formula);
			}

			template<typename = void> void P_enter_xor(const FormulaT& formula, std::false_type) {  P_enter_default(formula); }

			template<typename = void> void P_enter_iff(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_iff(formula);
			}

			template<typename = void> void P_enter_iff(const FormulaT& formula, std::false_type) {  P_enter_default(formula); }

			template<typename = void> void P_enter_not(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_not(formula);
			}

			template<typename = void> void P_enter_not(const FormulaT& formula, std::false_type) {  P_enter_default(formula); }

			template<typename = void> void P_enter_ite(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_ite(formula);
			}

			template<typename = void> void P_enter_ite(const FormulaT& formula, std::false_type) {  P_enter_default(formula); }

			template<typename = void> void P_enter_implication(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_implication(formula);
			}

			template<typename = void> void P_enter_implication(const FormulaT& formula, std::false_type) { P_enter_default(formula); }

			template<typename = void> void P_enter_quantified(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_quantified(formula);
			}

			template<typename = void> void P_enter_quantified(const FormulaT& formula, std::false_type) { P_enter_default(formula); }

			template<typename = void> void P_enter_exists(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_exists(formula);
			}

			template<typename = void> void P_enter_exists(const FormulaT& formula, std::false_type) {
				P_enter_quantified(formula, SMTRAT_DISP_TAG(enter_quantified));
			}

			template<typename = void> void P_enter_forall(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_forall(formula);
			}

			template<typename = void> void P_enter_forall(const FormulaT& formula, std::false_type) {
				P_enter_quantified(formula, SMTRAT_DISP_TAG(enter_quantified));
			}

			template<typename = void> void P_enter_leaf(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_leaf(formula);
			}

			template<typename = void> void P_enter_leaf(const FormulaT& formula, std::false_type) {
				P_enter_default(formula);
			}

			void P_enter_leaf(const FormulaT& formula) {
				P_enter_leaf(formula, SMTRAT_DISP_TAG(enter_leaf));
			}

			template<typename = void> void P_enter_true(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_true(formula);
			}

			template<typename = void> void P_enter_true(const FormulaT& formula, std::false_type) {
				P_enter_leaf(formula);
			}

			template<typename = void> void P_enter_false(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_false(formula);
			}

			template<typename = void> void P_enter_false(const FormulaT& formula, std::false_type) {
				P_enter_leaf(formula);
			}

			template<typename = void> void P_enter_ueq(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_ueq(formula);
			}

			template<typename = void> void P_enter_ueq(const FormulaT& formula, std::false_type) {
				P_enter_leaf(formula);
			}

			template<typename = void> void P_enter_constraint(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_constraint(formula);
			}

			template<typename = void> void P_enter_constraint(const FormulaT& formula, std::false_type) {
				P_enter_leaf(formula);
			}

			template<typename = void> void P_enter_bool(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_bool(formula);
			}

			template<typename = void> void P_enter_bool(const FormulaT& formula, std::false_type) {
				P_enter_leaf(formula);
			}

			result_type P_dispatch(const FormulaT& formula) {
				// make sure that ConcreteType is a complete type
				constexpr std::size_t require_complete_type = sizeof(ConcreteType);
				(void)require_complete_type;

				switch(formula.getType()) {
					case carl::OR: {
						P_enter_or(formula, SMTRAT_DISP_TAG(enter_or));

						set_type results;

						for(const FormulaT& subformula : formula.subformulas()) {
							results.insert(P_dispatch(subformula));
						}

						return P_visit_or(formula, std::move(results), SMTRAT_DISP_TAG(visit_or));
					}

					case carl::AND: {
						P_enter_and(formula, SMTRAT_DISP_TAG(enter_and));

						set_type results;

						for(const FormulaT& subformula : formula.subformulas()) {
							results.insert(P_dispatch(subformula));
						}

						return P_visit_and(formula, std::move(results), SMTRAT_DISP_TAG(visit_and));
					}

					case carl::XOR: {
						P_enter_xor(formula, SMTRAT_DISP_TAG(enter_xor));

						multiset_type results;

						for(const FormulaT& subformula : formula.subformulas()) {
							results.insert(P_dispatch(subformula));
						}

						return P_visit_xor(formula, std::move(results), SMTRAT_DISP_TAG(visit_xor));
					}

					case carl::IFF: {
						P_enter_iff(formula, SMTRAT_DISP_TAG(enter_iff));

						set_type results;

						for(const FormulaT& subformula : formula.subformulas()) {
							results.insert(P_dispatch(subformula));
						}

						return P_visit_iff(formula, std::move(results), SMTRAT_DISP_TAG(visit_iff));
					}

					case carl::NOT: {
						P_enter_not(formula, SMTRAT_DISP_TAG(enter_not));
						result_type result(P_dispatch(formula.subformula()));
						return P_visit_not(formula, std::move(result), SMTRAT_DISP_TAG(visit_not));
					}

					case carl::TRUE: {
						P_enter_true(formula, SMTRAT_DISP_TAG(enter_true));
						return P_visit_true(formula, SMTRAT_DISP_TAG(visit_true));
					}

					case carl::FALSE: {
						P_enter_false(formula, SMTRAT_DISP_TAG(enter_false));
						return P_visit_false(formula, SMTRAT_DISP_TAG(visit_false));
					}

					case carl::BOOL: {
						P_enter_bool(formula, SMTRAT_DISP_TAG(enter_bool));
						return P_visit_bool(formula, SMTRAT_DISP_TAG(visit_bool));
					}

					case carl::UEQ: {
						P_enter_ueq(formula, SMTRAT_DISP_TAG(enter_ueq));
						return P_visit_ueq(formula, SMTRAT_DISP_TAG(visit_ueq));
					}

					case carl::CONSTRAINT: {
						P_enter_constraint(formula, SMTRAT_DISP_TAG(enter_constraint));
						return P_visit_constraint(formula, SMTRAT_DISP_TAG(visit_constraint));
					}

					case carl::EXISTS: {
						P_enter_exists(formula, SMTRAT_DISP_TAG(enter_exists));
						result_type result(P_dispatch(formula.quantifiedFormula()));
						return P_visit_exists(formula, std::move(result), SMTRAT_DISP_TAG(visit_exists));
					}

					case carl::FORALL: {
						P_enter_forall(formula, SMTRAT_DISP_TAG(enter_forall));
						result_type result(P_dispatch(formula.quantifiedFormula()));
						return P_visit_forall(formula, std::move(result), SMTRAT_DISP_TAG(visit_forall));
					}

					case carl::IMPLIES: {
						P_enter_implication(formula, SMTRAT_DISP_TAG(enter_implication));
						result_type premise(P_dispatch(formula.premise()));
						result_type conclusion(P_dispatch(formula.conclusion()));
						return P_visit_implication(formula, std::move(premise), std::move(conclusion), SMTRAT_DISP_TAG(visit_implication));
					}

					case carl::ITE: {
						P_enter_ite(formula, SMTRAT_DISP_TAG(enter_ite));
						result_type condition(P_dispatch(formula.condition()));
						result_type true_case(P_dispatch(formula.firstCase()));
						result_type false_case(P_dispatch(formula.secondCase()));
						return P_visit_ite(formula, std::move(condition), std::move(true_case), std::move(false_case), SMTRAT_DISP_TAG(visit_ite));
					}

					default: {
						assert(false && "Unexpected formula encountered!");
						P_enter_default(formula);
						return P_visit_default(formula);
					}
				}
			}
			#undef SMTRAT_DISP_TAG
	};

	/**
	 * This is a specialization of the formula_visitor template for a void result type.
	 * In that case, no sets of intermediate results are computed and maintained.
	 * Visitors with a void result are useful e.g. to collect all subformulas with certain properties.
	 * For an example, see BoolUEQRewriter.h/CollectBoolsInUEQs.
	 */
	template<
		typename ConcreteType,
		typename Compare,
		typename Allocator
	> class formula_visitor<ConcreteType, void, Compare, Allocator> {
		public:
			typedef void result_type;

			void apply(const FormulaT& formula) {
				P_dispatch(formula);
			}

		private:
			#define SMTRAT_DISP_TAG(name) (typename has_decl_##name<ConcreteType>::type{})

			SMTRAT_HAS_DECL(visit_default);
			SMTRAT_HAS_DECL(visit_or);
			SMTRAT_HAS_DECL(visit_and);
			SMTRAT_HAS_DECL(visit_xor);
			SMTRAT_HAS_DECL(visit_iff);
			SMTRAT_HAS_DECL(visit_ite);
			SMTRAT_HAS_DECL(visit_implication);
			SMTRAT_HAS_DECL(visit_not);
			SMTRAT_HAS_DECL(visit_bool);
			SMTRAT_HAS_DECL(visit_constraint);
			SMTRAT_HAS_DECL(visit_true);
			SMTRAT_HAS_DECL(visit_false);
			SMTRAT_HAS_DECL(visit_ueq);
			SMTRAT_HAS_DECL(visit_forall);
			SMTRAT_HAS_DECL(visit_exists);
			SMTRAT_HAS_DECL(visit_quantified);
			SMTRAT_HAS_DECL(visit_leaf);
			SMTRAT_HAS_DECL(enter_default);
			SMTRAT_HAS_DECL(enter_or);
			SMTRAT_HAS_DECL(enter_and);
			SMTRAT_HAS_DECL(enter_xor);
			SMTRAT_HAS_DECL(enter_iff);
			SMTRAT_HAS_DECL(enter_ite);
			SMTRAT_HAS_DECL(enter_implication);
			SMTRAT_HAS_DECL(enter_not);
			SMTRAT_HAS_DECL(enter_bool);
			SMTRAT_HAS_DECL(enter_constraint);
			SMTRAT_HAS_DECL(enter_true);
			SMTRAT_HAS_DECL(enter_false);
			SMTRAT_HAS_DECL(enter_ueq);
			SMTRAT_HAS_DECL(enter_forall);
			SMTRAT_HAS_DECL(enter_exists);
			SMTRAT_HAS_DECL(enter_quantified);
			SMTRAT_HAS_DECL(enter_leaf);

			// these methods are "seamless" templates to ensure only the right overload is ever instantiated;
			// instantiating the wrong overload may cause compile-time errors due to calling non-existing methods
			template<typename = void> void P_visit_default(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->visit_default(formula);
			}

			template<typename = void> void P_visit_default(const FormulaT&, std::false_type) {}

			void P_visit_default(const FormulaT& formula) {
				P_visit_default(formula, SMTRAT_DISP_TAG(visit_default));
			}

			template<typename = void> void P_visit_or(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->visit_or(formula);
			}

			template<typename = void> void P_visit_or(const FormulaT& formula, std::false_type) {
				P_visit_default(formula);
			}

			template<typename = void> void P_visit_xor(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->visit_xor(formula);
			}

			template<typename = void> void P_visit_xor(const FormulaT& formula, std::false_type) {
				P_visit_default(formula);
			}

			template<typename = void> void P_visit_and(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->visit_and(formula);
			}

			template<typename = void> void P_visit_and(const FormulaT& formula, std::false_type) {
				P_visit_default(formula);
			}

			template<typename = void> void P_visit_iff(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->visit_iff(formula);
			}

			template<typename = void> void P_visit_iff(const FormulaT& formula, std::false_type) {
				P_visit_default(formula);
			}

			template<typename = void> void P_visit_not(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->visit_not(formula);
			}

			template<typename = void> void P_visit_not(const FormulaT& formula, std::false_type) {
				P_visit_default(formula);
			}

			template<typename = void> void P_visit_exists(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->visit_exists(formula);
			}

			template<typename = void> void P_visit_exists(const FormulaT& formula, std::false_type) {
				P_visit_quantified(formula, SMTRAT_DISP_TAG(visit_quantified));
			}

			template<typename = void> void P_visit_forall(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->visit_forall(formula);
			}

			template<typename = void> void P_visit_forall(const FormulaT& formula, std::false_type) {
				P_visit_quantified(formula, SMTRAT_DISP_TAG(visit_quantified));
			}

			template<typename = void> void P_visit_quantified(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->visit_quantified(formula);
			}

			template<typename = void> void P_visit_quantified(const FormulaT& formula, std::false_type) {
				P_visit_default(formula);
			}

			template<typename = void> void P_visit_leaf(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->visit_leaf(formula);
			}

			template<typename = void> void P_visit_leaf(const FormulaT& formula, std::false_type) {
				P_visit_default(formula);
			}

			void P_visit_leaf(const FormulaT& formula) {
				P_visit_leaf(formula, SMTRAT_DISP_TAG(visit_leaf));
			}

			template<typename = void> void P_visit_true(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->visit_true(formula);
			}

			template<typename = void> void P_visit_true(const FormulaT& formula, std::false_type) {
				P_visit_leaf(formula);
			}

			template<typename = void> void P_visit_false(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->visit_false(formula);
			}

			template<typename = void> void P_visit_false(const FormulaT& formula, std::false_type) {
				P_visit_leaf(formula);
			}

			template<typename = void> void P_visit_ueq(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->visit_ueq(formula);
			}

			template<typename = void> void P_visit_ueq(const FormulaT& formula, std::false_type) {
				P_visit_leaf(formula);
			}

			template<typename = void> void P_visit_constraint(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->visit_constraint(formula);
			}

			template<typename = void> void P_visit_constraint(const FormulaT& formula, std::false_type) {
				P_visit_leaf(formula);
			}

			template<typename = void> void P_visit_bool(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->visit_bool(formula);
			}

			template<typename = void> void P_visit_bool(const FormulaT& formula, std::false_type) {
				P_visit_leaf(formula);
			}

			template<typename = void> void P_visit_implication(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->visit_implication(formula);
			}

			template<typename = void> void P_visit_implication(const FormulaT& formula, std::false_type) {
				P_visit_default(formula);
			}

			template<typename = void> void P_visit_ite(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->visit_ite(formula);
			}

			template<typename = void> void P_visit_ite(const FormulaT& formula, std::false_type) {
				P_visit_default(formula);
			}

			template<typename = void> void P_enter_default(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_default(formula);
			}

			template<typename = void> void P_enter_default(const FormulaT&, std::false_type) {}

			void P_enter_default(const FormulaT& formula) {
				P_enter_default(formula, SMTRAT_DISP_TAG(enter_default));
			}

			template<typename = void> void P_enter_or(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_or(formula);
			}

			template<typename = void> void P_enter_or(const FormulaT& formula, std::false_type) { P_enter_default(formula); }

			template<typename = void> void P_enter_and(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_and(formula);
			}

			template<typename = void> void P_enter_and(const FormulaT& formula, std::false_type) {  P_enter_default(formula); }

			template<typename = void> void P_enter_xor(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_xor(formula);
			}

			template<typename = void> void P_enter_xor(const FormulaT& formula, std::false_type) {  P_enter_default(formula); }

			template<typename = void> void P_enter_iff(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_iff(formula);
			}

			template<typename = void> void P_enter_iff(const FormulaT& formula, std::false_type) {  P_enter_default(formula); }

			template<typename = void> void P_enter_not(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_not(formula);
			}

			template<typename = void> void P_enter_not(const FormulaT& formula, std::false_type) {  P_enter_default(formula); }

			template<typename = void> void P_enter_ite(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_ite(formula);
			}

			template<typename = void> void P_enter_ite(const FormulaT& formula, std::false_type) {  P_enter_default(formula); }

			template<typename = void> void P_enter_implication(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_implication(formula);
			}

			template<typename = void> void P_enter_implication(const FormulaT& formula, std::false_type) {  P_enter_default(formula); }

			template<typename = void> void P_enter_quantified(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_quantified(formula);
			}

			template<typename = void> void P_enter_quantified(const FormulaT& formula, std::false_type) {  P_enter_default(formula); }

			template<typename = void> void P_enter_exists(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_exists(formula);
			}

			template<typename = void> void P_enter_exists(const FormulaT& formula, std::false_type) {
				P_enter_quantified(formula, SMTRAT_DISP_TAG(enter_quantified));
			}

			template<typename = void> void P_enter_forall(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_forall(formula);
			}

			template<typename = void> void P_enter_forall(const FormulaT& formula, std::false_type) {
				P_enter_quantified(formula, SMTRAT_DISP_TAG(enter_quantified));
			}

			template<typename = void> void P_enter_leaf(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_leaf(formula);
			}

			template<typename = void> void P_enter_leaf(const FormulaT& formula, std::false_type) {
				P_enter_default(formula);
			}

			void P_enter_leaf(const FormulaT& formula) {
				P_enter_leaf(formula, SMTRAT_DISP_TAG(enter_leaf));
			}

			template<typename = void> void P_enter_true(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_true(formula);
			}

			template<typename = void> void P_enter_true(const FormulaT& formula, std::false_type) {
				P_enter_leaf(formula);
			}

			template<typename = void> void P_enter_false(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_false(formula);
			}

			template<typename = void> void P_enter_false(const FormulaT& formula, std::false_type) {
				P_enter_leaf(formula);
			}

			template<typename = void> void P_enter_ueq(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_ueq(formula);
			}

			template<typename = void> void P_enter_ueq(const FormulaT& formula, std::false_type) {
				P_enter_leaf(formula);
			}

			template<typename = void> void P_enter_constraint(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_constraint(formula);
			}

			template<typename = void> void P_enter_constraint(const FormulaT& formula, std::false_type) {
				P_enter_leaf(formula);
			}

			template<typename = void> void P_enter_bool(const FormulaT& formula, std::true_type) {
				static_cast<ConcreteType*>(this)->enter_bool(formula);
			}

			template<typename = void> void P_enter_bool(const FormulaT& formula, std::false_type) {
				P_enter_leaf(formula);
			}

			void P_dispatch(const FormulaT& formula) {
				// make sure that ConcreteType is a complete type
				constexpr std::size_t require_complete_type = sizeof(ConcreteType);
				(void)require_complete_type;

				switch(formula.getType()) {
					case carl::OR: {
						P_enter_or(formula, SMTRAT_DISP_TAG(enter_or));

						for(const FormulaT& subformula : formula.subformulas()) {
							P_dispatch(subformula);
						}

						P_visit_or(formula, SMTRAT_DISP_TAG(visit_or));
						return;
					}

					case carl::AND: {
						P_enter_and(formula, SMTRAT_DISP_TAG(enter_and));

						for(const FormulaT& subformula : formula.subformulas()) {
							P_dispatch(subformula);
						}

						P_visit_and(formula, SMTRAT_DISP_TAG(visit_and));
						return;
					}

					case carl::XOR: {
						P_enter_xor(formula, SMTRAT_DISP_TAG(enter_xor));

						for(const FormulaT& subformula : formula.subformulas()) {
							P_dispatch(subformula);
						}

						P_visit_xor(formula, SMTRAT_DISP_TAG(visit_xor));
						return;
					}

					case carl::IFF: {
						P_enter_iff(formula, SMTRAT_DISP_TAG(enter_iff));

						for(const FormulaT& subformula : formula.subformulas()) {
							P_dispatch(subformula);
						}

						P_visit_iff(formula, SMTRAT_DISP_TAG(visit_iff));
						return;
					}

					case carl::NOT: {
						P_enter_not(formula, SMTRAT_DISP_TAG(enter_not));
						P_dispatch(formula.subformula());
						P_visit_not(formula, SMTRAT_DISP_TAG(visit_not));
						return;
					}

					case carl::TRUE: {
						P_enter_true(formula, SMTRAT_DISP_TAG(enter_true));
						P_visit_true(formula, SMTRAT_DISP_TAG(visit_true));
						return;
					}

					case carl::FALSE: {
						P_enter_false(formula, SMTRAT_DISP_TAG(enter_false));
						P_visit_false(formula, SMTRAT_DISP_TAG(visit_false));
						return;
					}

					case carl::BOOL: {
						P_enter_bool(formula, SMTRAT_DISP_TAG(visit_bool));
						P_visit_bool(formula, SMTRAT_DISP_TAG(visit_bool));
						return;
					}

					case carl::UEQ: {
						P_enter_ueq(formula, SMTRAT_DISP_TAG(enter_ueq));
						P_visit_ueq(formula, SMTRAT_DISP_TAG(visit_ueq));
						return;
					}

					case carl::CONSTRAINT: {
						P_enter_constraint(formula, SMTRAT_DISP_TAG(enter_constraint));
						P_visit_constraint(formula, SMTRAT_DISP_TAG(visit_constraint));
						return;
					}

					case carl::EXISTS: {
						P_enter_exists(formula, SMTRAT_DISP_TAG(enter_exists));
						P_dispatch(formula.quantifiedFormula());
						P_visit_exists(formula, SMTRAT_DISP_TAG(visit_exists));
						return;
					}

					case carl::FORALL: {
						P_enter_forall(formula, SMTRAT_DISP_TAG(enter_forall));
						P_dispatch(formula.quantifiedFormula());
						P_visit_forall(formula, SMTRAT_DISP_TAG(visit_forall));
						return;
					}

					case carl::IMPLIES: {
						P_enter_implication(formula, SMTRAT_DISP_TAG(enter_implication));
						P_dispatch(formula.premise());
						P_dispatch(formula.conclusion());
						P_visit_implication(formula, SMTRAT_DISP_TAG(visit_implication));
						return;
					}

					case carl::ITE: {
						P_enter_ite(formula, SMTRAT_DISP_TAG(enter_ite));
						P_dispatch(formula.condition());
						P_dispatch(formula.firstCase());
						P_dispatch(formula.secondCase());
						P_visit_ite(formula, SMTRAT_DISP_TAG(visit_ite));
						return;
					}

					default: {
						assert(false && "Unexpected formula encountered!");
						P_enter_default(formula);
						P_visit_default(formula);
						return;
					}
				}
			}
			#undef SMTRAT_DISP_TAG
	};

	template<typename RewriterType> class formula_rewriter :
		public formula_visitor<
			formula_rewriter<RewriterType>, // the visitor shall use the rewriter as concrete type
			FormulaT,                       // the result of the rewriter is a formula
			typename FormulaSetT::value_compare, // use the comparator
			typename FormulaSetT::allocator_type // and allocator from FormulaSetT
		>
	{
		public:
			template<typename... Args> formula_rewriter(Args&&... args) :
				mRewriter(std::forward<Args>(args)...)
			{}

			RewriterType &get() noexcept { return mRewriter; }
			const RewriterType &get() const noexcept { return mRewriter; }

		private:
			#define SMTRAT_DISP_TAG(name) (typename has_decl_##name<RewriterType>::type{})

			friend class formula_visitor<
				formula_rewriter<RewriterType>,
				FormulaT,
				typename FormulaSetT::value_compare,
				typename FormulaSetT::allocator_type
			>;

			typedef formula_visitor<
				formula_rewriter<RewriterType>,
				FormulaT,
				typename FormulaSetT::value_compare,
				typename FormulaSetT::allocator_type
			> super_type;

			typedef typename super_type::set_type set_type;
			typedef typename super_type::multiset_type multiset_type;

			SMTRAT_HAS_DECL(rewrite_default);
			SMTRAT_HAS_DECL(rewrite_or);
			SMTRAT_HAS_DECL(rewrite_and);
			SMTRAT_HAS_DECL(rewrite_iff);
			SMTRAT_HAS_DECL(rewrite_xor);
			SMTRAT_HAS_DECL(rewrite_not);
			SMTRAT_HAS_DECL(rewrite_exists);
			SMTRAT_HAS_DECL(rewrite_forall);
			SMTRAT_HAS_DECL(rewrite_implication);
			SMTRAT_HAS_DECL(rewrite_ite);
			SMTRAT_HAS_DECL(rewrite_true);
			SMTRAT_HAS_DECL(rewrite_false);
			SMTRAT_HAS_DECL(rewrite_bool);
			SMTRAT_HAS_DECL(rewrite_ueq);
			SMTRAT_HAS_DECL(rewrite_constraint);
			SMTRAT_HAS_DECL(rewrite_quantified);
			SMTRAT_HAS_DECL(rewrite_leaf);

			SMTRAT_HAS_DECL(enter_default);
			SMTRAT_HAS_DECL(enter_or);
			SMTRAT_HAS_DECL(enter_and);
			SMTRAT_HAS_DECL(enter_iff);
			SMTRAT_HAS_DECL(enter_xor);
			SMTRAT_HAS_DECL(enter_not);
			SMTRAT_HAS_DECL(enter_exists);
			SMTRAT_HAS_DECL(enter_forall);
			SMTRAT_HAS_DECL(enter_implication);
			SMTRAT_HAS_DECL(enter_ite);
			SMTRAT_HAS_DECL(enter_true);
			SMTRAT_HAS_DECL(enter_false);
			SMTRAT_HAS_DECL(enter_bool);
			SMTRAT_HAS_DECL(enter_ueq);
			SMTRAT_HAS_DECL(enter_constraint);
			SMTRAT_HAS_DECL(enter_quantified);
			SMTRAT_HAS_DECL(enter_leaf);

			template<typename = void> FormulaT P_visit_or(const FormulaT& formula, set_type&& subformulas, std::true_type) {
				return mRewriter.rewrite_or(formula, std::move(subformulas));
			}

			template<typename = void> FormulaT P_visit_or(const FormulaT& formula, set_type&& subformulas, std::false_type) {
				return P_rewrite_default(formula, std::move(subformulas));
			}

			FormulaT visit_or(const FormulaT& formula, set_type&& subformulas) {
				return P_visit_or(formula, std::move(subformulas), SMTRAT_DISP_TAG(rewrite_or));
			}

			template<typename = void> FormulaT P_visit_and(const FormulaT& formula, set_type&& subformulas, std::true_type) {
				return mRewriter.rewrite_and(formula, std::move(subformulas));
			}

			template<typename = void> FormulaT P_visit_and(const FormulaT& formula, set_type&& subformulas, std::false_type) {
				return P_rewrite_default(formula, std::move(subformulas));
			}

			FormulaT visit_and(const FormulaT& formula, set_type&& subformulas) {
				return P_visit_and(formula, std::move(subformulas), SMTRAT_DISP_TAG(rewrite_and));
			}

			template<typename = void> FormulaT P_visit_iff(const FormulaT& formula, set_type&& subformulas, std::true_type) {
				return mRewriter.rewrite_iff(formula, std::move(subformulas));
			}

			template<typename = void> FormulaT P_visit_iff(const FormulaT& formula, set_type&& subformulas, std::false_type) {
				return P_rewrite_default(formula, std::move(subformulas));
			}

			FormulaT visit_iff(const FormulaT& formula, set_type&& subformulas) {
				return P_visit_iff(formula, std::move(subformulas), SMTRAT_DISP_TAG(rewrite_iff));
			}

			template<typename = void> FormulaT P_visit_xor(const FormulaT& formula, multiset_type&& subformulas, std::true_type) {
				return mRewriter.rewrite_xor(formula, std::move(subformulas));
			}

			template<typename = void> FormulaT P_visit_xor(const FormulaT& formula, multiset_type&& subformulas, std::false_type) {
				return P_rewrite_default(formula, std::move(subformulas));
			}

			FormulaT visit_xor(const FormulaT& formula, multiset_type&& subformulas) {
				return P_visit_xor(formula, std::move(subformulas), SMTRAT_DISP_TAG(rewrite_xor));
			}

			template<typename = void> FormulaT P_visit_not(const FormulaT& formula, FormulaT&& subformula, std::true_type) {
				return mRewriter.rewrite_not(formula, std::move(subformula));
			}

			template<typename = void> FormulaT P_visit_not(const FormulaT& formula, FormulaT&& subformula, std::false_type) {
				return P_rewrite_default(formula, FormulaT(carl::NOT, std::move(subformula)));
			}

			FormulaT visit_not(const FormulaT& formula, FormulaT&& subformula) {
				return P_visit_not(formula, std::move(subformula), SMTRAT_DISP_TAG(rewrite_not));
			}

			template<typename = void> FormulaT P_visit_quantified(const FormulaT& formula, FormulaT&& subformula, std::true_type) {
				return mRewriter.rewrite_quantified(formula, std::move(subformula));
			}

			template<typename = void> FormulaT P_visit_quantified(const FormulaT& formula, FormulaT&& subformula, std::false_type) {
				return P_rewrite_default(formula, FormulaT(formula.getType(), formula.quantifiedVariables(), std::move(subformula)));
			}

			FormulaT P_visit_quantified(const FormulaT& formula, FormulaT&& subformula) {
				return P_visit_quantified(formula, std::move(subformula), SMTRAT_DISP_TAG(rewrite_quantified));
			}

			template<typename = void> FormulaT P_visit_exists(const FormulaT& formula, FormulaT&& subformula, std::true_type) {
				return mRewriter.rewrite_exists(formula, std::move(subformula));
			}

			template<typename = void> FormulaT P_visit_exists(const FormulaT& formula, FormulaT&& subformula, std::false_type) {
				return P_visit_quantified(formula, std::move(subformula));
			}

			FormulaT visit_exists(const FormulaT& formula, FormulaT&& subformula) {
				return P_visit_exists(formula, std::move(subformula), SMTRAT_DISP_TAG(rewrite_exists));
			}

			template<typename = void> FormulaT P_visit_forall(const FormulaT& formula, FormulaT&& subformula, std::true_type) {
				return mRewriter.rewrite_forall(formula, std::move(subformula));
			}

			template<typename = void> FormulaT P_visit_forall(const FormulaT& formula, FormulaT&& subformula, std::false_type) {
				return P_visit_quantified(formula, std::move(subformula));
			}

			FormulaT visit_forall(const FormulaT& formula, FormulaT&& subformula) {
				return P_visit_forall(formula, std::move(subformula), SMTRAT_DISP_TAG(rewrite_forall));
			}

			template<typename = void> FormulaT P_visit_implication(const FormulaT& formula, FormulaT&& premise, FormulaT&& conclusion, std::true_type) {
				return mRewriter.rewrite_implication(formula, std::move(premise), std::move(conclusion));
			}

			template<typename = void> FormulaT P_visit_implication(const FormulaT& formula, FormulaT&& premise, FormulaT&& conclusion, std::false_type) {
				return P_rewrite_default(formula, FormulaT(carl::IMPLIES, {std::move(premise), std::move(conclusion)}));
			}

			FormulaT visit_implication(const FormulaT& formula, FormulaT&& premise, FormulaT&& conclusion) {
				return P_visit_implication(formula, std::move(premise), std::move(conclusion), SMTRAT_DISP_TAG(rewrite_implication));
			}

			template<typename = void> FormulaT P_visit_ite(const FormulaT& formula, FormulaT&& condition, FormulaT&& then, FormulaT&& else_, std::true_type) {
				return mRewriter.rewrite_ite(formula, std::move(condition), std::move(then), std::move(else_));
			}

			template<typename = void> FormulaT P_visit_ite(const FormulaT& formula, FormulaT&& condition, FormulaT&& then, FormulaT&& else_, std::false_type) {
				return P_rewrite_default(formula, FormulaT(carl::ITE, {std::move(condition), std::move(then), std::move(else_)}));
			}

			FormulaT visit_ite(const FormulaT& formula, FormulaT&& condition, FormulaT&& trueCase, FormulaT&& falseCase) {
				return P_visit_ite(formula, std::move(condition), std::move(trueCase), std::move(falseCase), SMTRAT_DISP_TAG(rewrite_ite));
			}

			template<typename = void> FormulaT P_visit_leaf(const FormulaT& formula, std::true_type) {
				return mRewriter.rewrite_leaf(formula);
			}

			template<typename = void> FormulaT P_visit_leaf(const FormulaT& formula, std::false_type) {
				return P_rewrite_default(formula, formula);
			}

			FormulaT P_visit_leaf(const FormulaT& formula) {
				return P_visit_leaf(formula, SMTRAT_DISP_TAG(rewrite_leaf));
			}

			template<typename = void> FormulaT P_visit_true(const FormulaT& formula, std::true_type) {
				return mRewriter.rewrite_true(formula);
			}

			template<typename = void> FormulaT P_visit_true(const FormulaT& formula, std::false_type) {
				return P_visit_leaf(formula);
			}

			FormulaT visit_true (const FormulaT& formula) {
				return P_visit_true(formula, SMTRAT_DISP_TAG(rewrite_true));
			}

			template<typename = void> FormulaT P_visit_false(const FormulaT& formula, std::true_type) {
				return mRewriter.rewrite_false(formula);
			}

			template<typename = void> FormulaT P_visit_false(const FormulaT& formula, std::false_type) {
				return P_visit_leaf(formula);
			}

			FormulaT visit_false(const FormulaT& formula) {
				return P_visit_false(formula, SMTRAT_DISP_TAG(rewrite_false));
			}

			template<typename = void> FormulaT P_visit_bool(const FormulaT& formula, std::true_type) {
				return mRewriter.rewrite_bool(formula);
			}

			template<typename = void> FormulaT P_visit_bool(const FormulaT& formula, std::false_type) {
				return P_visit_leaf(formula);
			}

			FormulaT visit_bool(const FormulaT& formula) {
				return P_visit_bool(formula, SMTRAT_DISP_TAG(rewrite_bool));
			}

			template<typename = void> FormulaT P_visit_ueq(const FormulaT& formula, std::true_type) {
				return mRewriter.rewrite_ueq(formula);
			}

			template<typename = void> FormulaT P_visit_ueq(const FormulaT& formula, std::false_type) {
				return P_visit_leaf(formula);
			}

			FormulaT visit_ueq (const FormulaT& formula) {
				return P_visit_ueq(formula, SMTRAT_DISP_TAG(rewrite_ueq));
			}

			template<typename = void> FormulaT P_visit_constraint(const FormulaT& formula, std::true_type) {
				return mRewriter.rewrite_constraint(formula);
			}

			template<typename = void> FormulaT P_visit_constraint(const FormulaT& formula, std::false_type) {
				return P_visit_leaf(formula);
			}

			FormulaT visit_constraint(const FormulaT& formula) {
				return P_visit_constraint(formula, SMTRAT_DISP_TAG(rewrite_constraint));
			}

			template<typename = void> void P_enter_default(const FormulaT& formula, std::true_type) {
				return mRewriter.enter_default(formula);
			}

			template<typename = void> void P_enter_default(const FormulaT&, std::false_type) {}

			void P_enter_default(const FormulaT& formula) {
				P_enter_default(formula, SMTRAT_DISP_TAG(enter_default));
			}

			template<typename = void> void P_enter_or(const FormulaT& formula, std::true_type) {
				mRewriter.enter_or(formula);
			}

			template<typename = void> void P_enter_or(const FormulaT& formula, std::false_type) {
				P_enter_default(formula);
			}

			void enter_or(const FormulaT& formula) {
				P_enter_or(formula, SMTRAT_DISP_TAG(enter_or));
			}

			template<typename = void> void P_enter_and(const FormulaT& formula, std::true_type) {
				mRewriter.enter_and(formula);
			}

			template<typename = void> void P_enter_and(const FormulaT& formula, std::false_type) {
				P_enter_default(formula);
			}

			void enter_and(const FormulaT& formula) {
				P_enter_and(formula, SMTRAT_DISP_TAG(enter_and));
			}

			template<typename = void> void P_enter_iff(const FormulaT& formula, std::true_type) {
				mRewriter.enter_iff(formula);
			}

			template<typename = void> void P_enter_iff(const FormulaT& formula, std::false_type) {
				P_enter_default(formula);
			}

			void enter_iff(const FormulaT& formula) {
				P_enter_iff(formula, SMTRAT_DISP_TAG(enter_iff));
			}

			template<typename = void> void P_enter_xor(const FormulaT& formula, std::true_type) {
				mRewriter.enter_xor(formula);
			}

			template<typename = void> void P_enter_xor(const FormulaT& formula, std::false_type) {
				P_enter_default(formula);
			}

			void enter_xor(const FormulaT& formula) {
				P_enter_xor(formula, SMTRAT_DISP_TAG(enter_xor));
			}

			template<typename = void> void P_enter_not(const FormulaT& formula, std::true_type) {
				mRewriter.enter_not(formula);
			}

			template<typename = void> void P_enter_not(const FormulaT& formula, std::false_type) {
				P_enter_default(formula);
			}

			void enter_not(const FormulaT& formula) {
				P_enter_not(formula, SMTRAT_DISP_TAG(enter_not));
			}

			template<typename = void> void P_enter_quantified(const FormulaT& formula, std::true_type) {
				mRewriter.enter_quantified(formula);
			}

			template<typename = void> void P_enter_quantified(const FormulaT& formula, std::false_type) {
				P_enter_default(formula);
			}

			void P_enter_quantified(const FormulaT& formula) {
				P_enter_quantified(formula, SMTRAT_DISP_TAG(enter_quantified));
			}

			template<typename = void> void P_enter_exists(const FormulaT& formula, std::true_type) {
				mRewriter.enter_exists(formula);
			}

			template<typename = void> void P_enter_exists(const FormulaT& formula, std::false_type) {
				P_enter_quantified(formula);
			}

			void enter_exists(const FormulaT& formula) {
				P_enter_exists(formula, SMTRAT_DISP_TAG(enter_exists));
			}

			template<typename = void> void P_enter_forall(const FormulaT& formula, std::true_type) {
				mRewriter.enter_forall(formula);
			}

			template<typename = void> void P_enter_forall(const FormulaT& formula, std::false_type) {
				P_enter_quantified(formula);
			}

			void enter_forall(const FormulaT& formula) {
				P_enter_forall(formula, SMTRAT_DISP_TAG(enter_forall));
			}

			template<typename = void> void P_enter_implication(const FormulaT& formula, std::true_type) {
				mRewriter.enter_implication(formula);
			}

			template<typename = void> void P_enter_implication(const FormulaT& formula, std::false_type) {
				P_enter_default(formula);
			}

			void enter_implication(const FormulaT& formula) {
				P_enter_implication(formula, SMTRAT_DISP_TAG(enter_implication));
			}

			template<typename = void> void P_enter_ite(const FormulaT& formula, std::true_type) {
				mRewriter.enter_ite(formula);
			}

			template<typename = void> void P_enter_ite(const FormulaT& formula, std::false_type) {
				P_enter_default(formula);
			}

			void enter_ite(const FormulaT& formula) {
				P_enter_ite(formula, SMTRAT_DISP_TAG(enter_ite));
			}

			template<typename = void> void P_enter_leaf(const FormulaT& formula, std::true_type) {
				mRewriter.enter_leaf(formula);
			}

			template<typename = void> void P_enter_leaf(const FormulaT& formula, std::false_type) {
				P_enter_default(formula);
			}

			void P_enter_leaf(const FormulaT& formula) {
				P_enter_leaf(formula, SMTRAT_DISP_TAG(enter_leaf));
			}

			template<typename = void> void P_enter_true(const FormulaT& formula, std::true_type) {
				mRewriter.enter_true(formula);
			}

			template<typename = void> void P_enter_true(const FormulaT& formula, std::false_type) {
				P_enter_leaf(formula);
			}

			void enter_true(const FormulaT& formula) {
				P_enter_true(formula, SMTRAT_DISP_TAG(enter_true));
			}

			template<typename = void> void P_enter_false(const FormulaT& formula, std::true_type) {
				mRewriter.enter_false(formula);
			}

			template<typename = void> void P_enter_false(const FormulaT& formula, std::false_type) {
				P_enter_leaf(formula);
			}

			void enter_false(const FormulaT& formula) {
				P_enter_false(formula, SMTRAT_DISP_TAG(enter_false));
			}

			template<typename = void> void P_enter_bool(const FormulaT& formula, std::true_type) {
				mRewriter.enter_bool(formula);
			}

			template<typename = void> void P_enter_bool(const FormulaT& formula, std::false_type) {
				P_enter_leaf(formula);
			}

			void enter_bool(const FormulaT& formula) {
				P_enter_bool(formula, SMTRAT_DISP_TAG(enter_bool));
			}

			template<typename = void> void P_enter_ueq(const FormulaT& formula, std::true_type) {
				mRewriter.enter_ueq(formula);
			}

			template<typename = void> void P_enter_ueq(const FormulaT& formula, std::false_type) {
				P_enter_leaf(formula);
			}

			void enter_ueq (const FormulaT& formula) {
				P_enter_ueq(formula, SMTRAT_DISP_TAG(enter_ueq));
			}

			template<typename = void> void P_enter_constraint(const FormulaT& formula, std::true_type) {
				mRewriter.enter_constraint(formula);
			}

			template<typename = void> void P_enter_constraint(const FormulaT& formula, std::false_type) {
				P_enter_leaf(formula);
			}

			void enter_constraint(const FormulaT& formula) {
				P_enter_constraint(formula, SMTRAT_DISP_TAG(enter_constraint));
			}

			template<template<typename,typename,typename> class SetTemplate, typename C, typename A>
				FormulaT P_rewrite_default(const FormulaT& formula, SetTemplate<FormulaT, C, A>&& subformulas)
			{
				return P_rewrite_default(formula, FormulaT(formula.getType(), std::move(subformulas)));
			}

			FormulaT P_rewrite_default(const FormulaT& formula, const FormulaT& default_result) {
				return P_rewrite_default(formula, default_result, SMTRAT_DISP_TAG(rewrite_default));
			}

			template<typename = void> FormulaT P_rewrite_default(const FormulaT& formula, const FormulaT& default_result, std::true_type) {
				return mRewriter.rewrite_default(formula, default_result);
			}

			template<typename = void> FormulaT P_rewrite_default(const FormulaT&, const FormulaT& default_result, std::false_type) {
				return default_result;
			}

			RewriterType mRewriter;

			#undef SMTRAT_DISP_TAG
	};

#undef SMTRAT_HAS_DECL
}

#endif
