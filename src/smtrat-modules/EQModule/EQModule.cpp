/**
 * @file EQModule.tpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2014-10-19
 * Created on 2014-10-19.
 */

#include <carl-formula/uninterpreted/SortValueManager.h>

#include <iostream>
#include <iterator>

#include "EQModule.h"

namespace smtrat {
	/**
	 * Constructors.
	 */
	template<class Settings>
	EQModule<Settings>::EQModule( const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager ):
		Module( _formula, _conditionals, _manager ),
		mLocalSplitAge(0), mGlobalSplitAge(0),
		mBfsQueue(Settings::initial_bfsqueue_capacity),
		mImplicitEdgeQueue(Settings::initial_bfsqueue_capacity),
		mCountNonUEQFormulas(0),
		mGlobalPairSetAge(0),
		mCheckForDeductionCounter(0)
	{}

	/**
	 * Destructor.
	 */
	template<class Settings>
		EQModule<Settings>::~EQModule()
	{}

	template<class Settings>
		bool EQModule<Settings>::informCore(const FormulaT& _constraint)
	{
		if(_constraint.type() == carl::UEQ) {
			const UEquality &ueq = _constraint.u_equality();
			const term_type &lhs = ueq.lhs();
			const term_type &rhs = ueq.rhs();
			
			if(ueq.negated()) {
				if(lhs == rhs) {
					return false;
				}
			}
			
			if(Settings::deduceUnassignedLiterals) {
				// add the terms to our map if not present
				g_iterator itrLhs; bool insertedLhs;
				g_iterator itrRhs; bool insertedRhs;
				std::tie(itrLhs, insertedLhs) = mEqualityGraph.emplace(std::piecewise_construct, std::forward_as_tuple(lhs), std::forward_as_tuple(*this));
				std::tie(itrRhs, insertedRhs) = mEqualityGraph.emplace(std::piecewise_construct, std::forward_as_tuple(rhs), std::forward_as_tuple(*this));

				if(insertedLhs) {
					if(ueq.lhs().isUFInstance()) {
						P_add_function_instance(ueq.lhs().asUFInstance(), itrLhs);
					} else {
						P_add_variable(ueq.lhs().asUVariable(), itrLhs);
					}
				}

				if(insertedRhs) {
					if(ueq.rhs().isUFInstance()) {
						P_add_function_instance(ueq.rhs().asUFInstance(), itrRhs);
					} else {
						P_add_variable(ueq.rhs().asUVariable(), itrRhs);
					}
				}

				// add term to normalization map; make sure we do not produce literals that did not occur in the input
				P_add_not_asserted_normalized(_constraint, ueq);
			}
		}
		
		return true;
	}

	template<class Settings>
		void EQModule<Settings>::init()
	{}

	template<class Settings>
		void EQModule<Settings>::P_add_not_asserted_normalized(FormulaT formula, const UEquality& ueq)
	{
		std::unordered_map<FormulaT, FormulaT>::iterator mapEntry;
		bool mapInserted;

		std::tie(mapEntry, mapInserted) = mEqualityNormalization.emplace(formula, formula);

		if(mapInserted) {
			FormulaT otherForm(ueq.lhs(), ueq.rhs(), !ueq.negated());
			auto otherFormIter = mEqualityNormalization.find(otherForm);

			if(otherFormIter != mEqualityNormalization.end()) {
				if(ueq.negated()) {
					mapEntry->second = otherForm;
				} else {
					otherFormIter->second = mapEntry->second;
					mAllNotAssertedEqualities.erase(not_asserted_equality(otherForm));
					mAllNotAssertedEqualities.emplace(formula, mEqualityGraph.find(ueq.lhs()), mEqualityGraph.find(ueq.rhs()));
				}
			} else {
				mAllNotAssertedEqualities.emplace(formula, mEqualityGraph.find(ueq.lhs()), mEqualityGraph.find(ueq.rhs()));
			}
		}
	}

	template<class Settings>
		void EQModule<Settings>::P_check_queue_caps()
	{
		if(mEqualityGraph.size() > mBfsQueue.capacity()) {
			mBfsQueue.set_capacity(mBfsQueue.capacity() * 2);
		}

		if(2 * mEqualityGraph.size() > mImplicitEdgeQueue.capacity()) {
			mImplicitEdgeQueue.set_capacity(mImplicitEdgeQueue.capacity() * 2);
		}
	}

	template<class Settings>
		void EQModule<Settings>::P_add_variable(const UVariable& var, g_iterator term_iter)
	{
		term_iter->second.mUFIndex = mUnionFind.add(term_iter);
		mComponentUnionFind.add(uf_component_entry{});
		mVariables.emplace_back(var, term_iter);
		P_check_queue_caps();
	}

	template<class Settings>
		void EQModule<Settings>::P_add_function_instance(const UFInstance& instance, g_iterator term_iter)
	{
		term_iter->second.mUFIndex = mUnionFind.add(term_iter);
		mComponentUnionFind.add(uf_component_entry{});

		UninterpretedFunction fn = instance.uninterpretedFunction();
		typename function_map_type::iterator i = mFunctionMap.find(fn);

		if(i == mFunctionMap.end()) {
			i = mFunctionMap.emplace(std::piecewise_construct, std::forward_as_tuple(fn), std::forward_as_tuple(*this, fn)).first;
		}

		i->second.mInstances.insert(term_iter);

		// add variables if that has not already happened, and add argument information
		const auto& args = instance.args();
		args_info* ainfo = static_cast<args_info*>(std::malloc((args.size()-1) * sizeof(g_iterator) + sizeof(args_info)));
		assert(ainfo != nullptr);

		ainfo->mBuckets = &(i->second.mHashBuckets);
		ainfo->mArity = args.size();
		std::size_t aindex = 0;
		for(const auto& term : args) {
			assert(term.isUVariable());
			const auto& var = term.asUVariable();
			g_iterator iter; bool inserted;
			std::tie(iter, inserted) = mEqualityGraph.emplace(std::piecewise_construct, std::forward_as_tuple(var), std::forward_as_tuple(*this));
			new (&(ainfo->mArgs[aindex++])) g_iterator(iter);

			if(inserted) {
				P_add_variable(var, iter);
			}
		}

		term_iter->second.mArgs = ainfo;
		P_check_queue_caps();

		i->second.mHashBuckets.insert_function_instance(term_iter);
	}

	template<class Settings>
		bool EQModule<Settings>::addCore(ModuleInput::const_iterator _subformula)
	{
		if(Settings::printFormulas) {
			std::cout << "assertSubformula: " << _subformula->formula() << std::endl;
		}

		if(_subformula->formula().type() != carl::UEQ) {
			++mCountNonUEQFormulas;
			return true;
		}
		
		const FormulaT& formula = _subformula->formula();
		const UEquality &ueq = formula.u_equality();
		const term_type &lhs = ueq.lhs();
		const term_type &rhs = ueq.rhs();

		// in any case, add the terms to our map if not present (even for an inequality, otherwise we have no iterators)
		g_iterator itrLhs;
		g_iterator itrRhs;
		itrLhs = mEqualityGraph.find(lhs);
		itrRhs = mEqualityGraph.find(rhs);

		if(itrLhs == mEqualityGraph.end()) {
			itrLhs = mEqualityGraph.emplace(std::piecewise_construct, std::forward_as_tuple(lhs), std::forward_as_tuple(*this)).first;
			if(ueq.lhs().isUFInstance()) {
				P_add_function_instance(ueq.lhs().asUFInstance(), itrLhs);
			} else {
				P_add_variable(ueq.lhs().asUVariable(), itrLhs);
			}
		}

		if(itrRhs == mEqualityGraph.end()) {
			itrRhs = mEqualityGraph.emplace(std::piecewise_construct, std::forward_as_tuple(rhs), std::forward_as_tuple(*this)).first;
			if(ueq.rhs().isUFInstance()) {
				P_add_function_instance(ueq.rhs().asUFInstance(), itrRhs);
			} else {
				P_add_variable(ueq.rhs().asUVariable(), itrRhs);
			}
		}

		if(Settings::deduceUnassignedLiterals) {
			mAllNotAssertedEqualities.erase(not_asserted_equality(mEqualityNormalization.find(formula)->second));
		}

		bool found_inconsistency = false;
		
		if(ueq.negated()) {
			std::size_t indexLhs = mUnionFind.find(itrLhs->second.mUFIndex);
			std::size_t indexRhs = mUnionFind.find(itrRhs->second.mUFIndex);
			
			std::size_t indexCLhs = mComponentUnionFind.find(indexLhs);
			std::size_t indexCRhs = mComponentUnionFind.find(indexRhs);
			
			if(indexCLhs == indexCRhs) {
				// construct edges for inequality
				ineq_edge_info *lhs_edge = &mIneqEdgeAlloc.emplace(
					mUnionFind[indexCLhs], mUnionFind[indexCRhs], itrLhs, itrRhs, formula
				);
				ineq_edge_info *rhs_edge = &mIneqEdgeAlloc.emplace(
					mUnionFind[indexCRhs], mUnionFind[indexCLhs], itrRhs, itrLhs, formula
				);

				lhs_edge->mOther = rhs_edge;
				rhs_edge->mOther = lhs_edge;
				
				// add inequality to inconsistencies since lhs and rhs are in same component
				mPossibleInconsistencies.push_back(lhs_edge);
				found_inconsistency = true;
				
				if(Settings::printFormulas) {
					std::cout << "Found inconsistency: " << lhs_edge->mFormula << std::endl;
				}
			} else {
				P_add_ineq_edge(indexCLhs, indexCRhs, itrLhs, itrRhs, formula);
			}
		} else {
			P_add_explicit_edge(itrLhs, itrRhs, formula);
			
			std::size_t indexLhs = mUnionFind.find(itrLhs->second.mUFIndex);
			std::size_t indexRhs = mUnionFind.find(itrRhs->second.mUFIndex);
			
			std::size_t indexCLhs = mComponentUnionFind.find(indexLhs);
			std::size_t indexCRhs = mComponentUnionFind.find(indexRhs);
			
			// we only have to do something if we actually merge two components
			if(indexLhs != indexRhs) {
				std::size_t indexNew = mUnionFind.fast_union(indexLhs, indexRhs);
				std::size_t indexCNew = mComponentUnionFind.find(indexNew);
				std::size_t indexOld = (indexNew == indexLhs) ? indexRhs : indexLhs;
				std::size_t indexCOld = (indexCNew == indexCLhs) ? indexCRhs : indexCLhs;
				
				if(indexCLhs == indexCRhs) {
					P_bfs_search_implicit(mUnionFind[indexLhs], mEqualityGraph.end());
					assert(mUnionFind[indexRhs]->second.mVisited);
					assert(mUnionFind[indexCLhs]->second.mVisited);

					// in case the two components are in the same class we have to delete some edge on the path from CLhs to CRhs to not introduce a cycle
					// to make sure we do not delete an edge that is necessary to prove another implicit edge, we remove the newest one, according to its mID
					g_iterator cur = mUnionFind[indexRhs];
					implicit_edge_info* maxEdge = cur->second.mImplicitPred;
					
					while (true) {
						if (cur->second.mImplicitPred->mPred == mUnionFind[indexLhs]) break;
						if (cur->second.mImplicitPred->mID > maxEdge->mID) {
							maxEdge = cur->second.mImplicitPred;
						}
						cur = cur->second.mImplicitPred->mPred;
					}
					P_destroy_implicit_edge(maxEdge);

					if(indexCLhs == indexOld) {
						// if old index was component component representative we have to update mComponentUnionFind, hash buckets and and inequality edges
						for(g_iterator entry : mEqualityComponent){
							mComponentUnionFind.set_class(entry->second.mUFIndex, indexNew);
						}
						mComponentUnionFind.set_class(indexOld, indexOld);
						
						P_merge_buckets(indexCLhs, indexNew);
						P_cc_union_for_ineq(indexCLhs, indexNew);
					} else {
						// indexOld might appear on some path in the component union find structure which can cause problems
						for(g_iterator entry : mEqualityComponent){
							mComponentUnionFind.set_class(entry->second.mUFIndex, indexCLhs);
						}
						mComponentUnionFind.set_class(indexOld, indexOld);
					}

					P_clear_bfs_markings();

					g_iterator nodeOld = mUnionFind[indexOld];
					g_iterator nodeNew = mUnionFind[indexNew];

					// implicit neighbors of the old component representative have to be moved to the new representative
					for(std::size_t i = nodeOld->second.mImplicit.size() - 1; i < nodeOld->second.mImplicit.size(); i--) {
						implicit_edge_info *edge = nodeOld->second.mImplicit[i];
						nodeOld->second.mImplicit.remove_back();
						nodeNew->second.mImplicit.add(edge);
						edge->mPred = nodeNew;
						edge->mOther->mSucc = nodeNew;
					}
				} else {
					// union two different component components and check for inconsistencies
					found_inconsistency = P_cc_union_for_ineq(indexCOld, indexCNew);
					
					P_bfs_search_implicit(mUnionFind[indexOld], mEqualityGraph.end());
					assert(mUnionFind[indexCOld]->second.mVisited);
					
					// update component union find; we can not just do a union here since indexOld might appear on some component union find path
					for(g_iterator entry : mEqualityComponent){
						mComponentUnionFind.set_class(entry->second.mUFIndex, indexCNew);
					}
					mComponentUnionFind.set_class(indexOld, indexOld);
					
					P_clear_bfs_markings();
					
					g_iterator nodeOld = mUnionFind[indexOld];
					g_iterator nodeNew = mUnionFind[indexNew];
					
					// implicit neighbors of the old component representative have to be moved to the new representative
					for(std::size_t i = nodeOld->second.mImplicit.size() - 1; i < nodeOld->second.mImplicit.size(); i--) {
						implicit_edge_info *edge = nodeOld->second.mImplicit[i];
						nodeOld->second.mImplicit.remove_back();
						edge->mPred = nodeNew;
						edge->mOther->mSucc = nodeNew;
						nodeNew->second.mImplicit.add(edge);
					}
					
					P_merge_buckets(indexCOld, indexCNew);
				}
			}
		}
		
		if(Settings::printBucketSets) {
			P_print_bucket_sets();
		}
		
		// construct infeasible subset in case inconsistency is found
		if(found_inconsistency) {
			ineq_edge_info* ineq_edge = mPossibleInconsistencies.back();
			P_construct_infeasible_subset(ineq_edge->mRealPred, ineq_edge->mRealSucc, ineq_edge->mFormula);
			return false;
		}

		return true;
	}

	template<class Settings>
		void EQModule<Settings>::removeCore(ModuleInput::const_iterator _subformula)
	{
		if(Settings::printFormulas) {
			std::cout << "removeSubformula: " << _subformula->formula() << std::endl;
		}

		if(_subformula->formula().type() != carl::UEQ) {
			--mCountNonUEQFormulas;
			return;
		}
		
		const FormulaT& formula = _subformula->formula();
		const UEquality &ueq = formula.u_equality();
		const term_type &lhs = ueq.lhs();
		const term_type &rhs = ueq.rhs();
		
		g_iterator itrLhs = mEqualityGraph.find(lhs);
		g_iterator itrRhs = mEqualityGraph.find(rhs);
		
		assert(itrLhs != mEqualityGraph.end());
		assert(itrRhs != mEqualityGraph.end());

		if(Settings::deduceUnassignedLiterals) {
			mAllNotAssertedEqualities.emplace(mEqualityNormalization.find(formula)->second, itrLhs, itrRhs);
		}

		if(ueq.negated()) {
			// we only have to remove the inequality edge in case of an inequality
			P_remove_ineq_edge(itrLhs, itrRhs, formula);
		} else {
			P_remove_edge(itrLhs, itrRhs, formula);

			// we only have to do something if the component splits
			if(!P_bfs_search_explicit(itrLhs, itrRhs)) {
				// first we have to split up the lower component and adjust the implicit neighbors
				
				std::size_t oldcentry = mUnionFind.find(itrLhs->second.mUFIndex);
				g_iterator oldcnode = mUnionFind[oldcentry];
				g_iterator newcnode;
				
				// if old component entry is on left side, keep it on left side, otherwise keep it on right side
				if(oldcnode->second.mVisited) {
					std::size_t split_pos = mEqualityComponent.size();
					if(P_bfs_search_explicit(itrRhs, itrLhs)) {
						assert(false);
					}
					
					// inform hash buckets about changing indizes
					for(g_iterator entry : mEqualityComponent) {
						if(entry->second.mArgs != nullptr) {
							hash_bucket_type* bucket = bucketsof(entry)->find(entry);
							if(!bucket->mEntries.trivial()) {
								bucketsof(entry)->mChanged.add_front(bucket);
							}
						}
					}

					// split classes in union find
					for(std::size_t i = 0; i < split_pos; i++){
						g_iterator entry = mEqualityComponent[i];
						entry->second.mVisited = false;
						mUnionFind.set_class(entry->second.mUFIndex, oldcentry);
					}

					newcnode = itrRhs;
					for(std::size_t i = split_pos; i < mEqualityComponent.size(); i++) {
						g_iterator entry = mEqualityComponent[i];
						mUnionFind.set_class(entry->second.mUFIndex, newcnode->second.mUFIndex);
					}

					// split implicit neighbors of the old representative
					for(std::size_t i = oldcnode->second.mImplicit.size() - 1; i < oldcnode->second.mImplicit.size(); i--) {
						implicit_edge_info *edge = oldcnode->second.mImplicit[i];
						if(edge->mRealPred->second.mVisited) {
							oldcnode->second.mImplicit.remove(edge);
							edge->mPred = newcnode;
							edge->mOther->mSucc = newcnode;
							newcnode->second.mImplicit.add(edge);
						}
					}
				} else {
					std::size_t split_pos = mEqualityComponent.size();
					if(P_bfs_search_explicit(itrRhs, itrLhs)) {
						assert(false);
					}
					
					// inform hash buckets about changing indizes
					for(g_iterator entry : mEqualityComponent) {
						if(entry->second.mArgs != nullptr) {
							hash_bucket_type* bucket = bucketsof(entry)->find(entry);
							if(!bucket->mEntries.trivial()) {
								bucketsof(entry)->mChanged.add_front(bucket);
							}
						}
					}
					
					// split classes in union find
					newcnode = itrLhs;
					for(std::size_t i = 0; i < split_pos; i++){
						g_iterator entry = mEqualityComponent[i];
						mUnionFind.set_class(entry->second.mUFIndex, newcnode->second.mUFIndex);
					}
					
					for(std::size_t i = split_pos; i < mEqualityComponent.size(); i++) {
						g_iterator entry = mEqualityComponent[i];
						entry->second.mVisited = false;
						mUnionFind.set_class(entry->second.mUFIndex, oldcentry);
					}
					
					// split implicit neighbors of the old representative
					for(std::size_t i = oldcnode->second.mImplicit.size() - 1; i < oldcnode->second.mImplicit.size(); i--) {
						implicit_edge_info *edge = oldcnode->second.mImplicit[i];
						if(edge->mRealPred->second.mVisited) {
							oldcnode->second.mImplicit.remove(edge);
							edge->mPred = newcnode;
							edge->mOther->mSucc = newcnode;
							newcnode->second.mImplicit.add(edge);
						}
					}
				}
				
				P_clear_bfs_markings();
				
				// split the upper component and update component union find
				
				std::size_t oldccentry = mComponentUnionFind.find(oldcentry);
				
				if(P_bfs_search_implicit(oldcnode, newcnode)) {
					assert(false);
				}
				g_iterator oldccnode = mUnionFind[oldccentry];
				g_iterator newccnode;
				
				// all inequality neighbors have to checked; instead we remove them all and add them to possible inconsistencies so they are reinserted at a later point all together
				P_remove_ineq_edges_of_vertex(oldccnode);
				
				// if old component entry is on left side, keep it on left side, otherwise keep it on right side
				if(oldccnode->second.mVisited) {
					for(g_iterator entry : mEqualityComponent) {
						mComponentUnionFind.set_class(entry->second.mUFIndex, oldccentry);
					}
					P_clear_bfs_markings();

					if(P_bfs_search_implicit(newcnode, oldcnode)) {
						assert(false);
					}

					newccnode = newcnode;
					for(g_iterator entry : mEqualityComponent) {
						mComponentUnionFind.set_class(entry->second.mUFIndex, newccnode->second.mUFIndex);
					}
					
				} else {
					newccnode = oldcnode;
					for(g_iterator entry : mEqualityComponent) {
						mComponentUnionFind.set_class(entry->second.mUFIndex, newccnode->second.mUFIndex);
					}
					P_clear_bfs_markings();

					if(P_bfs_search_implicit(newcnode, oldcnode)) {
						assert(false);
					}

					for(g_iterator entry : mEqualityComponent) {
						mComponentUnionFind.set_class(entry->second.mUFIndex, oldccentry);
					}
				}
				
				P_clear_bfs_markings();
				
				// remember that oldccentry was split; this information will be used to update the hash buckets
				mSplitClasses.push_back(oldccentry);
				mComponentUnionFind[oldccentry].mIsSplit = true;
				
				// update hash buckets and equality graph iteratively until it stabilizes
				P_process_split_list();
			}

			P_clear_bfs_markings();
		}

		if(Settings::printBucketSets) {
			P_print_bucket_sets();
		}
	}

	template<class Settings>
		void EQModule<Settings>::P_update_model_variable()
	{
		for(variable_type entry : mVariables) {
			std::size_t eqClass = mUnionFind.find(entry.second->second.mUFIndex);
			eqClass = mComponentUnionFind.find(eqClass);

			auto sortValueIter = mClassToSortValue.find(eqClass);

			if(sortValueIter == mClassToSortValue.end()) {
				sortValueIter = mClassToSortValue.emplace(eqClass, newSortValue(entry.first.domain())).first;
			}

			mModel.emplace(entry.first.variable(), sortValueIter->second);
		}
	}

	template<class Settings>
		bool EQModule<Settings>::P_check_model_extension(carl::UFModel& ufModel, g_iterator term, const std::vector<carl::SortValue>& args, const carl::SortValue& result) const
	{
		auto&& findVariableFor = [&] (const carl::SortValue& value) -> g_iterator {
			auto&& iter = std::find_if(mClassToSortValue.begin(), mClassToSortValue.end(), [&] (const std::pair<std::size_t, carl::SortValue>& entry) { return entry.second == value; } );

			assert(iter != mClassToSortValue.end());
			return mUnionFind[iter->first];
		};

		carl::SortValue val = ufModel.get(args);

		assert(term->first.isUFInstance());
		if(!(val == result) && !(val == defaultSortValue(term->first.asUFInstance().uninterpretedFunction().codomain()))) {
			std::cerr << "Failure: Trying to map " << term->first << "(arguments";

			for(std::size_t i = 0; i < args.size(); ++i) {
				std::cerr << " '" << findVariableFor(args[i])->first << '\'';
			}

			std::cerr << ") to sort value '" << result << "' (variable '" << findVariableFor(result)->first;
			std::cerr << "'), previously mapped to '" << val << "' (variable '" << findVariableFor(val)->first << "')!" << std::endl;
			return false;
		}

		return true;
	}

	template<class Settings>
		void EQModule<Settings>::P_update_model_function()
	{
		for(typename function_map_type::iterator i = mFunctionMap.begin(), e = mFunctionMap.end(); i != e; ++i) {
			carl::UFModel &ufModel = mModel.emplace(i->first, carl::UFModel(i->first)).first->second.asUFModel();

			for(g_iterator entry : i->second.mInstances) {
				std::vector<carl::SortValue> args;
				args.reserve(arityof(entry));
				for(std::size_t i = 0, s = arityof(entry); i < s; ++i) {
					const auto& term = boost::get<carl::UTerm>(argsof(entry)[i]->first);
					assert(term.isUVariable());
					const auto& var = term.asUVariable();
					args.push_back(mModel.find(var.variable())->second.asSortValue());
				}

				std::size_t eqClass = mUnionFind.find(entry->second.mUFIndex);
				eqClass = mComponentUnionFind.find(eqClass);

				auto sortValueIter = mClassToSortValue.find(eqClass);

				if(sortValueIter == mClassToSortValue.end()) {
					sortValueIter = mClassToSortValue.emplace(eqClass, newSortValue(i->first.codomain())).first;
				}

				assert(P_check_model_extension(ufModel, entry, args, sortValueIter->second));
				ufModel.extend(args, sortValueIter->second);
			}
		}
	}

	template<class Settings>
		void EQModule<Settings>::P_update_model()
	{
		mModel.clear();
		if(solverState() == SAT) {
			P_update_model_variable();
			P_update_model_function();
		}
	}

	template<class Settings>
		void EQModule<Settings>::updateModel() const
	{
		const_cast<EQModule<Settings>&>(*this).P_update_model();
	}
	
	template<typename Settings>
		void EQModule<Settings>::P_process_split_list()
	{
		bool change;

		do {
			change = false;

			mDeletedEdges.clear();

			// split hash buckets; this method uses the information saved in mSplitClasses and provides a list of edges to be deleted
			P_split_buckets();

			// save information about which classes will split due to removed edges
			for(bfs_todo_entry entry : mDeletedEdges){
				g_iterator node = entry.first;
				std::size_t index = mComponentUnionFind.find(node->second.mUFIndex);
				if(!mComponentUnionFind[index].mIsSplit){
					P_remove_ineq_edges_of_vertex(mUnionFind[index]);
					mSplitClasses.push_back(index);
					mComponentUnionFind[index].mIsSplit = true;
					change = true;
				}
			}

			// update component union find accordingly
			std::size_t position = 0;
			for(bfs_todo_entry entry : mDeletedEdges){
				g_iterator node = entry.first;
				if(!node->second.mVisited){
					if(P_bfs_search_implicit(node, entry.second)){
						assert(false);
					}

					for(std::size_t i = position; i < mEqualityComponent.size(); i++){
						mComponentUnionFind.set_class(	mEqualityComponent[i]->second.mUFIndex, 
														mEqualityComponent[position]->second.mUFIndex);
					}

					position = mEqualityComponent.size();
				}
			}
			P_clear_bfs_markings();

		} while(change);

		P_post_split_update_classes();
	}
	
	template<class Settings>
		void EQModule<Settings>::P_check_inconsistencies()
	{
		if(Settings::printFormulas) {
			std::cout << "Check inconsistencies (" << mPossibleInconsistencies.size() << "):" << std::endl;
		}
		
		for (std::size_t i = mPossibleInconsistencies.size() - 1; i < mPossibleInconsistencies.size(); i--) {
			ineq_edge_info* ineq_edge = mPossibleInconsistencies[i];
			
			std::size_t indexLhs = mUnionFind.find(ineq_edge->mRealPred->second.mUFIndex);
			std::size_t indexRhs = mUnionFind.find(ineq_edge->mRealSucc->second.mUFIndex);
			
			std::size_t indexCLhs = mComponentUnionFind.find(indexLhs);
			std::size_t indexCRhs = mComponentUnionFind.find(indexRhs);
			
			if(Settings::printFormulas) {
				std::cout << "\t" << ineq_edge->mFormula;
			}
			
			if (indexCLhs != indexCRhs) {
				ineq_edge->mPred = mUnionFind[indexCLhs];
				ineq_edge->mSucc = mUnionFind[indexCRhs];

				ineq_edge->mOther->mPred = mUnionFind[indexCRhs];
				ineq_edge->mOther->mSucc = mUnionFind[indexCLhs];

				ineq_edge->mPred->second.mIneq.add(ineq_edge);
				ineq_edge->mSucc->second.mIneq.add(ineq_edge->mOther);

				if(indexCLhs < indexCRhs) {
					mIneqMatrix[std::make_pair(indexCLhs,indexCRhs)].emplace_back(ineq_edge);
				} else {
					mIneqMatrix[std::make_pair(indexCRhs,indexCLhs)].emplace_back(ineq_edge->mOther);
				}
				
				std::swap(mPossibleInconsistencies.back(), mPossibleInconsistencies[i]);
				mPossibleInconsistencies.pop_back();
				
				if(Settings::printFormulas) {
					std::cout << " inserted" << std::endl;
				}
			} else {
				if(Settings::printFormulas) {
					std::cout << " not inserted" << std::endl;
				}
			}
		}
	}
	
	template<class Settings>
		bool EQModule<Settings>::P_cc_union_for_ineq(std::size_t indexCOld, std::size_t indexCNew)
	{
		assert(indexCOld != indexCNew);
		std::size_t max = std::max(indexCOld, indexCNew);
		std::size_t min = std::min(indexCOld, indexCNew);
		
		bool found_inconsistency = false;
		
		// check for inconsistency
		auto matrix_entry = mIneqMatrix.find(std::make_pair(min,max));
		
		if(matrix_entry != mIneqMatrix.end() && !matrix_entry->second.empty()) {
			for(ineq_edge_info* ineq_edge : matrix_entry->second) {
				ineq_edge->mSucc->second.mIneq.remove(ineq_edge->mOther);
				ineq_edge->mPred->second.mIneq.remove(ineq_edge);
				
				found_inconsistency = true;
				
				if(Settings::printFormulas) {
					std::cout << "Found inconsistency: " << ineq_edge->mFormula << std::endl;
				}
			}

			mPossibleInconsistencies.insert(mPossibleInconsistencies.end(), matrix_entry->second.begin(), matrix_entry->second.end());
			mIneqMatrix.erase(matrix_entry);
		}

		g_iterator nodeCOld = mUnionFind[indexCOld];
		g_iterator nodeCNew = mUnionFind[indexCNew];

		// fix inequality edges
		for(std::size_t i = nodeCOld->second.mIneq.size() - 1; i < nodeCOld->second.mIneq.size(); i--) {
			ineq_edge_info *edge = nodeCOld->second.mIneq[i];
			nodeCOld->second.mIneq.remove_back();
			edge->mPred = nodeCNew;
			edge->mOther->mSucc = nodeCNew;
			nodeCNew->second.mIneq.add(edge);

			std::size_t indexSucc = edge->mSucc->second.mUFIndex;
			if(indexCOld < indexSucc) {
				auto matrix_entry = mIneqMatrix.find(std::make_pair(indexCOld,indexSucc));
				
				if(matrix_entry != mIneqMatrix.end() && !matrix_entry->second.empty()) {
					auto &new_entry = (indexCNew < indexSucc) ? mIneqMatrix[std::make_pair(indexCNew, indexSucc)] : mIneqMatrix[std::make_pair(indexSucc, indexCNew)];

					if(indexCNew < indexSucc) {
						new_entry.consume(std::move(matrix_entry->second));
					} else {
						new_entry.reserve(new_entry.size() + matrix_entry->second.size());
						for(ineq_edge_info* ineq_edge : matrix_entry->second) {
							new_entry.emplace_back(ineq_edge->mOther);
						}
					}

					mIneqMatrix.erase(matrix_entry);
				}
			} else {
				auto matrix_entry = mIneqMatrix.find(std::make_pair(indexSucc,indexCOld));
				
				if(matrix_entry != mIneqMatrix.end() && !matrix_entry->second.empty()) {
					auto &new_entry = (indexCNew < indexSucc) ? mIneqMatrix[std::make_pair(indexCNew, indexSucc)] : mIneqMatrix[std::make_pair(indexSucc, indexCNew)];

					if(indexCNew < indexSucc) {
						new_entry.reserve(new_entry.size() + matrix_entry->second.size());
						for(ineq_edge_info* ineq_edge : matrix_entry->second) {
							new_entry.emplace_back(ineq_edge->mOther);
						}
					} else {
						new_entry.consume(std::move(matrix_entry->second));
					}

					mIneqMatrix.erase(matrix_entry);
				}
			}
		}
		
		return found_inconsistency;
	}
	
	template<class Settings>
		void EQModule<Settings>::P_remove_ineq_edges_of_vertex(g_iterator node)
	{
		for(std::size_t i = node->second.mIneq.size() - 1; i < node->second.mIneq.size(); i--) {
			ineq_edge_info *edge = node->second.mIneq[i];
			node->second.mIneq.remove_back();
			edge->mSucc->second.mIneq.remove(edge->mOther);
			mPossibleInconsistencies.push_back(edge);
			std::size_t pos1 = edge->mPred->second.mUFIndex;
			std::size_t pos2 = edge->mSucc->second.mUFIndex;
			if(pos1 < pos2) {
				mIneqMatrix.erase(std::make_pair(pos1,pos2));
			} else {
				mIneqMatrix.erase(std::make_pair(pos2,pos1));
			}
		}
	}

	template<std::size_t N, class RandomAccessIterator, class Comparator>
		static void select_best(
			typename std::iterator_traits<RandomAccessIterator>::value_type* result,
			RandomAccessIterator begin, RandomAccessIterator end,
			Comparator&& compare
		)
	{
		typename std::iterator_traits<RandomAccessIterator>::difference_type d = std::distance(begin, end);
		assert(d >= 0);

		if(static_cast<std::size_t>(d) <= N) {
			std::copy(begin, end, result);
		} else {
			RandomAccessIterator i(begin);
			std::advance(i, N);
			std::copy(begin, i, result);
			std::sort(result, result + N, std::forward<Comparator>(compare));

			for(; i != end; ++i) {
				const auto last = result + N - 1;
				auto j = last;

				for(; j >= result; --j) {
					if(!compare(*i, *j))
						break;
				}

				if(j != last) {
					++j;

					for(auto k = last; k > j; --k) {
						*k = std::move(*(k-1));
					}

					*j = *i;
				}
			}
		}
	}

	template<class Settings>
		Answer EQModule<Settings>::checkCore()
	{
		Answer answer = (mCountNonUEQFormulas == 0) ? SAT : UNKNOWN;
		
		if(!mFunctionMap.empty()) {
			process_merge_lists();
		}
		
		// check list of possible inconsistencies for real inconsistencies
		P_check_inconsistencies();
		
		// now, mPossibleInconsistencies contains only real inconsistencies
		if(!mPossibleInconsistencies.empty()) {
			answer = UNSAT;
			
			// return as many infeasible subsets as we are configured to do
			std::size_t count = mPossibleInconsistencies.size();
			if(count > Settings::useMaxInfeasibleSubsets) {
//				// TODO use the n best ones according to some heuristic (activities?? inverse activities seem to work better...?)
//				ineq_edge_info* best[Settings::useMaxInfeasibleSubsets];
//				select_best<Settings::useMaxInfeasibleSubsets>(
//					best,
//					mPossibleInconsistencies.begin(),
//					mPossibleInconsistencies.end(),
//					[] (ineq_edge_info* e1, ineq_edge_info* e2) -> bool {
//						return e1->mFormula.activity() < e2->mFormula.activity();
//					}
//				);
//
//				for(std::size_t i = 0; i < Settings::useMaxInfeasibleSubsets; ++i) {
//					ineq_edge_info* ineq_edge = best[i];
//					P_construct_infeasible_subset(ineq_edge->mRealPred, ineq_edge->mRealSucc, ineq_edge->mFormula);
//				}

				// select the useMaxInfeasibleSubsets first ones
				for(std::size_t i = 0; i < Settings::useMaxInfeasibleSubsets; ++i) {
					ineq_edge_info* ineq_edge = mPossibleInconsistencies[i];
					P_construct_infeasible_subset(ineq_edge->mRealPred, ineq_edge->mRealSucc, ineq_edge->mFormula);
				}
			} else {
				// use all
				for(std::size_t i = 0; i < count; i++) {
					ineq_edge_info* ineq_edge = mPossibleInconsistencies[i];
					P_construct_infeasible_subset(ineq_edge->mRealPred, ineq_edge->mRealSucc, ineq_edge->mFormula);
				}
			}
		} else {
			if(Settings::deduceUnassignedLiterals) {
				if(mCheckForDeductionCounter++ % Settings::testRateForDeductions == 0) {

#ifdef SMTRAT_DEVOPTION_Statistics
					mStatistics.countCheckedUnassignedLiterals();
#endif
					// check whether we can deduce unassigned literals
					P_check_for_unassigned_literals();
				}
			}
		}

		if(Settings::printFormulas) {
			std::cout << "Answer: " << answer << std::endl;
		}

		if(Settings::printInfeasibleSubsetFormulas && answer == UNSAT) {
			P_print_infeasible_subset();
		}

		if(Settings::visualiseGraphs) {
			if(!Settings::visualiseOnlyWhenInconsistent || answer == UNSAT) {
				P_print_graph();
			}
		}

		return answer;
	}

	template<class Settings>
		std::size_t EQModule<Settings>::arityof(g_iterator finstance)
	{
		assert(finstance->second.mArgs != nullptr);
		return finstance->second.mArgs->mArity;
	}

	template<class Settings>
		auto EQModule<Settings>::argsof(g_iterator finstance) -> const g_iterator*
	{
		assert(finstance->second.mArgs != nullptr);
		return finstance->second.mArgs->mArgs;
	}

	template<class Settings>
		auto EQModule<Settings>::bucketsof(g_iterator finstance) -> hash_buckets_type*
	{
		assert(finstance->second.mArgs != nullptr);
		return finstance->second.mArgs->mBuckets;
	}

	template<class Settings>
		void EQModule<Settings>::P_add_explicit_edge(g_iterator lhs, g_iterator rhs, const FormulaT& formula)
	{
		edge_info *lhs_edge = &mExplicitEdgeAlloc.emplace(lhs,rhs,formula);
		edge_info *rhs_edge = &mExplicitEdgeAlloc.emplace(rhs,lhs,formula);

		lhs_edge->mOther = rhs_edge;
		rhs_edge->mOther = lhs_edge;

		lhs->second.mExplicit.add(lhs_edge);
		rhs->second.mExplicit.add(rhs_edge);
	}

	template<class Settings>
		void EQModule<Settings>::P_destroy_implicit_edge(implicit_edge_info* edge)
	{
		implicit_edge_info* other = edge->mOther;

		assert(edge->mSupportingBucket == nullptr || other->mSupportingBucket == nullptr);
		assert(edge->mSupportingBucket != nullptr || other->mSupportingBucket != nullptr);

		implicit_edge_info *supported = edge;
		hash_bucket_type *bucket = edge->mSupportingBucket;
		if(bucket == nullptr) {
			supported = other;
			bucket = other->mSupportingBucket;
		}

		bucket->supportedEdges.remove(supported);

		edge->mPred->second.mImplicit.remove_destroy(edge);
		other->mPred->second.mImplicit.remove_destroy(other);
	}

	template<class Settings>
		auto EQModule<Settings>::P_add_implicit_edge(g_iterator lhs, g_iterator rhs, g_iterator real_lhs, g_iterator real_rhs) -> implicit_edge_info*
	{
		implicit_edge_info *lhs_edge = &mImplicitEdgeAlloc.emplace(lhs, rhs, real_lhs, real_rhs);
		implicit_edge_info *rhs_edge = &mImplicitEdgeAlloc.emplace(rhs, lhs, real_rhs, real_lhs);

		lhs_edge->mOther = rhs_edge;
		rhs_edge->mOther = lhs_edge;

		lhs->second.mImplicit.add(lhs_edge);
		rhs->second.mImplicit.add(rhs_edge);

		return lhs_edge;
	}
	
	template<class Settings>
		void EQModule<Settings>::P_remove_edge(g_iterator lhs, g_iterator rhs, const FormulaT& formula)
	{
		edge_info *lhsptr = lhs->second.find_edge(formula);
		edge_info *rhsptr = lhsptr->mOther;
		
		lhs->second.mExplicit.remove_destroy(lhsptr);
		rhs->second.mExplicit.remove_destroy(rhsptr);
	}
	
	template<class Settings>
		void EQModule<Settings>::P_add_ineq_edge(std::size_t indexLhs, std::size_t indexRhs, g_iterator real_lhs, g_iterator real_rhs, const FormulaT& formula)
	{
		assert(indexLhs != indexRhs);
		g_iterator lhs = mUnionFind[indexLhs];
		g_iterator rhs = mUnionFind[indexRhs];
		
		ineq_edge_info *lhs_edge = &mIneqEdgeAlloc.emplace(lhs,rhs,real_lhs,real_rhs,formula);
		ineq_edge_info *rhs_edge = &mIneqEdgeAlloc.emplace(rhs,lhs,real_rhs,real_lhs,formula);

		lhs_edge->mOther = rhs_edge;
		rhs_edge->mOther = lhs_edge;

		lhs->second.mIneq.add(lhs_edge);
		rhs->second.mIneq.add(rhs_edge);
		
		if(indexLhs < indexRhs) {
			mIneqMatrix[std::make_pair(indexLhs,indexRhs)].emplace_back(lhs_edge);
		} else {
			mIneqMatrix[std::make_pair(indexRhs,indexLhs)].emplace_back(rhs_edge);
		}
	}
	
	template<class Settings>
		void EQModule<Settings>::P_remove_ineq_edge(g_iterator lhs, g_iterator rhs, const FormulaT& formula)
	{
		std::size_t indexLhs = mUnionFind.find(lhs->second.mUFIndex);
		std::size_t indexRhs = mUnionFind.find(rhs->second.mUFIndex);
			
		std::size_t indexCLhs = mComponentUnionFind.find(indexLhs);
		std::size_t indexCRhs = mComponentUnionFind.find(indexRhs);
		
		for (std::size_t i = mPossibleInconsistencies.size() - 1; i < mPossibleInconsistencies.size(); i--) {
			ineq_edge_info* lhs_edge = mPossibleInconsistencies[i];

			if(lhs_edge->mFormula == formula) {
				std::swap(mPossibleInconsistencies.back(), mPossibleInconsistencies[i]);
				mPossibleInconsistencies.pop_back();
				
				lhs_edge->mOther->~ineq_edge_info();
				mIneqEdgeAlloc.free(lhs_edge->mOther);
				lhs_edge->~ineq_edge_info();
				mIneqEdgeAlloc.free(lhs_edge);
				return;
			}
		}
		
		g_iterator ccLhs = mUnionFind[indexCLhs];

		ineq_edge_info **ptr = std::find_if(ccLhs->second.mIneq.begin(), ccLhs->second.mIneq.end(), [&] (ineq_edge_info* e) -> bool { return e->mFormula == formula; } );
		assert(ptr != ccLhs->second.mIneq.end());
		ineq_edge_info* lhs_edge = *ptr;
		ineq_edge_info* rhs_edge = lhs_edge->mOther;

		if(indexCLhs < indexCRhs) {
			auto &edges = mIneqMatrix[std::make_pair(indexCLhs, indexCRhs)];
			auto pos = std::find(edges.begin(), edges.end(), lhs_edge);
			assert(pos != edges.end());
			std::swap(edges.back(), *pos);
			edges.pop_back();
		} else {
			auto &edges = mIneqMatrix[std::make_pair(indexCRhs, indexCLhs)];
			auto pos = std::find(edges.begin(), edges.end(), rhs_edge);
			assert(pos != edges.end());
			std::swap(edges.back(), *pos);
			edges.pop_back();
		}

		lhs_edge->mSucc->second.mIneq.remove_destroy(rhs_edge);
		ccLhs->second.mIneq.remove_destroy(lhs_edge);
	}

	template<class Settings>
		EQModule<Settings>::graph_info::~graph_info()
	{
		std::free(mArgs);
	}
	
	template<class Settings>
		auto EQModule<Settings>::graph_info::find_edge(const FormulaT& f) -> edge_info*
	{
		edge_info **ptr = std::find_if(mExplicit.begin(), mExplicit.end(), [&] (edge_info* e) -> bool { return e->mFormula == f; } );
		return ptr != mExplicit.end() ? *ptr : nullptr;
	}

	template<class Settings>
		bool EQModule<Settings>::P_bfs_search_implicit(g_iterator start, g_iterator target)
	{
		if(start == target) {
			return true;
		}

		bool found_target = false;

		mBfsQueue.push_back(start);
		mEqualityComponent.push_back(start);
		start->second.mVisited = true;

		while(!mBfsQueue.empty()) {
			g_iterator cur(mBfsQueue.front());
			mBfsQueue.pop_front();

			for(implicit_edge_info *edge : cur->second.mImplicit) {
				if(!edge->mSucc->second.mVisited) {
					mBfsQueue.push_back(edge->mSucc);
					mEqualityComponent.push_back(edge->mSucc);
					edge->mSucc->second.mVisited = true;
					edge->mSucc->second.mImplicitPred = edge;
					if(edge->mSucc == target) {
						mBfsQueue.clear();
						found_target = true;
						break;
					}
				}
			}
		}

		return found_target;
	}

	template<class Settings>
		bool EQModule<Settings>::P_bfs_search_explicit(g_iterator start, g_iterator target)
	{
		if(start == target) {
			return true;
		}

		g_iterator cur;
		bool found_target = false;

		mBfsQueue.push_back(start);
		mEqualityComponent.push_back(start);
		start->second.mVisited = true;

		while(!mBfsQueue.empty()) {
			cur = mBfsQueue.front();
			mBfsQueue.pop_front();

			for(edge_info *edge : cur->second.mExplicit) {
				if(!edge->mSucc->second.mVisited) {
					mBfsQueue.push_back(edge->mSucc);
					mEqualityComponent.push_back(edge->mSucc);
					edge->mSucc->second.mVisited = true;
					edge->mSucc->second.mPred = edge;
					if(edge->mSucc == target){
						mBfsQueue.clear();
						found_target = true;
						break;
					}
				}
			}
		}

		return found_target;
	}
	
	template<class Settings>
		bool EQModule<Settings>::P_bfs_search_weighted_explicit(g_iterator start, g_iterator target)
	{
		bool found_target = false;

		mBfsQueue.push_back(start);
		mEqualityComponent.push_back(start);
		start->second.mVisited = true;

		while(!mBfsQueue.empty()) {
			g_iterator cur(mBfsQueue.front());
			mBfsQueue.pop_front();

			cur->second.mWeightFixed = true;

			for(edge_info *edge : cur->second.mExplicit) {
				if(!edge->mSucc->second.mVisited) {
					mBfsQueue.push_back(edge->mSucc);
					mEqualityComponent.push_back(edge->mSucc);
					edge->mSucc->second.mVisited = true;
					edge->mSucc->second.mPred = edge;
					edge->mSucc->second.mWeight = cur->second.mWeight + edge->mFormula.activity();
				} else if(!edge->mSucc->second.mWeightFixed) {
					double cur_weight = cur->second.mWeight + edge->mFormula.activity();
					if(edge->mSucc->second.mWeight < cur_weight) {
						edge->mSucc->second.mWeight = cur_weight;
						edge->mSucc->second.mPred = edge;
					}
				}
			}

			if(cur == target) {
				mBfsQueue.clear();
				found_target = true;
				break;
			}
		}

		// reset flags for visited nodes
		for(std::size_t i = 0; i < mEqualityComponent.size(); i++) {
			mEqualityComponent[i]->second.mVisited = false;
			mEqualityComponent[i]->second.mWeight = 0;
			mEqualityComponent[i]->second.mWeightFixed = false;
		}
		
		// clear component infos
		mEqualityComponent.clear();
		
		return found_target;
	}
	
	template<class Settings>
		void EQModule<Settings>::P_clear_bfs_markings()
	{
		// reset flags for visited nodes
		for(std::size_t i = 0; i < mEqualityComponent.size(); i++) {
			mEqualityComponent[i]->second.mVisited = false;
		}

		// clear component infos
		mEqualityComponent.clear();
	}
	
	template<typename Settings>
		void EQModule<Settings>::P_add_explicit_path_to_infeasible(g_iterator start, g_iterator target, FormulaSetT& infeasible)
	{
		g_iterator current = target;
		
		while(current != start) {
			edge_info *cur = current->second.mPred;

			assert(pReceivedFormula()->contains(cur->mFormula));
			
			infeasible.insert(cur->mFormula);
			current = cur->mPred;
		}
	}
	
	template<typename Settings>
		void EQModule<Settings>::P_add_explicit_path_to_infeasible_neg(g_iterator start, g_iterator target, FormulaSetT& infeasible)
	{
		g_iterator current = target;

		while(current != start) {
			edge_info *cur = current->second.mPred;

			assert(pReceivedFormula()->contains(cur->mFormula));

			infeasible.insert(FormulaT(carl::NOT, cur->mFormula));
			current = cur->mPred;
		}
	}

	template<typename Settings>
		void EQModule<Settings>::P_construct_proof(FormulaSetT& output, g_iterator start, g_iterator target)
	{
		mImplicitEdgeQueue.push_back(bfs_todo_entry(start, target));
				
		while (!mImplicitEdgeQueue.empty()) {
			bfs_todo_entry front = mImplicitEdgeQueue.front();
			mImplicitEdgeQueue.pop_front();

			implicit_edge_info *current_edge = nullptr, *pred_edge;

			std::size_t index_start = mUnionFind.find(front.first->second.mUFIndex);
			std::size_t index_target = mUnionFind.find(front.second->second.mUFIndex);

			if(index_start == index_target) {
				bool foundPath = P_bfs_search_weighted_explicit(front.first, front.second);
				assert(foundPath); (void)foundPath;

				P_add_explicit_path_to_infeasible(front.first, front.second, output);
			} else {
				g_iterator start_component = mUnionFind[index_start];
				g_iterator target_component = mUnionFind[index_target];

				assert(mComponentUnionFind.equivalent(index_start, index_target));

				bool foundPath = P_bfs_search_implicit(start_component, target_component);
				P_clear_bfs_markings();
				assert(foundPath); (void)foundPath;

				g_iterator current = target_component;

				while(current != start_component) {
					pred_edge = current_edge;
					current_edge = current->second.mImplicitPred;

					assert(current_edge != nullptr);

					if(pred_edge == nullptr) {
						bool foundPath = P_bfs_search_weighted_explicit(current_edge->mRealSucc, front.second);
						assert(foundPath); (void)foundPath;

						P_add_explicit_path_to_infeasible(current_edge->mRealSucc, front.second, output);
					} else {
						bool foundPath = P_bfs_search_weighted_explicit(current_edge->mRealSucc, pred_edge->mRealPred);
						assert(foundPath); (void)foundPath;

						P_add_explicit_path_to_infeasible(current_edge->mRealSucc, pred_edge->mRealPred, output);
					}

					if(!current_edge->mIsProven) {
						const g_iterator *targetargs = argsof(current_edge->mRealSucc);
						const g_iterator *startargs = argsof(current_edge->mRealPred);

						for (std::size_t i = 0, s = arityof(current_edge->mRealSucc); i < s; ++i) {
							assert(mImplicitEdgeQueue.size() < mImplicitEdgeQueue.capacity());

							if(startargs[i] != targetargs[i]) {
								assert(
									mComponentUnionFind.equivalent(
										mUnionFind.find(startargs[i]->second.mUFIndex),
										mUnionFind.find(targetargs[i]->second.mUFIndex)
									)
								);

								mImplicitEdgeQueue.push_back(bfs_todo_entry(startargs[i], targetargs[i]));
							}
						}

						current_edge->mIsProven = true;
						current_edge->mOther->mIsProven = true;
						mImplicitEdgeIsProvenList.push_back(current_edge);
						mImplicitEdgeIsProvenList.push_back(current_edge->mOther);
					}

					current = current_edge->mPred;
				}

				foundPath = P_bfs_search_weighted_explicit(current_edge->mRealPred, front.first);
				assert(foundPath); (void)foundPath;

				P_add_explicit_path_to_infeasible(current_edge->mRealPred, front.first, output);
			}
		}
	}



	template<typename Settings>
		void EQModule<Settings>::P_construct_proof_neg(FormulaSetT& output, g_iterator start, g_iterator target)
	{
		mImplicitEdgeQueue.push_back(bfs_todo_entry(start, target));

		while (!mImplicitEdgeQueue.empty()) {
			bfs_todo_entry top = mImplicitEdgeQueue.front();
			mImplicitEdgeQueue.pop_front();

			implicit_edge_info *current_edge = nullptr, *pred_edge;

			std::size_t index_start = mUnionFind.find(top.first->second.mUFIndex);
			std::size_t index_target = mUnionFind.find(top.second->second.mUFIndex);

			if(index_start == index_target) {
				bool foundPath = P_bfs_search_weighted_explicit(top.first, top.second);
				assert(foundPath); (void)foundPath;

				P_add_explicit_path_to_infeasible_neg(top.first, top.second, output);
			} else {
				g_iterator start_component = mUnionFind[index_start];
				g_iterator target_component = mUnionFind[index_target];

				assert(mComponentUnionFind.equivalent(index_start, index_target));

				bool foundPath = P_bfs_search_implicit(start_component, target_component);
				P_clear_bfs_markings();
				assert(foundPath); (void)foundPath;

				g_iterator current = target_component;

				while(current != start_component) {
					pred_edge = current_edge;
					current_edge = current->second.mImplicitPred;

					assert(current_edge != nullptr);

					if(pred_edge == nullptr) {
						bool foundPath = P_bfs_search_weighted_explicit(current_edge->mRealSucc, top.second);
						assert(foundPath); (void)foundPath;

						P_add_explicit_path_to_infeasible_neg(current_edge->mRealSucc, top.second, output);
					} else {
						bool foundPath = P_bfs_search_weighted_explicit(current_edge->mRealSucc, pred_edge->mRealPred);
						assert(foundPath); (void)foundPath;

						P_add_explicit_path_to_infeasible_neg(current_edge->mRealSucc, pred_edge->mRealPred, output);
					}

					if(!current_edge->mIsProven) {
						const g_iterator *targetargs = argsof(current_edge->mRealSucc);
						const g_iterator *startargs = argsof(current_edge->mRealPred);

						for (std::size_t i = 0, s = arityof(current_edge->mRealSucc); i < s; ++i) {
							assert(mImplicitEdgeQueue.size() < mImplicitEdgeQueue.capacity());

							if(startargs[i] != targetargs[i]) {
								assert(
									mComponentUnionFind.equivalent(
										mUnionFind.find(startargs[i]->second.mUFIndex),
										mUnionFind.find(targetargs[i]->second.mUFIndex)
									)
								);

								mImplicitEdgeQueue.push_back(bfs_todo_entry(startargs[i], targetargs[i]));
							}
						}

						current_edge->mIsProven = true;
						current_edge->mOther->mIsProven = true;
						mImplicitEdgeIsProvenList.push_back(current_edge);
						mImplicitEdgeIsProvenList.push_back(current_edge->mOther);
					}

					current = current_edge->mPred;
				}

				foundPath = P_bfs_search_weighted_explicit(current_edge->mRealPred, top.first);
				assert(foundPath); (void)foundPath;

				P_add_explicit_path_to_infeasible_neg(current_edge->mRealPred, top.first, output);
			}
		}
	}

	template<typename Settings>
		void EQModule<Settings>::P_clear_proven()
	{
		for(implicit_edge_info *entry : mImplicitEdgeIsProvenList) {
			entry->mIsProven = false;
		}

		mImplicitEdgeIsProvenList.clear();
	}

	template<typename Settings>
		void EQModule<Settings>::P_construct_infeasible_subset(g_iterator start, g_iterator target, const FormulaT& inequality)
	{
		assert(start != target);

#ifdef SMTRAT_DEVOPTION_Statistics
		mStatistics.countInfeasibleSubsets();
#endif

		mInfeasibleSubsets.emplace_back();
		FormulaSetT& infeasible = mInfeasibleSubsets.back();
		infeasible.insert(inequality);
		
		P_construct_proof(infeasible, start, target);
		P_clear_proven();
	}

	template<typename Settings>
		void EQModule<Settings>::P_check_for_unassigned_literals()
	{
		for(auto entry = mAllNotAssertedEqualities.begin(); entry != mAllNotAssertedEqualities.end(); ) {
			const FormulaT &formula = entry->mFormula;
			const UEquality &ueq = formula.u_equality();
			
			g_iterator itrLhs = entry->mLhs;
			g_iterator itrRhs = entry->mRhs;

			assert(itrLhs != mEqualityGraph.end());
			assert(itrRhs != mEqualityGraph.end());

			std::size_t indexLhs = mComponentUnionFind.find(mUnionFind.find(itrLhs->second.mUFIndex));
			std::size_t indexRhs = mComponentUnionFind.find(mUnionFind.find(itrRhs->second.mUFIndex));

			// we can deduce an equality
			if(indexLhs == indexRhs) {
				FormulaSetT formulas;

				P_construct_proof_neg(formulas, itrRhs, itrLhs);
				P_clear_proven();
				
				if(ueq.negated()) {
					formulas.insert(FormulaT(carl::NOT, formula));
					entry = mAllNotAssertedEqualities.erase(entry);
				} else {
					formulas.insert(formula);
					++entry;
				}

				FormulaT or_(carl::OR, std::move(formulas));

				if(Settings::printFormulas) {
					std::cout << "Adding deduction for not asserted formula '" << formula << "': " << std::endl;
					std::cout << '\'' << or_ << '\'' << std::endl;
				}

				#ifdef SMTRAT_DEVOPTION_Statistics
				mStatistics.countDeducedUnassignedLiterals();
				#endif
				SMTRAT_VALIDATION_ADD("smtrat.modules.eq","lemma_1",FormulaT( carl::FormulaType::NOT, or_ ),false);
				addLemma(or_);
			} else {
				std::size_t min, max;
				g_iterator itrMin, itrMax;

				if(indexLhs < indexRhs) {
					min = indexLhs;
					max = indexRhs;
					itrMin = itrLhs;
					itrMax = itrRhs;
				} else {
					min = indexRhs;
					max = indexLhs;
					itrMin = itrRhs;
					itrMax = itrLhs;
				}

				auto matrix_entry = mIneqMatrix.find(std::make_pair(min,max));

				// we can deduce an inequality ((a = c and b = d and a != b) implies c != d)
				if(matrix_entry != mIneqMatrix.end() && !matrix_entry->second.empty()) {
					ineq_edge_info* ineq_edge = matrix_entry->second.front();

					FormulaSetT formulas;
					formulas.insert(FormulaT(carl::NOT, ineq_edge->mFormula));

					P_construct_proof_neg(formulas, itrMin, ineq_edge->mRealPred);
					P_construct_proof_neg(formulas, itrMax, ineq_edge->mRealSucc);
					P_clear_proven();

					if(ueq.negated()) {
						formulas.insert(formula);
						++entry;
					} else {
						formulas.insert(FormulaT(carl::NOT, formula));
						entry = mAllNotAssertedEqualities.erase(entry);
					}

					FormulaT or_(carl::OR, std::move(formulas));

					if(Settings::printFormulas) {
						std::cout << "Adding deduction for not asserted formula '" << formula << "': " << std::endl;
						std::cout << '\'' << or_ << '\'' << std::endl;
					}

					#ifdef SMTRAT_DEVOPTION_Statistics
					mStatistics.countDeducedUnassignedLiterals();
					#endif
					SMTRAT_VALIDATION_ADD("smtrat.modules.eq","lemma_2",FormulaT( carl::FormulaType::NOT, or_ ),false);
                    addLemma(or_);
				} else {
					++entry;
				}
			}
		}
	}
	
	template<typename Settings>
		void EQModule<Settings>::P_add_implicit_edge_deduction(g_iterator i, g_iterator j)
	{
		if(Settings::addImplicitEdgeDeductions) {
			std::size_t rpindex = i->second.mUFIndex;
			std::size_t rsindex = j->second.mUFIndex;

			std::size_t maxindex = std::max(rpindex, rsindex);
			std::size_t minindex = std::min(rpindex, rsindex);

			if(++mPairMatrix.at(minindex,maxindex).mImplicitEventCount % Settings::implicitEdgeDeductionRate == 0) {
#ifdef SMTRAT_DEVOPTION_Statistics
				mStatistics.countImplicitEdgeDeduction();
#endif

				FormulaSetT outerformulas;

				++mGlobalPairSetAge;
				for(std::size_t arg = 0, s = arityof(i); arg < s; ++arg) {
					g_iterator farg = argsof(i)[arg], sarg = argsof(j)[arg];

					if(farg != sarg) {
						std::size_t amin = std::min(farg->second.mUFIndex, sarg->second.mUFIndex);
						std::size_t amax = std::max(farg->second.mUFIndex, sarg->second.mUFIndex);

						auto &entry = mPairMatrix.at(amin, amax);
						if(entry.mPairSetAge != mGlobalPairSetAge) {
							entry.mPairSetAge = mGlobalPairSetAge;

							FormulaT rhs(farg->first, sarg->first, false);
							outerformulas.insert(FormulaT(carl::NOT, rhs));

							FormulaSetT innerformulas;

							P_construct_proof_neg(innerformulas, farg, sarg);
							P_clear_proven();

							if(innerformulas.size() > 1) {
								innerformulas.insert(rhs);
								FormulaT or_(carl::OR, std::move(innerformulas));
								SMTRAT_VALIDATION_ADD("smtrat.modules.eq","lemma_3",FormulaT( carl::FormulaType::NOT, or_ ),false);
                                addLemma(or_);

								if(Settings::printFormulas) {
									std::cout << "Added implicit edge deduction for arguments: " << or_ << std::endl;
								}
							}
						}
					}
				}

				outerformulas.insert(FormulaT(i->first, j->first, false));
				FormulaT or_(carl::OR, std::move(outerformulas));
				SMTRAT_VALIDATION_ADD("smtrat.modules.eq","lemma_4",FormulaT( carl::FormulaType::NOT, or_ ),false);
				addLemma(or_);

				if(Settings::printFormulas) {
					std::cout << "Added implicit edge deduction for function instances: " << or_ << std::endl;
				}
			}
		}
	}

	template<typename Settings>
		auto EQModule<Settings>::find_representative(const term_type& term) -> const term_type*
	{
		auto giter = mEqualityGraph.find(term);

		if(giter == mEqualityGraph.end())
			return nullptr;

		struct is_uvariable_visitor : boost::static_visitor<bool> {
			constexpr bool operator()(const UVariable&) const noexcept {
				return true;
			}

			constexpr bool operator()(const UFInstance&) const noexcept {
				return false;
			}
		};

		const term_type* min = &term;
		bool minIsUVariable = term.isUVariable();

		mBfsQueue.push_back(giter);
		giter->second.mVisited = true;
		mEqualityComponent.push_back(giter);

		while(!mBfsQueue.empty()) {
			g_iterator cur = mBfsQueue.front();
			mBfsQueue.pop_front();

			for(edge_info *e : cur->second.mExplicit) {
				if(!e->mSucc->second.mVisited) {
					if(minIsUVariable && e->mSucc->first.isUVariable()) {
						if(e->mSucc->first < *min) {
							min = &(e->mSucc->first);
						}
					} else {
						if(e->mSucc->first.isUVariable()) {
							min = &(e->mSucc->first);
						} else {
							if(e->mSucc->first < *min) {
								min = &(e->mSucc->first);
							}
						}
					}

					mBfsQueue.push_back(e->mSucc);
					mEqualityComponent.push_back(e->mSucc);
					e->mSucc->second.mVisited = true;
				}
			}

			for(implicit_edge_info *e : cur->second.mImplicit) {
				if(!e->mSucc->second.mVisited) {
					if(minIsUVariable && e->mSucc->first.isUVariable()) {
						if(e->mSucc->first < *min) {
							min = &(e->mSucc->first);
						}
					} else {
						if(e->mSucc->first.isUVariable()) {
							min = &(e->mSucc->first);
						} else {
							if(e->mSucc->first < *min) {
								min = &(e->mSucc->first);
							}
						}
					}

					mBfsQueue.push_back(e->mSucc);
					mEqualityComponent.push_back(e->mSucc);
					e->mSucc->second.mVisited = true;
				}
			}
		}

		for(g_iterator i : mEqualityComponent) {
			i->second.mVisited = false;
		}

		mEqualityComponent.clear();
		return min;
	}

	template<typename Settings>
		std::size_t EQModule<Settings>::get_class(const term_type& term)
	{
		auto iter = mEqualityGraph.find(term);

		if(iter == mEqualityGraph.end())
			return std::numeric_limits<std::size_t>::max();

		return mComponentUnionFind.find(mUnionFind.find(iter->second.mUFIndex));
	}
}

#include "Instantiation.h"
