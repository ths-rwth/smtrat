/**
 * @file EQModule.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2014-10-19
 * Created on 2014-10-19.
 */

#pragma once

#include "../../Common.h"
#include "../../solver/Module.h"
#include "EQStatistics.h"
#include "EQSettings.h"
#include "VariantHash.h"
#include "PairHash.h"
#include "IterHash.h"
#include "pmatrix.hpp"
#include "LinkedList.hpp"

#include <unordered_map>
#include <algorithm>
#include <limits>
#include <cstdlib>
#include <cassert>
#include <tuple>
#include <type_traits>
#include <vector>

#include <boost/variant.hpp>
#include <boost/circular_buffer.hpp>
#include <boost/operators.hpp>
#include "../../datastructures/eq/alloc.h"
#include "../../datastructures/eq/union_find.h"

namespace smtrat
{
	template<typename Settings>
		class EQModule : public Module
	{
		// ----------------------- HELPER TYPES -----------------------
		private:
			typedef carl::UTerm term_type;
			typedef carl::UEquality UEquality;
			typedef carl::UVariable UVariable;
			typedef carl::UninterpretedFunction UninterpretedFunction;
			typedef carl::UFInstance UFInstance;
			typedef carl::Sort Sort;

			struct edge_info;
			struct implicit_edge_info;
			struct ineq_edge_info;
			struct args_info;

			/**
			 * We store a graph_info element for every term (function instance or variable)
			 * that we encounter. Every graph_info element contains an index into the union-find datastructures,
			 * a list of explicit, implicit and inequality edges.
			 */
			class graph_info {
				public:
					graph_info(EQModule& module) noexcept :
						mExplicit(module.mExplicitEdgeAlloc),
						mImplicit(module.mImplicitEdgeAlloc),
						mIneq(module.mIneqEdgeAlloc),
						mUFIndex(std::numeric_limits<std::size_t>::max()),
						mArgs(nullptr),
						mPred(0), mImplicitPred(0),
						mWeight(0), mVisited(false), mWeightFixed(false)
					{}

					inline ~graph_info();

					/**
					 * Find the edge corresponding to the given formula.
					 */
					inline edge_info* find_edge(const FormulaT& f);

					/**
					 * Implements a list of edges.
					 * This is similar to a vector of edge-pointers, but
					 * allocates pointers from a freelist and supports O(1) removal
					 * by storing the index of an edge in this list inside the edge.
					 */
					template<typename EdgeType> struct edge_list_type {
						public:
							edge_list_type(freelist<EdgeType> &alloc) noexcept :
								mAlloc(alloc),
								mEdges(nullptr),
								mEdgeSize(0), mEdgeCap(0)
							{}

							~edge_list_type();

							typedef EdgeType** iterator;
							typedef const EdgeType* const* const_iterator;

							// obtain pointers to the beginning/end of the edges list
							iterator begin() noexcept { return mEdges; }
							iterator end() noexcept { return mEdges + mEdgeSize; }
							const_iterator begin() const noexcept { return mEdges; }
							const_iterator end() const noexcept { return mEdges + mEdgeSize; }

							EdgeType* &operator[](std::size_t i) noexcept {
								assert(i < mEdgeSize);
								return mEdges[i];
							}

							const EdgeType* operator[](std::size_t i) const noexcept {
								assert(i < mEdgeSize);
								return mEdges[i];
							}

							std::size_t size() const noexcept { return mEdgeSize; }

							// add edge O(1)
							inline void add(EdgeType* edge);
							// remove edge O(1), does not destroy/free
							inline void remove(EdgeType* edge);
							// remove last edge, faster O(1), does not destroy/free
							inline void remove_back();
							// remove and destroy pointed-to edge, O(1)
							inline void remove_destroy(EdgeType* edge);

						private:
							void P_grow();

							friend class graph_info;
							freelist<EdgeType> &mAlloc;
							iterator mEdges;
							std::size_t mEdgeSize, mEdgeCap;
					};

					edge_list_type<edge_info> mExplicit; ///< The list of explicit edges.
					edge_list_type<implicit_edge_info> mImplicit; ///< The list of implicit edges.
					edge_list_type<ineq_edge_info> mIneq; ///< The list of ineq edges.

					std::size_t mUFIndex; ///< The index of this graph_info in the union-find and component-union-find datastructures.

					args_info *mArgs; ///< Pointer to an args_info datastructure containing arity and arguments. Null if this is not a function instance.

					// additional infos for bfs or weighted bfs
					edge_info *mPred;  ///< predecessor for explicit bfs
					implicit_edge_info *mImplicitPred; ///< predecessor for implicit edge
					double mWeight;    ///< Weight of path from start to this node; this has to be maximized
					bool mVisited;     ///< Whether this node was already visited
					bool mWeightFixed; ///< As soon as the node is popped from queue, the weight will stay fixed

				private:
					graph_info(const graph_info&) = delete;
					graph_info &operator=(const graph_info&) = delete;
					graph_info(graph_info&&) = delete;
					graph_info &operator=(graph_info&&) = delete;
			};

			typedef std::unordered_map<term_type, graph_info> map_type;
			typedef typename map_type::iterator g_iterator;

			// information common to all edge types
			template<typename DerivedEdgeType> struct common_edge_info
			{
				common_edge_info(const common_edge_info&) = delete;
				common_edge_info &operator=(const common_edge_info&) = delete;

				common_edge_info(common_edge_info&&) = delete;
				common_edge_info &operator=(common_edge_info&&) = delete;

				common_edge_info(g_iterator pred, g_iterator succ) :
					mIndex(0),
					mOther(nullptr),
					mPred(pred),
					mSucc(succ)
				{}

				std::size_t mIndex;      // the index of this edge in the edge array
				DerivedEdgeType *mOther; // the edge in the other direction
				g_iterator mPred;        // the source of this edge
				g_iterator mSucc;        // the target of this edge
			};

			// an explicit edge
			struct edge_info : public common_edge_info<edge_info> {
				edge_info(g_iterator pred, g_iterator succ, const FormulaT& formula) :
					common_edge_info<edge_info>(pred, succ),
					mFormula(formula)
				{}

				FormulaT mFormula;  // the equality
			};
			
			// an inequality edge
			struct ineq_edge_info : public common_edge_info<ineq_edge_info> {
				ineq_edge_info(g_iterator pred, g_iterator succ, g_iterator real_pred, g_iterator real_succ, const FormulaT& formula) :
					common_edge_info<ineq_edge_info>(pred, succ),
					mRealPred(real_pred),
					mRealSucc(real_succ),
					mFormula(formula)
				{}

				g_iterator mRealPred;   // the real predecessor of this inequality edge
				g_iterator mRealSucc;   // the real successor of this inequality edge
				FormulaT mFormula;  // the inequality
			};

			typedef typename std::vector<g_iterator> component_vector_type;
			
			typedef std::pair<UVariable, g_iterator> variable_type;
			typedef std::pair<g_iterator, g_iterator> bfs_todo_entry;	// we have to find a path between these two nodes

			/**
			 * A set of buckets containing function instances.
			 * Each bucket contains all instances of a function that are currently equivalent
			 * due to having the same argument equivalence classes on the component union find level.
			 * This invariant can temporarily be violated during a remove operation (there, P_post_split_update_classes is used to restore it).
			 * Every bucket contains a list of implicit edges (=equalities) that are supported by it.
			 * Moreover, for each equivalence class, there is a list of buckets that contain it as argument class.
			 */
			class hash_bucket_set {
				private:
					friend class EQModule<Settings>;

					/**
					 * The initial size of the hash bucket set's underlying hash table is 1 << InitialCapacityShift (= 2**InitialCapacityShift).
					 */
					static constexpr std::size_t InitialCapacityShift = Settings::hash_bucket_set_initial_capacity_shift;

					/**
					 * The LoadFactor of the underlying hash table.
					 * Note that we do NOT shrink the hash table; we only increase it.
					 */
					using LoadFactor = typename Settings::hash_bucket_set_load_factor;

					/**
					 * An entry in a bucket.
					 * Each entry represents
					 * a distinct function instance
					 * (identified by a g_iterator into
					 * our map of terms).
					 */
					struct entry {
						entry* prev; ///< The previous entry (on the list of entries in a bucket)
						entry* next; ///< The next entry (on the list of entries in a bucket)
						g_iterator value; ///< The function instance corresponding to this entry.
					};

					/**
					 * An entry in our list of classes;
					 * it consists of the class value
					 * (index into component union find datastructure; during split operation, might also be usual union find)
					 * and the index at which the bucket that this
					 * entry corresponds to is contained in the
					 * vector of buckets that contain this class as argument.
					 * This value is used to implement O(1) removal
					 * of buckets from these lists.
					 */
					struct class_vector_entry {
						std::size_t mClass; ///< The equivalence class index (usually in the component union find, sometimes, during remove, only in the union find)
						std::size_t mBucketListIndex; ///< The index of the bucket in the bucket list of class mClass. This is only set for the first occurrence of the class in an entry.
					};

					/**
					 * A bucket in this bucket set contains
					 * a set of entries. Each entry corresponds
					 * to a distinct function instance.
					 * A bucket always contains all function instances
					 * that are currently considered equal due to
					 * congruence constraints (some function instances
					 * may be considered equal for other reasons,
					 * but may still be in different buckets).
					 */
					struct bucket : public circular_node_base<bucket> {
						bucket() :
							hashValue(0),
							nextSplit(nullptr),
							prevNeedsUpdate(nullptr),
							nextNeedsUpdate(nullptr),
							changedPrev(nullptr),
							changedNext(nullptr),
							splitAge(0)
						{}

						std::size_t hashValue; ///< the hash value (not reduced mod hash table size) of this bucket
						linked_list<entry, &entry::prev, &entry::next> mEntries; ///< the entries (function instances) in this bucket
						bucket *nextSplit; ///< required during split operations. undefined outside of split operations.
						bucket *prevNeedsUpdate, *nextNeedsUpdate; ///< the previous and next bucket in the list of buckets that need to be updated. used after bucket split operations
						bucket *changedPrev, *changedNext; ///< the previous and next bucket in the list of ALL nontrivial buckets that have been changed
						dynarray<implicit_edge_info*> supportedEdges; ///< the implicit edges supported by this bucket
						std::size_t splitAge; ///< a value identifying the last split operation during which this bucket was touched; used to avoid splitting the same bucket needlessly often
						class_vector_entry classes[1];  ///< the argument class indices; real length: mArity (the data in this array is allocated behind this object to avoid a level of redirection)
					};

					static_assert(std::is_trivially_destructible<entry>::value, "The entry type must be trivially destructible!");

					/**
					 * The hash bucket set consists of a hash table.
					 * Each hash table slot contains a bin;
					 * a bin is basically a linked list of buckets that share the same
					 * reduced (mod hash table size) hash value
					 * (bins are used to handle hash collisions).
					 */
					typedef circular_linked_list<bucket, circular_node_base<bucket>> bin;

				private:
					/**
					 * Doubles the size of the underlying hash table and moves buckets accordingly.
					 * This does not need to recompute the hashes.
					 */
					inline void P_resize();

					/* use tag dispatch to call the right overload; enables hash function selection at compile-time */
					// the functions below are implementations of different hash functions
					inline std::size_t P_compute_hash(const class_vector_entry* classes) const;
					inline void P_update_hash_step(std::size_t& hvalue, std::size_t c, std::size_t index);
					inline std::size_t P_reduce_hash(std::size_t hvalue) const;
					void P_redistribute_buckets(bin* newBins);

					/**
					 * Update a bucket by replacing every occurrence of oldClass by newClass.
					 * This shall only be called when there is at least one such occurrence.
					 * This also updates the bucket lists that track in which buckets a certain class occurs as argument.
					 */
					void P_update_bucket(bucket *b, std::size_t oldClass, std::size_t newClass);

					/**
					 * Allocates an initializes a bucket containing a single entry.
					 */
					inline bucket* P_construct_bucket(const class_vector_entry* classes, std::size_t hashValue, entry* e);

					/**
					 * Merges the bucket source into the bucket target, leaving source empty.
					 * This operation is used when the two buckets become
					 * equivalent due to having the same argument classes.
					 */
					inline void P_merge_buckets(bucket* target, bucket* source);

					/**
					 * Find a bucket with a certain set of classes in a bin, or return a nullptr.
					 * The hash value, not reduced by P_reduce_hash, shall already been computed prior to this call.
					 */
					inline bucket* P_find_bucket(bin& b, const class_vector_entry* classes, std::size_t hvalue);

					/**
					 * Inserts a bucket into the given bin.
					 */
					inline void P_insert_bucket(bin& bin_, bucket* bucket_);

					/**
					 * Removes a bucket from the given bin.
					 */
					inline void P_remove_bucket(bin& bin_, bucket* bucket_);

					/**
					 * Removes a bucket from the list of buckets containing the argument class bucket_->mClasses[argIndex].
					 */
					inline void P_remove_from_bucket_list(bucket* bucket_, std::size_t argIndex);

					/**
					 * Erase a bucket that has already been removed from its bin from all other data structures.
					 */
					inline void P_erase_bucket(bucket* bucket_, std::size_t ignoreClass);

					/**
					 * Erase a bucket from its bin and all other data structures;
					 * do not remove its entries or free it.
					 */
					inline void P_detach_bucket(bin& bin_, bucket* bucket_);

					/**
					 * As P_detach_bucket; ignores classes that did not take part in the current split operation.
					 */
					inline void P_detach_bucket_from_split(bin& bin_, bucket* bucket_);

					/**
					 * Add a bucket to the list of buckets that need to be updated after a split operation;
					 * this is necessary because the indices of such classes may be taken from the usual union find
					 * instead of the component union find.
					 */
					inline void P_add_split(bucket*& firstSplit, bucket*& lastSplit, bucket* b);

					/**
					 * Perform a bucket insertion operation during a bucket split.
					 * This is roughly equivalent to insert_function_instance, but also adds the resulting
					 * bucket to the list of split outcomes starting with firstSplit.
					 * This method also uses the union find datastructure instead of the component union find datastructure.
					 */
					bucket* P_insert_during_split(bucket*& firstSplit, bucket*& lastSplit, entry* e);

					/**
					 * Iterates through the update list and update all classes, replacing any index that is not a representative
					 * on the component union find level by its component union find-level representative.
					 * This method is called once after all split operations are completed in order to reinstate the invariants of the hash bucket set datastructure.
					 */
					void P_post_split_update_classes();

					/**
					 * Insert a bucket into the list of buckets containing the argument class class_;
					 * firstIndex must be the argument index of the first argument of this bucket that lies in class_.
					 */
					inline std::size_t P_insert_into_bucket_list(std::size_t class_, bucket* bucket_, std::size_t firstIndex);

					/**
					 * Inserts a bucket into the bucket lists of all classes that it contains.
					 */
					void P_insert_into_bucket_lists(bucket* b);

					/**
					 * Print this bucket datastructure to std::cout.
					 * Add all buckets that are found during this process to the given set.
					 */
					void P_print_buckets(std::unordered_set<bucket*>& foundBuckets);

				private:
					EQModule& mModule; ///< Reference to the module we are working with.
					const std::size_t mArity; ///< Arity of the function corresponding to this bucket set.
					std::size_t mBinShift;    ///< The number of bins in the underlying hash table is (1<<mBinShift).
					std::size_t mBucketCount; ///< Number of buckets currently in this bucket set.
					linked_list<bucket, &bucket::changedPrev, &bucket::changedNext> mChanged; ///< The list of changed buckets (processed by P_process_merge_lists).
					linked_list<bucket, &bucket::prevNeedsUpdate, &bucket::nextNeedsUpdate> mNeedUpdate; ///< The list of buckets that need updating after a split operation (processed by P_post_split_update_classes).
					bin* mBinPtr; ///< The underlying hash table; a pointer to an array of (1 << mBinShift) bins
					freelist<bucket> mBucketAlloc; ///< The allocator for buckets
					freelist<entry> mEntryAlloc;   ///< The allocator for entries
					class_vector_entry *mTmpClasses; ///< A pointer to an array of mArity class values.

				public:
					/**
					 * Construct a new bucket set for the given module and uninterpreted function.
					 */
					hash_bucket_set(EQModule& module, UninterpretedFunction fn);

					/**
					 * Destroy a bucket set, freeing all buckets/entries/bins.
					 */
					~hash_bucket_set();

					/**
					 * Insert a new function instance into the bucket set.
					 * The method returns a pointer to the bucket that this instance landed in.
					 * If this bucket previously existed, it is added to the change list (mChanged).
					 */
					bucket* insert_function_instance(g_iterator term_iter);

					/**
					 * Merge the class identified by oldClass into the class newClass with respect to the given bucket.
					 * May only be called if oldClass occurs in the given bucket.
					 * This may delete the given bucket; it returns the bucket produced by the merge operation.
					 * If this merges two buckets into one, the result is added to the change list (mChanged).
					 */
					bucket* merge_class_into(bucket* b, std::size_t oldClass, std::size_t newClass);

					/**
					 * Remove the given bucket from all bucket lists it is contained in.
					 */
					inline void remove_from_bucket_lists(bucket* bucket_);

					/**
					 * Split the given bucket according to the classes in the component union find.
					 * Basically, this works as if by reinserting every entry from this bucket into the bucket set.
					 * This may destroy the bucket if it is nontrivial.
					 */
					inline void split_bucket(bucket* b);

					/**
					 * Lookup the bucket containing a function instance,
					 * using the hash function and the component union find datastructure.
					 */
					inline bucket* find(g_iterator finstance);
			};

			typedef hash_bucket_set hash_buckets_type;
			typedef typename hash_buckets_type::bucket hash_bucket_type;
			typedef typename hash_buckets_type::entry hash_bucket_entry;

			// information about the argument terms of a function instance
			struct args_info {
				hash_buckets_type *mBuckets;
				std::size_t mArity;
				g_iterator mArgs[1]; // true length: mArity
			};

			// these are not members of graph_info because of the g_iterator return type
			inline std::size_t arityof(g_iterator finstance);
			inline const g_iterator *argsof(g_iterator finstance);
			inline hash_buckets_type *bucketsof(g_iterator finstance);

			// an implicit edge
			struct implicit_edge_info : public common_edge_info<implicit_edge_info> {
				implicit_edge_info(g_iterator pred, g_iterator succ, g_iterator real_pred, g_iterator real_succ) :
					common_edge_info<implicit_edge_info>(pred, succ),
					mRealPred(real_pred),
					mRealSucc(real_succ),
					mSupportingBucket(nullptr),
					mIsProven(false),
					mID(mIDCounter++)
				{}

				g_iterator mRealPred; // the real predecessor of this implicit edge
				g_iterator mRealSucc; // the real successor of this implicit edge, i.e. the function instance instead of the components representative
				hash_bucket_type *mSupportingBucket; // the hash bucket supporting this edge. Note that this will be null for half the edges
				bool mIsProven;       // is the implicit edge already shown for infeasible subset
				std::size_t mID; // identifier to determine age of implicit edges
				static std::atomic<std::size_t> mIDCounter;
			};

			struct bucket_list_entry {
				bucket_list_entry(hash_buckets_type* bucketSet, hash_bucket_type* bucket, std::size_t firstIndex) :
					mBucketSet(bucketSet),
					mBucket(bucket),
					mFirstIndex(firstIndex)
				{}

				hash_buckets_type* mBucketSet;
				hash_bucket_type* mBucket;
				std::size_t mFirstIndex;
			};

			struct uf_component_entry {
				uf_component_entry() :
					mLastSeenInSplit(0),
					mBuckets(),
					mIsSplit(false)
				{}

				std::size_t mLastSeenInSplit;
				std::vector<bucket_list_entry> mBuckets;
				bool mIsSplit;
			};

			struct function_map_entry {
				function_map_entry(EQModule& module, UninterpretedFunction fn) :
					mInstances(),
					mHashBuckets(module, fn)
				{}

				std::unordered_set< g_iterator, by_address_hasher<g_iterator> > mInstances;
				hash_buckets_type mHashBuckets;
			};

			typedef typename std::unordered_map< UninterpretedFunction, function_map_entry > function_map_type;

			struct variable_pair_entry {
				variable_pair_entry() :
					mPairSetAge(0),
					mImplicitEventCount(0)
				{}

				std::size_t mPairSetAge; // using these variables, a O(1) pair set (much like a bit set) can be implemented
				std::size_t mImplicitEventCount;
			};

			struct not_asserted_equality : private boost::equality_comparable<not_asserted_equality> {
				explicit not_asserted_equality(FormulaT formula) noexcept :
					mFormula(formula)
				{}

				not_asserted_equality(FormulaT formula, g_iterator lhs, g_iterator rhs) noexcept :
					mFormula(formula),
					mLhs(lhs),
					mRhs(rhs)
				{}

				bool operator==(const not_asserted_equality& nae) const noexcept { return mFormula == nae.mFormula; }

				FormulaT   mFormula;
				g_iterator mLhs, mRhs;

				struct hash {
					std::size_t operator()(const not_asserted_equality& nae) const noexcept {
						return std::hash<FormulaT>{}(nae.mFormula);
					}
				};
			};

		// ----------------------- MEMBERS -----------------------
		private:
			freelist<edge_info> mExplicitEdgeAlloc; // allocator for explicit edges
			freelist<implicit_edge_info> mImplicitEdgeAlloc; // allocator for implicit edges
			freelist<ineq_edge_info> mIneqEdgeAlloc; // allocator for inequality edges

			union_find<g_iterator, !Settings::uf_use_compression, Settings::uf_max_traceback_length> mUnionFind; // union find for explicit equalities
			union_find<uf_component_entry, !Settings::uf_use_compression, Settings::uf_max_traceback_length> mComponentUnionFind; // union find for implicit equalities; it is defined only on the class values of the other union find
			std::size_t mLocalSplitAge;
			std::size_t mGlobalSplitAge;
			map_type mEqualityGraph;
			component_vector_type mEqualityComponent; // list of all vertices visited in the last bfs search
			std::unordered_map<std::size_t, carl::SortValue> mClassToSortValue; // mapping from union find indices to sort values
			function_map_type mFunctionMap; // maps uninterpreted functions to the list of their instances and hash buckets
			std::vector<variable_type> mVariables; // list of all variables; used in updateModel to assign a sort to value to each variable
			boost::circular_buffer<g_iterator> mBfsQueue; // queue for breath first search in equality graph
			boost::circular_buffer<bfs_todo_entry> mImplicitEdgeQueue; // list of pairs of variables for which we still have to prove equality in generation of infeasible subsets
			std::vector<implicit_edge_info*> mImplicitEdgeIsProvenList; // list of implicit equalities that are already proven during generation of infeasible subset
			std::size_t mCountNonUEQFormulas; // number of incorrect formulas currently asserted
#ifdef SMTRAT_DEVOPTION_Statistics
			EQStatistics<Settings>* mStatistics;
#endif
			std::vector<std::size_t> mSplitClasses; // indices of implicit classes that were split; we have to update the hash buckets for these indices
			std::vector<bfs_todo_entry> mDeletedEdges; // list of implicit edges that have to be deleted in graph
			std::vector<ineq_edge_info*> mPossibleInconsistencies; // list of inequalities that potentially can cause inconsistencies

			std::unordered_map<
				std::pair<std::size_t, std::size_t>,
				dynarray<ineq_edge_info*>,
				pairhash<std::size_t, std::size_t>,
				std::equal_to<std::pair<std::size_t,std::size_t>>
//                    ,
//				fixedsize_allocator<std::pair<std::size_t, std::size_t>>
			> mIneqMatrix; ///< Implements a sparse matrix to check if inequality has to hold between two components

			pmatrix<variable_pair_entry> mPairMatrix; // sparse matrix to count occurrences of implicit edges for deductions
			std::size_t mGlobalPairSetAge; ///< used for the implicit edge deductions
			std::unordered_map<FormulaT, FormulaT> mEqualityNormalization; // maps all formulas to a normalized version if it occurs positive and negative (used for deductions);

			std::unordered_set<
				not_asserted_equality,
				typename not_asserted_equality::hash,
				std::equal_to<not_asserted_equality>,
				fixedsize_allocator<not_asserted_equality>
			> mAllNotAssertedEqualities; // list of all equalities obtained in inform that are currently not asserted; these formulas are used to generate deductions

			std::size_t mCheckForDeductionCounter;

		// ----------------------- PRIVATE HELPER METHODS -----------------------
		private:
			// insert a UEQ into the mEqualityNormalization and mAllNotAssertedEqualities datastructures
			inline void P_add_not_asserted_normalized(FormulaT formula, const UEquality& ueq);

			// check and update queue capacities to ensure they are big enough
			inline void P_check_queue_caps();
			
			// add an edge explicitly asserted by the sat module
			inline void P_add_explicit_edge(g_iterator lhs, g_iterator rhs, const FormulaT& formula);
			
			// removes and destroys an implicit edge
			inline void P_destroy_implicit_edge(implicit_edge_info* edge);
			
			/**
			 * adds an implicit edge
             * @param lhs the edge starts at lhs (representative of real_lhs)
             * @param rhs the edge ends in rhs (representative of real_rhs)
             * @param real_lhs the real start
             * @param real_rhs the real end
             * @return a pointer to the added implicit edge
             */
			implicit_edge_info* P_add_implicit_edge(g_iterator lhs, g_iterator rhs, g_iterator real_lhs, g_iterator real_rhs);
			
			// removes and destroys an explicit edge
			inline void P_remove_edge(g_iterator lhs, g_iterator rhs, const FormulaT& formula);
			
			/**
			 * add an inequality edge
             * @param indexLhs component union find index of the start of the edge
             * @param indexRhs component union find index of the end of the edge
             * @param real_lhs the real start
             * @param real_rhs the real end
             * @param formula the actual inequality
             */
			inline void P_add_ineq_edge(std::size_t indexLhs, std::size_t indexRhs, g_iterator real_lhs, g_iterator real_rhs, const FormulaT& formula);
			
			// removes an inequality edge
			inline void P_remove_ineq_edge(g_iterator lhs, g_iterator rhs, const FormulaT& formula);

			// performs bfs search to find shortest path from start to target, which is saved in graph info
			// uses only implicit edges for the bfs search
			bool P_bfs_search_implicit(g_iterator start, g_iterator target);
			
			// uses only explicit edges for the bfs search
			bool P_bfs_search_explicit(g_iterator start, g_iterator target);
			
			// performs weighted bfs search to find shortest path with maximal weight from start to target, which is saved in graph info
			bool P_bfs_search_weighted_explicit(g_iterator start, g_iterator target);
			
			// clear visited flags and mEqualityComponent
			void P_clear_bfs_markings();
			
			// add the path from start to target to infeasible subset
			void P_add_explicit_path_to_infeasible(g_iterator start, g_iterator target, FormulaSetT& infeasible);
			
			// add the negated equalities on the path from start to target to infeasible subset
			void P_add_explicit_path_to_infeasible_neg(g_iterator start, g_iterator target, FormulaSetT& infeasible);
			
			// construction of infeasible subset 
			void P_construct_infeasible_subset(g_iterator start, g_iterator target, const FormulaT& inequality);
			
			// add a variable
			void P_add_variable(const UVariable& var, g_iterator term_iter);

			// add a function instance
			void P_add_function_instance(const UFInstance& instance, g_iterator term_iter);

			// as update_model is incorrectly const, use this helper
			void P_update_model();
			
			// update model for variables
			inline void P_update_model_variable();
			
			// update model for function instances
			inline void P_update_model_function();
			
			// check whether previous inconsistencies are still inconsistent
			inline void P_check_inconsistencies();
			
			// check for possible inconsistencies
			bool P_cc_union_for_ineq(std::size_t indexCOld, std::size_t indexCNew);
			
			// remove all incident inequality edges from node in the graph and push them into the possible inconsistencies
			inline void P_remove_ineq_edges_of_vertex(g_iterator node);

			void P_post_split_update_classes();
			void P_merge_buckets(std::size_t oldClass, std::size_t newClass);
			void P_process_split_list();
			void P_split_buckets();
			
			// constructs a proof for the equality
			void P_construct_proof(FormulaSetT& output, g_iterator start, g_iterator target);
			
			// constructs a proof for the equality using negated formulas
			void P_construct_proof_neg(FormulaSetT& output, g_iterator start, g_iterator target);
			
			// forget which implicit edges we had proven
			void P_clear_proven();
			
			// add deductions for unassigned literals
			inline void P_check_for_unassigned_literals();
			// adds a deduction on the pair of function instances given
			void P_add_implicit_edge_deduction(g_iterator i, g_iterator j);

			// prints the current graph in a dot format
			void P_print_graph();
			
			// prints a single edge together with its start and end node
			template<typename EdgeType> void P_print_edge(std::ostream& out, EdgeType* edge, FormulaSetT& infeasible, std::unordered_set< g_iterator, by_address_hasher<g_iterator> >& inserted_nodes);

			// print infeasible subset into an smt2 file
			void P_print_infeasible_subset();

			// print information about all hash bucket sets to std::cout
			void P_print_bucket_sets();

			// check whether model extension satisfies functional consistency (called in debug-version only)
			bool P_check_model_extension(carl::UFModel& model, g_iterator term, const std::vector<carl::SortValue>& args, const carl::SortValue& result) const;

		public:
			typedef Settings SettingsType;
std::string moduleName() const {
return SettingsType::moduleName;
}
			EQModule( const ModuleInput* _formula, RuntimeSettings* _settings, Conditionals& _conditionals, Manager* _manager = NULL );

			~EQModule();

			// Main interfaces.

			/**
			 * Informs the module about the given constraint. It should be tried to inform this
			 * module about any constraint it could receive eventually before assertSubformula
			 * is called (preferably for the first time, but at least before adding a formula
			 * containing that constraint).
			 * @param _constraint The constraint to inform about.
			 * @return false, if it can be easily decided whether the given constraint is inconsistent;
			 *		  true, otherwise.
			 */
			bool informCore(const FormulaT& _constraint);

			/**
			 * Informs all backends about the so far encountered constraints, which have not yet been communicated.
			 * This method must not and will not be called more than once and only before the first runBackends call.
			 */
			void init();

			/**
			 * The module has to take the given sub-formula of the received formula into account.
			 *
			 * @param _subformula The sub-formula to take additionally into account.
			 * @return false, if it can be easily decided that this sub-formula causes a conflict with
			 *		  the already considered sub-formulas;
			 *		  true, otherwise.
			 */
			bool addCore(ModuleInput::const_iterator _subformula);

			/**
			 * Removes the subformula of the received formula at the given position to the considered ones of this module.
			 * Note that this includes every stored calculation which depended on this subformula, but should keep the other
			 * stored calculation, if possible, untouched.
			 *
			 * @param _subformula The position of the subformula to remove.
			 */
			void removeCore(ModuleInput::const_iterator _subformula);

			/**
			 * Updates the current assignment into the model.
			 * Note, that this is a unique but possibly symbolic assignment maybe containing newly introduced variables.
			 */
			void updateModel() const;

			/**
			 * Checks the received formula for consistency.
			 * @return SAT,	if the received formula is satisfiable;
			 *		 UNSAT,   if the received formula is not satisfiable;
			 *		 Unknown, otherwise.
			 */
			Answer checkCore();

		public:
			/// parts of the public interface that are not part of the general module interface
			void process_merge_lists();

			/// find a "canonical" representative for some term
			const term_type *find_representative(const term_type& term);

			/// returns the component-component-level class of some term
			std::size_t get_class(const term_type& term);
	};
}

template<typename Settings>
std::atomic<std::size_t> smtrat::EQModule<Settings>::implicit_edge_info::mIDCounter(0);

#include "EQModulePrinting.tpp"
#include "EQModuleHash.tpp"
#include "EQModuleEdgeList.tpp"
