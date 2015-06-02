#ifndef SRC_LIB_MODULES_EQMODULE_EQMODULEEDGELIST_TPP_
#define SRC_LIB_MODULES_EQMODULE_EQMODULEEDGELIST_TPP_

#include "EQModule.h"

namespace smtrat {
	template<typename Settings> template<typename EdgeType>
		void EQModule<Settings>::graph_info::edge_list_type<EdgeType>::P_grow()
	{
		std::size_t newCap = mEdgeCap * 2 + 16;
		EdgeType **ptr = static_cast<EdgeType**>(std::realloc(mEdges, sizeof(EdgeType*) * newCap));
		if(!ptr) throw std::bad_alloc();
		mEdges = ptr;
		mEdgeCap = newCap;
	}

	template<typename Settings> template<typename EdgeType>
		void EQModule<Settings>::graph_info::edge_list_type<EdgeType>::add(EdgeType* edge)
	{
		assert(edge != nullptr);

		if(mEdgeCap == mEdgeSize) {
			P_grow();
		}

		mEdges[mEdgeSize] = edge;
		edge->mIndex = mEdgeSize++;
	}

	template<typename Settings> template<typename EdgeType>
		void EQModule<Settings>::graph_info::edge_list_type<EdgeType>::remove(EdgeType* edge)
	{
		assert(edge != nullptr);
		assert(edge->mIndex < mEdgeSize);
		assert(mEdges[edge->mIndex] == edge);

		EdgeType* replacement = mEdges[--mEdgeSize];
		mEdges[edge->mIndex] = replacement;
		replacement->mIndex = edge->mIndex;
	}

	template<typename Settings> template<typename EdgeType>
		void EQModule<Settings>::graph_info::edge_list_type<EdgeType>::remove_back()
	{
		assert(mEdgeSize != 0);
		assert(mEdges[mEdgeSize-1]->mIndex == mEdgeSize-1);
		--mEdgeSize;
	}

	template<typename Settings> template<typename EdgeType>
		void EQModule<Settings>::graph_info::edge_list_type<EdgeType>::remove_destroy(EdgeType* edge)
	{
		assert(edge != nullptr);
		assert(edge->mIndex < mEdgeSize);
		assert(mEdges[edge->mIndex] == edge);

		EdgeType* replacement = mEdges[--mEdgeSize];
		mEdges[edge->mIndex] = replacement;
		replacement->mIndex = edge->mIndex;

		edge->~EdgeType();
		mAlloc.free(edge);
	}

	template<typename Settings> template<typename EdgeType>
		EQModule<Settings>::graph_info::edge_list_type<EdgeType>::~edge_list_type()
	{
		for(EdgeType* edge : *this) {
			edge->~EdgeType();
			mAlloc.free(edge);
		}

		std::free(mEdges);
	}
}

#endif /* SRC_LIB_MODULES_EQMODULE_EQMODULEEDGELIST_TPP_ */
