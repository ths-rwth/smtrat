#ifndef DYNHEAP_H_INCLUDED_
#define DYNHEAP_H_INCLUDED_

#include <vector>
#include <type_traits>
#include <cassert>

namespace smtrat {
	namespace datastructures {
		
		template<
			typename KeyType,
			class Compare = less<KeyType>,
			typename WeightType = std::size_t
		> class DynHeap {
			
		private:
			typedef std::size_t HeapPosition;
			typedef std::map<KeyType, HeapPosition, Compare> LookupMap;
			typedef typename LookupMap::iterator LookupPosition;
			
			struct m_HeapNode {
				LookupPosition lookupNode;
				WeightType weight;
				
				m_HeapNode(LookupPosition pLookupNode = LookupPosition(), WeightType pWeight = WeightType()):
					lookupNode(pLookupNode), weight(pWeight)
				{}
				
				inline bool operator<(const m_HeapNode& rhs) {
					return weight < rhs.weight;
				}
				
				inline bool operator>(const m_HeapNode& rhs) {
					return rhs.weight < weight;
				}
			};
			
			
			LookupMap m_lookupMap;
			std::vector<m_HeapNode> m_heapitems;
			
		public:
			explicit DynHeap():
				m_lookupMap(), m_heapitems()
			{
				m_heapitems.emplace_back();
			}
			
			explicit DynHeap(const std::vector<std::pair<KeyType, WeightType>>& elements):
				m_lookupMap(), m_heapitems()
			{
				m_heapitems.emplace_back();
				for(auto it=elements.cbegin(), end_=elements.cend(); it!=end_; ++it) {
					LookupPosition newLookupNode = m_lookupMap.emplace(it->first, size()+1).first;
					m_heapitems.emplace_back(newLookupNode, it->second);
				}
				
				for(HeapPosition pos = m_heapitems.size()/2; pos > 0; --pos)
					m_percolateDown(pos);
			}
			
			
			inline bool isEmpty() const {
				return size()==0;
			}
			
			inline std::size_t size() const {
				return m_heapitems.size()-1;
			}
			
			
			
			void insert(const KeyType& pKey, const WeightType pWeight) {
				LookupPosition newLookupNode = m_lookupMap.emplace(pKey, size()+1).first;
				
				m_heapitems.emplace_back(newLookupNode, pWeight);
				m_percolateUp(size());
			}
			
			KeyType extractMin() {
				assert(!isEmpty());
				
				KeyType res = m_heapitems[1].lookupNode->first;
				
				m_lookupMap.erase(m_heapitems[1].lookupNode);
				
				m_heapitems[1] = m_heapitems[size()];
				m_heapitems.pop_back();
				if(size() != 0)
					m_percolateDown(1);
				
				return res;
			}
			
			void update(const KeyType& pKey, const WeightType pWeight) {
				LookupPosition it = m_lookupMap.find(pKey);
				assert(it != m_lookupMap.end());
				
				HeapPosition pos = it->second;
				if(pWeight < m_heapitems[pos].weight) {
					m_heapitems[pos].weight = pWeight;
					m_percolateUp(pos);
				} else if (m_heapitems[pos].weight < pWeight) {
					m_heapitems[pos].weight = pWeight;
					m_percolateDown(pos);
				}
			}
			
			inline void clear() {
				m_lookupMap.clear();
				m_heapitems.clear();
				m_heapitems.emplace_back();
			}
			
		private:
			inline void m_updateLookupNode(HeapPosition pos) {
				m_heapitems[pos].lookupNode->second = pos;
			}
			
			inline void m_percolateDown(HeapPosition pos) {
				std::size_t size = this->size();
				HeapPosition child;
				m_HeapNode tmp = m_heapitems[pos];
				
				for(; pos*2 <= size; pos=child) {
					child = pos*2;
					if(child != size && m_heapitems[child+1] < m_heapitems[child])
						++child;
					if(m_heapitems[child] < tmp) {
						m_heapitems[pos] = m_heapitems[child];
						m_updateLookupNode(pos);
					} else
						break;
				}
				
				m_heapitems[pos] = tmp;
				m_updateLookupNode(pos);
			}
			
			inline void m_percolateUp(HeapPosition pos) {
				m_HeapNode tmp = m_heapitems[pos];
				
				for(; tmp < m_heapitems[pos/2]; pos/=2) {
					m_heapitems[pos] = m_heapitems[pos/2];
					m_updateLookupNode(pos);
				}
				
				m_heapitems[pos] = tmp;
				m_updateLookupNode(pos);
			}
		};
		
	};
}

#endif // DYNHEAP_H_INCLUDED_
