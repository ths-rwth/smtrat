#ifndef BINARYHEAP_H_INCLUDED_
#define BINARYHEAP_H_INCLUDED_

#include <vector>
#include <type_traits>
#include <cassert>

namespace smtrat {
	namespace datastructures {
		
		template<typename T> class BinaryHeap {
		public:
			explicit BinaryHeap(std::size_t initialSize = 100):
				m_elements(initialSize), m_size(0)
			{}
			
			explicit BinaryHeap(const std::vector<T>& elements):
				m_elements(elements.size() + 20), m_size(elements.size())
			{
				for(std::size_t i = 0; i < m_size; ++i)
					m_elements[i+1] = elements[i];
				m_buildHeap();
			}
			
			
			inline bool is_empty() const {
				return m_size==0;
			}
			
			inline std::size_t size() const {
				return m_size;
			}
			
			void insert(const T& item) {
				if(m_size == m_elements.size()-1)
					m_elements.resize(m_elements.size() *2);
				
				m_elements[++m_size] = item;
				m_percolateUp(m_size);
			}
			
			T extractMin() {
				assert(!is_empty());
				
				T res = m_elements[1];
				m_elements[1] = m_elements[m_size--];
				m_percolateDown(1);
				
				return res;
			}
			
			inline void clear() {
				m_size = 0;
			}
			
		private:
			std::size_t m_size;
			std::vector<T> m_elements;
			
			inline void m_buildHeap() {
				for(std::size_t i = m_size/2; i > 0; --i)
					m_percolateDown(i);
			}
			
			inline void m_percolateDown(std::size_t pos) {
				std:size_t child;
				T tmp = m_elements[pos];
				
				for(; pos*2 <= m_size; pos=child) {
					child = pos*2;
					if(child != m_size && m_elements[child+1] < m_elements[child])
						++child;
					if(m_elements[child] < tmp)
						m_elements[pos] = m_elements[child];
					else
						break;
				}
				
				m_elements[pos] = tmp;
			}
			
			inline void m_percolateUp(std::size_t pos) {
				T tmp = m_elements[pos];
				
				for(; pos > 1 && tmp < m_elements[pos/2]; pos/=2)
					m_elements[pos] = m_elements[pos/2];
				
				m_elements[pos] = tmp;
			}
		};
		
	};
}

#endif // BINARYHEAP_H_INCLUDED_

