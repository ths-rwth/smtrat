#ifndef SRC_LIB_MODULES_EQMODULE_LINKEDLIST_HPP_
#define SRC_LIB_MODULES_EQMODULE_LINKEDLIST_HPP_

#include <utility>
#include <type_traits>
#include <boost/iterator/iterator_facade.hpp>

namespace smtrat {
	/**
	 * An intrusive linked list pseudo-container that does not take ownership of its contents.
	 *
	 * Note: this somewhat resembles a standard container, however it is NOT a standard-compliant container (misses size(),
	 * does not really contain nodes, rather points to them).
	 * However, the for(... : ...) syntax works and the iterators are standard-compliant.
	 */
	template<typename NodeType, NodeType* NodeType::*PrevPtr, NodeType* NodeType::*NextPtr> class linked_list {
		public:
			typedef NodeType value_type;
			typedef NodeType &reference;
			typedef typename std::add_const<NodeType>::type &const_reference;
			typedef NodeType *pointer;
			typedef std::ptrdiff_t difference_type;
			typedef std::size_t size_type;

		private:
			template<typename RealNodeType> class node_iterator :
				public boost::iterator_facade<
					node_iterator<RealNodeType>,
					RealNodeType,
					boost::forward_traversal_tag
				>
			{
				private:
					friend class linked_list;
					friend class boost::iterator_core_access;
					struct enabler {};

				public:
					node_iterator() noexcept : mPtr(nullptr) {}

					template<typename OtherRealNodeType>
						node_iterator(
							const node_iterator<OtherRealNodeType>& other,
							std::enable_if<std::is_convertible<OtherRealNodeType*, RealNodeType*>::value, enabler> = enabler{}
						) noexcept : mPtr(other.mPtr)
					{}

				private:
					explicit node_iterator(RealNodeType* ptr) noexcept :
						mPtr(ptr)
					{}

					template<typename OtherRealNodeType>
						bool equal(const node_iterator<OtherRealNodeType>& other) const noexcept
					{
						return mPtr == other.mPtr;
					}

					void increment() noexcept {
						assert(mPtr);

						mPtr = mPtr->*NextPtr;
					}

					RealNodeType &dereference() const noexcept {
						assert(mPtr);

						return *mPtr;
					}

					RealNodeType* mPtr;
			};

		public:
			typedef node_iterator<NodeType> iterator;
			typedef node_iterator<const NodeType> const_iterator;

			linked_list() : first(nullptr), last(nullptr) {}

			void assign(pointer element) {
				assert(first == nullptr);
				assert(last == nullptr);

				first = last = element;
			}

			iterator begin() noexcept { return iterator(first); }
			iterator end() noexcept { return iterator{}; }

			const_iterator begin() const noexcept { return const_iterator(first); }
			const_iterator end() const noexcept { return const_iterator{}; }
			const_iterator cbegin() const noexcept { return const_iterator(first); }
			const_iterator cend() const noexcept { return const_iterator{}; }

			bool empty() const noexcept { return first == nullptr; }

			/**
			 * Returns true if this linked list is either empty or contains
			 * only a single element.
			 */
			bool trivial() const noexcept { return first == last; }

			/**
			 * Add the pointed-to node to the front of the list.
			 * Does NOT check whether this node is already on the list.
			 */
			void push_front(pointer ptr) {
				if(first) {
					first->*PrevPtr = ptr;
				} else {
					last = ptr;
				}

				ptr->*NextPtr = first;
				first = ptr;
			}

			/**
			 * Adds the pointed-to node to the front of the list,
			 * but only if it is not already on this linked_list.
			 */
			void add_front(pointer ptr) {
				// check that we are neither the first element of this list nor have a predecessor node
				if(ptr->*PrevPtr == nullptr && ptr != first) {
					push_front(ptr);
				}
			}

			void clear() { first = last = nullptr; }

			/**
			 * Removes the pointed-to node from this list.
			 * Assumes the node actually IS on this list.
			 */
			void erase(pointer ptr) {
				assert(ptr->*NextPtr || ptr == last);
				assert(ptr->*PrevPtr || ptr == first);

				if(ptr->*PrevPtr) {
					ptr->*PrevPtr->*NextPtr = ptr->*NextPtr;

					if(ptr->*NextPtr) {
						ptr->*NextPtr->*PrevPtr = ptr->*PrevPtr;
					} else {
						last = ptr->*PrevPtr;
					}

					ptr->*PrevPtr = nullptr;
				} else {
					first = ptr->*NextPtr;

					if(first) {
						first->*PrevPtr = nullptr;
						ptr->*NextPtr = nullptr;
					} else {
						last = nullptr;
					}
				}
			}

			/**
			 * Removes the pointed-to node from this list,
			 * but only if the node actually is on this list.
			 */
			void erase_if_present(pointer ptr) {
				if(ptr->*PrevPtr || ptr == first) {
					erase(ptr);
				}
			}

			void push_back(pointer ptr) {
				if(last) {
					last->*NextPtr = ptr;
				} else {
					first = ptr;
				}

				ptr->*PrevPtr = last;
				last = ptr;
			}

			void push_back_nonempty(pointer ptr) {
				assert(first != nullptr);
				assert(last != nullptr);

				last->*NextPtr = ptr;
				ptr->*PrevPtr = last;
				ptr->*NextPtr = nullptr;
				last = ptr;
			}

			void add_back(pointer ptr) {
				if(ptr->*NextPtr == nullptr && ptr != last) {
					push_back(ptr);
				}
			}

			pointer front() { return first; }
			pointer back() { return last; }

			pointer pop_front() {
				pointer result = first;

				if(result) {
					if((first = first->*NextPtr) != nullptr) {
						first->*PrevPtr = nullptr;
					} else {
						last = nullptr;
					}

					result->*PrevPtr = nullptr;
					result->*NextPtr = nullptr;
				}

				return result;
			}

			pointer pop_back() {
				pointer result = last;

				if(result) {
					if((last = last->*PrevPtr) != nullptr) {
						last->*NextPtr = nullptr;
					} else {
						first = nullptr;
					}

					result->*PrevPtr = nullptr;
					result->*NextPtr = nullptr;
				}

				return result;
			}

			void merge(linked_list& other) {
				assert(!empty() && !other.empty());

				last->*NextPtr = other.first;
				other.first->*PrevPtr = last;
				last = other.last;

				other.first = nullptr;
				other.last = nullptr;
			}

		private:
			pointer first, last;
	};

	template<typename TagType>
		class circular_node_base
	{
		public:
			circular_node_base() noexcept :
				prev(nullptr), next(nullptr)
			{}

		private:
			template<typename NodeType, typename NodeBaseType> friend class circular_linked_list;

			circular_node_base(circular_node_base *p, circular_node_base *n) noexcept :
				prev(p), next(n)
			{}

			circular_node_base *prev, *next;
	};

	/**
	 * An intrusive circular linked list pseudo-container that does not take ownership of its contents.
	 * It requires a node type as template parameter that publicly derives from a NodeBaseType; this makes it nearly impossible to put several
	 * of these lists onto a single node type; but circular linked list have better insertion/removal performance (less special cases), thus
	 * using this for one of the linked lists that some node type is on may have benefits.
	 * The NodeBaseType has to have members prev and next that point to the previous/next members.
	 * The circular_node_base struct above (with differing TagTypes to create multiple distinct types from it) can be used for that.
	 *
	 * Note: this somewhat resembles a standard container, however it is NOT a standard-compliant container (misses size(),
	 * does not really contain nodes, rather points to them).
	 * However, the for(... : ...) syntax works and the iterators are standard-compliant.
	 */
	template<typename NodeType, typename NodeBaseType> class circular_linked_list {
		public:
			typedef NodeType value_type;
			typedef NodeType &reference;
			typedef typename std::add_const<NodeType>::type &const_reference;
			typedef NodeType *pointer;
			typedef typename std::add_const<NodeType>::type *const_pointer;
			typedef std::ptrdiff_t difference_type;
			typedef std::size_t size_type;

		private:
			template<typename RealNodeBase, typename RealNodeType> class node_iterator :
				public boost::iterator_facade<
					node_iterator<RealNodeBase, RealNodeType>,
					RealNodeType,
					boost::bidirectional_traversal_tag
				>
			{
				private:
					friend class circular_linked_list;
					friend class boost::iterator_core_access;
					struct enabler {};

				public:
					node_iterator() noexcept : mPtr(nullptr) {}

					template<typename OtherRealNodeBase, typename OtherRealNodeType>
						node_iterator(
							const node_iterator<OtherRealNodeBase, OtherRealNodeType>& other,
							std::enable_if<std::is_convertible<OtherRealNodeBase*, RealNodeBase*>::value, enabler> = enabler{}
						) noexcept : mPtr(other.mPtr)
					{}

				private:
					explicit node_iterator(RealNodeBase* ptr) noexcept :
						mPtr(ptr)
					{}

					template<typename OtherRealNodeBase, typename OtherRealNodeType>
						bool equal(const node_iterator<OtherRealNodeBase, OtherRealNodeType>& other) const noexcept
					{
						return mPtr == other.mPtr;
					}

					void increment() noexcept {
						assert(mPtr);
						mPtr = mPtr->next;
					}

					void decrement() noexcept {
						assert(mPtr);
						mPtr = mPtr->prev;
					}

					RealNodeType &dereference() const noexcept {
						assert(mPtr);
						return *static_cast<RealNodeType*>(mPtr);
					}

					RealNodeBase *mPtr;
			};

		public:
			typedef node_iterator<NodeBaseType, NodeType> iterator;
			typedef node_iterator<const NodeBaseType, const NodeType> const_iterator;

			circular_linked_list() noexcept :
				node(&node, &node)
			{}

			void assign(pointer ptr_) noexcept {
				assert(empty());

				NodeBaseType* const ptr = static_cast<NodeBaseType*>(ptr_);

				node.next = ptr;
				node.prev = ptr;
				ptr->next = &node;
				ptr->prev = &node;
			}

			iterator begin() noexcept {
				return iterator(node.next);
			}

			iterator end() noexcept {
				return iterator(&node);
			}

			const_iterator begin() const noexcept {
				return const_iterator(node.next);
			}

			const_iterator end() const noexcept {
				return const_iterator(&node);
			}

			const_iterator cbegin() const noexcept {
				return const_iterator(node.next);
			}

			const_iterator cend() const noexcept {
				return const_iterator(&node);
			}

			bool empty() const noexcept {
				return node.next == &node;
			}

			bool trivial() const noexcept {
				return node.prev == node.next;
			}

			void clear() noexcept {
				node.prev = node.next = &node;
			}

			pointer front() noexcept {
				assert(!empty());
				return static_cast<pointer>(node.next);
			}

			pointer back() noexcept {
				assert(!empty());
				return static_cast<pointer>(node.prev);
			}

			const_pointer front() const noexcept {
				assert(!empty());
				return static_cast<const_pointer>(node.next);
			}

			const_pointer back() const noexcept {
				assert(!empty());
				return static_cast<const_pointer>(node.prev);
			}

			void push_front(pointer ptr_) noexcept {
				NodeBaseType* const ptr = static_cast<NodeBaseType*>(ptr_);

				ptr->next = node.next;
				ptr->prev = &node;
				node.next->prev = ptr;
				node.next = ptr;
			}

			void add_front(pointer ptr_) noexcept {
				NodeBaseType* const ptr = static_cast<NodeBaseType*>(ptr_);

				if(ptr->next == nullptr) {
					ptr->next = node.next;
					ptr->prev = &node;
					node.next->prev = ptr;
					node.next = ptr;
				}
			}

			void push_back(pointer ptr_) noexcept {
				NodeBaseType* const ptr = static_cast<NodeBaseType*>(ptr_);

				ptr->next = &node;
				ptr->prev = node.prev;
				node.prev->next = ptr;
				node.prev = ptr;
			}

			void push_back_nonempty(pointer ptr_) noexcept {
				push_back(ptr_);
			}

			void add_back(pointer ptr_) noexcept {
				NodeBaseType* const ptr = static_cast<NodeBaseType*>(ptr_);

				if(ptr->next == nullptr) {
					ptr->next = &node;
					ptr->prev = node.prev;
					node.prev->next = ptr;
					node.prev = ptr;
				}
			}

			pointer pop_front() noexcept {
				NodeBaseType* const ptr = node.next;
				if(ptr == &node) {
					return nullptr;
				}

				ptr->next->prev = &node;
				node.next = ptr->next;
				ptr->prev = nullptr;
				ptr->next = nullptr;

				return static_cast<pointer>(ptr);
			}

			pointer pop_back() noexcept {
				NodeBaseType* const ptr = node.prev;
				if(ptr == &node) {
					return nullptr;
				}

				ptr->prev->next = &node;
				node.prev = ptr->prev;
				ptr->prev = nullptr;
				ptr->next = nullptr;

				return static_cast<pointer>(ptr);
			}

			void erase(pointer ptr_) noexcept {
				NodeBaseType* const ptr = static_cast<NodeBaseType*>(ptr_);

				assert(ptr->next != nullptr);
				assert(ptr->prev != nullptr);
				assert(ptr != &node);

				ptr->next->prev = ptr->prev;
				ptr->prev->next = ptr->next;
				ptr->prev = nullptr;
				ptr->next = nullptr;
			}

			void erase_if_present(pointer ptr_) noexcept {
				NodeBaseType* const ptr = static_cast<NodeBaseType*>(ptr_);

				assert(ptr != &node);

				if(ptr->next != nullptr) {
					assert(ptr->prev != nullptr);

					ptr->next->prev = ptr->prev;
					ptr->prev->next = ptr->next;
					ptr->prev = nullptr;
					ptr->next = nullptr;
				}
			}

			void merge(circular_linked_list& other) noexcept {
				assert(!empty() && !other.empty());

				NodeBaseType* const oldLast = node.prev;
				node.prev = other.node.prev;
				other.node.prev->next = &node;
				oldLast->next = other.node.next;
				other.node.next->prev = oldLast;
				other.node.next = &(other.node);
				other.node.prev = &(other.node);
			}

		private:
			circular_linked_list(const circular_linked_list&) = delete;
			circular_linked_list &operator=(const circular_linked_list&) = delete;

			NodeBaseType node;
	};
}

#endif /* SRC_LIB_MODULES_EQMODULE_LINKEDLIST_HPP_ */
