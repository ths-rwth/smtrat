#ifndef UNION_FIND_HPP_INCLUDED_
#define UNION_FIND_HPP_INCLUDED_

#include <vector>
#include <cstddef>
#include <type_traits>
#include <utility>
#include <cassert>
#include <algorithm>
#include <iterator>

namespace smtrat {
	namespace uf_impl {
		/**
		 * Wrapper class that contains the rank and parent class of some entry of the UF datastructure.
		 * The compression parameter (default to off, this seems to be faster, can only enabled if sizeof(std::size_t) >= 8) controls whether
		 * the rank member is compressed together with the parent class.
		 * If this is true, sizeof(uf_rank_and_class<true>) is just sizeof(std::size_t), and
		 * the most significant byte of the class is interpreted as rank of the entry.
		 */
		template<bool compression> class uf_rank_and_class {
			public:
				uf_rank_and_class(std::size_t class_index) :
					M_class(class_index),
					M_rank(0)
				{}
				
				std::size_t rank() const noexcept { return M_rank; }
				std::size_t class_() const noexcept { return M_class; }
				void set_class(std::size_t newclass) noexcept { M_class = newclass; }
				void increment_rank() noexcept { ++M_rank; }
				void set_rank(std::size_t rank) { M_rank = rank; }

			private:
				std::size_t M_class, M_rank;
		};

		/**
		 * Compressed implementation of uf_rank_and_class.
		 */
		template<> class uf_rank_and_class<true> {
			public:
				uf_rank_and_class(std::size_t class_index) :
					M_rank_and_class(class_index)
				{}

				std::size_t rank() const noexcept {
					return M_rank_and_class >> 56;
				}

				std::size_t class_() const noexcept {
					return M_rank_and_class & ((std::size_t(1) << 56) - 1);
				}

				void set_class(std::size_t newclass) noexcept {
					M_rank_and_class = (M_rank_and_class & ~((std::size_t(1) << 56) - 1)) | newclass;
				}

				void increment_rank() noexcept {
					M_rank_and_class += (std::size_t(1) << 56);
				}

				void set_rank(std::size_t rank) {
					M_rank_and_class = (((std::size_t(1) << 56) - 1) & M_rank_and_class) | (rank << 56);
				}

			private:
				std::size_t M_rank_and_class;
		};

		/**
		 * Wrapper around data entry and uf_rank_and_class;
		 * this class contains a value of type T and both rank and class of
		 * an entry in the UF datastructure.
		 */
		template<typename T, bool compression> class uf_data_wrapper {
			public:
				typedef T value_type;
				
				uf_data_wrapper(T value_, std::size_t class_index) :
					M_value(value_),
					M_rank_and_class(class_index)
				{}

				T &value() noexcept { return M_value; }
				const T& value() const noexcept { return M_value; }

				std::size_t rank() const noexcept { return M_rank_and_class.rank(); }
				std::size_t class_() const noexcept { return M_rank_and_class.class_(); }
				void set_class(std::size_t newclass) noexcept { M_rank_and_class.set_class(newclass); }
				void increment_rank() noexcept { M_rank_and_class.increment_rank(); }
				void set_rank(std::size_t rank_) noexcept { M_rank_and_class.set_rank(rank_); }

			private:
				T M_value;
				uf_rank_and_class<compression> M_rank_and_class;
		};

		/**
		 * Special case of the uf_data_wrapper in case the data type is void.
		 * Then, there is no value member and no corresponding member functions.
		 */
		template<bool compression> class uf_data_wrapper<void, compression> {
			public:
				uf_data_wrapper(std::size_t class_index) :
					M_rank_and_class(class_index)
				{}

				std::size_t rank() const noexcept { return M_rank_and_class.rank(); }
				std::size_t class_() const noexcept { return M_rank_and_class.class_(); }
				void set_class(std::size_t newclass) noexcept { M_rank_and_class.set_class(newclass); }
				void increment_rank() noexcept { M_rank_and_class.increment_rank(); }
				void set_rank(std::size_t rank_) noexcept { M_rank_and_class.set_rank(rank_); }

			private:
				uf_rank_and_class<compression> M_rank_and_class;
		};

		/**
		 * Distance estimation for a range delimited by iterators;
		 * if the given iterators are random access, returns the result of std::distance in the estimate_distance function.
		 * Otherwise, it simply returns 0.
		 */
		template<
			typename IteratorType, 
			bool IsRandomAccess = std::is_convertible< typename std::iterator_traits<IteratorType>::iterator_category, std::random_access_iterator_tag >::value
		> struct estimator 
		{
			static std::size_t estimate_distance(IteratorType begin, IteratorType end) noexcept {
				return std::distance(begin, end);
			}
		};

		template<typename IteratorType> struct estimator<IteratorType, false> {
			static constexpr std::size_t estimate_distance(IteratorType, IteratorType) noexcept {
				return 0;
			}
		};
	}

	/**
	 * Implements a union-find datastructure, a datastructure containing an array of entries.
	 * Basically, this is an array of elements of type T with the following extra structure:
	 * Every entry is contained in an equivalence class identified by a single representative entry.
	 * In order to find this representative, every element has an associated parent entry;
	 * if this is the entry itself, the entry is the representative of its equivalence class.
	 * Using a rank count (basically a lower bound for the height of the tree below an entry),
	 * the height of the trees below the representative entries is ALWAYS less than ceil(log2(#entries)).
	 * Moreover, while finding the parent of an entry, all entries on the path to the root are set
	 * to directly point to the root element. This improves the amortized number of steps used to find
	 * the representative of an entry from O(log2(n)) to O(a(n)) where a(n) is the inverse of the Ackermann function.
	 * All this extra structure is embedded directly within the array.
	 */
	template<
		typename T = void, // the type to carry around with us
		bool no_compression = true, // turn on/off compression of rank and class index into the same 8-byte variable, defaults to off (seems to be faster)
		std::size_t MaxTracebackLength = 64 // how long may the path be that we compress during find? (note: ceil(log(#elements)) is strong upper bound, so 64 is very safe)
	> class union_find {
		public:
			/**
			 * Construct union-find datastructure with an empty array of entries.
			 */
			union_find() : M_array() {}

			/**
			 * Construct union-find datastructure with an array of size_ default-constructed elements.
			 */
			explicit union_find(std::size_t size_) : M_array() {
				initialize(size_);
			}

			/**
			 * Construct union-find datastructure, copying the sequence identified by [begin_,end_) into the array.
			 */
			template<typename InputIterator> union_find(
				InputIterator begin_,
				typename std::enable_if< !std::is_void<T>::value, InputIterator>::type end_
			) : M_array()
			{
				initialize(begin_, end_);
			}

			union_find(const union_find& other) :
				M_array(other.M_array)
			{}

			union_find &operator=(const union_find& other) {
				std::vector<wrapper_type> tmp(other.M_array);
				M_array = std::move(tmp);
				return *this;
			}

			/**
			 * Find the index of the representative of the entry at index index_.
			 * Note that this method is const-qualified as it does not change the
			 * observable behaviour of this class, but it is not bitwise-const due
			 * to the path compression behaviour.
			 * Therefore it is not safe to call this method from different threads
			 * on the same UF datastructure without external synchronization.
			 */
			std::size_t find(std::size_t index_) const noexcept {
				return const_cast<union_find&>(*this).P_do_find(index_);
			}

			/**
			 * Determines if the two entries at positions index1 and index2
			 * are considered equivalent, that is find(index1) == find(index2).
			 */
			bool equivalent(std::size_t index1, std::size_t index2) const noexcept {
				return find(index1) == find(index2);
			}

			/**
			 * Make the entries identified by index1 and index2 equivalent.
			 * As this is determined by the union-by-rank mechanism, either one
			 * of find(index1) or find(index2) can become the index of the new representative of both entries.
			 * Returns false when this operation did no changes on the datastructure and true otherwise.
			 */
			bool union_(std::size_t index1, std::size_t index2) noexcept {
				index1 = find(index1);
				index2 = find(index2);

				if(index1 != index2) {
					P_union_by_rank(index1, index2);
					return true;
				}

				return false;
			}

			/**
			 * As union_, but does NOT compute find(rep1), find(rep2),
			 * but assumes both indices are already pointing to representatives.
			 * Returns the new representative of both elements after the operation;
			 * this will either be rep1 or rep2.
			 */
			std::size_t fast_union(std::size_t rep1, std::size_t rep2) {
				assert(rep1 == find(rep1));
				assert(rep2 == find(rep2));
				assert(rep1 != rep2);

				return P_union_by_rank(rep1, rep2);
			}

			/**
			 * Add a new default-constructed value to the end of this union find array.
			 * This does not check for the uniqueness of this entry.
			 * This method can not be used if T is void.
			 * Returns the index associated with the new entry (i.e. the size of the UF structure before the call).
			 */
			template<bool Ignore = true> typename std::enable_if< !std::is_void<T>::value && Ignore, std::size_t>::type
				/* std::size_t */ add(const T& value)
			{
				std::size_t result = M_array.size();
				M_array.emplace_back(value, result);
				return result;
			}

			/*
			 * Set the class of element at index i to c.
			 * Note that this does NOT check anything;
			 * the moved element may or may not take any other elements with it.
			 * be sure to always reset the class values
			 * of all elements in a consistent manner before using find again.
			 */
			void set_class(std::size_t i, std::size_t c) {
				wrapper_type &wtype = M_array[i];
				wtype.set_class(c);
				wtype.set_rank(0);

				if(i != c && M_array[c].rank() == 0) {
					M_array[c].increment_rank();
				}
			}

			/**
			 * The rank (upper bound on the height of the tree rooted at i)
			 * of the entry at index i.
			 */
			std::size_t rank(std::size_t i) {
				return M_array[i].rank();
			}

			/**
			 * Access to values (only if T is not void, relies on C++11 feature: default template arguments for template methods).
			 */
			template<bool Ignore = true> typename std::enable_if< !std::is_void<T>::value && Ignore, T>::type&
				/* T& */ operator[](std::size_t index_) noexcept 
			{
				assert(index_ < M_array.size());
				return M_array[index_].value();
			}

			/**
			 * Access to values (only if T is not void, relies on C++11 feature: default template arguments for template methods), const.
			 */
			template<bool Ignore = true> typename std::enable_if< !std::is_void<T>::value && Ignore, const T>::type&
				/* const T& */ operator[](std::size_t index_) const noexcept 
			{
				assert(index_ < M_array.size());
				return M_array[index_].value();
			}

			/**
			 * Returns the number of entries in this union-find datastructure.
			 */
			std::size_t size() const noexcept { return M_array.size(); }

			/**
			 * Initialize the union-find datastructure with an array of new_size default-constructed entries,
			 * version for T != void.
			 */
			template<bool Ignore = true> typename std::enable_if<!std::is_void<T>::value && Ignore, void>::type initialize(std::size_t new_size) 
			{
				std::vector<wrapper_type> new_;
				new_.reserve(new_size);

				for(std::size_t i = 0; i < new_size; ++i) {
					new_.emplace_back(T(), i);
				}

				M_array = std::move(new_);
			}

			/**
			 * Initialize the union-find datastructure with an array of new_size default-constructed entries,
			 * version for T == void.
			 */
			template<bool Ignore = true> typename std::enable_if<std::is_void<T>::value && Ignore, void>::type initialize(std::size_t new_size)
			{
				std::vector<wrapper_type> new_;
				new_.reserve(new_size);

				for(std::size_t i = 0; i < new_size; ++i) {
					new_.emplace_back(i);
				}

				M_array = std::move(new_);
			}

			/**
			 * Initialize the union-find datastructure with an array of entries copied from the sequence [begin_,end_).
			 */
			template<typename InputIterator>
				typename std::enable_if<!std::is_void<T>::value && !std::is_void<InputIterator>::value, void>::type initialize(InputIterator begin_, InputIterator end_)
			{
				std::vector<wrapper_type> new_;
				const std::size_t est_size = uf_impl::estimator<InputIterator>::estimate_distance(begin_, end_);

				if(est_size) new_.reserve(est_size);

				std::size_t i = 0;
				for(; begin_ != end_; ++begin_) {
					new_.emplace_back(*begin_, i++);
				}

				M_array = std::move(new_);
			}

		private:
			/**
			 * Perform the find operation (walk the path until an entry
			 * with class == index is found).
			 */
			std::size_t P_do_find(std::size_t index_) noexcept {
				wrapper_type *traceback[MaxTracebackLength];
				std::size_t traceback_index = 0;

				for(;;) {
					std::size_t last = index_;
					wrapper_type &entry = M_array[index_];
					index_ = entry.class_();

					if(last == index_) break;

					assert(traceback_index < MaxTracebackLength);
					traceback[traceback_index++] = &entry;
				}

				// perform path compression
				for(std::size_t i = 0; i < traceback_index; ++i) {
					traceback[i]->set_class(index_);
				}

				return index_;
			}

			/**
			 * Union the two elements (must be representatives) by rank.
			 */
			std::size_t P_union_by_rank(std::size_t index1, std::size_t index2) {
				wrapper_type &e1 = M_array[index1];
				wrapper_type &e2 = M_array[index2];

				if(e1.rank() < e2.rank()) {
					e1.set_class(index2);
					return index2;
				} else if(e1.rank() > e2.rank()) {
					e2.set_class(index1);
					return index1;
				} else {
					e1.increment_rank();
					e2.set_class(index1);
					return index1;
				}
			}

			typedef uf_impl::uf_data_wrapper<T, sizeof(std::size_t) == 8 && !no_compression> wrapper_type;

			/**
			 * The backing vector of the datastructure.
			 */
			std::vector<wrapper_type> M_array;
	};
}

#endif

