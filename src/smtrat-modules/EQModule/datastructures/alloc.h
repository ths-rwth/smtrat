#ifndef SRC_LIB_DATASTRUCTURES_EQ_ALLOC_HPP_INCLUDED_
#define SRC_LIB_DATASTRUCTURES_EQ_ALLOC_HPP_INCLUDED_

#include <memory>
#include <algorithm>
#include <type_traits>
#include <vector>
#include <cassert>

#include <limits>

#ifdef SMTRAT_STRAT_PARALLEL_MODE
#include <mutex>
#endif

#ifdef __VS
	// Visual studio does neither support noexcept nor constexpr
	// TODO Matthias: Introduce project-wide
	#define NOEXCEPT 
	#define CONSTEXPR const
#else
	#define NOEXCEPT noexcept
	#define CONSTEXPR constexpr
#endif

namespace smtrat {
	namespace impl {
		/**
		 * Used to find ceil(log2(n)) (the shift distance in the freelist allocator).
		 */
		// TODO Matthias: workaround for other compilers
		// VS: https://stackoverflow.com/questions/355967/how-to-use-msvc-intrinsics-to-get-the-equivalent-of-this-gcc-code
		/*template<typename T> static CONSTEXPR inline std::size_t count_leading_zeros(T number);
		template<> inline CONSTEXPR std::size_t count_leading_zeros<unsigned int>(unsigned int number) { return static_cast<std::size_t>(__builtin_clz(number)); }
		template<> inline CONSTEXPR std::size_t count_leading_zeros<unsigned long>(unsigned long number) { return static_cast<std::size_t>(__builtin_clzl(number)); }
		template<> inline CONSTEXPR std::size_t count_leading_zeros<unsigned long long>(unsigned long long number) { return static_cast<std::size_t>(__builtin_clzll(number)); }
		*/
		template<typename T> static CONSTEXPR inline std::size_t roundup_log2(T /*number*/) {
			return (sizeof(T)*8 /*- count_leading_zeros(number)*/);
		}
	}

	/**
	 * Implements a fixed-(at-runtime)-size allocator based on a free list embedded in the space of currently unused objects.
	 *
	 * Caution: Do not use this with types
	 * that need their destructor to be called,
	 * only for trivial types (like pointers, iterators, scalar values, ...).
	 * Otherwise, do not use the clear() method and call the destructor before free().
	 */
	template<typename T> class freelist {
		public:
			explicit freelist() :
				freelist(sizeof(T))
			{}

			explicit freelist(std::size_t chunk_size_) :
				mSizeShift(impl::roundup_log2(std::max(sizeof(void*), std::max(sizeof(T), chunk_size_)))),
				mFree(0),
				mCurrentPage(0),
				mPageCount(1),
				mCurrentPageFreeFrom(0)
			{
				assert((1u<<mSizeShift) >= chunk_size_);
				assert((1u<<mSizeShift) >= sizeof(T));
				assert((1u<<mSizeShift) >= sizeof(void*));

				if((mPages[0] = malloc(first_page_size << mSizeShift)) == nullptr) {
					throw std::bad_alloc();
				}
			}

			~freelist() {
				for(std::size_t i = 0; i < mPageCount; ++i) {
					free(mPages[i]);
				}
			}

			template<typename... Args> T& emplace(Args&&... args) {
				void* addr = alloc();

				try {
					return *(new (addr) T(std::forward<Args>(args)...));
				} catch(...) {
					free(addr);
					throw;
				}
			}

			/**
			 * Allocate an object of size 1<<mSizeShift.
			 */
			void* alloc() {
				/**
				 * First, try to return the first entry on the freelist.
				 */
				if(mFree != nullptr) {
					void* result = mFree;
					mFree = *static_cast<void**>(mFree);
					return result;
				}

				/**
				 * If that is empty, try forward-allocation
				 * (allocating the next element on the current page
				 * that has never been allocated before.)
				 */
				if(mCurrentPageFreeFrom != (first_page_size << mCurrentPage)) {
					return static_cast<void*>(
						static_cast<char*>(mPages[mCurrentPage]) +
						(mCurrentPageFreeFrom++ << mSizeShift)
					);
				}

				/**
				 * Otherwise, go to the next page.
				 */
				++mCurrentPage;
				if(mCurrentPage < mPageCount) {
					mCurrentPageFreeFrom = 1;
					return mPages[mCurrentPage];
				}

				/**
				 * If there is no next page, allocate a new page with malloc.
				 * This page has twice the space of the previous page.
				 */
				void* newPage = malloc((first_page_size << mCurrentPage) << mSizeShift);
				if(newPage == nullptr) {
					--mCurrentPage;
					throw std::bad_alloc();
				}

				/**
				 * Start forward-allocation phase on the new page.
				 */
				mPages[mCurrentPage] = newPage;
				mCurrentPageFreeFrom = 1;
				return newPage;
			}

			/**
			 * Freeing means just prepending the free'd element to the front of the freelist.
			 */
			void free(void* ptr) NOEXCEPT {
				*static_cast<void**>(ptr) = mFree;
				mFree = ptr;
			}

			/**
			 * Invalidate ALL entries allocated using this allocator.
			 * Note that this does not call the destructor of any elements,
			 * and does not return any memory to the OS.
			 */
			 void clear() NOEXCEPT {
				mCurrentPage = 0;
				mCurrentPageFreeFrom = 0;
				mFree = nullptr;
			}
		private:
			static CONSTEXPR std::size_t first_page_size = 1024;

			freelist(const freelist&) = delete;
			freelist &operator=(const freelist&) = delete;

			const std::size_t mSizeShift;
			void* mPages[54];
			void* mFree;
			std::size_t mCurrentPage;
			std::size_t mPageCount;
			std::size_t mCurrentPageFreeFrom;
	};

	/**
	 * Implements a fixed-(at-compile-time)-size allocator based on a free list embedded in the space of currently unused objects.
	 */
	template<std::size_t ChunkSizeShift> class fixedsize_freelist {
		public:
			// TODO Matthias: activate again
			//static_assert((1 << ChunkSizeShift) >= sizeof(void*), "The size of a chunk must be at least sizeof(void*)!");

			explicit fixedsize_freelist() :
				mFree(nullptr),
				mCurrentPage(0),
				mPageCount(1),
				mCurrentPageFreeFrom(0)
			{
				if((mPages[0] = malloc(first_page_size << ChunkSizeShift)) == nullptr) {
					throw std::bad_alloc();
				}
			}

			~fixedsize_freelist() {
				for(std::size_t i = 0; i < mPageCount; ++i) {
					free(mPages[i]);
				}
			}

			/**
			 * Allocate an object of size 1<<ChunkSizeShift.
			 */
			void* alloc() {
#ifdef SMTRAT_STRAT_PARALLEL_MODE
				std::lock_guard<std::mutex> locker(mMutex);
#endif

				/**
				 * First, try to return the first entry on the freelist.
				 */
				if(mFree != nullptr) {
					void* result = mFree;
					mFree = *static_cast<void**>(mFree);
					return result;
				}

				/**
				 * If that is empty, try forward-allocation
				 * (allocating the next element on the current page
				 * that has never been allocated before.)
				 */
				if(mCurrentPageFreeFrom != (first_page_size << mCurrentPage)) {
					return static_cast<void*>(
						static_cast<char*>(mPages[mCurrentPage]) +
						(mCurrentPageFreeFrom++ << ChunkSizeShift)
					);
				}

				/**
				 * Otherwise, go to the next page.
				 */
				++mCurrentPage;
				if(mCurrentPage < mPageCount) {
					mCurrentPageFreeFrom = 1;
					return mPages[mCurrentPage];
				}

				/**
				 * If there is no next page, allocate a new page with malloc.
				 * This page has twice the space of the previous page.
				 */
				void* newPage = malloc((first_page_size << mCurrentPage) << ChunkSizeShift);
				if(newPage == nullptr) {
					--mCurrentPage;
					throw std::bad_alloc();
				}

				/**
				 * Start forward-allocation phase on the new page.
				 */
				mPages[mCurrentPage] = newPage;
				mCurrentPageFreeFrom = 1;
				return newPage;
			}

			/**
			 * Freeing means just prepending the free'd element to the front of the freelist.
			 */
			void free(void* ptr) NOEXCEPT {
#ifdef SMTRAT_STRAT_PARALLEL_MODE
				std::lock_guard<std::mutex> locker(mMutex);
#endif
				*static_cast<void**>(ptr) = mFree;
				mFree = ptr;
			}

		private:
			fixedsize_freelist(const fixedsize_freelist&) = delete;
			fixedsize_freelist &operator=(const fixedsize_freelist&) = delete;

			static CONSTEXPR std::size_t first_page_size = 1024;

#ifdef SMTRAT_STRAT_PARALLEL_MODE
			std::mutex mMutex;
#endif

			void* mPages[54];
			void* mFree;
			std::size_t mCurrentPage;
			std::size_t mPageCount;
			std::size_t mCurrentPageFreeFrom;
	};

	namespace impl {
		static CONSTEXPR std::size_t LOWER_SIZE_BOUND = sizeof(void*);
		static CONSTEXPR std::size_t UPPER_SIZE_BOUND = 256;

		template<typename T, std::size_t SizeShift, bool LargeEnough, bool SmallEnough> class fixedsize_allocator_impl;

		// TODO Matthias: activate again
		/**
		 * Publicly derive from all fixedsize_freelist types with chunk sizes between SizeCurrent and SizeMax.
		 */
		template<std::size_t SizeCurrent, std::size_t SizeMax, bool LowEnough = (SizeCurrent < SizeMax)> class fixedsize_freelists /*:
			public fixedsize_freelist<roundup_log2(SizeMax)>*/
		{};

		template<std::size_t SizeCurrent, std::size_t SizeMax> class fixedsize_freelists<SizeCurrent, SizeMax, true> :
			// TODO Matthias: activate again
			//public fixedsize_freelist<roundup_log2(SizeCurrent)>,
			public fixedsize_freelists<SizeCurrent * 2, SizeMax>
		{};

		class fixedsize_allocator_freelists :
			public fixedsize_freelists<LOWER_SIZE_BOUND, UPPER_SIZE_BOUND>
		{
			public:
				static fixedsize_allocator_freelists INSTANCE;

			private:
				fixedsize_allocator_freelists() {}
		};

		template<typename T, std::size_t SizeShift> class fixedsize_allocator_impl<T, SizeShift, true, true> {
			public:
				typedef T value_type;
				typedef T* pointer;
				typedef const T* const_pointer;
				typedef T& reference;
				typedef const T& const_reference;
				typedef std::size_t size_type;
				typedef std::ptrdiff_t difference_type;
				typedef std::true_type propagate_on_container_move_assignment;
				typedef std::true_type is_always_equal;

				pointer address(reference x) const NOEXCEPT { return std::addressof(x); }
				const_reference address(const_reference x) const NOEXCEPT { return std::addressof(x); }

				CONSTEXPR size_type max_size() const NOEXCEPT { return std::numeric_limits<std::size_t>::max(); }

				pointer allocate(size_type n, const void* hint = 0) {
					if(n == 1) {
//						return static_cast<pointer>(static_cast<fixedsize_freelist<SizeShift>&>(fixedsize_allocator_freelists::INSTANCE).alloc()); // @todo
						return std::allocator<T>{}.allocate(n, hint);
					} else {
						return std::allocator<T>{}.allocate(n, hint);
					}
				}

				void deallocate(pointer p, size_type n) {
					if(n == 1) {
//						static_cast<fixedsize_freelist<SizeShift>&>(fixedsize_allocator_freelists::INSTANCE).free(p); // @todo
					} else {
						std::allocator<T>{}.deallocate(p, n);
					}
				}

				template<class U, class... Args> void construct(U* p, Args&&... args) {
					::new((void*)p) U(std::forward<Args>(args)...);
				}

				template<class U> void destroy(U* p) {
					p->~U();
				}
		};

		template<typename T, std::size_t Size> class fixedsize_allocator_size_helper :
			public fixedsize_allocator_impl<T, roundup_log2(Size), (Size >= sizeof(void*)), (Size <= 2048)>
		{};
	}

	/**
	 * An allocator meant to be used for containers that typically allocate single objects or nodes,
	 * such as sets, maps and linked lists.
	 * For any allocation that allocates more than one element at once, this falls back to std::allocator.
	 * With this allocator, free consists of two single pointer operations only.
	 * Allocate is almost always as cheap as free.
	 */
	template<typename T> class fixedsize_allocator : public impl::fixedsize_allocator_size_helper<T, (sizeof(void*) > sizeof(T) ? sizeof(void*) : sizeof(T))> {
		public:
			template<class U> struct rebind {
				typedef fixedsize_allocator<U> other;
			};

			fixedsize_allocator() NOEXCEPT {}
			fixedsize_allocator(const fixedsize_allocator&) NOEXCEPT = default;
			template<typename U> fixedsize_allocator(const fixedsize_allocator<U>&) NOEXCEPT {}

			template<typename T2> CONSTEXPR bool operator==(const fixedsize_allocator<T2>&) const NOEXCEPT { return true; }
			template<typename T2> CONSTEXPR bool operator!=(const fixedsize_allocator<T2>&) const NOEXCEPT { return false; }
	};

	/**
	 * I do not know where an allocator for void would be of any use;
	 * but in order to mimic std::allocator (where this is explicitly mentioned) as good as possible, we do this for the void case.
	 */
	template<> class fixedsize_allocator<void> : public std::allocator<void> {};

	template<typename T> class dynarray;
	template<typename T> class dynarray_allocator {
		private:
			static dynarray_allocator<T> INSTANCE;
			friend class dynarray<T>;

			dynarray_allocator() {}
			~dynarray_allocator() {
				for(auto &s : mStubs) {
					free(s.mBuffer);
				}
			}

			struct dynarray_stub {
				dynarray_stub(T* buffer, std::size_t cap) :
					mBuffer(buffer),
					mCapacity(cap)
				{}

				T* mBuffer;
				std::size_t mCapacity;
			};

			void allocate_buffer(T* &buffer, std::size_t& capacity) {
#ifdef SMTRAT_STRAT_PARALLEL_MODE
				std::lock_guard<std::mutex> locker(mMutex);
#endif

				if(!mStubs.empty()) {
					buffer = mStubs.back().mBuffer;
					capacity = mStubs.back().mCapacity;
					mStubs.pop_back();
				} else {
					buffer = static_cast<T*>(malloc(64 * sizeof(T)));
					capacity = 64;
				}
			}

			void free_buffer(T* buffer, std::size_t capacity) {
#ifdef SMTRAT_STRAT_PARALLEL_MODE
				std::lock_guard<std::mutex> locker(mMutex);
#endif

				mStubs.emplace_back(buffer, capacity);
			}

#ifdef SMTRAT_STRAT_PARALLEL_MODE
			std::mutex mMutex;
#endif

			std::vector<dynarray_stub> mStubs;
	};

	template<typename T> dynarray_allocator<T> dynarray_allocator<T>::INSTANCE;

	/**
	 * dynarray is similar to std::vector, but has only a reduced interface.
	 * Moreover, it releases its memory to a dynarray_allocator in its destructor
	 * and supports an optimized consume method to move-add all elements from some dynarray to another,
	 * and also a swap-to-end remove method.
	 * It is to be used in contexts where dynamic arrays have to be allocated and freed relatively frequently.
	 */
	template<typename T> class dynarray {
		public:
			typedef T value_type;
			typedef T* iterator;
			typedef const T* const_iterator;
			typedef T& reference;
			typedef const T& const_reference;
			typedef T* pointer;
			typedef const T* const_pointer;

			dynarray() :
				mPointer(nullptr),
				mSize(0),
				mCapacity(0)
			{}

			dynarray(std::size_t initialCap) :
				mPointer(static_cast<T*>(malloc(initialCap * sizeof(T)))),
				mSize(0),
				mCapacity(initialCap)
			{
				if(!mPointer) {
					throw std::bad_alloc();
				}
			}

			~dynarray() {
				if(mCapacity) P_free();
			}

			dynarray(const dynarray&) = delete;
			dynarray &operator=(const dynarray&) = delete;

			dynarray(dynarray&& other) NOEXCEPT :
				mPointer(other.mPointer),
				mSize(other.mSize),
				mCapacity(other.mCapacity)
			{
				other.mPointer = nullptr;
				other.mSize = other.mCapacity = 0;
			}

				dynarray &operator=(dynarray&& other) NOEXCEPT {
				if(this != &other) {
					if(mCapacity) P_free();

					mPointer = other.mPointer;
					mSize = other.mSize;
					mCapacity = other.mCapacity;

					other.mPointer = nullptr;
					other.mSize = other.mCapacity = 0;
				}

				return *this;
			}

			iterator begin() NOEXCEPT { return mPointer; }
			iterator end() NOEXCEPT { return mPointer + mSize; }
			const_iterator begin() const NOEXCEPT { return mPointer; }
			const_iterator end() const NOEXCEPT { return mPointer + mSize; }

			bool empty() const NOEXCEPT { return mSize == 0; }
			std::size_t size() const NOEXCEPT { return mSize; }
			std::size_t capacity() const NOEXCEPT { return mCapacity; }

			void remove(const T& value) {
				T* ptr = std::find(begin(), end(), value);
				assert(ptr != end());
				std::swap(*ptr, back());
				pop_back();
			}

			template<typename... Args> T& emplace_back(Args&&... args) {
				if(mSize == mCapacity) {
					P_grow();
				}

				T& result = *new (&mPointer[mSize]) T(std::forward<Args>(args)...);
				++mSize;
				return result;
			}

			void swap(dynarray<T>& other) NOEXCEPT {
				std::swap(mPointer, other.mPointer);
				std::swap(mSize, other.mSize);
				std::swap(mCapacity, other.mCapacity);
			}

			void swap(dynarray<T>&& other) NOEXCEPT {
				std::swap(mPointer, other.mPointer);
				std::swap(mSize, other.mSize);
				std::swap(mCapacity, other.mCapacity);
			}

			void consume(dynarray<T>&& other) {
				if(mSize == 0) {
					swap(other);
				} else {
					if(other.mCapacity > mCapacity && other.mCapacity >= mSize + other.mSize) {
						swap(other);
					} else if(mCapacity < mSize + other.mSize) {
						P_grow(mSize + other.mSize);
					}

					for(std::size_t i = 0; i < other.mSize; ++i) {
						new (&mPointer[mSize+i]) T(std::move(other.mPointer[i]));
						other.mPointer[i].~T();
					}

					mSize += other.mSize;
					other.mSize = 0;
				}
			}

			T& front() NOEXCEPT { assert(mSize != 0); return *mPointer; }

			T& back() NOEXCEPT { assert(mSize != 0); return mPointer[mSize - 1]; }
			void pop_back() NOEXCEPT {
				mPointer[--mSize].~T();
			}

			reference operator[](std::size_t index) NOEXCEPT {
				assert(index < mSize);
				return mPointer[index];
			}

			const_reference operator[](std::size_t index) const NOEXCEPT {
				assert(index < mSize);
				return mPointer[index];
			}

			void clear() NOEXCEPT {
				if(!std::is_trivially_destructible<T>::value) {
					for(std::size_t i = 0; i < mSize; ++i) {
						mPointer[i].~T();
					}
				}

				mSize = 0;
			}

			void reserve(std::size_t minCap) {
				if(minCap > mCapacity) {
					P_realloc(minCap);
				}
			}

		private:
			void P_free() {
				if(!std::is_trivially_destructible<T>::value) {
					for(std::size_t i = 0; i < mSize; ++i) {
						mPointer[i].~T();
					}
				}

				dynarray_allocator<T>::INSTANCE.free_buffer(mPointer, mCapacity);
			}

			void P_grow() {
				if(mCapacity == 0) {
					dynarray_allocator<T>::INSTANCE.allocate_buffer(mPointer, mCapacity);
				} else {
					std::size_t newCap = 2*mCapacity + 16;
					P_realloc(newCap);
				}
			}

			void P_grow(std::size_t newSizeMin) {
				std::size_t newCap = std::max(newSizeMin, 2*mCapacity + 16);
				P_realloc(newCap);
			}

			void P_realloc(std::size_t newCap) {
				if(std::is_trivial<T>::value) {
					mPointer = static_cast<T*>(realloc(mPointer, newCap * sizeof(T)));
				} else {
					T* ptr = static_cast<T*>(malloc(newCap * sizeof(T)));

					for(std::size_t i = 0; i < mSize; ++i) {
						new (&ptr[i]) T(std::move(mPointer[i]));
						mPointer[i].~T();
					}

					free(mPointer);
					mPointer = ptr;
				}

				mCapacity = newCap;
			}

			T* mPointer;
			std::size_t mSize;
			std::size_t mCapacity;
	};
}

#endif
