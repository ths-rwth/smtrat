#pragma once

#include <algorithm>
#include <queue>
#include <vector>

namespace smtrat {
	
	template<typename T, typename Compare = std::less<T>>
	class PriorityQueue: public std::priority_queue<T,std::vector<T>,Compare> {
		using super = std::priority_queue<T,std::vector<T>,Compare>;
	public:
		explicit PriorityQueue(const Compare& comp): super(comp) {}
		const typename super::container_type& data() const {
			return super::c;
		}
	};
	
	template<typename T, typename Compare = std::less<T>>
	class DynamicPriorityQueue {
		using Sequence = std::vector<T>;

	public:
		using value_type = typename Sequence::value_type;

	protected:
		Sequence c;
		Compare comp;

	public:
		
		explicit DynamicPriorityQueue(const Compare& _comp = Compare()):
			c(), comp(_comp)
		{}
		explicit DynamicPriorityQueue(Sequence&& _seq, const Compare& _comp = Compare()):
			c(std::move(_seq)), comp(_comp)
		{
			std::make_heap(c.begin(), c.end(), comp);
		}
		
		void fix() {
			std::make_heap(c.begin(), c.end(), comp);
		}

		bool empty() const {
			return c.empty();
		}

		std::size_t size() const {
			return c.size();
		}

		const T& top() const {
			return c.front();
		}

		void push(const T& t) {
			c.push_back(t);
			std::push_heap(c.begin(), c.end(), comp);
		}

		void push(T&& t) {
			c.push_back(std::move(t));
			std::push_heap(c.begin(), c.end(), comp);
		}

		template<typename... Args>
		void emplace(Args&&... args) {
			c.emplace_back(std::forward<Args>(args)...);
			std::push_heap(c.begin(), c.end(), comp);
		}

		void pop() {
			std::pop_heap(c.begin(), c.end(), comp);
			c.pop_back();
		}
		T popTop() {
			T r = top();
			pop();
			return r;
		}
	};
}
