#pragma once

#include <algorithm>
#include <iostream>
#include <queue>
#include <vector>

namespace smtrat {
	
	template<typename T, typename Compare = std::less<T>>
	class PriorityQueue: public std::priority_queue<T,std::vector<T>,Compare> {
		using super = std::priority_queue<T,std::vector<T>,Compare>;
	public:
		explicit PriorityQueue(): super() {}
		explicit PriorityQueue(const Compare& comp): super(comp) {}
		const auto& data() const {
			return super::c;
		}
		auto& data() {
			return super::c;
		}
		auto find(const T& t) const {
			return std::find(data().begin(), data().end(), t);
		}
		auto begin() const {
			return data().begin();
		}
		auto begin() {
			return data().begin();
		}
		auto end() const {
			return data().end();
		}
		auto end() {
			return data().end();
		}
		auto erase(typename std::vector<T>::const_iterator it) {
			return data().erase(it);
		}
		auto erase(typename std::vector<T>::const_iterator it, typename std::vector<T>::const_iterator end) {
			return data().erase(it, end);
		}
		void fix() {
			std::make_heap(data().begin(), data().end(), super::comp);
		}
		template<typename F>
		void removeIf(F&& f) {
			auto it = std::remove_if(data().begin(), data().end(), f);
			data().erase(it, data().end());
			std::make_heap(data().begin(), data().end(), super::comp);
		}
		void clear() {
			data().clear();
		}
	};
	template<typename TT, typename C>
	std::ostream& operator<<(std::ostream& os, const PriorityQueue<TT,C>& pq) {
		os << "[";
		for (auto it = pq.data().begin(); it != pq.data().end(); it++) {
			if (it != pq.data().begin()) os << ", ";
			os << *it;
		}
		return os << "]";
	}
	
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
