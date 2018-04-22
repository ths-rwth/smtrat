#ifndef UNORDEREDBIMAP_HPP
#define UNORDEREDBIMAP_HPP

#include <iostream>
#include <forward_list>
#include <set>

template<class Class, typename FirstKeyType, FirstKeyType Class::*FirstKeyName, typename SecondKeyType, SecondKeyType Class::*SecondKeyName>
class Bimap
{
	public:
		typedef std::forward_list<Class> Data;
		typedef typename Data::iterator Iterator;
	
	private:
		struct FirstCompare
		{
			using is_transparent = void;
			
			bool operator()(const Iterator& lhs, const Iterator& rhs) const
			{
				return (*lhs).*FirstKeyName<(*rhs).*FirstKeyName;
			}
			
			bool operator()(const Iterator& lhs, const FirstKeyType& rhs) const
			{
				return (*lhs).*FirstKeyName<rhs;
			}
			
			bool operator()(const FirstKeyType& lhs, const Iterator& rhs) const
			{
				return lhs<(*rhs).*FirstKeyName;
			}
		};
		
		struct SecondCompare
		{
			using is_transparent = void;
			
			bool operator()(const Iterator& lhs, const Iterator& rhs) const
			{
				return (*lhs).*SecondKeyName<(*rhs).*SecondKeyName;
			}
			
			bool operator()(const Iterator& lhs, const SecondKeyType& rhs) const
			{
				return (*lhs).*SecondKeyName<rhs;
			}
			
			bool operator()(const SecondKeyType& lhs, const Iterator& rhs) const
			{
				return lhs<(*rhs).*SecondKeyName;
			}
		};
		
		Data mData;
		std::set<Iterator, FirstCompare> mFirstMap;
		std::set<Iterator, SecondCompare> mSecondMap;
	
	public:
		bool empty() const noexcept
		{
			return mData.empty();
		}
		
		Iterator begin() noexcept
		{
			return mData.begin();
		}
		
		Iterator end() noexcept
		{
			return mData.end();
		}
		
		Iterator firstFind(const FirstKeyType& firstKey)
		{
			auto firstIter{mFirstMap.find(firstKey)};
			if (firstIter == mFirstMap.end())
				return mData.end();
			else
				return *firstIter;
		}
		
		Iterator secondFind(const SecondKeyType& secondKey)
		{
			auto secondIter{mSecondMap.find(secondKey)};
			if (secondIter == mSecondMap.end())
				return mData.end();
			else
				return *secondIter;
		}
		
		template<typename... Args>
		Iterator emplace(const Args&&... args)
		{
			mData.emplace_front(std::move(args)...);
			mFirstMap.emplace(mData.begin());
			mSecondMap.emplace(mData.begin());
			return mData.begin();
		}
};

#endif
