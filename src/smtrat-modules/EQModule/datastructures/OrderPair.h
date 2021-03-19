#ifndef ORDERPAIR_H_INCLUDED_
#define ORDERPAIR_H_INCLUDED_

#include <tuple>

namespace smtrat {
	namespace datastructures {
		
		template<typename T1, typename T2, bool reversed = false>
			struct OrderPair : public std::pair<T1, T2>
		{
		private:
			typedef std::pair<T1, T2> P;
		public:
			OrderPair(T1 pFirst = T1(), T2 pSecond = T2()):
				P(pFirst, pSecond)
			{}
			
			inline bool operator< (const OrderPair<T1, T2, reversed>& rhs) const {
				return P::first < rhs.first || (!(rhs.first < P::first) && (P::second < rhs.second));
			}
		};
		
		template<typename T1, typename T2>
			struct OrderPair<T1, T2, true> : public std::pair<T1, T2> {
		private:
			typedef std::pair<T1, T2> P;
		public:
			OrderPair(T1 pFirst = T1(), T2 pSecond = T2()):
				P(pFirst, pSecond)
			{}
			
			inline bool operator< (const OrderPair<T1, T2, true>& rhs) const {
				return P::second < rhs.second || (!(rhs.second < P::second) && (P::first < rhs.first));
			}
		};
		
	};
}

#endif // ORDERPAIR_H_INCLUDED_
