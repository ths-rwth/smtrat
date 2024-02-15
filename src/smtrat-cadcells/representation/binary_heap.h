#pragma once

#include <vector>

namespace smtrat::cadcells::representation::util {

#define EPSILON 0.000001
#define GREATER(A, B) ((A) - (B) > EPSILON)

/*
This is a binary heap for pairs of the type (double key, int satellite)
It is assumed that satellites are unique integers
This is the case with graph algorithms, in which satellites are vertex or edge indices
 */
class BinaryHeap {
public:
	BinaryHeap()
		: satellite(1), size(0){};

	// Inserts (key k, satellite s) in the heap
	void Insert(double k, int s);

	// Deletes the element with minimum key and returns its satellite information
	int DeleteMin();

	// Returns the number of elements in the heap
	int Size();

private:
	std::vector<double> key;	// Given the satellite, this is its key
	std::vector<int> pos;		// Given the satellite, this is its position in the heap
	std::vector<int> satellite; // This is the heap!

	// Number of elements in the heap
	int size;
};

inline void BinaryHeap::Insert(double k, int s) {
	// Ajust the structures to fit new data
	if (s >= (int)pos.size()) {
		pos.resize(s + 1, -1);
		key.resize(s + 1);
		// Recall that position 0 of satellite is unused
		satellite.resize(s + 2);
	}
	// If satellite is already in the heap
	else if (pos[s] != -1) {
		SMTRAT_LOG_ERROR("smtrat.cadcells.representation", "Error: satellite already in heap");
	}

	int i;
	for (i = ++size; i / 2 > 0 && GREATER(key[satellite[i / 2]], k); i /= 2) {
		satellite[i] = satellite[i / 2];
		pos[satellite[i]] = i;
	}
	satellite[i] = s;
	pos[s] = i;
	key[s] = k;
}

inline int BinaryHeap::Size() {
	return size;
}

inline int BinaryHeap::DeleteMin() {
	if (size == 0)
		SMTRAT_LOG_ERROR("smtrat.cadcells.representation", "Error: empty heap");

	int min = satellite[1];
	int slast = satellite[size--];

	int child;
	int i;
	for (i = 1, child = 2; child <= size; i = child, child *= 2) {
		if (child < size && GREATER(key[satellite[child]], key[satellite[child + 1]]))
			child++;

		if (GREATER(key[slast], key[satellite[child]])) {
			satellite[i] = satellite[child];
			pos[satellite[child]] = i;
		} else
			break;
	}
	satellite[i] = slast;
	pos[slast] = i;

	pos[min] = -1;

	return min;
}

} // namespace smtrat::cadcells::representation::util
