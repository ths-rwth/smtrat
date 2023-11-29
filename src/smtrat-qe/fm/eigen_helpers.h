#include <smtrat-common/smtrat-common.h>

#include <eigen3/Eigen/Core>
#include <eigen3/Eigen/Dense>
#include <eigen3/Eigen/StdVector>

namespace smtrat::qe::fm {

using vector_t = Eigen::Matrix<Rational, Eigen::Dynamic, 1>;
using matrix_t = Eigen::Matrix<Rational, Eigen::Dynamic, Eigen::Dynamic>;


matrix_t selectRows(const matrix_t &original, const std::vector<std::size_t> &rowIndices) {
    matrix_t res = matrix_t(rowIndices.size(), original.cols());
    for (Eigen::Index index = 0; index < res.rows(); index++) {
        res.row(index) = original.row(Eigen::Index(rowIndices[index]));
    }
    return res;
}


matrix_t removeRows(const matrix_t &original, const std::vector<std::size_t> &rowIndices) {
    // compute all rows that need to remain, select those.
    std::vector<std::size_t> remainingRows;
    for (Eigen::Index i = 0; i < original.rows(); ++i) {
        if (std::find(rowIndices.begin(), rowIndices.end(), std::size_t(i)) == rowIndices.end()) {
            remainingRows.emplace_back(i);
        }
    }
    return selectRows(original, remainingRows);
}

matrix_t &appendRow(matrix_t &original, const vector_t &row) {
    assert(row.rows() == original.cols());
    original.conservativeResize(original.rows() + 1, original.cols());
    original.row(original.rows() - 1) = row;
    return original;
}

matrix_t &concatenateVertically(matrix_t &original, const matrix_t &other) {
    assert(original.cols() == other.cols());
    Eigen::Index originalRowCount = original.rows();
    original.conservativeResize(original.rows() + other.rows(), original.cols());
    original.block(originalRowCount, 0, other.rows(), other.cols()) = other;
    return original;
}

vector_t &concatenateVertically(vector_t &original, const vector_t &other) {
    Eigen::Index originalRowCount = original.rows();
    original.conservativeResize(original.rows() + other.rows(), original.cols());
    original.block(originalRowCount, 0, other.rows(), other.cols()) = other;
    return original;
}

vector_t &appendRow(vector_t &original, Rational entry) {
    original.conservativeResize(original.rows() + 1);
    original(original.rows() - 1) = entry;
    return original;
}

/**
 * @brief Append a specified number of zeroes at the end of a vector_t
 * @tparam Number The used number type
 * @param original The original vector
 * @param numberZeroes The number of zeroes that should be appended to original
 * @return A reference to the updated vector_t
 */
vector_t appendZeroes(vector_t &original, std::size_t numberZeroes) {
    auto oldSize = original.rows();
    original.conservativeResize(original.rows() + numberZeroes);
    original.block(oldSize, 0, 1, numberZeroes) = vector_t::Zero(numberZeroes);
    return original;
}


vector_t selectRows(const vector_t &original, const std::vector<std::size_t> &rowIndices) {
    vector_t res = vector_t(rowIndices.size());
    for (Eigen::Index index = 0; index < res.rows(); index++) {
        res(index) = original(Eigen::Index(rowIndices[index]));
    }
    return res;
}


vector_t removeRows(const vector_t &original, const std::vector<std::size_t> &rowIndices) {
    return vector_t(removeRows(matrix_t(original), rowIndices));
}


matrix_t removeCol(const matrix_t &original, std::size_t colIndex) {
    if (colIndex == 0) {
        return original.block(0, 1, original.rows(), original.cols() - 1);
    }
    if (Eigen::Index(colIndex) == original.cols() - 1) {
        return original.block(0, 0, original.rows(), original.cols() - 1);
    }
    matrix_t res = matrix_t(original.rows(), original.cols() - 1);
    res.block(0, 0, original.rows(), colIndex) = original.leftCols(colIndex);
    res.block(0, colIndex, original.rows(), original.cols() - (colIndex + 1)) = original.rightCols(
            original.cols() - (colIndex + 1));
    return res;
}


matrix_t selectCols(const matrix_t &original, const std::vector<std::size_t> &colIndices) {
    matrix_t res = matrix_t(original.rows(), Eigen::Index(colIndices.size()));
    for (Eigen::Index index = 0; index < res.cols(); index++) {
        res.col(index) = original.col(Eigen::Index(colIndices[index]));
    }
    return res;
}

static matrix_t combine(
        const matrix_t &lhsMatrix, const matrix_t &rhsMatrix,
        const std::vector<std::string> &haVar, const std::vector<std::string> &lhsVar,
        const std::vector<std::string> &rhsVar) {
    Eigen::Index lhsRows = lhsMatrix.rows();
    Eigen::Index rhsRows = rhsMatrix.rows();
    matrix_t tmpMatrix = matrix_t::Zero(lhsRows + rhsRows, haVar.size());

    size_t col = 0;
    unsigned colLhs = 0;
    while (colLhs < lhsMatrix.cols()) {
        if (haVar[col] == lhsVar[colLhs]) {
            tmpMatrix.block(0, col, lhsRows, 1) = lhsMatrix.block(0, colLhs, lhsRows, 1);
            col++;
            colLhs++;
            continue;
        }
        if (haVar[col] < lhsVar[colLhs]) {
            col++;
            continue;
        }
    }

    col = 0;
    unsigned colRhs = 0;
    while (colRhs < rhsMatrix.cols()) {
        if (haVar[col] == rhsVar[colRhs]) {
            tmpMatrix.block(lhsRows, col, rhsRows, 1) = rhsMatrix.block(0, colRhs, rhsRows, 1);
            col++;
            colRhs++;
            continue;
        }
        if (haVar[col] < rhsVar[colRhs]) {
            col++;
            continue;
        }
    }
    return tmpMatrix;
}

static vector_t combine(const vector_t &lhs, const vector_t &rhs) {
    vector_t newVec = vector_t::Zero(lhs.size() + rhs.size());
    newVec.head(lhs.size()) = lhs;
    newVec.tail(rhs.size()) = rhs;

    return newVec;
}

// interprets all vectors as row-vectors and creates a matrix
static matrix_t createMatrix(const std::vector<vector_t> &_in) {
    if (_in.empty()) {
        return matrix_t(0, 0);
    }
    matrix_t res = matrix_t(_in.size(), _in.begin()->rows());

    Eigen::Index rowCount = 0;
    for (const auto &r: _in) {
        assert(r.rows() == res.cols());
        res.row(rowCount) = r;
        ++rowCount;
    }

    return res;
}

static vector_t createVector(const std::vector<Rational> &_in) {
    if (_in.empty()) {
        return vector_t(0);
    }
    vector_t result(_in.size());
    for (unsigned rowId = 0; rowId != _in.size(); ++rowId) {
        result(rowId) = Rational(_in[rowId]);
    }
    return result;
}


}