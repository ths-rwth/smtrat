#pragma once

#include <vector>

#include <carl-formula/formula/Formula.h>
#include <carl-arith/poly/umvpoly/MultivariatePolynomial.h>

#include <eigen3/Eigen/Core>
#include <eigen3/Eigen/Dense>
#include <eigen3/Eigen/StdVector>

#include "fmplex.h"

namespace smtrat::fmplex {

using Formula  = carl::Formula<carl::MultivariatePolynomial<Rational>>;
using EigenMat = Eigen::Matrix<Rational, Eigen::Dynamic, Eigen::Dynamic>;
using EigenVec = Eigen::Matrix<Rational, Eigen::Dynamic, 1>;

Formula eliminate_variables(const Formula& f, const std::vector<carl::Variable>& vars);

std::pair<EigenMat, EigenVec> eliminate_cols(const EigenMat& constraints,
                                             const EigenVec& constants,
                                             const std::vector<std::size_t>& cols);

void write_matrix_to_ine(const EigenMat& constraints, const EigenVec& constants,
                         const std::vector<std::size_t>& cols, const std::string& filename);

}