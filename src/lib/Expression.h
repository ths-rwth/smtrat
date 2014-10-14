/**
 * @file Expression.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <boost/variant.hpp>
#include "Sort.h"
#include "Formula.h"

namespace smtrat {

    class NewExpressionType 
    {
        std::string name;
        Sort codomain;
        std::vector<Sort> domain;
    };

    class Expression 
    {
        
    private:

        struct ExpressionContent 
        {
            NewExpressionType et;
            std::vector<Expression> children;
            
            ExpressionContent(const NewExpressionType& et, const std::vector<Expression>& children):
                et(et), 
                children(children) 
            {}
        };

        struct IsFormula: public boost::static_visitor<bool> 
        {
            bool operator()(const Formula*) const { return true; }
            bool operator()(const Polynomial&) const { return false; }
            bool operator()(const ExpressionContent&) const { return false; }
        };
        
        struct IsPolynomial: public boost::static_visitor<bool> 
        {
            bool operator()(const Formula*) const { return false; }
            bool operator()(const Polynomial&) const { return true; }
            bool operator()(const ExpressionContent&) const { return false; }
        };
        
        struct IsExpression: public boost::static_visitor<bool> 
        {
            bool operator()(const Formula*) const { return false; }
            bool operator()(const Polynomial&) const { return false; }
            bool operator()(const ExpressionContent&) const { return true; }
        };

        boost::variant<const Formula*, Polynomial, ExpressionContent> mContent;

    public:
        
        Expression() {}

        Expression(const Expression& ex) 
        {
            mContent = ex.mContent;
        }

        Expression(bool value) 
        {
            if (value) 
                mContent = trueFormula();
            else 
                mContent = falseFormula();
        }

        Expression(const Rational& r) 
        {
            mContent = Polynomial(r);
        }

        Expression(carl::Variable::Arg v) 
        {
            if (v.getType() == carl::VariableType::VT_BOOL) 
            {
                mContent = newVariableFormula(v);
            }
            else 
            {
                mContent = Polynomial(v);
            }
        }

        Expression(const std::string& op, const Expression& ex) 
        {
            if (ex.isPolynomial()) 
            {
                if (op == "-") 
                    mContent = -ex.asPolynomial();
            }
            if (ex.isFormula()) 
            {
                if (op == "not") 
                    mContent = smtrat::newNegation(ex.asFormula());
            }
            if (mContent.empty()) 
            {
                mContent = ExpressionContent(NewExpressionType(), {ex});
            }
        }

        Expression(const std::string& op, const Expression& lhs, const Expression& rhs) 
        {
            if (lhs.isPolynomial() && rhs.isPolynomial()) 
            {
                if (op == "+") 
                    mContent = lhs.asPolynomial() + rhs.asPolynomial();
                else if (op == "-") 
                    mContent = lhs.asPolynomial() - rhs.asPolynomial();
                else if (op == "*") 
                    mContent = lhs.asPolynomial() * rhs.asPolynomial();
                else if (op == "/") 
                    mContent = lhs.asPolynomial() / rhs.asPolynomial();
            }
            if (lhs.isFormula() && rhs.isFormula()) 
            {
                if (op == "or") 
                    mContent = smtrat::newFormula(smtrat::OR, lhs.asFormula(), rhs.asFormula());
                else if (op == "and") 
                    mContent = smtrat::newFormula(smtrat::AND, lhs.asFormula(), rhs.asFormula());
            }
            if (mContent.empty()) 
            {
                mContent = ExpressionContent(NewExpressionType(), {ex});
            }
        }

        bool isFormula() const 
        {
            return boost::apply_visitor(IsFormula(), mContent);
        }

        bool isPolynomial() const 
        {
            return boost::apply_visitor(IsPolynomial(), mContent);
        }

        bool isExpression() const 
        {
            return boost::apply_visitor(IsExpression(), mContent);
        }

        const Formula* asFormula() const 
        {
            return boost::get<const Formula*>(mContent);
        }

        Polynomial asPolynomial() const 
        {
            return boost::get<Polynomial>(mContent);
        }

        ExpressionContent asExpression() const 
        {
            return boost::get<ExpressionContent>(mContent);
        }
    };
} // end namespace smtrat