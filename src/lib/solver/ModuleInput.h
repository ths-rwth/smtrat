/**
 * @file ModuleInput.h
 * @author Florian Corzilius
 * @version 2014-05-16
 */

#pragma once


#include <algorithm>
#include <list>
#include <vector>
#include <set>
#include <iterator>
#include "../Common.h"
#include "../config.h"

namespace smtrat
{
    /// Stores a formula along with its origins.
    class FormulaWithOrigins
    {
        friend class ModuleInput;
        // Member
        
        /// The formula.
        FormulaT mFormula;
        /// The formulas origins.
        std::shared_ptr<FormulasT> mOrigins;
        /// The deduction flag, which indicates, that this formula g is a direct sub-formula of
        /// a conjunction of formulas (and g f_1 .. f_n), and, that (implies (and f_1 .. f_n) g) holds.
        mutable bool mDeducted;
        
    public:
        
        FormulaWithOrigins(); // Default constructor disabled.
        
        /**
         * Constructs a formula with empty origins.
         * @param _formula The formula of the formula with origins to construct.
         */
        FormulaWithOrigins( const FormulaT& _formula ):
            mFormula( _formula ),
            mOrigins(nullptr),
            mDeducted( false )
        {}
        
        /**
         * Constructs a formula with the given origins.
         * @param _formula The formula of the formula with origins to construct.
         * @param _origins The origins of the formula with origins to construct.
         */
        FormulaWithOrigins( const FormulaT& _formula, const std::shared_ptr<FormulasT>& _origins ):
            mFormula( _formula ),
            mOrigins( _origins ),
            mDeducted( false )
        {}
        
        FormulaWithOrigins( const FormulaWithOrigins& ); // Copy constructor disabled.
        
        /**
         * @param _fwoA The first formula with origins to compare.
         * @param _fwoB The second formula with origins to compare.
         * @return true, if the formula of the first formula with origins is less than the formula of the second formula with origins;
         *         false, otherwise.
         */
        friend bool operator<( const FormulaWithOrigins& _fwoA, const FormulaWithOrigins& _fwoB )
        {
            return _fwoA.formula() < _fwoB.formula();
        }
        
        /**
         * @param _fwoA The first formula with origins to compare.
         * @param _fwoB The second formula with origins to compare.
         * @return true, if the formula of the first formula with origins and the formula of the second formula with origins are equal;
         *         false, otherwise.
         */
        friend bool operator==( const FormulaWithOrigins& _fwoA, const FormulaWithOrigins& _fwoB )
        {
            return _fwoA.formula() == _fwoB.formula();
        }
        
        /**
         * @return A constant reference to the formula.
         */
        const FormulaT& formula() const
        {
            return mFormula;
        }
        
        /**
         * @return true, if this sub-formula of the module input has origins.
         */
        bool hasOrigins() const
        {
            return mOrigins != nullptr;
        }
        
        /**
         * @return A constant reference to the origins.
         */
        const FormulasT& origins() const
        {
            return *mOrigins;
        }

        /**
         * Sets the deduction flag to the given value.
         * @param _deducted The value to set the deduction flag to.
         */
        void setDeducted( bool _deducted ) const
        {
            mDeducted = _deducted;
        }

        /**
         * @return The deduction flag, which indicates, that this formula g is a direct sub-formula of
         *          a conjunction of formulas (and g f_1 .. f_n), and, that (implies (and f_1 .. f_n) g) holds.
         */
        bool deducted() const
        {
            return mDeducted;
        }
    };
    
    /**
     * The input formula a module has to consider for it's satisfiability check. It is a list of formulas
     * and semantically considered as their conjunction.
     */
    class ModuleInput : private std::list<FormulaWithOrigins>
    {
        friend class Module;
        
        friend class Manager;
        
    private:
        
        typedef std::list<FormulaWithOrigins> super;
        
        
    public:
            
        /// Passing through the list::iterator.
        typedef super::iterator iterator;
        /// Passing through the list::const_iterator.
        typedef super::const_iterator const_iterator;
        
    private:
        
        // Member.
        /// Store some properties about the conjunction of the stored formulas.
        carl::Condition mProperties;
        /// A flag indicating whether the properties of this module input are updated.
        bool mPropertiesUpdated;
        /// Maps all formulas occurring (in the origins) at pos i in this module input to i. This is for a faster access.
        carl::FastMap<FormulaT,iterator> mFormulaPositionMap;
        
    public:
            
        /**
         * Constructs a module input.
         */
        ModuleInput(): 
            std::list<FormulaWithOrigins>(),
            mProperties(),
            mPropertiesUpdated(false),
            mFormulaPositionMap()
        {}
        
        // Methods.
        
        /**
         * @return All known properties of the underlying formula of this module input.
         */
        carl::Condition properties() const
        {
            assert( mPropertiesUpdated );
            return mProperties;
        }
        
        /**
         * @return true, if this formula is a conjunction of constraints;
         *         false, otherwise.
         */
        bool isConstraintConjunction() const
        {
            if( carl::PROP_IS_PURE_CONJUNCTION <= mProperties )
                return !(carl::PROP_CONTAINS_BOOLEAN <= mProperties) && !(carl::PROP_CONTAINS_UNINTERPRETED_EQUATIONS <= mProperties);
            else
                return false;
        }
        
        /**
         * @return true, if this formula is a conjunction of literals of constraints;
         *         false, otherwise.
         */
        bool isConstraintLiteralConjunction() const
        {
            if( carl::PROP_IS_LITERAL_CONJUNCTION <= mProperties )
                return !(carl::PROP_CONTAINS_BOOLEAN <= mProperties) && !(carl::PROP_CONTAINS_UNINTERPRETED_EQUATIONS <= mProperties);
            else
                return false;
        }

        /**
         * @return true, if this formula is a conjunction of real constraints;
         *         false, otherwise.
         */
        bool isRealConstraintConjunction() const
        {
            return isConstraintConjunction() && !(carl::PROP_CONTAINS_INTEGER_VALUED_VARS <= mProperties) && !(carl::PROP_CONTAINS_PSEUDOBOOLEAN <= mProperties);
        }

        /**
         * @return true, if this formula is a conjunction of literals of real constraints;
         *         false, otherwise.
         */
        bool isRealConstraintLiteralConjunction() const
        {
            return isConstraintLiteralConjunction() && !(carl::PROP_CONTAINS_INTEGER_VALUED_VARS <= mProperties);
        }

        /**
         * @return true, if this formula is a conjunction of integer constraints;
         *         false, otherwise.
         */
        bool isIntegerConstraintConjunction() const
        {
            return isConstraintConjunction() && !(carl::PROP_CONTAINS_REAL_VALUED_VARS <= mProperties);
        }

        /**
         * @return true, if this formula is a conjunction of literals of integer constraints;
         *         false, otherwise.
         */
        bool isIntegerConstraintLiteralConjunction() const
        {
            return isConstraintLiteralConjunction() && !(carl::PROP_CONTAINS_REAL_VALUED_VARS <= mProperties);
        }

        /**
         * @return true, if this formula contains bit vector constraints;
         *         false, otherwise.
         */
        bool containsBitVectorConstraints() const
        {
            return carl::PROP_CONTAINS_BITVECTOR <= mProperties;
        }

        /**
         * @return true, if this formula contains Boolean variables;
         *         false, otherwise.
         */
        bool containsBooleanVariables() const
        {
            return carl::PROP_CONTAINS_BOOLEAN <= mProperties;
        }

        /**
         * @return true, if this formula contains Boolean variables;
         *         false, otherwise.
         */
        bool containsRealVariables() const
        {
            return carl::PROP_CONTAINS_REAL_VALUED_VARS <= mProperties;
        }

        /**
         * @return true, if this formula contains Boolean variables;
         *         false, otherwise.
         */
        bool containsIntegerVariables() const
        {
            return carl::PROP_CONTAINS_INTEGER_VALUED_VARS <= mProperties;
        }

        /**
         * @return true, if this formula contains uninterpreted equations;
         *         false, otherwise.
         */
        bool containsUninterpretedEquations() const
        {
            return carl::PROP_CONTAINS_UNINTERPRETED_EQUATIONS <= mProperties;
        }
        
        /**
         * @return true, if this formula is propositional;
         *         false, otherwise.
         */
        bool isOnlyPropositional() const
        {
            return !(carl::PROP_CONTAINS_BITVECTOR <= mProperties) 
                && !(carl::PROP_CONTAINS_UNINTERPRETED_EQUATIONS <= mProperties)
                && !(carl::PROP_CONTAINS_INTEGER_VALUED_VARS <= mProperties)
                && !(carl::PROP_CONTAINS_REAL_VALUED_VARS <= mProperties)
                && !(carl::PROP_CONTAINS_PSEUDOBOOLEAN <= properties());
        }
        
        /**
         * @param _assignment The model to check conjunction of the stored formulas against.
         * @return 1, if the conjunction of the stored formulas is satisfied by the given model;
         *         0, if the given model conflicts the conjunction of the stored formulas;
         *         2, if it cannot be determined cheaply, whether the given model conflicts or satisfies 
         *            the conjunction of the stored formulas.
         */
        unsigned satisfiedBy( const Model& _assignment ) const;
        
        /**
         * @param _assignment The assignment to check conjunction of the stored formulas against.
         * @return 1, if the conjunction of the stored formulas is satisfied by the given assignment;
         *         0, if the given assignment conflicts the conjunction of the stored formulas;
         *         2, if it cannot be determined cheaply, whether the given assignment conflicts or satisfies 
         *            the conjunction of the stored formulas.
         */
        unsigned satisfiedBy( const EvalRationalMap& _assignment ) const;

		const auto& back() const {
			return super::back();
		}
        
        iterator begin()
        {
            return super::begin();
        }
        
        iterator end()
        {
            return super::end();
        }
        
        const_iterator begin() const
        {
            return super::begin();
        }
        
        const_iterator end() const
        {
            return super::end();
        }

        auto rbegin() const {
            return super::rbegin();
        }
        
        auto rend() const {
            return super::rend();
        }
        
        bool empty() const
        {
            return super::empty();
        }
        
        size_t size() const
        {
            return super::size();
        }
        
        iterator find( const FormulaT& _formula );
        
        const_iterator find( const FormulaT& _formula ) const;
        
        iterator find( const_iterator _hint, const FormulaT& _formula );
        
        const_iterator find( const_iterator _hint, const FormulaT& _formula ) const;
        
        /**
         * @param _subformula The formula for which to check whether it is one of the stored formulas.
         * @return true, if the given formula is one of the stored formulas;
         *         false, otherwise.
         */
        bool contains( const FormulaT& _subformula ) const
        {
            return mFormulaPositionMap.find( _subformula ) != mFormulaPositionMap.end();
        }
        
        /**
         * Updates all properties of the formula underlying this module input.
         */
        void updateProperties();

		void gatherVariables(carl::carlVariables& vars) const {
			for (const auto& f: *this) {
				f.formula().gatherVariables(vars);
			}
		}
        
        /**
         * Collects all variables occurring in this formula.
         * @param _vars The container to collect the variables in.
         */
		[[deprecated("Use gatherVariables() instead.")]]
        void vars( carl::Variables& _vars ) const
        {
            for( const FormulaWithOrigins& fwo : *this )
                fwo.formula().allVars( _vars );
        }
        
        /**
         * Collects all real valued variables occurring in this formula.
         * @param _realVars The container to collect the real valued variables in.
         */
		[[deprecated("Use gatherVariables() instead.")]]
        void realValuedVars( carl::Variables& _realVars ) const
        {
            for( const FormulaWithOrigins& fwo : *this )
                fwo.formula().realValuedVars( _realVars );
        }

        /**
         * Collects all integer valued variables occurring in this formula.
         * @param _intVars The container to collect the integer valued variables in.
         */
		[[deprecated("Use gatherVariables() instead.")]]
        void integerValuedVars( carl::Variables& _intVars ) const
        {
            for( const FormulaWithOrigins& fwo : *this )
                fwo.formula().integerValuedVars( _intVars );
        }

        /**
         * Collects all arithmetic variables occurring in this formula.
         * @param _arithmeticVars The container to collect the arithmetic variables in.
         */
		[[deprecated("Use gatherVariables() instead.")]]
        void arithmeticVars( carl::Variables& _arithmeticVars ) const
        {
            for( const FormulaWithOrigins& fwo : *this )
                fwo.formula().arithmeticVars( _arithmeticVars );
        }

        /**
         * Collects all Boolean variables occurring in this formula.
         * @param _booleanVars The container to collect the Boolean variables in.
         */
		[[deprecated("Use gatherVariables() instead.")]]
        void booleanVars( carl::Variables& _booleanVars ) const
        {
            for( const FormulaWithOrigins& fwo : *this )
                fwo.formula().booleanVars( _booleanVars );
        }
        
        struct IteratorCompare
        {
            bool operator() ( const_iterator i1, const_iterator i2 ) const
            {
                return (*i1) < (*i2);
            }
        };
        
        /**
         * @return The string representation of this module input.
         */
        std::string toString() const
        {
            std::stringstream ss;
			ss << "(and";
            for(const auto& fwo : *this )
                ss << " " << fwo.formula();
            ss << ")";
            return ss.str();
        }
        
        explicit operator FormulaT() const
        {
            FormulasT subFormulas;
            for( auto& fwo : *this )
                subFormulas.push_back( fwo.formula() );
            return FormulaT( carl::FormulaType::AND, subFormulas );
        }
        
        void addOrigin( iterator _formula, const FormulaT& _origin )
        {
            assert( _formula != end() );
            if( !_formula->hasOrigins() )
            {
                _formula->mOrigins = std::shared_ptr<FormulasT>( new FormulasT() );
            }
            _formula->mOrigins->push_back( _origin );
        }
        
        // @todo: we want a const_iterator here, but gcc 4.8 doesn't allow us :( even though it should
        iterator erase( iterator _formula );
        
        void clearOrigins( iterator _formula )
        {
            assert( _formula != end() );
            if( _formula->hasOrigins() )
            {
                _formula->mOrigins = nullptr;
            }
        }
        
        bool removeOrigin( iterator _formula, const FormulaT& _origin );
        
        bool removeOrigins( iterator _formula, const std::shared_ptr<FormulasT>& _origins );
        
        std::pair<iterator,bool> add( const FormulaT& _formula, bool _mightBeConjunction = true )
        {
            return add( _formula, false, FormulaT( carl::FormulaType::FALSE ), nullptr, _mightBeConjunction );
        }
        
        std::pair<iterator,bool> add( const FormulaT& _formula, const FormulaT& _origins, bool _mightBeConjunction = true )
        {
            return add( _formula, true, _origins, nullptr, _mightBeConjunction );
        }
        
        std::pair<iterator,bool> add( const FormulaT& _formula, const std::shared_ptr<FormulasT>& _origins, bool _mightBeConjunction = true )
        {
            return add( _formula, false, FormulaT( carl::FormulaType::FALSE ), _origins, _mightBeConjunction );
        }
        
        std::pair<iterator,bool> add( const FormulaT& _formula, bool _hasSingleOrigin, const FormulaT& _origin, const std::shared_ptr<FormulasT>& _origins, bool _mightBeConjunction = true );
    };

	inline std::ostream& operator<<(std::ostream& os, const ModuleInput& mi) {
		os << "(and";
		for (const auto& fwo : mi) os << " " << fwo.formula();
		os << ")";
		return os;
	}
    
    template<typename AnnotationType>
    void annotateFormula( const FormulaT&, const std::vector<AnnotationType>& );
}    // namespace smtrat
