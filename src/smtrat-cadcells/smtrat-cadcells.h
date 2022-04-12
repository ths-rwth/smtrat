namespace smtrat {

/**
 * @brief A framework for sample-based CAD algorithms. 
 * 
 * This is a highly modular framework for sample-based CAD algorithms, i.e. single cell construction and coverings.
 * 
 * The basic idea is to have properties (of some polynomials or real root functions); each property has a level w.r.t. to a variable ordering (i.e. the index of the main variable of a polynomial) and rules operating on them, each replacing a property by a "simpler" set of properties (eventually reducing the level).
 * At some stage, we delineate properties (that is, ordering the root under a partial sample), determine an ordering and cell boundaries (called representation) to continue proving properties. For more details on the general framework, we refer to the paper.
 * 
 * The structure of this implementation is as follows:
 * 
 * - @ref cadcells::datastructures contains the main datastructures. Read here for more details on the general structure of the framework.
 * - @ref cadcells::operators defines the properties, the rules and methods to delineate properties. These are used by operators which provide an interface for performing projections on certain steps.
 * - @ref cadcells::representation provides heuristics for computing the representations for cells, coverings and delineations.
 * - @ref cadcells::algorithms contains helper methods, building blocks for algorithms as well as algorithms themselves. Go here for usage of the framework and high-level interfaces.
 * 
 * 
 * ## Quick start
 * 
 * For an introduction, we refer to the code of @ref algorithms::onecell.
 *  
 */
namespace cadcells {

/**
 * @brief Main datastructures.
 * 
 * ## Polynomials and projection results
 * We assume a fixed variable ordering @ref VariableOrdering.
 * All polynomials are pooled in @ref PolyPool w.r.t. this ordering, that is, they are identified by a @ref PolyRef (a pair of the polynomial's level and an ID on this level).
 * Projection results are cached in @ref Projections. The latter holds a reference to a @ref PolyPool. An instance @ref Projections will be required for all kinds of operations and passed during various function calls. Thus, we initialize these data structures as follows:
 * 
 *      VariableOrdering vars; // a variable ordering of all variables that will occur.
 *      datastructures::PolyPool pool(vars);
 *      datastructures::Projections proj(pool);
 * 
 * Note that @ref PolyPool and @ref Projections do not do reference counting; the cache needs to be cleared explicitly, see @ref Projections::clear_cache and @ref Projections::clear_assignment_cache.
 * 
 * ## Basic datastructures
 * 
 * The basic datastructures for representing mathematical objects are @ref datastructures::IndexedRoot, @ref datastructures::CellDescription, @ref datastructures::CoveringDescription, and @ref datastructures::IndexedRootOrdering.
 * 
 * ## Properties
 * 
 * @ref datastructures::PropertiesT is the datastructure for storing properties on a single level.
 * 
 * If you work on an algorithm using this framework, you don't need to know this datastructure. If you need to implement a new property, then you find the interfaces a property needs to implement there.
 * 
 * ## Delineations
 * 
 * @ref datastructures::Delineation is the datastructure for storing the delineation of the indexed roots that stem from properties.
 * 
 * If you work on an algorithm using this framework, you don't need to know this datastructure. If you need to implement a new property or a heuristic for describing a cell (i.e. compute a representation), then you might be interested in this.
 * 
 * ## Derivations
 * 
 * In the derivation datastructures, all data regarding the derivation is stored - that is the current sample points, the set of properties, the delineation of roots and the possible cell boundaries.
 * 
 * This datastructure is recursive, that is, each derivation object handles only a single level and holds a pointer to a derivation object of the next lower level (the underyling derivation). All operations are forwarded to lower levels whenever neccessary.
 * 
 * Furthermore, there are three types of derivations: 
 * - @ref datastructures::BaseDerivation assumes no sample point or whatever. It simply stores properties.
 * - @ref datastructures::DelineatedDerivation extends the @ref datastructures::BaseDerivation; it requires that the underlying derivation is a @ref datastructures::SampledDerivation, thus a sample for all lower levels is present under which the properties of the current level can be delineated (i.e. their zeros can be isolated and sorted).
 * - @ref datastructures::SampledDerivation extends the @ref datastructures::DelineatedDerivation, thus a full sample point is available for which a cell can be isolated.
 * The derivation datastructures are thus two-dimensional recursive. Note that multiple derivation objects can have common underlying cells or even share the same base or delineated derivation.
 * 
 * @ref datastructures::DerivationRef allows to reference a derivation independent of its type.
 * 
 * For initializing derivations properly, use @ref datastructures::make_derivation. To create a sampled derivation from a delineated derivation and a sample, use @ref datastructures::make_sampled_derivation. For merging underlying derivations, use @ref datastructures::merge_underlying.
 * 
 * For more information on memory management read @ref datastructures::DerivationRef.
 * 
 * ## Representations
 * 
 * The derivation objects do not store heuristic decisions, they just describe the current state. At some point, a representation of this state needs to be determined that is passed to the operator. This heuristic decision is stored in @ref datastructures::CellRepresentation, @ref datastructures::CoveringRepresentation or @ref datastructures::DelineationRepresentation.
 * 
 * The heuristics for computing representations are in @ref representation.
 * 
 * ## Operators
 * 
 * The @ref operators work on derivations and representations.
 * 
 */
namespace datastructures {
    
}

// docs are in operators/operator.h
namespace operators {
    
}

// docs are in representation/heuristics.h
namespace representation {
    
}

/**
 * Various algorithms as well as helper functions for developing new algorithms.
 */
namespace algorithms {
    
}

}
}