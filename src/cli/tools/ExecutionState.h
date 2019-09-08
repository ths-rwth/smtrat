#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/model.h>

namespace smtrat {
namespace execution {

enum Mode {
    START=0, ASSERT=1, SAT=2, UNSAT=3
};


struct Assertion {
    FormulaT formula;
};
struct SoftAssertion {
    FormulaT formula;
    Rational weight;
    std::string id;
};
struct Objective {
    Poly function;
    bool minimize;
};
    
class ExecutionState {
    Mode mMode;

    carl::Logic mLogic;

    std::vector<Assertion> mAssertions;
    std::vector<SoftAssertion> mSoftAssertions;
    std::vector<Objective> mObjectives;
    std::vector<std::pair<FormulaT, std::string>> mAnnotatedNames;
    std::vector<std::tuple<size_t,size_t,size_t,size_t>> mBacktrackPoints;

    smtrat::Model mModel;
    smtrat::ObjectiveValues mObjectiveValues;


    std::function<void (const FormulaT&)> addAssertionHandler;
    std::function<void (const FormulaT&, Rational, const std::string&)> addSoftAssertionHandler;
    std::function<void (const Poly&, bool)> addObjectiveHandler;
    std::function<void (const FormulaT&, const std::string&)> addAnnotatedNameHandler;
    std::function<void (const FormulaT&)> removeAssertionHandler;
    std::function<void (const FormulaT&)> removeSoftAssertionHandler;
    std::function<void (const Poly&)> removeObjectiveHandler;
    std::function<void (const FormulaT&)> removeAnnotatedNameHandler;

    void set_mode(Mode mode) {
        mMode = mode;
    }

public:
    ExecutionState() : mMode(Mode::START) {}

    void set_add_assertion_handler(std::function<void (const FormulaT&)> f) { addAssertionHandler = f; }
    void set_add_soft_assertion_handler(std::function<void (const FormulaT&, Rational, const std::string&)> f) { addSoftAssertionHandler = f; }
    void set_add_objective_handler(std::function<void (const Poly&, bool)> f) { addObjectiveHandler = f; }
    void set_add_annotated_name_handler(std::function<void (const FormulaT&, const std::string&)> f) { addAnnotatedNameHandler = f; }
    void set_remove_assertion_handler(std::function<void (const FormulaT&)> f) { removeAssertionHandler = f; }
    void set_remove_soft_assertion_handler(std::function<void (const FormulaT&)> f) { removeSoftAssertionHandler = f; }
    void set_remove_objective_handler(std::function<void (const Poly&)> f) { removeObjectiveHandler = f; }
    void set_remove_annotated_name_handler(std::function<void (const FormulaT&)> f) { removeAnnotatedNameHandler = f; }

    
    bool is_mode(Mode mode) const {
        return mMode == mode;
    }

    void set_logic(carl::Logic logic) {
        assert(is_mode(Mode::START));
        mLogic = logic;
        set_mode(Mode::ASSERT);
    }
    auto logic() const {
        return mLogic;
    }

    void add_assertion(const FormulaT& formula) {
        reset_answer();
        assert(is_mode(Mode::ASSERT));

        // we do not try to resolve any conflict between assertions and soft assertions as the
        // semantic is ambiguous and there is no standard
        assert(!has_assertion(formula));
        assert(!has_soft_assertion(formula));
        mAssertions.push_back({formula});
        addAssertionHandler(formula);
    }

    bool has_assertion(const FormulaT& formula) const {
        return std::find_if(mAssertions.begin(), mAssertions.end(), [&formula](const Assertion& a) { return a.formula == formula; } ) != mAssertions.end();
    }

    const auto& assertions() const {
        return mAssertions;
    }

    void add_soft_assertion(const FormulaT& formula, Rational weight, const std::string& id) {
        reset_answer();
        assert(is_mode(Mode::ASSERT));

        // we do not try to resolve any conflict between assertions and soft assertions as the
        // semantic is ambiguous and there is no standard
        assert(!has_assertion(formula));
        assert(!has_soft_assertion(formula));
        mSoftAssertions.push_back({formula, weight, id});
        addSoftAssertionHandler(formula, weight, id);
    }
    
    bool has_soft_assertion(const FormulaT& formula) const {
        return std::find_if(mSoftAssertions.begin(), mSoftAssertions.end(), [&formula](const SoftAssertion& a) { return a.formula == formula; } ) != mSoftAssertions.end();
    }

    void add_objective(const Poly& function, bool minimize) {
        if (is_mode(Mode::SAT) || is_mode(Mode::UNSAT)) {
            reset_answer();
        }
        assert(is_mode(Mode::ASSERT));

        assert(!has_objective(function));
        mObjectives.push_back({function, minimize});
        addObjectiveHandler(function, minimize);
    }

    bool has_objective(const Poly& function) {
        return std::find_if(mObjectives.begin(), mObjectives.end(), [&function](const Objective& a) { return a.function == function; }) != mObjectives.end(); 
    }

    void push() {
        reset_answer();
        assert(is_mode(Mode::ASSERT));

        mBacktrackPoints.emplace_back(mAssertions.size(), mSoftAssertions.size(), mObjectives.size(), mAnnotatedNames.size());
    }
    void push(size_t n) {
        for (size_t i = 0; i < n; i++) push();
    }
    void pop() {
        reset_answer();
        assert(is_mode(Mode::ASSERT));

        if (mBacktrackPoints.empty()) return;

        assert(std::get<0>(mBacktrackPoints.back()) <= mAssertions.size());
        assert(std::get<1>(mBacktrackPoints.back()) <= mSoftAssertions.size());
        assert(std::get<2>(mBacktrackPoints.back()) <= mObjectives.size());
        assert(std::get<3>(mBacktrackPoints.back()) <= mAnnotatedNames.size());

        for (size_t i = mAssertions.size()-1; i >= std::get<0>(mBacktrackPoints.back()) ; i--) {
            removeAssertionHandler(mAssertions[i].formula);
        }
        for (size_t i = mSoftAssertions.size()-1; i >= std::get<1>(mBacktrackPoints.back()) ; i--) {
            removeSoftAssertionHandler(mSoftAssertions[i].formula);
        }
        for (size_t i = mObjectives.size()-1; i >= std::get<2>(mBacktrackPoints.back()) ; i--) {
            removeObjectiveHandler(mObjectives[i].function);
        }
        for (size_t i = mAnnotatedNames.size()-1; i >= std::get<3>(mBacktrackPoints.back()) ; i--) {
            removeAnnotatedNameHandler(mAnnotatedNames[i].first);
        }

        mAssertions.erase(mAssertions.begin() + std::get<0>(mBacktrackPoints.back()), mAssertions.end());
        mSoftAssertions.erase(mSoftAssertions.begin() + std::get<1>(mBacktrackPoints.back()), mSoftAssertions.end());
        mObjectives.erase(mObjectives.begin() + std::get<2>(mBacktrackPoints.back()), mObjectives.end());
        mAnnotatedNames.erase(mAnnotatedNames.begin() + std::get<3>(mBacktrackPoints.back()), mAnnotatedNames.end());

        mBacktrackPoints.pop_back();
    }
    void pop(size_t n) {
        for (size_t i = 0; i < n; i++) pop();
    }

    bool has_annotated_name(const std::string& n) {
        return std::find_if(mAnnotatedNames.begin(), mAnnotatedNames.end(), [&n](const auto& a) { return a.second == n; }) != mAnnotatedNames.end();
    }

    bool has_annotated_name_formula(const smtrat::FormulaT& f) {
        return std::find_if(mAnnotatedNames.begin(), mAnnotatedNames.end(), [&f](const auto& a) { return a.first == f; }) != mAnnotatedNames.end();
    }

    void annotate_name(const std::string& name, const smtrat::FormulaT& f) {
        reset_answer();
        assert(is_mode(Mode::ASSERT));

        assert(!has_annotated_name(name));
        assert(!has_annotated_name_formula(f));
        mAnnotatedNames.emplace_back(f, name);
        addAnnotatedNameHandler(f, name);
    }

    void enter_sat(const smtrat::Model& model, const ObjectiveValues& objectiveValues) {
        reset_answer();
        assert(is_mode(Mode::ASSERT));
        mModel = model;
        mObjectiveValues = objectiveValues;
        set_mode(Mode::SAT);
    }

    void enter_unsat() {
        reset_answer();
        assert(is_mode(Mode::ASSERT));
        set_mode(Mode::UNSAT);
    }

    const smtrat::Model& model() const {
        assert(is_mode(Mode::SAT));
        return mModel;
    }

    const smtrat::ObjectiveValues& objectiveValues() const {
        assert(is_mode(Mode::SAT));
        return mObjectiveValues;
    }

    void reset() {
        if (!is_mode(Mode::START)) {
            mLogic = carl::Logic::UNDEFINED;
            if (is_mode(Mode::SAT) || is_mode(Mode::UNSAT) || is_mode(Mode::ASSERT)) {
                reset_answer();
                mAssertions.clear();
                mSoftAssertions.clear();
                mObjectives.clear();
                mBacktrackPoints.clear();
                mAnnotatedNames.clear();
            }
            set_mode(Mode::START);
        }
    }

    void reset_assertions() {
        if (!is_mode(Mode::START)) {
            while (!mBacktrackPoints.empty()) pop();
            mBacktrackPoints.emplace_back(0,0,0,0);
            pop();
            assert(is_mode(Mode::ASSERT));
        }
    }

    void reset_answer() {
        if (is_mode(Mode::SAT) || is_mode(Mode::UNSAT)) {
            mModel.clear();
            mObjectiveValues.clear();
            set_mode(Mode::ASSERT);
        }
    }


};

}
}