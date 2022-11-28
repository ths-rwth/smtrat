namespace smtrat::fmplex::gauss {

class FMPlexGauss : Gauss {
    private:


    public:
    void init(const FormulasT& constraints, const std::map<carl::Variable, std::size_t>& variable_index) override {

    }

    void apply_gaussian_elimination() override {

    }

    FMPlexTableau get_transformed_inequalities() override {
        
    }
};

} // namespace smtrat::fmplex::gauss