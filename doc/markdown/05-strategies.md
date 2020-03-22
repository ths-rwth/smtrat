# Strategies {#strategies}

To compose modules to a solver, strategies are used.
Strategies are represented as trees of modules where the input file is passed to the root module.
Every module can issue calls to its **backend modules** (via `runBackends`) which then calls its child modules in the strategy on the formula this module has put in the passed formulas.
If no backend module exists, the call returns `unknown`.

A Strategy is specified by deriving from the Manager class and settings its strategy in the constructor using the `setStrategy` member function.
A simple example, supporting only propositional logic, would look like this:

	class PureSAT: public Manager {
		public:
		PureSAT(): Manager() {
			setStrategy(
				addBackend<SATModule<SATSettings1>>()
			);
		}
	};

Each module is added to the strategy tree using `addBackend<Module class>` where the module class is usually a template that is instantiated with some settings.
A slightly more complex, where the SATModule has the NewCADModule available for theory calls, might look as follows:

	class CADOnly: public Manager {
		public:
		CADOnly(): Manager() {
			setStrategy(
				addBackend<SATModule<SATSettings1>>(
					addBackend<NewCADModule<NewCADSettingsFOS>>()
				)
			);
		}
	};

Note that the arguments to `setStrategy` and `addBackend` can not only be a single element, but an `initializer_list` of multiple backends as well. In this case the backends are called in order until one returns a conclusive result (that is: not `unknown`).
If SMT-RAT was configured to allow for parallel execution, the backends are executed in parallel and the result of the first backend to terminate is used.

	class CADVSICP: public Manager {
		public:
		CADVSICP(): Manager() {
			setStrategy(
				addBackend<SATModule<SATSettings1>>({
					addBackend<NewCADModule<NewCADSettingsFOS>>(
						addBackend<VSModule<VSSettings234>>()
					),
					addBackend<ICPModule<ICPSettings1>>()
				})
			);
		}
	};

Finally, we can also attach conditions to individual backends to restrict their applicability. For example, we can construct a strategy that uses separate sub-strategies for linear and nonlinear problems:

	class RealSolver: public Manager {
		static bool is_nonlinear(carl::Condition condition) {
			return (carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL <= condition);
		}
		static bool is_linear(carl::Condition condition) {
			return !(carl::PROP_CONTAINS_NONLINEAR_POLYNOMIAL <= condition);
		}
		public:
		RealSolver(): Manager() {
			setStrategy({
				addBackend<FPPModule<FPPSettings1>>(
					addBackend<SATModule<SATSettings1>>(
						addBackend<ICPModule<ICPSettings1>>(
							addBackend<VSModule<VSSettings234>>(
								addBackend<NewCADModule<NewCADSettingsFOS>>()
							)
						)
					)
				).condition( &is_nonlinear ),
				addBackend<FPPModule<FPPSettings1>>(
					addBackend<SATModule<SATSettings1>>(
						addBackend<LRAModule<LRASettings1>>()
					)
				).condition( &is_linear )
			});
		}
	};
