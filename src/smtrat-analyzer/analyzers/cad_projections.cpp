#include "variables.h"
#include "utils.h"
#include "../settings.h"

#include <smtrat-cad/common.h>
#include <smtrat-cad/Settings.h>
#include <smtrat-cad/projection/Projection.h>
#include <smtrat-cad/projectionoperator/utils.h>
#include <smtrat-cad/utils/CADConstraints.h>
#include <smtrat-cad/variableordering/triangular_ordering.h>

namespace smtrat::analyzer {

template<typename Settings>
struct Projector {
	cad::CADConstraints<Settings::backtracking> mConstraints;
	cad::ProjectionT<Settings> mProjection;

	Projector():
		mConstraints(
			[&](const cad::UPoly& p, std::size_t cid, bool isBound){ mProjection.addPolynomial(cad::projection::normalize(p), cid, isBound); },
			[&](const cad::UPoly& p, std::size_t cid, bool isBound){ mProjection.addEqConstraint(cad::projection::normalize(p), cid, isBound); },
			[&](const cad::UPoly& p, std::size_t cid, bool isBound){ mProjection.removePolynomial(cad::projection::normalize(p), cid, isBound); }
		),
		mProjection(mConstraints)
	{}
	void add(const ConstraintT& c) {
		mConstraints.add(c);
	}
};

template<typename P>
void collect_projection_size(const std::string& prefix, const P& projection, AnalyzerStatistics& stats) {
	std::size_t sum = 0;
	DegreeCollector dc;
	for (std::size_t level = 1; level <= projection.mProjection.dim(); ++level) {
		sum += projection.mProjection.size(level);
		for (std::size_t pid = 0; pid < projection.mProjection.size(level); ++pid) {
			if (projection.mProjection.hasPolynomialById(level, pid)) {
				const auto& p = projection.mProjection.getPolynomialById(level, pid);
				dc(p);
			}
		}
	}
	stats.add(prefix + "_size", sum);
	stats.add(prefix + "_deg_max", dc.degree_max);
	stats.add(prefix + "_deg_sum", dc.degree_sum);
	stats.add(prefix + "_tdeg_max", dc.tdegree_max);
	stats.add(prefix + "_tdeg_sum", dc.tdegree_sum);
}

template<typename Settings>
void perform_projection(const std::string& prefix, const std::set<ConstraintT>& constraints, AnalyzerStatistics& stats) {
	Projector<Settings> p;
	std::vector<Poly> polys;
	for (const auto& c: constraints) {
		polys.emplace_back(c.lhs());
	}
	p.mConstraints.reset(cad::variable_ordering::triangular_ordering(polys));
	p.mProjection.reset();
	for (const auto& c: constraints) {
		p.add(c);
	}

	collect_projection_size(prefix, p, stats);
}

struct SettingsCollins: cad::BaseSettings {
	static constexpr cad::ProjectionType projectionOperator = cad::ProjectionType::Collins;
};
struct SettingsHong: cad::BaseSettings {
	static constexpr cad::ProjectionType projectionOperator = cad::ProjectionType::Hong;
};
struct SettingsMcCallum: cad::BaseSettings {
	static constexpr cad::ProjectionType projectionOperator = cad::ProjectionType::McCallum;
};
struct SettingsMcCallumPartial: cad::BaseSettings {
	static constexpr cad::ProjectionType projectionOperator = cad::ProjectionType::McCallum_partial;
};
struct SettingsLazard: cad::BaseSettings {
	static constexpr cad::ProjectionType projectionOperator = cad::ProjectionType::Lazard;
};
struct SettingsBrown: cad::BaseSettings {
	static constexpr cad::ProjectionType projectionOperator = cad::ProjectionType::Brown;
};

void analyze_cad_projections(const FormulaT& f, AnalyzerStatistics& stats) {
	if (settings_analyzer().analyze_projections == "none") return;

	std::set<ConstraintT> constraints;

	carl::visit(f, [&](const FormulaT& f){
		if (f.getType() == carl::FormulaType::CONSTRAINT) {
			constraints.insert(f.constraint());
		}
	});

	bool all = (settings_analyzer().analyze_projections == "all");
	if (all || settings_analyzer().analyze_projections == "collins") {
		perform_projection<SettingsCollins>("cad_projection_collins", constraints, stats);
	}
	if (all || settings_analyzer().analyze_projections == "hong") {
		perform_projection<SettingsHong>("cad_projection_hong", constraints, stats);
	}
	if (all || settings_analyzer().analyze_projections == "mccallum") {
		perform_projection<SettingsMcCallum>("cad_projection_mccallum", constraints, stats);
	}
	if (all || settings_analyzer().analyze_projections == "mccallum_partial") {
		perform_projection<SettingsMcCallumPartial>("cad_projection_mccallum_partial", constraints, stats);
	}
	if (all || settings_analyzer().analyze_projections == "lazard") {
		perform_projection<SettingsLazard>("cad_projection_lazard", constraints, stats);
	}
	if (all || settings_analyzer().analyze_projections == "brown") {
		perform_projection<SettingsBrown>("cad_projection_brown", constraints, stats);
	}
}

}