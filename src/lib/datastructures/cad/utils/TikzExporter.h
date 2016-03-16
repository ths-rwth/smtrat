#pragma once

#include <fstream>

#include "../Common.h"
#include "../CAD.h"

namespace smtrat {
namespace cad {
	class TikzExporter {
	protected:
		void prefix(std::ofstream& out) {
			out << """
\documentclass{article}
\usepackage{tikz}
\usepackage{fullpage}
\begin{document}
\begin{tikzpicture}
""";
		}
		void suffix(std::ofstream& out) {
			out << """
\end{tikzpicture}
\end{document}
""";
		}
		void plotConstraint(std::ofstream& out, const ConstraintT& c) {
			
		}
		void plotSample(std::ofstream& out, const Sample& s) {
		}
	public:
		template<typename CAD>
		void operator()(const std::string& filename, const CAD& cad) const {
			std::ofstream out(filename);
			prefix(out);
			for (const auto& c: cad.getConstraints()) plotConstraint(out, c);
			const auto& tree = cad.getLifting().getTree();
			std::size_t dim = cad.getLifting().dim();
			for (auto it = tree.begin_depth(dim); it != tree.end_depth(dim); it++) plotSample(out, *it);
			suffix(out);
			out.close();
		}
	};
}
}
