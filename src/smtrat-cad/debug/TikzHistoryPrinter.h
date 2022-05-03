#pragma once

#include <carl-common/datastructures/carlTree.h>

#include <boost/optional.hpp>

#include <fstream>
#include <map>
#include <sstream>

namespace smtrat {
namespace cad {
namespace debug {

struct IDSanitizer {
private:
	std::map<std::string,std::string> mMap;
	std::string mPrefix;
public:
	IDSanitizer(const std::string& prefix): mPrefix(prefix) {}
	std::string operator()(const std::string& raw) {
		auto it = mMap.find(raw);
		if (it == mMap.end()) {
			it = mMap.emplace(raw, mPrefix + "_" + std::to_string(mMap.size())).first;
		}
		return it->second;
	}
};

struct UnifiedData {
	std::vector<boost::optional<std::string>> steps;
	
	void add(std::size_t step, const std::string& data) {
		while (steps.size() < step) steps.emplace_back();
		steps.emplace_back(data);
	}
	bool showsOn(std::size_t step) const {
		if (step >= steps.size()) return false;
		return bool(steps[step]);
	}
	const std::string& data(std::size_t step) const {
		assert(steps.size() > step);
		assert(steps[step]);
		return *steps[step];
	}
};

class TikzBasePrinter {
protected:
	std::size_t mStep;
	std::string printableID(const std::string& raw, const std::string& prefix, std::map<std::string,std::string>& map) const {
		auto it = map.find(raw);
		if (it == map.end()) {
			it = map.emplace(raw, prefix + "_" + std::to_string(map.size())).first;
		}
		return it->second;
	}
public:
	virtual void addNode(std::size_t level, const std::string& parent, const std::string& node, const std::string& data) = 0;
	virtual void addEdge(const std::string& src, const std::string& dst, const std::string& data) = 0;
	void step() {
		mStep++;
	}
	virtual void layout() = 0;
	virtual void writeTo(std::ostream& os, int xBase) const = 0;
	
	virtual std::size_t width() const = 0;
};

class TikzDAGPrinter: public TikzBasePrinter {
private:
	struct Node {
		UnifiedData data;
		std::map<std::string, UnifiedData> outgoing;
	};
	using Level = std::map<std::string, Node>;
	using NodeIDs = std::map<std::string, Level::iterator>;
	std::vector<Level> mData;
	NodeIDs mNodeIDs;
	std::size_t mMaxWidth = 0;
public:
	void addNode(std::size_t level, const std::string&, const std::string& node, const std::string& data) override {
		while (level >= mData.size()) mData.emplace_back();
		auto it = mNodeIDs.find(node);
		if (it == mNodeIDs.end()) {
			auto newIt = mData[level].emplace(node, Node()).first;
			it = mNodeIDs.emplace(node, newIt).first;
		}
		it->second->second.data.add(mStep, data);
	}
	void addEdge(const std::string& src, const std::string& dst, const std::string& data) override {
		auto it = mNodeIDs.find(src);
		assert(it != mNodeIDs.end());
		auto outid = it->second->second.outgoing.find(dst);
		if (outid == it->second->second.outgoing.end()) {
			outid = it->second->second.outgoing.emplace(dst, UnifiedData()).first;
		}
		outid->second.add(mStep, data);
	}
	
	void layout() override {
		for (const auto& l: mData) {
			mMaxWidth = std::max(mMaxWidth, l.size() * 5);
		}
	}
	void writeTo(std::ostream& os, int xBase) const override {
		IDSanitizer sanitizer("projection");
		for (std::size_t level = 0; level < mData.size(); level++) {
			int curX = 0;
			int increment = 0;
			if (mData[level].size() > 1) {
				increment = int(mMaxWidth / (mData[level].size() - 1));
			}
			for (const auto& entry: mData[level]) {
				for (std::size_t step = 0; step < mStep; step++) {
					if (!entry.second.data.showsOn(step)) continue;
					std::size_t cur = step;
					while (cur < mStep && entry.second.data.showsOn(cur) && entry.second.data.data(cur) == entry.second.data.data(step)) cur++;
					os << "\t\\onslide<" << (step+1) << "-" << (cur+1) << ">{" << std::endl;
					os << "\t\t\\node [align=center] (" << sanitizer(entry.first) << ") at (" << (xBase + curX) << "," << level << ") {" << entry.second.data.data(step) << "};"<< std::endl;
					os << "\t};" << std::endl;
					step = cur;
				}
				curX += increment;
				for (const auto& edge: entry.second.outgoing) {
					for (std::size_t step = 0; step < mStep; step++) {
						if (!edge.second.showsOn(step)) continue;
						std::size_t cur = step;
						while (cur < mStep && edge.second.showsOn(cur) && edge.second.data(cur) == edge.second.data(step)) cur++;
						os << "\t\\onslide<" << (step+1) << "-" << (cur+1) << ">{" << std::endl;
						os << "\t\t\\path (" << sanitizer(entry.first) << ") edge (" << sanitizer(edge.first) << ") node {" << edge.second.data(step) << "};" << std::endl;
						os << "\t};" << std::endl;
						step = cur;
					}
				}
			}
		}
	}
	
	std::size_t width() const override {
		return mMaxWidth;
	}
};

class TikzTreePrinter: public TikzBasePrinter {
private:
	struct UnifiedNode {
		UnifiedData mData;
		std::string id;
		std::size_t depth = 0;
		std::size_t subtreeWidth = 0;
		int position = 0;

		void add(std::size_t step, const std::string& data) {
			mData.add(step, data);
		}
		bool showsOn(std::size_t step) const {
			return mData.showsOn(step);
		}
		const std::string& data(std::size_t step) const {
			return mData.data(step);
		}
		friend std::ostream& operator<<(std::ostream& os, const UnifiedNode& un) {
			return os << un.subtreeWidth << " @ " << un.id;
		}
	};
	using Tree = carl::tree<UnifiedNode>;
	using TreeIDs = std::map<std::string, Tree::iterator>;
	using Edges = std::map<std::pair<std::string,std::string>, UnifiedData>;
	Tree mTree;
	TreeIDs mTreeIDs;
	Edges mEdges;
	
	void doLayout(const Tree::iterator& it) {
		int cur = it->position - int(it->subtreeWidth / 2);
		for (auto cit = mTree.begin_children(it); cit != mTree.end_children(it); cit++) {
			cit->position = cur + int(cit->subtreeWidth / 2);
			doLayout(cit);
			cur += int(cit->subtreeWidth);
		}
	}
	template<typename It>
	void reorderTree(Tree& newTree, const It& source, const It& target) const {
		std::vector<It> children;
		for (auto it = mTree.begin_children(source); it != mTree.end_children(source); it++) {
			children.push_back(it);
		}
		std::sort(children.begin(), children.end(), [](auto l, auto r){ return l->id < r->id; });
		for (const auto& c: children) {
			auto it = newTree.append(target, *c);
			reorderTree(newTree, c, it);
		}
	}
public:
	void setRoot(const std::string& node, const std::string& data) {
		auto it = mTreeIDs.find(node);
		if (it == mTreeIDs.end()) {
			auto rit = mTree.setRoot(UnifiedNode());
			it = mTreeIDs.emplace(node, rit).first;
			it->second->id = node;
		}
		it->second->add(mStep, data);
	}
	void addNode(std::size_t level, const std::string& parent, const std::string& node, const std::string& data) override {
		if (level == 0)	return setRoot(node, data);
		auto pit = mTreeIDs.at(parent);
		auto nit = mTreeIDs.find(node);
		if (nit == mTreeIDs.end()) {
			auto newit = mTree.append(pit, UnifiedNode());
			nit = mTreeIDs.emplace(node, newit).first;
			nit->second->id = node;
		}
		assert(mTree.get_parent(nit->second) == pit);
		assert(nit->second.depth() == level);
		nit->second->add(mStep, data);
	}
	void addEdge(const std::string& src, const std::string& dst, const std::string& data) override {
		auto it = mEdges.find(std::make_pair(src,dst));
		if (it == mEdges.end()) {
			it = mEdges.emplace(std::make_pair(src,dst), UnifiedData()).first;
		}
		it->second.add(mStep, data);
	}
	void layout() override {
		Tree newTree;
		newTree.setRoot(*mTree.begin());
		reorderTree(newTree, mTree.begin(), newTree.begin());
		mTree = newTree;
		for (auto it = mTree.begin_postorder(); it != mTree.end_postorder(); it++) {
			it->subtreeWidth = 0;
			for (auto cit = mTree.begin_children(it); cit != mTree.end_children(it); cit++) {
				it->subtreeWidth += cit->subtreeWidth;
			}
			if (it->subtreeWidth == 0) it->subtreeWidth = 1;
		}
		mTree.begin()->position = 0;
		doLayout(mTree.begin());
	}
	void writeTo(std::ostream& os, int xBase) const override {
		IDSanitizer sanitizer("lifting");
		for (auto it = mTree.begin(); it != mTree.end(); it++) {
			for (std::size_t step = 0; step < mStep; step++) {
				if (!it->showsOn(step)) continue;
				std::size_t cur = step;
				while (cur < mStep && it->showsOn(cur) && it->data(cur) == it->data(step)) cur++;
				os << "\t\\onslide<" << (step+1) << "-" << (cur+1) << ">{" << std::endl;
				os << "\t\t\\node [align=center] (" << sanitizer(it->id) << ") at (" << (xBase + it->position) << "," << it.depth() << ") {" << it->data(step) << "};"<< std::endl;
				os << "\t};" << std::endl;
				step = cur;
			}
		}
		for (const auto& e: mEdges) {
			for (std::size_t step = 0; step < mStep; step++) {
				if (!e.second.showsOn(step)) continue;
				std::size_t cur = step;
				while (cur < mStep && e.second.showsOn(cur) && e.second.data(cur) == e.second.data(step)) cur++;
				os << "\t\\onslide<" << (step+1) << "-" << (cur+1) << ">{" << std::endl;
				os << "\t\t\\path (" << sanitizer(e.first.first) << ") edge (" << sanitizer(e.first.second) << ") node {" << e.second.data(step) << "};" << std::endl;
				os << "\t};" << std::endl;
				step = cur;
            }
		}
	}
	virtual std::size_t width() const override {
		return mTree.begin()->subtreeWidth;
	}
};

class TikzHistoryPrinter {
private:
	std::map<std::string, TikzBasePrinter*> mPrinter;
	std::size_t mStep = 0;
	
	TikzBasePrinter* getPrinter(const std::string& id) {
		return mPrinter.at(id);
	}
	template<typename T>
	std::string asString(const T& t) const {
		std::stringstream ss;
		ss << t;
		return ss.str();
	}
	std::string nodeValue(const Sample& s, bool asTex = false) const {
		std::stringstream ss;
		if (asTex) ss << "$";
		if (s.value().is_numeric()) ss << s.value().value();
		else ss << s.value().interval();
		if (asTex) {
			if (s.isRoot()) ss << "_R";
			ss << "$";
		}
		return ss.str();
	}
	std::string sampleID(const Sample& s) const {
		double val = 0;
		if (s.value().is_numeric()) val = carl::toDouble(s.value().value());
		else val = carl::toDouble(carl::center(s.value().interval()));
		if (val < 0) val = -1 / (val - 1);
		else val = val + 1;
		return std::to_string(val);
	}
	template<typename Tree, typename It>
	std::string nodeID(const Tree& t, const It& it) const {
		std::stringstream ss;
		for (auto i = t.begin_path(it); i != t.end_path(); i++) {
			ss << sampleID(*i) << "/";
		}
		return ss.str();
	}
	std::string polyID(std::size_t level, std::size_t id) const {
		return std::to_string(level) + "_" + std::to_string(id);
	}
public:
	template<typename Printer>
	void configure(const std::string& name) {
		mPrinter.emplace(name, new Printer());
	}
	
	template<typename ID1, typename ID2, typename T>
	void addNode(const std::string& printer, std::size_t level, const ID1& parent, const ID2& node, const T& data) {
		getPrinter(printer)->addNode(level, asString(parent), asString(node), asString(data));
	}
	template<typename ID1, typename ID2, typename T>
	void addEdge(const std::string& printer, const ID1& src, const ID2& dst, const T& data) {
		getPrinter(printer)->addEdge(asString(src), asString(dst), asString(data));
	}
	
	template<typename L>
	void addLifting(const L& l) {
		const auto& t = l.getTree();
		for (auto node = t.begin(); node != t.end(); node++) {
			if (node.isRoot()) {
				addNode("Lifting", node.depth(), "", nodeID(t, node), nodeValue(*node, true));
			} else {
				const auto& p = t.get_parent(node);
				addNode("Lifting", node.depth(), nodeID(t, p), nodeID(t, node), nodeValue(*node, true));
				addEdge("Lifting", nodeID(t, p), nodeID(t, node), "");
			}
		}
	}
	template<typename P>
	void addProjection(const P& p) {
		for (std::size_t level = 1; level <= p.dim(); level++) {
			for (std::size_t id = 0; id < p.size(level); id++) {
				if (!p.hasPolynomialById(level, id)) continue;
				const auto& poly = p.getPolynomialById(level, id);
				addNode("Projection", level, "", polyID(level, id), asString(poly));
				if (level == 0) continue;
				for (const auto& parent: p.getOrigin(level, id)) {
					addEdge("Projection", polyID(parent.level, parent.first), polyID(level, id), "");
					if (parent.first != parent.second) {
						addEdge("Projection", polyID(parent.level, parent.second), polyID(level, id), "");
					}
				}
			}
		}
	}
	
	void step() {
		mStep++;
		for (auto& p: mPrinter) p.second->step();
	}
	
	void layout() {
		for (auto& p: mPrinter) p.second->layout();
	}
	
	void writeTo(const std::string& filename) const {
		std::size_t width = 0;
		for (auto& p: mPrinter) {
			width += p.second->width();
		}
		std::ofstream out(filename);
		out << "\\documentclass[8pt]{beamer}" << std::endl;
		out << "\\usepackage{tikz}" << std::endl;
		out << "\\tikzset{font=\\tiny}" << std::endl;
		out << "\\setbeamertemplate{navigation symbols}{}" << std::endl;
		out << "\\begin{document}" << std::endl;
		out << "\\eject \\pdfpagewidth=" << (0.5*double(width) + 2) << "cm" << std::endl;
		out << "\\begin{frame}<1-" << mStep << ">" << std::endl;
		out << "\\begin{tikzpicture}[x=0.5cm, y=1cm]" << std::endl;
		for (auto& p: mPrinter) {
			p.second->writeTo(out, 0);
		}
		out << "\\end{tikzpicture}" << std::endl;
		out << "\\end{frame}" << std::endl;
		out << "\\end{document}" << std::endl;
	}
};

}
}
}
