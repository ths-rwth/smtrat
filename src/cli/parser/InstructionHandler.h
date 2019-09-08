#pragma once

#include "VariantMap.h"
#include "theories/Attribute.h"
#include "../ResourceLimitation.h"

#include <smtrat-common/model.h>
#include <smtrat-qe/smtrat-qe.h>

#include <iostream>

namespace smtrat {
namespace parser {

enum class OptimizationType { Maximize, Minimize };
inline std::ostream& operator<<(std::ostream& os, OptimizationType ot) {
	switch (ot) {
		case OptimizationType::Maximize: return os << "maximize";
		case OptimizationType::Minimize: return os << "minimize";
	}
	return os << "???";
}

class OutputWrapper {
	std::ostream out;
	std::string pre;
	std::string suf;
public:
	OutputWrapper(std::ostream& o, const std::string& prefix, const std::string& suffix)
	: out(o.rdbuf()), pre(prefix), suf(suffix) {
		this->out << pre;
	}
	OutputWrapper(const OutputWrapper&& o) : out(o.out.rdbuf()), pre(o.pre), suf(o.suf) {}
	~OutputWrapper() {
		this->out << suf;
	}
	template<typename T>
	OutputWrapper& operator<<(const T& t) {
		this->out << t;
		return *this;
	}
};

class InstructionHandler {
public:
	typedef types::AttributeValue Value;

private:
	std::queue<std::function<void()>> instructionQueue;
	std::vector<smtrat::ModelVariable> mArtificialVariables;
public:
	void addInstruction(std::function<void()> bind) {
		this->instructionQueue.push(bind);
	}
	bool hasInstructions() const {
		return !instructionQueue.empty();
	}
	void runInstructions() {
		while (!this->instructionQueue.empty()) {
			this->instructionQueue.front()();
			this->instructionQueue.pop();
		}
	}
	void setArtificialVariables(std::vector<smtrat::ModelVariable>&& vars) {
		mArtificialVariables = std::move(vars);
	}
	void cleanModel(smtrat::Model& model) const {
		for (const auto& v: mArtificialVariables) {
			model.erase(v);
		}
	}
protected:
	VariantMap<std::string, Value> infos;
	VariantMap<std::string, Value> options;
public:
	bool has_info(const std::string& key) const {
		return infos.find(key) != infos.end();
	}
	const auto& get_info(const std::string& key) const {
		return infos.find(key)->second;
	}
	template<typename T>
	T option(const std::string& key) const {
		return this->options.get<T>(key);
	}
	bool printInstruction() const {
		if (!this->options.has<bool>("print-instruction")) return false;
		return this->options.get<bool>("print-instruction");
	}
protected:
	std::ostream mRegular;
	std::ostream mDiagnostic;
	std::map<std::string, std::ofstream> streams;

	void setStream(const std::string& s, std::ostream& os) {
		if (s == "stdout") os.rdbuf(std::cout.rdbuf());
		else if (s == "stderr") os.rdbuf(std::cerr.rdbuf());
		else if (s == "stdlog") os.rdbuf(std::clog.rdbuf());
		else {
			if (this->streams.count(s) == 0) {
				this->streams[s].open(s);
			}
			os.rdbuf(this->streams[s].rdbuf());
		}
	}
public:
	InstructionHandler(): mRegular(std::cout.rdbuf()), mDiagnostic(std::cerr.rdbuf()) {
		Attribute attr("print-instruction", Value(false));
		this->setOption(attr);
		smtrat::resource::Limiter::getInstance().initialize();
	}
	virtual ~InstructionHandler() {
		for (auto& it: this->streams) it.second.close();
	}

	std::ostream& diagnostic() {
		return this->mDiagnostic;
	}
	void diagnostic(const std::string& s) {
		this->setStream(s, this->mDiagnostic);
	}
	std::ostream& regular() {
		return this->mRegular;
	}
	void regular(const std::string& s) {
		this->setStream(s, this->mRegular);
	}
	OutputWrapper error() {
		return OutputWrapper(mDiagnostic, "(error \"", "\")\n");
	}
	OutputWrapper warn() {
		return OutputWrapper(mDiagnostic, "(warn \"", "\")\n");
	}
	OutputWrapper info() {
		return OutputWrapper(mRegular, "(info \"", "\")\n");
	}
	virtual void add(const FormulaT& f) = 0;
	virtual void addSoft(const FormulaT& f, Rational weight, const std::string& id) = 0;
	virtual void annotateName(const FormulaT& f, const std::string& name) = 0;
	virtual void check() = 0;
	virtual void declareFun(const carl::Variable&) = 0;
	virtual void declareSort(const std::string&, const unsigned&) = 0;
	virtual void defineSort(const std::string&, const std::vector<std::string>&, const carl::Sort&) = 0;
	virtual void echo(const std::string& s) {
		regular() << s << std::endl;
	}
	virtual void eliminateQuantifiers(const qe::QEQuery& q) = 0;
	virtual void exit() = 0;
	virtual void getAllModels() = 0;
	virtual void getAssertions() = 0;
	virtual void getAssignment() = 0;
	void getInfo(const std::string& key) {
		if (this->infos.count(key) > 0) regular() << "(:" << key << " " << this->infos[key] << ")" << std::endl;
		else error() << "no info set for :" << key;
	}
	virtual void getModel() = 0;
	virtual void getObjectives() = 0;
	void getOption(const std::string& key) {
		if (this->options.count(key) > 0) regular() << "(:" << key << " " << this->options[key] << ")" << std::endl;
		else error() << "no option set for :" << key;
	}
	virtual void getProof() = 0;
	virtual void getUnsatCore() = 0;
	virtual void getValue(const std::vector<carl::Variable>&) = 0;
	virtual void addObjective(const Poly& p, OptimizationType ot) = 0;
	virtual void pop(std::size_t) = 0;
	virtual void push(std::size_t) = 0;
	virtual void reset() = 0;
	virtual void resetAssertions() = 0;
	void setInfo(const Attribute& attr) {
		if (this->infos.count(attr.key) > 0) warn() << "overwriting info for :" << attr.key;
		if (attr.key == "name" || attr.key == "authors" || attr.key == "version") error() << "The info :" << attr.key << " is read-only.";
		else this->infos[attr.key] = attr.value;
	}
	virtual void setLogic(const carl::Logic&) = 0;
	void setOption(const Attribute& option)  {
		std::string key = option.key;
		if (this->options.count(key) > 0) warn() << "overwriting option for :" << key;
		this->options[key] = option.value;
		if (key == "diagnostic-output-channel") this->diagnostic(this->options.get<std::string>(key));
		else if (key == "expand-definitions") this->error() << "The option :expand-definitions is not supported.";
		else if (key == "interactive-mode") {
			this->options.assertType<bool>("interactive-mode", std::bind(&InstructionHandler::error, this));
		}
		else if (key == "print-instruction") {
			this->options.assertType<bool>("print-instruction", std::bind(&InstructionHandler::error, this));
		}
		else if (key == "print-success") {
			this->options.assertType<bool>("print-success", std::bind(&InstructionHandler::error, this));
		}
		else if (key == "produce-assignments") {
			this->options.assertType<bool>("produce-assignments", std::bind(&InstructionHandler::error, this));
		}
		else if (key == "produce-models") {
			this->options.assertType<bool>("produce-models", std::bind(&InstructionHandler::error, this));
		}
		else if (key == "produce-proofs") {
			this->error() << "The option :produce-proofs is not supported.";
		}
		else if (key == "produce-unsat-cores") {
			this->options.assertType<bool>("produce-unsat-cores", std::bind(&InstructionHandler::error, this));
		}
		else if (key == "random-seed") {
			this->error() << "The option :random-seed is not supported.";
		}
		else if (key == "regular-output-channel") this->regular(this->options.get<std::string>(key));
		else if (key == "verbosity") {
			this->options.assertType<Rational>("verbosity", std::bind(&InstructionHandler::error, this));
		}
		else if (key == "timeout") {
			this->options.assertType<Rational>("timeout", std::bind(&InstructionHandler::error, this));
			carl::uint timeout = carl::toInt<carl::uint>(options.get<Rational>("timeout"));
			this->info() << "Setting timeout to " << timeout << " seconds";
			smtrat::resource::Limiter::getInstance().setTimeout(timeout);
		}
		else if (key == "memout") {
			this->options.assertType<Rational>("memout", std::bind(&InstructionHandler::error, this));
			smtrat::resource::Limiter::getInstance().setMemout(carl::toInt<carl::uint>(options.get<Rational>("memout")));
		}
	}
};

}
}
