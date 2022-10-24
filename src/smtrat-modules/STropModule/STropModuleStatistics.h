#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <smtrat-common/statistics/Statistics.h>
namespace smtrat {
class STropModuleStatistics : public Statistics {
public:
	enum class AnswerBy { NONE = 0,
						  TRIVIAL_UNSAT = 1,
						  METHOD = 2,
						  BACKEND = 3,
						  PARSER = 4 };

private:
	carl::statistics::timer m_theory_timer;
	carl::statistics::timer m_transformation_timer;
	std::size_t m_answer_by_TRIVIAL_UNSAT = 0;
	std::size_t m_answer_by_METHOD = 0;
	std::size_t m_answer_by_BACKEND = 0;
	std::size_t m_answer_by_PARSER = 0;
	std::size_t m_failed = 0;

public:
	void collect() {
		Statistics::addKeyValuePair("theory_call_time", m_theory_timer);
		Statistics::addKeyValuePair("transformation_time", m_transformation_timer);
		Statistics::addKeyValuePair("answer_by_TRIVIAL_UNSAT", m_answer_by_TRIVIAL_UNSAT);
		Statistics::addKeyValuePair("answer_by_METHOD", m_answer_by_METHOD);
		Statistics::addKeyValuePair("answer_by_BACKEND", m_answer_by_BACKEND);
		Statistics::addKeyValuePair("answer_by_PARSER", m_answer_by_PARSER);
		Statistics::addKeyValuePair("failed", m_failed);
	}

	void answer_by(AnswerBy answer_by) {
		switch (answer_by) {
		case AnswerBy::TRIVIAL_UNSAT:
			m_answer_by_TRIVIAL_UNSAT++;
			break;
		case AnswerBy::METHOD:
			m_answer_by_METHOD++;
			break;
		case AnswerBy::BACKEND:
			m_answer_by_BACKEND++;
			break;
		case AnswerBy::PARSER:
			m_answer_by_PARSER++;
			break;
		default:
		}
	}

	void failed() {
		m_failed++;
	}

	auto& theory_timer() {
		return m_theory_timer;
	}

	auto& transformation_timer() {
		return m_transformation_timer;
	}
};
} // namespace smtrat
#endif