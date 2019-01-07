#pragma once

#include "Statistics.h"
#include "StatisticsCollector.h"

#include <fstream>
#include <iostream>

namespace smtrat {

enum class StatisticsOutputFormat {
	SMTLIB,
	XML
};

template<StatisticsOutputFormat SOF>
struct StatisticsPrinter {};

template<StatisticsOutputFormat SOF>
std::ostream& operator<<(std::ostream& os, StatisticsPrinter<SOF>);

template<>
std::ostream& operator<<(std::ostream& os, StatisticsPrinter<StatisticsOutputFormat::SMTLIB>) {
	for (auto s: StatisticsCollector::getInstance().statistics()) {
		os << "(:" << s->name() << " (" << std::endl;
		std::size_t max_width = 0;
		for (const auto& kv: s->collected()) {
			max_width = std::max(max_width, kv.first.size());
		}
		for (const auto& kv: s->collected()) {
			os << "\t:" << std::setw(static_cast<int>(max_width)) << std::left << kv.first << " " << kv.second << std::endl;
		}
		os << "))" << std::endl;
	}
	return os;
}

template<>
std::ostream& operator<<(std::ostream& os, StatisticsPrinter<StatisticsOutputFormat::XML>) {
	for (auto s: StatisticsCollector::getInstance().statistics()) {
		std::string name = s->name();
		std::replace(name.begin(), name.end(), '<', '(');
		std::replace(name.begin(), name.end(), '>', ')');
		os << "\t<module name=\"" << name << "\">\n"; 
		for (const auto& kv: s->collected()) {
			os << "\t\t<stat name=\"" << kv.first << "\" value=\"" << kv.second << "\" />\n";
		}
		os << "\t</module>\n"; 
	}
	return os;
}

auto statistics_as_smtlib() {
	return StatisticsPrinter<StatisticsOutputFormat::SMTLIB>();
}
auto statistics_as_xml() {
	return StatisticsPrinter<StatisticsOutputFormat::XML>();
}

void statistics_to_xml_file(const std::string& filename) {
	std::ofstream file;
	file.open(filename, std::ios::out);
	file << "<runtimestats>" << std::endl;
	file << statistics_as_xml();
	file << "</runtimestats>" << std::endl;
	file.close();
}



}