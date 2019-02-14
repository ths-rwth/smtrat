/**
 * @file   Stats.cpp
 * @author: Sebastian Junges
 */

#include "Stats.h"
#include <iostream>
#include <filesystem>
#include <fstream>
#include <assert.h>
#include "../cli/config.h"

#include "settings/Settings.h"
#include "benchmarks/benchmarks.h"

namespace benchmax {

namespace fs = std::filesystem;

Stats::Stats(const std::string& _file, Type _type):
	mType(_type),
	mCollectingSolvers(0),
	mCollectingBenchmarkSets(0),
	mCollectingBenchmarkFiles(0),
	mCollectingInputStats(0),
	mCollectingRuns(0),
	mCollectingRunTimeStats(0),
	mCollectingResults(0),
	mFile(_file)
{
	if(mType == STATS_COLLECTION)
	{
		std::ofstream file;
		file.open(mFile, std::ios::out);
		file << "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n";
		file << "<files>\n";
		file.close();
	}
}

Stats::~Stats()
{
	std::ofstream file;
	file.open(mFile, std::ios::out | std::ios::app);
	if(mType == STATS_COLLECTION)
	{
		file << "</files>\n";
	}
	else
	{
		file << "\t\t\t\t</results>\n";
		file << "\t\t\t</run>\n";
		file << "\t\t</benchmarkfile>\n";
		file << "\t</benchmarkset>\n";
		file << "</benchmarksets>\n";
	}
	file.close();
}

void Stats::addSolver(const std::string& _name)
{
	assert(mType == BENCHMARK_RESULT);
	assert(mCollectingSolvers != -1);

	std::ofstream file;
	if(mCollectingSolvers == 0)
	{
		assert(mCollectingBenchmarkSets == 0);
		mCollectingSolvers = 1;
		file.open(mFile, std::ios::out);
		file << "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n";
		file << "<benchmarksets>\n";
		file << "\t<solvers>\n";
	}
	else
	{
		assert(mCollectingSolvers == 1);
		file.open(mFile, std::ios::out | std::ios::app);
	}
	file << "\t\t<solver solver_id=\"" << _name << "\"></solver>\n";
	file.close();
}

void Stats::addBenchmarkSet(const std::string& _name)
{
	assert(mType == BENCHMARK_RESULT);
	std::ofstream file;
	file.open(mFile, std::ios::out | std::ios::app);
	if(mCollectingBenchmarkSets == 0)
	{
		assert(mCollectingSolvers == 1);
		mCollectingBenchmarkSets = 1;
		mCollectingSolvers	   = -1;
		file << "\t</solvers>\n";
	}
	else
	{
		assert(mCollectingBenchmarkSets == 1);
		file << "\t\t\t\t</results>\n";
		file << "\t\t\t</run>\n";
		file << "\t\t</benchmarkfile>\n";
		file << "\t</benchmarkset>\n";
	}
	file << "\t<benchmarkset name=\"" << _name << "\">\n";
	file.close();
	mCollectingBenchmarkFiles = 0;
}

void Stats::addBenchmarkFile(const std::string& _name)
{
	assert(mType == BENCHMARK_RESULT);
	assert(mCollectingBenchmarkSets == 1);

	std::ofstream file;
	file.open(mFile, std::ios::out | std::ios::app);
	if(mCollectingBenchmarkFiles == 0)
	{
		mCollectingBenchmarkFiles = 1;
	}
	else
	{
		assert(mCollectingBenchmarkFiles == 1);
		file << "\t\t\t\t</results>\n";
		file << "\t\t\t</run>\n";
		file << "\t\t</benchmarkfile>\n";
	}
	mCollectingInputStats   = 0;
	mCollectingRuns		 = 0;
	mCollectingRunTimeStats = 0;
	mCollectingResults	  = 0;

	file << "\t\t<benchmarkfile name=\"" << _name << "\">\n";
	file.close();
}

void Stats::addInputStat(const std::string& _name, const std::string& _value)
{
	assert(mType == BENCHMARK_RESULT);
	assert(mCollectingBenchmarkFiles == 1);
	assert(mCollectingInputStats != -1);

	std::ofstream file;
	file.open(mFile, std::ios::out | std::ios::app);
	if(mCollectingInputStats == 0)
	{
		file << "\t\t\t<inputstats>\n";
		mCollectingInputStats = 1;
	}
	file << "\t\t\t\t<stat name=\"" << _name << "\">" << _value << "</stat>\n";
	file.close();
}

void Stats::addInputStat(const std::string& _name, int _value)
{
	std::stringstream out;
	out << _value;
	addInputStat(_name, out.str());
}

void Stats::addRun(const std::string& _solver, std::size_t _timeout)
{
	assert(mType == BENCHMARK_RESULT);
	assert(mCollectingBenchmarkFiles == 1);

	std::ofstream file;
	file.open(mFile, std::ios::out | std::ios::app);
	if(mCollectingInputStats == 1)
	{
		file << "\t\t\t</inputstats>\n";
		mCollectingInputStats = -1;
	}
	if(mCollectingRuns == 0)
	{
		mCollectingRuns = 1;
	}
	else
	{
		assert(mCollectingRuns == 1);
		file << "\t\t\t\t</results>\n";
		file << "\t\t\t</run>\n";
	}
	file << "\t\t\t<run solver_id=\"" << _solver << "\" timeout=\"" << _timeout << "\">\n";
	file.close();
}

void Stats::addRunTimeStat(const std::string& _name, const std::string& _value)
{
	assert(mType == BENCHMARK_RESULT);
	assert(mCollectingRuns == 1);
	assert(mCollectingRunTimeStats != -1);

	std::ofstream file;
	file.open(mFile, std::ios::out | std::ios::app);

	if(mCollectingRunTimeStats == 0)
	{
		file << "\t\t\t\t<runtimestats>\n";
		mCollectingRunTimeStats = 1;
	}
	file << "\t\t\t\t\t<stat name=\"" << _name << "\">" << _value << "</stat>\n";
	file.close();
}

void Stats::addResult(const std::string& _name, const std::string& _type, const std::string& _value)
{
	assert(mType == BENCHMARK_RESULT);
	assert(mCollectingRuns == 1);
	assert(mCollectingResults != -1);

	std::ofstream file;
	file.open(mFile, std::ios::out | std::ios::app);
	if(mCollectingRunTimeStats == 1)
	{
		file << "\t\t\t\t</runtimestats>\n";
		mCollectingRunTimeStats = -1;
	}
	if(mCollectingResults == 0)
	{
		file << "\t\t\t\t<results>\n";
		mCollectingResults = 1;
	}
	file << "\t\t\t\t\t<result name=\"" << _name << "\" type=\"" << _type << "\">" << _value << "</result>\n";
	file.close();
}

void Stats::addResult(const std::string& _name, bool value)
{
	addResult(_name, "bool", (value ? "true" : "false"));
}

void Stats::addStat(const std::string& _file)
{
	assert(mType == STATS_COLLECTION);

	std::ofstream file;
	file.open(mFile, std::ios::out | std::ios::app);
	file << "<file>" << _file << "</file>\n";
	file.close();
}

void Stats::createStatsCompose(const std::string& _fileName)
{
	std::ofstream file;
	file.open(_fileName, std::ios::out);
	file << "<?xml version=\"1.0\" encoding=\"UTF-8\"?>" << std::endl;
	file << "	   <xsl:stylesheet version=\"1.0\" xmlns:xsl=\"http://www.w3.org/1999/XSL/Transform\">" << std::endl;
	file << "	   <xsl:output omit-xml-declaration=\"no\" indent=\"yes\"/>" << std::endl;
	file << "	   <xsl:key name=\"kSolvers\" match=\"solver\" use=\"@solver_id\"/>" << std::endl;
	file << "	  <xsl:key name=\"sets\" match=\"benchmarkset\" use=\"@name\"/>" << std::endl;
	file << "	   <xsl:key name=\"runs\" match=\"benchmarkfile\" use=\"@name\"/>" << std::endl;
	file << "	   <xsl:template match=\"/\">" << std::endl;
	file << "		   <benchmarksets>" << std::endl;
	file << "		   <xsl:apply-templates/>" << std::endl;
	file << "		   <xsl:message>Done!</xsl:message>" << std::endl;
	file << "		   </benchmarksets>" << std::endl;
	file << "	   </xsl:template>" << std::endl;
	file << "	   <xsl:template match=\"files\">" << std::endl;
	file << "		   <xsl:apply-templates select=\"document(file)/benchmarksets\"/>" << std::endl;
	file << "			 <xsl:message>Processed files!</xsl:message>" << std::endl;
	file << "	   </xsl:template>" << std::endl;
	file << "	   <xsl:template match=\"benchmarksets\">" << std::endl;
	file << "			   <solvers>" << std::endl;
	file << "			   <xsl:for-each select=\"solvers/solver[generate-id() = generate-id(key(\'kSolvers\', @solver_id[1]))]\">" << std::endl;
	file << "				   <xsl:copy-of select=\"key(\'kSolvers\', @solver_id)[1]\"/>" << std::endl;
	file << "			   </xsl:for-each>" << std::endl;
	file << "			   </solvers>" << std::endl;
	file << "			   <xsl:for-each select=\"benchmarkset[generate-id() = generate-id(key(\'sets\', @name[1]))]\">" << std::endl;
	file << "				   <xsl:message>Processing benchmarkset</xsl:message>" << std::endl;
	file << "				   <benchmarkset>" << std::endl;
	file << "					   <xsl:attribute name=\"name\">" << std::endl;
	file << "						   <xsl:value-of select=\"@name\"/>" << std::endl;
	file << "					   </xsl:attribute>" << std::endl;
	file << "					   <xsl:for-each select=\"key(\'sets\', @name)/benchmarkfile[generate-id() = generate-id(key(\'runs\', @name[1]))]\">"
		 << std::endl;
	file << "						   <benchmarkfile>" << std::endl;
	file << "							   <xsl:attribute name=\"name\">" << std::endl;
	file << "								 <xsl:value-of select=\"@name\"/>" << std::endl;
	file << "							   </xsl:attribute>" << std::endl;
	file << "							   <xsl:copy-of select=\"key(\'runs\', @name)[1]/inputstats\"/>" << std::endl;
	file << "							   <xsl:for-each select=\"key(\'runs\', @name)\">" << std::endl;
	file << "								 <xsl:copy-of select=\"run\"/>" << std::endl;
	file << "							   </xsl:for-each>" << std::endl;
	file << "						   </benchmarkfile>" << std::endl;
	file << "					   </xsl:for-each>" << std::endl;
	file << "				   </benchmarkset>" << std::endl;
	file << "			   </xsl:for-each>" << std::endl;
	file << "	   </xsl:template>" << std::endl;
	file << "	   </xsl:stylesheet>" << std::endl;
	file.close();
}

void Stats::createLatexCompose(const std::string& _fileName)
{
	std::ofstream file;
	file.open(_fileName, std::ios::out);
	file << "<?xml version=\"1.0\" encoding=\"UTF-8\"?>" << std::endl;
	file << "	<xsl:stylesheet version=\"1.0\" xmlns:xsl=\"http://www.w3.org/1999/XSL/Transform\" xmlns:html=\"http://www.w3.org/TR/REC-html40\" xmlns:xforms=\"http://www.w3.org/2002/xforms\" xmlns:xlink=\"http://www.w3.org/1999/xlink\">"
		 << std::endl;
	file << "	<xsl:output method=\"text\" omit-xml-declaration=\"yes\" indent=\"yes\" /> " << std::endl;
	file << "   <xsl:template match=\"/\">" << std::endl;
	file << "\\documentclass{article}" << std::endl;
	file << "\\usepackage{color}" << std::endl;
	file << "\\usepackage{colortbl}" << std::endl;
	file << "\\usepackage{array}" << std::endl;
	file << "\\definecolor{Lightgray}{gray}{0.9}" << std::endl;
	file << "\\newcolumntype{g}{>{\\columncolor{Lightgray}}r}" << std::endl;
	file << "\\begin{document}" << std::endl;
	file << "		<xsl:apply-templates select=\"benchmarksets\" mode=\"overview\"/>" << std::endl;
	file << "\\end{document}" << std::endl;
	file << "	</xsl:template>" << std::endl;
	file << "" << std::endl;
	file << "   <xsl:template match=\"benchmarksets\" mode=\"overview\">" << std::endl;
	file << "\\section{Table with the Keys}" << std::endl;
	file << "	   <xsl:apply-templates select=\".\" mode=\"key\"/>" << std::endl;
	file << "\\section{Table with the Benchmark Sets as Columns}" << std::endl;
	file << "	   <xsl:apply-templates select=\".\" mode=\"sets_tools\"/>" << std::endl;
	file << "\\section{Table with the Tools as Columns}" << std::endl;
	file << "	   <xsl:apply-templates select=\".\" mode=\"tools_sets\"/>" << std::endl;
	file << "   </xsl:template>" << std::endl;
	file << "   " << std::endl;
	file << "   <!-- Generating table with the benchmark sets as row heads and the tools as column head. -->" << std::endl;
	file << "   <xsl:template match=\"benchmarksets\" mode=\"sets_tools\">" << std::endl;
	file << "	   <!-- The table header -->" << std::endl;
	file << "\\begin{table}[ht]" << std::endl;
	file << "\\caption{Write here your caption.}" << std::endl;
	file << "\\smallskip\\par" << std::endl;
	file << "\\begin{tabular*}{1.1\\linewidth}{@{\\extracolsep{\\fill}}l||<xsl:for-each select=\"//solvers/solver\">rg|</xsl:for-each>r|}"
		 << std::endl;
	file << "	   <xsl:for-each select=\"//solvers/solver\">" << std::endl;
	file << "   &#38; \\multicolumn{2}{c|}{solver<xsl:value-of select=\"position()\"/>}" << std::endl;
	file << "	   </xsl:for-each>" << std::endl;
	file << "   &#38; \\emph{all} \\\\" << std::endl;
	file << "	   <xsl:for-each select=\"//solvers/solver\">" << std::endl;
	file << "   &#38;  \\multicolumn{1}{c}{\\emph{\\#}}" << std::endl;
	file << "   &#38;  \\multicolumn{1}{c|}{\\emph{time}}" << std::endl;
	file << "	   </xsl:for-each>" << std::endl;
	file << "   &#38; \\emph{\\#}" << std::endl;
	file << "\\\\\\hline\\hline" << std::endl;
	file << "<!-- The table content -->" << std::endl;
	file << "	   <xsl:for-each select=\"//benchmarksets/benchmarkset\">" << std::endl;
	file << "   set<xsl:value-of select=\"position()\"/> &#38; <xsl:variable name=\"SET\" select=\".\"/><xsl:for-each select=\"//solvers/solver\"><xsl:variable name=\"ID\"><xsl:value-of select='@solver_id'/></xsl:variable>$<xsl:value-of select=\"count($SET/benchmarkfile/run[@solver_id=$ID]/results[result='sat' or result='unsat'])\"/>$ &#38; $<xsl:value-of select=\"format-number(sum($SET/benchmarkfile/run[@solver_id=$ID]/results[result='sat' or result='unsat']/result[@name='runtime']), '0.0')\"/>$ &#38; </xsl:for-each>$<xsl:value-of select=\"count($SET/benchmarkfile)\"/>$ \\\\" << std::endl;
	file << "   \\quad - sat &#38; <xsl:for-each select=\"//solvers/solver\"><xsl:variable name=\"ID\"><xsl:value-of select='@solver_id'/></xsl:variable>$<xsl:value-of select=\"count($SET/benchmarkfile/run[@solver_id=$ID]/results[result='sat'])\"/>$ &#38; $<xsl:value-of select=\"format-number(sum($SET/benchmarkfile/run[@solver_id=$ID]/results[result='sat']/result[@name='runtime']), '0.0')\"/>$ &#38; </xsl:for-each>\\\\" << std::endl;
	file << "   \\quad - unsat &#38; <xsl:for-each select=\"//solvers/solver\"><xsl:variable name=\"ID\"><xsl:value-of select='@solver_id'/></xsl:variable>$<xsl:value-of select=\"count($SET/benchmarkfile/run[@solver_id=$ID]/results[result='unsat'])\"/>$ &#38; $<xsl:value-of select=\"format-number(sum($SET/benchmarkfile/run[@solver_id=$ID]/results[result='unsat']/result[@name='runtime']), '0.0')\"/>$ &#38; </xsl:for-each>\\\\ \\hline" << std::endl;
	file << "   </xsl:for-each>\\hline" << std::endl;
	file << "   all &#38; <xsl:for-each select=\"//solvers/solver\"><xsl:variable name=\"ID\"><xsl:value-of select='@solver_id'/></xsl:variable>$<xsl:value-of select=\"count(//benchmarksets/benchmarkset/benchmarkfile/run[@solver_id=$ID]/results[result='sat' or result='unsat'])\"/>$ &#38;\\ $<xsl:value-of select=\"format-number(sum(//benchmarksets/benchmarkset/benchmarkfile/run[@solver_id=$ID]/results[result='sat' or result='unsat']/result[@name='runtime']), '0.0')\"/>$ &#38; </xsl:for-each>$<xsl:value-of select=\"count(//benchmarksets/benchmarkset/benchmarkfile)\"/>$ \\\\" << std::endl;
	file << "   \\quad - sat &#38; <xsl:for-each select=\"//solvers/solver\"><xsl:variable name=\"ID\"><xsl:value-of select='@solver_id'/></xsl:variable>$<xsl:value-of select=\"count(//benchmarksets/benchmarkset/benchmarkfile/run[@solver_id=$ID]/results[result='sat'])\"/>$ &#38;\\ $<xsl:value-of select=\"format-number(sum(//benchmarksets/benchmarkset/benchmarkfile/run[@solver_id=$ID]/results[result='sat']/result[@name='runtime']), '0.0')\"/>$ &#38; </xsl:for-each> \\\\" << std::endl;
	file << "   \\quad - unsat &#38; <xsl:for-each select=\"//solvers/solver\"><xsl:variable name=\"ID\"><xsl:value-of select='@solver_id'/></xsl:variable>$<xsl:value-of select=\"count(//benchmarksets/benchmarkset/benchmarkfile/run[@solver_id=$ID]/results[result='unsat'])\"/>$ &#38;\\ $<xsl:value-of select=\"format-number(sum(//benchmarksets/benchmarkset/benchmarkfile/run[@solver_id=$ID]/results[result='unsat']/result[@name='runtime']), '0.0')\"/>$ &#38; </xsl:for-each>\\\\ \\hline" << std::endl;
	file << "\\end{tabular*}" << std::endl;
	file << "\\end{table}" << std::endl;
	file << "   </xsl:template>" << std::endl;
	file << "   " << std::endl;
	file << "   <!-- Generating table with the tools as row heads and the benchmark sets as column head. -->" << std::endl;
	file << "   <xsl:template match=\"benchmarksets\" mode=\"tools_sets\">" << std::endl;
	file << "	   <!-- The table header -->" << std::endl;
	file << "\\begin{table}[ht]" << std::endl;
	file << "\\caption{Write here your caption.}" << std::endl;
	file << "\\smallskip\\par" << std::endl;
	file << "\\begin{tabular*}{1.1\\linewidth}{@{\\extracolsep{\\fill}}l||<xsl:for-each select=\"//benchmarksets/benchmarkset\">rg|</xsl:for-each>rg|}"
		 << std::endl;
	file << "	   <xsl:for-each select=\"//benchmarksets/benchmarkset\">" << std::endl;
	file << "   &#38; \\multicolumn{2}{c|}{set<xsl:value-of select=\"position()\"/> ($<xsl:value-of select=\"count(./benchmarkfile)\"/>$)}"
		 << std::endl;
	file << "	   </xsl:for-each>" << std::endl;
	file << "   &#38; \\multicolumn{2}{c|}{\\emph{all} ($<xsl:value-of select=\"count(//benchmarksets/benchmarkset/benchmarkfile)\"/>$)} \\\\"
		 << std::endl;
	file << "	   <xsl:for-each select=\"//solvers/solver\">" << std::endl;
	file << "   &#38;  \\multicolumn{1}{c}{\\emph{\\#}}" << std::endl;
	file << "   &#38;  \\multicolumn{1}{c|}{\\emph{time}}" << std::endl;
	file << "	   </xsl:for-each>" << std::endl;
	file << "   &#38;  \\multicolumn{1}{c}{\\emph{\\#}}" << std::endl;
	file << "   &#38;  \\multicolumn{1}{c|}{\\emph{time}}" << std::endl;
	file << "\\\\\\hline\\hline" << std::endl;
	file << "<!-- The table content -->" << std::endl;
	file << "	   <xsl:for-each select=\"//solvers/solver\">" << std::endl;
	file << "   solver<xsl:value-of select=\"position()\"/> &#38; <xsl:variable name=\"ID\"><xsl:value-of select='@solver_id'/></xsl:variable><xsl:for-each select=\"//benchmarksets/benchmarkset\">$<xsl:value-of select=\"count(./benchmarkfile/run[@solver_id=$ID]/results[result='sat' or result='unsat'])\"/>$ &#38;\\ $<xsl:value-of select=\"format-number(sum(./benchmarkfile/run[@solver_id=$ID]/results[result='sat' or result='unsat']/result[@name='runtime']), '0.0')\"/>$ &#38; </xsl:for-each>$<xsl:value-of select=\"count(//benchmarksets/benchmarkset/benchmarkfile/run[@solver_id=$ID]/results[result='sat' or result='unsat'])\"/>$ &#38;\\ $<xsl:value-of select=\"format-number(sum(//benchmarksets/benchmarkset/benchmarkfile/run[@solver_id=$ID]/results[result='sat' or result='unsat']/result[@name='runtime']), '0.0')\"/>$ \\\\" << std::endl;
	file << "   \\quad - sat &#38; <xsl:for-each select=\"//benchmarksets/benchmarkset\">$<xsl:value-of select=\"count(./benchmarkfile/run[@solver_id=$ID]/results[result='sat'])\"/>$ &#38; $<xsl:value-of select=\"format-number(sum(./benchmarkfile/run[@solver_id=$ID]/results[result='sat']/result[@name='runtime']), '0.0')\"/>$ &#38; </xsl:for-each>$<xsl:value-of select=\"count(//benchmarksets/benchmarkset/benchmarkfile/run[@solver_id=$ID]/results[result='sat'])\"/>$ &#38; $<xsl:value-of select=\"format-number(sum(//benchmarksets/benchmarkset/benchmarkfile/run[@solver_id=$ID]/results[result='sat']/result[@name='runtime']), '0.0')\"/>$ \\\\" << std::endl;
	file << "   \\quad - unsat &#38; <xsl:for-each select=\"//benchmarksets/benchmarkset\">$<xsl:value-of select=\"count(./benchmarkfile/run[@solver_id=$ID]/results[result='unsat'])\"/>$ &#38; $<xsl:value-of select=\"format-number(sum(./benchmarkfile/run[@solver_id=$ID]/results[result='unsat']/result[@name='runtime']), '0.0')\"/>$ &#38; </xsl:for-each>$<xsl:value-of select=\"count(//benchmarksets/benchmarkset/benchmarkfile/run[@solver_id=$ID]/results[result='unsat'])\"/>$ &#38; $<xsl:value-of select=\"format-number(sum(//benchmarksets/benchmarkset/benchmarkfile/run[@solver_id=$ID]/results[result='unsat']/result[@name='runtime']), '0.0')\"/>$ \\\\ \\hline" << std::endl;
	file << "	   </xsl:for-each>\\hline" << std::endl;
	file << "\\end{tabular*}" << std::endl;
	file << "\\end{table}" << std::endl;
	file << "   </xsl:template>" << std::endl;
	file << "" << std::endl;
	file << "   <!-- Generate the key to the solvers and benchmark sets. -->" << std::endl;
	file << "   <xsl:template match=\"benchmarksets\" mode=\"key\">" << std::endl;
	file << "	   <!-- Description of the solvers. -->" << std::endl;
	file << "\\subsection{Solvers}" << std::endl;
	file << "" << std::endl;
	file << "\\begin{enumerate}<xsl:for-each select=\"//solvers/solver\">" << std::endl;
	file << "   \\item solver<xsl:value-of select=\"position()\"/>: <xsl:value-of select=\"translate(@solver_id, '_', ' ')\"/></xsl:for-each>"
		 << std::endl;
	file << "\\end{enumerate}" << std::endl;
	file << "" << std::endl;
	file << "	   <!-- Description of the benchmark sets. -->" << std::endl;
	file << "\\subsection{Benchmark sets}" << std::endl;
	file << "" << std::endl;
	file << "\\begin{enumerate}<xsl:for-each select=\"//benchmarksets/benchmarkset\">" << std::endl;
	file << "   \\item set<xsl:value-of select=\"position()\"/>: <xsl:value-of select=\"translate(@name, '_', ' ')\"/></xsl:for-each>" << std::endl;
	file << "\\end{enumerate}" << std::endl;
	file << "   </xsl:template>" << std::endl;
	file << "	</xsl:stylesheet>" << std::endl;
	file.close();
}

void Stats::composeStats(const std::vector<std::string>& files)
{
	Stats* stats = new Stats(settings_benchmarks().output_file_xml, STATS_COLLECTION);
	for(std::vector<std::string>::const_iterator it = files.begin(); it != files.end(); ++it)
	{
		stats->addStat(*it);
	}
	delete stats;
	createStatsCompose(settings_benchmarks().output_dir.native() + "statsCompose.xsl");
	callComposeProcessor();
	fs::remove(fs::path(settings_benchmarks().output_dir.native() + "statsCompose.xsl"));
}

/**
 * @param io the resulting statistics file.
 */
void Stats::callComposeProcessor(const std::string& io)
{
	system(std::string("xsltproc -o " + settings_benchmarks().output_dir.native() + "stats.xml.tmp " + settings_benchmarks().output_dir.native() + "statsCompose.xsl "
					   + io).c_str());
	system(std::string("xsltproc -o " + io + " " + settings_benchmarks().output_dir.native() + "statsCompose.xsl " + settings_benchmarks().output_dir.native()
					   + "stats.xml.tmp").c_str());
	fs::remove(fs::path(settings_benchmarks().output_dir.native() + "stats.xml.tmp"));
	//if(Settings::ProduceLatex)
	//{
	//	createLatexCompose(settings_benchmarks().output_dir + "latexCompose.xsl");
	//	system(std::string("xsltproc -o " + settings_benchmarks().output_dir + "results.tex " + settings_benchmarks().output_dir + "latexCompose.xsl "
	//					   + settings_benchmarks().output_file_xml).c_str());
	//	fs::remove(fs::path(settings_benchmarks().output_dir + "latexCompose.xsl"));
	//}
}

void Stats::callComposeProcessor()
{
	callComposeProcessor(std::string(settings_benchmarks().output_dir.native() + settings_benchmarks().output_file_xml.native()));
}

}
