
#include "Node.h"

Tool*			   BenchmarkTool::ValidationTool				= NULL;
std::string		 BenchmarkTool::assumptionsfile			   = "assumptions_to_check.smt2";
std::string		 BenchmarkTool::TemporaryValidationResultFile = "validationresult";
std::string		 BenchmarkTool::TemporaryAnswerFile		   = "answer_file";
std::string		 BenchmarkTool::OutputDirectory			   = "";
std::string		 BenchmarkTool::StatsXMLFile				  = "stats.xml";
std::string		 BenchmarkTool::RemoteOutputDirectory		 = "/scratch/";
std::string		 BenchmarkTool::ExitMessage				   = "AllDone";
bool				BenchmarkTool::UseStats					  = false;
bool				BenchmarkTool::ProduceLatex				  = false;
std::ostream		BenchmarkTool::OStream(std::cout.rdbuf());
std::string		 BenchmarkTool::PathOfBenchmarkTool = "";
std::string		 BenchmarkTool::WrongResultPath	 = BenchmarkTool::OutputDirectory + "wrong_results/";
std::vector<Node*>* BenchmarkTool::Nodes			   = new std::vector<Node*>();
unsigned			BenchmarkTool::Timeout			 = 150;
unsigned			BenchmarkTool::Memout			  = 1000;

//std::string BenchmarkTool::Parser


