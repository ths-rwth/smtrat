/**
 * @file:   Node.h
 * @author: Sebastian Junges
 * @created 27/11/2012
 * @version 28/11/2012
 */

#pragma once

#include <boost/filesystem.hpp>

#include "ssh/SshConnection.h"
#include "Benchmark.h"
#include "Settings.h"


namespace fs =boost:: filesystem;

namespace benchmax {

/**
 * Class which represents another computer.
 */
class Node
{
	protected:

		std::string mNodeName;
		std::string mUsername;
		std::string mPassword;
		unsigned mNrCores;
		unsigned short mPort;
		unsigned mCallNr;
		SshConnection mSsh;
		std::vector<std::string> mJobIds;

	public:

		/**
		 *
		 * @param nodeName
		 * @param user
		 * @param password
		 * @param nrCores
		 * @param port
		 */
		Node(const std::string& nodeName, const std::string& user, const std::string& password, unsigned nrCores = 1, unsigned short port = 22):
			mNodeName(nodeName),
			mUsername(user),
			mPassword(password),
			mNrCores(nrCores),
			mPort(port),
			mSsh(nrCores)
		{}

		/**
		 * Start an SSH session
		 * @return true iff success.
		 */
		const std::vector<std::string>& jobIds() const
		{
			return mJobIds;
		}

		const SshConnection& sshConnection() const
		{
			return mSsh;
		}

		bool createSSHconnection()
		{
			return mSsh.buildConnection(mNodeName.c_str(), mPort, mUsername, mPassword);
		}

		bool connected()
		{
			if(blocked())
				return false;
			return mSsh.connectionEstablished();
		}

		bool blocked()
		{
			return mSsh.connectionBlocked();
		}

		/**
		 *
		 */
		bool assignAndExecuteBenchmarks(Benchmark& benchmark, unsigned nrOfInstances, const std::string& callID)
		{
			if(connected() && freeCores() > 0)
			{
				std::list<fs::path> benchmarks = benchmark.pop(nrOfInstances);
				//assert(benchmarks.size() > 0);
				std::stringstream command;
				mJobIds.push_back(callID);
				command << Settings::PathOfBenchmarkTool << " -T " << benchmark.timeout() << " -M " << benchmark.memout() << " ";
				command << "-f " << Settings::RemoteOutputDirectory << "benchmark_" << callID << ".out ";
				command << "-o " << Settings::RemoteOutputDirectory << " ";
				command << "-X stats_" << callID << ".xml ";
				if(Settings::UseStats)
				{
					command << "-s ";
				}
				if(Settings::ValidationTool != NULL)
				{
					command << "-W " << Settings::RemoteOutputDirectory << "wrong_results_" << callID << "/ ";
					command << "-V " << Settings::ValidationTool->path() << " ";
				}
				command << benchmark.tool()->interfaceToCommandString() << " " << benchmark.tool()->path() << benchmark.tool()->arguments('@');
//				if(Settings::UseStats)
//					command << "@--stats:exportXml=" << Settings::RemoteOutputDirectory << "stats_" << callID << ".xml ";
				command << " ";
				for(std::list<fs::path>::const_iterator file = benchmarks.begin(); file != benchmarks.end(); ++file)
				{
					command << "-D " << file->generic_string() << " ";
				}
				if(benchmark.mute())
				{
					command << "-m ";
				}
				else if(benchmark.quiet())
				{
					command << "-q ";
				}
				mSsh.remoteCall(command.str());
				return true;
			}
			else
			{
				return false;
			}
		}

		bool downloadFile(const std::string& _from, const std::string& _to)
		{
			if(mSsh.initDownload(_from, _to, true))
			{
				return mSsh.processDownload(true);
			}
			return false;
		}

		bool updateResponses()
		{
			return mSsh.updateResponses();
		}

		/**
		* return the number of free cores
		*/
		std::size_t freeCores() const
		{
			return mSsh.getNrFreeChannels();
		}

		bool idle() const
		{
			return (freeCores() == mNrCores);
		}

		void cancel()
		{
			mSsh.cancel();
		}

		void restartActiveCalls()
		{
			mSsh.restartActiveCalls();
		}
};

}