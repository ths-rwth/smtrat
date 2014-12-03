/**
 * @file:   SshConnection.h
 * @author: Sebastian Junges
 *
 * Based on code found on:
 * http://www.p-jansson.com/2011/06/ssh-communication-using-libssh2-and.html
 * and native sockets as seen here:
 * http://www.libssh2.org/examples/ssh2_exec.html
 *
 * @created 27-11-2012
 * @version 28-11-2012
 */

#pragma once

#include <boost/asio/io_service.hpp>
#include <boost/asio/ip/tcp.hpp>
#include <boost/utility.hpp>
#include <libssh2.h>
#include "SshChannel.h"
#include "SFTPDownloader.h"

#include "../logging.h"

struct Sessiondata
{
	std::string password;
};

static void kbd_callback(const char*,
						 int,
						 const char*,
						 int,
						 int num_prompts,
						 const LIBSSH2_USERAUTH_KBDINT_PROMPT*,
						 LIBSSH2_USERAUTH_KBDINT_RESPONSE* responses,
						 void** abstract)
{
	for(int i = 0; i < num_prompts; i++)
	{
		Sessiondata** sess	 = (Sessiondata**)abstract;

		char*		 writable = new char[(**sess).password.size() + 1];
		std::copy((**sess).password.begin(), (**sess).password.end(), writable);
		writable[(**sess).password.size()] = '\0';	// don't forget the terminating 0

		//BenchmarkTool::OStream  << "Password for k-i: " << writable << std::endl;
		responses[i].text   = writable;
		responses[i].length = (unsigned)(**sess).password.length();
	}
}

/**
 * Class which builds a Ssh connection via Boost::Asio sockets.
 */
class SshConnection:
	public boost::noncopyable
{
	private:

		Sessiondata sesdata;

		int		 mSocket;
		/// @brief The SSH session structure to use in all
		/// communcations using this instance.
		LIBSSH2_SESSION* session;
		/// Flag indicating problems with authentification. If set, building connections is prevented.
		bool mBlocked;
		/// Flag indicating whether a connection has been established
		bool mConnectionEstablished;
		/// Vector of channels currently used.
		std::map<SshChannel* const , const std::string> mActiveChannels;
		/// Vector of channels which are ready to be used.
		std::vector<SshChannel*> mIdleChannels;

		// Something related to the native sockets
		struct sockaddr_in sin;

		SFTPDownloader mDownloader;

		unsigned	   mNrOfChannels;

	public:

		SshConnection(unsigned nrChannels = 0):
			sesdata(),
			mSocket(socket(AF_INET, SOCK_STREAM, 0)),
			session(libssh2_session_init_ex(NULL, NULL, NULL, &sesdata)),
			mBlocked(false),
			mConnectionEstablished(false),
			mDownloader(mSocket, session),
			mNrOfChannels(nrChannels)
		{
			for(unsigned i = 0; i < nrChannels; ++i)
			{
				mIdleChannels.push_back(new SshChannel(mSocket));
			}
		}

		virtual ~SshConnection()
		{
			if(mConnectionEstablished)
			{
				assert(mActiveChannels.empty());
				while(!mIdleChannels.empty())
				{
					SshChannel* toDelete = mIdleChannels.back();
					mIdleChannels.pop_back();
					delete toDelete;
				}
				mConnectionEstablished = false;
				libssh2_session_disconnect(session, "Goodbye.");
				libssh2_session_free(session);
			}
			close(mSocket);
		}

		void cancelConnection()
		{
			remoteCall("echo hallo");
		}

		void addIdleChannel(unsigned nrChannels = 1)
		{
			for(unsigned i = 0; i < nrChannels; ++i)
			{
				mIdleChannels.push_back(new SshChannel(mSocket));
			}
			mNrOfChannels += nrChannels;
		}

		/**
		*
		* @param IP
		* @param PortNumber
		* @param user The username
		* @param pw The password
		* @return true iff the connection is established (or already was established)
		*/
		int buildConnection(const char* hostname, unsigned short port, const std::string& user, const std::string& password)
		{
			if(mConnectionEstablished)
				return true;
			if(mBlocked)
				return false;
			BENCHMAX_LOG_INFO("benchmark.ssh", "Connecting with " << hostname << ":" << port << " ...");
			/* Connect to SSH server */
			sin.sin_family	  = AF_INET;
			sin.sin_port = htons(port);
			sin.sin_addr.s_addr = inet_addr(hostname);
			if(connect(mSocket, (struct sockaddr*)(&sin), sizeof(struct sockaddr_in)) != 0)
			{
				BENCHMAX_LOG_ERROR("benchmax.ssh", "Failed to connect!");
				return -1;
			}

			BenchmarkTool::OStream << "Handshaking.." << std::endl;
			int rc = libssh2_session_handshake(session, mSocket);
			if(0 > rc)
			{
				BenchmarkTool::OStream << "..failed (return code=" << rc << ")" << std::endl;
			}

			char* userauthlist = libssh2_userauth_list(session, user.c_str(), (unsigned)user.length());
			if(libssh2_userauth_authenticated(session) != 1)
			{
				BenchmarkTool::OStream << "Authentication methods: " << userauthlist << std::endl;
				int auth_pw = 0;
				if(strstr(userauthlist, "password") != NULL)
				{
					auth_pw |= 1;
				}
				if(strstr(userauthlist, "keyboard-interactive") != NULL)
				{
					auth_pw |= 2;
				}
				if(strstr(userauthlist, "publickey") != NULL)
				{
					auth_pw |= 4;
				}
				// Authentification with password.
				BenchmarkTool::OStream << "User: " << user << " Password: " << password << std::endl;
				if(auth_pw & 1)
				{
					int retval = libssh2_userauth_password(session, user.c_str(), password.c_str());
					if(retval == LIBSSH2_ERROR_AUTHENTICATION_FAILED)
					{
						BenchmarkTool::OStream << "Authentification failed." << std::endl;
						mBlocked = true;
						return 0;
					}
					else if(retval == 0)
					{
						mConnectionEstablished = true;
						BenchmarkTool::OStream << "Connection established" << std::endl;
						return 1;
					}
					else
					{
						BenchmarkTool::OStream << "General ssh auth. error" << std::endl;
						exit(1);
					}
				}
				else if(auth_pw & 4)
				{
					sesdata.password = password;
					if(libssh2_userauth_keyboard_interactive(session, user.c_str(), &kbd_callback))
					{
						BenchmarkTool::OStream << "\tAuthentication by keyboard-interactive failed!\n";
						mBlocked = true;
					}
					else
					{
						mConnectionEstablished = true;
					}

				}
			}
			else
			{
				BenchmarkTool::OStream << "Authentification succeeded without password" << std::endl;
				mConnectionEstablished = true;
			}
			return 1;
		}

		/**
		* Get an idle channel and send the command to it. The channel becomes active.
		* @param cmd command to be executed

		*/
		void remoteCall(const std::string& cmd)
		{
			BenchmarkTool::OStream << "Remote call: " << cmd << std::endl;
			SshChannel* channel = mIdleChannels.back();
			channel->openChannel(session);
			channel->setBlocking(false);
			if(channel->executeCommand(cmd))
			{
				mIdleChannels.pop_back();
				assert(mActiveChannels.find(channel) == mActiveChannels.end());
				mActiveChannels.insert(std::pair<SshChannel* const , const std::string>(channel, cmd));
			}
			else
			{
				channel->closeChannel();
			}
		}

		/**
		*
		* @param file Path to the file that should be downloaded.
		* @param deleteAfter
		* @return
		*/
		bool initDownload(const std::string& remoteFile, const std::string& destFile, bool deleteAfter)
		{
			mDownloader.setDestination(destFile);
			mDownloader.removeAfterwards(deleteAfter);
			return mDownloader.initDownload(remoteFile);
		}

		bool processDownload(bool wait)
		{
			return mDownloader.download(wait);
		}

		void printActiveRemoteCalls(std::ostream& _out, const std::string& _init = "") const
		{
			for(std::map<SshChannel* const , const std::string>::const_iterator channel = mActiveChannels.begin(); channel != mActiveChannels.end();
					++channel)
			{
				_out << _init << channel->second << std::endl << std::endl;
			}
		}

		/**
		*
		* @return true iff a channel has become idle.
		*/
		bool updateResponses()
		{
			if(!mConnectionEstablished)
				return false;
			bool result = false;
			std::map<SshChannel* const , const std::string>::iterator it = mActiveChannels.begin();
			while(it != mActiveChannels.end())
			{
				//read response. If execution is done, we close the channel
				if(it->first->readResponse())
				{
					it->first->closeChannel();
					mIdleChannels.push_back(it->first);
					result = true;
					it	 = mActiveChannels.erase(it);
				}
				else
				{
					++it;
				}
			}
			return result;
		}

		/**
		*
		* @return The number of free channels.
		*/
		size_t getNrFreeChannels() const
		{
			assert(mIdleChannels.size() + mActiveChannels.size() == mNrOfChannels);
			return mIdleChannels.size();
		}

		bool connectionEstablished()
		{
			return mConnectionEstablished;
		}

		bool connectionBlocked()
		{
			return mBlocked;
		}

		void cancel()
		{
			BenchmarkTool::OStream << "Cancelling .. " << std::endl;
			SshChannel* channel;
			if(!mIdleChannels.empty())
			{
				channel = mIdleChannels.back();
			}
			else
			{
				channel = mActiveChannels.begin()->first;
			}
			channel->openChannel(session);
			channel->setBlocking(false);
			channel->executeCommand("killall -9 benchmax");
			channel->closeChannel();
		}

		void restartActiveCalls()
		{
			std::map<SshChannel* const , const std::string>::iterator it = mActiveChannels.begin();
			while(it != mActiveChannels.end())
			{
				BenchmarkTool::OStream << "Remote call: " << it->second << std::endl;
				SshChannel* channel = it->first;
				channel->openChannel(session);
				channel->setBlocking(false);
				if(!channel->executeCommand(it->second))
				{
					channel->closeChannel();
				}
				++it;
			}
		}
};
