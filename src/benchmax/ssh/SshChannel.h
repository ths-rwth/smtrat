/**
 * @file:   SshChannel.h
 * @author: Sebastian Junges
 * @created 28/11/2012
 */

#pragma once

#include <sstream>
#include <libssh2.h>

#include "SshWaitSocket.h"

#include "../BenchmarkTool.h"
#include "../logging.h"

/**
 */
class SshChannel
{
	LIBSSH2_CHANNEL* mChannel;
	std::stringstream response_stream;
	int mSocket;
	LIBSSH2_SESSION* mSession;
	int mId;
	static int IdCounter;

	public:

		SshChannel(int socket):
			mChannel(NULL),
			mSocket(socket),
			mId(IdCounter++)
		{}

		/**
		 *
		 * @param session
		 */
		void openChannel(LIBSSH2_SESSION* session)
		{
			if(mChannel != NULL)
			{
				BENCHMAX_LOG_ERROR("benchmax.ssh", "Channel is still open.");
			}
			mSession = session;
			while((mChannel = libssh2_channel_open_session(mSession)) == NULL
					&& libssh2_session_last_error(mSession, NULL, NULL, 0) == LIBSSH2_ERROR_EAGAIN)
			{
				waitsocket(mSocket, mSession);
			}
			if(NULL == mChannel)
			{
				throw std::runtime_error("Could not open SSH communication channel.");
			}

		}

		/**
		 *
		 * @param blocking
		 */
		void setBlocking(bool blocking)
		{
			blocking ? libssh2_channel_set_blocking(mChannel, 1) : libssh2_channel_set_blocking(mChannel, 0);
		}

		/**
		 *
		 * @param command
		 * @return true if the command is executing on the channel.
		 */
		bool executeCommand(const std::string& command)
		{
			int rc;
			while((rc = libssh2_channel_exec(mChannel, command.c_str())) == LIBSSH2_ERROR_EAGAIN)
			{
				waitsocket(mSocket, mSession);
			}
			if(rc == 0)
			{
				BENCHMAX_LOG_DEBUG("benchmax.ssh", "Sent command \"" << command << "\".");
				return true;
			}
			else
			{
				return false;
			}
		}

		/**
		 *
		 * @return
		 */
		bool readResponse()
		{
			if(mChannel == NULL)
				return false;
			for(; ; )
			{
				/* loop until we block */
				long rc;
				do
				{
					char buffer[0x4000];
					rc = libssh2_channel_read(mChannel, buffer, sizeof(buffer));

					if(rc > 0)
					{
						response_stream.write(buffer, rc);
						// temporarily output response for debugging.
						BENCHMAX_LOG_DEBUG("benchmax.ssh", "Response: " << response_stream.str());
					}
					else if(rc == 0)
					{
						break;
					}
					else
					{
						if (rc != LIBSSH2_ERROR_EAGAIN) {
							BENCHMAX_LOG_ERROR("benchmax.ssh", "libssh2_channel_read failed (return code = " << rc << ")");
						}
					}
				}
				while(rc > 0);

				/* this is due to blocking that would occur otherwise so we loop on
				   this condition */
				if(rc == LIBSSH2_ERROR_EAGAIN)
				{
					//std::cout << "waitsocket" << std::endl;
					//waitsocket(mSocket, mSession);
					break;
				}
				else
				{
					//std::cout << "stop waiting" << std::endl;
					break;
				}
			}
			std::size_t result = response_stream.str().find(benchmax::BenchmarkTool::ExitMessage);
			// if the exit message was found, we return true
			if(result != std::string::npos)
				return true;
			return false;
		}

		/**
		 * @return exit code
		 */
		int closeChannel()
		{
			BENCHMAX_LOG_DEBUG("benchmax.ssh", "Closing channel.");
			int   rc;
			int   exitcode = 1;
			char* exitsignal = (char*)"none";
			while((rc = libssh2_channel_close(mChannel)) == LIBSSH2_ERROR_EAGAIN)
			{
				waitsocket(mSocket, mSession);
			}
			if(rc == 0)
			{
				exitcode = libssh2_channel_get_exit_status(mChannel);
				libssh2_channel_get_exit_signal(mChannel, &exitsignal, NULL, NULL, NULL, NULL, NULL);
			}

			if(exitsignal) {
				BENCHMAX_LOG_WARN("benchmax.ssh", "Got signal " << exitsignal);
			} else {
				BENCHMAX_LOG_INFO("benchmax.ssh", "Clean exit: " << exitsignal);
			}

			libssh2_channel_free(mChannel);

			response_stream.str("");
			mChannel		= NULL;
			return exitcode;

		}
};
