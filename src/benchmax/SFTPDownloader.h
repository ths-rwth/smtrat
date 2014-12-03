/*
 * File:   SFTPDownloader.h
 * Author: Sebastian Junges
 *
 * Created on November 29, 2012, 7:11 PM
 *
 * based on example found here
 * http://www.libssh2.org/examples/sftp_nonblock.html
 */

#ifndef SFTPDOWNLOADER_H
#define SFTPDOWNLOADER_H

#include <libssh2.h>
#include <libssh2_sftp.h>
#include "SshWaitSocket.h"
#include "BenchmarkTool.h"
#include <fstream>

class SFTPDownloader
{
	int				  mSocket;
	LIBSSH2_SESSION*	 mSession;
	LIBSSH2_SFTP*		mSftpSession;
	LIBSSH2_SFTP_HANDLE* mSftpHandle;
	std::stringstream	response_stream;
	std::string		  mRemoteFile;
	std::string		  mDestinationPath;
	bool				 mRemove;

	public:
		SFTPDownloader(int socket, LIBSSH2_SESSION* session):
			mSocket(socket),
			mSession(session),
			mRemoteFile(""),
			mDestinationPath("default.tmp"),
			mRemove(false)
		{}

		void setDestination(const std::string& destination)
		{
			mDestinationPath = destination;
		}

		void removeAfterwards(bool remove)
		{
			mRemove = remove;
		}

		bool initDownload(const std::string& sftpPath)
		{
			mRemoteFile = sftpPath;
			int rc;
			do
			{
				mSftpSession = libssh2_sftp_init(mSession);
				if(!mSftpSession)
				{
					if((rc = libssh2_session_last_errno(mSession)) == LIBSSH2_ERROR_EAGAIN)
					{
						waitsocket(mSocket, mSession);	/* now we wait */
					}
					else
					{
						break;
					}
				}
			}
			while(!mSftpSession);
			do
			{
				mSftpHandle = libssh2_sftp_open(mSftpSession, sftpPath.c_str(), LIBSSH2_FXF_READ, 0);
				if(!mSftpHandle)
				{
					if(libssh2_session_last_errno(mSession) != LIBSSH2_ERROR_EAGAIN)
					{
						libssh2_sftp_close(mSftpHandle);
						libssh2_sftp_shutdown(mSftpSession);
						return false;
					}
					else
					{
						waitsocket(mSocket, mSession);	/* now we wait */
					}
				}
			}
			while(!mSftpHandle);
			return true;

			// libssh2_sftp_open() is done, now receive data!
		}

		/**
		 */
		bool download(bool wait)
		{
			if(mRemoteFile == "")
				return false;
			long rc;
			long totalBytes = 0;
			do
			{
				char buffer[1024 * 24];

				do
				{
					rc = libssh2_sftp_read(mSftpHandle, buffer, sizeof(buffer));
					if(rc > 0)
					{
						totalBytes += rc;
						response_stream.write(buffer, rc);
						//BenchmarkTool::OStream  << "Response: " << response_stream.str() << std::endl;
					}
					else if(rc == 0)
					{
					}
					else
					{
						if(rc != LIBSSH2_ERROR_EAGAIN)
							BenchmarkTool::OStream << "Error reading data (rc=" << rc << ")\n";
					}

				}
				while(rc > 0);
				/* loop until we fail */
				if(wait && (rc == LIBSSH2_ERROR_EAGAIN))
				{
					waitsocket(mSocket, mSession);
				}
				else
				{
					break;
				}
			}
			while(1);
			if(rc == LIBSSH2_ERROR_EAGAIN)
			{
				// we have to come back
				return false;
			}
			else
			{
				// download finished.
				std::ofstream file;
				file.open(mDestinationPath, std::ios::out);
				file << response_stream.str();
				file.flush();
				file.close();

				response_stream.str("");

				libssh2_sftp_close(mSftpHandle);

				if(mRemove)
				{
					int ret;
					while((ret = libssh2_sftp_unlink(mSftpSession, mRemoteFile.c_str())) != LIBSSH2_ERROR_EAGAIN)
					{
						waitsocket(mSocket, mSession);
					}
					if(ret < 0)
					{
						if(ret != LIBSSH2_ERROR_EAGAIN)
						{
							BenchmarkTool::OStream << "Error removing file << " << mRemoteFile << " (rc=" << ret << ")" << std::endl;
						}
					}
				}
				libssh2_sftp_shutdown(mSftpSession);
				return true;
			}
		}
};

#endif   /* SFTPDOWNLOADER_H */
