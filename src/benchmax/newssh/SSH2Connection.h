#pragma once

#include <mutex>
#include <libssh/libssh.h>
#include <libssh/sftp.h>

#include "Node.h"
#include "../Settings.h"
#include "../logging.h"

#define SSH_LOCKED(expr) { std::lock_guard<std::mutex> guard(mutex); expr; }

namespace benchmax {
namespace ssh {
	
class SSHConnection {
private:
	Node node;
	std::size_t curChannels;
	std::size_t maxChannels;
	ssh_session session;
	std::mutex mutex;
	
	ssh_channel getChannel() {
		assert(!busy());
		std::lock_guard<std::mutex> guard(mutex);
		ssh_channel channel = ssh_channel_new(session);
		if (channel == nullptr) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", "Failed to create new ssh channel: " << ssh_get_error(session));
			exit(1);
		}
		int rc = ssh_channel_open_session(channel);
		if (rc != SSH_OK) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", "Failed to open ssh channel: " << ssh_get_error(session));
			exit(1);
		}
		curChannels++;
		return channel;
	}
	ssh_scp getSCP(int mode, const std::string& basedir) {
		assert(!busy());
		std::lock_guard<std::mutex> guard(mutex);
		ssh_scp scp = ssh_scp_new(session, mode, basedir.c_str());
		if (scp == nullptr) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", "Failed to create new scp session: " << ssh_get_error(session));
			exit(1);
		}
		int rc = ssh_scp_init(scp);
		if (rc != SSH_OK) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", "Failed to initialize scp session: " << ssh_get_error(session));
			exit(1);
		}
		curChannels++;
		return scp;
	}
	sftp_session getSFTP() {
		assert(!busy());
		std::lock_guard<std::mutex> guard(mutex);
		sftp_session sftp = sftp_new(session);
		if (sftp == nullptr) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", "Failed to create new sftp session: " << ssh_get_error(session));
			exit(1);
		}
		int rc = sftp_init(sftp);
		if (rc != SSH_OK) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", "Failed to initialize sftp session: " << ssh_get_error(session));
			exit(1);
		}
	}
	void destroy(ssh_channel channel) {
		std::lock_guard<std::mutex> guard(mutex);
		ssh_channel_close(channel);
		ssh_channel_free(channel);
		curChannels--;
	}
	void destroy(ssh_scp scp) {
		std::lock_guard<std::mutex> guard(mutex);
		ssh_scp_close(scp);
		ssh_scp_free(scp);
		curChannels--;
	}
	void destroy(sftp_session sftp) {
		std::lock_guard<std::mutex> guard(mutex);
		sftp_free(sftp);
		curChannels--;
	}
public:
	SSHConnection(const Node& n): node(n), curChannels(0), maxChannels(node.cores) {
		session = ssh_new();
		if (session == nullptr) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", "Failed to create SSH session.");
		}
		std::cout << "session = " << session << std::endl;
		std::cout << "Initializing session to " << node.hostname << " " << node.port << " " << node.username << std::endl;
		ssh_options_set(session, SSH_OPTIONS_HOST, node.hostname.c_str());
		ssh_options_set(session, SSH_OPTIONS_PORT, &(node.port));
		ssh_options_set(session, SSH_OPTIONS_USER, node.username.c_str());
		
		int rc = ssh_connect(session);
		if (rc != SSH_OK) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", "Failed to connect to " << node.username << " @ "<< node.hostname << ":" << node.port);
			exit(1);
		}
		BENCHMAX_LOG_DEBUG("benchmax.ssh", "Connected to " << node.username << " @ "<< node.hostname << ":" << node.port);
		
		rc = ssh_userauth_publickey_auto(session, nullptr, nullptr);
		if (rc != SSH_AUTH_SUCCESS) {
			rc = ssh_userauth_password(session, nullptr, node.password.c_str());
			if (rc != SSH_AUTH_SUCCESS) {
				BENCHMAX_LOG_ERROR("benchmax.ssh", "Failed to authenticate as " << node.username << ".");
				exit(1);
			}
		}
		BENCHMAX_LOG_DEBUG("benchmax.ssh", "Authenticated as " << node.username << ".");
	}
	~SSHConnection() {
		while (curChannels > 0) {
			std::this_thread::sleep_for(std::chrono::milliseconds(100));
		}
		ssh_free(session);
	}
	
	bool busy() {
		return curChannels == maxChannels;
	}
	
	bool uploadFile(const fs::path& local, const std::string& remote) {
		sftp_session sftp = getSFTP();
		destroy(sftp);
		return true;
	}
	
	bool uploadFileSCP(const fs::path& local, const std::string& remote) {
		ssh_scp scp = getSCP(SSH_SCP_WRITE | SSH_SCP_RECURSIVE, "");
		int rc;
		SSH_LOCKED(rc = ssh_scp_push_file(scp, remote.c_str(), remote.size(), S_IRUSR | S_IWUSR));
		if (rc != SSH_OK) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", "Failed to create remote file: " << remote);
			return false;
		}
		std::ifstream in(local.native(), std::ios::binary);
		char buf[1024];
		while (!in.eof()) {
			in.read(buf, sizeof(buf));
			ssh_scp_write(scp, buf, in.gcount());
		}
		destroy(scp);
		return true;
	}
	
	bool executeCommand(const std::string& cmd, std::string& output) {
		ssh_channel channel = getChannel();
		int rc;
		SSH_LOCKED(rc = ssh_channel_request_exec(channel, cmd.c_str()));
		if (rc != SSH_OK) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", "Failed to execute: " << cmd);
			return false;
		}
		output = "";
		char buf[512];
		int n;
		SSH_LOCKED(n = ssh_channel_read(channel, buf, sizeof(buf), 0));
		while (n > 0) {
			output += std::string(buf, std::size_t(n));
			SSH_LOCKED(n = ssh_channel_read(channel, buf, sizeof(buf), 0));
		}
		destroy(channel);
		return true;
	}
};

}
}
