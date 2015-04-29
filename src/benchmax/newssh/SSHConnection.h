#pragma once

#include <mutex>
#include <sys/stat.h>
#include <libssh/libssh.h>
#include <libssh/sftp.h>

#include "Node.h"
#include "../Settings.h"
#include "../logging.h"
#include "../BenchmarkStatus.h"
#include "../utils/backend.h"

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
	int verbosity;
	
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
		return sftp;
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
		verbosity = SSH_LOG_NOLOG;
		ssh_options_set(session, SSH_OPTIONS_LOG_VERBOSITY, &verbosity);
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
		ssh_disconnect(session);
		ssh_free(session);
	}
	const Node& getNode() const {
		return node;
	}
	
	bool busy() {
		return curChannels == maxChannels;
	}
	
	std::string createTmpDir(const string& folder) {
		BENCHMAX_LOG_DEBUG("benchmax.ssh", "Creating directory " << folder);
		ssh_scp scp = getSCP(SSH_SCP_WRITE | SSH_SCP_RECURSIVE, Settings::ssh_tmpdir.c_str());
		int rc;
		SSH_LOCKED(rc = ssh_scp_push_directory(scp, folder.c_str(), S_IRWXU));
		if (rc != SSH_OK) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", "Failed to create temporary directory \"" << folder << "\": " << ssh_get_error(session));
			exit(1);
		}
		destroy(scp);
		return Settings::ssh_tmpdir + folder + "/";
	}
	
	void removeDir(const std::string& folder) {
		BENCHMAX_LOG_DEBUG("benchmax.ssh", "Removing directory " << folder);
		sftp_session sftp = getSFTP();
		sftp_dir dir;
		sftp_attributes attr;
		int rc;
		SSH_LOCKED(dir = sftp_opendir(sftp, folder.c_str()));
		if (dir == nullptr) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", "Failed to open directory \"" << folder << "\": " << ssh_get_error(session));
			exit(1);
		}
		while (true) {
			SSH_LOCKED(attr = sftp_readdir(sftp, dir));
			if (attr == nullptr) break;
			if (std::string(attr->name) == ".") continue;
			if (std::string(attr->name) == "..") continue;
			SSH_LOCKED(rc = sftp_unlink(sftp, (folder + std::string(attr->name)).c_str()));
			if (rc != SSH_OK) {
				BENCHMAX_LOG_WARN("benchmax.ssh", "Failed to unlink \"" << attr->name << "\": " << ssh_get_error(session));
			}
			sftp_attributes_free(attr);
		}
		SSH_LOCKED(rc = sftp_closedir(dir));
		if (rc != SSH_OK) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", "Failed to close directory \"" << folder << "\": " << ssh_get_error(session));
			exit(1);
		}
		SSH_LOCKED(rc = sftp_rmdir(sftp, folder.c_str()));
		if (rc != SSH_OK) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", "Failed to remove directory \"" << folder << "\": " << ssh_get_error(session));
			exit(1);
		}
		destroy(sftp);
	}
	
	bool uploadFile(const fs::path& local, const std::string& base, const std::string& remote, int mode = S_IRUSR | S_IWUSR) {
		BENCHMAX_LOG_DEBUG("benchmax.ssh", "Pushing file " << base << remote);
		ssh_scp scp = getSCP(SSH_SCP_WRITE | SSH_SCP_RECURSIVE, base.c_str());
		std::ifstream tmp(local.native(), std::ios::binary | std::ios::ate);
		int rc;
		SSH_LOCKED(rc = ssh_scp_push_file(scp, remote.c_str(), (std::size_t)tmp.tellg(), mode));
		if (rc != SSH_OK) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", "Failed to create remote file: " << ssh_get_error(session));
			return false;
		}
		std::ifstream in(local.native(), std::ios::binary);
		char buf[1024];
		while (!in.eof()) {
			in.read(buf, sizeof(buf));
			std::size_t bytes = (std::size_t)in.gcount();
			SSH_LOCKED(ssh_scp_write(scp, buf, bytes));
		}
		destroy(scp);
		return true;
	}
	
	bool executeCommand(const std::string& cmd, BenchmarkResults& result) {
		BENCHMAX_LOG_DEBUG("benchmax.ssh", "Executing command " << cmd);
		ssh_channel channel = getChannel();
		std::stringstream call;
		call << "date +\"Start: %s%3N\" ; ";
		call << "ulimit -S -t " << Settings::timeLimit << " && ";
		call << "ulimit -S -v " << (Settings::memoryLimit * 1024) << " && ";
		call << cmd << " ; rc=$? ;";
		call << "date +\"End: %s%3N\" ; exit $rc";
		int rc;
		SSH_LOCKED(rc = ssh_channel_request_exec(channel, call.str().c_str()));
		if (rc != SSH_OK) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", "Failed to execute: " << cmd);
			return false;
		}
		result.stdout = "";
		result.stderr = "";
		char buf[512];
		int n;
		SSH_LOCKED(n = ssh_channel_read(channel, buf, sizeof(buf), 0));
		while (n > 0) {
			result.stdout += std::string(buf, std::size_t(n));
			SSH_LOCKED(n = ssh_channel_read(channel, buf, sizeof(buf), 0));
		}
		SSH_LOCKED(n = ssh_channel_read(channel, buf, sizeof(buf), 1));
		while (n > 0) {
			result.stderr += std::string(buf, std::size_t(n));
			SSH_LOCKED(n = ssh_channel_read(channel, buf, sizeof(buf), 1));
		}
		SSH_LOCKED(result.exitCode = ssh_channel_get_exit_status(channel));
		result.time = parseDuration(result.stdout);
		destroy(channel);
		return true;
	}
};

}
}
