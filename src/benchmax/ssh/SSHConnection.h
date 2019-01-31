#pragma once

#include <mutex>
#include <sys/stat.h>
#include <libssh/libssh.h>
#include <libssh/sftp.h>

#include "Node.h"
#include "SSHSettings.h"
#include "../logging.h"
#include "../BenchmarkStatus.h"
#include "../utils/backend.h"
#include "../utils/durations.h"

#define SSH_LOCKED(expr) { std::lock_guard<std::mutex> guard(mutex); expr; }

namespace benchmax {
namespace ssh {
	
class SSHConnection {
private:
	Node node;
	std::size_t curChannels;
	std::size_t maxChannels;
	std::atomic<std::size_t> curJobs;
	ssh_session session;
	std::mutex mutex;
	int verbosity;
	
	ssh_channel getChannel() {
		std::lock_guard<std::mutex> guard(mutex);
		BENCHMAX_LOG_DEBUG("benchmax.ssh", this << " Allocating channel, currently " << curChannels << " / " << maxChannels);
		assert(!busy());
		ssh_channel channel = ssh_channel_new(session);
		if (channel == nullptr) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", this << " Failed to create new ssh channel: " << ssh_get_error(session));
			exit(1);
		}
		int rc = ssh_channel_open_session(channel);
		if (rc != SSH_OK) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", this << " Failed to open ssh channel: " << ssh_get_error(session));
			exit(1);
		}
		curChannels++;
		return channel;
	}
	ssh_scp getSCP(int mode, const std::string& basedir) {
		std::lock_guard<std::mutex> guard(mutex);
		BENCHMAX_LOG_DEBUG("benchmax.ssh", this << " Allocating scp, currently " << curChannels << " / " << maxChannels);
		assert(!busy());
		ssh_scp scp = ssh_scp_new(session, mode, basedir.c_str());
		if (scp == nullptr) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", this << " Failed to create new scp session: " << ssh_get_error(session));
			exit(1);
		}
		int rc = ssh_scp_init(scp);
		if (rc != SSH_OK) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", this << " Failed to initialize scp session: " << ssh_get_error(session));
			exit(1);
		}
		curChannels++;
		return scp;
	}
	sftp_session getSFTP() {
		std::lock_guard<std::mutex> guard(mutex);
		BENCHMAX_LOG_DEBUG("benchmax.ssh", this << " Allocating sftp, currently " << curChannels << " / " << maxChannels);
		assert(!busy());
		sftp_session sftp = sftp_new(session);
		if (sftp == nullptr) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", this << " Failed to create new sftp session: " << ssh_get_error(session));
			exit(1);
		}
		int rc = sftp_init(sftp);
		if (rc != SSH_OK) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", this << " Failed to initialize sftp session: " << ssh_get_error(session));
			exit(1);
		}
		curChannels++;
		return sftp;
	}
	void destroy(ssh_channel channel) {
		std::lock_guard<std::mutex> guard(mutex);
		BENCHMAX_LOG_DEBUG("benchmax.ssh", this << " Destroying channel, currently " << curChannels << " / " << maxChannels);
		ssh_channel_close(channel);
		ssh_channel_free(channel);
		curChannels--;
	}
	void destroy(ssh_scp scp) {
		std::lock_guard<std::mutex> guard(mutex);
		BENCHMAX_LOG_DEBUG("benchmax.ssh", this << " Destroying scp, currently " << curChannels << " / " << maxChannels);
		ssh_scp_close(scp);
		ssh_scp_free(scp);
		curChannels--;
	}
	void destroy(sftp_session sftp) {
		std::lock_guard<std::mutex> guard(mutex);
		BENCHMAX_LOG_DEBUG("benchmax.ssh", this << " Destroying sftp, currently " << curChannels << " / " << maxChannels);
		sftp_free(sftp);
		curChannels--;
	}
public:
	SSHConnection(const Node& n): node(n), curChannels(0), maxChannels(node.cores), curJobs(0) {
		session = ssh_new();
		if (session == nullptr) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", this << " Failed to create SSH session.");
		}
		verbosity = SSH_LOG_NOLOG;
		ssh_options_set(session, SSH_OPTIONS_LOG_VERBOSITY, &verbosity);
		ssh_options_set(session, SSH_OPTIONS_HOST, node.hostname.c_str());
		ssh_options_set(session, SSH_OPTIONS_PORT, &(node.port));
		ssh_options_set(session, SSH_OPTIONS_USER, node.username.c_str());
		
		int rc = ssh_connect(session);
		if (rc != SSH_OK) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", this << " Failed to connect to " << node.username << "@" << node.hostname);
			exit(1);
		}
		BENCHMAX_LOG_DEBUG("benchmax.ssh", this << " Connected to " << node.username << "@"<< node.hostname);
		
		rc = ssh_userauth_publickey_auto(session, nullptr, nullptr);
		if (rc != SSH_AUTH_SUCCESS) {
			rc = ssh_userauth_password(session, nullptr, node.password.c_str());
			if (rc != SSH_AUTH_SUCCESS) {
				BENCHMAX_LOG_ERROR("benchmax.ssh", this << " Failed to authenticate as " << node.username << ".");
				exit(1);
			}
		}
		BENCHMAX_LOG_DEBUG("benchmax.ssh", this << " Authenticated as " << node.username << ".");
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
	bool jobFree() {
		return curJobs < maxChannels;
	}
	void newJob() {
		assert(curJobs < maxChannels);
		curJobs++;
	}
	void finishJob() {
		curJobs--;
	}
	std::size_t jobs() const {
		return curJobs;
	}
	bool busy() {
		//BENCHMAX_LOG_DEBUG("benchmax.ssh", "Currently " << curChannels << " / " << maxChannels);
		return curChannels >= maxChannels;
	}
	
	std::string createTmpDir(const std::string& folder) {
		BENCHMAX_LOG_DEBUG("benchmax.ssh", this << " Creating directory " << folder);
		ssh_scp scp = getSCP(SSH_SCP_WRITE | SSH_SCP_RECURSIVE, settings_ssh().tmpdir.c_str());
		int rc;
		SSH_LOCKED(rc = ssh_scp_push_directory(scp, folder.c_str(), S_IRWXU));
		if (rc != SSH_OK) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", this << " Failed to create temporary directory \"" << folder << "\": " << ssh_get_error(session));
			exit(1);
		}
		destroy(scp);
		return settings_ssh().tmpdir + folder + "/";
	}
	
	void removeDir(const std::string& folder) {
		BENCHMAX_LOG_DEBUG("benchmax.ssh", this << " Removing directory " << folder);
		sftp_session sftp = getSFTP();
		sftp_dir dir;
		sftp_attributes attr;
		int rc;
		SSH_LOCKED(dir = sftp_opendir(sftp, folder.c_str()));
		if (dir == nullptr) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", this << " Failed to open directory \"" << folder << "\": " << ssh_get_error(session));
			exit(1);
		}
		while (true) {
			SSH_LOCKED(attr = sftp_readdir(sftp, dir));
			if (attr == nullptr) break;
			if (std::string(attr->name) == ".") continue;
			if (std::string(attr->name) == "..") continue;
			SSH_LOCKED(rc = sftp_unlink(sftp, (folder + std::string(attr->name)).c_str()));
			if (rc != SSH_OK) {
				BENCHMAX_LOG_WARN("benchmax.ssh", this << " Failed to unlink \"" << attr->name << "\": " << ssh_get_error(session));
			}
			sftp_attributes_free(attr);
		}
		SSH_LOCKED(rc = sftp_closedir(dir));
		if (rc != SSH_OK) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", this << " Failed to close directory \"" << folder << "\": " << ssh_get_error(session));
			exit(1);
		}
		SSH_LOCKED(rc = sftp_rmdir(sftp, folder.c_str()));
		if (rc != SSH_OK) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", this << " Failed to remove directory \"" << folder << "\": " << ssh_get_error(session));
			exit(1);
		}
		destroy(sftp);
	}
	
	bool uploadFile(const fs::path& local, const std::string& base, const std::string& remote, int mode = S_IRUSR | S_IWUSR) {
		BENCHMAX_LOG_DEBUG("benchmax.ssh", this << " Pushing file " << base << remote);
		ssh_scp scp = getSCP(SSH_SCP_WRITE | SSH_SCP_RECURSIVE, base.c_str());
		std::ifstream tmp(local.native(), std::ios::binary | std::ios::ate);
		int rc;
		SSH_LOCKED(rc = ssh_scp_push_file(scp, remote.c_str(), (std::size_t)tmp.tellg(), mode));
		if (rc != SSH_OK) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", this << " Failed to create remote file " << remote << " from local file " << local << ": " << ssh_get_error(session));
			destroy(scp);
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
	
	bool executeCommand(const std::string& cmd, BenchmarkResult& result) {
		BENCHMAX_LOG_DEBUG("benchmax.ssh", this << " Executing command " << cmd);
		ssh_channel channel = getChannel();
		std::stringstream call;
		call << "date +\"Start: %s%3N\" ; ";
		auto timeout = (seconds(settings_benchmarks().limit_time) + std::chrono::seconds(3)).count();
		if (settings_benchmarks().use_wallclock) call << "timeout " << timeout << "s ";
		else call << "ulimit -S -t " << timeout << " && ";
		call << "ulimit -S -v " << (settings_benchmarks().limit_memory * 1024) << " && ";
		call << cmd << " ; rc=$? ;";
		call << "date +\"End: %s%3N\" ; exit $rc";
		int rc;
		SSH_LOCKED(rc = ssh_channel_request_exec(channel, call.str().c_str()));
		if (rc != SSH_OK) {
			BENCHMAX_LOG_ERROR("benchmax.ssh", this << " Failed to execute: " << cmd);
			return false;
		}
		result.stdout = "";
		result.stderr = "";
		bool collectOutput = true;
		char buf[512];
		int n;
		int eof = 0;
		while (eof == 0) {
			SSH_LOCKED(eof = ssh_channel_is_eof(channel));
			SSH_LOCKED(n = ssh_channel_read_nonblocking(channel, buf, sizeof(buf), 0));
			if (n > 0 && collectOutput) result.stdout += std::string(buf, std::size_t(n));
			SSH_LOCKED(n = ssh_channel_read_nonblocking(channel, buf, sizeof(buf), 1));
			if (n > 0 && collectOutput) result.stderr += std::string(buf, std::size_t(n));
			collectOutput = (result.stdout.size() < 10240) && (result.stderr.size() < 10240);
			std::this_thread::yield();
			std::this_thread::sleep_for(std::chrono::milliseconds(10));
		}
		if (!collectOutput) {
			result.additional.emplace("output", "truncated");
		} else {
			BENCHMAX_LOG_DEBUG("benchmax.ssh", "stdout = " << result.stdout);
			BENCHMAX_LOG_DEBUG("benchmax.ssh", "stderr = " << result.stderr);
		}
		SSH_LOCKED(result.exitCode = ssh_channel_get_exit_status(channel));
		result.time = parseDuration(result.stdout);
		destroy(channel);
		return true;
	}
};

}
}
