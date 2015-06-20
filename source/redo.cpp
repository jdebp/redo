/* COPYING ******************************************************************
For copyright and licensing terms, see the file named COPYING.
// **************************************************************************
*/

#include <string>
#include <list>
#include <map>
#include <vector>
#include <iostream>
#include <iomanip>
#include <fstream>
#include <sstream>
#include <cassert>
#include <cctype>
#include <cstring>
#include <cstdio>
#include <cstdlib>
#include <climits>
#include <cerrno>
#include <ctime>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>
#include <poll.h>
#if defined(__OS2__) || defined(__WIN32__) || defined(__NT__)
#include <direct.h>	// for mkdir()
#include <process.h>	// for spawn()
#else
#include <sys/wait.h>
#include <ftw.h>
#endif
#include "popt.h"
#include "CubeHash.h"
#if defined(__unix__) || defined(__UNIX__) || (defined(__APPLE__) && defined(__MACH__)) || defined(__INTERIX)
extern "C" char ** environ;
#endif

struct catchall_definition : public popt::definition {
public:
	catchall_definition() {}
	virtual bool execute(popt::processor &, char) { return true; }
	virtual bool execute(popt::processor &, char, const char *) { return true; }
	virtual bool execute(popt::processor &, const char *) { return true; }
	virtual ~catchall_definition() {}
};

struct special_string_definition : public popt::string_definition {
public:
	special_string_definition(char s, const char * l, const char * a, const char * d, const char * & v) : string_definition(s, l, a, d, v) {}
	virtual bool execute(popt::processor &, char) { return false; }
	virtual bool execute(popt::processor &, char, const char *) { return false; }
	virtual bool execute(popt::processor &, const char * s)
	{
		if (const char * long_name = query_long_name()) {
			const std::size_t len(std::strlen(long_name));
			if (0 == std::memcmp(long_name, s, len) && '=' == s[len]) {
				value = s + len + 1;
				return true;
			}
		}
		return false;
	}
};

enum { MAX_META_DEPTH = 1U };
static bool keep_going(false);
static bool debug(false);
static bool silent(false);
static bool verbose(false);
static int jobserver_fds[2] = { -1, -1 };
static int redoparent_fd = -1;
static std::string makelevel;

static
std::ostream &
msg (
	const char * prog,
	const char * prefix
) {
	std::clog << prog;
	if (!makelevel.empty())
		std::clog << "[" << makelevel << "]";
	return std::clog << ": " << prefix << ": ";
}

/* Filename manipulation ****************************************************
// **************************************************************************
*/

static inline
const char *
extension (
	const char * s
) {
	if (const char * dot = std::strchr(s, '.'))
		return dot;
	return std::strchr(s, '\0');
}

static inline
const char *
basename_of (
	const char * s
) {
	if (const char * slash = std::strrchr(s, '/'))
		s = slash + 1;
#if defined(__OS2__) || defined(__WIN32__) || defined(__NT__)
	else if (const char * bslash = std::strrchr(s, '\\'))
		s = bslash + 1;
	else if (std::isalpha(s[0]) && ':' == s[1])
		s += 2;
#endif
	return s;
}

/* Wrappers for POSIX API calls. ********************************************
// **************************************************************************
*/

static inline
int
posix_rename (
	const char * old_name,
	const char * new_name
) {
#if defined(__OS2__) || defined(__WIN32__) || defined(__NT__)
	int r = std::remove(new_name);
	if (0 > r && ENOENT != errno) return r;
#endif
	return std::rename(old_name, new_name);
}

static inline
int
posix_lstat (
	const char * name,
	struct stat * buf
) {
#if defined(__OS2__) || defined(__WIN32__) || defined(__NT__)
	return stat(name, buf);
#else
	return lstat(name, buf);
#endif
}

static inline
int
posix_mkdir (
	const char * name,
	unsigned int mode
) {
#if defined(__OS2__) || defined(__WIN32__) || defined(__NT__)
	mode = mode;
	return mkdir(name);
#else
	return mkdir(name, mode);
#endif
}

#if defined(__OS2__) || defined(__WIN32__) || defined(__NT__)
static inline
int
rmrf(const char *path)
{
	return errno = ENOSYS, -1;
}
#else
static
int
unlink_cb(const char *fpath, const struct stat *, int typeflag, struct FTW *)
{
	switch (typeflag) {
		case FTW_D:
		case FTW_DP:
		case FTW_DNR:
		case FTW_F:
		case FTW_SL:
			return std::remove(fpath);
		default:
			return errno = EINVAL, -1;
	}
}

static inline
int
rmrf(const char *path)
{
	struct stat stbuf;
	if (0 <= posix_lstat(path, &stbuf) && S_ISDIR(stbuf.st_mode))
		return nftw(path, unlink_cb, 64, FTW_DEPTH | FTW_PHYS);
	else
		return std::remove(path);
}
#endif

#if !defined(__OS2__) && !defined(__WIN32__) && !defined(__NT__)
enum { P_WAIT, P_NOWAIT };
static inline
int
spawnve (
	int mode,
	const char * prog,
	const char * argv[],
	const char * envv[]
) {
	std::clog << std::flush;
	int pid = fork();
	if (0 > pid)
		return pid;
	else if (0 == pid) {
		execve(prog, const_cast<char **>(argv), const_cast<char **>(envv));
		const int error(errno);
		std::clog << prog << ": " << std::strerror(error) << '\n' << std::flush;
		_exit(255);
	} else {
		if (P_WAIT != mode) return pid;
		int status;
		int r = waitpid(pid, &status, 0);
		if (0 > r) return r;
		if (WIFEXITED(status)) return WEXITSTATUS(status);
		return 255;
	}
}
#endif

static
void
makepath (
	const std::string & dir
) {
	const char * arg(dir.c_str());
	const char * b(basename_of(arg));
	if (b != arg)
		makepath(std::string(arg, static_cast<std::size_t>(b - 1 - arg)));
	posix_mkdir(arg, 0777);
}

/* string manipulation ******************************************************
// **************************************************************************
*/

static inline
int
x2d (
	char c
) {
	if (!std::isxdigit(c)) return -1;
	if (std::isdigit(c)) return c - '0';
	if (std::isupper(c)) return c - 'A' + 10;
	if (std::islower(c)) return c - 'a' + 10;
	return -1;
}

static inline
std::list<std::string>
split(
	const char * s,
	bool prefixdash
) {
	std::list<std::string> l;
	if (prefixdash && *s && std::isspace(*s)) prefixdash = false;
	for (;;) {
		while (!prefixdash && *s && std::isspace(*s)) ++s;
		if (!*s) break;
		std::string r(prefixdash ? "-" : "");
		prefixdash = false;
		bool quoted(false);
		while (char c = *s) {
			if ('\"' == c)
				quoted = !quoted;
			else if ('\\' == c) {
				c = *++s;
				if (c)
					r += c;
				else {
					r += '\\';
					break;
				}
			} else if (!quoted && std::isspace(c))
				break;
			else
				r += c;
			++s;
		}
		l.push_back(r);
	}
	return l;
}

static
std::vector<const char *>
convert (
	const std::list<std::string> & s
) {
	std::vector<const char *> v;
	for (std::list<std::string>::const_iterator i(s.begin()); s.end() != i; ++i)
		v.push_back(i->c_str());
	return v;
}

/* struct Information and the cache of directory entry information **********
// **************************************************************************
*/

struct Information {
	enum { NOTHING, SPECIAL, DIRECTORY, FILE } type;
	std::time_t last_written;
	unsigned char hash[32];		// 256 bits
};

static inline
Information
read_file_info (
	const std::string & name,
	const Information * old_info
) {
	Information i;
	struct stat stbuf;
	if (0 > posix_lstat(name.c_str(), &stbuf)) {
		i.type = i.NOTHING;
		i.last_written = -1;
		for ( std::size_t j(0);j < sizeof i.hash/sizeof *i.hash; ++j)
			i.hash[j] = 0;
	} else {
		i.last_written = stbuf.st_mtime;
		if (S_ISREG(stbuf.st_mode)) {
			i.type = i.FILE;
			if (old_info && old_info->last_written == i.last_written) {
				memmove(i.hash, old_info->hash, sizeof i.hash);
			} else {
				// This is Dan Bernstein's SHA-3-AHS256 proposal from 2010-11.
				CubeHash h(16U, 16U, 32U, 32U, 8U * sizeof i.hash/sizeof *i.hash);
				std::ifstream f(name.c_str(), std::ios::binary);
				if (!f.fail()) {
					char buf[4096];
					for (;;) {
						f.read(buf, sizeof buf);
						h.Update(reinterpret_cast<unsigned char *>(buf), static_cast<std::size_t>(f.gcount()));
						if (f.eof()) break;
					}
				}
				h.Final();
				for ( std::size_t j(0);j < sizeof i.hash/sizeof *i.hash; ++j)
					i.hash[j] = h.hashval[j];
			}
		} else {
			if (S_ISDIR(stbuf.st_mode))
				i.type = i.DIRECTORY;
			else
				i.type = i.SPECIAL;
			for ( std::size_t j(0);j < sizeof i.hash/sizeof *i.hash; ++j)
				i.hash[j] = 0;
		}
	}
	return i;
}

typedef std::map<std::string, Information> InfoMap;
static InfoMap file_info_map;

static
Information &
get_file_info (
	const std::string & name,
	const Information * old_info
) {
	InfoMap::iterator f(file_info_map.find(name));
	if (f == file_info_map.end())
		f = file_info_map.insert(InfoMap::value_type(name, read_file_info(name, old_info))).first;
	return f->second;
}

static inline
void
delete_file_info (
	const std::string & name
) {
	file_info_map.erase(name);
}

/* Parsing and updating of the .redo database *******************************
// **************************************************************************
*/

static inline
void
read_db_line (
	std::istream & s,
	Information & i,
	std::string & name
) {
	switch (int c = s.get()) {
		default:
		case EOF:
		case 'a':
			i.type = i.NOTHING;
			break;
		case 's':
			i.type = i.SPECIAL;
			goto atime;
		case 'd':
			i.type = i.DIRECTORY;
			goto atime;
		case 'f':
			i.type = i.FILE;
			goto cksum;
		cksum:
		{
#if defined(__WATCOMC__)
			s.setf(s.skipws);
			s.ipfx(0);
#else
			s >> std::skipws;
			std::istream::sentry ipfx(s, /*noskipws=*/false);
#endif
			for ( std::size_t j(0);j < sizeof i.hash/sizeof *i.hash; ++j) {
				char two[2];
				s.read(two, 2);
				i.hash[j] = static_cast<unsigned char>(x2d(two[0]) << 4) + static_cast<unsigned char>(x2d(two[1]));
			}
#if defined(__WATCOMC__)
			s.isfx();
			s.unsetf(s.skipws);
#else
			s >> std::noskipws;
#endif
		}
		atime:
#if defined(__WATCOMC__)
			s.setf(s.skipws);
#else
			s >> std::skipws;
#endif
			s >> std::hex >> i.last_written >> std::dec;
#if defined(__WATCOMC__)
			s.unsetf(s.skipws);
#else
			s >> std::noskipws;
#endif
			break;
		// FIXME: Delete this special case once we switch to the new .redo database filenames.
		case '\n':
		case '\t':
		case '\f':
		case '\b':
		case '\v':
		case '\r':
		case ' ':
		{
			char md5sum[128/8];
			i.type = i.FILE;
#if defined(__WATCOMC__)
			s.setf(s.skipws);
#else
			s >> std::skipws;
#endif
			s >> name >> std::hex >> i.last_written >> std::dec;
			for (std::size_t j(0); j < sizeof md5sum/sizeof *md5sum; ++j) {
				char two[2];
				s.read(two, 2);
				md5sum[j] = static_cast<char>(x2d(two[0]) << 4) + static_cast<char>(x2d(two[1]));
			}
#if defined(__WATCOMC__)
			s.unsetf(s.skipws);
#else
			s >> std::noskipws;
#endif
			return;
		}
	}
	while (!s.eof() && std::isspace(s.peek()))
		s.get();
	char namebuf[PATH_MAX];
	s.getline(namebuf, sizeof namebuf);
	name = namebuf;
}

static inline
void
write_db_line (
	std::ostream & s,
	const Information & info,
	const char * name
) {
	switch (info.type) {
		case Information::NOTHING:	s.put('a') << name << '\n'; break;
		case Information::SPECIAL:	s.put('s') << std::hex << info.last_written << ' ' << std::dec << name << '\n'; break;
		case Information::DIRECTORY:	s.put('d') << std::hex << info.last_written << ' ' << std::dec << name << '\n'; break;
		case Information::FILE:
			s.put('f') << std::hex << std::setfill('0');
			for ( std::size_t j(0);j < (sizeof info.hash/sizeof *info.hash); ++j)
				s << std::setw(2) << static_cast<unsigned int>(info.hash[j]);
			s << ' ' << info.last_written << ' ' << std::setfill(' ') << std::dec << name << '\n';
			break;
	}
}

static inline
void
puthash (
	std::ostream & s,
	const Information & info
) {
	s << std::hex << std::setfill('0');
	for ( std::size_t j(0);j < sizeof info.hash/sizeof *info.hash; ++j)
		s << std::setw(2) << static_cast<unsigned int>(info.hash[j]);
	s << std::setfill(' ') << std::dec;
}

/* The GNU make jobserver ***************************************************
// **************************************************************************
*/

static unsigned implicit_jobs = 1;

static inline
bool
try_procure_job_slot(
	const char * prog
) {
	if (implicit_jobs) {
		--implicit_jobs;
		if (debug) {
			msg(prog, "INFO") << "Re-using implicit job slot that is this process itself.\n";
		}
		return true;
	}
	if (-1 != jobserver_fds[0]) {
		pollfd p;
		p.fd = jobserver_fds[0];
		p.events = POLLIN;
		const int r0(poll(&p, sizeof p/sizeof(pollfd), 0));
		if ((0 <= r0) && (p.revents & POLLIN)) {
			char c;
			const int r(read(jobserver_fds[0], &c, sizeof c));
			if (debug) {
				if (0 < r)
					msg(prog, "INFO") << "Procured a job slot from the jobserver.\n";
				else
					msg(prog, "INFO") << "Failed to procure a job slot from the jobserver.\n";
			}
			return 0 < r;
		}
	}
	return false;
}

static inline
bool
procure_job_slot(
	const char * prog
) {
	if (implicit_jobs) {
		--implicit_jobs;
		if (debug) {
			msg(prog, "INFO") << "Re-using implicit job slot that is this process itself.\n";
		}
		return true;
	}
	if (-1 != jobserver_fds[0]) {
		char c;
		const int r(read(jobserver_fds[0], &c, sizeof c));
		if (debug) {
			if (0 < r)
				msg(prog, "INFO") << "Procured a job slot from the jobserver.\n";
			else
				msg(prog, "INFO") << "Failed to procure a job slot from the jobserver.\n";
		}
		return 0 < r;
	}
	return false;
}

static inline
void
vacate_job_slot(
	const char * prog
) {
	if (-1 != jobserver_fds[1]) {
		const char c('\0');
		write(jobserver_fds[1], &c, sizeof c);
		if (debug) {
			msg(prog, "INFO") << "Vacated a job slot to the jobserver.\n";
		}
	} else
		++implicit_jobs;
}

/* Redo internals ***********************************************************
// **************************************************************************
*/

static inline
bool
record_prerequisites (
	const char * prog,
	const std::vector<const char *> & filev
) {
	if (-1 == redoparent_fd) {
		msg(prog, "ERROR") << "Not invoked within a .do script.\n";
		return false;
	}
	if (debug) {
		msg(prog, "INFO") << "RECORD-PREREQUISITES: >";
		for ( std::vector<const char *>::const_iterator i = filev.begin(); i != filev.end(); ++i ) {
			const char * arg(*i);
			std::clog << ' ' << arg;
		}
		std::clog << '<' << std::endl;
	}

	std::ostringstream tmp_db;
	for ( std::vector<const char *>::const_iterator i = filev.begin(); i != filev.end(); ++i ) {
		const char * arg(*i);
		const Information & info(get_file_info(arg, 0));
		write_db_line(tmp_db, info, arg);
		if (tmp_db.fail()) {
			int error = errno;
			msg(prog, "ERROR") << std::strerror(error) << "\n";
			return false;
		}
	}
	const std::string & s(tmp_db.str());
	if (0 > write(redoparent_fd, s.c_str(), s.length())) {
		int error = errno;
		msg(prog, "ERROR") << std::strerror(error) << "\n";
		return false;
	}

	return true;
}

static inline bool redo (bool, const char * prog, unsigned meta_depth, const std::vector<const char *> & filev);

static
bool
redo_ifcreate (
	const char * prog,
	const std::vector<const char *> & filev
) {
	bool status(true);
	for ( std::vector<const char *>::const_iterator i = filev.begin(); i != filev.end(); ++i ) {
		const char * arg(*i);
		if (0 <= access(arg, F_OK)) {
			msg(prog, "ERROR") << arg << ": File/directory exists.\n";
			status = false;
			continue;
		}
	}
	if (!status) return status;

	return record_prerequisites (prog, filev);
}

static inline
bool
redo_ifcreate_1 (
	const char * prog,
	const char * file
) {
	std::vector<const char *> filev;
	filev.push_back(file);
	return redo_ifcreate(prog, filev);
}

static inline
bool
redo_ifchange (
	const char * prog,
	unsigned meta_depth,
	const std::vector<const char *> & filev
) {
	return redo(false, prog, meta_depth, filev) && record_prerequisites(prog, filev);
}

static inline
bool
redo_ifchange_1 (
	const char * prog,
	unsigned meta_depth,
	const char * file
) {
	std::vector<const char *> filev;
	filev.push_back(file);
	return redo_ifchange(prog, meta_depth, filev);
}

static inline
bool
find_do_file (
	const char * prog,
	unsigned meta_depth,
	const char * const arg,
	const char * const b,
	std::string & dofile_name,
	std::string & base,
	std::string & ext
) {
	const char * const be(extension(b));
	std::string dir(arg, static_cast<std::size_t>(b - arg));
	for (;;) {
		base = b;
		ext = std::string();
		dofile_name = dir + base + ".do";
		if (0 <= access(dofile_name.c_str(), F_OK)) {
			redo_ifchange_1(prog, meta_depth + 1, dofile_name.c_str());
			return true;
		} else
			redo_ifcreate_1(prog, dofile_name.c_str());

		for (const char * e(be); ; e = extension(e + 1)) {
			base = std::string(b, static_cast<std::size_t>(e - b));
			ext = e;
			dofile_name = dir + "default" + ext + ".do";
			if (0 <= access(dofile_name.c_str(), F_OK)) {
				redo_ifchange_1(prog, meta_depth + 1, dofile_name.c_str());
				return true;
			} else
				redo_ifcreate_1(prog, dofile_name.c_str());

			if (!*e) break;
		}

		std::string::size_type len(dir.length());
		if (len < 2) return false;
		std::string::size_type slash(dir.find_last_of('/', len - 2));
#if defined(__OS2__) || defined(__WIN32__) || defined(__NT__)
		if (std::string::npos == slash)
			slash = dir.find_last_of('\\', len - 2);
#endif
		if (std::string::npos == slash)
			dir = std::string();
		else
			dir = dir.substr(0, slash + 1);
	}
}

/* Jobs *********************************************************************
// **************************************************************************
*/

class RedoParentFDStack {
public:
	RedoParentFDStack ( int new_fd ) : old_fd(redoparent_fd) { redoparent_fd = new_fd; }
	~RedoParentFDStack() { redoparent_fd = old_fd; }
protected:
	int old_fd;
};

struct Job {
	int lock_fd, pid;
	const char * arg;
	std::string target;
	std::string tmp_target;
	std::string script;
	std::string database_name;
	std::string tmp_database_name;
	std::string lock_database_name;
};

static inline
bool
run (
#if defined(__OS2__) || defined(__WIN32__) || defined(__NT__)
	const char * comspec,
#endif
	const char * prog,
	unsigned meta_depth,
	Job & job
) {
	job.pid = -1;

	const char * b(basename_of(job.arg));
	if (b != job.arg)
		makepath(".redo/" + std::string(job.arg, static_cast<std::size_t>(b - 1 - job.arg)));

#if defined(__OS2__) || defined(__WIN32__) || defined(__NT__)
	int lock_fd(open(job.lock_database_name.c_str(), O_WRONLY|O_TRUNC|O_CREAT, 0777));
#else		
	int lock_fd(open(job.lock_database_name.c_str(), O_WRONLY|O_TRUNC|O_CREAT|O_NOCTTY, 0777));
#endif		
	if (0 > lock_fd) {
		const int error(errno);
		msg(prog, "ERROR") << job.lock_database_name << ": " << std::strerror(error) << "\n";
		return false;
	}
#if defined(__OS2__) || defined(__WIN32__) || defined(__NT__)
#else
	if (debug) {
		msg(prog, "INFO") << job.lock_database_name << ": Locking ...\n";
	}
	struct flock flock;
	flock.l_whence = SEEK_SET;
	flock.l_start = 0;
	flock.l_len = 0;
	flock.l_type = F_WRLCK;
	int f(fcntl(lock_fd, F_SETLKW, &flock));
	if (0 > f) {
		const int error(errno);
		msg(prog, "ERROR") << job.lock_database_name << ": " << std::strerror(error) << "\n";
		close(lock_fd);
		return false;
	}
#endif
#if defined(__OS2__) || defined(__WIN32__) || defined(__NT__)		
	int db_fd(open(job.tmp_database_name.c_str(), O_WRONLY|O_TRUNC|O_CREAT, 0777));
#else		
	int db_fd(open(job.tmp_database_name.c_str(), O_WRONLY|O_TRUNC|O_CREAT|O_NOCTTY, 0777));
#endif		
	if (0 > db_fd) {
		const int error(errno);
		msg(prog, "ERROR") << job.tmp_database_name << ": " << std::strerror(error) << "\n";
		close(lock_fd);
		return false;
	}

	RedoParentFDStack saved_parent(db_fd);
	std::string dofile_name, dir(job.arg, static_cast<std::size_t>(b - job.arg)), base, ext;
	if (!find_do_file(prog, meta_depth, job.arg, b, dofile_name, base, ext)) {
		msg(prog, "ERROR") << job.arg << ": Cannot find .do file to use.\n";
		close(db_fd);
		close(lock_fd);
		return false;
	}
	const std::string fullbase(dir + base);
	std::remove(job.tmp_target.c_str());
#if defined(__OS2__) || defined(__WIN32__) || defined(__NT__)
	if (ext.empty()) ext = ".";	// There is a bug in the Interix sh.bat that causes it to lose empty arguments.
#endif

	job.lock_fd = lock_fd;
	job.script = dofile_name;

#if !defined(__OS2__) && !defined(__WIN32__) && !defined(__NT__)
	const char * comspec(job.script.c_str());
#endif
	const char * argv[9] = {
#if defined(__OS2__) || defined(__WIN32__) || defined(__NT__)
		comspec,
		"/c",
		"sh",
		"-e",
#endif
		dofile_name.c_str(),
		fullbase.c_str(),
		ext.c_str(),
		job.tmp_target.c_str(),
		NULL
	};
	std::vector<const char *> envv;
	for (char **e(environ); *e; ++e)
		envv.push_back(*e);
	std::ostringstream redoflags;
	redoflags << "REDOFLAGS=";
	if (keep_going) redoflags << " --keep-going";
	if (debug) redoflags << " --debug";
	if (silent) redoflags << " --silent";
	if (verbose) redoflags << " --verbose";
	if (-1 != db_fd) redoflags << " --redoparent-fd=" << db_fd;
	if (-1 != jobserver_fds[0]) {
		redoflags << " --jobserver-fds=" << jobserver_fds[0];
		if (-1 != jobserver_fds[1])
			redoflags << "," << jobserver_fds[1];
	}
	const std::string redoflags_str(redoflags.str());
	envv.push_back(redoflags_str.c_str());
	envv.push_back(0);

	if (verbose)
		msg(prog, "INFO") << "spawn: " << dofile_name << " " << fullbase << " " << ext << " " << job.tmp_target << "\n" << std::flush;
	job.pid = spawnve(P_NOWAIT, comspec, argv, const_cast<const char **>(&envv.front()));
	close(db_fd);

	return true;
}

static inline
bool
finish (
	const char * prog,
	Job & job,
	int exit_status
) {
	job.pid = -1;
	if (!WIFEXITED(exit_status) || (0 < WEXITSTATUS(exit_status))) {
		msg(prog, "ERROR") << job.target << ": Not done.\n";
		rmrf(job.tmp_target.c_str());
		close(job.lock_fd); 
		return false;
	}
	struct stat stbuf;
	if (0 > posix_lstat(job.tmp_target.c_str(), &stbuf)) {
		std::ofstream tmp(job.tmp_target.c_str(), std::ios::app);
	}
	if ((0 <= posix_lstat(job.target.c_str(), &stbuf)) && S_ISDIR(stbuf.st_mode)) {
		if (0 > rmrf(job.target.c_str())) {
			const int error(errno);
			msg(prog, "ERROR") << job.target << ": Unable to remove contents of target directory: " << std::strerror(error) << "\n";
			rmrf(job.tmp_target.c_str());
			close(job.lock_fd); 
			return false;
		}
	}
	delete_file_info(job.target);
	if (0 > posix_rename(job.tmp_database_name.c_str(), job.database_name.c_str())) {
		const int error(errno);
		msg(prog, "ERROR") << job.tmp_database_name << ": Unable to rename database file: " << std::strerror(error) << "\n";
		rmrf(job.tmp_target.c_str());
		close(job.lock_fd); 
		return false;
	}
	if (0 > posix_rename(job.tmp_target.c_str(), job.target.c_str())) {
		const int error(errno);
		msg(prog, "ERROR") << job.target << ": Unable to rename target file: " << std::strerror(error) << "\n";
		rmrf(job.tmp_target.c_str());
		close(job.lock_fd); 
		return false;
	}
	if (!silent) {
		msg(prog, "INFO") << job.target << ": Redone.\n" << std::flush;
	}
	close(job.lock_fd); 
	return true;
}

static inline
bool
run (
	const char * prog,
	unsigned meta_depth,
	std::list<Job> & jobs
) {
	bool status = true;
#if defined(__OS2__) || defined(__WIN32__) || defined(__NT__)
	const char * comspec(std::getenv("COMSPEC"));
	if (!comspec) {
		msg(prog, "ERROR") << "Cannot find command interpreter.\n";
		return false;
	}
#endif
	std::list<Job>::iterator bi(jobs.begin()), ri(bi), ai(ri), ei(jobs.end());
	while (ai != ei) {
		if (debug) {
			if (ri != ei)
				msg(prog, "INFO") << "Jobs still available to start.\n";
			if (ai != ri)
				msg(prog, "INFO") << "Jobs still available to await.\n";
		}
		while ((ri != ei) && try_procure_job_slot(prog)) {
			if (!run(prog, meta_depth, *ri)) {
				status = false;
				vacate_job_slot(prog);
			} else if (0 > ri->pid) {
				const int error(errno);
				msg(prog, "ERROR") << ri->script << ": " << std::strerror(error) << "\n";
				status = false;
				vacate_job_slot(prog);
			}
			++ri;
		}
		while ((ai != ri) && (0 > ai->pid)) {
			++ai;
		}
		if (ai != ri) {
			int exit_status;
			const int pid(waitpid(-1, &exit_status, 0));
			if (0 > pid) {
				const int error(errno);
				msg(prog, "ERROR") << std::strerror(error) << "\n";
				status = false;
				continue;
			}
			bool found = false;
			for ( std::list<Job>::iterator i(ai); i != ri; ++i ) {
				if (pid == i->pid) {
					if (!finish(prog, *i, exit_status))
						status = false;
					found = true;
				}
			}
			if (!found) {
				msg(prog, "ERROR") << "Unknown child process ID " << pid << ".\n";
			}
			vacate_job_slot(prog);
		}
	}
	return status;
}

/* Redo internals ***********************************************************
// **************************************************************************
*/

static inline
bool
exists(
	const std::string & name
) {
	return 0 <= access(name.c_str(), F_OK);
}

static inline
bool
satisfies_existence (
	const char * prog,
	const std::string & target_name
) {
	if (!exists(target_name)) {
		if (verbose)
			msg(prog, "INFO") << target_name << " needs rebuilding because it does not exist.\n";
		return false;
	}
	return true;
}

static inline
bool
satisfies_prerequisites (
	const char * prog,
	const std::string & target_name
) {
	const std::string database_name(".redo/" + target_name + ".prereqs");
	std::ifstream file(database_name.c_str());
	if (file.fail()) return false;
	bool satisfaction(true);
	while (EOF != file.peek()) {
		Information db_info;
		std::string prereq_name;
		read_db_line(file, db_info, prereq_name);
		const Information & fs_info(get_file_info(prereq_name, &db_info));
		if (db_info.type != fs_info.type) {
			if (verbose) {
				msg(prog, "INFO") << target_name << " needs rebuilding because " << prereq_name;
				if (fs_info.NOTHING == fs_info.type)
					std::clog << " does not exist.\n";
				else
					std::clog << " has changed type.\n";
			}
			satisfaction = false;
			if (!keep_going) break;
		} else
		if (fs_info.NOTHING != fs_info.type
		&&  fs_info.last_written != db_info.last_written
		) {
			if (fs_info.SPECIAL == fs_info.type || fs_info.DIRECTORY == fs_info.type) {
				if (verbose) {
					char fs_buf[64], db_buf[64];
					struct std::tm fs_tm(*std::localtime(&fs_info.last_written));
					struct std::tm db_tm(*std::localtime(&db_info.last_written));
					std::strftime(fs_buf, sizeof fs_buf, "%F %T %z", &fs_tm);
					std::strftime(db_buf, sizeof db_buf, "%F %T %z", &db_tm);
					msg(prog, "INFO") << target_name << " needs rebuilding because " << prereq_name << " has changed timestamp from " << db_buf << " to " << fs_buf << ".\n";
				}
				satisfaction = false;
				if (!keep_going) break;
			} else
			if (0 != std::memcmp(fs_info.hash, db_info.hash, sizeof db_info.hash)) {
				if (verbose) {
					msg(prog, "INFO") << target_name << " needs rebuilding because " << prereq_name << " has changed hash value from ";
					puthash(std::clog, db_info);
					std::clog << " to ";
					puthash(std::clog, fs_info);
					std::clog << ".\n";
				}
				satisfaction = false;
				if (!keep_going) break;
			}
		}
	}
	return satisfaction;
}

static inline
bool
is_sourcefile(
	const std::string & name
) {
	if (!exists(name)) return false;
	if (exists(".redo/" + name + ".prereqs")) return false;
	if (exists(".redo/" + name + ".prereqsne")) return false;
	if (exists(".redo/" + name + ".prereqs.build")) return false;
	if (exists(".redo/" + name + ".prereqsne.build")) return false;
	return true;
}

static inline
bool
recurse_prerequisites (
	const char * prog,
	unsigned meta_depth,
	const std::string & name
) {
	const std::string database_name(".redo/" + name + ".prereqs");
	std::ifstream file(database_name.c_str());
	if (file.fail()) return false;
	std::list<std::string> files;
	while (EOF != file.peek()) {
		Information info;
		std::string prereq_name;
		read_db_line(file, info, prereq_name);
		if (info.NOTHING != info.type && !is_sourcefile(prereq_name))
			files.push_back(prereq_name);
	}
	return files.empty() || redo(false, prog, meta_depth, convert(files));
}

static
bool
redo (
	bool unconditional,
	const char * prog,
	unsigned meta_depth,
	const std::vector<const char *> & filev
) {
	if (meta_depth >= MAX_META_DEPTH) return true;
	bool status(true);
	if (debug) {
		msg(prog, "INFO") << "REDO" << (unconditional ? "" : "-IFCHANGE-INTERNAL") << ": >";
		for ( std::vector<const char *>::const_iterator i = filev.begin(); i != filev.end(); ++i ) {
			const char * arg(*i);
			std::clog << ' ';
			if (is_sourcefile(arg)) std::clog << "(" << arg << ")"; else std::clog << arg;
		}
		std::clog << '<' << std::endl;
	}

	std::list<Job> jobs;

	for ( std::vector<const char *>::const_iterator i = filev.begin(); i != filev.end(); ++i ) {
		const char * arg(*i);
		if (is_sourcefile(arg)) continue;
		if (!unconditional) {
			if (satisfies_existence(prog, arg)) {
				if (recurse_prerequisites(prog, meta_depth, arg)
				&&  satisfies_existence(prog, arg)
				&&  satisfies_prerequisites(prog, arg)
				)
					continue;
			}
		}

		jobs.push_back(Job());
		Job & job(jobs.back());
		job.arg = arg;
		job.target = arg;
		job.tmp_target = job.target + ".doing";
		job.database_name = ".redo/" + job.target + ".prereqs";
		job.tmp_database_name = job.database_name + ".build";
		job.lock_database_name = job.database_name + ".lock";
	}
	if (!run(prog, meta_depth, jobs))
		status = false;
	if (debug) {
		msg(prog, "INFO") << "Redo status = " << status << ".\n" << std::flush;
	}
	return status;
}

static 
bool
parse_fds(
	const char * prog, 
	const char * str,
	int fds[],
	size_t count
) {
	char * s(const_cast<char *>(str));
	for (size_t j(0); j < count; ++j) {
		if (j > 0) {
			if (!*s) {
				fds[j] = fds[j - 1];
				continue;
			} else
			if (',' != *s) {
				msg(prog, "ERROR") << str << ": " << s << ": Missing comma.\n";
				return false;
			} else
				++s;
		}
		const char * old(s);
		long i(std::strtol(old, &s, 0));
		if (old == s) {
			msg(prog, "ERROR") << str << ": " << s << ": File descriptor number not supplied.\n";
			return false;
		}
		fds[j] = i;
	}
	if (*s) {
		msg(prog, "ERROR") << str << ": " << s << ": Trailing junk after file descriptor(s).\n";
		return false;
	}
	return true;
}

int
main ( int argc, const char * argv[] )
{
	const char * prog(basename_of(argv[0]));

        std::vector<const char *> filev;

	try {
		std::string jobserver_fds_string;
		std::string redoparent_fd_string;
		const char * jobserver_fds_c_str = 0;
		const char * redoparent_fd_c_str = 0;
		const char * directory = 0;
		unsigned long max_jobs = 0;
		popt::bool_definition silent_option('s', "silent", "Operate quietly.", silent);
		popt::bool_definition quiet_option('\0', "quiet", "alias for --silent", silent);
		popt::bool_definition keep_going_option('k', "keep-going", "Continue with the next target if a .do script fails.", keep_going);
		popt::bool_definition debug_option('d', "debug", "Output debugging information.", debug);
		popt::bool_definition verbose_option('\0', "verbose", "Display information about the database.", verbose);
		popt::bool_definition print_option('p', "print", "alias for --verbose", verbose);
		popt::unsigned_number_definition jobs_option('j', "jobs", "number", "Allow multiple jobs to run in parallel.", max_jobs, 0);
		popt::string_definition directory_option('C', "directory", "directory", "Change to directory before doing anything.", directory);
		popt::definition * top_table[] = {
			&silent_option,
			&quiet_option,
			&debug_option,
			&keep_going_option,
			&verbose_option,
			&print_option,
			&jobs_option,
			&directory_option
		};
		popt::top_table_definition main_option(sizeof top_table/sizeof *top_table, top_table, "Main options", "filename(s)");
		catchall_definition ignore;
		special_string_definition jobserver_option('\0', "jobserver-fds", "fd-list", "Provide the file descriptor numbers of the jobserver pipe.", jobserver_fds_c_str);
		special_string_definition redoparent_option('\0', "redoparent-fd", "fd", "Provide the file descriptor number of the redo database current parent file.", redoparent_fd_c_str);
		popt::definition * make_env_top_table[] = {
			&silent_option,
			&quiet_option,
			&debug_option,
			&keep_going_option,
			&verbose_option,
			&print_option,
			&jobs_option,
			&jobserver_option,
			&ignore
		};
		popt::table_definition make_env_main_option(sizeof make_env_top_table/sizeof *make_env_top_table, make_env_top_table, "Main options (environment variable arguments)");
		popt::definition * redo_env_top_table[] = {
			&silent_option,
			&quiet_option,
			&debug_option,
			&keep_going_option,
			&verbose_option,
			&print_option,
			&jobs_option,
			&jobserver_option,
			&redoparent_option,
		};
		popt::table_definition redo_env_main_option(sizeof redo_env_top_table/sizeof *redo_env_top_table, redo_env_top_table, "Main options (environment variable arguments)");

		static const char * vars[] = { "REDOFLAGS", "MAKEFLAGS", "MFLAGS" };
		for ( unsigned i = 0 ; i < sizeof vars/sizeof *vars; ++i ) {
			const char * var(vars[i]);
			if (const char * s = std::getenv(var)) {
				std::list<std::string> args(split(s, 1 == i));	 // Special bodge for MAKEFLAGS, which omits the "-" from the first option.
				std::vector<const char *> argv(convert(args));
				std::vector<const char *> filev;
				popt::arg_processor<std::vector<const char *>::const_iterator> p(argv.begin(), argv.end(), prog, i ? make_env_main_option : redo_env_main_option, filev);
				p.process(false /* allow intermingling of options and arguments */);
				if (p.stopped())
					msg(prog, "WARNING") << var << ": Ignoring halt of option processing.\n";
				if (1 == i) {	// Special bodge for MAKEFLAGS, which BSD make puts macro definitions into.
					for ( std::vector<const char *>::iterator j = filev.begin(); j != filev.end(); ) {
						if (std::strchr(*j, '='))
							j = filev.erase(j);
						else
							++j;
					}
				}
				if (!filev.empty())
					msg(prog, "WARNING") << var << ": Ignoring filenames.\n";
				if (jobserver_fds_c_str) { jobserver_fds_string = jobserver_fds_c_str; jobserver_fds_c_str = 0; }
				if (redoparent_fd_c_str) { redoparent_fd_string = redoparent_fd_c_str; redoparent_fd_c_str = 0; }
				break;
			}
		}

		popt::arg_processor<const char **> p(argv + 1, argv + argc, prog, main_option, filev);
		p.process(false /* allow intermingling of options and arguments */);
		if (p.stopped()) return EXIT_SUCCESS;
		if (directory) { 
			const int r(chdir(directory));
			if (r < 0) {
				const int error(errno);
				msg(prog, "ERROR") << directory << ": " << std::strerror(error) << "\n";
				return EXIT_FAILURE;
			}
		}
		if (jobserver_fds_c_str) { jobserver_fds_string = jobserver_fds_c_str; jobserver_fds_c_str = 0; }
		if (redoparent_fd_c_str) { redoparent_fd_string = redoparent_fd_c_str; redoparent_fd_c_str = 0; }

		if (!jobserver_fds_string.empty()) {
			if (!parse_fds(prog, jobserver_fds_string.c_str(), jobserver_fds, sizeof jobserver_fds/sizeof *jobserver_fds))
				return EXIT_FAILURE;
			if (jobs_option.is_set())
				msg(prog, "WARNING") << "Ignoring jobs option when there's already a job server.\n";
		} else {
			if (jobs_option.is_set()) {
				if (max_jobs < 1U) {
					msg(prog, "ERROR") << "Invalid job limit.\n";
					return EXIT_FAILURE;
				}
				if (0 > pipe(jobserver_fds)) {
					const int error(errno);
					msg(prog, "ERROR") << "pipe: " << std::strerror(error) << "\n";
					return EXIT_FAILURE;
				}
				for (unsigned m(max_jobs); m > 1U; --m) 
					vacate_job_slot(prog);
			}
		}
		if (!redoparent_fd_string.empty()) {
			if (!parse_fds(prog, redoparent_fd_string.c_str(), &redoparent_fd, 1U))
				return EXIT_FAILURE;
		}
	} catch (const popt::error & e) {
		msg(prog, "ERROR") << e.arg << ": " << e.msg << "\n";
		return EXIT_FAILURE;
	}

	if (filev.empty()) {
		msg(prog, "ERROR") << "No filenames supplied.\n";
		return EXIT_FAILURE;
	}

	const unsigned meta_depth(0U);

	// Increment MAKELEVEL
	char levelbuf[sizeof "MAKELEVEL=" + 64] = "MAKELEVEL=";
	if (char * level = std::getenv("MAKELEVEL")) {
		makelevel = level;
		unsigned long ul(std::strtoul(level, &level, 0));
		snprintf(levelbuf + sizeof "MAKELEVEL=" - 1, 64, "%lu", ul + 1);
	} else
		snprintf(levelbuf + sizeof "MAKELEVEL=" - 1, 64, "%lu", 1UL);
	putenv(levelbuf);

	if (0 == std::strcmp(prog, "redo-ifcreate")
#if defined(__OS2__) || defined(__WIN32__) || defined(__NT__)
	||  0 == stricmp(prog, "redo-ifcreate.exe")
#endif
	)
		return redo_ifcreate(prog, filev) ? EXIT_SUCCESS : EXIT_FAILURE;
	else
	if (0 == std::strcmp(prog, "redo-ifchange")
#if defined(__OS2__) || defined(__WIN32__) || defined(__NT__)
	||  0 == stricmp(prog, "redo-ifchange.exe")
#endif
	) {
		const bool r(redo_ifchange(prog, meta_depth, filev));
		procure_job_slot(prog);
		return r ? EXIT_SUCCESS : EXIT_FAILURE;
	}
	else
	if (0 == std::strcmp(prog, "redo")
#if defined(__OS2__) || defined(__WIN32__) || defined(__NT__)
	||  0 == stricmp(prog, "redo.exe")
#endif
	) {
		posix_mkdir(".redo", 0777);
		const bool r(redo(true, prog, meta_depth, filev));
		procure_job_slot(prog);
		return r ? EXIT_SUCCESS : EXIT_FAILURE;
	}
	if (0 == std::strcmp(prog, "cubehash")
#if defined(__OS2__) || defined(__WIN32__) || defined(__NT__)
	||  0 == stricmp(prog, "cubehash.exe")
#endif
	)
	{
		for ( std::vector<const char *>::const_iterator i = filev.begin(); i != filev.end(); ++i ) {
			const char * arg(*i);
			const Information & info(get_file_info(arg, 0));
			write_db_line(std::cout, info, arg);
		}
		return EXIT_SUCCESS;
	}
	else
	{
		msg(prog, "ERROR") << "Unknown function.\n";
		return EXIT_FAILURE;
	}
}
