// dt_syswrap.c
#include "pub_tool_basics.h"
#include "pub_tool_vki.h"
#include "pub_tool_vkiscnums.h"
#include "pub_tool_hashtable.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_libcproc.h"
#include "pub_tool_libcfile.h"
#include "pub_tool_machine.h"
#include "pub_tool_aspacemgr.h"
#include "pub_tool_threadstate.h"
#include "pub_tool_stacktrace.h"   // for VG_(get_and_pp_StackTrace)
#include "pub_tool_debuginfo.h"	   // VG_(describe_IP), VG_(get_fnname)

#include "valgrind.h"

#include "dt_main.h"
#include "dt_debug.h"
#include "dt_taint.h"
#include "dt_wrap.h"

#include "untitled.h"


static Bool identifyFdType(ThreadId tid, Int fd, HChar *path) 
{
	Int len = VG_(strlen)(path);

	fds[tid][fd].type = FdUnknown;
	// Some special cases
	if( (len > 8) && (VG_(memcmp)(path, "/system/", 8) == 0) ) {
		fds[tid][fd].type = FdSystemLib;  // What if it's under /system/bin/? (why?)
	} else if(VG_(memcmp)(path, "/proc/", 6) == 0) {
		fds[tid][fd].type = FdProcMap;
	} else if( (VG_(memcmp)(path, "/dev/", 5) == 0)
			|| (VG_(memcmp)(path, "/sys/devices/", 13) == 0)) {
		fds[tid][fd].type = FdDevice;
	}	else {
	// Some general cases
		if( VG_(memcmp)((HChar*)&path[len-3], ".so", 3) == 0) {
			// Dynamic linked library (it is not under /system/, so it
			// probably contains an application's native codes)
			fds[tid][fd].type = FdAppLib;
		} else if( VG_(memcmp)((HChar*)&path[len-4], ".apk", 4) == 0) {
			// Apparently it is an apk file
			fds[tid][fd].type = FdAppApk;
		} else if( VG_(memcmp)((HChar*)&path[len-4], ".jar", 4) == 0) {
			// Apparently it is a jar file
			fds[tid][fd].type = FdAppJar;
		} else if( VG_(memcmp)((HChar*)&path[len-3], "dex", 3) == 0) {
			// It is an odex file, or a dex file
			if( len > 40 && VG_(memcmp)(path, "/data/dalvik-cache/system@framework@", 36) == 0) {
				// This dex/odex file does not belong to the application
				fds[tid][fd].type = FdFrameworkDex;
			} else {
				// This dex/odex file belongs to the application
				fds[tid][fd].type = FdAppDex;
			}
		}
	}
	// Other types are marked unknown (FdUnknown)

	// Copy the file path into the name field
	VG_(strcpy)(fds[tid][fd].name, path);
	// Some logging stuff
#if DBG_SYSCALL
	DT_LOGI("IDENTIFY: %d %d %s\n",
			fd, fds[tid][fd].type, path);
#endif
	if(fds[tid][fd].type > 0) {
		// Highly suspected to be forever true since it looks like
		// no one would set the type to a negative value
		// Moreover, `fds[tid][fd].type` is of an enum type, the
		// value of which type is considered unsigned (?)
		return True;
	} else {
		DT_LOGI("[ UNTITLED ] Really? This is impossible\n");
		fds[tid][fd].type = FdUnknown;  // Is this really necessary?
		return False;
	}
}


static INLINE Bool isThirdFd( Int tid, Int fd) {
	if (fd <= 0)
		return False;
	if ( (fds[tid][fd].type == FdAppDex)
			/*|| (fds[tid][fd].type == FdAppLib)*/
			|| (fds[tid][fd].type == FdAppJar)
			|| (fds[tid][fd].type == FdProcMap)
			|| (fds[tid][fd].type == FdUnknown) ) {
		return True;
	}
	return False;
}

static void resolve_filename(UWord fd, HChar *path, Int max)
{
	HChar src[FD_MAX_PATH];
	Int len = 0;

	// TODO: Cache resolved fds by also catching open()s and close()s
	VG_(sprintf)(src, "/proc/%d/fd/%d", VG_(getpid)(), (int)fd);
	len = VG_(readlink)(src, path, max);  // The path to the opend file (absolute path?)

	// Just give emptiness on error.
	if (len == -1) len = 0;
	path[len] = '\0';  // Warning: the buffer size must be at least (`max` + 1) bytes
}

void dt_syscall_lseek(ThreadId tid, UWord* args, UInt nArgs,
		SysRes res) {
	// off_t lseek(int fd, off_t offset, int whence);
	Int   fd      = args[0];
	ULong offset  = args[1];
	UInt  whence  = args[2];

	Int   retval       = sr_Res(res);
#ifdef DBG_SYSCALL
	DBG_SYSCALL_INFO("_lseek() tid=%d fd=%d ", tid, fd);
	DT_LOGI("offset: 0x%x whence: 0x%x ", (UInt)offset, whence);
	DT_LOGI("retval: 0x%x read_offset: 0x%x\n", retval, fds[tid][fd].offset);
#endif
	if( whence == 0/*SEEK_SET*/ )
		fds[tid][fd].offset = (UInt)offset;
	else if( whence == 1/*SEEK_CUR*/ )
		fds[tid][fd].offset += (UInt)offset;
	else if( whence == 2/*SEEK_END*/ )
		fds[tid][fd].offset = retval;
	else {
		DT_LOGI("whence %x\n", whence);
		tl_assert(0);
	}
}

void dt_syscall_llseek(ThreadId tid, UWord* args, UInt nArgs,
		SysRes res) {
	// int  _llseek(int fildes, ulong offset_high, ulong offset_low, loff_t *result,, uint whence);
	Int   fd           = args[0];
	ULong offset_high  = args[1];
	ULong offset_low   = args[2];
	UInt  result       = args[3];
	UInt  whence       = args[4];
	ULong offset;

	Int   retval       = sr_Res(res);

#ifdef DBG_SYSCALL
	DBG_SYSCALL_INFO("_llseek() tid=%d fd=%d ", tid, fd);
	DT_LOGI("0x%x 0x%x 0x%x 0x%x\n", (UInt)offset_high, (UInt)offset_low, result, whence);
	DT_LOGI("0x%x\n", retval);
#endif

	offset = (offset_high<<32) | offset_low;

	if( whence == 0/*SEEK_SET*/ )
		fds[tid][fd].offset = 0 + (UInt)offset;
	else if( whence == 1/*SEEK_CUR*/ )
		fds[tid][fd].offset += (UInt)offset;
	else {//if( whence == 2/*SEEK_END*/ )
		DT_LOGI("whence %x\n", whence);
		tl_assert(0);
	}
}

void dt_syscall_read(ThreadId tid, UWord* args, UInt nArgs,
		SysRes res) {
	// ssize_t  read(int fildes, void *buf, size_t nbyte);
	Int   fd           = args[0];  // file descriptor
	HChar *data        = (HChar *)args[1];  // User buffer
	// The third argument is the maximum number of bytes that should be read, however, is not used here
	UInt  curr_offset  = fds[tid][fd].offset;  // Current offset of the cursor (after read?)
	Int   curr_len     = sr_Res(res);  // The number of bytes that has just been read

	dt_check_fd_access(tid, fd, FD_READ);  // The implementation of this function is commented out, so actually do nothing here

	// Some logging stuff
#ifdef DBG_SYSCALL
	DBG_SYSCALL_INFO("read() tid=%d, fd=%d offset=0x%08x len=%d data(0x%8x)=%s\n", tid, fd, curr_offset, curr_len, (Int)data, data);
#endif

	if (curr_len == 0) return;  // If nothing has been read, then just return

	dt_make_mem_untainted( (UWord)data, curr_len );  // Mark the newly written area of buffer (written by the `read` operation) untainted (why?)

	// Update file position
	fds[tid][fd].offset += curr_len;  // Keep the offset up to date
}

void dt_syscall_pread(ThreadId tid, UWord* args, UInt nArgs,
		SysRes res) {
	// ssize_t pread(int fildes, void *buf, size_t nbyte, size_t offset);
	// Reads up to `nbyte` bytes from file descriptor `fildes` at
	// offset `offset` (from the start of the file) into the buffer
	// starting at `buf`. The file offset is NOT changed
	Int   fd           = args[0];  // File descriptor
	HChar *data        = (HChar *)args[1];  // User buffer
	UInt  curr_offset  = (Int)args[3];  // Cursor offset
	Int   curr_len     = sr_Res(res);  // The number of bytes that has just been read

	if (curr_len == 0) return;  // If nothing has been read, then just return

	dt_make_mem_untainted( (UWord)data, curr_len );  // Mark the newly written area of buffer (written by the `read` operation) untainted (why?)

	// Some logging stuff
#ifdef DBG_SYSCALL
	DBG_SYSCALL_INFO("pread() tid=%d fd=%d offset=0x%8x len=0x%x data(0x%8x)=%s\n", tid, fd, curr_offset, curr_len, (UInt)data, data);
#endif

	// According to the Linux manual, the file offset remains
	// unchanged, so do not change the offset in `fds`
}

// ssize_t readv(int fd, const struct iovec *iov, int iovcnt);
// Reads `iovcnt` buffers from the file associated with the file
// descriptor `fd` into the buffers described by `iov` ("scatter
// input")
void dt_syscall_readv(ThreadId tid, UWord* args, UInt nArgs, SysRes res)
{
	Int fd					= args[0];  // File descriptor
	struct iovec *iov = (struct iovec*)args[1];  // Array of I/O vectors (descriptors of pieces of user buffers)
	Int iovcnt			= args[2];  // Length of the I/O vector array
	int	re			= sr_Res(res);  // The number of bytes that has just been read
	
	// So here comes the question: why not mark the user buffer as
	// "untainted" here?

	// If the tainting has not yet started, do not log the invocation
	// (sounds like some logging reduction strategy)
	if ( dt_clo_taint_begin == False)
		return;
#ifdef DBG_SYSCALL
	DBG_SYSCALL_INFO("readv() tid=%d fd=%d base=0x%08x len=%d\n", 
			tid, fd, (Int)iov->iov_base, iov->iov_len);
#endif

	// Warning: file offset not updated (why?)
}

// ssize_t preadv(int fd, const struct iovec *iov, int iovcnt, off_t offset);
// Combines the functionality of readv() and pread(2). It performs the
// same task as readv(), but adds a fourth argument, offset, which
// specifies the file offset at which the input operation is to be
// performed. The file offset is NOT changed.
void dt_syscall_preadv(ThreadId tid, UWord* args, UInt nArgs, SysRes res)
{
	Int fd					= args[0];  // File descriptor
	struct iovec *iov = (struct iovec*)args[1];  // Pointers and lengths of user buffers
	Int iovcnt			= args[2];  // The number of user buffers specified in `iov`
	int   offset  = args[3];  // Cursor offset
	int		re			= sr_Res(res);  // The number of bytes that has just been read

	// Why not mark untainted?

	// Againt, some logging reduction strategy
	if ( dt_clo_taint_begin == False )
		return;
#ifdef DBG_SYSCALL
	DBG_SYSCALL_INFO("preadv %d fd=%d offset=0x%x 0x%x %d\n", 
			tid, fd, offset, (Int)iov->iov_base, iov->iov_len);
#endif

	// Since the file offset is not changed, no need to update `fds`
}

void dt_syscall_open(ThreadId tid, UWord* args, UInt nArgs, SysRes res) {
	//  int open (const char *filename, int flags[, mode_t mode])
	HChar fdpath[FD_MAX_PATH];
	Int fd = sr_Res(res);  // File descriptor
	if (fd > -1 && fd < FD_MAX) {  // If the `fd` is within a valid range
		// Get opened file path ("-1" for a reserved position for '\0')
		resolve_filename(fd, fdpath, FD_MAX_PATH-1);
		// Identify file type and store it in `fds[tid][fd].type`
		// fds[tid][fd].name is set by this function at the same
		// time
		identifyFdType(tid, fd, fdpath);  // The returned value is dicarded
		// Initialize the cursor offset to 0 since it is newly opened
		fds[tid][fd].offset = 0;

		// Some logging stuff
#ifdef DBG_SYSCALL
		DBG_SYSCALL_INFO("open() tid=%d path=%s flogs=%lx fd=%d\n", tid, fdpath, args[1], fd);
#endif
		// Mark "dex file is opened" if the application has just
		// opened an "application dex file"
		if(fds[tid][fd].type == FdAppDex) {
			dt_dex_is_open = True;
			UN_PRINT_DEBUG("[ UNTITLED ] [ DEBUG ] `dt_dex_is_open` is set to `True` due to the opened file: %s\n", fdpath);
		}
	} 
}

void dt_syscall_close(ThreadId tid, UWord* args, UInt nArgs, SysRes res) {
	//   int close (int filedes)
	Int fd = args[0];  // File descriptor

	// If the `fd` is within a valid range, keep the `fds` up to date
	if (fd > -1 && fd < FD_MAX){
		//shared_fds[fd] = 0;
		if( fds[tid][fd].type > 0) {
			// Simply reset the offset and type
			fds[tid][fd].type = 0;
			fds[tid][fd].offset = 0;
		}
		// Some logging stuff
#ifdef DBG_SYSCALL
		DBG_SYSCALL_INFO("close() tid=%d path=%s fd=%d\n", tid, fds[tid][fd].name, fd);
#endif
	}
}

void dt_syscall_write(ThreadId tid, UWord* args, UInt nArgs, SysRes res) {
	// ssize_t write(int fd, const void *buf, size_t nbytes);
	Int fd = args[0];  // File descriptor
	HChar *data        = (HChar *)args[1];  // User buffer
	Int   curr_len     = sr_Res(res);  // The number of bytes written to the file associated with the file descriptor `fd`

	dt_check_fd_access(tid, fd, FD_WRITE);  // The body of this function is empty

	// Some logging stuff
#ifdef DBG_SYSCALL
	DBG_SYSCALL_INFO("write() tid=%d, fd=%d, len=%d data(0x%08x)=%s\n", 
			tid, fd, curr_len, (Int)data , data);
#endif
	if(trace_ins_taint) {
		Bool isT = dt_check_mem_tainted( data, curr_len);  // Check if this area of memory is tainted
		if(isT) {
			// Some logging stuff
			TNT_LOGI("[T] %d sys_write(fd=%d) curr_len=%d data(0x%x)=%s\n", 
					tid, fd, curr_len, (Int)data , data);
			// Warning: `data` is not guaranteed to end with '\0'
		}
	}
}

// ssize_t writev(int fd, const struct iovec *iov, int iovcnt);
void dt_syscall_writev(ThreadId tid, UWord* args, UInt nArgs, SysRes res)
{
	Int fd					= args[0];  // File descriptor
	struct iovec *iov = (struct iovec*)args[1];  // Pointers and lengths of user buffers
	Int iovcnt			= args[2];  // The number of user buffers
	Int	re			= sr_Res(res);  // The number of bytes written to the file associated with the file descriptor `fd`

	// If the tainting is not started or the syscall failed, just return
	// This condition is weird
	if ( dt_clo_taint_begin == False || re < 0)
		return;
#ifdef DBG_SYSCALL
	DBG_SYSCALL_INFO("writev() tid=%d fd=%d base=0x%x len=%d\n", 
			tid, fd, (Int)iov->iov_base, iov->iov_len);
#endif
	// Why not check if the memory areas are tainted?
	// Warning: file offset not updated (why?)
}
// ssize_t pwritev(int fd, const struct iovec *iov, int iovcnt, off_t offset);
void dt_syscall_pwritev(ThreadId tid, UWord* args, UInt nArgs, SysRes res)
{
	Int fd					= args[0];  // File descriptor
	struct iovec *iov = (struct iovec*)args[1];  // Pointers and lengths of user buffers
	Int iovcnt			= args[2];  // The number of user buffers
	int		  offset  = args[3];  // Cursor offset
	int			re			= sr_Res(res);  // The number of written bytes

	// If the tainting is not started or the syscall failed, just return
	// This condition is weird
	if ( dt_clo_taint_begin == False || re < 0)
		return;
#ifdef DBG_SYSCALL
	DBG_SYSCALL_INFO("pwritev() tid=%d fd=%d offset=0x%08x base=0x%08x len=%d\n", 
			tid, fd, offset, (Int)iov->iov_base, iov->iov_len);
#endif
	// Why not check if the memory areas are tainted?
	// Warning: file offset not updated (why?)
}

void dt_get_fnname(ThreadId tid, const HChar** buf) {
	UInt pc = VG_(get_IP)(tid);
	VG_(get_fnname)(pc, buf);
}

void dt_check_fd_access(ThreadId tid, UInt fd, Int fd_request) {
#if 0
	if (IN_SANDBOX) {
		Bool allowed = shared_fds[fd] & fd_request;
		//		VG_(printf)("checking if allowed to %s from fd %d ... %d\n", (fd_request == FD_READ ? "read" : "write"), fd, allowed);
		if (!allowed) {
			const HChar* access_str;
			switch (fd_request) {
				case FD_READ: {
												access_str = "read from";
												break;
											}
				case FD_WRITE: {
												 access_str = "wrote to";
												 break;
											 }
				default: {
									 tl_assert(0);
									 break;
								 }
			}
			HChar fdpath[FD_MAX_PATH];
#ifdef VGO_freebsd
			VG_(resolve_filename)(fd, fdpath, FD_MAX_PATH-1);
#elif defined VGO_linux
			resolve_filename(fd, fdpath, FD_MAX_PATH-1);
#else
#error OS unknown
#endif
			const HChar *fnname;
			dt_get_fnname(tid, &fnname);
			VG_(printf)("*** Sandbox %s %s (fd: %d) in method %s, but it is not allowed to. ***\n", access_str, fdpath, fd, fnname);
			VG_(get_and_pp_StackTrace)(tid, STACK_TRACE_SIZE);
			VG_(printf)("\n");
		}
	}
#endif
}
// ssize_t send(int socket, const void *buffer, size_t length, int flags);
void dt_syscall_send(ThreadId tid, UWord* args, UInt nArgs, SysRes res) {
	Int len     = sr_Res(res);  // The number of bytes sent, or -1 on error
	Int sd      = (Int)args[0];  // Socket file descriptor
	HChar *data = (HChar *)args[1];  // User buffer

	// Some logging stuff
#ifdef DBG_SYSCALL
	// DBG_SYSCALL_INFO("send() tid=%d sd=%d len=%d data(%08x)=%s\n", tid, sd, len, data, data);
	DBG_SYSCALL_INFO("send() tid=%d sd=%d len=%d data(%08x)=", tid, sd, len, data);
	Int i;
	for(i = 0; i < len; i++) VG_(printf)("%c", data[i]);
	VG_(printf)("\n");
#endif

	// Why no tainting? (handled in client request handler?)
}

// ssize_t sendto(int socket, const void *message, size_t length,
//		       int flags, const struct sockaddr *dest_addr,
//					        socklen_t dest_len);
void dt_syscall_sendto(ThreadId tid, UWord* args, UInt nArgs, SysRes res) {
	Int msglen	= sr_Res(res);  // The number of bytes sent, or -1 on error
	Int sd			= (Int)args[0];  // Socket file descriptor
	HChar *data	= (HChar *)args[1];  // User buffer

	// Some logging stuff
#ifdef DBG_SYSCALL
	//DBG_SYSCALL_INFO("recvfrom %d 0x%x %d %s\n", tid, data, msglen, data);
	// DBG_SYSCALL_INFO("sendto() tid=%d sd=%d len=%d data(0x%08x)=%s\n", tid, sd, msglen, data, data);
	DBG_SYSCALL_INFO("sendto() tid=%d sd=%d len=%d data(0x%08x)=", tid, sd, msglen, data);
	Int i;
	for(i = 0; i < msglen; i++) VG_(printf)("%c", data[i]);
	VG_(printf)("\n");
#endif
}

void dt_syscall_recv(ThreadId tid, UWord* args, UInt nArgs, SysRes res) {
	// ssize_t recv(int sockfd, void *buf, size_t len, int flags)
	Int msglen  = sr_Res(res);  // The number of byte received, or -1 on error
	Int sd			= (Int)args[0];  // Socket file desceriptor
	HChar *data = (HChar *)args[1];
#ifdef DBG_SYSCALL
	DBG_SYSCALL_INFO("recv() tid=%d sd=%d len=%d data(%08x)=", tid, sd, msglen, data);
	Int i;
	for(i = 0; i < msglen; i++) VG_(printf)("%c", data[i]);
	VG_(printf)("\n");
#endif
}

void dt_syscall_recvfrom(ThreadId tid, UWord* args, UInt nArgs, SysRes res) {
	// ssize_t recvfrom(int sockfd, void *buf, size_t len, int flags,
	//                 struct sockaddr *src_addr, socklen_t *addrlen)
	// TODO: #include <arpa/inet.h> inet_ntop to pretty print IP address
	Int msglen  = sr_Res(res);  // The number of bytes received, or -1 on error
	Int sd			= (Int)args[0];  // Socket file descriptor
	HChar *data = (HChar *)args[1];  // User buffer

	// Some logging stuff
#ifdef DBG_SYSCALL
	//DBG_SYSCALL_INFO("recvfrom %d 0x%x %d %s\n", tid, data, msglen, data);
	DBG_SYSCALL_INFO("recvfrom() tid=%d sd=%d len=%d data(0x%08x)=", tid, sd, msglen, data);
	Int i;
	for(i = 0; i < msglen; i++) VG_(printf)("%c", data[i]);
	VG_(printf)("\n");
#endif
}

// void *mmap(void *addr, size_t length, int prot, int flags, int fd, off_t offset);
// Creates a new mapping in the virtual address space of the calling process.
// The starting address for the new mapping is specified in addr. The length
// argument specifies the length of the mapping.
// If addr is NULL, then the kernel chooses the address at which to create
// the mapping; this is the most portable method of creating a new mapping.
// If addr is not NULL, then the kernel takes it as a hint about where to
// place the mapping; on Linux, the mapping will be created at a nearby page
// boundary. The address of the new mapping is returned as the result of the
// call.
void dt_syscall_mmap( ThreadId tid, UWord* args, UInt nArgs, SysRes res) {
	// Warning: convert unsigned value into signed value (void * => signed int)
	Int begin_addr = sr_Res(res);  // The starting address of the map
	Int size  = (Int)args[1];  // Size of the map
	Int prot = (Int)args[2];  // Protection flags ("rwx" permissions of the map)
	Int flags = (Int)args[3];  // Map flag (see https://linux.die.net/man/2/mmap)
	Int  fd = (Int)args[4];  // File descriptor
	UInt offset = (Int)args[5];  // File offset
	if( begin_addr <= 0 || prot == PROT_NONE )  // If the protection mode is "cannot be accessed at all", just return
		return;

	// Some logging stuff
#ifdef DBG_SYSCALL
	DBG_SYSCALL_INFO("mmap() tid=%d fd=%d off=0x%08x -> mem=0x%08x-0x%08x size=%d prot=%c%c%c flags=0x%x\n", 
			tid, fd, offset, begin_addr, begin_addr+size, size, 
			(prot & PROT_READ) ? 'r' : '-',
			(prot & PROT_WRITE) ? 'w' : '-',
			(prot & PROT_EXEC) ? 'x' : '-',
			flags);
#endif
}

// int mprotect(void *addr, size_t len, int prot);
// Changes protection for the calling process's memory page(s)
// containing any part of the address range in the interval
// [addr, addr+len-1]. addr must be aligned to a page boundary.
// [ UNTITLED ] Set memory page(s) "rwx" permissions
void dt_syscall_mprotect( ThreadId tid, UWord* args, UInt nArgs, SysRes res) {
	Addr begin_addr = (Addr)args[0];  // Starting address of the page(s)
	Int  size = (Int)args[1];  // Size of the page(s)
	Int  prot = (Int)args[2];  // Protection flag (rwx)
	Int  re  = sr_Res(res);  // 0 on success, -1 on error

	// If the page(s) is set to "cannot be accessed at all", just return
	if( prot == PROT_NONE )
		return;

	// Some logging stuff
#ifdef DBG_SYSCALL
	if( re >= 0)  // If the operation successed
		DBG_SYSCALL_INFO("mprotect() tid=%d mem=0x%08x-0x%08x prot=%c%c%c\n",
				tid, begin_addr, begin_addr+size,
				(prot & PROT_READ) ? 'r' : '-',
				(prot & PROT_WRITE) ? 'w' : '-',
				(prot & PROT_EXEC) ? 'x' : '-');
#endif
}

// int msync(void *addr, size_t length, int flags);
// Flushes changes made to the in-core copy of a file that was mapped
// into memory using mmap(2) back to disk. Without use of this call
// there is no guarantee that changes are written back before munmap(2)
// is called. To be more precise, the part of the file that corresponds
// to the memory area starting at `addr` and having length `length` is
// updated.
void dt_syscall_msync( ThreadId tid, UWord* args, UInt nArgs, SysRes res) {
	Addr begin_addr = (Addr)args[0];  // Starting address of the memory map (corresponds to a file)
	Int  length		  = (Int)args[1];  // Length of the map
	Int	 flags			= (Int)args[2];  // Synchronization flag (the operation is async or sync, whether to invalidate other maps)
	Int  re				= sr_Res(res);  // 0 on success, -1 on error

	// Some logging stuff
#ifdef DBG_SYSCALL
	if(re == 0) {  // If successed
		DBG_SYSCALL_INFO("msync() tid=%d mem=0x%08x-0x%08x flags=0x%x\n",
				tid, begin_addr, begin_addr+length, flags);
	}
#endif
}

// int munmap(void *addr, size_t len); 
void dt_syscall_munmap( ThreadId tid, UWord* args, UInt nArgs, SysRes res) {
	Addr begin_addr = (Addr)args[0];  // Starting address of a memory map
	Int  size = (Int)args[1];  // Size of the map

	// If the tainting is not started, just return
	if ( dt_clo_taint_begin == False )
		return;
	if( begin_addr > 0) {  // This condition is highly suspected to be forever true,
		// since `begin_addr` is of type `Addr`, which is an alias of `unsigned long`,
		// so the only case that this expression yields `false` is when `begin_addr`
		// equals to 0, which is seemingly an invalid pointer for this syscall
		// (why?)
#ifdef DBG_SYSCALL
		// Some logging stuff
		DBG_SYSCALL_INFO("munmap() tid=%d mem=0x%08x-0x%08x\n", 
				tid, begin_addr, begin_addr+size);
#endif
	}
}

// int ptrace(int request, pid_t pid, caddr_t addr, int data);
// long ptrace(enum __ptrace_request request, pid_t pid, void *addr, void *data);
// Provides a means by which one process (the "tracer") may observe and
// control the execution of another process (the "tracee"), and examine and
// change the tracee's memory and registers. It is primarily used to implement
// breakpoint debugging and system call tracing
void dt_syscall_ptrace( ThreadId tid, UWord* args, UInt nArgs, SysRes res) {
	Int request = (Int)args[0];  // ptrace request ("trace me", "attach", etc.)
	Int pid = (Int)args[1];  // Target process ID
	Int data = (Int)args[3];  // Some kind of data (or some pointer?)

	// Some logging stuff
#ifdef DBG_SYSCALL
	DBG_SYSCALL_INFO("ptrace() tid=%d req=0x%x pid=%d data=%d\n", 
			tid, request, pid, data);
#endif
}

// int execve(const char *filename, char *const argv[], char *const envp[])
void dt_syscall_execve(ThreadId tid, UWord* args, UInt nArgs, SysRes res) {
	UChar *cmd = (HChar *)args[0];
#ifdef DBG_SYSCALL
	DBG_SYSCALL_INFO("execv() tid=%d cmd(0x%08x)=%s\n", 
			tid, (Int)cmd, (HChar*)cmd);
#endif
}

// int unlink(const char *path)
void dt_syscall_unlink(ThreadId tid, UWord* args, UInt nArgs, SysRes res) {
	UChar *path = (HChar *)args[0];
	Int r = sr_Res(res);
#ifdef DBG_SYSCALL
	DBG_SYSCALL_INFO("unlink() tid=%d path=%s res=%d\n", tid, (HChar*)path, r);
#endif
}

// int setuid(uid_t uid)
// Sets the effective user ID of the calling process. If the effective UID of
// the caller is root, the real UID and saved set-user-ID are also set
void dt_syscall_setuid(ThreadId tid, UWord* args, UInt nArgs, SysRes res) {
	Int uid = (Int)args[0];  // User ID
	Int re = sr_Res(res);  // 1 on success, -1 on error

	// Some logging stuff
#ifdef DBG_SYSCALL
	DBG_SYSCALL_INFO("setuid() tid=%d uid=%d res=%d\n", 
			tid, uid, re);
#endif
}
// int setreuid(uid_t ruid, uid_t euid)
// Sets real and effective user IDs of the calling process. Supplying a value
// of -1 for either the real or effective user ID forces the system to leave
// that ID unchanged.
void dt_syscall_setreuid(ThreadId tid, UWord* args, UInt nArgs, SysRes res) {
	Int ruid = (Int)args[0];  // Real user ID
	Int euid = (Int)args[1];  // Effective user ID
	Int re = sr_Res(res);  // 1 on success, -1 on error

	// Some logging stuff
#ifdef DBG_SYSCALL
	DBG_SYSCALL_INFO("setreuid() tid=%d ruid=%d euid=%d res=%d\n", 
			tid, ruid, euid, re);
#endif
}
// int setgid(uid_t uid)
// Sets the effective group ID of the calling process. If the caller is the
// superuser, the real GID and saved set-group-ID are also set.
void dt_syscall_setgid(ThreadId tid, UWord* args, UInt nArgs, SysRes res) {
	Int gid = (Int)args[0];  // Group ID
	Int re = sr_Res(res);  // 1 on success, -1 on error

	// Some logging stuff
#ifdef DBG_SYSCALL
	DBG_SYSCALL_INFO("setgid() tid=%d gid=%d res=%d\n", tid, gid, re);
#endif
}

// int setreuid(uid_t ruid, uid_t euid)
// Sets real and effective group IDs of the calling process
void dt_syscall_setregid(ThreadId tid, UWord* args, UInt nArgs, SysRes res) {
	Int rgid = (Int)args[0];  // Real group ID
	Int egid = (Int)args[1];  // Effective group ID
	Int re = sr_Res(res);  // 1 on success, -1 on error

	// Some logging stuff
#ifdef DBG_SYSCALL
	DBG_SYSCALL_INFO("setregid() tid=%d rgid=%d egid=%d res=%d\n", 
			tid, rgid, egid, re);
#endif
}
void dt_syscall_action(ThreadId tid, UWord* args, UInt nArgs, SysRes res) {
	Int sigNum = (Int)args[0];
#ifdef DBG_SYSCALL
	DBG_SYSCALL_INFO("sigaction() tid=%d for sigNo=%d\n", 
			tid, sigNum);
#endif
}
// long clone(unsigned long flags, void *child_stack,
//                  void *ptid, void *ctid,
//                                   struct pt_regs *regs);
void dt_syscall_clone(ThreadId tid, UWord* args, UInt nArgs, SysRes res) {
	ULong flag	= (ULong)args[0];
	Addr ptid		= (Int)args[2];
	Addr ctid		= (Int)args[3];
	ULong r   = sr_Res(res);
#ifdef DBG_SYSCALL
	DBG_SYSCALL_INFO("clone() tid=%d flag=0x%lx ptid=0x%08x, ctid=0x%08x, res=0x%lx\n", 
			tid, flag, ptid, ctid, r);
#endif
}
/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
