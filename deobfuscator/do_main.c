#include "pub_tool_basics.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_libcassert.h"    // tl_assert()
#include "pub_tool_libcprint.h"     // VG_(printf)
#include "pub_tool_machine.h"       // VG_(fnptr_to_fnentry)
#include "pub_tool_libcbase.h"      // VG_(strcmp)
#include "pub_tool_options.h"
#include "pub_tool_libcfile.h"      // VG_(readlink)
#include "pub_tool_vki.h"           // keeps libcproc.h happy, syscall nums

#include "pub_tool_guest.h"
#include "pub_tool_debuginfo.h"

#include "pub_core_threadstate.h"

#include "unistd-asm-arm.h"

#include "util.h"
#include "copy.h"
#include "do_dexparse.h"
#include "do_oatparse.h"
#include "do_wrappers.h"
#include "do_framework.h"
#include "do_instrument.h"

#include "shadow_memory.h"
#include "taint_analysis.h"
#include "symbolic_execution.h"

#include "do_string.h"


#if DBG_OAT_PARSE
Bool is_parse_oat = False;
#endif 


HChar *mth_index_name[MAX_MTH_NUM] = {'\0'};

static Bool mytest = False;

static HChar* unknown_str = "????";
// export VALGRIND_LIB=/home/fanatic/valgrind-3.8.1/inst/lib/valgrind/

UChar codeLayer[TG_N_THREADS] = {0};

static Char* clo_fnname = NULL;
int fd_to_taint = 0;

static HChar *libartFunc = NULL;
static Addr libartFuncReturnAddr = 0;

DebugInfo *di_libart = NULL;
Addr libart_text_addr = 0;
UInt libart_text_size = 0;

Addr base_oatdata_addr = 0;
UInt base_oatdata_size = 0;
Addr base_oatexec_addr = 0;
UInt base_oatexec_size = 0;
Addr boot_oatdata_addr = 0;
UInt boot_oatdata_size = 0;
Addr boot_oatexec_addr = 0;
UInt boot_oatexec_size = 0;

Int			do_start_method_index = -1;
HChar*	do_start_method_name = NULL;
HChar*	do_start_method_shorty = NULL;
Int			do_stop_method_index = -1;
HChar*	do_stop_method_name = NULL;
Addr		do_exit_addr = 0;
HChar*	do_start_clazz = NULL;
HChar*	do_main_activity = NULL;
HChar*	do_stop_clazz = NULL;


UInt		do_time_slower = 1;
Int			do_main_oncreate_index = -1;

Bool do_is_start = True;
UInt is_trace_irst = 0;
UInt start_trace_irst = 0;
UInt is_in_vm = 0;

UInt is_monitor_memory_alloc = 0;

struct DexFilePlus *pMDexFileObj  = NULL;
struct DexClassDef *pMClassDefObj = NULL;

Bool do_method_trace = False;

Bool is_in_openmemory = False;

Bool is_dump_raw = False;
#ifdef BAIDU_VMP
Addr last_new_mem_addr1 = 0;
Addr last_new_mem_addr2 = 0;
UInt last_new_mem_size1 = 0;
UInt last_new_mem_size2 = 0;
Addr pcode_items_addr = 0;
UInt pcode_items_size = 0;
UInt baidu_vmp_version = 0;
Addr baidu_vmp_table_addr = 0;
UInt baidu_vmp_table_size = 0;
//UInt last_code_header_addr = 0;
#endif

const HChar* SHUTDOWN_HOW[3] = {
	"SHUT_RD",
	"SHUT_WR",
	"SHUT_RDWR"
};
/* Address family has 42 types in total, now we only suports the 11 most popular types */
const HChar* ADDRESS_FAMILY[11] = {
	/* 0*/"AF_UNSPEC",
	/* 1*/"AF_UNIX/LOCAL",
	/* 2*/"AF_INET",
	/* 3*/"AF_AX25",
	/* 4*/"AF_IPX",
	/* 5*/"AF_APPLETALK",
	/* 6*/"AF_NETROM",
	/* 7*/"AF_BRIDGE",
	/* 8*/"AF_ATMPVC",
	/* 9*/"AF_X25",
	/*10*/"AF_INET6",
	/*11*/"AF_ROSE",     /* Amateur Radio X.25 PLP       */
	/*12*/"AF_UNKNOWN",
	/*13*/"AF_MAX",      /* For now.. */
	/*14*/"AF_UNKNOWN",
	/*15*/"AF_UNKNOWN",
	/*16*/"AF_UNKNOWN",
	/*17*/"AF_PACKET"    /* Forward compat hook          */
};
/* Protocol family also has 42 types, each of which has one corresponding addres type */
const char* PROTOCOL_FAMILY[11] = {
	/* 0*/"PF_UNSPEC",
	/* 1*/"PF_UNIX/LOCAL",
	/* 2*/"PF_INET",
	/* 3*/"PF_AX25",
	/* 4*/"PF_IPX",
	/* 5*/"PF_APPLETALK",
	/* 6*/"PF_NETROM",
	/* 7*/"PF_BRIDGE",
	/* 8*/"PF_ATMPVC",
	/* 9*/"PF_X25",
	/*10*/"PF_INET6"
		/*11*/"PF_ROSE",   
	/*12*/"PF_UNKNOWN",
	/*13*/"PF_MAX",   
	/*14*/"PF_UNKNOWN",
	/*15*/"PF_UNKNOWN",
	/*16*/"PF_UNKNOWN",
	/*17*/"PF_PACKET" 
};

/* Socket type */
const HChar* SOCKET_TYPE[11] = {
	/* 0*/"SOCK_UNKNOWN",
	/* 1*/"SOCK_STREAM",
	/* 2*/"SOCK_DGRAM",
	/* 3*/"SOCK_RAM",
	/* 4*/"SOCK_RDM",
	/* 5*/"SOCK_SEQPACKET",
	/* 6*/"SOCK_UNKNOWN",
	/* 7*/"SOCK_UNKNOWN",
	/* 8*/"SOCK_UNKNOWN",
	/* 9*/"SOCK_UNKNOWN",
	/*10*/"SOCK_PACKET",
};

/* dexFileParse flags */
const HChar* DEXFILEPARSE_FLAG[3] = { 
	"kDexParseDefault",					//     = 0,
	"kDexParseVerifyChecksum",	//     = 1,
	"kDexParseContinueOnError"  //     = (1 << 1),
};


static UInt raw_file_index = 0;

static void dumpMemory(UInt index, UChar* a, UInt size) {
	tl_assert(a != 0);
	Int fout;
	HChar fpath[255];
	VG_(sprintf)(fpath, "/data/local/tmp/fuzz/0x%08x-0x%X-%d-%d.raw", (Addr)a, index, size, raw_file_index++);
	fout = VG_(fd_open)(fpath, VKI_O_WRONLY|VKI_O_TRUNC, 0);
	if (fout <= 0) {
		fout = VG_(fd_open)(fpath, VKI_O_CREAT|VKI_O_WRONLY, VKI_S_IRUSR|VKI_S_IWUSR);
		if( fout <= 0 ) {
			OAT_LOGI("Create raw file error.\n");
			return;
		}
	} 
	VG_(write)(fout, a, size);
	VG_(close)(fout);
	return True;
}


static void do_set_instrumentate(const HChar *reason, Bool state) {
	do_method_trace = state; // Represent the instrumentation state

	VG_(discard_translations_safely)( (Addr)0x1000, ~(SizeT)0xfff, "datatrace");
	MY_LOGI("%s: Switch instrumentation %s ... \n",
			reason, state ? "ON" : "OFF");

	if (VG_(clo_verbosity) > 1)
		VG_(message)(Vg_DebugMsg, "%s: instrumentation switched %s\n",
				reason, state ? "ON" : "OFF");
}


static
INLINE Bool is_base_apk(Char *path) {
	Int i = 0, j = 0, len = VG_(strlen)(path);
	Char *fileName = NULL;
	for(i = 0; i < len; i++) {
		if(path[i] == '/')
			j = i;
	}
	fileName = &path[j+1];
	if(VG_(strcmp)("base.apk", fileName) == 0) {
		return True;
	}
	return False;
}

static
Bool isFrameworkClass(HChar* desc) {
	return False;
}


ULong do_ptrace(UWord req, UInt pid, void *addr, void *data) {
	MY_LOGI("Try to invoke patrae req=0x%x pid=%d addr=0x%08x data=0x%08x\n",
			req, pid, (Addr)addr, (Addr)data);
	ULong res = VG_(ptrace)(req, pid, addr, data);
	return res;
}


#ifdef REPLACE_GETTIMEOFDAY
static UInt last_ttt = 0;
static ULong last_nts[4];
static ULong first_nts[4];

#define DBG_SHOW_STRING 0
#endif

static
Bool do_handle_client_requests( ThreadId tid, UWord *arg, UWord *ret) {
	//if(tid != 1) // Only parse the requests from the main thread
	//	return False;
	switch (arg[0]) {
#ifdef REPLACE_GETTIMEOFDAY
		case VG_USERREQ__WRAPPER_LIBC_GETTIMEOFDAY:
			{
				struct vki_timeval* tv = (struct vki_timeval*)arg[1];
				if(do_time_slower == 1)
					break;
				if(first_nts[0] == 0)
					first_nts[0] = tv->tv_sec * 1000000000ULL + tv->tv_usec * 1000ULL;
				//if(tid != 1)
				//	break;
				ULong  current_nts = tv->tv_sec * 1000000000ULL + tv->tv_usec;
				if( do_time_slower != 1 && do_time_slower != 0) {
					Double slower = (Double)do_time_slower;
					current_nts = ((current_nts - first_nts[0]) / slower) + first_nts[0];
					tv->tv_sec  = (current_nts) / 1000000000ULL;
					tv->tv_usec = ((current_nts) % 1000000000ULL) / 1000ULL;
				}
				//VG_(printf)("[LIBC] %d gettimeofday() res=%u.%u (%llu)\n",
				//		tid, tv->tv_sec, tv->tv_usec, last_ts[0]);
				last_nts[0] = current_nts;
				break;
			}
		case VG_USERREQ__WRAPPER_LIBC_CLOCK_GETTIME:
			{
				struct vki_timespec *tp = (struct vki_timespec*)arg[2];
				UInt clockid = arg[1];
				if(arg[2] == 0 || do_time_slower == 1)
					break;
				//VG_(printf)("[LIBC] %d clock_gettime() res=%u.%u (%llu) 0x%08x 0x%08x 0x%08x\n",
				//		tid, tp->tv_sec, tp->tv_nsec, last_ts[0], arg[0], arg[1], arg[2]);
				if(first_nts[clockid] == 0)
					first_nts[clockid] = tp->tv_sec * 1000000000ULL + tp->tv_nsec;
				ULong  current_nts = tp->tv_sec * 1000000000ULL + tp->tv_nsec;
				if( do_time_slower != 1 && do_time_slower != 0) {
					Double slower = (Double)do_time_slower;
					current_nts = ((current_nts - first_nts[clockid]) / slower) + first_nts[clockid];
					tp->tv_sec  = (current_nts) / 1000000000ULL;
					tp->tv_nsec = (current_nts) % 1000000000ULL;
				}
				//VG_(printf)("[LIBC] %d clock_gettime() res=%u.%09u (%llu) 1\n",
				//		tid, tp->tv_sec, tp->tv_nsec, current_nts-last_nts[0]);
				last_nts[0] = current_nts;
				break;

			}
#endif
		case VG_USERREQ__WRAPPER_LIBC_STRLEN:
			{
				if(is_in_vm > 0)
					MY_LOGI("[LIBC] %d strlen() strAddr=0x%08x res=%d\n",
							tid, (Addr)arg[1], (int)arg[2]);
				break;
			}
		case VG_USERREQ__WRAPPER_LIBC_STRDUP:
			{
				if(is_in_vm > 0)
					MY_LOGI("[LIBC] %d strdup() oldChar=0x%08x newChar=0x%08x\n",
							tid, (Addr)arg[1], (Addr)arg[2]);
				break;
			}
		case VG_USERREQ__WRAPPER_LIBC_STRCPY:
			{
				if(is_in_vm > 0)
					MY_LOGI("[LIBC] %d strcpy() srcChar=0x%08x dstChar=0x%08x\n",
							tid, (Addr)arg[1], (Addr)arg[2]);
				break;
			}
		case VG_USERREQ__WRAPPER_LIBC_MEMCPY:
			{
				if(is_in_vm > 0)
					MY_LOGI("[LIBC] %d memcpy() srcChar=0x%08x dstChar=0x%08x len=%d\n",
							tid, (Addr)arg[1], (Addr)arg[2], (int)arg[3]);
				break;
			}
		case VG_USERREQ__WRAPPER_LIBC_KILL:
			{
				VG_(printf)("[LIBC] %d kill() pid=%d sig=%d res=%d\n",	tid, arg[1], arg[2], arg[3]);
				break;
			} 
		case VG_USERREQ__WRAPPER_LIBC_EXIT:
			{
				VG_(printf)("[LIBC] %d exit()\n",	tid);
				break;
			} 
		case VG_USERREQ__WRAPPER_LIBC_EXIT_GROUP:
			{
				VG_(printf)("[LIBC] %d exit_group()\n",	tid);
				break;
			} 
		case VG_USERREQ__WRAPPER_LIBC_ABORT:
			{
				VG_(printf)("[LIBC] %d abort()\n",	tid);
				break;
			}
		case VG_USERREQ__WRAPPER_LIBC_INOTIFY_ADD_WATCH:
			{
				Int fd = (Int)arg[1];
				HChar *path = (HChar*)arg[2];
				UInt mask = (UInt)arg[3];
				VG_(printf)("[LIBC] %d inotify_add_watch() fd=%d path=%s mask=0x%x\n",
						tid, fd, path, mask);
				break;
			}
#if 0
		case VG_USERREQ__WRAPPER_ART_TEST_PRE:
			{
				Addr	this = (Addr)arg[1];
				HChar *std = (HChar*)arg[2];
				HChar *str = (HChar*)arg[3];
				MY_LOGI("[0]LIBART(%d):RewhyTest() 0x%8x 0x%08x %s\n", 
						tid, (Addr)std, (Addr)str, str);
				break;
			} 
		case VG_USERREQ__WRAPPER_ART_TEST:
			{
				Addr	this = (Addr)arg[1];
				HChar *std = (HChar*)arg[2];
				HChar *str = (HChar*)arg[3];
				MY_LOGI("[1]LIBART(%d):RewhyTest() 0x%8x 0x%08x %s\n", 
						tid, (Addr)sErrortd, (Addr)str, str);
				break;
			}
#endif
#if 1
		case VG_USERREQ__WRAPPER_LIBC_SOCKET:
			{
				Int namespace = (Int)arg[1];
				Int style			= (Int)arg[2];
				Int protocol	= (Int)arg[3];
				Int sk        = (Int)arg[4];
				VG_(printf)("[LIBC] %d socket() %d(%s) %d(%s) %d(%s) res_sk=%d\n", 
						tid, namespace, ADDRESS_FAMILY[namespace],
						style, SOCKET_TYPE[style],
						protocol, PROTOCOL_FAMILY[protocol],
						sk);
				break;
			}
		case VG_USERREQ__WRAPPER_LIBC_BIND:
			{
				Int sk = (Int)arg[1];
				struct sockaddr_in* sa = (struct sockaddr_in*)arg[2];
				HChar *addr;
				if (sa->sa_family == AF_INET)
					addr = inet_ntoa(sa->addr);
				else
					addr = ((struct sockaddr*)sa)->sa_data;
				VG_(printf)("[LIBC] %d bind() sk=%d, family=%d, addr=%s\n",
						tid, sk, sa->sa_family, addr);
				break;
			}
		case VG_USERREQ__WRAPPER_LIBC_CONNECT_PRE:
			{
				Int sk = (Int)arg[1];
				struct sockaddr_in* sa = (struct sockaddr_in*)arg[2];
				HChar *addr;
				if (sa->sa_family == AF_INET) {
					addr = inet_ntoa(sa->addr);
					VG_(printf)("[LIBC] %d connect() sk=%d, AF_INET, addr=%s:%d\n",
							tid, sk, addr, NTOHS(sa->sa_port));
					inet_aton("10.10.0.1", &sa->addr);
					addr = inet_ntoa(sa->addr);
					VG_(printf)("[LIBC] %d connect() target address modified to %s\n",
							tid, addr);
				}
				else {
					addr = ((struct sockaddr*)sa)->sa_data;
					VG_(printf)("[LIBC] %d connect() sk=%d, AF_UNIX, addr=%s\n",
							tid, sk, addr);
				}
				break;
			}
		case VG_USERREQ__WRAPPER_LIBC_CONNECT:
			{
				Int sk = (Int)arg[1];
				struct sockaddr_in* sa = (struct sockaddr_in*)arg[2];
				HChar *addr;
				Int* res = (Int*)arg[3];
				if (sa->sa_family == AF_INET) {
					addr = inet_ntoa(sa->addr);
					VG_(printf)("%d connect() sk=%d, AF_INET, addr=%s:%d, res=%d (taint)\n",
							tid, sk, addr, NTOHS(sa->sa_port), *res);
				}
				else {
					addr = ((struct sockaddr*)sa)->sa_data;
					VG_(printf)("%d connect() sk=%d, AF_UNIX, addr=%s, res=%d\n",
							tid, sk, addr, *res);
				}
				if(*res < 0) {
					*res = 0;
					VG_(printf)("%d connect() res modified to %d\n", tid, *res);
				}
				break;
			}
		case VG_USERREQ__WRAPPER_LIBC_LISTEN:
			{
				Int sk = (Int)arg[1];
				Int bl = (Int)arg[2];
				MY_LOGI("POSTREQ(%d):listen sk=%d, backlog=%d\n", tid, sk, bl);
				break;
			}
		case VG_USERREQ__WRAPPER_LIBC_ACCEPT:
			{
				Int sk = (Int)arg[1];
				struct sockaddr_in* sa = (struct sockaddr_in*)arg[2];
				Int rk = (Int)arg[3];
				HChar *addr;
				if (sa->sa_family == AF_INET)
					addr = inet_ntoa(sa->addr);
				else
					addr = ((struct sockaddr*)sa)->sa_data;
				MY_LOGI("POSTREQ(%d):accept sk=%d, family=%d, addr=%s, res=%d\n", 
						tid, sk, sa->sa_family, addr, rk);
				break;
			}
		case VG_USERREQ__WRAPPER_LIBC_SEND:
			{
				Int sk = arg[1];
				HChar* buf = (HChar*)arg[2];
				UShort flags = (UShort)arg[3];
				Int *res = (Int*)arg[4];

				MY_LOGI("POSTREQ(%d):send sk=%d, 0x%08x(%s), len=%d\n", 
						tid, sk, (Int)buf, buf, *res);
				break;
			}
		case VG_USERREQ__WRAPPER_LIBC_SENDTO:
			{
				Int sk = (Int)arg[1];
				HChar* buf = (HChar*)arg[2];
				UShort flags = (UShort)arg[3];
				struct sockaddr_in* sa = (struct sockaddr_in*)arg[4];
				Int *rlen = (Int*)arg[5];
				HChar *addr;
				if(sa) {
					if (sa->sa_family == AF_INET) {
						addr = inet_ntoa(sa->addr);
						MY_LOGI("POSTREQ(%d):sendto sk=%d, addr=%s:%d, AF_INET, 0x%08x(%s), len=%d\n", 
								tid, sk, addr, NTOHS(sa->sa_port), (Int)buf, buf, *rlen);
					}
					else {
						addr = ((struct sockaddr*)sa)->sa_data;
						MY_LOGI("POSTREQ(%d):sendto sk=%d, addr=%s:%d, AF_UNIX, 0x%08x(%s), len=%d\n", 
								tid, sk, addr, NTOHS(sa->sa_port), (Int)buf, buf, *rlen);
					}
				} else {
					MY_LOGI("POSTREQ(%d):sendto sk=%d , AF_UNIX, 0x%08x(%s), len=%d\n", 
							tid, sk,  (Int)buf, buf, *rlen);
				}

				break;
			}
		case VG_USERREQ__WRAPPER_LIBC_RECV_PRE:
			{
				Int sk = arg[1];
				HChar* buf = (HChar*)arg[2];
				UShort flags = (UShort)arg[3];
				Int *bufsize = (Int*)arg[4];

				MY_LOGI("PREVREQ(%d):recv sk=%d, 0x%08x, size=%d\n", 
						tid, sk, (Int)buf, *bufsize);
				break;
			}
		case VG_USERREQ__WRAPPER_LIBC_RECV:
			{
				Int sk = arg[1];
				HChar* buf = (HChar*)arg[2];
				UShort flags = (UShort)arg[3];
				Int *res = (Int*)arg[4];

				MY_LOGI("POSTREQ(%d):recv sk=%d, 0x%08x(%s), len=%d\n", 
						tid, sk, (Int)buf, buf, *res);

				break;
			}
		case VG_USERREQ__WRAPPER_LIBC_RECVFROM_PRE:
			{
				Int sk = (Int)arg[1];
				HChar* buf = (HChar*)arg[2];
				UShort flags = (UShort)arg[3];
				struct sockaddr_in* sa = (struct sockaddr_in*)arg[4];
				Int* rlen = (Int*)arg[5];
				HChar *addr;
				if(sa) {
					if (sa->sa_family == AF_INET) {
						addr = inet_ntoa(sa->addr);
						MY_LOGI("PREVREQ(%d):recvfrom sk=%d, addr=%s:%d, AF_INET, 0x%08x(%s), len=%d\n", 
								tid, sk, addr, NTOHS(sa->sa_port), (Int)buf, (HChar*)buf, *rlen);
					}
					else {
						addr = ((struct sockaddr*)sa)->sa_data;
						MY_LOGI("PREVREQ(%d):recvfrom sk=%d, addr=%s:%d, AF_UNIX, 0x%08x(%s), len=%d\n", 
								tid, sk, addr, NTOHS(sa->sa_port), (Int)buf, (HChar*)buf, *rlen);
					}
				} else {
					MY_LOGI("PREVREQ(%d):recvfrom sk=%d , AF_UNIX, 0x%08x(%s), len=%d\n", 
							tid, sk,  (Int)buf, (HChar*)buf, *rlen);
				}
				break;
			}
		case VG_USERREQ__WRAPPER_LIBC_RECVFROM:
			{
				Int sk = (Int)arg[1];
				HChar* buf = (HChar*)arg[2];
				UShort flags = (UShort)arg[3];
				struct sockaddr_in* sa = (struct sockaddr_in*)arg[4];
				Int* rlen = (Int*)arg[5];
				HChar *addr;
				if(sa) {
					if (sa->sa_family == AF_INET) {
						addr = inet_ntoa(sa->addr);
						MY_LOGI("POSTREQ(%d):recvfrom sk=%d, addr=%s:%d, AF_INET, 0x%08x(%s), len=%d\n", 
								tid, sk, addr, NTOHS(sa->sa_port), (Int)buf, (HChar*)buf, *rlen);
					}
					else {
						addr = ((struct sockaddr*)sa)->sa_data;
						MY_LOGI("POSTREQ(%d):recvfrom sk=%d, addr=%s:%d, AF_UNIX, 0x%08x(%s), len=%d\n", 
								tid, sk, addr, NTOHS(sa->sa_port), (Int)buf, (HChar*)buf, *rlen);
					}
				} else {
					MY_LOGI("POSTREQ(%d):recvfrom sk=%d , AF_UNIX, 0x%08x(%s), len=%d\n", 
							tid, sk,  (Int)buf, (HChar*)buf, *rlen);
				}
				break;
			}
#endif
		case VG_USERREQ__WRAPPER_DLOPEN_PRE:
			{
				MY_LOGI("[0]LIBDL(%d):dlopen() %s 0x%x\n",
						tid, (HChar*)arg[1], arg[2]);
				break;
			}
		case VG_USERREQ__WRAPPER_DLOPEN:
			{
				MY_LOGI("[1]LIBDL(%d):dlopen() %s 0x%x res=0x%08x\n",
						tid, (HChar*)arg[1], arg[2], arg[3]);
				break;
			}
		case VG_USERREQ__WRAPPER_DLSYM_PRE:
			{
				MY_LOGI("[0]LIBDL(%d):dlsym() %s handle=0x%08x\n",
						tid, (HChar*)arg[2], arg[1]);
				break;
			}
		case VG_USERREQ__WRAPPER_DLSYM:
			{
				HChar *symbol = (HChar*)arg[2];
				MY_LOGI("[1]LIBDL(%d):dlsym() %s handle=0x%08x res=0x%08x\n",
						tid, symbol, arg[1], arg[3]);
				*ret = arg[3];
				break;
				if(VG_(strcmp)("ptrace", symbol) == 0
						|| VG_(strcmp)("write", symbol) == 0)
					*ret = NULL;//(Addr)do_ptrace;
				else
					*ret = arg[3];
				break;
			}
		case VG_USERREQ__WRAPPER_ART_FINDNATIVEMETHOD:
			{
				// void* FindNativeMethod(ArtMethod* m, std::string& detail)
				struct ArtMethodPlus *pAMth = (struct ArtMethodPlus *)arg[2];
				struct StdString *library = (struct StdString*)arg[3];
				Addr codeAddr = (Addr)arg[4];
				MY_LOGI("[0]LIBART(%d) FindNativeMethod() method=%s res=0x%08x\n", tid, library ? library->data : "NULL", codeAddr);
				break;
			}
		case VG_USERREQ__WRAPPER_ART_LOADNATIVELIBRARY_PRE:
			{
				struct StdString *path = (struct StdString*)arg[1];
				if((VG_(memcmp)(path->data, "/data/", 6) == 0)
						//|| (VG_(strcmp)("/system/lib/libwebviewchromium_loader.so", path->data) == 0)
					) {
					do_set_instrumentate("start instrumentation in LoadNativeLibrary()", True);
					do_is_start = True;
				}
				MY_LOGI("[0]LIBART(%d) LoadNativeLibrary() %s\n", tid, path ? path->data : "Unknown");
				break;
			}
		case VG_USERREQ__WRAPPER_ART_LOADNATIVELIBRARY:
			{
				struct StdString *path = (struct StdString*)arg[2];
				MY_LOGI("[1]LIBART(%d) LoadNativeLibrary() %s\n", tid, path ? path->data : "Unknown");
				if(VG_(memcmp)(path->data, "/data/data/", 11) == 0 
						|| VG_(memcmp)(path->data, "/data/user/", 11) == 0 
						|| VG_(memcmp)(path->data, "/data/app/", 10) == 0) {
					//|| (VG_(strcmp)("/system/lib/libwebviewchromium_loader.so", path->data) == 0) )
					if (is_monitor_memory_alloc > 0 && VG_(strstr)(path->data, "libbaiduprotect.so")) 
					{
						is_monitor_memory_alloc = 0;
						is_dump_raw = False;
						start_trace_irst = 0;
						is_in_vm = 0;
#ifdef BAIDU_VMP
						if(pcode_items_addr > 0 && pcode_items_size > 0) {
							UInt index = 0;
							UInt size = 0;
							UInt code_addr = 0;
							UInt* pcode_array = (UInt*)pcode_items_addr;
							for (UInt ii = 0; ii < pcode_items_size; ii++) {
								index = *((UInt*)pcode_array[ii]);
								if(baidu_vmp_version == 1) {
									size  = *((UInt*)(pcode_array[ii] + 0x18)) * 2; // previous version
									code_addr = *((UInt*)(pcode_array[ii] + 0x1C));
								} else if(baidu_vmp_version == 2) {
									size  = *((UShort*)(pcode_array[ii] + 0x16)) * 2;
									code_addr = *((UInt*)(pcode_array[ii] + 0x18));
								}
								dumpMemory(index, code_addr, size);
								VG_(printf)("Dump PCode %d 0x%08x %d\n", index, code_addr, size);
							}
						}
#endif

					}
					initSysLib();
					parseOatFile(NULL);
				} else {
					if(do_is_start && path) {
						addMonitorLib(path->data);
					}
				}
				break;
			}
		case VG_USERREQ__WRAPPER_ART_OPENMEMORY_PRE:
			{
				struct StdString	 *location		= (struct StdString*)arg[1];
				struct MemMapPlus	 *pMemMapObj	= (struct MemMapPlus*)arg[2];
				MY_LOGI("[0]LIBART(%d) OpenMemory() pMemMapObj=0x%08x, location=%s\n",
						tid, (Addr)pMemMapObj, location->data);
				is_in_openmemory = True;
				break;
			}
		case VG_USERREQ__WRAPPER_ART_OPENMEMORY:
			{
				struct DexFilePlus *pDexFileObj = (struct DexFilePlus*)arg[1];
				struct StdString	 *location		= (struct StdString*)arg[2];
				struct MemMapPlus	 *pMemMapObj	= (struct MemMapPlus*)arg[3];
				MY_LOGI("[1]LIBART(%d) OpenMemory() pMemMapObj=0x%08x, location=%s, pDexFileObj=0x%08x, addr=0x%08x, size=%d\n",
						tid, (Addr)pMemMapObj, location->data, (Addr)pDexFileObj, pDexFileObj->begin_, pDexFileObj->size_);
				if(addDexFileObj((Addr)arg[1], False)) {
					addMonMap(pDexFileObj->begin_, pDexFileObj->size_, 0x0, location->data);
				}
				is_in_openmemory = False;
#if 0
				if(location->data) {
					//if(is_base_apk(location->data))
					if(VG_(memcmp)(location->data, "/data/app/", 10) == 0) {
						do_set_instrumentate("start instrumentation", True);
						if( do_is_start == False) {
							initSysLib();
							parseOatFile(NULL);
							do_is_start = True;
						}
					}
				}
#endif
				break;
			}
		case VG_USERREQ__WRAPPER_ART_DEFINECLASS_PRE:
			{
				HChar	 *descriptor = (HChar*)arg[1];
				if(isFrameworkClass(descriptor))
					break;
				//MY_LOGI("[0]LIBART(%d):DefineClass()\n", tid);
				//break;
				struct DexFilePlus *pDexFileObj = (struct DexFilePlus*)arg[2];
				struct DexClassDef *pDexClassDef = (struct DexClassDef*)arg[3];
				struct MemMapPlus  *pMemMapObj  = pDexFileObj->mem_map_;
				struct DexHeader   *pHeader     = pDexFileObj->header_;
				MY_LOGI("[0]LIBART(%d) DefineClass() %s pDexFileObj=0x%08x pMemMapObj=0x%08x 0x%08x-0x%08x 0x%08x %d\n",
						tid, descriptor, (Addr)pDexFileObj, (Addr)pMemMapObj, pDexFileObj->begin_,
						(Addr)pDexFileObj->begin_ + pDexFileObj->size_, (Addr)pHeader, pHeader->fileSize);
				VG_(printf)("	  classIdx=%d, sourceFileIdx=%d classDataOff=0x%08x staticValuesOff=0x%08x\n",
						pDexClassDef->classIdx, pDexClassDef->sourceFileIdx, pDexClassDef->classDataOff, 
						pDexClassDef->staticValuesOff);
				break;
			}
		case VG_USERREQ__WRAPPER_ART_DEFINECLASS:
			{
				HChar	 *descriptor = (HChar*)arg[1];
				if(isFrameworkClass(descriptor))
					break;
				struct DexFilePlus *pDexFileObj = (struct DexFilePlus*)arg[2];
				struct DexClassDef *pDexClassDef = (struct DexClassDef*)arg[3];
				struct MemMapPlus  *pMemMapObj  = pDexFileObj->mem_map_;
				struct DexHeader   *pHeader     = pDexFileObj->header_;
				Bool   isSave = False;
				MY_LOGI("[1]LIBART(%d) DefineClass() %s pDexFileObj=0x%08x pMemMapObj=0x%08x 0x%08x-0x%08x 0x%08x %d\n",
						tid, descriptor, (Addr)pDexFileObj, (Addr)pMemMapObj, pDexFileObj->begin_,
						(Addr)pDexFileObj->begin_ + pDexFileObj->size_, (Addr)pHeader, pHeader->fileSize);
				VG_(printf)("	  classIdx=%d, sourceFileIdx=%d classDataOff=0x%08x staticValuesOff=0x%08x\n",
						pDexClassDef->classIdx, pDexClassDef->sourceFileIdx, pDexClassDef->classDataOff, 
						pDexClassDef->staticValuesOff);
				if (pMDexFileObj == NULL && pDexClassDef->classIdx > 0) {
					if (VG_(strcmp)(do_main_activity, descriptor) == 0 ) {
						MY_LOGI("[1]LIBART(%d) The main activity class is defined..\n", tid);
						pMDexFileObj = pDexFileObj;
						pMClassDefObj = pDexClassDef;
						dumpRawData(pMDexFileObj->begin_, pMDexFileObj->size_, 0);
						//isSave = True;
					}
				}
				if( addDexFileObj((Addr)arg[2], isSave) ) {
					addMonMap(pDexFileObj->begin_, pDexFileObj->size_, 0x0, descriptor);
					if(VG_(strcmp)("Lbbbbbbbb1;", descriptor) == 0) {
						meetDexFilePlus(pDexFileObj, pDexFileObj->begin_, pDexFileObj->size_, 2);
					}
				}
#if DBG_TENCENT
				if(VG_(strcmp)("Lcom/tencent/StubShell/ZipUtil;", descriptor) == 0) {
					do_set_instrumentate("Lcom/tencent/StubShell/ZipUtil;", True);
					//initSysLib();
					//parseOatFile(NULL);
				}
#endif
				break;
			}
		case VG_USERREQ__WRAPPER_ART_LOADCLASS_PRE:
			{
				break;
			}
		case VG_USERREQ__WRAPPER_ART_LOADCLASS:
			{
				struct DexFilePlus *pDexFileObj = (struct DexFilePlus*)arg[1];
				struct DexClassDef *pDexClassDef = (struct DexClassDef*)arg[2];
				struct MemMapPlus  *pMemMapObj  = pDexFileObj->mem_map_;
				struct DexHeader   *pHeader     = pDexFileObj->header_;
				MY_LOGI("[1]LIBART(%d) LoadClass() pDexFileObj=0x%08x pMemMapObj=0x%08x 0x%08x-0x%08x 0x%08x %d\n",
						tid, (Addr)pDexFileObj, (Addr)pMemMapObj, pDexFileObj->begin_,
						(Addr)pDexFileObj->begin_ + pDexFileObj->size_, (Addr)pHeader, pHeader->fileSize);
				VG_(printf)("	  kclass=0x%08x, classIdx=%d, sourceFileIdx=%d classDataOff=0x%08x staticValuesOff=0x%08x\n",
						arg[3], pDexClassDef->classIdx, pDexClassDef->sourceFileIdx, pDexClassDef->classDataOff, 
						pDexClassDef->staticValuesOff);
				break;
			}
		case VG_USERREQ__WRAPPER_ART_LOADCLASSMEMBERS_PRE:
			{ //DO_CREQ_v_WWWW(VG_USERREQ__WRAPPER_ART_LOADCLASSMEMBERS_PRE, void*, dex_file, void*, class_data, void*, klass, void*, oat_class);
				struct DexFilePlus *pDexFileObj = (struct DexFilePlus*)arg[1];
				struct MemMapPlus  *pMemMapObj  = pDexFileObj->mem_map_;
				struct DexHeader   *pHeader     = pDexFileObj->header_;
				UChar *class_data = (UChar*)arg[2];
				MY_LOGI("[0]LIBART(%d) LoadClassMembers() pDexFileObj=0x%08x pMemMapObj=0x%08x 0x%08x-0x%08x 0x%08x %d class_data=0x%08x\n",
						tid, (Addr)pDexFileObj, (Addr)pMemMapObj, pDexFileObj->begin_,
						(Addr)pDexFileObj->begin_ + pDexFileObj->size_, (Addr)pHeader,
						pHeader->fileSize, (Addr)class_data);
				break;
			}
		case VG_USERREQ__WRAPPER_ART_LOADCLASSMEMBERS:
			{ //DO_CREQ_v_WWWW(VG_USERREQ__WRAPPER_ART_LOADCLASSMEMBERS_PRE, void*, dex_file, void*, class_data, void*, klass, void*, oat_class);
				struct DexFilePlus *pDexFileObj = (struct DexFilePlus*)arg[1];
				struct MemMapPlus  *pMemMapObj  = pDexFileObj->mem_map_;
				struct DexHeader   *pHeader     = pDexFileObj->header_;
				UChar *class_data = (UChar*)arg[2];
				MY_LOGI("[1]LIBART(%d) LoadClassMembers() pDexFileObj=0x%08x pMemMapObj=0x%08x 0x%08x-0x%08x 0x%08x %d class_data=0x%08x 0x%08x 0x%08x\n",
						tid, (Addr)pDexFileObj, (Addr)pMemMapObj, pDexFileObj->begin_,
						(Addr)pDexFileObj->begin_ + pDexFileObj->size_, (Addr)pHeader,
						pHeader->fileSize, (Addr)class_data, (Addr)arg[3], (Addr)arg[4]);
				if (pDexFileObj == pMDexFileObj) {
				}
				break;
			}
		case VG_USERREQ__WRAPPER_ART_CALLMETHODA:
			{
				HChar *fn_name = (HChar*)arg[1];
				Int mid				 = arg[2];
				Int type			 = arg[3];
				Int invoke		 = arg[4];
				MY_LOGI("[0]LIBART(%d) CallMethodA() %s mid=%d type=%dinvoke=%d\n", tid, fn_name, mid, type, invoke);
				break;
			}
		case VG_USERREQ__WRAPPER_ART_CALLMETHODV:
			{
				HChar *fn_name = (HChar*)arg[1];
				Int mid				 = arg[2];
				Int type			 = arg[3];
				Int invoke		 = arg[4];
				MY_LOGI("[0]LIBART(%d) CallMethodV() %s mid=%d type=%dinvoke=%d\n", tid, fn_name, mid, type, invoke);
				break;
			}
#if 0
		case VG_USERREQ__WRAPPER_ART_INVOKEWITHVARARGS:
			{
				Int mid = (Int)arg[3];
				MY_LOGI("[1]LIBART(%d):InvokeWithVarArgs(JNI Reflection) mid=%d\n",tid, mid);
				break;
			}
		case VG_USERREQ__WRAPPER_ART_INVOKEWITHJVALUES:
			{
				Int mid = (Int)arg[3];
				MY_LOGI("[1]LIBART(%d):InvokeWithJValues(JNI Reflection) mid=%d\n",tid, mid);
				break;
			}
		case VG_USERREQ__WRAPPER_ART_INVOKEVIRTUALORINTERFACEWITHJVALUES:
			{
				Int mid = (Int)arg[3];
				MY_LOGI("[1]LIBART(%d):InvokeVirtualOrInterfaceWithJValues(JNI Reflection) mid=%d\n",tid, mid);
				break;
			}
		case VG_USERREQ__WRAPPER_ART_INVOKEVIRTUALORINTERFACEWITHVARARGS:
			{
				Int mid = (Int)arg[3];
				MY_LOGI("[1]LIBART(%d):InvokVirtualOrInterfaceWithVarArgs(JNI Reflection) mid=%d\n",tid, mid);
				break;
			}
		case VG_USERREQ__WRAPPER_ART_INVOKEMETHOD:
			{
				MY_LOGI("[1]LIBART(%d):InvokeMethod(Java Reflection) javaMethod=0x%08x\n", tid, arg[2]);
				break;
			}
		case VG_USERREQ__WRAPPER_ART_INVOKEWITHARGARRAY:
			{
				struct ArtMethodPlus *pAMth = (struct ArtMethodPlus *)arg[1];
				MY_LOGI("[1]LIBART(%d):InvokeWithArgArray() pArtMethod=0x%08x\n", tid, (Addr)pAMth);
				break;
			}
		case VG_USERREQ__WRAPPER_ART_INVOKE_PRE:
			{
				if(do_is_start == False)
					return False;
				struct ArtMethodPlus *pAMth = (struct ArtMethodPlus *)arg[1];
				MY_LOGI("[0]LIBART(%d):Invoke() pArtMethod=0x%08x index=%d %s()\n", tid, (Addr)pAMth,
						pAMth->dex_method_index_,
						((pAMth->dex_method_index_ < MAX_MTH_NUM) && (mth_index_name[pAMth->dex_method_index_] == NULL)) ? "???" : mth_index_name[pAMth->dex_method_index_]);
				break;
			}
#endif
		case VG_USERREQ__WRAPPER_ART_INVOKE:
			{
				if(do_is_start == False)
					return False;
				struct ArtMethodPlus *pAMth = (struct ArtMethodPlus *)arg[1];
				MY_LOGI("[1]LIBART(%d):Invoke() pArtMethod=0x%08x index=%d %s()\n", tid, (Addr)pAMth,
						pAMth->dex_method_index_,
						((pAMth->dex_method_index_ < MAX_MTH_NUM) && (mth_index_name[pAMth->dex_method_index_] == NULL)) ? "???" : mth_index_name[pAMth->dex_method_index_]);
				if( pAMth->dex_method_index_ == do_main_oncreate_index ) {
						dumpRawData(pMDexFileObj->begin_, pMDexFileObj->size_, 0);
				}
				break;
			}
		case VG_USERREQ__WRAPPER_ART_REGISTERNATIVE:
			{
				struct ArtMethodPlus *pAMth = (struct ArtMethodPlus *)arg[1];
				if(do_is_start == False)
					return False;
				//MthNode* query_method_node(Addr codeAddr, Int index)
				//MthNode *pNote = (MthNode*)query_method_node(pAMth->codeAddr, pAMth
				HChar *codeInfo;
				codeInfo = VG_(describe_IP) ( arg[2], NULL );
				MY_LOGI("[1]LIBART(%d):RegisterNative() pArtMethod=0x%08x nativeCode=0x%08x (%s)\n", 
						tid, (Addr)pAMth, (Addr)arg[2], codeInfo);
				break;
			}
		case VG_USERREQ__WRAPPER_ART_GETSTRINGUTFCHARS:
			{
				HChar *str = (HChar*)arg[1];
				if(do_is_start == False)
					return False;
				//if(VG_(memcmp)("aGlvZi5lbm", str, 10) == 0)
				//	str[1] = 'b';
				MY_LOGI("[1]LIBART(%d):GetStringUTFChars() res=%s\n", tid, str);
				break;
			}
		case VG_USERREQ__WRAPPER_ART_JNIFINDCLASS:
			{
				HChar *class_name = (HChar*)arg[2];
				Addr  res         = (Addr)arg[3];
				MY_LOGI("[1]LIBART(%d):FindClass() 0x%08x(%s) jclass=0x%08x\n",tid, (Addr)class_name, class_name, res);
				if(do_is_start == False)
					return False;
				if (is_monitor_memory_alloc == 0 && VG_(strstr)(class_name, "bbbbbbbb1")) {
					is_monitor_memory_alloc = tid;
					//start_trace_irst = tid;
					is_in_vm = tid;
				}
				break;
			}
		case VG_USERREQ__WRAPPER_ART_JNIGETMETHODID:
			{
				Addr cl = (Addr)arg[1];
				HChar* mth_name = (HChar*)arg[2];
				HChar* sig = (HChar*)arg[3];
				struct ArtMethodPlus *pAMth = (struct ArtMethodPlus *)arg[4];
				UInt c_flags = 0;
				if(pAMth) {
					c_flags = get_declaring_class_flags(pAMth->declaring_class_);
				}
				MY_LOGI("[1]LIBART(%d):GetMethodID() jclass=0x%08x %s %s jmethodId=0x%08x, accFlags=0x%08x(0x%08x), declaring_class=0x%08x, dex_method_index=%d, method_idex=%d\n",
						tid, cl, mth_name, sig, (Addr)pAMth,
						pAMth == NULL ? 0  : pAMth->access_flags_,
						c_flags,
						pAMth == NULL ? -1 : pAMth->declaring_class_,
						pAMth == NULL ? -1 : pAMth->dex_method_index_,
						pAMth == NULL ? -1 : pAMth->method_index_);

				if(pAMth != NULL ) { 
					if(pAMth->dex_method_index_ < MAX_MTH_NUM) {
						mth_index_name[pAMth->dex_method_index_] = mth_name;
					}
				}
				/*if(do_is_start) {
					if(VG_(strcmp)("intern", mth_name) == 0) {
				//start_trace_irst = tid;
				//is_in_vm = tid;
				is_monitor_memory_alloc = tid;
				}
				}*/
				break;
			}
		case VG_USERREQ__WRAPPER_ART_JNIGETSTATICMETHODID:
			{
				Addr cl = (Addr)arg[1];
				HChar* mth_name = (HChar*)arg[2];
				HChar* sig = (HChar*)arg[3];
				Addr res = (Addr)arg[4];
				MY_LOGI("[1]LIBART(%d):GetStaticMethodID() 0x%08x %s %s id=0x%08x\n",tid, cl, mth_name, sig, res);
				break;
			}
		case VG_USERREQ__WRAPPER_ART_DEXFILE:
			{
				struct DexFilePlus *pDexFileObj = (struct DexFilePlus*)arg[1];
				struct MemMapPlus  *pMemMapObj  = pDexFileObj->mem_map_;
				Addr base = (Addr)arg[2];
				UInt len  = (UInt)arg[3];
				struct StdString *location = (struct StdString*)arg[4];
				Addr memmap = (Addr)arg[5];
				MY_LOGI("[1]LIBART(%d):DexFile() pMemMapObj=0x%08x, location=%s, pDexFileObj=0x%08s\n",
						tid, (Addr)pMemMapObj, location->data, (Addr)pDexFileObj);
				break;
			}
		case VG_USERREQ__WRAPPER_ART_JNI_NEWGLOBALREF:
			{
				const Addr oldObj = (Addr)arg[1];
				const Addr newObj = (Addr)arg[2];
				MY_LOGI("[1]LIBART(%d):NewGlobalRef() oldObj=0x%08x newObj=0x%08x\n",
						tid, oldObj, newObj);
				break;
			}
		case VG_USERREQ__WRAPPER_ART_JNI_NEWCHARARRAY:
			{
				const Addr len = (Addr)arg[1];
				const Addr res = (Addr)arg[2];
				MY_LOGI("[1]LIBART(%d):NewCharArray() len=%d res=0x%08x\n",
						tid, len, res);
				break;
			}
		case VG_USERREQ__WRAPPER_ART_JNI_NEWBYTEARRAY:
			{
				const Addr len = (Addr)arg[1];
				const Addr res = (Addr)arg[2];
				MY_LOGI("[1]LIBART(%d):NewByteArray() len=%d res=0x%08x\n",
						tid, len, res);
				break;
			}
		case VG_USERREQ__WRAPPER_ART_JNI_NEWINTARRAY:
			{
				const Addr len = (Addr)arg[1];
				const Addr res = (Addr)arg[2];
				MY_LOGI("[1]LIBART(%d):NewIntArray() len=%d res=0x%08x\n",
						tid, len, res);
				break;
			}
		case VG_USERREQ__WRAPPER_ART_JNI_NEWOBJECTARRAY:
			{
				const Addr len = (Addr)arg[1];
				const Addr res = (Addr)arg[4];
				MY_LOGI("[1]LIBART(%d):NewObjectArray() len=%d res=0x%08x\n",
						tid, len, res);
				break;
			}
#if 1
		case VG_USERREQ__WRAPPER_CLASSLINKER_LOADMETHOD:
			{
				if(do_is_start == False)
					break;

				struct DexFilePlus *pDexFileObj = (struct DexFilePlus*)arg[1];
				const Addr jclass = (Addr)arg[2];
				struct ArtMethodPlus *pAMth = (struct ArtMethodPlus *)arg[3];
				Addr dex_code_item_addr = 0; 
				if( pAMth->dex_code_item_offset_ > 0 ) 
					dex_code_item_addr = pDexFileObj->begin_ + pAMth->dex_code_item_offset_;
				MY_LOGI("[1]LIBART[%d]:LoadMethod() ArtMethod=0x%08x dex_method_index=%d method_index=%d kclass=0x%08x pDexFileObj=0x%08x dexCodeItemOffset=0x%08x(0x%08x)\n", 
						tid, (Addr)pAMth, pAMth->dex_method_index_, pAMth->method_index_,
						(Addr)jclass, (Addr)pDexFileObj, pAMth->dex_code_item_offset_, dex_code_item_addr);
				//if(pAMth->dex_code_item_offset_ > 0)
				//	dumpCode((const struct DexCode*)dex_code_item_addr);
				// (mth_index_name[pAMth->dex_method_index_] == NULL) ? "???" : mth_index_name[pAMth->dex_method_index_]);
				break;
			}
#endif
		case VG_USERREQ__WRAPPER_CLASSLINKER_LINKCODE:
			{ 
				struct ArtMethodPlus *pAMth = (struct ArtMethodPlus *)arg[1];
				MY_LOGI("[1]LIBART[%d]:LinkCode() flags=0x%08x dex_method_index=%d method_index=%d\n", 
						tid, pAMth->access_flags_, pAMth->dex_method_index_, arg[3]);
				break;
			}
		case VG_USERREQ__WRAPPER_REP_MEMSET:
			{
				const HChar *s = (HChar*)arg[1];
				const HChar c = (HChar)arg[2];
				const Int n = (Int)arg[3];
				//if(is_in_vm > 0)
				if(is_monitor_memory_alloc == tid)
					VG_(printf)("[MEM]: %2d memset() s=0x%08x c=0x%02x n=%d\n", tid, (Addr)s, c, n);
#ifdef STR_COMPARE
#endif
				break;
			}
		case VG_USERREQ__WRAPPER_REP_STRCPY:
			{
				if(is_in_vm > 0)
					MY_LOGI("[REP] %d strcpy() srcChar=0x%08x dstChar=0x%08x\n",
							tid, (Addr)arg[1], (Addr)arg[2]);
				break;
			}
		case VG_USERREQ__WRAPPER_REP_MEMCPY:
			{
				if(is_in_vm > 0)
					MY_LOGI("[REP] %d memcpy() srcChar=0x%08x dstChar=0x%08x\n",
							tid, (Addr)arg[1], (Addr)arg[2]);
				break;
			}
		case VG_USERREQ__WRAPPER_REP_MEMMOVE_OR_MEMCPY:
			{
				const HChar *s1 = (HChar*)arg[1];
				const HChar *s2 = (HChar*)arg[2];
				const Int n = (Int)arg[3];
				//if(is_in_vm > 0 && tid == 1)
				if(is_monitor_memory_alloc == tid)
				{
					VG_(printf)("[MEM]: %2d memcpy() s1=0x%08x s2=0x%08x n=%d %s\n", tid, (Addr)s1, (Addr)s2, n, s2);
#if 0 
					//BAIDU_VMP
					if(is_dump_raw) {
						if((last_new_mem_addr2 == (Addr)s1) && (last_new_mem_size2 == n)) {
							if(last_new_mem_size1 == 44) {
								UInt index = *((UInt*)last_new_mem_addr1);
								UInt size  = *((UInt*)last_new_mem_addr1 + 6) * 2;
								Addr code_addr = *((UInt*)last_new_mem_addr1 + 7);
								if((size == n) && (code_addr == (Addr)s1))
								{
									dumpMemory(index, s2, n);
									VG_(printf)("Dump PCode %d 0x%08x %d", index, s2, n);
								}
								last_code_header_addr = last_new_mem_addr1;
							} else {
								UInt index = *((UInt*)last_code_header_addr);
								UInt tries_num      = *((UInt*)last_code_header_addr + 8);
								UInt tries_mem_size = *((UInt*)last_code_header_addr + 9);
							}
						}
						if(VG_(strstr)(s2, "Finish") > 0) {
							is_monitor_memory_alloc = 0;
							is_dump_raw = False;
							start_trace_irst = 0;
							is_in_vm = 0;
						} 
					}
#endif
				}
#ifdef STR_COMPARE
#endif
				break;
			}
		case VG_USERREQ__WRAPPER_REP_STRLEN:
			{
				const HChar *s1 = (HChar*)arg[1];
				const Int n = (Int)arg[2];
				//if(is_in_vm > 0)
				if(is_monitor_memory_alloc == tid)
					VG_(printf)("[MEM]: %2d strlen() s=0x%08x(%s) len=%d\n", tid, arg[1], s1, n);
#ifdef STR_COMPARE
#endif
				break;
			}
		case VG_USERREQ__WRAPPER_REP_MEMCMP:
			{
				const HChar *s1 = (HChar*)arg[1];
				const HChar *s2 = (HChar*)arg[2];
				const Int n = (Int)arg[3];
				//if(is_in_vm > 0)
				if(is_monitor_memory_alloc == tid)
					VG_(printf)("[MEM]: %2d memcmp() s1=0x%08x(%s) s2=0x%08x(%s) n=%d\n", tid, arg[1], s1, arg[2], s2, n);
#ifdef STR_COMPARE
#endif
				break;
			}
		case VG_USERREQ__WRAPPER_REP_STRSTR:
			{
				const HChar *s1 = (HChar*)arg[1];
				const HChar *s2 = (HChar*)arg[2];
				if(is_in_vm > 0)
					if(is_monitor_memory_alloc == tid)
						VG_(printf)("[MEM] %2d strstr() s1=0x%08x(%s) s2=0x%08x(%s)\n", tid, arg[1], s1, arg[2], s2); 
#ifdef STR_COMPARE
#endif
				break;
			}
		case VG_USERREQ__WRAPPER_REP_STRCASECMP:
		case VG_USERREQ__WRAPPER_REP_STRCMP:
			{
				const HChar *s1 = (HChar*)arg[1];
				const HChar *s2 = (HChar*)arg[2];
				//if(is_in_vm > 0)
				if(is_monitor_memory_alloc == tid) {
					VG_(printf)("[MEM]: %2d strcmp() s1=0x%08x(%s) s2=0x%08x(%s)\n", tid, arg[1], s1, arg[2], s2);
#ifdef BAIDU_VMP
					if(VG_(strcmp)("BAIDU0", s1) == 0) {
						is_dump_raw = True; 
						if(VG_(strcmp)("BAIDU0", s2) == 0) {
							baidu_vmp_version = 1;
						} else {
							baidu_vmp_version = 2;
						}
						VG_(printf)("[PCODE]: %02d Start to parse PCode (Baidu packer version %d)\n", tid, baidu_vmp_version);
					}
#endif
				}
#ifdef STR_COMPARE
#endif
				break;
			}
		case VG_USERREQ__WRAPPER_REP_STRNCASECMP:
		case VG_USERREQ__WRAPPER_REP_STRNCMP:
			{
				const HChar *s1 = (HChar*)arg[1];
				const HChar *s2 = (HChar*)arg[2];
				const Int len = (Int)arg[3];
				//if(is_in_vm > 0 && tid == 1)
				if(is_monitor_memory_alloc == tid)
					VG_(printf)("[MEM]: %2d strncmp() s1=0x%08x(%s) s2=0x%08x(%s) len=%d\n", tid, arg[1], s1, arg[2], s2, len);
#ifdef STR_COMPARE
#endif
				break;
			}
		case VG_USERREQ__WRAPPER_ART_CALLSTATICOBJECTMETHODV_PRE:
			{
				const Addr jclass = (Addr)arg[2];
				const Int  mid = (Addr)arg[3];
				if(codeLayer[tid] == 1)
					MY_LOGI("[0]LIBART[%d]:CallStaticObjectMethodV jclass=0x%08x mid=0x%x\n", tid, jclass, mid);
				break;
			}
		case VG_USERREQ__WRAPPER_ART_CALLSTATICOBJECTMETHODV:
			{
				const Addr jclass = (Addr)arg[2];
				const Int  mid = (Addr)arg[3];
				if(codeLayer[tid] == 1)
					MY_LOGI("[1]LIBART[%d]:CallStaticObjectMethodV jclass=0x%08x mid=0x%x\n", tid, jclass, mid); 
				break;
			}
		default:
			{
				return False;
			}
	}
	return True;
}

/*-------------------------- End ----------------------------------*/

//
//  SYSCALL WRAPPERS
//

// #define TEST_FILE   "test.txt"

void handle_sys_read(ThreadId tid, UWord *args, UInt nArgs, SysRes res)
{
	int fd;
	void* buf;
	unsigned long i;

	Int len = sr_Res(res);
	if (len > 0)
	{
		fd = (int)args[0];
		buf = (void*)args[1];

		if (fd == fd_to_taint)
		{
			VG_(printf)("read(%p) = %lu\n", buf, len);

			for (i = 0; i < len; i++)
			{
				if (!memory_is_tainted(((UInt)buf)+i, 8))
				{
					flip_memory(((UInt)buf)+i, 8, 1);
				}

				char dep[DEP_MAX_LEN] = {0};
				VG_(snprintf)(dep, DEP_MAX_LEN, "INPUT(%lu)", i);

				update_memory_dep(((UInt)buf)+i, dep, 8);
			}
		}
	}
}

static void pre_syscall(ThreadId tid, UInt syscall_number, UWord* args, UInt nArgs)
{
	//VG_(printf)("0 %d sysno = %-3d %s\n", tid, syscall_number, syscallnames[syscall_number]);
	switch ((int)syscall_number) {
		case __NR_exit:
			DO_(syscall_pre_exit)(tid, args, nArgs);
			break;
		case __NR_execve:
			DO_(syscall_pre_execve)(tid, args, nArgs);
			break;
		case __NR_unlinkat:
			DO_(syscall_pre_unlinkat)(tid, args, nArgs);
			break;
		default:
			break;
	}
	if(do_is_start == False) 
		return False;
	switch ((int)syscall_number) {
		case __NR_fork:
			DO_(syscall_pre_fork)(tid, args, nArgs);
			break;
		case __NR_ptrace:
			DO_(syscall_pre_ptrace)(tid, args, nArgs);
			break;
		case __NR_rt_sigreturn:
			DO_(syscall_pre_rt_sigreturn)(tid, args, nArgs);
			break;
		default:
			break;
	}
}

static void post_syscall(ThreadId tid, UInt syscall_number, UWord* args, UInt nArgs, SysRes res)
{
	//if(do_is_start == False) 
	//	return False;
	//if(tid != 1)
	//	return;
	//VG_(printf)("1 %d sysno = %d\n", tid, syscall_number);
	switch ((int)syscall_number) {
		// Should be defined by respective include/vki/vki-scnums-arch-os.h
		case __NR_clone:
			DO_(syscall_clone)(tid, args, nArgs, res);
			break;
		case __NR_rt_sigaction:
		case __NR_sigaction:
			DO_(syscall_action)(tid, args, nArgs, res);
			break;
		case __NR_unlink:
			DO_(syscall_unlink)(tid, args, nArgs, res);
			break;
		case __NR_unlinkat:
			DO_(syscall_unlinkat)(tid, args, nArgs, res);
			break;
		case __NR_execve:
			DO_(syscall_execve)(tid, args, nArgs, res);
			break;
		case __NR_read:
			DO_(syscall_read)(tid, args, nArgs, res);
			break;
		case __NR_pread64:
			DO_(syscall_pread)(tid, args, nArgs, res);
			break;
		case __NR_readv:
			DO_(syscall_readv)(tid, args, nArgs, res);
			break;
		case __NR_preadv:
			DO_(syscall_preadv)(tid, args, nArgs, res);
			break;
		case __NR_write:
			DO_(syscall_write)(tid, args, nArgs, res);
			break;
		case __NR_writev:
			DO_(syscall_writev)(tid, args, nArgs, res);
			break;
		case __NR_pwritev:
			DO_(syscall_pwritev)(tid, args, nArgs, res);
			break;
		case __NR_close:
			DO_(syscall_close)(tid, args, nArgs, res);
			break;
		case __NR_mprotect:
			DO_(syscall_mprotect)(tid, args, nArgs, res);
			break;
		case __NR_msync:
			DO_(syscall_msync)(tid, args, nArgs, res);
			break;
		case __NR_munmap:
			DO_(syscall_munmap)(tid, args, nArgs, res);
			break;
		case __NR_mmap2:
			DO_(syscall_mmap)(tid, args, nArgs, res);
			break;
		case __NR_ptrace:
			DO_(syscall_ptrace)(tid, args, nArgs, res);
			break;
		case __NR_open:
		case __NR_openat:
			DO_(syscall_open)(tid, args, nArgs, res);
			break;
		case __NR_fork:
			DO_(syscall_fork)(tid, args, nArgs, res);
			break;
		case __NR_lseek:
			//	DO_(syscall_lseek)(tid, args, nArgs, res);
			break;
		case __NR_madvise:
			DO_(syscall_madvise)(tid, args, nArgs, res);
			break;
		case __NR_futex:
			DO_(syscall_futex)(tid, args, nArgs, res);
			break;
		case __NR_flock:
			DO_(syscall_flock)(tid, args, nArgs, res);
			break;
		case __NR_fstatat64:
			DO_(fstatat)(tid, args, nArgs, res);
			break;
		case __NR_inotify_add_watch:
			DO_(inotify_add_watch)(tid, args, nArgs, res);
			break;
#ifdef __NR_llseek
		case __NR_llseek:
			DO_(syscall_llseek)(tid, args, nArgs, res);
			break;
#endif
#if 0
		case __NR_setuid:
		case __NR_setuid32:
			DO_(syscall_setuid)(tid, args, nArgs, res);
			break;
		case __NR_setreuid:
		case __NR_setreuid32:
			DO_(syscall_setreuid)(tid, args, nArgs, res);
			break;
		case __NR_setgid:
		case __NR_setgid32:
			DO_(syscall_setgid)(tid, args, nArgs, res);
			break;
		case __NR_setregid:
		case __NR_setregid32:
			DO_(syscall_setregid)(tid, args, nArgs, res);
			break;
#ifdef __NR_recv
		case __NR_recv:
			DO_(syscall_recv)(tid, args, nArgs, res);
			break;
#endif
#ifdef __NR_recvfrom
		case __NR_recvfrom:
			DO_(syscall_recvfrom)(tid, args, nArgs, res);
			break;
#endif
		default:
			break;
#endif // VGO_freebsd
	}
}

//
//  BASIC TOOL FUNCTIONS
//
static Bool do_process_cmd_line_option(Char* arg)
{
	if VG_STR_CLO(arg, "--fname", clo_fnname) {}
	else if VG_INT_CLO(arg, "--start-index",		do_start_method_index){}
	else if VG_STR_CLO(arg, "--start-method",		do_start_method_name){VG_(printf)("Start method: %s\n", do_start_method_name);}
	else if VG_STR_CLO(arg, "--start-shorty",		do_start_method_shorty){VG_(printf)("Start shorty: %s\n", do_start_method_shorty);}
	else if VG_INT_CLO(arg, "--stop-index",			do_stop_method_index){}
	else if VG_STR_CLO(arg, "--stop-method",		do_stop_method_name){VG_(printf)("Stop method: %s\n", do_stop_method_name);}
	else if VG_STR_CLO(arg, "--start-class",		do_start_clazz) {VG_(printf)("Start class: %s\n", do_start_clazz);}
	else if VG_STR_CLO(arg, "--main-activity",	do_main_activity) {VG_(printf)("Main activity: %s\n", do_main_activity);}
	else if VG_STR_CLO(arg, "--stop-class",			do_stop_clazz) {VG_(printf)("Stop class: %s\n", do_stop_clazz);}
	else if VG_INT_CLO(arg, "--time-slow",			do_time_slower) {}
	else 
		return VG_(replacement_malloc_process_cmd_line_option)(arg);

	// tl_assert(clo_fnname);
	// tl_assert(clo_fnname[0]);
	return True;
}

static void do_print_usage(void)
{
	VG_(printf)(
			"    --fnname=<filename>								file to taint\n"
			"    --start-index=<Method_index>				the mthod index for starting analysis in detail\n"
			"    --start-method=<Method_name>				the mthod name for starting analysis in detail\n"
			"    --stop-index=<Method_index>				the result of the method for tainting\n"
			"    --stop-name=<Method_name>					the arguments of the method for tainting\n"
			"    --start-class=<Class_name>					the class name for starting analysis\n"
			"    --stop-class=<Class_name>					the class name for stopping analysis\n"
			"    --time-slow=<slower>               the times for making the timestamps slower\n"
			);
}

static void do_print_debug_usage(void)
{
	VG_(printf)("    (none)\n");
}

static void do_post_clo_init(void)
{
	// init_shadow_memory();
}


static void do_fini(Int exitcode)
{
	destroy_shadow_memory();
	releaseDexFileList();
	if (pMDexFileObj == NULL) {
		saveDexFileObjs();
	} else {
		dumpRawData(pMDexFileObj->begin_, pMDexFileObj->size_, 2);
	}
	do_is_start = False;
}

static void do_pre_clo_init(void)
{
	VG_(details_name)            ("deobfustator");
	VG_(details_version)         ("0.1.2");
	VG_(details_description)     ("A tool for de-obfuscating the packed Android apps");
	VG_(details_copyright_author)("Copyright (C) 2016, Rewhy.");
	VG_(details_bug_reports_to)  (VG_BUGS_TO);

	VG_(details_avg_translation_sizeB) ( 275 );

	VG_(needs_libc_freeres)				();
	VG_(needs_malloc_replacement)	(
			do_malloc,
			do_builtin_new,
			do_builtin_vec_new,
			do_memalign,
			do_calloc,
			do_free,
			do_builtin_delete,
			do_builtin_vec_delete,
			do_realloc,
			do_malloc_usable_size,
			0 );

	do_malloc_list = VG_(HT_construct)( "do_malloc_list" );
	VG_(basic_tool_funcs)        (do_post_clo_init,
			do_instrument,
			do_fini);

	VG_(needs_command_line_options)(do_process_cmd_line_option,
			do_print_usage,
			do_print_debug_usage);

	VG_(needs_syscall_wrapper) (pre_syscall, post_syscall);
	VG_(needs_client_requests) (do_handle_client_requests);
	/* No needs, no core events to track */
}

VG_DETERMINE_INTERFACE_VERSION(do_pre_clo_init)
