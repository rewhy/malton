// do_instrument.c
#include "pub_tool_basics.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_libcassert.h"    // tl_assert()
#include "pub_tool_libcprint.h"     // VG_(printf)
#include "pub_tool_machine.h"       // VG_(fnptr_to_fnentry)
#include "pub_tool_libcbase.h"      // VG_(strcmp)
#include "pub_tool_options.h"
#include "pub_tool_libcfile.h"      // VG_(readlink)
#include "pub_tool_vki.h"           // keeps libcproc.h happy, syscall nums

#include "pub_tool_debuginfo.h"
#include "pub_core_threadstate.h"

#include "do_dexparse.h"
#include "do_oatparse.h"
#include "do_framework.h"

#include "do_wrappers.h"
#include "shadow_memory.h"

extern Bool do_method_trace;

extern Int		do_start_method_index;
extern HChar*	do_start_method_name;
extern HChar*	do_start_method_shorty;
extern Int		do_stop_method_index;
extern HChar*	do_stop_method_name;
extern Addr		do_exit_addr;
extern HChar*	do_start_clazz;
extern HChar*	do_main_activity;
extern HChar*	do_stop_clazz;

extern Bool do_is_start;
extern UInt is_trace_irst;
extern UInt start_trace_irst;
extern UInt is_in_vm;

Addr target_mem_addr = 0;
UInt target_mem_len  = 0;

extern UChar codeLayer[TG_N_THREADS];

extern struct DexFilePlus *pMDexFileObj;

static UInt valueOfConst(IRExpr* data) 
{
	UInt data_value = -1;
	if (data->tag == Iex_Const)
	{
		switch (data->Iex.Const.con->tag)
		{
			case Ico_U1:	data_value = data->Iex.Const.con->Ico.U1; break;
			case Ico_U8:	data_value = data->Iex.Const.con->Ico.U8; break;
			case Ico_U16: data_value = data->Iex.Const.con->Ico.U16; break;
			case Ico_V128:data_value = data->Iex.Const.con->Ico.V128; break;
			case Ico_U32: data_value = data->Iex.Const.con->Ico.U32; break;
			case Ico_F32i:data_value = data->Iex.Const.con->Ico.F32i; break;
			case Ico_V256:data_value = data->Iex.Const.con->Ico.V256; break;
			case Ico_U64:	data_value = data->Iex.Const.con->Ico.U64; break;
			case Ico_F64i:data_value = data->Iex.Const.con->Ico.F64i; break;
			default: ppIRExpr(data); tl_assert(0);
		}
	}
	return data_value;
}

static Int sizeofIRType_bits(IRType ty)
{
	switch (ty)
	{
		case Ity_I1: return 1;
		case Ity_I8: return 8;
		case Ity_I16: return 16;
		case Ity_I32: return 32;
		case Ity_I64: return 64;
		case Ity_I128: return 128;
		case Ity_F32: return 32;
		case Ity_F64: return 64;
		case Ity_D32: return 32;
		case Ity_D64: return 64;
		case Ity_D128: return 128;
		case Ity_F128: return 128;
		case Ity_V128: return 128;
		case Ity_V256: return 256;
		default: VG_(tool_panic)("sizeofIRType_bits");
	}
}

/*
	 Bind the given expression to a new temporary, and return the temporary.
	 This effectively converts an arbitrary expression into an IRAtom.
	 */
static IRExpr* assignNew(IRSB* sb_out, IRExpr* expr)
{
	IRTemp tmp = newIRTemp(sb_out->tyenv, typeOfIRExpr(sb_out->tyenv, expr));

	addStmtToIRSB(sb_out, IRStmt_WrTmp(tmp, expr));

	return IRExpr_RdTmp(tmp);
}
static IRExpr* assignNew_HWord(IRSB* sb_out, IRExpr* expr)
{
	IRTemp tmp = newIRTemp(sb_out->tyenv, Ity_I32), tmp1;

	switch (typeOfIRExpr(sb_out->tyenv, expr))
	{
		case Ity_I1:
			addStmtToIRSB(sb_out, IRStmt_WrTmp(tmp, IRExpr_Unop(Iop_1Uto32, expr)));
			break;
		case Ity_I8:
			addStmtToIRSB(sb_out, IRStmt_WrTmp(tmp, IRExpr_Unop(Iop_8Uto32, expr)));
			break;
		case Ity_I16:
			addStmtToIRSB(sb_out, IRStmt_WrTmp(tmp, IRExpr_Unop(Iop_16Uto32, expr)));
			break;
		case Ity_I32:
			addStmtToIRSB(sb_out, IRStmt_WrTmp(tmp, expr));
			break;
		case Ity_I64:
			tmp1 = newIRTemp(sb_out->tyenv, Ity_I64);
			addStmtToIRSB(sb_out, IRStmt_WrTmp(tmp1, expr));
			addStmtToIRSB(sb_out, IRStmt_WrTmp(tmp, IRExpr_Unop(Iop_64to32, IRExpr_RdTmp(tmp1))));
			break;
			/*
			 * case Ity_F32:
			 addStmtToIRSB(sb_out, IRStmt_WrTmp(tmp, IRExpr_Unop(Iop_F32toI32U, expr)));
			 break;
			 * case Ity_F64:
			 addStmtToIRSB(sb_out, IRStmt_WrTmp(tmp, IRExpr_Unop(Iop_F64toI32U, expr)));
			 break;*/
		default:
			/*VG_(printf)("Unknown: ");
				ppIRExpr(expr);
				ppIRType(typeOfIRExpr(sb_out->tyenv, expr));
				VG_(printf)("\n");*/
			return mkIRExpr_HWord(0xffffffff);
			tl_assert(0);
			//VG_(tool_panic)("assignNew_HWord");
	}

	return IRExpr_RdTmp(tmp);
}

static IRExpr* assignNew_ULong(IRSB* sb_out, IRExpr* expr)
{
	IRTemp tmp = newIRTemp(sb_out->tyenv, Ity_I64);

	switch (typeOfIRExpr(sb_out->tyenv, expr))
	{
		case Ity_I1:
			addStmtToIRSB(sb_out, IRStmt_WrTmp(tmp, IRExpr_Unop(Iop_1Uto64, expr)));
			break;
		case Ity_I8:
			addStmtToIRSB(sb_out, IRStmt_WrTmp(tmp, IRExpr_Unop(Iop_8Uto64, expr)));
			break;
		case Ity_I16:
			addStmtToIRSB(sb_out, IRStmt_WrTmp(tmp, IRExpr_Unop(Iop_16Uto64, expr)));
			break;
		case Ity_I32:
			addStmtToIRSB(sb_out, IRStmt_WrTmp(tmp, IRExpr_Unop(Iop_32Uto64, expr)));
			break;
		case Ity_I64:
			addStmtToIRSB(sb_out, IRStmt_WrTmp(tmp, expr));
			break;
		default:
			ppIRExpr(expr);
			ppIRType(typeOfIRExpr(sb_out->tyenv, expr));
			tl_assert(0);
			//VG_(tool_panic)("assignNew_HWord");
	}

	return IRExpr_RdTmp(tmp);
}

static VG_REGPARM(4) void helper_instrument_Put(UInt offset, IRTemp data, Int value, UInt size)
{
	ThreadId tid = VG_(get_running_tid)();
	if (is_trace_irst != tid)
		return;
	if(data == IRTemp_INVALID) {
#ifdef FZ_LOG_IR
		ST_LOGI("0x%04x 0x%04x PUT(%d) <- 0x%x:I%d\n", Ist_Put, 0x1, offset, value, size);
#endif
	} else {
#ifdef FZ_LOG_IR
		ST_LOGI("0x%04x 0x%04x PUT(%d) <- t%d:I%d | (0x%x)\n", Ist_Put, 0x2, offset, data, size, value);
#endif
	}
	return;
}

static VG_REGPARM(4) void helper_instrument_PutI(UInt base, UInt ix, UInt bias, UInt nElems)
{
	ThreadId tid = VG_(get_running_tid)();
	if (is_trace_irst != tid)
		return;

	UInt index = base+((ix+bias)%nElems);
#ifdef FZ_LOG_IR
	ST_LOGI("0x%04x 0x%04x PutI()[%d:%d]\n", Ist_PutI, 0x0, ix, bias);
#endif
}

static VG_REGPARM(4) void helper_instrument_WrTmp_Get(IRTemp tmp, UInt offset, UInt value, UInt size)
{
	ThreadId tid = VG_(get_running_tid)();
	if (is_trace_irst != tid)
		return;
#ifdef FZ_LOG_IR
	ST_LOGI("0x%04x 0x%04x t%d <- GET:I%d(%u) | 0x%x\n", Ist_WrTmp, Iex_Get, tmp, size, offset, value);
#endif
	return;
}

static VG_REGPARM(4) void helper_instrument_WrTmp_GetI(UInt base, UInt ix, UInt bias, UInt nElems)
{
	ThreadId tid = VG_(get_running_tid)();
	if (is_trace_irst != tid)
		return;
	UInt index = base+((ix+bias)%nElems);
#ifdef FZ_LOG_IR
	ST_LOGI("0x%04x 0x%04x GetI()[%d:%d]\n", Ist_WrTmp, Iex_GetI, ix, bias);
#endif
}

static VG_REGPARM(4) void helper_instrument_WrTmp_RdTmp(IRTemp tmp_lhs, IRTemp tmp_rhs, UInt value, UInt size)
{
	ThreadId tid = VG_(get_running_tid)();
	if (is_trace_irst != tid)
		return;

#ifdef FZ_LOG_IR
	ST_LOGI("0x%04x 0x%04x t%d <- t%d:I%d | 0x%x\n", Ist_WrTmp, Iex_RdTmp, tmp_lhs, tmp_rhs, size, value);
#endif
	return;
}

static VG_REGPARM(4) void helper_instrument_WrTmp_Triop_SetElem(IRStmt *clone, UInt size, UInt arg1_value, UInt arg3_value)
{
	ThreadId tid = VG_(get_running_tid)();
	if (is_trace_irst != tid)
		return;

	IRExpr *e1 = NULL, *e2 = NULL, *e3 = NULL;
	IROp	 op		= clone->Ist.WrTmp.data->Iex.Triop.details->op;
	e1 = clone->Ist.WrTmp.data->Iex.Triop.details->arg1;
	e2 = clone->Ist.WrTmp.data->Iex.Triop.details->arg2;
	e3 = clone->Ist.WrTmp.data->Iex.Triop.details->arg3;
	IRTemp tmp  = clone->Ist.WrTmp.tmp;
	IRTemp arg1 = (e1->tag == Iex_RdTmp) ? e1->Iex.RdTmp.tmp : IRTemp_INVALID;
	Int    arg2_value = valueOfConst(e2);
	IRTemp arg3 = (e3->tag == Iex_RdTmp) ? e3->Iex.RdTmp.tmp : IRTemp_INVALID;
	Int size0 = size & 0xff, size1 = (size >> 8) & 0xff, size2 = (size >> 16) & 0xff, size3 = (size >> 24) & 0xff;
	char str[32] = {0};
	IROp_to_str(op, str);
#ifdef FZ_LOG_IR
	ST_LOGI("0x%04x 0x%04x t%d <- %s(t%d, 0x%x:I8, t%d) | Triop_SetElem(0x%x, 0x%x, 0x%x)\n", Ist_WrTmp, op,
			tmp, str, arg1, arg2_value, arg3, arg1_value, arg2_value, arg3_value);
#endif
	return;
}

static VG_REGPARM(4) void helper_instrument_WrTmp_Binop(IRStmt *clone, UInt size, UInt arg1_value, UInt arg2_value)
{
	ThreadId tid = VG_(get_running_tid)();
	if (is_trace_irst != tid)
		return;

	IRExpr *e1 = NULL, *e2 = NULL;
	char str[32] = {0};

	tl_assert(clone);

	e1 = clone->Ist.WrTmp.data->Iex.Binop.arg1;
	e2 = clone->Ist.WrTmp.data->Iex.Binop.arg2;
	IROp	 op		= clone->Ist.WrTmp.data->Iex.Binop.op;
	IRTemp tmp  = clone->Ist.WrTmp.tmp;
	IRTemp arg1 = (e1->tag == Iex_RdTmp) ? e1->Iex.RdTmp.tmp : IRTemp_INVALID;
	IRTemp arg2 = (e2->tag == Iex_RdTmp) ? e2->Iex.RdTmp.tmp : IRTemp_INVALID;
	Int size0 = size & 0xff, size1 = (size >> 8) & 0xff, size2 = (size >> 16) & 0xff;

	IROp_to_str(op, str);
#ifdef FZ_LOG_IR
	ST_LOGI("0x%04x 0x%04x t%d <- %s(t%d, t%d) | Binop(0x%x, 0x%x)\n", Ist_WrTmp, op,
			tmp, str, arg1, arg2, arg1_value, arg2_value);
#endif
	return;
}

static VG_REGPARM(3) void helper_instrument_WrTmp_Unop(IRStmt *clone, UInt value, UInt size)
{
	ThreadId tid = VG_(get_running_tid)();
	if (is_trace_irst != tid)
		return;

	IRTemp   dst = clone->Ist.WrTmp.tmp;
	IRExpr* data = clone->Ist.WrTmp.data;
	IROp op = data->Iex.Unop.op;
	IRExpr*  tmp = data->Iex.Unop.arg;
	IRTemp   arg = (tmp->tag == Iex_RdTmp) ? tmp->Iex.RdTmp.tmp : IRTemp_INVALID;
	char str[32] = {0};
	IROp_to_str(op, str);
#ifdef FZ_LOG_IR
	ST_LOGI("0x%04x 0x%04x t%d = %s(t%d) | Unop(0x%x)\n", Ist_WrTmp, op,
			dst, str, arg, value);
#endif
	return;
}

static VG_REGPARM(4) void helper_instrument_WrTmp_Load(IRStmt *clone, UInt addr_value, UInt size, UInt load_value)
{
	ThreadId tid = VG_(get_running_tid)();
	if (is_trace_irst != tid)
		return;

	IRTemp  dst  = clone->Ist.WrTmp.tmp;
	IRExpr* data = clone->Ist.WrTmp.data;
	IRExpr* tmp  = data->Iex.Load.addr;
	IRTemp  addr = (tmp->tag == Iex_RdTmp) ? tmp->Iex.RdTmp.tmp : IRTemp_INVALID;

	UInt pc = VG_(get_IP)(tid);
	HChar* addrInfo = NULL;
#ifdef FZ_LOG_IR
	addrInfo = VG_(describe_IP) ( addr_value, NULL );
	ST_LOGI("0x%04x 0x%04x t%d:I%d = LD(t%d) | 0x%x <- LD(0x%08x) | %s\n", Ist_WrTmp, Iex_Load,
			dst, size, addr, load_value, addr_value, addrInfo);
#endif
}

static VG_REGPARM(2) void helper_instrument_WrTmp_Const(IRTemp tmp, UInt value)
{
	ThreadId tid = VG_(get_running_tid)();
	if (is_trace_irst != tid)
		return;
#ifdef FZ_LOG_IR
	ST_LOGI("0x%04x 0x%04x t%d = Const(%d)", Ist_WrTmp, Iex_Const, tmp, value);
#endif
	return;
}

static VG_REGPARM(4) void helper_instrument_WrTmp_CCall_armg_calculate_condition(IRStmt* clone, UInt cc_arg1_value, UInt cc_arg2_value, UInt cc_n_op_value)
{
	ThreadId tid = VG_(get_running_tid)();
	if (is_trace_irst != tid)
		return;

	IRExpr** args = clone->Ist.WrTmp.data->Iex.CCall.args;

	Int cond = cc_n_op_value >> 4;
	Int cc_op = cc_n_op_value & 0xF;

	IRTemp tmp = clone->Ist.WrTmp.tmp;
	IRTemp cc_n_op = (args[0]->tag == Iex_RdTmp) ? args[0]->Iex.RdTmp.tmp : IRTemp_INVALID;
	IRTemp cc_arg1 = (args[1]->tag == Iex_RdTmp) ? args[1]->Iex.RdTmp.tmp : IRTemp_INVALID;
	IRTemp cc_arg2 = (args[2]->tag == Iex_RdTmp) ? args[2]->Iex.RdTmp.tmp : IRTemp_INVALID;
	IRTemp cc_arg3 = (args[3]->tag == Iex_RdTmp) ? args[3]->Iex.RdTmp.tmp : IRTemp_INVALID;

#ifdef FZ_LOG_IR
	ST_LOGI("0x%04x 0x%04x t%d <- armg_calculate_condition(t%d, t%d, t%d, t%d) | (%d, %d, %d, 0)\n", Ist_WrTmp, Iex_CCall,
			tmp, cc_n_op, cc_arg1, cc_arg2, cc_arg3, cc_n_op_value, cc_arg1_value, cc_arg2_value);
#endif
	return;
}

static VG_REGPARM(0) void helper_instrument_WrTmp_CCall_else()
{
	ThreadId tid = VG_(get_running_tid)();
	if (is_trace_irst != tid)
		return;
#ifdef FZ_LOG_IR
	ST_LOGI("0x%04x 0x%04x helper_instrument_WrTmp_CCall_else()\n", Ist_WrTmp, Iex_CCall);
#endif
}

static VG_REGPARM(3) void helper_instrument_WrTmp_ITE(IRStmt *clone, UInt cond_value, UInt size)
{
	ThreadId tid = VG_(get_running_tid)();
	if (is_trace_irst != tid)
		return;
	IRTemp	tmp		= clone->Ist.WrTmp.tmp;
	IRExpr* data	= clone->Ist.WrTmp.data;
	IRExpr* econd  = data->Iex.ITE.cond;
	IRExpr* eexpr0	= data->Iex.ITE.iftrue;
	IRExpr* eexprX	= data->Iex.ITE.iffalse;
	IRTemp  cond    = (econd->tag == Iex_RdTmp) ? econd->Iex.RdTmp.tmp : IRTemp_INVALID;
	IRTemp  expr0   = (eexpr0->tag == Iex_RdTmp) ? eexpr0->Iex.RdTmp.tmp : IRTemp_INVALID;
	IRTemp  exprX   = (eexprX->tag == Iex_RdTmp) ? eexprX->Iex.RdTmp.tmp : IRTemp_INVALID;
#ifdef FZ_LOG_IR
	ST_LOGI("0x%04x 0x%04x t%d = ITE(t%d, t%d, t%d) | %c\n", Ist_WrTmp, Iex_ITE,
			tmp, cond, expr0, exprX, cond_value == 0 ? 'F' : 'T' );
#endif
	return;
}

#if 0
typedef
struct {
	IREndness end;    /* Endianness of the load */
	IRLoadGOp cvt;    /* Conversion to apply to the loaded value */
	IRTemp    dst;    /* Destination (LHS) of assignment */
	IRExpr*   addr;   /* Address being loaded from */
	IRExpr*   alt;    /* Value if load is not done. */
	IRExpr*   guard;  /* Guarding value */
} IRLoadG;
t<tmp> = if (<guard>) <cvt>(LD<end>(<addr>)) else <alt>
#endif

//static VG_REGPARM(0) void helper_instrument_LoadG(IRTemp tmp, UInt addr_value, UInt size)
static VG_REGPARM(4) void helper_instrument_LoadG(IRStmt *clone, UInt addr_value, UInt load_value, UInt guard_value)
{
	ThreadId tid = VG_(get_running_tid)();
	if (is_trace_irst != tid)
		return;

	UInt pc = VG_(get_IP)(tid);
	HChar *pcInfo = NULL, *addrInfo = NULL;
	IRLoadG* lg		= clone->Ist.LoadG.details;
	UInt size = 0;
	switch (lg->cvt) {
		case ILGop_Ident32: size = 32; break;
		case ILGop_16Uto32: size = 16; break;
		case ILGop_16Sto32: size = 16; break;
		case ILGop_8Uto32:  size = 8; break;
		case ILGop_8Sto32:  size = 8; break;
		default: VG_(tool_panic)("instrument_LoadG()");
	}
	IRTemp alt    = lg->alt->tag == Iex_RdTmp ? lg->alt->Iex.RdTmp.tmp : IRTemp_INVALID;
	IRTemp addr   = lg->addr->tag == Iex_RdTmp ? lg->addr->Iex.RdTmp.tmp : IRTemp_INVALID;;
	IRTemp dst		= lg->dst;
	if(guard_value != 0)  {
#ifdef FZ_LOG_IR
		addrInfo = VG_(describe_IP) ( addr_value, NULL );
		ST_LOGI("0x%04x 0x%04x t%d <- <cvt>LD(t%d) | 0x%08x <- LD(0x%08x) | %s\n", Ist_LoadG, guard_value,
				dst, addr, load_value, addr_value, pcInfo);
#endif
	}	else {
#ifdef FZ_LOG_IR
		ST_LOGI("0x%04x 0x%04x t%d = <alt>t%d | 0x%08x\n", Ist_LoadG, guard_value, dst, alt, load_value);
#endif
	}
	return;
}

static VG_REGPARM(4) void helper_instrument_Store(IRStmt *clone, UInt addr_value, UInt data_value, UInt size)
{
	ThreadId tid = VG_(get_running_tid)();
	HChar *srcInfo = NULL, *pcInfo = NULL, *addrInfo = NULL;
	UInt pc = VG_(get_IP)(tid);
	if( do_is_start == False || tid != 1) {
		return;
	}
#ifdef DBG_MOD_IR
	if( (isMonMap(addr_value, &addrInfo) > 0) && (isMonMap(pc, &pcInfo) > 0) ) {
		VG_(printf)("[MODI2] ST(0x%08x) <- 0x%x | %s | %s\n", addr_value, data_value, addrInfo, pcInfo);
	}
	if( pMDexFileObj ) {
		if( (addr_value >= pMDexFileObj->begin_) && (addr_value < pMDexFileObj->begin_ + pMDexFileObj->size_)) {
			addrInfo = VG_(describe_IP) ( addr_value, NULL );
			VG_(printf)("[MODI1] ST(0x%08x) <- 0x%x | %s | ", addr_value, data_value, addrInfo);
			pcInfo = VG_(describe_IP) ( pc, NULL );
			VG_(printf)("%s\n", pcInfo);
		}
	}
#endif
	if (is_trace_irst != tid)
		return;
	IRExpr* tmp1 = clone->Ist.Store.addr;
	IRExpr* tmp2 = clone->Ist.Store.data;
	IRTemp  addr = tmp1->tag == Iex_RdTmp ? tmp1->Iex.RdTmp.tmp : IRTemp_INVALID;
	IRTemp  data = tmp2->tag == Iex_RdTmp ? tmp2->Iex.RdTmp.tmp : IRTemp_INVALID;
#ifdef FZ_LOG_IR
	addrInfo = VG_(describe_IP) ( addr_value, NULL );
	ST_LOGI("0x%04x 0x%04x ST(t%d) = t%d:I%d | ST(0x%08x) <- 0x%x | %s\n", Ist_Store, 0x0,
			addr, data, size, addr_value, data_value, addrInfo);
#endif
	return;
}

//static VG_REGPARM(0) void helper_instrument_StoreG(UInt addr, IRTemp data, UInt size, UInt guard)
static VG_REGPARM(4) void helper_instrument_StoreG(UInt addr_value, UInt data, UInt size, UInt guard_value)
{
	// if (<guard>) ST<end>(<addr>) = <data>
	ThreadId tid = VG_(get_running_tid)();
	HChar *addrInfo = NULL, *pcInfo = NULL; 
	UInt pc = VG_(get_IP)(tid);
	if( do_is_start == False || tid != 1) {
		return;
	}
#ifdef DBG_MOD_IR
	if( (isMonMap(addr_value, &addrInfo) > 0) && (isMonMap(pc, &pcInfo) > 0)) {
		VG_(printf)("[MODI2] ST(0x%08x) <? 0x%x:I%d | %s | %s\n", addr_value, data, size, addrInfo, pcInfo);
	}
	if( pMDexFileObj ) {
		if( (addr_value >= pMDexFileObj->begin_) && (addr_value < pMDexFileObj->begin_ + pMDexFileObj->size_)) {
			addrInfo = VG_(describe_IP) ( addr_value, NULL );
			VG_(printf)("[MODI1] ST(0x%08x) <? 0x%x:I%d | %s | \n", addr_value, data, size, addrInfo);
			pcInfo = VG_(describe_IP) ( pc, NULL );
			VG_(printf)("%s\n", pcInfo);
		}
	}
#endif
	if (is_trace_irst != tid || guard_value == 0) {
		return;
	}

#ifdef FZ_LOG_IR
	addrInfo = VG_(describe_IP) ( addr_value, NULL );
	ST_LOGI("0x%04x 0x%04x ST(0x%08x) <? 0x%x:I%d | %s\n", Ist_StoreG, 0x0, addr_value, data, size, addrInfo);
#endif
}

static VG_REGPARM(4) void helper_instrument_CAS_single_element(UInt addr, IRTemp dataLo, UInt size, UInt cas_succeeded)
{
	ThreadId tid = VG_(get_running_tid)();
	if (is_trace_irst != tid)
		return;
#ifdef FZ_LOG_IR
	ST_LOGI("0x%04x 0x%04x 0x%08x:I%d <- CASle(t%d) | cas_succeeded=%d\n", Ist_CAS, 0x1,
			addr, size, dataLo, cas_succeeded);
#endif
	return;
}

static VG_REGPARM(4) void helper_instrument_CAS_double_element(IRStmt* clone, UInt addr, UInt size, UInt cas_succeeded)
{
	ThreadId tid = VG_(get_running_tid)();
	if (is_trace_irst != tid)
		return;
	char dep[DEP_MAX_LEN] = {0};
	char *tmp_rhs = NULL;
	IRCAS*  cas = clone->Ist.CAS.details;
	IRTemp  dataLo = (cas->expdLo->tag == Iex_RdTmp) ? cas->expdLo->Iex.RdTmp.tmp : IRTemp_INVALID;
	IRTemp  dataHi = (cas->expdHi->tag == Iex_RdTmp) ? cas->expdHi->Iex.RdTmp.tmp : IRTemp_INVALID;
#ifdef FZ_LOG_IR
	ST_LOGI("0x%04x 0x%04x 0x%08x:I%d <- CASle(t%d, t%d) | cas_succeeded=%d\n", Ist_CAS, 0x2,
			addr+size, size, dataHi, dataLo, cas_succeeded);
#endif
	return;
}

//static VG_REGPARM(4) void helper_instrument_LLSC_Load_Linked(IRTemp result, UInt addr, UInt size, UInt load_value)
static VG_REGPARM(4) void helper_instrument_LLSC_Load_Linked(IRTemp result, UInt addr, UInt size)
{
	ThreadId tid = VG_(get_running_tid)();
	if (is_trace_irst != tid)
		return;
#ifdef FZ_LOG_IR
	ST_LOGI("0x%04x 0x%04x t%d <- LDle-Linked(0x%08x:I%d)\n", Ist_LLSC,  0x1,
			result, addr, size);
#endif
	return;
}

static VG_REGPARM(4) void helper_instrument_LLSC_Store_Conditional(UInt addr, IRTemp storedata, UInt size, UInt store_succeeded)
{
	ThreadId tid = VG_(get_running_tid)();
	if (is_trace_irst != tid)
		return;

#ifdef FZ_LOG_IR
	ST_LOGI("0x%04x 0x%04x 0x%08x:I%d <- STle-Cond(t%d) | (%c)\n", Ist_LLSC, 0x2,
			addr, size, storedata, store_succeeded == 0 ? 'F' : 'T');
#endif
	return;
}

static ULong bn = 0;
static void parse_jump_insn(ThreadId tid, UInt guard_value, Addr src, Addr dst, Int type) 
{
	//if (guard_value == 0 || is_trace_irst == 0)
	if (guard_value == 0 || start_trace_irst == 0) {
		return;
	}
	HChar *srcInfo = NULL; //VG_(describe_IP) ( src, NULL );
	HChar *dstInfo = NULL; //VG_(describe_IP) ( src, NULL );
	UWord r0 = 0, r1 = 0, r2 = 0, r3 = 0, sp = 0;
	ThreadState *tst	= VG_(get_ThreadState) ( tid );
	VexGuestArchState	*arch_state = &tst->arch.vex;
	HChar tmp[255];
	Addr src_map = 0;
	Addr dst_map = 0;
	UInt size = 0;
#if defined(VGPV_arm_linux_android)
	r0 = arch_state->guest_R0;
	r1 = arch_state->guest_R1;
	r2 = arch_state->guest_R2;
	r3 = arch_state->guest_R3;
	sp = arch_state->guest_R13;
#endif
	if( is_trace_irst == is_in_vm) {
		if( (isMonMap(src, &srcInfo) > 0) && (isMonMap(dst,&dstInfo) == 0)) {
			dstInfo = VG_(describe_IP) ( dst, NULL );
			VG_(printf)("[I] %d Jump from 0x%08x(%s)@%llu to 0x%08x(%s) 0x%08x 0x%08x 0x%08x 0x%08x 0x%08x\n", 
					tid, src, srcInfo, bn, dst, dstInfo, r0, r1, r2, r3, sp);
			is_trace_irst = 0;
		} else {
			VG_(printf)("[S] %d Jump from 0x%08x(%s)@%llu to 0x%08x(%s) 0x%08x 0x%08x 0x%08x 0x%08x 0x%08x\n", 
					tid, src, srcInfo, bn, dst, dstInfo, r0, r1, r2, r3, sp);
		}
		bn++;
	} else if(is_trace_irst == 0) {
		src_map = isMonMap(src, &srcInfo);
		dst_map = isMonMap(dst, &dstInfo);
		if( src_map == 0 && dst_map > 0 ) {
			srcInfo = VG_(describe_IP) ( src, NULL );
			VG_(printf)("[R] %d Jump from 0x%08x(%s) to 0x%08x(%s) 0x%08x 0x%08x 0x%08x 0x%08x 0x%08x\n", 
					tid, src, srcInfo,  dst, dstInfo, r0, r1, r2, r3, sp);
			is_trace_irst = is_in_vm;
			bn = 0;

			dumpMemMap(dst_map);
		} /*else if (is_in_vm > 0) {
				srcInfo = VG_(describe_IP) ( src, NULL );
				VG_(strcpy)(tmp, srcInfo);
				dstInfo = VG_(describe_IP) ( dst, NULL );
				VG_(printf)("[R] %d Jump from 0x%08x(%s) to 0x%08x(%s) 0x%08x 0x%08x 0x%08x 0x%08x 0x%08x\n", 
				tid, src, tmp,  dst, dstInfo, r0, r1, r2, r3, sp);
				}*/
	}
}
//static VG_REGPARM(0) void helper_instrument_Exit(UInt branch_is_taken, UInt offsIP, UInt size, IRtemp guard)
static VG_REGPARM(4) void helper_instrument_Exit(UInt guard_value, Addr src, Addr dst, IRTemp guard)
{
	ThreadId tid			= VG_(get_running_tid)();
	if(is_in_vm == tid) {
#ifdef FZ_LOG_IR
		if (is_trace_irst == tid) {
			ST_LOGI("0x%04x 0x%04x if(t%d) goto 0x%08x | (%d)\n", Ist_Exit, 0,
					guard, dst, guard_value);
		}
#endif
		parse_jump_insn(tid, guard_value, src, dst, 0);
	}
}

static VG_REGPARM(3) void helper_instrument_Next(Addr src, Addr dst, IRTemp nxt)
{
	ThreadId tid			= VG_(get_running_tid)();
	if(is_in_vm == tid) {
#ifdef FZ_LOG_IR
		if (is_trace_irst == tid) {
			if(nxt != IRTemp_INVALID)
				ST_LOGI("0x%04x 0x%04x goto t%d | 0x%08x\n", 0x1eff, 0x1,	nxt, dst);
			else
				ST_LOGI("0x%04x 0x%04x goto 0x%08x\n", 0x1eff, 0x2, dst);
		}
#endif
		parse_jump_insn(tid, 1, src, dst, 1);
	}
}

//
//  VEX INSTRUMENTATION FUNCTIONS
//
static void instrument_Put(IRStmt* st, IRSB* sb_out)
{
	Int offset = st->Ist.Put.offset;
	IRExpr* data = st->Ist.Put.data;
	Int size = sizeofIRType_bits(typeOfIRExpr(sb_out->tyenv, data));
	IRDirty* di;
	UInt data_value = -1;

	tl_assert(isIRAtom(data));
	// the data transfer type is the type of data
#if 0
	if (data->tag == Iex_Const)
	{
		switch (data->Iex.Const.con->tag)
		{
			case Ico_U1:  data_value = data->Iex.Const.con->Ico.U1; break;
			case Ico_U8:  data_value = data->Iex.Const.con->Ico.U8; break;
			case Ico_U16: data_value = data->Iex.Const.con->Ico.U16; break;
			case Ico_V128:data_value = data->Iex.Const.con->Ico.V128; break;
			case Ico_U32: data_value = data->Iex.Const.con->Ico.U32; break;
			case Ico_F32i:data_value = data->Iex.Const.con->Ico.F32i; break;
			case Ico_V256:data_value = data->Iex.Const.con->Ico.V256; break;
			case Ico_U64: data_value = data->Iex.Const.con->Ico.U64; break;
			case Ico_F64i:data_value = data->Iex.Const.con->Ico.F64i; break;
			default: ppIRStmt(st); tl_assert(0);
		}
	}
#endif
	di = unsafeIRDirty_0_N(0,
			"helper_instrument_Put",
			VG_(fnptr_to_fnentry)(helper_instrument_Put),
			mkIRExprVec_4(mkIRExpr_HWord(offset),
				mkIRExpr_HWord((data->tag == Iex_RdTmp) ? data->Iex.RdTmp.tmp : IRTemp_INVALID),
				(data->tag == Iex_RdTmp) ? assignNew_HWord(sb_out, data) : mkIRExpr_HWord(valueOfConst(data)),
				mkIRExpr_HWord(size))
			);
	addStmtToIRSB(sb_out, IRStmt_Dirty(di));
}
/*
	 The PutI statement is used to write guest registers which identity is not known until run time,
	 i.e. not the registers we are shadowing (in principle), no harm in verifying though.
	 */
static void instrument_PutI(IRStmt* st, IRSB* sb_out)
{
	IRPutI* details = st->Ist.PutI.details;
	IRRegArray* descr = details->descr;
	Int base = descr->base;
	Int nElems = descr->nElems;
	IRExpr* ix = details->ix;
	Int bias = details->bias;
	IRDirty* di;

	tl_assert(ix->tag == Iex_RdTmp);

	di = unsafeIRDirty_0_N(0,
			"helper_instrument_PutI",
			VG_(fnptr_to_fnentry)(helper_instrument_PutI),
			mkIRExprVec_4(mkIRExpr_HWord(base),
				assignNew_HWord(sb_out, ix),
				mkIRExpr_HWord(bias),
				mkIRExpr_HWord(nElems))
			);
	addStmtToIRSB(sb_out, IRStmt_Dirty(di));
}
static void instrument_WrTmp_Get(IRStmt* st, IRSB* sb_out)
{
	IRTemp tmp = st->Ist.WrTmp.tmp;
	IRExpr* data = st->Ist.WrTmp.data;
	Int offset = data->Iex.Get.offset;
	Int size = sizeofIRType_bits(data->Iex.Get.ty);
	IRDirty* di;

	tl_assert(typeOfIRTemp(sb_out->tyenv, tmp) == data->Iex.Get.ty);

	di = unsafeIRDirty_0_N(0,
			"helper_instrument_WrTmp_Get",
			VG_(fnptr_to_fnentry)(helper_instrument_WrTmp_Get),
			mkIRExprVec_4(mkIRExpr_HWord(tmp),
				mkIRExpr_HWord(offset),
				assignNew_HWord(sb_out, data),
				mkIRExpr_HWord(size))
			);
	addStmtToIRSB(sb_out, IRStmt_Dirty(di));
}
/*
	 The GetI expression is used to read guest registers which identity is not known until run time,
	 i.e. not the registers we are shadowing (in principle), no harm in verifying though.
	 */
static void instrument_WrTmp_GetI(IRStmt* st, IRSB* sb_out)
{
	IRExpr* data = st->Ist.WrTmp.data;
	IRRegArray* descr = data->Iex.GetI.descr;
	Int base = descr->base;
	Int nElems = descr->nElems;
	IRExpr* ix = data->Iex.GetI.ix;
	Int bias = data->Iex.GetI.bias;
	IRDirty* di;

	tl_assert(ix->tag == Iex_RdTmp);

	di = unsafeIRDirty_0_N(0,
			"helper_instrument_WrTmp_GetI",
			VG_(fnptr_to_fnentry)(helper_instrument_WrTmp_GetI),
			mkIRExprVec_4(mkIRExpr_HWord(base),
				assignNew_HWord(sb_out, ix),
				mkIRExpr_HWord(bias),
				mkIRExpr_HWord(nElems))
			);
	addStmtToIRSB(sb_out, IRStmt_Dirty(di));
}

static void instrument_WrTmp_RdTmp(IRStmt* st, IRSB* sb_out)
{
	IRTemp tmp_lhs = st->Ist.WrTmp.tmp;
	IRExpr* data = st->Ist.WrTmp.data;
	IRTemp tmp_rhs = data->Iex.RdTmp.tmp;
	Int size = sizeofIRType_bits(typeOfIRTemp(sb_out->tyenv, tmp_rhs));
	IRDirty* di;

	tl_assert(typeOfIRTemp(sb_out->tyenv, tmp_lhs) == typeOfIRTemp(sb_out->tyenv, tmp_rhs));

	di = unsafeIRDirty_0_N(0,
			"helper_instrument_WrTmp_RdTmp",
			VG_(fnptr_to_fnentry)(helper_instrument_WrTmp_RdTmp),
			mkIRExprVec_4(mkIRExpr_HWord(tmp_lhs),
				mkIRExpr_HWord(tmp_rhs),
				assignNew_HWord(sb_out, data),
				mkIRExpr_HWord(size))
			);
	addStmtToIRSB(sb_out, IRStmt_Dirty(di));
}

static void instrument_WrTmp_Triop_SetElem(IRStmt* st, IRSB* sb_out)
{
	IRTriop *triop = st->Ist.WrTmp.data->Iex.Triop.details;
	IRExpr* arg1 = triop->arg1;
	IRExpr* arg2 = triop->arg2;
	IRExpr* arg3 = triop->arg3;
	Int size = sizeofIRType_bits(typeOfIRExpr(sb_out->tyenv, st->Ist.WrTmp.data));
	Int size1 = sizeofIRType_bits(typeOfIRExpr(sb_out->tyenv, arg1));
	Int size2 = sizeofIRType_bits(typeOfIRExpr(sb_out->tyenv, arg2));
	Int size3 = sizeofIRType_bits(typeOfIRExpr(sb_out->tyenv, arg3));

	IRStmt* stclone = deepMallocIRStmt(st);
	IRDirty* di = unsafeIRDirty_0_N(0,
			"helper_instrument_WrTmp_Triop_SetElem",
			VG_(fnptr_to_fnentry)(helper_instrument_WrTmp_Triop_SetElem),
			mkIRExprVec_4(mkIRExpr_HWord((HWord)stclone),
				mkIRExpr_HWord(size | (size1 << 8) | (size2 << 16) | (size3 << 24)),
				(arg1->tag == Iex_RdTmp) ? assignNew_HWord(sb_out, arg1) : mkIRExpr_HWord(valueOfConst(arg1)),
				(arg3->tag == Iex_RdTmp) ? assignNew_HWord(sb_out, arg3) : mkIRExpr_HWord(valueOfConst(arg3)))
			);
	addStmtToIRSB(sb_out, IRStmt_Dirty(di));

}

static void instrument_WrTmp_Triop(IRStmt* st, IRSB* sb_out)
{
	IRTriop *triop = st->Ist.WrTmp.data->Iex.Triop.details;
	switch(triop->op) {
		case Iop_Slice64:
			break;
		case Iop_SetElem8x8:
		case Iop_SetElem16x4:
		case Iop_SetElem32x2:
			instrument_WrTmp_Triop_SetElem(st, sb_out);
			break;
		default:
			break;
	}
}

static void instrument_WrTmp_Binop(IRStmt* st, IRSB* sb_out)
{
	IRTemp tmp = st->Ist.WrTmp.tmp;
	IRExpr* data = st->Ist.WrTmp.data;
	IROp op = data->Iex.Binop.op;
	IRExpr* arg1 = data->Iex.Binop.arg1;
	IRExpr* arg2 = data->Iex.Binop.arg2;
	UInt arg1_value = 0, arg2_value = 0;
	IRExpr* expr = IRExpr_Binop(op, arg1, arg2);
	Int size = sizeofIRType_bits(typeOfIRExpr(sb_out->tyenv, expr));
	Int size1 = sizeofIRType_bits(typeOfIRExpr(sb_out->tyenv, arg1));
	Int size2 = sizeofIRType_bits(typeOfIRExpr(sb_out->tyenv, arg2));
	IRDirty* di;

	// we don't care about floating point and SIMD operations
	//if (op > Iop_AddF64)
	//	return;

	tl_assert(isIRAtom(arg1));
	tl_assert(isIRAtom(arg2));
	tl_assert(typeOfIRTemp(sb_out->tyenv, tmp) == typeOfIRExpr(sb_out->tyenv, expr));

	if (arg1->tag == Iex_Const)
	{
		switch (arg1->Iex.Const.con->tag)
		{
			case Ico_U1: arg1_value = arg1->Iex.Const.con->Ico.U1; break;
			case Ico_U8: arg1_value = arg1->Iex.Const.con->Ico.U8; break;
			case Ico_U16: arg1_value = arg1->Iex.Const.con->Ico.U16; break;
			case Ico_V128: arg1_value = arg1->Iex.Const.con->Ico.V128; break;
			case Ico_U32:  arg1_value = arg1->Iex.Const.con->Ico.U32; break;
			case Ico_V256: arg1_value = arg1->Iex.Const.con->Ico.V256; break;
			case Ico_U64:  arg1_value = arg1->Iex.Const.con->Ico.U64; break;
			default: ppIRStmt(st); tl_assert(0); VG_(tool_panic)("instrument_WrTmp_Binop");
		}
	}
	if (arg2->tag == Iex_Const)
	{
		switch (arg2->Iex.Const.con->tag)
		{
			case Ico_U1: arg2_value = arg2->Iex.Const.con->Ico.U1; break;
			case Ico_U8: arg2_value = arg2->Iex.Const.con->Ico.U8; break;
			case Ico_U16: arg2_value = arg2->Iex.Const.con->Ico.U16; break;
			case Ico_V128: arg2_value = arg2->Iex.Const.con->Ico.V128; break;
			case Ico_U32:  arg2_value = arg2->Iex.Const.con->Ico.U32; break;
			case Ico_V256: arg2_value = arg2->Iex.Const.con->Ico.V256; break;
			case Ico_U64:  arg2_value = arg2->Iex.Const.con->Ico.U64; break;
			default: ppIRStmt(st); tl_assert(0); VG_(tool_panic)("instrument_WrTmp_Binop");
		}
	}

	IRStmt* stclone = deepMallocIRStmt(st);
	di = unsafeIRDirty_0_N(0,
			"helper_instrument_WrTmp_Binop",
			VG_(fnptr_to_fnentry)(helper_instrument_WrTmp_Binop),
			mkIRExprVec_4(mkIRExpr_HWord((HWord)stclone),
				mkIRExpr_HWord(size | (size1 << 8) | (size2 << 16)),
				(arg1->tag == Iex_RdTmp) ? assignNew_HWord(sb_out, arg1) : mkIRExpr_HWord(arg1_value),
				(arg2->tag == Iex_RdTmp) ? assignNew_HWord(sb_out, arg2) : mkIRExpr_HWord(arg2_value))
			);
	addStmtToIRSB(sb_out, IRStmt_Dirty(di));
}

static void instrument_WrTmp_Unop(IRStmt* st, IRSB* sb_out)
{
	IRTemp tmp = st->Ist.WrTmp.tmp;
	IRExpr* data = st->Ist.WrTmp.data;
	IROp op = data->Iex.Unop.op;
	IRExpr* arg = data->Iex.Unop.arg;
	IRExpr* expr = IRExpr_Unop(op, arg);
	Int size = sizeofIRType_bits(typeOfIRExpr(sb_out->tyenv, expr));
	IRDirty* di;

	tl_assert(isIRAtom(arg));
	tl_assert(typeOfIRTemp(sb_out->tyenv, tmp) == typeOfIRExpr(sb_out->tyenv, expr));

	IRStmt* stclone = deepMallocIRStmt(st);
	di = unsafeIRDirty_0_N(0,
			"helper_instrument_WrTmp_Unop",
			VG_(fnptr_to_fnentry)(helper_instrument_WrTmp_Unop),
			mkIRExprVec_3(mkIRExpr_HWord((HWord)stclone),
				(arg->tag == Iex_RdTmp) ? assignNew_HWord(sb_out, arg) : mkIRExpr_HWord(valueOfConst(arg)),
				mkIRExpr_HWord(size))
			);
	addStmtToIRSB(sb_out, IRStmt_Dirty(di));
}

static void instrument_WrTmp_Load(IRStmt* st, IRSB* sb_out)
{
	IRTemp tmp = st->Ist.WrTmp.tmp;
	IRExpr* data = st->Ist.WrTmp.data;
	IRExpr* addr = data->Iex.Load.addr;
	Int size = sizeofIRType_bits(data->Iex.Load.ty);
	IRDirty* di;

	tl_assert(isIRAtom(addr));
	if (addr->tag == Iex_Const) tl_assert(addr->Iex.Const.con->tag == Ico_U32);
	tl_assert(typeOfIRTemp(sb_out->tyenv, tmp) == data->Iex.Load.ty);

	IRStmt* stclone = deepMallocIRStmt(st);
	di = unsafeIRDirty_0_N(0,
			"helper_instrument_WrTmp_Load",
			VG_(fnptr_to_fnentry)(helper_instrument_WrTmp_Load),
			mkIRExprVec_4(mkIRExpr_HWord((HWord)stclone),
				(addr->tag == Iex_RdTmp) ? assignNew_HWord(sb_out, addr) : mkIRExpr_HWord(addr->Iex.Const.con->Ico.U32),
				mkIRExpr_HWord(size),
				assignNew_HWord(sb_out, IRExpr_RdTmp(tmp)))
			);
	addStmtToIRSB(sb_out, IRStmt_Dirty(di));
}

static void instrument_WrTmp_Const(IRStmt* st, IRSB* sb_out)
{
	IRTemp  tmp = st->Ist.WrTmp.tmp;
	IRExpr* arg = st->Ist.WrTmp.data;
	UInt	arg_value;
	IRDirty* di;

	switch (arg->Iex.Const.con->tag)
	{
		case Ico_U1: arg_value = arg->Iex.Const.con->Ico.U1; break;
		case Ico_U8: arg_value = arg->Iex.Const.con->Ico.U8; break;
		case Ico_U16: arg_value = arg->Iex.Const.con->Ico.U16; break;
		case Ico_U32: arg_value = arg->Iex.Const.con->Ico.U32; break;
		case Ico_F32i: arg_value = arg->Iex.Const.con->Ico.F32i; break;
		case Ico_U64: arg_value = arg->Iex.Const.con->Ico.U64; break;
		case Ico_F64i: arg_value = arg->Iex.Const.con->Ico.F64i; break;
		default: ppIRStmt(st); tl_assert(0); //VG_(tool_panic)("instrument_WrTmp_Binop");
	}

	di = unsafeIRDirty_0_N(0,
			"helper_instrument_WrTmp_Const",
			VG_(fnptr_to_fnentry)(helper_instrument_WrTmp_Const),
			mkIRExprVec_2(mkIRExpr_HWord(tmp),
				mkIRExpr_HWord(arg_value))
			);
	addStmtToIRSB(sb_out, IRStmt_Dirty(di));
}
/*
	 cc_op
	 add/sub/mul
	 adc/sbb
	 shl/Shl/sar
	 tmp = cond(cc_op(cc_dep1, cc_dep2))
	 and/or/xor
	 inc/dec
	 rol/ror
	 tmp = cond(cc_op(cc_dep1, 0))

	 The taintness of tmp depends on taintness of both args. (we can't handle and(cc_dep1, 0) which gives an untainted result)
	 cf. valgrind guest_x86_defs.h
	 */

static void instrument_WrTmp_CCall(IRStmt* st, IRSB* sb_out)
{
	IRTemp tmp = st->Ist.WrTmp.tmp;
	IRExpr* data = st->Ist.WrTmp.data;
	IRCallee* cee = data->Iex.CCall.cee;
	IRExpr** args = data->Iex.CCall.args;
	IRDirty* di;

	//#if defined(VGPV_arm_linux_android)
	//UInt armg_calculate_condition ( UInt cond_n_op /* (ARMCondcode << 4) | cc_op */,
	//                          UInt cc_dep1,
	//                          UInt cc_dep2, UInt cc_dep3 )
	if (VG_(strcmp)(cee->name, "armg_calculate_condition") == 0)
	{
		IRExpr* cc_n_op = args[0];
		IRExpr* cc_dep1 = args[1];
		IRExpr* cc_dep2 = args[2];
		IRExpr* cc_dep3 = args[3];

		//tl_assert(cc_n_op->tag == Iex_Const && cc_n_op->Iex.Const.con->tag == Ico_U32);
		tl_assert(isIRAtom(cc_n_op));
		tl_assert(isIRAtom(cc_dep1));
		tl_assert(isIRAtom(cc_dep2));
		tl_assert(isIRAtom(cc_dep3));
		if (cc_n_op->tag == Iex_Const) tl_assert(cc_n_op->Iex.Const.con->tag == Ico_U32);
		if (cc_dep1->tag == Iex_Const) tl_assert(cc_dep1->Iex.Const.con->tag == Ico_U32);
		if (cc_dep2->tag == Iex_Const) tl_assert(cc_dep2->Iex.Const.con->tag == Ico_U32);
		if (cc_dep3->tag == Iex_Const) tl_assert(cc_dep3->Iex.Const.con->tag == Ico_U32);
		IRStmt* stclone = deepMallocIRStmt(st);
		di = unsafeIRDirty_0_N(0,
				"helper_instrument_WrTmp_CCall_armg_calculate_condition",
				VG_(fnptr_to_fnentry)(helper_instrument_WrTmp_CCall_armg_calculate_condition),
				mkIRExprVec_4(mkIRExpr_HWord((HWord)stclone),
					(cc_dep1->tag == Iex_RdTmp) ? assignNew_HWord(sb_out, cc_dep1) : mkIRExpr_HWord(cc_dep1->Iex.Const.con->Ico.U32),
					(cc_dep2->tag == Iex_RdTmp) ? assignNew_HWord(sb_out, cc_dep2) : mkIRExpr_HWord(cc_dep2->Iex.Const.con->Ico.U32),
					//(cc_dep3->tag == Iex_RdTmp) ? assignNew_HWord(sb_out, cc_dep3) : mkIRExpr_HWord(cc_dep3->Iex.Const.con->Ico.U32))
				(cc_n_op->tag == Iex_RdTmp) ? assignNew_HWord(sb_out, cc_n_op) : mkIRExpr_HWord(cc_n_op->Iex.Const.con->Ico.U32))
			);
		addStmtToIRSB(sb_out, IRStmt_Dirty(di));
	} else {
		di = unsafeIRDirty_0_N(0,
				"helper_instrument_WrTmp_CCall_else",
				VG_(fnptr_to_fnentry)(helper_instrument_WrTmp_CCall_else),
				mkIRExprVec_0()
				);
		addStmtToIRSB(sb_out, IRStmt_Dirty(di));
	}
}

static void instrument_WrTmp_ITE(IRStmt* st, IRSB* sb_out)
{
	IRTemp tmp = st->Ist.WrTmp.tmp;
	IRExpr* data = st->Ist.WrTmp.data;
	IRExpr* cond = data->Iex.ITE.cond;
	IRExpr* expr0 = data->Iex.ITE.iftrue;
	IRExpr* exprX = data->Iex.ITE.iffalse;
	Int size = sizeofIRType_bits(typeOfIRExpr(sb_out->tyenv, expr0));
	IRDirty* di;

	tl_assert(cond->tag == Iex_RdTmp);
	tl_assert(isIRAtom(expr0));
	tl_assert(isIRAtom(exprX));
	tl_assert(typeOfIRTemp(sb_out->tyenv, tmp) == typeOfIRExpr(sb_out->tyenv, expr0));
	tl_assert(typeOfIRTemp(sb_out->tyenv, tmp) == typeOfIRExpr(sb_out->tyenv, exprX));

	IRStmt* stclone = deepMallocIRStmt(st);
	di = unsafeIRDirty_0_N(0,
			"helper_instrument_WrTmp_ITE",
			VG_(fnptr_to_fnentry)(helper_instrument_WrTmp_ITE),
			mkIRExprVec_3(mkIRExpr_HWord((HWord)stclone),
				assignNew_HWord(sb_out, cond),
				mkIRExpr_HWord(size))
			);
	addStmtToIRSB(sb_out, IRStmt_Dirty(di));
}

static void instrument_WrTmp(IRStmt* st, IRSB* sb_out)
{
	switch (st->Ist.WrTmp.data->tag)
	{
		//case Iex_Binder:
		// we don't care about floating point and SIMD operations
		//case Iex_Qop:
		//	break;

		case Iex_Get:
#ifdef DO_INSTRUMENTATION
			instrument_WrTmp_Get(st, sb_out);
#endif
			break;
		case Iex_GetI:
#ifdef DO_INSTRUMENTATION
			instrument_WrTmp_GetI(st, sb_out);
#endif
			break;
		case Iex_RdTmp:
#ifdef DO_INSTRUMENTATION
			instrument_WrTmp_RdTmp(st, sb_out);
#endif
			break;
		case Iex_Unop:
#ifdef DO_INSTRUMENTATION
			instrument_WrTmp_Unop(st, sb_out);
#endif
			break;
		case Iex_Binop:
#ifdef DO_INSTRUMENTATION
			instrument_WrTmp_Binop(st, sb_out);
#endif
			break;
		case Iex_Triop:
#ifdef DO_INSTRUMENTATION
			instrument_WrTmp_Triop(st, sb_out);
#endif
			break;
		case Iex_Const:
#ifdef DO_INSTRUMENTATION
			instrument_WrTmp_Const(st, sb_out);
#endif
			break;
		case Iex_CCall:
#ifdef DO_INSTRUMENTATION
			instrument_WrTmp_CCall(st, sb_out);
#endif
			break;
		case Iex_ITE:
#ifdef DO_INSTRUMENTATION
			instrument_WrTmp_ITE(st, sb_out);
#endif
			break;
		case Iex_Load:
#ifdef DO_INS_LOAD
			instrument_WrTmp_Load(st, sb_out);
#endif
			break;
#if 0
		case Iex_Mux0X:
			instrument_WrTmp_Mux0X(st, sb_out);
			break;
#endif
		default:
			ppIRStmt(st);
			tl_assert(0);
	}
}

static void instrument_Store(IRStmt* st, IRSB* sb_out)
{
	IRExpr* addr = st->Ist.Store.addr;
	IRExpr* data = st->Ist.Store.data;
	Int size = sizeofIRType_bits(typeOfIRExpr(sb_out->tyenv, st->Ist.Store.data));
	IRDirty* di;

	tl_assert(isIRAtom(addr));
	tl_assert(isIRAtom(data));
	if (addr->tag == Iex_Const) tl_assert(addr->Iex.Const.con->tag == Ico_U32);
	// the data transfer type is the type of data

	IRStmt* stclone = deepMallocIRStmt(st);
	di = unsafeIRDirty_0_N(0,
			"helper_instrument_Store",
			VG_(fnptr_to_fnentry)(helper_instrument_Store),
			mkIRExprVec_4( mkIRExpr_HWord((HWord)stclone),
				(addr->tag == Iex_RdTmp) ? assignNew_HWord(sb_out, addr) : mkIRExpr_HWord(addr->Iex.Const.con->Ico.U32),
				(data->tag == Iex_RdTmp) ? assignNew_HWord(sb_out, data) : mkIRExpr_HWord(valueOfConst(data)),
				mkIRExpr_HWord(size))
			);
	addStmtToIRSB(sb_out, IRStmt_Dirty(di));
}

static void instrument_StoreG(IRStmt* st, IRSB* sb_out)
{
	IRStoreG* sg = st->Ist.StoreG.details;
	IRExpr* addr = sg->addr;
	IRExpr* data = sg->data;
	IRExpr* guard = sg->guard;
	Int size = sizeofIRType_bits(typeOfIRExpr(sb_out->tyenv, data));
	IRDirty* di;

	tl_assert(isIRAtom(addr));
	tl_assert(isIRAtom(data));
	tl_assert(isIRAtom(guard)); 
	if (addr->tag == Iex_Const) tl_assert(addr->Iex.Const.con->tag == Ico_U32);
	// the data transfer type is the type of data


	di = unsafeIRDirty_0_N(0,
			"helper_instrument_StoreG",
			VG_(fnptr_to_fnentry)(helper_instrument_StoreG),
			mkIRExprVec_4(
				(addr->tag == Iex_RdTmp) ? assignNew_HWord(sb_out, addr) : mkIRExpr_HWord(addr->Iex.Const.con->Ico.U32),
				(data->tag == Iex_RdTmp) ? assignNew_HWord(sb_out, data) : mkIRExpr_HWord(valueOfConst(data)),
				mkIRExpr_HWord(size),
				assignNew_HWord(sb_out, guard))
			);
	addStmtToIRSB(sb_out, IRStmt_Dirty(di));
}

static void instrument_LoadG(IRStmt* st, IRSB* sb_out)
{
	IRLoadG* lg = st->Ist.LoadG.details;

	IRTemp  dst		= lg->dst;
	IRExpr* addr	= lg->addr;
	IRExpr* alt		= lg->alt;
	IRExpr* guard	= lg->guard;
	IRDirty* di;

	IROp vwiden = Iop_INVALID;

	tl_assert(isIRAtom(addr));
	tl_assert(isIRAtom(alt));
	tl_assert(isIRAtom(guard));

	IRStmt* stclone = deepMallocIRStmt(st);

	di = unsafeIRDirty_0_N(0,
			"helper_instrument_LoadG",
			VG_(fnptr_to_fnentry)(helper_instrument_LoadG),
			mkIRExprVec_4(mkIRExpr_HWord((HWord)stclone),
				(addr->tag == Iex_RdTmp) ? assignNew_HWord(sb_out, addr) : mkIRExpr_HWord(addr->Iex.Const.con->Ico.U32),
				assignNew_HWord(sb_out, IRExpr_RdTmp(dst)),
				assignNew_HWord(sb_out, guard))
			);
	addStmtToIRSB(sb_out, IRStmt_Dirty(di));
}

static void instrument_CAS_single_element(IRStmt* st, IRSB* sb_out)
{
	IRCAS* cas = st->Ist.CAS.details;
	IRTemp oldLo = cas->oldLo;
	IRExpr* addr = cas->addr;
	IRExpr* expdLo = cas->expdLo;
	IRExpr* dataLo = cas->dataLo;
	Int size = sizeofIRType_bits(typeOfIRExpr(sb_out->tyenv, dataLo));
	IROp op;
	IRExpr* expr;
	IRDirty* di;

	tl_assert(isIRAtom(addr));
	tl_assert(isIRAtom(dataLo));
	if (addr->tag == Iex_Const) tl_assert(addr->Iex.Const.con->tag == Ico_U32);
	tl_assert(typeOfIRExpr(sb_out->tyenv, addr) == typeOfIRExpr(sb_out->tyenv, dataLo));

	switch (size)
	{
		case 8: op = Iop_CasCmpEQ8; break;
		case 16: op = Iop_CasCmpEQ16; break;
		case 32: op = Iop_CasCmpEQ32; break;
		default: VG_(tool_panic)("instrument_CAS_single_element");
	}

	expr = assignNew(sb_out, IRExpr_Binop(op, IRExpr_RdTmp(oldLo), expdLo)); // statement has to be flat

	di = unsafeIRDirty_0_N(0,
			"helper_instrument_CAS_single_element",
			VG_(fnptr_to_fnentry)(helper_instrument_CAS_single_element),
			mkIRExprVec_4((addr->tag == Iex_RdTmp) ? assignNew_HWord(sb_out, addr) : mkIRExpr_HWord(addr->Iex.Const.con->Ico.U32),
				mkIRExpr_HWord((dataLo->tag == Iex_RdTmp) ? dataLo->Iex.RdTmp.tmp : IRTemp_INVALID),
				mkIRExpr_HWord(size),
				assignNew_HWord(sb_out, expr))
			);
	addStmtToIRSB(sb_out, IRStmt_Dirty(di));
}

static void instrument_CAS_double_element(IRStmt* st, IRSB* sb_out)
{
	IRCAS* cas = st->Ist.CAS.details;
	IRTemp oldHi = cas->oldHi, oldLo = cas->oldLo;
	IREndness end = cas->end;
	IRExpr* addr = cas->addr;
	IRExpr *expdHi = cas->expdHi, *expdLo = cas->expdLo;
	IRExpr *dataHi = cas->dataHi, *dataLo = cas->dataLo;
	Int size = sizeofIRType_bits(typeOfIRExpr(sb_out->tyenv, dataLo));
	IROp op;
#if defined(VGPV_arm_linux_android)
	IROp op1;
#endif
	IRExpr *expr1, *expr2;
	IRDirty* di;

	tl_assert(isIRAtom(addr));
	tl_assert(end == Iend_LE); // we assume endianness is little endian
	tl_assert(isIRAtom(dataLo));
	tl_assert(isIRAtom(dataHi));
	if (addr->tag == Iex_Const) tl_assert(addr->Iex.Const.con->tag == Ico_U32);
	tl_assert(typeOfIRExpr(sb_out->tyenv, addr) == typeOfIRExpr(sb_out->tyenv, dataLo));

	switch (size)
	{
		case 8: 
			op = Iop_CasCmpEQ8; 
#if defined(VGPV_arm_linux_android)
			op1 =  Iop_And8;
#endif
			break;
		case 16: 
			op = Iop_CasCmpEQ16;
#if defined(VGPV_arm_linux_android)
			op1 =  Iop_And16;
#endif
			break;
		case 32:
			op = Iop_CasCmpEQ32; 
#if defined(VGPV_arm_linux_android)
			op1 =  Iop_And32;
#endif
			break;
		default: 
			VG_(tool_panic)("instrument_CAS_double_element");
	}

	expr1 = assignNew(sb_out, IRExpr_Binop(op, IRExpr_RdTmp(oldLo), expdLo)); // statement has to be flat
	expr2 = assignNew(sb_out, IRExpr_Binop(op, IRExpr_RdTmp(oldHi), expdHi)); // statement has to be flat
#if defined(VGPV_arm_linux_android)
	IRExpr *expr = assignNew(sb_out, IRExpr_Binop(op1, expr1, expr2));
	IRStmt* stclone = deepMallocIRStmt(st);
	di = unsafeIRDirty_0_N(0,
			"helper_instrument_CAS_double_element",
			VG_(fnptr_to_fnentry)(helper_instrument_CAS_double_element),
			mkIRExprVec_4(mkIRExpr_HWord((HWord)stclone),
				(addr->tag == Iex_RdTmp) ? assignNew_HWord(sb_out, addr) : mkIRExpr_HWord(addr->Iex.Const.con->Ico.U32),
				mkIRExpr_HWord(size),
				assignNew_HWord(sb_out, expr))
			);
#else
	di = unsafeIRDirty_0_N(0,
			"helper_instrument_CAS_double_element",
			VG_(fnptr_to_fnentry)(helper_instrument_CAS_double_element),
			mkIRExprVec_6((addr->tag == Iex_RdTmp) ? assignNew_HWord(sb_out, addr) : mkIRExpr_HWord(addr->Iex.Const.con->Ico.U32),
				mkIRExpr_HWord((dataLo->tag == Iex_RdTmp) ? dataLo->Iex.RdTmp.tmp : IRTemp_INVALID),
				mkIRExpr_HWord((dataHi->tag == Iex_RdTmp) ? dataHi->Iex.RdTmp.tmp : IRTemp_INVALID),
				mkIRExpr_HWord(size),
				assignNew_HWord(sb_out, expr1),
				assignNew_HWord(sb_out, expr2))
			);
#endif // defined(VGA_arm)
	addStmtToIRSB(sb_out, IRStmt_Dirty(di));
}

static void instrument_CAS(IRStmt* st, IRSB* sb_out)
{
	if (st->Ist.CAS.details->oldHi == IRTemp_INVALID)
	{
		instrument_CAS_single_element(st, sb_out);
	}
	else
	{
		instrument_CAS_double_element(st, sb_out);
	}
}

static void instrument_LLSC_Load_Linked(IRStmt* st, IRSB* sb_out)
{
	IRTemp result = st->Ist.LLSC.result;
	IRExpr* addr = st->Ist.LLSC.addr;
	Int size = sizeofIRType_bits(typeOfIRTemp(sb_out->tyenv, result));
	IRDirty* di;

	tl_assert(isIRAtom(addr));
	if (addr->tag == Iex_Const) tl_assert(addr->Iex.Const.con->tag == Ico_U32);
	// the data transfer type is the type of result

	di = unsafeIRDirty_0_N(0,
			"helper_instrument_LLSC_Load_Linked",
			VG_(fnptr_to_fnentry)(helper_instrument_LLSC_Load_Linked),
			mkIRExprVec_3(mkIRExpr_HWord(result),
				(addr->tag == Iex_RdTmp) ? assignNew_HWord(sb_out, addr) : mkIRExpr_HWord(addr->Iex.Const.con->Ico.U32),
				mkIRExpr_HWord(size))
			//assignNew_HWord(sb_out, IRExpr_RdTmp(result)))
				);
	addStmtToIRSB(sb_out, IRStmt_Dirty(di));
}

static void instrument_LLSC_Store_Conditional(IRStmt* st, IRSB* sb_out)
{
	IRTemp result = st->Ist.LLSC.result;
	IRExpr* addr = st->Ist.LLSC.addr;
	IRExpr* storedata = st->Ist.LLSC.storedata;
	Int size = sizeofIRType_bits(typeOfIRExpr(sb_out->tyenv, storedata));
	IRExpr* result_expr = IRExpr_RdTmp(result);
	IRDirty* di;

	tl_assert(isIRAtom(addr));
	tl_assert(isIRAtom(storedata));
	if (addr->tag == Iex_Const) tl_assert(addr->Iex.Const.con->tag == Ico_U32);
	// the data transfer type is the type of storedata
	di = unsafeIRDirty_0_N(0,
			"helper_instrument_LLSC_Store_Conditional",
			VG_(fnptr_to_fnentry)(helper_instrument_LLSC_Store_Conditional),
			mkIRExprVec_4((addr->tag == Iex_RdTmp) ? assignNew_HWord(sb_out, addr) : mkIRExpr_HWord(addr->Iex.Const.con->Ico.U32),
				mkIRExpr_HWord((storedata->tag == Iex_RdTmp) ? storedata->Iex.RdTmp.tmp : IRTemp_INVALID),
				mkIRExpr_HWord(size),
				assignNew_HWord(sb_out, result_expr))
			);
	addStmtToIRSB(sb_out, IRStmt_Dirty(di));
}

static void instrument_LLSC(IRStmt* st, IRSB* sb_out)
{
	if (st->Ist.LLSC.storedata == NULL)
	{ /* Load linked 
		 * Just treat it as the normal load statement,
		 * followed by an assignement of the value to .result
		 */
		instrument_LLSC_Load_Linked(st, sb_out);
	}
	else
	{
		/* Store conditional
		 * It writes .result with a value for indicating whether 
		 * the store statment is successful.
		 */
		instrument_LLSC_Store_Conditional(st, sb_out);
	}
}

static void instrument_Exit(Addr src, IRStmt* st, IRSB* sb_out)
{
	IRExpr* guard = st->Ist.Exit.guard;
	IRDirty* di = NULL;
	tl_assert(guard->tag == Iex_RdTmp);

	IRStmt* stclone = deepMallocIRStmt(st);
	di = unsafeIRDirty_0_N(0,
			"helper_instrument_Exit",
			VG_(fnptr_to_fnentry)((void*)&helper_instrument_Exit),
			mkIRExprVec_4( assignNew_HWord(sb_out, guard),
				mkIRExpr_HWord(src),
				mkIRExpr_HWord(st->Ist.Exit.dst->Ico.U32),
				mkIRExpr_HWord(guard->Iex.RdTmp.tmp))
			);
	addStmtToIRSB(sb_out, IRStmt_Dirty(di));
}

static void instrument_Next(Addr src, IRExpr *next, IRSB* sb_out)
{
	IRDirty* di = NULL;
	di = unsafeIRDirty_0_N(3,
			"helper_instrument_Next",
			VG_(fnptr_to_fnentry)((void*)&helper_instrument_Next),
			mkIRExprVec_3( mkIRExpr_HWord(src),
				assignNew_HWord(sb_out, next),
				next->tag == Iex_RdTmp ? mkIRExpr_HWord(next->Iex.RdTmp.tmp) : mkIRExpr_HWord(IRTemp_INVALID))
			);
	addStmtToIRSB(sb_out, IRStmt_Dirty(di));
}



/*-----------------------------------------------*/
/*------- For tracking ART Methods --------------*/
/*-----------------------------------------------*/
#define TG_N_THREADS		256

static Bool trace_obj_taint = False;
static MthStack mthStack[TG_N_THREADS];


static
INLINE Bool is_framework_bb(Addr a) {
	IRDirty *di = NULL;
	DebugInfo *dbgInfo = VG_(find_DebugInfo)(a);
	if(dbgInfo) {
		if(VG_(DebugInfo_is_oat)(dbgInfo)) {
			return True;
		}
	}
	return False;
}

static Bool is_mth_stack_full = False;

static 
INLINE Int mth_stack_size(ThreadId tid) {
	return mthStack[tid].size;
}

static
INLINE void mth_stack_print(ThreadId tid) {
}

#define MTH_CALL_DEPTH 4
static Int mth_push_stack(ThreadId tid, Addr addr, Addr sp, MthNode *mth, UChar taintTag) {
	MthStack *ms = NULL;
	if(tid < TG_N_THREADS) {
		ms = &mthStack[tid];
		if(ms->size > MTH_CALL_DEPTH) {
			is_mth_stack_full = True;
			return -1;
		}
		if(ms->size < MAX_STACK_SIZE) {
			ms->addr[ms->size] = addr;
			ms->stack[ms->size] = sp;
			ms->mth[ms->size]  = (Addr)mth;
			ms->taintTag[ms->size] = taintTag;
			ms->size++;
		} else {
			MY_LOGI("Method stack overflow!!!\n");
			mth_stack_print(tid);
			tl_assert(0);
		}
		return ms->size;
	}
	return -1;
}

static Int mth_pop_stack(ThreadId tid, Int num) {
	MthStack *ms = NULL;
	tl_assert(num > 0);
	UInt i = 0;
	if(tid < TG_N_THREADS) {
		ms = &mthStack[tid];
		if(ms->size > num) {
			ms->size -= num;
			for(i = 0; i < num; i++) {
				ms->mth[ms->size + i] = NULL;
				ms->addr[ms->size + i] = 0;
				ms->stack[ms->size + i] = 0;
				ms->taintTag[ms->size + i] = 0;
			}
		} else {
			ms->size = 0;
		}
		if(is_mth_stack_full) 
			is_mth_stack_full = False;
		return ms->size;
	}
	return -1;
}

static  Bool mth_top_stack1(ThreadId tid, Addr *addr, Addr *stack,
		MthNode **mth,
		UChar *taintTag,
		Int index) {
	MthStack *ms = NULL;
	if(tid < TG_N_THREADS) {
		ms = &mthStack[tid];
		if(ms->size >= index) {
			*addr = ms->addr[ms->size - index];
			*stack = ms->stack[ms->size - index];
			if(mth) {
				*mth = (MthNode*)ms->mth[ms->size - index];
				*taintTag = ms->taintTag[ms->size - index];
			}
			return True;
		}
	}
	return False;
}

static  Bool mth_top_stack(ThreadId tid, Addr *addr, Addr *addr1, 
		MthNode **mth, MthNode **mth1, 
		UChar *taintTag, UChar *taintTag1) {
	MthStack *ms = NULL;
	if(tid < TG_N_THREADS) {
		ms = &mthStack[tid];
		if(ms->size > 0) {
			*addr = ms->addr[ms->size - 1];
			if(mth) {
				*mth = (MthNode*)ms->mth[ms->size - 1];
				*taintTag = ms->taintTag[ms->size - 1];
			}
		} else {
			return False;
		}
		if(ms->size > 1) {
			*addr1 = ms->addr[ms->size - 2];
			if(mth1) {
				*mth1 = (MthNode*)ms->mth[ms->size - 2];
				*taintTag1 = ms->taintTag[ms->size - 2];
			}
		} else {
			*addr1 = -1;
		}
		return True;
	}
	return False;
}

static MthNode* mth_lookup_stack(ThreadId tid, Addr a) {
	MthStack *ms = NULL;
	Addr addr;
	if(tid < TG_N_THREADS) {
		ms = &mthStack[tid];
		for(Int i = ms->size; i > 0; i--){
			addr = ms->addr[i - 1];
			if(a & ~0x1 == addr & ~0x1) {
				return (MthNode*)ms->mth[i - 1];
			}
		}
	}
	return NULL;
}

Addr dlopen_addr = 0, dlsym_addr = 0;

//void* dlopen(const char* filename, int flags)
//__dl_dlopen
//
static void helper_invoke_superblock_dlopen(VexGuestLayout *layout) {
#if defined(VGPV_arm_linux_android)
	ThreadId tid			= VG_(get_running_tid)();
	ThreadState *tst	= VG_(get_ThreadState) ( tid );
	VexGuestArchState	*arch_state = &tst->arch.vex;
	const HChar* filename = (HChar*)arch_state->guest_R0;
	const Int    flags = (Int)arch_state->guest_R1;
	MY_LOGI("Call[%d]: dlopen() filename=%s flags=0x%x\n", tid, filename, flags);
#endif
}
//void* dlsym(void* handle, const char* symbol)
// const ElfW(Sym)* dlsym_handle_lookup(soinfo* si, soinfo** found, const char* name)
//__dl_dlsym
static void helper_invoke_superblock_dlsym_lookup(VexGuestLayout *layout) {
#if defined(VGPV_arm_linux_android)
	ThreadId tid			= VG_(get_running_tid)();
	ThreadState *tst	= VG_(get_ThreadState) ( tid );
	VexGuestArchState	*arch_state = &tst->arch.vex;
	const Addr        si = (Addr)arch_state->guest_R0;
	const Addr* si_found = (Addr)arch_state->guest_R1;
	const HChar* name = (HChar*)arch_state->guest_R2;
	MY_LOGI("Call[%d]: dlsym() hsi=0x%08x found=0x%08x symbol=%s\n", tid, si, *si_found, name);
#endif
}

/* Check if a framwork is invoked, if so, parse the arguments */
static void invoke_framework_method(Addr irst_addr, MthList *mList) {
	Int tt = 0, i = 0, s = 0;
	Addr last_lr;
	Bool isSource = False;
	UChar taintTag = 0;
	UWord r0 = 0, r1 = 0, r2 = 0, r3 = 0, r4 = 0, r8 = 0, r9 = 0, r10 = 0, r11 = 0, r12 = 0, sp = 0, lr = 0, pc = 0;
	ThreadId tid			= VG_(get_running_tid)();
	ThreadState *tst	= VG_(get_ThreadState) ( tid );
	VexGuestArchState	*arch_state = &tst->arch.vex;
#if defined(VGPV_arm_linux_android)
	r0 = arch_state->guest_R0;
	r1 = arch_state->guest_R1;
	r2 = arch_state->guest_R2;
	r3 = arch_state->guest_R3;
	r4 = arch_state->guest_R4;
	r8 = arch_state->guest_R8;
	r9 = arch_state->guest_R9;
	r10 = arch_state->guest_R10;
	r11 = arch_state->guest_R11;
	r12 = arch_state->guest_R12;
	sp = arch_state->guest_R13;
	lr = arch_state->guest_R14;
	pc = arch_state->guest_R15T;
#endif
	struct ArtMethodPlus *pAMth = (struct ArtMethodPlus *)r0;
	MthNode *mNode = NULL;
	for(i = 0; i < mList->num; i++) {
		mNode = (MthNode *)mList->mthNodes[i];
		if(mNode->mthKey == pAMth->dex_method_index_)
			break;
	}
	if(mNode == NULL || i == mList->num)
		return;
	Bool isStatic = (mNode->accessFlags & ACC_STATIC) ? True : False;
	Bool isEntrance = False;


	s = mth_stack_size(tid);
	if(mNode->mthKey == do_start_method_index) {
		if((VG_(strcmp)(mNode->method, do_start_method_name) == 0) /*&& (s == 61 || s == 57 || s == 53)is_in_vm == 0*/) {
			is_in_vm = VG_(get_running_tid)();
			start_trace_irst = VG_(get_running_tid)();
			isEntrance = True;
			do_exit_addr = lr;
			MY_LOGI("Start the detail analysis (ret=0x%08x).\n", lr);
			if (target_mem_addr > 0) {
				UChar *s1 = (UChar*)target_mem_addr;
				for (UInt i = 0; i < target_mem_len; i++) {
					VG_(printf)("0x%02x ", s1[i]);
					if (i % 16 == 0)
						VG_(printf)("\n");
				}
				VG_(printf)("\n");
			}
		}
	} 

	if( is_in_vm == 0 ) {
		return;
	}
	
	// VG_(printf)("[REGS] r8=0x%08x r9=0x%08x r10=0x%08x r11=0x%08x r12=0x%08x sp=0x%08x lr=0x%08x pc=0x%08x\n",
	//		r8, r9, r10, r11, r12, sp, lr, pc);
	ART_INVOKE("%02d %d %05d %s %s() %s isNative=%c flag=0x%8x pArtMethod=0x%08x (0x%08x, 0x%08x, 0x%08x, this=0x%08x, sp=0x%08x)\n",
			tid, s, mNode->mthKey, mNode->clazz, mNode->method, mNode->shorty,
			(pAMth->access_flags_ & ACC_NATIVE) ? '1' : '0',
			pAMth->access_flags_, (Addr)pAMth,
			pAMth->declaring_class_,
			pAMth->ptr_sized_fields_.entry_point_from_jni_,
			pAMth->ptr_sized_fields_.entry_point_from_quick_compiled_code_,
			r0, sp);
	tt = mth_push_stack(tid, lr, sp, mNode, taintTag);
#ifdef PARSE_RET_PARAMETER
	//taintTag = check_mth_invoke(mNode, tid, isSource);
	check_mth_invoke(mNode, tid, isSource);
#else
	if(isEntrance)
		check_mth_invoke(mNode, tid, isSource);
#endif
	mNode->pAMth = (Addr)pAMth;
	if(pAMth->access_flags_ & ACC_NATIVE) {
		codeLayer[tid] = 1;
	}
}

/* Check if a framework returns, if so, parse the results */
static void return_framework_method(Addr a) {
	ThreadId tid = VG_(get_running_tid)();
	ThreadState *tst = VG_(get_ThreadState) ( tid );
	VexGuestArchState *arch_state = &tst->arch.vex;
	Addr addr, addr1, stack;
	MthNode *mNode = NULL, *mNode1 = NULL;
	UWord sp = 0;
	UChar taintTag = 0, taintTag1 = 0;
	Bool isSource = False;
#if defined(VGPV_arm_linux_android)
	sp = arch_state->guest_R13;
#endif
	Bool isStatic = False;
	Int  index = 0, s = 0;
	while(mth_top_stack1(tid, &addr, &stack, &mNode, &taintTag, ++index)) {
		if(((addr & 0xfffffffe) == (a & 0xfffffffe)) && ((stack & 0xfffffffe) == (sp & 0xfffffffe))) {
			s = mth_pop_stack(tid, index);
			isStatic = (mNode->accessFlags & ACC_STATIC) ? True : False;
			ART_RETURN("%02d %d %05d %s %s() %s isSource=%s pArtMthod=0x%08x (pc=0x%08x, top=0x%08x, sp=0x%08x)\n",
					tid, s, mNode->mthKey, mNode->clazz, mNode->method,	mNode->shorty,
					mNode->type & TYPE_SOURCE ? "True" : "Flase", mNode->pAMth, a, addr, sp);
			if(mNode->accessFlags & ACC_NATIVE) { codeLayer[tid] = 0;	}
#ifdef PARSE_RET_PARAMETER
			/*if(do_method_trace) {
				if(isSource) {
				do_taint_source(mNode, tid);
				} else {
				check_mth_return(mNode, tid, taintTag);
				}
				}*/
			check_mth_return(mNode, tid, taintTag);
#endif
		}
		if(is_mth_stack_full == False) {
			break;
		}
		break; // only compare the top address
	}
	if((do_exit_addr > 0) && ((do_exit_addr & 0xfffffffe) == (a & 0xfffffffe))) 
	{
		is_in_vm = 0;
		do_is_start = False;
		start_trace_irst = 0;
		MY_LOGI("Stop the detail analysis\n");
#ifdef BAIDU_VMP
		dumpBinary(baidu_vmp_table_addr, baidu_vmp_table_size);
#endif
		if (target_mem_addr > 0) {
			UChar *s1 = (UChar*)target_mem_addr;
			for (UInt i = 0; i < target_mem_len; i++) {
				VG_(printf)("0x%02x ", s1[i]);
				if (i % 16 == 0)
					VG_(printf)("\n");
			}
			VG_(printf)("\n");
		}
#if DBG_OAT_PARSE
		is_parse_oat = True;
#endif
		// release the Dex files
		releaseDexFileList();
		saveDexFileObjs();
		if (pMDexFileObj == NULL) {
			saveDexFileObjs();
		} 
#if 0
		else {
			dumpRawData(pMDexFileObj->begin_, pMDexFileObj->size_, 1);
		}
#endif
#if DBG_OAT_PARSE
		is_parse_oat = False;
#endif
		parseOatFile(NULL);
	}
}


/* The helper dirty function inserted into the beginning of a IRSB */
static VG_REGPARM(0) void helper_instrument_superblock( Addr irst_addr, Addr mListAddr)
{
	if (do_is_start == False)
		return;

	if(do_method_trace && mListAddr > 0) {
		MthList *mList = (MthList *)mListAddr;
		invoke_framework_method(irst_addr, mList);
	}
}

/* The helper dirty function inserted at the end of a IRSB */
static VG_REGPARM(1) UInt helper_instrument_tmp_next(Addr d)
{ 
	Addr dst = d;
	if(do_method_trace)
		return_framework_method(dst);
	return dst;
}


static VG_REGPARM(1) UInt helper_instrument_const_next(Addr d)
{
	Addr dst = d;
	return d;
}

static INLINE
Bool is_instrument_needed( VgCallbackClosure* closure ) {
	Addr a = closure->nraddr;
	return !isSysLib(a, NULL);// || ( a >= libart_text_beg && a <= libart_text_end);
}


IRSB* do_instrument ( VgCallbackClosure* closure,
		IRSB* sb_in,
		const VexGuestLayout* layout,
		const VexGuestExtents* vge,
		const VexArchInfo* archinfo_host,
		IRType gWordTy, IRType hWordTy )
{
	if((do_is_start == False) && (do_method_trace == False))
		return sb_in;
	Int i;
	IRSB* sb_out;
	IRDirty* di;
	MthList *mList = NULL;
	MthNode *mNode = NULL;
	Bool		isEntry = False;
	Bool		is_debug = False;

	if (gWordTy != hWordTy) {
		ppIRType(gWordTy);
		ppIRType(hWordTy);
		/* We don't currently support this case. */
		VG_(tool_panic)("host/guest word size mismatch");
	}
	/* Set up SB */
	sb_out = deepCopyIRSBExceptStmts(sb_in);

	// Copy verbatim any IR preamble preceding the first IMark
	i = 0;
	while (i < sb_in->stmts_used && sb_in->stmts[i]->tag != Ist_IMark) {
		addStmtToIRSB(sb_out, sb_in->stmts[i]);
		i++;
	}

	/*-------- For method tracking ---------*/
	if(do_method_trace) {
		if (is_framework_bb(vge->base[0])) {
			mList = query_method_list(vge->base[0]&0xfffffffc);
		}
	}
	di = unsafeIRDirty_0_N(2, 
			"helper_instrument_superblock",
			VG_(fnptr_to_fnentry) ( helper_instrument_superblock ),
			mkIRExprVec_2(mkIRExpr_HWord((Addr)vge->base[0]),
				mkIRExpr_HWord((Addr)mList)));
	addStmtToIRSB(sb_out, IRStmt_Dirty(di));

	for (/*use current i*/; i < sb_in->stmts_used; i++)
	{
		IRStmt* st = sb_in->stmts[i];
		if (!st)
			continue;

		switch (st->tag)
		{
			case Ist_NoOp:
			case Ist_IMark:
			case Ist_AbiHint:
			case Ist_Dirty:
			case Ist_MBE:
				addStmtToIRSB(sb_out, st);
				break;

			case Ist_WrTmp:
				addStmtToIRSB(sb_out, st);
				instrument_WrTmp(st, sb_out);
				break;
			case Ist_Put:
#ifdef DO_INSTRUMENTATION
				instrument_Put(st, sb_out);
#endif
				addStmtToIRSB(sb_out, st);
				break;
			case Ist_PutI:
#ifdef DO_INSTRUMENTATION
				instrument_PutI(st, sb_out);
#endif
				addStmtToIRSB(sb_out, st);
				break;
			case Ist_Store:
#ifdef DO_INS_STORE
				instrument_Store(st, sb_out);
#endif
				addStmtToIRSB(sb_out, st);
				break;
			case Ist_StoreG:
				addStmtToIRSB(sb_out, st);
				// if (<guard>) ST<end>(<addr>) = <data>
#ifdef DO_INS_STORE
				instrument_StoreG(st, sb_out);
#endif
				break;
			case Ist_LoadG: 
				// t<tmp> = if (<guard>) <cvt>(LD<end>(<addr>)) else <alt>
				addStmtToIRSB(sb_out, st);
#ifdef DO_INS_LOAD
				instrument_LoadG(st, sb_out);
#endif
				break;
			case Ist_CAS:
				addStmtToIRSB(sb_out, st); // dirty helpers use temporaries (oldHi, oldLo) defined in the instruction
#ifdef DO_INSTRUMENTATION
				instrument_CAS(st, sb_out);
#endif
				break;
			case Ist_LLSC:
				addStmtToIRSB(sb_out, st);
#ifdef DO_INSTRUMENTATION
				instrument_LLSC(st, sb_out);
#endif
				break;
			case Ist_Exit:
				instrument_Exit(closure->nraddr, st, sb_out);
				addStmtToIRSB(sb_out, st);
				break;
			default:
				MY_LOGI("do_main.c: do_instrument(), Unhandled IRStmt.\n");
				ppIRStmt(st);
				VG_(printf)("\n");
				tl_assert(0);
		}
	}
	//if( do_is_start && is_instrument_needed(closure)) {
	if( do_is_start ) {
		IRExpr *next = sb_in->next;
		instrument_Next(closure->nraddr, next, sb_out);
		switch(next->tag) {
			case Iex_Const:
				{
					Addr next_addr = valueOfConst(next);
					IRTemp dst = newIRTemp(sb_out->tyenv, Ity_I32);
					di = unsafeIRDirty_1_N(dst, 0,
							"helper_instrument_const_next",
							VG_(fnptr_to_fnentry)(helper_instrument_const_next),
							mkIRExprVec_1(mkIRExpr_HWord(next_addr))
							);
					addStmtToIRSB(sb_out, IRStmt_Dirty(di));
					sb_out->next = IRExpr_RdTmp(dst);
					break;
				}     
			case Iex_RdTmp:
				{     
					IRTemp dst = newIRTemp(sb_out->tyenv, Ity_I32);
					di = unsafeIRDirty_1_N(dst, 0,
							"helper_instrument_tmp_next",
							VG_(fnptr_to_fnentry)(helper_instrument_tmp_next),
							mkIRExprVec_1(assignNew_HWord(sb_out, sb_in->next))
							);
					addStmtToIRSB(sb_out, IRStmt_Dirty(di));
					sb_out->next = IRExpr_RdTmp(dst);
					break;
				}     
			default:
				tl_assert(0);
		}
	}
#ifdef FZ_DEBUG
	if(is_in_vm > 0) { 
		VG_(printf)("Output (0x%08x) ", vge->base[0]);
		ppIRSB(sb_out);
	}
	if(is_in_vm > 0) {
		if(isMonMap(vge->base[0], NULL) > 0) {
			VG_(printf)("Output (0x%08x) ", vge->base[0]);
			ppIRSB(sb_out);
		}
	}
	if(do_is_start || is_debug) {
		VG_(printf)("Debug output (0x%08x, %d) ", vge->base[0], vge->len[0]);
		ppIRSB(sb_out);
	}
#endif
	return sb_out;
}
