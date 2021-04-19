#ifndef _DO_INSTRUMENT_H
#define _DO_INSTRUMENT_H

#include "pub_tool_basics.h"

#define STR_COMPARE
#undef  STR_COMPARE

#define PARSE_RET_PARAMETER
#undef  PARSE_RET_PARAMETER

#define FZ_LOG_IR
#undef  FZ_LOG_IR


IRSB* do_instrument ( VgCallbackClosure* closure,
		IRSB* sb_in,
		const VexGuestLayout* layout,
		const VexGuestExtents* vge,
		const VexArchInfo* archinfo_host,
		IRType gWordTy, IRType hWordTy );


#endif // _DO_INSTRUMENT_H
