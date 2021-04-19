#ifndef _UNTITLED_H
#define _UNTITLED_H

#define UN_SHOULD_PRINT_FUNC 0
#define UN_SHOULD_PRINT_FUNC_EXIT 0
#define UN_SHOULD_PRINT_COND 0
#define UN_SHOULD_PRINT_DEBUG 0
#define DBG_PARAMETER_PARSE 0

#define UN_DO_NOTHING(x...) do {} while(0)

#if UN_SHOULD_PRINT_FUNC
    #define UN_PRINT_FUNC() do { VG_(printf)("[ UNTITLED ] [ FUNC ] In %s\n", __func__); } while(0)
#else
    #define UN_PRINT_FUNC() UN_DO_NOTHING()
#endif

#if UN_SHOULD_PRINT_FUNC_EXIT
    #define UN_PRINT_FUNC_EXIT() do { VG_(printf)("[ UNTITLED ] [ FUNC ] Exiting %s\n", __func__); } while(0)
#else
    #define UN_PRINT_FUNC_EXIT() UN_DO_NOTHING()
#endif

#define UN_PRINT_COND_PREFIX "[ UNTITLED ] [ COND ] %s "

#define UN_BOOL_TO_NUM(x) x ? "1" : "0"
// #if UN_SHOULD_PRINT_COND
//     #define UN_PRINT_COND(fmt, x...) do { VG_(printf)("[ UNTITLED ] [ COND ] %s "fmt, __func__, ##x); } while(0)
// #else
//     #define UN_PRINT_COND(fmt, x...) do {} while(0)
// #endif

#if UN_SHOULD_PRINT_DEBUG
    #define UN_PRINT_DEBUG(fmt, x...) do { VG_(printf)(fmt, ##x); } while(0)
#else
    #define UN_PRINT_DEBUG(fmt, x...) UN_DO_NOTHING()
#endif

#endif  // _UNTITLED_H