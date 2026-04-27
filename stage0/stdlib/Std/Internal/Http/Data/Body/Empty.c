// Lean compiler output
// Module: Std.Internal.Http.Data.Body.Empty
// Imports: public import Std.Internal.Http.Data.Request public import Std.Internal.Http.Data.Response public import Std.Internal.Http.Data.Body.Any
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Internal_IO_Async_EAsync_instMonad(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* l_Std_Internal_IO_Async_EAsync_instMonadLiftBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Internal_IO_Async_Waiter_race___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Any_ofBody___redArg(lean_object*, lean_object*);
lean_object* l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Http_Request_Builder_body___redArg(lean_object*, lean_object*);
lean_object* l_Std_Http_Response_Builder_body___redArg(lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Any_ofBody(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_toCtorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instInhabitedEmpty_default;
LEAN_EXPORT lean_object* l_Std_Http_Body_instInhabitedEmpty;
LEAN_EXPORT uint8_t l_Std_Http_Body_instBEqEmpty_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instBEqEmpty_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instBEqEmpty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instBEqEmpty_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instBEqEmpty___closed__0 = (const lean_object*)&l_Std_Http_Body_instBEqEmpty___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instBEqEmpty = (const lean_object*)&l_Std_Http_Body_instBEqEmpty___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_Empty_recv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Body_Empty_recv___redArg___closed__0 = (const lean_object*)&l_Std_Http_Body_Empty_recv___redArg___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_Empty_recv___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_Empty_recv___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_Body_Empty_recv___redArg___closed__1 = (const lean_object*)&l_Std_Http_Body_Empty_recv___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recv___redArg();
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recv___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recv(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recv___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Body_Empty_close___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Body_Empty_close___redArg___closed__0 = (const lean_object*)&l_Std_Http_Body_Empty_close___redArg___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_Empty_close___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_Empty_close___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_Body_Empty_close___redArg___closed__1 = (const lean_object*)&l_Std_Http_Body_Empty_close___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_close___redArg();
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_close___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_close(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_close___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Body_Empty_isClosed___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_Body_Empty_isClosed___redArg___closed__0 = (const lean_object*)&l_Std_Http_Body_Empty_isClosed___redArg___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_Empty_isClosed___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_Empty_isClosed___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_Body_Empty_isClosed___redArg___closed__1 = (const lean_object*)&l_Std_Http_Body_Empty_isClosed___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_isClosed___redArg();
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_isClosed___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_isClosed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_isClosed___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Body_Empty_tryRecv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Body_Empty_tryRecv___redArg___closed__0 = (const lean_object*)&l_Std_Http_Body_Empty_tryRecv___redArg___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_Empty_tryRecv___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Body_Empty_tryRecv___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_Body_Empty_tryRecv___redArg___closed__1 = (const lean_object*)&l_Std_Http_Body_Empty_tryRecv___redArg___closed__1_value;
static const lean_ctor_object l_Std_Http_Body_Empty_tryRecv___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_Empty_tryRecv___redArg___closed__1_value)}};
static const lean_object* l_Std_Http_Body_Empty_tryRecv___redArg___closed__2 = (const lean_object*)&l_Std_Http_Body_Empty_tryRecv___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_tryRecv___redArg();
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_tryRecv___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_tryRecv(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_tryRecv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Empty_recvSelector___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___lam__2___closed__0 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__3___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Body_Empty_recvSelector___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Empty_recvSelector___closed__0;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_EAsync_instMonadLiftBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___closed__1 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__1_value;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___closed__2 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__2_value;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___closed__3 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__3_value;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__2_value),((lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__3_value)} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___closed__4 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__4_value;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__4_value),((lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__1_value)} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___closed__5 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__5_value;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Empty_recvSelector___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___closed__6 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__6_value;
static lean_once_cell_t l_Std_Http_Body_Empty_recvSelector___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Empty_recvSelector___closed__7;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Empty_recvSelector___lam__3___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_Empty_tryRecv___redArg___closed__0_value)} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___closed__8 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__8_value;
static lean_once_cell_t l_Std_Http_Body_Empty_recvSelector___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Empty_recvSelector___closed__9;
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector(lean_object*);
static const lean_ctor_object l_Std_Http_Body_instEmpty___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Body_instEmpty___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Body_instEmpty___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_instEmpty___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Body_instEmpty___lam__0___closed__0_value)}};
static const lean_object* l_Std_Http_Body_instEmpty___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Body_instEmpty___lam__0___closed__1_value;
static const lean_ctor_object l_Std_Http_Body_instEmpty___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Body_instEmpty___lam__0___closed__1_value)}};
static const lean_object* l_Std_Http_Body_instEmpty___lam__0___closed__2 = (const lean_object*)&l_Std_Http_Body_instEmpty___lam__0___closed__2_value;
static const lean_ctor_object l_Std_Http_Body_instEmpty___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_instEmpty___lam__0___closed__2_value)}};
static const lean_object* l_Std_Http_Body_instEmpty___lam__0___closed__3 = (const lean_object*)&l_Std_Http_Body_instEmpty___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instEmpty___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instEmpty___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instEmpty___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instEmpty___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instEmpty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instEmpty___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instEmpty___closed__0 = (const lean_object*)&l_Std_Http_Body_instEmpty___closed__0_value;
static const lean_closure_object l_Std_Http_Body_instEmpty___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instEmpty___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instEmpty___closed__1 = (const lean_object*)&l_Std_Http_Body_instEmpty___closed__1_value;
static const lean_closure_object l_Std_Http_Body_instEmpty___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Empty_recv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instEmpty___closed__2 = (const lean_object*)&l_Std_Http_Body_instEmpty___closed__2_value;
static const lean_closure_object l_Std_Http_Body_instEmpty___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Empty_close___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instEmpty___closed__3 = (const lean_object*)&l_Std_Http_Body_instEmpty___closed__3_value;
static const lean_closure_object l_Std_Http_Body_instEmpty___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Empty_isClosed___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instEmpty___closed__4 = (const lean_object*)&l_Std_Http_Body_instEmpty___closed__4_value;
static const lean_closure_object l_Std_Http_Body_instEmpty___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Empty_recvSelector, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instEmpty___closed__5 = (const lean_object*)&l_Std_Http_Body_instEmpty___closed__5_value;
static const lean_closure_object l_Std_Http_Body_instEmpty___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Empty_tryRecv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instEmpty___closed__6 = (const lean_object*)&l_Std_Http_Body_instEmpty___closed__6_value;
static const lean_ctor_object l_Std_Http_Body_instEmpty___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_instEmpty___closed__2_value),((lean_object*)&l_Std_Http_Body_instEmpty___closed__3_value),((lean_object*)&l_Std_Http_Body_instEmpty___closed__4_value),((lean_object*)&l_Std_Http_Body_instEmpty___closed__5_value),((lean_object*)&l_Std_Http_Body_instEmpty___closed__6_value),((lean_object*)&l_Std_Http_Body_instEmpty___closed__0_value),((lean_object*)&l_Std_Http_Body_instEmpty___closed__1_value)}};
static const lean_object* l_Std_Http_Body_instEmpty___closed__7 = (const lean_object*)&l_Std_Http_Body_instEmpty___closed__7_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instEmpty = (const lean_object*)&l_Std_Http_Body_instEmpty___closed__7_value;
static const lean_closure_object l_Std_Http_Body_instCoeEmptyAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Any_ofBody, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Body_instEmpty___closed__7_value)} };
static const lean_object* l_Std_Http_Body_instCoeEmptyAny___closed__0 = (const lean_object*)&l_Std_Http_Body_instCoeEmptyAny___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instCoeEmptyAny = (const lean_object*)&l_Std_Http_Body_instCoeEmptyAny___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseEmptyAny___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instCoeResponseEmptyAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instCoeResponseEmptyAny___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_instEmpty___closed__7_value)} };
static const lean_object* l_Std_Http_Body_instCoeResponseEmptyAny___closed__0 = (const lean_object*)&l_Std_Http_Body_instCoeResponseEmptyAny___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instCoeResponseEmptyAny = (const lean_object*)&l_Std_Http_Body_instCoeResponseEmptyAny___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_instEmpty___closed__7_value)} };
static const lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__0 = (const lean_object*)&l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__0_value;
static const lean_closure_object l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__0_value)} };
static const lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__1 = (const lean_object*)&l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny = (const lean_object*)&l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__0_value)} };
static const lean_object* l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___closed__0 = (const lean_object*)&l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny = (const lean_object*)&l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_empty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_empty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_empty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_empty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_toCtorIdx(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
}
static lean_object* _init_l_Std_Http_Body_instInhabitedEmpty_default(void){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
}
static lean_object* _init_l_Std_Http_Body_instInhabitedEmpty(void){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_box(0);
return v___x_4_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Body_instBEqEmpty_beq(lean_object* v_x_5_, lean_object* v_y_6_){
_start:
{
uint8_t v___x_7_; 
v___x_7_ = 1;
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instBEqEmpty_beq___boxed(lean_object* v_x_8_, lean_object* v_y_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_Std_Http_Body_instBEqEmpty_beq(v_x_8_, v_y_9_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recv___redArg(){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = ((lean_object*)(l_Std_Http_Body_Empty_recv___redArg___closed__1));
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recv___redArg___boxed(lean_object* v_a_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Std_Http_Body_Empty_recv___redArg();
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recv(lean_object* v_x_22_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = ((lean_object*)(l_Std_Http_Body_Empty_recv___redArg___closed__1));
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recv___boxed(lean_object* v_x_25_, lean_object* v_a_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Std_Http_Body_Empty_recv(v_x_25_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_close___redArg(){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = ((lean_object*)(l_Std_Http_Body_Empty_close___redArg___closed__1));
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_close___redArg___boxed(lean_object* v_a_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Std_Http_Body_Empty_close___redArg();
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_close(lean_object* v_x_36_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = ((lean_object*)(l_Std_Http_Body_Empty_close___redArg___closed__1));
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_close___boxed(lean_object* v_x_39_, lean_object* v_a_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Std_Http_Body_Empty_close(v_x_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_isClosed___redArg(){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = ((lean_object*)(l_Std_Http_Body_Empty_isClosed___redArg___closed__1));
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_isClosed___redArg___boxed(lean_object* v_a_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Std_Http_Body_Empty_isClosed___redArg();
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_isClosed(lean_object* v_x_51_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = ((lean_object*)(l_Std_Http_Body_Empty_isClosed___redArg___closed__1));
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_isClosed___boxed(lean_object* v_x_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Std_Http_Body_Empty_isClosed(v_x_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_tryRecv___redArg(){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = ((lean_object*)(l_Std_Http_Body_Empty_tryRecv___redArg___closed__2));
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_tryRecv___redArg___boxed(lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Std_Http_Body_Empty_tryRecv___redArg();
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_tryRecv(lean_object* v_x_67_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = ((lean_object*)(l_Std_Http_Body_Empty_tryRecv___redArg___closed__2));
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_tryRecv___boxed(lean_object* v_x_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Std_Http_Body_Empty_tryRecv(v_x_70_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__0(lean_object* v___x_73_, lean_object* v_promise_74_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_76_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_73_);
v___x_77_ = lean_io_promise_resolve(v___x_76_, v_promise_74_);
v___x_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
v___x_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__0___boxed(lean_object* v___x_80_, lean_object* v_promise_81_, lean_object* v___y_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Std_Http_Body_Empty_recvSelector___lam__0(v___x_80_, v_promise_81_);
lean_dec(v_promise_81_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__1(lean_object* v___x_84_){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_86_, 0, v___x_84_);
v___x_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__1___boxed(lean_object* v___x_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Std_Http_Body_Empty_recvSelector___lam__1(v___x_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__2(lean_object* v___x_93_, lean_object* v___f_94_, lean_object* v_win_95_, lean_object* v_waiter_96_){
_start:
{
lean_object* v_lose_98_; lean_object* v___x_221__overap_99_; lean_object* v___x_100_; 
v_lose_98_ = ((lean_object*)(l_Std_Http_Body_Empty_recvSelector___lam__2___closed__0));
v___x_221__overap_99_ = l_Std_Internal_IO_Async_Waiter_race___redArg(v___x_93_, v___f_94_, v_waiter_96_, v_lose_98_, v_win_95_);
v___x_100_ = lean_apply_1(v___x_221__overap_99_, lean_box(0));
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__2___boxed(lean_object* v___x_101_, lean_object* v___f_102_, lean_object* v_win_103_, lean_object* v_waiter_104_, lean_object* v___y_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Std_Http_Body_Empty_recvSelector___lam__2(v___x_101_, v___f_102_, v_win_103_, v_waiter_104_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__3(lean_object* v___x_107_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_109_, 0, v___x_107_);
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__3___boxed(lean_object* v___x_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Std_Http_Body_Empty_recvSelector___lam__3(v___x_111_);
return v_res_113_;
}
}
static lean_object* _init_l_Std_Http_Body_Empty_recvSelector___closed__0(void){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Std_Internal_IO_Async_EAsync_instMonad(lean_box(0));
return v___x_114_;
}
}
static lean_object* _init_l_Std_Http_Body_Empty_recvSelector___closed__7(void){
_start:
{
lean_object* v_win_126_; lean_object* v___f_127_; lean_object* v___x_128_; lean_object* v___f_129_; 
v_win_126_ = ((lean_object*)(l_Std_Http_Body_Empty_recvSelector___closed__6));
v___f_127_ = ((lean_object*)(l_Std_Http_Body_Empty_recvSelector___closed__5));
v___x_128_ = lean_obj_once(&l_Std_Http_Body_Empty_recvSelector___closed__0, &l_Std_Http_Body_Empty_recvSelector___closed__0_once, _init_l_Std_Http_Body_Empty_recvSelector___closed__0);
v___f_129_ = lean_alloc_closure((void*)(l_Std_Http_Body_Empty_recvSelector___lam__2___boxed), 5, 3);
lean_closure_set(v___f_129_, 0, v___x_128_);
lean_closure_set(v___f_129_, 1, v___f_127_);
lean_closure_set(v___f_129_, 2, v_win_126_);
return v___f_129_;
}
}
static lean_object* _init_l_Std_Http_Body_Empty_recvSelector___closed__9(void){
_start:
{
lean_object* v___f_132_; lean_object* v___f_133_; lean_object* v___f_134_; lean_object* v___x_135_; 
v___f_132_ = ((lean_object*)(l_Std_Http_Body_Empty_recvSelector___lam__2___closed__0));
v___f_133_ = lean_obj_once(&l_Std_Http_Body_Empty_recvSelector___closed__7, &l_Std_Http_Body_Empty_recvSelector___closed__7_once, _init_l_Std_Http_Body_Empty_recvSelector___closed__7);
v___f_134_ = ((lean_object*)(l_Std_Http_Body_Empty_recvSelector___closed__8));
v___x_135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_135_, 0, v___f_134_);
lean_ctor_set(v___x_135_, 1, v___f_133_);
lean_ctor_set(v___x_135_, 2, v___f_132_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector(lean_object* v_x_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = lean_obj_once(&l_Std_Http_Body_Empty_recvSelector___closed__9, &l_Std_Http_Body_Empty_recvSelector___closed__9_once, _init_l_Std_Http_Body_Empty_recvSelector___closed__9);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instEmpty___lam__0(lean_object* v_x_146_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = ((lean_object*)(l_Std_Http_Body_instEmpty___lam__0___closed__3));
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instEmpty___lam__0___boxed(lean_object* v_x_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Std_Http_Body_instEmpty___lam__0(v_x_149_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instEmpty___lam__1(lean_object* v_x_152_, lean_object* v_x_153_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = ((lean_object*)(l_Std_Http_Body_Empty_close___redArg___closed__1));
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instEmpty___lam__1___boxed(lean_object* v_x_156_, lean_object* v_x_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Std_Http_Body_instEmpty___lam__1(v_x_156_, v_x_157_);
lean_dec(v_x_157_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseEmptyAny___lam__0(lean_object* v___x_179_, lean_object* v_f_180_){
_start:
{
lean_object* v_line_181_; lean_object* v_body_182_; lean_object* v_extensions_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_191_; 
v_line_181_ = lean_ctor_get(v_f_180_, 0);
v_body_182_ = lean_ctor_get(v_f_180_, 1);
v_extensions_183_ = lean_ctor_get(v_f_180_, 2);
v_isSharedCheck_191_ = !lean_is_exclusive(v_f_180_);
if (v_isSharedCheck_191_ == 0)
{
v___x_185_ = v_f_180_;
v_isShared_186_ = v_isSharedCheck_191_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_extensions_183_);
lean_inc(v_body_182_);
lean_inc(v_line_181_);
lean_dec(v_f_180_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_191_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_187_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_179_, v_body_182_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 1, v___x_187_);
v___x_189_ = v___x_185_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_line_181_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_190_, 2, v_extensions_183_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0(lean_object* v___x_195_, lean_object* v_x_196_){
_start:
{
if (lean_obj_tag(v_x_196_) == 0)
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_206_; 
lean_dec_ref(v___x_195_);
v_a_198_ = lean_ctor_get(v_x_196_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v_x_196_);
if (v_isSharedCheck_206_ == 0)
{
v___x_200_ = v_x_196_;
v_isShared_201_ = v_isSharedCheck_206_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v_x_196_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_206_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_198_);
v___x_203_ = v_reuseFailAlloc_205_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
lean_object* v___x_204_; 
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
}
else
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_226_; 
v_a_207_ = lean_ctor_get(v_x_196_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v_x_196_);
if (v_isSharedCheck_226_ == 0)
{
v___x_209_ = v_x_196_;
v_isShared_210_ = v_isSharedCheck_226_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v_x_196_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_226_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v_line_211_; lean_object* v_body_212_; lean_object* v_extensions_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_225_; 
v_line_211_ = lean_ctor_get(v_a_207_, 0);
v_body_212_ = lean_ctor_get(v_a_207_, 1);
v_extensions_213_ = lean_ctor_get(v_a_207_, 2);
v_isSharedCheck_225_ = !lean_is_exclusive(v_a_207_);
if (v_isSharedCheck_225_ == 0)
{
v___x_215_ = v_a_207_;
v_isShared_216_ = v_isSharedCheck_225_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_extensions_213_);
lean_inc(v_body_212_);
lean_inc(v_line_211_);
lean_dec(v_a_207_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_225_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; lean_object* v___x_219_; 
v___x_217_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_195_, v_body_212_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 1, v___x_217_);
v___x_219_ = v___x_215_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_line_211_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v___x_217_);
lean_ctor_set(v_reuseFailAlloc_224_, 2, v_extensions_213_);
v___x_219_ = v_reuseFailAlloc_224_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
lean_object* v___x_221_; 
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 0, v___x_219_);
v___x_221_ = v___x_209_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_223_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_222_; 
v___x_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
return v___x_222_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0___boxed(lean_object* v___x_227_, lean_object* v_x_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0(v___x_227_, v_x_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1(lean_object* v___f_231_, lean_object* v_action_232_, lean_object* v___y_233_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; uint8_t v___x_237_; lean_object* v___x_238_; 
lean_inc_ref(v___y_233_);
v___x_235_ = lean_apply_2(v_action_232_, v___y_233_, lean_box(0));
v___x_236_ = lean_unsigned_to_nat(0u);
v___x_237_ = 0;
v___x_238_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_236_, v___x_237_, v___x_235_, v___f_231_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1___boxed(lean_object* v___f_239_, lean_object* v_action_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1(v___f_239_, v_action_240_, v___y_241_);
lean_dec_ref(v___y_241_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1(lean_object* v___f_249_, lean_object* v_action_250_, lean_object* v___y_251_){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; lean_object* v___x_256_; 
v___x_253_ = lean_apply_1(v_action_250_, lean_box(0));
v___x_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = 0;
v___x_256_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_254_, v___x_255_, v___x_253_, v___f_249_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1___boxed(lean_object* v___f_257_, lean_object* v_action_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1(v___f_257_, v_action_258_, v___y_259_);
lean_dec_ref(v___y_259_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_empty(lean_object* v_builder_265_){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_267_ = lean_box(0);
v___x_268_ = l_Std_Http_Request_Builder_body___redArg(v_builder_265_, v___x_267_);
v___x_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
v___x_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_empty___boxed(lean_object* v_builder_271_, lean_object* v_a_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Std_Http_Request_Builder_empty(v_builder_271_);
lean_dec_ref(v_builder_271_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_empty(lean_object* v_builder_274_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_276_ = lean_box(0);
v___x_277_ = l_Std_Http_Response_Builder_body___redArg(v_builder_274_, v___x_276_);
v___x_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_empty___boxed(lean_object* v_builder_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Std_Http_Response_Builder_empty(v_builder_280_);
lean_dec_ref(v_builder_280_);
return v_res_282_;
}
}
lean_object* runtime_initialize_Std_Internal_Http_Data_Request(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Response(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Body_Any(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Http_Data_Body_Empty(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Internal_Http_Data_Request(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Response(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Body_Any(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_Body_instInhabitedEmpty_default = _init_l_Std_Http_Body_instInhabitedEmpty_default();
lean_mark_persistent(l_Std_Http_Body_instInhabitedEmpty_default);
l_Std_Http_Body_instInhabitedEmpty = _init_l_Std_Http_Body_instInhabitedEmpty();
lean_mark_persistent(l_Std_Http_Body_instInhabitedEmpty);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Http_Data_Body_Empty(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Http_Data_Request(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_Response(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_Body_Any(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Http_Data_Body_Empty(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Http_Data_Request(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_Response(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_Body_Any(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Body_Empty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Http_Data_Body_Empty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Http_Data_Body_Empty(builtin);
}
#ifdef __cplusplus
}
#endif
