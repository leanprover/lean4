// Lean compiler output
// Module: Std.Http.Data.Body.Empty
// Imports: public import Std.Http.Data.Request public import Std.Http.Data.Response public import Std.Http.Data.Body.Any
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
lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
lean_object* l_Std_Async_BaseAsync_lift___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* l_Std_Async_EAsync_instMonad___redArg();
lean_object* l_Std_Async_Waiter_race___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Any_ofReplayableBody___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Http_Request_Builder_body___redArg(lean_object*, lean_object*);
lean_object* l_Std_Http_Response_Builder_body___redArg(lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Any_ofReplayableBody(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instInhabitedEmpty_default;
LEAN_EXPORT lean_object* l_Std_Http_Body_instInhabitedEmpty;
LEAN_EXPORT uint8_t l_Std_Http_Body_instBEqEmpty_beq___redArg();
LEAN_EXPORT lean_object* l_Std_Http_Body_instBEqEmpty_beq___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Empty_recvSelector___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__2___closed__0 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___redArg___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__3___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Body_Empty_recvSelector___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___closed__0;
static lean_once_cell_t l_Std_Http_Body_Empty_recvSelector___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___closed__1;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_BaseAsync_lift___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___closed__2 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___redArg___closed__2_value;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___closed__3 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___redArg___closed__3_value;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___closed__4 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___redArg___closed__4_value;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_Body_Empty_recvSelector___redArg___closed__3_value),((lean_object*)&l_Std_Http_Body_Empty_recvSelector___redArg___closed__4_value)} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___closed__5 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___redArg___closed__5_value;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_Body_Empty_recvSelector___redArg___closed__5_value),((lean_object*)&l_Std_Http_Body_Empty_recvSelector___redArg___closed__2_value)} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___closed__6 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___redArg___closed__6_value;
static lean_once_cell_t l_Std_Http_Body_Empty_recvSelector___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___closed__7;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Empty_recvSelector___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___closed__8 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___redArg___closed__8_value;
static lean_once_cell_t l_Std_Http_Body_Empty_recvSelector___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___closed__9;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Empty_recvSelector___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_Empty_tryRecv___redArg___closed__0_value)} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___closed__10 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___redArg___closed__10_value;
static lean_once_cell_t l_Std_Http_Body_Empty_recvSelector___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___closed__11;
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg();
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Body_instReplayableEmpty___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instReplayableEmpty___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instReplayableEmpty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instReplayableEmpty___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instReplayableEmpty___closed__0 = (const lean_object*)&l_Std_Http_Body_instReplayableEmpty___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instReplayableEmpty = (const lean_object*)&l_Std_Http_Body_instReplayableEmpty___closed__0_value;
static const lean_closure_object l_Std_Http_Body_instCoeEmptyAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Any_ofReplayableBody, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Body_instEmpty___closed__7_value),((lean_object*)&l_Std_Http_Body_instReplayableEmpty___closed__0_value)} };
static const lean_object* l_Std_Http_Body_instCoeEmptyAny___closed__0 = (const lean_object*)&l_Std_Http_Body_instCoeEmptyAny___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instCoeEmptyAny = (const lean_object*)&l_Std_Http_Body_instCoeEmptyAny___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseEmptyAny___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instCoeResponseEmptyAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instCoeResponseEmptyAny___lam__0, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_Body_instEmpty___closed__7_value),((lean_object*)&l_Std_Http_Body_instReplayableEmpty___closed__0_value)} };
static const lean_object* l_Std_Http_Body_instCoeResponseEmptyAny___closed__0 = (const lean_object*)&l_Std_Http_Body_instCoeResponseEmptyAny___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instCoeResponseEmptyAny = (const lean_object*)&l_Std_Http_Body_instCoeResponseEmptyAny___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_Body_instEmpty___closed__7_value),((lean_object*)&l_Std_Http_Body_instReplayableEmpty___closed__0_value)} };
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
static lean_object* _init_l_Std_Http_Body_instInhabitedEmpty_default(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
static lean_object* _init_l_Std_Http_Body_instInhabitedEmpty(void){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Body_instBEqEmpty_beq___redArg(){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = 1;
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instBEqEmpty_beq___redArg___boxed(lean_object* v___dummy_5_){
_start:
{
uint8_t v_res_6_; lean_object* v_r_7_; 
v_res_6_ = l_Std_Http_Body_instBEqEmpty_beq___redArg();
v_r_7_ = lean_box(v_res_6_);
return v_r_7_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Body_instBEqEmpty_beq(lean_object* v_x_8_, lean_object* v_y_9_){
_start:
{
uint8_t v___x_10_; 
v___x_10_ = 1;
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instBEqEmpty_beq___boxed(lean_object* v_x_11_, lean_object* v_y_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Std_Http_Body_instBEqEmpty_beq(v_x_11_, v_y_12_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recv___redArg(){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = ((lean_object*)(l_Std_Http_Body_Empty_recv___redArg___closed__1));
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recv___redArg___boxed(lean_object* v_a_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_Http_Body_Empty_recv___redArg();
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recv(lean_object* v_x_25_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = ((lean_object*)(l_Std_Http_Body_Empty_recv___redArg___closed__1));
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recv___boxed(lean_object* v_x_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Std_Http_Body_Empty_recv(v_x_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_close___redArg(){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = ((lean_object*)(l_Std_Http_Body_Empty_close___redArg___closed__1));
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_close___redArg___boxed(lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Std_Http_Body_Empty_close___redArg();
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_close(lean_object* v_x_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = ((lean_object*)(l_Std_Http_Body_Empty_close___redArg___closed__1));
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_close___boxed(lean_object* v_x_42_, lean_object* v_a_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Std_Http_Body_Empty_close(v_x_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_isClosed___redArg(){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = ((lean_object*)(l_Std_Http_Body_Empty_isClosed___redArg___closed__1));
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_isClosed___redArg___boxed(lean_object* v_a_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Std_Http_Body_Empty_isClosed___redArg();
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_isClosed(lean_object* v_x_54_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = ((lean_object*)(l_Std_Http_Body_Empty_isClosed___redArg___closed__1));
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_isClosed___boxed(lean_object* v_x_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Std_Http_Body_Empty_isClosed(v_x_57_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_tryRecv___redArg(){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = ((lean_object*)(l_Std_Http_Body_Empty_tryRecv___redArg___closed__2));
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_tryRecv___redArg___boxed(lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Std_Http_Body_Empty_tryRecv___redArg();
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_tryRecv(lean_object* v_x_70_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = ((lean_object*)(l_Std_Http_Body_Empty_tryRecv___redArg___closed__2));
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_tryRecv___boxed(lean_object* v_x_73_, lean_object* v_a_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Std_Http_Body_Empty_tryRecv(v_x_73_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__0(lean_object* v___x_76_, lean_object* v_promise_77_){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_79_, 0, v___x_76_);
v___x_80_ = lean_io_promise_resolve(v___x_79_, v_promise_77_);
v___x_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__0___boxed(lean_object* v___x_83_, lean_object* v_promise_84_, lean_object* v___y_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_Http_Body_Empty_recvSelector___redArg___lam__0(v___x_83_, v_promise_84_);
lean_dec(v_promise_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__1(lean_object* v___x_87_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_89_, 0, v___x_87_);
v___x_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__1___boxed(lean_object* v___x_91_, lean_object* v___y_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Std_Http_Body_Empty_recvSelector___redArg___lam__1(v___x_91_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__2(lean_object* v___x_96_, lean_object* v___f_97_, lean_object* v_win_98_, lean_object* v_waiter_99_){
_start:
{
lean_object* v_lose_101_; lean_object* v___x_310__overap_102_; lean_object* v___x_103_; 
v_lose_101_ = ((lean_object*)(l_Std_Http_Body_Empty_recvSelector___redArg___lam__2___closed__0));
v___x_310__overap_102_ = l_Std_Async_Waiter_race___redArg(v___x_96_, v___f_97_, v_waiter_99_, v_lose_101_, v_win_98_);
v___x_103_ = lean_apply_1(v___x_310__overap_102_, lean_box(0));
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__2___boxed(lean_object* v___x_104_, lean_object* v___f_105_, lean_object* v_win_106_, lean_object* v_waiter_107_, lean_object* v___y_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Std_Http_Body_Empty_recvSelector___redArg___lam__2(v___x_104_, v___f_105_, v_win_106_, v_waiter_107_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__3(lean_object* v___x_110_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_110_);
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__3___boxed(lean_object* v___x_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Std_Http_Body_Empty_recvSelector___redArg___lam__3(v___x_114_);
return v_res_116_;
}
}
static lean_object* _init_l_Std_Http_Body_Empty_recvSelector___redArg___closed__0(void){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_117_;
}
}
static lean_object* _init_l_Std_Http_Body_Empty_recvSelector___redArg___closed__1(void){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
return v___x_118_;
}
}
static lean_object* _init_l_Std_Http_Body_Empty_recvSelector___redArg___closed__7(void){
_start:
{
lean_object* v___x_128_; lean_object* v___f_129_; lean_object* v___f_130_; 
v___x_128_ = lean_obj_once(&l_Std_Http_Body_Empty_recvSelector___redArg___closed__1, &l_Std_Http_Body_Empty_recvSelector___redArg___closed__1_once, _init_l_Std_Http_Body_Empty_recvSelector___redArg___closed__1);
v___f_129_ = ((lean_object*)(l_Std_Http_Body_Empty_recvSelector___redArg___closed__6));
v___f_130_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_130_, 0, v___f_129_);
lean_closure_set(v___f_130_, 1, v___x_128_);
return v___f_130_;
}
}
static lean_object* _init_l_Std_Http_Body_Empty_recvSelector___redArg___closed__9(void){
_start:
{
lean_object* v_win_133_; lean_object* v___f_134_; lean_object* v___x_135_; lean_object* v___f_136_; 
v_win_133_ = ((lean_object*)(l_Std_Http_Body_Empty_recvSelector___redArg___closed__8));
v___f_134_ = lean_obj_once(&l_Std_Http_Body_Empty_recvSelector___redArg___closed__7, &l_Std_Http_Body_Empty_recvSelector___redArg___closed__7_once, _init_l_Std_Http_Body_Empty_recvSelector___redArg___closed__7);
v___x_135_ = lean_obj_once(&l_Std_Http_Body_Empty_recvSelector___redArg___closed__0, &l_Std_Http_Body_Empty_recvSelector___redArg___closed__0_once, _init_l_Std_Http_Body_Empty_recvSelector___redArg___closed__0);
v___f_136_ = lean_alloc_closure((void*)(l_Std_Http_Body_Empty_recvSelector___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_136_, 0, v___x_135_);
lean_closure_set(v___f_136_, 1, v___f_134_);
lean_closure_set(v___f_136_, 2, v_win_133_);
return v___f_136_;
}
}
static lean_object* _init_l_Std_Http_Body_Empty_recvSelector___redArg___closed__11(void){
_start:
{
lean_object* v___f_139_; lean_object* v___f_140_; lean_object* v___f_141_; lean_object* v___x_142_; 
v___f_139_ = ((lean_object*)(l_Std_Http_Body_Empty_recvSelector___redArg___lam__2___closed__0));
v___f_140_ = lean_obj_once(&l_Std_Http_Body_Empty_recvSelector___redArg___closed__9, &l_Std_Http_Body_Empty_recvSelector___redArg___closed__9_once, _init_l_Std_Http_Body_Empty_recvSelector___redArg___closed__9);
v___f_141_ = ((lean_object*)(l_Std_Http_Body_Empty_recvSelector___redArg___closed__10));
v___x_142_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_142_, 0, v___f_141_);
lean_ctor_set(v___x_142_, 1, v___f_140_);
lean_ctor_set(v___x_142_, 2, v___f_139_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg(){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = lean_obj_once(&l_Std_Http_Body_Empty_recvSelector___redArg___closed__11, &l_Std_Http_Body_Empty_recvSelector___redArg___closed__11_once, _init_l_Std_Http_Body_Empty_recvSelector___redArg___closed__11);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___boxed(lean_object* v___dummy_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Std_Http_Body_Empty_recvSelector___redArg();
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector(lean_object* v_x_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = lean_obj_once(&l_Std_Http_Body_Empty_recvSelector___redArg___closed__11, &l_Std_Http_Body_Empty_recvSelector___redArg___closed__11_once, _init_l_Std_Http_Body_Empty_recvSelector___redArg___closed__11);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instEmpty___lam__0(lean_object* v_x_157_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = ((lean_object*)(l_Std_Http_Body_instEmpty___lam__0___closed__3));
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instEmpty___lam__0___boxed(lean_object* v_x_160_, lean_object* v___y_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Std_Http_Body_instEmpty___lam__0(v_x_160_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instEmpty___lam__1(lean_object* v_x_163_, lean_object* v_x_164_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = ((lean_object*)(l_Std_Http_Body_Empty_close___redArg___closed__1));
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instEmpty___lam__1___boxed(lean_object* v_x_167_, lean_object* v_x_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Std_Http_Body_instEmpty___lam__1(v_x_167_, v_x_168_);
lean_dec(v_x_168_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instReplayableEmpty___lam__0(lean_object* v_x_187_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = ((lean_object*)(l_Std_Http_Body_Empty_close___redArg___closed__1));
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instReplayableEmpty___lam__0___boxed(lean_object* v_x_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Std_Http_Body_instReplayableEmpty___lam__0(v_x_190_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseEmptyAny___lam__0(lean_object* v___x_199_, lean_object* v___f_200_, lean_object* v_f_201_){
_start:
{
lean_object* v_line_202_; lean_object* v_body_203_; lean_object* v_extensions_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_212_; 
v_line_202_ = lean_ctor_get(v_f_201_, 0);
v_body_203_ = lean_ctor_get(v_f_201_, 1);
v_extensions_204_ = lean_ctor_get(v_f_201_, 2);
v_isSharedCheck_212_ = !lean_is_exclusive(v_f_201_);
if (v_isSharedCheck_212_ == 0)
{
v___x_206_ = v_f_201_;
v_isShared_207_ = v_isSharedCheck_212_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_extensions_204_);
lean_inc(v_body_203_);
lean_inc(v_line_202_);
lean_dec(v_f_201_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_212_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_208_; lean_object* v___x_210_; 
v___x_208_ = l_Std_Http_Body_Any_ofReplayableBody___redArg(v___x_199_, v___f_200_, v_body_203_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 1, v___x_208_);
v___x_210_ = v___x_206_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_line_202_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_211_, 2, v_extensions_204_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0(lean_object* v___x_217_, lean_object* v___f_218_, lean_object* v_x_219_){
_start:
{
if (lean_obj_tag(v_x_219_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_229_; 
lean_dec_ref(v___f_218_);
lean_dec_ref(v___x_217_);
v_a_221_ = lean_ctor_get(v_x_219_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v_x_219_);
if (v_isSharedCheck_229_ == 0)
{
v___x_223_ = v_x_219_;
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v_x_219_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_221_);
v___x_226_ = v_reuseFailAlloc_228_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_227_; 
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
}
}
else
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_249_; 
v_a_230_ = lean_ctor_get(v_x_219_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v_x_219_);
if (v_isSharedCheck_249_ == 0)
{
v___x_232_ = v_x_219_;
v_isShared_233_ = v_isSharedCheck_249_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v_x_219_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_249_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v_line_234_; lean_object* v_body_235_; lean_object* v_extensions_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_248_; 
v_line_234_ = lean_ctor_get(v_a_230_, 0);
v_body_235_ = lean_ctor_get(v_a_230_, 1);
v_extensions_236_ = lean_ctor_get(v_a_230_, 2);
v_isSharedCheck_248_ = !lean_is_exclusive(v_a_230_);
if (v_isSharedCheck_248_ == 0)
{
v___x_238_ = v_a_230_;
v_isShared_239_ = v_isSharedCheck_248_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_extensions_236_);
lean_inc(v_body_235_);
lean_inc(v_line_234_);
lean_dec(v_a_230_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_248_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_240_ = l_Std_Http_Body_Any_ofReplayableBody___redArg(v___x_217_, v___f_218_, v_body_235_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v___x_240_);
v___x_242_ = v___x_238_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_line_234_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_247_, 2, v_extensions_236_);
v___x_242_ = v_reuseFailAlloc_247_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_244_; 
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_242_);
v___x_244_ = v___x_232_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_242_);
v___x_244_ = v_reuseFailAlloc_246_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_245_; 
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0___boxed(lean_object* v___x_250_, lean_object* v___f_251_, lean_object* v_x_252_, lean_object* v___y_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0(v___x_250_, v___f_251_, v_x_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1(lean_object* v___f_255_, lean_object* v_action_256_, lean_object* v___y_257_){
_start:
{
lean_object* v___x_259_; uint8_t v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_259_ = lean_unsigned_to_nat(0u);
v___x_260_ = 0;
lean_inc_ref(v___y_257_);
v___x_261_ = lean_apply_2(v_action_256_, v___y_257_, lean_box(0));
v___x_262_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_259_, v___x_260_, v___x_261_, v___f_255_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1___boxed(lean_object* v___f_263_, lean_object* v_action_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1(v___f_263_, v_action_264_, v___y_265_);
lean_dec_ref(v___y_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1(lean_object* v___f_274_, lean_object* v_action_275_, lean_object* v___y_276_){
_start:
{
lean_object* v___x_278_; uint8_t v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_278_ = lean_unsigned_to_nat(0u);
v___x_279_ = 0;
v___x_280_ = lean_apply_1(v_action_275_, lean_box(0));
v___x_281_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_278_, v___x_279_, v___x_280_, v___f_274_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1___boxed(lean_object* v___f_282_, lean_object* v_action_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1(v___f_282_, v_action_283_, v___y_284_);
lean_dec_ref(v___y_284_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_empty(lean_object* v_builder_290_){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_292_ = lean_box(0);
v___x_293_ = l_Std_Http_Request_Builder_body___redArg(v_builder_290_, v___x_292_);
v___x_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_empty___boxed(lean_object* v_builder_296_, lean_object* v_a_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Std_Http_Request_Builder_empty(v_builder_296_);
lean_dec_ref(v_builder_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_empty(lean_object* v_builder_299_){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_301_ = lean_box(0);
v___x_302_ = l_Std_Http_Response_Builder_body___redArg(v_builder_299_, v___x_301_);
v___x_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
v___x_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_empty___boxed(lean_object* v_builder_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Std_Http_Response_Builder_empty(v_builder_305_);
lean_dec_ref(v_builder_305_);
return v_res_307_;
}
}
lean_object* runtime_initialize_Std_Http_Data_Request(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Response(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Body_Any(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_Body_Empty(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Http_Data_Request(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Response(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Body_Any(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_Body_instInhabitedEmpty_default = _init_l_Std_Http_Body_instInhabitedEmpty_default();
lean_mark_persistent(l_Std_Http_Body_instInhabitedEmpty_default);
l_Std_Http_Body_instInhabitedEmpty = _init_l_Std_Http_Body_instInhabitedEmpty();
lean_mark_persistent(l_Std_Http_Body_instInhabitedEmpty);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Data_Body_Empty(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Http_Data_Request(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Response(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Body_Any(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Data_Body_Empty(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Http_Data_Request(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Response(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Body_Any(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Body_Empty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Data_Body_Empty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Data_Body_Empty(builtin);
}
#ifdef __cplusplus
}
#endif
