// Lean compiler output
// Module: Std.Internal.Async.Signal
// Imports: public import Std.Time public import Std.Internal.UV.Signal public import Std.Internal.Async.Select
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
uint32_t lean_int32_of_nat(lean_object*);
lean_object* lean_uv_signal_mk(uint32_t, uint8_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
uint8_t lean_io_get_task_state(lean_object*);
lean_object* l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_uv_signal_next(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_uv_signal_cancel(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_uv_signal_stop(lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sighup_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sighup_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sighup_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sighup_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigint_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigint_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigint_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigint_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigquit_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigquit_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigquit_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigquit_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigtrap_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigtrap_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigtrap_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigtrap_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigabrt_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigabrt_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigabrt_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigabrt_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigemt_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigemt_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigemt_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigemt_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigsys_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigsys_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigsys_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigsys_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigalrm_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigalrm_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigalrm_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigalrm_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigterm_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigterm_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigterm_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigterm_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigurg_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigurg_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigurg_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigurg_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigtstp_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigtstp_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigtstp_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigtstp_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigcont_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigcont_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigcont_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigcont_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigchld_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigchld_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigchld_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigchld_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigttin_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigttin_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigttin_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigttin_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigttou_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigttou_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigttou_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigttou_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigio_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigio_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigio_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigio_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigxcpu_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigxcpu_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigxcpu_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigxcpu_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigxfsz_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigxfsz_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigxfsz_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigxfsz_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigvtalrm_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigvtalrm_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigvtalrm_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigvtalrm_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigprof_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigprof_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigprof_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigprof_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigwinch_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigwinch_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigwinch_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigwinch_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_siginfo_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_siginfo_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_siginfo_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_siginfo_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigusr1_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigusr1_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigusr1_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigusr1_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigusr2_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigusr2_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigusr2_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigusr2_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Std.Internal.IO.Async.Signal.sighup"};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__0_value;
static const lean_ctor_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__0_value)}};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__1 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__1_value;
static const lean_string_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Std.Internal.IO.Async.Signal.sigint"};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__2 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__2_value;
static const lean_ctor_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__2_value)}};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__3 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__3_value;
static const lean_string_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Internal.IO.Async.Signal.sigquit"};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__4 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__4_value;
static const lean_ctor_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__4_value)}};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__5 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__5_value;
static const lean_string_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Internal.IO.Async.Signal.sigtrap"};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__6 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__6_value;
static const lean_ctor_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__6_value)}};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__7 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__7_value;
static const lean_string_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Internal.IO.Async.Signal.sigabrt"};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__8 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__8_value;
static const lean_ctor_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__8_value)}};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__9 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__9_value;
static const lean_string_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Std.Internal.IO.Async.Signal.sigemt"};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__10 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__10_value;
static const lean_ctor_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__10_value)}};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__11 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__11_value;
static const lean_string_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Std.Internal.IO.Async.Signal.sigsys"};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__12 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__12_value;
static const lean_ctor_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__12_value)}};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__13 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__13_value;
static const lean_string_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Internal.IO.Async.Signal.sigalrm"};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__14 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__14_value;
static const lean_ctor_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__14_value)}};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__15 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__15_value;
static const lean_string_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Internal.IO.Async.Signal.sigterm"};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__16 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__16_value;
static const lean_ctor_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__16_value)}};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__17 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__17_value;
static const lean_string_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Std.Internal.IO.Async.Signal.sigurg"};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__18 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__18_value;
static const lean_ctor_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__18_value)}};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__19 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__19_value;
static const lean_string_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Internal.IO.Async.Signal.sigtstp"};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__20 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__20_value;
static const lean_ctor_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__20_value)}};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__21 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__21_value;
static const lean_string_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Internal.IO.Async.Signal.sigcont"};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__22 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__22_value;
static const lean_ctor_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__22_value)}};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__23 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__23_value;
static const lean_string_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Internal.IO.Async.Signal.sigchld"};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__24 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__24_value;
static const lean_ctor_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__24_value)}};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__25 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__25_value;
static const lean_string_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Internal.IO.Async.Signal.sigttin"};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__26 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__26_value;
static const lean_ctor_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__26_value)}};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__27 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__27_value;
static const lean_string_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Internal.IO.Async.Signal.sigttou"};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__28 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__28_value;
static const lean_ctor_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__28_value)}};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__29 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__29_value;
static const lean_string_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Std.Internal.IO.Async.Signal.sigio"};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__30 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__30_value;
static const lean_ctor_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__30_value)}};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__31 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__31_value;
static const lean_string_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Internal.IO.Async.Signal.sigxcpu"};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__32 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__32_value;
static const lean_ctor_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__32_value)}};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__33 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__33_value;
static const lean_string_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Internal.IO.Async.Signal.sigxfsz"};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__34 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__34_value;
static const lean_ctor_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__34_value)}};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__35 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__35_value;
static const lean_string_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Std.Internal.IO.Async.Signal.sigvtalrm"};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__36 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__36_value;
static const lean_ctor_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__36_value)}};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__37 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__37_value;
static const lean_string_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Internal.IO.Async.Signal.sigprof"};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__38 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__38_value;
static const lean_ctor_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__38_value)}};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__39 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__39_value;
static const lean_string_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Std.Internal.IO.Async.Signal.sigwinch"};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__40 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__40_value;
static const lean_ctor_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__40_value)}};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__41 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__41_value;
static const lean_string_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Internal.IO.Async.Signal.siginfo"};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__42 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__42_value;
static const lean_ctor_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__42_value)}};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__43 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__43_value;
static const lean_string_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Internal.IO.Async.Signal.sigusr1"};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__44 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__44_value;
static const lean_ctor_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__44_value)}};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__45 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__45_value;
static const lean_string_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Internal.IO.Async.Signal.sigusr2"};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__46 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__46_value;
static const lean_ctor_object l_Std_Internal_IO_Async_instReprSignal_repr___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__46_value)}};
static const lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__47 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal_repr___closed__47_value;
static lean_once_cell_t l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__48;
static lean_once_cell_t l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__49;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_instReprSignal_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_IO_Async_instReprSignal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_instReprSignal_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_IO_Async_instReprSignal___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Internal_IO_Async_instReprSignal = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Internal_IO_Async_Signal_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_IO_Async_instDecidableEqSignal(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_instDecidableEqSignal___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_IO_Async_instBEqSignal_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_instBEqSignal_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_IO_Async_instBEqSignal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_instBEqSignal_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_IO_Async_instBEqSignal___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_instBEqSignal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Internal_IO_Async_instBEqSignal = (const lean_object*)&l_Std_Internal_IO_Async_instBEqSignal___closed__0_value;
static lean_once_cell_t l_Std_Internal_IO_Async_Signal_toInt32___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Std_Internal_IO_Async_Signal_toInt32___closed__0;
static lean_once_cell_t l_Std_Internal_IO_Async_Signal_toInt32___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Std_Internal_IO_Async_Signal_toInt32___closed__1;
static lean_once_cell_t l_Std_Internal_IO_Async_Signal_toInt32___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Std_Internal_IO_Async_Signal_toInt32___closed__2;
static lean_once_cell_t l_Std_Internal_IO_Async_Signal_toInt32___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Std_Internal_IO_Async_Signal_toInt32___closed__3;
static lean_once_cell_t l_Std_Internal_IO_Async_Signal_toInt32___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Std_Internal_IO_Async_Signal_toInt32___closed__4;
static lean_once_cell_t l_Std_Internal_IO_Async_Signal_toInt32___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Std_Internal_IO_Async_Signal_toInt32___closed__5;
static lean_once_cell_t l_Std_Internal_IO_Async_Signal_toInt32___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Std_Internal_IO_Async_Signal_toInt32___closed__6;
static lean_once_cell_t l_Std_Internal_IO_Async_Signal_toInt32___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Std_Internal_IO_Async_Signal_toInt32___closed__7;
static lean_once_cell_t l_Std_Internal_IO_Async_Signal_toInt32___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Std_Internal_IO_Async_Signal_toInt32___closed__8;
static lean_once_cell_t l_Std_Internal_IO_Async_Signal_toInt32___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Std_Internal_IO_Async_Signal_toInt32___closed__9;
static lean_once_cell_t l_Std_Internal_IO_Async_Signal_toInt32___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Std_Internal_IO_Async_Signal_toInt32___closed__10;
static lean_once_cell_t l_Std_Internal_IO_Async_Signal_toInt32___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Std_Internal_IO_Async_Signal_toInt32___closed__11;
static lean_once_cell_t l_Std_Internal_IO_Async_Signal_toInt32___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Std_Internal_IO_Async_Signal_toInt32___closed__12;
static lean_once_cell_t l_Std_Internal_IO_Async_Signal_toInt32___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Std_Internal_IO_Async_Signal_toInt32___closed__13;
static lean_once_cell_t l_Std_Internal_IO_Async_Signal_toInt32___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Std_Internal_IO_Async_Signal_toInt32___closed__14;
static lean_once_cell_t l_Std_Internal_IO_Async_Signal_toInt32___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Std_Internal_IO_Async_Signal_toInt32___closed__15;
static lean_once_cell_t l_Std_Internal_IO_Async_Signal_toInt32___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Std_Internal_IO_Async_Signal_toInt32___closed__16;
static lean_once_cell_t l_Std_Internal_IO_Async_Signal_toInt32___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Std_Internal_IO_Async_Signal_toInt32___closed__17;
static lean_once_cell_t l_Std_Internal_IO_Async_Signal_toInt32___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Std_Internal_IO_Async_Signal_toInt32___closed__18;
static lean_once_cell_t l_Std_Internal_IO_Async_Signal_toInt32___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Std_Internal_IO_Async_Signal_toInt32___closed__19;
static lean_once_cell_t l_Std_Internal_IO_Async_Signal_toInt32___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Std_Internal_IO_Async_Signal_toInt32___closed__20;
static lean_once_cell_t l_Std_Internal_IO_Async_Signal_toInt32___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Std_Internal_IO_Async_Signal_toInt32___closed__21;
static lean_once_cell_t l_Std_Internal_IO_Async_Signal_toInt32___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Std_Internal_IO_Async_Signal_toInt32___closed__22;
static lean_once_cell_t l_Std_Internal_IO_Async_Signal_toInt32___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Std_Internal_IO_Async_Signal_toInt32___closed__23;
LEAN_EXPORT uint32_t l_Std_Internal_IO_Async_Signal_toInt32(uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_toInt32___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_mk(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_mk___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_wait___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_IO_Async_Signal_Waiter_wait___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "the promise linked to the Async Task was dropped"};
static const lean_object* l_Std_Internal_IO_Async_Signal_Waiter_wait___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Signal_Waiter_wait___closed__0_value;
static const lean_closure_object l_Std_Internal_IO_Async_Signal_Waiter_wait___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_Signal_Waiter_wait___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Signal_Waiter_wait___closed__0_value)} };
static const lean_object* l_Std_Internal_IO_Async_Signal_Waiter_wait___closed__1 = (const lean_object*)&l_Std_Internal_IO_Async_Signal_Waiter_wait___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_wait(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_wait___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_stop(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_stop___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Signal_Waiter_selector_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Signal_Waiter_selector_spec__0___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Signal_Waiter_selector_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Signal_Waiter_selector_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Signal_Waiter_selector_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__1___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__1___closed__0_value;
static const lean_ctor_object l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__1___closed__0_value)}};
static const lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__1___closed__1 = (const lean_object*)&l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__2___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__2___closed__0_value;
static const lean_ctor_object l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__2___closed__0_value)}};
static const lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__2___closed__1 = (const lean_object*)&l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__2___closed__1_value;
static const lean_ctor_object l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__2___closed__1_value)}};
static const lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__2___closed__2 = (const lean_object*)&l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__2___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__5(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__8(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__8___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__8___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__9___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__9___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__9___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Signal_Waiter_selector_spec__0___closed__0_value)}};
static const lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__10___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__10___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_IO_Async_Signal_Waiter_selector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Signal_Waiter_selector___closed__0_value;
static const lean_closure_object l_Std_Internal_IO_Async_Signal_Waiter_selector___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__3, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___closed__1 = (const lean_object*)&l_Std_Internal_IO_Async_Signal_Waiter_selector___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
case 4:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
case 5:
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
case 6:
{
lean_object* v___x_8_; 
v___x_8_ = lean_unsigned_to_nat(6u);
return v___x_8_;
}
case 7:
{
lean_object* v___x_9_; 
v___x_9_ = lean_unsigned_to_nat(7u);
return v___x_9_;
}
case 8:
{
lean_object* v___x_10_; 
v___x_10_ = lean_unsigned_to_nat(8u);
return v___x_10_;
}
case 9:
{
lean_object* v___x_11_; 
v___x_11_ = lean_unsigned_to_nat(9u);
return v___x_11_;
}
case 10:
{
lean_object* v___x_12_; 
v___x_12_ = lean_unsigned_to_nat(10u);
return v___x_12_;
}
case 11:
{
lean_object* v___x_13_; 
v___x_13_ = lean_unsigned_to_nat(11u);
return v___x_13_;
}
case 12:
{
lean_object* v___x_14_; 
v___x_14_ = lean_unsigned_to_nat(12u);
return v___x_14_;
}
case 13:
{
lean_object* v___x_15_; 
v___x_15_ = lean_unsigned_to_nat(13u);
return v___x_15_;
}
case 14:
{
lean_object* v___x_16_; 
v___x_16_ = lean_unsigned_to_nat(14u);
return v___x_16_;
}
case 15:
{
lean_object* v___x_17_; 
v___x_17_ = lean_unsigned_to_nat(15u);
return v___x_17_;
}
case 16:
{
lean_object* v___x_18_; 
v___x_18_ = lean_unsigned_to_nat(16u);
return v___x_18_;
}
case 17:
{
lean_object* v___x_19_; 
v___x_19_ = lean_unsigned_to_nat(17u);
return v___x_19_;
}
case 18:
{
lean_object* v___x_20_; 
v___x_20_ = lean_unsigned_to_nat(18u);
return v___x_20_;
}
case 19:
{
lean_object* v___x_21_; 
v___x_21_ = lean_unsigned_to_nat(19u);
return v___x_21_;
}
case 20:
{
lean_object* v___x_22_; 
v___x_22_ = lean_unsigned_to_nat(20u);
return v___x_22_;
}
case 21:
{
lean_object* v___x_23_; 
v___x_23_ = lean_unsigned_to_nat(21u);
return v___x_23_;
}
case 22:
{
lean_object* v___x_24_; 
v___x_24_ = lean_unsigned_to_nat(22u);
return v___x_24_;
}
default: 
{
lean_object* v___x_25_; 
v___x_25_ = lean_unsigned_to_nat(23u);
return v___x_25_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_ctorIdx___boxed(lean_object* v_x_26_){
_start:
{
uint8_t v_x_boxed_27_; lean_object* v_res_28_; 
v_x_boxed_27_ = lean_unbox(v_x_26_);
v_res_28_ = l_Std_Internal_IO_Async_Signal_ctorIdx(v_x_boxed_27_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_toCtorIdx(uint8_t v_x_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Std_Internal_IO_Async_Signal_ctorIdx(v_x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_toCtorIdx___boxed(lean_object* v_x_31_){
_start:
{
uint8_t v_x_4__boxed_32_; lean_object* v_res_33_; 
v_x_4__boxed_32_ = lean_unbox(v_x_31_);
v_res_33_ = l_Std_Internal_IO_Async_Signal_toCtorIdx(v_x_4__boxed_32_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_ctorElim___redArg(lean_object* v_k_34_){
_start:
{
lean_inc(v_k_34_);
return v_k_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_ctorElim___redArg___boxed(lean_object* v_k_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Std_Internal_IO_Async_Signal_ctorElim___redArg(v_k_35_);
lean_dec(v_k_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_ctorElim(lean_object* v_motive_37_, lean_object* v_ctorIdx_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_k_41_){
_start:
{
lean_inc(v_k_41_);
return v_k_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_ctorElim___boxed(lean_object* v_motive_42_, lean_object* v_ctorIdx_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_k_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Std_Internal_IO_Async_Signal_ctorElim(v_motive_42_, v_ctorIdx_43_, v_t_boxed_47_, v_h_45_, v_k_46_);
lean_dec(v_k_46_);
lean_dec(v_ctorIdx_43_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sighup_elim___redArg(lean_object* v_sighup_49_){
_start:
{
lean_inc(v_sighup_49_);
return v_sighup_49_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sighup_elim___redArg___boxed(lean_object* v_sighup_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Std_Internal_IO_Async_Signal_sighup_elim___redArg(v_sighup_50_);
lean_dec(v_sighup_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sighup_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_sighup_55_){
_start:
{
lean_inc(v_sighup_55_);
return v_sighup_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sighup_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_sighup_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Std_Internal_IO_Async_Signal_sighup_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_sighup_59_);
lean_dec(v_sighup_59_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigint_elim___redArg(lean_object* v_sigint_62_){
_start:
{
lean_inc(v_sigint_62_);
return v_sigint_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigint_elim___redArg___boxed(lean_object* v_sigint_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Std_Internal_IO_Async_Signal_sigint_elim___redArg(v_sigint_63_);
lean_dec(v_sigint_63_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigint_elim(lean_object* v_motive_65_, uint8_t v_t_66_, lean_object* v_h_67_, lean_object* v_sigint_68_){
_start:
{
lean_inc(v_sigint_68_);
return v_sigint_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigint_elim___boxed(lean_object* v_motive_69_, lean_object* v_t_70_, lean_object* v_h_71_, lean_object* v_sigint_72_){
_start:
{
uint8_t v_t_boxed_73_; lean_object* v_res_74_; 
v_t_boxed_73_ = lean_unbox(v_t_70_);
v_res_74_ = l_Std_Internal_IO_Async_Signal_sigint_elim(v_motive_69_, v_t_boxed_73_, v_h_71_, v_sigint_72_);
lean_dec(v_sigint_72_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigquit_elim___redArg(lean_object* v_sigquit_75_){
_start:
{
lean_inc(v_sigquit_75_);
return v_sigquit_75_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigquit_elim___redArg___boxed(lean_object* v_sigquit_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Std_Internal_IO_Async_Signal_sigquit_elim___redArg(v_sigquit_76_);
lean_dec(v_sigquit_76_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigquit_elim(lean_object* v_motive_78_, uint8_t v_t_79_, lean_object* v_h_80_, lean_object* v_sigquit_81_){
_start:
{
lean_inc(v_sigquit_81_);
return v_sigquit_81_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigquit_elim___boxed(lean_object* v_motive_82_, lean_object* v_t_83_, lean_object* v_h_84_, lean_object* v_sigquit_85_){
_start:
{
uint8_t v_t_boxed_86_; lean_object* v_res_87_; 
v_t_boxed_86_ = lean_unbox(v_t_83_);
v_res_87_ = l_Std_Internal_IO_Async_Signal_sigquit_elim(v_motive_82_, v_t_boxed_86_, v_h_84_, v_sigquit_85_);
lean_dec(v_sigquit_85_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigtrap_elim___redArg(lean_object* v_sigtrap_88_){
_start:
{
lean_inc(v_sigtrap_88_);
return v_sigtrap_88_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigtrap_elim___redArg___boxed(lean_object* v_sigtrap_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Std_Internal_IO_Async_Signal_sigtrap_elim___redArg(v_sigtrap_89_);
lean_dec(v_sigtrap_89_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigtrap_elim(lean_object* v_motive_91_, uint8_t v_t_92_, lean_object* v_h_93_, lean_object* v_sigtrap_94_){
_start:
{
lean_inc(v_sigtrap_94_);
return v_sigtrap_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigtrap_elim___boxed(lean_object* v_motive_95_, lean_object* v_t_96_, lean_object* v_h_97_, lean_object* v_sigtrap_98_){
_start:
{
uint8_t v_t_boxed_99_; lean_object* v_res_100_; 
v_t_boxed_99_ = lean_unbox(v_t_96_);
v_res_100_ = l_Std_Internal_IO_Async_Signal_sigtrap_elim(v_motive_95_, v_t_boxed_99_, v_h_97_, v_sigtrap_98_);
lean_dec(v_sigtrap_98_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigabrt_elim___redArg(lean_object* v_sigabrt_101_){
_start:
{
lean_inc(v_sigabrt_101_);
return v_sigabrt_101_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigabrt_elim___redArg___boxed(lean_object* v_sigabrt_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Std_Internal_IO_Async_Signal_sigabrt_elim___redArg(v_sigabrt_102_);
lean_dec(v_sigabrt_102_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigabrt_elim(lean_object* v_motive_104_, uint8_t v_t_105_, lean_object* v_h_106_, lean_object* v_sigabrt_107_){
_start:
{
lean_inc(v_sigabrt_107_);
return v_sigabrt_107_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigabrt_elim___boxed(lean_object* v_motive_108_, lean_object* v_t_109_, lean_object* v_h_110_, lean_object* v_sigabrt_111_){
_start:
{
uint8_t v_t_boxed_112_; lean_object* v_res_113_; 
v_t_boxed_112_ = lean_unbox(v_t_109_);
v_res_113_ = l_Std_Internal_IO_Async_Signal_sigabrt_elim(v_motive_108_, v_t_boxed_112_, v_h_110_, v_sigabrt_111_);
lean_dec(v_sigabrt_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigemt_elim___redArg(lean_object* v_sigemt_114_){
_start:
{
lean_inc(v_sigemt_114_);
return v_sigemt_114_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigemt_elim___redArg___boxed(lean_object* v_sigemt_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Std_Internal_IO_Async_Signal_sigemt_elim___redArg(v_sigemt_115_);
lean_dec(v_sigemt_115_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigemt_elim(lean_object* v_motive_117_, uint8_t v_t_118_, lean_object* v_h_119_, lean_object* v_sigemt_120_){
_start:
{
lean_inc(v_sigemt_120_);
return v_sigemt_120_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigemt_elim___boxed(lean_object* v_motive_121_, lean_object* v_t_122_, lean_object* v_h_123_, lean_object* v_sigemt_124_){
_start:
{
uint8_t v_t_boxed_125_; lean_object* v_res_126_; 
v_t_boxed_125_ = lean_unbox(v_t_122_);
v_res_126_ = l_Std_Internal_IO_Async_Signal_sigemt_elim(v_motive_121_, v_t_boxed_125_, v_h_123_, v_sigemt_124_);
lean_dec(v_sigemt_124_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigsys_elim___redArg(lean_object* v_sigsys_127_){
_start:
{
lean_inc(v_sigsys_127_);
return v_sigsys_127_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigsys_elim___redArg___boxed(lean_object* v_sigsys_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Std_Internal_IO_Async_Signal_sigsys_elim___redArg(v_sigsys_128_);
lean_dec(v_sigsys_128_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigsys_elim(lean_object* v_motive_130_, uint8_t v_t_131_, lean_object* v_h_132_, lean_object* v_sigsys_133_){
_start:
{
lean_inc(v_sigsys_133_);
return v_sigsys_133_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigsys_elim___boxed(lean_object* v_motive_134_, lean_object* v_t_135_, lean_object* v_h_136_, lean_object* v_sigsys_137_){
_start:
{
uint8_t v_t_boxed_138_; lean_object* v_res_139_; 
v_t_boxed_138_ = lean_unbox(v_t_135_);
v_res_139_ = l_Std_Internal_IO_Async_Signal_sigsys_elim(v_motive_134_, v_t_boxed_138_, v_h_136_, v_sigsys_137_);
lean_dec(v_sigsys_137_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigalrm_elim___redArg(lean_object* v_sigalrm_140_){
_start:
{
lean_inc(v_sigalrm_140_);
return v_sigalrm_140_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigalrm_elim___redArg___boxed(lean_object* v_sigalrm_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Std_Internal_IO_Async_Signal_sigalrm_elim___redArg(v_sigalrm_141_);
lean_dec(v_sigalrm_141_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigalrm_elim(lean_object* v_motive_143_, uint8_t v_t_144_, lean_object* v_h_145_, lean_object* v_sigalrm_146_){
_start:
{
lean_inc(v_sigalrm_146_);
return v_sigalrm_146_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigalrm_elim___boxed(lean_object* v_motive_147_, lean_object* v_t_148_, lean_object* v_h_149_, lean_object* v_sigalrm_150_){
_start:
{
uint8_t v_t_boxed_151_; lean_object* v_res_152_; 
v_t_boxed_151_ = lean_unbox(v_t_148_);
v_res_152_ = l_Std_Internal_IO_Async_Signal_sigalrm_elim(v_motive_147_, v_t_boxed_151_, v_h_149_, v_sigalrm_150_);
lean_dec(v_sigalrm_150_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigterm_elim___redArg(lean_object* v_sigterm_153_){
_start:
{
lean_inc(v_sigterm_153_);
return v_sigterm_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigterm_elim___redArg___boxed(lean_object* v_sigterm_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Std_Internal_IO_Async_Signal_sigterm_elim___redArg(v_sigterm_154_);
lean_dec(v_sigterm_154_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigterm_elim(lean_object* v_motive_156_, uint8_t v_t_157_, lean_object* v_h_158_, lean_object* v_sigterm_159_){
_start:
{
lean_inc(v_sigterm_159_);
return v_sigterm_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigterm_elim___boxed(lean_object* v_motive_160_, lean_object* v_t_161_, lean_object* v_h_162_, lean_object* v_sigterm_163_){
_start:
{
uint8_t v_t_boxed_164_; lean_object* v_res_165_; 
v_t_boxed_164_ = lean_unbox(v_t_161_);
v_res_165_ = l_Std_Internal_IO_Async_Signal_sigterm_elim(v_motive_160_, v_t_boxed_164_, v_h_162_, v_sigterm_163_);
lean_dec(v_sigterm_163_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigurg_elim___redArg(lean_object* v_sigurg_166_){
_start:
{
lean_inc(v_sigurg_166_);
return v_sigurg_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigurg_elim___redArg___boxed(lean_object* v_sigurg_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Std_Internal_IO_Async_Signal_sigurg_elim___redArg(v_sigurg_167_);
lean_dec(v_sigurg_167_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigurg_elim(lean_object* v_motive_169_, uint8_t v_t_170_, lean_object* v_h_171_, lean_object* v_sigurg_172_){
_start:
{
lean_inc(v_sigurg_172_);
return v_sigurg_172_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigurg_elim___boxed(lean_object* v_motive_173_, lean_object* v_t_174_, lean_object* v_h_175_, lean_object* v_sigurg_176_){
_start:
{
uint8_t v_t_boxed_177_; lean_object* v_res_178_; 
v_t_boxed_177_ = lean_unbox(v_t_174_);
v_res_178_ = l_Std_Internal_IO_Async_Signal_sigurg_elim(v_motive_173_, v_t_boxed_177_, v_h_175_, v_sigurg_176_);
lean_dec(v_sigurg_176_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigtstp_elim___redArg(lean_object* v_sigtstp_179_){
_start:
{
lean_inc(v_sigtstp_179_);
return v_sigtstp_179_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigtstp_elim___redArg___boxed(lean_object* v_sigtstp_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Std_Internal_IO_Async_Signal_sigtstp_elim___redArg(v_sigtstp_180_);
lean_dec(v_sigtstp_180_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigtstp_elim(lean_object* v_motive_182_, uint8_t v_t_183_, lean_object* v_h_184_, lean_object* v_sigtstp_185_){
_start:
{
lean_inc(v_sigtstp_185_);
return v_sigtstp_185_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigtstp_elim___boxed(lean_object* v_motive_186_, lean_object* v_t_187_, lean_object* v_h_188_, lean_object* v_sigtstp_189_){
_start:
{
uint8_t v_t_boxed_190_; lean_object* v_res_191_; 
v_t_boxed_190_ = lean_unbox(v_t_187_);
v_res_191_ = l_Std_Internal_IO_Async_Signal_sigtstp_elim(v_motive_186_, v_t_boxed_190_, v_h_188_, v_sigtstp_189_);
lean_dec(v_sigtstp_189_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigcont_elim___redArg(lean_object* v_sigcont_192_){
_start:
{
lean_inc(v_sigcont_192_);
return v_sigcont_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigcont_elim___redArg___boxed(lean_object* v_sigcont_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Std_Internal_IO_Async_Signal_sigcont_elim___redArg(v_sigcont_193_);
lean_dec(v_sigcont_193_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigcont_elim(lean_object* v_motive_195_, uint8_t v_t_196_, lean_object* v_h_197_, lean_object* v_sigcont_198_){
_start:
{
lean_inc(v_sigcont_198_);
return v_sigcont_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigcont_elim___boxed(lean_object* v_motive_199_, lean_object* v_t_200_, lean_object* v_h_201_, lean_object* v_sigcont_202_){
_start:
{
uint8_t v_t_boxed_203_; lean_object* v_res_204_; 
v_t_boxed_203_ = lean_unbox(v_t_200_);
v_res_204_ = l_Std_Internal_IO_Async_Signal_sigcont_elim(v_motive_199_, v_t_boxed_203_, v_h_201_, v_sigcont_202_);
lean_dec(v_sigcont_202_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigchld_elim___redArg(lean_object* v_sigchld_205_){
_start:
{
lean_inc(v_sigchld_205_);
return v_sigchld_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigchld_elim___redArg___boxed(lean_object* v_sigchld_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Std_Internal_IO_Async_Signal_sigchld_elim___redArg(v_sigchld_206_);
lean_dec(v_sigchld_206_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigchld_elim(lean_object* v_motive_208_, uint8_t v_t_209_, lean_object* v_h_210_, lean_object* v_sigchld_211_){
_start:
{
lean_inc(v_sigchld_211_);
return v_sigchld_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigchld_elim___boxed(lean_object* v_motive_212_, lean_object* v_t_213_, lean_object* v_h_214_, lean_object* v_sigchld_215_){
_start:
{
uint8_t v_t_boxed_216_; lean_object* v_res_217_; 
v_t_boxed_216_ = lean_unbox(v_t_213_);
v_res_217_ = l_Std_Internal_IO_Async_Signal_sigchld_elim(v_motive_212_, v_t_boxed_216_, v_h_214_, v_sigchld_215_);
lean_dec(v_sigchld_215_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigttin_elim___redArg(lean_object* v_sigttin_218_){
_start:
{
lean_inc(v_sigttin_218_);
return v_sigttin_218_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigttin_elim___redArg___boxed(lean_object* v_sigttin_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Std_Internal_IO_Async_Signal_sigttin_elim___redArg(v_sigttin_219_);
lean_dec(v_sigttin_219_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigttin_elim(lean_object* v_motive_221_, uint8_t v_t_222_, lean_object* v_h_223_, lean_object* v_sigttin_224_){
_start:
{
lean_inc(v_sigttin_224_);
return v_sigttin_224_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigttin_elim___boxed(lean_object* v_motive_225_, lean_object* v_t_226_, lean_object* v_h_227_, lean_object* v_sigttin_228_){
_start:
{
uint8_t v_t_boxed_229_; lean_object* v_res_230_; 
v_t_boxed_229_ = lean_unbox(v_t_226_);
v_res_230_ = l_Std_Internal_IO_Async_Signal_sigttin_elim(v_motive_225_, v_t_boxed_229_, v_h_227_, v_sigttin_228_);
lean_dec(v_sigttin_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigttou_elim___redArg(lean_object* v_sigttou_231_){
_start:
{
lean_inc(v_sigttou_231_);
return v_sigttou_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigttou_elim___redArg___boxed(lean_object* v_sigttou_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Std_Internal_IO_Async_Signal_sigttou_elim___redArg(v_sigttou_232_);
lean_dec(v_sigttou_232_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigttou_elim(lean_object* v_motive_234_, uint8_t v_t_235_, lean_object* v_h_236_, lean_object* v_sigttou_237_){
_start:
{
lean_inc(v_sigttou_237_);
return v_sigttou_237_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigttou_elim___boxed(lean_object* v_motive_238_, lean_object* v_t_239_, lean_object* v_h_240_, lean_object* v_sigttou_241_){
_start:
{
uint8_t v_t_boxed_242_; lean_object* v_res_243_; 
v_t_boxed_242_ = lean_unbox(v_t_239_);
v_res_243_ = l_Std_Internal_IO_Async_Signal_sigttou_elim(v_motive_238_, v_t_boxed_242_, v_h_240_, v_sigttou_241_);
lean_dec(v_sigttou_241_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigio_elim___redArg(lean_object* v_sigio_244_){
_start:
{
lean_inc(v_sigio_244_);
return v_sigio_244_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigio_elim___redArg___boxed(lean_object* v_sigio_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Std_Internal_IO_Async_Signal_sigio_elim___redArg(v_sigio_245_);
lean_dec(v_sigio_245_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigio_elim(lean_object* v_motive_247_, uint8_t v_t_248_, lean_object* v_h_249_, lean_object* v_sigio_250_){
_start:
{
lean_inc(v_sigio_250_);
return v_sigio_250_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigio_elim___boxed(lean_object* v_motive_251_, lean_object* v_t_252_, lean_object* v_h_253_, lean_object* v_sigio_254_){
_start:
{
uint8_t v_t_boxed_255_; lean_object* v_res_256_; 
v_t_boxed_255_ = lean_unbox(v_t_252_);
v_res_256_ = l_Std_Internal_IO_Async_Signal_sigio_elim(v_motive_251_, v_t_boxed_255_, v_h_253_, v_sigio_254_);
lean_dec(v_sigio_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigxcpu_elim___redArg(lean_object* v_sigxcpu_257_){
_start:
{
lean_inc(v_sigxcpu_257_);
return v_sigxcpu_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigxcpu_elim___redArg___boxed(lean_object* v_sigxcpu_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Std_Internal_IO_Async_Signal_sigxcpu_elim___redArg(v_sigxcpu_258_);
lean_dec(v_sigxcpu_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigxcpu_elim(lean_object* v_motive_260_, uint8_t v_t_261_, lean_object* v_h_262_, lean_object* v_sigxcpu_263_){
_start:
{
lean_inc(v_sigxcpu_263_);
return v_sigxcpu_263_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigxcpu_elim___boxed(lean_object* v_motive_264_, lean_object* v_t_265_, lean_object* v_h_266_, lean_object* v_sigxcpu_267_){
_start:
{
uint8_t v_t_boxed_268_; lean_object* v_res_269_; 
v_t_boxed_268_ = lean_unbox(v_t_265_);
v_res_269_ = l_Std_Internal_IO_Async_Signal_sigxcpu_elim(v_motive_264_, v_t_boxed_268_, v_h_266_, v_sigxcpu_267_);
lean_dec(v_sigxcpu_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigxfsz_elim___redArg(lean_object* v_sigxfsz_270_){
_start:
{
lean_inc(v_sigxfsz_270_);
return v_sigxfsz_270_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigxfsz_elim___redArg___boxed(lean_object* v_sigxfsz_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Std_Internal_IO_Async_Signal_sigxfsz_elim___redArg(v_sigxfsz_271_);
lean_dec(v_sigxfsz_271_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigxfsz_elim(lean_object* v_motive_273_, uint8_t v_t_274_, lean_object* v_h_275_, lean_object* v_sigxfsz_276_){
_start:
{
lean_inc(v_sigxfsz_276_);
return v_sigxfsz_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigxfsz_elim___boxed(lean_object* v_motive_277_, lean_object* v_t_278_, lean_object* v_h_279_, lean_object* v_sigxfsz_280_){
_start:
{
uint8_t v_t_boxed_281_; lean_object* v_res_282_; 
v_t_boxed_281_ = lean_unbox(v_t_278_);
v_res_282_ = l_Std_Internal_IO_Async_Signal_sigxfsz_elim(v_motive_277_, v_t_boxed_281_, v_h_279_, v_sigxfsz_280_);
lean_dec(v_sigxfsz_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigvtalrm_elim___redArg(lean_object* v_sigvtalrm_283_){
_start:
{
lean_inc(v_sigvtalrm_283_);
return v_sigvtalrm_283_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigvtalrm_elim___redArg___boxed(lean_object* v_sigvtalrm_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Std_Internal_IO_Async_Signal_sigvtalrm_elim___redArg(v_sigvtalrm_284_);
lean_dec(v_sigvtalrm_284_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigvtalrm_elim(lean_object* v_motive_286_, uint8_t v_t_287_, lean_object* v_h_288_, lean_object* v_sigvtalrm_289_){
_start:
{
lean_inc(v_sigvtalrm_289_);
return v_sigvtalrm_289_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigvtalrm_elim___boxed(lean_object* v_motive_290_, lean_object* v_t_291_, lean_object* v_h_292_, lean_object* v_sigvtalrm_293_){
_start:
{
uint8_t v_t_boxed_294_; lean_object* v_res_295_; 
v_t_boxed_294_ = lean_unbox(v_t_291_);
v_res_295_ = l_Std_Internal_IO_Async_Signal_sigvtalrm_elim(v_motive_290_, v_t_boxed_294_, v_h_292_, v_sigvtalrm_293_);
lean_dec(v_sigvtalrm_293_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigprof_elim___redArg(lean_object* v_sigprof_296_){
_start:
{
lean_inc(v_sigprof_296_);
return v_sigprof_296_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigprof_elim___redArg___boxed(lean_object* v_sigprof_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Std_Internal_IO_Async_Signal_sigprof_elim___redArg(v_sigprof_297_);
lean_dec(v_sigprof_297_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigprof_elim(lean_object* v_motive_299_, uint8_t v_t_300_, lean_object* v_h_301_, lean_object* v_sigprof_302_){
_start:
{
lean_inc(v_sigprof_302_);
return v_sigprof_302_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigprof_elim___boxed(lean_object* v_motive_303_, lean_object* v_t_304_, lean_object* v_h_305_, lean_object* v_sigprof_306_){
_start:
{
uint8_t v_t_boxed_307_; lean_object* v_res_308_; 
v_t_boxed_307_ = lean_unbox(v_t_304_);
v_res_308_ = l_Std_Internal_IO_Async_Signal_sigprof_elim(v_motive_303_, v_t_boxed_307_, v_h_305_, v_sigprof_306_);
lean_dec(v_sigprof_306_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigwinch_elim___redArg(lean_object* v_sigwinch_309_){
_start:
{
lean_inc(v_sigwinch_309_);
return v_sigwinch_309_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigwinch_elim___redArg___boxed(lean_object* v_sigwinch_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Std_Internal_IO_Async_Signal_sigwinch_elim___redArg(v_sigwinch_310_);
lean_dec(v_sigwinch_310_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigwinch_elim(lean_object* v_motive_312_, uint8_t v_t_313_, lean_object* v_h_314_, lean_object* v_sigwinch_315_){
_start:
{
lean_inc(v_sigwinch_315_);
return v_sigwinch_315_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigwinch_elim___boxed(lean_object* v_motive_316_, lean_object* v_t_317_, lean_object* v_h_318_, lean_object* v_sigwinch_319_){
_start:
{
uint8_t v_t_boxed_320_; lean_object* v_res_321_; 
v_t_boxed_320_ = lean_unbox(v_t_317_);
v_res_321_ = l_Std_Internal_IO_Async_Signal_sigwinch_elim(v_motive_316_, v_t_boxed_320_, v_h_318_, v_sigwinch_319_);
lean_dec(v_sigwinch_319_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_siginfo_elim___redArg(lean_object* v_siginfo_322_){
_start:
{
lean_inc(v_siginfo_322_);
return v_siginfo_322_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_siginfo_elim___redArg___boxed(lean_object* v_siginfo_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Std_Internal_IO_Async_Signal_siginfo_elim___redArg(v_siginfo_323_);
lean_dec(v_siginfo_323_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_siginfo_elim(lean_object* v_motive_325_, uint8_t v_t_326_, lean_object* v_h_327_, lean_object* v_siginfo_328_){
_start:
{
lean_inc(v_siginfo_328_);
return v_siginfo_328_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_siginfo_elim___boxed(lean_object* v_motive_329_, lean_object* v_t_330_, lean_object* v_h_331_, lean_object* v_siginfo_332_){
_start:
{
uint8_t v_t_boxed_333_; lean_object* v_res_334_; 
v_t_boxed_333_ = lean_unbox(v_t_330_);
v_res_334_ = l_Std_Internal_IO_Async_Signal_siginfo_elim(v_motive_329_, v_t_boxed_333_, v_h_331_, v_siginfo_332_);
lean_dec(v_siginfo_332_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigusr1_elim___redArg(lean_object* v_sigusr1_335_){
_start:
{
lean_inc(v_sigusr1_335_);
return v_sigusr1_335_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigusr1_elim___redArg___boxed(lean_object* v_sigusr1_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Std_Internal_IO_Async_Signal_sigusr1_elim___redArg(v_sigusr1_336_);
lean_dec(v_sigusr1_336_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigusr1_elim(lean_object* v_motive_338_, uint8_t v_t_339_, lean_object* v_h_340_, lean_object* v_sigusr1_341_){
_start:
{
lean_inc(v_sigusr1_341_);
return v_sigusr1_341_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigusr1_elim___boxed(lean_object* v_motive_342_, lean_object* v_t_343_, lean_object* v_h_344_, lean_object* v_sigusr1_345_){
_start:
{
uint8_t v_t_boxed_346_; lean_object* v_res_347_; 
v_t_boxed_346_ = lean_unbox(v_t_343_);
v_res_347_ = l_Std_Internal_IO_Async_Signal_sigusr1_elim(v_motive_342_, v_t_boxed_346_, v_h_344_, v_sigusr1_345_);
lean_dec(v_sigusr1_345_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigusr2_elim___redArg(lean_object* v_sigusr2_348_){
_start:
{
lean_inc(v_sigusr2_348_);
return v_sigusr2_348_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigusr2_elim___redArg___boxed(lean_object* v_sigusr2_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_Internal_IO_Async_Signal_sigusr2_elim___redArg(v_sigusr2_349_);
lean_dec(v_sigusr2_349_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigusr2_elim(lean_object* v_motive_351_, uint8_t v_t_352_, lean_object* v_h_353_, lean_object* v_sigusr2_354_){
_start:
{
lean_inc(v_sigusr2_354_);
return v_sigusr2_354_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigusr2_elim___boxed(lean_object* v_motive_355_, lean_object* v_t_356_, lean_object* v_h_357_, lean_object* v_sigusr2_358_){
_start:
{
uint8_t v_t_boxed_359_; lean_object* v_res_360_; 
v_t_boxed_359_ = lean_unbox(v_t_356_);
v_res_360_ = l_Std_Internal_IO_Async_Signal_sigusr2_elim(v_motive_355_, v_t_boxed_359_, v_h_357_, v_sigusr2_358_);
lean_dec(v_sigusr2_358_);
return v_res_360_;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_unsigned_to_nat(2u);
v___x_434_ = lean_nat_to_int(v___x_433_);
return v___x_434_;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_unsigned_to_nat(1u);
v___x_436_ = lean_nat_to_int(v___x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_instReprSignal_repr(uint8_t v_x_437_, lean_object* v_prec_438_){
_start:
{
lean_object* v___y_440_; lean_object* v___y_447_; lean_object* v___y_454_; lean_object* v___y_461_; lean_object* v___y_468_; lean_object* v___y_475_; lean_object* v___y_482_; lean_object* v___y_489_; lean_object* v___y_496_; lean_object* v___y_503_; lean_object* v___y_510_; lean_object* v___y_517_; lean_object* v___y_524_; lean_object* v___y_531_; lean_object* v___y_538_; lean_object* v___y_545_; lean_object* v___y_552_; lean_object* v___y_559_; lean_object* v___y_566_; lean_object* v___y_573_; lean_object* v___y_580_; lean_object* v___y_587_; lean_object* v___y_594_; lean_object* v___y_601_; 
switch(v_x_437_)
{
case 0:
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = lean_unsigned_to_nat(1024u);
v___x_608_ = lean_nat_dec_le(v___x_607_, v_prec_438_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; 
v___x_609_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
v___y_440_ = v___x_609_;
goto v___jp_439_;
}
else
{
lean_object* v___x_610_; 
v___x_610_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
v___y_440_ = v___x_610_;
goto v___jp_439_;
}
}
case 1:
{
lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_611_ = lean_unsigned_to_nat(1024u);
v___x_612_ = lean_nat_dec_le(v___x_611_, v_prec_438_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; 
v___x_613_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
v___y_447_ = v___x_613_;
goto v___jp_446_;
}
else
{
lean_object* v___x_614_; 
v___x_614_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
v___y_447_ = v___x_614_;
goto v___jp_446_;
}
}
case 2:
{
lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_615_ = lean_unsigned_to_nat(1024u);
v___x_616_ = lean_nat_dec_le(v___x_615_, v_prec_438_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; 
v___x_617_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
v___y_454_ = v___x_617_;
goto v___jp_453_;
}
else
{
lean_object* v___x_618_; 
v___x_618_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
v___y_454_ = v___x_618_;
goto v___jp_453_;
}
}
case 3:
{
lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_619_ = lean_unsigned_to_nat(1024u);
v___x_620_ = lean_nat_dec_le(v___x_619_, v_prec_438_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; 
v___x_621_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
v___y_461_ = v___x_621_;
goto v___jp_460_;
}
else
{
lean_object* v___x_622_; 
v___x_622_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
v___y_461_ = v___x_622_;
goto v___jp_460_;
}
}
case 4:
{
lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_623_ = lean_unsigned_to_nat(1024u);
v___x_624_ = lean_nat_dec_le(v___x_623_, v_prec_438_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; 
v___x_625_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
v___y_468_ = v___x_625_;
goto v___jp_467_;
}
else
{
lean_object* v___x_626_; 
v___x_626_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
v___y_468_ = v___x_626_;
goto v___jp_467_;
}
}
case 5:
{
lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_627_ = lean_unsigned_to_nat(1024u);
v___x_628_ = lean_nat_dec_le(v___x_627_, v_prec_438_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; 
v___x_629_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
v___y_475_ = v___x_629_;
goto v___jp_474_;
}
else
{
lean_object* v___x_630_; 
v___x_630_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
v___y_475_ = v___x_630_;
goto v___jp_474_;
}
}
case 6:
{
lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_631_ = lean_unsigned_to_nat(1024u);
v___x_632_ = lean_nat_dec_le(v___x_631_, v_prec_438_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; 
v___x_633_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
v___y_482_ = v___x_633_;
goto v___jp_481_;
}
else
{
lean_object* v___x_634_; 
v___x_634_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
v___y_482_ = v___x_634_;
goto v___jp_481_;
}
}
case 7:
{
lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_635_ = lean_unsigned_to_nat(1024u);
v___x_636_ = lean_nat_dec_le(v___x_635_, v_prec_438_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; 
v___x_637_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
v___y_489_ = v___x_637_;
goto v___jp_488_;
}
else
{
lean_object* v___x_638_; 
v___x_638_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
v___y_489_ = v___x_638_;
goto v___jp_488_;
}
}
case 8:
{
lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_639_ = lean_unsigned_to_nat(1024u);
v___x_640_ = lean_nat_dec_le(v___x_639_, v_prec_438_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; 
v___x_641_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
v___y_496_ = v___x_641_;
goto v___jp_495_;
}
else
{
lean_object* v___x_642_; 
v___x_642_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
v___y_496_ = v___x_642_;
goto v___jp_495_;
}
}
case 9:
{
lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_643_ = lean_unsigned_to_nat(1024u);
v___x_644_ = lean_nat_dec_le(v___x_643_, v_prec_438_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; 
v___x_645_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
v___y_503_ = v___x_645_;
goto v___jp_502_;
}
else
{
lean_object* v___x_646_; 
v___x_646_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
v___y_503_ = v___x_646_;
goto v___jp_502_;
}
}
case 10:
{
lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = lean_unsigned_to_nat(1024u);
v___x_648_ = lean_nat_dec_le(v___x_647_, v_prec_438_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; 
v___x_649_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
v___y_510_ = v___x_649_;
goto v___jp_509_;
}
else
{
lean_object* v___x_650_; 
v___x_650_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
v___y_510_ = v___x_650_;
goto v___jp_509_;
}
}
case 11:
{
lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_651_ = lean_unsigned_to_nat(1024u);
v___x_652_ = lean_nat_dec_le(v___x_651_, v_prec_438_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; 
v___x_653_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
v___y_517_ = v___x_653_;
goto v___jp_516_;
}
else
{
lean_object* v___x_654_; 
v___x_654_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
v___y_517_ = v___x_654_;
goto v___jp_516_;
}
}
case 12:
{
lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_655_ = lean_unsigned_to_nat(1024u);
v___x_656_ = lean_nat_dec_le(v___x_655_, v_prec_438_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; 
v___x_657_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
v___y_524_ = v___x_657_;
goto v___jp_523_;
}
else
{
lean_object* v___x_658_; 
v___x_658_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
v___y_524_ = v___x_658_;
goto v___jp_523_;
}
}
case 13:
{
lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_659_ = lean_unsigned_to_nat(1024u);
v___x_660_ = lean_nat_dec_le(v___x_659_, v_prec_438_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; 
v___x_661_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
v___y_531_ = v___x_661_;
goto v___jp_530_;
}
else
{
lean_object* v___x_662_; 
v___x_662_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
v___y_531_ = v___x_662_;
goto v___jp_530_;
}
}
case 14:
{
lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_663_ = lean_unsigned_to_nat(1024u);
v___x_664_ = lean_nat_dec_le(v___x_663_, v_prec_438_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; 
v___x_665_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
v___y_538_ = v___x_665_;
goto v___jp_537_;
}
else
{
lean_object* v___x_666_; 
v___x_666_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
v___y_538_ = v___x_666_;
goto v___jp_537_;
}
}
case 15:
{
lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_667_ = lean_unsigned_to_nat(1024u);
v___x_668_ = lean_nat_dec_le(v___x_667_, v_prec_438_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; 
v___x_669_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
v___y_545_ = v___x_669_;
goto v___jp_544_;
}
else
{
lean_object* v___x_670_; 
v___x_670_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
v___y_545_ = v___x_670_;
goto v___jp_544_;
}
}
case 16:
{
lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_671_ = lean_unsigned_to_nat(1024u);
v___x_672_ = lean_nat_dec_le(v___x_671_, v_prec_438_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; 
v___x_673_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
v___y_552_ = v___x_673_;
goto v___jp_551_;
}
else
{
lean_object* v___x_674_; 
v___x_674_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
v___y_552_ = v___x_674_;
goto v___jp_551_;
}
}
case 17:
{
lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = lean_unsigned_to_nat(1024u);
v___x_676_ = lean_nat_dec_le(v___x_675_, v_prec_438_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; 
v___x_677_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
v___y_559_ = v___x_677_;
goto v___jp_558_;
}
else
{
lean_object* v___x_678_; 
v___x_678_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
v___y_559_ = v___x_678_;
goto v___jp_558_;
}
}
case 18:
{
lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_679_ = lean_unsigned_to_nat(1024u);
v___x_680_ = lean_nat_dec_le(v___x_679_, v_prec_438_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; 
v___x_681_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
v___y_566_ = v___x_681_;
goto v___jp_565_;
}
else
{
lean_object* v___x_682_; 
v___x_682_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
v___y_566_ = v___x_682_;
goto v___jp_565_;
}
}
case 19:
{
lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_683_ = lean_unsigned_to_nat(1024u);
v___x_684_ = lean_nat_dec_le(v___x_683_, v_prec_438_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; 
v___x_685_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
v___y_573_ = v___x_685_;
goto v___jp_572_;
}
else
{
lean_object* v___x_686_; 
v___x_686_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
v___y_573_ = v___x_686_;
goto v___jp_572_;
}
}
case 20:
{
lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_687_ = lean_unsigned_to_nat(1024u);
v___x_688_ = lean_nat_dec_le(v___x_687_, v_prec_438_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; 
v___x_689_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
v___y_580_ = v___x_689_;
goto v___jp_579_;
}
else
{
lean_object* v___x_690_; 
v___x_690_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
v___y_580_ = v___x_690_;
goto v___jp_579_;
}
}
case 21:
{
lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_691_ = lean_unsigned_to_nat(1024u);
v___x_692_ = lean_nat_dec_le(v___x_691_, v_prec_438_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; 
v___x_693_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
v___y_587_ = v___x_693_;
goto v___jp_586_;
}
else
{
lean_object* v___x_694_; 
v___x_694_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
v___y_587_ = v___x_694_;
goto v___jp_586_;
}
}
case 22:
{
lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_695_ = lean_unsigned_to_nat(1024u);
v___x_696_ = lean_nat_dec_le(v___x_695_, v_prec_438_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; 
v___x_697_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
v___y_594_ = v___x_697_;
goto v___jp_593_;
}
else
{
lean_object* v___x_698_; 
v___x_698_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
v___y_594_ = v___x_698_;
goto v___jp_593_;
}
}
default: 
{
lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_699_ = lean_unsigned_to_nat(1024u);
v___x_700_ = lean_nat_dec_le(v___x_699_, v_prec_438_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; 
v___x_701_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
v___y_601_ = v___x_701_;
goto v___jp_600_;
}
else
{
lean_object* v___x_702_; 
v___x_702_ = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
v___y_601_ = v___x_702_;
goto v___jp_600_;
}
}
}
v___jp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_441_ = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__1));
v___x_442_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_442_, 0, v___y_440_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___x_443_ = 0;
v___x_444_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_444_, 0, v___x_442_);
lean_ctor_set_uint8(v___x_444_, sizeof(void*)*1, v___x_443_);
v___x_445_ = l_Repr_addAppParen(v___x_444_, v_prec_438_);
return v___x_445_;
}
v___jp_446_:
{
lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_448_ = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__3));
v___x_449_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_449_, 0, v___y_447_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = 0;
v___x_451_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set_uint8(v___x_451_, sizeof(void*)*1, v___x_450_);
v___x_452_ = l_Repr_addAppParen(v___x_451_, v_prec_438_);
return v___x_452_;
}
v___jp_453_:
{
lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_455_ = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__5));
v___x_456_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_456_, 0, v___y_454_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = 0;
v___x_458_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*1, v___x_457_);
v___x_459_ = l_Repr_addAppParen(v___x_458_, v_prec_438_);
return v___x_459_;
}
v___jp_460_:
{
lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_462_ = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__7));
v___x_463_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_463_, 0, v___y_461_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = 0;
v___x_465_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set_uint8(v___x_465_, sizeof(void*)*1, v___x_464_);
v___x_466_ = l_Repr_addAppParen(v___x_465_, v_prec_438_);
return v___x_466_;
}
v___jp_467_:
{
lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_469_ = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__9));
v___x_470_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_470_, 0, v___y_468_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
v___x_471_ = 0;
v___x_472_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_472_, 0, v___x_470_);
lean_ctor_set_uint8(v___x_472_, sizeof(void*)*1, v___x_471_);
v___x_473_ = l_Repr_addAppParen(v___x_472_, v_prec_438_);
return v___x_473_;
}
v___jp_474_:
{
lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_476_ = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__11));
v___x_477_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_477_, 0, v___y_475_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
v___x_478_ = 0;
v___x_479_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_479_, 0, v___x_477_);
lean_ctor_set_uint8(v___x_479_, sizeof(void*)*1, v___x_478_);
v___x_480_ = l_Repr_addAppParen(v___x_479_, v_prec_438_);
return v___x_480_;
}
v___jp_481_:
{
lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_483_ = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__13));
v___x_484_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_484_, 0, v___y_482_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
v___x_485_ = 0;
v___x_486_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_486_, 0, v___x_484_);
lean_ctor_set_uint8(v___x_486_, sizeof(void*)*1, v___x_485_);
v___x_487_ = l_Repr_addAppParen(v___x_486_, v_prec_438_);
return v___x_487_;
}
v___jp_488_:
{
lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_490_ = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__15));
v___x_491_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_491_, 0, v___y_489_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
v___x_492_ = 0;
v___x_493_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_493_, 0, v___x_491_);
lean_ctor_set_uint8(v___x_493_, sizeof(void*)*1, v___x_492_);
v___x_494_ = l_Repr_addAppParen(v___x_493_, v_prec_438_);
return v___x_494_;
}
v___jp_495_:
{
lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_497_ = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__17));
v___x_498_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_498_, 0, v___y_496_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = 0;
v___x_500_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_500_, 0, v___x_498_);
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*1, v___x_499_);
v___x_501_ = l_Repr_addAppParen(v___x_500_, v_prec_438_);
return v___x_501_;
}
v___jp_502_:
{
lean_object* v___x_504_; lean_object* v___x_505_; uint8_t v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_504_ = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__19));
v___x_505_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_505_, 0, v___y_503_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
v___x_506_ = 0;
v___x_507_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_507_, 0, v___x_505_);
lean_ctor_set_uint8(v___x_507_, sizeof(void*)*1, v___x_506_);
v___x_508_ = l_Repr_addAppParen(v___x_507_, v_prec_438_);
return v___x_508_;
}
v___jp_509_:
{
lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_511_ = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__21));
v___x_512_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_512_, 0, v___y_510_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = 0;
v___x_514_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_514_, 0, v___x_512_);
lean_ctor_set_uint8(v___x_514_, sizeof(void*)*1, v___x_513_);
v___x_515_ = l_Repr_addAppParen(v___x_514_, v_prec_438_);
return v___x_515_;
}
v___jp_516_:
{
lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_518_ = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__23));
v___x_519_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_519_, 0, v___y_517_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = 0;
v___x_521_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_521_, 0, v___x_519_);
lean_ctor_set_uint8(v___x_521_, sizeof(void*)*1, v___x_520_);
v___x_522_ = l_Repr_addAppParen(v___x_521_, v_prec_438_);
return v___x_522_;
}
v___jp_523_:
{
lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_525_ = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__25));
v___x_526_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_526_, 0, v___y_524_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = 0;
v___x_528_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_528_, 0, v___x_526_);
lean_ctor_set_uint8(v___x_528_, sizeof(void*)*1, v___x_527_);
v___x_529_ = l_Repr_addAppParen(v___x_528_, v_prec_438_);
return v___x_529_;
}
v___jp_530_:
{
lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_532_ = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__27));
v___x_533_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_533_, 0, v___y_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = 0;
v___x_535_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set_uint8(v___x_535_, sizeof(void*)*1, v___x_534_);
v___x_536_ = l_Repr_addAppParen(v___x_535_, v_prec_438_);
return v___x_536_;
}
v___jp_537_:
{
lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_539_ = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__29));
v___x_540_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_540_, 0, v___y_538_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = 0;
v___x_542_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_542_, 0, v___x_540_);
lean_ctor_set_uint8(v___x_542_, sizeof(void*)*1, v___x_541_);
v___x_543_ = l_Repr_addAppParen(v___x_542_, v_prec_438_);
return v___x_543_;
}
v___jp_544_:
{
lean_object* v___x_546_; lean_object* v___x_547_; uint8_t v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_546_ = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__31));
v___x_547_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_547_, 0, v___y_545_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
v___x_548_ = 0;
v___x_549_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_549_, 0, v___x_547_);
lean_ctor_set_uint8(v___x_549_, sizeof(void*)*1, v___x_548_);
v___x_550_ = l_Repr_addAppParen(v___x_549_, v_prec_438_);
return v___x_550_;
}
v___jp_551_:
{
lean_object* v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_553_ = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__33));
v___x_554_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_554_, 0, v___y_552_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = 0;
v___x_556_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_556_, 0, v___x_554_);
lean_ctor_set_uint8(v___x_556_, sizeof(void*)*1, v___x_555_);
v___x_557_ = l_Repr_addAppParen(v___x_556_, v_prec_438_);
return v___x_557_;
}
v___jp_558_:
{
lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_560_ = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__35));
v___x_561_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_561_, 0, v___y_559_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = 0;
v___x_563_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_563_, 0, v___x_561_);
lean_ctor_set_uint8(v___x_563_, sizeof(void*)*1, v___x_562_);
v___x_564_ = l_Repr_addAppParen(v___x_563_, v_prec_438_);
return v___x_564_;
}
v___jp_565_:
{
lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_567_ = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__37));
v___x_568_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_568_, 0, v___y_566_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
v___x_569_ = 0;
v___x_570_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_570_, 0, v___x_568_);
lean_ctor_set_uint8(v___x_570_, sizeof(void*)*1, v___x_569_);
v___x_571_ = l_Repr_addAppParen(v___x_570_, v_prec_438_);
return v___x_571_;
}
v___jp_572_:
{
lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_574_ = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__39));
v___x_575_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_575_, 0, v___y_573_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___x_576_ = 0;
v___x_577_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_577_, 0, v___x_575_);
lean_ctor_set_uint8(v___x_577_, sizeof(void*)*1, v___x_576_);
v___x_578_ = l_Repr_addAppParen(v___x_577_, v_prec_438_);
return v___x_578_;
}
v___jp_579_:
{
lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_581_ = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__41));
v___x_582_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_582_, 0, v___y_580_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = 0;
v___x_584_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_584_, 0, v___x_582_);
lean_ctor_set_uint8(v___x_584_, sizeof(void*)*1, v___x_583_);
v___x_585_ = l_Repr_addAppParen(v___x_584_, v_prec_438_);
return v___x_585_;
}
v___jp_586_:
{
lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_588_ = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__43));
v___x_589_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_589_, 0, v___y_587_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
v___x_590_ = 0;
v___x_591_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_591_, 0, v___x_589_);
lean_ctor_set_uint8(v___x_591_, sizeof(void*)*1, v___x_590_);
v___x_592_ = l_Repr_addAppParen(v___x_591_, v_prec_438_);
return v___x_592_;
}
v___jp_593_:
{
lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_595_ = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__45));
v___x_596_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_596_, 0, v___y_594_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = 0;
v___x_598_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_598_, 0, v___x_596_);
lean_ctor_set_uint8(v___x_598_, sizeof(void*)*1, v___x_597_);
v___x_599_ = l_Repr_addAppParen(v___x_598_, v_prec_438_);
return v___x_599_;
}
v___jp_600_:
{
lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_602_ = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__47));
v___x_603_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_603_, 0, v___y_601_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = 0;
v___x_605_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_605_, 0, v___x_603_);
lean_ctor_set_uint8(v___x_605_, sizeof(void*)*1, v___x_604_);
v___x_606_ = l_Repr_addAppParen(v___x_605_, v_prec_438_);
return v___x_606_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___boxed(lean_object* v_x_703_, lean_object* v_prec_704_){
_start:
{
uint8_t v_x_1353__boxed_705_; lean_object* v_res_706_; 
v_x_1353__boxed_705_ = lean_unbox(v_x_703_);
v_res_706_ = l_Std_Internal_IO_Async_instReprSignal_repr(v_x_1353__boxed_705_, v_prec_704_);
lean_dec(v_prec_704_);
return v_res_706_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IO_Async_Signal_ofNat(lean_object* v_n_709_){
_start:
{
lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_710_ = lean_unsigned_to_nat(11u);
v___x_711_ = lean_nat_dec_le(v_n_709_, v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_712_ = lean_unsigned_to_nat(17u);
v___x_713_ = lean_nat_dec_le(v_n_709_, v___x_712_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_714_ = lean_unsigned_to_nat(20u);
v___x_715_ = lean_nat_dec_le(v_n_709_, v___x_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_716_ = lean_unsigned_to_nat(21u);
v___x_717_ = lean_nat_dec_le(v_n_709_, v___x_716_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = lean_unsigned_to_nat(22u);
v___x_719_ = lean_nat_dec_le(v_n_709_, v___x_718_);
if (v___x_719_ == 0)
{
uint8_t v___x_720_; 
v___x_720_ = 23;
return v___x_720_;
}
else
{
uint8_t v___x_721_; 
v___x_721_ = 22;
return v___x_721_;
}
}
else
{
uint8_t v___x_722_; 
v___x_722_ = 21;
return v___x_722_;
}
}
else
{
lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_723_ = lean_unsigned_to_nat(18u);
v___x_724_ = lean_nat_dec_le(v_n_709_, v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_725_ = lean_unsigned_to_nat(19u);
v___x_726_ = lean_nat_dec_le(v_n_709_, v___x_725_);
if (v___x_726_ == 0)
{
uint8_t v___x_727_; 
v___x_727_ = 20;
return v___x_727_;
}
else
{
uint8_t v___x_728_; 
v___x_728_ = 19;
return v___x_728_;
}
}
else
{
uint8_t v___x_729_; 
v___x_729_ = 18;
return v___x_729_;
}
}
}
else
{
lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_730_ = lean_unsigned_to_nat(14u);
v___x_731_ = lean_nat_dec_le(v_n_709_, v___x_730_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_732_ = lean_unsigned_to_nat(15u);
v___x_733_ = lean_nat_dec_le(v_n_709_, v___x_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_734_ = lean_unsigned_to_nat(16u);
v___x_735_ = lean_nat_dec_le(v_n_709_, v___x_734_);
if (v___x_735_ == 0)
{
uint8_t v___x_736_; 
v___x_736_ = 17;
return v___x_736_;
}
else
{
uint8_t v___x_737_; 
v___x_737_ = 16;
return v___x_737_;
}
}
else
{
uint8_t v___x_738_; 
v___x_738_ = 15;
return v___x_738_;
}
}
else
{
lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_739_ = lean_unsigned_to_nat(12u);
v___x_740_ = lean_nat_dec_le(v_n_709_, v___x_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_741_ = lean_unsigned_to_nat(13u);
v___x_742_ = lean_nat_dec_le(v_n_709_, v___x_741_);
if (v___x_742_ == 0)
{
uint8_t v___x_743_; 
v___x_743_ = 14;
return v___x_743_;
}
else
{
uint8_t v___x_744_; 
v___x_744_ = 13;
return v___x_744_;
}
}
else
{
uint8_t v___x_745_; 
v___x_745_ = 12;
return v___x_745_;
}
}
}
}
else
{
lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_746_ = lean_unsigned_to_nat(5u);
v___x_747_ = lean_nat_dec_le(v_n_709_, v___x_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_748_ = lean_unsigned_to_nat(8u);
v___x_749_ = lean_nat_dec_le(v_n_709_, v___x_748_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_750_ = lean_unsigned_to_nat(9u);
v___x_751_ = lean_nat_dec_le(v_n_709_, v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_752_ = lean_unsigned_to_nat(10u);
v___x_753_ = lean_nat_dec_le(v_n_709_, v___x_752_);
if (v___x_753_ == 0)
{
uint8_t v___x_754_; 
v___x_754_ = 11;
return v___x_754_;
}
else
{
uint8_t v___x_755_; 
v___x_755_ = 10;
return v___x_755_;
}
}
else
{
uint8_t v___x_756_; 
v___x_756_ = 9;
return v___x_756_;
}
}
else
{
lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_757_ = lean_unsigned_to_nat(6u);
v___x_758_ = lean_nat_dec_le(v_n_709_, v___x_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_759_ = lean_unsigned_to_nat(7u);
v___x_760_ = lean_nat_dec_le(v_n_709_, v___x_759_);
if (v___x_760_ == 0)
{
uint8_t v___x_761_; 
v___x_761_ = 8;
return v___x_761_;
}
else
{
uint8_t v___x_762_; 
v___x_762_ = 7;
return v___x_762_;
}
}
else
{
uint8_t v___x_763_; 
v___x_763_ = 6;
return v___x_763_;
}
}
}
else
{
lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_764_ = lean_unsigned_to_nat(2u);
v___x_765_ = lean_nat_dec_le(v_n_709_, v___x_764_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_766_ = lean_unsigned_to_nat(3u);
v___x_767_ = lean_nat_dec_le(v_n_709_, v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_768_ = lean_unsigned_to_nat(4u);
v___x_769_ = lean_nat_dec_le(v_n_709_, v___x_768_);
if (v___x_769_ == 0)
{
uint8_t v___x_770_; 
v___x_770_ = 5;
return v___x_770_;
}
else
{
uint8_t v___x_771_; 
v___x_771_ = 4;
return v___x_771_;
}
}
else
{
uint8_t v___x_772_; 
v___x_772_ = 3;
return v___x_772_;
}
}
else
{
lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = lean_nat_dec_le(v_n_709_, v___x_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = lean_unsigned_to_nat(1u);
v___x_776_ = lean_nat_dec_le(v_n_709_, v___x_775_);
if (v___x_776_ == 0)
{
uint8_t v___x_777_; 
v___x_777_ = 2;
return v___x_777_;
}
else
{
uint8_t v___x_778_; 
v___x_778_ = 1;
return v___x_778_;
}
}
else
{
uint8_t v___x_779_; 
v___x_779_ = 0;
return v___x_779_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_ofNat___boxed(lean_object* v_n_780_){
_start:
{
uint8_t v_res_781_; lean_object* v_r_782_; 
v_res_781_ = l_Std_Internal_IO_Async_Signal_ofNat(v_n_780_);
lean_dec(v_n_780_);
v_r_782_ = lean_box(v_res_781_);
return v_r_782_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IO_Async_instDecidableEqSignal(uint8_t v_x_783_, uint8_t v_y_784_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_785_ = l_Std_Internal_IO_Async_Signal_ctorIdx(v_x_783_);
v___x_786_ = l_Std_Internal_IO_Async_Signal_ctorIdx(v_y_784_);
v___x_787_ = lean_nat_dec_eq(v___x_785_, v___x_786_);
lean_dec(v___x_786_);
lean_dec(v___x_785_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_instDecidableEqSignal___boxed(lean_object* v_x_788_, lean_object* v_y_789_){
_start:
{
uint8_t v_x_13__boxed_790_; uint8_t v_y_14__boxed_791_; uint8_t v_res_792_; lean_object* v_r_793_; 
v_x_13__boxed_790_ = lean_unbox(v_x_788_);
v_y_14__boxed_791_ = lean_unbox(v_y_789_);
v_res_792_ = l_Std_Internal_IO_Async_instDecidableEqSignal(v_x_13__boxed_790_, v_y_14__boxed_791_);
v_r_793_ = lean_box(v_res_792_);
return v_r_793_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IO_Async_instBEqSignal_beq(uint8_t v_x_794_, uint8_t v_y_795_){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; 
v___x_796_ = l_Std_Internal_IO_Async_Signal_ctorIdx(v_x_794_);
v___x_797_ = l_Std_Internal_IO_Async_Signal_ctorIdx(v_y_795_);
v___x_798_ = lean_nat_dec_eq(v___x_796_, v___x_797_);
lean_dec(v___x_797_);
lean_dec(v___x_796_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_instBEqSignal_beq___boxed(lean_object* v_x_799_, lean_object* v_y_800_){
_start:
{
uint8_t v_x_17__boxed_801_; uint8_t v_y_18__boxed_802_; uint8_t v_res_803_; lean_object* v_r_804_; 
v_x_17__boxed_801_ = lean_unbox(v_x_799_);
v_y_18__boxed_802_ = lean_unbox(v_y_800_);
v_res_803_ = l_Std_Internal_IO_Async_instBEqSignal_beq(v_x_17__boxed_801_, v_y_18__boxed_802_);
v_r_804_ = lean_box(v_res_803_);
return v_r_804_;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__0(void){
_start:
{
lean_object* v___x_807_; uint32_t v___x_808_; 
v___x_807_ = lean_unsigned_to_nat(1u);
v___x_808_ = lean_int32_of_nat(v___x_807_);
return v___x_808_;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__1(void){
_start:
{
lean_object* v___x_809_; uint32_t v___x_810_; 
v___x_809_ = lean_unsigned_to_nat(2u);
v___x_810_ = lean_int32_of_nat(v___x_809_);
return v___x_810_;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__2(void){
_start:
{
lean_object* v___x_811_; uint32_t v___x_812_; 
v___x_811_ = lean_unsigned_to_nat(3u);
v___x_812_ = lean_int32_of_nat(v___x_811_);
return v___x_812_;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__3(void){
_start:
{
lean_object* v___x_813_; uint32_t v___x_814_; 
v___x_813_ = lean_unsigned_to_nat(5u);
v___x_814_ = lean_int32_of_nat(v___x_813_);
return v___x_814_;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__4(void){
_start:
{
lean_object* v___x_815_; uint32_t v___x_816_; 
v___x_815_ = lean_unsigned_to_nat(6u);
v___x_816_ = lean_int32_of_nat(v___x_815_);
return v___x_816_;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__5(void){
_start:
{
lean_object* v___x_817_; uint32_t v___x_818_; 
v___x_817_ = lean_unsigned_to_nat(7u);
v___x_818_ = lean_int32_of_nat(v___x_817_);
return v___x_818_;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__6(void){
_start:
{
lean_object* v___x_819_; uint32_t v___x_820_; 
v___x_819_ = lean_unsigned_to_nat(12u);
v___x_820_ = lean_int32_of_nat(v___x_819_);
return v___x_820_;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__7(void){
_start:
{
lean_object* v___x_821_; uint32_t v___x_822_; 
v___x_821_ = lean_unsigned_to_nat(14u);
v___x_822_ = lean_int32_of_nat(v___x_821_);
return v___x_822_;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__8(void){
_start:
{
lean_object* v___x_823_; uint32_t v___x_824_; 
v___x_823_ = lean_unsigned_to_nat(15u);
v___x_824_ = lean_int32_of_nat(v___x_823_);
return v___x_824_;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__9(void){
_start:
{
lean_object* v___x_825_; uint32_t v___x_826_; 
v___x_825_ = lean_unsigned_to_nat(16u);
v___x_826_ = lean_int32_of_nat(v___x_825_);
return v___x_826_;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__10(void){
_start:
{
lean_object* v___x_827_; uint32_t v___x_828_; 
v___x_827_ = lean_unsigned_to_nat(18u);
v___x_828_ = lean_int32_of_nat(v___x_827_);
return v___x_828_;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__11(void){
_start:
{
lean_object* v___x_829_; uint32_t v___x_830_; 
v___x_829_ = lean_unsigned_to_nat(19u);
v___x_830_ = lean_int32_of_nat(v___x_829_);
return v___x_830_;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__12(void){
_start:
{
lean_object* v___x_831_; uint32_t v___x_832_; 
v___x_831_ = lean_unsigned_to_nat(20u);
v___x_832_ = lean_int32_of_nat(v___x_831_);
return v___x_832_;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__13(void){
_start:
{
lean_object* v___x_833_; uint32_t v___x_834_; 
v___x_833_ = lean_unsigned_to_nat(21u);
v___x_834_ = lean_int32_of_nat(v___x_833_);
return v___x_834_;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__14(void){
_start:
{
lean_object* v___x_835_; uint32_t v___x_836_; 
v___x_835_ = lean_unsigned_to_nat(22u);
v___x_836_ = lean_int32_of_nat(v___x_835_);
return v___x_836_;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__15(void){
_start:
{
lean_object* v___x_837_; uint32_t v___x_838_; 
v___x_837_ = lean_unsigned_to_nat(23u);
v___x_838_ = lean_int32_of_nat(v___x_837_);
return v___x_838_;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__16(void){
_start:
{
lean_object* v___x_839_; uint32_t v___x_840_; 
v___x_839_ = lean_unsigned_to_nat(24u);
v___x_840_ = lean_int32_of_nat(v___x_839_);
return v___x_840_;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__17(void){
_start:
{
lean_object* v___x_841_; uint32_t v___x_842_; 
v___x_841_ = lean_unsigned_to_nat(25u);
v___x_842_ = lean_int32_of_nat(v___x_841_);
return v___x_842_;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__18(void){
_start:
{
lean_object* v___x_843_; uint32_t v___x_844_; 
v___x_843_ = lean_unsigned_to_nat(26u);
v___x_844_ = lean_int32_of_nat(v___x_843_);
return v___x_844_;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__19(void){
_start:
{
lean_object* v___x_845_; uint32_t v___x_846_; 
v___x_845_ = lean_unsigned_to_nat(27u);
v___x_846_ = lean_int32_of_nat(v___x_845_);
return v___x_846_;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__20(void){
_start:
{
lean_object* v___x_847_; uint32_t v___x_848_; 
v___x_847_ = lean_unsigned_to_nat(28u);
v___x_848_ = lean_int32_of_nat(v___x_847_);
return v___x_848_;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__21(void){
_start:
{
lean_object* v___x_849_; uint32_t v___x_850_; 
v___x_849_ = lean_unsigned_to_nat(29u);
v___x_850_ = lean_int32_of_nat(v___x_849_);
return v___x_850_;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__22(void){
_start:
{
lean_object* v___x_851_; uint32_t v___x_852_; 
v___x_851_ = lean_unsigned_to_nat(30u);
v___x_852_ = lean_int32_of_nat(v___x_851_);
return v___x_852_;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__23(void){
_start:
{
lean_object* v___x_853_; uint32_t v___x_854_; 
v___x_853_ = lean_unsigned_to_nat(31u);
v___x_854_ = lean_int32_of_nat(v___x_853_);
return v___x_854_;
}
}
LEAN_EXPORT uint32_t l_Std_Internal_IO_Async_Signal_toInt32(uint8_t v_x_855_){
_start:
{
switch(v_x_855_)
{
case 0:
{
uint32_t v___x_856_; 
v___x_856_ = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__0, &l_Std_Internal_IO_Async_Signal_toInt32___closed__0_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__0);
return v___x_856_;
}
case 1:
{
uint32_t v___x_857_; 
v___x_857_ = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__1, &l_Std_Internal_IO_Async_Signal_toInt32___closed__1_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__1);
return v___x_857_;
}
case 2:
{
uint32_t v___x_858_; 
v___x_858_ = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__2, &l_Std_Internal_IO_Async_Signal_toInt32___closed__2_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__2);
return v___x_858_;
}
case 3:
{
uint32_t v___x_859_; 
v___x_859_ = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__3, &l_Std_Internal_IO_Async_Signal_toInt32___closed__3_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__3);
return v___x_859_;
}
case 4:
{
uint32_t v___x_860_; 
v___x_860_ = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__4, &l_Std_Internal_IO_Async_Signal_toInt32___closed__4_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__4);
return v___x_860_;
}
case 5:
{
uint32_t v___x_861_; 
v___x_861_ = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__5, &l_Std_Internal_IO_Async_Signal_toInt32___closed__5_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__5);
return v___x_861_;
}
case 6:
{
uint32_t v___x_862_; 
v___x_862_ = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__6, &l_Std_Internal_IO_Async_Signal_toInt32___closed__6_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__6);
return v___x_862_;
}
case 7:
{
uint32_t v___x_863_; 
v___x_863_ = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__7, &l_Std_Internal_IO_Async_Signal_toInt32___closed__7_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__7);
return v___x_863_;
}
case 8:
{
uint32_t v___x_864_; 
v___x_864_ = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__8, &l_Std_Internal_IO_Async_Signal_toInt32___closed__8_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__8);
return v___x_864_;
}
case 9:
{
uint32_t v___x_865_; 
v___x_865_ = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__9, &l_Std_Internal_IO_Async_Signal_toInt32___closed__9_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__9);
return v___x_865_;
}
case 10:
{
uint32_t v___x_866_; 
v___x_866_ = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__10, &l_Std_Internal_IO_Async_Signal_toInt32___closed__10_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__10);
return v___x_866_;
}
case 11:
{
uint32_t v___x_867_; 
v___x_867_ = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__11, &l_Std_Internal_IO_Async_Signal_toInt32___closed__11_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__11);
return v___x_867_;
}
case 12:
{
uint32_t v___x_868_; 
v___x_868_ = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__12, &l_Std_Internal_IO_Async_Signal_toInt32___closed__12_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__12);
return v___x_868_;
}
case 13:
{
uint32_t v___x_869_; 
v___x_869_ = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__13, &l_Std_Internal_IO_Async_Signal_toInt32___closed__13_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__13);
return v___x_869_;
}
case 14:
{
uint32_t v___x_870_; 
v___x_870_ = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__14, &l_Std_Internal_IO_Async_Signal_toInt32___closed__14_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__14);
return v___x_870_;
}
case 15:
{
uint32_t v___x_871_; 
v___x_871_ = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__15, &l_Std_Internal_IO_Async_Signal_toInt32___closed__15_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__15);
return v___x_871_;
}
case 16:
{
uint32_t v___x_872_; 
v___x_872_ = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__16, &l_Std_Internal_IO_Async_Signal_toInt32___closed__16_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__16);
return v___x_872_;
}
case 17:
{
uint32_t v___x_873_; 
v___x_873_ = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__17, &l_Std_Internal_IO_Async_Signal_toInt32___closed__17_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__17);
return v___x_873_;
}
case 18:
{
uint32_t v___x_874_; 
v___x_874_ = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__18, &l_Std_Internal_IO_Async_Signal_toInt32___closed__18_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__18);
return v___x_874_;
}
case 19:
{
uint32_t v___x_875_; 
v___x_875_ = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__19, &l_Std_Internal_IO_Async_Signal_toInt32___closed__19_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__19);
return v___x_875_;
}
case 20:
{
uint32_t v___x_876_; 
v___x_876_ = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__20, &l_Std_Internal_IO_Async_Signal_toInt32___closed__20_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__20);
return v___x_876_;
}
case 21:
{
uint32_t v___x_877_; 
v___x_877_ = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__21, &l_Std_Internal_IO_Async_Signal_toInt32___closed__21_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__21);
return v___x_877_;
}
case 22:
{
uint32_t v___x_878_; 
v___x_878_ = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__22, &l_Std_Internal_IO_Async_Signal_toInt32___closed__22_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__22);
return v___x_878_;
}
default: 
{
uint32_t v___x_879_; 
v___x_879_ = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__23, &l_Std_Internal_IO_Async_Signal_toInt32___closed__23_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__23);
return v___x_879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_toInt32___boxed(lean_object* v_x_880_){
_start:
{
uint8_t v_x_388__boxed_881_; uint32_t v_res_882_; lean_object* v_r_883_; 
v_x_388__boxed_881_ = lean_unbox(v_x_880_);
v_res_882_ = l_Std_Internal_IO_Async_Signal_toInt32(v_x_388__boxed_881_);
v_r_883_ = lean_box_uint32(v_res_882_);
return v_r_883_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_mk(uint8_t v_signum_884_, uint8_t v_repeating_885_){
_start:
{
uint32_t v___x_887_; lean_object* v___x_888_; 
v___x_887_ = l_Std_Internal_IO_Async_Signal_toInt32(v_signum_884_);
v___x_888_ = lean_uv_signal_mk(v___x_887_, v_repeating_885_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
v_a_897_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_888_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_888_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_mk___boxed(lean_object* v_signum_905_, lean_object* v_repeating_906_, lean_object* v_a_907_){
_start:
{
uint8_t v_signum_boxed_908_; uint8_t v_repeating_boxed_909_; lean_object* v_res_910_; 
v_signum_boxed_908_ = lean_unbox(v_signum_905_);
v_repeating_boxed_909_ = lean_unbox(v_repeating_906_);
v_res_910_ = l_Std_Internal_IO_Async_Signal_Waiter_mk(v_signum_boxed_908_, v_repeating_boxed_909_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_wait___lam__0(lean_object* v___x_911_, lean_object* v_x_912_){
_start:
{
if (lean_obj_tag(v_x_912_) == 0)
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = lean_mk_io_user_error(v___x_911_);
v___x_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
return v___x_914_;
}
else
{
lean_object* v_val_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec_ref(v___x_911_);
v_val_915_ = lean_ctor_get(v_x_912_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v_x_912_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v_x_912_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_val_915_);
lean_dec(v_x_912_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_val_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_wait(lean_object* v_s_926_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = lean_uv_signal_next(v_s_926_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_941_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_941_ == 0)
{
v___x_931_ = v___x_928_;
v_isShared_932_ = v_isSharedCheck_941_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_928_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_941_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___f_933_; lean_object* v___x_934_; lean_object* v___x_935_; uint8_t v___x_936_; lean_object* v___x_937_; lean_object* v___x_939_; 
v___f_933_ = ((lean_object*)(l_Std_Internal_IO_Async_Signal_Waiter_wait___closed__1));
v___x_934_ = lean_io_promise_result_opt(v_a_929_);
lean_dec(v_a_929_);
v___x_935_ = lean_unsigned_to_nat(0u);
v___x_936_ = 1;
v___x_937_ = lean_task_map(v___f_933_, v___x_934_, v___x_935_, v___x_936_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v___x_937_);
v___x_939_ = v___x_931_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_937_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
v_a_942_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_928_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_928_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_wait___boxed(lean_object* v_s_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Std_Internal_IO_Async_Signal_Waiter_wait(v_s_950_);
lean_dec(v_s_950_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_stop(lean_object* v_s_953_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = lean_uv_signal_stop(v_s_953_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_stop___boxed(lean_object* v_s_956_, lean_object* v_a_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Std_Internal_IO_Async_Signal_Waiter_stop(v_s_956_);
lean_dec(v_s_956_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Signal_Waiter_selector_spec__0(lean_object* v_w_961_, lean_object* v_lose_962_){
_start:
{
lean_object* v_finished_964_; lean_object* v_promise_965_; lean_object* v___x_966_; uint8_t v___y_968_; uint8_t v___x_976_; 
v_finished_964_ = lean_ctor_get(v_w_961_, 0);
v_promise_965_ = lean_ctor_get(v_w_961_, 1);
v___x_966_ = lean_st_ref_take(v_finished_964_);
v___x_976_ = lean_unbox(v___x_966_);
lean_dec(v___x_966_);
if (v___x_976_ == 0)
{
uint8_t v___x_977_; 
v___x_977_ = 1;
v___y_968_ = v___x_977_;
goto v___jp_967_;
}
else
{
uint8_t v___x_978_; 
v___x_978_ = 0;
v___y_968_ = v___x_978_;
goto v___jp_967_;
}
v___jp_967_:
{
uint8_t v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_969_ = 1;
v___x_970_ = lean_box(v___x_969_);
v___x_971_ = lean_st_ref_set(v_finished_964_, v___x_970_);
if (v___y_968_ == 0)
{
lean_object* v___x_972_; 
v___x_972_ = lean_apply_1(v_lose_962_, lean_box(0));
return v___x_972_;
}
else
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
lean_dec_ref(v_lose_962_);
v___x_973_ = ((lean_object*)(l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Signal_Waiter_selector_spec__0___closed__0));
v___x_974_ = lean_io_promise_resolve(v___x_973_, v_promise_965_);
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
return v___x_975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Signal_Waiter_selector_spec__0___boxed(lean_object* v_w_979_, lean_object* v_lose_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Signal_Waiter_selector_spec__0(v_w_979_, v_lose_980_);
lean_dec_ref(v_w_979_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__0(lean_object* v_s_983_){
_start:
{
lean_object* v_val_986_; lean_object* v___x_988_; 
v___x_988_ = lean_uv_signal_cancel(v_s_983_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_988_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_988_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
lean_ctor_set_tag(v___x_991_, 1);
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
v_val_986_ = v___x_994_;
goto v___jp_985_;
}
}
}
else
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
v_a_997_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_988_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_988_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
lean_ctor_set_tag(v___x_999_, 0);
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
v_val_986_ = v___x_1002_;
goto v___jp_985_;
}
}
}
v___jp_985_:
{
lean_object* v___x_987_; 
v___x_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_987_, 0, v_val_986_);
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__0___boxed(lean_object* v_s_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__0(v_s_1005_);
lean_dec(v_s_1005_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__1(lean_object* v_x_1012_){
_start:
{
if (lean_obj_tag(v_x_1012_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1022_; 
v_a_1014_ = lean_ctor_get(v_x_1012_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_x_1012_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1016_ = v_x_1012_;
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v_x_1012_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
return v___x_1020_;
}
}
}
else
{
lean_object* v___x_1023_; 
lean_dec_ref(v_x_1012_);
v___x_1023_ = ((lean_object*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__1___closed__1));
return v___x_1023_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__1___boxed(lean_object* v_x_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__1(v_x_1024_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__2(lean_object* v___f_1033_, lean_object* v_s_1034_, lean_object* v_x_1035_){
_start:
{
if (lean_obj_tag(v_x_1035_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1045_; 
lean_dec_ref(v___f_1033_);
v_a_1037_ = lean_ctor_get(v_x_1035_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_x_1035_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1039_ = v_x_1035_;
v_isShared_1040_ = v_isSharedCheck_1045_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v_x_1035_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1045_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
return v___x_1043_;
}
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1067_; 
v_a_1046_ = lean_ctor_get(v_x_1035_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_x_1035_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1048_ = v_x_1035_;
v_isShared_1049_ = v_isSharedCheck_1067_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v_x_1035_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1067_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v_val_1051_; uint8_t v___x_1056_; 
v___x_1056_ = lean_unbox(v_a_1046_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; 
v___x_1057_ = lean_uv_signal_cancel(v_s_1034_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; lean_object* v___x_1060_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1058_);
lean_dec_ref(v___x_1057_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v_a_1058_);
v___x_1060_ = v___x_1048_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1058_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
v_val_1051_ = v___x_1060_;
goto v___jp_1050_;
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; 
v_a_1062_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1062_);
lean_dec_ref(v___x_1057_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set_tag(v___x_1048_, 0);
lean_ctor_set(v___x_1048_, 0, v_a_1062_);
v___x_1064_ = v___x_1048_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
v_val_1051_ = v___x_1064_;
goto v___jp_1050_;
}
}
}
else
{
lean_object* v___x_1066_; 
lean_del_object(v___x_1048_);
lean_dec(v_a_1046_);
lean_dec_ref(v___f_1033_);
v___x_1066_ = ((lean_object*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__2___closed__2));
return v___x_1066_;
}
v___jp_1050_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; lean_object* v___x_1055_; 
v___x_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1052_, 0, v_val_1051_);
v___x_1053_ = lean_unsigned_to_nat(0u);
v___x_1054_ = lean_unbox(v_a_1046_);
lean_dec(v_a_1046_);
v___x_1055_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1053_, v___x_1054_, v___x_1052_, v___f_1033_);
return v___x_1055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__2___boxed(lean_object* v___f_1068_, lean_object* v_s_1069_, lean_object* v_x_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__2(v___f_1068_, v_s_1069_, v_x_1070_);
lean_dec(v_s_1069_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__3(lean_object* v_x_1073_){
_start:
{
if (lean_obj_tag(v_x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v___x_1075_; 
v_a_1074_ = lean_ctor_get(v_x_1073_, 0);
lean_inc(v_a_1074_);
lean_dec_ref(v_x_1073_);
v___x_1075_ = lean_task_pure(v_a_1074_);
return v___x_1075_;
}
else
{
lean_object* v_a_1076_; 
v_a_1076_ = lean_ctor_get(v_x_1073_, 0);
lean_inc_ref(v_a_1076_);
lean_dec_ref(v_x_1073_);
return v_a_1076_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__5(lean_object* v_s_1077_){
_start:
{
lean_object* v_val_1080_; lean_object* v___x_1082_; 
v___x_1082_ = lean_uv_signal_next(v_s_1077_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1095_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1085_ = v___x_1082_;
v_isShared_1086_ = v_isSharedCheck_1095_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1095_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___f_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___f_1087_ = ((lean_object*)(l_Std_Internal_IO_Async_Signal_Waiter_wait___closed__1));
v___x_1088_ = lean_io_promise_result_opt(v_a_1083_);
lean_dec(v_a_1083_);
v___x_1089_ = lean_unsigned_to_nat(0u);
v___x_1090_ = 1;
v___x_1091_ = lean_task_map(v___f_1087_, v___x_1088_, v___x_1089_, v___x_1090_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set_tag(v___x_1085_, 1);
lean_ctor_set(v___x_1085_, 0, v___x_1091_);
v___x_1093_ = v___x_1085_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
v_val_1080_ = v___x_1093_;
goto v___jp_1079_;
}
}
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
v_a_1096_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1082_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1082_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
lean_ctor_set_tag(v___x_1098_, 0);
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
v_val_1080_ = v___x_1101_;
goto v___jp_1079_;
}
}
}
v___jp_1079_:
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1081_, 0, v_val_1080_);
return v___x_1081_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__5___boxed(lean_object* v_s_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__5(v_s_1104_);
lean_dec(v_s_1104_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__4(lean_object* v___f_1107_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_apply_1(v___f_1107_, lean_box(0));
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__4___boxed(lean_object* v___f_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__4(v___f_1110_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__6(lean_object* v___x_1113_, lean_object* v___f_1114_, lean_object* v_x_1115_){
_start:
{
if (lean_obj_tag(v_x_1115_) == 0)
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1125_; 
lean_dec_ref(v___f_1114_);
lean_dec(v___x_1113_);
v_a_1117_ = lean_ctor_get(v_x_1115_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_x_1115_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1119_ = v_x_1115_;
v_isShared_1120_ = v_isSharedCheck_1125_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v_x_1115_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1125_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1123_; 
v___x_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
return v___x_1123_;
}
}
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1142_; 
v_a_1126_ = lean_ctor_get(v_x_1115_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_x_1115_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1128_ = v_x_1115_;
v_isShared_1129_ = v_isSharedCheck_1142_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v_x_1115_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1142_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
uint8_t v___x_1130_; uint8_t v_val_1132_; 
v___x_1130_ = lean_io_get_task_state(v_a_1126_);
lean_dec(v_a_1126_);
if (v___x_1130_ == 2)
{
uint8_t v___x_1140_; 
v___x_1140_ = 1;
v_val_1132_ = v___x_1140_;
goto v___jp_1131_;
}
else
{
uint8_t v___x_1141_; 
v___x_1141_ = 0;
v_val_1132_ = v___x_1141_;
goto v___jp_1131_;
}
v___jp_1131_:
{
lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1133_ = lean_box(v_val_1132_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 0, v___x_1133_);
v___x_1135_ = v___x_1128_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1136_; uint8_t v___x_1137_; lean_object* v___x_1138_; 
v___x_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
v___x_1137_ = 0;
v___x_1138_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1113_, v___x_1137_, v___x_1136_, v___f_1114_);
return v___x_1138_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__6___boxed(lean_object* v___x_1143_, lean_object* v___f_1144_, lean_object* v_x_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__6(v___x_1143_, v___f_1144_, v_x_1145_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__7(lean_object* v___f_1148_, lean_object* v___x_1149_, lean_object* v___f_1150_, lean_object* v___f_1151_){
_start:
{
lean_object* v___x_1153_; uint8_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; lean_object* v___x_1159_; 
lean_inc(v___x_1149_);
v___x_1153_ = lean_io_as_task(v___f_1148_, v___x_1149_);
v___x_1154_ = 1;
lean_inc(v___x_1149_);
v___x_1155_ = lean_task_bind(v___x_1153_, v___f_1150_, v___x_1149_, v___x_1154_);
v___x_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
v___x_1158_ = 0;
v___x_1159_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1149_, v___x_1158_, v___x_1157_, v___f_1151_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__7___boxed(lean_object* v___f_1160_, lean_object* v___x_1161_, lean_object* v___f_1162_, lean_object* v___f_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__7(v___f_1160_, v___x_1161_, v___f_1162_, v___f_1163_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__8(lean_object* v___x_1166_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1166_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__8___boxed(lean_object* v___x_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__8(v___x_1169_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__9(lean_object* v_waiter_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v_a_1178_; 
if (lean_obj_tag(v_a_1175_) == 0)
{
lean_object* v_a_1180_; 
v_a_1180_ = lean_ctor_get(v_a_1175_, 0);
lean_inc(v_a_1180_);
lean_dec_ref(v_a_1175_);
v_a_1178_ = v_a_1180_;
goto v___jp_1177_;
}
else
{
lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1191_; 
v_isSharedCheck_1191_ = !lean_is_exclusive(v_a_1175_);
if (v_isSharedCheck_1191_ == 0)
{
lean_object* v_unused_1192_; 
v_unused_1192_ = lean_ctor_get(v_a_1175_, 0);
lean_dec(v_unused_1192_);
v___x_1182_ = v_a_1175_;
v_isShared_1183_ = v_isSharedCheck_1191_;
goto v_resetjp_1181_;
}
else
{
lean_dec(v_a_1175_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1191_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___f_1184_; lean_object* v___x_1185_; 
v___f_1184_ = ((lean_object*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__9___closed__0));
v___x_1185_ = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Signal_Waiter_selector_spec__0(v_waiter_1174_, v___f_1184_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1188_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1186_);
lean_dec_ref(v___x_1185_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v_a_1186_);
v___x_1188_ = v___x_1182_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1186_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
else
{
lean_object* v_a_1190_; 
lean_del_object(v___x_1182_);
v_a_1190_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1190_);
lean_dec_ref(v___x_1185_);
v_a_1178_ = v_a_1190_;
goto v___jp_1177_;
}
}
}
v___jp_1177_:
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1179_, 0, v_a_1178_);
return v___x_1179_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__9___boxed(lean_object* v_waiter_1193_, lean_object* v_a_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__9(v_waiter_1193_, v_a_1194_);
lean_dec_ref(v_waiter_1193_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__10(lean_object* v___f_1199_, lean_object* v___x_1200_, lean_object* v_x_1201_){
_start:
{
if (lean_obj_tag(v_x_1201_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1211_; 
lean_dec(v___x_1200_);
lean_dec_ref(v___f_1199_);
v_a_1203_ = lean_ctor_get(v_x_1201_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_x_1201_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1205_ = v_x_1201_;
v_isShared_1206_ = v_isSharedCheck_1211_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v_x_1201_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1211_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1209_; 
v___x_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
return v___x_1209_;
}
}
}
else
{
lean_object* v_a_1212_; uint8_t v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v_a_1212_ = lean_ctor_get(v_x_1201_, 0);
lean_inc(v_a_1212_);
lean_dec_ref(v_x_1201_);
v___x_1213_ = 0;
v___x_1214_ = lean_io_map_task(v___f_1199_, v_a_1212_, v___x_1200_, v___x_1213_);
lean_dec_ref(v___x_1214_);
v___x_1215_ = ((lean_object*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__10___closed__0));
return v___x_1215_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__10___boxed(lean_object* v___f_1216_, lean_object* v___x_1217_, lean_object* v_x_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__10(v___f_1216_, v___x_1217_, v_x_1218_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__11(lean_object* v___f_1221_, lean_object* v___x_1222_, lean_object* v_waiter_1223_){
_start:
{
lean_object* v___x_1225_; lean_object* v___f_1226_; lean_object* v___f_1227_; uint8_t v___x_1228_; lean_object* v___x_1229_; 
v___x_1225_ = lean_apply_1(v___f_1221_, lean_box(0));
v___f_1226_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__9___boxed), 3, 1);
lean_closure_set(v___f_1226_, 0, v_waiter_1223_);
lean_inc(v___x_1222_);
v___f_1227_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__10___boxed), 4, 2);
lean_closure_set(v___f_1227_, 0, v___f_1226_);
lean_closure_set(v___f_1227_, 1, v___x_1222_);
v___x_1228_ = 0;
v___x_1229_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1222_, v___x_1228_, v___x_1225_, v___f_1227_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__11___boxed(lean_object* v___f_1230_, lean_object* v___x_1231_, lean_object* v_waiter_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__11(v___f_1230_, v___x_1231_, v_waiter_1232_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector(lean_object* v_s_1237_){
_start:
{
lean_object* v___f_1238_; lean_object* v___f_1239_; lean_object* v___f_1240_; lean_object* v___f_1241_; lean_object* v___f_1242_; lean_object* v___f_1243_; lean_object* v___x_1244_; lean_object* v___f_1245_; lean_object* v___f_1246_; lean_object* v___f_1247_; lean_object* v___x_1248_; 
lean_inc(v_s_1237_);
v___f_1238_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1238_, 0, v_s_1237_);
v___f_1239_ = ((lean_object*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___closed__0));
lean_inc(v_s_1237_);
v___f_1240_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1240_, 0, v___f_1239_);
lean_closure_set(v___f_1240_, 1, v_s_1237_);
v___f_1241_ = ((lean_object*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___closed__1));
v___f_1242_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__5___boxed), 2, 1);
lean_closure_set(v___f_1242_, 0, v_s_1237_);
lean_inc_ref(v___f_1242_);
v___f_1243_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__4___boxed), 2, 1);
lean_closure_set(v___f_1243_, 0, v___f_1242_);
v___x_1244_ = lean_unsigned_to_nat(0u);
v___f_1245_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__6___boxed), 4, 2);
lean_closure_set(v___f_1245_, 0, v___x_1244_);
lean_closure_set(v___f_1245_, 1, v___f_1240_);
v___f_1246_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__7___boxed), 5, 4);
lean_closure_set(v___f_1246_, 0, v___f_1243_);
lean_closure_set(v___f_1246_, 1, v___x_1244_);
lean_closure_set(v___f_1246_, 2, v___f_1241_);
lean_closure_set(v___f_1246_, 3, v___f_1245_);
v___f_1247_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__11___boxed), 4, 2);
lean_closure_set(v___f_1247_, 0, v___f_1242_);
lean_closure_set(v___f_1247_, 1, v___x_1244_);
v___x_1248_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1248_, 0, v___f_1246_);
lean_ctor_set(v___x_1248_, 1, v___f_1247_);
lean_ctor_set(v___x_1248_, 2, v___f_1238_);
return v___x_1248_;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_UV_Signal(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Async_Select(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Async_Signal(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_UV_Signal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Async_Select(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Async_Signal(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time(uint8_t builtin);
lean_object* initialize_Std_Internal_UV_Signal(uint8_t builtin);
lean_object* initialize_Std_Internal_Async_Select(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Async_Signal(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_UV_Signal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Async_Select(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Async_Signal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Async_Signal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Async_Signal(builtin);
}
#ifdef __cplusplus
}
#endif
