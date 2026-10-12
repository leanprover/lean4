// Lean compiler output
// Module: Std.Async.Signal
// Imports: public import Std.Time public import Std.Internal.UV.Signal public import Std.Async.Select
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
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_IO_Promise_isResolved___redArg(lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_uv_signal_cancel(lean_object*);
uint32_t lean_int32_of_nat(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_uv_signal_next(lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_uv_signal_stop(lean_object*);
lean_object* lean_uv_signal_mk(uint32_t, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sighup_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sighup_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sighup_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sighup_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigint_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigint_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigint_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigint_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigquit_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigquit_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigquit_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigquit_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtrap_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtrap_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtrap_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtrap_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigabrt_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigabrt_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigabrt_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigabrt_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr1_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr1_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr1_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr1_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr2_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr2_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr2_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr2_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigalrm_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigalrm_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigalrm_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigalrm_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigterm_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigterm_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigterm_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigterm_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigchld_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigchld_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigchld_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigchld_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigcont_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigcont_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigcont_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigcont_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtstp_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtstp_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtstp_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtstp_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttin_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttin_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttin_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttin_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttou_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttou_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttou_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttou_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigurg_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigurg_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigurg_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigurg_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxcpu_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxcpu_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxcpu_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxcpu_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxfsz_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxfsz_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxfsz_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxfsz_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigvtalrm_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigvtalrm_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigvtalrm_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigvtalrm_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigprof_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigprof_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigprof_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigprof_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigwinch_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigwinch_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigwinch_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigwinch_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigio_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigio_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigio_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigio_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigsys_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigsys_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigsys_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigsys_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Async.Signal.sighup"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__0 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__0_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__0_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__1 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__1_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Async.Signal.sigint"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__2 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__2_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__2_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__3 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__3_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigquit"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__4 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__4_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__4_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__5 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__5_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigtrap"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__6 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__6_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__6_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__7 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__7_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigabrt"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__8 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__8_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__8_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__9 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__9_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigusr1"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__10 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__10_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__10_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__11 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__11_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigusr2"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__12 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__12_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__12_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__13 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__13_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigalrm"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__14 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__14_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__14_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__15 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__15_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigterm"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__16 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__16_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__16_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__17 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__17_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigchld"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__18 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__18_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__18_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__19 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__19_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigcont"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__20 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__20_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__20_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__21 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__21_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigtstp"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__22 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__22_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__22_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__23 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__23_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigttin"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__24 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__24_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__24_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__25 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__25_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigttou"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__26 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__26_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__26_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__27 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__27_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Async.Signal.sigurg"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__28 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__28_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__28_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__29 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__29_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigxcpu"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__30 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__30_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__30_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__31 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__31_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigxfsz"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__32 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__32_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__32_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__33 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__33_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Std.Async.Signal.sigvtalrm"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__34 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__34_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__34_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__35 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__35_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigprof"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__36 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__36_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__36_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__37 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__37_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Std.Async.Signal.sigwinch"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__38 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__38_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__38_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__39 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__39_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Async.Signal.sigio"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__40 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__40_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__40_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__41 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__41_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Async.Signal.sigsys"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__42 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__42_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__42_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__43 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__43_value;
static lean_once_cell_t l_Std_Async_instReprSignal_repr___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_instReprSignal_repr___closed__44;
static lean_once_cell_t l_Std_Async_instReprSignal_repr___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_instReprSignal_repr___closed__45;
LEAN_EXPORT lean_object* l_Std_Async_instReprSignal_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instReprSignal_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_instReprSignal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_instReprSignal_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_instReprSignal___closed__0 = (const lean_object*)&l_Std_Async_instReprSignal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_instReprSignal = (const lean_object*)&l_Std_Async_instReprSignal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Async_Signal_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Async_instDecidableEqSignal(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_instDecidableEqSignal___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Async_instBEqSignal_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_instBEqSignal_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_instBEqSignal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_instBEqSignal_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_instBEqSignal___closed__0 = (const lean_object*)&l_Std_Async_instBEqSignal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_instBEqSignal = (const lean_object*)&l_Std_Async_instBEqSignal___closed__0_value;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21;
LEAN_EXPORT uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_mk(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_mk___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_wait___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Std_Async_Signal_Waiter_wait___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "the promise linked to the Async Task was dropped"};
static const lean_object* l_Std_Async_Signal_Waiter_wait___closed__0 = (const lean_object*)&l_Std_Async_Signal_Waiter_wait___closed__0_value;
static const lean_closure_object l_Std_Async_Signal_Waiter_wait___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Signal_Waiter_wait___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_Signal_Waiter_wait___closed__0_value)} };
static const lean_object* l_Std_Async_Signal_Waiter_wait___closed__1 = (const lean_object*)&l_Std_Async_Signal_Waiter_wait___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_wait(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_wait___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_stop(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_stop___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___closed__0 = (const lean_object*)&l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_Signal_Waiter_selector___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__0___closed__0 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Async_Signal_Waiter_selector___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__0___closed__0_value)}};
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__0___closed__1 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__0___closed__1_value;
static const lean_ctor_object l_Std_Async_Signal_Waiter_selector___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__0___closed__2 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__0___closed__2_value;
static const lean_ctor_object l_Std_Async_Signal_Waiter_selector___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__0___closed__2_value)}};
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__0___closed__3 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__0___closed__3_value;
static const lean_ctor_object l_Std_Async_Signal_Waiter_selector___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__0___closed__3_value)}};
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__0___closed__4 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__0___closed__4_value;
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Signal_Waiter_selector___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Signal_Waiter_selector___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__2___closed__0 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_Signal_Waiter_selector___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___closed__0_value)}};
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__3___closed__0 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__8___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Signal_Waiter_selector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Signal_Waiter_selector___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_Signal_Waiter_selector___closed__0 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector(lean_object*);
lean_object* l_Std_Async_Signal_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Std_Async_Signal_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Std_Async_Signal_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Std_Async_Signal_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Std_Async_Signal_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Std_Async_Signal_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Std_Async_Signal_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Std_Async_Signal_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Std_Async_Signal_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sighup_elim___redArg(lean_object* v_sighup_24_){
_start:
{
lean_inc(v_sighup_24_);
return v_sighup_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sighup_elim___redArg___boxed(lean_object* v_sighup_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_Async_Signal_sighup_elim___redArg(v_sighup_25_);
lean_dec(v_sighup_25_);
return v_res_26_;
}
}
lean_object* l_Std_Async_Signal_sighup_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_sighup_30_){
_start:
{
lean_inc(v_sighup_30_);
return v_sighup_30_;
}
}
LEAN_EXPORT void l_Std_Async_Signal_sighup_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_sighup_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Std_Async_Signal_sighup_elim(lean_box(0), v_t_28_, lean_box(0), v_sighup_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sighup_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_sighup_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Std_Async_Signal_sighup_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_sighup_35_);
lean_dec(v_sighup_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigint_elim___redArg(lean_object* v_sigint_38_){
_start:
{
lean_inc(v_sigint_38_);
return v_sigint_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigint_elim___redArg___boxed(lean_object* v_sigint_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_Async_Signal_sigint_elim___redArg(v_sigint_39_);
lean_dec(v_sigint_39_);
return v_res_40_;
}
}
lean_object* l_Std_Async_Signal_sigint_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_sigint_44_){
_start:
{
lean_inc(v_sigint_44_);
return v_sigint_44_;
}
}
LEAN_EXPORT void l_Std_Async_Signal_sigint_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_sigint_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Std_Async_Signal_sigint_elim(lean_box(0), v_t_42_, lean_box(0), v_sigint_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigint_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_sigint_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Std_Async_Signal_sigint_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_sigint_49_);
lean_dec(v_sigint_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigquit_elim___redArg(lean_object* v_sigquit_52_){
_start:
{
lean_inc(v_sigquit_52_);
return v_sigquit_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigquit_elim___redArg___boxed(lean_object* v_sigquit_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Std_Async_Signal_sigquit_elim___redArg(v_sigquit_53_);
lean_dec(v_sigquit_53_);
return v_res_54_;
}
}
lean_object* l_Std_Async_Signal_sigquit_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_sigquit_58_){
_start:
{
lean_inc(v_sigquit_58_);
return v_sigquit_58_;
}
}
LEAN_EXPORT void l_Std_Async_Signal_sigquit_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_sigquit_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Std_Async_Signal_sigquit_elim(lean_box(0), v_t_56_, lean_box(0), v_sigquit_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigquit_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_sigquit_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Std_Async_Signal_sigquit_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_sigquit_63_);
lean_dec(v_sigquit_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtrap_elim___redArg(lean_object* v_sigtrap_66_){
_start:
{
lean_inc(v_sigtrap_66_);
return v_sigtrap_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtrap_elim___redArg___boxed(lean_object* v_sigtrap_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Std_Async_Signal_sigtrap_elim___redArg(v_sigtrap_67_);
lean_dec(v_sigtrap_67_);
return v_res_68_;
}
}
lean_object* l_Std_Async_Signal_sigtrap_elim(lean_object* v_motive_69_, uint8_t v_t_70_, lean_object* v_h_71_, lean_object* v_sigtrap_72_){
_start:
{
lean_inc(v_sigtrap_72_);
return v_sigtrap_72_;
}
}
LEAN_EXPORT void l_Std_Async_Signal_sigtrap_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_70_ = stack[1].m_num;
lean_object* v_sigtrap_72_ = stack[3].m_obj;
lean_object* v_res_73_;
v_res_73_ = l_Std_Async_Signal_sigtrap_elim(lean_box(0), v_t_70_, lean_box(0), v_sigtrap_72_);
stack->m_obj
 = v_res_73_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtrap_elim___boxed(lean_object* v_motive_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_sigtrap_77_){
_start:
{
uint8_t v_t_boxed_78_; lean_object* v_res_79_; 
v_t_boxed_78_ = lean_unbox(v_t_75_);
v_res_79_ = l_Std_Async_Signal_sigtrap_elim(v_motive_74_, v_t_boxed_78_, v_h_76_, v_sigtrap_77_);
lean_dec(v_sigtrap_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigabrt_elim___redArg(lean_object* v_sigabrt_80_){
_start:
{
lean_inc(v_sigabrt_80_);
return v_sigabrt_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigabrt_elim___redArg___boxed(lean_object* v_sigabrt_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Std_Async_Signal_sigabrt_elim___redArg(v_sigabrt_81_);
lean_dec(v_sigabrt_81_);
return v_res_82_;
}
}
lean_object* l_Std_Async_Signal_sigabrt_elim(lean_object* v_motive_83_, uint8_t v_t_84_, lean_object* v_h_85_, lean_object* v_sigabrt_86_){
_start:
{
lean_inc(v_sigabrt_86_);
return v_sigabrt_86_;
}
}
LEAN_EXPORT void l_Std_Async_Signal_sigabrt_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_84_ = stack[1].m_num;
lean_object* v_sigabrt_86_ = stack[3].m_obj;
lean_object* v_res_87_;
v_res_87_ = l_Std_Async_Signal_sigabrt_elim(lean_box(0), v_t_84_, lean_box(0), v_sigabrt_86_);
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigabrt_elim___boxed(lean_object* v_motive_88_, lean_object* v_t_89_, lean_object* v_h_90_, lean_object* v_sigabrt_91_){
_start:
{
uint8_t v_t_boxed_92_; lean_object* v_res_93_; 
v_t_boxed_92_ = lean_unbox(v_t_89_);
v_res_93_ = l_Std_Async_Signal_sigabrt_elim(v_motive_88_, v_t_boxed_92_, v_h_90_, v_sigabrt_91_);
lean_dec(v_sigabrt_91_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr1_elim___redArg(lean_object* v_sigusr1_94_){
_start:
{
lean_inc(v_sigusr1_94_);
return v_sigusr1_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr1_elim___redArg___boxed(lean_object* v_sigusr1_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_Async_Signal_sigusr1_elim___redArg(v_sigusr1_95_);
lean_dec(v_sigusr1_95_);
return v_res_96_;
}
}
lean_object* l_Std_Async_Signal_sigusr1_elim(lean_object* v_motive_97_, uint8_t v_t_98_, lean_object* v_h_99_, lean_object* v_sigusr1_100_){
_start:
{
lean_inc(v_sigusr1_100_);
return v_sigusr1_100_;
}
}
LEAN_EXPORT void l_Std_Async_Signal_sigusr1_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_98_ = stack[1].m_num;
lean_object* v_sigusr1_100_ = stack[3].m_obj;
lean_object* v_res_101_;
v_res_101_ = l_Std_Async_Signal_sigusr1_elim(lean_box(0), v_t_98_, lean_box(0), v_sigusr1_100_);
stack->m_obj
 = v_res_101_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr1_elim___boxed(lean_object* v_motive_102_, lean_object* v_t_103_, lean_object* v_h_104_, lean_object* v_sigusr1_105_){
_start:
{
uint8_t v_t_boxed_106_; lean_object* v_res_107_; 
v_t_boxed_106_ = lean_unbox(v_t_103_);
v_res_107_ = l_Std_Async_Signal_sigusr1_elim(v_motive_102_, v_t_boxed_106_, v_h_104_, v_sigusr1_105_);
lean_dec(v_sigusr1_105_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr2_elim___redArg(lean_object* v_sigusr2_108_){
_start:
{
lean_inc(v_sigusr2_108_);
return v_sigusr2_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr2_elim___redArg___boxed(lean_object* v_sigusr2_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Std_Async_Signal_sigusr2_elim___redArg(v_sigusr2_109_);
lean_dec(v_sigusr2_109_);
return v_res_110_;
}
}
lean_object* l_Std_Async_Signal_sigusr2_elim(lean_object* v_motive_111_, uint8_t v_t_112_, lean_object* v_h_113_, lean_object* v_sigusr2_114_){
_start:
{
lean_inc(v_sigusr2_114_);
return v_sigusr2_114_;
}
}
LEAN_EXPORT void l_Std_Async_Signal_sigusr2_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_112_ = stack[1].m_num;
lean_object* v_sigusr2_114_ = stack[3].m_obj;
lean_object* v_res_115_;
v_res_115_ = l_Std_Async_Signal_sigusr2_elim(lean_box(0), v_t_112_, lean_box(0), v_sigusr2_114_);
stack->m_obj
 = v_res_115_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr2_elim___boxed(lean_object* v_motive_116_, lean_object* v_t_117_, lean_object* v_h_118_, lean_object* v_sigusr2_119_){
_start:
{
uint8_t v_t_boxed_120_; lean_object* v_res_121_; 
v_t_boxed_120_ = lean_unbox(v_t_117_);
v_res_121_ = l_Std_Async_Signal_sigusr2_elim(v_motive_116_, v_t_boxed_120_, v_h_118_, v_sigusr2_119_);
lean_dec(v_sigusr2_119_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigalrm_elim___redArg(lean_object* v_sigalrm_122_){
_start:
{
lean_inc(v_sigalrm_122_);
return v_sigalrm_122_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigalrm_elim___redArg___boxed(lean_object* v_sigalrm_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Std_Async_Signal_sigalrm_elim___redArg(v_sigalrm_123_);
lean_dec(v_sigalrm_123_);
return v_res_124_;
}
}
lean_object* l_Std_Async_Signal_sigalrm_elim(lean_object* v_motive_125_, uint8_t v_t_126_, lean_object* v_h_127_, lean_object* v_sigalrm_128_){
_start:
{
lean_inc(v_sigalrm_128_);
return v_sigalrm_128_;
}
}
LEAN_EXPORT void l_Std_Async_Signal_sigalrm_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_126_ = stack[1].m_num;
lean_object* v_sigalrm_128_ = stack[3].m_obj;
lean_object* v_res_129_;
v_res_129_ = l_Std_Async_Signal_sigalrm_elim(lean_box(0), v_t_126_, lean_box(0), v_sigalrm_128_);
stack->m_obj
 = v_res_129_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigalrm_elim___boxed(lean_object* v_motive_130_, lean_object* v_t_131_, lean_object* v_h_132_, lean_object* v_sigalrm_133_){
_start:
{
uint8_t v_t_boxed_134_; lean_object* v_res_135_; 
v_t_boxed_134_ = lean_unbox(v_t_131_);
v_res_135_ = l_Std_Async_Signal_sigalrm_elim(v_motive_130_, v_t_boxed_134_, v_h_132_, v_sigalrm_133_);
lean_dec(v_sigalrm_133_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigterm_elim___redArg(lean_object* v_sigterm_136_){
_start:
{
lean_inc(v_sigterm_136_);
return v_sigterm_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigterm_elim___redArg___boxed(lean_object* v_sigterm_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Std_Async_Signal_sigterm_elim___redArg(v_sigterm_137_);
lean_dec(v_sigterm_137_);
return v_res_138_;
}
}
lean_object* l_Std_Async_Signal_sigterm_elim(lean_object* v_motive_139_, uint8_t v_t_140_, lean_object* v_h_141_, lean_object* v_sigterm_142_){
_start:
{
lean_inc(v_sigterm_142_);
return v_sigterm_142_;
}
}
LEAN_EXPORT void l_Std_Async_Signal_sigterm_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_140_ = stack[1].m_num;
lean_object* v_sigterm_142_ = stack[3].m_obj;
lean_object* v_res_143_;
v_res_143_ = l_Std_Async_Signal_sigterm_elim(lean_box(0), v_t_140_, lean_box(0), v_sigterm_142_);
stack->m_obj
 = v_res_143_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigterm_elim___boxed(lean_object* v_motive_144_, lean_object* v_t_145_, lean_object* v_h_146_, lean_object* v_sigterm_147_){
_start:
{
uint8_t v_t_boxed_148_; lean_object* v_res_149_; 
v_t_boxed_148_ = lean_unbox(v_t_145_);
v_res_149_ = l_Std_Async_Signal_sigterm_elim(v_motive_144_, v_t_boxed_148_, v_h_146_, v_sigterm_147_);
lean_dec(v_sigterm_147_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigchld_elim___redArg(lean_object* v_sigchld_150_){
_start:
{
lean_inc(v_sigchld_150_);
return v_sigchld_150_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigchld_elim___redArg___boxed(lean_object* v_sigchld_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Std_Async_Signal_sigchld_elim___redArg(v_sigchld_151_);
lean_dec(v_sigchld_151_);
return v_res_152_;
}
}
lean_object* l_Std_Async_Signal_sigchld_elim(lean_object* v_motive_153_, uint8_t v_t_154_, lean_object* v_h_155_, lean_object* v_sigchld_156_){
_start:
{
lean_inc(v_sigchld_156_);
return v_sigchld_156_;
}
}
LEAN_EXPORT void l_Std_Async_Signal_sigchld_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_154_ = stack[1].m_num;
lean_object* v_sigchld_156_ = stack[3].m_obj;
lean_object* v_res_157_;
v_res_157_ = l_Std_Async_Signal_sigchld_elim(lean_box(0), v_t_154_, lean_box(0), v_sigchld_156_);
stack->m_obj
 = v_res_157_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigchld_elim___boxed(lean_object* v_motive_158_, lean_object* v_t_159_, lean_object* v_h_160_, lean_object* v_sigchld_161_){
_start:
{
uint8_t v_t_boxed_162_; lean_object* v_res_163_; 
v_t_boxed_162_ = lean_unbox(v_t_159_);
v_res_163_ = l_Std_Async_Signal_sigchld_elim(v_motive_158_, v_t_boxed_162_, v_h_160_, v_sigchld_161_);
lean_dec(v_sigchld_161_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigcont_elim___redArg(lean_object* v_sigcont_164_){
_start:
{
lean_inc(v_sigcont_164_);
return v_sigcont_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigcont_elim___redArg___boxed(lean_object* v_sigcont_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_Async_Signal_sigcont_elim___redArg(v_sigcont_165_);
lean_dec(v_sigcont_165_);
return v_res_166_;
}
}
lean_object* l_Std_Async_Signal_sigcont_elim(lean_object* v_motive_167_, uint8_t v_t_168_, lean_object* v_h_169_, lean_object* v_sigcont_170_){
_start:
{
lean_inc(v_sigcont_170_);
return v_sigcont_170_;
}
}
LEAN_EXPORT void l_Std_Async_Signal_sigcont_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_168_ = stack[1].m_num;
lean_object* v_sigcont_170_ = stack[3].m_obj;
lean_object* v_res_171_;
v_res_171_ = l_Std_Async_Signal_sigcont_elim(lean_box(0), v_t_168_, lean_box(0), v_sigcont_170_);
stack->m_obj
 = v_res_171_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigcont_elim___boxed(lean_object* v_motive_172_, lean_object* v_t_173_, lean_object* v_h_174_, lean_object* v_sigcont_175_){
_start:
{
uint8_t v_t_boxed_176_; lean_object* v_res_177_; 
v_t_boxed_176_ = lean_unbox(v_t_173_);
v_res_177_ = l_Std_Async_Signal_sigcont_elim(v_motive_172_, v_t_boxed_176_, v_h_174_, v_sigcont_175_);
lean_dec(v_sigcont_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtstp_elim___redArg(lean_object* v_sigtstp_178_){
_start:
{
lean_inc(v_sigtstp_178_);
return v_sigtstp_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtstp_elim___redArg___boxed(lean_object* v_sigtstp_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Std_Async_Signal_sigtstp_elim___redArg(v_sigtstp_179_);
lean_dec(v_sigtstp_179_);
return v_res_180_;
}
}
lean_object* l_Std_Async_Signal_sigtstp_elim(lean_object* v_motive_181_, uint8_t v_t_182_, lean_object* v_h_183_, lean_object* v_sigtstp_184_){
_start:
{
lean_inc(v_sigtstp_184_);
return v_sigtstp_184_;
}
}
LEAN_EXPORT void l_Std_Async_Signal_sigtstp_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_182_ = stack[1].m_num;
lean_object* v_sigtstp_184_ = stack[3].m_obj;
lean_object* v_res_185_;
v_res_185_ = l_Std_Async_Signal_sigtstp_elim(lean_box(0), v_t_182_, lean_box(0), v_sigtstp_184_);
stack->m_obj
 = v_res_185_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtstp_elim___boxed(lean_object* v_motive_186_, lean_object* v_t_187_, lean_object* v_h_188_, lean_object* v_sigtstp_189_){
_start:
{
uint8_t v_t_boxed_190_; lean_object* v_res_191_; 
v_t_boxed_190_ = lean_unbox(v_t_187_);
v_res_191_ = l_Std_Async_Signal_sigtstp_elim(v_motive_186_, v_t_boxed_190_, v_h_188_, v_sigtstp_189_);
lean_dec(v_sigtstp_189_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttin_elim___redArg(lean_object* v_sigttin_192_){
_start:
{
lean_inc(v_sigttin_192_);
return v_sigttin_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttin_elim___redArg___boxed(lean_object* v_sigttin_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Std_Async_Signal_sigttin_elim___redArg(v_sigttin_193_);
lean_dec(v_sigttin_193_);
return v_res_194_;
}
}
lean_object* l_Std_Async_Signal_sigttin_elim(lean_object* v_motive_195_, uint8_t v_t_196_, lean_object* v_h_197_, lean_object* v_sigttin_198_){
_start:
{
lean_inc(v_sigttin_198_);
return v_sigttin_198_;
}
}
LEAN_EXPORT void l_Std_Async_Signal_sigttin_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_196_ = stack[1].m_num;
lean_object* v_sigttin_198_ = stack[3].m_obj;
lean_object* v_res_199_;
v_res_199_ = l_Std_Async_Signal_sigttin_elim(lean_box(0), v_t_196_, lean_box(0), v_sigttin_198_);
stack->m_obj
 = v_res_199_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttin_elim___boxed(lean_object* v_motive_200_, lean_object* v_t_201_, lean_object* v_h_202_, lean_object* v_sigttin_203_){
_start:
{
uint8_t v_t_boxed_204_; lean_object* v_res_205_; 
v_t_boxed_204_ = lean_unbox(v_t_201_);
v_res_205_ = l_Std_Async_Signal_sigttin_elim(v_motive_200_, v_t_boxed_204_, v_h_202_, v_sigttin_203_);
lean_dec(v_sigttin_203_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttou_elim___redArg(lean_object* v_sigttou_206_){
_start:
{
lean_inc(v_sigttou_206_);
return v_sigttou_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttou_elim___redArg___boxed(lean_object* v_sigttou_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_Async_Signal_sigttou_elim___redArg(v_sigttou_207_);
lean_dec(v_sigttou_207_);
return v_res_208_;
}
}
lean_object* l_Std_Async_Signal_sigttou_elim(lean_object* v_motive_209_, uint8_t v_t_210_, lean_object* v_h_211_, lean_object* v_sigttou_212_){
_start:
{
lean_inc(v_sigttou_212_);
return v_sigttou_212_;
}
}
LEAN_EXPORT void l_Std_Async_Signal_sigttou_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_210_ = stack[1].m_num;
lean_object* v_sigttou_212_ = stack[3].m_obj;
lean_object* v_res_213_;
v_res_213_ = l_Std_Async_Signal_sigttou_elim(lean_box(0), v_t_210_, lean_box(0), v_sigttou_212_);
stack->m_obj
 = v_res_213_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttou_elim___boxed(lean_object* v_motive_214_, lean_object* v_t_215_, lean_object* v_h_216_, lean_object* v_sigttou_217_){
_start:
{
uint8_t v_t_boxed_218_; lean_object* v_res_219_; 
v_t_boxed_218_ = lean_unbox(v_t_215_);
v_res_219_ = l_Std_Async_Signal_sigttou_elim(v_motive_214_, v_t_boxed_218_, v_h_216_, v_sigttou_217_);
lean_dec(v_sigttou_217_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigurg_elim___redArg(lean_object* v_sigurg_220_){
_start:
{
lean_inc(v_sigurg_220_);
return v_sigurg_220_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigurg_elim___redArg___boxed(lean_object* v_sigurg_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Std_Async_Signal_sigurg_elim___redArg(v_sigurg_221_);
lean_dec(v_sigurg_221_);
return v_res_222_;
}
}
lean_object* l_Std_Async_Signal_sigurg_elim(lean_object* v_motive_223_, uint8_t v_t_224_, lean_object* v_h_225_, lean_object* v_sigurg_226_){
_start:
{
lean_inc(v_sigurg_226_);
return v_sigurg_226_;
}
}
LEAN_EXPORT void l_Std_Async_Signal_sigurg_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_224_ = stack[1].m_num;
lean_object* v_sigurg_226_ = stack[3].m_obj;
lean_object* v_res_227_;
v_res_227_ = l_Std_Async_Signal_sigurg_elim(lean_box(0), v_t_224_, lean_box(0), v_sigurg_226_);
stack->m_obj
 = v_res_227_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigurg_elim___boxed(lean_object* v_motive_228_, lean_object* v_t_229_, lean_object* v_h_230_, lean_object* v_sigurg_231_){
_start:
{
uint8_t v_t_boxed_232_; lean_object* v_res_233_; 
v_t_boxed_232_ = lean_unbox(v_t_229_);
v_res_233_ = l_Std_Async_Signal_sigurg_elim(v_motive_228_, v_t_boxed_232_, v_h_230_, v_sigurg_231_);
lean_dec(v_sigurg_231_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxcpu_elim___redArg(lean_object* v_sigxcpu_234_){
_start:
{
lean_inc(v_sigxcpu_234_);
return v_sigxcpu_234_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxcpu_elim___redArg___boxed(lean_object* v_sigxcpu_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Std_Async_Signal_sigxcpu_elim___redArg(v_sigxcpu_235_);
lean_dec(v_sigxcpu_235_);
return v_res_236_;
}
}
lean_object* l_Std_Async_Signal_sigxcpu_elim(lean_object* v_motive_237_, uint8_t v_t_238_, lean_object* v_h_239_, lean_object* v_sigxcpu_240_){
_start:
{
lean_inc(v_sigxcpu_240_);
return v_sigxcpu_240_;
}
}
LEAN_EXPORT void l_Std_Async_Signal_sigxcpu_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_238_ = stack[1].m_num;
lean_object* v_sigxcpu_240_ = stack[3].m_obj;
lean_object* v_res_241_;
v_res_241_ = l_Std_Async_Signal_sigxcpu_elim(lean_box(0), v_t_238_, lean_box(0), v_sigxcpu_240_);
stack->m_obj
 = v_res_241_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxcpu_elim___boxed(lean_object* v_motive_242_, lean_object* v_t_243_, lean_object* v_h_244_, lean_object* v_sigxcpu_245_){
_start:
{
uint8_t v_t_boxed_246_; lean_object* v_res_247_; 
v_t_boxed_246_ = lean_unbox(v_t_243_);
v_res_247_ = l_Std_Async_Signal_sigxcpu_elim(v_motive_242_, v_t_boxed_246_, v_h_244_, v_sigxcpu_245_);
lean_dec(v_sigxcpu_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxfsz_elim___redArg(lean_object* v_sigxfsz_248_){
_start:
{
lean_inc(v_sigxfsz_248_);
return v_sigxfsz_248_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxfsz_elim___redArg___boxed(lean_object* v_sigxfsz_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Std_Async_Signal_sigxfsz_elim___redArg(v_sigxfsz_249_);
lean_dec(v_sigxfsz_249_);
return v_res_250_;
}
}
lean_object* l_Std_Async_Signal_sigxfsz_elim(lean_object* v_motive_251_, uint8_t v_t_252_, lean_object* v_h_253_, lean_object* v_sigxfsz_254_){
_start:
{
lean_inc(v_sigxfsz_254_);
return v_sigxfsz_254_;
}
}
LEAN_EXPORT void l_Std_Async_Signal_sigxfsz_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_252_ = stack[1].m_num;
lean_object* v_sigxfsz_254_ = stack[3].m_obj;
lean_object* v_res_255_;
v_res_255_ = l_Std_Async_Signal_sigxfsz_elim(lean_box(0), v_t_252_, lean_box(0), v_sigxfsz_254_);
stack->m_obj
 = v_res_255_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxfsz_elim___boxed(lean_object* v_motive_256_, lean_object* v_t_257_, lean_object* v_h_258_, lean_object* v_sigxfsz_259_){
_start:
{
uint8_t v_t_boxed_260_; lean_object* v_res_261_; 
v_t_boxed_260_ = lean_unbox(v_t_257_);
v_res_261_ = l_Std_Async_Signal_sigxfsz_elim(v_motive_256_, v_t_boxed_260_, v_h_258_, v_sigxfsz_259_);
lean_dec(v_sigxfsz_259_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigvtalrm_elim___redArg(lean_object* v_sigvtalrm_262_){
_start:
{
lean_inc(v_sigvtalrm_262_);
return v_sigvtalrm_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigvtalrm_elim___redArg___boxed(lean_object* v_sigvtalrm_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Std_Async_Signal_sigvtalrm_elim___redArg(v_sigvtalrm_263_);
lean_dec(v_sigvtalrm_263_);
return v_res_264_;
}
}
lean_object* l_Std_Async_Signal_sigvtalrm_elim(lean_object* v_motive_265_, uint8_t v_t_266_, lean_object* v_h_267_, lean_object* v_sigvtalrm_268_){
_start:
{
lean_inc(v_sigvtalrm_268_);
return v_sigvtalrm_268_;
}
}
LEAN_EXPORT void l_Std_Async_Signal_sigvtalrm_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_266_ = stack[1].m_num;
lean_object* v_sigvtalrm_268_ = stack[3].m_obj;
lean_object* v_res_269_;
v_res_269_ = l_Std_Async_Signal_sigvtalrm_elim(lean_box(0), v_t_266_, lean_box(0), v_sigvtalrm_268_);
stack->m_obj
 = v_res_269_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigvtalrm_elim___boxed(lean_object* v_motive_270_, lean_object* v_t_271_, lean_object* v_h_272_, lean_object* v_sigvtalrm_273_){
_start:
{
uint8_t v_t_boxed_274_; lean_object* v_res_275_; 
v_t_boxed_274_ = lean_unbox(v_t_271_);
v_res_275_ = l_Std_Async_Signal_sigvtalrm_elim(v_motive_270_, v_t_boxed_274_, v_h_272_, v_sigvtalrm_273_);
lean_dec(v_sigvtalrm_273_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigprof_elim___redArg(lean_object* v_sigprof_276_){
_start:
{
lean_inc(v_sigprof_276_);
return v_sigprof_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigprof_elim___redArg___boxed(lean_object* v_sigprof_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Std_Async_Signal_sigprof_elim___redArg(v_sigprof_277_);
lean_dec(v_sigprof_277_);
return v_res_278_;
}
}
lean_object* l_Std_Async_Signal_sigprof_elim(lean_object* v_motive_279_, uint8_t v_t_280_, lean_object* v_h_281_, lean_object* v_sigprof_282_){
_start:
{
lean_inc(v_sigprof_282_);
return v_sigprof_282_;
}
}
LEAN_EXPORT void l_Std_Async_Signal_sigprof_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_280_ = stack[1].m_num;
lean_object* v_sigprof_282_ = stack[3].m_obj;
lean_object* v_res_283_;
v_res_283_ = l_Std_Async_Signal_sigprof_elim(lean_box(0), v_t_280_, lean_box(0), v_sigprof_282_);
stack->m_obj
 = v_res_283_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigprof_elim___boxed(lean_object* v_motive_284_, lean_object* v_t_285_, lean_object* v_h_286_, lean_object* v_sigprof_287_){
_start:
{
uint8_t v_t_boxed_288_; lean_object* v_res_289_; 
v_t_boxed_288_ = lean_unbox(v_t_285_);
v_res_289_ = l_Std_Async_Signal_sigprof_elim(v_motive_284_, v_t_boxed_288_, v_h_286_, v_sigprof_287_);
lean_dec(v_sigprof_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigwinch_elim___redArg(lean_object* v_sigwinch_290_){
_start:
{
lean_inc(v_sigwinch_290_);
return v_sigwinch_290_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigwinch_elim___redArg___boxed(lean_object* v_sigwinch_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Std_Async_Signal_sigwinch_elim___redArg(v_sigwinch_291_);
lean_dec(v_sigwinch_291_);
return v_res_292_;
}
}
lean_object* l_Std_Async_Signal_sigwinch_elim(lean_object* v_motive_293_, uint8_t v_t_294_, lean_object* v_h_295_, lean_object* v_sigwinch_296_){
_start:
{
lean_inc(v_sigwinch_296_);
return v_sigwinch_296_;
}
}
LEAN_EXPORT void l_Std_Async_Signal_sigwinch_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_294_ = stack[1].m_num;
lean_object* v_sigwinch_296_ = stack[3].m_obj;
lean_object* v_res_297_;
v_res_297_ = l_Std_Async_Signal_sigwinch_elim(lean_box(0), v_t_294_, lean_box(0), v_sigwinch_296_);
stack->m_obj
 = v_res_297_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigwinch_elim___boxed(lean_object* v_motive_298_, lean_object* v_t_299_, lean_object* v_h_300_, lean_object* v_sigwinch_301_){
_start:
{
uint8_t v_t_boxed_302_; lean_object* v_res_303_; 
v_t_boxed_302_ = lean_unbox(v_t_299_);
v_res_303_ = l_Std_Async_Signal_sigwinch_elim(v_motive_298_, v_t_boxed_302_, v_h_300_, v_sigwinch_301_);
lean_dec(v_sigwinch_301_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigio_elim___redArg(lean_object* v_sigio_304_){
_start:
{
lean_inc(v_sigio_304_);
return v_sigio_304_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigio_elim___redArg___boxed(lean_object* v_sigio_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Std_Async_Signal_sigio_elim___redArg(v_sigio_305_);
lean_dec(v_sigio_305_);
return v_res_306_;
}
}
lean_object* l_Std_Async_Signal_sigio_elim(lean_object* v_motive_307_, uint8_t v_t_308_, lean_object* v_h_309_, lean_object* v_sigio_310_){
_start:
{
lean_inc(v_sigio_310_);
return v_sigio_310_;
}
}
LEAN_EXPORT void l_Std_Async_Signal_sigio_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_308_ = stack[1].m_num;
lean_object* v_sigio_310_ = stack[3].m_obj;
lean_object* v_res_311_;
v_res_311_ = l_Std_Async_Signal_sigio_elim(lean_box(0), v_t_308_, lean_box(0), v_sigio_310_);
stack->m_obj
 = v_res_311_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigio_elim___boxed(lean_object* v_motive_312_, lean_object* v_t_313_, lean_object* v_h_314_, lean_object* v_sigio_315_){
_start:
{
uint8_t v_t_boxed_316_; lean_object* v_res_317_; 
v_t_boxed_316_ = lean_unbox(v_t_313_);
v_res_317_ = l_Std_Async_Signal_sigio_elim(v_motive_312_, v_t_boxed_316_, v_h_314_, v_sigio_315_);
lean_dec(v_sigio_315_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigsys_elim___redArg(lean_object* v_sigsys_318_){
_start:
{
lean_inc(v_sigsys_318_);
return v_sigsys_318_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigsys_elim___redArg___boxed(lean_object* v_sigsys_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Std_Async_Signal_sigsys_elim___redArg(v_sigsys_319_);
lean_dec(v_sigsys_319_);
return v_res_320_;
}
}
lean_object* l_Std_Async_Signal_sigsys_elim(lean_object* v_motive_321_, uint8_t v_t_322_, lean_object* v_h_323_, lean_object* v_sigsys_324_){
_start:
{
lean_inc(v_sigsys_324_);
return v_sigsys_324_;
}
}
LEAN_EXPORT void l_Std_Async_Signal_sigsys_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_322_ = stack[1].m_num;
lean_object* v_sigsys_324_ = stack[3].m_obj;
lean_object* v_res_325_;
v_res_325_ = l_Std_Async_Signal_sigsys_elim(lean_box(0), v_t_322_, lean_box(0), v_sigsys_324_);
stack->m_obj
 = v_res_325_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigsys_elim___boxed(lean_object* v_motive_326_, lean_object* v_t_327_, lean_object* v_h_328_, lean_object* v_sigsys_329_){
_start:
{
uint8_t v_t_boxed_330_; lean_object* v_res_331_; 
v_t_boxed_330_ = lean_unbox(v_t_327_);
v_res_331_ = l_Std_Async_Signal_sigsys_elim(v_motive_326_, v_t_boxed_330_, v_h_328_, v_sigsys_329_);
lean_dec(v_sigsys_329_);
return v_res_331_;
}
}
static lean_object* _init_l_Std_Async_instReprSignal_repr___closed__44(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = lean_unsigned_to_nat(2u);
v___x_399_ = lean_nat_to_int(v___x_398_);
return v___x_399_;
}
}
static lean_object* _init_l_Std_Async_instReprSignal_repr___closed__45(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = lean_unsigned_to_nat(1u);
v___x_401_ = lean_nat_to_int(v___x_400_);
return v___x_401_;
}
}
lean_object* l_Std_Async_instReprSignal_repr(uint8_t v_x_402_, lean_object* v_prec_403_){
_start:
{
lean_object* v___y_405_; lean_object* v___y_412_; lean_object* v___y_419_; lean_object* v___y_426_; lean_object* v___y_433_; lean_object* v___y_440_; lean_object* v___y_447_; lean_object* v___y_454_; lean_object* v___y_461_; lean_object* v___y_468_; lean_object* v___y_475_; lean_object* v___y_482_; lean_object* v___y_489_; lean_object* v___y_496_; lean_object* v___y_503_; lean_object* v___y_510_; lean_object* v___y_517_; lean_object* v___y_524_; lean_object* v___y_531_; lean_object* v___y_538_; lean_object* v___y_545_; lean_object* v___y_552_; 
switch(v_x_402_)
{
case 0:
{
lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_558_ = lean_unsigned_to_nat(1024u);
v___x_559_ = lean_nat_dec_le(v___x_558_, v_prec_403_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; 
v___x_560_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_405_ = v___x_560_;
goto v___jp_404_;
}
else
{
lean_object* v___x_561_; 
v___x_561_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_405_ = v___x_561_;
goto v___jp_404_;
}
}
case 1:
{
lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_562_ = lean_unsigned_to_nat(1024u);
v___x_563_ = lean_nat_dec_le(v___x_562_, v_prec_403_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; 
v___x_564_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_412_ = v___x_564_;
goto v___jp_411_;
}
else
{
lean_object* v___x_565_; 
v___x_565_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_412_ = v___x_565_;
goto v___jp_411_;
}
}
case 2:
{
lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_566_ = lean_unsigned_to_nat(1024u);
v___x_567_ = lean_nat_dec_le(v___x_566_, v_prec_403_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; 
v___x_568_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_419_ = v___x_568_;
goto v___jp_418_;
}
else
{
lean_object* v___x_569_; 
v___x_569_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_419_ = v___x_569_;
goto v___jp_418_;
}
}
case 3:
{
lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_570_ = lean_unsigned_to_nat(1024u);
v___x_571_ = lean_nat_dec_le(v___x_570_, v_prec_403_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; 
v___x_572_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_426_ = v___x_572_;
goto v___jp_425_;
}
else
{
lean_object* v___x_573_; 
v___x_573_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_426_ = v___x_573_;
goto v___jp_425_;
}
}
case 4:
{
lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_574_ = lean_unsigned_to_nat(1024u);
v___x_575_ = lean_nat_dec_le(v___x_574_, v_prec_403_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; 
v___x_576_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_433_ = v___x_576_;
goto v___jp_432_;
}
else
{
lean_object* v___x_577_; 
v___x_577_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_433_ = v___x_577_;
goto v___jp_432_;
}
}
case 5:
{
lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_578_ = lean_unsigned_to_nat(1024u);
v___x_579_ = lean_nat_dec_le(v___x_578_, v_prec_403_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; 
v___x_580_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_440_ = v___x_580_;
goto v___jp_439_;
}
else
{
lean_object* v___x_581_; 
v___x_581_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_440_ = v___x_581_;
goto v___jp_439_;
}
}
case 6:
{
lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_582_ = lean_unsigned_to_nat(1024u);
v___x_583_ = lean_nat_dec_le(v___x_582_, v_prec_403_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; 
v___x_584_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_447_ = v___x_584_;
goto v___jp_446_;
}
else
{
lean_object* v___x_585_; 
v___x_585_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_447_ = v___x_585_;
goto v___jp_446_;
}
}
case 7:
{
lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(1024u);
v___x_587_ = lean_nat_dec_le(v___x_586_, v_prec_403_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; 
v___x_588_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_454_ = v___x_588_;
goto v___jp_453_;
}
else
{
lean_object* v___x_589_; 
v___x_589_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_454_ = v___x_589_;
goto v___jp_453_;
}
}
case 8:
{
lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_590_ = lean_unsigned_to_nat(1024u);
v___x_591_ = lean_nat_dec_le(v___x_590_, v_prec_403_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; 
v___x_592_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_461_ = v___x_592_;
goto v___jp_460_;
}
else
{
lean_object* v___x_593_; 
v___x_593_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_461_ = v___x_593_;
goto v___jp_460_;
}
}
case 9:
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = lean_unsigned_to_nat(1024u);
v___x_595_ = lean_nat_dec_le(v___x_594_, v_prec_403_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
v___x_596_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_468_ = v___x_596_;
goto v___jp_467_;
}
else
{
lean_object* v___x_597_; 
v___x_597_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_468_ = v___x_597_;
goto v___jp_467_;
}
}
case 10:
{
lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_598_ = lean_unsigned_to_nat(1024u);
v___x_599_ = lean_nat_dec_le(v___x_598_, v_prec_403_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; 
v___x_600_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_475_ = v___x_600_;
goto v___jp_474_;
}
else
{
lean_object* v___x_601_; 
v___x_601_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_475_ = v___x_601_;
goto v___jp_474_;
}
}
case 11:
{
lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_602_ = lean_unsigned_to_nat(1024u);
v___x_603_ = lean_nat_dec_le(v___x_602_, v_prec_403_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; 
v___x_604_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_482_ = v___x_604_;
goto v___jp_481_;
}
else
{
lean_object* v___x_605_; 
v___x_605_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_482_ = v___x_605_;
goto v___jp_481_;
}
}
case 12:
{
lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = lean_unsigned_to_nat(1024u);
v___x_607_ = lean_nat_dec_le(v___x_606_, v_prec_403_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; 
v___x_608_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_489_ = v___x_608_;
goto v___jp_488_;
}
else
{
lean_object* v___x_609_; 
v___x_609_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_489_ = v___x_609_;
goto v___jp_488_;
}
}
case 13:
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = lean_unsigned_to_nat(1024u);
v___x_611_ = lean_nat_dec_le(v___x_610_, v_prec_403_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; 
v___x_612_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_496_ = v___x_612_;
goto v___jp_495_;
}
else
{
lean_object* v___x_613_; 
v___x_613_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_496_ = v___x_613_;
goto v___jp_495_;
}
}
case 14:
{
lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_614_ = lean_unsigned_to_nat(1024u);
v___x_615_ = lean_nat_dec_le(v___x_614_, v_prec_403_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; 
v___x_616_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_503_ = v___x_616_;
goto v___jp_502_;
}
else
{
lean_object* v___x_617_; 
v___x_617_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_503_ = v___x_617_;
goto v___jp_502_;
}
}
case 15:
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = lean_unsigned_to_nat(1024u);
v___x_619_ = lean_nat_dec_le(v___x_618_, v_prec_403_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
v___x_620_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_510_ = v___x_620_;
goto v___jp_509_;
}
else
{
lean_object* v___x_621_; 
v___x_621_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_510_ = v___x_621_;
goto v___jp_509_;
}
}
case 16:
{
lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_622_ = lean_unsigned_to_nat(1024u);
v___x_623_ = lean_nat_dec_le(v___x_622_, v_prec_403_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; 
v___x_624_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_517_ = v___x_624_;
goto v___jp_516_;
}
else
{
lean_object* v___x_625_; 
v___x_625_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_517_ = v___x_625_;
goto v___jp_516_;
}
}
case 17:
{
lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_626_ = lean_unsigned_to_nat(1024u);
v___x_627_ = lean_nat_dec_le(v___x_626_, v_prec_403_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; 
v___x_628_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_524_ = v___x_628_;
goto v___jp_523_;
}
else
{
lean_object* v___x_629_; 
v___x_629_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_524_ = v___x_629_;
goto v___jp_523_;
}
}
case 18:
{
lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_630_ = lean_unsigned_to_nat(1024u);
v___x_631_ = lean_nat_dec_le(v___x_630_, v_prec_403_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; 
v___x_632_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_531_ = v___x_632_;
goto v___jp_530_;
}
else
{
lean_object* v___x_633_; 
v___x_633_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_531_ = v___x_633_;
goto v___jp_530_;
}
}
case 19:
{
lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_634_ = lean_unsigned_to_nat(1024u);
v___x_635_ = lean_nat_dec_le(v___x_634_, v_prec_403_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; 
v___x_636_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_538_ = v___x_636_;
goto v___jp_537_;
}
else
{
lean_object* v___x_637_; 
v___x_637_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_538_ = v___x_637_;
goto v___jp_537_;
}
}
case 20:
{
lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_638_ = lean_unsigned_to_nat(1024u);
v___x_639_ = lean_nat_dec_le(v___x_638_, v_prec_403_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; 
v___x_640_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_545_ = v___x_640_;
goto v___jp_544_;
}
else
{
lean_object* v___x_641_; 
v___x_641_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_545_ = v___x_641_;
goto v___jp_544_;
}
}
default: 
{
lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_642_ = lean_unsigned_to_nat(1024u);
v___x_643_ = lean_nat_dec_le(v___x_642_, v_prec_403_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; 
v___x_644_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_552_ = v___x_644_;
goto v___jp_551_;
}
else
{
lean_object* v___x_645_; 
v___x_645_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_552_ = v___x_645_;
goto v___jp_551_;
}
}
}
v___jp_404_:
{
lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_406_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__1));
lean_inc(v___y_405_);
v___x_407_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_407_, 0, v___y_405_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = 0;
v___x_409_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_409_, 0, v___x_407_);
lean_ctor_set_uint8(v___x_409_, sizeof(void*)*1, v___x_408_);
v___x_410_ = l_Repr_addAppParen(v___x_409_, v_prec_403_);
return v___x_410_;
}
v___jp_411_:
{
lean_object* v___x_413_; lean_object* v___x_414_; uint8_t v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_413_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__3));
lean_inc(v___y_412_);
v___x_414_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_414_, 0, v___y_412_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
v___x_415_ = 0;
v___x_416_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_416_, 0, v___x_414_);
lean_ctor_set_uint8(v___x_416_, sizeof(void*)*1, v___x_415_);
v___x_417_ = l_Repr_addAppParen(v___x_416_, v_prec_403_);
return v___x_417_;
}
v___jp_418_:
{
lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_420_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__5));
lean_inc(v___y_419_);
v___x_421_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_421_, 0, v___y_419_);
lean_ctor_set(v___x_421_, 1, v___x_420_);
v___x_422_ = 0;
v___x_423_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_423_, 0, v___x_421_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*1, v___x_422_);
v___x_424_ = l_Repr_addAppParen(v___x_423_, v_prec_403_);
return v___x_424_;
}
v___jp_425_:
{
lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_427_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__7));
lean_inc(v___y_426_);
v___x_428_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_428_, 0, v___y_426_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
v___x_429_ = 0;
v___x_430_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_430_, 0, v___x_428_);
lean_ctor_set_uint8(v___x_430_, sizeof(void*)*1, v___x_429_);
v___x_431_ = l_Repr_addAppParen(v___x_430_, v_prec_403_);
return v___x_431_;
}
v___jp_432_:
{
lean_object* v___x_434_; lean_object* v___x_435_; uint8_t v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_434_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__9));
lean_inc(v___y_433_);
v___x_435_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_435_, 0, v___y_433_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
v___x_436_ = 0;
v___x_437_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_437_, 0, v___x_435_);
lean_ctor_set_uint8(v___x_437_, sizeof(void*)*1, v___x_436_);
v___x_438_ = l_Repr_addAppParen(v___x_437_, v_prec_403_);
return v___x_438_;
}
v___jp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_441_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__11));
lean_inc(v___y_440_);
v___x_442_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_442_, 0, v___y_440_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___x_443_ = 0;
v___x_444_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_444_, 0, v___x_442_);
lean_ctor_set_uint8(v___x_444_, sizeof(void*)*1, v___x_443_);
v___x_445_ = l_Repr_addAppParen(v___x_444_, v_prec_403_);
return v___x_445_;
}
v___jp_446_:
{
lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_448_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__13));
lean_inc(v___y_447_);
v___x_449_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_449_, 0, v___y_447_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = 0;
v___x_451_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set_uint8(v___x_451_, sizeof(void*)*1, v___x_450_);
v___x_452_ = l_Repr_addAppParen(v___x_451_, v_prec_403_);
return v___x_452_;
}
v___jp_453_:
{
lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_455_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__15));
lean_inc(v___y_454_);
v___x_456_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_456_, 0, v___y_454_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = 0;
v___x_458_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*1, v___x_457_);
v___x_459_ = l_Repr_addAppParen(v___x_458_, v_prec_403_);
return v___x_459_;
}
v___jp_460_:
{
lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_462_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__17));
lean_inc(v___y_461_);
v___x_463_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_463_, 0, v___y_461_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = 0;
v___x_465_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set_uint8(v___x_465_, sizeof(void*)*1, v___x_464_);
v___x_466_ = l_Repr_addAppParen(v___x_465_, v_prec_403_);
return v___x_466_;
}
v___jp_467_:
{
lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_469_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__19));
lean_inc(v___y_468_);
v___x_470_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_470_, 0, v___y_468_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
v___x_471_ = 0;
v___x_472_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_472_, 0, v___x_470_);
lean_ctor_set_uint8(v___x_472_, sizeof(void*)*1, v___x_471_);
v___x_473_ = l_Repr_addAppParen(v___x_472_, v_prec_403_);
return v___x_473_;
}
v___jp_474_:
{
lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_476_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__21));
lean_inc(v___y_475_);
v___x_477_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_477_, 0, v___y_475_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
v___x_478_ = 0;
v___x_479_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_479_, 0, v___x_477_);
lean_ctor_set_uint8(v___x_479_, sizeof(void*)*1, v___x_478_);
v___x_480_ = l_Repr_addAppParen(v___x_479_, v_prec_403_);
return v___x_480_;
}
v___jp_481_:
{
lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_483_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__23));
lean_inc(v___y_482_);
v___x_484_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_484_, 0, v___y_482_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
v___x_485_ = 0;
v___x_486_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_486_, 0, v___x_484_);
lean_ctor_set_uint8(v___x_486_, sizeof(void*)*1, v___x_485_);
v___x_487_ = l_Repr_addAppParen(v___x_486_, v_prec_403_);
return v___x_487_;
}
v___jp_488_:
{
lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_490_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__25));
lean_inc(v___y_489_);
v___x_491_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_491_, 0, v___y_489_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
v___x_492_ = 0;
v___x_493_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_493_, 0, v___x_491_);
lean_ctor_set_uint8(v___x_493_, sizeof(void*)*1, v___x_492_);
v___x_494_ = l_Repr_addAppParen(v___x_493_, v_prec_403_);
return v___x_494_;
}
v___jp_495_:
{
lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_497_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__27));
lean_inc(v___y_496_);
v___x_498_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_498_, 0, v___y_496_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = 0;
v___x_500_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_500_, 0, v___x_498_);
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*1, v___x_499_);
v___x_501_ = l_Repr_addAppParen(v___x_500_, v_prec_403_);
return v___x_501_;
}
v___jp_502_:
{
lean_object* v___x_504_; lean_object* v___x_505_; uint8_t v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_504_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__29));
lean_inc(v___y_503_);
v___x_505_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_505_, 0, v___y_503_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
v___x_506_ = 0;
v___x_507_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_507_, 0, v___x_505_);
lean_ctor_set_uint8(v___x_507_, sizeof(void*)*1, v___x_506_);
v___x_508_ = l_Repr_addAppParen(v___x_507_, v_prec_403_);
return v___x_508_;
}
v___jp_509_:
{
lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_511_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__31));
lean_inc(v___y_510_);
v___x_512_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_512_, 0, v___y_510_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = 0;
v___x_514_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_514_, 0, v___x_512_);
lean_ctor_set_uint8(v___x_514_, sizeof(void*)*1, v___x_513_);
v___x_515_ = l_Repr_addAppParen(v___x_514_, v_prec_403_);
return v___x_515_;
}
v___jp_516_:
{
lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_518_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__33));
lean_inc(v___y_517_);
v___x_519_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_519_, 0, v___y_517_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = 0;
v___x_521_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_521_, 0, v___x_519_);
lean_ctor_set_uint8(v___x_521_, sizeof(void*)*1, v___x_520_);
v___x_522_ = l_Repr_addAppParen(v___x_521_, v_prec_403_);
return v___x_522_;
}
v___jp_523_:
{
lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_525_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__35));
lean_inc(v___y_524_);
v___x_526_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_526_, 0, v___y_524_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = 0;
v___x_528_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_528_, 0, v___x_526_);
lean_ctor_set_uint8(v___x_528_, sizeof(void*)*1, v___x_527_);
v___x_529_ = l_Repr_addAppParen(v___x_528_, v_prec_403_);
return v___x_529_;
}
v___jp_530_:
{
lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_532_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__37));
lean_inc(v___y_531_);
v___x_533_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_533_, 0, v___y_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = 0;
v___x_535_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set_uint8(v___x_535_, sizeof(void*)*1, v___x_534_);
v___x_536_ = l_Repr_addAppParen(v___x_535_, v_prec_403_);
return v___x_536_;
}
v___jp_537_:
{
lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_539_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__39));
lean_inc(v___y_538_);
v___x_540_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_540_, 0, v___y_538_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = 0;
v___x_542_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_542_, 0, v___x_540_);
lean_ctor_set_uint8(v___x_542_, sizeof(void*)*1, v___x_541_);
v___x_543_ = l_Repr_addAppParen(v___x_542_, v_prec_403_);
return v___x_543_;
}
v___jp_544_:
{
lean_object* v___x_546_; lean_object* v___x_547_; uint8_t v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_546_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__41));
lean_inc(v___y_545_);
v___x_547_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_547_, 0, v___y_545_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
v___x_548_ = 0;
v___x_549_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_549_, 0, v___x_547_);
lean_ctor_set_uint8(v___x_549_, sizeof(void*)*1, v___x_548_);
v___x_550_ = l_Repr_addAppParen(v___x_549_, v_prec_403_);
return v___x_550_;
}
v___jp_551_:
{
lean_object* v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_553_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__43));
lean_inc(v___y_552_);
v___x_554_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_554_, 0, v___y_552_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = 0;
v___x_556_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_556_, 0, v___x_554_);
lean_ctor_set_uint8(v___x_556_, sizeof(void*)*1, v___x_555_);
v___x_557_ = l_Repr_addAppParen(v___x_556_, v_prec_403_);
return v___x_557_;
}
}
}
LEAN_EXPORT void l_Std_Async_instReprSignal_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_402_ = stack[0].m_num;
lean_object* v_prec_403_ = stack[1].m_obj;
lean_object* v_res_646_;
v_res_646_ = l_Std_Async_instReprSignal_repr(v_x_402_, v_prec_403_);
stack->m_obj
 = v_res_646_;
}
LEAN_EXPORT lean_object* l_Std_Async_instReprSignal_repr___boxed(lean_object* v_x_647_, lean_object* v_prec_648_){
_start:
{
uint8_t v_x_1197__boxed_649_; lean_object* v_res_650_; 
v_x_1197__boxed_649_ = lean_unbox(v_x_647_);
v_res_650_ = l_Std_Async_instReprSignal_repr(v_x_1197__boxed_649_, v_prec_648_);
lean_dec(v_prec_648_);
return v_res_650_;
}
}
uint8_t l_Std_Async_Signal_ofNat(lean_object* v_n_653_){
_start:
{
lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_654_ = lean_unsigned_to_nat(10u);
v___x_655_ = lean_nat_dec_le(v_n_653_, v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_656_ = lean_unsigned_to_nat(15u);
v___x_657_ = lean_nat_dec_le(v_n_653_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_658_ = lean_unsigned_to_nat(18u);
v___x_659_ = lean_nat_dec_le(v_n_653_, v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_660_ = lean_unsigned_to_nat(19u);
v___x_661_ = lean_nat_dec_le(v_n_653_, v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = lean_unsigned_to_nat(20u);
v___x_663_ = lean_nat_dec_le(v_n_653_, v___x_662_);
if (v___x_663_ == 0)
{
uint8_t v___x_664_; 
v___x_664_ = 21;
return v___x_664_;
}
else
{
uint8_t v___x_665_; 
v___x_665_ = 20;
return v___x_665_;
}
}
else
{
uint8_t v___x_666_; 
v___x_666_ = 19;
return v___x_666_;
}
}
else
{
lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_667_ = lean_unsigned_to_nat(16u);
v___x_668_ = lean_nat_dec_le(v_n_653_, v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_669_ = lean_unsigned_to_nat(17u);
v___x_670_ = lean_nat_dec_le(v_n_653_, v___x_669_);
if (v___x_670_ == 0)
{
uint8_t v___x_671_; 
v___x_671_ = 18;
return v___x_671_;
}
else
{
uint8_t v___x_672_; 
v___x_672_ = 17;
return v___x_672_;
}
}
else
{
uint8_t v___x_673_; 
v___x_673_ = 16;
return v___x_673_;
}
}
}
else
{
lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_674_ = lean_unsigned_to_nat(12u);
v___x_675_ = lean_nat_dec_le(v_n_653_, v___x_674_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_676_ = lean_unsigned_to_nat(13u);
v___x_677_ = lean_nat_dec_le(v_n_653_, v___x_676_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_678_ = lean_unsigned_to_nat(14u);
v___x_679_ = lean_nat_dec_le(v_n_653_, v___x_678_);
if (v___x_679_ == 0)
{
uint8_t v___x_680_; 
v___x_680_ = 15;
return v___x_680_;
}
else
{
uint8_t v___x_681_; 
v___x_681_ = 14;
return v___x_681_;
}
}
else
{
uint8_t v___x_682_; 
v___x_682_ = 13;
return v___x_682_;
}
}
else
{
lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_683_ = lean_unsigned_to_nat(11u);
v___x_684_ = lean_nat_dec_le(v_n_653_, v___x_683_);
if (v___x_684_ == 0)
{
uint8_t v___x_685_; 
v___x_685_ = 12;
return v___x_685_;
}
else
{
uint8_t v___x_686_; 
v___x_686_ = 11;
return v___x_686_;
}
}
}
}
else
{
lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_687_ = lean_unsigned_to_nat(4u);
v___x_688_ = lean_nat_dec_le(v_n_653_, v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_689_ = lean_unsigned_to_nat(7u);
v___x_690_ = lean_nat_dec_le(v_n_653_, v___x_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_691_ = lean_unsigned_to_nat(8u);
v___x_692_ = lean_nat_dec_le(v_n_653_, v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_693_ = lean_unsigned_to_nat(9u);
v___x_694_ = lean_nat_dec_le(v_n_653_, v___x_693_);
if (v___x_694_ == 0)
{
uint8_t v___x_695_; 
v___x_695_ = 10;
return v___x_695_;
}
else
{
uint8_t v___x_696_; 
v___x_696_ = 9;
return v___x_696_;
}
}
else
{
uint8_t v___x_697_; 
v___x_697_ = 8;
return v___x_697_;
}
}
else
{
lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_698_ = lean_unsigned_to_nat(5u);
v___x_699_ = lean_nat_dec_le(v_n_653_, v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_700_ = lean_unsigned_to_nat(6u);
v___x_701_ = lean_nat_dec_le(v_n_653_, v___x_700_);
if (v___x_701_ == 0)
{
uint8_t v___x_702_; 
v___x_702_ = 7;
return v___x_702_;
}
else
{
uint8_t v___x_703_; 
v___x_703_ = 6;
return v___x_703_;
}
}
else
{
uint8_t v___x_704_; 
v___x_704_ = 5;
return v___x_704_;
}
}
}
else
{
lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_705_ = lean_unsigned_to_nat(1u);
v___x_706_ = lean_nat_dec_le(v_n_653_, v___x_705_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_707_ = lean_unsigned_to_nat(2u);
v___x_708_ = lean_nat_dec_le(v_n_653_, v___x_707_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; uint8_t v___x_710_; 
v___x_709_ = lean_unsigned_to_nat(3u);
v___x_710_ = lean_nat_dec_le(v_n_653_, v___x_709_);
if (v___x_710_ == 0)
{
uint8_t v___x_711_; 
v___x_711_ = 4;
return v___x_711_;
}
else
{
uint8_t v___x_712_; 
v___x_712_ = 3;
return v___x_712_;
}
}
else
{
uint8_t v___x_713_; 
v___x_713_ = 2;
return v___x_713_;
}
}
else
{
lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_714_ = lean_unsigned_to_nat(0u);
v___x_715_ = lean_nat_dec_le(v_n_653_, v___x_714_);
if (v___x_715_ == 0)
{
uint8_t v___x_716_; 
v___x_716_ = 1;
return v___x_716_;
}
else
{
uint8_t v___x_717_; 
v___x_717_ = 0;
return v___x_717_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Signal_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_653_ = stack[0].m_obj;
uint8_t v_res_718_;
v_res_718_ = l_Std_Async_Signal_ofNat(v_n_653_);
stack->m_num = v_res_718_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_ofNat___boxed(lean_object* v_n_719_){
_start:
{
uint8_t v_res_720_; lean_object* v_r_721_; 
v_res_720_ = l_Std_Async_Signal_ofNat(v_n_719_);
lean_dec(v_n_719_);
v_r_721_ = lean_box(v_res_720_);
return v_r_721_;
}
}
uint8_t l_Std_Async_instDecidableEqSignal(uint8_t v_x_722_, uint8_t v_y_723_){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_724_ = lean_box(v_x_722_);
v___x_725_ = lean_obj_tag_nat(v___x_724_);
lean_dec(v___x_724_);
v___x_726_ = lean_box(v_y_723_);
v___x_727_ = lean_obj_tag_nat(v___x_726_);
lean_dec(v___x_726_);
v___x_728_ = lean_nat_dec_eq(v___x_725_, v___x_727_);
return v___x_728_;
}
}
LEAN_EXPORT void l_Std_Async_instDecidableEqSignal_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_722_ = stack[0].m_num;
uint8_t v_y_723_ = stack[1].m_num;
uint8_t v_res_729_;
v_res_729_ = l_Std_Async_instDecidableEqSignal(v_x_722_, v_y_723_);
stack->m_num = v_res_729_;
}
LEAN_EXPORT lean_object* l_Std_Async_instDecidableEqSignal___boxed(lean_object* v_x_730_, lean_object* v_y_731_){
_start:
{
uint8_t v_x_23__boxed_732_; uint8_t v_y_24__boxed_733_; uint8_t v_res_734_; lean_object* v_r_735_; 
v_x_23__boxed_732_ = lean_unbox(v_x_730_);
v_y_24__boxed_733_ = lean_unbox(v_y_731_);
v_res_734_ = l_Std_Async_instDecidableEqSignal(v_x_23__boxed_732_, v_y_24__boxed_733_);
v_r_735_ = lean_box(v_res_734_);
return v_r_735_;
}
}
uint8_t l_Std_Async_instBEqSignal_beq(uint8_t v_x_736_, uint8_t v_y_737_){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_738_ = lean_box(v_x_736_);
v___x_739_ = lean_obj_tag_nat(v___x_738_);
lean_dec(v___x_738_);
v___x_740_ = lean_box(v_y_737_);
v___x_741_ = lean_obj_tag_nat(v___x_740_);
lean_dec(v___x_740_);
v___x_742_ = lean_nat_dec_eq(v___x_739_, v___x_741_);
return v___x_742_;
}
}
LEAN_EXPORT void l_Std_Async_instBEqSignal_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_736_ = stack[0].m_num;
uint8_t v_y_737_ = stack[1].m_num;
uint8_t v_res_743_;
v_res_743_ = l_Std_Async_instBEqSignal_beq(v_x_736_, v_y_737_);
stack->m_num = v_res_743_;
}
LEAN_EXPORT lean_object* l_Std_Async_instBEqSignal_beq___boxed(lean_object* v_x_744_, lean_object* v_y_745_){
_start:
{
uint8_t v_x_24__boxed_746_; uint8_t v_y_25__boxed_747_; uint8_t v_res_748_; lean_object* v_r_749_; 
v_x_24__boxed_746_ = lean_unbox(v_x_744_);
v_y_25__boxed_747_ = lean_unbox(v_y_745_);
v_res_748_ = l_Std_Async_instBEqSignal_beq(v_x_24__boxed_746_, v_y_25__boxed_747_);
v_r_749_ = lean_box(v_res_748_);
return v_r_749_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0(void){
_start:
{
lean_object* v___x_752_; uint32_t v___x_753_; 
v___x_752_ = lean_unsigned_to_nat(1u);
v___x_753_ = lean_int32_of_nat(v___x_752_);
return v___x_753_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1(void){
_start:
{
lean_object* v___x_754_; uint32_t v___x_755_; 
v___x_754_ = lean_unsigned_to_nat(2u);
v___x_755_ = lean_int32_of_nat(v___x_754_);
return v___x_755_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2(void){
_start:
{
lean_object* v___x_756_; uint32_t v___x_757_; 
v___x_756_ = lean_unsigned_to_nat(3u);
v___x_757_ = lean_int32_of_nat(v___x_756_);
return v___x_757_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3(void){
_start:
{
lean_object* v___x_758_; uint32_t v___x_759_; 
v___x_758_ = lean_unsigned_to_nat(5u);
v___x_759_ = lean_int32_of_nat(v___x_758_);
return v___x_759_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4(void){
_start:
{
lean_object* v___x_760_; uint32_t v___x_761_; 
v___x_760_ = lean_unsigned_to_nat(6u);
v___x_761_ = lean_int32_of_nat(v___x_760_);
return v___x_761_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5(void){
_start:
{
lean_object* v___x_762_; uint32_t v___x_763_; 
v___x_762_ = lean_unsigned_to_nat(10u);
v___x_763_ = lean_int32_of_nat(v___x_762_);
return v___x_763_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6(void){
_start:
{
lean_object* v___x_764_; uint32_t v___x_765_; 
v___x_764_ = lean_unsigned_to_nat(12u);
v___x_765_ = lean_int32_of_nat(v___x_764_);
return v___x_765_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7(void){
_start:
{
lean_object* v___x_766_; uint32_t v___x_767_; 
v___x_766_ = lean_unsigned_to_nat(14u);
v___x_767_ = lean_int32_of_nat(v___x_766_);
return v___x_767_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8(void){
_start:
{
lean_object* v___x_768_; uint32_t v___x_769_; 
v___x_768_ = lean_unsigned_to_nat(15u);
v___x_769_ = lean_int32_of_nat(v___x_768_);
return v___x_769_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9(void){
_start:
{
lean_object* v___x_770_; uint32_t v___x_771_; 
v___x_770_ = lean_unsigned_to_nat(17u);
v___x_771_ = lean_int32_of_nat(v___x_770_);
return v___x_771_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10(void){
_start:
{
lean_object* v___x_772_; uint32_t v___x_773_; 
v___x_772_ = lean_unsigned_to_nat(18u);
v___x_773_ = lean_int32_of_nat(v___x_772_);
return v___x_773_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11(void){
_start:
{
lean_object* v___x_774_; uint32_t v___x_775_; 
v___x_774_ = lean_unsigned_to_nat(20u);
v___x_775_ = lean_int32_of_nat(v___x_774_);
return v___x_775_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12(void){
_start:
{
lean_object* v___x_776_; uint32_t v___x_777_; 
v___x_776_ = lean_unsigned_to_nat(21u);
v___x_777_ = lean_int32_of_nat(v___x_776_);
return v___x_777_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13(void){
_start:
{
lean_object* v___x_778_; uint32_t v___x_779_; 
v___x_778_ = lean_unsigned_to_nat(22u);
v___x_779_ = lean_int32_of_nat(v___x_778_);
return v___x_779_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14(void){
_start:
{
lean_object* v___x_780_; uint32_t v___x_781_; 
v___x_780_ = lean_unsigned_to_nat(23u);
v___x_781_ = lean_int32_of_nat(v___x_780_);
return v___x_781_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15(void){
_start:
{
lean_object* v___x_782_; uint32_t v___x_783_; 
v___x_782_ = lean_unsigned_to_nat(24u);
v___x_783_ = lean_int32_of_nat(v___x_782_);
return v___x_783_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16(void){
_start:
{
lean_object* v___x_784_; uint32_t v___x_785_; 
v___x_784_ = lean_unsigned_to_nat(25u);
v___x_785_ = lean_int32_of_nat(v___x_784_);
return v___x_785_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17(void){
_start:
{
lean_object* v___x_786_; uint32_t v___x_787_; 
v___x_786_ = lean_unsigned_to_nat(26u);
v___x_787_ = lean_int32_of_nat(v___x_786_);
return v___x_787_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18(void){
_start:
{
lean_object* v___x_788_; uint32_t v___x_789_; 
v___x_788_ = lean_unsigned_to_nat(27u);
v___x_789_ = lean_int32_of_nat(v___x_788_);
return v___x_789_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19(void){
_start:
{
lean_object* v___x_790_; uint32_t v___x_791_; 
v___x_790_ = lean_unsigned_to_nat(28u);
v___x_791_ = lean_int32_of_nat(v___x_790_);
return v___x_791_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20(void){
_start:
{
lean_object* v___x_792_; uint32_t v___x_793_; 
v___x_792_ = lean_unsigned_to_nat(29u);
v___x_793_ = lean_int32_of_nat(v___x_792_);
return v___x_793_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21(void){
_start:
{
lean_object* v___x_794_; uint32_t v___x_795_; 
v___x_794_ = lean_unsigned_to_nat(31u);
v___x_795_ = lean_int32_of_nat(v___x_794_);
return v___x_795_;
}
}
uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32(uint8_t v_x_796_){
_start:
{
switch(v_x_796_)
{
case 0:
{
uint32_t v___x_797_; 
v___x_797_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0);
return v___x_797_;
}
case 1:
{
uint32_t v___x_798_; 
v___x_798_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1);
return v___x_798_;
}
case 2:
{
uint32_t v___x_799_; 
v___x_799_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2);
return v___x_799_;
}
case 3:
{
uint32_t v___x_800_; 
v___x_800_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3);
return v___x_800_;
}
case 4:
{
uint32_t v___x_801_; 
v___x_801_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4);
return v___x_801_;
}
case 5:
{
uint32_t v___x_802_; 
v___x_802_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5);
return v___x_802_;
}
case 6:
{
uint32_t v___x_803_; 
v___x_803_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6);
return v___x_803_;
}
case 7:
{
uint32_t v___x_804_; 
v___x_804_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7);
return v___x_804_;
}
case 8:
{
uint32_t v___x_805_; 
v___x_805_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8);
return v___x_805_;
}
case 9:
{
uint32_t v___x_806_; 
v___x_806_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9);
return v___x_806_;
}
case 10:
{
uint32_t v___x_807_; 
v___x_807_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10);
return v___x_807_;
}
case 11:
{
uint32_t v___x_808_; 
v___x_808_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11);
return v___x_808_;
}
case 12:
{
uint32_t v___x_809_; 
v___x_809_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12);
return v___x_809_;
}
case 13:
{
uint32_t v___x_810_; 
v___x_810_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13);
return v___x_810_;
}
case 14:
{
uint32_t v___x_811_; 
v___x_811_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14);
return v___x_811_;
}
case 15:
{
uint32_t v___x_812_; 
v___x_812_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15);
return v___x_812_;
}
case 16:
{
uint32_t v___x_813_; 
v___x_813_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16);
return v___x_813_;
}
case 17:
{
uint32_t v___x_814_; 
v___x_814_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17);
return v___x_814_;
}
case 18:
{
uint32_t v___x_815_; 
v___x_815_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18);
return v___x_815_;
}
case 19:
{
uint32_t v___x_816_; 
v___x_816_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19);
return v___x_816_;
}
case 20:
{
uint32_t v___x_817_; 
v___x_817_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20);
return v___x_817_;
}
default: 
{
uint32_t v___x_818_; 
v___x_818_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21);
return v___x_818_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_796_ = stack[0].m_num;
uint32_t v_res_819_;
v_res_819_ = l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32(v_x_796_);
stack->m_num = v_res_819_;
}
LEAN_EXPORT lean_object* l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___boxed(lean_object* v_x_820_){
_start:
{
uint8_t v_x_356__boxed_821_; uint32_t v_res_822_; lean_object* v_r_823_; 
v_x_356__boxed_821_ = lean_unbox(v_x_820_);
v_res_822_ = l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32(v_x_356__boxed_821_);
v_r_823_ = lean_box_uint32(v_res_822_);
return v_r_823_;
}
}
lean_object* l_Std_Async_Signal_Waiter_mk(uint8_t v_signum_824_, uint8_t v_repeating_825_){
_start:
{
uint32_t v___x_827_; lean_object* v___x_828_; 
v___x_827_ = l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32(v_signum_824_);
v___x_828_ = lean_uv_signal_mk(v___x_827_, v_repeating_825_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_828_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
v_a_837_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_828_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_828_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Signal_Waiter_mk_0interp(lean_interpreter_value* stack)
{
uint8_t v_signum_824_ = stack[0].m_num;
uint8_t v_repeating_825_ = stack[1].m_num;
lean_object* v_res_845_;
v_res_845_ = l_Std_Async_Signal_Waiter_mk(v_signum_824_, v_repeating_825_);
stack->m_obj
 = v_res_845_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_mk___boxed(lean_object* v_signum_846_, lean_object* v_repeating_847_, lean_object* v_a_848_){
_start:
{
uint8_t v_signum_boxed_849_; uint8_t v_repeating_boxed_850_; lean_object* v_res_851_; 
v_signum_boxed_849_ = lean_unbox(v_signum_846_);
v_repeating_boxed_850_ = lean_unbox(v_repeating_847_);
v_res_851_ = l_Std_Async_Signal_Waiter_mk(v_signum_boxed_849_, v_repeating_boxed_850_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_wait___lam__0(lean_object* v___x_852_, lean_object* v_x_853_){
_start:
{
if (lean_obj_tag(v_x_853_) == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_mk_io_user_error(v___x_852_);
v___x_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
return v___x_855_;
}
else
{
lean_object* v_val_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
lean_dec_ref(v___x_852_);
v_val_856_ = lean_ctor_get(v_x_853_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v_x_853_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v_x_853_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_val_856_);
lean_dec(v_x_853_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_val_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
}
lean_object* l_Std_Async_Signal_Waiter_wait(lean_object* v_s_867_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = lean_uv_signal_next(v_s_867_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_882_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_882_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_882_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_882_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___f_874_; lean_object* v___x_875_; lean_object* v___x_876_; uint8_t v___x_877_; lean_object* v___x_878_; lean_object* v___x_880_; 
v___f_874_ = ((lean_object*)(l_Std_Async_Signal_Waiter_wait___closed__1));
v___x_875_ = lean_io_promise_result_opt(v_a_870_);
lean_dec(v_a_870_);
v___x_876_ = lean_unsigned_to_nat(0u);
v___x_877_ = 1;
v___x_878_ = lean_task_map(v___f_874_, v___x_875_, v___x_876_, v___x_877_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_878_);
v___x_880_ = v___x_872_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
v_a_883_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_869_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_869_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Signal_Waiter_wait_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_867_ = stack[0].m_obj;
lean_object* v_res_891_;
v_res_891_ = l_Std_Async_Signal_Waiter_wait(v_s_867_);
stack->m_obj
 = v_res_891_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_wait___boxed(lean_object* v_s_892_, lean_object* v_a_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Std_Async_Signal_Waiter_wait(v_s_892_);
lean_dec(v_s_892_);
return v_res_894_;
}
}
lean_object* l_Std_Async_Signal_Waiter_stop(lean_object* v_s_895_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = lean_uv_signal_stop(v_s_895_);
return v___x_897_;
}
}
LEAN_EXPORT void l_Std_Async_Signal_Waiter_stop_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_895_ = stack[0].m_obj;
lean_object* v_res_898_;
v_res_898_ = l_Std_Async_Signal_Waiter_stop(v_s_895_);
stack->m_obj
 = v_res_898_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_stop___boxed(lean_object* v_s_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Std_Async_Signal_Waiter_stop(v_s_899_);
lean_dec(v_s_899_);
return v_res_901_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0(lean_object* v_w_904_, lean_object* v_lose_905_){
_start:
{
lean_object* v_finished_907_; lean_object* v_promise_908_; lean_object* v___x_909_; uint8_t v___y_911_; uint8_t v___x_919_; 
v_finished_907_ = lean_ctor_get(v_w_904_, 0);
v_promise_908_ = lean_ctor_get(v_w_904_, 1);
v___x_909_ = lean_st_ref_take(v_finished_907_);
v___x_919_ = lean_unbox(v___x_909_);
lean_dec(v___x_909_);
if (v___x_919_ == 0)
{
uint8_t v___x_920_; 
v___x_920_ = 1;
v___y_911_ = v___x_920_;
goto v___jp_910_;
}
else
{
uint8_t v___x_921_; 
v___x_921_ = 0;
v___y_911_ = v___x_921_;
goto v___jp_910_;
}
v___jp_910_:
{
uint8_t v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_912_ = 1;
v___x_913_ = lean_box(v___x_912_);
v___x_914_ = lean_st_ref_put(v_finished_907_, v___x_913_);
if (v___y_911_ == 0)
{
lean_object* v___x_915_; 
v___x_915_ = lean_apply_1(v_lose_905_, lean_box(0));
return v___x_915_;
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
lean_dec_ref(v_lose_905_);
v___x_916_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___closed__0));
v___x_917_ = lean_io_promise_resolve(v___x_916_, v_promise_908_);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_904_ = stack[0].m_obj;
lean_object* v_lose_905_ = stack[1].m_obj;
lean_object* v_res_922_;
v_res_922_ = l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0(v_w_904_, v_lose_905_);
stack->m_obj
 = v_res_922_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___boxed(lean_object* v_w_923_, lean_object* v_lose_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0(v_w_923_, v_lose_924_);
lean_dec_ref(v_w_923_);
return v_res_926_;
}
}
lean_object* l_Std_Async_Signal_Waiter_selector___lam__0(lean_object* v_x_937_){
_start:
{
if (lean_obj_tag(v_x_937_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_947_; 
v_a_939_ = lean_ctor_get(v_x_937_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v_x_937_);
if (v_isSharedCheck_947_ == 0)
{
v___x_941_ = v_x_937_;
v_isShared_942_ = v_isSharedCheck_947_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v_x_937_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_947_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_946_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_945_; 
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
return v___x_945_;
}
}
}
else
{
lean_object* v_a_948_; uint8_t v___x_949_; 
v_a_948_ = lean_ctor_get(v_x_937_, 0);
lean_inc(v_a_948_);
lean_dec_ref_known(v_x_937_, 1);
v___x_949_ = lean_unbox(v_a_948_);
lean_dec(v_a_948_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; 
v___x_950_ = ((lean_object*)(l_Std_Async_Signal_Waiter_selector___lam__0___closed__1));
return v___x_950_;
}
else
{
lean_object* v___x_951_; 
v___x_951_ = ((lean_object*)(l_Std_Async_Signal_Waiter_selector___lam__0___closed__4));
return v___x_951_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_Signal_Waiter_selector___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_937_ = stack[0].m_obj;
lean_object* v_res_952_;
v_res_952_ = l_Std_Async_Signal_Waiter_selector___lam__0(v_x_937_);
stack->m_obj
 = v_res_952_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__0___boxed(lean_object* v_x_953_, lean_object* v___y_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Std_Async_Signal_Waiter_selector___lam__0(v_x_953_);
return v_res_955_;
}
}
lean_object* l_Std_Async_Signal_Waiter_selector___lam__1(lean_object* v___x_956_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_956_);
return v___x_958_;
}
}
LEAN_EXPORT void l_Std_Async_Signal_Waiter_selector___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_956_ = stack[0].m_obj;
lean_object* v_res_959_;
v_res_959_ = l_Std_Async_Signal_Waiter_selector___lam__1(v___x_956_);
stack->m_obj
 = v_res_959_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__1___boxed(lean_object* v___x_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Std_Async_Signal_Waiter_selector___lam__1(v___x_960_);
return v_res_962_;
}
}
lean_object* l_Std_Async_Signal_Waiter_selector___lam__2(lean_object* v_waiter_965_, lean_object* v_a_966_){
_start:
{
lean_object* v_a_969_; 
if (lean_obj_tag(v_a_966_) == 0)
{
lean_object* v_a_971_; 
v_a_971_ = lean_ctor_get(v_a_966_, 0);
lean_inc(v_a_971_);
lean_dec_ref_known(v_a_966_, 1);
v_a_969_ = v_a_971_;
goto v___jp_968_;
}
else
{
lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_982_; 
v_isSharedCheck_982_ = !lean_is_exclusive(v_a_966_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; 
v_unused_983_ = lean_ctor_get(v_a_966_, 0);
lean_dec(v_unused_983_);
v___x_973_ = v_a_966_;
v_isShared_974_ = v_isSharedCheck_982_;
goto v_resetjp_972_;
}
else
{
lean_dec(v_a_966_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_982_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___f_975_; lean_object* v___x_976_; 
v___f_975_ = ((lean_object*)(l_Std_Async_Signal_Waiter_selector___lam__2___closed__0));
v___x_976_ = l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0(v_waiter_965_, v___f_975_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v___x_979_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_a_977_);
lean_dec_ref_known(v___x_976_, 1);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v_a_977_);
v___x_979_ = v___x_973_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
else
{
lean_object* v_a_981_; 
lean_del_object(v___x_973_);
v_a_981_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_a_981_);
lean_dec_ref_known(v___x_976_, 1);
v_a_969_ = v_a_981_;
goto v___jp_968_;
}
}
}
v___jp_968_:
{
lean_object* v___x_970_; 
v___x_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_970_, 0, v_a_969_);
return v___x_970_;
}
}
}
LEAN_EXPORT void l_Std_Async_Signal_Waiter_selector___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_waiter_965_ = stack[0].m_obj;
lean_object* v_a_966_ = stack[1].m_obj;
lean_object* v_res_984_;
v_res_984_ = l_Std_Async_Signal_Waiter_selector___lam__2(v_waiter_965_, v_a_966_);
stack->m_obj
 = v_res_984_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__2___boxed(lean_object* v_waiter_985_, lean_object* v_a_986_, lean_object* v___y_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Std_Async_Signal_Waiter_selector___lam__2(v_waiter_985_, v_a_986_);
lean_dec_ref(v_waiter_985_);
return v_res_988_;
}
}
lean_object* l_Std_Async_Signal_Waiter_selector___lam__3(lean_object* v___f_991_, lean_object* v_x_992_){
_start:
{
if (lean_obj_tag(v_x_992_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1002_; 
lean_dec_ref(v___f_991_);
v_a_994_ = lean_ctor_get(v_x_992_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_x_992_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_996_ = v_x_992_;
v_isShared_997_ = v_isSharedCheck_1002_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v_x_992_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1002_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_994_);
v___x_999_ = v_reuseFailAlloc_1001_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1000_; 
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
return v___x_1000_;
}
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_a_1003_ = lean_ctor_get(v_x_992_, 0);
lean_inc(v_a_1003_);
lean_dec_ref_known(v_x_992_, 1);
v___x_1004_ = lean_unsigned_to_nat(0u);
v___x_1005_ = 0;
v___x_1006_ = lean_io_map_task(v___f_991_, v_a_1003_, v___x_1004_, v___x_1005_);
lean_dec_ref(v___x_1006_);
v___x_1007_ = ((lean_object*)(l_Std_Async_Signal_Waiter_selector___lam__3___closed__0));
return v___x_1007_;
}
}
}
LEAN_EXPORT void l_Std_Async_Signal_Waiter_selector___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_991_ = stack[0].m_obj;
lean_object* v_x_992_ = stack[1].m_obj;
lean_object* v_res_1008_;
v_res_1008_ = l_Std_Async_Signal_Waiter_selector___lam__3(v___f_991_, v_x_992_);
stack->m_obj
 = v_res_1008_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__3___boxed(lean_object* v___f_1009_, lean_object* v_x_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Std_Async_Signal_Waiter_selector___lam__3(v___f_1009_, v_x_1010_);
return v_res_1012_;
}
}
lean_object* l_Std_Async_Signal_Waiter_selector___lam__5(lean_object* v_s_1013_, lean_object* v_waiter_1014_){
_start:
{
lean_object* v___f_1016_; lean_object* v___f_1017_; lean_object* v___x_1018_; uint8_t v___x_1019_; lean_object* v_val_1021_; lean_object* v___x_1024_; 
v___f_1016_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1016_, 0, v_waiter_1014_);
v___f_1017_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1017_, 0, v___f_1016_);
v___x_1018_ = lean_unsigned_to_nat(0u);
v___x_1019_ = 0;
v___x_1024_ = lean_uv_signal_next(v_s_1013_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1036_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1036_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1036_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___f_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___f_1029_ = ((lean_object*)(l_Std_Async_Signal_Waiter_wait___closed__1));
v___x_1030_ = lean_io_promise_result_opt(v_a_1025_);
lean_dec(v_a_1025_);
v___x_1031_ = 1;
v___x_1032_ = lean_task_map(v___f_1029_, v___x_1030_, v___x_1018_, v___x_1031_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set_tag(v___x_1027_, 1);
lean_ctor_set(v___x_1027_, 0, v___x_1032_);
v___x_1034_ = v___x_1027_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
v_val_1021_ = v___x_1034_;
goto v___jp_1020_;
}
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
v_a_1037_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1024_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1024_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set_tag(v___x_1039_, 0);
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
v_val_1021_ = v___x_1042_;
goto v___jp_1020_;
}
}
}
v___jp_1020_:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1022_, 0, v_val_1021_);
v___x_1023_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1018_, v___x_1019_, v___x_1022_, v___f_1017_);
return v___x_1023_;
}
}
}
LEAN_EXPORT void l_Std_Async_Signal_Waiter_selector___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1013_ = stack[0].m_obj;
lean_object* v_waiter_1014_ = stack[1].m_obj;
lean_object* v_res_1045_;
v_res_1045_ = l_Std_Async_Signal_Waiter_selector___lam__5(v_s_1013_, v_waiter_1014_);
stack->m_obj
 = v_res_1045_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__5___boxed(lean_object* v_s_1046_, lean_object* v_waiter_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Std_Async_Signal_Waiter_selector___lam__5(v_s_1046_, v_waiter_1047_);
lean_dec(v_s_1046_);
return v_res_1049_;
}
}
lean_object* l_Std_Async_Signal_Waiter_selector___lam__4(lean_object* v_s_1050_){
_start:
{
lean_object* v_val_1053_; lean_object* v___x_1055_; 
v___x_1055_ = lean_uv_signal_cancel(v_s_1050_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1055_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1055_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
lean_ctor_set_tag(v___x_1058_, 1);
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
v_val_1053_ = v___x_1061_;
goto v___jp_1052_;
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
v_a_1064_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1055_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1055_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 0);
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
v_val_1053_ = v___x_1069_;
goto v___jp_1052_;
}
}
}
v___jp_1052_:
{
lean_object* v___x_1054_; 
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v_val_1053_);
return v___x_1054_;
}
}
}
LEAN_EXPORT void l_Std_Async_Signal_Waiter_selector___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1050_ = stack[0].m_obj;
lean_object* v_res_1072_;
v_res_1072_ = l_Std_Async_Signal_Waiter_selector___lam__4(v_s_1050_);
stack->m_obj
 = v_res_1072_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__4___boxed(lean_object* v_s_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Std_Async_Signal_Waiter_selector___lam__4(v_s_1073_);
lean_dec(v_s_1073_);
return v_res_1075_;
}
}
lean_object* l_Std_Async_Signal_Waiter_selector___lam__6(lean_object* v_a_1076_, lean_object* v___f_1077_, lean_object* v_x_1078_){
_start:
{
if (lean_obj_tag(v_x_1078_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1088_; 
lean_dec_ref(v___f_1077_);
v_a_1080_ = lean_ctor_get(v_x_1078_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_x_1078_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1082_ = v_x_1078_;
v_isShared_1083_ = v_isSharedCheck_1088_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v_x_1078_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1088_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
return v___x_1086_;
}
}
}
else
{
lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1101_; 
v_isSharedCheck_1101_ = !lean_is_exclusive(v_x_1078_);
if (v_isSharedCheck_1101_ == 0)
{
lean_object* v_unused_1102_; 
v_unused_1102_ = lean_ctor_get(v_x_1078_, 0);
lean_dec(v_unused_1102_);
v___x_1090_ = v_x_1078_;
v_isShared_1091_ = v_isSharedCheck_1101_;
goto v_resetjp_1089_;
}
else
{
lean_dec(v_x_1078_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1101_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; uint8_t v___x_1093_; uint8_t v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1092_ = lean_unsigned_to_nat(0u);
v___x_1093_ = 0;
v___x_1094_ = l_IO_Promise_isResolved___redArg(v_a_1076_);
v___x_1095_ = lean_box(v___x_1094_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1095_);
v___x_1097_ = v___x_1090_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
v___x_1099_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1092_, v___x_1093_, v___x_1098_, v___f_1077_);
return v___x_1099_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Signal_Waiter_selector___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1076_ = stack[0].m_obj;
lean_object* v___f_1077_ = stack[1].m_obj;
lean_object* v_x_1078_ = stack[2].m_obj;
lean_object* v_res_1103_;
v_res_1103_ = l_Std_Async_Signal_Waiter_selector___lam__6(v_a_1076_, v___f_1077_, v_x_1078_);
stack->m_obj
 = v_res_1103_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__6___boxed(lean_object* v_a_1104_, lean_object* v___f_1105_, lean_object* v_x_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Std_Async_Signal_Waiter_selector___lam__6(v_a_1104_, v___f_1105_, v_x_1106_);
lean_dec(v_a_1104_);
return v_res_1108_;
}
}
lean_object* l_Std_Async_Signal_Waiter_selector___lam__7(lean_object* v___f_1109_, lean_object* v_s_1110_, lean_object* v_x_1111_){
_start:
{
if (lean_obj_tag(v_x_1111_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1121_; 
lean_dec_ref(v___f_1109_);
v_a_1113_ = lean_ctor_get(v_x_1111_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_x_1111_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1115_ = v_x_1111_;
v_isShared_1116_ = v_isSharedCheck_1121_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v_x_1111_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1121_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
return v___x_1119_;
}
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1142_; 
v_a_1122_ = lean_ctor_get(v_x_1111_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_x_1111_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1124_ = v_x_1111_;
v_isShared_1125_ = v_isSharedCheck_1142_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v_x_1111_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1142_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___f_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; lean_object* v_val_1130_; lean_object* v___x_1133_; 
v___f_1126_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__6___boxed), 4, 2);
lean_closure_set(v___f_1126_, 0, v_a_1122_);
lean_closure_set(v___f_1126_, 1, v___f_1109_);
v___x_1127_ = lean_unsigned_to_nat(0u);
v___x_1128_ = 0;
v___x_1133_ = lean_uv_signal_cancel(v_s_1110_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1136_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1134_);
lean_dec_ref_known(v___x_1133_, 1);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v_a_1134_);
v___x_1136_ = v___x_1124_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
v_val_1130_ = v___x_1136_;
goto v___jp_1129_;
}
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; 
v_a_1138_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1138_);
lean_dec_ref_known(v___x_1133_, 1);
if (v_isShared_1125_ == 0)
{
lean_ctor_set_tag(v___x_1124_, 0);
lean_ctor_set(v___x_1124_, 0, v_a_1138_);
v___x_1140_ = v___x_1124_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
v_val_1130_ = v___x_1140_;
goto v___jp_1129_;
}
}
v___jp_1129_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1131_, 0, v_val_1130_);
v___x_1132_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1127_, v___x_1128_, v___x_1131_, v___f_1126_);
return v___x_1132_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Signal_Waiter_selector___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1109_ = stack[0].m_obj;
lean_object* v_s_1110_ = stack[1].m_obj;
lean_object* v_x_1111_ = stack[2].m_obj;
lean_object* v_res_1143_;
v_res_1143_ = l_Std_Async_Signal_Waiter_selector___lam__7(v___f_1109_, v_s_1110_, v_x_1111_);
stack->m_obj
 = v_res_1143_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__7___boxed(lean_object* v___f_1144_, lean_object* v_s_1145_, lean_object* v_x_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Std_Async_Signal_Waiter_selector___lam__7(v___f_1144_, v_s_1145_, v_x_1146_);
lean_dec(v_s_1145_);
return v_res_1148_;
}
}
lean_object* l_Std_Async_Signal_Waiter_selector___lam__8(lean_object* v___f_1149_, lean_object* v_s_1150_){
_start:
{
lean_object* v___x_1152_; uint8_t v___x_1153_; lean_object* v_val_1155_; lean_object* v___x_1158_; 
v___x_1152_ = lean_unsigned_to_nat(0u);
v___x_1153_ = 0;
v___x_1158_ = lean_uv_signal_next(v_s_1150_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1158_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1158_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
lean_ctor_set_tag(v___x_1161_, 1);
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
v_val_1155_ = v___x_1164_;
goto v___jp_1154_;
}
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
v_a_1167_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1158_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1158_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set_tag(v___x_1169_, 0);
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
v_val_1155_ = v___x_1172_;
goto v___jp_1154_;
}
}
}
v___jp_1154_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1156_, 0, v_val_1155_);
v___x_1157_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1152_, v___x_1153_, v___x_1156_, v___f_1149_);
return v___x_1157_;
}
}
}
LEAN_EXPORT void l_Std_Async_Signal_Waiter_selector___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1149_ = stack[0].m_obj;
lean_object* v_s_1150_ = stack[1].m_obj;
lean_object* v_res_1175_;
v_res_1175_ = l_Std_Async_Signal_Waiter_selector___lam__8(v___f_1149_, v_s_1150_);
stack->m_obj
 = v_res_1175_;
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__8___boxed(lean_object* v___f_1176_, lean_object* v_s_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Std_Async_Signal_Waiter_selector___lam__8(v___f_1176_, v_s_1177_);
lean_dec(v_s_1177_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector(lean_object* v_s_1181_){
_start:
{
lean_object* v___f_1182_; lean_object* v___f_1183_; lean_object* v___f_1184_; lean_object* v___f_1185_; lean_object* v___f_1186_; lean_object* v___x_1187_; 
v___f_1182_ = ((lean_object*)(l_Std_Async_Signal_Waiter_selector___closed__0));
lean_inc_n(v_s_1181_, 3);
v___f_1183_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__5___boxed), 3, 1);
lean_closure_set(v___f_1183_, 0, v_s_1181_);
v___f_1184_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__4___boxed), 2, 1);
lean_closure_set(v___f_1184_, 0, v_s_1181_);
v___f_1185_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__7___boxed), 4, 2);
lean_closure_set(v___f_1185_, 0, v___f_1182_);
lean_closure_set(v___f_1185_, 1, v_s_1181_);
v___f_1186_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__8___boxed), 3, 2);
lean_closure_set(v___f_1186_, 0, v___f_1185_);
lean_closure_set(v___f_1186_, 1, v_s_1181_);
v___x_1187_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1187_, 0, v___f_1186_);
lean_ctor_set(v___x_1187_, 1, v___f_1183_);
lean_ctor_set(v___x_1187_, 2, v___f_1184_);
return v___x_1187_;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_UV_Signal(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_Select(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Async_Signal(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_UV_Signal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_Select(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Async_Signal(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time(uint8_t builtin);
lean_object* initialize_Std_Internal_UV_Signal(uint8_t builtin);
lean_object* initialize_Std_Async_Select(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Async_Signal(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_UV_Signal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Async_Select(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_Signal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Async_Signal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Async_Signal(builtin);
}
#ifdef __cplusplus
}
#endif
