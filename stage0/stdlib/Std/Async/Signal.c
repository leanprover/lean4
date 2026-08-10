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
lean_object* lean_uv_signal_cancel(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint32_t lean_int32_of_nat(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_io_get_task_state(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_uv_signal_next(lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_uv_signal_stop(lean_object*);
lean_object* lean_uv_signal_mk(uint32_t, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_Signal_Waiter_selector___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__1___closed__0 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__1___closed__0_value;
static const lean_ctor_object l_Std_Async_Signal_Waiter_selector___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__1___closed__0_value)}};
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__1___closed__1 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_Signal_Waiter_selector___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__2___closed__0 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__2___closed__0_value;
static const lean_ctor_object l_Std_Async_Signal_Waiter_selector___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__2___closed__0_value)}};
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__2___closed__1 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__2___closed__1_value;
static const lean_ctor_object l_Std_Async_Signal_Waiter_selector___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__2___closed__1_value)}};
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__2___closed__2 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__2___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__5(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__8(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__8___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Signal_Waiter_selector___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Signal_Waiter_selector___lam__8___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__9___closed__0 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__9___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__9___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_Signal_Waiter_selector___lam__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___closed__0_value)}};
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__10___closed__0 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__10___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Signal_Waiter_selector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Signal_Waiter_selector___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_Signal_Waiter_selector___closed__0 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___closed__0_value;
static const lean_closure_object l_Std_Async_Signal_Waiter_selector___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Signal_Waiter_selector___lam__3, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_Signal_Waiter_selector___closed__1 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorIdx(uint8_t v_x_1_){
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
default: 
{
lean_object* v___x_23_; 
v___x_23_ = lean_unsigned_to_nat(21u);
return v___x_23_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorIdx___boxed(lean_object* v_x_24_){
_start:
{
uint8_t v_x_boxed_25_; lean_object* v_res_26_; 
v_x_boxed_25_ = lean_unbox(v_x_24_);
v_res_26_ = l_Std_Async_Signal_ctorIdx(v_x_boxed_25_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorElim___redArg(lean_object* v_k_27_){
_start:
{
lean_inc(v_k_27_);
return v_k_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorElim___redArg___boxed(lean_object* v_k_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Std_Async_Signal_ctorElim___redArg(v_k_28_);
lean_dec(v_k_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorElim(lean_object* v_motive_30_, lean_object* v_ctorIdx_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_k_34_){
_start:
{
lean_inc(v_k_34_);
return v_k_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorElim___boxed(lean_object* v_motive_35_, lean_object* v_ctorIdx_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_k_39_){
_start:
{
uint8_t v_t_boxed_40_; lean_object* v_res_41_; 
v_t_boxed_40_ = lean_unbox(v_t_37_);
v_res_41_ = l_Std_Async_Signal_ctorElim(v_motive_35_, v_ctorIdx_36_, v_t_boxed_40_, v_h_38_, v_k_39_);
lean_dec(v_k_39_);
lean_dec(v_ctorIdx_36_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sighup_elim___redArg(lean_object* v_sighup_42_){
_start:
{
lean_inc(v_sighup_42_);
return v_sighup_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sighup_elim___redArg___boxed(lean_object* v_sighup_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Std_Async_Signal_sighup_elim___redArg(v_sighup_43_);
lean_dec(v_sighup_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sighup_elim(lean_object* v_motive_45_, uint8_t v_t_46_, lean_object* v_h_47_, lean_object* v_sighup_48_){
_start:
{
lean_inc(v_sighup_48_);
return v_sighup_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sighup_elim___boxed(lean_object* v_motive_49_, lean_object* v_t_50_, lean_object* v_h_51_, lean_object* v_sighup_52_){
_start:
{
uint8_t v_t_boxed_53_; lean_object* v_res_54_; 
v_t_boxed_53_ = lean_unbox(v_t_50_);
v_res_54_ = l_Std_Async_Signal_sighup_elim(v_motive_49_, v_t_boxed_53_, v_h_51_, v_sighup_52_);
lean_dec(v_sighup_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigint_elim___redArg(lean_object* v_sigint_55_){
_start:
{
lean_inc(v_sigint_55_);
return v_sigint_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigint_elim___redArg___boxed(lean_object* v_sigint_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Std_Async_Signal_sigint_elim___redArg(v_sigint_56_);
lean_dec(v_sigint_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigint_elim(lean_object* v_motive_58_, uint8_t v_t_59_, lean_object* v_h_60_, lean_object* v_sigint_61_){
_start:
{
lean_inc(v_sigint_61_);
return v_sigint_61_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigint_elim___boxed(lean_object* v_motive_62_, lean_object* v_t_63_, lean_object* v_h_64_, lean_object* v_sigint_65_){
_start:
{
uint8_t v_t_boxed_66_; lean_object* v_res_67_; 
v_t_boxed_66_ = lean_unbox(v_t_63_);
v_res_67_ = l_Std_Async_Signal_sigint_elim(v_motive_62_, v_t_boxed_66_, v_h_64_, v_sigint_65_);
lean_dec(v_sigint_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigquit_elim___redArg(lean_object* v_sigquit_68_){
_start:
{
lean_inc(v_sigquit_68_);
return v_sigquit_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigquit_elim___redArg___boxed(lean_object* v_sigquit_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Std_Async_Signal_sigquit_elim___redArg(v_sigquit_69_);
lean_dec(v_sigquit_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigquit_elim(lean_object* v_motive_71_, uint8_t v_t_72_, lean_object* v_h_73_, lean_object* v_sigquit_74_){
_start:
{
lean_inc(v_sigquit_74_);
return v_sigquit_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigquit_elim___boxed(lean_object* v_motive_75_, lean_object* v_t_76_, lean_object* v_h_77_, lean_object* v_sigquit_78_){
_start:
{
uint8_t v_t_boxed_79_; lean_object* v_res_80_; 
v_t_boxed_79_ = lean_unbox(v_t_76_);
v_res_80_ = l_Std_Async_Signal_sigquit_elim(v_motive_75_, v_t_boxed_79_, v_h_77_, v_sigquit_78_);
lean_dec(v_sigquit_78_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtrap_elim___redArg(lean_object* v_sigtrap_81_){
_start:
{
lean_inc(v_sigtrap_81_);
return v_sigtrap_81_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtrap_elim___redArg___boxed(lean_object* v_sigtrap_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Std_Async_Signal_sigtrap_elim___redArg(v_sigtrap_82_);
lean_dec(v_sigtrap_82_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtrap_elim(lean_object* v_motive_84_, uint8_t v_t_85_, lean_object* v_h_86_, lean_object* v_sigtrap_87_){
_start:
{
lean_inc(v_sigtrap_87_);
return v_sigtrap_87_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtrap_elim___boxed(lean_object* v_motive_88_, lean_object* v_t_89_, lean_object* v_h_90_, lean_object* v_sigtrap_91_){
_start:
{
uint8_t v_t_boxed_92_; lean_object* v_res_93_; 
v_t_boxed_92_ = lean_unbox(v_t_89_);
v_res_93_ = l_Std_Async_Signal_sigtrap_elim(v_motive_88_, v_t_boxed_92_, v_h_90_, v_sigtrap_91_);
lean_dec(v_sigtrap_91_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigabrt_elim___redArg(lean_object* v_sigabrt_94_){
_start:
{
lean_inc(v_sigabrt_94_);
return v_sigabrt_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigabrt_elim___redArg___boxed(lean_object* v_sigabrt_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_Async_Signal_sigabrt_elim___redArg(v_sigabrt_95_);
lean_dec(v_sigabrt_95_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigabrt_elim(lean_object* v_motive_97_, uint8_t v_t_98_, lean_object* v_h_99_, lean_object* v_sigabrt_100_){
_start:
{
lean_inc(v_sigabrt_100_);
return v_sigabrt_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigabrt_elim___boxed(lean_object* v_motive_101_, lean_object* v_t_102_, lean_object* v_h_103_, lean_object* v_sigabrt_104_){
_start:
{
uint8_t v_t_boxed_105_; lean_object* v_res_106_; 
v_t_boxed_105_ = lean_unbox(v_t_102_);
v_res_106_ = l_Std_Async_Signal_sigabrt_elim(v_motive_101_, v_t_boxed_105_, v_h_103_, v_sigabrt_104_);
lean_dec(v_sigabrt_104_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr1_elim___redArg(lean_object* v_sigusr1_107_){
_start:
{
lean_inc(v_sigusr1_107_);
return v_sigusr1_107_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr1_elim___redArg___boxed(lean_object* v_sigusr1_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Std_Async_Signal_sigusr1_elim___redArg(v_sigusr1_108_);
lean_dec(v_sigusr1_108_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr1_elim(lean_object* v_motive_110_, uint8_t v_t_111_, lean_object* v_h_112_, lean_object* v_sigusr1_113_){
_start:
{
lean_inc(v_sigusr1_113_);
return v_sigusr1_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr1_elim___boxed(lean_object* v_motive_114_, lean_object* v_t_115_, lean_object* v_h_116_, lean_object* v_sigusr1_117_){
_start:
{
uint8_t v_t_boxed_118_; lean_object* v_res_119_; 
v_t_boxed_118_ = lean_unbox(v_t_115_);
v_res_119_ = l_Std_Async_Signal_sigusr1_elim(v_motive_114_, v_t_boxed_118_, v_h_116_, v_sigusr1_117_);
lean_dec(v_sigusr1_117_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr2_elim___redArg(lean_object* v_sigusr2_120_){
_start:
{
lean_inc(v_sigusr2_120_);
return v_sigusr2_120_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr2_elim___redArg___boxed(lean_object* v_sigusr2_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Std_Async_Signal_sigusr2_elim___redArg(v_sigusr2_121_);
lean_dec(v_sigusr2_121_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr2_elim(lean_object* v_motive_123_, uint8_t v_t_124_, lean_object* v_h_125_, lean_object* v_sigusr2_126_){
_start:
{
lean_inc(v_sigusr2_126_);
return v_sigusr2_126_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr2_elim___boxed(lean_object* v_motive_127_, lean_object* v_t_128_, lean_object* v_h_129_, lean_object* v_sigusr2_130_){
_start:
{
uint8_t v_t_boxed_131_; lean_object* v_res_132_; 
v_t_boxed_131_ = lean_unbox(v_t_128_);
v_res_132_ = l_Std_Async_Signal_sigusr2_elim(v_motive_127_, v_t_boxed_131_, v_h_129_, v_sigusr2_130_);
lean_dec(v_sigusr2_130_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigalrm_elim___redArg(lean_object* v_sigalrm_133_){
_start:
{
lean_inc(v_sigalrm_133_);
return v_sigalrm_133_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigalrm_elim___redArg___boxed(lean_object* v_sigalrm_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Std_Async_Signal_sigalrm_elim___redArg(v_sigalrm_134_);
lean_dec(v_sigalrm_134_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigalrm_elim(lean_object* v_motive_136_, uint8_t v_t_137_, lean_object* v_h_138_, lean_object* v_sigalrm_139_){
_start:
{
lean_inc(v_sigalrm_139_);
return v_sigalrm_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigalrm_elim___boxed(lean_object* v_motive_140_, lean_object* v_t_141_, lean_object* v_h_142_, lean_object* v_sigalrm_143_){
_start:
{
uint8_t v_t_boxed_144_; lean_object* v_res_145_; 
v_t_boxed_144_ = lean_unbox(v_t_141_);
v_res_145_ = l_Std_Async_Signal_sigalrm_elim(v_motive_140_, v_t_boxed_144_, v_h_142_, v_sigalrm_143_);
lean_dec(v_sigalrm_143_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigterm_elim___redArg(lean_object* v_sigterm_146_){
_start:
{
lean_inc(v_sigterm_146_);
return v_sigterm_146_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigterm_elim___redArg___boxed(lean_object* v_sigterm_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Std_Async_Signal_sigterm_elim___redArg(v_sigterm_147_);
lean_dec(v_sigterm_147_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigterm_elim(lean_object* v_motive_149_, uint8_t v_t_150_, lean_object* v_h_151_, lean_object* v_sigterm_152_){
_start:
{
lean_inc(v_sigterm_152_);
return v_sigterm_152_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigterm_elim___boxed(lean_object* v_motive_153_, lean_object* v_t_154_, lean_object* v_h_155_, lean_object* v_sigterm_156_){
_start:
{
uint8_t v_t_boxed_157_; lean_object* v_res_158_; 
v_t_boxed_157_ = lean_unbox(v_t_154_);
v_res_158_ = l_Std_Async_Signal_sigterm_elim(v_motive_153_, v_t_boxed_157_, v_h_155_, v_sigterm_156_);
lean_dec(v_sigterm_156_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigchld_elim___redArg(lean_object* v_sigchld_159_){
_start:
{
lean_inc(v_sigchld_159_);
return v_sigchld_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigchld_elim___redArg___boxed(lean_object* v_sigchld_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Std_Async_Signal_sigchld_elim___redArg(v_sigchld_160_);
lean_dec(v_sigchld_160_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigchld_elim(lean_object* v_motive_162_, uint8_t v_t_163_, lean_object* v_h_164_, lean_object* v_sigchld_165_){
_start:
{
lean_inc(v_sigchld_165_);
return v_sigchld_165_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigchld_elim___boxed(lean_object* v_motive_166_, lean_object* v_t_167_, lean_object* v_h_168_, lean_object* v_sigchld_169_){
_start:
{
uint8_t v_t_boxed_170_; lean_object* v_res_171_; 
v_t_boxed_170_ = lean_unbox(v_t_167_);
v_res_171_ = l_Std_Async_Signal_sigchld_elim(v_motive_166_, v_t_boxed_170_, v_h_168_, v_sigchld_169_);
lean_dec(v_sigchld_169_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigcont_elim___redArg(lean_object* v_sigcont_172_){
_start:
{
lean_inc(v_sigcont_172_);
return v_sigcont_172_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigcont_elim___redArg___boxed(lean_object* v_sigcont_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Std_Async_Signal_sigcont_elim___redArg(v_sigcont_173_);
lean_dec(v_sigcont_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigcont_elim(lean_object* v_motive_175_, uint8_t v_t_176_, lean_object* v_h_177_, lean_object* v_sigcont_178_){
_start:
{
lean_inc(v_sigcont_178_);
return v_sigcont_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigcont_elim___boxed(lean_object* v_motive_179_, lean_object* v_t_180_, lean_object* v_h_181_, lean_object* v_sigcont_182_){
_start:
{
uint8_t v_t_boxed_183_; lean_object* v_res_184_; 
v_t_boxed_183_ = lean_unbox(v_t_180_);
v_res_184_ = l_Std_Async_Signal_sigcont_elim(v_motive_179_, v_t_boxed_183_, v_h_181_, v_sigcont_182_);
lean_dec(v_sigcont_182_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtstp_elim___redArg(lean_object* v_sigtstp_185_){
_start:
{
lean_inc(v_sigtstp_185_);
return v_sigtstp_185_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtstp_elim___redArg___boxed(lean_object* v_sigtstp_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Std_Async_Signal_sigtstp_elim___redArg(v_sigtstp_186_);
lean_dec(v_sigtstp_186_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtstp_elim(lean_object* v_motive_188_, uint8_t v_t_189_, lean_object* v_h_190_, lean_object* v_sigtstp_191_){
_start:
{
lean_inc(v_sigtstp_191_);
return v_sigtstp_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtstp_elim___boxed(lean_object* v_motive_192_, lean_object* v_t_193_, lean_object* v_h_194_, lean_object* v_sigtstp_195_){
_start:
{
uint8_t v_t_boxed_196_; lean_object* v_res_197_; 
v_t_boxed_196_ = lean_unbox(v_t_193_);
v_res_197_ = l_Std_Async_Signal_sigtstp_elim(v_motive_192_, v_t_boxed_196_, v_h_194_, v_sigtstp_195_);
lean_dec(v_sigtstp_195_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttin_elim___redArg(lean_object* v_sigttin_198_){
_start:
{
lean_inc(v_sigttin_198_);
return v_sigttin_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttin_elim___redArg___boxed(lean_object* v_sigttin_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Std_Async_Signal_sigttin_elim___redArg(v_sigttin_199_);
lean_dec(v_sigttin_199_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttin_elim(lean_object* v_motive_201_, uint8_t v_t_202_, lean_object* v_h_203_, lean_object* v_sigttin_204_){
_start:
{
lean_inc(v_sigttin_204_);
return v_sigttin_204_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttin_elim___boxed(lean_object* v_motive_205_, lean_object* v_t_206_, lean_object* v_h_207_, lean_object* v_sigttin_208_){
_start:
{
uint8_t v_t_boxed_209_; lean_object* v_res_210_; 
v_t_boxed_209_ = lean_unbox(v_t_206_);
v_res_210_ = l_Std_Async_Signal_sigttin_elim(v_motive_205_, v_t_boxed_209_, v_h_207_, v_sigttin_208_);
lean_dec(v_sigttin_208_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttou_elim___redArg(lean_object* v_sigttou_211_){
_start:
{
lean_inc(v_sigttou_211_);
return v_sigttou_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttou_elim___redArg___boxed(lean_object* v_sigttou_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Std_Async_Signal_sigttou_elim___redArg(v_sigttou_212_);
lean_dec(v_sigttou_212_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttou_elim(lean_object* v_motive_214_, uint8_t v_t_215_, lean_object* v_h_216_, lean_object* v_sigttou_217_){
_start:
{
lean_inc(v_sigttou_217_);
return v_sigttou_217_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttou_elim___boxed(lean_object* v_motive_218_, lean_object* v_t_219_, lean_object* v_h_220_, lean_object* v_sigttou_221_){
_start:
{
uint8_t v_t_boxed_222_; lean_object* v_res_223_; 
v_t_boxed_222_ = lean_unbox(v_t_219_);
v_res_223_ = l_Std_Async_Signal_sigttou_elim(v_motive_218_, v_t_boxed_222_, v_h_220_, v_sigttou_221_);
lean_dec(v_sigttou_221_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigurg_elim___redArg(lean_object* v_sigurg_224_){
_start:
{
lean_inc(v_sigurg_224_);
return v_sigurg_224_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigurg_elim___redArg___boxed(lean_object* v_sigurg_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Std_Async_Signal_sigurg_elim___redArg(v_sigurg_225_);
lean_dec(v_sigurg_225_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigurg_elim(lean_object* v_motive_227_, uint8_t v_t_228_, lean_object* v_h_229_, lean_object* v_sigurg_230_){
_start:
{
lean_inc(v_sigurg_230_);
return v_sigurg_230_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigurg_elim___boxed(lean_object* v_motive_231_, lean_object* v_t_232_, lean_object* v_h_233_, lean_object* v_sigurg_234_){
_start:
{
uint8_t v_t_boxed_235_; lean_object* v_res_236_; 
v_t_boxed_235_ = lean_unbox(v_t_232_);
v_res_236_ = l_Std_Async_Signal_sigurg_elim(v_motive_231_, v_t_boxed_235_, v_h_233_, v_sigurg_234_);
lean_dec(v_sigurg_234_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxcpu_elim___redArg(lean_object* v_sigxcpu_237_){
_start:
{
lean_inc(v_sigxcpu_237_);
return v_sigxcpu_237_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxcpu_elim___redArg___boxed(lean_object* v_sigxcpu_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Std_Async_Signal_sigxcpu_elim___redArg(v_sigxcpu_238_);
lean_dec(v_sigxcpu_238_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxcpu_elim(lean_object* v_motive_240_, uint8_t v_t_241_, lean_object* v_h_242_, lean_object* v_sigxcpu_243_){
_start:
{
lean_inc(v_sigxcpu_243_);
return v_sigxcpu_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxcpu_elim___boxed(lean_object* v_motive_244_, lean_object* v_t_245_, lean_object* v_h_246_, lean_object* v_sigxcpu_247_){
_start:
{
uint8_t v_t_boxed_248_; lean_object* v_res_249_; 
v_t_boxed_248_ = lean_unbox(v_t_245_);
v_res_249_ = l_Std_Async_Signal_sigxcpu_elim(v_motive_244_, v_t_boxed_248_, v_h_246_, v_sigxcpu_247_);
lean_dec(v_sigxcpu_247_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxfsz_elim___redArg(lean_object* v_sigxfsz_250_){
_start:
{
lean_inc(v_sigxfsz_250_);
return v_sigxfsz_250_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxfsz_elim___redArg___boxed(lean_object* v_sigxfsz_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Std_Async_Signal_sigxfsz_elim___redArg(v_sigxfsz_251_);
lean_dec(v_sigxfsz_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxfsz_elim(lean_object* v_motive_253_, uint8_t v_t_254_, lean_object* v_h_255_, lean_object* v_sigxfsz_256_){
_start:
{
lean_inc(v_sigxfsz_256_);
return v_sigxfsz_256_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxfsz_elim___boxed(lean_object* v_motive_257_, lean_object* v_t_258_, lean_object* v_h_259_, lean_object* v_sigxfsz_260_){
_start:
{
uint8_t v_t_boxed_261_; lean_object* v_res_262_; 
v_t_boxed_261_ = lean_unbox(v_t_258_);
v_res_262_ = l_Std_Async_Signal_sigxfsz_elim(v_motive_257_, v_t_boxed_261_, v_h_259_, v_sigxfsz_260_);
lean_dec(v_sigxfsz_260_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigvtalrm_elim___redArg(lean_object* v_sigvtalrm_263_){
_start:
{
lean_inc(v_sigvtalrm_263_);
return v_sigvtalrm_263_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigvtalrm_elim___redArg___boxed(lean_object* v_sigvtalrm_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Std_Async_Signal_sigvtalrm_elim___redArg(v_sigvtalrm_264_);
lean_dec(v_sigvtalrm_264_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigvtalrm_elim(lean_object* v_motive_266_, uint8_t v_t_267_, lean_object* v_h_268_, lean_object* v_sigvtalrm_269_){
_start:
{
lean_inc(v_sigvtalrm_269_);
return v_sigvtalrm_269_;
}
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
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigprof_elim(lean_object* v_motive_279_, uint8_t v_t_280_, lean_object* v_h_281_, lean_object* v_sigprof_282_){
_start:
{
lean_inc(v_sigprof_282_);
return v_sigprof_282_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigprof_elim___boxed(lean_object* v_motive_283_, lean_object* v_t_284_, lean_object* v_h_285_, lean_object* v_sigprof_286_){
_start:
{
uint8_t v_t_boxed_287_; lean_object* v_res_288_; 
v_t_boxed_287_ = lean_unbox(v_t_284_);
v_res_288_ = l_Std_Async_Signal_sigprof_elim(v_motive_283_, v_t_boxed_287_, v_h_285_, v_sigprof_286_);
lean_dec(v_sigprof_286_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigwinch_elim___redArg(lean_object* v_sigwinch_289_){
_start:
{
lean_inc(v_sigwinch_289_);
return v_sigwinch_289_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigwinch_elim___redArg___boxed(lean_object* v_sigwinch_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Std_Async_Signal_sigwinch_elim___redArg(v_sigwinch_290_);
lean_dec(v_sigwinch_290_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigwinch_elim(lean_object* v_motive_292_, uint8_t v_t_293_, lean_object* v_h_294_, lean_object* v_sigwinch_295_){
_start:
{
lean_inc(v_sigwinch_295_);
return v_sigwinch_295_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigwinch_elim___boxed(lean_object* v_motive_296_, lean_object* v_t_297_, lean_object* v_h_298_, lean_object* v_sigwinch_299_){
_start:
{
uint8_t v_t_boxed_300_; lean_object* v_res_301_; 
v_t_boxed_300_ = lean_unbox(v_t_297_);
v_res_301_ = l_Std_Async_Signal_sigwinch_elim(v_motive_296_, v_t_boxed_300_, v_h_298_, v_sigwinch_299_);
lean_dec(v_sigwinch_299_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigio_elim___redArg(lean_object* v_sigio_302_){
_start:
{
lean_inc(v_sigio_302_);
return v_sigio_302_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigio_elim___redArg___boxed(lean_object* v_sigio_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Std_Async_Signal_sigio_elim___redArg(v_sigio_303_);
lean_dec(v_sigio_303_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigio_elim(lean_object* v_motive_305_, uint8_t v_t_306_, lean_object* v_h_307_, lean_object* v_sigio_308_){
_start:
{
lean_inc(v_sigio_308_);
return v_sigio_308_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigio_elim___boxed(lean_object* v_motive_309_, lean_object* v_t_310_, lean_object* v_h_311_, lean_object* v_sigio_312_){
_start:
{
uint8_t v_t_boxed_313_; lean_object* v_res_314_; 
v_t_boxed_313_ = lean_unbox(v_t_310_);
v_res_314_ = l_Std_Async_Signal_sigio_elim(v_motive_309_, v_t_boxed_313_, v_h_311_, v_sigio_312_);
lean_dec(v_sigio_312_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigsys_elim___redArg(lean_object* v_sigsys_315_){
_start:
{
lean_inc(v_sigsys_315_);
return v_sigsys_315_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigsys_elim___redArg___boxed(lean_object* v_sigsys_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Std_Async_Signal_sigsys_elim___redArg(v_sigsys_316_);
lean_dec(v_sigsys_316_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigsys_elim(lean_object* v_motive_318_, uint8_t v_t_319_, lean_object* v_h_320_, lean_object* v_sigsys_321_){
_start:
{
lean_inc(v_sigsys_321_);
return v_sigsys_321_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigsys_elim___boxed(lean_object* v_motive_322_, lean_object* v_t_323_, lean_object* v_h_324_, lean_object* v_sigsys_325_){
_start:
{
uint8_t v_t_boxed_326_; lean_object* v_res_327_; 
v_t_boxed_326_ = lean_unbox(v_t_323_);
v_res_327_ = l_Std_Async_Signal_sigsys_elim(v_motive_322_, v_t_boxed_326_, v_h_324_, v_sigsys_325_);
lean_dec(v_sigsys_325_);
return v_res_327_;
}
}
static lean_object* _init_l_Std_Async_instReprSignal_repr___closed__44(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = lean_unsigned_to_nat(2u);
v___x_395_ = lean_nat_to_int(v___x_394_);
return v___x_395_;
}
}
static lean_object* _init_l_Std_Async_instReprSignal_repr___closed__45(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = lean_unsigned_to_nat(1u);
v___x_397_ = lean_nat_to_int(v___x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instReprSignal_repr(uint8_t v_x_398_, lean_object* v_prec_399_){
_start:
{
lean_object* v___y_401_; lean_object* v___y_408_; lean_object* v___y_415_; lean_object* v___y_422_; lean_object* v___y_429_; lean_object* v___y_436_; lean_object* v___y_443_; lean_object* v___y_450_; lean_object* v___y_457_; lean_object* v___y_464_; lean_object* v___y_471_; lean_object* v___y_478_; lean_object* v___y_485_; lean_object* v___y_492_; lean_object* v___y_499_; lean_object* v___y_506_; lean_object* v___y_513_; lean_object* v___y_520_; lean_object* v___y_527_; lean_object* v___y_534_; lean_object* v___y_541_; lean_object* v___y_548_; 
switch(v_x_398_)
{
case 0:
{
lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_554_ = lean_unsigned_to_nat(1024u);
v___x_555_ = lean_nat_dec_le(v___x_554_, v_prec_399_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; 
v___x_556_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_401_ = v___x_556_;
goto v___jp_400_;
}
else
{
lean_object* v___x_557_; 
v___x_557_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_401_ = v___x_557_;
goto v___jp_400_;
}
}
case 1:
{
lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_558_ = lean_unsigned_to_nat(1024u);
v___x_559_ = lean_nat_dec_le(v___x_558_, v_prec_399_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; 
v___x_560_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_408_ = v___x_560_;
goto v___jp_407_;
}
else
{
lean_object* v___x_561_; 
v___x_561_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_408_ = v___x_561_;
goto v___jp_407_;
}
}
case 2:
{
lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_562_ = lean_unsigned_to_nat(1024u);
v___x_563_ = lean_nat_dec_le(v___x_562_, v_prec_399_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; 
v___x_564_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_415_ = v___x_564_;
goto v___jp_414_;
}
else
{
lean_object* v___x_565_; 
v___x_565_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_415_ = v___x_565_;
goto v___jp_414_;
}
}
case 3:
{
lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_566_ = lean_unsigned_to_nat(1024u);
v___x_567_ = lean_nat_dec_le(v___x_566_, v_prec_399_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; 
v___x_568_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_422_ = v___x_568_;
goto v___jp_421_;
}
else
{
lean_object* v___x_569_; 
v___x_569_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_422_ = v___x_569_;
goto v___jp_421_;
}
}
case 4:
{
lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_570_ = lean_unsigned_to_nat(1024u);
v___x_571_ = lean_nat_dec_le(v___x_570_, v_prec_399_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; 
v___x_572_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_429_ = v___x_572_;
goto v___jp_428_;
}
else
{
lean_object* v___x_573_; 
v___x_573_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_429_ = v___x_573_;
goto v___jp_428_;
}
}
case 5:
{
lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_574_ = lean_unsigned_to_nat(1024u);
v___x_575_ = lean_nat_dec_le(v___x_574_, v_prec_399_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; 
v___x_576_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_436_ = v___x_576_;
goto v___jp_435_;
}
else
{
lean_object* v___x_577_; 
v___x_577_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_436_ = v___x_577_;
goto v___jp_435_;
}
}
case 6:
{
lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_578_ = lean_unsigned_to_nat(1024u);
v___x_579_ = lean_nat_dec_le(v___x_578_, v_prec_399_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; 
v___x_580_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_443_ = v___x_580_;
goto v___jp_442_;
}
else
{
lean_object* v___x_581_; 
v___x_581_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_443_ = v___x_581_;
goto v___jp_442_;
}
}
case 7:
{
lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_582_ = lean_unsigned_to_nat(1024u);
v___x_583_ = lean_nat_dec_le(v___x_582_, v_prec_399_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; 
v___x_584_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_450_ = v___x_584_;
goto v___jp_449_;
}
else
{
lean_object* v___x_585_; 
v___x_585_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_450_ = v___x_585_;
goto v___jp_449_;
}
}
case 8:
{
lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(1024u);
v___x_587_ = lean_nat_dec_le(v___x_586_, v_prec_399_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; 
v___x_588_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_457_ = v___x_588_;
goto v___jp_456_;
}
else
{
lean_object* v___x_589_; 
v___x_589_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_457_ = v___x_589_;
goto v___jp_456_;
}
}
case 9:
{
lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_590_ = lean_unsigned_to_nat(1024u);
v___x_591_ = lean_nat_dec_le(v___x_590_, v_prec_399_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; 
v___x_592_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_464_ = v___x_592_;
goto v___jp_463_;
}
else
{
lean_object* v___x_593_; 
v___x_593_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_464_ = v___x_593_;
goto v___jp_463_;
}
}
case 10:
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = lean_unsigned_to_nat(1024u);
v___x_595_ = lean_nat_dec_le(v___x_594_, v_prec_399_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
v___x_596_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_471_ = v___x_596_;
goto v___jp_470_;
}
else
{
lean_object* v___x_597_; 
v___x_597_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_471_ = v___x_597_;
goto v___jp_470_;
}
}
case 11:
{
lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_598_ = lean_unsigned_to_nat(1024u);
v___x_599_ = lean_nat_dec_le(v___x_598_, v_prec_399_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; 
v___x_600_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_478_ = v___x_600_;
goto v___jp_477_;
}
else
{
lean_object* v___x_601_; 
v___x_601_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_478_ = v___x_601_;
goto v___jp_477_;
}
}
case 12:
{
lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_602_ = lean_unsigned_to_nat(1024u);
v___x_603_ = lean_nat_dec_le(v___x_602_, v_prec_399_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; 
v___x_604_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_485_ = v___x_604_;
goto v___jp_484_;
}
else
{
lean_object* v___x_605_; 
v___x_605_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_485_ = v___x_605_;
goto v___jp_484_;
}
}
case 13:
{
lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = lean_unsigned_to_nat(1024u);
v___x_607_ = lean_nat_dec_le(v___x_606_, v_prec_399_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; 
v___x_608_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_492_ = v___x_608_;
goto v___jp_491_;
}
else
{
lean_object* v___x_609_; 
v___x_609_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_492_ = v___x_609_;
goto v___jp_491_;
}
}
case 14:
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = lean_unsigned_to_nat(1024u);
v___x_611_ = lean_nat_dec_le(v___x_610_, v_prec_399_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; 
v___x_612_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_499_ = v___x_612_;
goto v___jp_498_;
}
else
{
lean_object* v___x_613_; 
v___x_613_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_499_ = v___x_613_;
goto v___jp_498_;
}
}
case 15:
{
lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_614_ = lean_unsigned_to_nat(1024u);
v___x_615_ = lean_nat_dec_le(v___x_614_, v_prec_399_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; 
v___x_616_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_506_ = v___x_616_;
goto v___jp_505_;
}
else
{
lean_object* v___x_617_; 
v___x_617_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_506_ = v___x_617_;
goto v___jp_505_;
}
}
case 16:
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = lean_unsigned_to_nat(1024u);
v___x_619_ = lean_nat_dec_le(v___x_618_, v_prec_399_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
v___x_620_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_513_ = v___x_620_;
goto v___jp_512_;
}
else
{
lean_object* v___x_621_; 
v___x_621_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_513_ = v___x_621_;
goto v___jp_512_;
}
}
case 17:
{
lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_622_ = lean_unsigned_to_nat(1024u);
v___x_623_ = lean_nat_dec_le(v___x_622_, v_prec_399_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; 
v___x_624_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_520_ = v___x_624_;
goto v___jp_519_;
}
else
{
lean_object* v___x_625_; 
v___x_625_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_520_ = v___x_625_;
goto v___jp_519_;
}
}
case 18:
{
lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_626_ = lean_unsigned_to_nat(1024u);
v___x_627_ = lean_nat_dec_le(v___x_626_, v_prec_399_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; 
v___x_628_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_527_ = v___x_628_;
goto v___jp_526_;
}
else
{
lean_object* v___x_629_; 
v___x_629_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_527_ = v___x_629_;
goto v___jp_526_;
}
}
case 19:
{
lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_630_ = lean_unsigned_to_nat(1024u);
v___x_631_ = lean_nat_dec_le(v___x_630_, v_prec_399_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; 
v___x_632_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_534_ = v___x_632_;
goto v___jp_533_;
}
else
{
lean_object* v___x_633_; 
v___x_633_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_534_ = v___x_633_;
goto v___jp_533_;
}
}
case 20:
{
lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_634_ = lean_unsigned_to_nat(1024u);
v___x_635_ = lean_nat_dec_le(v___x_634_, v_prec_399_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; 
v___x_636_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_541_ = v___x_636_;
goto v___jp_540_;
}
else
{
lean_object* v___x_637_; 
v___x_637_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_541_ = v___x_637_;
goto v___jp_540_;
}
}
default: 
{
lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_638_ = lean_unsigned_to_nat(1024u);
v___x_639_ = lean_nat_dec_le(v___x_638_, v_prec_399_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; 
v___x_640_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_548_ = v___x_640_;
goto v___jp_547_;
}
else
{
lean_object* v___x_641_; 
v___x_641_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_548_ = v___x_641_;
goto v___jp_547_;
}
}
}
v___jp_400_:
{
lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_402_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__1));
lean_inc(v___y_401_);
v___x_403_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_403_, 0, v___y_401_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = 0;
v___x_405_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_405_, 0, v___x_403_);
lean_ctor_set_uint8(v___x_405_, sizeof(void*)*1, v___x_404_);
v___x_406_ = l_Repr_addAppParen(v___x_405_, v_prec_399_);
return v___x_406_;
}
v___jp_407_:
{
lean_object* v___x_409_; lean_object* v___x_410_; uint8_t v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_409_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__3));
lean_inc(v___y_408_);
v___x_410_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_410_, 0, v___y_408_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = 0;
v___x_412_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_412_, 0, v___x_410_);
lean_ctor_set_uint8(v___x_412_, sizeof(void*)*1, v___x_411_);
v___x_413_ = l_Repr_addAppParen(v___x_412_, v_prec_399_);
return v___x_413_;
}
v___jp_414_:
{
lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_416_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__5));
lean_inc(v___y_415_);
v___x_417_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_417_, 0, v___y_415_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = 0;
v___x_419_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_419_, 0, v___x_417_);
lean_ctor_set_uint8(v___x_419_, sizeof(void*)*1, v___x_418_);
v___x_420_ = l_Repr_addAppParen(v___x_419_, v_prec_399_);
return v___x_420_;
}
v___jp_421_:
{
lean_object* v___x_423_; lean_object* v___x_424_; uint8_t v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_423_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__7));
lean_inc(v___y_422_);
v___x_424_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_424_, 0, v___y_422_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = 0;
v___x_426_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_426_, 0, v___x_424_);
lean_ctor_set_uint8(v___x_426_, sizeof(void*)*1, v___x_425_);
v___x_427_ = l_Repr_addAppParen(v___x_426_, v_prec_399_);
return v___x_427_;
}
v___jp_428_:
{
lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_430_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__9));
lean_inc(v___y_429_);
v___x_431_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_431_, 0, v___y_429_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
v___x_432_ = 0;
v___x_433_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_433_, 0, v___x_431_);
lean_ctor_set_uint8(v___x_433_, sizeof(void*)*1, v___x_432_);
v___x_434_ = l_Repr_addAppParen(v___x_433_, v_prec_399_);
return v___x_434_;
}
v___jp_435_:
{
lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_437_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__11));
lean_inc(v___y_436_);
v___x_438_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_438_, 0, v___y_436_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
v___x_439_ = 0;
v___x_440_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_440_, 0, v___x_438_);
lean_ctor_set_uint8(v___x_440_, sizeof(void*)*1, v___x_439_);
v___x_441_ = l_Repr_addAppParen(v___x_440_, v_prec_399_);
return v___x_441_;
}
v___jp_442_:
{
lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_444_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__13));
lean_inc(v___y_443_);
v___x_445_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_445_, 0, v___y_443_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = 0;
v___x_447_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_447_, 0, v___x_445_);
lean_ctor_set_uint8(v___x_447_, sizeof(void*)*1, v___x_446_);
v___x_448_ = l_Repr_addAppParen(v___x_447_, v_prec_399_);
return v___x_448_;
}
v___jp_449_:
{
lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_451_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__15));
lean_inc(v___y_450_);
v___x_452_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_452_, 0, v___y_450_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
v___x_453_ = 0;
v___x_454_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_454_, 0, v___x_452_);
lean_ctor_set_uint8(v___x_454_, sizeof(void*)*1, v___x_453_);
v___x_455_ = l_Repr_addAppParen(v___x_454_, v_prec_399_);
return v___x_455_;
}
v___jp_456_:
{
lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_458_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__17));
lean_inc(v___y_457_);
v___x_459_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_459_, 0, v___y_457_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = 0;
v___x_461_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_461_, 0, v___x_459_);
lean_ctor_set_uint8(v___x_461_, sizeof(void*)*1, v___x_460_);
v___x_462_ = l_Repr_addAppParen(v___x_461_, v_prec_399_);
return v___x_462_;
}
v___jp_463_:
{
lean_object* v___x_465_; lean_object* v___x_466_; uint8_t v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_465_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__19));
lean_inc(v___y_464_);
v___x_466_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_466_, 0, v___y_464_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
v___x_467_ = 0;
v___x_468_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_468_, 0, v___x_466_);
lean_ctor_set_uint8(v___x_468_, sizeof(void*)*1, v___x_467_);
v___x_469_ = l_Repr_addAppParen(v___x_468_, v_prec_399_);
return v___x_469_;
}
v___jp_470_:
{
lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_472_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__21));
lean_inc(v___y_471_);
v___x_473_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_473_, 0, v___y_471_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
v___x_474_ = 0;
v___x_475_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_475_, 0, v___x_473_);
lean_ctor_set_uint8(v___x_475_, sizeof(void*)*1, v___x_474_);
v___x_476_ = l_Repr_addAppParen(v___x_475_, v_prec_399_);
return v___x_476_;
}
v___jp_477_:
{
lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_479_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__23));
lean_inc(v___y_478_);
v___x_480_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_480_, 0, v___y_478_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
v___x_481_ = 0;
v___x_482_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_482_, 0, v___x_480_);
lean_ctor_set_uint8(v___x_482_, sizeof(void*)*1, v___x_481_);
v___x_483_ = l_Repr_addAppParen(v___x_482_, v_prec_399_);
return v___x_483_;
}
v___jp_484_:
{
lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_486_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__25));
lean_inc(v___y_485_);
v___x_487_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_487_, 0, v___y_485_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = 0;
v___x_489_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_489_, 0, v___x_487_);
lean_ctor_set_uint8(v___x_489_, sizeof(void*)*1, v___x_488_);
v___x_490_ = l_Repr_addAppParen(v___x_489_, v_prec_399_);
return v___x_490_;
}
v___jp_491_:
{
lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_493_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__27));
lean_inc(v___y_492_);
v___x_494_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_494_, 0, v___y_492_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = 0;
v___x_496_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_496_, 0, v___x_494_);
lean_ctor_set_uint8(v___x_496_, sizeof(void*)*1, v___x_495_);
v___x_497_ = l_Repr_addAppParen(v___x_496_, v_prec_399_);
return v___x_497_;
}
v___jp_498_:
{
lean_object* v___x_500_; lean_object* v___x_501_; uint8_t v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_500_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__29));
lean_inc(v___y_499_);
v___x_501_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_501_, 0, v___y_499_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = 0;
v___x_503_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_503_, 0, v___x_501_);
lean_ctor_set_uint8(v___x_503_, sizeof(void*)*1, v___x_502_);
v___x_504_ = l_Repr_addAppParen(v___x_503_, v_prec_399_);
return v___x_504_;
}
v___jp_505_:
{
lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_507_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__31));
lean_inc(v___y_506_);
v___x_508_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_508_, 0, v___y_506_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = 0;
v___x_510_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_510_, 0, v___x_508_);
lean_ctor_set_uint8(v___x_510_, sizeof(void*)*1, v___x_509_);
v___x_511_ = l_Repr_addAppParen(v___x_510_, v_prec_399_);
return v___x_511_;
}
v___jp_512_:
{
lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_514_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__33));
lean_inc(v___y_513_);
v___x_515_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_515_, 0, v___y_513_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
v___x_516_ = 0;
v___x_517_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_517_, 0, v___x_515_);
lean_ctor_set_uint8(v___x_517_, sizeof(void*)*1, v___x_516_);
v___x_518_ = l_Repr_addAppParen(v___x_517_, v_prec_399_);
return v___x_518_;
}
v___jp_519_:
{
lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_521_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__35));
lean_inc(v___y_520_);
v___x_522_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_522_, 0, v___y_520_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
v___x_523_ = 0;
v___x_524_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set_uint8(v___x_524_, sizeof(void*)*1, v___x_523_);
v___x_525_ = l_Repr_addAppParen(v___x_524_, v_prec_399_);
return v___x_525_;
}
v___jp_526_:
{
lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_528_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__37));
lean_inc(v___y_527_);
v___x_529_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_529_, 0, v___y_527_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = 0;
v___x_531_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set_uint8(v___x_531_, sizeof(void*)*1, v___x_530_);
v___x_532_ = l_Repr_addAppParen(v___x_531_, v_prec_399_);
return v___x_532_;
}
v___jp_533_:
{
lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_535_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__39));
lean_inc(v___y_534_);
v___x_536_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_536_, 0, v___y_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = 0;
v___x_538_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set_uint8(v___x_538_, sizeof(void*)*1, v___x_537_);
v___x_539_ = l_Repr_addAppParen(v___x_538_, v_prec_399_);
return v___x_539_;
}
v___jp_540_:
{
lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_542_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__41));
lean_inc(v___y_541_);
v___x_543_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_543_, 0, v___y_541_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = 0;
v___x_545_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_545_, 0, v___x_543_);
lean_ctor_set_uint8(v___x_545_, sizeof(void*)*1, v___x_544_);
v___x_546_ = l_Repr_addAppParen(v___x_545_, v_prec_399_);
return v___x_546_;
}
v___jp_547_:
{
lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_549_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__43));
lean_inc(v___y_548_);
v___x_550_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_550_, 0, v___y_548_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = 0;
v___x_552_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_552_, 0, v___x_550_);
lean_ctor_set_uint8(v___x_552_, sizeof(void*)*1, v___x_551_);
v___x_553_ = l_Repr_addAppParen(v___x_552_, v_prec_399_);
return v___x_553_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_instReprSignal_repr___boxed(lean_object* v_x_642_, lean_object* v_prec_643_){
_start:
{
uint8_t v_x_1241__boxed_644_; lean_object* v_res_645_; 
v_x_1241__boxed_644_ = lean_unbox(v_x_642_);
v_res_645_ = l_Std_Async_instReprSignal_repr(v_x_1241__boxed_644_, v_prec_643_);
lean_dec(v_prec_643_);
return v_res_645_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_Signal_ofNat(lean_object* v_n_648_){
_start:
{
lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_649_ = lean_unsigned_to_nat(10u);
v___x_650_ = lean_nat_dec_le(v_n_648_, v___x_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_651_ = lean_unsigned_to_nat(15u);
v___x_652_ = lean_nat_dec_le(v_n_648_, v___x_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_653_ = lean_unsigned_to_nat(18u);
v___x_654_ = lean_nat_dec_le(v_n_648_, v___x_653_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_655_ = lean_unsigned_to_nat(19u);
v___x_656_ = lean_nat_dec_le(v_n_648_, v___x_655_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_657_ = lean_unsigned_to_nat(20u);
v___x_658_ = lean_nat_dec_le(v_n_648_, v___x_657_);
if (v___x_658_ == 0)
{
uint8_t v___x_659_; 
v___x_659_ = 21;
return v___x_659_;
}
else
{
uint8_t v___x_660_; 
v___x_660_ = 20;
return v___x_660_;
}
}
else
{
uint8_t v___x_661_; 
v___x_661_ = 19;
return v___x_661_;
}
}
else
{
lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = lean_unsigned_to_nat(16u);
v___x_663_ = lean_nat_dec_le(v_n_648_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_664_ = lean_unsigned_to_nat(17u);
v___x_665_ = lean_nat_dec_le(v_n_648_, v___x_664_);
if (v___x_665_ == 0)
{
uint8_t v___x_666_; 
v___x_666_ = 18;
return v___x_666_;
}
else
{
uint8_t v___x_667_; 
v___x_667_ = 17;
return v___x_667_;
}
}
else
{
uint8_t v___x_668_; 
v___x_668_ = 16;
return v___x_668_;
}
}
}
else
{
lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_669_ = lean_unsigned_to_nat(12u);
v___x_670_ = lean_nat_dec_le(v_n_648_, v___x_669_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_671_ = lean_unsigned_to_nat(13u);
v___x_672_ = lean_nat_dec_le(v_n_648_, v___x_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_673_ = lean_unsigned_to_nat(14u);
v___x_674_ = lean_nat_dec_le(v_n_648_, v___x_673_);
if (v___x_674_ == 0)
{
uint8_t v___x_675_; 
v___x_675_ = 15;
return v___x_675_;
}
else
{
uint8_t v___x_676_; 
v___x_676_ = 14;
return v___x_676_;
}
}
else
{
uint8_t v___x_677_; 
v___x_677_ = 13;
return v___x_677_;
}
}
else
{
lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_678_ = lean_unsigned_to_nat(11u);
v___x_679_ = lean_nat_dec_le(v_n_648_, v___x_678_);
if (v___x_679_ == 0)
{
uint8_t v___x_680_; 
v___x_680_ = 12;
return v___x_680_;
}
else
{
uint8_t v___x_681_; 
v___x_681_ = 11;
return v___x_681_;
}
}
}
}
else
{
lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_682_ = lean_unsigned_to_nat(4u);
v___x_683_ = lean_nat_dec_le(v_n_648_, v___x_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_684_ = lean_unsigned_to_nat(7u);
v___x_685_ = lean_nat_dec_le(v_n_648_, v___x_684_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_686_ = lean_unsigned_to_nat(8u);
v___x_687_ = lean_nat_dec_le(v_n_648_, v___x_686_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_688_ = lean_unsigned_to_nat(9u);
v___x_689_ = lean_nat_dec_le(v_n_648_, v___x_688_);
if (v___x_689_ == 0)
{
uint8_t v___x_690_; 
v___x_690_ = 10;
return v___x_690_;
}
else
{
uint8_t v___x_691_; 
v___x_691_ = 9;
return v___x_691_;
}
}
else
{
uint8_t v___x_692_; 
v___x_692_ = 8;
return v___x_692_;
}
}
else
{
lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_693_ = lean_unsigned_to_nat(5u);
v___x_694_ = lean_nat_dec_le(v_n_648_, v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_695_ = lean_unsigned_to_nat(6u);
v___x_696_ = lean_nat_dec_le(v_n_648_, v___x_695_);
if (v___x_696_ == 0)
{
uint8_t v___x_697_; 
v___x_697_ = 7;
return v___x_697_;
}
else
{
uint8_t v___x_698_; 
v___x_698_ = 6;
return v___x_698_;
}
}
else
{
uint8_t v___x_699_; 
v___x_699_ = 5;
return v___x_699_;
}
}
}
else
{
lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_700_ = lean_unsigned_to_nat(1u);
v___x_701_ = lean_nat_dec_le(v_n_648_, v___x_700_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_702_ = lean_unsigned_to_nat(2u);
v___x_703_ = lean_nat_dec_le(v_n_648_, v___x_702_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_704_ = lean_unsigned_to_nat(3u);
v___x_705_ = lean_nat_dec_le(v_n_648_, v___x_704_);
if (v___x_705_ == 0)
{
uint8_t v___x_706_; 
v___x_706_ = 4;
return v___x_706_;
}
else
{
uint8_t v___x_707_; 
v___x_707_ = 3;
return v___x_707_;
}
}
else
{
uint8_t v___x_708_; 
v___x_708_ = 2;
return v___x_708_;
}
}
else
{
lean_object* v___x_709_; uint8_t v___x_710_; 
v___x_709_ = lean_unsigned_to_nat(0u);
v___x_710_ = lean_nat_dec_le(v_n_648_, v___x_709_);
if (v___x_710_ == 0)
{
uint8_t v___x_711_; 
v___x_711_ = 1;
return v___x_711_;
}
else
{
uint8_t v___x_712_; 
v___x_712_ = 0;
return v___x_712_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_ofNat___boxed(lean_object* v_n_713_){
_start:
{
uint8_t v_res_714_; lean_object* v_r_715_; 
v_res_714_ = l_Std_Async_Signal_ofNat(v_n_713_);
lean_dec(v_n_713_);
v_r_715_ = lean_box(v_res_714_);
return v_r_715_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_instDecidableEqSignal(uint8_t v_x_716_, uint8_t v_y_717_){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_718_ = l_Std_Async_Signal_ctorIdx(v_x_716_);
v___x_719_ = l_Std_Async_Signal_ctorIdx(v_y_717_);
v___x_720_ = lean_nat_dec_eq(v___x_718_, v___x_719_);
lean_dec(v___x_719_);
lean_dec(v___x_718_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instDecidableEqSignal___boxed(lean_object* v_x_721_, lean_object* v_y_722_){
_start:
{
uint8_t v_x_13__boxed_723_; uint8_t v_y_14__boxed_724_; uint8_t v_res_725_; lean_object* v_r_726_; 
v_x_13__boxed_723_ = lean_unbox(v_x_721_);
v_y_14__boxed_724_ = lean_unbox(v_y_722_);
v_res_725_ = l_Std_Async_instDecidableEqSignal(v_x_13__boxed_723_, v_y_14__boxed_724_);
v_r_726_ = lean_box(v_res_725_);
return v_r_726_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_instBEqSignal_beq(uint8_t v_x_727_, uint8_t v_y_728_){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_729_ = l_Std_Async_Signal_ctorIdx(v_x_727_);
v___x_730_ = l_Std_Async_Signal_ctorIdx(v_y_728_);
v___x_731_ = lean_nat_dec_eq(v___x_729_, v___x_730_);
lean_dec(v___x_730_);
lean_dec(v___x_729_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instBEqSignal_beq___boxed(lean_object* v_x_732_, lean_object* v_y_733_){
_start:
{
uint8_t v_x_17__boxed_734_; uint8_t v_y_18__boxed_735_; uint8_t v_res_736_; lean_object* v_r_737_; 
v_x_17__boxed_734_ = lean_unbox(v_x_732_);
v_y_18__boxed_735_ = lean_unbox(v_y_733_);
v_res_736_ = l_Std_Async_instBEqSignal_beq(v_x_17__boxed_734_, v_y_18__boxed_735_);
v_r_737_ = lean_box(v_res_736_);
return v_r_737_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0(void){
_start:
{
lean_object* v___x_740_; uint32_t v___x_741_; 
v___x_740_ = lean_unsigned_to_nat(1u);
v___x_741_ = lean_int32_of_nat(v___x_740_);
return v___x_741_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1(void){
_start:
{
lean_object* v___x_742_; uint32_t v___x_743_; 
v___x_742_ = lean_unsigned_to_nat(2u);
v___x_743_ = lean_int32_of_nat(v___x_742_);
return v___x_743_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2(void){
_start:
{
lean_object* v___x_744_; uint32_t v___x_745_; 
v___x_744_ = lean_unsigned_to_nat(3u);
v___x_745_ = lean_int32_of_nat(v___x_744_);
return v___x_745_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3(void){
_start:
{
lean_object* v___x_746_; uint32_t v___x_747_; 
v___x_746_ = lean_unsigned_to_nat(5u);
v___x_747_ = lean_int32_of_nat(v___x_746_);
return v___x_747_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4(void){
_start:
{
lean_object* v___x_748_; uint32_t v___x_749_; 
v___x_748_ = lean_unsigned_to_nat(6u);
v___x_749_ = lean_int32_of_nat(v___x_748_);
return v___x_749_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5(void){
_start:
{
lean_object* v___x_750_; uint32_t v___x_751_; 
v___x_750_ = lean_unsigned_to_nat(10u);
v___x_751_ = lean_int32_of_nat(v___x_750_);
return v___x_751_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6(void){
_start:
{
lean_object* v___x_752_; uint32_t v___x_753_; 
v___x_752_ = lean_unsigned_to_nat(12u);
v___x_753_ = lean_int32_of_nat(v___x_752_);
return v___x_753_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7(void){
_start:
{
lean_object* v___x_754_; uint32_t v___x_755_; 
v___x_754_ = lean_unsigned_to_nat(14u);
v___x_755_ = lean_int32_of_nat(v___x_754_);
return v___x_755_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8(void){
_start:
{
lean_object* v___x_756_; uint32_t v___x_757_; 
v___x_756_ = lean_unsigned_to_nat(15u);
v___x_757_ = lean_int32_of_nat(v___x_756_);
return v___x_757_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9(void){
_start:
{
lean_object* v___x_758_; uint32_t v___x_759_; 
v___x_758_ = lean_unsigned_to_nat(17u);
v___x_759_ = lean_int32_of_nat(v___x_758_);
return v___x_759_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10(void){
_start:
{
lean_object* v___x_760_; uint32_t v___x_761_; 
v___x_760_ = lean_unsigned_to_nat(18u);
v___x_761_ = lean_int32_of_nat(v___x_760_);
return v___x_761_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11(void){
_start:
{
lean_object* v___x_762_; uint32_t v___x_763_; 
v___x_762_ = lean_unsigned_to_nat(20u);
v___x_763_ = lean_int32_of_nat(v___x_762_);
return v___x_763_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12(void){
_start:
{
lean_object* v___x_764_; uint32_t v___x_765_; 
v___x_764_ = lean_unsigned_to_nat(21u);
v___x_765_ = lean_int32_of_nat(v___x_764_);
return v___x_765_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13(void){
_start:
{
lean_object* v___x_766_; uint32_t v___x_767_; 
v___x_766_ = lean_unsigned_to_nat(22u);
v___x_767_ = lean_int32_of_nat(v___x_766_);
return v___x_767_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14(void){
_start:
{
lean_object* v___x_768_; uint32_t v___x_769_; 
v___x_768_ = lean_unsigned_to_nat(23u);
v___x_769_ = lean_int32_of_nat(v___x_768_);
return v___x_769_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15(void){
_start:
{
lean_object* v___x_770_; uint32_t v___x_771_; 
v___x_770_ = lean_unsigned_to_nat(24u);
v___x_771_ = lean_int32_of_nat(v___x_770_);
return v___x_771_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16(void){
_start:
{
lean_object* v___x_772_; uint32_t v___x_773_; 
v___x_772_ = lean_unsigned_to_nat(25u);
v___x_773_ = lean_int32_of_nat(v___x_772_);
return v___x_773_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17(void){
_start:
{
lean_object* v___x_774_; uint32_t v___x_775_; 
v___x_774_ = lean_unsigned_to_nat(26u);
v___x_775_ = lean_int32_of_nat(v___x_774_);
return v___x_775_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18(void){
_start:
{
lean_object* v___x_776_; uint32_t v___x_777_; 
v___x_776_ = lean_unsigned_to_nat(27u);
v___x_777_ = lean_int32_of_nat(v___x_776_);
return v___x_777_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19(void){
_start:
{
lean_object* v___x_778_; uint32_t v___x_779_; 
v___x_778_ = lean_unsigned_to_nat(28u);
v___x_779_ = lean_int32_of_nat(v___x_778_);
return v___x_779_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20(void){
_start:
{
lean_object* v___x_780_; uint32_t v___x_781_; 
v___x_780_ = lean_unsigned_to_nat(29u);
v___x_781_ = lean_int32_of_nat(v___x_780_);
return v___x_781_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21(void){
_start:
{
lean_object* v___x_782_; uint32_t v___x_783_; 
v___x_782_ = lean_unsigned_to_nat(31u);
v___x_783_ = lean_int32_of_nat(v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32(uint8_t v_x_784_){
_start:
{
switch(v_x_784_)
{
case 0:
{
uint32_t v___x_785_; 
v___x_785_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0);
return v___x_785_;
}
case 1:
{
uint32_t v___x_786_; 
v___x_786_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1);
return v___x_786_;
}
case 2:
{
uint32_t v___x_787_; 
v___x_787_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2);
return v___x_787_;
}
case 3:
{
uint32_t v___x_788_; 
v___x_788_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3);
return v___x_788_;
}
case 4:
{
uint32_t v___x_789_; 
v___x_789_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4);
return v___x_789_;
}
case 5:
{
uint32_t v___x_790_; 
v___x_790_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5);
return v___x_790_;
}
case 6:
{
uint32_t v___x_791_; 
v___x_791_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6);
return v___x_791_;
}
case 7:
{
uint32_t v___x_792_; 
v___x_792_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7);
return v___x_792_;
}
case 8:
{
uint32_t v___x_793_; 
v___x_793_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8);
return v___x_793_;
}
case 9:
{
uint32_t v___x_794_; 
v___x_794_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9);
return v___x_794_;
}
case 10:
{
uint32_t v___x_795_; 
v___x_795_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10);
return v___x_795_;
}
case 11:
{
uint32_t v___x_796_; 
v___x_796_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11);
return v___x_796_;
}
case 12:
{
uint32_t v___x_797_; 
v___x_797_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12);
return v___x_797_;
}
case 13:
{
uint32_t v___x_798_; 
v___x_798_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13);
return v___x_798_;
}
case 14:
{
uint32_t v___x_799_; 
v___x_799_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14);
return v___x_799_;
}
case 15:
{
uint32_t v___x_800_; 
v___x_800_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15);
return v___x_800_;
}
case 16:
{
uint32_t v___x_801_; 
v___x_801_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16);
return v___x_801_;
}
case 17:
{
uint32_t v___x_802_; 
v___x_802_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17);
return v___x_802_;
}
case 18:
{
uint32_t v___x_803_; 
v___x_803_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18);
return v___x_803_;
}
case 19:
{
uint32_t v___x_804_; 
v___x_804_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19);
return v___x_804_;
}
case 20:
{
uint32_t v___x_805_; 
v___x_805_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20);
return v___x_805_;
}
default: 
{
uint32_t v___x_806_; 
v___x_806_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21);
return v___x_806_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___boxed(lean_object* v_x_807_){
_start:
{
uint8_t v_x_356__boxed_808_; uint32_t v_res_809_; lean_object* v_r_810_; 
v_x_356__boxed_808_ = lean_unbox(v_x_807_);
v_res_809_ = l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32(v_x_356__boxed_808_);
v_r_810_ = lean_box_uint32(v_res_809_);
return v_r_810_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_mk(uint8_t v_signum_811_, uint8_t v_repeating_812_){
_start:
{
uint32_t v___x_814_; lean_object* v___x_815_; 
v___x_814_ = l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32(v_signum_811_);
v___x_815_ = lean_uv_signal_mk(v___x_814_, v_repeating_812_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_815_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_815_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
v_a_824_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_815_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_815_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_mk___boxed(lean_object* v_signum_832_, lean_object* v_repeating_833_, lean_object* v_a_834_){
_start:
{
uint8_t v_signum_boxed_835_; uint8_t v_repeating_boxed_836_; lean_object* v_res_837_; 
v_signum_boxed_835_ = lean_unbox(v_signum_832_);
v_repeating_boxed_836_ = lean_unbox(v_repeating_833_);
v_res_837_ = l_Std_Async_Signal_Waiter_mk(v_signum_boxed_835_, v_repeating_boxed_836_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_wait___lam__0(lean_object* v___x_838_, lean_object* v_x_839_){
_start:
{
if (lean_obj_tag(v_x_839_) == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = lean_mk_io_user_error(v___x_838_);
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
else
{
lean_object* v_val_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec_ref(v___x_838_);
v_val_842_ = lean_ctor_get(v_x_839_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v_x_839_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v_x_839_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_val_842_);
lean_dec(v_x_839_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_val_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_wait(lean_object* v_s_853_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = lean_uv_signal_next(v_s_853_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_868_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_868_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_868_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_868_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___f_860_; lean_object* v___x_861_; lean_object* v___x_862_; uint8_t v___x_863_; lean_object* v___x_864_; lean_object* v___x_866_; 
v___f_860_ = ((lean_object*)(l_Std_Async_Signal_Waiter_wait___closed__1));
v___x_861_ = lean_io_promise_result_opt(v_a_856_);
lean_dec(v_a_856_);
v___x_862_ = lean_unsigned_to_nat(0u);
v___x_863_ = 1;
v___x_864_ = lean_task_map(v___f_860_, v___x_861_, v___x_862_, v___x_863_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_864_);
v___x_866_ = v___x_858_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
v_a_869_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_855_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_855_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_wait___boxed(lean_object* v_s_877_, lean_object* v_a_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Std_Async_Signal_Waiter_wait(v_s_877_);
lean_dec(v_s_877_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_stop(lean_object* v_s_880_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = lean_uv_signal_stop(v_s_880_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_stop___boxed(lean_object* v_s_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Std_Async_Signal_Waiter_stop(v_s_883_);
lean_dec(v_s_883_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0(lean_object* v_w_888_, lean_object* v_lose_889_){
_start:
{
lean_object* v_finished_891_; lean_object* v_promise_892_; lean_object* v___x_893_; uint8_t v___y_895_; uint8_t v___x_903_; 
v_finished_891_ = lean_ctor_get(v_w_888_, 0);
v_promise_892_ = lean_ctor_get(v_w_888_, 1);
v___x_893_ = lean_st_ref_take(v_finished_891_);
v___x_903_ = lean_unbox(v___x_893_);
lean_dec(v___x_893_);
if (v___x_903_ == 0)
{
uint8_t v___x_904_; 
v___x_904_ = 1;
v___y_895_ = v___x_904_;
goto v___jp_894_;
}
else
{
uint8_t v___x_905_; 
v___x_905_ = 0;
v___y_895_ = v___x_905_;
goto v___jp_894_;
}
v___jp_894_:
{
uint8_t v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_896_ = 1;
v___x_897_ = lean_box(v___x_896_);
v___x_898_ = lean_st_ref_set(v_finished_891_, v___x_897_);
if (v___y_895_ == 0)
{
lean_object* v___x_899_; 
v___x_899_ = lean_apply_1(v_lose_889_, lean_box(0));
return v___x_899_;
}
else
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
lean_dec_ref(v_lose_889_);
v___x_900_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___closed__0));
v___x_901_ = lean_io_promise_resolve(v___x_900_, v_promise_892_);
v___x_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
return v___x_902_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___boxed(lean_object* v_w_906_, lean_object* v_lose_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0(v_w_906_, v_lose_907_);
lean_dec_ref(v_w_906_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__0(lean_object* v_s_910_){
_start:
{
lean_object* v_val_913_; lean_object* v___x_915_; 
v___x_915_ = lean_uv_signal_cancel(v_s_910_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_915_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set_tag(v___x_918_, 1);
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
v_val_913_ = v___x_921_;
goto v___jp_912_;
}
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
v_a_924_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_915_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_915_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set_tag(v___x_926_, 0);
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
v_val_913_ = v___x_929_;
goto v___jp_912_;
}
}
}
v___jp_912_:
{
lean_object* v___x_914_; 
v___x_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_914_, 0, v_val_913_);
return v___x_914_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__0___boxed(lean_object* v_s_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Std_Async_Signal_Waiter_selector___lam__0(v_s_932_);
lean_dec(v_s_932_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__1(lean_object* v_x_939_){
_start:
{
if (lean_obj_tag(v_x_939_) == 0)
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_949_; 
v_a_941_ = lean_ctor_get(v_x_939_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v_x_939_);
if (v_isSharedCheck_949_ == 0)
{
v___x_943_ = v_x_939_;
v_isShared_944_ = v_isSharedCheck_949_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v_x_939_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_949_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_948_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_947_; 
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
return v___x_947_;
}
}
}
else
{
lean_object* v___x_950_; 
lean_dec_ref_known(v_x_939_, 1);
v___x_950_ = ((lean_object*)(l_Std_Async_Signal_Waiter_selector___lam__1___closed__1));
return v___x_950_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__1___boxed(lean_object* v_x_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Std_Async_Signal_Waiter_selector___lam__1(v_x_951_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__2(lean_object* v___f_960_, lean_object* v_s_961_, lean_object* v_x_962_){
_start:
{
if (lean_obj_tag(v_x_962_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_972_; 
lean_dec_ref(v___f_960_);
v_a_964_ = lean_ctor_get(v_x_962_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v_x_962_);
if (v_isSharedCheck_972_ == 0)
{
v___x_966_ = v_x_962_;
v_isShared_967_ = v_isSharedCheck_972_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v_x_962_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_972_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_964_);
v___x_969_ = v_reuseFailAlloc_971_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_970_; 
v___x_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
return v___x_970_;
}
}
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_994_; 
v_a_973_ = lean_ctor_get(v_x_962_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v_x_962_);
if (v_isSharedCheck_994_ == 0)
{
v___x_975_ = v_x_962_;
v_isShared_976_ = v_isSharedCheck_994_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v_x_962_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_994_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v_val_978_; uint8_t v___x_983_; 
v___x_983_ = lean_unbox(v_a_973_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; 
v___x_984_ = lean_uv_signal_cancel(v_s_961_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v___x_987_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_984_, 1);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v_a_985_);
v___x_987_ = v___x_975_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
v_val_978_ = v___x_987_;
goto v___jp_977_;
}
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; 
v_a_989_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_989_);
lean_dec_ref_known(v___x_984_, 1);
if (v_isShared_976_ == 0)
{
lean_ctor_set_tag(v___x_975_, 0);
lean_ctor_set(v___x_975_, 0, v_a_989_);
v___x_991_ = v___x_975_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
v_val_978_ = v___x_991_;
goto v___jp_977_;
}
}
}
else
{
lean_object* v___x_993_; 
lean_del_object(v___x_975_);
lean_dec(v_a_973_);
lean_dec_ref(v___f_960_);
v___x_993_ = ((lean_object*)(l_Std_Async_Signal_Waiter_selector___lam__2___closed__2));
return v___x_993_;
}
v___jp_977_:
{
lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; lean_object* v___x_982_; 
v___x_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_979_, 0, v_val_978_);
v___x_980_ = lean_unsigned_to_nat(0u);
v___x_981_ = lean_unbox(v_a_973_);
lean_dec(v_a_973_);
v___x_982_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_980_, v___x_981_, v___x_979_, v___f_960_);
return v___x_982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__2___boxed(lean_object* v___f_995_, lean_object* v_s_996_, lean_object* v_x_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Std_Async_Signal_Waiter_selector___lam__2(v___f_995_, v_s_996_, v_x_997_);
lean_dec(v_s_996_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__3(lean_object* v_x_1000_){
_start:
{
if (lean_obj_tag(v_x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; 
v_a_1001_ = lean_ctor_get(v_x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v_x_1000_, 1);
v___x_1002_ = lean_task_pure(v_a_1001_);
return v___x_1002_;
}
else
{
lean_object* v_a_1003_; 
v_a_1003_ = lean_ctor_get(v_x_1000_, 0);
lean_inc_ref(v_a_1003_);
lean_dec_ref_known(v_x_1000_, 1);
return v_a_1003_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__5(lean_object* v_s_1004_){
_start:
{
lean_object* v_val_1007_; lean_object* v___x_1009_; 
v___x_1009_ = lean_uv_signal_next(v_s_1004_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1022_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1012_ = v___x_1009_;
v_isShared_1013_ = v_isSharedCheck_1022_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1009_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1022_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___f_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1020_; 
v___f_1014_ = ((lean_object*)(l_Std_Async_Signal_Waiter_wait___closed__1));
v___x_1015_ = lean_io_promise_result_opt(v_a_1010_);
lean_dec(v_a_1010_);
v___x_1016_ = lean_unsigned_to_nat(0u);
v___x_1017_ = 1;
v___x_1018_ = lean_task_map(v___f_1014_, v___x_1015_, v___x_1016_, v___x_1017_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set_tag(v___x_1012_, 1);
lean_ctor_set(v___x_1012_, 0, v___x_1018_);
v___x_1020_ = v___x_1012_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1018_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
v_val_1007_ = v___x_1020_;
goto v___jp_1006_;
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
v_a_1023_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1009_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1009_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
lean_ctor_set_tag(v___x_1025_, 0);
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
v_val_1007_ = v___x_1028_;
goto v___jp_1006_;
}
}
}
v___jp_1006_:
{
lean_object* v___x_1008_; 
v___x_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1008_, 0, v_val_1007_);
return v___x_1008_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__5___boxed(lean_object* v_s_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Std_Async_Signal_Waiter_selector___lam__5(v_s_1031_);
lean_dec(v_s_1031_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__4(lean_object* v___f_1034_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_apply_1(v___f_1034_, lean_box(0));
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__4___boxed(lean_object* v___f_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Std_Async_Signal_Waiter_selector___lam__4(v___f_1037_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__6(lean_object* v___x_1040_, lean_object* v___f_1041_, lean_object* v_x_1042_){
_start:
{
if (lean_obj_tag(v_x_1042_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1052_; 
lean_dec_ref(v___f_1041_);
lean_dec(v___x_1040_);
v_a_1044_ = lean_ctor_get(v_x_1042_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_x_1042_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1046_ = v_x_1042_;
v_isShared_1047_ = v_isSharedCheck_1052_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v_x_1042_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1052_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
return v___x_1050_;
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1069_; 
v_a_1053_ = lean_ctor_get(v_x_1042_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_x_1042_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1055_ = v_x_1042_;
v_isShared_1056_ = v_isSharedCheck_1069_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v_x_1042_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1069_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
uint8_t v___x_1057_; uint8_t v_val_1059_; 
v___x_1057_ = lean_io_get_task_state(v_a_1053_);
lean_dec(v_a_1053_);
if (v___x_1057_ == 2)
{
uint8_t v___x_1067_; 
v___x_1067_ = 1;
v_val_1059_ = v___x_1067_;
goto v___jp_1058_;
}
else
{
uint8_t v___x_1068_; 
v___x_1068_ = 0;
v_val_1059_ = v___x_1068_;
goto v___jp_1058_;
}
v___jp_1058_:
{
lean_object* v___x_1060_; lean_object* v___x_1062_; 
v___x_1060_ = lean_box(v_val_1059_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1060_);
v___x_1062_ = v___x_1055_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
lean_object* v___x_1063_; uint8_t v___x_1064_; lean_object* v___x_1065_; 
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
v___x_1064_ = 0;
v___x_1065_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1040_, v___x_1064_, v___x_1063_, v___f_1041_);
return v___x_1065_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__6___boxed(lean_object* v___x_1070_, lean_object* v___f_1071_, lean_object* v_x_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Std_Async_Signal_Waiter_selector___lam__6(v___x_1070_, v___f_1071_, v_x_1072_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__7(lean_object* v___f_1075_, lean_object* v___x_1076_, lean_object* v___f_1077_, lean_object* v___f_1078_){
_start:
{
lean_object* v___x_1080_; uint8_t v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; lean_object* v___x_1086_; 
lean_inc_n(v___x_1076_, 2);
v___x_1080_ = lean_io_as_task(v___f_1075_, v___x_1076_);
v___x_1081_ = 1;
v___x_1082_ = lean_task_bind(v___x_1080_, v___f_1077_, v___x_1076_, v___x_1081_);
v___x_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
v___x_1085_ = 0;
v___x_1086_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1076_, v___x_1085_, v___x_1084_, v___f_1078_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__7___boxed(lean_object* v___f_1087_, lean_object* v___x_1088_, lean_object* v___f_1089_, lean_object* v___f_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Std_Async_Signal_Waiter_selector___lam__7(v___f_1087_, v___x_1088_, v___f_1089_, v___f_1090_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__8(lean_object* v___x_1093_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__8___boxed(lean_object* v___x_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Std_Async_Signal_Waiter_selector___lam__8(v___x_1096_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__9(lean_object* v_waiter_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v_a_1105_; 
if (lean_obj_tag(v_a_1102_) == 0)
{
lean_object* v_a_1107_; 
v_a_1107_ = lean_ctor_get(v_a_1102_, 0);
lean_inc(v_a_1107_);
lean_dec_ref_known(v_a_1102_, 1);
v_a_1105_ = v_a_1107_;
goto v___jp_1104_;
}
else
{
lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1118_; 
v_isSharedCheck_1118_ = !lean_is_exclusive(v_a_1102_);
if (v_isSharedCheck_1118_ == 0)
{
lean_object* v_unused_1119_; 
v_unused_1119_ = lean_ctor_get(v_a_1102_, 0);
lean_dec(v_unused_1119_);
v___x_1109_ = v_a_1102_;
v_isShared_1110_ = v_isSharedCheck_1118_;
goto v_resetjp_1108_;
}
else
{
lean_dec(v_a_1102_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1118_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___f_1111_; lean_object* v___x_1112_; 
v___f_1111_ = ((lean_object*)(l_Std_Async_Signal_Waiter_selector___lam__9___closed__0));
v___x_1112_ = l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0(v_waiter_1101_, v___f_1111_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1115_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1113_);
lean_dec_ref_known(v___x_1112_, 1);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v_a_1113_);
v___x_1115_ = v___x_1109_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
else
{
lean_object* v_a_1117_; 
lean_del_object(v___x_1109_);
v_a_1117_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1112_, 1);
v_a_1105_ = v_a_1117_;
goto v___jp_1104_;
}
}
}
v___jp_1104_:
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1106_, 0, v_a_1105_);
return v___x_1106_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__9___boxed(lean_object* v_waiter_1120_, lean_object* v_a_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Std_Async_Signal_Waiter_selector___lam__9(v_waiter_1120_, v_a_1121_);
lean_dec_ref(v_waiter_1120_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__10(lean_object* v___f_1126_, lean_object* v___x_1127_, lean_object* v_x_1128_){
_start:
{
if (lean_obj_tag(v_x_1128_) == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1138_; 
lean_dec(v___x_1127_);
lean_dec_ref(v___f_1126_);
v_a_1130_ = lean_ctor_get(v_x_1128_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_x_1128_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1132_ = v_x_1128_;
v_isShared_1133_ = v_isSharedCheck_1138_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v_x_1128_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1138_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
return v___x_1136_;
}
}
}
else
{
lean_object* v_a_1139_; uint8_t v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v_a_1139_ = lean_ctor_get(v_x_1128_, 0);
lean_inc(v_a_1139_);
lean_dec_ref_known(v_x_1128_, 1);
v___x_1140_ = 0;
v___x_1141_ = lean_io_map_task(v___f_1126_, v_a_1139_, v___x_1127_, v___x_1140_);
lean_dec_ref(v___x_1141_);
v___x_1142_ = ((lean_object*)(l_Std_Async_Signal_Waiter_selector___lam__10___closed__0));
return v___x_1142_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__10___boxed(lean_object* v___f_1143_, lean_object* v___x_1144_, lean_object* v_x_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Std_Async_Signal_Waiter_selector___lam__10(v___f_1143_, v___x_1144_, v_x_1145_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__11(lean_object* v___f_1148_, lean_object* v___x_1149_, lean_object* v_waiter_1150_){
_start:
{
lean_object* v___x_1152_; lean_object* v___f_1153_; lean_object* v___f_1154_; uint8_t v___x_1155_; lean_object* v___x_1156_; 
v___x_1152_ = lean_apply_1(v___f_1148_, lean_box(0));
v___f_1153_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__9___boxed), 3, 1);
lean_closure_set(v___f_1153_, 0, v_waiter_1150_);
lean_inc(v___x_1149_);
v___f_1154_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__10___boxed), 4, 2);
lean_closure_set(v___f_1154_, 0, v___f_1153_);
lean_closure_set(v___f_1154_, 1, v___x_1149_);
v___x_1155_ = 0;
v___x_1156_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1149_, v___x_1155_, v___x_1152_, v___f_1154_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__11___boxed(lean_object* v___f_1157_, lean_object* v___x_1158_, lean_object* v_waiter_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Std_Async_Signal_Waiter_selector___lam__11(v___f_1157_, v___x_1158_, v_waiter_1159_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector(lean_object* v_s_1164_){
_start:
{
lean_object* v___f_1165_; lean_object* v___f_1166_; lean_object* v___f_1167_; lean_object* v___f_1168_; lean_object* v___f_1169_; lean_object* v___f_1170_; lean_object* v___x_1171_; lean_object* v___f_1172_; lean_object* v___f_1173_; lean_object* v___f_1174_; lean_object* v___x_1175_; 
lean_inc_n(v_s_1164_, 2);
v___f_1165_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1165_, 0, v_s_1164_);
v___f_1166_ = ((lean_object*)(l_Std_Async_Signal_Waiter_selector___closed__0));
v___f_1167_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1167_, 0, v___f_1166_);
lean_closure_set(v___f_1167_, 1, v_s_1164_);
v___f_1168_ = ((lean_object*)(l_Std_Async_Signal_Waiter_selector___closed__1));
v___f_1169_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__5___boxed), 2, 1);
lean_closure_set(v___f_1169_, 0, v_s_1164_);
lean_inc_ref(v___f_1169_);
v___f_1170_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__4___boxed), 2, 1);
lean_closure_set(v___f_1170_, 0, v___f_1169_);
v___x_1171_ = lean_unsigned_to_nat(0u);
v___f_1172_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__6___boxed), 4, 2);
lean_closure_set(v___f_1172_, 0, v___x_1171_);
lean_closure_set(v___f_1172_, 1, v___f_1167_);
v___f_1173_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__7___boxed), 5, 4);
lean_closure_set(v___f_1173_, 0, v___f_1170_);
lean_closure_set(v___f_1173_, 1, v___x_1171_);
lean_closure_set(v___f_1173_, 2, v___f_1168_);
lean_closure_set(v___f_1173_, 3, v___f_1172_);
v___f_1174_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__11___boxed), 4, 2);
lean_closure_set(v___f_1174_, 0, v___f_1169_);
lean_closure_set(v___f_1174_, 1, v___x_1171_);
v___x_1175_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1175_, 0, v___f_1173_);
lean_ctor_set(v___x_1175_, 1, v___f_1174_);
lean_ctor_set(v___x_1175_, 2, v___f_1165_);
return v___x_1175_;
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
