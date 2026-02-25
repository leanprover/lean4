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
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__48;
static lean_once_cell_t l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___closed__49;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_instReprSignal_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_IO_Async_instReprSignal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_instReprSignal_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_IO_Async_instReprSignal___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Internal_IO_Async_instReprSignal = (const lean_object*)&l_Std_Internal_IO_Async_instReprSignal___closed__0_value;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_IO_Async_Signal_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_ofNat___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_IO_Async_instDecidableEqSignal(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_instDecidableEqSignal___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_IO_Async_instBEqSignal_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_instBEqSignal_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_IO_Async_instBEqSignal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_instBEqSignal_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_IO_Async_instBEqSignal___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_instBEqSignal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Internal_IO_Async_instBEqSignal = (const lean_object*)&l_Std_Internal_IO_Async_instBEqSignal___closed__0_value;
uint32_t lean_int32_of_nat(lean_object*);
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
lean_object* lean_uv_signal_mk(uint32_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_mk(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_mk___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_wait___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_IO_Async_Signal_Waiter_wait___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "the promise linked to the Async Task was dropped"};
static const lean_object* l_Std_Internal_IO_Async_Signal_Waiter_wait___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Signal_Waiter_wait___closed__0_value;
static const lean_closure_object l_Std_Internal_IO_Async_Signal_Waiter_wait___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_Signal_Waiter_wait___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Signal_Waiter_wait___closed__0_value)} };
static const lean_object* l_Std_Internal_IO_Async_Signal_Waiter_wait___closed__1 = (const lean_object*)&l_Std_Internal_IO_Async_Signal_Waiter_wait___closed__1_value;
lean_object* lean_uv_signal_next(lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_wait(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_wait___boxed(lean_object*, lean_object*);
lean_object* lean_uv_signal_stop(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_stop(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_stop___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Signal_Waiter_selector_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Signal_Waiter_selector_spec__0___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Signal_Waiter_selector_spec__0___closed__0_value;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Signal_Waiter_selector_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Signal_Waiter_selector_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_signal_cancel(lean_object*);
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
lean_object* l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__5(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__4___boxed(lean_object*, lean_object*);
uint8_t lean_io_get_task_state(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_IO_Async_Signal_Waiter_selector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Signal_Waiter_selector___closed__0_value;
static const lean_closure_object l_Std_Internal_IO_Async_Signal_Waiter_selector___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__3, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___closed__1 = (const lean_object*)&l_Std_Internal_IO_Async_Signal_Waiter_selector___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_ctorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(5u);
return x_7;
}
case 6:
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(6u);
return x_8;
}
case 7:
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(7u);
return x_9;
}
case 8:
{
lean_object* x_10; 
x_10 = lean_unsigned_to_nat(8u);
return x_10;
}
case 9:
{
lean_object* x_11; 
x_11 = lean_unsigned_to_nat(9u);
return x_11;
}
case 10:
{
lean_object* x_12; 
x_12 = lean_unsigned_to_nat(10u);
return x_12;
}
case 11:
{
lean_object* x_13; 
x_13 = lean_unsigned_to_nat(11u);
return x_13;
}
case 12:
{
lean_object* x_14; 
x_14 = lean_unsigned_to_nat(12u);
return x_14;
}
case 13:
{
lean_object* x_15; 
x_15 = lean_unsigned_to_nat(13u);
return x_15;
}
case 14:
{
lean_object* x_16; 
x_16 = lean_unsigned_to_nat(14u);
return x_16;
}
case 15:
{
lean_object* x_17; 
x_17 = lean_unsigned_to_nat(15u);
return x_17;
}
case 16:
{
lean_object* x_18; 
x_18 = lean_unsigned_to_nat(16u);
return x_18;
}
case 17:
{
lean_object* x_19; 
x_19 = lean_unsigned_to_nat(17u);
return x_19;
}
case 18:
{
lean_object* x_20; 
x_20 = lean_unsigned_to_nat(18u);
return x_20;
}
case 19:
{
lean_object* x_21; 
x_21 = lean_unsigned_to_nat(19u);
return x_21;
}
case 20:
{
lean_object* x_22; 
x_22 = lean_unsigned_to_nat(20u);
return x_22;
}
case 21:
{
lean_object* x_23; 
x_23 = lean_unsigned_to_nat(21u);
return x_23;
}
case 22:
{
lean_object* x_24; 
x_24 = lean_unsigned_to_nat(22u);
return x_24;
}
default: 
{
lean_object* x_25; 
x_25 = lean_unsigned_to_nat(23u);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Internal_IO_Async_Signal_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_Signal_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Internal_IO_Async_Signal_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_Signal_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Std_Internal_IO_Async_Signal_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sighup_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sighup_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_Signal_sighup_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sighup_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sighup_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_Signal_sighup_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigint_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigint_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_Signal_sigint_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigint_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigint_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_Signal_sigint_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigquit_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigquit_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_Signal_sigquit_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigquit_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigquit_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_Signal_sigquit_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigtrap_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigtrap_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_Signal_sigtrap_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigtrap_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigtrap_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_Signal_sigtrap_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigabrt_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigabrt_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_Signal_sigabrt_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigabrt_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigabrt_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_Signal_sigabrt_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigemt_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigemt_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_Signal_sigemt_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigemt_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigemt_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_Signal_sigemt_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigsys_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigsys_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_Signal_sigsys_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigsys_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigsys_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_Signal_sigsys_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigalrm_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigalrm_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_Signal_sigalrm_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigalrm_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigalrm_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_Signal_sigalrm_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigterm_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigterm_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_Signal_sigterm_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigterm_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigterm_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_Signal_sigterm_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigurg_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigurg_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_Signal_sigurg_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigurg_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigurg_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_Signal_sigurg_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigtstp_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigtstp_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_Signal_sigtstp_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigtstp_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigtstp_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_Signal_sigtstp_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigcont_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigcont_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_Signal_sigcont_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigcont_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigcont_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_Signal_sigcont_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigchld_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigchld_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_Signal_sigchld_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigchld_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigchld_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_Signal_sigchld_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigttin_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigttin_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_Signal_sigttin_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigttin_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigttin_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_Signal_sigttin_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigttou_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigttou_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_Signal_sigttou_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigttou_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigttou_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_Signal_sigttou_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigio_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigio_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_Signal_sigio_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigio_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigio_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_Signal_sigio_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigxcpu_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigxcpu_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_Signal_sigxcpu_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigxcpu_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigxcpu_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_Signal_sigxcpu_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigxfsz_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigxfsz_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_Signal_sigxfsz_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigxfsz_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigxfsz_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_Signal_sigxfsz_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigvtalrm_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigvtalrm_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_Signal_sigvtalrm_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigvtalrm_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigvtalrm_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_Signal_sigvtalrm_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigprof_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigprof_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_Signal_sigprof_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigprof_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigprof_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_Signal_sigprof_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigwinch_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigwinch_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_Signal_sigwinch_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigwinch_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigwinch_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_Signal_sigwinch_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_siginfo_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_siginfo_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_Signal_siginfo_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_siginfo_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_siginfo_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_Signal_siginfo_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigusr1_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigusr1_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_Signal_sigusr1_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigusr1_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigusr1_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_Signal_sigusr1_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigusr2_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigusr2_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_Signal_sigusr2_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigusr2_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_sigusr2_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_Signal_sigusr2_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_instReprSignal_repr(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_10; lean_object* x_17; lean_object* x_24; lean_object* x_31; lean_object* x_38; lean_object* x_45; lean_object* x_52; lean_object* x_59; lean_object* x_66; lean_object* x_73; lean_object* x_80; lean_object* x_87; lean_object* x_94; lean_object* x_101; lean_object* x_108; lean_object* x_115; lean_object* x_122; lean_object* x_129; lean_object* x_136; lean_object* x_143; lean_object* x_150; lean_object* x_157; lean_object* x_164; 
switch (x_1) {
case 0:
{
lean_object* x_171; uint8_t x_172; 
x_171 = lean_unsigned_to_nat(1024u);
x_172 = lean_nat_dec_le(x_171, x_2);
if (x_172 == 0)
{
lean_object* x_173; 
x_173 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
x_3 = x_173;
goto block_9;
}
else
{
lean_object* x_174; 
x_174 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
x_3 = x_174;
goto block_9;
}
}
case 1:
{
lean_object* x_175; uint8_t x_176; 
x_175 = lean_unsigned_to_nat(1024u);
x_176 = lean_nat_dec_le(x_175, x_2);
if (x_176 == 0)
{
lean_object* x_177; 
x_177 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
x_10 = x_177;
goto block_16;
}
else
{
lean_object* x_178; 
x_178 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
x_10 = x_178;
goto block_16;
}
}
case 2:
{
lean_object* x_179; uint8_t x_180; 
x_179 = lean_unsigned_to_nat(1024u);
x_180 = lean_nat_dec_le(x_179, x_2);
if (x_180 == 0)
{
lean_object* x_181; 
x_181 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
x_17 = x_181;
goto block_23;
}
else
{
lean_object* x_182; 
x_182 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
x_17 = x_182;
goto block_23;
}
}
case 3:
{
lean_object* x_183; uint8_t x_184; 
x_183 = lean_unsigned_to_nat(1024u);
x_184 = lean_nat_dec_le(x_183, x_2);
if (x_184 == 0)
{
lean_object* x_185; 
x_185 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
x_24 = x_185;
goto block_30;
}
else
{
lean_object* x_186; 
x_186 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
x_24 = x_186;
goto block_30;
}
}
case 4:
{
lean_object* x_187; uint8_t x_188; 
x_187 = lean_unsigned_to_nat(1024u);
x_188 = lean_nat_dec_le(x_187, x_2);
if (x_188 == 0)
{
lean_object* x_189; 
x_189 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
x_31 = x_189;
goto block_37;
}
else
{
lean_object* x_190; 
x_190 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
x_31 = x_190;
goto block_37;
}
}
case 5:
{
lean_object* x_191; uint8_t x_192; 
x_191 = lean_unsigned_to_nat(1024u);
x_192 = lean_nat_dec_le(x_191, x_2);
if (x_192 == 0)
{
lean_object* x_193; 
x_193 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
x_38 = x_193;
goto block_44;
}
else
{
lean_object* x_194; 
x_194 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
x_38 = x_194;
goto block_44;
}
}
case 6:
{
lean_object* x_195; uint8_t x_196; 
x_195 = lean_unsigned_to_nat(1024u);
x_196 = lean_nat_dec_le(x_195, x_2);
if (x_196 == 0)
{
lean_object* x_197; 
x_197 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
x_45 = x_197;
goto block_51;
}
else
{
lean_object* x_198; 
x_198 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
x_45 = x_198;
goto block_51;
}
}
case 7:
{
lean_object* x_199; uint8_t x_200; 
x_199 = lean_unsigned_to_nat(1024u);
x_200 = lean_nat_dec_le(x_199, x_2);
if (x_200 == 0)
{
lean_object* x_201; 
x_201 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
x_52 = x_201;
goto block_58;
}
else
{
lean_object* x_202; 
x_202 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
x_52 = x_202;
goto block_58;
}
}
case 8:
{
lean_object* x_203; uint8_t x_204; 
x_203 = lean_unsigned_to_nat(1024u);
x_204 = lean_nat_dec_le(x_203, x_2);
if (x_204 == 0)
{
lean_object* x_205; 
x_205 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
x_59 = x_205;
goto block_65;
}
else
{
lean_object* x_206; 
x_206 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
x_59 = x_206;
goto block_65;
}
}
case 9:
{
lean_object* x_207; uint8_t x_208; 
x_207 = lean_unsigned_to_nat(1024u);
x_208 = lean_nat_dec_le(x_207, x_2);
if (x_208 == 0)
{
lean_object* x_209; 
x_209 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
x_66 = x_209;
goto block_72;
}
else
{
lean_object* x_210; 
x_210 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
x_66 = x_210;
goto block_72;
}
}
case 10:
{
lean_object* x_211; uint8_t x_212; 
x_211 = lean_unsigned_to_nat(1024u);
x_212 = lean_nat_dec_le(x_211, x_2);
if (x_212 == 0)
{
lean_object* x_213; 
x_213 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
x_73 = x_213;
goto block_79;
}
else
{
lean_object* x_214; 
x_214 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
x_73 = x_214;
goto block_79;
}
}
case 11:
{
lean_object* x_215; uint8_t x_216; 
x_215 = lean_unsigned_to_nat(1024u);
x_216 = lean_nat_dec_le(x_215, x_2);
if (x_216 == 0)
{
lean_object* x_217; 
x_217 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
x_80 = x_217;
goto block_86;
}
else
{
lean_object* x_218; 
x_218 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
x_80 = x_218;
goto block_86;
}
}
case 12:
{
lean_object* x_219; uint8_t x_220; 
x_219 = lean_unsigned_to_nat(1024u);
x_220 = lean_nat_dec_le(x_219, x_2);
if (x_220 == 0)
{
lean_object* x_221; 
x_221 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
x_87 = x_221;
goto block_93;
}
else
{
lean_object* x_222; 
x_222 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
x_87 = x_222;
goto block_93;
}
}
case 13:
{
lean_object* x_223; uint8_t x_224; 
x_223 = lean_unsigned_to_nat(1024u);
x_224 = lean_nat_dec_le(x_223, x_2);
if (x_224 == 0)
{
lean_object* x_225; 
x_225 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
x_94 = x_225;
goto block_100;
}
else
{
lean_object* x_226; 
x_226 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
x_94 = x_226;
goto block_100;
}
}
case 14:
{
lean_object* x_227; uint8_t x_228; 
x_227 = lean_unsigned_to_nat(1024u);
x_228 = lean_nat_dec_le(x_227, x_2);
if (x_228 == 0)
{
lean_object* x_229; 
x_229 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
x_101 = x_229;
goto block_107;
}
else
{
lean_object* x_230; 
x_230 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
x_101 = x_230;
goto block_107;
}
}
case 15:
{
lean_object* x_231; uint8_t x_232; 
x_231 = lean_unsigned_to_nat(1024u);
x_232 = lean_nat_dec_le(x_231, x_2);
if (x_232 == 0)
{
lean_object* x_233; 
x_233 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
x_108 = x_233;
goto block_114;
}
else
{
lean_object* x_234; 
x_234 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
x_108 = x_234;
goto block_114;
}
}
case 16:
{
lean_object* x_235; uint8_t x_236; 
x_235 = lean_unsigned_to_nat(1024u);
x_236 = lean_nat_dec_le(x_235, x_2);
if (x_236 == 0)
{
lean_object* x_237; 
x_237 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
x_115 = x_237;
goto block_121;
}
else
{
lean_object* x_238; 
x_238 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
x_115 = x_238;
goto block_121;
}
}
case 17:
{
lean_object* x_239; uint8_t x_240; 
x_239 = lean_unsigned_to_nat(1024u);
x_240 = lean_nat_dec_le(x_239, x_2);
if (x_240 == 0)
{
lean_object* x_241; 
x_241 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
x_122 = x_241;
goto block_128;
}
else
{
lean_object* x_242; 
x_242 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
x_122 = x_242;
goto block_128;
}
}
case 18:
{
lean_object* x_243; uint8_t x_244; 
x_243 = lean_unsigned_to_nat(1024u);
x_244 = lean_nat_dec_le(x_243, x_2);
if (x_244 == 0)
{
lean_object* x_245; 
x_245 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
x_129 = x_245;
goto block_135;
}
else
{
lean_object* x_246; 
x_246 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
x_129 = x_246;
goto block_135;
}
}
case 19:
{
lean_object* x_247; uint8_t x_248; 
x_247 = lean_unsigned_to_nat(1024u);
x_248 = lean_nat_dec_le(x_247, x_2);
if (x_248 == 0)
{
lean_object* x_249; 
x_249 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
x_136 = x_249;
goto block_142;
}
else
{
lean_object* x_250; 
x_250 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
x_136 = x_250;
goto block_142;
}
}
case 20:
{
lean_object* x_251; uint8_t x_252; 
x_251 = lean_unsigned_to_nat(1024u);
x_252 = lean_nat_dec_le(x_251, x_2);
if (x_252 == 0)
{
lean_object* x_253; 
x_253 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
x_143 = x_253;
goto block_149;
}
else
{
lean_object* x_254; 
x_254 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
x_143 = x_254;
goto block_149;
}
}
case 21:
{
lean_object* x_255; uint8_t x_256; 
x_255 = lean_unsigned_to_nat(1024u);
x_256 = lean_nat_dec_le(x_255, x_2);
if (x_256 == 0)
{
lean_object* x_257; 
x_257 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
x_150 = x_257;
goto block_156;
}
else
{
lean_object* x_258; 
x_258 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
x_150 = x_258;
goto block_156;
}
}
case 22:
{
lean_object* x_259; uint8_t x_260; 
x_259 = lean_unsigned_to_nat(1024u);
x_260 = lean_nat_dec_le(x_259, x_2);
if (x_260 == 0)
{
lean_object* x_261; 
x_261 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
x_157 = x_261;
goto block_163;
}
else
{
lean_object* x_262; 
x_262 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
x_157 = x_262;
goto block_163;
}
}
default: 
{
lean_object* x_263; uint8_t x_264; 
x_263 = lean_unsigned_to_nat(1024u);
x_264 = lean_nat_dec_le(x_263, x_2);
if (x_264 == 0)
{
lean_object* x_265; 
x_265 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__48, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__48_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__48);
x_164 = x_265;
goto block_170;
}
else
{
lean_object* x_266; 
x_266 = lean_obj_once(&l_Std_Internal_IO_Async_instReprSignal_repr___closed__49, &l_Std_Internal_IO_Async_instReprSignal_repr___closed__49_once, _init_l_Std_Internal_IO_Async_instReprSignal_repr___closed__49);
x_164 = x_266;
goto block_170;
}
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__1));
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = 0;
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
block_16:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__3));
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = 0;
x_14 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = l_Repr_addAppParen(x_14, x_2);
return x_15;
}
block_23:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_18 = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__5));
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = 0;
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = l_Repr_addAppParen(x_21, x_2);
return x_22;
}
block_30:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_25 = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__7));
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = 0;
x_28 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = l_Repr_addAppParen(x_28, x_2);
return x_29;
}
block_37:
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_32 = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__9));
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = 0;
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = l_Repr_addAppParen(x_35, x_2);
return x_36;
}
block_44:
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__11));
x_40 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = 0;
x_42 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = l_Repr_addAppParen(x_42, x_2);
return x_43;
}
block_51:
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_46 = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__13));
x_47 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = 0;
x_49 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_48);
x_50 = l_Repr_addAppParen(x_49, x_2);
return x_50;
}
block_58:
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_53 = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__15));
x_54 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = 0;
x_56 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_55);
x_57 = l_Repr_addAppParen(x_56, x_2);
return x_57;
}
block_65:
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; 
x_60 = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__17));
x_61 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = 0;
x_63 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_62);
x_64 = l_Repr_addAppParen(x_63, x_2);
return x_64;
}
block_72:
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_67 = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__19));
x_68 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = 0;
x_70 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*1, x_69);
x_71 = l_Repr_addAppParen(x_70, x_2);
return x_71;
}
block_79:
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; 
x_74 = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__21));
x_75 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = 0;
x_77 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set_uint8(x_77, sizeof(void*)*1, x_76);
x_78 = l_Repr_addAppParen(x_77, x_2);
return x_78;
}
block_86:
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; 
x_81 = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__23));
x_82 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = 0;
x_84 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_83);
x_85 = l_Repr_addAppParen(x_84, x_2);
return x_85;
}
block_93:
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; 
x_88 = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__25));
x_89 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = 0;
x_91 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_90);
x_92 = l_Repr_addAppParen(x_91, x_2);
return x_92;
}
block_100:
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_95 = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__27));
x_96 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = 0;
x_98 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set_uint8(x_98, sizeof(void*)*1, x_97);
x_99 = l_Repr_addAppParen(x_98, x_2);
return x_99;
}
block_107:
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; 
x_102 = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__29));
x_103 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = 0;
x_105 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set_uint8(x_105, sizeof(void*)*1, x_104);
x_106 = l_Repr_addAppParen(x_105, x_2);
return x_106;
}
block_114:
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; 
x_109 = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__31));
x_110 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = 0;
x_112 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set_uint8(x_112, sizeof(void*)*1, x_111);
x_113 = l_Repr_addAppParen(x_112, x_2);
return x_113;
}
block_121:
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; 
x_116 = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__33));
x_117 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = 0;
x_119 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set_uint8(x_119, sizeof(void*)*1, x_118);
x_120 = l_Repr_addAppParen(x_119, x_2);
return x_120;
}
block_128:
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; 
x_123 = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__35));
x_124 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = 0;
x_126 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set_uint8(x_126, sizeof(void*)*1, x_125);
x_127 = l_Repr_addAppParen(x_126, x_2);
return x_127;
}
block_135:
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; 
x_130 = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__37));
x_131 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = 0;
x_133 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set_uint8(x_133, sizeof(void*)*1, x_132);
x_134 = l_Repr_addAppParen(x_133, x_2);
return x_134;
}
block_142:
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; 
x_137 = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__39));
x_138 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = 0;
x_140 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set_uint8(x_140, sizeof(void*)*1, x_139);
x_141 = l_Repr_addAppParen(x_140, x_2);
return x_141;
}
block_149:
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; 
x_144 = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__41));
x_145 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = 0;
x_147 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set_uint8(x_147, sizeof(void*)*1, x_146);
x_148 = l_Repr_addAppParen(x_147, x_2);
return x_148;
}
block_156:
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; 
x_151 = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__43));
x_152 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = 0;
x_154 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set_uint8(x_154, sizeof(void*)*1, x_153);
x_155 = l_Repr_addAppParen(x_154, x_2);
return x_155;
}
block_163:
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; 
x_158 = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__45));
x_159 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = 0;
x_161 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set_uint8(x_161, sizeof(void*)*1, x_160);
x_162 = l_Repr_addAppParen(x_161, x_2);
return x_162;
}
block_170:
{
lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; 
x_165 = ((lean_object*)(l_Std_Internal_IO_Async_instReprSignal_repr___closed__47));
x_166 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_167 = 0;
x_168 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set_uint8(x_168, sizeof(void*)*1, x_167);
x_169 = l_Repr_addAppParen(x_168, x_2);
return x_169;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_instReprSignal_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Std_Internal_IO_Async_instReprSignal_repr(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IO_Async_Signal_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(17u);
x_5 = lean_nat_dec_le(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(20u);
x_7 = lean_nat_dec_le(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(21u);
x_9 = lean_nat_dec_le(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(22u);
x_11 = lean_nat_dec_le(x_1, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 23;
return x_12;
}
else
{
uint8_t x_13; 
x_13 = 22;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 21;
return x_14;
}
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(18u);
x_16 = lean_nat_dec_le(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(19u);
x_18 = lean_nat_dec_le(x_1, x_17);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = 20;
return x_19;
}
else
{
uint8_t x_20; 
x_20 = 19;
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = 18;
return x_21;
}
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_unsigned_to_nat(14u);
x_23 = lean_nat_dec_le(x_1, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_unsigned_to_nat(15u);
x_25 = lean_nat_dec_le(x_1, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_unsigned_to_nat(16u);
x_27 = lean_nat_dec_le(x_1, x_26);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = 17;
return x_28;
}
else
{
uint8_t x_29; 
x_29 = 16;
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = 15;
return x_30;
}
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_unsigned_to_nat(12u);
x_32 = lean_nat_dec_le(x_1, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_unsigned_to_nat(13u);
x_34 = lean_nat_dec_le(x_1, x_33);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = 14;
return x_35;
}
else
{
uint8_t x_36; 
x_36 = 13;
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = 12;
return x_37;
}
}
}
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_unsigned_to_nat(5u);
x_39 = lean_nat_dec_le(x_1, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_unsigned_to_nat(8u);
x_41 = lean_nat_dec_le(x_1, x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_unsigned_to_nat(9u);
x_43 = lean_nat_dec_le(x_1, x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_unsigned_to_nat(10u);
x_45 = lean_nat_dec_le(x_1, x_44);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = 11;
return x_46;
}
else
{
uint8_t x_47; 
x_47 = 10;
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = 9;
return x_48;
}
}
else
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_unsigned_to_nat(6u);
x_50 = lean_nat_dec_le(x_1, x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_unsigned_to_nat(7u);
x_52 = lean_nat_dec_le(x_1, x_51);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = 8;
return x_53;
}
else
{
uint8_t x_54; 
x_54 = 7;
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = 6;
return x_55;
}
}
}
else
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_unsigned_to_nat(2u);
x_57 = lean_nat_dec_le(x_1, x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_unsigned_to_nat(3u);
x_59 = lean_nat_dec_le(x_1, x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_unsigned_to_nat(4u);
x_61 = lean_nat_dec_le(x_1, x_60);
if (x_61 == 0)
{
uint8_t x_62; 
x_62 = 5;
return x_62;
}
else
{
uint8_t x_63; 
x_63 = 4;
return x_63;
}
}
else
{
uint8_t x_64; 
x_64 = 3;
return x_64;
}
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_nat_dec_le(x_1, x_65);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_dec_le(x_1, x_67);
if (x_68 == 0)
{
uint8_t x_69; 
x_69 = 2;
return x_69;
}
else
{
uint8_t x_70; 
x_70 = 1;
return x_70;
}
}
else
{
uint8_t x_71; 
x_71 = 0;
return x_71;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Internal_IO_Async_Signal_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IO_Async_instDecidableEqSignal(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Std_Internal_IO_Async_Signal_ctorIdx(x_1);
x_4 = l_Std_Internal_IO_Async_Signal_ctorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_instDecidableEqSignal___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Std_Internal_IO_Async_instDecidableEqSignal(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IO_Async_instBEqSignal_beq(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Std_Internal_IO_Async_Signal_ctorIdx(x_1);
x_4 = l_Std_Internal_IO_Async_Signal_ctorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_instBEqSignal_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Std_Internal_IO_Async_instBEqSignal_beq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__0(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__1(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__2(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__3(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__4(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__5(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__6(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(12u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__7(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(14u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__8(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(15u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__9(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(16u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__10(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(18u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__11(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(19u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__12(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(20u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__13(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(21u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__14(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(22u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__15(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(23u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__16(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(24u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__17(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(25u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__18(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(26u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__19(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(27u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__20(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(28u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__21(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(29u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__22(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(30u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static uint32_t _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__23(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT uint32_t l_Std_Internal_IO_Async_Signal_toInt32(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
uint32_t x_2; 
x_2 = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__0, &l_Std_Internal_IO_Async_Signal_toInt32___closed__0_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__0);
return x_2;
}
case 1:
{
uint32_t x_3; 
x_3 = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__1, &l_Std_Internal_IO_Async_Signal_toInt32___closed__1_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__1);
return x_3;
}
case 2:
{
uint32_t x_4; 
x_4 = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__2, &l_Std_Internal_IO_Async_Signal_toInt32___closed__2_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__2);
return x_4;
}
case 3:
{
uint32_t x_5; 
x_5 = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__3, &l_Std_Internal_IO_Async_Signal_toInt32___closed__3_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__3);
return x_5;
}
case 4:
{
uint32_t x_6; 
x_6 = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__4, &l_Std_Internal_IO_Async_Signal_toInt32___closed__4_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__4);
return x_6;
}
case 5:
{
uint32_t x_7; 
x_7 = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__5, &l_Std_Internal_IO_Async_Signal_toInt32___closed__5_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__5);
return x_7;
}
case 6:
{
uint32_t x_8; 
x_8 = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__6, &l_Std_Internal_IO_Async_Signal_toInt32___closed__6_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__6);
return x_8;
}
case 7:
{
uint32_t x_9; 
x_9 = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__7, &l_Std_Internal_IO_Async_Signal_toInt32___closed__7_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__7);
return x_9;
}
case 8:
{
uint32_t x_10; 
x_10 = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__8, &l_Std_Internal_IO_Async_Signal_toInt32___closed__8_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__8);
return x_10;
}
case 9:
{
uint32_t x_11; 
x_11 = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__9, &l_Std_Internal_IO_Async_Signal_toInt32___closed__9_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__9);
return x_11;
}
case 10:
{
uint32_t x_12; 
x_12 = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__10, &l_Std_Internal_IO_Async_Signal_toInt32___closed__10_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__10);
return x_12;
}
case 11:
{
uint32_t x_13; 
x_13 = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__11, &l_Std_Internal_IO_Async_Signal_toInt32___closed__11_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__11);
return x_13;
}
case 12:
{
uint32_t x_14; 
x_14 = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__12, &l_Std_Internal_IO_Async_Signal_toInt32___closed__12_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__12);
return x_14;
}
case 13:
{
uint32_t x_15; 
x_15 = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__13, &l_Std_Internal_IO_Async_Signal_toInt32___closed__13_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__13);
return x_15;
}
case 14:
{
uint32_t x_16; 
x_16 = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__14, &l_Std_Internal_IO_Async_Signal_toInt32___closed__14_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__14);
return x_16;
}
case 15:
{
uint32_t x_17; 
x_17 = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__15, &l_Std_Internal_IO_Async_Signal_toInt32___closed__15_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__15);
return x_17;
}
case 16:
{
uint32_t x_18; 
x_18 = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__16, &l_Std_Internal_IO_Async_Signal_toInt32___closed__16_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__16);
return x_18;
}
case 17:
{
uint32_t x_19; 
x_19 = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__17, &l_Std_Internal_IO_Async_Signal_toInt32___closed__17_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__17);
return x_19;
}
case 18:
{
uint32_t x_20; 
x_20 = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__18, &l_Std_Internal_IO_Async_Signal_toInt32___closed__18_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__18);
return x_20;
}
case 19:
{
uint32_t x_21; 
x_21 = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__19, &l_Std_Internal_IO_Async_Signal_toInt32___closed__19_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__19);
return x_21;
}
case 20:
{
uint32_t x_22; 
x_22 = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__20, &l_Std_Internal_IO_Async_Signal_toInt32___closed__20_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__20);
return x_22;
}
case 21:
{
uint32_t x_23; 
x_23 = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__21, &l_Std_Internal_IO_Async_Signal_toInt32___closed__21_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__21);
return x_23;
}
case 22:
{
uint32_t x_24; 
x_24 = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__22, &l_Std_Internal_IO_Async_Signal_toInt32___closed__22_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__22);
return x_24;
}
default: 
{
uint32_t x_25; 
x_25 = lean_uint32_once(&l_Std_Internal_IO_Async_Signal_toInt32___closed__23, &l_Std_Internal_IO_Async_Signal_toInt32___closed__23_once, _init_l_Std_Internal_IO_Async_Signal_toInt32___closed__23);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_toInt32___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Internal_IO_Async_Signal_toInt32(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_mk(uint8_t x_1, uint8_t x_2) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = l_Std_Internal_IO_Async_Signal_toInt32(x_1);
x_5 = lean_uv_signal_mk(x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_mk___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_Signal_Waiter_mk(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_wait___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_io_user_error(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
uint8_t x_5; 
lean_dec_ref(x_1);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_wait(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_signal_next(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = ((lean_object*)(l_Std_Internal_IO_Async_Signal_Waiter_wait___closed__1));
x_7 = lean_io_promise_result_opt(x_5);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = 1;
x_10 = lean_task_map(x_6, x_7, x_8, x_9);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = ((lean_object*)(l_Std_Internal_IO_Async_Signal_Waiter_wait___closed__1));
x_13 = lean_io_promise_result_opt(x_11);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = 1;
x_16 = lean_task_map(x_12, x_13, x_14, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
return x_3;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
lean_dec(x_3);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_wait___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Signal_Waiter_wait(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_stop(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_signal_stop(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_stop___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Signal_Waiter_stop(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Signal_Waiter_selector_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_16; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_st_ref_take(x_4);
x_16 = lean_unbox(x_6);
lean_dec(x_6);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = 1;
x_7 = x_17;
goto block_15;
}
else
{
uint8_t x_18; 
x_18 = 0;
x_7 = x_18;
goto block_15;
}
block_15:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = 1;
x_9 = lean_box(x_8);
x_10 = lean_st_ref_set(x_4, x_9);
if (x_7 == 0)
{
lean_object* x_11; 
x_11 = lean_apply_1(x_2, lean_box(0));
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_2);
x_12 = ((lean_object*)(l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Signal_Waiter_selector_spec__0___closed__0));
x_13 = lean_io_promise_resolve(x_12, x_5);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Signal_Waiter_selector_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Signal_Waiter_selector_spec__0(x_1, x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_7; 
x_7 = lean_uv_signal_cancel(x_1);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
x_3 = x_7;
x_4 = lean_box(0);
goto block_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_3 = x_10;
x_4 = lean_box(0);
goto block_6;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_ctor_set_tag(x_7, 0);
x_3 = x_7;
x_4 = lean_box(0);
goto block_6;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_3 = x_13;
x_4 = lean_box(0);
goto block_6;
}
}
block_6:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__0(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; 
lean_dec_ref(x_1);
x_8 = ((lean_object*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__1___closed__1));
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__1(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
lean_dec_ref(x_1);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_19; 
x_11 = lean_ctor_get(x_3, 0);
x_19 = lean_unbox(x_11);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_uv_signal_cancel(x_2);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
lean_ctor_set(x_3, 0, x_21);
x_12 = x_3;
x_13 = lean_box(0);
goto block_18;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec_ref(x_20);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_22);
x_12 = x_3;
x_13 = lean_box(0);
goto block_18;
}
}
else
{
lean_object* x_23; 
lean_free_object(x_3);
lean_dec(x_11);
lean_dec_ref(x_1);
x_23 = ((lean_object*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__2___closed__2));
return x_23;
}
block_18:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_unbox(x_11);
lean_dec(x_11);
x_17 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_15, x_16, x_14, x_1);
return x_17;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_32; 
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
lean_dec(x_3);
x_32 = lean_unbox(x_24);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_uv_signal_cancel(x_2);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_25 = x_35;
x_26 = lean_box(0);
goto block_31;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec_ref(x_33);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_25 = x_37;
x_26 = lean_box(0);
goto block_31;
}
}
else
{
lean_object* x_38; 
lean_dec(x_24);
lean_dec_ref(x_1);
x_38 = ((lean_object*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__2___closed__2));
return x_38;
}
block_31:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_25);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_unbox(x_24);
lean_dec(x_24);
x_30 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_28, x_29, x_27, x_1);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__3(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = lean_task_pure(x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__5(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_7; 
x_7 = lean_uv_signal_next(x_1);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = ((lean_object*)(l_Std_Internal_IO_Async_Signal_Waiter_wait___closed__1));
x_11 = lean_io_promise_result_opt(x_9);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = 1;
x_14 = lean_task_map(x_10, x_11, x_12, x_13);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_14);
x_3 = x_7;
x_4 = lean_box(0);
goto block_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
x_16 = ((lean_object*)(l_Std_Internal_IO_Async_Signal_Waiter_wait___closed__1));
x_17 = lean_io_promise_result_opt(x_15);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = 1;
x_20 = lean_task_map(x_16, x_17, x_18, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_3 = x_21;
x_4 = lean_box(0);
goto block_6;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_7);
if (x_22 == 0)
{
lean_ctor_set_tag(x_7, 0);
x_3 = x_7;
x_4 = lean_box(0);
goto block_6;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_7, 0);
lean_inc(x_23);
lean_dec(x_7);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_3 = x_24;
x_4 = lean_box(0);
goto block_6;
}
}
block_6:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__5(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__4(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__4(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_11 = x_3;
} else {
 lean_dec_ref(x_3);
 x_11 = lean_box(0);
}
x_12 = lean_io_get_task_state(x_10);
lean_dec(x_10);
if (x_12 == 2)
{
uint8_t x_20; 
x_20 = 1;
x_13 = x_20;
goto block_19;
}
else
{
uint8_t x_21; 
x_21 = 0;
x_13 = x_21;
goto block_19;
}
block_19:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_box(x_13);
if (lean_is_scalar(x_11)) {
 x_15 = lean_alloc_ctor(1, 1, 0);
} else {
 x_15 = x_11;
}
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = 0;
x_18 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_1, x_17, x_16, x_2);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__6(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
lean_inc(x_2);
x_6 = lean_io_as_task(x_1, x_2);
x_7 = 1;
lean_inc(x_2);
x_8 = lean_task_bind(x_6, x_3, x_2, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = 0;
x_12 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_2, x_11, x_10, x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__7(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__8(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__8(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__9(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec_ref(x_2);
x_4 = x_8;
x_5 = lean_box(0);
goto block_7;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_dec(x_10);
x_11 = ((lean_object*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__9___closed__0));
x_12 = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Signal_Waiter_selector_spec__0(x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
else
{
lean_object* x_14; 
lean_free_object(x_2);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec_ref(x_12);
x_4 = x_14;
x_5 = lean_box(0);
goto block_7;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_15 = ((lean_object*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__9___closed__0));
x_16 = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Signal_Waiter_selector_spec__0(x_1, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec_ref(x_16);
x_4 = x_19;
x_5 = lean_box(0);
goto block_7;
}
}
}
block_7:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__9(x_1, x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec_ref(x_3);
x_11 = 0;
x_12 = lean_io_map_task(x_1, x_10, x_2, x_11);
lean_dec_ref(x_12);
x_13 = ((lean_object*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__10___closed__0));
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__10(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_apply_1(x_1, lean_box(0));
x_6 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__9___boxed), 3, 1);
lean_closure_set(x_6, 0, x_3);
lean_inc(x_2);
x_7 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__10___boxed), 4, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_2);
x_8 = 0;
x_9 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_2, x_8, x_5, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__11(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Signal_Waiter_selector(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = ((lean_object*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___closed__0));
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__2___boxed), 4, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
x_5 = ((lean_object*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___closed__1));
x_6 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__5___boxed), 2, 1);
lean_closure_set(x_6, 0, x_1);
lean_inc_ref(x_6);
x_7 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__4___boxed), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__6___boxed), 4, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_4);
x_10 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__7___boxed), 5, 4);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_8);
lean_closure_set(x_10, 2, x_5);
lean_closure_set(x_10, 3, x_9);
x_11 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Signal_Waiter_selector___lam__11___boxed), 4, 2);
lean_closure_set(x_11, 0, x_6);
lean_closure_set(x_11, 1, x_8);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_2);
return x_12;
}
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
