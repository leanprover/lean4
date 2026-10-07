// Lean compiler output
// Module: Lake.Util.MainM
// Imports: public import Lake.Util.Log public import Lake.Util.Exit
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
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lake_OutStream_get(lean_object*);
uint8_t l_Lake_AnsiMode_isEnabled(lean_object*, uint8_t);
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lake_OutStream_logEntry(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_instMonadBaseIO;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lake_Log_maxLv(lean_object*);
uint8_t l_Lake_instOrdLogLevel_ord(uint8_t, uint8_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadMainM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadMainM___aux__1___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadMainM___closed__0 = (const lean_object*)&l_Lake_instMonadMainM___closed__0_value;
static const lean_closure_object l_Lake_instMonadMainM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadMainM___aux__3___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadMainM___closed__1 = (const lean_object*)&l_Lake_instMonadMainM___closed__1_value;
static const lean_ctor_object l_Lake_instMonadMainM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instMonadMainM___closed__0_value),((lean_object*)&l_Lake_instMonadMainM___closed__1_value)}};
static const lean_object* l_Lake_instMonadMainM___closed__2 = (const lean_object*)&l_Lake_instMonadMainM___closed__2_value;
static const lean_closure_object l_Lake_instMonadMainM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadMainM___aux__5___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadMainM___closed__3 = (const lean_object*)&l_Lake_instMonadMainM___closed__3_value;
static const lean_closure_object l_Lake_instMonadMainM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadMainM___aux__7___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadMainM___closed__4 = (const lean_object*)&l_Lake_instMonadMainM___closed__4_value;
static const lean_closure_object l_Lake_instMonadMainM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadMainM___aux__9___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadMainM___closed__5 = (const lean_object*)&l_Lake_instMonadMainM___closed__5_value;
static const lean_closure_object l_Lake_instMonadMainM___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadMainM___aux__11___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadMainM___closed__6 = (const lean_object*)&l_Lake_instMonadMainM___closed__6_value;
static const lean_ctor_object l_Lake_instMonadMainM___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instMonadMainM___closed__2_value),((lean_object*)&l_Lake_instMonadMainM___closed__3_value),((lean_object*)&l_Lake_instMonadMainM___closed__4_value),((lean_object*)&l_Lake_instMonadMainM___closed__5_value),((lean_object*)&l_Lake_instMonadMainM___closed__6_value)}};
static const lean_object* l_Lake_instMonadMainM___closed__7 = (const lean_object*)&l_Lake_instMonadMainM___closed__7_value;
static const lean_closure_object l_Lake_instMonadMainM___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadMainM___aux__13___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadMainM___closed__8 = (const lean_object*)&l_Lake_instMonadMainM___closed__8_value;
static const lean_ctor_object l_Lake_instMonadMainM___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instMonadMainM___closed__7_value),((lean_object*)&l_Lake_instMonadMainM___closed__8_value)}};
static const lean_object* l_Lake_instMonadMainM___closed__9 = (const lean_object*)&l_Lake_instMonadMainM___closed__9_value;
LEAN_EXPORT const lean_object* l_Lake_instMonadMainM = (const lean_object*)&l_Lake_instMonadMainM___closed__9_value;
LEAN_EXPORT lean_object* l_Lake_instMonadFinallyMainM___aux__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadFinallyMainM___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadFinallyMainM___aux__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadFinallyMainM___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadFinallyMainM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadFinallyMainM___aux__1___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadFinallyMainM___closed__0 = (const lean_object*)&l_Lake_instMonadFinallyMainM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instMonadFinallyMainM = (const lean_object*)&l_Lake_instMonadFinallyMainM___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instMonadLiftBaseIOMainM___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftBaseIOMainM___aux__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftBaseIOMainM___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftBaseIOMainM___aux__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadLiftBaseIOMainM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadLiftBaseIOMainM___aux__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadLiftBaseIOMainM___closed__0 = (const lean_object*)&l_Lake_instMonadLiftBaseIOMainM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instMonadLiftBaseIOMainM = (const lean_object*)&l_Lake_instMonadLiftBaseIOMainM___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_MainM_mk___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_mk___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_mk(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_mk___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_toEIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_toEIO___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_toEIO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_toEIO___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_toBaseIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_toBaseIO___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_toBaseIO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_toBaseIO___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lake_MainM_run___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_run___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lake_MainM_run(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_run___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_exit___redArg(uint32_t);
LEAN_EXPORT lean_object* l_Lake_MainM_exit___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_exit(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_MainM_exit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_MainM_instMonadExit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_MainM_exit___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_MainM_instMonadExit___closed__0 = (const lean_object*)&l_Lake_MainM_instMonadExit___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_MainM_instMonadExit = (const lean_object*)&l_Lake_MainM_instMonadExit___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchExit___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchExit___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchExit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchExit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchError___redArg___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchError___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchError___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchError(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchError___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_failure___redArg___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_MainM_failure___redArg();
LEAN_EXPORT lean_object* l_Lake_MainM_failure___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_failure(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_failure___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_orElse___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_orElse___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_orElse(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_orElse___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_MainM_failure___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__0 = (const lean_object*)&l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__0_value;
static const lean_closure_object l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_MainM_orElse___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__1 = (const lean_object*)&l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative;
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadLog___lam__0(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadLog___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_MainM_instMonadLog___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_MainM_instMonadLog___lam__0___boxed, .m_arity = 5, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_MainM_instMonadLog___closed__0 = (const lean_object*)&l_Lake_MainM_instMonadLog___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_MainM_instMonadLog = (const lean_object*)&l_Lake_MainM_instMonadLog___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_MainM_error___redArg(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_MainM_error___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_error(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_MainM_error___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadError___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadError___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_MainM_instMonadError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_MainM_instMonadError___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_MainM_instMonadError___closed__0 = (const lean_object*)&l_Lake_MainM_instMonadError___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_MainM_instMonadError = (const lean_object*)&l_Lake_MainM_instMonadError___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadLiftIO___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadLiftIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_MainM_instMonadLiftIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_MainM_instMonadLiftIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_MainM_instMonadLiftIO___closed__0 = (const lean_object*)&l_Lake_MainM_instMonadLiftIO___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_MainM_instMonadLiftIO = (const lean_object*)&l_Lake_MainM_instMonadLiftIO___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO___redArg___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_MainM_runLogIO___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_MainM_runLogIO___redArg___closed__0 = (const lean_object*)&l_Lake_MainM_runLogIO___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_liftLogIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_liftLogIO___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_liftLogIO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_liftLogIO___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_MainM_instMonadLiftLogIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_MainM_liftLogIO___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_MainM_instMonadLiftLogIO___closed__0 = (const lean_object*)&l_Lake_MainM_instMonadLiftLogIO___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_MainM_instMonadLiftLogIO = (const lean_object*)&l_Lake_MainM_instMonadLiftLogIO___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO___redArg___lam__0(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO___redArg___lam__0(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_MainM_instMonadLiftLoggerIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_MainM_liftLoggerIO___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_MainM_instMonadLiftLoggerIO___closed__0 = (const lean_object*)&l_Lake_MainM_instMonadLiftLoggerIO___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_MainM_instMonadLiftLoggerIO = (const lean_object*)&l_Lake_MainM_instMonadLiftLoggerIO___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__1___redArg(lean_object* v_a_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_1(v_a_2_, lean_box(0));
if (lean_obj_tag(v___x_4_) == 0)
{
lean_object* v_a_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_13_; 
v_a_5_ = lean_ctor_get(v___x_4_, 0);
v_isSharedCheck_13_ = !lean_is_exclusive(v___x_4_);
if (v_isSharedCheck_13_ == 0)
{
v___x_7_ = v___x_4_;
v_isShared_8_ = v_isSharedCheck_13_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_a_5_);
lean_dec(v___x_4_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_13_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_9_; lean_object* v___x_11_; 
v___x_9_ = lean_apply_1(v_a_1_, v_a_5_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 0, v___x_9_);
v___x_11_ = v___x_7_;
goto v_reusejp_10_;
}
else
{
lean_object* v_reuseFailAlloc_12_; 
v_reuseFailAlloc_12_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_12_, 0, v___x_9_);
v___x_11_ = v_reuseFailAlloc_12_;
goto v_reusejp_10_;
}
v_reusejp_10_:
{
return v___x_11_;
}
}
}
else
{
lean_object* v_a_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_21_; 
lean_dec(v_a_1_);
v_a_14_ = lean_ctor_get(v___x_4_, 0);
v_isSharedCheck_21_ = !lean_is_exclusive(v___x_4_);
if (v_isSharedCheck_21_ == 0)
{
v___x_16_ = v___x_4_;
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_a_14_);
lean_dec(v___x_4_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_19_; 
if (v_isShared_17_ == 0)
{
v___x_19_ = v___x_16_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v_a_14_);
v___x_19_ = v_reuseFailAlloc_20_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
return v___x_19_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__1___redArg___boxed(lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lake_instMonadMainM___aux__1___redArg(v_a_22_, v_a_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__1(lean_object* v_00_u03b1_26_, lean_object* v_00_u03b2_27_, lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_apply_1(v_a_29_, lean_box(0));
if (lean_obj_tag(v___x_31_) == 0)
{
lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_40_; 
v_a_32_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_40_ == 0)
{
v___x_34_ = v___x_31_;
v_isShared_35_ = v_isSharedCheck_40_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_31_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_40_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_36_; lean_object* v___x_38_; 
v___x_36_ = lean_apply_1(v_a_28_, v_a_32_);
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 0, v___x_36_);
v___x_38_ = v___x_34_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_36_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
else
{
lean_object* v_a_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_48_; 
lean_dec(v_a_28_);
v_a_41_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_48_ == 0)
{
v___x_43_ = v___x_31_;
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_a_41_);
lean_dec(v___x_31_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_46_; 
if (v_isShared_44_ == 0)
{
v___x_46_ = v___x_43_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_a_41_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__1___boxed(lean_object* v_00_u03b1_49_, lean_object* v_00_u03b2_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lake_instMonadMainM___aux__1(v_00_u03b1_49_, v_00_u03b2_50_, v_a_51_, v_a_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__3___redArg(lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lean_apply_1(v_a_56_, lean_box(0));
if (lean_obj_tag(v___x_58_) == 0)
{
lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_65_; 
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_65_ == 0)
{
lean_object* v_unused_66_; 
v_unused_66_ = lean_ctor_get(v___x_58_, 0);
lean_dec(v_unused_66_);
v___x_60_ = v___x_58_;
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
else
{
lean_dec(v___x_58_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_63_; 
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 0, v_a_55_);
v___x_63_ = v___x_60_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_a_55_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
else
{
lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_74_; 
lean_dec(v_a_55_);
v_a_67_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_74_ == 0)
{
v___x_69_ = v___x_58_;
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v___x_58_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_72_; 
if (v_isShared_70_ == 0)
{
v___x_72_ = v___x_69_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_a_67_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__3___redArg___boxed(lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lake_instMonadMainM___aux__3___redArg(v_a_75_, v_a_76_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__3(lean_object* v_00_u03b1_79_, lean_object* v_00_u03b2_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lean_apply_1(v_a_82_, lean_box(0));
if (lean_obj_tag(v___x_84_) == 0)
{
lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_91_; 
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_91_ == 0)
{
lean_object* v_unused_92_; 
v_unused_92_ = lean_ctor_get(v___x_84_, 0);
lean_dec(v_unused_92_);
v___x_86_ = v___x_84_;
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
else
{
lean_dec(v___x_84_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_89_; 
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 0, v_a_81_);
v___x_89_ = v___x_86_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_a_81_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
else
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_100_; 
lean_dec(v_a_81_);
v_a_93_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_100_ == 0)
{
v___x_95_ = v___x_84_;
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_84_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_a_93_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__3___boxed(lean_object* v_00_u03b1_101_, lean_object* v_00_u03b2_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lake_instMonadMainM___aux__3(v_00_u03b1_101_, v_00_u03b2_102_, v_a_103_, v_a_104_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__5___redArg(lean_object* v_a_107_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_109_, 0, v_a_107_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__5___redArg___boxed(lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lake_instMonadMainM___aux__5___redArg(v_a_110_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__5(lean_object* v_00_u03b1_113_, lean_object* v_a_114_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v_a_114_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__5___boxed(lean_object* v_00_u03b1_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lake_instMonadMainM___aux__5(v_00_u03b1_117_, v_a_118_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__7___redArg(lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = lean_apply_1(v_a_121_, lean_box(0));
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_a_125_);
lean_dec_ref_known(v___x_124_, 1);
v___x_126_ = lean_box(0);
v___x_127_ = lean_apply_2(v_a_122_, v___x_126_, lean_box(0));
if (lean_obj_tag(v___x_127_) == 0)
{
lean_object* v_a_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_136_; 
v_a_128_ = lean_ctor_get(v___x_127_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_127_);
if (v_isSharedCheck_136_ == 0)
{
v___x_130_ = v___x_127_;
v_isShared_131_ = v_isSharedCheck_136_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_a_128_);
lean_dec(v___x_127_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_136_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_132_ = lean_apply_1(v_a_125_, v_a_128_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 0, v___x_132_);
v___x_134_ = v___x_130_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
else
{
lean_object* v_a_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_144_; 
lean_dec(v_a_125_);
v_a_137_ = lean_ctor_get(v___x_127_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_127_);
if (v_isSharedCheck_144_ == 0)
{
v___x_139_ = v___x_127_;
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_a_137_);
lean_dec(v___x_127_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_140_ == 0)
{
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_a_137_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
else
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
lean_dec_ref(v_a_122_);
v_a_145_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v___x_124_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_124_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__7___redArg___boxed(lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lake_instMonadMainM___aux__7___redArg(v_a_153_, v_a_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__7(lean_object* v_00_u03b1_157_, lean_object* v_00_u03b2_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = lean_apply_1(v_a_159_, lean_box(0));
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v_a_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v_a_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_a_163_);
lean_dec_ref_known(v___x_162_, 1);
v___x_164_ = lean_box(0);
v___x_165_ = lean_apply_2(v_a_160_, v___x_164_, lean_box(0));
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v_a_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_174_; 
v_a_166_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_174_ == 0)
{
v___x_168_ = v___x_165_;
v_isShared_169_ = v_isSharedCheck_174_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_a_166_);
lean_dec(v___x_165_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_174_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_170_ = lean_apply_1(v_a_163_, v_a_166_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 0, v___x_170_);
v___x_172_ = v___x_168_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_170_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
else
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_182_; 
lean_dec(v_a_163_);
v_a_175_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_182_ == 0)
{
v___x_177_ = v___x_165_;
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_165_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
if (v_isShared_178_ == 0)
{
v___x_180_ = v___x_177_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_a_175_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
else
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_190_; 
lean_dec_ref(v_a_160_);
v_a_183_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_190_ == 0)
{
v___x_185_ = v___x_162_;
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_162_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_a_183_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__7___boxed(lean_object* v_00_u03b1_191_, lean_object* v_00_u03b2_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lake_instMonadMainM___aux__7(v_00_u03b1_191_, v_00_u03b2_192_, v_a_193_, v_a_194_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__9___redArg(lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_apply_1(v_a_197_, lean_box(0));
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_a_201_);
lean_dec_ref_known(v___x_200_, 1);
v___x_202_ = lean_box(0);
v___x_203_ = lean_apply_2(v_a_198_, v___x_202_, lean_box(0));
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_210_ == 0)
{
lean_object* v_unused_211_; 
v_unused_211_ = lean_ctor_get(v___x_203_, 0);
lean_dec(v_unused_211_);
v___x_205_ = v___x_203_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_dec(v___x_203_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 0, v_a_201_);
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_201_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
else
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_219_; 
lean_dec(v_a_201_);
v_a_212_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_219_ == 0)
{
v___x_214_ = v___x_203_;
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_203_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_a_212_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
else
{
lean_dec_ref(v_a_198_);
return v___x_200_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__9___redArg___boxed(lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lake_instMonadMainM___aux__9___redArg(v_a_220_, v_a_221_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__9(lean_object* v_00_u03b1_224_, lean_object* v_00_u03b2_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = lean_apply_1(v_a_226_, lean_box(0));
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_a_230_);
lean_dec_ref_known(v___x_229_, 1);
v___x_231_ = lean_box(0);
v___x_232_ = lean_apply_2(v_a_227_, v___x_231_, lean_box(0));
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_239_ == 0)
{
lean_object* v_unused_240_; 
v_unused_240_ = lean_ctor_get(v___x_232_, 0);
lean_dec(v_unused_240_);
v___x_234_ = v___x_232_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_dec(v___x_232_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v_a_230_);
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_230_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
else
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_248_; 
lean_dec(v_a_230_);
v_a_241_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_248_ == 0)
{
v___x_243_ = v___x_232_;
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_232_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_244_ == 0)
{
v___x_246_ = v___x_243_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_a_241_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
else
{
lean_dec_ref(v_a_227_);
return v___x_229_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__9___boxed(lean_object* v_00_u03b1_249_, lean_object* v_00_u03b2_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lake_instMonadMainM___aux__9(v_00_u03b1_249_, v_00_u03b2_250_, v_a_251_, v_a_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__11___redArg(lean_object* v_a_255_, lean_object* v_a_256_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = lean_apply_1(v_a_255_, lean_box(0));
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec_ref_known(v___x_258_, 1);
v___x_259_ = lean_box(0);
v___x_260_ = lean_apply_2(v_a_256_, v___x_259_, lean_box(0));
return v___x_260_;
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
lean_dec_ref(v_a_256_);
v_a_261_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_258_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_258_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__11___redArg___boxed(lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lake_instMonadMainM___aux__11___redArg(v_a_269_, v_a_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__11(lean_object* v_00_u03b1_273_, lean_object* v_00_u03b2_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = lean_apply_1(v_a_275_, lean_box(0));
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; 
lean_dec_ref_known(v___x_278_, 1);
v___x_279_ = lean_box(0);
v___x_280_ = lean_apply_2(v_a_276_, v___x_279_, lean_box(0));
return v___x_280_;
}
else
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
lean_dec_ref(v_a_276_);
v_a_281_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_288_ == 0)
{
v___x_283_ = v___x_278_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_278_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_a_281_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__11___boxed(lean_object* v_00_u03b1_289_, lean_object* v_00_u03b2_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lake_instMonadMainM___aux__11(v_00_u03b1_289_, v_00_u03b2_290_, v_a_291_, v_a_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__13___redArg(lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = lean_apply_1(v_a_295_, lean_box(0));
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v_a_299_; lean_object* v___x_300_; 
v_a_299_ = lean_ctor_get(v___x_298_, 0);
lean_inc(v_a_299_);
lean_dec_ref_known(v___x_298_, 1);
v___x_300_ = lean_apply_2(v_a_296_, v_a_299_, lean_box(0));
return v___x_300_;
}
else
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
lean_dec_ref(v_a_296_);
v_a_301_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_308_ == 0)
{
v___x_303_ = v___x_298_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_298_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_301_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__13___redArg___boxed(lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lake_instMonadMainM___aux__13___redArg(v_a_309_, v_a_310_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__13(lean_object* v_00_u03b1_313_, lean_object* v_00_u03b2_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = lean_apply_1(v_a_315_, lean_box(0));
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; lean_object* v___x_320_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_a_319_);
lean_dec_ref_known(v___x_318_, 1);
v___x_320_ = lean_apply_2(v_a_316_, v_a_319_, lean_box(0));
return v___x_320_;
}
else
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
lean_dec_ref(v_a_316_);
v_a_321_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_318_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_318_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__13___boxed(lean_object* v_00_u03b1_329_, lean_object* v_00_u03b2_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lake_instMonadMainM___aux__13(v_00_u03b1_329_, v_00_u03b2_330_, v_a_331_, v_a_332_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadFinallyMainM___aux__1___redArg(lean_object* v_x_355_, lean_object* v_f_356_){
_start:
{
lean_object* v_r_358_; 
v_r_358_ = lean_apply_1(v_x_355_, lean_box(0));
if (lean_obj_tag(v_r_358_) == 0)
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_384_; 
v_a_359_ = lean_ctor_get(v_r_358_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v_r_358_);
if (v_isSharedCheck_384_ == 0)
{
v___x_361_ = v_r_358_;
v_isShared_362_ = v_isSharedCheck_384_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v_r_358_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_384_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
lean_inc(v_a_359_);
if (v_isShared_362_ == 0)
{
lean_ctor_set_tag(v___x_361_, 1);
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_383_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_365_; 
v___x_365_ = lean_apply_2(v_f_356_, v___x_364_, lean_box(0));
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_374_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_374_ == 0)
{
v___x_368_ = v___x_365_;
v_isShared_369_ = v_isSharedCheck_374_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_374_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_370_, 0, v_a_359_);
lean_ctor_set(v___x_370_, 1, v_a_366_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_370_);
v___x_372_ = v___x_368_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_dec(v_a_359_);
v_a_375_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_365_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_365_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v_a_385_ = lean_ctor_get(v_r_358_, 0);
lean_inc(v_a_385_);
lean_dec_ref_known(v_r_358_, 1);
v___x_386_ = lean_box(0);
v___x_387_ = lean_apply_2(v_f_356_, v___x_386_, lean_box(0));
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_394_ == 0)
{
lean_object* v_unused_395_; 
v_unused_395_ = lean_ctor_get(v___x_387_, 0);
lean_dec(v_unused_395_);
v___x_389_ = v___x_387_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_dec(v___x_387_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
lean_ctor_set_tag(v___x_389_, 1);
lean_ctor_set(v___x_389_, 0, v_a_385_);
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_385_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
else
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
lean_dec(v_a_385_);
v_a_396_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_387_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_387_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadFinallyMainM___aux__1___redArg___boxed(lean_object* v_x_404_, lean_object* v_f_405_, lean_object* v_a_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lake_instMonadFinallyMainM___aux__1___redArg(v_x_404_, v_f_405_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadFinallyMainM___aux__1(lean_object* v_00_u03b1_408_, lean_object* v_00_u03b2_409_, lean_object* v_x_410_, lean_object* v_f_411_){
_start:
{
lean_object* v_r_413_; 
v_r_413_ = lean_apply_1(v_x_410_, lean_box(0));
if (lean_obj_tag(v_r_413_) == 0)
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_439_; 
v_a_414_ = lean_ctor_get(v_r_413_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v_r_413_);
if (v_isSharedCheck_439_ == 0)
{
v___x_416_ = v_r_413_;
v_isShared_417_ = v_isSharedCheck_439_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v_r_413_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_439_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
lean_inc(v_a_414_);
if (v_isShared_417_ == 0)
{
lean_ctor_set_tag(v___x_416_, 1);
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_438_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
lean_object* v___x_420_; 
v___x_420_ = lean_apply_2(v_f_411_, v___x_419_, lean_box(0));
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_429_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_429_ == 0)
{
v___x_423_ = v___x_420_;
v_isShared_424_ = v_isSharedCheck_429_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_429_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v_a_414_);
lean_ctor_set(v___x_425_, 1, v_a_421_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_425_);
v___x_427_ = v___x_423_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_dec(v_a_414_);
v_a_430_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_420_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_420_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
}
else
{
lean_object* v_a_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v_a_440_ = lean_ctor_get(v_r_413_, 0);
lean_inc(v_a_440_);
lean_dec_ref_known(v_r_413_, 1);
v___x_441_ = lean_box(0);
v___x_442_ = lean_apply_2(v_f_411_, v___x_441_, lean_box(0));
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_449_ == 0)
{
lean_object* v_unused_450_; 
v_unused_450_ = lean_ctor_get(v___x_442_, 0);
lean_dec(v_unused_450_);
v___x_444_ = v___x_442_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_dec(v___x_442_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
lean_ctor_set_tag(v___x_444_, 1);
lean_ctor_set(v___x_444_, 0, v_a_440_);
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_440_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec(v_a_440_);
v_a_451_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_442_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_442_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadFinallyMainM___aux__1___boxed(lean_object* v_00_u03b1_459_, lean_object* v_00_u03b2_460_, lean_object* v_x_461_, lean_object* v_f_462_, lean_object* v_a_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lake_instMonadFinallyMainM___aux__1(v_00_u03b1_459_, v_00_u03b2_460_, v_x_461_, v_f_462_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftBaseIOMainM___aux__1___redArg(lean_object* v_act_467_){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = lean_apply_1(v_act_467_, lean_box(0));
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftBaseIOMainM___aux__1___redArg___boxed(lean_object* v_act_471_, lean_object* v_a_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lake_instMonadLiftBaseIOMainM___aux__1___redArg(v_act_471_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftBaseIOMainM___aux__1(lean_object* v_00_u03b1_474_, lean_object* v_act_475_){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_apply_1(v_act_475_, lean_box(0));
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftBaseIOMainM___aux__1___boxed(lean_object* v_00_u03b1_479_, lean_object* v_act_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lake_instMonadLiftBaseIOMainM___aux__1(v_00_u03b1_479_, v_act_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_mk___redArg(lean_object* v_x_485_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = lean_apply_1(v_x_485_, lean_box(0));
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_mk___redArg___boxed(lean_object* v_x_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lake_MainM_mk___redArg(v_x_488_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_mk(lean_object* v_00_u03b1_491_, lean_object* v_x_492_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = lean_apply_1(v_x_492_, lean_box(0));
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_mk___boxed(lean_object* v_00_u03b1_495_, lean_object* v_x_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lake_MainM_mk(v_00_u03b1_495_, v_x_496_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_toEIO___redArg(lean_object* v_self_499_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = lean_apply_1(v_self_499_, lean_box(0));
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_toEIO___redArg___boxed(lean_object* v_self_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lake_MainM_toEIO___redArg(v_self_502_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_toEIO(lean_object* v_00_u03b1_505_, lean_object* v_self_506_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = lean_apply_1(v_self_506_, lean_box(0));
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_toEIO___boxed(lean_object* v_00_u03b1_509_, lean_object* v_self_510_, lean_object* v_a_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lake_MainM_toEIO(v_00_u03b1_509_, v_self_510_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_toBaseIO___redArg(lean_object* v_self_513_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = lean_apply_1(v_self_513_, lean_box(0));
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_515_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_515_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
lean_ctor_set_tag(v___x_518_, 1);
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
v_a_524_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_515_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_515_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
lean_ctor_set_tag(v___x_526_, 0);
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_toBaseIO___redArg___boxed(lean_object* v_self_532_, lean_object* v_a_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lake_MainM_toBaseIO___redArg(v_self_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_toBaseIO(lean_object* v_00_u03b1_535_, lean_object* v_self_536_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = lean_apply_1(v_self_536_, lean_box(0));
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
lean_ctor_set_tag(v___x_541_, 1);
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
v_a_547_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_538_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_538_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
lean_ctor_set_tag(v___x_549_, 0);
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_toBaseIO___boxed(lean_object* v_00_u03b1_555_, lean_object* v_self_556_, lean_object* v_a_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lake_MainM_toBaseIO(v_00_u03b1_555_, v_self_556_);
return v_res_558_;
}
}
LEAN_EXPORT uint32_t l_Lake_MainM_run___redArg(lean_object* v_self_559_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = lean_apply_1(v_self_559_, lean_box(0));
if (lean_obj_tag(v___x_561_) == 0)
{
uint32_t v___x_562_; 
lean_dec_ref_known(v___x_561_, 1);
v___x_562_ = 0;
return v___x_562_;
}
else
{
lean_object* v_a_563_; uint32_t v___x_564_; 
v_a_563_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_a_563_);
lean_dec_ref_known(v___x_561_, 1);
v___x_564_ = lean_unbox_uint32(v_a_563_);
lean_dec(v_a_563_);
return v___x_564_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_run___redArg___boxed(lean_object* v_self_565_, lean_object* v_a_566_){
_start:
{
uint32_t v_res_567_; lean_object* v_r_568_; 
v_res_567_ = l_Lake_MainM_run___redArg(v_self_565_);
v_r_568_ = lean_box_uint32(v_res_567_);
return v_r_568_;
}
}
LEAN_EXPORT uint32_t l_Lake_MainM_run(lean_object* v_00_u03b1_569_, lean_object* v_self_570_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = lean_apply_1(v_self_570_, lean_box(0));
if (lean_obj_tag(v___x_572_) == 0)
{
uint32_t v___x_573_; 
lean_dec_ref_known(v___x_572_, 1);
v___x_573_ = 0;
return v___x_573_;
}
else
{
lean_object* v_a_574_; uint32_t v___x_575_; 
v_a_574_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_574_);
lean_dec_ref_known(v___x_572_, 1);
v___x_575_ = lean_unbox_uint32(v_a_574_);
lean_dec(v_a_574_);
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_run___boxed(lean_object* v_00_u03b1_576_, lean_object* v_self_577_, lean_object* v_a_578_){
_start:
{
uint32_t v_res_579_; lean_object* v_r_580_; 
v_res_579_ = l_Lake_MainM_run(v_00_u03b1_576_, v_self_577_);
v_r_580_ = lean_box_uint32(v_res_579_);
return v_r_580_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_exit___redArg(uint32_t v_rc_581_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = lean_box_uint32(v_rc_581_);
v___x_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_exit___redArg___boxed(lean_object* v_rc_585_, lean_object* v_a_586_){
_start:
{
uint32_t v_rc_boxed_587_; lean_object* v_res_588_; 
v_rc_boxed_587_ = lean_unbox_uint32(v_rc_585_);
lean_dec(v_rc_585_);
v_res_588_ = l_Lake_MainM_exit___redArg(v_rc_boxed_587_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_exit(lean_object* v_00_u03b1_589_, uint32_t v_rc_590_){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_box_uint32(v_rc_590_);
v___x_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_exit___boxed(lean_object* v_00_u03b1_594_, lean_object* v_rc_595_, lean_object* v_a_596_){
_start:
{
uint32_t v_rc_boxed_597_; lean_object* v_res_598_; 
v_rc_boxed_597_ = lean_unbox_uint32(v_rc_595_);
lean_dec(v_rc_595_);
v_res_598_ = l_Lake_MainM_exit(v_00_u03b1_594_, v_rc_boxed_597_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchExit___redArg(lean_object* v_f_601_, lean_object* v_self_602_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = lean_apply_1(v_self_602_, lean_box(0));
if (lean_obj_tag(v___x_604_) == 0)
{
lean_dec_ref(v_f_601_);
return v___x_604_;
}
else
{
lean_object* v_a_605_; lean_object* v___x_606_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___x_604_, 1);
v___x_606_ = lean_apply_2(v_f_601_, v_a_605_, lean_box(0));
return v___x_606_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchExit___redArg___boxed(lean_object* v_f_607_, lean_object* v_self_608_, lean_object* v_a_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lake_MainM_tryCatchExit___redArg(v_f_607_, v_self_608_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchExit(lean_object* v_00_u03b1_611_, lean_object* v_f_612_, lean_object* v_self_613_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = lean_apply_1(v_self_613_, lean_box(0));
if (lean_obj_tag(v___x_615_) == 0)
{
lean_dec_ref(v_f_612_);
return v___x_615_;
}
else
{
lean_object* v_a_616_; lean_object* v___x_617_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_616_);
lean_dec_ref_known(v___x_615_, 1);
v___x_617_ = lean_apply_2(v_f_612_, v_a_616_, lean_box(0));
return v___x_617_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchExit___boxed(lean_object* v_00_u03b1_618_, lean_object* v_f_619_, lean_object* v_self_620_, lean_object* v_a_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lake_MainM_tryCatchExit(v_00_u03b1_618_, v_f_619_, v_self_620_);
return v_res_622_;
}
}
static lean_object* _init_l_Lake_MainM_tryCatchError___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_623_; lean_object* v___x_624_; 
v___x_623_ = 0;
v___x_624_ = lean_box_uint32(v___x_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchError___redArg(lean_object* v_f_625_, lean_object* v_self_626_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = lean_apply_1(v_self_626_, lean_box(0));
if (lean_obj_tag(v___x_628_) == 0)
{
lean_dec_ref(v_f_625_);
return v___x_628_;
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_641_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_641_ == 0)
{
v___x_631_ = v___x_628_;
v_isShared_632_ = v_isSharedCheck_641_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_628_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_641_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
uint32_t v___x_633_; uint32_t v___x_634_; uint8_t v___x_635_; 
v___x_633_ = 0;
v___x_634_ = lean_unbox_uint32(v_a_629_);
v___x_635_ = lean_uint32_dec_eq(v___x_634_, v___x_633_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; 
lean_del_object(v___x_631_);
v___x_636_ = lean_apply_2(v_f_625_, v_a_629_, lean_box(0));
return v___x_636_;
}
else
{
lean_object* v___x_637_; lean_object* v___x_639_; 
lean_dec(v_a_629_);
lean_dec_ref(v_f_625_);
v___x_637_ = l_Lake_MainM_tryCatchError___redArg___boxed__const__1;
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v___x_637_);
v___x_639_ = v___x_631_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchError___redArg___boxed(lean_object* v_f_642_, lean_object* v_self_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lake_MainM_tryCatchError___redArg(v_f_642_, v_self_643_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchError(lean_object* v_00_u03b1_646_, lean_object* v_f_647_, lean_object* v_self_648_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = lean_apply_1(v_self_648_, lean_box(0));
if (lean_obj_tag(v___x_650_) == 0)
{
lean_dec_ref(v_f_647_);
return v___x_650_;
}
else
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_663_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_663_ == 0)
{
v___x_653_ = v___x_650_;
v_isShared_654_ = v_isSharedCheck_663_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_650_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_663_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
uint32_t v___x_655_; uint32_t v___x_656_; uint8_t v___x_657_; 
v___x_655_ = 0;
v___x_656_ = lean_unbox_uint32(v_a_651_);
v___x_657_ = lean_uint32_dec_eq(v___x_656_, v___x_655_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
lean_del_object(v___x_653_);
v___x_658_ = lean_apply_2(v_f_647_, v_a_651_, lean_box(0));
return v___x_658_;
}
else
{
lean_object* v___x_659_; lean_object* v___x_661_; 
lean_dec(v_a_651_);
lean_dec_ref(v_f_647_);
v___x_659_ = l_Lake_MainM_tryCatchError___redArg___boxed__const__1;
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 0, v___x_659_);
v___x_661_ = v___x_653_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchError___boxed(lean_object* v_00_u03b1_664_, lean_object* v_f_665_, lean_object* v_self_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lake_MainM_tryCatchError(v_00_u03b1_664_, v_f_665_, v_self_666_);
return v_res_668_;
}
}
static lean_object* _init_l_Lake_MainM_failure___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_669_; lean_object* v___x_670_; 
v___x_669_ = 1;
v___x_670_ = lean_box_uint32(v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_failure___redArg(){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = l_Lake_MainM_failure___redArg___boxed__const__1;
v___x_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_failure___redArg___boxed(lean_object* v_a_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lake_MainM_failure___redArg();
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_failure(lean_object* v_00_u03b1_676_){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = l_Lake_MainM_failure___redArg___boxed__const__1;
v___x_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_failure___boxed(lean_object* v_00_u03b1_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lake_MainM_failure(v_00_u03b1_680_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_orElse___redArg(lean_object* v_self_683_, lean_object* v_other_684_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = lean_apply_1(v_self_683_, lean_box(0));
if (lean_obj_tag(v___x_686_) == 0)
{
lean_dec_ref(v_other_684_);
return v___x_686_;
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_700_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_700_ == 0)
{
v___x_689_ = v___x_686_;
v_isShared_690_ = v_isSharedCheck_700_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_686_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_700_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
uint32_t v___x_691_; uint32_t v___x_692_; uint8_t v___x_693_; 
v___x_691_ = 0;
v___x_692_ = lean_unbox_uint32(v_a_687_);
lean_dec(v_a_687_);
v___x_693_ = lean_uint32_dec_eq(v___x_692_, v___x_691_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_695_; 
lean_del_object(v___x_689_);
v___x_694_ = lean_box(0);
v___x_695_ = lean_apply_2(v_other_684_, v___x_694_, lean_box(0));
return v___x_695_;
}
else
{
lean_object* v___x_696_; lean_object* v___x_698_; 
lean_dec_ref(v_other_684_);
v___x_696_ = l_Lake_MainM_tryCatchError___redArg___boxed__const__1;
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_696_);
v___x_698_ = v___x_689_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_orElse___redArg___boxed(lean_object* v_self_701_, lean_object* v_other_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lake_MainM_orElse___redArg(v_self_701_, v_other_702_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_orElse(lean_object* v_00_u03b1_705_, lean_object* v_self_706_, lean_object* v_other_707_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = lean_apply_1(v_self_706_, lean_box(0));
if (lean_obj_tag(v___x_709_) == 0)
{
lean_dec_ref(v_other_707_);
return v___x_709_;
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_723_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_723_ == 0)
{
v___x_712_ = v___x_709_;
v_isShared_713_ = v_isSharedCheck_723_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_709_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_723_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
uint32_t v___x_714_; uint32_t v___x_715_; uint8_t v___x_716_; 
v___x_714_ = 0;
v___x_715_ = lean_unbox_uint32(v_a_710_);
lean_dec(v_a_710_);
v___x_716_ = lean_uint32_dec_eq(v___x_715_, v___x_714_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; lean_object* v___x_718_; 
lean_del_object(v___x_712_);
v___x_717_ = lean_box(0);
v___x_718_ = lean_apply_2(v_other_707_, v___x_717_, lean_box(0));
return v___x_718_;
}
else
{
lean_object* v___x_719_; lean_object* v___x_721_; 
lean_dec_ref(v_other_707_);
v___x_719_ = l_Lake_MainM_tryCatchError___redArg___boxed__const__1;
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_719_);
v___x_721_ = v___x_712_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_orElse___boxed(lean_object* v_00_u03b1_724_, lean_object* v_self_725_, lean_object* v_other_726_, lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lake_MainM_orElse(v_00_u03b1_724_, v_self_725_, v_other_726_);
return v_res_728_;
}
}
static lean_object* _init_l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative(void){
_start:
{
lean_object* v___x_731_; lean_object* v_toApplicative_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_731_ = ((lean_object*)(l_Lake_instMonadMainM));
v_toApplicative_732_ = lean_ctor_get(v___x_731_, 0);
v___x_733_ = ((lean_object*)(l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__0));
v___x_734_ = ((lean_object*)(l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__1));
lean_inc_ref(v_toApplicative_732_);
v___x_735_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_735_, 0, v_toApplicative_732_);
lean_ctor_set(v___x_735_, 1, v___x_733_);
lean_ctor_set(v___x_735_, 2, v___x_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadLog___lam__0(lean_object* v___x_736_, uint8_t v___x_737_, uint8_t v___x_738_, lean_object* v_e_739_){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = l_Lake_OutStream_logEntry(v___x_736_, v_e_739_, v___x_737_, v___x_738_);
v___x_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadLog___lam__0___boxed(lean_object* v___x_743_, lean_object* v___x_744_, lean_object* v___x_745_, lean_object* v_e_746_, lean_object* v___y_747_){
_start:
{
uint8_t v___x_37__boxed_748_; uint8_t v___x_38__boxed_749_; lean_object* v_res_750_; 
v___x_37__boxed_748_ = lean_unbox(v___x_744_);
v___x_38__boxed_749_ = lean_unbox(v___x_745_);
v_res_750_ = l_Lake_MainM_instMonadLog___lam__0(v___x_743_, v___x_37__boxed_748_, v___x_38__boxed_749_, v_e_746_);
lean_dec_ref(v_e_746_);
lean_dec(v___x_743_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_error___redArg(lean_object* v_msg_758_, uint32_t v_rc_759_){
_start:
{
uint8_t v___x_761_; uint8_t v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_761_ = 1;
v___x_762_ = 0;
v___x_763_ = lean_box(1);
v___x_764_ = 3;
v___x_765_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_765_, 0, v_msg_758_);
lean_ctor_set_uint8(v___x_765_, sizeof(void*)*1, v___x_764_);
v___x_766_ = l_Lake_OutStream_logEntry(v___x_763_, v___x_765_, v___x_761_, v___x_762_);
lean_dec_ref_known(v___x_765_, 1);
v___x_767_ = lean_box_uint32(v_rc_759_);
v___x_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_error___redArg___boxed(lean_object* v_msg_769_, lean_object* v_rc_770_, lean_object* v_a_771_){
_start:
{
uint32_t v_rc_boxed_772_; lean_object* v_res_773_; 
v_rc_boxed_772_ = lean_unbox_uint32(v_rc_770_);
lean_dec(v_rc_770_);
v_res_773_ = l_Lake_MainM_error___redArg(v_msg_769_, v_rc_boxed_772_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_error(lean_object* v_00_u03b1_774_, lean_object* v_msg_775_, uint32_t v_rc_776_){
_start:
{
uint8_t v___x_778_; uint8_t v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_778_ = 1;
v___x_779_ = 0;
v___x_780_ = lean_box(1);
v___x_781_ = 3;
v___x_782_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_782_, 0, v_msg_775_);
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*1, v___x_781_);
v___x_783_ = l_Lake_OutStream_logEntry(v___x_780_, v___x_782_, v___x_778_, v___x_779_);
lean_dec_ref_known(v___x_782_, 1);
v___x_784_ = lean_box_uint32(v_rc_776_);
v___x_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_error___boxed(lean_object* v_00_u03b1_786_, lean_object* v_msg_787_, lean_object* v_rc_788_, lean_object* v_a_789_){
_start:
{
uint32_t v_rc_boxed_790_; lean_object* v_res_791_; 
v_rc_boxed_790_ = lean_unbox_uint32(v_rc_788_);
lean_dec(v_rc_788_);
v_res_791_ = l_Lake_MainM_error(v_00_u03b1_786_, v_msg_787_, v_rc_boxed_790_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadError___lam__0(lean_object* v_00_u03b1_792_, lean_object* v_msg_793_){
_start:
{
uint8_t v___x_795_; uint8_t v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_795_ = 1;
v___x_796_ = 0;
v___x_797_ = lean_box(1);
v___x_798_ = 3;
v___x_799_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_799_, 0, v_msg_793_);
lean_ctor_set_uint8(v___x_799_, sizeof(void*)*1, v___x_798_);
v___x_800_ = l_Lake_OutStream_logEntry(v___x_797_, v___x_799_, v___x_795_, v___x_796_);
lean_dec_ref_known(v___x_799_, 1);
v___x_801_ = l_Lake_MainM_failure___redArg___boxed__const__1;
v___x_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadError___lam__0___boxed(lean_object* v_00_u03b1_803_, lean_object* v_msg_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lake_MainM_instMonadError___lam__0(v_00_u03b1_803_, v_msg_804_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadLiftIO___lam__0(lean_object* v_00_u03b1_809_, lean_object* v___y_810_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = lean_apply_1(v___y_810_, lean_box(0));
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_812_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_836_; 
v_a_821_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_836_ == 0)
{
v___x_823_ = v___x_812_;
v_isShared_824_ = v_isSharedCheck_836_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_812_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_836_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; uint8_t v___x_826_; uint8_t v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_825_ = lean_io_error_to_string(v_a_821_);
v___x_826_ = 1;
v___x_827_ = 0;
v___x_828_ = lean_box(1);
v___x_829_ = 3;
v___x_830_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_830_, 0, v___x_825_);
lean_ctor_set_uint8(v___x_830_, sizeof(void*)*1, v___x_829_);
v___x_831_ = l_Lake_OutStream_logEntry(v___x_828_, v___x_830_, v___x_826_, v___x_827_);
lean_dec_ref_known(v___x_830_, 1);
v___x_832_ = l_Lake_MainM_failure___redArg___boxed__const__1;
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v___x_832_);
v___x_834_ = v___x_823_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadLiftIO___lam__0___boxed(lean_object* v_00_u03b1_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lake_MainM_instMonadLiftIO___lam__0(v_00_u03b1_837_, v___y_838_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO___redArg___lam__0(lean_object* v_val_843_, uint8_t v___y_844_, uint8_t v_val_845_, lean_object* v_x_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lake_logToStream(v___y_847_, v_val_843_, v___y_844_, v_val_845_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO___redArg___lam__0___boxed(lean_object* v_val_850_, lean_object* v___y_851_, lean_object* v_val_852_, lean_object* v_x_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
uint8_t v___y_383__boxed_856_; uint8_t v_val_384__boxed_857_; lean_object* v_res_858_; 
v___y_383__boxed_856_ = lean_unbox(v___y_851_);
v_val_384__boxed_857_ = lean_unbox(v_val_852_);
v_res_858_ = l_Lake_MainM_runLogIO___redArg___lam__0(v_val_850_, v___y_383__boxed_856_, v_val_384__boxed_857_, v_x_853_, v___y_854_);
lean_dec_ref(v___y_854_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO___redArg(lean_object* v_x_861_, lean_object* v_cfg_862_){
_start:
{
uint8_t v___y_868_; lean_object* v___y_869_; lean_object* v___x_878_; uint8_t v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; uint8_t v___y_883_; lean_object* v___y_900_; lean_object* v___y_901_; uint8_t v___y_902_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_878_ = l_instMonadBaseIO;
v___x_904_ = ((lean_object*)(l_Lake_MainM_runLogIO___redArg___closed__0));
v___x_905_ = lean_apply_2(v_x_861_, v___x_904_, lean_box(0));
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v_a_907_; uint8_t v_failLv_908_; uint8_t v_outLv_909_; lean_object* v___x_910_; uint8_t v___x_911_; uint8_t v___x_912_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_a_906_);
v_a_907_ = lean_ctor_get(v___x_905_, 1);
lean_inc(v_a_907_);
lean_dec_ref_known(v___x_905_, 2);
v_failLv_908_ = lean_ctor_get_uint8(v_cfg_862_, sizeof(void*)*1);
v_outLv_909_ = lean_ctor_get_uint8(v_cfg_862_, sizeof(void*)*1 + 1);
v___x_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_910_, 0, v_a_906_);
v___x_911_ = l_Lake_Log_maxLv(v_a_907_);
v___x_912_ = l_Lake_instOrdLogLevel_ord(v_failLv_908_, v___x_911_);
if (v___x_912_ == 2)
{
uint8_t v___x_913_; 
v___x_913_ = 0;
v___y_880_ = v___x_913_;
v___y_881_ = v_a_907_;
v___y_882_ = v___x_910_;
v___y_883_ = v_outLv_909_;
goto v___jp_879_;
}
else
{
uint8_t v___x_914_; 
v___x_914_ = 1;
v___y_900_ = v_a_907_;
v___y_901_ = v___x_910_;
v___y_902_ = v___x_914_;
goto v___jp_899_;
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v_a_915_ = lean_ctor_get(v___x_905_, 1);
lean_inc(v_a_915_);
lean_dec_ref_known(v___x_905_, 2);
v___x_916_ = lean_box(0);
v___x_917_ = 1;
v___y_900_ = v_a_915_;
v___y_901_ = v___x_916_;
v___y_902_ = v___x_917_;
goto v___jp_899_;
}
v___jp_864_:
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = l_Lake_MainM_failure___redArg___boxed__const__1;
v___x_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
return v___x_866_;
}
v___jp_867_:
{
if (v___y_868_ == 0)
{
if (lean_obj_tag(v___y_869_) == 0)
{
goto v___jp_864_;
}
else
{
lean_object* v_val_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
v_val_870_ = lean_ctor_get(v___y_869_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___y_869_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___y_869_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_val_870_);
lean_dec(v___y_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
lean_ctor_set_tag(v___x_872_, 0);
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_val_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
else
{
lean_dec(v___y_869_);
goto v___jp_864_;
}
}
v___jp_879_:
{
uint8_t v_ansiMode_884_; lean_object* v_out_885_; lean_object* v___x_886_; uint8_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
v_ansiMode_884_ = lean_ctor_get_uint8(v_cfg_862_, sizeof(void*)*1 + 2);
v_out_885_ = lean_ctor_get(v_cfg_862_, 0);
v___x_886_ = l_Lake_OutStream_get(v_out_885_);
lean_inc_ref(v___x_886_);
v___x_887_ = l_Lake_AnsiMode_isEnabled(v___x_886_, v_ansiMode_884_);
v___x_888_ = lean_unsigned_to_nat(0u);
v___x_889_ = lean_array_get_size(v___y_881_);
v___x_890_ = lean_nat_dec_lt(v___x_888_, v___x_889_);
if (v___x_890_ == 0)
{
lean_dec_ref(v___x_886_);
lean_dec_ref(v___y_881_);
v___y_868_ = v___y_880_;
v___y_869_ = v___y_882_;
goto v___jp_867_;
}
else
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___f_893_; lean_object* v___x_894_; size_t v___x_895_; size_t v___x_896_; lean_object* v___x_130__overap_897_; lean_object* v___x_898_; 
v___x_891_ = lean_box(v___y_883_);
v___x_892_ = lean_box(v___x_887_);
v___f_893_ = lean_alloc_closure((void*)(l_Lake_MainM_runLogIO___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_893_, 0, v___x_886_);
lean_closure_set(v___f_893_, 1, v___x_891_);
lean_closure_set(v___f_893_, 2, v___x_892_);
v___x_894_ = lean_box(0);
v___x_895_ = ((size_t)0ULL);
v___x_896_ = lean_usize_of_nat(v___x_889_);
v___x_130__overap_897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_878_, v___f_893_, v___y_881_, v___x_895_, v___x_896_, v___x_894_);
v___x_898_ = lean_apply_1(v___x_130__overap_897_, lean_box(0));
v___y_868_ = v___y_880_;
v___y_869_ = v___y_882_;
goto v___jp_867_;
}
}
v___jp_899_:
{
uint8_t v___x_903_; 
v___x_903_ = 0;
v___y_880_ = v___y_902_;
v___y_881_ = v___y_900_;
v___y_882_ = v___y_901_;
v___y_883_ = v___x_903_;
goto v___jp_879_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO___redArg___boxed(lean_object* v_x_918_, lean_object* v_cfg_919_, lean_object* v_a_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lake_MainM_runLogIO___redArg(v_x_918_, v_cfg_919_);
lean_dec_ref(v_cfg_919_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO(lean_object* v_00_u03b1_922_, lean_object* v_x_923_, lean_object* v_cfg_924_){
_start:
{
uint8_t v___y_930_; lean_object* v___y_931_; lean_object* v___x_940_; uint8_t v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; uint8_t v___y_945_; lean_object* v___y_962_; lean_object* v___y_963_; uint8_t v___y_964_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_940_ = l_instMonadBaseIO;
v___x_966_ = ((lean_object*)(l_Lake_MainM_runLogIO___redArg___closed__0));
v___x_967_ = lean_apply_2(v_x_923_, v___x_966_, lean_box(0));
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v_a_969_; uint8_t v_failLv_970_; uint8_t v_outLv_971_; lean_object* v___x_972_; uint8_t v___x_973_; uint8_t v___x_974_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
v_a_969_ = lean_ctor_get(v___x_967_, 1);
lean_inc(v_a_969_);
lean_dec_ref_known(v___x_967_, 2);
v_failLv_970_ = lean_ctor_get_uint8(v_cfg_924_, sizeof(void*)*1);
v_outLv_971_ = lean_ctor_get_uint8(v_cfg_924_, sizeof(void*)*1 + 1);
v___x_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_972_, 0, v_a_968_);
v___x_973_ = l_Lake_Log_maxLv(v_a_969_);
v___x_974_ = l_Lake_instOrdLogLevel_ord(v_failLv_970_, v___x_973_);
if (v___x_974_ == 2)
{
uint8_t v___x_975_; 
v___x_975_ = 0;
v___y_942_ = v___x_975_;
v___y_943_ = v_a_969_;
v___y_944_ = v___x_972_;
v___y_945_ = v_outLv_971_;
goto v___jp_941_;
}
else
{
uint8_t v___x_976_; 
v___x_976_ = 1;
v___y_962_ = v_a_969_;
v___y_963_ = v___x_972_;
v___y_964_ = v___x_976_;
goto v___jp_961_;
}
}
else
{
lean_object* v_a_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
v_a_977_ = lean_ctor_get(v___x_967_, 1);
lean_inc(v_a_977_);
lean_dec_ref_known(v___x_967_, 2);
v___x_978_ = lean_box(0);
v___x_979_ = 1;
v___y_962_ = v_a_977_;
v___y_963_ = v___x_978_;
v___y_964_ = v___x_979_;
goto v___jp_961_;
}
v___jp_926_:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = l_Lake_MainM_failure___redArg___boxed__const__1;
v___x_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
return v___x_928_;
}
v___jp_929_:
{
if (v___y_930_ == 0)
{
if (lean_obj_tag(v___y_931_) == 0)
{
goto v___jp_926_;
}
else
{
lean_object* v_val_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
v_val_932_ = lean_ctor_get(v___y_931_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___y_931_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___y_931_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_val_932_);
lean_dec(v___y_931_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
lean_ctor_set_tag(v___x_934_, 0);
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_val_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
else
{
lean_dec(v___y_931_);
goto v___jp_926_;
}
}
v___jp_941_:
{
uint8_t v_ansiMode_946_; lean_object* v_out_947_; lean_object* v___x_948_; uint8_t v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; uint8_t v___x_952_; 
v_ansiMode_946_ = lean_ctor_get_uint8(v_cfg_924_, sizeof(void*)*1 + 2);
v_out_947_ = lean_ctor_get(v_cfg_924_, 0);
v___x_948_ = l_Lake_OutStream_get(v_out_947_);
lean_inc_ref(v___x_948_);
v___x_949_ = l_Lake_AnsiMode_isEnabled(v___x_948_, v_ansiMode_946_);
v___x_950_ = lean_unsigned_to_nat(0u);
v___x_951_ = lean_array_get_size(v___y_943_);
v___x_952_ = lean_nat_dec_lt(v___x_950_, v___x_951_);
if (v___x_952_ == 0)
{
lean_dec_ref(v___x_948_);
lean_dec_ref(v___y_943_);
v___y_930_ = v___y_942_;
v___y_931_ = v___y_944_;
goto v___jp_929_;
}
else
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___f_955_; lean_object* v___x_956_; size_t v___x_957_; size_t v___x_958_; lean_object* v___x_308__overap_959_; lean_object* v___x_960_; 
v___x_953_ = lean_box(v___y_945_);
v___x_954_ = lean_box(v___x_949_);
v___f_955_ = lean_alloc_closure((void*)(l_Lake_MainM_runLogIO___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_955_, 0, v___x_948_);
lean_closure_set(v___f_955_, 1, v___x_953_);
lean_closure_set(v___f_955_, 2, v___x_954_);
v___x_956_ = lean_box(0);
v___x_957_ = ((size_t)0ULL);
v___x_958_ = lean_usize_of_nat(v___x_951_);
v___x_308__overap_959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_940_, v___f_955_, v___y_943_, v___x_957_, v___x_958_, v___x_956_);
v___x_960_ = lean_apply_1(v___x_308__overap_959_, lean_box(0));
v___y_930_ = v___y_942_;
v___y_931_ = v___y_944_;
goto v___jp_929_;
}
}
v___jp_961_:
{
uint8_t v___x_965_; 
v___x_965_ = 0;
v___y_942_ = v___y_964_;
v___y_943_ = v___y_962_;
v___y_944_ = v___y_963_;
v___y_945_ = v___x_965_;
goto v___jp_941_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO___boxed(lean_object* v_00_u03b1_980_, lean_object* v_x_981_, lean_object* v_cfg_982_, lean_object* v_a_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lake_MainM_runLogIO(v_00_u03b1_980_, v_x_981_, v_cfg_982_);
lean_dec_ref(v_cfg_982_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0(lean_object* v_val_985_, uint8_t v___y_986_, uint8_t v_val_987_, lean_object* v_as_988_, size_t v_i_989_, size_t v_stop_990_, lean_object* v_b_991_){
_start:
{
uint8_t v___x_993_; 
v___x_993_ = lean_usize_dec_eq(v_i_989_, v_stop_990_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; lean_object* v___x_995_; size_t v___x_996_; size_t v___x_997_; 
v___x_994_ = lean_array_uget_borrowed(v_as_988_, v_i_989_);
lean_inc_ref(v_val_985_);
v___x_995_ = l_Lake_logToStream(v___x_994_, v_val_985_, v___y_986_, v_val_987_);
v___x_996_ = ((size_t)1ULL);
v___x_997_ = lean_usize_add(v_i_989_, v___x_996_);
v_i_989_ = v___x_997_;
v_b_991_ = v___x_995_;
goto _start;
}
else
{
lean_dec_ref(v_val_985_);
return v_b_991_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0___boxed(lean_object* v_val_999_, lean_object* v___y_1000_, lean_object* v_val_1001_, lean_object* v_as_1002_, lean_object* v_i_1003_, lean_object* v_stop_1004_, lean_object* v_b_1005_, lean_object* v___y_1006_){
_start:
{
uint8_t v___y_251__boxed_1007_; uint8_t v_val_252__boxed_1008_; size_t v_i_boxed_1009_; size_t v_stop_boxed_1010_; lean_object* v_res_1011_; 
v___y_251__boxed_1007_ = lean_unbox(v___y_1000_);
v_val_252__boxed_1008_ = lean_unbox(v_val_1001_);
v_i_boxed_1009_ = lean_unbox_usize(v_i_1003_);
lean_dec(v_i_1003_);
v_stop_boxed_1010_ = lean_unbox_usize(v_stop_1004_);
lean_dec(v_stop_1004_);
v_res_1011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0(v_val_999_, v___y_251__boxed_1007_, v_val_252__boxed_1008_, v_as_1002_, v_i_boxed_1009_, v_stop_boxed_1010_, v_b_1005_);
lean_dec_ref(v_as_1002_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_liftLogIO___redArg(lean_object* v_x_1012_){
_start:
{
lean_object* v___y_1018_; uint8_t v___y_1019_; uint8_t v___x_1028_; uint8_t v___x_1029_; uint8_t v___x_1030_; lean_object* v___x_1031_; lean_object* v___y_1033_; uint8_t v___y_1034_; lean_object* v___y_1035_; uint8_t v___y_1036_; lean_object* v___y_1047_; lean_object* v___y_1048_; uint8_t v___y_1049_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1028_ = 3;
v___x_1029_ = 1;
v___x_1030_ = 0;
v___x_1031_ = lean_box(1);
v___x_1051_ = ((lean_object*)(l_Lake_MainM_runLogIO___redArg___closed__0));
v___x_1052_ = lean_apply_2(v_x_1012_, v___x_1051_, lean_box(0));
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v_a_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; uint8_t v___x_1057_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
v_a_1054_ = lean_ctor_get(v___x_1052_, 1);
lean_inc(v_a_1054_);
lean_dec_ref_known(v___x_1052_, 2);
v___x_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1055_, 0, v_a_1053_);
v___x_1056_ = l_Lake_Log_maxLv(v_a_1054_);
v___x_1057_ = l_Lake_instOrdLogLevel_ord(v___x_1028_, v___x_1056_);
if (v___x_1057_ == 2)
{
uint8_t v___x_1058_; 
v___x_1058_ = 0;
v___y_1033_ = v___x_1055_;
v___y_1034_ = v___x_1058_;
v___y_1035_ = v_a_1054_;
v___y_1036_ = v___x_1029_;
goto v___jp_1032_;
}
else
{
uint8_t v___x_1059_; 
v___x_1059_ = 1;
v___y_1047_ = v___x_1055_;
v___y_1048_ = v_a_1054_;
v___y_1049_ = v___x_1059_;
goto v___jp_1046_;
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v_a_1060_ = lean_ctor_get(v___x_1052_, 1);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___x_1052_, 2);
v___x_1061_ = lean_box(0);
v___x_1062_ = 1;
v___y_1047_ = v___x_1061_;
v___y_1048_ = v_a_1060_;
v___y_1049_ = v___x_1062_;
goto v___jp_1046_;
}
v___jp_1014_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = l_Lake_MainM_failure___redArg___boxed__const__1;
v___x_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
return v___x_1016_;
}
v___jp_1017_:
{
if (v___y_1019_ == 0)
{
if (lean_obj_tag(v___y_1018_) == 0)
{
goto v___jp_1014_;
}
else
{
lean_object* v_val_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
v_val_1020_ = lean_ctor_get(v___y_1018_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___y_1018_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___y_1018_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_val_1020_);
lean_dec(v___y_1018_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
lean_ctor_set_tag(v___x_1022_, 0);
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_val_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
else
{
lean_dec(v___y_1018_);
goto v___jp_1014_;
}
}
v___jp_1032_:
{
lean_object* v___x_1037_; uint8_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v___x_1037_ = l_Lake_OutStream_get(v___x_1031_);
lean_inc_ref(v___x_1037_);
v___x_1038_ = l_Lake_AnsiMode_isEnabled(v___x_1037_, v___x_1030_);
v___x_1039_ = lean_unsigned_to_nat(0u);
v___x_1040_ = lean_array_get_size(v___y_1035_);
v___x_1041_ = lean_nat_dec_lt(v___x_1039_, v___x_1040_);
if (v___x_1041_ == 0)
{
lean_dec_ref(v___x_1037_);
lean_dec_ref(v___y_1035_);
v___y_1018_ = v___y_1033_;
v___y_1019_ = v___y_1034_;
goto v___jp_1017_;
}
else
{
lean_object* v___x_1042_; size_t v___x_1043_; size_t v___x_1044_; lean_object* v___x_1045_; 
v___x_1042_ = lean_box(0);
v___x_1043_ = ((size_t)0ULL);
v___x_1044_ = lean_usize_of_nat(v___x_1040_);
v___x_1045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0(v___x_1037_, v___y_1036_, v___x_1038_, v___y_1035_, v___x_1043_, v___x_1044_, v___x_1042_);
lean_dec_ref(v___y_1035_);
v___y_1018_ = v___y_1033_;
v___y_1019_ = v___y_1034_;
goto v___jp_1017_;
}
}
v___jp_1046_:
{
uint8_t v___x_1050_; 
v___x_1050_ = 0;
v___y_1033_ = v___y_1047_;
v___y_1034_ = v___y_1049_;
v___y_1035_ = v___y_1048_;
v___y_1036_ = v___x_1050_;
goto v___jp_1032_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_liftLogIO___redArg___boxed(lean_object* v_x_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lake_MainM_liftLogIO___redArg(v_x_1063_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_liftLogIO(lean_object* v_00_u03b1_1066_, lean_object* v_x_1067_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lake_MainM_liftLogIO___redArg(v_x_1067_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_liftLogIO___boxed(lean_object* v_00_u03b1_1070_, lean_object* v_x_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lake_MainM_liftLogIO(v_00_u03b1_1070_, v_x_1071_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO___redArg___lam__0(lean_object* v_val_1076_, uint8_t v_outLv_1077_, uint8_t v_val_1078_, lean_object* v_e_1079_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lake_logToStream(v_e_1079_, v_val_1076_, v_outLv_1077_, v_val_1078_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO___redArg___lam__0___boxed(lean_object* v_val_1082_, lean_object* v_outLv_1083_, lean_object* v_val_1084_, lean_object* v_e_1085_, lean_object* v___y_1086_){
_start:
{
uint8_t v_outLv_boxed_1087_; uint8_t v_val_188__boxed_1088_; lean_object* v_res_1089_; 
v_outLv_boxed_1087_ = lean_unbox(v_outLv_1083_);
v_val_188__boxed_1088_ = lean_unbox(v_val_1084_);
v_res_1089_ = l_Lake_MainM_runLoggerIO___redArg___lam__0(v_val_1082_, v_outLv_boxed_1087_, v_val_188__boxed_1088_, v_e_1085_);
lean_dec_ref(v_e_1085_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO___redArg(lean_object* v_x_1090_, lean_object* v_cfg_1091_){
_start:
{
uint8_t v_outLv_1093_; uint8_t v_ansiMode_1094_; lean_object* v_out_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___f_1100_; lean_object* v___x_1101_; 
v_outLv_1093_ = lean_ctor_get_uint8(v_cfg_1091_, sizeof(void*)*1 + 1);
v_ansiMode_1094_ = lean_ctor_get_uint8(v_cfg_1091_, sizeof(void*)*1 + 2);
v_out_1095_ = lean_ctor_get(v_cfg_1091_, 0);
v___x_1096_ = l_Lake_OutStream_get(v_out_1095_);
lean_inc_ref(v___x_1096_);
v___x_1097_ = l_Lake_AnsiMode_isEnabled(v___x_1096_, v_ansiMode_1094_);
v___x_1098_ = lean_box(v_outLv_1093_);
v___x_1099_ = lean_box(v___x_1097_);
v___f_1100_ = lean_alloc_closure((void*)(l_Lake_MainM_runLoggerIO___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1100_, 0, v___x_1096_);
lean_closure_set(v___f_1100_, 1, v___x_1098_);
lean_closure_set(v___f_1100_, 2, v___x_1099_);
v___x_1101_ = lean_apply_2(v_x_1090_, v___f_1100_, lean_box(0));
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1101_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1101_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
else
{
lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1117_; 
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1117_ == 0)
{
lean_object* v_unused_1118_; 
v_unused_1118_ = lean_ctor_get(v___x_1101_, 0);
lean_dec(v_unused_1118_);
v___x_1111_ = v___x_1101_;
v_isShared_1112_ = v_isSharedCheck_1117_;
goto v_resetjp_1110_;
}
else
{
lean_dec(v___x_1101_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1117_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; lean_object* v___x_1115_; 
v___x_1113_ = l_Lake_MainM_failure___redArg___boxed__const__1;
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1113_);
v___x_1115_ = v___x_1111_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO___redArg___boxed(lean_object* v_x_1119_, lean_object* v_cfg_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lake_MainM_runLoggerIO___redArg(v_x_1119_, v_cfg_1120_);
lean_dec_ref(v_cfg_1120_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO(lean_object* v_00_u03b1_1123_, lean_object* v_x_1124_, lean_object* v_cfg_1125_){
_start:
{
uint8_t v_outLv_1127_; uint8_t v_ansiMode_1128_; lean_object* v_out_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___f_1134_; lean_object* v___x_1135_; 
v_outLv_1127_ = lean_ctor_get_uint8(v_cfg_1125_, sizeof(void*)*1 + 1);
v_ansiMode_1128_ = lean_ctor_get_uint8(v_cfg_1125_, sizeof(void*)*1 + 2);
v_out_1129_ = lean_ctor_get(v_cfg_1125_, 0);
v___x_1130_ = l_Lake_OutStream_get(v_out_1129_);
lean_inc_ref(v___x_1130_);
v___x_1131_ = l_Lake_AnsiMode_isEnabled(v___x_1130_, v_ansiMode_1128_);
v___x_1132_ = lean_box(v_outLv_1127_);
v___x_1133_ = lean_box(v___x_1131_);
v___f_1134_ = lean_alloc_closure((void*)(l_Lake_MainM_runLoggerIO___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1134_, 0, v___x_1130_);
lean_closure_set(v___f_1134_, 1, v___x_1132_);
lean_closure_set(v___f_1134_, 2, v___x_1133_);
v___x_1135_ = lean_apply_2(v_x_1124_, v___f_1134_, lean_box(0));
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1135_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1135_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
else
{
lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1151_; 
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1151_ == 0)
{
lean_object* v_unused_1152_; 
v_unused_1152_ = lean_ctor_get(v___x_1135_, 0);
lean_dec(v_unused_1152_);
v___x_1145_ = v___x_1135_;
v_isShared_1146_ = v_isSharedCheck_1151_;
goto v_resetjp_1144_;
}
else
{
lean_dec(v___x_1135_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1151_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1147_ = l_Lake_MainM_failure___redArg___boxed__const__1;
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1147_);
v___x_1149_ = v___x_1145_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO___boxed(lean_object* v_00_u03b1_1153_, lean_object* v_x_1154_, lean_object* v_cfg_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lake_MainM_runLoggerIO(v_00_u03b1_1153_, v_x_1154_, v_cfg_1155_);
lean_dec_ref(v_cfg_1155_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO___redArg___lam__0(lean_object* v_val_1158_, uint8_t v___x_1159_, uint8_t v_val_1160_, lean_object* v_e_1161_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lake_logToStream(v_e_1161_, v_val_1158_, v___x_1159_, v_val_1160_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO___redArg___lam__0___boxed(lean_object* v_val_1164_, lean_object* v___x_1165_, lean_object* v_val_1166_, lean_object* v_e_1167_, lean_object* v___y_1168_){
_start:
{
uint8_t v___x_38__boxed_1169_; uint8_t v_val_39__boxed_1170_; lean_object* v_res_1171_; 
v___x_38__boxed_1169_ = lean_unbox(v___x_1165_);
v_val_39__boxed_1170_ = lean_unbox(v_val_1166_);
v_res_1171_ = l_Lake_MainM_liftLoggerIO___redArg___lam__0(v_val_1164_, v___x_38__boxed_1169_, v_val_39__boxed_1170_, v_e_1167_);
lean_dec_ref(v_e_1167_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO___redArg(lean_object* v_x_1172_){
_start:
{
uint8_t v___x_1174_; uint8_t v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___f_1181_; lean_object* v___x_1182_; 
v___x_1174_ = 1;
v___x_1175_ = 0;
v___x_1176_ = lean_box(1);
v___x_1177_ = l_Lake_OutStream_get(v___x_1176_);
lean_inc_ref(v___x_1177_);
v___x_1178_ = l_Lake_AnsiMode_isEnabled(v___x_1177_, v___x_1175_);
v___x_1179_ = lean_box(v___x_1174_);
v___x_1180_ = lean_box(v___x_1178_);
v___f_1181_ = lean_alloc_closure((void*)(l_Lake_MainM_liftLoggerIO___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1181_, 0, v___x_1177_);
lean_closure_set(v___f_1181_, 1, v___x_1179_);
lean_closure_set(v___f_1181_, 2, v___x_1180_);
v___x_1182_ = lean_apply_2(v_x_1172_, v___f_1181_, lean_box(0));
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1182_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
else
{
lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1198_; 
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; 
v_unused_1199_ = lean_ctor_get(v___x_1182_, 0);
lean_dec(v_unused_1199_);
v___x_1192_ = v___x_1182_;
v_isShared_1193_ = v_isSharedCheck_1198_;
goto v_resetjp_1191_;
}
else
{
lean_dec(v___x_1182_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1198_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1194_ = l_Lake_MainM_failure___redArg___boxed__const__1;
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v___x_1194_);
v___x_1196_ = v___x_1192_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO___redArg___boxed(lean_object* v_x_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lake_MainM_liftLoggerIO___redArg(v_x_1200_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO(lean_object* v_00_u03b1_1203_, lean_object* v_x_1204_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lake_MainM_liftLoggerIO___redArg(v_x_1204_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO___boxed(lean_object* v_00_u03b1_1207_, lean_object* v_x_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lake_MainM_liftLoggerIO(v_00_u03b1_1207_, v_x_1208_);
return v_res_1210_;
}
}
lean_object* runtime_initialize_Lake_Util_Log(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Exit(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_MainM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Util_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Exit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_MainM_tryCatchError___redArg___boxed__const__1 = _init_l_Lake_MainM_tryCatchError___redArg___boxed__const__1();
lean_mark_persistent(l_Lake_MainM_tryCatchError___redArg___boxed__const__1);
l_Lake_MainM_failure___redArg___boxed__const__1 = _init_l_Lake_MainM_failure___redArg___boxed__const__1();
lean_mark_persistent(l_Lake_MainM_failure___redArg___boxed__const__1);
l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative = _init_l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative();
lean_mark_persistent(l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_MainM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Util_Log(uint8_t builtin);
lean_object* initialize_Lake_Util_Exit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_MainM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Exit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_MainM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_MainM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_MainM(builtin);
}
#ifdef __cplusplus
}
#endif
