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
lean_object* l_Lake_instMonadMainM___aux__1___redArg(lean_object* v_a_1_, lean_object* v_a_2_){
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
LEAN_EXPORT void l_Lake_instMonadMainM___aux__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_res_22_;
v_res_22_ = l_Lake_instMonadMainM___aux__1___redArg(v_a_1_, v_a_2_);
stack->m_obj
 = v_res_22_;
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__1___redArg___boxed(lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lake_instMonadMainM___aux__1___redArg(v_a_23_, v_a_24_);
return v_res_26_;
}
}
lean_object* l_Lake_instMonadMainM___aux__1(lean_object* v_00_u03b1_27_, lean_object* v_00_u03b2_28_, lean_object* v_a_29_, lean_object* v_a_30_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lean_apply_1(v_a_30_, lean_box(0));
if (lean_obj_tag(v___x_32_) == 0)
{
lean_object* v_a_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_41_; 
v_a_33_ = lean_ctor_get(v___x_32_, 0);
v_isSharedCheck_41_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_41_ == 0)
{
v___x_35_ = v___x_32_;
v_isShared_36_ = v_isSharedCheck_41_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_a_33_);
lean_dec(v___x_32_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_41_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_37_; lean_object* v___x_39_; 
v___x_37_ = lean_apply_1(v_a_29_, v_a_33_);
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 0, v___x_37_);
v___x_39_ = v___x_35_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v___x_37_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
return v___x_39_;
}
}
}
else
{
lean_object* v_a_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_49_; 
lean_dec(v_a_29_);
v_a_42_ = lean_ctor_get(v___x_32_, 0);
v_isSharedCheck_49_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_49_ == 0)
{
v___x_44_ = v___x_32_;
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_a_42_);
lean_dec(v___x_32_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_47_; 
if (v_isShared_45_ == 0)
{
v___x_47_ = v___x_44_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_a_42_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
return v___x_47_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_instMonadMainM___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_29_ = stack[2].m_obj;
lean_object* v_a_30_ = stack[3].m_obj;
lean_object* v_res_50_;
v_res_50_ = l_Lake_instMonadMainM___aux__1(lean_box(0), lean_box(0), v_a_29_, v_a_30_);
stack->m_obj
 = v_res_50_;
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__1___boxed(lean_object* v_00_u03b1_51_, lean_object* v_00_u03b2_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lake_instMonadMainM___aux__1(v_00_u03b1_51_, v_00_u03b2_52_, v_a_53_, v_a_54_);
return v_res_56_;
}
}
lean_object* l_Lake_instMonadMainM___aux__3___redArg(lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lean_apply_1(v_a_58_, lean_box(0));
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_67_; 
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_67_ == 0)
{
lean_object* v_unused_68_; 
v_unused_68_ = lean_ctor_get(v___x_60_, 0);
lean_dec(v_unused_68_);
v___x_62_ = v___x_60_;
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
else
{
lean_dec(v___x_60_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_65_; 
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 0, v_a_57_);
v___x_65_ = v___x_62_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_a_57_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
else
{
lean_object* v_a_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_76_; 
lean_dec(v_a_57_);
v_a_69_ = lean_ctor_get(v___x_60_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_76_ == 0)
{
v___x_71_ = v___x_60_;
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_a_69_);
lean_dec(v___x_60_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_74_; 
if (v_isShared_72_ == 0)
{
v___x_74_ = v___x_71_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_a_69_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_instMonadMainM___aux__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_57_ = stack[0].m_obj;
lean_object* v_a_58_ = stack[1].m_obj;
lean_object* v_res_77_;
v_res_77_ = l_Lake_instMonadMainM___aux__3___redArg(v_a_57_, v_a_58_);
stack->m_obj
 = v_res_77_;
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__3___redArg___boxed(lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lake_instMonadMainM___aux__3___redArg(v_a_78_, v_a_79_);
return v_res_81_;
}
}
lean_object* l_Lake_instMonadMainM___aux__3(lean_object* v_00_u03b1_82_, lean_object* v_00_u03b2_83_, lean_object* v_a_84_, lean_object* v_a_85_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lean_apply_1(v_a_85_, lean_box(0));
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_94_; 
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_94_ == 0)
{
lean_object* v_unused_95_; 
v_unused_95_ = lean_ctor_get(v___x_87_, 0);
lean_dec(v_unused_95_);
v___x_89_ = v___x_87_;
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
else
{
lean_dec(v___x_87_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v_a_84_);
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_a_84_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
lean_dec(v_a_84_);
v_a_96_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_87_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_87_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_instMonadMainM___aux__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_84_ = stack[2].m_obj;
lean_object* v_a_85_ = stack[3].m_obj;
lean_object* v_res_104_;
v_res_104_ = l_Lake_instMonadMainM___aux__3(lean_box(0), lean_box(0), v_a_84_, v_a_85_);
stack->m_obj
 = v_res_104_;
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__3___boxed(lean_object* v_00_u03b1_105_, lean_object* v_00_u03b2_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lake_instMonadMainM___aux__3(v_00_u03b1_105_, v_00_u03b2_106_, v_a_107_, v_a_108_);
return v_res_110_;
}
}
lean_object* l_Lake_instMonadMainM___aux__5___redArg(lean_object* v_a_111_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v_a_111_);
return v___x_113_;
}
}
LEAN_EXPORT void l_Lake_instMonadMainM___aux__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_111_ = stack[0].m_obj;
lean_object* v_res_114_;
v_res_114_ = l_Lake_instMonadMainM___aux__5___redArg(v_a_111_);
stack->m_obj
 = v_res_114_;
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__5___redArg___boxed(lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lake_instMonadMainM___aux__5___redArg(v_a_115_);
return v_res_117_;
}
}
lean_object* l_Lake_instMonadMainM___aux__5(lean_object* v_00_u03b1_118_, lean_object* v_a_119_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_121_, 0, v_a_119_);
return v___x_121_;
}
}
LEAN_EXPORT void l_Lake_instMonadMainM___aux__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_119_ = stack[1].m_obj;
lean_object* v_res_122_;
v_res_122_ = l_Lake_instMonadMainM___aux__5(lean_box(0), v_a_119_);
stack->m_obj
 = v_res_122_;
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__5___boxed(lean_object* v_00_u03b1_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lake_instMonadMainM___aux__5(v_00_u03b1_123_, v_a_124_);
return v_res_126_;
}
}
lean_object* l_Lake_instMonadMainM___aux__7___redArg(lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = lean_apply_1(v_a_127_, lean_box(0));
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v_a_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v_a_131_ = lean_ctor_get(v___x_130_, 0);
lean_inc(v_a_131_);
lean_dec_ref_known(v___x_130_, 1);
v___x_132_ = lean_box(0);
v___x_133_ = lean_apply_2(v_a_128_, v___x_132_, lean_box(0));
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_142_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_142_ == 0)
{
v___x_136_ = v___x_133_;
v_isShared_137_ = v_isSharedCheck_142_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_133_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_142_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_138_; lean_object* v___x_140_; 
v___x_138_ = lean_apply_1(v_a_131_, v_a_134_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 0, v___x_138_);
v___x_140_ = v___x_136_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_138_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
else
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
lean_dec(v_a_131_);
v_a_143_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_150_ == 0)
{
v___x_145_ = v___x_133_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_133_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_143_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
else
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
lean_dec_ref(v_a_128_);
v_a_151_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v___x_130_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_130_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_instMonadMainM___aux__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_127_ = stack[0].m_obj;
lean_object* v_a_128_ = stack[1].m_obj;
lean_object* v_res_159_;
v_res_159_ = l_Lake_instMonadMainM___aux__7___redArg(v_a_127_, v_a_128_);
stack->m_obj
 = v_res_159_;
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__7___redArg___boxed(lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lake_instMonadMainM___aux__7___redArg(v_a_160_, v_a_161_);
return v_res_163_;
}
}
lean_object* l_Lake_instMonadMainM___aux__7(lean_object* v_00_u03b1_164_, lean_object* v_00_u03b2_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = lean_apply_1(v_a_166_, lean_box(0));
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_a_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_a_170_ = lean_ctor_get(v___x_169_, 0);
lean_inc(v_a_170_);
lean_dec_ref_known(v___x_169_, 1);
v___x_171_ = lean_box(0);
v___x_172_ = lean_apply_2(v_a_167_, v___x_171_, lean_box(0));
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_181_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_181_ == 0)
{
v___x_175_ = v___x_172_;
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_172_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_177_ = lean_apply_1(v_a_170_, v_a_173_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v___x_177_);
v___x_179_ = v___x_175_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
else
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
lean_dec(v_a_170_);
v_a_182_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_189_ == 0)
{
v___x_184_ = v___x_172_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_172_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_a_182_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
else
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_197_; 
lean_dec_ref(v_a_167_);
v_a_190_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_197_ == 0)
{
v___x_192_ = v___x_169_;
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_169_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_a_190_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_instMonadMainM___aux__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_166_ = stack[2].m_obj;
lean_object* v_a_167_ = stack[3].m_obj;
lean_object* v_res_198_;
v_res_198_ = l_Lake_instMonadMainM___aux__7(lean_box(0), lean_box(0), v_a_166_, v_a_167_);
stack->m_obj
 = v_res_198_;
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__7___boxed(lean_object* v_00_u03b1_199_, lean_object* v_00_u03b2_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lake_instMonadMainM___aux__7(v_00_u03b1_199_, v_00_u03b2_200_, v_a_201_, v_a_202_);
return v_res_204_;
}
}
lean_object* l_Lake_instMonadMainM___aux__9___redArg(lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = lean_apply_1(v_a_205_, lean_box(0));
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_a_209_);
lean_dec_ref_known(v___x_208_, 1);
v___x_210_ = lean_box(0);
v___x_211_ = lean_apply_2(v_a_206_, v___x_210_, lean_box(0));
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_218_; 
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; 
v_unused_219_ = lean_ctor_get(v___x_211_, 0);
lean_dec(v_unused_219_);
v___x_213_ = v___x_211_;
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
else
{
lean_dec(v___x_211_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v_a_209_);
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_a_209_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
else
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_227_; 
lean_dec(v_a_209_);
v_a_220_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_227_ == 0)
{
v___x_222_ = v___x_211_;
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_211_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_a_220_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
else
{
lean_dec_ref(v_a_206_);
return v___x_208_;
}
}
}
LEAN_EXPORT void l_Lake_instMonadMainM___aux__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_205_ = stack[0].m_obj;
lean_object* v_a_206_ = stack[1].m_obj;
lean_object* v_res_228_;
v_res_228_ = l_Lake_instMonadMainM___aux__9___redArg(v_a_205_, v_a_206_);
stack->m_obj
 = v_res_228_;
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__9___redArg___boxed(lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lake_instMonadMainM___aux__9___redArg(v_a_229_, v_a_230_);
return v_res_232_;
}
}
lean_object* l_Lake_instMonadMainM___aux__9(lean_object* v_00_u03b1_233_, lean_object* v_00_u03b2_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = lean_apply_1(v_a_235_, lean_box(0));
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_a_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v_a_239_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_a_239_);
lean_dec_ref_known(v___x_238_, 1);
v___x_240_ = lean_box(0);
v___x_241_ = lean_apply_2(v_a_236_, v___x_240_, lean_box(0));
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_248_; 
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_248_ == 0)
{
lean_object* v_unused_249_; 
v_unused_249_ = lean_ctor_get(v___x_241_, 0);
lean_dec(v_unused_249_);
v___x_243_ = v___x_241_;
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
else
{
lean_dec(v___x_241_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v_a_239_);
v___x_246_ = v___x_243_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_a_239_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
else
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_257_; 
lean_dec(v_a_239_);
v_a_250_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_257_ == 0)
{
v___x_252_ = v___x_241_;
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_241_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_253_ == 0)
{
v___x_255_ = v___x_252_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_a_250_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
else
{
lean_dec_ref(v_a_236_);
return v___x_238_;
}
}
}
LEAN_EXPORT void l_Lake_instMonadMainM___aux__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_235_ = stack[2].m_obj;
lean_object* v_a_236_ = stack[3].m_obj;
lean_object* v_res_258_;
v_res_258_ = l_Lake_instMonadMainM___aux__9(lean_box(0), lean_box(0), v_a_235_, v_a_236_);
stack->m_obj
 = v_res_258_;
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__9___boxed(lean_object* v_00_u03b1_259_, lean_object* v_00_u03b2_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lake_instMonadMainM___aux__9(v_00_u03b1_259_, v_00_u03b2_260_, v_a_261_, v_a_262_);
return v_res_264_;
}
}
lean_object* l_Lake_instMonadMainM___aux__11___redArg(lean_object* v_a_265_, lean_object* v_a_266_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = lean_apply_1(v_a_265_, lean_box(0));
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; 
lean_dec_ref_known(v___x_268_, 1);
v___x_269_ = lean_box(0);
v___x_270_ = lean_apply_2(v_a_266_, v___x_269_, lean_box(0));
return v___x_270_;
}
else
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
lean_dec_ref(v_a_266_);
v_a_271_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_278_ == 0)
{
v___x_273_ = v___x_268_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_268_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_271_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_instMonadMainM___aux__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_265_ = stack[0].m_obj;
lean_object* v_a_266_ = stack[1].m_obj;
lean_object* v_res_279_;
v_res_279_ = l_Lake_instMonadMainM___aux__11___redArg(v_a_265_, v_a_266_);
stack->m_obj
 = v_res_279_;
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__11___redArg___boxed(lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lake_instMonadMainM___aux__11___redArg(v_a_280_, v_a_281_);
return v_res_283_;
}
}
lean_object* l_Lake_instMonadMainM___aux__11(lean_object* v_00_u03b1_284_, lean_object* v_00_u03b2_285_, lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = lean_apply_1(v_a_286_, lean_box(0));
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; 
lean_dec_ref_known(v___x_289_, 1);
v___x_290_ = lean_box(0);
v___x_291_ = lean_apply_2(v_a_287_, v___x_290_, lean_box(0));
return v___x_291_;
}
else
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
lean_dec_ref(v_a_287_);
v_a_292_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_289_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_289_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_instMonadMainM___aux__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_286_ = stack[2].m_obj;
lean_object* v_a_287_ = stack[3].m_obj;
lean_object* v_res_300_;
v_res_300_ = l_Lake_instMonadMainM___aux__11(lean_box(0), lean_box(0), v_a_286_, v_a_287_);
stack->m_obj
 = v_res_300_;
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__11___boxed(lean_object* v_00_u03b1_301_, lean_object* v_00_u03b2_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lake_instMonadMainM___aux__11(v_00_u03b1_301_, v_00_u03b2_302_, v_a_303_, v_a_304_);
return v_res_306_;
}
}
lean_object* l_Lake_instMonadMainM___aux__13___redArg(lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = lean_apply_1(v_a_307_, lean_box(0));
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v___x_312_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_a_311_);
lean_dec_ref_known(v___x_310_, 1);
v___x_312_ = lean_apply_2(v_a_308_, v_a_311_, lean_box(0));
return v___x_312_;
}
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
lean_dec_ref(v_a_308_);
v_a_313_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_310_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_310_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_instMonadMainM___aux__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_307_ = stack[0].m_obj;
lean_object* v_a_308_ = stack[1].m_obj;
lean_object* v_res_321_;
v_res_321_ = l_Lake_instMonadMainM___aux__13___redArg(v_a_307_, v_a_308_);
stack->m_obj
 = v_res_321_;
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__13___redArg___boxed(lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lake_instMonadMainM___aux__13___redArg(v_a_322_, v_a_323_);
return v_res_325_;
}
}
lean_object* l_Lake_instMonadMainM___aux__13(lean_object* v_00_u03b1_326_, lean_object* v_00_u03b2_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = lean_apply_1(v_a_328_, lean_box(0));
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v___x_333_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
lean_dec_ref_known(v___x_331_, 1);
v___x_333_ = lean_apply_2(v_a_329_, v_a_332_, lean_box(0));
return v___x_333_;
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
lean_dec_ref(v_a_329_);
v_a_334_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_331_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_331_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_instMonadMainM___aux__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_328_ = stack[2].m_obj;
lean_object* v_a_329_ = stack[3].m_obj;
lean_object* v_res_342_;
v_res_342_ = l_Lake_instMonadMainM___aux__13(lean_box(0), lean_box(0), v_a_328_, v_a_329_);
stack->m_obj
 = v_res_342_;
}
LEAN_EXPORT lean_object* l_Lake_instMonadMainM___aux__13___boxed(lean_object* v_00_u03b1_343_, lean_object* v_00_u03b2_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lake_instMonadMainM___aux__13(v_00_u03b1_343_, v_00_u03b2_344_, v_a_345_, v_a_346_);
return v_res_348_;
}
}
lean_object* l_Lake_instMonadFinallyMainM___aux__1___redArg(lean_object* v_x_369_, lean_object* v_f_370_){
_start:
{
lean_object* v_r_372_; 
v_r_372_ = lean_apply_1(v_x_369_, lean_box(0));
if (lean_obj_tag(v_r_372_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_398_; 
v_a_373_ = lean_ctor_get(v_r_372_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v_r_372_);
if (v_isSharedCheck_398_ == 0)
{
v___x_375_ = v_r_372_;
v_isShared_376_ = v_isSharedCheck_398_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v_r_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_398_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
lean_inc(v_a_373_);
if (v_isShared_376_ == 0)
{
lean_ctor_set_tag(v___x_375_, 1);
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_397_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_379_; 
v___x_379_ = lean_apply_2(v_f_370_, v___x_378_, lean_box(0));
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_388_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_388_ == 0)
{
v___x_382_ = v___x_379_;
v_isShared_383_ = v_isSharedCheck_388_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_379_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_388_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v_a_373_);
lean_ctor_set(v___x_384_, 1, v_a_380_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_384_);
v___x_386_ = v___x_382_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_384_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
lean_dec(v_a_373_);
v_a_389_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_379_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_379_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v_a_399_ = lean_ctor_get(v_r_372_, 0);
lean_inc(v_a_399_);
lean_dec_ref_known(v_r_372_, 1);
v___x_400_ = lean_box(0);
v___x_401_ = lean_apply_2(v_f_370_, v___x_400_, lean_box(0));
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_408_ == 0)
{
lean_object* v_unused_409_; 
v_unused_409_ = lean_ctor_get(v___x_401_, 0);
lean_dec(v_unused_409_);
v___x_403_ = v___x_401_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_dec(v___x_401_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
lean_ctor_set_tag(v___x_403_, 1);
lean_ctor_set(v___x_403_, 0, v_a_399_);
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_399_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_dec(v_a_399_);
v_a_410_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_401_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_401_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_instMonadFinallyMainM___aux__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_369_ = stack[0].m_obj;
lean_object* v_f_370_ = stack[1].m_obj;
lean_object* v_res_418_;
v_res_418_ = l_Lake_instMonadFinallyMainM___aux__1___redArg(v_x_369_, v_f_370_);
stack->m_obj
 = v_res_418_;
}
LEAN_EXPORT lean_object* l_Lake_instMonadFinallyMainM___aux__1___redArg___boxed(lean_object* v_x_419_, lean_object* v_f_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lake_instMonadFinallyMainM___aux__1___redArg(v_x_419_, v_f_420_);
return v_res_422_;
}
}
lean_object* l_Lake_instMonadFinallyMainM___aux__1(lean_object* v_00_u03b1_423_, lean_object* v_00_u03b2_424_, lean_object* v_x_425_, lean_object* v_f_426_){
_start:
{
lean_object* v_r_428_; 
v_r_428_ = lean_apply_1(v_x_425_, lean_box(0));
if (lean_obj_tag(v_r_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_454_; 
v_a_429_ = lean_ctor_get(v_r_428_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v_r_428_);
if (v_isSharedCheck_454_ == 0)
{
v___x_431_ = v_r_428_;
v_isShared_432_ = v_isSharedCheck_454_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v_r_428_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_454_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
lean_inc(v_a_429_);
if (v_isShared_432_ == 0)
{
lean_ctor_set_tag(v___x_431_, 1);
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_453_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_435_; 
v___x_435_ = lean_apply_2(v_f_426_, v___x_434_, lean_box(0));
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_444_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_444_ == 0)
{
v___x_438_ = v___x_435_;
v_isShared_439_ = v_isSharedCheck_444_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_435_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_444_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v_a_429_);
lean_ctor_set(v___x_440_, 1, v_a_436_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_440_);
v___x_442_ = v___x_438_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
lean_dec(v_a_429_);
v_a_445_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_435_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_435_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v_a_455_ = lean_ctor_get(v_r_428_, 0);
lean_inc(v_a_455_);
lean_dec_ref_known(v_r_428_, 1);
v___x_456_ = lean_box(0);
v___x_457_ = lean_apply_2(v_f_426_, v___x_456_, lean_box(0));
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; 
v_unused_465_ = lean_ctor_get(v___x_457_, 0);
lean_dec(v_unused_465_);
v___x_459_ = v___x_457_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_dec(v___x_457_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
lean_ctor_set_tag(v___x_459_, 1);
lean_ctor_set(v___x_459_, 0, v_a_455_);
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_455_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_dec(v_a_455_);
v_a_466_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_457_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_457_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_instMonadFinallyMainM___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_425_ = stack[2].m_obj;
lean_object* v_f_426_ = stack[3].m_obj;
lean_object* v_res_474_;
v_res_474_ = l_Lake_instMonadFinallyMainM___aux__1(lean_box(0), lean_box(0), v_x_425_, v_f_426_);
stack->m_obj
 = v_res_474_;
}
LEAN_EXPORT lean_object* l_Lake_instMonadFinallyMainM___aux__1___boxed(lean_object* v_00_u03b1_475_, lean_object* v_00_u03b2_476_, lean_object* v_x_477_, lean_object* v_f_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lake_instMonadFinallyMainM___aux__1(v_00_u03b1_475_, v_00_u03b2_476_, v_x_477_, v_f_478_);
return v_res_480_;
}
}
lean_object* l_Lake_instMonadLiftBaseIOMainM___aux__1___redArg(lean_object* v_act_483_){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_apply_1(v_act_483_, lean_box(0));
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT void l_Lake_instMonadLiftBaseIOMainM___aux__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_483_ = stack[0].m_obj;
lean_object* v_res_487_;
v_res_487_ = l_Lake_instMonadLiftBaseIOMainM___aux__1___redArg(v_act_483_);
stack->m_obj
 = v_res_487_;
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftBaseIOMainM___aux__1___redArg___boxed(lean_object* v_act_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lake_instMonadLiftBaseIOMainM___aux__1___redArg(v_act_488_);
return v_res_490_;
}
}
lean_object* l_Lake_instMonadLiftBaseIOMainM___aux__1(lean_object* v_00_u03b1_491_, lean_object* v_act_492_){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_apply_1(v_act_492_, lean_box(0));
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT void l_Lake_instMonadLiftBaseIOMainM___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_492_ = stack[1].m_obj;
lean_object* v_res_496_;
v_res_496_ = l_Lake_instMonadLiftBaseIOMainM___aux__1(lean_box(0), v_act_492_);
stack->m_obj
 = v_res_496_;
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftBaseIOMainM___aux__1___boxed(lean_object* v_00_u03b1_497_, lean_object* v_act_498_, lean_object* v_a_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lake_instMonadLiftBaseIOMainM___aux__1(v_00_u03b1_497_, v_act_498_);
return v_res_500_;
}
}
lean_object* l_Lake_MainM_mk___redArg(lean_object* v_x_503_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = lean_apply_1(v_x_503_, lean_box(0));
return v___x_505_;
}
}
LEAN_EXPORT void l_Lake_MainM_mk___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_503_ = stack[0].m_obj;
lean_object* v_res_506_;
v_res_506_ = l_Lake_MainM_mk___redArg(v_x_503_);
stack->m_obj
 = v_res_506_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_mk___redArg___boxed(lean_object* v_x_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lake_MainM_mk___redArg(v_x_507_);
return v_res_509_;
}
}
lean_object* l_Lake_MainM_mk(lean_object* v_00_u03b1_510_, lean_object* v_x_511_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = lean_apply_1(v_x_511_, lean_box(0));
return v___x_513_;
}
}
LEAN_EXPORT void l_Lake_MainM_mk_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_511_ = stack[1].m_obj;
lean_object* v_res_514_;
v_res_514_ = l_Lake_MainM_mk(lean_box(0), v_x_511_);
stack->m_obj
 = v_res_514_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_mk___boxed(lean_object* v_00_u03b1_515_, lean_object* v_x_516_, lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lake_MainM_mk(v_00_u03b1_515_, v_x_516_);
return v_res_518_;
}
}
lean_object* l_Lake_MainM_toEIO___redArg(lean_object* v_self_519_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = lean_apply_1(v_self_519_, lean_box(0));
return v___x_521_;
}
}
LEAN_EXPORT void l_Lake_MainM_toEIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_519_ = stack[0].m_obj;
lean_object* v_res_522_;
v_res_522_ = l_Lake_MainM_toEIO___redArg(v_self_519_);
stack->m_obj
 = v_res_522_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_toEIO___redArg___boxed(lean_object* v_self_523_, lean_object* v_a_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lake_MainM_toEIO___redArg(v_self_523_);
return v_res_525_;
}
}
lean_object* l_Lake_MainM_toEIO(lean_object* v_00_u03b1_526_, lean_object* v_self_527_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = lean_apply_1(v_self_527_, lean_box(0));
return v___x_529_;
}
}
LEAN_EXPORT void l_Lake_MainM_toEIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_527_ = stack[1].m_obj;
lean_object* v_res_530_;
v_res_530_ = l_Lake_MainM_toEIO(lean_box(0), v_self_527_);
stack->m_obj
 = v_res_530_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_toEIO___boxed(lean_object* v_00_u03b1_531_, lean_object* v_self_532_, lean_object* v_a_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lake_MainM_toEIO(v_00_u03b1_531_, v_self_532_);
return v_res_534_;
}
}
lean_object* l_Lake_MainM_toBaseIO___redArg(lean_object* v_self_535_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = lean_apply_1(v_self_535_, lean_box(0));
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_537_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_537_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
lean_ctor_set_tag(v___x_540_, 1);
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
else
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_553_; 
v_a_546_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_553_ == 0)
{
v___x_548_ = v___x_537_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_537_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
lean_ctor_set_tag(v___x_548_, 0);
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_MainM_toBaseIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_535_ = stack[0].m_obj;
lean_object* v_res_554_;
v_res_554_ = l_Lake_MainM_toBaseIO___redArg(v_self_535_);
stack->m_obj
 = v_res_554_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_toBaseIO___redArg___boxed(lean_object* v_self_555_, lean_object* v_a_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lake_MainM_toBaseIO___redArg(v_self_555_);
return v_res_557_;
}
}
lean_object* l_Lake_MainM_toBaseIO(lean_object* v_00_u03b1_558_, lean_object* v_self_559_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = lean_apply_1(v_self_559_, lean_box(0));
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_561_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_561_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
lean_ctor_set_tag(v___x_564_, 1);
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
v_a_570_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_561_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_561_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
lean_ctor_set_tag(v___x_572_, 0);
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_MainM_toBaseIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_559_ = stack[1].m_obj;
lean_object* v_res_578_;
v_res_578_ = l_Lake_MainM_toBaseIO(lean_box(0), v_self_559_);
stack->m_obj
 = v_res_578_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_toBaseIO___boxed(lean_object* v_00_u03b1_579_, lean_object* v_self_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lake_MainM_toBaseIO(v_00_u03b1_579_, v_self_580_);
return v_res_582_;
}
}
uint32_t l_Lake_MainM_run___redArg(lean_object* v_self_583_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = lean_apply_1(v_self_583_, lean_box(0));
if (lean_obj_tag(v___x_585_) == 0)
{
uint32_t v___x_586_; 
lean_dec_ref_known(v___x_585_, 1);
v___x_586_ = 0;
return v___x_586_;
}
else
{
lean_object* v_a_587_; uint32_t v___x_588_; 
v_a_587_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_a_587_);
lean_dec_ref_known(v___x_585_, 1);
v___x_588_ = lean_unbox_uint32(v_a_587_);
lean_dec(v_a_587_);
return v___x_588_;
}
}
}
LEAN_EXPORT void l_Lake_MainM_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_583_ = stack[0].m_obj;
uint32_t v_res_589_;
v_res_589_ = l_Lake_MainM_run___redArg(v_self_583_);
stack->m_num = v_res_589_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_run___redArg___boxed(lean_object* v_self_590_, lean_object* v_a_591_){
_start:
{
uint32_t v_res_592_; lean_object* v_r_593_; 
v_res_592_ = l_Lake_MainM_run___redArg(v_self_590_);
v_r_593_ = lean_box_uint32(v_res_592_);
return v_r_593_;
}
}
uint32_t l_Lake_MainM_run(lean_object* v_00_u03b1_594_, lean_object* v_self_595_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = lean_apply_1(v_self_595_, lean_box(0));
if (lean_obj_tag(v___x_597_) == 0)
{
uint32_t v___x_598_; 
lean_dec_ref_known(v___x_597_, 1);
v___x_598_ = 0;
return v___x_598_;
}
else
{
lean_object* v_a_599_; uint32_t v___x_600_; 
v_a_599_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_a_599_);
lean_dec_ref_known(v___x_597_, 1);
v___x_600_ = lean_unbox_uint32(v_a_599_);
lean_dec(v_a_599_);
return v___x_600_;
}
}
}
LEAN_EXPORT void l_Lake_MainM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_595_ = stack[1].m_obj;
uint32_t v_res_601_;
v_res_601_ = l_Lake_MainM_run(lean_box(0), v_self_595_);
stack->m_num = v_res_601_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_run___boxed(lean_object* v_00_u03b1_602_, lean_object* v_self_603_, lean_object* v_a_604_){
_start:
{
uint32_t v_res_605_; lean_object* v_r_606_; 
v_res_605_ = l_Lake_MainM_run(v_00_u03b1_602_, v_self_603_);
v_r_606_ = lean_box_uint32(v_res_605_);
return v_r_606_;
}
}
lean_object* l_Lake_MainM_exit___redArg(uint32_t v_rc_607_){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_box_uint32(v_rc_607_);
v___x_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
}
LEAN_EXPORT void l_Lake_MainM_exit___redArg_0interp(lean_interpreter_value* stack)
{
uint32_t v_rc_607_ = stack[0].m_num;
lean_object* v_res_611_;
v_res_611_ = l_Lake_MainM_exit___redArg(v_rc_607_);
stack->m_obj
 = v_res_611_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_exit___redArg___boxed(lean_object* v_rc_612_, lean_object* v_a_613_){
_start:
{
uint32_t v_rc_boxed_614_; lean_object* v_res_615_; 
v_rc_boxed_614_ = lean_unbox_uint32(v_rc_612_);
lean_dec(v_rc_612_);
v_res_615_ = l_Lake_MainM_exit___redArg(v_rc_boxed_614_);
return v_res_615_;
}
}
lean_object* l_Lake_MainM_exit(lean_object* v_00_u03b1_616_, uint32_t v_rc_617_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_box_uint32(v_rc_617_);
v___x_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT void l_Lake_MainM_exit_0interp(lean_interpreter_value* stack)
{
uint32_t v_rc_617_ = stack[1].m_num;
lean_object* v_res_621_;
v_res_621_ = l_Lake_MainM_exit(lean_box(0), v_rc_617_);
stack->m_obj
 = v_res_621_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_exit___boxed(lean_object* v_00_u03b1_622_, lean_object* v_rc_623_, lean_object* v_a_624_){
_start:
{
uint32_t v_rc_boxed_625_; lean_object* v_res_626_; 
v_rc_boxed_625_ = lean_unbox_uint32(v_rc_623_);
lean_dec(v_rc_623_);
v_res_626_ = l_Lake_MainM_exit(v_00_u03b1_622_, v_rc_boxed_625_);
return v_res_626_;
}
}
lean_object* l_Lake_MainM_tryCatchExit___redArg(lean_object* v_f_629_, lean_object* v_self_630_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = lean_apply_1(v_self_630_, lean_box(0));
if (lean_obj_tag(v___x_632_) == 0)
{
lean_dec_ref(v_f_629_);
return v___x_632_;
}
else
{
lean_object* v_a_633_; lean_object* v___x_634_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref_known(v___x_632_, 1);
v___x_634_ = lean_apply_2(v_f_629_, v_a_633_, lean_box(0));
return v___x_634_;
}
}
}
LEAN_EXPORT void l_Lake_MainM_tryCatchExit___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_629_ = stack[0].m_obj;
lean_object* v_self_630_ = stack[1].m_obj;
lean_object* v_res_635_;
v_res_635_ = l_Lake_MainM_tryCatchExit___redArg(v_f_629_, v_self_630_);
stack->m_obj
 = v_res_635_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchExit___redArg___boxed(lean_object* v_f_636_, lean_object* v_self_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lake_MainM_tryCatchExit___redArg(v_f_636_, v_self_637_);
return v_res_639_;
}
}
lean_object* l_Lake_MainM_tryCatchExit(lean_object* v_00_u03b1_640_, lean_object* v_f_641_, lean_object* v_self_642_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = lean_apply_1(v_self_642_, lean_box(0));
if (lean_obj_tag(v___x_644_) == 0)
{
lean_dec_ref(v_f_641_);
return v___x_644_;
}
else
{
lean_object* v_a_645_; lean_object* v___x_646_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
lean_dec_ref_known(v___x_644_, 1);
v___x_646_ = lean_apply_2(v_f_641_, v_a_645_, lean_box(0));
return v___x_646_;
}
}
}
LEAN_EXPORT void l_Lake_MainM_tryCatchExit_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_641_ = stack[1].m_obj;
lean_object* v_self_642_ = stack[2].m_obj;
lean_object* v_res_647_;
v_res_647_ = l_Lake_MainM_tryCatchExit(lean_box(0), v_f_641_, v_self_642_);
stack->m_obj
 = v_res_647_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchExit___boxed(lean_object* v_00_u03b1_648_, lean_object* v_f_649_, lean_object* v_self_650_, lean_object* v_a_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lake_MainM_tryCatchExit(v_00_u03b1_648_, v_f_649_, v_self_650_);
return v_res_652_;
}
}
static lean_object* _init_l_Lake_MainM_tryCatchError___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_653_; lean_object* v___x_654_; 
v___x_653_ = 0;
v___x_654_ = lean_box_uint32(v___x_653_);
return v___x_654_;
}
}
lean_object* l_Lake_MainM_tryCatchError___redArg(lean_object* v_f_655_, lean_object* v_self_656_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = lean_apply_1(v_self_656_, lean_box(0));
if (lean_obj_tag(v___x_658_) == 0)
{
lean_dec_ref(v_f_655_);
return v___x_658_;
}
else
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_671_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_671_ == 0)
{
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_671_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_671_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
uint32_t v___x_663_; uint32_t v___x_664_; uint8_t v___x_665_; 
v___x_663_ = 0;
v___x_664_ = lean_unbox_uint32(v_a_659_);
v___x_665_ = lean_uint32_dec_eq(v___x_664_, v___x_663_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; 
lean_del_object(v___x_661_);
v___x_666_ = lean_apply_2(v_f_655_, v_a_659_, lean_box(0));
return v___x_666_;
}
else
{
lean_object* v___x_667_; lean_object* v___x_669_; 
lean_dec(v_a_659_);
lean_dec_ref(v_f_655_);
v___x_667_ = l_Lake_MainM_tryCatchError___redArg___boxed__const__1;
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_667_);
v___x_669_ = v___x_661_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_MainM_tryCatchError___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_655_ = stack[0].m_obj;
lean_object* v_self_656_ = stack[1].m_obj;
lean_object* v_res_672_;
v_res_672_ = l_Lake_MainM_tryCatchError___redArg(v_f_655_, v_self_656_);
stack->m_obj
 = v_res_672_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchError___redArg___boxed(lean_object* v_f_673_, lean_object* v_self_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lake_MainM_tryCatchError___redArg(v_f_673_, v_self_674_);
return v_res_676_;
}
}
lean_object* l_Lake_MainM_tryCatchError(lean_object* v_00_u03b1_677_, lean_object* v_f_678_, lean_object* v_self_679_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = lean_apply_1(v_self_679_, lean_box(0));
if (lean_obj_tag(v___x_681_) == 0)
{
lean_dec_ref(v_f_678_);
return v___x_681_;
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_694_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_694_ == 0)
{
v___x_684_ = v___x_681_;
v_isShared_685_ = v_isSharedCheck_694_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_681_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_694_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
uint32_t v___x_686_; uint32_t v___x_687_; uint8_t v___x_688_; 
v___x_686_ = 0;
v___x_687_ = lean_unbox_uint32(v_a_682_);
v___x_688_ = lean_uint32_dec_eq(v___x_687_, v___x_686_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; 
lean_del_object(v___x_684_);
v___x_689_ = lean_apply_2(v_f_678_, v_a_682_, lean_box(0));
return v___x_689_;
}
else
{
lean_object* v___x_690_; lean_object* v___x_692_; 
lean_dec(v_a_682_);
lean_dec_ref(v_f_678_);
v___x_690_ = l_Lake_MainM_tryCatchError___redArg___boxed__const__1;
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v___x_690_);
v___x_692_ = v___x_684_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_690_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_MainM_tryCatchError_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_678_ = stack[1].m_obj;
lean_object* v_self_679_ = stack[2].m_obj;
lean_object* v_res_695_;
v_res_695_ = l_Lake_MainM_tryCatchError(lean_box(0), v_f_678_, v_self_679_);
stack->m_obj
 = v_res_695_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchError___boxed(lean_object* v_00_u03b1_696_, lean_object* v_f_697_, lean_object* v_self_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lake_MainM_tryCatchError(v_00_u03b1_696_, v_f_697_, v_self_698_);
return v_res_700_;
}
}
static lean_object* _init_l_Lake_MainM_failure___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_701_; lean_object* v___x_702_; 
v___x_701_ = 1;
v___x_702_ = lean_box_uint32(v___x_701_);
return v___x_702_;
}
}
lean_object* l_Lake_MainM_failure___redArg(){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = l_Lake_MainM_failure___redArg___boxed__const__1;
v___x_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
return v___x_705_;
}
}
LEAN_EXPORT void l_Lake_MainM_failure___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_706_;
v_res_706_ = l_Lake_MainM_failure___redArg();
stack->m_obj
 = v_res_706_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_failure___redArg___boxed(lean_object* v_a_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lake_MainM_failure___redArg();
return v_res_708_;
}
}
lean_object* l_Lake_MainM_failure(lean_object* v_00_u03b1_709_){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = l_Lake_MainM_failure___redArg___boxed__const__1;
v___x_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
return v___x_712_;
}
}
LEAN_EXPORT void l_Lake_MainM_failure_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_713_;
v_res_713_ = l_Lake_MainM_failure(lean_box(0));
stack->m_obj
 = v_res_713_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_failure___boxed(lean_object* v_00_u03b1_714_, lean_object* v_a_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lake_MainM_failure(v_00_u03b1_714_);
return v_res_716_;
}
}
lean_object* l_Lake_MainM_orElse___redArg(lean_object* v_self_717_, lean_object* v_other_718_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = lean_apply_1(v_self_717_, lean_box(0));
if (lean_obj_tag(v___x_720_) == 0)
{
lean_dec_ref(v_other_718_);
return v___x_720_;
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_734_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_734_ == 0)
{
v___x_723_ = v___x_720_;
v_isShared_724_ = v_isSharedCheck_734_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_720_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_734_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
uint32_t v___x_725_; uint32_t v___x_726_; uint8_t v___x_727_; 
v___x_725_ = 0;
v___x_726_ = lean_unbox_uint32(v_a_721_);
lean_dec(v_a_721_);
v___x_727_ = lean_uint32_dec_eq(v___x_726_, v___x_725_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; 
lean_del_object(v___x_723_);
v___x_728_ = lean_box(0);
v___x_729_ = lean_apply_2(v_other_718_, v___x_728_, lean_box(0));
return v___x_729_;
}
else
{
lean_object* v___x_730_; lean_object* v___x_732_; 
lean_dec_ref(v_other_718_);
v___x_730_ = l_Lake_MainM_tryCatchError___redArg___boxed__const__1;
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v___x_730_);
v___x_732_ = v___x_723_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_MainM_orElse___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_717_ = stack[0].m_obj;
lean_object* v_other_718_ = stack[1].m_obj;
lean_object* v_res_735_;
v_res_735_ = l_Lake_MainM_orElse___redArg(v_self_717_, v_other_718_);
stack->m_obj
 = v_res_735_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_orElse___redArg___boxed(lean_object* v_self_736_, lean_object* v_other_737_, lean_object* v_a_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lake_MainM_orElse___redArg(v_self_736_, v_other_737_);
return v_res_739_;
}
}
lean_object* l_Lake_MainM_orElse(lean_object* v_00_u03b1_740_, lean_object* v_self_741_, lean_object* v_other_742_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = lean_apply_1(v_self_741_, lean_box(0));
if (lean_obj_tag(v___x_744_) == 0)
{
lean_dec_ref(v_other_742_);
return v___x_744_;
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_758_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_758_ == 0)
{
v___x_747_ = v___x_744_;
v_isShared_748_ = v_isSharedCheck_758_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_744_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_758_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
uint32_t v___x_749_; uint32_t v___x_750_; uint8_t v___x_751_; 
v___x_749_ = 0;
v___x_750_ = lean_unbox_uint32(v_a_745_);
lean_dec(v_a_745_);
v___x_751_ = lean_uint32_dec_eq(v___x_750_, v___x_749_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; 
lean_del_object(v___x_747_);
v___x_752_ = lean_box(0);
v___x_753_ = lean_apply_2(v_other_742_, v___x_752_, lean_box(0));
return v___x_753_;
}
else
{
lean_object* v___x_754_; lean_object* v___x_756_; 
lean_dec_ref(v_other_742_);
v___x_754_ = l_Lake_MainM_tryCatchError___redArg___boxed__const__1;
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v___x_754_);
v___x_756_ = v___x_747_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_MainM_orElse_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_741_ = stack[1].m_obj;
lean_object* v_other_742_ = stack[2].m_obj;
lean_object* v_res_759_;
v_res_759_ = l_Lake_MainM_orElse(lean_box(0), v_self_741_, v_other_742_);
stack->m_obj
 = v_res_759_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_orElse___boxed(lean_object* v_00_u03b1_760_, lean_object* v_self_761_, lean_object* v_other_762_, lean_object* v_a_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lake_MainM_orElse(v_00_u03b1_760_, v_self_761_, v_other_762_);
return v_res_764_;
}
}
static lean_object* _init_l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative(void){
_start:
{
lean_object* v___x_767_; lean_object* v_toApplicative_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_767_ = ((lean_object*)(l_Lake_instMonadMainM));
v_toApplicative_768_ = lean_ctor_get(v___x_767_, 0);
v___x_769_ = ((lean_object*)(l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__0));
v___x_770_ = ((lean_object*)(l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__1));
lean_inc_ref(v_toApplicative_768_);
v___x_771_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_771_, 0, v_toApplicative_768_);
lean_ctor_set(v___x_771_, 1, v___x_769_);
lean_ctor_set(v___x_771_, 2, v___x_770_);
return v___x_771_;
}
}
lean_object* l_Lake_MainM_instMonadLog___lam__0(lean_object* v___x_772_, uint8_t v___x_773_, uint8_t v___x_774_, lean_object* v_e_775_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = l_Lake_OutStream_logEntry(v___x_772_, v_e_775_, v___x_773_, v___x_774_);
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT void l_Lake_MainM_instMonadLog___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_772_ = stack[0].m_obj;
uint8_t v___x_773_ = stack[1].m_num;
uint8_t v___x_774_ = stack[2].m_num;
lean_object* v_e_775_ = stack[3].m_obj;
lean_object* v_res_779_;
v_res_779_ = l_Lake_MainM_instMonadLog___lam__0(v___x_772_, v___x_773_, v___x_774_, v_e_775_);
stack->m_obj
 = v_res_779_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadLog___lam__0___boxed(lean_object* v___x_780_, lean_object* v___x_781_, lean_object* v___x_782_, lean_object* v_e_783_, lean_object* v___y_784_){
_start:
{
uint8_t v___x_37__boxed_785_; uint8_t v___x_38__boxed_786_; lean_object* v_res_787_; 
v___x_37__boxed_785_ = lean_unbox(v___x_781_);
v___x_38__boxed_786_ = lean_unbox(v___x_782_);
v_res_787_ = l_Lake_MainM_instMonadLog___lam__0(v___x_780_, v___x_37__boxed_785_, v___x_38__boxed_786_, v_e_783_);
lean_dec_ref(v_e_783_);
lean_dec(v___x_780_);
return v_res_787_;
}
}
lean_object* l_Lake_MainM_error___redArg(lean_object* v_msg_795_, uint32_t v_rc_796_){
_start:
{
uint8_t v___x_798_; uint8_t v___x_799_; lean_object* v___x_800_; uint8_t v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_798_ = 1;
v___x_799_ = 0;
v___x_800_ = lean_box(1);
v___x_801_ = 3;
v___x_802_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_802_, 0, v_msg_795_);
lean_ctor_set_uint8(v___x_802_, sizeof(void*)*1, v___x_801_);
v___x_803_ = l_Lake_OutStream_logEntry(v___x_800_, v___x_802_, v___x_798_, v___x_799_);
lean_dec_ref_known(v___x_802_, 1);
v___x_804_ = lean_box_uint32(v_rc_796_);
v___x_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
return v___x_805_;
}
}
LEAN_EXPORT void l_Lake_MainM_error___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_795_ = stack[0].m_obj;
uint32_t v_rc_796_ = stack[1].m_num;
lean_object* v_res_806_;
v_res_806_ = l_Lake_MainM_error___redArg(v_msg_795_, v_rc_796_);
stack->m_obj
 = v_res_806_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_error___redArg___boxed(lean_object* v_msg_807_, lean_object* v_rc_808_, lean_object* v_a_809_){
_start:
{
uint32_t v_rc_boxed_810_; lean_object* v_res_811_; 
v_rc_boxed_810_ = lean_unbox_uint32(v_rc_808_);
lean_dec(v_rc_808_);
v_res_811_ = l_Lake_MainM_error___redArg(v_msg_807_, v_rc_boxed_810_);
return v_res_811_;
}
}
lean_object* l_Lake_MainM_error(lean_object* v_00_u03b1_812_, lean_object* v_msg_813_, uint32_t v_rc_814_){
_start:
{
uint8_t v___x_816_; uint8_t v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_816_ = 1;
v___x_817_ = 0;
v___x_818_ = lean_box(1);
v___x_819_ = 3;
v___x_820_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_820_, 0, v_msg_813_);
lean_ctor_set_uint8(v___x_820_, sizeof(void*)*1, v___x_819_);
v___x_821_ = l_Lake_OutStream_logEntry(v___x_818_, v___x_820_, v___x_816_, v___x_817_);
lean_dec_ref_known(v___x_820_, 1);
v___x_822_ = lean_box_uint32(v_rc_814_);
v___x_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
return v___x_823_;
}
}
LEAN_EXPORT void l_Lake_MainM_error_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_813_ = stack[1].m_obj;
uint32_t v_rc_814_ = stack[2].m_num;
lean_object* v_res_824_;
v_res_824_ = l_Lake_MainM_error(lean_box(0), v_msg_813_, v_rc_814_);
stack->m_obj
 = v_res_824_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_error___boxed(lean_object* v_00_u03b1_825_, lean_object* v_msg_826_, lean_object* v_rc_827_, lean_object* v_a_828_){
_start:
{
uint32_t v_rc_boxed_829_; lean_object* v_res_830_; 
v_rc_boxed_829_ = lean_unbox_uint32(v_rc_827_);
lean_dec(v_rc_827_);
v_res_830_ = l_Lake_MainM_error(v_00_u03b1_825_, v_msg_826_, v_rc_boxed_829_);
return v_res_830_;
}
}
lean_object* l_Lake_MainM_instMonadError___lam__0(lean_object* v_00_u03b1_831_, lean_object* v_msg_832_){
_start:
{
uint8_t v___x_834_; uint8_t v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_834_ = 1;
v___x_835_ = 0;
v___x_836_ = lean_box(1);
v___x_837_ = 3;
v___x_838_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_838_, 0, v_msg_832_);
lean_ctor_set_uint8(v___x_838_, sizeof(void*)*1, v___x_837_);
v___x_839_ = l_Lake_OutStream_logEntry(v___x_836_, v___x_838_, v___x_834_, v___x_835_);
lean_dec_ref_known(v___x_838_, 1);
v___x_840_ = l_Lake_MainM_failure___redArg___boxed__const__1;
v___x_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
}
LEAN_EXPORT void l_Lake_MainM_instMonadError___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_832_ = stack[1].m_obj;
lean_object* v_res_842_;
v_res_842_ = l_Lake_MainM_instMonadError___lam__0(lean_box(0), v_msg_832_);
stack->m_obj
 = v_res_842_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadError___lam__0___boxed(lean_object* v_00_u03b1_843_, lean_object* v_msg_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lake_MainM_instMonadError___lam__0(v_00_u03b1_843_, v_msg_844_);
return v_res_846_;
}
}
lean_object* l_Lake_MainM_instMonadLiftIO___lam__0(lean_object* v_00_u03b1_849_, lean_object* v___y_850_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = lean_apply_1(v___y_850_, lean_box(0));
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_852_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_852_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_876_; 
v_a_861_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_876_ == 0)
{
v___x_863_ = v___x_852_;
v_isShared_864_ = v_isSharedCheck_876_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_852_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_876_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; uint8_t v___x_866_; uint8_t v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_865_ = lean_io_error_to_string(v_a_861_);
v___x_866_ = 1;
v___x_867_ = 0;
v___x_868_ = lean_box(1);
v___x_869_ = 3;
v___x_870_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_870_, 0, v___x_865_);
lean_ctor_set_uint8(v___x_870_, sizeof(void*)*1, v___x_869_);
v___x_871_ = l_Lake_OutStream_logEntry(v___x_868_, v___x_870_, v___x_866_, v___x_867_);
lean_dec_ref_known(v___x_870_, 1);
v___x_872_ = l_Lake_MainM_failure___redArg___boxed__const__1;
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_872_);
v___x_874_ = v___x_863_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_872_);
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
LEAN_EXPORT void l_Lake_MainM_instMonadLiftIO___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_850_ = stack[1].m_obj;
lean_object* v_res_877_;
v_res_877_ = l_Lake_MainM_instMonadLiftIO___lam__0(lean_box(0), v___y_850_);
stack->m_obj
 = v_res_877_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadLiftIO___lam__0___boxed(lean_object* v_00_u03b1_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lake_MainM_instMonadLiftIO___lam__0(v_00_u03b1_878_, v___y_879_);
return v_res_881_;
}
}
lean_object* l_Lake_MainM_runLogIO___redArg___lam__0(lean_object* v_val_884_, uint8_t v___y_885_, uint8_t v_val_886_, lean_object* v_x_887_, lean_object* v___y_888_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Lake_logToStream(v___y_888_, v_val_884_, v___y_885_, v_val_886_);
return v___x_890_;
}
}
LEAN_EXPORT void l_Lake_MainM_runLogIO___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_884_ = stack[0].m_obj;
uint8_t v___y_885_ = stack[1].m_num;
uint8_t v_val_886_ = stack[2].m_num;
lean_object* v_x_887_ = stack[3].m_obj;
lean_object* v___y_888_ = stack[4].m_obj;
lean_object* v_res_891_;
v_res_891_ = l_Lake_MainM_runLogIO___redArg___lam__0(v_val_884_, v___y_885_, v_val_886_, v_x_887_, v___y_888_);
stack->m_obj
 = v_res_891_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO___redArg___lam__0___boxed(lean_object* v_val_892_, lean_object* v___y_893_, lean_object* v_val_894_, lean_object* v_x_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
uint8_t v___y_383__boxed_898_; uint8_t v_val_384__boxed_899_; lean_object* v_res_900_; 
v___y_383__boxed_898_ = lean_unbox(v___y_893_);
v_val_384__boxed_899_ = lean_unbox(v_val_894_);
v_res_900_ = l_Lake_MainM_runLogIO___redArg___lam__0(v_val_892_, v___y_383__boxed_898_, v_val_384__boxed_899_, v_x_895_, v___y_896_);
lean_dec_ref(v___y_896_);
return v_res_900_;
}
}
lean_object* l_Lake_MainM_runLogIO___redArg(lean_object* v_x_903_, lean_object* v_cfg_904_){
_start:
{
uint8_t v___y_910_; lean_object* v___y_911_; lean_object* v___x_920_; uint8_t v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; uint8_t v___y_925_; lean_object* v___y_942_; lean_object* v___y_943_; uint8_t v___y_944_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_920_ = l_instMonadBaseIO;
v___x_946_ = ((lean_object*)(l_Lake_MainM_runLogIO___redArg___closed__0));
v___x_947_ = lean_apply_2(v_x_903_, v___x_946_, lean_box(0));
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; lean_object* v_a_949_; uint8_t v_failLv_950_; uint8_t v_outLv_951_; lean_object* v___x_952_; uint8_t v___x_953_; uint8_t v___x_954_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_a_948_);
v_a_949_ = lean_ctor_get(v___x_947_, 1);
lean_inc(v_a_949_);
lean_dec_ref_known(v___x_947_, 2);
v_failLv_950_ = lean_ctor_get_uint8(v_cfg_904_, sizeof(void*)*1);
v_outLv_951_ = lean_ctor_get_uint8(v_cfg_904_, sizeof(void*)*1 + 1);
v___x_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_952_, 0, v_a_948_);
v___x_953_ = l_Lake_Log_maxLv(v_a_949_);
v___x_954_ = l_Lake_instOrdLogLevel_ord(v_failLv_950_, v___x_953_);
if (v___x_954_ == 2)
{
uint8_t v___x_955_; 
v___x_955_ = 0;
v___y_922_ = v___x_955_;
v___y_923_ = v___x_952_;
v___y_924_ = v_a_949_;
v___y_925_ = v_outLv_951_;
goto v___jp_921_;
}
else
{
uint8_t v___x_956_; 
v___x_956_ = 1;
v___y_942_ = v___x_952_;
v___y_943_ = v_a_949_;
v___y_944_ = v___x_956_;
goto v___jp_941_;
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v_a_957_ = lean_ctor_get(v___x_947_, 1);
lean_inc(v_a_957_);
lean_dec_ref_known(v___x_947_, 2);
v___x_958_ = lean_box(0);
v___x_959_ = 1;
v___y_942_ = v___x_958_;
v___y_943_ = v_a_957_;
v___y_944_ = v___x_959_;
goto v___jp_941_;
}
v___jp_906_:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = l_Lake_MainM_failure___redArg___boxed__const__1;
v___x_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
return v___x_908_;
}
v___jp_909_:
{
if (v___y_910_ == 0)
{
if (lean_obj_tag(v___y_911_) == 0)
{
goto v___jp_906_;
}
else
{
lean_object* v_val_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
v_val_912_ = lean_ctor_get(v___y_911_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___y_911_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___y_911_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_val_912_);
lean_dec(v___y_911_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
lean_ctor_set_tag(v___x_914_, 0);
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_val_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
else
{
lean_dec(v___y_911_);
goto v___jp_906_;
}
}
v___jp_921_:
{
uint8_t v_ansiMode_926_; lean_object* v_out_927_; lean_object* v___x_928_; uint8_t v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; uint8_t v___x_932_; 
v_ansiMode_926_ = lean_ctor_get_uint8(v_cfg_904_, sizeof(void*)*1 + 2);
v_out_927_ = lean_ctor_get(v_cfg_904_, 0);
v___x_928_ = l_Lake_OutStream_get(v_out_927_);
lean_inc_ref(v___x_928_);
v___x_929_ = l_Lake_AnsiMode_isEnabled(v___x_928_, v_ansiMode_926_);
v___x_930_ = lean_unsigned_to_nat(0u);
v___x_931_ = lean_array_get_size(v___y_924_);
v___x_932_ = lean_nat_dec_lt(v___x_930_, v___x_931_);
if (v___x_932_ == 0)
{
lean_dec_ref(v___x_928_);
lean_dec_ref(v___y_924_);
v___y_910_ = v___y_922_;
v___y_911_ = v___y_923_;
goto v___jp_909_;
}
else
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___f_935_; lean_object* v___x_936_; size_t v___x_937_; size_t v___x_938_; lean_object* v___x_130__overap_939_; lean_object* v___x_940_; 
v___x_933_ = lean_box(v___y_925_);
v___x_934_ = lean_box(v___x_929_);
v___f_935_ = lean_alloc_closure((void*)(l_Lake_MainM_runLogIO___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_935_, 0, v___x_928_);
lean_closure_set(v___f_935_, 1, v___x_933_);
lean_closure_set(v___f_935_, 2, v___x_934_);
v___x_936_ = lean_box(0);
v___x_937_ = ((size_t)0ULL);
v___x_938_ = lean_usize_of_nat(v___x_931_);
v___x_130__overap_939_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_920_, v___f_935_, v___y_924_, v___x_937_, v___x_938_, v___x_936_);
v___x_940_ = lean_apply_1(v___x_130__overap_939_, lean_box(0));
v___y_910_ = v___y_922_;
v___y_911_ = v___y_923_;
goto v___jp_909_;
}
}
v___jp_941_:
{
uint8_t v___x_945_; 
v___x_945_ = 0;
v___y_922_ = v___y_944_;
v___y_923_ = v___y_942_;
v___y_924_ = v___y_943_;
v___y_925_ = v___x_945_;
goto v___jp_921_;
}
}
}
LEAN_EXPORT void l_Lake_MainM_runLogIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_903_ = stack[0].m_obj;
lean_object* v_cfg_904_ = stack[1].m_obj;
lean_object* v_res_960_;
v_res_960_ = l_Lake_MainM_runLogIO___redArg(v_x_903_, v_cfg_904_);
stack->m_obj
 = v_res_960_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO___redArg___boxed(lean_object* v_x_961_, lean_object* v_cfg_962_, lean_object* v_a_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lake_MainM_runLogIO___redArg(v_x_961_, v_cfg_962_);
lean_dec_ref(v_cfg_962_);
return v_res_964_;
}
}
lean_object* l_Lake_MainM_runLogIO(lean_object* v_00_u03b1_965_, lean_object* v_x_966_, lean_object* v_cfg_967_){
_start:
{
uint8_t v___y_973_; lean_object* v___y_974_; lean_object* v___x_983_; uint8_t v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; uint8_t v___y_988_; lean_object* v___y_1005_; lean_object* v___y_1006_; uint8_t v___y_1007_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_983_ = l_instMonadBaseIO;
v___x_1009_ = ((lean_object*)(l_Lake_MainM_runLogIO___redArg___closed__0));
v___x_1010_ = lean_apply_2(v_x_966_, v___x_1009_, lean_box(0));
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v_a_1012_; uint8_t v_failLv_1013_; uint8_t v_outLv_1014_; lean_object* v___x_1015_; uint8_t v___x_1016_; uint8_t v___x_1017_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
v_a_1012_ = lean_ctor_get(v___x_1010_, 1);
lean_inc(v_a_1012_);
lean_dec_ref_known(v___x_1010_, 2);
v_failLv_1013_ = lean_ctor_get_uint8(v_cfg_967_, sizeof(void*)*1);
v_outLv_1014_ = lean_ctor_get_uint8(v_cfg_967_, sizeof(void*)*1 + 1);
v___x_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1015_, 0, v_a_1011_);
v___x_1016_ = l_Lake_Log_maxLv(v_a_1012_);
v___x_1017_ = l_Lake_instOrdLogLevel_ord(v_failLv_1013_, v___x_1016_);
if (v___x_1017_ == 2)
{
uint8_t v___x_1018_; 
v___x_1018_ = 0;
v___y_985_ = v___x_1018_;
v___y_986_ = v___x_1015_;
v___y_987_ = v_a_1012_;
v___y_988_ = v_outLv_1014_;
goto v___jp_984_;
}
else
{
uint8_t v___x_1019_; 
v___x_1019_ = 1;
v___y_1005_ = v___x_1015_;
v___y_1006_ = v_a_1012_;
v___y_1007_ = v___x_1019_;
goto v___jp_1004_;
}
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; 
v_a_1020_ = lean_ctor_get(v___x_1010_, 1);
lean_inc(v_a_1020_);
lean_dec_ref_known(v___x_1010_, 2);
v___x_1021_ = lean_box(0);
v___x_1022_ = 1;
v___y_1005_ = v___x_1021_;
v___y_1006_ = v_a_1020_;
v___y_1007_ = v___x_1022_;
goto v___jp_1004_;
}
v___jp_969_:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = l_Lake_MainM_failure___redArg___boxed__const__1;
v___x_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
return v___x_971_;
}
v___jp_972_:
{
if (v___y_973_ == 0)
{
if (lean_obj_tag(v___y_974_) == 0)
{
goto v___jp_969_;
}
else
{
lean_object* v_val_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
v_val_975_ = lean_ctor_get(v___y_974_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___y_974_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___y_974_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_val_975_);
lean_dec(v___y_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
lean_ctor_set_tag(v___x_977_, 0);
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_val_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
else
{
lean_dec(v___y_974_);
goto v___jp_969_;
}
}
v___jp_984_:
{
uint8_t v_ansiMode_989_; lean_object* v_out_990_; lean_object* v___x_991_; uint8_t v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
v_ansiMode_989_ = lean_ctor_get_uint8(v_cfg_967_, sizeof(void*)*1 + 2);
v_out_990_ = lean_ctor_get(v_cfg_967_, 0);
v___x_991_ = l_Lake_OutStream_get(v_out_990_);
lean_inc_ref(v___x_991_);
v___x_992_ = l_Lake_AnsiMode_isEnabled(v___x_991_, v_ansiMode_989_);
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = lean_array_get_size(v___y_987_);
v___x_995_ = lean_nat_dec_lt(v___x_993_, v___x_994_);
if (v___x_995_ == 0)
{
lean_dec_ref(v___x_991_);
lean_dec_ref(v___y_987_);
v___y_973_ = v___y_985_;
v___y_974_ = v___y_986_;
goto v___jp_972_;
}
else
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___f_998_; lean_object* v___x_999_; size_t v___x_1000_; size_t v___x_1001_; lean_object* v___x_308__overap_1002_; lean_object* v___x_1003_; 
v___x_996_ = lean_box(v___y_988_);
v___x_997_ = lean_box(v___x_992_);
v___f_998_ = lean_alloc_closure((void*)(l_Lake_MainM_runLogIO___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_998_, 0, v___x_991_);
lean_closure_set(v___f_998_, 1, v___x_996_);
lean_closure_set(v___f_998_, 2, v___x_997_);
v___x_999_ = lean_box(0);
v___x_1000_ = ((size_t)0ULL);
v___x_1001_ = lean_usize_of_nat(v___x_994_);
v___x_308__overap_1002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_983_, v___f_998_, v___y_987_, v___x_1000_, v___x_1001_, v___x_999_);
v___x_1003_ = lean_apply_1(v___x_308__overap_1002_, lean_box(0));
v___y_973_ = v___y_985_;
v___y_974_ = v___y_986_;
goto v___jp_972_;
}
}
v___jp_1004_:
{
uint8_t v___x_1008_; 
v___x_1008_ = 0;
v___y_985_ = v___y_1007_;
v___y_986_ = v___y_1005_;
v___y_987_ = v___y_1006_;
v___y_988_ = v___x_1008_;
goto v___jp_984_;
}
}
}
LEAN_EXPORT void l_Lake_MainM_runLogIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_966_ = stack[1].m_obj;
lean_object* v_cfg_967_ = stack[2].m_obj;
lean_object* v_res_1023_;
v_res_1023_ = l_Lake_MainM_runLogIO(lean_box(0), v_x_966_, v_cfg_967_);
stack->m_obj
 = v_res_1023_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO___boxed(lean_object* v_00_u03b1_1024_, lean_object* v_x_1025_, lean_object* v_cfg_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lake_MainM_runLogIO(v_00_u03b1_1024_, v_x_1025_, v_cfg_1026_);
lean_dec_ref(v_cfg_1026_);
return v_res_1028_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0(lean_object* v_val_1029_, uint8_t v___y_1030_, uint8_t v_val_1031_, lean_object* v_as_1032_, size_t v_i_1033_, size_t v_stop_1034_, lean_object* v_b_1035_){
_start:
{
uint8_t v___x_1037_; 
v___x_1037_ = lean_usize_dec_eq(v_i_1033_, v_stop_1034_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; lean_object* v___x_1039_; size_t v___x_1040_; size_t v___x_1041_; 
v___x_1038_ = lean_array_uget_borrowed(v_as_1032_, v_i_1033_);
lean_inc_ref(v_val_1029_);
v___x_1039_ = l_Lake_logToStream(v___x_1038_, v_val_1029_, v___y_1030_, v_val_1031_);
v___x_1040_ = ((size_t)1ULL);
v___x_1041_ = lean_usize_add(v_i_1033_, v___x_1040_);
v_i_1033_ = v___x_1041_;
v_b_1035_ = v___x_1039_;
goto _start;
}
else
{
lean_dec_ref(v_val_1029_);
return v_b_1035_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1029_ = stack[0].m_obj;
uint8_t v___y_1030_ = stack[1].m_num;
uint8_t v_val_1031_ = stack[2].m_num;
lean_object* v_as_1032_ = stack[3].m_obj;
size_t v_i_1033_ = stack[4].m_num;
size_t v_stop_1034_ = stack[5].m_num;
lean_object* v_b_1035_ = stack[6].m_obj;
lean_object* v_res_1043_;
v_res_1043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0(v_val_1029_, v___y_1030_, v_val_1031_, v_as_1032_, v_i_1033_, v_stop_1034_, v_b_1035_);
stack->m_obj
 = v_res_1043_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0___boxed(lean_object* v_val_1044_, lean_object* v___y_1045_, lean_object* v_val_1046_, lean_object* v_as_1047_, lean_object* v_i_1048_, lean_object* v_stop_1049_, lean_object* v_b_1050_, lean_object* v___y_1051_){
_start:
{
uint8_t v___y_251__boxed_1052_; uint8_t v_val_252__boxed_1053_; size_t v_i_boxed_1054_; size_t v_stop_boxed_1055_; lean_object* v_res_1056_; 
v___y_251__boxed_1052_ = lean_unbox(v___y_1045_);
v_val_252__boxed_1053_ = lean_unbox(v_val_1046_);
v_i_boxed_1054_ = lean_unbox_usize(v_i_1048_);
lean_dec(v_i_1048_);
v_stop_boxed_1055_ = lean_unbox_usize(v_stop_1049_);
lean_dec(v_stop_1049_);
v_res_1056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0(v_val_1044_, v___y_251__boxed_1052_, v_val_252__boxed_1053_, v_as_1047_, v_i_boxed_1054_, v_stop_boxed_1055_, v_b_1050_);
lean_dec_ref(v_as_1047_);
return v_res_1056_;
}
}
lean_object* l_Lake_MainM_liftLogIO___redArg(lean_object* v_x_1057_){
_start:
{
uint8_t v___y_1063_; lean_object* v___y_1064_; uint8_t v___x_1073_; uint8_t v___x_1074_; uint8_t v___x_1075_; lean_object* v___x_1076_; lean_object* v___y_1078_; uint8_t v___y_1079_; lean_object* v___y_1080_; uint8_t v___y_1081_; lean_object* v___y_1092_; lean_object* v___y_1093_; uint8_t v___y_1094_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1073_ = 3;
v___x_1074_ = 1;
v___x_1075_ = 0;
v___x_1076_ = lean_box(1);
v___x_1096_ = ((lean_object*)(l_Lake_MainM_runLogIO___redArg___closed__0));
v___x_1097_ = lean_apply_2(v_x_1057_, v___x_1096_, lean_box(0));
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v_a_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; uint8_t v___x_1102_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_a_1098_);
v_a_1099_ = lean_ctor_get(v___x_1097_, 1);
lean_inc(v_a_1099_);
lean_dec_ref_known(v___x_1097_, 2);
v___x_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1100_, 0, v_a_1098_);
v___x_1101_ = l_Lake_Log_maxLv(v_a_1099_);
v___x_1102_ = l_Lake_instOrdLogLevel_ord(v___x_1073_, v___x_1101_);
if (v___x_1102_ == 2)
{
uint8_t v___x_1103_; 
v___x_1103_ = 0;
v___y_1078_ = v_a_1099_;
v___y_1079_ = v___x_1103_;
v___y_1080_ = v___x_1100_;
v___y_1081_ = v___x_1074_;
goto v___jp_1077_;
}
else
{
uint8_t v___x_1104_; 
v___x_1104_ = 1;
v___y_1092_ = v_a_1099_;
v___y_1093_ = v___x_1100_;
v___y_1094_ = v___x_1104_;
goto v___jp_1091_;
}
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; 
v_a_1105_ = lean_ctor_get(v___x_1097_, 1);
lean_inc(v_a_1105_);
lean_dec_ref_known(v___x_1097_, 2);
v___x_1106_ = lean_box(0);
v___x_1107_ = 1;
v___y_1092_ = v_a_1105_;
v___y_1093_ = v___x_1106_;
v___y_1094_ = v___x_1107_;
goto v___jp_1091_;
}
v___jp_1059_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = l_Lake_MainM_failure___redArg___boxed__const__1;
v___x_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
return v___x_1061_;
}
v___jp_1062_:
{
if (v___y_1063_ == 0)
{
if (lean_obj_tag(v___y_1064_) == 0)
{
goto v___jp_1059_;
}
else
{
lean_object* v_val_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
v_val_1065_ = lean_ctor_get(v___y_1064_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___y_1064_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___y_1064_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_val_1065_);
lean_dec(v___y_1064_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
lean_ctor_set_tag(v___x_1067_, 0);
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_val_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
else
{
lean_dec(v___y_1064_);
goto v___jp_1059_;
}
}
v___jp_1077_:
{
lean_object* v___x_1082_; uint8_t v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
v___x_1082_ = l_Lake_OutStream_get(v___x_1076_);
lean_inc_ref(v___x_1082_);
v___x_1083_ = l_Lake_AnsiMode_isEnabled(v___x_1082_, v___x_1075_);
v___x_1084_ = lean_unsigned_to_nat(0u);
v___x_1085_ = lean_array_get_size(v___y_1078_);
v___x_1086_ = lean_nat_dec_lt(v___x_1084_, v___x_1085_);
if (v___x_1086_ == 0)
{
lean_dec_ref(v___x_1082_);
lean_dec_ref(v___y_1078_);
v___y_1063_ = v___y_1079_;
v___y_1064_ = v___y_1080_;
goto v___jp_1062_;
}
else
{
lean_object* v___x_1087_; size_t v___x_1088_; size_t v___x_1089_; lean_object* v___x_1090_; 
v___x_1087_ = lean_box(0);
v___x_1088_ = ((size_t)0ULL);
v___x_1089_ = lean_usize_of_nat(v___x_1085_);
v___x_1090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0(v___x_1082_, v___y_1081_, v___x_1083_, v___y_1078_, v___x_1088_, v___x_1089_, v___x_1087_);
lean_dec_ref(v___y_1078_);
v___y_1063_ = v___y_1079_;
v___y_1064_ = v___y_1080_;
goto v___jp_1062_;
}
}
v___jp_1091_:
{
uint8_t v___x_1095_; 
v___x_1095_ = 0;
v___y_1078_ = v___y_1092_;
v___y_1079_ = v___y_1094_;
v___y_1080_ = v___y_1093_;
v___y_1081_ = v___x_1095_;
goto v___jp_1077_;
}
}
}
LEAN_EXPORT void l_Lake_MainM_liftLogIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1057_ = stack[0].m_obj;
lean_object* v_res_1108_;
v_res_1108_ = l_Lake_MainM_liftLogIO___redArg(v_x_1057_);
stack->m_obj
 = v_res_1108_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_liftLogIO___redArg___boxed(lean_object* v_x_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lake_MainM_liftLogIO___redArg(v_x_1109_);
return v_res_1111_;
}
}
lean_object* l_Lake_MainM_liftLogIO(lean_object* v_00_u03b1_1112_, lean_object* v_x_1113_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Lake_MainM_liftLogIO___redArg(v_x_1113_);
return v___x_1115_;
}
}
LEAN_EXPORT void l_Lake_MainM_liftLogIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1113_ = stack[1].m_obj;
lean_object* v_res_1116_;
v_res_1116_ = l_Lake_MainM_liftLogIO(lean_box(0), v_x_1113_);
stack->m_obj
 = v_res_1116_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_liftLogIO___boxed(lean_object* v_00_u03b1_1117_, lean_object* v_x_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lake_MainM_liftLogIO(v_00_u03b1_1117_, v_x_1118_);
return v_res_1120_;
}
}
lean_object* l_Lake_MainM_runLoggerIO___redArg___lam__0(lean_object* v_val_1123_, uint8_t v_outLv_1124_, uint8_t v_val_1125_, lean_object* v_e_1126_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lake_logToStream(v_e_1126_, v_val_1123_, v_outLv_1124_, v_val_1125_);
return v___x_1128_;
}
}
LEAN_EXPORT void l_Lake_MainM_runLoggerIO___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1123_ = stack[0].m_obj;
uint8_t v_outLv_1124_ = stack[1].m_num;
uint8_t v_val_1125_ = stack[2].m_num;
lean_object* v_e_1126_ = stack[3].m_obj;
lean_object* v_res_1129_;
v_res_1129_ = l_Lake_MainM_runLoggerIO___redArg___lam__0(v_val_1123_, v_outLv_1124_, v_val_1125_, v_e_1126_);
stack->m_obj
 = v_res_1129_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO___redArg___lam__0___boxed(lean_object* v_val_1130_, lean_object* v_outLv_1131_, lean_object* v_val_1132_, lean_object* v_e_1133_, lean_object* v___y_1134_){
_start:
{
uint8_t v_outLv_boxed_1135_; uint8_t v_val_188__boxed_1136_; lean_object* v_res_1137_; 
v_outLv_boxed_1135_ = lean_unbox(v_outLv_1131_);
v_val_188__boxed_1136_ = lean_unbox(v_val_1132_);
v_res_1137_ = l_Lake_MainM_runLoggerIO___redArg___lam__0(v_val_1130_, v_outLv_boxed_1135_, v_val_188__boxed_1136_, v_e_1133_);
lean_dec_ref(v_e_1133_);
return v_res_1137_;
}
}
lean_object* l_Lake_MainM_runLoggerIO___redArg(lean_object* v_x_1138_, lean_object* v_cfg_1139_){
_start:
{
uint8_t v_outLv_1141_; uint8_t v_ansiMode_1142_; lean_object* v_out_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___f_1148_; lean_object* v___x_1149_; 
v_outLv_1141_ = lean_ctor_get_uint8(v_cfg_1139_, sizeof(void*)*1 + 1);
v_ansiMode_1142_ = lean_ctor_get_uint8(v_cfg_1139_, sizeof(void*)*1 + 2);
v_out_1143_ = lean_ctor_get(v_cfg_1139_, 0);
v___x_1144_ = l_Lake_OutStream_get(v_out_1143_);
lean_inc_ref(v___x_1144_);
v___x_1145_ = l_Lake_AnsiMode_isEnabled(v___x_1144_, v_ansiMode_1142_);
v___x_1146_ = lean_box(v_outLv_1141_);
v___x_1147_ = lean_box(v___x_1145_);
v___f_1148_ = lean_alloc_closure((void*)(l_Lake_MainM_runLoggerIO___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1148_, 0, v___x_1144_);
lean_closure_set(v___f_1148_, 1, v___x_1146_);
lean_closure_set(v___f_1148_, 2, v___x_1147_);
v___x_1149_ = lean_apply_2(v_x_1138_, v___f_1148_, lean_box(0));
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
else
{
lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1165_; 
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1165_ == 0)
{
lean_object* v_unused_1166_; 
v_unused_1166_ = lean_ctor_get(v___x_1149_, 0);
lean_dec(v_unused_1166_);
v___x_1159_ = v___x_1149_;
v_isShared_1160_ = v_isSharedCheck_1165_;
goto v_resetjp_1158_;
}
else
{
lean_dec(v___x_1149_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1165_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1161_ = l_Lake_MainM_failure___redArg___boxed__const__1;
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1161_);
v___x_1163_ = v___x_1159_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1161_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_MainM_runLoggerIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1138_ = stack[0].m_obj;
lean_object* v_cfg_1139_ = stack[1].m_obj;
lean_object* v_res_1167_;
v_res_1167_ = l_Lake_MainM_runLoggerIO___redArg(v_x_1138_, v_cfg_1139_);
stack->m_obj
 = v_res_1167_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO___redArg___boxed(lean_object* v_x_1168_, lean_object* v_cfg_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lake_MainM_runLoggerIO___redArg(v_x_1168_, v_cfg_1169_);
lean_dec_ref(v_cfg_1169_);
return v_res_1171_;
}
}
lean_object* l_Lake_MainM_runLoggerIO(lean_object* v_00_u03b1_1172_, lean_object* v_x_1173_, lean_object* v_cfg_1174_){
_start:
{
uint8_t v_outLv_1176_; uint8_t v_ansiMode_1177_; lean_object* v_out_1178_; lean_object* v___x_1179_; uint8_t v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___f_1183_; lean_object* v___x_1184_; 
v_outLv_1176_ = lean_ctor_get_uint8(v_cfg_1174_, sizeof(void*)*1 + 1);
v_ansiMode_1177_ = lean_ctor_get_uint8(v_cfg_1174_, sizeof(void*)*1 + 2);
v_out_1178_ = lean_ctor_get(v_cfg_1174_, 0);
v___x_1179_ = l_Lake_OutStream_get(v_out_1178_);
lean_inc_ref(v___x_1179_);
v___x_1180_ = l_Lake_AnsiMode_isEnabled(v___x_1179_, v_ansiMode_1177_);
v___x_1181_ = lean_box(v_outLv_1176_);
v___x_1182_ = lean_box(v___x_1180_);
v___f_1183_ = lean_alloc_closure((void*)(l_Lake_MainM_runLoggerIO___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1183_, 0, v___x_1179_);
lean_closure_set(v___f_1183_, 1, v___x_1181_);
lean_closure_set(v___f_1183_, 2, v___x_1182_);
v___x_1184_ = lean_apply_2(v_x_1173_, v___f_1183_, lean_box(0));
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1184_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1184_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
else
{
lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1200_; 
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1200_ == 0)
{
lean_object* v_unused_1201_; 
v_unused_1201_ = lean_ctor_get(v___x_1184_, 0);
lean_dec(v_unused_1201_);
v___x_1194_ = v___x_1184_;
v_isShared_1195_ = v_isSharedCheck_1200_;
goto v_resetjp_1193_;
}
else
{
lean_dec(v___x_1184_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1200_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; lean_object* v___x_1198_; 
v___x_1196_ = l_Lake_MainM_failure___redArg___boxed__const__1;
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1196_);
v___x_1198_ = v___x_1194_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_MainM_runLoggerIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1173_ = stack[1].m_obj;
lean_object* v_cfg_1174_ = stack[2].m_obj;
lean_object* v_res_1202_;
v_res_1202_ = l_Lake_MainM_runLoggerIO(lean_box(0), v_x_1173_, v_cfg_1174_);
stack->m_obj
 = v_res_1202_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO___boxed(lean_object* v_00_u03b1_1203_, lean_object* v_x_1204_, lean_object* v_cfg_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lake_MainM_runLoggerIO(v_00_u03b1_1203_, v_x_1204_, v_cfg_1205_);
lean_dec_ref(v_cfg_1205_);
return v_res_1207_;
}
}
lean_object* l_Lake_MainM_liftLoggerIO___redArg___lam__0(lean_object* v_val_1208_, uint8_t v___x_1209_, uint8_t v_val_1210_, lean_object* v_e_1211_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_Lake_logToStream(v_e_1211_, v_val_1208_, v___x_1209_, v_val_1210_);
return v___x_1213_;
}
}
LEAN_EXPORT void l_Lake_MainM_liftLoggerIO___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1208_ = stack[0].m_obj;
uint8_t v___x_1209_ = stack[1].m_num;
uint8_t v_val_1210_ = stack[2].m_num;
lean_object* v_e_1211_ = stack[3].m_obj;
lean_object* v_res_1214_;
v_res_1214_ = l_Lake_MainM_liftLoggerIO___redArg___lam__0(v_val_1208_, v___x_1209_, v_val_1210_, v_e_1211_);
stack->m_obj
 = v_res_1214_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO___redArg___lam__0___boxed(lean_object* v_val_1215_, lean_object* v___x_1216_, lean_object* v_val_1217_, lean_object* v_e_1218_, lean_object* v___y_1219_){
_start:
{
uint8_t v___x_38__boxed_1220_; uint8_t v_val_39__boxed_1221_; lean_object* v_res_1222_; 
v___x_38__boxed_1220_ = lean_unbox(v___x_1216_);
v_val_39__boxed_1221_ = lean_unbox(v_val_1217_);
v_res_1222_ = l_Lake_MainM_liftLoggerIO___redArg___lam__0(v_val_1215_, v___x_38__boxed_1220_, v_val_39__boxed_1221_, v_e_1218_);
lean_dec_ref(v_e_1218_);
return v_res_1222_;
}
}
lean_object* l_Lake_MainM_liftLoggerIO___redArg(lean_object* v_x_1223_){
_start:
{
uint8_t v___x_1225_; uint8_t v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___f_1232_; lean_object* v___x_1233_; 
v___x_1225_ = 1;
v___x_1226_ = 0;
v___x_1227_ = lean_box(1);
v___x_1228_ = l_Lake_OutStream_get(v___x_1227_);
lean_inc_ref(v___x_1228_);
v___x_1229_ = l_Lake_AnsiMode_isEnabled(v___x_1228_, v___x_1226_);
v___x_1230_ = lean_box(v___x_1225_);
v___x_1231_ = lean_box(v___x_1229_);
v___f_1232_ = lean_alloc_closure((void*)(l_Lake_MainM_liftLoggerIO___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1232_, 0, v___x_1228_);
lean_closure_set(v___f_1232_, 1, v___x_1230_);
lean_closure_set(v___f_1232_, 2, v___x_1231_);
v___x_1233_ = lean_apply_2(v_x_1223_, v___f_1232_, lean_box(0));
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1233_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1233_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
else
{
lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1249_; 
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1249_ == 0)
{
lean_object* v_unused_1250_; 
v_unused_1250_ = lean_ctor_get(v___x_1233_, 0);
lean_dec(v_unused_1250_);
v___x_1243_ = v___x_1233_;
v_isShared_1244_ = v_isSharedCheck_1249_;
goto v_resetjp_1242_;
}
else
{
lean_dec(v___x_1233_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1249_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; lean_object* v___x_1247_; 
v___x_1245_ = l_Lake_MainM_failure___redArg___boxed__const__1;
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v___x_1245_);
v___x_1247_ = v___x_1243_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1245_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_MainM_liftLoggerIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1223_ = stack[0].m_obj;
lean_object* v_res_1251_;
v_res_1251_ = l_Lake_MainM_liftLoggerIO___redArg(v_x_1223_);
stack->m_obj
 = v_res_1251_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO___redArg___boxed(lean_object* v_x_1252_, lean_object* v_a_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lake_MainM_liftLoggerIO___redArg(v_x_1252_);
return v_res_1254_;
}
}
lean_object* l_Lake_MainM_liftLoggerIO(lean_object* v_00_u03b1_1255_, lean_object* v_x_1256_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lake_MainM_liftLoggerIO___redArg(v_x_1256_);
return v___x_1258_;
}
}
LEAN_EXPORT void l_Lake_MainM_liftLoggerIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1256_ = stack[1].m_obj;
lean_object* v_res_1259_;
v_res_1259_ = l_Lake_MainM_liftLoggerIO(lean_box(0), v_x_1256_);
stack->m_obj
 = v_res_1259_;
}
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO___boxed(lean_object* v_00_u03b1_1260_, lean_object* v_x_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lake_MainM_liftLoggerIO(v_00_u03b1_1260_, v_x_1261_);
return v_res_1263_;
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
