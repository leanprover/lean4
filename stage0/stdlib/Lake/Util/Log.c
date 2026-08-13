// Lean compiler output
// Module: Lake.Util.Log
// Imports: public import Lean.Data.Json public import Lake.Util.Error public import Lake.Util.EStateT public import Lean.Message public import Lake.Util.Lift import Init.Data.String.TakeDrop import Init.Data.String.Modify
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
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Json_getTag_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*);
lean_object* l_Lean_mkErrorStringWithPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lake_EResult_result_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_get_stdout();
lean_object* lean_get_stderr();
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lake_EResult_toProd(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lake_EResult_toProd_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EResult_toExcept___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_IO_setStderr___boxed(lean_object*, lean_object*);
lean_object* l_IO_setStdout___boxed(lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* l_IO_mkRef___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
extern lean_object* l_instMonadBaseIO;
lean_object* lean_stream_of_handle(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Array_toJson___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Array_fromJson_x3f___redArg(lean_object*, lean_object*);
lean_object* l_instMonadStateOfStateTOfMonad___redArg(lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instFunctor___redArg(lean_object*);
lean_object* l_Lake_EStateT_instPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonadStateOfOfPure___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_quiet_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_quiet_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_quiet_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_quiet_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_normal_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_normal_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_normal_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_normal_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_verbose_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_verbose_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_verbose_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_verbose_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_instReprVerbosity_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.Verbosity.quiet"};
static const lean_object* l_Lake_instReprVerbosity_repr___closed__0 = (const lean_object*)&l_Lake_instReprVerbosity_repr___closed__0_value;
static const lean_ctor_object l_Lake_instReprVerbosity_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprVerbosity_repr___closed__0_value)}};
static const lean_object* l_Lake_instReprVerbosity_repr___closed__1 = (const lean_object*)&l_Lake_instReprVerbosity_repr___closed__1_value;
static const lean_string_object l_Lake_instReprVerbosity_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lake.Verbosity.normal"};
static const lean_object* l_Lake_instReprVerbosity_repr___closed__2 = (const lean_object*)&l_Lake_instReprVerbosity_repr___closed__2_value;
static const lean_ctor_object l_Lake_instReprVerbosity_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprVerbosity_repr___closed__2_value)}};
static const lean_object* l_Lake_instReprVerbosity_repr___closed__3 = (const lean_object*)&l_Lake_instReprVerbosity_repr___closed__3_value;
static const lean_string_object l_Lake_instReprVerbosity_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lake.Verbosity.verbose"};
static const lean_object* l_Lake_instReprVerbosity_repr___closed__4 = (const lean_object*)&l_Lake_instReprVerbosity_repr___closed__4_value;
static const lean_ctor_object l_Lake_instReprVerbosity_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprVerbosity_repr___closed__4_value)}};
static const lean_object* l_Lake_instReprVerbosity_repr___closed__5 = (const lean_object*)&l_Lake_instReprVerbosity_repr___closed__5_value;
static lean_once_cell_t l_Lake_instReprVerbosity_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprVerbosity_repr___closed__6;
static lean_once_cell_t l_Lake_instReprVerbosity_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprVerbosity_repr___closed__7;
LEAN_EXPORT lean_object* l_Lake_instReprVerbosity_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprVerbosity_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprVerbosity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprVerbosity_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprVerbosity___closed__0 = (const lean_object*)&l_Lake_instReprVerbosity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprVerbosity = (const lean_object*)&l_Lake_instReprVerbosity___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_Verbosity_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqVerbosity___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instOrdVerbosity_ord(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instOrdVerbosity_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instOrdVerbosity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instOrdVerbosity_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instOrdVerbosity___closed__0 = (const lean_object*)&l_Lake_instOrdVerbosity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instOrdVerbosity = (const lean_object*)&l_Lake_instOrdVerbosity___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instLTVerbosity;
LEAN_EXPORT lean_object* l_Lake_instLEVerbosity;
LEAN_EXPORT uint8_t l_Lake_instMinVerbosity___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instMinVerbosity___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMinVerbosity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMinVerbosity___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMinVerbosity___closed__0 = (const lean_object*)&l_Lake_instMinVerbosity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instMinVerbosity = (const lean_object*)&l_Lake_instMinVerbosity___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_instMaxVerbosity___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instMaxVerbosity___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMaxVerbosity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMaxVerbosity___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMaxVerbosity___closed__0 = (const lean_object*)&l_Lake_instMaxVerbosity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instMaxVerbosity = (const lean_object*)&l_Lake_instMaxVerbosity___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_instInhabitedVerbosity;
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_auto_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_auto_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_auto_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_auto_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ansi_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ansi_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ansi_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ansi_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noAnsi_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noAnsi_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noAnsi_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noAnsi_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_instReprAnsiMode_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lake.AnsiMode.auto"};
static const lean_object* l_Lake_instReprAnsiMode_repr___closed__0 = (const lean_object*)&l_Lake_instReprAnsiMode_repr___closed__0_value;
static const lean_ctor_object l_Lake_instReprAnsiMode_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprAnsiMode_repr___closed__0_value)}};
static const lean_object* l_Lake_instReprAnsiMode_repr___closed__1 = (const lean_object*)&l_Lake_instReprAnsiMode_repr___closed__1_value;
static const lean_string_object l_Lake_instReprAnsiMode_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lake.AnsiMode.ansi"};
static const lean_object* l_Lake_instReprAnsiMode_repr___closed__2 = (const lean_object*)&l_Lake_instReprAnsiMode_repr___closed__2_value;
static const lean_ctor_object l_Lake_instReprAnsiMode_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprAnsiMode_repr___closed__2_value)}};
static const lean_object* l_Lake_instReprAnsiMode_repr___closed__3 = (const lean_object*)&l_Lake_instReprAnsiMode_repr___closed__3_value;
static const lean_string_object l_Lake_instReprAnsiMode_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.AnsiMode.noAnsi"};
static const lean_object* l_Lake_instReprAnsiMode_repr___closed__4 = (const lean_object*)&l_Lake_instReprAnsiMode_repr___closed__4_value;
static const lean_ctor_object l_Lake_instReprAnsiMode_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprAnsiMode_repr___closed__4_value)}};
static const lean_object* l_Lake_instReprAnsiMode_repr___closed__5 = (const lean_object*)&l_Lake_instReprAnsiMode_repr___closed__5_value;
LEAN_EXPORT lean_object* l_Lake_instReprAnsiMode_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprAnsiMode_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprAnsiMode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprAnsiMode_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprAnsiMode___closed__0 = (const lean_object*)&l_Lake_instReprAnsiMode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprAnsiMode = (const lean_object*)&l_Lake_instReprAnsiMode___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_AnsiMode_isEnabled(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_isEnabled___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Ansi_chalk___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\033[1;"};
static const lean_object* l_Lake_Ansi_chalk___closed__0 = (const lean_object*)&l_Lake_Ansi_chalk___closed__0_value;
static const lean_string_object l_Lake_Ansi_chalk___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "m"};
static const lean_object* l_Lake_Ansi_chalk___closed__1 = (const lean_object*)&l_Lake_Ansi_chalk___closed__1_value;
static const lean_string_object l_Lake_Ansi_chalk___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "\033[m"};
static const lean_object* l_Lake_Ansi_chalk___closed__2 = (const lean_object*)&l_Lake_Ansi_chalk___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_Ansi_chalk(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Ansi_chalk___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_stdout_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_stdout_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_stderr_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_stderr_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_stream_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_stream_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_get(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeStreamOutStream___lam__0(lean_object*);
static const lean_closure_object l_Lake_instCoeStreamOutStream___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instCoeStreamOutStream___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instCoeStreamOutStream___closed__0 = (const lean_object*)&l_Lake_instCoeStreamOutStream___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instCoeStreamOutStream = (const lean_object*)&l_Lake_instCoeStreamOutStream___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instCoeHandleOutStream___lam__0(lean_object*);
static const lean_closure_object l_Lake_instCoeHandleOutStream___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instCoeHandleOutStream___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instCoeHandleOutStream___closed__0 = (const lean_object*)&l_Lake_instCoeHandleOutStream___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instCoeHandleOutStream = (const lean_object*)&l_Lake_instCoeHandleOutStream___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_trace_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_trace_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_trace_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_trace_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_info_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_info_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_info_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_info_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_warning_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_warning_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_warning_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_warning_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_error_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_error_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_error_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_error_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instInhabitedLogLevel_default;
LEAN_EXPORT uint8_t l_Lake_instInhabitedLogLevel;
static const lean_string_object l_Lake_instReprLogLevel_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lake.LogLevel.trace"};
static const lean_object* l_Lake_instReprLogLevel_repr___closed__0 = (const lean_object*)&l_Lake_instReprLogLevel_repr___closed__0_value;
static const lean_ctor_object l_Lake_instReprLogLevel_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLogLevel_repr___closed__0_value)}};
static const lean_object* l_Lake_instReprLogLevel_repr___closed__1 = (const lean_object*)&l_Lake_instReprLogLevel_repr___closed__1_value;
static const lean_string_object l_Lake_instReprLogLevel_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lake.LogLevel.info"};
static const lean_object* l_Lake_instReprLogLevel_repr___closed__2 = (const lean_object*)&l_Lake_instReprLogLevel_repr___closed__2_value;
static const lean_ctor_object l_Lake_instReprLogLevel_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLogLevel_repr___closed__2_value)}};
static const lean_object* l_Lake_instReprLogLevel_repr___closed__3 = (const lean_object*)&l_Lake_instReprLogLevel_repr___closed__3_value;
static const lean_string_object l_Lake_instReprLogLevel_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lake.LogLevel.warning"};
static const lean_object* l_Lake_instReprLogLevel_repr___closed__4 = (const lean_object*)&l_Lake_instReprLogLevel_repr___closed__4_value;
static const lean_ctor_object l_Lake_instReprLogLevel_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLogLevel_repr___closed__4_value)}};
static const lean_object* l_Lake_instReprLogLevel_repr___closed__5 = (const lean_object*)&l_Lake_instReprLogLevel_repr___closed__5_value;
static const lean_string_object l_Lake_instReprLogLevel_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lake.LogLevel.error"};
static const lean_object* l_Lake_instReprLogLevel_repr___closed__6 = (const lean_object*)&l_Lake_instReprLogLevel_repr___closed__6_value;
static const lean_ctor_object l_Lake_instReprLogLevel_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLogLevel_repr___closed__6_value)}};
static const lean_object* l_Lake_instReprLogLevel_repr___closed__7 = (const lean_object*)&l_Lake_instReprLogLevel_repr___closed__7_value;
LEAN_EXPORT lean_object* l_Lake_instReprLogLevel_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprLogLevel_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprLogLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprLogLevel_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprLogLevel___closed__0 = (const lean_object*)&l_Lake_instReprLogLevel___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprLogLevel = (const lean_object*)&l_Lake_instReprLogLevel___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_LogLevel_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqLogLevel(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqLogLevel___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instOrdLogLevel_ord(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instOrdLogLevel_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instOrdLogLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instOrdLogLevel_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instOrdLogLevel___closed__0 = (const lean_object*)&l_Lake_instOrdLogLevel___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instOrdLogLevel = (const lean_object*)&l_Lake_instOrdLogLevel___closed__0_value;
static const lean_string_object l_Lake_instToJsonLogLevel_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lake_instToJsonLogLevel_toJson___closed__0 = (const lean_object*)&l_Lake_instToJsonLogLevel_toJson___closed__0_value;
static const lean_ctor_object l_Lake_instToJsonLogLevel_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instToJsonLogLevel_toJson___closed__0_value)}};
static const lean_object* l_Lake_instToJsonLogLevel_toJson___closed__1 = (const lean_object*)&l_Lake_instToJsonLogLevel_toJson___closed__1_value;
static const lean_string_object l_Lake_instToJsonLogLevel_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "info"};
static const lean_object* l_Lake_instToJsonLogLevel_toJson___closed__2 = (const lean_object*)&l_Lake_instToJsonLogLevel_toJson___closed__2_value;
static const lean_ctor_object l_Lake_instToJsonLogLevel_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instToJsonLogLevel_toJson___closed__2_value)}};
static const lean_object* l_Lake_instToJsonLogLevel_toJson___closed__3 = (const lean_object*)&l_Lake_instToJsonLogLevel_toJson___closed__3_value;
static const lean_string_object l_Lake_instToJsonLogLevel_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "warning"};
static const lean_object* l_Lake_instToJsonLogLevel_toJson___closed__4 = (const lean_object*)&l_Lake_instToJsonLogLevel_toJson___closed__4_value;
static const lean_ctor_object l_Lake_instToJsonLogLevel_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instToJsonLogLevel_toJson___closed__4_value)}};
static const lean_object* l_Lake_instToJsonLogLevel_toJson___closed__5 = (const lean_object*)&l_Lake_instToJsonLogLevel_toJson___closed__5_value;
static const lean_string_object l_Lake_instToJsonLogLevel_toJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "error"};
static const lean_object* l_Lake_instToJsonLogLevel_toJson___closed__6 = (const lean_object*)&l_Lake_instToJsonLogLevel_toJson___closed__6_value;
static const lean_ctor_object l_Lake_instToJsonLogLevel_toJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instToJsonLogLevel_toJson___closed__6_value)}};
static const lean_object* l_Lake_instToJsonLogLevel_toJson___closed__7 = (const lean_object*)&l_Lake_instToJsonLogLevel_toJson___closed__7_value;
LEAN_EXPORT lean_object* l_Lake_instToJsonLogLevel_toJson(uint8_t);
LEAN_EXPORT lean_object* l_Lake_instToJsonLogLevel_toJson___boxed(lean_object*);
static const lean_closure_object l_Lake_instToJsonLogLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToJsonLogLevel_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToJsonLogLevel___closed__0 = (const lean_object*)&l_Lake_instToJsonLogLevel___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToJsonLogLevel = (const lean_object*)&l_Lake_instToJsonLogLevel___closed__0_value;
static const lean_string_object l_Lake_instFromJsonLogLevel_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "no inductive tag found"};
static const lean_object* l_Lake_instFromJsonLogLevel_fromJson___closed__0 = (const lean_object*)&l_Lake_instFromJsonLogLevel_fromJson___closed__0_value;
static const lean_ctor_object l_Lake_instFromJsonLogLevel_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instFromJsonLogLevel_fromJson___closed__0_value)}};
static const lean_object* l_Lake_instFromJsonLogLevel_fromJson___closed__1 = (const lean_object*)&l_Lake_instFromJsonLogLevel_fromJson___closed__1_value;
static const lean_string_object l_Lake_instFromJsonLogLevel_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "no inductive constructor matched"};
static const lean_object* l_Lake_instFromJsonLogLevel_fromJson___closed__2 = (const lean_object*)&l_Lake_instFromJsonLogLevel_fromJson___closed__2_value;
static const lean_ctor_object l_Lake_instFromJsonLogLevel_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instFromJsonLogLevel_fromJson___closed__2_value)}};
static const lean_object* l_Lake_instFromJsonLogLevel_fromJson___closed__3 = (const lean_object*)&l_Lake_instFromJsonLogLevel_fromJson___closed__3_value;
static const lean_ctor_object l_Lake_instFromJsonLogLevel_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lake_instFromJsonLogLevel_fromJson___closed__4 = (const lean_object*)&l_Lake_instFromJsonLogLevel_fromJson___closed__4_value;
static const lean_ctor_object l_Lake_instFromJsonLogLevel_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instFromJsonLogLevel_fromJson___closed__5 = (const lean_object*)&l_Lake_instFromJsonLogLevel_fromJson___closed__5_value;
static const lean_ctor_object l_Lake_instFromJsonLogLevel_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_instFromJsonLogLevel_fromJson___closed__6 = (const lean_object*)&l_Lake_instFromJsonLogLevel_fromJson___closed__6_value;
static const lean_ctor_object l_Lake_instFromJsonLogLevel_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lake_instFromJsonLogLevel_fromJson___closed__7 = (const lean_object*)&l_Lake_instFromJsonLogLevel_fromJson___closed__7_value;
LEAN_EXPORT lean_object* l_Lake_instFromJsonLogLevel_fromJson(lean_object*);
static const lean_closure_object l_Lake_instFromJsonLogLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instFromJsonLogLevel_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instFromJsonLogLevel___closed__0 = (const lean_object*)&l_Lake_instFromJsonLogLevel___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instFromJsonLogLevel = (const lean_object*)&l_Lake_instFromJsonLogLevel___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instLTLogLevel;
LEAN_EXPORT lean_object* l_Lake_instLELogLevel;
LEAN_EXPORT uint8_t l_Lake_instMinLogLevel___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instMinLogLevel___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMinLogLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMinLogLevel___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMinLogLevel___closed__0 = (const lean_object*)&l_Lake_instMinLogLevel___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instMinLogLevel = (const lean_object*)&l_Lake_instMinLogLevel___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_instMaxLogLevel___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instMaxLogLevel___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMaxLogLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMaxLogLevel___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMaxLogLevel___closed__0 = (const lean_object*)&l_Lake_instMaxLogLevel___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instMaxLogLevel = (const lean_object*)&l_Lake_instMaxLogLevel___closed__0_value;
LEAN_EXPORT uint32_t l_Lake_LogLevel_icon(uint8_t);
LEAN_EXPORT lean_object* l_Lake_LogLevel_icon___boxed(lean_object*);
static const lean_string_object l_Lake_LogLevel_ansiColor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "33"};
static const lean_object* l_Lake_LogLevel_ansiColor___closed__0 = (const lean_object*)&l_Lake_LogLevel_ansiColor___closed__0_value;
static const lean_string_object l_Lake_LogLevel_ansiColor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "31"};
static const lean_object* l_Lake_LogLevel_ansiColor___closed__1 = (const lean_object*)&l_Lake_LogLevel_ansiColor___closed__1_value;
static const lean_string_object l_Lake_LogLevel_ansiColor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "34"};
static const lean_object* l_Lake_LogLevel_ansiColor___closed__2 = (const lean_object*)&l_Lake_LogLevel_ansiColor___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_LogLevel_ansiColor(uint8_t);
LEAN_EXPORT lean_object* l_Lake_LogLevel_ansiColor___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00Lake_LogLevel_ofString_x3f_spec__0(lean_object*, lean_object*);
static const lean_ctor_object l_Lake_LogLevel_ofString_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_LogLevel_ofString_x3f___closed__0 = (const lean_object*)&l_Lake_LogLevel_ofString_x3f___closed__0_value;
static const lean_ctor_object l_Lake_LogLevel_ofString_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lake_LogLevel_ofString_x3f___closed__1 = (const lean_object*)&l_Lake_LogLevel_ofString_x3f___closed__1_value;
static const lean_string_object l_Lake_LogLevel_ofString_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "information"};
static const lean_object* l_Lake_LogLevel_ofString_x3f___closed__2 = (const lean_object*)&l_Lake_LogLevel_ofString_x3f___closed__2_value;
static const lean_string_object l_Lake_LogLevel_ofString_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "warn"};
static const lean_object* l_Lake_LogLevel_ofString_x3f___closed__3 = (const lean_object*)&l_Lake_LogLevel_ofString_x3f___closed__3_value;
static const lean_ctor_object l_Lake_LogLevel_ofString_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lake_LogLevel_ofString_x3f___closed__4 = (const lean_object*)&l_Lake_LogLevel_ofString_x3f___closed__4_value;
static const lean_ctor_object l_Lake_LogLevel_ofString_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_LogLevel_ofString_x3f___closed__5 = (const lean_object*)&l_Lake_LogLevel_ofString_x3f___closed__5_value;
LEAN_EXPORT lean_object* l_Lake_LogLevel_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_toString(uint8_t);
LEAN_EXPORT lean_object* l_Lake_LogLevel_toString___boxed(lean_object*);
static const lean_closure_object l___private_Lake_Util_Log_0__Lake_instToStringLogLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LogLevel_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Util_Log_0__Lake_instToStringLogLevel___closed__0 = (const lean_object*)&l___private_Lake_Util_Log_0__Lake_instToStringLogLevel___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Util_Log_0__Lake_instToStringLogLevel = (const lean_object*)&l___private_Lake_Util_Log_0__Lake_instToStringLogLevel___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_LogLevel_ofMessageSeverity(uint8_t);
LEAN_EXPORT lean_object* l_Lake_LogLevel_ofMessageSeverity___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_LogLevel_toMessageSeverity(uint8_t);
LEAN_EXPORT lean_object* l_Lake_LogLevel_toMessageSeverity___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Verbosity_minLogLv(uint8_t);
LEAN_EXPORT lean_object* l_Lake_Verbosity_minLogLv___boxed(lean_object*);
static const lean_string_object l_Lake_instInhabitedLogEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedLogEntry_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedLogEntry_default___closed__0_value;
static const lean_ctor_object l_Lake_instInhabitedLogEntry_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instInhabitedLogEntry_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_instInhabitedLogEntry_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedLogEntry_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedLogEntry_default = (const lean_object*)&l_Lake_instInhabitedLogEntry_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedLogEntry = (const lean_object*)&l_Lake_instInhabitedLogEntry_default___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_instToJsonLogEntry_toJson_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lake_instToJsonLogEntry_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "level"};
static const lean_object* l_Lake_instToJsonLogEntry_toJson___closed__0 = (const lean_object*)&l_Lake_instToJsonLogEntry_toJson___closed__0_value;
static const lean_string_object l_Lake_instToJsonLogEntry_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "message"};
static const lean_object* l_Lake_instToJsonLogEntry_toJson___closed__1 = (const lean_object*)&l_Lake_instToJsonLogEntry_toJson___closed__1_value;
static const lean_array_object l_Lake_instToJsonLogEntry_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_instToJsonLogEntry_toJson___closed__2 = (const lean_object*)&l_Lake_instToJsonLogEntry_toJson___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_instToJsonLogEntry_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonLogEntry_toJson___boxed(lean_object*);
static const lean_closure_object l_Lake_instToJsonLogEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToJsonLogEntry_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToJsonLogEntry___closed__0 = (const lean_object*)&l_Lake_instToJsonLogEntry___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToJsonLogEntry = (const lean_object*)&l_Lake_instToJsonLogEntry___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_instFromJsonLogEntry_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_instFromJsonLogEntry_fromJson___closed__0 = (const lean_object*)&l_Lake_instFromJsonLogEntry_fromJson___closed__0_value;
static const lean_string_object l_Lake_instFromJsonLogEntry_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "LogEntry"};
static const lean_object* l_Lake_instFromJsonLogEntry_fromJson___closed__1 = (const lean_object*)&l_Lake_instFromJsonLogEntry_fromJson___closed__1_value;
static const lean_ctor_object l_Lake_instFromJsonLogEntry_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instFromJsonLogEntry_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_instFromJsonLogEntry_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_instFromJsonLogEntry_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lake_instFromJsonLogEntry_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(32, 96, 108, 55, 70, 212, 138, 58)}};
static const lean_object* l_Lake_instFromJsonLogEntry_fromJson___closed__2 = (const lean_object*)&l_Lake_instFromJsonLogEntry_fromJson___closed__2_value;
static lean_once_cell_t l_Lake_instFromJsonLogEntry_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instFromJsonLogEntry_fromJson___closed__3;
static const lean_string_object l_Lake_instFromJsonLogEntry_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_instFromJsonLogEntry_fromJson___closed__4 = (const lean_object*)&l_Lake_instFromJsonLogEntry_fromJson___closed__4_value;
static lean_once_cell_t l_Lake_instFromJsonLogEntry_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instFromJsonLogEntry_fromJson___closed__5;
static const lean_ctor_object l_Lake_instFromJsonLogEntry_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instToJsonLogEntry_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 87, 114, 95, 43, 103, 70, 253)}};
static const lean_object* l_Lake_instFromJsonLogEntry_fromJson___closed__6 = (const lean_object*)&l_Lake_instFromJsonLogEntry_fromJson___closed__6_value;
static lean_once_cell_t l_Lake_instFromJsonLogEntry_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instFromJsonLogEntry_fromJson___closed__7;
static lean_once_cell_t l_Lake_instFromJsonLogEntry_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instFromJsonLogEntry_fromJson___closed__8;
static const lean_string_object l_Lake_instFromJsonLogEntry_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lake_instFromJsonLogEntry_fromJson___closed__9 = (const lean_object*)&l_Lake_instFromJsonLogEntry_fromJson___closed__9_value;
static lean_once_cell_t l_Lake_instFromJsonLogEntry_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instFromJsonLogEntry_fromJson___closed__10;
static const lean_ctor_object l_Lake_instFromJsonLogEntry_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instToJsonLogEntry_toJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(149, 62, 76, 216, 222, 7, 163, 13)}};
static const lean_object* l_Lake_instFromJsonLogEntry_fromJson___closed__11 = (const lean_object*)&l_Lake_instFromJsonLogEntry_fromJson___closed__11_value;
static lean_once_cell_t l_Lake_instFromJsonLogEntry_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instFromJsonLogEntry_fromJson___closed__12;
static lean_once_cell_t l_Lake_instFromJsonLogEntry_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instFromJsonLogEntry_fromJson___closed__13;
static lean_once_cell_t l_Lake_instFromJsonLogEntry_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instFromJsonLogEntry_fromJson___closed__14;
LEAN_EXPORT lean_object* l_Lake_instFromJsonLogEntry_fromJson(lean_object*);
static const lean_closure_object l_Lake_instFromJsonLogEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instFromJsonLogEntry_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instFromJsonLogEntry___closed__0 = (const lean_object*)&l_Lake_instFromJsonLogEntry___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instFromJsonLogEntry = (const lean_object*)&l_Lake_instFromJsonLogEntry___closed__0_value;
static const lean_string_object l_Lake_LogEntry_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lake_LogEntry_toString___closed__0 = (const lean_object*)&l_Lake_LogEntry_toString___closed__0_value;
static const lean_string_object l_Lake_LogEntry_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lake_LogEntry_toString___closed__1 = (const lean_object*)&l_Lake_LogEntry_toString___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_LogEntry_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_LogEntry_toString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToStringLogEntry___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToStringLogEntry___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instToStringLogEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToStringLogEntry___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToStringLogEntry___closed__0 = (const lean_object*)&l_Lake_instToStringLogEntry___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToStringLogEntry = (const lean_object*)&l_Lake_instToStringLogEntry___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_LogEntry_trace(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogEntry_info(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogEntry_warning(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogEntry_error(lean_object*);
static const lean_string_object l_Lake_LogEntry_ofSerialMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":\n"};
static const lean_object* l_Lake_LogEntry_ofSerialMessage___closed__0 = (const lean_object*)&l_Lake_LogEntry_ofSerialMessage___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_LogEntry_ofSerialMessage(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogEntry_ofMessage(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogEntry_ofMessage___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logVerbose___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logVerbose(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logVerbose___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logInfo___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logInfo(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logWarning___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logWarning(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logError___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logError(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logSerialMessage___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logSerialMessage(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logMessage___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logMessage___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logMessage(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_logToStream___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_instInhabitedOfPure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_instInhabitedOfPure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_error___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_error___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_error(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_logEntry(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutStream_logEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_logger(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___redArg(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_instInhabitedLog_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_instInhabitedLog_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedLog_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedLog_default = (const lean_object*)&l_Lake_instInhabitedLog_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedLog = (const lean_object*)&l_Lake_instInhabitedLog_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instToJsonLog___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instToJsonLog___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToJsonLog___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_instToJsonLogEntry___closed__0_value)} };
static const lean_object* l_Lake_instToJsonLog___closed__0 = (const lean_object*)&l_Lake_instToJsonLog___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToJsonLog = (const lean_object*)&l_Lake_instToJsonLog___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instFromJsonLog___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instFromJsonLog___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instFromJsonLog___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_instFromJsonLogEntry___closed__0_value)} };
static const lean_object* l_Lake_instFromJsonLog___closed__0 = (const lean_object*)&l_Lake_instFromJsonLog___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instFromJsonLog = (const lean_object*)&l_Lake_instFromJsonLog___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Log_instInhabitedPos_default;
LEAN_EXPORT lean_object* l_Lake_Log_instInhabitedPos;
LEAN_EXPORT uint8_t l_Lake_Log_instDecidableEqPos_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_instDecidableEqPos_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Log_instDecidableEqPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_instDecidableEqPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instOfNatPos;
LEAN_EXPORT uint8_t l_Lake_instOrdPos___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instOrdPos___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instOrdPos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instOrdPos___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instOrdPos___closed__0 = (const lean_object*)&l_Lake_instOrdPos___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instOrdPos = (const lean_object*)&l_Lake_instOrdPos___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instLTPos;
LEAN_EXPORT uint8_t l_Lake_instDecidableRelPosLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableRelPosLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instLEPos;
LEAN_EXPORT uint8_t l_Lake_instDecidableRelPosLe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableRelPosLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMinPos___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMinPos___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMinPos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMinPos___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMinPos___closed__0 = (const lean_object*)&l_Lake_instMinPos___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instMinPos = (const lean_object*)&l_Lake_instMinPos___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instMaxPos___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMaxPos___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMaxPos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMaxPos___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMaxPos___closed__0 = (const lean_object*)&l_Lake_instMaxPos___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instMaxPos = (const lean_object*)&l_Lake_instMaxPos___closed__0_value;
static const lean_array_object l_Lake_Log_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Log_empty___closed__0 = (const lean_object*)&l_Lake_Log_empty___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Log_empty = (const lean_object*)&l_Lake_Log_empty___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Log_instEmptyCollection = (const lean_object*)&l_Lake_Log_empty___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Log_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_size___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Log_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_isEmpty___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Log_hasEntries(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_hasEntries___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_endPos(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_endPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_append___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Log_instAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Log_append___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Log_instAppend___closed__0 = (const lean_object*)&l_Lake_Log_instAppend___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Log_instAppend = (const lean_object*)&l_Lake_Log_instAppend___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Log_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_extract___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_dropFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_dropFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_takeFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_takeFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_split(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_toString___boxed(lean_object*);
static const lean_closure_object l_Lake_Log_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Log_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Log_instToString___closed__0 = (const lean_object*)&l_Lake_Log_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Log_instToString = (const lean_object*)&l_Lake_Log_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Log_replay___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_replay___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_replay(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_filter___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_Log_filter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Log_filter___closed__0 = (const lean_object*)&l_Lake_Log_filter___closed__0_value;
static const lean_closure_object l_Lake_Log_filter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Log_filter___closed__1 = (const lean_object*)&l_Lake_Log_filter___closed__1_value;
static const lean_closure_object l_Lake_Log_filter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Log_filter___closed__2 = (const lean_object*)&l_Lake_Log_filter___closed__2_value;
static const lean_closure_object l_Lake_Log_filter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Log_filter___closed__3 = (const lean_object*)&l_Lake_Log_filter___closed__3_value;
static const lean_closure_object l_Lake_Log_filter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Log_filter___closed__4 = (const lean_object*)&l_Lake_Log_filter___closed__4_value;
static const lean_closure_object l_Lake_Log_filter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Log_filter___closed__5 = (const lean_object*)&l_Lake_Log_filter___closed__5_value;
static const lean_closure_object l_Lake_Log_filter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Log_filter___closed__6 = (const lean_object*)&l_Lake_Log_filter___closed__6_value;
static const lean_ctor_object l_Lake_Log_filter___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Log_filter___closed__0_value),((lean_object*)&l_Lake_Log_filter___closed__1_value)}};
static const lean_object* l_Lake_Log_filter___closed__7 = (const lean_object*)&l_Lake_Log_filter___closed__7_value;
static const lean_ctor_object l_Lake_Log_filter___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Log_filter___closed__7_value),((lean_object*)&l_Lake_Log_filter___closed__2_value),((lean_object*)&l_Lake_Log_filter___closed__3_value),((lean_object*)&l_Lake_Log_filter___closed__4_value),((lean_object*)&l_Lake_Log_filter___closed__5_value)}};
static const lean_object* l_Lake_Log_filter___closed__8 = (const lean_object*)&l_Lake_Log_filter___closed__8_value;
static const lean_ctor_object l_Lake_Log_filter___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Log_filter___closed__8_value),((lean_object*)&l_Lake_Log_filter___closed__6_value)}};
static const lean_object* l_Lake_Log_filter___closed__9 = (const lean_object*)&l_Lake_Log_filter___closed__9_value;
LEAN_EXPORT lean_object* l_Lake_Log_filter(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Log_any___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_any___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Log_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_any___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(lean_object*, size_t, size_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Log_maxLv(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_maxLv___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_pushLogEntry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_ofMonadState___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_ofMonadState(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLog___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLog___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLog(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLog___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLogPos___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLogPos___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLogPos___redArg___closed__0 = (const lean_object*)&l_Lake_getLogPos___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLogPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeLog___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lake_takeLog___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_takeLog___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_takeLog___redArg___closed__0 = (const lean_object*)&l_Lake_takeLog___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_takeLog___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeLog(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeLogFrom___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeLogFrom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeLogFrom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_dropLogFrom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_extractLog(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withExtractLog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_throwIfLogs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_errorWithLog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__2(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_withLoggedIO___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "stdout/stderr:\n"};
static const lean_object* l_Lake_withLoggedIO___redArg___lam__3___closed__0 = (const lean_object*)&l_Lake_withLoggedIO___redArg___lam__3___closed__0_value;
static const lean_string_object l_Lake_withLoggedIO___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Init.Data.String.Basic"};
static const lean_object* l_Lake_withLoggedIO___redArg___lam__3___closed__1 = (const lean_object*)&l_Lake_withLoggedIO___redArg___lam__3___closed__1_value;
static const lean_string_object l_Lake_withLoggedIO___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "String.fromUTF8!"};
static const lean_object* l_Lake_withLoggedIO___redArg___lam__3___closed__2 = (const lean_object*)&l_Lake_withLoggedIO___redArg___lam__3___closed__2_value;
static const lean_string_object l_Lake_withLoggedIO___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid UTF-8 string"};
static const lean_object* l_Lake_withLoggedIO___redArg___lam__3___closed__3 = (const lean_object*)&l_Lake_withLoggedIO___redArg___lam__3___closed__3_value;
static lean_once_cell_t l_Lake_withLoggedIO___redArg___lam__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_withLoggedIO___redArg___lam__3___closed__4;
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_withLoggedIO___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_withLoggedIO___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_withLoggedIO___redArg___closed__0 = (const lean_object*)&l_Lake_withLoggedIO___redArg___closed__0_value;
static lean_once_cell_t l_Lake_withLoggedIO___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_withLoggedIO___redArg___closed__1;
static lean_once_cell_t l_Lake_withLoggedIO___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_withLoggedIO___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLoggedIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_error___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_error___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_error(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_monadError___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_monadError___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_monadError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_failure___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_failure___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_failure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_alternative(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLogLogTOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLogLogTOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_LogT_run_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LogT_run_x27___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LogT_run_x27___redArg___closed__0 = (const lean_object*)&l_Lake_LogT_run_x27___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLogELogTOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLogELogTOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadErrorELogTOfMonad___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadErrorELogTOfMonad___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___closed__0 = (const lean_object*)&l_Lake_instMonadErrorELogTOfMonad___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_run(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_ELogT_run_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_EResult_toExcept___boxed, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_ELogT_run_x27___redArg___closed__0 = (const lean_object*)&l_Lake_ELogT_run_x27___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_ELogT_toLogT___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_EResult_toProd, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_ELogT_toLogT___redArg___closed__0 = (const lean_object*)&l_Lake_ELogT_toLogT___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_ELogT_toLogT_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_EResult_toProd_x3f, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_ELogT_toLogT_x3f___redArg___closed__0 = (const lean_object*)&l_Lake_ELogT_toLogT_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_ELogT_run_x3f_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_EResult_result_x3f___boxed, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_ELogT_run_x3f_x27___redArg___closed__0 = (const lean_object*)&l_Lake_ELogT_run_x3f_x27___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___redArg___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogIO_instMonadLiftIO___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogIO_instMonadLiftIO___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_LogIO_instMonadLiftIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LogIO_instMonadLiftIO___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LogIO_instMonadLiftIO___closed__0 = (const lean_object*)&l_Lake_LogIO_instMonadLiftIO___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_LogIO_instMonadLiftIO = (const lean_object*)&l_Lake_LogIO_instMonadLiftIO___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogIO_captureLog___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogIO_captureLog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadError___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadError___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_LoggerIO_instMonadError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LoggerIO_instMonadError___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LoggerIO_instMonadError___closed__0 = (const lean_object*)&l_Lake_LoggerIO_instMonadError___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_LoggerIO_instMonadError = (const lean_object*)&l_Lake_LoggerIO_instMonadError___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftIO___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftIO___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_LoggerIO_instMonadLiftIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LoggerIO_instMonadLiftIO___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LoggerIO_instMonadLiftIO___closed__0 = (const lean_object*)&l_Lake_LoggerIO_instMonadLiftIO___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_LoggerIO_instMonadLiftIO = (const lean_object*)&l_Lake_LoggerIO_instMonadLiftIO___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_LoggerIO_instMonadLiftLogIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LoggerIO_instMonadLiftLogIO___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___closed__0 = (const lean_object*)&l_Lake_LoggerIO_instMonadLiftLogIO___closed__0_value;
static lean_once_cell_t l_Lake_LoggerIO_instMonadLiftLogIO___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___closed__1;
static lean_once_cell_t l_Lake_LoggerIO_instMonadLiftLogIO___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___closed__2;
static lean_once_cell_t l_Lake_LoggerIO_instMonadLiftLogIO___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___closed__3;
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO;
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg___lam__0(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorIdx(uint8_t v_x_1_){
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
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lake_Verbosity_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lake_Verbosity_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lake_Verbosity_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_quiet_elim___redArg(lean_object* v_quiet_23_){
_start:
{
lean_inc(v_quiet_23_);
return v_quiet_23_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_quiet_elim___redArg___boxed(lean_object* v_quiet_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lake_Verbosity_quiet_elim___redArg(v_quiet_24_);
lean_dec(v_quiet_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_quiet_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_quiet_29_){
_start:
{
lean_inc(v_quiet_29_);
return v_quiet_29_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_quiet_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_quiet_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lake_Verbosity_quiet_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_quiet_33_);
lean_dec(v_quiet_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_normal_elim___redArg(lean_object* v_normal_36_){
_start:
{
lean_inc(v_normal_36_);
return v_normal_36_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_normal_elim___redArg___boxed(lean_object* v_normal_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lake_Verbosity_normal_elim___redArg(v_normal_37_);
lean_dec(v_normal_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_normal_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_normal_42_){
_start:
{
lean_inc(v_normal_42_);
return v_normal_42_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_normal_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_normal_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lake_Verbosity_normal_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_normal_46_);
lean_dec(v_normal_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_verbose_elim___redArg(lean_object* v_verbose_49_){
_start:
{
lean_inc(v_verbose_49_);
return v_verbose_49_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_verbose_elim___redArg___boxed(lean_object* v_verbose_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lake_Verbosity_verbose_elim___redArg(v_verbose_50_);
lean_dec(v_verbose_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_verbose_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_verbose_55_){
_start:
{
lean_inc(v_verbose_55_);
return v_verbose_55_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_verbose_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_verbose_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lake_Verbosity_verbose_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_verbose_59_);
lean_dec(v_verbose_59_);
return v_res_61_;
}
}
static lean_object* _init_l_Lake_instReprVerbosity_repr___closed__6(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(2u);
v___x_72_ = lean_nat_to_int(v___x_71_);
return v___x_72_;
}
}
static lean_object* _init_l_Lake_instReprVerbosity_repr___closed__7(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_unsigned_to_nat(1u);
v___x_74_ = lean_nat_to_int(v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerbosity_repr(uint8_t v_x_75_, lean_object* v_prec_76_){
_start:
{
lean_object* v___y_78_; lean_object* v___y_85_; lean_object* v___y_92_; 
switch(v_x_75_)
{
case 0:
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = lean_unsigned_to_nat(1024u);
v___x_99_ = lean_nat_dec_le(v___x_98_, v_prec_76_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
v___x_100_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_78_ = v___x_100_;
goto v___jp_77_;
}
else
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_78_ = v___x_101_;
goto v___jp_77_;
}
}
case 1:
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = lean_unsigned_to_nat(1024u);
v___x_103_ = lean_nat_dec_le(v___x_102_, v_prec_76_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; 
v___x_104_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_85_ = v___x_104_;
goto v___jp_84_;
}
else
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_85_ = v___x_105_;
goto v___jp_84_;
}
}
default: 
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = lean_unsigned_to_nat(1024u);
v___x_107_ = lean_nat_dec_le(v___x_106_, v_prec_76_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_92_ = v___x_108_;
goto v___jp_91_;
}
else
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_92_ = v___x_109_;
goto v___jp_91_;
}
}
}
v___jp_77_:
{
lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_79_ = ((lean_object*)(l_Lake_instReprVerbosity_repr___closed__1));
lean_inc(v___y_78_);
v___x_80_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_80_, 0, v___y_78_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = 0;
v___x_82_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_82_, 0, v___x_80_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*1, v___x_81_);
v___x_83_ = l_Repr_addAppParen(v___x_82_, v_prec_76_);
return v___x_83_;
}
v___jp_84_:
{
lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_86_ = ((lean_object*)(l_Lake_instReprVerbosity_repr___closed__3));
lean_inc(v___y_85_);
v___x_87_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_87_, 0, v___y_85_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = 0;
v___x_89_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*1, v___x_88_);
v___x_90_ = l_Repr_addAppParen(v___x_89_, v_prec_76_);
return v___x_90_;
}
v___jp_91_:
{
lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_93_ = ((lean_object*)(l_Lake_instReprVerbosity_repr___closed__5));
lean_inc(v___y_92_);
v___x_94_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_94_, 0, v___y_92_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = 0;
v___x_96_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_96_, 0, v___x_94_);
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*1, v___x_95_);
v___x_97_ = l_Repr_addAppParen(v___x_96_, v_prec_76_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerbosity_repr___boxed(lean_object* v_x_110_, lean_object* v_prec_111_){
_start:
{
uint8_t v_x_177__boxed_112_; lean_object* v_res_113_; 
v_x_177__boxed_112_ = lean_unbox(v_x_110_);
v_res_113_ = l_Lake_instReprVerbosity_repr(v_x_177__boxed_112_, v_prec_111_);
lean_dec(v_prec_111_);
return v_res_113_;
}
}
LEAN_EXPORT uint8_t l_Lake_Verbosity_ofNat(lean_object* v_n_116_){
_start:
{
lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = lean_nat_dec_le(v_n_116_, v___x_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(1u);
v___x_120_ = lean_nat_dec_le(v_n_116_, v___x_119_);
if (v___x_120_ == 0)
{
uint8_t v___x_121_; 
v___x_121_ = 2;
return v___x_121_;
}
else
{
uint8_t v___x_122_; 
v___x_122_ = 1;
return v___x_122_;
}
}
else
{
uint8_t v___x_123_; 
v___x_123_ = 0;
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_ofNat___boxed(lean_object* v_n_124_){
_start:
{
uint8_t v_res_125_; lean_object* v_r_126_; 
v_res_125_ = l_Lake_Verbosity_ofNat(v_n_124_);
lean_dec(v_n_124_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqVerbosity(uint8_t v_x_127_, uint8_t v_y_128_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_129_ = l_Lake_Verbosity_ctorIdx(v_x_127_);
v___x_130_ = l_Lake_Verbosity_ctorIdx(v_y_128_);
v___x_131_ = lean_nat_dec_eq(v___x_129_, v___x_130_);
lean_dec(v___x_130_);
lean_dec(v___x_129_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqVerbosity___boxed(lean_object* v_x_132_, lean_object* v_y_133_){
_start:
{
uint8_t v_x_13__boxed_134_; uint8_t v_y_14__boxed_135_; uint8_t v_res_136_; lean_object* v_r_137_; 
v_x_13__boxed_134_ = lean_unbox(v_x_132_);
v_y_14__boxed_135_ = lean_unbox(v_y_133_);
v_res_136_ = l_Lake_instDecidableEqVerbosity(v_x_13__boxed_134_, v_y_14__boxed_135_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT uint8_t l_Lake_instOrdVerbosity_ord(uint8_t v_x_138_, uint8_t v_y_139_){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_140_ = l_Lake_Verbosity_ctorIdx(v_x_138_);
v___x_141_ = l_Lake_Verbosity_ctorIdx(v_y_139_);
v___x_142_ = lean_nat_dec_lt(v___x_140_, v___x_141_);
if (v___x_142_ == 0)
{
uint8_t v___x_143_; 
v___x_143_ = lean_nat_dec_eq(v___x_140_, v___x_141_);
lean_dec(v___x_141_);
lean_dec(v___x_140_);
if (v___x_143_ == 0)
{
uint8_t v___x_144_; 
v___x_144_ = 2;
return v___x_144_;
}
else
{
uint8_t v___x_145_; 
v___x_145_ = 1;
return v___x_145_;
}
}
else
{
uint8_t v___x_146_; 
lean_dec(v___x_141_);
lean_dec(v___x_140_);
v___x_146_ = 0;
return v___x_146_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instOrdVerbosity_ord___boxed(lean_object* v_x_147_, lean_object* v_y_148_){
_start:
{
uint8_t v_x_30__boxed_149_; uint8_t v_y_31__boxed_150_; uint8_t v_res_151_; lean_object* v_r_152_; 
v_x_30__boxed_149_ = lean_unbox(v_x_147_);
v_y_31__boxed_150_ = lean_unbox(v_y_148_);
v_res_151_ = l_Lake_instOrdVerbosity_ord(v_x_30__boxed_149_, v_y_31__boxed_150_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
static lean_object* _init_l_Lake_instLTVerbosity(void){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = lean_box(0);
return v___x_155_;
}
}
static lean_object* _init_l_Lake_instLEVerbosity(void){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = lean_box(0);
return v___x_156_;
}
}
LEAN_EXPORT uint8_t l_Lake_instMinVerbosity___lam__0(uint8_t v_x_157_, uint8_t v_y_158_){
_start:
{
uint8_t v___x_159_; 
v___x_159_ = l_Lake_instOrdVerbosity_ord(v_x_157_, v_y_158_);
if (v___x_159_ == 2)
{
return v_y_158_;
}
else
{
return v_x_157_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMinVerbosity___lam__0___boxed(lean_object* v_x_160_, lean_object* v_y_161_){
_start:
{
uint8_t v_x_boxed_162_; uint8_t v_y_boxed_163_; uint8_t v_res_164_; lean_object* v_r_165_; 
v_x_boxed_162_ = lean_unbox(v_x_160_);
v_y_boxed_163_ = lean_unbox(v_y_161_);
v_res_164_ = l_Lake_instMinVerbosity___lam__0(v_x_boxed_162_, v_y_boxed_163_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
LEAN_EXPORT uint8_t l_Lake_instMaxVerbosity___lam__0(uint8_t v_x_168_, uint8_t v_y_169_){
_start:
{
uint8_t v___x_170_; 
v___x_170_ = l_Lake_instOrdVerbosity_ord(v_x_168_, v_y_169_);
if (v___x_170_ == 2)
{
return v_x_168_;
}
else
{
return v_y_169_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxVerbosity___lam__0___boxed(lean_object* v_x_171_, lean_object* v_y_172_){
_start:
{
uint8_t v_x_boxed_173_; uint8_t v_y_boxed_174_; uint8_t v_res_175_; lean_object* v_r_176_; 
v_x_boxed_173_ = lean_unbox(v_x_171_);
v_y_boxed_174_ = lean_unbox(v_y_172_);
v_res_175_ = l_Lake_instMaxVerbosity___lam__0(v_x_boxed_173_, v_y_boxed_174_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
static uint8_t _init_l_Lake_instInhabitedVerbosity(void){
_start:
{
uint8_t v___x_179_; 
v___x_179_ = 1;
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorIdx(uint8_t v_x_180_){
_start:
{
switch(v_x_180_)
{
case 0:
{
lean_object* v___x_181_; 
v___x_181_ = lean_unsigned_to_nat(0u);
return v___x_181_;
}
case 1:
{
lean_object* v___x_182_; 
v___x_182_ = lean_unsigned_to_nat(1u);
return v___x_182_;
}
default: 
{
lean_object* v___x_183_; 
v___x_183_ = lean_unsigned_to_nat(2u);
return v___x_183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorIdx___boxed(lean_object* v_x_184_){
_start:
{
uint8_t v_x_boxed_185_; lean_object* v_res_186_; 
v_x_boxed_185_ = lean_unbox(v_x_184_);
v_res_186_ = l_Lake_AnsiMode_ctorIdx(v_x_boxed_185_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorElim___redArg(lean_object* v_k_187_){
_start:
{
lean_inc(v_k_187_);
return v_k_187_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorElim___redArg___boxed(lean_object* v_k_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lake_AnsiMode_ctorElim___redArg(v_k_188_);
lean_dec(v_k_188_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorElim(lean_object* v_motive_190_, lean_object* v_ctorIdx_191_, uint8_t v_t_192_, lean_object* v_h_193_, lean_object* v_k_194_){
_start:
{
lean_inc(v_k_194_);
return v_k_194_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorElim___boxed(lean_object* v_motive_195_, lean_object* v_ctorIdx_196_, lean_object* v_t_197_, lean_object* v_h_198_, lean_object* v_k_199_){
_start:
{
uint8_t v_t_boxed_200_; lean_object* v_res_201_; 
v_t_boxed_200_ = lean_unbox(v_t_197_);
v_res_201_ = l_Lake_AnsiMode_ctorElim(v_motive_195_, v_ctorIdx_196_, v_t_boxed_200_, v_h_198_, v_k_199_);
lean_dec(v_k_199_);
lean_dec(v_ctorIdx_196_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_auto_elim___redArg(lean_object* v_auto_202_){
_start:
{
lean_inc(v_auto_202_);
return v_auto_202_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_auto_elim___redArg___boxed(lean_object* v_auto_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lake_AnsiMode_auto_elim___redArg(v_auto_203_);
lean_dec(v_auto_203_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_auto_elim(lean_object* v_motive_205_, uint8_t v_t_206_, lean_object* v_h_207_, lean_object* v_auto_208_){
_start:
{
lean_inc(v_auto_208_);
return v_auto_208_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_auto_elim___boxed(lean_object* v_motive_209_, lean_object* v_t_210_, lean_object* v_h_211_, lean_object* v_auto_212_){
_start:
{
uint8_t v_t_boxed_213_; lean_object* v_res_214_; 
v_t_boxed_213_ = lean_unbox(v_t_210_);
v_res_214_ = l_Lake_AnsiMode_auto_elim(v_motive_209_, v_t_boxed_213_, v_h_211_, v_auto_212_);
lean_dec(v_auto_212_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ansi_elim___redArg(lean_object* v_ansi_215_){
_start:
{
lean_inc(v_ansi_215_);
return v_ansi_215_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ansi_elim___redArg___boxed(lean_object* v_ansi_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lake_AnsiMode_ansi_elim___redArg(v_ansi_216_);
lean_dec(v_ansi_216_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ansi_elim(lean_object* v_motive_218_, uint8_t v_t_219_, lean_object* v_h_220_, lean_object* v_ansi_221_){
_start:
{
lean_inc(v_ansi_221_);
return v_ansi_221_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ansi_elim___boxed(lean_object* v_motive_222_, lean_object* v_t_223_, lean_object* v_h_224_, lean_object* v_ansi_225_){
_start:
{
uint8_t v_t_boxed_226_; lean_object* v_res_227_; 
v_t_boxed_226_ = lean_unbox(v_t_223_);
v_res_227_ = l_Lake_AnsiMode_ansi_elim(v_motive_222_, v_t_boxed_226_, v_h_224_, v_ansi_225_);
lean_dec(v_ansi_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noAnsi_elim___redArg(lean_object* v_noAnsi_228_){
_start:
{
lean_inc(v_noAnsi_228_);
return v_noAnsi_228_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noAnsi_elim___redArg___boxed(lean_object* v_noAnsi_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lake_AnsiMode_noAnsi_elim___redArg(v_noAnsi_229_);
lean_dec(v_noAnsi_229_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noAnsi_elim(lean_object* v_motive_231_, uint8_t v_t_232_, lean_object* v_h_233_, lean_object* v_noAnsi_234_){
_start:
{
lean_inc(v_noAnsi_234_);
return v_noAnsi_234_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noAnsi_elim___boxed(lean_object* v_motive_235_, lean_object* v_t_236_, lean_object* v_h_237_, lean_object* v_noAnsi_238_){
_start:
{
uint8_t v_t_boxed_239_; lean_object* v_res_240_; 
v_t_boxed_239_ = lean_unbox(v_t_236_);
v_res_240_ = l_Lake_AnsiMode_noAnsi_elim(v_motive_235_, v_t_boxed_239_, v_h_237_, v_noAnsi_238_);
lean_dec(v_noAnsi_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprAnsiMode_repr(uint8_t v_x_250_, lean_object* v_prec_251_){
_start:
{
lean_object* v___y_253_; lean_object* v___y_260_; lean_object* v___y_267_; 
switch(v_x_250_)
{
case 0:
{
lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_273_ = lean_unsigned_to_nat(1024u);
v___x_274_ = lean_nat_dec_le(v___x_273_, v_prec_251_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; 
v___x_275_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_253_ = v___x_275_;
goto v___jp_252_;
}
else
{
lean_object* v___x_276_; 
v___x_276_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_253_ = v___x_276_;
goto v___jp_252_;
}
}
case 1:
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = lean_unsigned_to_nat(1024u);
v___x_278_ = lean_nat_dec_le(v___x_277_, v_prec_251_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; 
v___x_279_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_260_ = v___x_279_;
goto v___jp_259_;
}
else
{
lean_object* v___x_280_; 
v___x_280_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_260_ = v___x_280_;
goto v___jp_259_;
}
}
default: 
{
lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_281_ = lean_unsigned_to_nat(1024u);
v___x_282_ = lean_nat_dec_le(v___x_281_, v_prec_251_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; 
v___x_283_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_267_ = v___x_283_;
goto v___jp_266_;
}
else
{
lean_object* v___x_284_; 
v___x_284_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_267_ = v___x_284_;
goto v___jp_266_;
}
}
}
v___jp_252_:
{
lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_254_ = ((lean_object*)(l_Lake_instReprAnsiMode_repr___closed__1));
lean_inc(v___y_253_);
v___x_255_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_255_, 0, v___y_253_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = 0;
v___x_257_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_257_, 0, v___x_255_);
lean_ctor_set_uint8(v___x_257_, sizeof(void*)*1, v___x_256_);
v___x_258_ = l_Repr_addAppParen(v___x_257_, v_prec_251_);
return v___x_258_;
}
v___jp_259_:
{
lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_261_ = ((lean_object*)(l_Lake_instReprAnsiMode_repr___closed__3));
lean_inc(v___y_260_);
v___x_262_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_262_, 0, v___y_260_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
v___x_263_ = 0;
v___x_264_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_264_, 0, v___x_262_);
lean_ctor_set_uint8(v___x_264_, sizeof(void*)*1, v___x_263_);
v___x_265_ = l_Repr_addAppParen(v___x_264_, v_prec_251_);
return v___x_265_;
}
v___jp_266_:
{
lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_268_ = ((lean_object*)(l_Lake_instReprAnsiMode_repr___closed__5));
lean_inc(v___y_267_);
v___x_269_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_269_, 0, v___y_267_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = 0;
v___x_271_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_271_, 0, v___x_269_);
lean_ctor_set_uint8(v___x_271_, sizeof(void*)*1, v___x_270_);
v___x_272_ = l_Repr_addAppParen(v___x_271_, v_prec_251_);
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprAnsiMode_repr___boxed(lean_object* v_x_285_, lean_object* v_prec_286_){
_start:
{
uint8_t v_x_173__boxed_287_; lean_object* v_res_288_; 
v_x_173__boxed_287_ = lean_unbox(v_x_285_);
v_res_288_ = l_Lake_instReprAnsiMode_repr(v_x_173__boxed_287_, v_prec_286_);
lean_dec(v_prec_286_);
return v_res_288_;
}
}
LEAN_EXPORT uint8_t l_Lake_AnsiMode_isEnabled(lean_object* v_out_291_, uint8_t v_x_292_){
_start:
{
switch(v_x_292_)
{
case 0:
{
lean_object* v_isTty_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v_isTty_294_ = lean_ctor_get(v_out_291_, 5);
lean_inc_ref(v_isTty_294_);
lean_dec_ref(v_out_291_);
v___x_295_ = lean_apply_1(v_isTty_294_, lean_box(0));
v___x_296_ = lean_unbox(v___x_295_);
return v___x_296_;
}
case 1:
{
uint8_t v___x_297_; 
lean_dec_ref(v_out_291_);
v___x_297_ = 1;
return v___x_297_;
}
default: 
{
uint8_t v___x_298_; 
lean_dec_ref(v_out_291_);
v___x_298_ = 0;
return v___x_298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_isEnabled___boxed(lean_object* v_out_299_, lean_object* v_x_300_, lean_object* v_a_301_){
_start:
{
uint8_t v_x_140__boxed_302_; uint8_t v_res_303_; lean_object* v_r_304_; 
v_x_140__boxed_302_ = lean_unbox(v_x_300_);
v_res_303_ = l_Lake_AnsiMode_isEnabled(v_out_299_, v_x_140__boxed_302_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
LEAN_EXPORT lean_object* l_Lake_Ansi_chalk(lean_object* v_colorCode_308_, lean_object* v_text_309_){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_310_ = ((lean_object*)(l_Lake_Ansi_chalk___closed__0));
v___x_311_ = lean_string_append(v___x_310_, v_colorCode_308_);
v___x_312_ = ((lean_object*)(l_Lake_Ansi_chalk___closed__1));
v___x_313_ = lean_string_append(v___x_311_, v___x_312_);
v___x_314_ = lean_string_append(v___x_313_, v_text_309_);
v___x_315_ = ((lean_object*)(l_Lake_Ansi_chalk___closed__2));
v___x_316_ = lean_string_append(v___x_314_, v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lake_Ansi_chalk___boxed(lean_object* v_colorCode_317_, lean_object* v_text_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lake_Ansi_chalk(v_colorCode_317_, v_text_318_);
lean_dec_ref(v_text_318_);
lean_dec_ref(v_colorCode_317_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorIdx(lean_object* v_x_320_){
_start:
{
switch(lean_obj_tag(v_x_320_))
{
case 0:
{
lean_object* v___x_321_; 
v___x_321_ = lean_unsigned_to_nat(0u);
return v___x_321_;
}
case 1:
{
lean_object* v___x_322_; 
v___x_322_ = lean_unsigned_to_nat(1u);
return v___x_322_;
}
default: 
{
lean_object* v___x_323_; 
v___x_323_ = lean_unsigned_to_nat(2u);
return v___x_323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorIdx___boxed(lean_object* v_x_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lake_OutStream_ctorIdx(v_x_324_);
lean_dec(v_x_324_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorElim___redArg(lean_object* v_t_326_, lean_object* v_k_327_){
_start:
{
if (lean_obj_tag(v_t_326_) == 2)
{
lean_object* v_s_328_; lean_object* v___x_329_; 
v_s_328_ = lean_ctor_get(v_t_326_, 0);
lean_inc_ref(v_s_328_);
lean_dec_ref_known(v_t_326_, 1);
v___x_329_ = lean_apply_1(v_k_327_, v_s_328_);
return v___x_329_;
}
else
{
lean_dec(v_t_326_);
return v_k_327_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorElim(lean_object* v_motive_330_, lean_object* v_ctorIdx_331_, lean_object* v_t_332_, lean_object* v_h_333_, lean_object* v_k_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lake_OutStream_ctorElim___redArg(v_t_332_, v_k_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorElim___boxed(lean_object* v_motive_336_, lean_object* v_ctorIdx_337_, lean_object* v_t_338_, lean_object* v_h_339_, lean_object* v_k_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lake_OutStream_ctorElim(v_motive_336_, v_ctorIdx_337_, v_t_338_, v_h_339_, v_k_340_);
lean_dec(v_ctorIdx_337_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_stdout_elim___redArg(lean_object* v_t_342_, lean_object* v_stdout_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Lake_OutStream_ctorElim___redArg(v_t_342_, v_stdout_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_stdout_elim(lean_object* v_motive_345_, lean_object* v_t_346_, lean_object* v_h_347_, lean_object* v_stdout_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lake_OutStream_ctorElim___redArg(v_t_346_, v_stdout_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_stderr_elim___redArg(lean_object* v_t_350_, lean_object* v_stderr_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lake_OutStream_ctorElim___redArg(v_t_350_, v_stderr_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_stderr_elim(lean_object* v_motive_353_, lean_object* v_t_354_, lean_object* v_h_355_, lean_object* v_stderr_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lake_OutStream_ctorElim___redArg(v_t_354_, v_stderr_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_stream_elim___redArg(lean_object* v_t_358_, lean_object* v_stream_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lake_OutStream_ctorElim___redArg(v_t_358_, v_stream_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_stream_elim(lean_object* v_motive_361_, lean_object* v_t_362_, lean_object* v_h_363_, lean_object* v_stream_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lake_OutStream_ctorElim___redArg(v_t_362_, v_stream_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_get(lean_object* v_x_366_){
_start:
{
switch(lean_obj_tag(v_x_366_))
{
case 0:
{
lean_object* v___x_368_; 
v___x_368_ = lean_get_stdout();
return v___x_368_;
}
case 1:
{
lean_object* v___x_369_; 
v___x_369_ = lean_get_stderr();
return v___x_369_;
}
default: 
{
lean_object* v_s_370_; 
v_s_370_ = lean_ctor_get(v_x_366_, 0);
lean_inc_ref(v_s_370_);
return v_s_370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_get___boxed(lean_object* v_x_371_, lean_object* v_a_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lake_OutStream_get(v_x_371_);
lean_dec(v_x_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeStreamOutStream___lam__0(lean_object* v_s_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_375_, 0, v_s_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeHandleOutStream___lam__0(lean_object* v_h_378_){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_stream_of_handle(v_h_378_);
v___x_380_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorIdx(uint8_t v_x_383_){
_start:
{
switch(v_x_383_)
{
case 0:
{
lean_object* v___x_384_; 
v___x_384_ = lean_unsigned_to_nat(0u);
return v___x_384_;
}
case 1:
{
lean_object* v___x_385_; 
v___x_385_ = lean_unsigned_to_nat(1u);
return v___x_385_;
}
case 2:
{
lean_object* v___x_386_; 
v___x_386_ = lean_unsigned_to_nat(2u);
return v___x_386_;
}
default: 
{
lean_object* v___x_387_; 
v___x_387_ = lean_unsigned_to_nat(3u);
return v___x_387_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorIdx___boxed(lean_object* v_x_388_){
_start:
{
uint8_t v_x_boxed_389_; lean_object* v_res_390_; 
v_x_boxed_389_ = lean_unbox(v_x_388_);
v_res_390_ = l_Lake_LogLevel_ctorIdx(v_x_boxed_389_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorElim___redArg(lean_object* v_k_391_){
_start:
{
lean_inc(v_k_391_);
return v_k_391_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorElim___redArg___boxed(lean_object* v_k_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lake_LogLevel_ctorElim___redArg(v_k_392_);
lean_dec(v_k_392_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorElim(lean_object* v_motive_394_, lean_object* v_ctorIdx_395_, uint8_t v_t_396_, lean_object* v_h_397_, lean_object* v_k_398_){
_start:
{
lean_inc(v_k_398_);
return v_k_398_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorElim___boxed(lean_object* v_motive_399_, lean_object* v_ctorIdx_400_, lean_object* v_t_401_, lean_object* v_h_402_, lean_object* v_k_403_){
_start:
{
uint8_t v_t_boxed_404_; lean_object* v_res_405_; 
v_t_boxed_404_ = lean_unbox(v_t_401_);
v_res_405_ = l_Lake_LogLevel_ctorElim(v_motive_399_, v_ctorIdx_400_, v_t_boxed_404_, v_h_402_, v_k_403_);
lean_dec(v_k_403_);
lean_dec(v_ctorIdx_400_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_trace_elim___redArg(lean_object* v_trace_406_){
_start:
{
lean_inc(v_trace_406_);
return v_trace_406_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_trace_elim___redArg___boxed(lean_object* v_trace_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lake_LogLevel_trace_elim___redArg(v_trace_407_);
lean_dec(v_trace_407_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_trace_elim(lean_object* v_motive_409_, uint8_t v_t_410_, lean_object* v_h_411_, lean_object* v_trace_412_){
_start:
{
lean_inc(v_trace_412_);
return v_trace_412_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_trace_elim___boxed(lean_object* v_motive_413_, lean_object* v_t_414_, lean_object* v_h_415_, lean_object* v_trace_416_){
_start:
{
uint8_t v_t_boxed_417_; lean_object* v_res_418_; 
v_t_boxed_417_ = lean_unbox(v_t_414_);
v_res_418_ = l_Lake_LogLevel_trace_elim(v_motive_413_, v_t_boxed_417_, v_h_415_, v_trace_416_);
lean_dec(v_trace_416_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_info_elim___redArg(lean_object* v_info_419_){
_start:
{
lean_inc(v_info_419_);
return v_info_419_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_info_elim___redArg___boxed(lean_object* v_info_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lake_LogLevel_info_elim___redArg(v_info_420_);
lean_dec(v_info_420_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_info_elim(lean_object* v_motive_422_, uint8_t v_t_423_, lean_object* v_h_424_, lean_object* v_info_425_){
_start:
{
lean_inc(v_info_425_);
return v_info_425_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_info_elim___boxed(lean_object* v_motive_426_, lean_object* v_t_427_, lean_object* v_h_428_, lean_object* v_info_429_){
_start:
{
uint8_t v_t_boxed_430_; lean_object* v_res_431_; 
v_t_boxed_430_ = lean_unbox(v_t_427_);
v_res_431_ = l_Lake_LogLevel_info_elim(v_motive_426_, v_t_boxed_430_, v_h_428_, v_info_429_);
lean_dec(v_info_429_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_warning_elim___redArg(lean_object* v_warning_432_){
_start:
{
lean_inc(v_warning_432_);
return v_warning_432_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_warning_elim___redArg___boxed(lean_object* v_warning_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lake_LogLevel_warning_elim___redArg(v_warning_433_);
lean_dec(v_warning_433_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_warning_elim(lean_object* v_motive_435_, uint8_t v_t_436_, lean_object* v_h_437_, lean_object* v_warning_438_){
_start:
{
lean_inc(v_warning_438_);
return v_warning_438_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_warning_elim___boxed(lean_object* v_motive_439_, lean_object* v_t_440_, lean_object* v_h_441_, lean_object* v_warning_442_){
_start:
{
uint8_t v_t_boxed_443_; lean_object* v_res_444_; 
v_t_boxed_443_ = lean_unbox(v_t_440_);
v_res_444_ = l_Lake_LogLevel_warning_elim(v_motive_439_, v_t_boxed_443_, v_h_441_, v_warning_442_);
lean_dec(v_warning_442_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_error_elim___redArg(lean_object* v_error_445_){
_start:
{
lean_inc(v_error_445_);
return v_error_445_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_error_elim___redArg___boxed(lean_object* v_error_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lake_LogLevel_error_elim___redArg(v_error_446_);
lean_dec(v_error_446_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_error_elim(lean_object* v_motive_448_, uint8_t v_t_449_, lean_object* v_h_450_, lean_object* v_error_451_){
_start:
{
lean_inc(v_error_451_);
return v_error_451_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_error_elim___boxed(lean_object* v_motive_452_, lean_object* v_t_453_, lean_object* v_h_454_, lean_object* v_error_455_){
_start:
{
uint8_t v_t_boxed_456_; lean_object* v_res_457_; 
v_t_boxed_456_ = lean_unbox(v_t_453_);
v_res_457_ = l_Lake_LogLevel_error_elim(v_motive_452_, v_t_boxed_456_, v_h_454_, v_error_455_);
lean_dec(v_error_455_);
return v_res_457_;
}
}
static uint8_t _init_l_Lake_instInhabitedLogLevel_default(void){
_start:
{
uint8_t v___x_458_; 
v___x_458_ = 0;
return v___x_458_;
}
}
static uint8_t _init_l_Lake_instInhabitedLogLevel(void){
_start:
{
uint8_t v___x_459_; 
v___x_459_ = 0;
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLogLevel_repr(uint8_t v_x_472_, lean_object* v_prec_473_){
_start:
{
lean_object* v___y_475_; lean_object* v___y_482_; lean_object* v___y_489_; lean_object* v___y_496_; 
switch(v_x_472_)
{
case 0:
{
lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_502_ = lean_unsigned_to_nat(1024u);
v___x_503_ = lean_nat_dec_le(v___x_502_, v_prec_473_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; 
v___x_504_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_475_ = v___x_504_;
goto v___jp_474_;
}
else
{
lean_object* v___x_505_; 
v___x_505_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_475_ = v___x_505_;
goto v___jp_474_;
}
}
case 1:
{
lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_506_ = lean_unsigned_to_nat(1024u);
v___x_507_ = lean_nat_dec_le(v___x_506_, v_prec_473_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
v___x_508_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_482_ = v___x_508_;
goto v___jp_481_;
}
else
{
lean_object* v___x_509_; 
v___x_509_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_482_ = v___x_509_;
goto v___jp_481_;
}
}
case 2:
{
lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_510_ = lean_unsigned_to_nat(1024u);
v___x_511_ = lean_nat_dec_le(v___x_510_, v_prec_473_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; 
v___x_512_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_489_ = v___x_512_;
goto v___jp_488_;
}
else
{
lean_object* v___x_513_; 
v___x_513_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_489_ = v___x_513_;
goto v___jp_488_;
}
}
default: 
{
lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_514_ = lean_unsigned_to_nat(1024u);
v___x_515_ = lean_nat_dec_le(v___x_514_, v_prec_473_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; 
v___x_516_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_496_ = v___x_516_;
goto v___jp_495_;
}
else
{
lean_object* v___x_517_; 
v___x_517_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_496_ = v___x_517_;
goto v___jp_495_;
}
}
}
v___jp_474_:
{
lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_476_ = ((lean_object*)(l_Lake_instReprLogLevel_repr___closed__1));
lean_inc(v___y_475_);
v___x_477_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_477_, 0, v___y_475_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
v___x_478_ = 0;
v___x_479_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_479_, 0, v___x_477_);
lean_ctor_set_uint8(v___x_479_, sizeof(void*)*1, v___x_478_);
v___x_480_ = l_Repr_addAppParen(v___x_479_, v_prec_473_);
return v___x_480_;
}
v___jp_481_:
{
lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_483_ = ((lean_object*)(l_Lake_instReprLogLevel_repr___closed__3));
lean_inc(v___y_482_);
v___x_484_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_484_, 0, v___y_482_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
v___x_485_ = 0;
v___x_486_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_486_, 0, v___x_484_);
lean_ctor_set_uint8(v___x_486_, sizeof(void*)*1, v___x_485_);
v___x_487_ = l_Repr_addAppParen(v___x_486_, v_prec_473_);
return v___x_487_;
}
v___jp_488_:
{
lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_490_ = ((lean_object*)(l_Lake_instReprLogLevel_repr___closed__5));
lean_inc(v___y_489_);
v___x_491_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_491_, 0, v___y_489_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
v___x_492_ = 0;
v___x_493_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_493_, 0, v___x_491_);
lean_ctor_set_uint8(v___x_493_, sizeof(void*)*1, v___x_492_);
v___x_494_ = l_Repr_addAppParen(v___x_493_, v_prec_473_);
return v___x_494_;
}
v___jp_495_:
{
lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_497_ = ((lean_object*)(l_Lake_instReprLogLevel_repr___closed__7));
lean_inc(v___y_496_);
v___x_498_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_498_, 0, v___y_496_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = 0;
v___x_500_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_500_, 0, v___x_498_);
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*1, v___x_499_);
v___x_501_ = l_Repr_addAppParen(v___x_500_, v_prec_473_);
return v___x_501_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLogLevel_repr___boxed(lean_object* v_x_518_, lean_object* v_prec_519_){
_start:
{
uint8_t v_x_229__boxed_520_; lean_object* v_res_521_; 
v_x_229__boxed_520_ = lean_unbox(v_x_518_);
v_res_521_ = l_Lake_instReprLogLevel_repr(v_x_229__boxed_520_, v_prec_519_);
lean_dec(v_prec_519_);
return v_res_521_;
}
}
LEAN_EXPORT uint8_t l_Lake_LogLevel_ofNat(lean_object* v_n_524_){
_start:
{
lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_525_ = lean_unsigned_to_nat(1u);
v___x_526_ = lean_nat_dec_le(v_n_524_, v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_527_ = lean_unsigned_to_nat(2u);
v___x_528_ = lean_nat_dec_le(v_n_524_, v___x_527_);
if (v___x_528_ == 0)
{
uint8_t v___x_529_; 
v___x_529_ = 3;
return v___x_529_;
}
else
{
uint8_t v___x_530_; 
v___x_530_ = 2;
return v___x_530_;
}
}
else
{
lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_531_ = lean_unsigned_to_nat(0u);
v___x_532_ = lean_nat_dec_le(v_n_524_, v___x_531_);
if (v___x_532_ == 0)
{
uint8_t v___x_533_; 
v___x_533_ = 1;
return v___x_533_;
}
else
{
uint8_t v___x_534_; 
v___x_534_ = 0;
return v___x_534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ofNat___boxed(lean_object* v_n_535_){
_start:
{
uint8_t v_res_536_; lean_object* v_r_537_; 
v_res_536_ = l_Lake_LogLevel_ofNat(v_n_535_);
lean_dec(v_n_535_);
v_r_537_ = lean_box(v_res_536_);
return v_r_537_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqLogLevel(uint8_t v_x_538_, uint8_t v_y_539_){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_540_ = l_Lake_LogLevel_ctorIdx(v_x_538_);
v___x_541_ = l_Lake_LogLevel_ctorIdx(v_y_539_);
v___x_542_ = lean_nat_dec_eq(v___x_540_, v___x_541_);
lean_dec(v___x_541_);
lean_dec(v___x_540_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqLogLevel___boxed(lean_object* v_x_543_, lean_object* v_y_544_){
_start:
{
uint8_t v_x_13__boxed_545_; uint8_t v_y_14__boxed_546_; uint8_t v_res_547_; lean_object* v_r_548_; 
v_x_13__boxed_545_ = lean_unbox(v_x_543_);
v_y_14__boxed_546_ = lean_unbox(v_y_544_);
v_res_547_ = l_Lake_instDecidableEqLogLevel(v_x_13__boxed_545_, v_y_14__boxed_546_);
v_r_548_ = lean_box(v_res_547_);
return v_r_548_;
}
}
LEAN_EXPORT uint8_t l_Lake_instOrdLogLevel_ord(uint8_t v_x_549_, uint8_t v_y_550_){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_551_ = l_Lake_LogLevel_ctorIdx(v_x_549_);
v___x_552_ = l_Lake_LogLevel_ctorIdx(v_y_550_);
v___x_553_ = lean_nat_dec_lt(v___x_551_, v___x_552_);
if (v___x_553_ == 0)
{
uint8_t v___x_554_; 
v___x_554_ = lean_nat_dec_eq(v___x_551_, v___x_552_);
lean_dec(v___x_552_);
lean_dec(v___x_551_);
if (v___x_554_ == 0)
{
uint8_t v___x_555_; 
v___x_555_ = 2;
return v___x_555_;
}
else
{
uint8_t v___x_556_; 
v___x_556_ = 1;
return v___x_556_;
}
}
else
{
uint8_t v___x_557_; 
lean_dec(v___x_552_);
lean_dec(v___x_551_);
v___x_557_ = 0;
return v___x_557_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instOrdLogLevel_ord___boxed(lean_object* v_x_558_, lean_object* v_y_559_){
_start:
{
uint8_t v_x_30__boxed_560_; uint8_t v_y_31__boxed_561_; uint8_t v_res_562_; lean_object* v_r_563_; 
v_x_30__boxed_560_ = lean_unbox(v_x_558_);
v_y_31__boxed_561_ = lean_unbox(v_y_559_);
v_res_562_ = l_Lake_instOrdLogLevel_ord(v_x_30__boxed_560_, v_y_31__boxed_561_);
v_r_563_ = lean_box(v_res_562_);
return v_r_563_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonLogLevel_toJson(uint8_t v_x_578_){
_start:
{
switch(v_x_578_)
{
case 0:
{
lean_object* v___x_579_; 
v___x_579_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__1));
return v___x_579_;
}
case 1:
{
lean_object* v___x_580_; 
v___x_580_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__3));
return v___x_580_;
}
case 2:
{
lean_object* v___x_581_; 
v___x_581_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__5));
return v___x_581_;
}
default: 
{
lean_object* v___x_582_; 
v___x_582_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__7));
return v___x_582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonLogLevel_toJson___boxed(lean_object* v_x_583_){
_start:
{
uint8_t v_x_88__boxed_584_; lean_object* v_res_585_; 
v_x_88__boxed_584_ = lean_unbox(v_x_583_);
v_res_585_ = l_Lake_instToJsonLogLevel_toJson(v_x_88__boxed_584_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonLogLevel_fromJson(lean_object* v_json_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_Json_getTag_x3f(v_json_606_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v___x_608_; 
v___x_608_ = ((lean_object*)(l_Lake_instFromJsonLogLevel_fromJson___closed__1));
return v___x_608_;
}
else
{
lean_object* v_val_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v_val_609_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_val_609_);
lean_dec_ref_known(v___x_607_, 1);
v___x_610_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__6));
v___x_611_ = lean_string_dec_eq(v_val_609_, v___x_610_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__0));
v___x_613_ = lean_string_dec_eq(v_val_609_, v___x_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_614_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__2));
v___x_615_ = lean_string_dec_eq(v_val_609_, v___x_614_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__4));
v___x_617_ = lean_string_dec_eq(v_val_609_, v___x_616_);
lean_dec(v_val_609_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
v___x_618_ = ((lean_object*)(l_Lake_instFromJsonLogLevel_fromJson___closed__3));
return v___x_618_;
}
else
{
lean_object* v___x_619_; 
v___x_619_ = ((lean_object*)(l_Lake_instFromJsonLogLevel_fromJson___closed__4));
return v___x_619_;
}
}
else
{
lean_object* v___x_620_; 
lean_dec(v_val_609_);
v___x_620_ = ((lean_object*)(l_Lake_instFromJsonLogLevel_fromJson___closed__5));
return v___x_620_;
}
}
else
{
lean_object* v___x_621_; 
lean_dec(v_val_609_);
v___x_621_ = ((lean_object*)(l_Lake_instFromJsonLogLevel_fromJson___closed__6));
return v___x_621_;
}
}
else
{
lean_object* v___x_622_; 
lean_dec(v_val_609_);
v___x_622_ = ((lean_object*)(l_Lake_instFromJsonLogLevel_fromJson___closed__7));
return v___x_622_;
}
}
}
}
static lean_object* _init_l_Lake_instLTLogLevel(void){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = lean_box(0);
return v___x_625_;
}
}
static lean_object* _init_l_Lake_instLELogLevel(void){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = lean_box(0);
return v___x_626_;
}
}
LEAN_EXPORT uint8_t l_Lake_instMinLogLevel___lam__0(uint8_t v_x_627_, uint8_t v_y_628_){
_start:
{
uint8_t v___x_629_; 
v___x_629_ = l_Lake_instOrdLogLevel_ord(v_x_627_, v_y_628_);
if (v___x_629_ == 2)
{
return v_y_628_;
}
else
{
return v_x_627_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMinLogLevel___lam__0___boxed(lean_object* v_x_630_, lean_object* v_y_631_){
_start:
{
uint8_t v_x_boxed_632_; uint8_t v_y_boxed_633_; uint8_t v_res_634_; lean_object* v_r_635_; 
v_x_boxed_632_ = lean_unbox(v_x_630_);
v_y_boxed_633_ = lean_unbox(v_y_631_);
v_res_634_ = l_Lake_instMinLogLevel___lam__0(v_x_boxed_632_, v_y_boxed_633_);
v_r_635_ = lean_box(v_res_634_);
return v_r_635_;
}
}
LEAN_EXPORT uint8_t l_Lake_instMaxLogLevel___lam__0(uint8_t v_x_638_, uint8_t v_y_639_){
_start:
{
uint8_t v___x_640_; 
v___x_640_ = l_Lake_instOrdLogLevel_ord(v_x_638_, v_y_639_);
if (v___x_640_ == 2)
{
return v_x_638_;
}
else
{
return v_y_639_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxLogLevel___lam__0___boxed(lean_object* v_x_641_, lean_object* v_y_642_){
_start:
{
uint8_t v_x_boxed_643_; uint8_t v_y_boxed_644_; uint8_t v_res_645_; lean_object* v_r_646_; 
v_x_boxed_643_ = lean_unbox(v_x_641_);
v_y_boxed_644_ = lean_unbox(v_y_642_);
v_res_645_ = l_Lake_instMaxLogLevel___lam__0(v_x_boxed_643_, v_y_boxed_644_);
v_r_646_ = lean_box(v_res_645_);
return v_r_646_;
}
}
LEAN_EXPORT uint32_t l_Lake_LogLevel_icon(uint8_t v_x_649_){
_start:
{
switch(v_x_649_)
{
case 2:
{
uint32_t v___x_650_; 
v___x_650_ = 9888;
return v___x_650_;
}
case 3:
{
uint32_t v___x_651_; 
v___x_651_ = 10006;
return v___x_651_;
}
default: 
{
uint32_t v___x_652_; 
v___x_652_ = 8505;
return v___x_652_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_icon___boxed(lean_object* v_x_653_){
_start:
{
uint8_t v_x_33__boxed_654_; uint32_t v_res_655_; lean_object* v_r_656_; 
v_x_33__boxed_654_ = lean_unbox(v_x_653_);
v_res_655_ = l_Lake_LogLevel_icon(v_x_33__boxed_654_);
v_r_656_ = lean_box_uint32(v_res_655_);
return v_r_656_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ansiColor(uint8_t v_x_660_){
_start:
{
switch(v_x_660_)
{
case 2:
{
lean_object* v___x_661_; 
v___x_661_ = ((lean_object*)(l_Lake_LogLevel_ansiColor___closed__0));
return v___x_661_;
}
case 3:
{
lean_object* v___x_662_; 
v___x_662_ = ((lean_object*)(l_Lake_LogLevel_ansiColor___closed__1));
return v___x_662_;
}
default: 
{
lean_object* v___x_663_; 
v___x_663_ = ((lean_object*)(l_Lake_LogLevel_ansiColor___closed__2));
return v___x_663_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ansiColor___boxed(lean_object* v_x_664_){
_start:
{
uint8_t v_x_36__boxed_665_; lean_object* v_res_666_; 
v_x_36__boxed_665_ = lean_unbox(v_x_664_);
v_res_666_ = l_Lake_LogLevel_ansiColor(v_x_36__boxed_665_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00Lake_LogLevel_ofString_x3f_spec__0(lean_object* v_s_667_, lean_object* v_p_668_){
_start:
{
uint32_t v___y_670_; lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = lean_string_utf8_byte_size(v_s_667_);
v___x_676_ = lean_nat_dec_eq(v_p_668_, v___x_675_);
if (v___x_676_ == 0)
{
uint32_t v___x_677_; uint32_t v___x_678_; uint8_t v___x_679_; 
v___x_677_ = lean_string_utf8_get_fast(v_s_667_, v_p_668_);
v___x_678_ = 65;
v___x_679_ = lean_uint32_dec_le(v___x_678_, v___x_677_);
if (v___x_679_ == 0)
{
v___y_670_ = v___x_677_;
goto v___jp_669_;
}
else
{
uint32_t v___x_680_; uint8_t v___x_681_; 
v___x_680_ = 90;
v___x_681_ = lean_uint32_dec_le(v___x_677_, v___x_680_);
if (v___x_681_ == 0)
{
v___y_670_ = v___x_677_;
goto v___jp_669_;
}
else
{
uint32_t v___x_682_; uint32_t v___x_683_; 
v___x_682_ = 32;
v___x_683_ = lean_uint32_add(v___x_677_, v___x_682_);
v___y_670_ = v___x_683_;
goto v___jp_669_;
}
}
}
else
{
lean_dec(v_p_668_);
return v_s_667_;
}
v___jp_669_:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
lean_inc(v_p_668_);
v___x_671_ = lean_string_utf8_set(v_s_667_, v_p_668_, v___y_670_);
v___x_672_ = l_Char_utf8Size(v___y_670_);
v___x_673_ = lean_nat_add(v_p_668_, v___x_672_);
lean_dec(v___x_672_);
lean_dec(v_p_668_);
v_s_667_ = v___x_671_;
v_p_668_ = v___x_673_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ofString_x3f(lean_object* v_s_698_){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = l_String_mapAux___at___00Lake_LogLevel_ofString_x3f_spec__0(v_s_698_, v___x_703_);
v___x_705_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__0));
v___x_706_ = lean_string_dec_eq(v___x_704_, v___x_705_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_707_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__2));
v___x_708_ = lean_string_dec_eq(v___x_704_, v___x_707_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; uint8_t v___x_710_; 
v___x_709_ = ((lean_object*)(l_Lake_LogLevel_ofString_x3f___closed__2));
v___x_710_ = lean_string_dec_eq(v___x_704_, v___x_709_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_711_ = ((lean_object*)(l_Lake_LogLevel_ofString_x3f___closed__3));
v___x_712_ = lean_string_dec_eq(v___x_704_, v___x_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_713_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__4));
v___x_714_ = lean_string_dec_eq(v___x_704_, v___x_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_715_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__6));
v___x_716_ = lean_string_dec_eq(v___x_704_, v___x_715_);
lean_dec_ref(v___x_704_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; 
v___x_717_ = lean_box(0);
return v___x_717_;
}
else
{
lean_object* v___x_718_; 
v___x_718_ = ((lean_object*)(l_Lake_LogLevel_ofString_x3f___closed__4));
return v___x_718_;
}
}
else
{
lean_dec_ref(v___x_704_);
goto v___jp_701_;
}
}
else
{
lean_dec_ref(v___x_704_);
goto v___jp_701_;
}
}
else
{
lean_dec_ref(v___x_704_);
goto v___jp_699_;
}
}
else
{
lean_dec_ref(v___x_704_);
goto v___jp_699_;
}
}
else
{
lean_object* v___x_719_; 
lean_dec_ref(v___x_704_);
v___x_719_ = ((lean_object*)(l_Lake_LogLevel_ofString_x3f___closed__5));
return v___x_719_;
}
v___jp_699_:
{
lean_object* v___x_700_; 
v___x_700_ = ((lean_object*)(l_Lake_LogLevel_ofString_x3f___closed__0));
return v___x_700_;
}
v___jp_701_:
{
lean_object* v___x_702_; 
v___x_702_ = ((lean_object*)(l_Lake_LogLevel_ofString_x3f___closed__1));
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_toString(uint8_t v_x_720_){
_start:
{
switch(v_x_720_)
{
case 0:
{
lean_object* v___x_721_; 
v___x_721_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__0));
return v___x_721_;
}
case 1:
{
lean_object* v___x_722_; 
v___x_722_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__2));
return v___x_722_;
}
case 2:
{
lean_object* v___x_723_; 
v___x_723_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__4));
return v___x_723_;
}
default: 
{
lean_object* v___x_724_; 
v___x_724_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__6));
return v___x_724_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_toString___boxed(lean_object* v_x_725_){
_start:
{
uint8_t v_x_36__boxed_726_; lean_object* v_res_727_; 
v_x_36__boxed_726_ = lean_unbox(v_x_725_);
v_res_727_ = l_Lake_LogLevel_toString(v_x_36__boxed_726_);
return v_res_727_;
}
}
LEAN_EXPORT uint8_t l_Lake_LogLevel_ofMessageSeverity(uint8_t v_x_730_){
_start:
{
switch(v_x_730_)
{
case 0:
{
uint8_t v___x_731_; 
v___x_731_ = 1;
return v___x_731_;
}
case 1:
{
uint8_t v___x_732_; 
v___x_732_ = 2;
return v___x_732_;
}
default: 
{
uint8_t v___x_733_; 
v___x_733_ = 3;
return v___x_733_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ofMessageSeverity___boxed(lean_object* v_x_734_){
_start:
{
uint8_t v_x_25__boxed_735_; uint8_t v_res_736_; lean_object* v_r_737_; 
v_x_25__boxed_735_ = lean_unbox(v_x_734_);
v_res_736_ = l_Lake_LogLevel_ofMessageSeverity(v_x_25__boxed_735_);
v_r_737_ = lean_box(v_res_736_);
return v_r_737_;
}
}
LEAN_EXPORT uint8_t l_Lake_LogLevel_toMessageSeverity(uint8_t v_x_738_){
_start:
{
switch(v_x_738_)
{
case 2:
{
uint8_t v___x_739_; 
v___x_739_ = 1;
return v___x_739_;
}
case 3:
{
uint8_t v___x_740_; 
v___x_740_ = 2;
return v___x_740_;
}
default: 
{
uint8_t v___x_741_; 
v___x_741_ = 0;
return v___x_741_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_toMessageSeverity___boxed(lean_object* v_x_742_){
_start:
{
uint8_t v_x_30__boxed_743_; uint8_t v_res_744_; lean_object* v_r_745_; 
v_x_30__boxed_743_ = lean_unbox(v_x_742_);
v_res_744_ = l_Lake_LogLevel_toMessageSeverity(v_x_30__boxed_743_);
v_r_745_ = lean_box(v_res_744_);
return v_r_745_;
}
}
LEAN_EXPORT uint8_t l_Lake_Verbosity_minLogLv(uint8_t v_x_746_){
_start:
{
switch(v_x_746_)
{
case 0:
{
uint8_t v___x_747_; 
v___x_747_ = 2;
return v___x_747_;
}
case 1:
{
uint8_t v___x_748_; 
v___x_748_ = 1;
return v___x_748_;
}
default: 
{
uint8_t v___x_749_; 
v___x_749_ = 0;
return v___x_749_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_minLogLv___boxed(lean_object* v_x_750_){
_start:
{
uint8_t v_x_25__boxed_751_; uint8_t v_res_752_; lean_object* v_r_753_; 
v_x_25__boxed_751_ = lean_unbox(v_x_750_);
v_res_752_ = l_Lake_Verbosity_minLogLv(v_x_25__boxed_751_);
v_r_753_ = lean_box(v_res_752_);
return v_r_753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_instToJsonLogEntry_toJson_spec__0(lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
if (lean_obj_tag(v_a_760_) == 0)
{
lean_object* v___x_762_; 
v___x_762_ = lean_array_to_list(v_a_761_);
return v___x_762_;
}
else
{
lean_object* v_head_763_; lean_object* v_tail_764_; lean_object* v___x_765_; 
v_head_763_ = lean_ctor_get(v_a_760_, 0);
lean_inc(v_head_763_);
v_tail_764_ = lean_ctor_get(v_a_760_, 1);
lean_inc(v_tail_764_);
lean_dec_ref_known(v_a_760_, 2);
v___x_765_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_761_, v_head_763_);
v_a_760_ = v_tail_764_;
v_a_761_ = v___x_765_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonLogEntry_toJson(lean_object* v_x_771_){
_start:
{
uint8_t v_level_772_; lean_object* v_message_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_level_772_ = lean_ctor_get_uint8(v_x_771_, sizeof(void*)*1);
v_message_773_ = lean_ctor_get(v_x_771_, 0);
v___x_774_ = ((lean_object*)(l_Lake_instToJsonLogEntry_toJson___closed__0));
v___x_775_ = l_Lake_instToJsonLogLevel_toJson(v_level_772_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_774_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = lean_box(0);
v___x_778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_776_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = ((lean_object*)(l_Lake_instToJsonLogEntry_toJson___closed__1));
lean_inc_ref(v_message_773_);
v___x_780_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_780_, 0, v_message_773_);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_779_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
lean_ctor_set(v___x_782_, 1, v___x_777_);
v___x_783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
lean_ctor_set(v___x_783_, 1, v___x_777_);
v___x_784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_778_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = ((lean_object*)(l_Lake_instToJsonLogEntry_toJson___closed__2));
v___x_786_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_instToJsonLogEntry_toJson_spec__0(v___x_784_, v___x_785_);
v___x_787_ = l_Lean_Json_mkObj(v___x_786_);
lean_dec(v___x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonLogEntry_toJson___boxed(lean_object* v_x_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lake_instToJsonLogEntry_toJson(v_x_788_);
lean_dec_ref(v_x_788_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__0(lean_object* v_j_792_, lean_object* v_k_793_){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = l_Lean_Json_getObjValD(v_j_792_, v_k_793_);
v___x_795_ = l_Lake_instFromJsonLogLevel_fromJson(v___x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__0___boxed(lean_object* v_j_796_, lean_object* v_k_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__0(v_j_796_, v_k_797_);
lean_dec_ref(v_k_797_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1(lean_object* v_j_799_, lean_object* v_k_800_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = l_Lean_Json_getObjValD(v_j_799_, v_k_800_);
v___x_802_ = l_Lean_Json_getStr_x3f(v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1___boxed(lean_object* v_j_803_, lean_object* v_k_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1(v_j_803_, v_k_804_);
lean_dec_ref(v_k_804_);
return v_res_805_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__3(void){
_start:
{
uint8_t v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_811_ = 1;
v___x_812_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__2));
v___x_813_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_812_, v___x_811_);
return v___x_813_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__5(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_815_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__4));
v___x_816_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__3, &l_Lake_instFromJsonLogEntry_fromJson___closed__3_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__3);
v___x_817_ = lean_string_append(v___x_816_, v___x_815_);
return v___x_817_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__7(void){
_start:
{
uint8_t v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = 1;
v___x_821_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__6));
v___x_822_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_821_, v___x_820_);
return v___x_822_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__8(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_823_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__7, &l_Lake_instFromJsonLogEntry_fromJson___closed__7_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__7);
v___x_824_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__5, &l_Lake_instFromJsonLogEntry_fromJson___closed__5_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__5);
v___x_825_ = lean_string_append(v___x_824_, v___x_823_);
return v___x_825_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__10(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_827_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__9));
v___x_828_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__8, &l_Lake_instFromJsonLogEntry_fromJson___closed__8_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__8);
v___x_829_ = lean_string_append(v___x_828_, v___x_827_);
return v___x_829_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__12(void){
_start:
{
uint8_t v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_832_ = 1;
v___x_833_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__11));
v___x_834_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_833_, v___x_832_);
return v___x_834_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__13(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_835_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__12, &l_Lake_instFromJsonLogEntry_fromJson___closed__12_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__12);
v___x_836_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__5, &l_Lake_instFromJsonLogEntry_fromJson___closed__5_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__5);
v___x_837_ = lean_string_append(v___x_836_, v___x_835_);
return v___x_837_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__14(void){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_838_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__9));
v___x_839_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__13, &l_Lake_instFromJsonLogEntry_fromJson___closed__13_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__13);
v___x_840_ = lean_string_append(v___x_839_, v___x_838_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonLogEntry_fromJson(lean_object* v_json_841_){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = ((lean_object*)(l_Lake_instToJsonLogEntry_toJson___closed__0));
lean_inc(v_json_841_);
v___x_843_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__0(v_json_841_, v___x_842_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_853_; 
lean_dec(v_json_841_);
v_a_844_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_853_ == 0)
{
v___x_846_ = v___x_843_;
v_isShared_847_ = v_isSharedCheck_853_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_843_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_853_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_848_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__10, &l_Lake_instFromJsonLogEntry_fromJson___closed__10_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__10);
v___x_849_ = lean_string_append(v___x_848_, v_a_844_);
lean_dec(v_a_844_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_849_);
v___x_851_ = v___x_846_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
else
{
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
lean_dec(v_json_841_);
v_a_854_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_843_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_843_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
lean_ctor_set_tag(v___x_856_, 0);
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v_a_862_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_862_);
lean_dec_ref_known(v___x_843_, 1);
v___x_863_ = ((lean_object*)(l_Lake_instToJsonLogEntry_toJson___closed__1));
v___x_864_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1(v_json_841_, v___x_863_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_874_; 
lean_dec(v_a_862_);
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_874_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_874_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_874_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_869_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__14, &l_Lake_instFromJsonLogEntry_fromJson___closed__14_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__14);
v___x_870_ = lean_string_append(v___x_869_, v_a_865_);
lean_dec(v_a_865_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_870_);
v___x_872_ = v___x_867_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
else
{
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec(v_a_862_);
v_a_875_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_864_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_864_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
lean_ctor_set_tag(v___x_877_, 0);
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
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
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_892_; 
v_a_883_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_892_ == 0)
{
v___x_885_ = v___x_864_;
v_isShared_886_ = v_isSharedCheck_892_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_864_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_892_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; uint8_t v___x_888_; lean_object* v___x_890_; 
v___x_887_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_887_, 0, v_a_883_);
v___x_888_ = lean_unbox(v_a_862_);
lean_dec(v_a_862_);
lean_ctor_set_uint8(v___x_887_, sizeof(void*)*1, v___x_888_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_887_);
v___x_890_ = v___x_885_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_887_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_toString(lean_object* v_self_897_, uint8_t v_useAnsi_898_){
_start:
{
if (v_useAnsi_898_ == 0)
{
uint8_t v_level_899_; lean_object* v_message_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v_level_899_ = lean_ctor_get_uint8(v_self_897_, sizeof(void*)*1);
v_message_900_ = lean_ctor_get(v_self_897_, 0);
v___x_901_ = l_Lake_LogLevel_toString(v_level_899_);
v___x_902_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__9));
v___x_903_ = lean_string_append(v___x_901_, v___x_902_);
v___x_904_ = lean_string_append(v___x_903_, v_message_900_);
return v___x_904_;
}
else
{
uint8_t v_level_905_; lean_object* v_message_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v_pre_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v_level_905_ = lean_ctor_get_uint8(v_self_897_, sizeof(void*)*1);
v_message_906_ = lean_ctor_get(v_self_897_, 0);
v___x_907_ = l_Lake_LogLevel_ansiColor(v_level_905_);
v___x_908_ = l_Lake_LogLevel_toString(v_level_905_);
v___x_909_ = ((lean_object*)(l_Lake_LogEntry_toString___closed__0));
v___x_910_ = lean_string_append(v___x_908_, v___x_909_);
v_pre_911_ = l_Lake_Ansi_chalk(v___x_907_, v___x_910_);
lean_dec_ref(v___x_910_);
lean_dec_ref(v___x_907_);
v___x_912_ = ((lean_object*)(l_Lake_LogEntry_toString___closed__1));
v___x_913_ = lean_string_append(v_pre_911_, v___x_912_);
v___x_914_ = lean_string_append(v___x_913_, v_message_906_);
return v___x_914_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_toString___boxed(lean_object* v_self_915_, lean_object* v_useAnsi_916_){
_start:
{
uint8_t v_useAnsi_boxed_917_; lean_object* v_res_918_; 
v_useAnsi_boxed_917_ = lean_unbox(v_useAnsi_916_);
v_res_918_ = l_Lake_LogEntry_toString(v_self_915_, v_useAnsi_boxed_917_);
lean_dec_ref(v_self_915_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToStringLogEntry___lam__0(lean_object* v_self_919_){
_start:
{
uint8_t v___x_920_; lean_object* v___x_921_; 
v___x_920_ = 0;
v___x_921_ = l_Lake_LogEntry_toString(v_self_919_, v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToStringLogEntry___lam__0___boxed(lean_object* v_self_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lake_instToStringLogEntry___lam__0(v_self_922_);
lean_dec_ref(v_self_922_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_trace(lean_object* v_message_926_){
_start:
{
uint8_t v___x_927_; lean_object* v___x_928_; 
v___x_927_ = 0;
v___x_928_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_928_, 0, v_message_926_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*1, v___x_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_info(lean_object* v_message_929_){
_start:
{
uint8_t v___x_930_; lean_object* v___x_931_; 
v___x_930_ = 1;
v___x_931_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_931_, 0, v_message_929_);
lean_ctor_set_uint8(v___x_931_, sizeof(void*)*1, v___x_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_warning(lean_object* v_message_932_){
_start:
{
uint8_t v___x_933_; lean_object* v___x_934_; 
v___x_933_ = 2;
v___x_934_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_934_, 0, v_message_932_);
lean_ctor_set_uint8(v___x_934_, sizeof(void*)*1, v___x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_error(lean_object* v_message_935_){
_start:
{
uint8_t v___x_936_; lean_object* v___x_937_; 
v___x_936_ = 3;
v___x_937_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_937_, 0, v_message_935_);
lean_ctor_set_uint8(v___x_937_, sizeof(void*)*1, v___x_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_ofSerialMessage(lean_object* v_msg_939_){
_start:
{
lean_object* v_toBaseMessage_940_; lean_object* v_fileName_941_; lean_object* v_pos_942_; uint8_t v_severity_943_; lean_object* v_caption_944_; lean_object* v_data_945_; lean_object* v___y_947_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v_startInclusive_956_; lean_object* v_endExclusive_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v_toBaseMessage_940_ = lean_ctor_get(v_msg_939_, 0);
lean_inc_ref(v_toBaseMessage_940_);
lean_dec_ref(v_msg_939_);
v_fileName_941_ = lean_ctor_get(v_toBaseMessage_940_, 0);
lean_inc_ref(v_fileName_941_);
v_pos_942_ = lean_ctor_get(v_toBaseMessage_940_, 1);
lean_inc_ref(v_pos_942_);
v_severity_943_ = lean_ctor_get_uint8(v_toBaseMessage_940_, sizeof(void*)*5 + 1);
v_caption_944_ = lean_ctor_get(v_toBaseMessage_940_, 3);
lean_inc_ref(v_caption_944_);
v_data_945_ = lean_ctor_get(v_toBaseMessage_940_, 4);
lean_inc(v_data_945_);
lean_dec_ref(v_toBaseMessage_940_);
v___x_952_ = lean_unsigned_to_nat(0u);
v___x_953_ = lean_string_utf8_byte_size(v_caption_944_);
v___x_954_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_954_, 0, v_caption_944_);
lean_ctor_set(v___x_954_, 1, v___x_952_);
lean_ctor_set(v___x_954_, 2, v___x_953_);
v___x_955_ = l_String_Slice_trimAscii(v___x_954_);
v_startInclusive_956_ = lean_ctor_get(v___x_955_, 1);
lean_inc(v_startInclusive_956_);
v_endExclusive_957_ = lean_ctor_get(v___x_955_, 2);
lean_inc(v_endExclusive_957_);
v___x_958_ = lean_nat_sub(v_endExclusive_957_, v_startInclusive_956_);
lean_dec(v_startInclusive_956_);
lean_dec(v_endExclusive_957_);
v___x_959_ = lean_nat_dec_eq(v___x_958_, v___x_952_);
lean_dec(v___x_958_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_973_; 
v___x_960_ = l_String_Slice_toString(v___x_955_);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_973_ == 0)
{
lean_object* v_unused_974_; lean_object* v_unused_975_; lean_object* v_unused_976_; 
v_unused_974_ = lean_ctor_get(v___x_955_, 2);
lean_dec(v_unused_974_);
v_unused_975_ = lean_ctor_get(v___x_955_, 1);
lean_dec(v_unused_975_);
v_unused_976_ = lean_ctor_get(v___x_955_, 0);
lean_dec(v_unused_976_);
v___x_962_ = v___x_955_;
v_isShared_963_ = v_isSharedCheck_973_;
goto v_resetjp_961_;
}
else
{
lean_dec(v___x_955_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_973_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_964_ = ((lean_object*)(l_Lake_LogEntry_ofSerialMessage___closed__0));
v___x_965_ = lean_string_append(v___x_960_, v___x_964_);
v___x_966_ = lean_string_utf8_byte_size(v_data_945_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 2, v___x_966_);
lean_ctor_set(v___x_962_, 1, v___x_952_);
lean_ctor_set(v___x_962_, 0, v_data_945_);
v___x_968_ = v___x_962_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_data_945_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v___x_952_);
lean_ctor_set(v_reuseFailAlloc_972_, 2, v___x_966_);
v___x_968_ = v_reuseFailAlloc_972_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_969_ = l_String_Slice_trimAscii(v___x_968_);
v___x_970_ = l_String_Slice_toString(v___x_969_);
lean_dec_ref(v___x_969_);
v___x_971_ = lean_string_append(v___x_965_, v___x_970_);
lean_dec_ref(v___x_970_);
v___y_947_ = v___x_971_;
goto v___jp_946_;
}
}
}
else
{
lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_989_; 
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_989_ == 0)
{
lean_object* v_unused_990_; lean_object* v_unused_991_; lean_object* v_unused_992_; 
v_unused_990_ = lean_ctor_get(v___x_955_, 2);
lean_dec(v_unused_990_);
v_unused_991_ = lean_ctor_get(v___x_955_, 1);
lean_dec(v_unused_991_);
v_unused_992_ = lean_ctor_get(v___x_955_, 0);
lean_dec(v_unused_992_);
v___x_978_ = v___x_955_;
v_isShared_979_ = v_isSharedCheck_989_;
goto v_resetjp_977_;
}
else
{
lean_dec(v___x_955_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_989_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_980_ = lean_string_utf8_byte_size(v_data_945_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 2, v___x_980_);
lean_ctor_set(v___x_978_, 1, v___x_952_);
lean_ctor_set(v___x_978_, 0, v_data_945_);
v___x_982_ = v___x_978_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_data_945_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v___x_952_);
lean_ctor_set(v_reuseFailAlloc_988_, 2, v___x_980_);
v___x_982_ = v_reuseFailAlloc_988_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_983_; lean_object* v_str_984_; lean_object* v_startInclusive_985_; lean_object* v_endExclusive_986_; lean_object* v___x_987_; 
v___x_983_ = l_String_Slice_trimAscii(v___x_982_);
v_str_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc_ref(v_str_984_);
v_startInclusive_985_ = lean_ctor_get(v___x_983_, 1);
lean_inc(v_startInclusive_985_);
v_endExclusive_986_ = lean_ctor_get(v___x_983_, 2);
lean_inc(v_endExclusive_986_);
lean_dec_ref(v___x_983_);
v___x_987_ = lean_string_utf8_extract_fast(v_str_984_, v_startInclusive_985_, v_endExclusive_986_);
lean_dec(v_endExclusive_986_);
lean_dec(v_startInclusive_985_);
lean_dec_ref(v_str_984_);
v___y_947_ = v___x_987_;
goto v___jp_946_;
}
}
}
v___jp_946_:
{
uint8_t v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_948_ = l_Lake_LogLevel_ofMessageSeverity(v_severity_943_);
v___x_949_ = lean_box(0);
v___x_950_ = l_Lean_mkErrorStringWithPos(v_fileName_941_, v_pos_942_, v___y_947_, v___x_949_, v___x_949_, v___x_949_);
lean_dec_ref(v___y_947_);
v___x_951_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set_uint8(v___x_951_, sizeof(void*)*1, v___x_948_);
return v___x_951_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_ofMessage(lean_object* v_msg_993_){
_start:
{
lean_object* v_fileName_995_; lean_object* v_pos_996_; uint8_t v_severity_997_; lean_object* v_caption_998_; lean_object* v_data_999_; lean_object* v___x_1000_; lean_object* v___y_1002_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v_startInclusive_1011_; lean_object* v_endExclusive_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
v_fileName_995_ = lean_ctor_get(v_msg_993_, 0);
lean_inc_ref(v_fileName_995_);
v_pos_996_ = lean_ctor_get(v_msg_993_, 1);
lean_inc_ref(v_pos_996_);
v_severity_997_ = lean_ctor_get_uint8(v_msg_993_, sizeof(void*)*5 + 1);
v_caption_998_ = lean_ctor_get(v_msg_993_, 3);
lean_inc_ref(v_caption_998_);
v_data_999_ = lean_ctor_get(v_msg_993_, 4);
lean_inc(v_data_999_);
lean_dec_ref(v_msg_993_);
v___x_1000_ = l_Lean_MessageData_toString(v_data_999_);
v___x_1007_ = lean_unsigned_to_nat(0u);
v___x_1008_ = lean_string_utf8_byte_size(v_caption_998_);
v___x_1009_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1009_, 0, v_caption_998_);
lean_ctor_set(v___x_1009_, 1, v___x_1007_);
lean_ctor_set(v___x_1009_, 2, v___x_1008_);
v___x_1010_ = l_String_Slice_trimAscii(v___x_1009_);
v_startInclusive_1011_ = lean_ctor_get(v___x_1010_, 1);
lean_inc(v_startInclusive_1011_);
v_endExclusive_1012_ = lean_ctor_get(v___x_1010_, 2);
lean_inc(v_endExclusive_1012_);
v___x_1013_ = lean_nat_sub(v_endExclusive_1012_, v_startInclusive_1011_);
lean_dec(v_startInclusive_1011_);
lean_dec(v_endExclusive_1012_);
v___x_1014_ = lean_nat_dec_eq(v___x_1013_, v___x_1007_);
lean_dec(v___x_1013_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1028_; 
v___x_1015_ = l_String_Slice_toString(v___x_1010_);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1028_ == 0)
{
lean_object* v_unused_1029_; lean_object* v_unused_1030_; lean_object* v_unused_1031_; 
v_unused_1029_ = lean_ctor_get(v___x_1010_, 2);
lean_dec(v_unused_1029_);
v_unused_1030_ = lean_ctor_get(v___x_1010_, 1);
lean_dec(v_unused_1030_);
v_unused_1031_ = lean_ctor_get(v___x_1010_, 0);
lean_dec(v_unused_1031_);
v___x_1017_ = v___x_1010_;
v_isShared_1018_ = v_isSharedCheck_1028_;
goto v_resetjp_1016_;
}
else
{
lean_dec(v___x_1010_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1028_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1019_ = ((lean_object*)(l_Lake_LogEntry_ofSerialMessage___closed__0));
v___x_1020_ = lean_string_append(v___x_1015_, v___x_1019_);
v___x_1021_ = lean_string_utf8_byte_size(v___x_1000_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 2, v___x_1021_);
lean_ctor_set(v___x_1017_, 1, v___x_1007_);
lean_ctor_set(v___x_1017_, 0, v___x_1000_);
v___x_1023_ = v___x_1017_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1000_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v___x_1007_);
lean_ctor_set(v_reuseFailAlloc_1027_, 2, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1024_ = l_String_Slice_trimAscii(v___x_1023_);
v___x_1025_ = l_String_Slice_toString(v___x_1024_);
lean_dec_ref(v___x_1024_);
v___x_1026_ = lean_string_append(v___x_1020_, v___x_1025_);
lean_dec_ref(v___x_1025_);
v___y_1002_ = v___x_1026_;
goto v___jp_1001_;
}
}
}
else
{
lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1044_; 
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1044_ == 0)
{
lean_object* v_unused_1045_; lean_object* v_unused_1046_; lean_object* v_unused_1047_; 
v_unused_1045_ = lean_ctor_get(v___x_1010_, 2);
lean_dec(v_unused_1045_);
v_unused_1046_ = lean_ctor_get(v___x_1010_, 1);
lean_dec(v_unused_1046_);
v_unused_1047_ = lean_ctor_get(v___x_1010_, 0);
lean_dec(v_unused_1047_);
v___x_1033_ = v___x_1010_;
v_isShared_1034_ = v_isSharedCheck_1044_;
goto v_resetjp_1032_;
}
else
{
lean_dec(v___x_1010_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1044_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1035_ = lean_string_utf8_byte_size(v___x_1000_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 2, v___x_1035_);
lean_ctor_set(v___x_1033_, 1, v___x_1007_);
lean_ctor_set(v___x_1033_, 0, v___x_1000_);
v___x_1037_ = v___x_1033_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1000_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v___x_1007_);
lean_ctor_set(v_reuseFailAlloc_1043_, 2, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1038_; lean_object* v_str_1039_; lean_object* v_startInclusive_1040_; lean_object* v_endExclusive_1041_; lean_object* v___x_1042_; 
v___x_1038_ = l_String_Slice_trimAscii(v___x_1037_);
v_str_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc_ref(v_str_1039_);
v_startInclusive_1040_ = lean_ctor_get(v___x_1038_, 1);
lean_inc(v_startInclusive_1040_);
v_endExclusive_1041_ = lean_ctor_get(v___x_1038_, 2);
lean_inc(v_endExclusive_1041_);
lean_dec_ref(v___x_1038_);
v___x_1042_ = lean_string_utf8_extract_fast(v_str_1039_, v_startInclusive_1040_, v_endExclusive_1041_);
lean_dec(v_endExclusive_1041_);
lean_dec(v_startInclusive_1040_);
lean_dec_ref(v_str_1039_);
v___y_1002_ = v___x_1042_;
goto v___jp_1001_;
}
}
}
v___jp_1001_:
{
uint8_t v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1003_ = l_Lake_LogLevel_ofMessageSeverity(v_severity_997_);
v___x_1004_ = lean_box(0);
v___x_1005_ = l_Lean_mkErrorStringWithPos(v_fileName_995_, v_pos_996_, v___y_1002_, v___x_1004_, v___x_1004_, v___x_1004_);
lean_dec_ref(v___y_1002_);
v___x_1006_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set_uint8(v___x_1006_, sizeof(void*)*1, v___x_1003_);
return v___x_1006_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_ofMessage___boxed(lean_object* v_msg_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lake_LogEntry_ofMessage(v_msg_1048_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lake_logVerbose___redArg(lean_object* v_inst_1051_, lean_object* v_message_1052_){
_start:
{
uint8_t v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1053_ = 0;
v___x_1054_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1054_, 0, v_message_1052_);
lean_ctor_set_uint8(v___x_1054_, sizeof(void*)*1, v___x_1053_);
v___x_1055_ = lean_apply_1(v_inst_1051_, v___x_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lake_logVerbose(lean_object* v_m_1056_, lean_object* v_inst_1057_, lean_object* v_inst_1058_, lean_object* v_message_1059_){
_start:
{
uint8_t v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1060_ = 0;
v___x_1061_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1061_, 0, v_message_1059_);
lean_ctor_set_uint8(v___x_1061_, sizeof(void*)*1, v___x_1060_);
v___x_1062_ = lean_apply_1(v_inst_1058_, v___x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lake_logVerbose___boxed(lean_object* v_m_1063_, lean_object* v_inst_1064_, lean_object* v_inst_1065_, lean_object* v_message_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lake_logVerbose(v_m_1063_, v_inst_1064_, v_inst_1065_, v_message_1066_);
lean_dec_ref(v_inst_1064_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lake_logInfo___redArg(lean_object* v_inst_1068_, lean_object* v_message_1069_){
_start:
{
uint8_t v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1070_ = 1;
v___x_1071_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1071_, 0, v_message_1069_);
lean_ctor_set_uint8(v___x_1071_, sizeof(void*)*1, v___x_1070_);
v___x_1072_ = lean_apply_1(v_inst_1068_, v___x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lake_logInfo(lean_object* v_m_1073_, lean_object* v_inst_1074_, lean_object* v_inst_1075_, lean_object* v_message_1076_){
_start:
{
uint8_t v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1077_ = 1;
v___x_1078_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1078_, 0, v_message_1076_);
lean_ctor_set_uint8(v___x_1078_, sizeof(void*)*1, v___x_1077_);
v___x_1079_ = lean_apply_1(v_inst_1075_, v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lake_logInfo___boxed(lean_object* v_m_1080_, lean_object* v_inst_1081_, lean_object* v_inst_1082_, lean_object* v_message_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lake_logInfo(v_m_1080_, v_inst_1081_, v_inst_1082_, v_message_1083_);
lean_dec_ref(v_inst_1081_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lake_logWarning___redArg(lean_object* v_inst_1085_, lean_object* v_message_1086_){
_start:
{
uint8_t v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1087_ = 2;
v___x_1088_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1088_, 0, v_message_1086_);
lean_ctor_set_uint8(v___x_1088_, sizeof(void*)*1, v___x_1087_);
v___x_1089_ = lean_apply_1(v_inst_1085_, v___x_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lake_logWarning(lean_object* v_m_1090_, lean_object* v_inst_1091_, lean_object* v_message_1092_){
_start:
{
uint8_t v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1093_ = 2;
v___x_1094_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1094_, 0, v_message_1092_);
lean_ctor_set_uint8(v___x_1094_, sizeof(void*)*1, v___x_1093_);
v___x_1095_ = lean_apply_1(v_inst_1091_, v___x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lake_logError___redArg(lean_object* v_inst_1096_, lean_object* v_message_1097_){
_start:
{
uint8_t v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1098_ = 3;
v___x_1099_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1099_, 0, v_message_1097_);
lean_ctor_set_uint8(v___x_1099_, sizeof(void*)*1, v___x_1098_);
v___x_1100_ = lean_apply_1(v_inst_1096_, v___x_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lake_logError(lean_object* v_m_1101_, lean_object* v_inst_1102_, lean_object* v_message_1103_){
_start:
{
uint8_t v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1104_ = 3;
v___x_1105_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1105_, 0, v_message_1103_);
lean_ctor_set_uint8(v___x_1105_, sizeof(void*)*1, v___x_1104_);
v___x_1106_ = lean_apply_1(v_inst_1102_, v___x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lake_logSerialMessage___redArg(lean_object* v_msg_1107_, lean_object* v_inst_1108_, lean_object* v_inst_1109_){
_start:
{
lean_object* v_toBaseMessage_1110_; uint8_t v_isSilent_1111_; 
v_toBaseMessage_1110_ = lean_ctor_get(v_msg_1107_, 0);
v_isSilent_1111_ = lean_ctor_get_uint8(v_toBaseMessage_1110_, sizeof(void*)*5 + 2);
if (v_isSilent_1111_ == 0)
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
lean_dec_ref(v_inst_1108_);
v___x_1112_ = l_Lake_LogEntry_ofSerialMessage(v_msg_1107_);
v___x_1113_ = lean_apply_1(v_inst_1109_, v___x_1112_);
return v___x_1113_;
}
else
{
lean_object* v_toApplicative_1114_; lean_object* v_toPure_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
lean_dec(v_inst_1109_);
lean_dec_ref(v_msg_1107_);
v_toApplicative_1114_ = lean_ctor_get(v_inst_1108_, 0);
lean_inc_ref(v_toApplicative_1114_);
lean_dec_ref(v_inst_1108_);
v_toPure_1115_ = lean_ctor_get(v_toApplicative_1114_, 1);
lean_inc(v_toPure_1115_);
lean_dec_ref(v_toApplicative_1114_);
v___x_1116_ = lean_box(0);
v___x_1117_ = lean_apply_2(v_toPure_1115_, lean_box(0), v___x_1116_);
return v___x_1117_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logSerialMessage(lean_object* v_m_1118_, lean_object* v_msg_1119_, lean_object* v_inst_1120_, lean_object* v_inst_1121_){
_start:
{
lean_object* v_toBaseMessage_1122_; uint8_t v_isSilent_1123_; 
v_toBaseMessage_1122_ = lean_ctor_get(v_msg_1119_, 0);
v_isSilent_1123_ = lean_ctor_get_uint8(v_toBaseMessage_1122_, sizeof(void*)*5 + 2);
if (v_isSilent_1123_ == 0)
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
lean_dec_ref(v_inst_1120_);
v___x_1124_ = l_Lake_LogEntry_ofSerialMessage(v_msg_1119_);
v___x_1125_ = lean_apply_1(v_inst_1121_, v___x_1124_);
return v___x_1125_;
}
else
{
lean_object* v_toApplicative_1126_; lean_object* v_toPure_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
lean_dec(v_inst_1121_);
lean_dec_ref(v_msg_1119_);
v_toApplicative_1126_ = lean_ctor_get(v_inst_1120_, 0);
lean_inc_ref(v_toApplicative_1126_);
lean_dec_ref(v_inst_1120_);
v_toPure_1127_ = lean_ctor_get(v_toApplicative_1126_, 1);
lean_inc(v_toPure_1127_);
lean_dec_ref(v_toApplicative_1126_);
v___x_1128_ = lean_box(0);
v___x_1129_ = lean_apply_2(v_toPure_1127_, lean_box(0), v___x_1128_);
return v___x_1129_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logMessage___redArg___lam__0(lean_object* v_inst_1130_, lean_object* v_____do__lift_1131_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_apply_1(v_inst_1130_, v_____do__lift_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lake_logMessage___redArg(lean_object* v_msg_1133_, lean_object* v_inst_1134_, lean_object* v_inst_1135_, lean_object* v_inst_1136_){
_start:
{
uint8_t v_isSilent_1137_; 
v_isSilent_1137_ = lean_ctor_get_uint8(v_msg_1133_, sizeof(void*)*5 + 2);
if (v_isSilent_1137_ == 0)
{
lean_object* v_toBind_1138_; lean_object* v___f_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v_toBind_1138_ = lean_ctor_get(v_inst_1134_, 1);
lean_inc(v_toBind_1138_);
lean_dec_ref(v_inst_1134_);
v___f_1139_ = lean_alloc_closure((void*)(l_Lake_logMessage___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1139_, 0, v_inst_1135_);
v___x_1140_ = lean_alloc_closure((void*)(l_Lake_LogEntry_ofMessage___boxed), 2, 1);
lean_closure_set(v___x_1140_, 0, v_msg_1133_);
v___x_1141_ = lean_apply_2(v_inst_1136_, lean_box(0), v___x_1140_);
v___x_1142_ = lean_apply_4(v_toBind_1138_, lean_box(0), lean_box(0), v___x_1141_, v___f_1139_);
return v___x_1142_;
}
else
{
lean_object* v_toApplicative_1143_; lean_object* v_toPure_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_dec(v_inst_1136_);
lean_dec(v_inst_1135_);
lean_dec_ref(v_msg_1133_);
v_toApplicative_1143_ = lean_ctor_get(v_inst_1134_, 0);
lean_inc_ref(v_toApplicative_1143_);
lean_dec_ref(v_inst_1134_);
v_toPure_1144_ = lean_ctor_get(v_toApplicative_1143_, 1);
lean_inc(v_toPure_1144_);
lean_dec_ref(v_toApplicative_1143_);
v___x_1145_ = lean_box(0);
v___x_1146_ = lean_apply_2(v_toPure_1144_, lean_box(0), v___x_1145_);
return v___x_1146_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logMessage(lean_object* v_m_1147_, lean_object* v_msg_1148_, lean_object* v_inst_1149_, lean_object* v_inst_1150_, lean_object* v_inst_1151_){
_start:
{
uint8_t v_isSilent_1152_; 
v_isSilent_1152_ = lean_ctor_get_uint8(v_msg_1148_, sizeof(void*)*5 + 2);
if (v_isSilent_1152_ == 0)
{
lean_object* v_toBind_1153_; lean_object* v___f_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v_toBind_1153_ = lean_ctor_get(v_inst_1149_, 1);
lean_inc(v_toBind_1153_);
lean_dec_ref(v_inst_1149_);
v___f_1154_ = lean_alloc_closure((void*)(l_Lake_logMessage___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1154_, 0, v_inst_1150_);
v___x_1155_ = lean_alloc_closure((void*)(l_Lake_LogEntry_ofMessage___boxed), 2, 1);
lean_closure_set(v___x_1155_, 0, v_msg_1148_);
v___x_1156_ = lean_apply_2(v_inst_1151_, lean_box(0), v___x_1155_);
v___x_1157_ = lean_apply_4(v_toBind_1153_, lean_box(0), lean_box(0), v___x_1156_, v___f_1154_);
return v___x_1157_;
}
else
{
lean_object* v_toApplicative_1158_; lean_object* v_toPure_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_dec(v_inst_1151_);
lean_dec(v_inst_1150_);
lean_dec_ref(v_msg_1148_);
v_toApplicative_1158_ = lean_ctor_get(v_inst_1149_, 0);
lean_inc_ref(v_toApplicative_1158_);
lean_dec_ref(v_inst_1149_);
v_toPure_1159_ = lean_ctor_get(v_toApplicative_1158_, 1);
lean_inc(v_toPure_1159_);
lean_dec_ref(v_toApplicative_1158_);
v___x_1160_ = lean_box(0);
v___x_1161_ = lean_apply_2(v_toPure_1159_, lean_box(0), v___x_1160_);
return v___x_1161_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logToStream(lean_object* v_e_1162_, lean_object* v_out_1163_, uint8_t v_minLv_1164_, uint8_t v_useAnsi_1165_){
_start:
{
uint8_t v_level_1167_; uint8_t v___x_1168_; 
v_level_1167_ = lean_ctor_get_uint8(v_e_1162_, sizeof(void*)*1);
v___x_1168_ = l_Lake_instOrdLogLevel_ord(v_minLv_1164_, v_level_1167_);
if (v___x_1168_ == 2)
{
lean_object* v___x_1169_; 
lean_dec_ref(v_out_1163_);
v___x_1169_ = lean_box(0);
return v___x_1169_;
}
else
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = l_Lake_LogEntry_toString(v_e_1162_, v_useAnsi_1165_);
v___x_1171_ = l_IO_FS_Stream_putStrLn(v_out_1163_, v___x_1170_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_a_1172_);
lean_dec_ref_known(v___x_1171_, 1);
return v_a_1172_;
}
else
{
lean_object* v___x_1173_; 
lean_dec_ref_known(v___x_1171_, 1);
v___x_1173_ = lean_box(0);
return v___x_1173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_logToStream___boxed(lean_object* v_e_1174_, lean_object* v_out_1175_, lean_object* v_minLv_1176_, lean_object* v_useAnsi_1177_, lean_object* v_a_1178_){
_start:
{
uint8_t v_minLv_boxed_1179_; uint8_t v_useAnsi_boxed_1180_; lean_object* v_res_1181_; 
v_minLv_boxed_1179_ = lean_unbox(v_minLv_1176_);
v_useAnsi_boxed_1180_ = lean_unbox(v_useAnsi_1177_);
v_res_1181_ = l_Lake_logToStream(v_e_1174_, v_out_1175_, v_minLv_boxed_1179_, v_useAnsi_boxed_1180_);
lean_dec_ref(v_e_1174_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___redArg___lam__0(lean_object* v_inst_1182_, lean_object* v_x_1183_){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = lean_box(0);
v___x_1185_ = lean_apply_2(v_inst_1182_, lean_box(0), v___x_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___redArg___lam__0___boxed(lean_object* v_inst_1186_, lean_object* v_x_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lake_MonadLog_nop___redArg___lam__0(v_inst_1186_, v_x_1187_);
lean_dec_ref(v_x_1187_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___redArg(lean_object* v_inst_1189_){
_start:
{
lean_object* v___f_1190_; 
v___f_1190_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1190_, 0, v_inst_1189_);
return v___f_1190_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop(lean_object* v_m_1191_, lean_object* v_inst_1192_){
_start:
{
lean_object* v___f_1193_; 
v___f_1193_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1193_, 0, v_inst_1192_);
return v___f_1193_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instInhabitedOfPure___redArg(lean_object* v_inst_1194_){
_start:
{
lean_object* v___f_1195_; 
v___f_1195_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1195_, 0, v_inst_1194_);
return v___f_1195_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instInhabitedOfPure(lean_object* v_m_1196_, lean_object* v_inst_1197_){
_start:
{
lean_object* v___f_1198_; 
v___f_1198_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1198_, 0, v_inst_1197_);
return v___f_1198_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift___redArg___lam__0(lean_object* v_self_1199_, lean_object* v_inst_1200_, lean_object* v_e_1201_){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = lean_apply_1(v_self_1199_, v_e_1201_);
v___x_1203_ = lean_apply_2(v_inst_1200_, lean_box(0), v___x_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift___redArg(lean_object* v_inst_1204_, lean_object* v_self_1205_){
_start:
{
lean_object* v___f_1206_; 
v___f_1206_ = lean_alloc_closure((void*)(l_Lake_MonadLog_lift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1206_, 0, v_self_1205_);
lean_closure_set(v___f_1206_, 1, v_inst_1204_);
return v___f_1206_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift(lean_object* v_m_1207_, lean_object* v_n_1208_, lean_object* v_inst_1209_, lean_object* v_self_1210_){
_start:
{
lean_object* v___f_1211_; 
v___f_1211_ = lean_alloc_closure((void*)(l_Lake_MonadLog_lift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1211_, 0, v_self_1210_);
lean_closure_set(v___f_1211_, 1, v_inst_1209_);
return v___f_1211_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift___redArg___lam__0(lean_object* v_methods_1212_, lean_object* v_inst_1213_, lean_object* v_e_1214_){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = lean_apply_1(v_methods_1212_, v_e_1214_);
v___x_1216_ = lean_apply_2(v_inst_1213_, lean_box(0), v___x_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift___redArg(lean_object* v_inst_1217_, lean_object* v_methods_1218_){
_start:
{
lean_object* v___f_1219_; 
v___f_1219_ = lean_alloc_closure((void*)(l_Lake_MonadLog_instOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1219_, 0, v_methods_1218_);
lean_closure_set(v___f_1219_, 1, v_inst_1217_);
return v___f_1219_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift(lean_object* v_m_1220_, lean_object* v_n_1221_, lean_object* v_inst_1222_, lean_object* v_methods_1223_){
_start:
{
lean_object* v___f_1224_; 
v___f_1224_ = lean_alloc_closure((void*)(l_Lake_MonadLog_instOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1224_, 0, v_methods_1223_);
lean_closure_set(v___f_1224_, 1, v_inst_1222_);
return v___f_1224_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg___lam__0(lean_object* v_out_1225_, uint8_t v_minLv_1226_, uint8_t v_useAnsi_1227_, lean_object* v_inst_1228_, lean_object* v_e_1229_){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1230_ = lean_box(v_minLv_1226_);
v___x_1231_ = lean_box(v_useAnsi_1227_);
v___x_1232_ = lean_alloc_closure((void*)(l_Lake_logToStream___boxed), 5, 4);
lean_closure_set(v___x_1232_, 0, v_e_1229_);
lean_closure_set(v___x_1232_, 1, v_out_1225_);
lean_closure_set(v___x_1232_, 2, v___x_1230_);
lean_closure_set(v___x_1232_, 3, v___x_1231_);
v___x_1233_ = lean_apply_2(v_inst_1228_, lean_box(0), v___x_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg___lam__0___boxed(lean_object* v_out_1234_, lean_object* v_minLv_1235_, lean_object* v_useAnsi_1236_, lean_object* v_inst_1237_, lean_object* v_e_1238_){
_start:
{
uint8_t v_minLv_boxed_1239_; uint8_t v_useAnsi_boxed_1240_; lean_object* v_res_1241_; 
v_minLv_boxed_1239_ = lean_unbox(v_minLv_1235_);
v_useAnsi_boxed_1240_ = lean_unbox(v_useAnsi_1236_);
v_res_1241_ = l_Lake_MonadLog_stream___redArg___lam__0(v_out_1234_, v_minLv_boxed_1239_, v_useAnsi_boxed_1240_, v_inst_1237_, v_e_1238_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg(lean_object* v_inst_1242_, lean_object* v_out_1243_, uint8_t v_minLv_1244_, uint8_t v_useAnsi_1245_){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___f_1248_; 
v___x_1246_ = lean_box(v_minLv_1244_);
v___x_1247_ = lean_box(v_useAnsi_1245_);
v___f_1248_ = lean_alloc_closure((void*)(l_Lake_MonadLog_stream___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1248_, 0, v_out_1243_);
lean_closure_set(v___f_1248_, 1, v___x_1246_);
lean_closure_set(v___f_1248_, 2, v___x_1247_);
lean_closure_set(v___f_1248_, 3, v_inst_1242_);
return v___f_1248_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg___boxed(lean_object* v_inst_1249_, lean_object* v_out_1250_, lean_object* v_minLv_1251_, lean_object* v_useAnsi_1252_){
_start:
{
uint8_t v_minLv_boxed_1253_; uint8_t v_useAnsi_boxed_1254_; lean_object* v_res_1255_; 
v_minLv_boxed_1253_ = lean_unbox(v_minLv_1251_);
v_useAnsi_boxed_1254_ = lean_unbox(v_useAnsi_1252_);
v_res_1255_ = l_Lake_MonadLog_stream___redArg(v_inst_1249_, v_out_1250_, v_minLv_boxed_1253_, v_useAnsi_boxed_1254_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream(lean_object* v_m_1256_, lean_object* v_inst_1257_, lean_object* v_out_1258_, uint8_t v_minLv_1259_, uint8_t v_useAnsi_1260_){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___f_1263_; 
v___x_1261_ = lean_box(v_minLv_1259_);
v___x_1262_ = lean_box(v_useAnsi_1260_);
v___f_1263_ = lean_alloc_closure((void*)(l_Lake_MonadLog_stream___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1263_, 0, v_out_1258_);
lean_closure_set(v___f_1263_, 1, v___x_1261_);
lean_closure_set(v___f_1263_, 2, v___x_1262_);
lean_closure_set(v___f_1263_, 3, v_inst_1257_);
return v___f_1263_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___boxed(lean_object* v_m_1264_, lean_object* v_inst_1265_, lean_object* v_out_1266_, lean_object* v_minLv_1267_, lean_object* v_useAnsi_1268_){
_start:
{
uint8_t v_minLv_boxed_1269_; uint8_t v_useAnsi_boxed_1270_; lean_object* v_res_1271_; 
v_minLv_boxed_1269_ = lean_unbox(v_minLv_1267_);
v_useAnsi_boxed_1270_ = lean_unbox(v_useAnsi_1268_);
v_res_1271_ = l_Lake_MonadLog_stream(v_m_1264_, v_inst_1265_, v_out_1266_, v_minLv_boxed_1269_, v_useAnsi_boxed_1270_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_error___redArg___lam__0(lean_object* v_failure_1272_, lean_object* v_x_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = lean_apply_1(v_failure_1272_, lean_box(0));
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_error___redArg(lean_object* v_inst_1275_, lean_object* v_inst_1276_, lean_object* v_msg_1277_){
_start:
{
lean_object* v_toApplicative_1278_; lean_object* v_failure_1279_; lean_object* v_toSeqRight_1280_; lean_object* v___f_1281_; uint8_t v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v_toApplicative_1278_ = lean_ctor_get(v_inst_1275_, 0);
lean_inc_ref(v_toApplicative_1278_);
v_failure_1279_ = lean_ctor_get(v_inst_1275_, 1);
lean_inc(v_failure_1279_);
lean_dec_ref(v_inst_1275_);
v_toSeqRight_1280_ = lean_ctor_get(v_toApplicative_1278_, 4);
lean_inc(v_toSeqRight_1280_);
lean_dec_ref(v_toApplicative_1278_);
v___f_1281_ = lean_alloc_closure((void*)(l_Lake_MonadLog_error___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1281_, 0, v_failure_1279_);
v___x_1282_ = 3;
v___x_1283_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1283_, 0, v_msg_1277_);
lean_ctor_set_uint8(v___x_1283_, sizeof(void*)*1, v___x_1282_);
v___x_1284_ = lean_apply_1(v_inst_1276_, v___x_1283_);
v___x_1285_ = lean_apply_4(v_toSeqRight_1280_, lean_box(0), lean_box(0), v___x_1284_, v___f_1281_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_error(lean_object* v_m_1286_, lean_object* v_00_u03b1_1287_, lean_object* v_inst_1288_, lean_object* v_inst_1289_, lean_object* v_msg_1290_){
_start:
{
lean_object* v_toApplicative_1291_; lean_object* v_failure_1292_; lean_object* v_toSeqRight_1293_; lean_object* v___f_1294_; uint8_t v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v_toApplicative_1291_ = lean_ctor_get(v_inst_1288_, 0);
lean_inc_ref(v_toApplicative_1291_);
v_failure_1292_ = lean_ctor_get(v_inst_1288_, 1);
lean_inc(v_failure_1292_);
lean_dec_ref(v_inst_1288_);
v_toSeqRight_1293_ = lean_ctor_get(v_toApplicative_1291_, 4);
lean_inc(v_toSeqRight_1293_);
lean_dec_ref(v_toApplicative_1291_);
v___f_1294_ = lean_alloc_closure((void*)(l_Lake_MonadLog_error___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1294_, 0, v_failure_1292_);
v___x_1295_ = 3;
v___x_1296_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1296_, 0, v_msg_1290_);
lean_ctor_set_uint8(v___x_1296_, sizeof(void*)*1, v___x_1295_);
v___x_1297_ = lean_apply_1(v_inst_1289_, v___x_1296_);
v___x_1298_ = lean_apply_4(v_toSeqRight_1293_, lean_box(0), lean_box(0), v___x_1297_, v___f_1294_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logEntry(lean_object* v_self_1299_, lean_object* v_e_1300_, uint8_t v_minLv_1301_, uint8_t v_ansiMode_1302_){
_start:
{
lean_object* v___x_1304_; uint8_t v___x_1305_; lean_object* v___x_1306_; 
v___x_1304_ = l_Lake_OutStream_get(v_self_1299_);
lean_inc_ref(v___x_1304_);
v___x_1305_ = l_Lake_AnsiMode_isEnabled(v___x_1304_, v_ansiMode_1302_);
v___x_1306_ = l_Lake_logToStream(v_e_1300_, v___x_1304_, v_minLv_1301_, v___x_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logEntry___boxed(lean_object* v_self_1307_, lean_object* v_e_1308_, lean_object* v_minLv_1309_, lean_object* v_ansiMode_1310_, lean_object* v_a_1311_){
_start:
{
uint8_t v_minLv_boxed_1312_; uint8_t v_ansiMode_boxed_1313_; lean_object* v_res_1314_; 
v_minLv_boxed_1312_ = lean_unbox(v_minLv_1309_);
v_ansiMode_boxed_1313_ = lean_unbox(v_ansiMode_1310_);
v_res_1314_ = l_Lake_OutStream_logEntry(v_self_1307_, v_e_1308_, v_minLv_boxed_1312_, v_ansiMode_boxed_1313_);
lean_dec_ref(v_e_1308_);
lean_dec(v_self_1307_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg___lam__0(lean_object* v_out_1315_, uint8_t v_minLv_1316_, uint8_t v_ansiMode_1317_, lean_object* v_inst_1318_, lean_object* v_e_1319_){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1320_ = lean_box(v_minLv_1316_);
v___x_1321_ = lean_box(v_ansiMode_1317_);
v___x_1322_ = lean_alloc_closure((void*)(l_Lake_OutStream_logEntry___boxed), 5, 4);
lean_closure_set(v___x_1322_, 0, v_out_1315_);
lean_closure_set(v___x_1322_, 1, v_e_1319_);
lean_closure_set(v___x_1322_, 2, v___x_1320_);
lean_closure_set(v___x_1322_, 3, v___x_1321_);
v___x_1323_ = lean_apply_2(v_inst_1318_, lean_box(0), v___x_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg___lam__0___boxed(lean_object* v_out_1324_, lean_object* v_minLv_1325_, lean_object* v_ansiMode_1326_, lean_object* v_inst_1327_, lean_object* v_e_1328_){
_start:
{
uint8_t v_minLv_boxed_1329_; uint8_t v_ansiMode_boxed_1330_; lean_object* v_res_1331_; 
v_minLv_boxed_1329_ = lean_unbox(v_minLv_1325_);
v_ansiMode_boxed_1330_ = lean_unbox(v_ansiMode_1326_);
v_res_1331_ = l_Lake_OutStream_logger___redArg___lam__0(v_out_1324_, v_minLv_boxed_1329_, v_ansiMode_boxed_1330_, v_inst_1327_, v_e_1328_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg(lean_object* v_inst_1332_, lean_object* v_out_1333_, uint8_t v_minLv_1334_, uint8_t v_ansiMode_1335_){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___f_1338_; 
v___x_1336_ = lean_box(v_minLv_1334_);
v___x_1337_ = lean_box(v_ansiMode_1335_);
v___f_1338_ = lean_alloc_closure((void*)(l_Lake_OutStream_logger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1338_, 0, v_out_1333_);
lean_closure_set(v___f_1338_, 1, v___x_1336_);
lean_closure_set(v___f_1338_, 2, v___x_1337_);
lean_closure_set(v___f_1338_, 3, v_inst_1332_);
return v___f_1338_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg___boxed(lean_object* v_inst_1339_, lean_object* v_out_1340_, lean_object* v_minLv_1341_, lean_object* v_ansiMode_1342_){
_start:
{
uint8_t v_minLv_boxed_1343_; uint8_t v_ansiMode_boxed_1344_; lean_object* v_res_1345_; 
v_minLv_boxed_1343_ = lean_unbox(v_minLv_1341_);
v_ansiMode_boxed_1344_ = lean_unbox(v_ansiMode_1342_);
v_res_1345_ = l_Lake_OutStream_logger___redArg(v_inst_1339_, v_out_1340_, v_minLv_boxed_1343_, v_ansiMode_boxed_1344_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger(lean_object* v_m_1346_, lean_object* v_inst_1347_, lean_object* v_out_1348_, uint8_t v_minLv_1349_, uint8_t v_ansiMode_1350_){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___f_1353_; 
v___x_1351_ = lean_box(v_minLv_1349_);
v___x_1352_ = lean_box(v_ansiMode_1350_);
v___f_1353_ = lean_alloc_closure((void*)(l_Lake_OutStream_logger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1353_, 0, v_out_1348_);
lean_closure_set(v___f_1353_, 1, v___x_1351_);
lean_closure_set(v___f_1353_, 2, v___x_1352_);
lean_closure_set(v___f_1353_, 3, v_inst_1347_);
return v___f_1353_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___boxed(lean_object* v_m_1354_, lean_object* v_inst_1355_, lean_object* v_out_1356_, lean_object* v_minLv_1357_, lean_object* v_ansiMode_1358_){
_start:
{
uint8_t v_minLv_boxed_1359_; uint8_t v_ansiMode_boxed_1360_; lean_object* v_res_1361_; 
v_minLv_boxed_1359_ = lean_unbox(v_minLv_1357_);
v_ansiMode_boxed_1360_ = lean_unbox(v_ansiMode_1358_);
v_res_1361_ = l_Lake_OutStream_logger(v_m_1354_, v_inst_1355_, v_out_1356_, v_minLv_boxed_1359_, v_ansiMode_boxed_1360_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg___lam__0(lean_object* v___x_1362_, uint8_t v_minLv_1363_, uint8_t v_ansiMode_1364_, lean_object* v_inst_1365_, lean_object* v_e_1366_){
_start:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1367_ = lean_box(v_minLv_1363_);
v___x_1368_ = lean_box(v_ansiMode_1364_);
v___x_1369_ = lean_alloc_closure((void*)(l_Lake_OutStream_logEntry___boxed), 5, 4);
lean_closure_set(v___x_1369_, 0, v___x_1362_);
lean_closure_set(v___x_1369_, 1, v_e_1366_);
lean_closure_set(v___x_1369_, 2, v___x_1367_);
lean_closure_set(v___x_1369_, 3, v___x_1368_);
v___x_1370_ = lean_apply_2(v_inst_1365_, lean_box(0), v___x_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg___lam__0___boxed(lean_object* v___x_1371_, lean_object* v_minLv_1372_, lean_object* v_ansiMode_1373_, lean_object* v_inst_1374_, lean_object* v_e_1375_){
_start:
{
uint8_t v_minLv_boxed_1376_; uint8_t v_ansiMode_boxed_1377_; lean_object* v_res_1378_; 
v_minLv_boxed_1376_ = lean_unbox(v_minLv_1372_);
v_ansiMode_boxed_1377_ = lean_unbox(v_ansiMode_1373_);
v_res_1378_ = l_Lake_MonadLog_stdout___redArg___lam__0(v___x_1371_, v_minLv_boxed_1376_, v_ansiMode_boxed_1377_, v_inst_1374_, v_e_1375_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg(lean_object* v_inst_1379_, uint8_t v_minLv_1380_, uint8_t v_ansiMode_1381_){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___f_1385_; 
v___x_1382_ = lean_box(0);
v___x_1383_ = lean_box(v_minLv_1380_);
v___x_1384_ = lean_box(v_ansiMode_1381_);
v___f_1385_ = lean_alloc_closure((void*)(l_Lake_MonadLog_stdout___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1385_, 0, v___x_1382_);
lean_closure_set(v___f_1385_, 1, v___x_1383_);
lean_closure_set(v___f_1385_, 2, v___x_1384_);
lean_closure_set(v___f_1385_, 3, v_inst_1379_);
return v___f_1385_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg___boxed(lean_object* v_inst_1386_, lean_object* v_minLv_1387_, lean_object* v_ansiMode_1388_){
_start:
{
uint8_t v_minLv_boxed_1389_; uint8_t v_ansiMode_boxed_1390_; lean_object* v_res_1391_; 
v_minLv_boxed_1389_ = lean_unbox(v_minLv_1387_);
v_ansiMode_boxed_1390_ = lean_unbox(v_ansiMode_1388_);
v_res_1391_ = l_Lake_MonadLog_stdout___redArg(v_inst_1386_, v_minLv_boxed_1389_, v_ansiMode_boxed_1390_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout(lean_object* v_m_1392_, lean_object* v_inst_1393_, uint8_t v_minLv_1394_, uint8_t v_ansiMode_1395_){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___f_1399_; 
v___x_1396_ = lean_box(0);
v___x_1397_ = lean_box(v_minLv_1394_);
v___x_1398_ = lean_box(v_ansiMode_1395_);
v___f_1399_ = lean_alloc_closure((void*)(l_Lake_MonadLog_stdout___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1399_, 0, v___x_1396_);
lean_closure_set(v___f_1399_, 1, v___x_1397_);
lean_closure_set(v___f_1399_, 2, v___x_1398_);
lean_closure_set(v___f_1399_, 3, v_inst_1393_);
return v___f_1399_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___boxed(lean_object* v_m_1400_, lean_object* v_inst_1401_, lean_object* v_minLv_1402_, lean_object* v_ansiMode_1403_){
_start:
{
uint8_t v_minLv_boxed_1404_; uint8_t v_ansiMode_boxed_1405_; lean_object* v_res_1406_; 
v_minLv_boxed_1404_ = lean_unbox(v_minLv_1402_);
v_ansiMode_boxed_1405_ = lean_unbox(v_ansiMode_1403_);
v_res_1406_ = l_Lake_MonadLog_stdout(v_m_1400_, v_inst_1401_, v_minLv_boxed_1404_, v_ansiMode_boxed_1405_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___redArg(lean_object* v_inst_1407_, uint8_t v_minLv_1408_, uint8_t v_ansiMode_1409_){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___f_1413_; 
v___x_1410_ = lean_box(1);
v___x_1411_ = lean_box(v_minLv_1408_);
v___x_1412_ = lean_box(v_ansiMode_1409_);
v___f_1413_ = lean_alloc_closure((void*)(l_Lake_MonadLog_stdout___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1413_, 0, v___x_1410_);
lean_closure_set(v___f_1413_, 1, v___x_1411_);
lean_closure_set(v___f_1413_, 2, v___x_1412_);
lean_closure_set(v___f_1413_, 3, v_inst_1407_);
return v___f_1413_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___redArg___boxed(lean_object* v_inst_1414_, lean_object* v_minLv_1415_, lean_object* v_ansiMode_1416_){
_start:
{
uint8_t v_minLv_boxed_1417_; uint8_t v_ansiMode_boxed_1418_; lean_object* v_res_1419_; 
v_minLv_boxed_1417_ = lean_unbox(v_minLv_1415_);
v_ansiMode_boxed_1418_ = lean_unbox(v_ansiMode_1416_);
v_res_1419_ = l_Lake_MonadLog_stderr___redArg(v_inst_1414_, v_minLv_boxed_1417_, v_ansiMode_boxed_1418_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr(lean_object* v_m_1420_, lean_object* v_inst_1421_, uint8_t v_minLv_1422_, uint8_t v_ansiMode_1423_){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___f_1427_; 
v___x_1424_ = lean_box(1);
v___x_1425_ = lean_box(v_minLv_1422_);
v___x_1426_ = lean_box(v_ansiMode_1423_);
v___f_1427_ = lean_alloc_closure((void*)(l_Lake_MonadLog_stdout___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1427_, 0, v___x_1424_);
lean_closure_set(v___f_1427_, 1, v___x_1425_);
lean_closure_set(v___f_1427_, 2, v___x_1426_);
lean_closure_set(v___f_1427_, 3, v_inst_1421_);
return v___f_1427_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___boxed(lean_object* v_m_1428_, lean_object* v_inst_1429_, lean_object* v_minLv_1430_, lean_object* v_ansiMode_1431_){
_start:
{
uint8_t v_minLv_boxed_1432_; uint8_t v_ansiMode_boxed_1433_; lean_object* v_res_1434_; 
v_minLv_boxed_1432_ = lean_unbox(v_minLv_1430_);
v_ansiMode_boxed_1433_ = lean_unbox(v_ansiMode_1431_);
v_res_1434_ = l_Lake_MonadLog_stderr(v_m_1428_, v_inst_1429_, v_minLv_boxed_1432_, v_ansiMode_boxed_1433_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg___lam__0(lean_object* v_val_1435_, uint8_t v_minLv_1436_, uint8_t v_val_1437_, lean_object* v_inst_1438_, lean_object* v_e_1439_){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1440_ = lean_box(v_minLv_1436_);
v___x_1441_ = lean_box(v_val_1437_);
v___x_1442_ = lean_alloc_closure((void*)(l_Lake_logToStream___boxed), 5, 4);
lean_closure_set(v___x_1442_, 0, v_e_1439_);
lean_closure_set(v___x_1442_, 1, v_val_1435_);
lean_closure_set(v___x_1442_, 2, v___x_1440_);
lean_closure_set(v___x_1442_, 3, v___x_1441_);
v___x_1443_ = lean_apply_2(v_inst_1438_, lean_box(0), v___x_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg___lam__0___boxed(lean_object* v_val_1444_, lean_object* v_minLv_1445_, lean_object* v_val_1446_, lean_object* v_inst_1447_, lean_object* v_e_1448_){
_start:
{
uint8_t v_minLv_boxed_1449_; uint8_t v_val_105__boxed_1450_; lean_object* v_res_1451_; 
v_minLv_boxed_1449_ = lean_unbox(v_minLv_1445_);
v_val_105__boxed_1450_ = lean_unbox(v_val_1446_);
v_res_1451_ = l_Lake_OutStream_getLogger___redArg___lam__0(v_val_1444_, v_minLv_boxed_1449_, v_val_105__boxed_1450_, v_inst_1447_, v_e_1448_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg(lean_object* v_inst_1452_, lean_object* v_out_1453_, uint8_t v_minLv_1454_, uint8_t v_ansiMode_1455_){
_start:
{
lean_object* v___x_1457_; uint8_t v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___f_1461_; 
v___x_1457_ = l_Lake_OutStream_get(v_out_1453_);
lean_inc_ref(v___x_1457_);
v___x_1458_ = l_Lake_AnsiMode_isEnabled(v___x_1457_, v_ansiMode_1455_);
v___x_1459_ = lean_box(v_minLv_1454_);
v___x_1460_ = lean_box(v___x_1458_);
v___f_1461_ = lean_alloc_closure((void*)(l_Lake_OutStream_getLogger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1461_, 0, v___x_1457_);
lean_closure_set(v___f_1461_, 1, v___x_1459_);
lean_closure_set(v___f_1461_, 2, v___x_1460_);
lean_closure_set(v___f_1461_, 3, v_inst_1452_);
return v___f_1461_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg___boxed(lean_object* v_inst_1462_, lean_object* v_out_1463_, lean_object* v_minLv_1464_, lean_object* v_ansiMode_1465_, lean_object* v_a_1466_){
_start:
{
uint8_t v_minLv_boxed_1467_; uint8_t v_ansiMode_boxed_1468_; lean_object* v_res_1469_; 
v_minLv_boxed_1467_ = lean_unbox(v_minLv_1464_);
v_ansiMode_boxed_1468_ = lean_unbox(v_ansiMode_1465_);
v_res_1469_ = l_Lake_OutStream_getLogger___redArg(v_inst_1462_, v_out_1463_, v_minLv_boxed_1467_, v_ansiMode_boxed_1468_);
lean_dec(v_out_1463_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger(lean_object* v_m_1470_, lean_object* v_inst_1471_, lean_object* v_out_1472_, uint8_t v_minLv_1473_, uint8_t v_ansiMode_1474_){
_start:
{
lean_object* v___x_1476_; uint8_t v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___f_1480_; 
v___x_1476_ = l_Lake_OutStream_get(v_out_1472_);
lean_inc_ref(v___x_1476_);
v___x_1477_ = l_Lake_AnsiMode_isEnabled(v___x_1476_, v_ansiMode_1474_);
v___x_1478_ = lean_box(v_minLv_1473_);
v___x_1479_ = lean_box(v___x_1477_);
v___f_1480_ = lean_alloc_closure((void*)(l_Lake_OutStream_getLogger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1480_, 0, v___x_1476_);
lean_closure_set(v___f_1480_, 1, v___x_1478_);
lean_closure_set(v___f_1480_, 2, v___x_1479_);
lean_closure_set(v___f_1480_, 3, v_inst_1471_);
return v___f_1480_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___boxed(lean_object* v_m_1481_, lean_object* v_inst_1482_, lean_object* v_out_1483_, lean_object* v_minLv_1484_, lean_object* v_ansiMode_1485_, lean_object* v_a_1486_){
_start:
{
uint8_t v_minLv_boxed_1487_; uint8_t v_ansiMode_boxed_1488_; lean_object* v_res_1489_; 
v_minLv_boxed_1487_ = lean_unbox(v_minLv_1484_);
v_ansiMode_boxed_1488_ = lean_unbox(v_ansiMode_1485_);
v_res_1489_ = l_Lake_OutStream_getLogger(v_m_1481_, v_inst_1482_, v_out_1483_, v_minLv_boxed_1487_, v_ansiMode_boxed_1488_);
lean_dec(v_out_1483_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0(lean_object* v_inst_1490_, lean_object* v_inst_1491_, lean_object* v_x_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_apply_2(v_inst_1490_, lean_box(0), v_inst_1491_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0___boxed(lean_object* v_inst_1494_, lean_object* v_inst_1495_, lean_object* v_x_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0(v_inst_1494_, v_inst_1495_, v_x_1496_);
lean_dec(v_x_1496_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___redArg(lean_object* v_inst_1498_, lean_object* v_inst_1499_){
_start:
{
lean_object* v___f_1500_; 
v___f_1500_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1500_, 0, v_inst_1498_);
lean_closure_set(v___f_1500_, 1, v_inst_1499_);
return v___f_1500_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure(lean_object* v_n_1501_, lean_object* v_00_u03b1_1502_, lean_object* v_m_1503_, lean_object* v_inst_1504_, lean_object* v_inst_1505_){
_start:
{
lean_object* v___f_1506_; 
v___f_1506_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1506_, 0, v_inst_1504_);
lean_closure_set(v___f_1506_, 1, v_inst_1505_);
return v___f_1506_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__0(lean_object* v_e_1507_, lean_object* v_inst_1508_, lean_object* v_a_1509_){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = lean_apply_1(v_a_1509_, v_e_1507_);
v___x_1511_ = lean_apply_2(v_inst_1508_, lean_box(0), v___x_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1(lean_object* v_inst_1512_, lean_object* v_inst_1513_, lean_object* v_e_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v_toApplicative_1516_; lean_object* v_toBind_1517_; lean_object* v_toPure_1518_; lean_object* v___f_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v_toApplicative_1516_ = lean_ctor_get(v_inst_1512_, 0);
lean_inc_ref(v_toApplicative_1516_);
v_toBind_1517_ = lean_ctor_get(v_inst_1512_, 1);
lean_inc(v_toBind_1517_);
lean_dec_ref(v_inst_1512_);
v_toPure_1518_ = lean_ctor_get(v_toApplicative_1516_, 1);
lean_inc(v_toPure_1518_);
lean_dec_ref(v_toApplicative_1516_);
v___f_1519_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1519_, 0, v_e_1514_);
lean_closure_set(v___f_1519_, 1, v_inst_1513_);
lean_inc(v___y_1515_);
v___x_1520_ = lean_apply_2(v_toPure_1518_, lean_box(0), v___y_1515_);
v___x_1521_ = lean_apply_4(v_toBind_1517_, lean_box(0), lean_box(0), v___x_1520_, v___f_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1___boxed(lean_object* v_inst_1522_, lean_object* v_inst_1523_, lean_object* v_e_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1(v_inst_1522_, v_inst_1523_, v_e_1524_, v___y_1525_);
lean_dec(v___y_1525_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg(lean_object* v_inst_1527_, lean_object* v_inst_1528_){
_start:
{
lean_object* v___f_1529_; 
v___f_1529_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1529_, 0, v_inst_1527_);
lean_closure_set(v___f_1529_, 1, v_inst_1528_);
return v___f_1529_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT(lean_object* v_n_1530_, lean_object* v_m_1531_, lean_object* v_inst_1532_, lean_object* v_inst_1533_){
_start:
{
lean_object* v___f_1534_; 
v___f_1534_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1534_, 0, v_inst_1532_);
lean_closure_set(v___f_1534_, 1, v_inst_1533_);
return v___f_1534_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___redArg(lean_object* v_f_1535_, lean_object* v_self_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
lean_inc(v_a_1537_);
v___x_1538_ = lean_apply_1(v_f_1535_, v_a_1537_);
v___x_1539_ = lean_apply_1(v_self_1536_, v___x_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___redArg___boxed(lean_object* v_f_1540_, lean_object* v_self_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Lake_MonadLogT_adaptMethods___redArg(v_f_1540_, v_self_1541_, v_a_1542_);
lean_dec(v_a_1542_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods(lean_object* v_n_1544_, lean_object* v_m_1545_, lean_object* v_m_x27_1546_, lean_object* v_00_u03b1_1547_, lean_object* v_inst_1548_, lean_object* v_f_1549_, lean_object* v_self_1550_, lean_object* v_a_1551_){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
lean_inc(v_a_1551_);
v___x_1552_ = lean_apply_1(v_f_1549_, v_a_1551_);
v___x_1553_ = lean_apply_1(v_self_1550_, v___x_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___boxed(lean_object* v_n_1554_, lean_object* v_m_1555_, lean_object* v_m_x27_1556_, lean_object* v_00_u03b1_1557_, lean_object* v_inst_1558_, lean_object* v_f_1559_, lean_object* v_self_1560_, lean_object* v_a_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_Lake_MonadLogT_adaptMethods(v_n_1554_, v_m_1555_, v_m_x27_1556_, v_00_u03b1_1557_, v_inst_1558_, v_f_1559_, v_self_1560_, v_a_1561_);
lean_dec(v_a_1561_);
lean_dec_ref(v_inst_1558_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog___redArg(lean_object* v_inst_1563_, lean_object* v_self_1564_){
_start:
{
lean_object* v___f_1565_; lean_object* v___x_1566_; 
v___f_1565_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1565_, 0, v_inst_1563_);
v___x_1566_ = lean_apply_1(v_self_1564_, v___f_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog(lean_object* v_m_1567_, lean_object* v_n_1568_, lean_object* v_00_u03b1_1569_, lean_object* v_inst_1570_, lean_object* v_self_1571_){
_start:
{
lean_object* v___f_1572_; lean_object* v___x_1573_; 
v___f_1572_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1572_, 0, v_inst_1570_);
v___x_1573_ = lean_apply_1(v_self_1571_, v___f_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonLog___lam__0(lean_object* v___x_1578_, lean_object* v_x_1579_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Lean_Array_toJson___redArg(v___x_1578_, v_x_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonLog___lam__0(lean_object* v___x_1584_, lean_object* v_x_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_Array_fromJson_x3f___redArg(v___x_1584_, v_x_1585_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1586_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1586_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
v_a_1595_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1586_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1586_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
}
static lean_object* _init_l_Lake_Log_instInhabitedPos_default(void){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = lean_unsigned_to_nat(0u);
return v___x_1606_;
}
}
static lean_object* _init_l_Lake_Log_instInhabitedPos(void){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = lean_unsigned_to_nat(0u);
return v___x_1607_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_instDecidableEqPos_decEq(lean_object* v_x_1608_, lean_object* v_x_1609_){
_start:
{
uint8_t v___x_1610_; 
v___x_1610_ = lean_nat_dec_eq(v_x_1608_, v_x_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_instDecidableEqPos_decEq___boxed(lean_object* v_x_1611_, lean_object* v_x_1612_){
_start:
{
uint8_t v_res_1613_; lean_object* v_r_1614_; 
v_res_1613_ = l_Lake_Log_instDecidableEqPos_decEq(v_x_1611_, v_x_1612_);
lean_dec(v_x_1612_);
lean_dec(v_x_1611_);
v_r_1614_ = lean_box(v_res_1613_);
return v_r_1614_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_instDecidableEqPos(lean_object* v_x_1615_, lean_object* v_x_1616_){
_start:
{
uint8_t v___x_1617_; 
v___x_1617_ = lean_nat_dec_eq(v_x_1615_, v_x_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_instDecidableEqPos___boxed(lean_object* v_x_1618_, lean_object* v_x_1619_){
_start:
{
uint8_t v_res_1620_; lean_object* v_r_1621_; 
v_res_1620_ = l_Lake_Log_instDecidableEqPos(v_x_1618_, v_x_1619_);
lean_dec(v_x_1619_);
lean_dec(v_x_1618_);
v_r_1621_ = lean_box(v_res_1620_);
return v_r_1621_;
}
}
static lean_object* _init_l_Lake_instOfNatPos(void){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_unsigned_to_nat(0u);
return v___x_1622_;
}
}
LEAN_EXPORT uint8_t l_Lake_instOrdPos___lam__0(lean_object* v_x1_1623_, lean_object* v_x2_1624_){
_start:
{
uint8_t v___x_1625_; 
v___x_1625_ = lean_nat_dec_lt(v_x1_1623_, v_x2_1624_);
if (v___x_1625_ == 0)
{
uint8_t v___x_1626_; 
v___x_1626_ = lean_nat_dec_eq(v_x1_1623_, v_x2_1624_);
if (v___x_1626_ == 0)
{
uint8_t v___x_1627_; 
v___x_1627_ = 2;
return v___x_1627_;
}
else
{
uint8_t v___x_1628_; 
v___x_1628_ = 1;
return v___x_1628_;
}
}
else
{
uint8_t v___x_1629_; 
v___x_1629_ = 0;
return v___x_1629_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instOrdPos___lam__0___boxed(lean_object* v_x1_1630_, lean_object* v_x2_1631_){
_start:
{
uint8_t v_res_1632_; lean_object* v_r_1633_; 
v_res_1632_ = l_Lake_instOrdPos___lam__0(v_x1_1630_, v_x2_1631_);
lean_dec(v_x2_1631_);
lean_dec(v_x1_1630_);
v_r_1633_ = lean_box(v_res_1632_);
return v_r_1633_;
}
}
static lean_object* _init_l_Lake_instLTPos(void){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = lean_box(0);
return v___x_1636_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableRelPosLt(lean_object* v_a_1637_, lean_object* v_b_1638_){
_start:
{
uint8_t v___x_1639_; 
v___x_1639_ = lean_nat_dec_lt(v_a_1637_, v_b_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableRelPosLt___boxed(lean_object* v_a_1640_, lean_object* v_b_1641_){
_start:
{
uint8_t v_res_1642_; lean_object* v_r_1643_; 
v_res_1642_ = l_Lake_instDecidableRelPosLt(v_a_1640_, v_b_1641_);
lean_dec(v_b_1641_);
lean_dec(v_a_1640_);
v_r_1643_ = lean_box(v_res_1642_);
return v_r_1643_;
}
}
static lean_object* _init_l_Lake_instLEPos(void){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = lean_box(0);
return v___x_1644_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableRelPosLe(lean_object* v_a_1645_, lean_object* v_b_1646_){
_start:
{
uint8_t v___x_1647_; 
v___x_1647_ = lean_nat_dec_le(v_a_1645_, v_b_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableRelPosLe___boxed(lean_object* v_a_1648_, lean_object* v_b_1649_){
_start:
{
uint8_t v_res_1650_; lean_object* v_r_1651_; 
v_res_1650_ = l_Lake_instDecidableRelPosLe(v_a_1648_, v_b_1649_);
lean_dec(v_b_1649_);
lean_dec(v_a_1648_);
v_r_1651_ = lean_box(v_res_1650_);
return v_r_1651_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMinPos___lam__0(lean_object* v_x_1652_, lean_object* v_y_1653_){
_start:
{
uint8_t v___x_1654_; 
v___x_1654_ = lean_nat_dec_le(v_x_1652_, v_y_1653_);
if (v___x_1654_ == 0)
{
lean_inc(v_y_1653_);
return v_y_1653_;
}
else
{
lean_inc(v_x_1652_);
return v_x_1652_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMinPos___lam__0___boxed(lean_object* v_x_1655_, lean_object* v_y_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lake_instMinPos___lam__0(v_x_1655_, v_y_1656_);
lean_dec(v_y_1656_);
lean_dec(v_x_1655_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxPos___lam__0(lean_object* v_x_1660_, lean_object* v_y_1661_){
_start:
{
uint8_t v___x_1662_; 
v___x_1662_ = lean_nat_dec_le(v_x_1660_, v_y_1661_);
if (v___x_1662_ == 0)
{
lean_inc(v_x_1660_);
return v_x_1660_;
}
else
{
lean_inc(v_y_1661_);
return v_y_1661_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxPos___lam__0___boxed(lean_object* v_x_1663_, lean_object* v_y_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lake_instMaxPos___lam__0(v_x_1663_, v_y_1664_);
lean_dec(v_y_1664_);
lean_dec(v_x_1663_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_size(lean_object* v_log_1672_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = lean_array_get_size(v_log_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_size___boxed(lean_object* v_log_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lake_Log_size(v_log_1674_);
lean_dec_ref(v_log_1674_);
return v_res_1675_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_isEmpty(lean_object* v_log_1676_){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
v___x_1677_ = lean_array_get_size(v_log_1676_);
v___x_1678_ = lean_unsigned_to_nat(0u);
v___x_1679_ = lean_nat_dec_eq(v___x_1677_, v___x_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_isEmpty___boxed(lean_object* v_log_1680_){
_start:
{
uint8_t v_res_1681_; lean_object* v_r_1682_; 
v_res_1681_ = l_Lake_Log_isEmpty(v_log_1680_);
lean_dec_ref(v_log_1680_);
v_r_1682_ = lean_box(v_res_1681_);
return v_r_1682_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_hasEntries(lean_object* v_log_1683_){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; uint8_t v___x_1686_; 
v___x_1684_ = lean_array_get_size(v_log_1683_);
v___x_1685_ = lean_unsigned_to_nat(0u);
v___x_1686_ = lean_nat_dec_eq(v___x_1684_, v___x_1685_);
if (v___x_1686_ == 0)
{
uint8_t v___x_1687_; 
v___x_1687_ = 1;
return v___x_1687_;
}
else
{
uint8_t v___x_1688_; 
v___x_1688_ = 0;
return v___x_1688_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_hasEntries___boxed(lean_object* v_log_1689_){
_start:
{
uint8_t v_res_1690_; lean_object* v_r_1691_; 
v_res_1690_ = l_Lake_Log_hasEntries(v_log_1689_);
lean_dec_ref(v_log_1689_);
v_r_1691_ = lean_box(v_res_1690_);
return v_r_1691_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_endPos(lean_object* v_log_1692_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = lean_array_get_size(v_log_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_endPos___boxed(lean_object* v_log_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lake_Log_endPos(v_log_1694_);
lean_dec_ref(v_log_1694_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_push(lean_object* v_log_1696_, lean_object* v_e_1697_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = lean_array_push(v_log_1696_, v_e_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_append(lean_object* v_log_1699_, lean_object* v_o_1700_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = l_Array_append___redArg(v_log_1699_, v_o_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_append___boxed(lean_object* v_log_1702_, lean_object* v_o_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lake_Log_append(v_log_1702_, v_o_1703_);
lean_dec_ref(v_o_1703_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_extract(lean_object* v_log_1707_, lean_object* v_start_1708_, lean_object* v_stop_1709_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Array_extract___redArg(v_log_1707_, v_start_1708_, v_stop_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_extract___boxed(lean_object* v_log_1711_, lean_object* v_start_1712_, lean_object* v_stop_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lake_Log_extract(v_log_1711_, v_start_1712_, v_stop_1713_);
lean_dec_ref(v_log_1711_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_dropFrom(lean_object* v_log_1715_, lean_object* v_pos_1716_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Array_shrink___redArg(v_log_1715_, v_pos_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_dropFrom___boxed(lean_object* v_log_1718_, lean_object* v_pos_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lake_Log_dropFrom(v_log_1718_, v_pos_1719_);
lean_dec(v_pos_1719_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_takeFrom(lean_object* v_log_1721_, lean_object* v_pos_1722_){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = lean_array_get_size(v_log_1721_);
v___x_1724_ = l_Array_extract___redArg(v_log_1721_, v_pos_1722_, v___x_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_takeFrom___boxed(lean_object* v_log_1725_, lean_object* v_pos_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Lake_Log_takeFrom(v_log_1725_, v_pos_1726_);
lean_dec_ref(v_log_1725_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_split(lean_object* v_log_1728_, lean_object* v_pos_1729_){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
lean_inc_ref(v_log_1728_);
v___x_1730_ = l_Array_shrink___redArg(v_log_1728_, v_pos_1729_);
v___x_1731_ = lean_array_get_size(v_log_1728_);
v___x_1732_ = l_Array_extract___redArg(v_log_1728_, v_pos_1729_, v___x_1731_);
lean_dec_ref(v_log_1728_);
v___x_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1730_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(lean_object* v_as_1735_, size_t v_i_1736_, size_t v_stop_1737_, lean_object* v_b_1738_){
_start:
{
uint8_t v___x_1739_; 
v___x_1739_ = lean_usize_dec_eq(v_i_1736_, v_stop_1737_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; size_t v___x_1745_; size_t v___x_1746_; 
v___x_1740_ = lean_array_uget_borrowed(v_as_1735_, v_i_1736_);
v___x_1741_ = l_Lake_LogEntry_toString(v___x_1740_, v___x_1739_);
v___x_1742_ = lean_string_append(v_b_1738_, v___x_1741_);
lean_dec_ref(v___x_1741_);
v___x_1743_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0___closed__0));
v___x_1744_ = lean_string_append(v___x_1742_, v___x_1743_);
v___x_1745_ = ((size_t)1ULL);
v___x_1746_ = lean_usize_add(v_i_1736_, v___x_1745_);
v_i_1736_ = v___x_1746_;
v_b_1738_ = v___x_1744_;
goto _start;
}
else
{
return v_b_1738_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0___boxed(lean_object* v_as_1748_, lean_object* v_i_1749_, lean_object* v_stop_1750_, lean_object* v_b_1751_){
_start:
{
size_t v_i_boxed_1752_; size_t v_stop_boxed_1753_; lean_object* v_res_1754_; 
v_i_boxed_1752_ = lean_unbox_usize(v_i_1749_);
lean_dec(v_i_1749_);
v_stop_boxed_1753_ = lean_unbox_usize(v_stop_1750_);
lean_dec(v_stop_1750_);
v_res_1754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(v_as_1748_, v_i_boxed_1752_, v_stop_boxed_1753_, v_b_1751_);
lean_dec_ref(v_as_1748_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_toString(lean_object* v_log_1755_){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1756_ = ((lean_object*)(l_Lake_instInhabitedLogEntry_default___closed__0));
v___x_1757_ = lean_unsigned_to_nat(0u);
v___x_1758_ = lean_array_get_size(v_log_1755_);
v___x_1759_ = lean_nat_dec_lt(v___x_1757_, v___x_1758_);
if (v___x_1759_ == 0)
{
return v___x_1756_;
}
else
{
uint8_t v___x_1760_; 
v___x_1760_ = lean_nat_dec_le(v___x_1758_, v___x_1758_);
if (v___x_1760_ == 0)
{
if (v___x_1759_ == 0)
{
return v___x_1756_;
}
else
{
size_t v___x_1761_; size_t v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = ((size_t)0ULL);
v___x_1762_ = lean_usize_of_nat(v___x_1758_);
v___x_1763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(v_log_1755_, v___x_1761_, v___x_1762_, v___x_1756_);
return v___x_1763_;
}
}
else
{
size_t v___x_1764_; size_t v___x_1765_; lean_object* v___x_1766_; 
v___x_1764_ = ((size_t)0ULL);
v___x_1765_ = lean_usize_of_nat(v___x_1758_);
v___x_1766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(v_log_1755_, v___x_1764_, v___x_1765_, v___x_1756_);
return v___x_1766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_toString___boxed(lean_object* v_log_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lake_Log_toString(v_log_1767_);
lean_dec_ref(v_log_1767_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_replay___redArg___lam__0(lean_object* v_logger_1771_, lean_object* v_x_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = lean_apply_1(v_logger_1771_, v___y_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_replay___redArg(lean_object* v_inst_1775_, lean_object* v_logger_1776_, lean_object* v_log_1777_){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; 
v___x_1778_ = lean_unsigned_to_nat(0u);
v___x_1779_ = lean_array_get_size(v_log_1777_);
v___x_1780_ = lean_box(0);
v___x_1781_ = lean_nat_dec_lt(v___x_1778_, v___x_1779_);
if (v___x_1781_ == 0)
{
lean_object* v_toApplicative_1782_; lean_object* v_toPure_1783_; lean_object* v___x_1784_; 
lean_dec_ref(v_log_1777_);
lean_dec(v_logger_1776_);
v_toApplicative_1782_ = lean_ctor_get(v_inst_1775_, 0);
lean_inc_ref(v_toApplicative_1782_);
lean_dec_ref(v_inst_1775_);
v_toPure_1783_ = lean_ctor_get(v_toApplicative_1782_, 1);
lean_inc(v_toPure_1783_);
lean_dec_ref(v_toApplicative_1782_);
v___x_1784_ = lean_apply_2(v_toPure_1783_, lean_box(0), v___x_1780_);
return v___x_1784_;
}
else
{
lean_object* v___f_1785_; uint8_t v___x_1786_; 
v___f_1785_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1785_, 0, v_logger_1776_);
v___x_1786_ = lean_nat_dec_le(v___x_1779_, v___x_1779_);
if (v___x_1786_ == 0)
{
if (v___x_1781_ == 0)
{
lean_object* v_toApplicative_1787_; lean_object* v_toPure_1788_; lean_object* v___x_1789_; 
lean_dec_ref(v___f_1785_);
lean_dec_ref(v_log_1777_);
v_toApplicative_1787_ = lean_ctor_get(v_inst_1775_, 0);
lean_inc_ref(v_toApplicative_1787_);
lean_dec_ref(v_inst_1775_);
v_toPure_1788_ = lean_ctor_get(v_toApplicative_1787_, 1);
lean_inc(v_toPure_1788_);
lean_dec_ref(v_toApplicative_1787_);
v___x_1789_ = lean_apply_2(v_toPure_1788_, lean_box(0), v___x_1780_);
return v___x_1789_;
}
else
{
size_t v___x_1790_; size_t v___x_1791_; lean_object* v___x_1792_; 
v___x_1790_ = ((size_t)0ULL);
v___x_1791_ = lean_usize_of_nat(v___x_1779_);
v___x_1792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1775_, v___f_1785_, v_log_1777_, v___x_1790_, v___x_1791_, v___x_1780_);
return v___x_1792_;
}
}
else
{
size_t v___x_1793_; size_t v___x_1794_; lean_object* v___x_1795_; 
v___x_1793_ = ((size_t)0ULL);
v___x_1794_ = lean_usize_of_nat(v___x_1779_);
v___x_1795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1775_, v___f_1785_, v_log_1777_, v___x_1793_, v___x_1794_, v___x_1780_);
return v___x_1795_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_replay(lean_object* v_m_1796_, lean_object* v_inst_1797_, lean_object* v_logger_1798_, lean_object* v_log_1799_){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1800_ = lean_unsigned_to_nat(0u);
v___x_1801_ = lean_array_get_size(v_log_1799_);
v___x_1802_ = lean_box(0);
v___x_1803_ = lean_nat_dec_lt(v___x_1800_, v___x_1801_);
if (v___x_1803_ == 0)
{
lean_object* v_toApplicative_1804_; lean_object* v_toPure_1805_; lean_object* v___x_1806_; 
lean_dec_ref(v_log_1799_);
lean_dec(v_logger_1798_);
v_toApplicative_1804_ = lean_ctor_get(v_inst_1797_, 0);
lean_inc_ref(v_toApplicative_1804_);
lean_dec_ref(v_inst_1797_);
v_toPure_1805_ = lean_ctor_get(v_toApplicative_1804_, 1);
lean_inc(v_toPure_1805_);
lean_dec_ref(v_toApplicative_1804_);
v___x_1806_ = lean_apply_2(v_toPure_1805_, lean_box(0), v___x_1802_);
return v___x_1806_;
}
else
{
lean_object* v___f_1807_; uint8_t v___x_1808_; 
v___f_1807_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1807_, 0, v_logger_1798_);
v___x_1808_ = lean_nat_dec_le(v___x_1801_, v___x_1801_);
if (v___x_1808_ == 0)
{
if (v___x_1803_ == 0)
{
lean_object* v_toApplicative_1809_; lean_object* v_toPure_1810_; lean_object* v___x_1811_; 
lean_dec_ref(v___f_1807_);
lean_dec_ref(v_log_1799_);
v_toApplicative_1809_ = lean_ctor_get(v_inst_1797_, 0);
lean_inc_ref(v_toApplicative_1809_);
lean_dec_ref(v_inst_1797_);
v_toPure_1810_ = lean_ctor_get(v_toApplicative_1809_, 1);
lean_inc(v_toPure_1810_);
lean_dec_ref(v_toApplicative_1809_);
v___x_1811_ = lean_apply_2(v_toPure_1810_, lean_box(0), v___x_1802_);
return v___x_1811_;
}
else
{
size_t v___x_1812_; size_t v___x_1813_; lean_object* v___x_1814_; 
v___x_1812_ = ((size_t)0ULL);
v___x_1813_ = lean_usize_of_nat(v___x_1801_);
v___x_1814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1797_, v___f_1807_, v_log_1799_, v___x_1812_, v___x_1813_, v___x_1802_);
return v___x_1814_;
}
}
else
{
size_t v___x_1815_; size_t v___x_1816_; lean_object* v___x_1817_; 
v___x_1815_ = ((size_t)0ULL);
v___x_1816_ = lean_usize_of_nat(v___x_1801_);
v___x_1817_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1797_, v___f_1807_, v_log_1799_, v___x_1815_, v___x_1816_, v___x_1802_);
return v___x_1817_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_filter___lam__0(lean_object* v_f_1818_, lean_object* v_x1_1819_, lean_object* v_x2_1820_){
_start:
{
lean_object* v___x_1821_; uint8_t v___x_1822_; 
lean_inc_ref(v_x2_1820_);
v___x_1821_ = lean_apply_1(v_f_1818_, v_x2_1820_);
v___x_1822_ = lean_unbox(v___x_1821_);
if (v___x_1822_ == 0)
{
lean_dec_ref(v_x2_1820_);
return v_x1_1819_;
}
else
{
lean_object* v___x_1823_; 
v___x_1823_ = lean_array_push(v_x1_1819_, v_x2_1820_);
return v___x_1823_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_filter(lean_object* v_f_1843_, lean_object* v_log_1844_){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; 
v___x_1845_ = lean_unsigned_to_nat(0u);
v___x_1846_ = lean_array_get_size(v_log_1844_);
v___x_1847_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_1848_ = ((lean_object*)(l_Lake_Log_filter___closed__9));
v___x_1849_ = lean_nat_dec_lt(v___x_1845_, v___x_1846_);
if (v___x_1849_ == 0)
{
lean_dec_ref(v_log_1844_);
lean_dec_ref(v_f_1843_);
return v___x_1847_;
}
else
{
lean_object* v___f_1850_; uint8_t v___x_1851_; 
v___f_1850_ = lean_alloc_closure((void*)(l_Lake_Log_filter___lam__0), 3, 1);
lean_closure_set(v___f_1850_, 0, v_f_1843_);
v___x_1851_ = lean_nat_dec_le(v___x_1846_, v___x_1846_);
if (v___x_1851_ == 0)
{
if (v___x_1849_ == 0)
{
lean_dec_ref(v___f_1850_);
lean_dec_ref(v_log_1844_);
return v___x_1847_;
}
else
{
size_t v___x_1852_; size_t v___x_1853_; lean_object* v___x_1854_; 
v___x_1852_ = ((size_t)0ULL);
v___x_1853_ = lean_usize_of_nat(v___x_1846_);
v___x_1854_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1848_, v___f_1850_, v_log_1844_, v___x_1852_, v___x_1853_, v___x_1847_);
return v___x_1854_;
}
}
else
{
size_t v___x_1855_; size_t v___x_1856_; lean_object* v___x_1857_; 
v___x_1855_ = ((size_t)0ULL);
v___x_1856_ = lean_usize_of_nat(v___x_1846_);
v___x_1857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1848_, v___f_1850_, v_log_1844_, v___x_1855_, v___x_1856_, v___x_1847_);
return v___x_1857_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_Log_any___lam__0(lean_object* v_f_1858_, lean_object* v_x_1859_){
_start:
{
lean_object* v___x_1860_; uint8_t v___x_1861_; 
v___x_1860_ = lean_apply_1(v_f_1858_, v_x_1859_);
v___x_1861_ = lean_unbox(v___x_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_any___lam__0___boxed(lean_object* v_f_1862_, lean_object* v_x_1863_){
_start:
{
uint8_t v_res_1864_; lean_object* v_r_1865_; 
v_res_1864_ = l_Lake_Log_any___lam__0(v_f_1862_, v_x_1863_);
v_r_1865_ = lean_box(v_res_1864_);
return v_r_1865_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_any(lean_object* v_f_1866_, lean_object* v_log_1867_){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; uint8_t v___x_1871_; 
v___x_1868_ = lean_unsigned_to_nat(0u);
v___x_1869_ = lean_array_get_size(v_log_1867_);
v___x_1870_ = ((lean_object*)(l_Lake_Log_filter___closed__9));
v___x_1871_ = lean_nat_dec_lt(v___x_1868_, v___x_1869_);
if (v___x_1871_ == 0)
{
lean_dec_ref(v_log_1867_);
lean_dec_ref(v_f_1866_);
return v___x_1871_;
}
else
{
if (v___x_1871_ == 0)
{
lean_dec_ref(v_log_1867_);
lean_dec_ref(v_f_1866_);
return v___x_1871_;
}
else
{
lean_object* v___f_1872_; size_t v___x_1873_; size_t v___x_1874_; lean_object* v___x_1875_; uint8_t v___x_1876_; 
v___f_1872_ = lean_alloc_closure((void*)(l_Lake_Log_any___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1872_, 0, v_f_1866_);
v___x_1873_ = ((size_t)0ULL);
v___x_1874_ = lean_usize_of_nat(v___x_1869_);
v___x_1875_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_1870_, v___f_1872_, v_log_1867_, v___x_1873_, v___x_1874_);
v___x_1876_ = lean_unbox(v___x_1875_);
lean_dec(v___x_1875_);
return v___x_1876_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_any___boxed(lean_object* v_f_1877_, lean_object* v_log_1878_){
_start:
{
uint8_t v_res_1879_; lean_object* v_r_1880_; 
v_res_1879_ = l_Lake_Log_any(v_f_1877_, v_log_1878_);
v_r_1880_ = lean_box(v_res_1879_);
return v_r_1880_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(lean_object* v_as_1881_, size_t v_i_1882_, size_t v_stop_1883_, uint8_t v_b_1884_){
_start:
{
uint8_t v___y_1886_; uint8_t v___x_1890_; 
v___x_1890_ = lean_usize_dec_eq(v_i_1882_, v_stop_1883_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; uint8_t v_level_1892_; uint8_t v___x_1893_; 
v___x_1891_ = lean_array_uget_borrowed(v_as_1881_, v_i_1882_);
v_level_1892_ = lean_ctor_get_uint8(v___x_1891_, sizeof(void*)*1);
v___x_1893_ = l_Lake_instOrdLogLevel_ord(v_b_1884_, v_level_1892_);
if (v___x_1893_ == 2)
{
if (v___x_1890_ == 0)
{
v___y_1886_ = v_b_1884_;
goto v___jp_1885_;
}
else
{
v___y_1886_ = v_level_1892_;
goto v___jp_1885_;
}
}
else
{
v___y_1886_ = v_level_1892_;
goto v___jp_1885_;
}
}
else
{
return v_b_1884_;
}
v___jp_1885_:
{
size_t v___x_1887_; size_t v___x_1888_; 
v___x_1887_ = ((size_t)1ULL);
v___x_1888_ = lean_usize_add(v_i_1882_, v___x_1887_);
v_i_1882_ = v___x_1888_;
v_b_1884_ = v___y_1886_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0___boxed(lean_object* v_as_1894_, lean_object* v_i_1895_, lean_object* v_stop_1896_, lean_object* v_b_1897_){
_start:
{
size_t v_i_boxed_1898_; size_t v_stop_boxed_1899_; uint8_t v_b_boxed_1900_; uint8_t v_res_1901_; lean_object* v_r_1902_; 
v_i_boxed_1898_ = lean_unbox_usize(v_i_1895_);
lean_dec(v_i_1895_);
v_stop_boxed_1899_ = lean_unbox_usize(v_stop_1896_);
lean_dec(v_stop_1896_);
v_b_boxed_1900_ = lean_unbox(v_b_1897_);
v_res_1901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(v_as_1894_, v_i_boxed_1898_, v_stop_boxed_1899_, v_b_boxed_1900_);
lean_dec_ref(v_as_1894_);
v_r_1902_ = lean_box(v_res_1901_);
return v_r_1902_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_maxLv(lean_object* v_log_1903_){
_start:
{
uint8_t v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; uint8_t v___x_1907_; 
v___x_1904_ = 0;
v___x_1905_ = lean_unsigned_to_nat(0u);
v___x_1906_ = lean_array_get_size(v_log_1903_);
v___x_1907_ = lean_nat_dec_lt(v___x_1905_, v___x_1906_);
if (v___x_1907_ == 0)
{
return v___x_1904_;
}
else
{
uint8_t v___x_1908_; 
v___x_1908_ = lean_nat_dec_le(v___x_1906_, v___x_1906_);
if (v___x_1908_ == 0)
{
if (v___x_1907_ == 0)
{
return v___x_1904_;
}
else
{
size_t v___x_1909_; size_t v___x_1910_; uint8_t v___x_1911_; 
v___x_1909_ = ((size_t)0ULL);
v___x_1910_ = lean_usize_of_nat(v___x_1906_);
v___x_1911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(v_log_1903_, v___x_1909_, v___x_1910_, v___x_1904_);
return v___x_1911_;
}
}
else
{
size_t v___x_1912_; size_t v___x_1913_; uint8_t v___x_1914_; 
v___x_1912_ = ((size_t)0ULL);
v___x_1913_ = lean_usize_of_nat(v___x_1906_);
v___x_1914_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(v_log_1903_, v___x_1912_, v___x_1913_, v___x_1904_);
return v___x_1914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_maxLv___boxed(lean_object* v_log_1915_){
_start:
{
uint8_t v_res_1916_; lean_object* v_r_1917_; 
v_res_1916_ = l_Lake_Log_maxLv(v_log_1915_);
lean_dec_ref(v_log_1915_);
v_r_1917_ = lean_box(v_res_1916_);
return v_r_1917_;
}
}
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___redArg___lam__0(lean_object* v_e_1918_, lean_object* v_s_1919_){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1920_ = lean_box(0);
v___x_1921_ = lean_array_push(v_s_1919_, v_e_1918_);
v___x_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___redArg(lean_object* v_inst_1923_, lean_object* v_e_1924_){
_start:
{
lean_object* v_modifyGet_1925_; lean_object* v___f_1926_; lean_object* v___x_1927_; 
v_modifyGet_1925_ = lean_ctor_get(v_inst_1923_, 2);
lean_inc(v_modifyGet_1925_);
lean_dec_ref(v_inst_1923_);
v___f_1926_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1926_, 0, v_e_1924_);
v___x_1927_ = lean_apply_2(v_modifyGet_1925_, lean_box(0), v___f_1926_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Lake_pushLogEntry(lean_object* v_m_1928_, lean_object* v_inst_1929_, lean_object* v_e_1930_){
_start:
{
lean_object* v_modifyGet_1931_; lean_object* v___f_1932_; lean_object* v___x_1933_; 
v_modifyGet_1931_ = lean_ctor_get(v_inst_1929_, 2);
lean_inc(v_modifyGet_1931_);
lean_dec_ref(v_inst_1929_);
v___f_1932_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1932_, 0, v_e_1930_);
v___x_1933_ = lean_apply_2(v_modifyGet_1931_, lean_box(0), v___f_1932_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_ofMonadState___redArg(lean_object* v_inst_1934_){
_start:
{
lean_object* v___x_1935_; 
v___x_1935_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(v___x_1935_, 0, lean_box(0));
lean_closure_set(v___x_1935_, 1, v_inst_1934_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_ofMonadState(lean_object* v_m_1936_, lean_object* v_inst_1937_){
_start:
{
lean_object* v___x_1938_; 
v___x_1938_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(v___x_1938_, 0, lean_box(0));
lean_closure_set(v___x_1938_, 1, v_inst_1937_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog___redArg(lean_object* v_inst_1939_){
_start:
{
lean_object* v_get_1940_; 
v_get_1940_ = lean_ctor_get(v_inst_1939_, 0);
lean_inc(v_get_1940_);
return v_get_1940_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog___redArg___boxed(lean_object* v_inst_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Lake_getLog___redArg(v_inst_1941_);
lean_dec_ref(v_inst_1941_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog(lean_object* v_m_1943_, lean_object* v_inst_1944_){
_start:
{
lean_object* v_get_1945_; 
v_get_1945_ = lean_ctor_get(v_inst_1944_, 0);
lean_inc(v_get_1945_);
return v_get_1945_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog___boxed(lean_object* v_m_1946_, lean_object* v_inst_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lake_getLog(v_m_1946_, v_inst_1947_);
lean_dec_ref(v_inst_1947_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg___lam__0(lean_object* v_x_1949_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = lean_array_get_size(v_x_1949_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg___lam__0___boxed(lean_object* v_x_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_Lake_getLogPos___redArg___lam__0(v_x_1951_);
lean_dec_ref(v_x_1951_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg(lean_object* v_inst_1954_, lean_object* v_inst_1955_){
_start:
{
lean_object* v_map_1956_; lean_object* v_get_1957_; lean_object* v___f_1958_; lean_object* v___x_1959_; 
v_map_1956_ = lean_ctor_get(v_inst_1954_, 0);
lean_inc(v_map_1956_);
lean_dec_ref(v_inst_1954_);
v_get_1957_ = lean_ctor_get(v_inst_1955_, 0);
lean_inc(v_get_1957_);
lean_dec_ref(v_inst_1955_);
v___f_1958_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_1959_ = lean_apply_4(v_map_1956_, lean_box(0), lean_box(0), v___f_1958_, v_get_1957_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos(lean_object* v_m_1960_, lean_object* v_inst_1961_, lean_object* v_inst_1962_){
_start:
{
lean_object* v_map_1963_; lean_object* v_get_1964_; lean_object* v___f_1965_; lean_object* v___x_1966_; 
v_map_1963_ = lean_ctor_get(v_inst_1961_, 0);
lean_inc(v_map_1963_);
lean_dec_ref(v_inst_1961_);
v_get_1964_ = lean_ctor_get(v_inst_1962_, 0);
lean_inc(v_get_1964_);
lean_dec_ref(v_inst_1962_);
v___f_1965_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_1966_ = lean_apply_4(v_map_1963_, lean_box(0), lean_box(0), v___f_1965_, v_get_1964_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLog___redArg___lam__0(lean_object* v_log_1967_){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_1969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1969_, 0, v_log_1967_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLog___redArg(lean_object* v_inst_1971_){
_start:
{
lean_object* v_modifyGet_1972_; lean_object* v___f_1973_; lean_object* v___x_1974_; 
v_modifyGet_1972_ = lean_ctor_get(v_inst_1971_, 2);
lean_inc(v_modifyGet_1972_);
lean_dec_ref(v_inst_1971_);
v___f_1973_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_1974_ = lean_apply_2(v_modifyGet_1972_, lean_box(0), v___f_1973_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLog(lean_object* v_m_1975_, lean_object* v_inst_1976_){
_start:
{
lean_object* v_modifyGet_1977_; lean_object* v___f_1978_; lean_object* v___x_1979_; 
v_modifyGet_1977_ = lean_ctor_get(v_inst_1976_, 2);
lean_inc(v_modifyGet_1977_);
lean_dec_ref(v_inst_1976_);
v___f_1978_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_1979_ = lean_apply_2(v_modifyGet_1977_, lean_box(0), v___f_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLogFrom___redArg___lam__0(lean_object* v_pos_1980_, lean_object* v_log_1981_){
_start:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1982_ = lean_array_get_size(v_log_1981_);
lean_inc(v_pos_1980_);
v___x_1983_ = l_Array_extract___redArg(v_log_1981_, v_pos_1980_, v___x_1982_);
v___x_1984_ = l_Array_shrink___redArg(v_log_1981_, v_pos_1980_);
lean_dec(v_pos_1980_);
v___x_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1983_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLogFrom___redArg(lean_object* v_inst_1986_, lean_object* v_pos_1987_){
_start:
{
lean_object* v_modifyGet_1988_; lean_object* v___f_1989_; lean_object* v___x_1990_; 
v_modifyGet_1988_ = lean_ctor_get(v_inst_1986_, 2);
lean_inc(v_modifyGet_1988_);
lean_dec_ref(v_inst_1986_);
v___f_1989_ = lean_alloc_closure((void*)(l_Lake_takeLogFrom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1989_, 0, v_pos_1987_);
v___x_1990_ = lean_apply_2(v_modifyGet_1988_, lean_box(0), v___f_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLogFrom(lean_object* v_m_1991_, lean_object* v_inst_1992_, lean_object* v_pos_1993_){
_start:
{
lean_object* v_modifyGet_1994_; lean_object* v___f_1995_; lean_object* v___x_1996_; 
v_modifyGet_1994_ = lean_ctor_get(v_inst_1992_, 2);
lean_inc(v_modifyGet_1994_);
lean_dec_ref(v_inst_1992_);
v___f_1995_ = lean_alloc_closure((void*)(l_Lake_takeLogFrom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1995_, 0, v_pos_1993_);
v___x_1996_ = lean_apply_2(v_modifyGet_1994_, lean_box(0), v___f_1995_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg___lam__0(lean_object* v_pos_1997_, lean_object* v_s_1998_){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_1999_ = lean_box(0);
v___x_2000_ = l_Array_shrink___redArg(v_s_1998_, v_pos_1997_);
v___x_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1999_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg___lam__0___boxed(lean_object* v_pos_2002_, lean_object* v_s_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_Lake_dropLogFrom___redArg___lam__0(v_pos_2002_, v_s_2003_);
lean_dec(v_pos_2002_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg(lean_object* v_inst_2005_, lean_object* v_pos_2006_){
_start:
{
lean_object* v_modifyGet_2007_; lean_object* v___f_2008_; lean_object* v___x_2009_; 
v_modifyGet_2007_ = lean_ctor_get(v_inst_2005_, 2);
lean_inc(v_modifyGet_2007_);
lean_dec_ref(v_inst_2005_);
v___f_2008_ = lean_alloc_closure((void*)(l_Lake_dropLogFrom___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2008_, 0, v_pos_2006_);
v___x_2009_ = lean_apply_2(v_modifyGet_2007_, lean_box(0), v___f_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom(lean_object* v_m_2010_, lean_object* v_inst_2011_, lean_object* v_pos_2012_){
_start:
{
lean_object* v_modifyGet_2013_; lean_object* v___f_2014_; lean_object* v___x_2015_; 
v_modifyGet_2013_ = lean_ctor_get(v_inst_2011_, 2);
lean_inc(v_modifyGet_2013_);
lean_dec_ref(v_inst_2011_);
v___f_2014_ = lean_alloc_closure((void*)(l_Lake_dropLogFrom___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2014_, 0, v_pos_2012_);
v___x_2015_ = lean_apply_2(v_modifyGet_2013_, lean_box(0), v___f_2014_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__1(lean_object* v_iniPos_2016_, lean_object* v_toPure_2017_, lean_object* v_log_2018_){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2019_ = lean_array_get_size(v_log_2018_);
v___x_2020_ = l_Array_extract___redArg(v_log_2018_, v_iniPos_2016_, v___x_2019_);
v___x_2021_ = lean_apply_2(v_toPure_2017_, lean_box(0), v___x_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__1___boxed(lean_object* v_iniPos_2022_, lean_object* v_toPure_2023_, lean_object* v_log_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lake_extractLog___redArg___lam__1(v_iniPos_2022_, v_toPure_2023_, v_log_2024_);
lean_dec_ref(v_log_2024_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__0(lean_object* v_toBind_2026_, lean_object* v_get_2027_, lean_object* v___f_2028_, lean_object* v_____r_2029_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = lean_apply_4(v_toBind_2026_, lean_box(0), lean_box(0), v_get_2027_, v___f_2028_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__2(lean_object* v_toPure_2031_, lean_object* v_toBind_2032_, lean_object* v_get_2033_, lean_object* v_x_2034_, lean_object* v_iniPos_2035_){
_start:
{
lean_object* v___f_2036_; lean_object* v___f_2037_; lean_object* v___x_2038_; 
v___f_2036_ = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2036_, 0, v_iniPos_2035_);
lean_closure_set(v___f_2036_, 1, v_toPure_2031_);
lean_inc(v_toBind_2032_);
v___f_2037_ = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2037_, 0, v_toBind_2032_);
lean_closure_set(v___f_2037_, 1, v_get_2033_);
lean_closure_set(v___f_2037_, 2, v___f_2036_);
v___x_2038_ = lean_apply_4(v_toBind_2032_, lean_box(0), lean_box(0), v_x_2034_, v___f_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg(lean_object* v_inst_2039_, lean_object* v_inst_2040_, lean_object* v_x_2041_){
_start:
{
lean_object* v_toApplicative_2042_; lean_object* v_toFunctor_2043_; lean_object* v_toBind_2044_; lean_object* v_toPure_2045_; lean_object* v_map_2046_; lean_object* v_get_2047_; lean_object* v___f_2048_; lean_object* v___f_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v_toApplicative_2042_ = lean_ctor_get(v_inst_2039_, 0);
lean_inc_ref(v_toApplicative_2042_);
v_toFunctor_2043_ = lean_ctor_get(v_toApplicative_2042_, 0);
lean_inc_ref(v_toFunctor_2043_);
v_toBind_2044_ = lean_ctor_get(v_inst_2039_, 1);
lean_inc_n(v_toBind_2044_, 2);
lean_dec_ref(v_inst_2039_);
v_toPure_2045_ = lean_ctor_get(v_toApplicative_2042_, 1);
lean_inc(v_toPure_2045_);
lean_dec_ref(v_toApplicative_2042_);
v_map_2046_ = lean_ctor_get(v_toFunctor_2043_, 0);
lean_inc(v_map_2046_);
lean_dec_ref(v_toFunctor_2043_);
v_get_2047_ = lean_ctor_get(v_inst_2040_, 0);
lean_inc_n(v_get_2047_, 2);
lean_dec_ref(v_inst_2040_);
v___f_2048_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2049_ = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2049_, 0, v_toPure_2045_);
lean_closure_set(v___f_2049_, 1, v_toBind_2044_);
lean_closure_set(v___f_2049_, 2, v_get_2047_);
lean_closure_set(v___f_2049_, 3, v_x_2041_);
v___x_2050_ = lean_apply_4(v_map_2046_, lean_box(0), lean_box(0), v___f_2048_, v_get_2047_);
v___x_2051_ = lean_apply_4(v_toBind_2044_, lean_box(0), lean_box(0), v___x_2050_, v___f_2049_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog(lean_object* v_m_2052_, lean_object* v_inst_2053_, lean_object* v_inst_2054_, lean_object* v_x_2055_){
_start:
{
lean_object* v_toApplicative_2056_; lean_object* v_toFunctor_2057_; lean_object* v_toBind_2058_; lean_object* v_toPure_2059_; lean_object* v_map_2060_; lean_object* v_get_2061_; lean_object* v___f_2062_; lean_object* v___f_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v_toApplicative_2056_ = lean_ctor_get(v_inst_2053_, 0);
lean_inc_ref(v_toApplicative_2056_);
v_toFunctor_2057_ = lean_ctor_get(v_toApplicative_2056_, 0);
lean_inc_ref(v_toFunctor_2057_);
v_toBind_2058_ = lean_ctor_get(v_inst_2053_, 1);
lean_inc_n(v_toBind_2058_, 2);
lean_dec_ref(v_inst_2053_);
v_toPure_2059_ = lean_ctor_get(v_toApplicative_2056_, 1);
lean_inc(v_toPure_2059_);
lean_dec_ref(v_toApplicative_2056_);
v_map_2060_ = lean_ctor_get(v_toFunctor_2057_, 0);
lean_inc(v_map_2060_);
lean_dec_ref(v_toFunctor_2057_);
v_get_2061_ = lean_ctor_get(v_inst_2054_, 0);
lean_inc_n(v_get_2061_, 2);
lean_dec_ref(v_inst_2054_);
v___f_2062_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2063_ = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2063_, 0, v_toPure_2059_);
lean_closure_set(v___f_2063_, 1, v_toBind_2058_);
lean_closure_set(v___f_2063_, 2, v_get_2061_);
lean_closure_set(v___f_2063_, 3, v_x_2055_);
v___x_2064_ = lean_apply_4(v_map_2060_, lean_box(0), lean_box(0), v___f_2062_, v_get_2061_);
v___x_2065_ = lean_apply_4(v_toBind_2058_, lean_box(0), lean_box(0), v___x_2064_, v___f_2063_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__1(lean_object* v_iniPos_2066_, lean_object* v_a_2067_, lean_object* v_toPure_2068_, lean_object* v_log_2069_){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2070_ = lean_array_get_size(v_log_2069_);
v___x_2071_ = l_Array_extract___redArg(v_log_2069_, v_iniPos_2066_, v___x_2070_);
v___x_2072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2072_, 0, v_a_2067_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
v___x_2073_ = lean_apply_2(v_toPure_2068_, lean_box(0), v___x_2072_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__1___boxed(lean_object* v_iniPos_2074_, lean_object* v_a_2075_, lean_object* v_toPure_2076_, lean_object* v_log_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Lake_withExtractLog___redArg___lam__1(v_iniPos_2074_, v_a_2075_, v_toPure_2076_, v_log_2077_);
lean_dec_ref(v_log_2077_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__0(lean_object* v_iniPos_2079_, lean_object* v_toPure_2080_, lean_object* v_toBind_2081_, lean_object* v_get_2082_, lean_object* v_a_2083_){
_start:
{
lean_object* v___f_2084_; lean_object* v___x_2085_; 
v___f_2084_ = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2084_, 0, v_iniPos_2079_);
lean_closure_set(v___f_2084_, 1, v_a_2083_);
lean_closure_set(v___f_2084_, 2, v_toPure_2080_);
v___x_2085_ = lean_apply_4(v_toBind_2081_, lean_box(0), lean_box(0), v_get_2082_, v___f_2084_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__2(lean_object* v_toPure_2086_, lean_object* v_toBind_2087_, lean_object* v_get_2088_, lean_object* v_x_2089_, lean_object* v_iniPos_2090_){
_start:
{
lean_object* v___f_2091_; lean_object* v___x_2092_; 
lean_inc(v_toBind_2087_);
v___f_2091_ = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2091_, 0, v_iniPos_2090_);
lean_closure_set(v___f_2091_, 1, v_toPure_2086_);
lean_closure_set(v___f_2091_, 2, v_toBind_2087_);
lean_closure_set(v___f_2091_, 3, v_get_2088_);
v___x_2092_ = lean_apply_4(v_toBind_2087_, lean_box(0), lean_box(0), v_x_2089_, v___f_2091_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg(lean_object* v_inst_2093_, lean_object* v_inst_2094_, lean_object* v_x_2095_){
_start:
{
lean_object* v_toApplicative_2096_; lean_object* v_toFunctor_2097_; lean_object* v_toBind_2098_; lean_object* v_toPure_2099_; lean_object* v_map_2100_; lean_object* v_get_2101_; lean_object* v___f_2102_; lean_object* v___f_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v_toApplicative_2096_ = lean_ctor_get(v_inst_2093_, 0);
lean_inc_ref(v_toApplicative_2096_);
v_toFunctor_2097_ = lean_ctor_get(v_toApplicative_2096_, 0);
lean_inc_ref(v_toFunctor_2097_);
v_toBind_2098_ = lean_ctor_get(v_inst_2093_, 1);
lean_inc_n(v_toBind_2098_, 2);
lean_dec_ref(v_inst_2093_);
v_toPure_2099_ = lean_ctor_get(v_toApplicative_2096_, 1);
lean_inc(v_toPure_2099_);
lean_dec_ref(v_toApplicative_2096_);
v_map_2100_ = lean_ctor_get(v_toFunctor_2097_, 0);
lean_inc(v_map_2100_);
lean_dec_ref(v_toFunctor_2097_);
v_get_2101_ = lean_ctor_get(v_inst_2094_, 0);
lean_inc_n(v_get_2101_, 2);
lean_dec_ref(v_inst_2094_);
v___f_2102_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2103_ = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2103_, 0, v_toPure_2099_);
lean_closure_set(v___f_2103_, 1, v_toBind_2098_);
lean_closure_set(v___f_2103_, 2, v_get_2101_);
lean_closure_set(v___f_2103_, 3, v_x_2095_);
v___x_2104_ = lean_apply_4(v_map_2100_, lean_box(0), lean_box(0), v___f_2102_, v_get_2101_);
v___x_2105_ = lean_apply_4(v_toBind_2098_, lean_box(0), lean_box(0), v___x_2104_, v___f_2103_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog(lean_object* v_m_2106_, lean_object* v_00_u03b1_2107_, lean_object* v_inst_2108_, lean_object* v_inst_2109_, lean_object* v_x_2110_){
_start:
{
lean_object* v_toApplicative_2111_; lean_object* v_toFunctor_2112_; lean_object* v_toBind_2113_; lean_object* v_toPure_2114_; lean_object* v_map_2115_; lean_object* v_get_2116_; lean_object* v___f_2117_; lean_object* v___f_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v_toApplicative_2111_ = lean_ctor_get(v_inst_2108_, 0);
lean_inc_ref(v_toApplicative_2111_);
v_toFunctor_2112_ = lean_ctor_get(v_toApplicative_2111_, 0);
lean_inc_ref(v_toFunctor_2112_);
v_toBind_2113_ = lean_ctor_get(v_inst_2108_, 1);
lean_inc_n(v_toBind_2113_, 2);
lean_dec_ref(v_inst_2108_);
v_toPure_2114_ = lean_ctor_get(v_toApplicative_2111_, 1);
lean_inc(v_toPure_2114_);
lean_dec_ref(v_toApplicative_2111_);
v_map_2115_ = lean_ctor_get(v_toFunctor_2112_, 0);
lean_inc(v_map_2115_);
lean_dec_ref(v_toFunctor_2112_);
v_get_2116_ = lean_ctor_get(v_inst_2109_, 0);
lean_inc_n(v_get_2116_, 2);
lean_dec_ref(v_inst_2109_);
v___f_2117_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2118_ = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2118_, 0, v_toPure_2114_);
lean_closure_set(v___f_2118_, 1, v_toBind_2113_);
lean_closure_set(v___f_2118_, 2, v_get_2116_);
lean_closure_set(v___f_2118_, 3, v_x_2110_);
v___x_2119_ = lean_apply_4(v_map_2115_, lean_box(0), lean_box(0), v___f_2117_, v_get_2116_);
v___x_2120_ = lean_apply_4(v_toBind_2113_, lean_box(0), lean_box(0), v___x_2119_, v___f_2118_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__1(lean_object* v_iniPos_2121_, lean_object* v_inst_2122_, lean_object* v_toPure_2123_, lean_object* v_a_2124_, lean_object* v_endPos_2125_){
_start:
{
uint8_t v___x_2126_; 
v___x_2126_ = lean_nat_dec_eq(v_iniPos_2121_, v_endPos_2125_);
if (v___x_2126_ == 0)
{
lean_object* v_throw_2127_; lean_object* v___x_2128_; 
lean_dec(v_a_2124_);
lean_dec(v_toPure_2123_);
v_throw_2127_ = lean_ctor_get(v_inst_2122_, 0);
lean_inc(v_throw_2127_);
lean_dec_ref(v_inst_2122_);
v___x_2128_ = lean_apply_2(v_throw_2127_, lean_box(0), v_iniPos_2121_);
return v___x_2128_;
}
else
{
lean_object* v___x_2129_; 
lean_dec_ref(v_inst_2122_);
lean_dec(v_iniPos_2121_);
v___x_2129_ = lean_apply_2(v_toPure_2123_, lean_box(0), v_a_2124_);
return v___x_2129_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__1___boxed(lean_object* v_iniPos_2130_, lean_object* v_inst_2131_, lean_object* v_toPure_2132_, lean_object* v_a_2133_, lean_object* v_endPos_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l_Lake_throwIfLogs___redArg___lam__1(v_iniPos_2130_, v_inst_2131_, v_toPure_2132_, v_a_2133_, v_endPos_2134_);
lean_dec(v_endPos_2134_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__0(lean_object* v_iniPos_2136_, lean_object* v_inst_2137_, lean_object* v_toPure_2138_, lean_object* v_toBind_2139_, lean_object* v___x_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v___f_2142_; lean_object* v___x_2143_; 
v___f_2142_ = lean_alloc_closure((void*)(l_Lake_throwIfLogs___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2142_, 0, v_iniPos_2136_);
lean_closure_set(v___f_2142_, 1, v_inst_2137_);
lean_closure_set(v___f_2142_, 2, v_toPure_2138_);
lean_closure_set(v___f_2142_, 3, v_a_2141_);
v___x_2143_ = lean_apply_4(v_toBind_2139_, lean_box(0), lean_box(0), v___x_2140_, v___f_2142_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__2(lean_object* v_inst_2144_, lean_object* v_toPure_2145_, lean_object* v_toBind_2146_, lean_object* v___x_2147_, lean_object* v_x_2148_, lean_object* v_iniPos_2149_){
_start:
{
lean_object* v___f_2150_; lean_object* v___x_2151_; 
lean_inc(v_toBind_2146_);
v___f_2150_ = lean_alloc_closure((void*)(l_Lake_throwIfLogs___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2150_, 0, v_iniPos_2149_);
lean_closure_set(v___f_2150_, 1, v_inst_2144_);
lean_closure_set(v___f_2150_, 2, v_toPure_2145_);
lean_closure_set(v___f_2150_, 3, v_toBind_2146_);
lean_closure_set(v___f_2150_, 4, v___x_2147_);
v___x_2151_ = lean_apply_4(v_toBind_2146_, lean_box(0), lean_box(0), v_x_2148_, v___f_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg(lean_object* v_inst_2152_, lean_object* v_inst_2153_, lean_object* v_inst_2154_, lean_object* v_x_2155_){
_start:
{
lean_object* v_toApplicative_2156_; lean_object* v_toFunctor_2157_; lean_object* v_toBind_2158_; lean_object* v_toPure_2159_; lean_object* v_map_2160_; lean_object* v_get_2161_; lean_object* v___f_2162_; lean_object* v___x_2163_; lean_object* v___f_2164_; lean_object* v___x_2165_; 
v_toApplicative_2156_ = lean_ctor_get(v_inst_2152_, 0);
lean_inc_ref(v_toApplicative_2156_);
v_toFunctor_2157_ = lean_ctor_get(v_toApplicative_2156_, 0);
lean_inc_ref(v_toFunctor_2157_);
v_toBind_2158_ = lean_ctor_get(v_inst_2152_, 1);
lean_inc_n(v_toBind_2158_, 2);
lean_dec_ref(v_inst_2152_);
v_toPure_2159_ = lean_ctor_get(v_toApplicative_2156_, 1);
lean_inc(v_toPure_2159_);
lean_dec_ref(v_toApplicative_2156_);
v_map_2160_ = lean_ctor_get(v_toFunctor_2157_, 0);
lean_inc(v_map_2160_);
lean_dec_ref(v_toFunctor_2157_);
v_get_2161_ = lean_ctor_get(v_inst_2153_, 0);
lean_inc(v_get_2161_);
lean_dec_ref(v_inst_2153_);
v___f_2162_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_2163_ = lean_apply_4(v_map_2160_, lean_box(0), lean_box(0), v___f_2162_, v_get_2161_);
lean_inc(v___x_2163_);
v___f_2164_ = lean_alloc_closure((void*)(l_Lake_throwIfLogs___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2164_, 0, v_inst_2154_);
lean_closure_set(v___f_2164_, 1, v_toPure_2159_);
lean_closure_set(v___f_2164_, 2, v_toBind_2158_);
lean_closure_set(v___f_2164_, 3, v___x_2163_);
lean_closure_set(v___f_2164_, 4, v_x_2155_);
v___x_2165_ = lean_apply_4(v_toBind_2158_, lean_box(0), lean_box(0), v___x_2163_, v___f_2164_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs(lean_object* v_m_2166_, lean_object* v_00_u03b1_2167_, lean_object* v_inst_2168_, lean_object* v_inst_2169_, lean_object* v_inst_2170_, lean_object* v_x_2171_){
_start:
{
lean_object* v_toApplicative_2172_; lean_object* v_toFunctor_2173_; lean_object* v_toBind_2174_; lean_object* v_toPure_2175_; lean_object* v_map_2176_; lean_object* v_get_2177_; lean_object* v___f_2178_; lean_object* v___x_2179_; lean_object* v___f_2180_; lean_object* v___x_2181_; 
v_toApplicative_2172_ = lean_ctor_get(v_inst_2168_, 0);
lean_inc_ref(v_toApplicative_2172_);
v_toFunctor_2173_ = lean_ctor_get(v_toApplicative_2172_, 0);
lean_inc_ref(v_toFunctor_2173_);
v_toBind_2174_ = lean_ctor_get(v_inst_2168_, 1);
lean_inc_n(v_toBind_2174_, 2);
lean_dec_ref(v_inst_2168_);
v_toPure_2175_ = lean_ctor_get(v_toApplicative_2172_, 1);
lean_inc(v_toPure_2175_);
lean_dec_ref(v_toApplicative_2172_);
v_map_2176_ = lean_ctor_get(v_toFunctor_2173_, 0);
lean_inc(v_map_2176_);
lean_dec_ref(v_toFunctor_2173_);
v_get_2177_ = lean_ctor_get(v_inst_2169_, 0);
lean_inc(v_get_2177_);
lean_dec_ref(v_inst_2169_);
v___f_2178_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_2179_ = lean_apply_4(v_map_2176_, lean_box(0), lean_box(0), v___f_2178_, v_get_2177_);
lean_inc(v___x_2179_);
v___f_2180_ = lean_alloc_closure((void*)(l_Lake_throwIfLogs___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2180_, 0, v_inst_2170_);
lean_closure_set(v___f_2180_, 1, v_toPure_2175_);
lean_closure_set(v___f_2180_, 2, v_toBind_2174_);
lean_closure_set(v___f_2180_, 3, v___x_2179_);
lean_closure_set(v___f_2180_, 4, v_x_2171_);
v___x_2181_ = lean_apply_4(v_toBind_2174_, lean_box(0), lean_box(0), v___x_2179_, v___f_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__1(lean_object* v_throw_2182_, lean_object* v_iniPos_2183_, lean_object* v_x_2184_){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = lean_apply_2(v_throw_2182_, lean_box(0), v_iniPos_2183_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__1___boxed(lean_object* v_throw_2186_, lean_object* v_iniPos_2187_, lean_object* v_x_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Lake_withLogErrorPos___redArg___lam__1(v_throw_2186_, v_iniPos_2187_, v_x_2188_);
lean_dec(v_x_2188_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__0(lean_object* v_inst_2190_, lean_object* v_self_2191_, lean_object* v_iniPos_2192_){
_start:
{
lean_object* v_throw_2193_; lean_object* v_tryCatch_2194_; lean_object* v___f_2195_; lean_object* v___x_2196_; 
v_throw_2193_ = lean_ctor_get(v_inst_2190_, 0);
lean_inc(v_throw_2193_);
v_tryCatch_2194_ = lean_ctor_get(v_inst_2190_, 1);
lean_inc(v_tryCatch_2194_);
lean_dec_ref(v_inst_2190_);
v___f_2195_ = lean_alloc_closure((void*)(l_Lake_withLogErrorPos___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2195_, 0, v_throw_2193_);
lean_closure_set(v___f_2195_, 1, v_iniPos_2192_);
v___x_2196_ = lean_apply_3(v_tryCatch_2194_, lean_box(0), v_self_2191_, v___f_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg(lean_object* v_inst_2197_, lean_object* v_inst_2198_, lean_object* v_inst_2199_, lean_object* v_self_2200_){
_start:
{
lean_object* v_toApplicative_2201_; lean_object* v_toFunctor_2202_; lean_object* v_toBind_2203_; lean_object* v_map_2204_; lean_object* v_get_2205_; lean_object* v___f_2206_; lean_object* v___f_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v_toApplicative_2201_ = lean_ctor_get(v_inst_2197_, 0);
v_toFunctor_2202_ = lean_ctor_get(v_toApplicative_2201_, 0);
lean_inc_ref(v_toFunctor_2202_);
v_toBind_2203_ = lean_ctor_get(v_inst_2197_, 1);
lean_inc(v_toBind_2203_);
lean_dec_ref(v_inst_2197_);
v_map_2204_ = lean_ctor_get(v_toFunctor_2202_, 0);
lean_inc(v_map_2204_);
lean_dec_ref(v_toFunctor_2202_);
v_get_2205_ = lean_ctor_get(v_inst_2198_, 0);
lean_inc(v_get_2205_);
lean_dec_ref(v_inst_2198_);
v___f_2206_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2207_ = lean_alloc_closure((void*)(l_Lake_withLogErrorPos___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2207_, 0, v_inst_2199_);
lean_closure_set(v___f_2207_, 1, v_self_2200_);
v___x_2208_ = lean_apply_4(v_map_2204_, lean_box(0), lean_box(0), v___f_2206_, v_get_2205_);
v___x_2209_ = lean_apply_4(v_toBind_2203_, lean_box(0), lean_box(0), v___x_2208_, v___f_2207_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos(lean_object* v_m_2210_, lean_object* v_00_u03b1_2211_, lean_object* v_inst_2212_, lean_object* v_inst_2213_, lean_object* v_inst_2214_, lean_object* v_self_2215_){
_start:
{
lean_object* v_toApplicative_2216_; lean_object* v_toFunctor_2217_; lean_object* v_toBind_2218_; lean_object* v_map_2219_; lean_object* v_get_2220_; lean_object* v___f_2221_; lean_object* v___f_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v_toApplicative_2216_ = lean_ctor_get(v_inst_2212_, 0);
v_toFunctor_2217_ = lean_ctor_get(v_toApplicative_2216_, 0);
lean_inc_ref(v_toFunctor_2217_);
v_toBind_2218_ = lean_ctor_get(v_inst_2212_, 1);
lean_inc(v_toBind_2218_);
lean_dec_ref(v_inst_2212_);
v_map_2219_ = lean_ctor_get(v_toFunctor_2217_, 0);
lean_inc(v_map_2219_);
lean_dec_ref(v_toFunctor_2217_);
v_get_2220_ = lean_ctor_get(v_inst_2213_, 0);
lean_inc(v_get_2220_);
lean_dec_ref(v_inst_2213_);
v___f_2221_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2222_ = lean_alloc_closure((void*)(l_Lake_withLogErrorPos___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2222_, 0, v_inst_2214_);
lean_closure_set(v___f_2222_, 1, v_self_2215_);
v___x_2223_ = lean_apply_4(v_map_2219_, lean_box(0), lean_box(0), v___f_2221_, v_get_2220_);
v___x_2224_ = lean_apply_4(v_toBind_2218_, lean_box(0), lean_box(0), v___x_2223_, v___f_2222_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__1(lean_object* v_toPure_2225_, lean_object* v_x_2226_){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = lean_box(0);
v___x_2228_ = lean_apply_2(v_toPure_2225_, lean_box(0), v___x_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__1___boxed(lean_object* v_toPure_2229_, lean_object* v_x_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lake_errorWithLog___redArg___lam__1(v_toPure_2229_, v_x_2230_);
lean_dec(v_x_2230_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__0(lean_object* v_throw_2232_, lean_object* v_iniPos_2233_, lean_object* v_____r_2234_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = lean_apply_2(v_throw_2232_, lean_box(0), v_iniPos_2233_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__2(lean_object* v_inst_2236_, lean_object* v_self_2237_, lean_object* v___f_2238_, lean_object* v_toBind_2239_, lean_object* v_iniPos_2240_){
_start:
{
lean_object* v_throw_2241_; lean_object* v_tryCatch_2242_; lean_object* v___f_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v_throw_2241_ = lean_ctor_get(v_inst_2236_, 0);
lean_inc(v_throw_2241_);
v_tryCatch_2242_ = lean_ctor_get(v_inst_2236_, 1);
lean_inc(v_tryCatch_2242_);
lean_dec_ref(v_inst_2236_);
v___f_2243_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2243_, 0, v_throw_2241_);
lean_closure_set(v___f_2243_, 1, v_iniPos_2240_);
v___x_2244_ = lean_apply_3(v_tryCatch_2242_, lean_box(0), v_self_2237_, v___f_2238_);
v___x_2245_ = lean_apply_4(v_toBind_2239_, lean_box(0), lean_box(0), v___x_2244_, v___f_2243_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg(lean_object* v_inst_2246_, lean_object* v_inst_2247_, lean_object* v_inst_2248_, lean_object* v_self_2249_){
_start:
{
lean_object* v_toApplicative_2250_; lean_object* v_toFunctor_2251_; lean_object* v_toBind_2252_; lean_object* v_toPure_2253_; lean_object* v_map_2254_; lean_object* v_get_2255_; lean_object* v___f_2256_; lean_object* v___f_2257_; lean_object* v___f_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v_toApplicative_2250_ = lean_ctor_get(v_inst_2246_, 0);
lean_inc_ref(v_toApplicative_2250_);
v_toFunctor_2251_ = lean_ctor_get(v_toApplicative_2250_, 0);
lean_inc_ref(v_toFunctor_2251_);
v_toBind_2252_ = lean_ctor_get(v_inst_2246_, 1);
lean_inc_n(v_toBind_2252_, 2);
lean_dec_ref(v_inst_2246_);
v_toPure_2253_ = lean_ctor_get(v_toApplicative_2250_, 1);
lean_inc(v_toPure_2253_);
lean_dec_ref(v_toApplicative_2250_);
v_map_2254_ = lean_ctor_get(v_toFunctor_2251_, 0);
lean_inc(v_map_2254_);
lean_dec_ref(v_toFunctor_2251_);
v_get_2255_ = lean_ctor_get(v_inst_2247_, 0);
lean_inc(v_get_2255_);
lean_dec_ref(v_inst_2247_);
v___f_2256_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2257_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2257_, 0, v_toPure_2253_);
v___f_2258_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2258_, 0, v_inst_2248_);
lean_closure_set(v___f_2258_, 1, v_self_2249_);
lean_closure_set(v___f_2258_, 2, v___f_2257_);
lean_closure_set(v___f_2258_, 3, v_toBind_2252_);
v___x_2259_ = lean_apply_4(v_map_2254_, lean_box(0), lean_box(0), v___f_2256_, v_get_2255_);
v___x_2260_ = lean_apply_4(v_toBind_2252_, lean_box(0), lean_box(0), v___x_2259_, v___f_2258_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog(lean_object* v_m_2261_, lean_object* v_00_u03b2_2262_, lean_object* v_inst_2263_, lean_object* v_inst_2264_, lean_object* v_inst_2265_, lean_object* v_self_2266_){
_start:
{
lean_object* v_toApplicative_2267_; lean_object* v_toFunctor_2268_; lean_object* v_toBind_2269_; lean_object* v_toPure_2270_; lean_object* v_map_2271_; lean_object* v_get_2272_; lean_object* v___f_2273_; lean_object* v___f_2274_; lean_object* v___f_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v_toApplicative_2267_ = lean_ctor_get(v_inst_2263_, 0);
lean_inc_ref(v_toApplicative_2267_);
v_toFunctor_2268_ = lean_ctor_get(v_toApplicative_2267_, 0);
lean_inc_ref(v_toFunctor_2268_);
v_toBind_2269_ = lean_ctor_get(v_inst_2263_, 1);
lean_inc_n(v_toBind_2269_, 2);
lean_dec_ref(v_inst_2263_);
v_toPure_2270_ = lean_ctor_get(v_toApplicative_2267_, 1);
lean_inc(v_toPure_2270_);
lean_dec_ref(v_toApplicative_2267_);
v_map_2271_ = lean_ctor_get(v_toFunctor_2268_, 0);
lean_inc(v_map_2271_);
lean_dec_ref(v_toFunctor_2268_);
v_get_2272_ = lean_ctor_get(v_inst_2264_, 0);
lean_inc(v_get_2272_);
lean_dec_ref(v_inst_2264_);
v___f_2273_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2274_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2274_, 0, v_toPure_2270_);
v___f_2275_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2275_, 0, v_inst_2265_);
lean_closure_set(v___f_2275_, 1, v_self_2266_);
lean_closure_set(v___f_2275_, 2, v___f_2274_);
lean_closure_set(v___f_2275_, 3, v_toBind_2269_);
v___x_2276_ = lean_apply_4(v_map_2271_, lean_box(0), lean_box(0), v___f_2273_, v_get_2272_);
v___x_2277_ = lean_apply_4(v_toBind_2269_, lean_box(0), lean_box(0), v___x_2276_, v___f_2275_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__0(lean_object* v_x_2278_){
_start:
{
lean_object* v_fst_2279_; 
v_fst_2279_ = lean_ctor_get(v_x_2278_, 0);
lean_inc(v_fst_2279_);
return v_fst_2279_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__0___boxed(lean_object* v_x_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_Lake_withLoggedIO___redArg___lam__0(v_x_2280_);
lean_dec_ref(v_x_2280_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__1(lean_object* v_buf_2282_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = lean_st_ref_get(v_buf_2282_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__1___boxed(lean_object* v_buf_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l_Lake_withLoggedIO___redArg___lam__1(v_buf_2285_);
lean_dec(v_buf_2285_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__2(lean_object* v_toPure_2288_, lean_object* v_a_2289_, lean_object* v_____r_2290_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = lean_apply_2(v_toPure_2288_, lean_box(0), v_a_2289_);
return v___x_2291_;
}
}
static lean_object* _init_l_Lake_withLoggedIO___redArg___lam__3___closed__4(void){
_start:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2296_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___lam__3___closed__3));
v___x_2297_ = lean_unsigned_to_nat(46u);
v___x_2298_ = lean_unsigned_to_nat(193u);
v___x_2299_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___lam__3___closed__2));
v___x_2300_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___lam__3___closed__1));
v___x_2301_ = l_mkPanicMessageWithDecl(v___x_2300_, v___x_2299_, v___x_2298_, v___x_2297_, v___x_2296_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__3(lean_object* v___x_2302_, lean_object* v_inst_2303_, lean_object* v_toBind_2304_, lean_object* v___f_2305_, lean_object* v_toPure_2306_, lean_object* v_a_2307_, lean_object* v_buf_2308_){
_start:
{
lean_object* v___y_2310_; lean_object* v_data_2323_; uint8_t v___x_2324_; 
v_data_2323_ = lean_ctor_get(v_buf_2308_, 0);
lean_inc_ref(v_data_2323_);
lean_dec_ref(v_buf_2308_);
v___x_2324_ = lean_string_validate_utf8(v_data_2323_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
lean_dec_ref(v_data_2323_);
v___x_2325_ = ((lean_object*)(l_Lake_instInhabitedLogEntry_default___closed__0));
v___x_2326_ = lean_obj_once(&l_Lake_withLoggedIO___redArg___lam__3___closed__4, &l_Lake_withLoggedIO___redArg___lam__3___closed__4_once, _init_l_Lake_withLoggedIO___redArg___lam__3___closed__4);
v___x_2327_ = l_panic___redArg(v___x_2325_, v___x_2326_);
v___y_2310_ = v___x_2327_;
goto v___jp_2309_;
}
else
{
lean_object* v___x_2328_; 
v___x_2328_ = lean_string_from_utf8_unchecked(v_data_2323_);
v___y_2310_ = v___x_2328_;
goto v___jp_2309_;
}
v___jp_2309_:
{
lean_object* v___x_2311_; uint8_t v___x_2312_; 
v___x_2311_ = lean_string_utf8_byte_size(v___y_2310_);
v___x_2312_ = lean_nat_dec_eq(v___x_2311_, v___x_2302_);
if (v___x_2312_ == 0)
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
lean_dec(v_a_2307_);
lean_dec(v_toPure_2306_);
v___x_2313_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___lam__3___closed__0));
v___x_2314_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2314_, 0, v___y_2310_);
lean_ctor_set(v___x_2314_, 1, v___x_2302_);
lean_ctor_set(v___x_2314_, 2, v___x_2311_);
v___x_2315_ = l_String_Slice_trimAscii(v___x_2314_);
v___x_2316_ = l_String_Slice_toString(v___x_2315_);
lean_dec_ref(v___x_2315_);
v___x_2317_ = lean_string_append(v___x_2313_, v___x_2316_);
lean_dec_ref(v___x_2316_);
v___x_2318_ = 1;
v___x_2319_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2319_, 0, v___x_2317_);
lean_ctor_set_uint8(v___x_2319_, sizeof(void*)*1, v___x_2318_);
v___x_2320_ = lean_apply_1(v_inst_2303_, v___x_2319_);
v___x_2321_ = lean_apply_4(v_toBind_2304_, lean_box(0), lean_box(0), v___x_2320_, v___f_2305_);
return v___x_2321_;
}
else
{
lean_object* v___x_2322_; 
lean_dec_ref(v___y_2310_);
lean_dec(v___f_2305_);
lean_dec(v_toBind_2304_);
lean_dec(v_inst_2303_);
lean_dec(v___x_2302_);
v___x_2322_ = lean_apply_2(v_toPure_2306_, lean_box(0), v_a_2307_);
return v___x_2322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__4(lean_object* v_toPure_2329_, lean_object* v___x_2330_, lean_object* v_inst_2331_, lean_object* v_toBind_2332_, lean_object* v_inst_2333_, lean_object* v___f_2334_, lean_object* v_a_2335_){
_start:
{
lean_object* v___f_2336_; lean_object* v___f_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
lean_inc(v_a_2335_);
lean_inc(v_toPure_2329_);
v___f_2336_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2336_, 0, v_toPure_2329_);
lean_closure_set(v___f_2336_, 1, v_a_2335_);
lean_inc(v_toBind_2332_);
v___f_2337_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__3), 7, 6);
lean_closure_set(v___f_2337_, 0, v___x_2330_);
lean_closure_set(v___f_2337_, 1, v_inst_2331_);
lean_closure_set(v___f_2337_, 2, v_toBind_2332_);
lean_closure_set(v___f_2337_, 3, v___f_2336_);
lean_closure_set(v___f_2337_, 4, v_toPure_2329_);
lean_closure_set(v___f_2337_, 5, v_a_2335_);
v___x_2338_ = lean_apply_2(v_inst_2333_, lean_box(0), v___f_2334_);
v___x_2339_ = lean_apply_4(v_toBind_2332_, lean_box(0), lean_box(0), v___x_2338_, v___f_2337_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__5(lean_object* v_stderr_2340_, lean_object* v_inst_2341_, lean_object* v_mapConst_2342_, lean_object* v_____r_2343_){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2344_ = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(v___x_2344_, 0, v_stderr_2340_);
v___x_2345_ = lean_apply_2(v_inst_2341_, lean_box(0), v___x_2344_);
v___x_2346_ = lean_box(0);
v___x_2347_ = lean_apply_4(v_mapConst_2342_, lean_box(0), lean_box(0), v___x_2346_, v___x_2345_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__6(lean_object* v___x_2348_, lean_object* v_x_2349_){
_start:
{
lean_inc(v___x_2348_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__6___boxed(lean_object* v___x_2350_, lean_object* v_x_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Lake_withLoggedIO___redArg___lam__6(v___x_2350_, v_x_2351_);
lean_dec(v_x_2351_);
lean_dec(v___x_2350_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__7(lean_object* v_toFunctor_2353_, lean_object* v_inst_2354_, lean_object* v_stdout_2355_, lean_object* v_toBind_2356_, lean_object* v_inst_2357_, lean_object* v_x_2358_, lean_object* v___f_2359_, lean_object* v___f_2360_, lean_object* v_stderr_2361_){
_start:
{
lean_object* v_map_2362_; lean_object* v_mapConst_2363_; lean_object* v___f_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___f_2370_; lean_object* v_y_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v_map_2362_ = lean_ctor_get(v_toFunctor_2353_, 0);
lean_inc(v_map_2362_);
v_mapConst_2363_ = lean_ctor_get(v_toFunctor_2353_, 1);
lean_inc_n(v_mapConst_2363_, 2);
lean_dec_ref(v_toFunctor_2353_);
lean_inc(v_inst_2354_);
v___f_2364_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__5), 4, 3);
lean_closure_set(v___f_2364_, 0, v_stderr_2361_);
lean_closure_set(v___f_2364_, 1, v_inst_2354_);
lean_closure_set(v___f_2364_, 2, v_mapConst_2363_);
v___x_2365_ = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(v___x_2365_, 0, v_stdout_2355_);
v___x_2366_ = lean_apply_2(v_inst_2354_, lean_box(0), v___x_2365_);
v___x_2367_ = lean_box(0);
v___x_2368_ = lean_apply_4(v_mapConst_2363_, lean_box(0), lean_box(0), v___x_2367_, v___x_2366_);
lean_inc(v_toBind_2356_);
v___x_2369_ = lean_apply_4(v_toBind_2356_, lean_box(0), lean_box(0), v___x_2368_, v___f_2364_);
v___f_2370_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__6___boxed), 2, 1);
lean_closure_set(v___f_2370_, 0, v___x_2369_);
v_y_2371_ = lean_apply_4(v_inst_2357_, lean_box(0), lean_box(0), v_x_2358_, v___f_2370_);
v___x_2372_ = lean_apply_4(v_map_2362_, lean_box(0), lean_box(0), v___f_2359_, v_y_2371_);
v___x_2373_ = lean_apply_4(v_toBind_2356_, lean_box(0), lean_box(0), v___x_2372_, v___f_2360_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__8(lean_object* v_toFunctor_2374_, lean_object* v_inst_2375_, lean_object* v_toBind_2376_, lean_object* v_inst_2377_, lean_object* v_x_2378_, lean_object* v___f_2379_, lean_object* v___f_2380_, lean_object* v___x_2381_, lean_object* v_stdout_2382_){
_start:
{
lean_object* v___f_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
lean_inc(v_toBind_2376_);
lean_inc(v_inst_2375_);
v___f_2383_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__7), 9, 8);
lean_closure_set(v___f_2383_, 0, v_toFunctor_2374_);
lean_closure_set(v___f_2383_, 1, v_inst_2375_);
lean_closure_set(v___f_2383_, 2, v_stdout_2382_);
lean_closure_set(v___f_2383_, 3, v_toBind_2376_);
lean_closure_set(v___f_2383_, 4, v_inst_2377_);
lean_closure_set(v___f_2383_, 5, v_x_2378_);
lean_closure_set(v___f_2383_, 6, v___f_2379_);
lean_closure_set(v___f_2383_, 7, v___f_2380_);
v___x_2384_ = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(v___x_2384_, 0, v___x_2381_);
v___x_2385_ = lean_apply_2(v_inst_2375_, lean_box(0), v___x_2384_);
v___x_2386_ = lean_apply_4(v_toBind_2376_, lean_box(0), lean_box(0), v___x_2385_, v___f_2383_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__9(lean_object* v_toPure_2387_, lean_object* v___x_2388_, lean_object* v_inst_2389_, lean_object* v_toBind_2390_, lean_object* v_inst_2391_, lean_object* v_toFunctor_2392_, lean_object* v_inst_2393_, lean_object* v_x_2394_, lean_object* v___f_2395_, lean_object* v_buf_2396_){
_start:
{
lean_object* v___f_2397_; lean_object* v___f_2398_; lean_object* v___x_2399_; lean_object* v___f_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
lean_inc(v_buf_2396_);
v___f_2397_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2397_, 0, v_buf_2396_);
lean_inc_n(v_inst_2391_, 2);
lean_inc_n(v_toBind_2390_, 2);
v___f_2398_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__4), 7, 6);
lean_closure_set(v___f_2398_, 0, v_toPure_2387_);
lean_closure_set(v___f_2398_, 1, v___x_2388_);
lean_closure_set(v___f_2398_, 2, v_inst_2389_);
lean_closure_set(v___f_2398_, 3, v_toBind_2390_);
lean_closure_set(v___f_2398_, 4, v_inst_2391_);
lean_closure_set(v___f_2398_, 5, v___f_2397_);
v___x_2399_ = l_IO_FS_Stream_ofBuffer(v_buf_2396_);
lean_inc_ref(v___x_2399_);
v___f_2400_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__8), 9, 8);
lean_closure_set(v___f_2400_, 0, v_toFunctor_2392_);
lean_closure_set(v___f_2400_, 1, v_inst_2391_);
lean_closure_set(v___f_2400_, 2, v_toBind_2390_);
lean_closure_set(v___f_2400_, 3, v_inst_2393_);
lean_closure_set(v___f_2400_, 4, v_x_2394_);
lean_closure_set(v___f_2400_, 5, v___f_2395_);
lean_closure_set(v___f_2400_, 6, v___f_2398_);
lean_closure_set(v___f_2400_, 7, v___x_2399_);
v___x_2401_ = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(v___x_2401_, 0, v___x_2399_);
v___x_2402_ = lean_apply_2(v_inst_2391_, lean_box(0), v___x_2401_);
v___x_2403_ = lean_apply_4(v_toBind_2390_, lean_box(0), lean_box(0), v___x_2402_, v___f_2400_);
return v___x_2403_;
}
}
static lean_object* _init_l_Lake_withLoggedIO___redArg___closed__1(void){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2405_ = lean_unsigned_to_nat(0u);
v___x_2406_ = l_ByteArray_empty;
v___x_2407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
lean_ctor_set(v___x_2407_, 1, v___x_2405_);
return v___x_2407_;
}
}
static lean_object* _init_l_Lake_withLoggedIO___redArg___closed__2(void){
_start:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = lean_obj_once(&l_Lake_withLoggedIO___redArg___closed__1, &l_Lake_withLoggedIO___redArg___closed__1_once, _init_l_Lake_withLoggedIO___redArg___closed__1);
v___x_2409_ = lean_alloc_closure((void*)(l_IO_mkRef___boxed), 3, 2);
lean_closure_set(v___x_2409_, 0, lean_box(0));
lean_closure_set(v___x_2409_, 1, v___x_2408_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg(lean_object* v_inst_2410_, lean_object* v_inst_2411_, lean_object* v_inst_2412_, lean_object* v_inst_2413_, lean_object* v_x_2414_){
_start:
{
lean_object* v_toApplicative_2415_; lean_object* v_toBind_2416_; lean_object* v_toFunctor_2417_; lean_object* v_toPure_2418_; lean_object* v___f_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___f_2423_; lean_object* v___x_2424_; 
v_toApplicative_2415_ = lean_ctor_get(v_inst_2410_, 0);
lean_inc_ref(v_toApplicative_2415_);
v_toBind_2416_ = lean_ctor_get(v_inst_2410_, 1);
lean_inc_n(v_toBind_2416_, 2);
lean_dec_ref(v_inst_2410_);
v_toFunctor_2417_ = lean_ctor_get(v_toApplicative_2415_, 0);
lean_inc_ref(v_toFunctor_2417_);
v_toPure_2418_ = lean_ctor_get(v_toApplicative_2415_, 1);
lean_inc(v_toPure_2418_);
lean_dec_ref(v_toApplicative_2415_);
v___f_2419_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___closed__0));
v___x_2420_ = lean_unsigned_to_nat(0u);
v___x_2421_ = lean_obj_once(&l_Lake_withLoggedIO___redArg___closed__2, &l_Lake_withLoggedIO___redArg___closed__2_once, _init_l_Lake_withLoggedIO___redArg___closed__2);
lean_inc(v_inst_2411_);
v___x_2422_ = lean_apply_2(v_inst_2411_, lean_box(0), v___x_2421_);
v___f_2423_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__9), 10, 9);
lean_closure_set(v___f_2423_, 0, v_toPure_2418_);
lean_closure_set(v___f_2423_, 1, v___x_2420_);
lean_closure_set(v___f_2423_, 2, v_inst_2412_);
lean_closure_set(v___f_2423_, 3, v_toBind_2416_);
lean_closure_set(v___f_2423_, 4, v_inst_2411_);
lean_closure_set(v___f_2423_, 5, v_toFunctor_2417_);
lean_closure_set(v___f_2423_, 6, v_inst_2413_);
lean_closure_set(v___f_2423_, 7, v_x_2414_);
lean_closure_set(v___f_2423_, 8, v___f_2419_);
v___x_2424_ = lean_apply_4(v_toBind_2416_, lean_box(0), lean_box(0), v___x_2422_, v___f_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO(lean_object* v_m_2425_, lean_object* v_00_u03b1_2426_, lean_object* v_inst_2427_, lean_object* v_inst_2428_, lean_object* v_inst_2429_, lean_object* v_inst_2430_, lean_object* v_x_2431_){
_start:
{
lean_object* v_toApplicative_2432_; lean_object* v_toBind_2433_; lean_object* v_toFunctor_2434_; lean_object* v_toPure_2435_; lean_object* v___f_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___f_2440_; lean_object* v___x_2441_; 
v_toApplicative_2432_ = lean_ctor_get(v_inst_2427_, 0);
lean_inc_ref(v_toApplicative_2432_);
v_toBind_2433_ = lean_ctor_get(v_inst_2427_, 1);
lean_inc_n(v_toBind_2433_, 2);
lean_dec_ref(v_inst_2427_);
v_toFunctor_2434_ = lean_ctor_get(v_toApplicative_2432_, 0);
lean_inc_ref(v_toFunctor_2434_);
v_toPure_2435_ = lean_ctor_get(v_toApplicative_2432_, 1);
lean_inc(v_toPure_2435_);
lean_dec_ref(v_toApplicative_2432_);
v___f_2436_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___closed__0));
v___x_2437_ = lean_unsigned_to_nat(0u);
v___x_2438_ = lean_obj_once(&l_Lake_withLoggedIO___redArg___closed__2, &l_Lake_withLoggedIO___redArg___closed__2_once, _init_l_Lake_withLoggedIO___redArg___closed__2);
lean_inc(v_inst_2428_);
v___x_2439_ = lean_apply_2(v_inst_2428_, lean_box(0), v___x_2438_);
v___f_2440_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__9), 10, 9);
lean_closure_set(v___f_2440_, 0, v_toPure_2435_);
lean_closure_set(v___f_2440_, 1, v___x_2437_);
lean_closure_set(v___f_2440_, 2, v_inst_2429_);
lean_closure_set(v___f_2440_, 3, v_toBind_2433_);
lean_closure_set(v___f_2440_, 4, v_inst_2428_);
lean_closure_set(v___f_2440_, 5, v_toFunctor_2434_);
lean_closure_set(v___f_2440_, 6, v_inst_2430_);
lean_closure_set(v___f_2440_, 7, v_x_2431_);
lean_closure_set(v___f_2440_, 8, v___f_2436_);
v___x_2441_ = lean_apply_4(v_toBind_2433_, lean_box(0), lean_box(0), v___x_2439_, v___f_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_error___redArg___lam__3(lean_object* v_inst_2442_, lean_object* v___x_2443_, lean_object* v___f_2444_, lean_object* v_toBind_2445_, lean_object* v_iniPos_2446_){
_start:
{
lean_object* v_throw_2447_; lean_object* v_tryCatch_2448_; lean_object* v___f_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v_throw_2447_ = lean_ctor_get(v_inst_2442_, 0);
lean_inc(v_throw_2447_);
v_tryCatch_2448_ = lean_ctor_get(v_inst_2442_, 1);
lean_inc(v_tryCatch_2448_);
lean_dec_ref(v_inst_2442_);
v___f_2449_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2449_, 0, v_throw_2447_);
lean_closure_set(v___f_2449_, 1, v_iniPos_2446_);
v___x_2450_ = lean_apply_3(v_tryCatch_2448_, lean_box(0), v___x_2443_, v___f_2444_);
v___x_2451_ = lean_apply_4(v_toBind_2445_, lean_box(0), lean_box(0), v___x_2450_, v___f_2449_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_error___redArg(lean_object* v_inst_2452_, lean_object* v_inst_2453_, lean_object* v_inst_2454_, lean_object* v_inst_2455_, lean_object* v_msg_2456_){
_start:
{
lean_object* v_toApplicative_2457_; lean_object* v_toFunctor_2458_; lean_object* v_toBind_2459_; lean_object* v_toPure_2460_; lean_object* v_map_2461_; lean_object* v_get_2462_; lean_object* v___f_2463_; uint8_t v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___f_2467_; lean_object* v___f_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v_toApplicative_2457_ = lean_ctor_get(v_inst_2452_, 0);
lean_inc_ref(v_toApplicative_2457_);
v_toFunctor_2458_ = lean_ctor_get(v_toApplicative_2457_, 0);
lean_inc_ref(v_toFunctor_2458_);
v_toBind_2459_ = lean_ctor_get(v_inst_2452_, 1);
lean_inc_n(v_toBind_2459_, 2);
lean_dec_ref(v_inst_2452_);
v_toPure_2460_ = lean_ctor_get(v_toApplicative_2457_, 1);
lean_inc(v_toPure_2460_);
lean_dec_ref(v_toApplicative_2457_);
v_map_2461_ = lean_ctor_get(v_toFunctor_2458_, 0);
lean_inc(v_map_2461_);
lean_dec_ref(v_toFunctor_2458_);
v_get_2462_ = lean_ctor_get(v_inst_2454_, 0);
lean_inc(v_get_2462_);
lean_dec_ref(v_inst_2454_);
v___f_2463_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_2464_ = 3;
v___x_2465_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2465_, 0, v_msg_2456_);
lean_ctor_set_uint8(v___x_2465_, sizeof(void*)*1, v___x_2464_);
v___x_2466_ = lean_apply_1(v_inst_2453_, v___x_2465_);
v___f_2467_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2467_, 0, v_toPure_2460_);
v___f_2468_ = lean_alloc_closure((void*)(l_Lake_ELog_error___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2468_, 0, v_inst_2455_);
lean_closure_set(v___f_2468_, 1, v___x_2466_);
lean_closure_set(v___f_2468_, 2, v___f_2467_);
lean_closure_set(v___f_2468_, 3, v_toBind_2459_);
v___x_2469_ = lean_apply_4(v_map_2461_, lean_box(0), lean_box(0), v___f_2463_, v_get_2462_);
v___x_2470_ = lean_apply_4(v_toBind_2459_, lean_box(0), lean_box(0), v___x_2469_, v___f_2468_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_error(lean_object* v_m_2471_, lean_object* v_00_u03b1_2472_, lean_object* v_inst_2473_, lean_object* v_inst_2474_, lean_object* v_inst_2475_, lean_object* v_inst_2476_, lean_object* v_msg_2477_){
_start:
{
lean_object* v_toApplicative_2478_; lean_object* v_toFunctor_2479_; lean_object* v_toBind_2480_; lean_object* v_toPure_2481_; lean_object* v_map_2482_; lean_object* v_get_2483_; lean_object* v___f_2484_; uint8_t v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___f_2488_; lean_object* v___f_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v_toApplicative_2478_ = lean_ctor_get(v_inst_2473_, 0);
lean_inc_ref(v_toApplicative_2478_);
v_toFunctor_2479_ = lean_ctor_get(v_toApplicative_2478_, 0);
lean_inc_ref(v_toFunctor_2479_);
v_toBind_2480_ = lean_ctor_get(v_inst_2473_, 1);
lean_inc_n(v_toBind_2480_, 2);
lean_dec_ref(v_inst_2473_);
v_toPure_2481_ = lean_ctor_get(v_toApplicative_2478_, 1);
lean_inc(v_toPure_2481_);
lean_dec_ref(v_toApplicative_2478_);
v_map_2482_ = lean_ctor_get(v_toFunctor_2479_, 0);
lean_inc(v_map_2482_);
lean_dec_ref(v_toFunctor_2479_);
v_get_2483_ = lean_ctor_get(v_inst_2475_, 0);
lean_inc(v_get_2483_);
lean_dec_ref(v_inst_2475_);
v___f_2484_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_2485_ = 3;
v___x_2486_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2486_, 0, v_msg_2477_);
lean_ctor_set_uint8(v___x_2486_, sizeof(void*)*1, v___x_2485_);
v___x_2487_ = lean_apply_1(v_inst_2474_, v___x_2486_);
v___f_2488_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2488_, 0, v_toPure_2481_);
v___f_2489_ = lean_alloc_closure((void*)(l_Lake_ELog_error___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2489_, 0, v_inst_2476_);
lean_closure_set(v___f_2489_, 1, v___x_2487_);
lean_closure_set(v___f_2489_, 2, v___f_2488_);
lean_closure_set(v___f_2489_, 3, v_toBind_2480_);
v___x_2490_ = lean_apply_4(v_map_2482_, lean_box(0), lean_box(0), v___f_2484_, v_get_2483_);
v___x_2491_ = lean_apply_4(v_toBind_2480_, lean_box(0), lean_box(0), v___x_2490_, v___f_2489_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_monadError___redArg___lam__4(lean_object* v_inst_2492_, lean_object* v_inst_2493_, lean_object* v_inst_2494_, lean_object* v_inst_2495_, lean_object* v___f_2496_, lean_object* v_00_u03b1_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v_toApplicative_2499_; lean_object* v_toFunctor_2500_; lean_object* v_toBind_2501_; lean_object* v_toPure_2502_; lean_object* v_map_2503_; lean_object* v_get_2504_; uint8_t v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___f_2508_; lean_object* v___f_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v_toApplicative_2499_ = lean_ctor_get(v_inst_2492_, 0);
lean_inc_ref(v_toApplicative_2499_);
v_toFunctor_2500_ = lean_ctor_get(v_toApplicative_2499_, 0);
lean_inc_ref(v_toFunctor_2500_);
v_toBind_2501_ = lean_ctor_get(v_inst_2492_, 1);
lean_inc_n(v_toBind_2501_, 2);
lean_dec_ref(v_inst_2492_);
v_toPure_2502_ = lean_ctor_get(v_toApplicative_2499_, 1);
lean_inc(v_toPure_2502_);
lean_dec_ref(v_toApplicative_2499_);
v_map_2503_ = lean_ctor_get(v_toFunctor_2500_, 0);
lean_inc(v_map_2503_);
lean_dec_ref(v_toFunctor_2500_);
v_get_2504_ = lean_ctor_get(v_inst_2493_, 0);
lean_inc(v_get_2504_);
lean_dec_ref(v_inst_2493_);
v___x_2505_ = 3;
v___x_2506_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2506_, 0, v___y_2498_);
lean_ctor_set_uint8(v___x_2506_, sizeof(void*)*1, v___x_2505_);
v___x_2507_ = lean_apply_1(v_inst_2494_, v___x_2506_);
v___f_2508_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2508_, 0, v_toPure_2502_);
v___f_2509_ = lean_alloc_closure((void*)(l_Lake_ELog_error___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2509_, 0, v_inst_2495_);
lean_closure_set(v___f_2509_, 1, v___x_2507_);
lean_closure_set(v___f_2509_, 2, v___f_2508_);
lean_closure_set(v___f_2509_, 3, v_toBind_2501_);
v___x_2510_ = lean_apply_4(v_map_2503_, lean_box(0), lean_box(0), v___f_2496_, v_get_2504_);
v___x_2511_ = lean_apply_4(v_toBind_2501_, lean_box(0), lean_box(0), v___x_2510_, v___f_2509_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_monadError___redArg(lean_object* v_inst_2512_, lean_object* v_inst_2513_, lean_object* v_inst_2514_, lean_object* v_inst_2515_){
_start:
{
lean_object* v___f_2516_; lean_object* v___f_2517_; 
v___f_2516_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2517_ = lean_alloc_closure((void*)(l_Lake_ELog_monadError___redArg___lam__4), 7, 5);
lean_closure_set(v___f_2517_, 0, v_inst_2512_);
lean_closure_set(v___f_2517_, 1, v_inst_2514_);
lean_closure_set(v___f_2517_, 2, v_inst_2513_);
lean_closure_set(v___f_2517_, 3, v_inst_2515_);
lean_closure_set(v___f_2517_, 4, v___f_2516_);
return v___f_2517_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_monadError(lean_object* v_m_2518_, lean_object* v_inst_2519_, lean_object* v_inst_2520_, lean_object* v_inst_2521_, lean_object* v_inst_2522_){
_start:
{
lean_object* v___f_2523_; lean_object* v___f_2524_; 
v___f_2523_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2524_ = lean_alloc_closure((void*)(l_Lake_ELog_monadError___redArg___lam__4), 7, 5);
lean_closure_set(v___f_2524_, 0, v_inst_2519_);
lean_closure_set(v___f_2524_, 1, v_inst_2521_);
lean_closure_set(v___f_2524_, 2, v_inst_2520_);
lean_closure_set(v___f_2524_, 3, v_inst_2522_);
lean_closure_set(v___f_2524_, 4, v___f_2523_);
return v___f_2524_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_failure___redArg___lam__1(lean_object* v_inst_2525_, lean_object* v_____do__lift_2526_){
_start:
{
lean_object* v_throw_2527_; lean_object* v___x_2528_; 
v_throw_2527_ = lean_ctor_get(v_inst_2525_, 0);
lean_inc(v_throw_2527_);
lean_dec_ref(v_inst_2525_);
v___x_2528_ = lean_apply_2(v_throw_2527_, lean_box(0), v_____do__lift_2526_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_failure___redArg(lean_object* v_inst_2529_, lean_object* v_inst_2530_, lean_object* v_inst_2531_){
_start:
{
lean_object* v_toApplicative_2532_; lean_object* v_toFunctor_2533_; lean_object* v_toBind_2534_; lean_object* v_map_2535_; lean_object* v_get_2536_; lean_object* v___f_2537_; lean_object* v___f_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v_toApplicative_2532_ = lean_ctor_get(v_inst_2529_, 0);
v_toFunctor_2533_ = lean_ctor_get(v_toApplicative_2532_, 0);
lean_inc_ref(v_toFunctor_2533_);
v_toBind_2534_ = lean_ctor_get(v_inst_2529_, 1);
lean_inc(v_toBind_2534_);
lean_dec_ref(v_inst_2529_);
v_map_2535_ = lean_ctor_get(v_toFunctor_2533_, 0);
lean_inc(v_map_2535_);
lean_dec_ref(v_toFunctor_2533_);
v_get_2536_ = lean_ctor_get(v_inst_2530_, 0);
lean_inc(v_get_2536_);
lean_dec_ref(v_inst_2530_);
v___f_2537_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2538_ = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2538_, 0, v_inst_2531_);
v___x_2539_ = lean_apply_4(v_map_2535_, lean_box(0), lean_box(0), v___f_2537_, v_get_2536_);
v___x_2540_ = lean_apply_4(v_toBind_2534_, lean_box(0), lean_box(0), v___x_2539_, v___f_2538_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_failure(lean_object* v_m_2541_, lean_object* v_00_u03b1_2542_, lean_object* v_inst_2543_, lean_object* v_inst_2544_, lean_object* v_inst_2545_){
_start:
{
lean_object* v_toApplicative_2546_; lean_object* v_toFunctor_2547_; lean_object* v_toBind_2548_; lean_object* v_map_2549_; lean_object* v_get_2550_; lean_object* v___f_2551_; lean_object* v___f_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v_toApplicative_2546_ = lean_ctor_get(v_inst_2543_, 0);
v_toFunctor_2547_ = lean_ctor_get(v_toApplicative_2546_, 0);
lean_inc_ref(v_toFunctor_2547_);
v_toBind_2548_ = lean_ctor_get(v_inst_2543_, 1);
lean_inc(v_toBind_2548_);
lean_dec_ref(v_inst_2543_);
v_map_2549_ = lean_ctor_get(v_toFunctor_2547_, 0);
lean_inc(v_map_2549_);
lean_dec_ref(v_toFunctor_2547_);
v_get_2550_ = lean_ctor_get(v_inst_2544_, 0);
lean_inc(v_get_2550_);
lean_dec_ref(v_inst_2544_);
v___f_2551_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2552_ = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2552_, 0, v_inst_2545_);
v___x_2553_ = lean_apply_4(v_map_2549_, lean_box(0), lean_box(0), v___f_2551_, v_get_2550_);
v___x_2554_ = lean_apply_4(v_toBind_2548_, lean_box(0), lean_box(0), v___x_2553_, v___f_2552_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__0(lean_object* v_y_2555_, lean_object* v_____r_2556_){
_start:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2557_ = lean_box(0);
v___x_2558_ = lean_apply_1(v_y_2555_, v___x_2557_);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__1(lean_object* v_errPos_2559_, lean_object* v_s_2560_){
_start:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2561_ = lean_box(0);
v___x_2562_ = l_Array_shrink___redArg(v_s_2560_, v_errPos_2559_);
v___x_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2561_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__1___boxed(lean_object* v_errPos_2564_, lean_object* v_s_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lake_ELog_orElse___redArg___lam__1(v_errPos_2564_, v_s_2565_);
lean_dec(v_errPos_2564_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__2(lean_object* v_inst_2567_, lean_object* v_toBind_2568_, lean_object* v___f_2569_, lean_object* v_errPos_2570_){
_start:
{
lean_object* v_modifyGet_2571_; lean_object* v___f_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v_modifyGet_2571_ = lean_ctor_get(v_inst_2567_, 2);
lean_inc(v_modifyGet_2571_);
lean_dec_ref(v_inst_2567_);
v___f_2572_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2572_, 0, v_errPos_2570_);
v___x_2573_ = lean_apply_2(v_modifyGet_2571_, lean_box(0), v___f_2572_);
v___x_2574_ = lean_apply_4(v_toBind_2568_, lean_box(0), lean_box(0), v___x_2573_, v___f_2569_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg(lean_object* v_inst_2575_, lean_object* v_inst_2576_, lean_object* v_inst_2577_, lean_object* v_x_2578_, lean_object* v_y_2579_){
_start:
{
lean_object* v_toBind_2580_; lean_object* v_tryCatch_2581_; lean_object* v___f_2582_; lean_object* v___f_2583_; lean_object* v___x_2584_; 
v_toBind_2580_ = lean_ctor_get(v_inst_2575_, 1);
lean_inc(v_toBind_2580_);
lean_dec_ref(v_inst_2575_);
v_tryCatch_2581_ = lean_ctor_get(v_inst_2577_, 1);
lean_inc(v_tryCatch_2581_);
lean_dec_ref(v_inst_2577_);
v___f_2582_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2582_, 0, v_y_2579_);
v___f_2583_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2583_, 0, v_inst_2576_);
lean_closure_set(v___f_2583_, 1, v_toBind_2580_);
lean_closure_set(v___f_2583_, 2, v___f_2582_);
v___x_2584_ = lean_apply_3(v_tryCatch_2581_, lean_box(0), v_x_2578_, v___f_2583_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse(lean_object* v_m_2585_, lean_object* v_00_u03b1_2586_, lean_object* v_inst_2587_, lean_object* v_inst_2588_, lean_object* v_inst_2589_, lean_object* v_x_2590_, lean_object* v_y_2591_){
_start:
{
lean_object* v_toBind_2592_; lean_object* v_tryCatch_2593_; lean_object* v___f_2594_; lean_object* v___f_2595_; lean_object* v___x_2596_; 
v_toBind_2592_ = lean_ctor_get(v_inst_2587_, 1);
lean_inc(v_toBind_2592_);
lean_dec_ref(v_inst_2587_);
v_tryCatch_2593_ = lean_ctor_get(v_inst_2589_, 1);
lean_inc(v_tryCatch_2593_);
lean_dec_ref(v_inst_2589_);
v___f_2594_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2594_, 0, v_y_2591_);
v___f_2595_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2595_, 0, v_inst_2588_);
lean_closure_set(v___f_2595_, 1, v_toBind_2592_);
lean_closure_set(v___f_2595_, 2, v___f_2594_);
v___x_2596_ = lean_apply_3(v_tryCatch_2593_, lean_box(0), v_x_2590_, v___f_2595_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__2(lean_object* v_toApplicative_2597_, lean_object* v_inst_2598_, lean_object* v___f_2599_, lean_object* v_toBind_2600_, lean_object* v___f_2601_, lean_object* v_00_u03b1_2602_){
_start:
{
lean_object* v_toFunctor_2603_; lean_object* v_map_2604_; lean_object* v_get_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v_toFunctor_2603_ = lean_ctor_get(v_toApplicative_2597_, 0);
lean_inc_ref(v_toFunctor_2603_);
lean_dec_ref(v_toApplicative_2597_);
v_map_2604_ = lean_ctor_get(v_toFunctor_2603_, 0);
lean_inc(v_map_2604_);
lean_dec_ref(v_toFunctor_2603_);
v_get_2605_ = lean_ctor_get(v_inst_2598_, 0);
lean_inc(v_get_2605_);
lean_dec_ref(v_inst_2598_);
v___x_2606_ = lean_apply_4(v_map_2604_, lean_box(0), lean_box(0), v___f_2599_, v_get_2605_);
v___x_2607_ = lean_apply_4(v_toBind_2600_, lean_box(0), lean_box(0), v___x_2606_, v___f_2601_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__0(lean_object* v___y_2608_, lean_object* v_____r_2609_){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = lean_box(0);
v___x_2611_ = lean_apply_1(v___y_2608_, v___x_2610_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__4(lean_object* v_inst_2612_, lean_object* v_inst_2613_, lean_object* v_toBind_2614_, lean_object* v_00_u03b1_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
lean_object* v_tryCatch_2618_; lean_object* v___f_2619_; lean_object* v___f_2620_; lean_object* v___x_2621_; 
v_tryCatch_2618_ = lean_ctor_get(v_inst_2612_, 1);
lean_inc(v_tryCatch_2618_);
lean_dec_ref(v_inst_2612_);
v___f_2619_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2619_, 0, v___y_2617_);
v___f_2620_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2620_, 0, v_inst_2613_);
lean_closure_set(v___f_2620_, 1, v_toBind_2614_);
lean_closure_set(v___f_2620_, 2, v___f_2619_);
v___x_2621_ = lean_apply_3(v_tryCatch_2618_, lean_box(0), v___y_2616_, v___f_2620_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg(lean_object* v_inst_2622_, lean_object* v_inst_2623_, lean_object* v_inst_2624_){
_start:
{
lean_object* v_toApplicative_2625_; lean_object* v_toBind_2626_; lean_object* v___f_2627_; lean_object* v___f_2628_; lean_object* v___f_2629_; lean_object* v___f_2630_; lean_object* v___x_2631_; 
v_toApplicative_2625_ = lean_ctor_get(v_inst_2622_, 0);
lean_inc_ref_n(v_toApplicative_2625_, 2);
v_toBind_2626_ = lean_ctor_get(v_inst_2622_, 1);
lean_inc_n(v_toBind_2626_, 2);
lean_dec_ref(v_inst_2622_);
v___f_2627_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
lean_inc_ref(v_inst_2624_);
v___f_2628_ = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2628_, 0, v_inst_2624_);
lean_inc_ref(v_inst_2623_);
v___f_2629_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2629_, 0, v_toApplicative_2625_);
lean_closure_set(v___f_2629_, 1, v_inst_2623_);
lean_closure_set(v___f_2629_, 2, v___f_2627_);
lean_closure_set(v___f_2629_, 3, v_toBind_2626_);
lean_closure_set(v___f_2629_, 4, v___f_2628_);
v___f_2630_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__4), 6, 3);
lean_closure_set(v___f_2630_, 0, v_inst_2624_);
lean_closure_set(v___f_2630_, 1, v_inst_2623_);
lean_closure_set(v___f_2630_, 2, v_toBind_2626_);
v___x_2631_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2631_, 0, v_toApplicative_2625_);
lean_ctor_set(v___x_2631_, 1, v___f_2629_);
lean_ctor_set(v___x_2631_, 2, v___f_2630_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative(lean_object* v_m_2632_, lean_object* v_inst_2633_, lean_object* v_inst_2634_, lean_object* v_inst_2635_){
_start:
{
lean_object* v_toApplicative_2636_; lean_object* v_toBind_2637_; lean_object* v___f_2638_; lean_object* v___f_2639_; lean_object* v___f_2640_; lean_object* v___f_2641_; lean_object* v___x_2642_; 
v_toApplicative_2636_ = lean_ctor_get(v_inst_2633_, 0);
lean_inc_ref_n(v_toApplicative_2636_, 2);
v_toBind_2637_ = lean_ctor_get(v_inst_2633_, 1);
lean_inc_n(v_toBind_2637_, 2);
lean_dec_ref(v_inst_2633_);
v___f_2638_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
lean_inc_ref(v_inst_2635_);
v___f_2639_ = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2639_, 0, v_inst_2635_);
lean_inc_ref(v_inst_2634_);
v___f_2640_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2640_, 0, v_toApplicative_2636_);
lean_closure_set(v___f_2640_, 1, v_inst_2634_);
lean_closure_set(v___f_2640_, 2, v___f_2638_);
lean_closure_set(v___f_2640_, 3, v_toBind_2637_);
lean_closure_set(v___f_2640_, 4, v___f_2639_);
v___f_2641_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__4), 6, 3);
lean_closure_set(v___f_2641_, 0, v_inst_2635_);
lean_closure_set(v___f_2641_, 1, v_inst_2634_);
lean_closure_set(v___f_2641_, 2, v_toBind_2637_);
v___x_2642_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2642_, 0, v_toApplicative_2636_);
lean_ctor_set(v___x_2642_, 1, v___f_2640_);
lean_ctor_set(v___x_2642_, 2, v___f_2641_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogLogTOfMonad___redArg(lean_object* v_inst_2643_){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2644_ = l_instMonadStateOfStateTOfMonad___redArg(v_inst_2643_);
v___x_2645_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(v___x_2645_, 0, lean_box(0));
lean_closure_set(v___x_2645_, 1, v___x_2644_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogLogTOfMonad(lean_object* v_m_2646_, lean_object* v_inst_2647_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l_Lake_instMonadLogLogTOfMonad___redArg(v_inst_2647_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run___redArg(lean_object* v_self_2649_, lean_object* v_log_2650_){
_start:
{
lean_object* v___x_2651_; 
v___x_2651_ = lean_apply_1(v_self_2649_, v_log_2650_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run(lean_object* v_m_2652_, lean_object* v_00_u03b1_2653_, lean_object* v_self_2654_, lean_object* v_log_2655_){
_start:
{
lean_object* v___x_2656_; 
v___x_2656_ = lean_apply_1(v_self_2654_, v_log_2655_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg___lam__0(lean_object* v_x_2657_){
_start:
{
lean_object* v_fst_2658_; 
v_fst_2658_ = lean_ctor_get(v_x_2657_, 0);
lean_inc(v_fst_2658_);
return v_fst_2658_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg___lam__0___boxed(lean_object* v_x_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_Lake_LogT_run_x27___redArg___lam__0(v_x_2659_);
lean_dec_ref(v_x_2659_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg(lean_object* v_inst_2662_, lean_object* v_self_2663_, lean_object* v_log_2664_){
_start:
{
lean_object* v_map_2665_; lean_object* v___f_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
v_map_2665_ = lean_ctor_get(v_inst_2662_, 0);
lean_inc(v_map_2665_);
lean_dec_ref(v_inst_2662_);
v___f_2666_ = ((lean_object*)(l_Lake_LogT_run_x27___redArg___closed__0));
v___x_2667_ = lean_apply_1(v_self_2663_, v_log_2664_);
v___x_2668_ = lean_apply_4(v_map_2665_, lean_box(0), lean_box(0), v___f_2666_, v___x_2667_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27(lean_object* v_m_2669_, lean_object* v_00_u03b1_2670_, lean_object* v_inst_2671_, lean_object* v_self_2672_, lean_object* v_log_2673_){
_start:
{
lean_object* v_map_2674_; lean_object* v___f_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v_map_2674_ = lean_ctor_get(v_inst_2671_, 0);
lean_inc(v_map_2674_);
lean_dec_ref(v_inst_2671_);
v___f_2675_ = ((lean_object*)(l_Lake_LogT_run_x27___redArg___closed__0));
v___x_2676_ = lean_apply_1(v_self_2672_, v_log_2673_);
v___x_2677_ = lean_apply_4(v_map_2674_, lean_box(0), lean_box(0), v___f_2675_, v___x_2676_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__1(lean_object* v_toPure_2678_, lean_object* v_fst_2679_, lean_object* v_____r_2680_){
_start:
{
lean_object* v___x_2681_; 
v___x_2681_ = lean_apply_2(v_toPure_2678_, lean_box(0), v_fst_2679_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__0(lean_object* v_toPure_2682_, lean_object* v_set_2683_, lean_object* v_toBind_2684_, lean_object* v_____x_2685_){
_start:
{
lean_object* v_fst_2686_; lean_object* v_snd_2687_; lean_object* v___f_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v_fst_2686_ = lean_ctor_get(v_____x_2685_, 0);
lean_inc(v_fst_2686_);
v_snd_2687_ = lean_ctor_get(v_____x_2685_, 1);
lean_inc(v_snd_2687_);
lean_dec_ref(v_____x_2685_);
v___f_2688_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2688_, 0, v_toPure_2682_);
lean_closure_set(v___f_2688_, 1, v_fst_2686_);
v___x_2689_ = lean_apply_1(v_set_2683_, v_snd_2687_);
v___x_2690_ = lean_apply_4(v_toBind_2684_, lean_box(0), lean_box(0), v___x_2689_, v___f_2688_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__2(lean_object* v_self_2691_, lean_object* v_inst_2692_, lean_object* v_toBind_2693_, lean_object* v___f_2694_, lean_object* v_____do__lift_2695_){
_start:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2696_ = lean_apply_1(v_self_2691_, v_____do__lift_2695_);
v___x_2697_ = lean_apply_2(v_inst_2692_, lean_box(0), v___x_2696_);
v___x_2698_ = lean_apply_4(v_toBind_2693_, lean_box(0), lean_box(0), v___x_2697_, v___f_2694_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg(lean_object* v_inst_2699_, lean_object* v_inst_2700_, lean_object* v_inst_2701_, lean_object* v_self_2702_){
_start:
{
lean_object* v_toApplicative_2703_; lean_object* v_toBind_2704_; lean_object* v_set_2705_; lean_object* v_modifyGet_2706_; lean_object* v_toPure_2707_; lean_object* v___f_2708_; lean_object* v___x_2709_; lean_object* v___f_2710_; lean_object* v___f_2711_; lean_object* v___x_2712_; 
v_toApplicative_2703_ = lean_ctor_get(v_inst_2699_, 0);
lean_inc_ref(v_toApplicative_2703_);
v_toBind_2704_ = lean_ctor_get(v_inst_2699_, 1);
lean_inc_n(v_toBind_2704_, 3);
lean_dec_ref(v_inst_2699_);
v_set_2705_ = lean_ctor_get(v_inst_2700_, 1);
lean_inc(v_set_2705_);
v_modifyGet_2706_ = lean_ctor_get(v_inst_2700_, 2);
lean_inc(v_modifyGet_2706_);
lean_dec_ref(v_inst_2700_);
v_toPure_2707_ = lean_ctor_get(v_toApplicative_2703_, 1);
lean_inc(v_toPure_2707_);
lean_dec_ref(v_toApplicative_2703_);
v___f_2708_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_2709_ = lean_apply_2(v_modifyGet_2706_, lean_box(0), v___f_2708_);
v___f_2710_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2710_, 0, v_toPure_2707_);
lean_closure_set(v___f_2710_, 1, v_set_2705_);
lean_closure_set(v___f_2710_, 2, v_toBind_2704_);
v___f_2711_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2711_, 0, v_self_2702_);
lean_closure_set(v___f_2711_, 1, v_inst_2701_);
lean_closure_set(v___f_2711_, 2, v_toBind_2704_);
lean_closure_set(v___f_2711_, 3, v___f_2710_);
v___x_2712_ = lean_apply_4(v_toBind_2704_, lean_box(0), lean_box(0), v___x_2709_, v___f_2711_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun(lean_object* v_n_2713_, lean_object* v_m_2714_, lean_object* v_00_u03b1_2715_, lean_object* v_inst_2716_, lean_object* v_inst_2717_, lean_object* v_inst_2718_, lean_object* v_inst_2719_, lean_object* v_self_2720_){
_start:
{
lean_object* v_toApplicative_2721_; lean_object* v_toBind_2722_; lean_object* v_set_2723_; lean_object* v_modifyGet_2724_; lean_object* v_toPure_2725_; lean_object* v___f_2726_; lean_object* v___x_2727_; lean_object* v___f_2728_; lean_object* v___f_2729_; lean_object* v___x_2730_; 
v_toApplicative_2721_ = lean_ctor_get(v_inst_2716_, 0);
lean_inc_ref(v_toApplicative_2721_);
v_toBind_2722_ = lean_ctor_get(v_inst_2716_, 1);
lean_inc_n(v_toBind_2722_, 3);
lean_dec_ref(v_inst_2716_);
v_set_2723_ = lean_ctor_get(v_inst_2717_, 1);
lean_inc(v_set_2723_);
v_modifyGet_2724_ = lean_ctor_get(v_inst_2717_, 2);
lean_inc(v_modifyGet_2724_);
lean_dec_ref(v_inst_2717_);
v_toPure_2725_ = lean_ctor_get(v_toApplicative_2721_, 1);
lean_inc(v_toPure_2725_);
lean_dec_ref(v_toApplicative_2721_);
v___f_2726_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_2727_ = lean_apply_2(v_modifyGet_2724_, lean_box(0), v___f_2726_);
v___f_2728_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2728_, 0, v_toPure_2725_);
lean_closure_set(v___f_2728_, 1, v_set_2723_);
lean_closure_set(v___f_2728_, 2, v_toBind_2722_);
v___f_2729_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2729_, 0, v_self_2720_);
lean_closure_set(v___f_2729_, 1, v_inst_2718_);
lean_closure_set(v___f_2729_, 2, v_toBind_2722_);
lean_closure_set(v___f_2729_, 3, v___f_2728_);
v___x_2730_ = lean_apply_4(v_toBind_2722_, lean_box(0), lean_box(0), v___x_2727_, v___f_2729_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___boxed(lean_object* v_n_2731_, lean_object* v_m_2732_, lean_object* v_00_u03b1_2733_, lean_object* v_inst_2734_, lean_object* v_inst_2735_, lean_object* v_inst_2736_, lean_object* v_inst_2737_, lean_object* v_self_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Lake_LogT_takeAndRun(v_n_2731_, v_m_2732_, v_00_u03b1_2733_, v_inst_2734_, v_inst_2735_, v_inst_2736_, v_inst_2737_, v_self_2738_);
lean_dec(v_inst_2737_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg___lam__2(lean_object* v_toPure_2740_, lean_object* v___x_2741_, lean_object* v_toBind_2742_, lean_object* v_inst_2743_, lean_object* v___f_2744_, lean_object* v_____x_2745_){
_start:
{
lean_object* v_fst_2746_; lean_object* v_snd_2747_; lean_object* v___f_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; uint8_t v___x_2751_; 
v_fst_2746_ = lean_ctor_get(v_____x_2745_, 0);
lean_inc(v_fst_2746_);
v_snd_2747_ = lean_ctor_get(v_____x_2745_, 1);
lean_inc(v_snd_2747_);
lean_dec_ref(v_____x_2745_);
lean_inc(v_toPure_2740_);
v___f_2748_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2748_, 0, v_toPure_2740_);
lean_closure_set(v___f_2748_, 1, v_fst_2746_);
v___x_2749_ = lean_array_get_size(v_snd_2747_);
v___x_2750_ = lean_box(0);
v___x_2751_ = lean_nat_dec_lt(v___x_2741_, v___x_2749_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
lean_dec(v_snd_2747_);
lean_dec(v___f_2744_);
lean_dec_ref(v_inst_2743_);
v___x_2752_ = lean_apply_2(v_toPure_2740_, lean_box(0), v___x_2750_);
v___x_2753_ = lean_apply_4(v_toBind_2742_, lean_box(0), lean_box(0), v___x_2752_, v___f_2748_);
return v___x_2753_;
}
else
{
uint8_t v___x_2754_; 
v___x_2754_ = lean_nat_dec_le(v___x_2749_, v___x_2749_);
if (v___x_2754_ == 0)
{
if (v___x_2751_ == 0)
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
lean_dec(v_snd_2747_);
lean_dec(v___f_2744_);
lean_dec_ref(v_inst_2743_);
v___x_2755_ = lean_apply_2(v_toPure_2740_, lean_box(0), v___x_2750_);
v___x_2756_ = lean_apply_4(v_toBind_2742_, lean_box(0), lean_box(0), v___x_2755_, v___f_2748_);
return v___x_2756_;
}
else
{
size_t v___x_2757_; size_t v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
lean_dec(v_toPure_2740_);
v___x_2757_ = ((size_t)0ULL);
v___x_2758_ = lean_usize_of_nat(v___x_2749_);
v___x_2759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2743_, v___f_2744_, v_snd_2747_, v___x_2757_, v___x_2758_, v___x_2750_);
v___x_2760_ = lean_apply_4(v_toBind_2742_, lean_box(0), lean_box(0), v___x_2759_, v___f_2748_);
return v___x_2760_;
}
}
else
{
size_t v___x_2761_; size_t v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
lean_dec(v_toPure_2740_);
v___x_2761_ = ((size_t)0ULL);
v___x_2762_ = lean_usize_of_nat(v___x_2749_);
v___x_2763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2743_, v___f_2744_, v_snd_2747_, v___x_2761_, v___x_2762_, v___x_2750_);
v___x_2764_ = lean_apply_4(v_toBind_2742_, lean_box(0), lean_box(0), v___x_2763_, v___f_2748_);
return v___x_2764_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg___lam__2___boxed(lean_object* v_toPure_2765_, lean_object* v___x_2766_, lean_object* v_toBind_2767_, lean_object* v_inst_2768_, lean_object* v___f_2769_, lean_object* v_____x_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l_Lake_LogT_replayLog___redArg___lam__2(v_toPure_2765_, v___x_2766_, v_toBind_2767_, v_inst_2768_, v___f_2769_, v_____x_2770_);
lean_dec(v___x_2766_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg(lean_object* v_inst_2772_, lean_object* v_logger_2773_, lean_object* v_inst_2774_, lean_object* v_self_2775_){
_start:
{
lean_object* v_toApplicative_2776_; lean_object* v_toBind_2777_; lean_object* v_toPure_2778_; lean_object* v___f_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___f_2784_; lean_object* v___x_2785_; 
v_toApplicative_2776_ = lean_ctor_get(v_inst_2772_, 0);
v_toBind_2777_ = lean_ctor_get(v_inst_2772_, 1);
lean_inc_n(v_toBind_2777_, 2);
v_toPure_2778_ = lean_ctor_get(v_toApplicative_2776_, 1);
lean_inc(v_toPure_2778_);
v___f_2779_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2779_, 0, v_logger_2773_);
v___x_2780_ = lean_unsigned_to_nat(0u);
v___x_2781_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_2782_ = lean_apply_1(v_self_2775_, v___x_2781_);
v___x_2783_ = lean_apply_2(v_inst_2774_, lean_box(0), v___x_2782_);
v___f_2784_ = lean_alloc_closure((void*)(l_Lake_LogT_replayLog___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_2784_, 0, v_toPure_2778_);
lean_closure_set(v___f_2784_, 1, v___x_2780_);
lean_closure_set(v___f_2784_, 2, v_toBind_2777_);
lean_closure_set(v___f_2784_, 3, v_inst_2772_);
lean_closure_set(v___f_2784_, 4, v___f_2779_);
v___x_2785_ = lean_apply_4(v_toBind_2777_, lean_box(0), lean_box(0), v___x_2783_, v___f_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog(lean_object* v_n_2786_, lean_object* v_m_2787_, lean_object* v_00_u03b1_2788_, lean_object* v_inst_2789_, lean_object* v_logger_2790_, lean_object* v_inst_2791_, lean_object* v_self_2792_){
_start:
{
lean_object* v_toApplicative_2793_; lean_object* v_toBind_2794_; lean_object* v_toPure_2795_; lean_object* v___f_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___f_2801_; lean_object* v___x_2802_; 
v_toApplicative_2793_ = lean_ctor_get(v_inst_2789_, 0);
v_toBind_2794_ = lean_ctor_get(v_inst_2789_, 1);
lean_inc_n(v_toBind_2794_, 2);
v_toPure_2795_ = lean_ctor_get(v_toApplicative_2793_, 1);
lean_inc(v_toPure_2795_);
v___f_2796_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2796_, 0, v_logger_2790_);
v___x_2797_ = lean_unsigned_to_nat(0u);
v___x_2798_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_2799_ = lean_apply_1(v_self_2792_, v___x_2798_);
v___x_2800_ = lean_apply_2(v_inst_2791_, lean_box(0), v___x_2799_);
v___f_2801_ = lean_alloc_closure((void*)(l_Lake_LogT_replayLog___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_2801_, 0, v_toPure_2795_);
lean_closure_set(v___f_2801_, 1, v___x_2797_);
lean_closure_set(v___f_2801_, 2, v_toBind_2794_);
lean_closure_set(v___f_2801_, 3, v_inst_2789_);
lean_closure_set(v___f_2801_, 4, v___f_2796_);
v___x_2802_ = lean_apply_4(v_toBind_2794_, lean_box(0), lean_box(0), v___x_2800_, v___f_2801_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogELogTOfMonad___redArg(lean_object* v_inst_2803_){
_start:
{
lean_object* v_toApplicative_2804_; lean_object* v_toPure_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v_toApplicative_2804_ = lean_ctor_get(v_inst_2803_, 0);
lean_inc_ref(v_toApplicative_2804_);
lean_dec_ref(v_inst_2803_);
v_toPure_2805_ = lean_ctor_get(v_toApplicative_2804_, 1);
lean_inc(v_toPure_2805_);
lean_dec_ref(v_toApplicative_2804_);
v___x_2806_ = l_Lake_EStateT_instMonadStateOfOfPure___redArg(v_toPure_2805_);
v___x_2807_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(v___x_2807_, 0, lean_box(0));
lean_closure_set(v___x_2807_, 1, v___x_2806_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogELogTOfMonad(lean_object* v_m_2808_, lean_object* v_inst_2809_){
_start:
{
lean_object* v___x_2810_; 
v___x_2810_ = l_Lake_instMonadLogELogTOfMonad___redArg(v_inst_2809_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__0(lean_object* v_x_2811_){
_start:
{
if (lean_obj_tag(v_x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2821_; 
v_a_2812_ = lean_ctor_get(v_x_2811_, 0);
v_a_2813_ = lean_ctor_get(v_x_2811_, 1);
v_isSharedCheck_2821_ = !lean_is_exclusive(v_x_2811_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2815_ = v_x_2811_;
v_isShared_2816_ = v_isSharedCheck_2821_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_inc(v_a_2812_);
lean_dec(v_x_2811_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2821_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2817_; lean_object* v___x_2819_; 
v___x_2817_ = lean_array_get_size(v_a_2812_);
lean_dec(v_a_2812_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 0, v___x_2817_);
v___x_2819_ = v___x_2815_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v___x_2817_);
lean_ctor_set(v_reuseFailAlloc_2820_, 1, v_a_2813_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
else
{
lean_object* v_a_2822_; lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
v_a_2822_ = lean_ctor_get(v_x_2811_, 0);
v_a_2823_ = lean_ctor_get(v_x_2811_, 1);
v_isSharedCheck_2830_ = !lean_is_exclusive(v_x_2811_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v_x_2811_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_inc(v_a_2822_);
lean_dec(v_x_2811_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2822_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v_a_2823_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__1(lean_object* v_a_2831_, lean_object* v_toPure_2832_, lean_object* v_____do__lift_2833_){
_start:
{
if (lean_obj_tag(v_____do__lift_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2842_; 
v_a_2834_ = lean_ctor_get(v_____do__lift_2833_, 1);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_____do__lift_2833_);
if (v_isSharedCheck_2842_ == 0)
{
lean_object* v_unused_2843_; 
v_unused_2843_ = lean_ctor_get(v_____do__lift_2833_, 0);
lean_dec(v_unused_2843_);
v___x_2836_ = v_____do__lift_2833_;
v_isShared_2837_ = v_isSharedCheck_2842_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v_____do__lift_2833_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2842_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
lean_ctor_set_tag(v___x_2836_, 1);
lean_ctor_set(v___x_2836_, 0, v_a_2831_);
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2831_);
lean_ctor_set(v_reuseFailAlloc_2841_, 1, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
lean_object* v___x_2840_; 
v___x_2840_ = lean_apply_2(v_toPure_2832_, lean_box(0), v___x_2839_);
return v___x_2840_;
}
}
}
else
{
lean_object* v_a_2844_; lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2853_; 
lean_dec(v_a_2831_);
v_a_2844_ = lean_ctor_get(v_____do__lift_2833_, 0);
v_a_2845_ = lean_ctor_get(v_____do__lift_2833_, 1);
v_isSharedCheck_2853_ = !lean_is_exclusive(v_____do__lift_2833_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2847_ = v_____do__lift_2833_;
v_isShared_2848_ = v_isSharedCheck_2853_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_inc(v_a_2844_);
lean_dec(v_____do__lift_2833_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2853_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2844_);
lean_ctor_set(v_reuseFailAlloc_2852_, 1, v_a_2845_);
v___x_2850_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
lean_object* v___x_2851_; 
v___x_2851_ = lean_apply_2(v_toPure_2832_, lean_box(0), v___x_2850_);
return v___x_2851_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__2(lean_object* v_toPure_2854_, lean_object* v___x_2855_, lean_object* v_____do__lift_2856_){
_start:
{
if (lean_obj_tag(v_____do__lift_2856_) == 0)
{
lean_object* v___x_2857_; 
v___x_2857_ = lean_apply_2(v_toPure_2854_, lean_box(0), v_____do__lift_2856_);
return v___x_2857_;
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2866_; 
v_a_2858_ = lean_ctor_get(v_____do__lift_2856_, 1);
v_isSharedCheck_2866_ = !lean_is_exclusive(v_____do__lift_2856_);
if (v_isSharedCheck_2866_ == 0)
{
lean_object* v_unused_2867_; 
v_unused_2867_ = lean_ctor_get(v_____do__lift_2856_, 0);
lean_dec(v_unused_2867_);
v___x_2860_ = v_____do__lift_2856_;
v_isShared_2861_ = v_isSharedCheck_2866_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v_____do__lift_2856_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2866_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
lean_ctor_set_tag(v___x_2860_, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2855_);
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v___x_2855_);
lean_ctor_set(v_reuseFailAlloc_2865_, 1, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
lean_object* v___x_2864_; 
v___x_2864_ = lean_apply_2(v_toPure_2854_, lean_box(0), v___x_2863_);
return v___x_2864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__3(lean_object* v_toPure_2868_, lean_object* v___x_2869_, lean_object* v_toBind_2870_, lean_object* v_____do__lift_2871_){
_start:
{
if (lean_obj_tag(v_____do__lift_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2887_; 
v_a_2872_ = lean_ctor_get(v_____do__lift_2871_, 0);
v_a_2873_ = lean_ctor_get(v_____do__lift_2871_, 1);
v_isSharedCheck_2887_ = !lean_is_exclusive(v_____do__lift_2871_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2875_ = v_____do__lift_2871_;
v_isShared_2876_ = v_isSharedCheck_2887_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_inc(v_a_2872_);
lean_dec(v_____do__lift_2871_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2887_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___f_2877_; lean_object* v___x_2878_; lean_object* v___f_2879_; lean_object* v___x_2880_; lean_object* v___x_2882_; 
lean_inc_n(v_toPure_2868_, 2);
v___f_2877_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2877_, 0, v_a_2872_);
lean_closure_set(v___f_2877_, 1, v_toPure_2868_);
v___x_2878_ = lean_box(0);
v___f_2879_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2879_, 0, v_toPure_2868_);
lean_closure_set(v___f_2879_, 1, v___x_2878_);
v___x_2880_ = lean_array_push(v_a_2873_, v___x_2869_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 1, v___x_2880_);
lean_ctor_set(v___x_2875_, 0, v___x_2878_);
v___x_2882_ = v___x_2875_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2878_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v___x_2880_);
v___x_2882_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2883_ = lean_apply_2(v_toPure_2868_, lean_box(0), v___x_2882_);
lean_inc(v_toBind_2870_);
v___x_2884_ = lean_apply_4(v_toBind_2870_, lean_box(0), lean_box(0), v___x_2883_, v___f_2879_);
v___x_2885_ = lean_apply_4(v_toBind_2870_, lean_box(0), lean_box(0), v___x_2884_, v___f_2877_);
return v___x_2885_;
}
}
}
else
{
lean_object* v_a_2888_; lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2897_; 
lean_dec(v_toBind_2870_);
lean_dec_ref(v___x_2869_);
v_a_2888_ = lean_ctor_get(v_____do__lift_2871_, 0);
v_a_2889_ = lean_ctor_get(v_____do__lift_2871_, 1);
v_isSharedCheck_2897_ = !lean_is_exclusive(v_____do__lift_2871_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2891_ = v_____do__lift_2871_;
v_isShared_2892_ = v_isSharedCheck_2897_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_inc(v_a_2888_);
lean_dec(v_____do__lift_2871_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2897_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2888_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v_a_2889_);
v___x_2894_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
lean_object* v___x_2895_; 
v___x_2895_ = lean_apply_2(v_toPure_2868_, lean_box(0), v___x_2894_);
return v___x_2895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__4(lean_object* v_toFunctor_2898_, lean_object* v_toPure_2899_, lean_object* v_toBind_2900_, lean_object* v___f_2901_, lean_object* v_00_u03b1_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_){
_start:
{
lean_object* v_map_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2918_; 
v_map_2905_ = lean_ctor_get(v_toFunctor_2898_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v_toFunctor_2898_);
if (v_isSharedCheck_2918_ == 0)
{
lean_object* v_unused_2919_; 
v_unused_2919_ = lean_ctor_get(v_toFunctor_2898_, 1);
lean_dec(v_unused_2919_);
v___x_2907_ = v_toFunctor_2898_;
v_isShared_2908_ = v_isSharedCheck_2918_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_map_2905_);
lean_dec(v_toFunctor_2898_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2918_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
uint8_t v___x_2909_; lean_object* v___x_2910_; lean_object* v___f_2911_; lean_object* v___x_2913_; 
v___x_2909_ = 3;
v___x_2910_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2910_, 0, v___y_2903_);
lean_ctor_set_uint8(v___x_2910_, sizeof(void*)*1, v___x_2909_);
lean_inc(v_toBind_2900_);
lean_inc(v_toPure_2899_);
v___f_2911_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__3), 4, 3);
lean_closure_set(v___f_2911_, 0, v_toPure_2899_);
lean_closure_set(v___f_2911_, 1, v___x_2910_);
lean_closure_set(v___f_2911_, 2, v_toBind_2900_);
lean_inc_ref(v___y_2904_);
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 1, v___y_2904_);
lean_ctor_set(v___x_2907_, 0, v___y_2904_);
v___x_2913_ = v___x_2907_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v___y_2904_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v___y_2904_);
v___x_2913_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2914_ = lean_apply_2(v_toPure_2899_, lean_box(0), v___x_2913_);
v___x_2915_ = lean_apply_4(v_map_2905_, lean_box(0), lean_box(0), v___f_2901_, v___x_2914_);
v___x_2916_ = lean_apply_4(v_toBind_2900_, lean_box(0), lean_box(0), v___x_2915_, v___f_2911_);
return v___x_2916_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg(lean_object* v_inst_2921_){
_start:
{
lean_object* v_toApplicative_2922_; lean_object* v_toBind_2923_; lean_object* v_toFunctor_2924_; lean_object* v_toPure_2925_; lean_object* v___f_2926_; lean_object* v___f_2927_; 
v_toApplicative_2922_ = lean_ctor_get(v_inst_2921_, 0);
lean_inc_ref(v_toApplicative_2922_);
v_toBind_2923_ = lean_ctor_get(v_inst_2921_, 1);
lean_inc(v_toBind_2923_);
lean_dec_ref(v_inst_2921_);
v_toFunctor_2924_ = lean_ctor_get(v_toApplicative_2922_, 0);
lean_inc_ref(v_toFunctor_2924_);
v_toPure_2925_ = lean_ctor_get(v_toApplicative_2922_, 1);
lean_inc(v_toPure_2925_);
lean_dec_ref(v_toApplicative_2922_);
v___f_2926_ = ((lean_object*)(l_Lake_instMonadErrorELogTOfMonad___redArg___closed__0));
v___f_2927_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__4), 7, 4);
lean_closure_set(v___f_2927_, 0, v_toFunctor_2924_);
lean_closure_set(v___f_2927_, 1, v_toPure_2925_);
lean_closure_set(v___f_2927_, 2, v_toBind_2923_);
lean_closure_set(v___f_2927_, 3, v___f_2926_);
return v___f_2927_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad(lean_object* v_m_2928_, lean_object* v_inst_2929_){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = l_Lake_instMonadErrorELogTOfMonad___redArg(v_inst_2929_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__1(lean_object* v___y_2931_, lean_object* v___x_2932_, lean_object* v_toPure_2933_, lean_object* v_____do__lift_2934_){
_start:
{
if (lean_obj_tag(v_____do__lift_2934_) == 0)
{
lean_object* v_a_2935_; lean_object* v___x_2936_; 
lean_dec(v_toPure_2933_);
v_a_2935_ = lean_ctor_get(v_____do__lift_2934_, 1);
lean_inc(v_a_2935_);
lean_dec_ref_known(v_____do__lift_2934_, 2);
v___x_2936_ = lean_apply_2(v___y_2931_, v___x_2932_, v_a_2935_);
return v___x_2936_;
}
else
{
lean_object* v_a_2937_; lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2946_; 
lean_dec(v___y_2931_);
v_a_2937_ = lean_ctor_get(v_____do__lift_2934_, 0);
v_a_2938_ = lean_ctor_get(v_____do__lift_2934_, 1);
v_isSharedCheck_2946_ = !lean_is_exclusive(v_____do__lift_2934_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2940_ = v_____do__lift_2934_;
v_isShared_2941_ = v_isSharedCheck_2946_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_inc(v_a_2937_);
lean_dec(v_____do__lift_2934_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2946_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2943_; 
if (v_isShared_2941_ == 0)
{
v___x_2943_ = v___x_2940_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2937_);
lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_a_2938_);
v___x_2943_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
lean_object* v___x_2944_; 
v___x_2944_ = lean_apply_2(v_toPure_2933_, lean_box(0), v___x_2943_);
return v___x_2944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__0(lean_object* v_toPure_2947_, lean_object* v___y_2948_, lean_object* v_toBind_2949_, lean_object* v_____do__lift_2950_){
_start:
{
if (lean_obj_tag(v_____do__lift_2950_) == 0)
{
lean_object* v___x_2951_; 
lean_dec(v_toBind_2949_);
lean_dec(v___y_2948_);
v___x_2951_ = lean_apply_2(v_toPure_2947_, lean_box(0), v_____do__lift_2950_);
return v___x_2951_;
}
else
{
lean_object* v_a_2952_; lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2965_; 
v_a_2952_ = lean_ctor_get(v_____do__lift_2950_, 0);
v_a_2953_ = lean_ctor_get(v_____do__lift_2950_, 1);
v_isSharedCheck_2965_ = !lean_is_exclusive(v_____do__lift_2950_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2955_ = v_____do__lift_2950_;
v_isShared_2956_ = v_isSharedCheck_2965_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_inc(v_a_2952_);
lean_dec(v_____do__lift_2950_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2965_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2957_; lean_object* v___f_2958_; lean_object* v___x_2959_; lean_object* v___x_2961_; 
v___x_2957_ = lean_box(0);
lean_inc(v_toPure_2947_);
v___f_2958_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2958_, 0, v___y_2948_);
lean_closure_set(v___f_2958_, 1, v___x_2957_);
lean_closure_set(v___f_2958_, 2, v_toPure_2947_);
v___x_2959_ = l_Array_shrink___redArg(v_a_2953_, v_a_2952_);
lean_dec(v_a_2952_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set_tag(v___x_2955_, 0);
lean_ctor_set(v___x_2955_, 1, v___x_2959_);
lean_ctor_set(v___x_2955_, 0, v___x_2957_);
v___x_2961_ = v___x_2955_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2957_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v___x_2959_);
v___x_2961_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2962_ = lean_apply_2(v_toPure_2947_, lean_box(0), v___x_2961_);
v___x_2963_ = lean_apply_4(v_toBind_2949_, lean_box(0), lean_box(0), v___x_2962_, v___f_2958_);
return v___x_2963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__2(lean_object* v_toPure_2966_, lean_object* v_toBind_2967_, lean_object* v_00_u03b1_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v___f_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
lean_inc(v_toBind_2967_);
v___f_2972_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2972_, 0, v_toPure_2966_);
lean_closure_set(v___f_2972_, 1, v___y_2970_);
lean_closure_set(v___f_2972_, 2, v_toBind_2967_);
v___x_2973_ = lean_apply_1(v___y_2969_, v___y_2971_);
v___x_2974_ = lean_apply_4(v_toBind_2967_, lean_box(0), lean_box(0), v___x_2973_, v___f_2972_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__3(lean_object* v_toPure_2975_, lean_object* v_____do__lift_2976_){
_start:
{
if (lean_obj_tag(v_____do__lift_2976_) == 0)
{
lean_object* v_a_2977_; lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2986_; 
v_a_2977_ = lean_ctor_get(v_____do__lift_2976_, 0);
v_a_2978_ = lean_ctor_get(v_____do__lift_2976_, 1);
v_isSharedCheck_2986_ = !lean_is_exclusive(v_____do__lift_2976_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2980_ = v_____do__lift_2976_;
v_isShared_2981_ = v_isSharedCheck_2986_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_inc(v_a_2977_);
lean_dec(v_____do__lift_2976_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2986_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
lean_ctor_set_tag(v___x_2980_, 1);
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2977_);
lean_ctor_set(v_reuseFailAlloc_2985_, 1, v_a_2978_);
v___x_2983_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
lean_object* v___x_2984_; 
v___x_2984_ = lean_apply_2(v_toPure_2975_, lean_box(0), v___x_2983_);
return v___x_2984_;
}
}
}
else
{
lean_object* v_a_2987_; lean_object* v_a_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2996_; 
v_a_2987_ = lean_ctor_get(v_____do__lift_2976_, 0);
v_a_2988_ = lean_ctor_get(v_____do__lift_2976_, 1);
v_isSharedCheck_2996_ = !lean_is_exclusive(v_____do__lift_2976_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2990_ = v_____do__lift_2976_;
v_isShared_2991_ = v_isSharedCheck_2996_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_inc(v_a_2987_);
lean_dec(v_____do__lift_2976_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_2996_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2993_; 
if (v_isShared_2991_ == 0)
{
v___x_2993_ = v___x_2990_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2987_);
lean_ctor_set(v_reuseFailAlloc_2995_, 1, v_a_2988_);
v___x_2993_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
lean_object* v___x_2994_; 
v___x_2994_ = lean_apply_2(v_toPure_2975_, lean_box(0), v___x_2993_);
return v___x_2994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__4(lean_object* v_toFunctor_2997_, lean_object* v_toPure_2998_, lean_object* v___f_2999_, lean_object* v_toBind_3000_, lean_object* v___f_3001_, lean_object* v_00_u03b1_3002_, lean_object* v___y_3003_){
_start:
{
lean_object* v_map_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3014_; 
v_map_3004_ = lean_ctor_get(v_toFunctor_2997_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v_toFunctor_2997_);
if (v_isSharedCheck_3014_ == 0)
{
lean_object* v_unused_3015_; 
v_unused_3015_ = lean_ctor_get(v_toFunctor_2997_, 1);
lean_dec(v_unused_3015_);
v___x_3006_ = v_toFunctor_2997_;
v_isShared_3007_ = v_isSharedCheck_3014_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_map_3004_);
lean_dec(v_toFunctor_2997_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3014_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3009_; 
lean_inc_ref(v___y_3003_);
if (v_isShared_3007_ == 0)
{
lean_ctor_set(v___x_3006_, 1, v___y_3003_);
lean_ctor_set(v___x_3006_, 0, v___y_3003_);
v___x_3009_ = v___x_3006_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___y_3003_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v___y_3003_);
v___x_3009_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3010_ = lean_apply_2(v_toPure_2998_, lean_box(0), v___x_3009_);
v___x_3011_ = lean_apply_4(v_map_3004_, lean_box(0), lean_box(0), v___f_2999_, v___x_3010_);
v___x_3012_ = lean_apply_4(v_toBind_3000_, lean_box(0), lean_box(0), v___x_3011_, v___f_3001_);
return v___x_3012_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg(lean_object* v_inst_3016_){
_start:
{
lean_object* v_toApplicative_3017_; lean_object* v_toBind_3018_; lean_object* v_toFunctor_3019_; lean_object* v_toPure_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3038_; 
v_toApplicative_3017_ = lean_ctor_get(v_inst_3016_, 0);
lean_inc_ref(v_toApplicative_3017_);
v_toBind_3018_ = lean_ctor_get(v_inst_3016_, 1);
lean_inc(v_toBind_3018_);
lean_dec_ref(v_inst_3016_);
v_toFunctor_3019_ = lean_ctor_get(v_toApplicative_3017_, 0);
v_toPure_3020_ = lean_ctor_get(v_toApplicative_3017_, 1);
v_isSharedCheck_3038_ = !lean_is_exclusive(v_toApplicative_3017_);
if (v_isSharedCheck_3038_ == 0)
{
lean_object* v_unused_3039_; lean_object* v_unused_3040_; lean_object* v_unused_3041_; 
v_unused_3039_ = lean_ctor_get(v_toApplicative_3017_, 4);
lean_dec(v_unused_3039_);
v_unused_3040_ = lean_ctor_get(v_toApplicative_3017_, 3);
lean_dec(v_unused_3040_);
v_unused_3041_ = lean_ctor_get(v_toApplicative_3017_, 2);
lean_dec(v_unused_3041_);
v___x_3022_ = v_toApplicative_3017_;
v_isShared_3023_ = v_isSharedCheck_3038_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_toPure_3020_);
lean_inc(v_toFunctor_3019_);
lean_dec(v_toApplicative_3017_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3038_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___f_3024_; lean_object* v___f_3025_; lean_object* v___f_3026_; lean_object* v___f_3027_; lean_object* v___f_3028_; lean_object* v___f_3029_; lean_object* v___f_3030_; lean_object* v___f_3031_; lean_object* v___x_3032_; lean_object* v___f_3033_; lean_object* v___x_3035_; 
v___f_3024_ = ((lean_object*)(l_Lake_instMonadErrorELogTOfMonad___redArg___closed__0));
lean_inc_n(v_toBind_3018_, 4);
lean_inc_n(v_toPure_3020_, 7);
v___f_3025_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__2), 6, 2);
lean_closure_set(v___f_3025_, 0, v_toPure_3020_);
lean_closure_set(v___f_3025_, 1, v_toBind_3018_);
v___f_3026_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3026_, 0, v_toPure_3020_);
lean_inc_ref_n(v_toFunctor_3019_, 2);
v___f_3027_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__4), 7, 5);
lean_closure_set(v___f_3027_, 0, v_toFunctor_3019_);
lean_closure_set(v___f_3027_, 1, v_toPure_3020_);
lean_closure_set(v___f_3027_, 2, v___f_3024_);
lean_closure_set(v___f_3027_, 3, v_toBind_3018_);
lean_closure_set(v___f_3027_, 4, v___f_3026_);
v___f_3028_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_3028_, 0, v_toPure_3020_);
lean_closure_set(v___f_3028_, 1, v_toBind_3018_);
v___f_3029_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_3029_, 0, v_toPure_3020_);
lean_closure_set(v___f_3029_, 1, v_toBind_3018_);
v___f_3030_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_3030_, 0, v_toPure_3020_);
lean_closure_set(v___f_3030_, 1, v___f_3028_);
v___f_3031_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_3031_, 0, v_toFunctor_3019_);
lean_closure_set(v___f_3031_, 1, v_toPure_3020_);
lean_closure_set(v___f_3031_, 2, v_toBind_3018_);
v___x_3032_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_3019_);
v___f_3033_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3033_, 0, v_toPure_3020_);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 4, v___f_3029_);
lean_ctor_set(v___x_3022_, 3, v___f_3030_);
lean_ctor_set(v___x_3022_, 2, v___f_3031_);
lean_ctor_set(v___x_3022_, 1, v___f_3033_);
lean_ctor_set(v___x_3022_, 0, v___x_3032_);
v___x_3035_ = v___x_3022_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_3032_);
lean_ctor_set(v_reuseFailAlloc_3037_, 1, v___f_3033_);
lean_ctor_set(v_reuseFailAlloc_3037_, 2, v___f_3031_);
lean_ctor_set(v_reuseFailAlloc_3037_, 3, v___f_3030_);
lean_ctor_set(v_reuseFailAlloc_3037_, 4, v___f_3029_);
v___x_3035_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
lean_object* v___x_3036_; 
v___x_3036_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3035_);
lean_ctor_set(v___x_3036_, 1, v___f_3027_);
lean_ctor_set(v___x_3036_, 2, v___f_3025_);
return v___x_3036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad(lean_object* v_m_3042_, lean_object* v_inst_3043_){
_start:
{
lean_object* v___x_3044_; 
v___x_3044_ = l_Lake_instAlternativeELogTOfMonad___redArg(v_inst_3043_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run___redArg(lean_object* v_self_3045_, lean_object* v_log_3046_){
_start:
{
lean_object* v___x_3047_; 
v___x_3047_ = lean_apply_1(v_self_3045_, v_log_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run(lean_object* v_m_3048_, lean_object* v_00_u03b1_3049_, lean_object* v_self_3050_, lean_object* v_log_3051_){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = lean_apply_1(v_self_3050_, v_log_3051_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x27___redArg(lean_object* v_inst_3054_, lean_object* v_self_3055_, lean_object* v_log_3056_){
_start:
{
lean_object* v_map_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v_map_3057_ = lean_ctor_get(v_inst_3054_, 0);
lean_inc(v_map_3057_);
lean_dec_ref(v_inst_3054_);
v___x_3058_ = ((lean_object*)(l_Lake_ELogT_run_x27___redArg___closed__0));
v___x_3059_ = lean_apply_1(v_self_3055_, v_log_3056_);
v___x_3060_ = lean_apply_4(v_map_3057_, lean_box(0), lean_box(0), v___x_3058_, v___x_3059_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x27(lean_object* v_m_3061_, lean_object* v_00_u03b1_3062_, lean_object* v_inst_3063_, lean_object* v_self_3064_, lean_object* v_log_3065_){
_start:
{
lean_object* v_map_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v_map_3066_ = lean_ctor_get(v_inst_3063_, 0);
lean_inc(v_map_3066_);
lean_dec_ref(v_inst_3063_);
v___x_3067_ = ((lean_object*)(l_Lake_ELogT_run_x27___redArg___closed__0));
v___x_3068_ = lean_apply_1(v_self_3064_, v_log_3065_);
v___x_3069_ = lean_apply_4(v_map_3066_, lean_box(0), lean_box(0), v___x_3067_, v___x_3068_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT___redArg(lean_object* v_inst_3071_, lean_object* v_self_3072_, lean_object* v_a_3073_){
_start:
{
lean_object* v_map_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v_map_3074_ = lean_ctor_get(v_inst_3071_, 0);
lean_inc(v_map_3074_);
lean_dec_ref(v_inst_3071_);
v___x_3075_ = ((lean_object*)(l_Lake_ELogT_toLogT___redArg___closed__0));
v___x_3076_ = lean_apply_1(v_self_3072_, v_a_3073_);
v___x_3077_ = lean_apply_4(v_map_3074_, lean_box(0), lean_box(0), v___x_3075_, v___x_3076_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT(lean_object* v_m_3078_, lean_object* v_00_u03b1_3079_, lean_object* v_inst_3080_, lean_object* v_self_3081_, lean_object* v_a_3082_){
_start:
{
lean_object* v_map_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v_map_3083_ = lean_ctor_get(v_inst_3080_, 0);
lean_inc(v_map_3083_);
lean_dec_ref(v_inst_3080_);
v___x_3084_ = ((lean_object*)(l_Lake_ELogT_toLogT___redArg___closed__0));
v___x_3085_ = lean_apply_1(v_self_3081_, v_a_3082_);
v___x_3086_ = lean_apply_4(v_map_3083_, lean_box(0), lean_box(0), v___x_3084_, v___x_3085_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT_x3f___redArg(lean_object* v_inst_3088_, lean_object* v_self_3089_, lean_object* v_a_3090_){
_start:
{
lean_object* v_map_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v_map_3091_ = lean_ctor_get(v_inst_3088_, 0);
lean_inc(v_map_3091_);
lean_dec_ref(v_inst_3088_);
v___x_3092_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3093_ = lean_apply_1(v_self_3089_, v_a_3090_);
v___x_3094_ = lean_apply_4(v_map_3091_, lean_box(0), lean_box(0), v___x_3092_, v___x_3093_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT_x3f(lean_object* v_m_3095_, lean_object* v_00_u03b1_3096_, lean_object* v_inst_3097_, lean_object* v_self_3098_, lean_object* v_a_3099_){
_start:
{
lean_object* v_map_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v_map_3100_ = lean_ctor_get(v_inst_3097_, 0);
lean_inc(v_map_3100_);
lean_dec_ref(v_inst_3097_);
v___x_3101_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3102_ = lean_apply_1(v_self_3098_, v_a_3099_);
v___x_3103_ = lean_apply_4(v_map_3100_, lean_box(0), lean_box(0), v___x_3101_, v___x_3102_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f___redArg(lean_object* v_inst_3104_, lean_object* v_self_3105_, lean_object* v_log_3106_){
_start:
{
lean_object* v_map_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v_map_3107_ = lean_ctor_get(v_inst_3104_, 0);
lean_inc(v_map_3107_);
lean_dec_ref(v_inst_3104_);
v___x_3108_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3109_ = lean_apply_1(v_self_3105_, v_log_3106_);
v___x_3110_ = lean_apply_4(v_map_3107_, lean_box(0), lean_box(0), v___x_3108_, v___x_3109_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f(lean_object* v_m_3111_, lean_object* v_00_u03b1_3112_, lean_object* v_inst_3113_, lean_object* v_self_3114_, lean_object* v_log_3115_){
_start:
{
lean_object* v_map_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v_map_3116_ = lean_ctor_get(v_inst_3113_, 0);
lean_inc(v_map_3116_);
lean_dec_ref(v_inst_3113_);
v___x_3117_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3118_ = lean_apply_1(v_self_3114_, v_log_3115_);
v___x_3119_ = lean_apply_4(v_map_3116_, lean_box(0), lean_box(0), v___x_3117_, v___x_3118_);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f_x27___redArg(lean_object* v_inst_3121_, lean_object* v_self_3122_, lean_object* v_log_3123_){
_start:
{
lean_object* v_map_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v_map_3124_ = lean_ctor_get(v_inst_3121_, 0);
lean_inc(v_map_3124_);
lean_dec_ref(v_inst_3121_);
v___x_3125_ = ((lean_object*)(l_Lake_ELogT_run_x3f_x27___redArg___closed__0));
v___x_3126_ = lean_apply_1(v_self_3122_, v_log_3123_);
v___x_3127_ = lean_apply_4(v_map_3124_, lean_box(0), lean_box(0), v___x_3125_, v___x_3126_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f_x27(lean_object* v_m_3128_, lean_object* v_00_u03b1_3129_, lean_object* v_inst_3130_, lean_object* v_self_3131_, lean_object* v_log_3132_){
_start:
{
lean_object* v_map_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
v_map_3133_ = lean_ctor_get(v_inst_3130_, 0);
lean_inc(v_map_3133_);
lean_dec_ref(v_inst_3130_);
v___x_3134_ = ((lean_object*)(l_Lake_ELogT_run_x3f_x27___redArg___closed__0));
v___x_3135_ = lean_apply_1(v_self_3131_, v_log_3132_);
v___x_3136_ = lean_apply_4(v_map_3133_, lean_box(0), lean_box(0), v___x_3134_, v___x_3135_);
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg___lam__0(lean_object* v_f_3137_, lean_object* v_____x_3138_){
_start:
{
lean_object* v_fst_3139_; lean_object* v_snd_3140_; lean_object* v___x_3141_; 
v_fst_3139_ = lean_ctor_get(v_____x_3138_, 0);
lean_inc(v_fst_3139_);
v_snd_3140_ = lean_ctor_get(v_____x_3138_, 1);
lean_inc(v_snd_3140_);
lean_dec_ref(v_____x_3138_);
v___x_3141_ = lean_apply_2(v_f_3137_, v_fst_3139_, v_snd_3140_);
return v___x_3141_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg___lam__1(lean_object* v_toPure_3142_, lean_object* v_toBind_3143_, lean_object* v___f_3144_, lean_object* v_____do__lift_3145_){
_start:
{
if (lean_obj_tag(v_____do__lift_3145_) == 0)
{
lean_object* v_a_3146_; lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3155_; 
lean_dec(v___f_3144_);
lean_dec(v_toBind_3143_);
v_a_3146_ = lean_ctor_get(v_____do__lift_3145_, 0);
v_a_3147_ = lean_ctor_get(v_____do__lift_3145_, 1);
v_isSharedCheck_3155_ = !lean_is_exclusive(v_____do__lift_3145_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3149_ = v_____do__lift_3145_;
v_isShared_3150_ = v_isSharedCheck_3155_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_inc(v_a_3146_);
lean_dec(v_____do__lift_3145_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3155_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3150_ == 0)
{
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3146_);
lean_ctor_set(v_reuseFailAlloc_3154_, 1, v_a_3147_);
v___x_3152_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
lean_object* v___x_3153_; 
v___x_3153_ = lean_apply_2(v_toPure_3142_, lean_box(0), v___x_3152_);
return v___x_3153_;
}
}
}
else
{
lean_object* v_a_3156_; lean_object* v_a_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3169_; 
v_a_3156_ = lean_ctor_get(v_____do__lift_3145_, 0);
v_a_3157_ = lean_ctor_get(v_____do__lift_3145_, 1);
v_isSharedCheck_3169_ = !lean_is_exclusive(v_____do__lift_3145_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3159_ = v_____do__lift_3145_;
v_isShared_3160_ = v_isSharedCheck_3169_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_a_3157_);
lean_inc(v_a_3156_);
lean_dec(v_____do__lift_3145_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3169_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3165_; 
v___x_3161_ = lean_array_get_size(v_a_3157_);
lean_inc(v_a_3156_);
v___x_3162_ = l_Array_extract___redArg(v_a_3157_, v_a_3156_, v___x_3161_);
v___x_3163_ = l_Array_shrink___redArg(v_a_3157_, v_a_3156_);
lean_dec(v_a_3156_);
if (v_isShared_3160_ == 0)
{
lean_ctor_set_tag(v___x_3159_, 0);
lean_ctor_set(v___x_3159_, 1, v___x_3163_);
lean_ctor_set(v___x_3159_, 0, v___x_3162_);
v___x_3165_ = v___x_3159_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v___x_3162_);
lean_ctor_set(v_reuseFailAlloc_3168_, 1, v___x_3163_);
v___x_3165_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3166_ = lean_apply_2(v_toPure_3142_, lean_box(0), v___x_3165_);
v___x_3167_ = lean_apply_4(v_toBind_3143_, lean_box(0), lean_box(0), v___x_3166_, v___f_3144_);
return v___x_3167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg(lean_object* v_inst_3170_, lean_object* v_f_3171_, lean_object* v_self_3172_, lean_object* v_a_3173_){
_start:
{
lean_object* v_toApplicative_3174_; lean_object* v_toBind_3175_; lean_object* v_toPure_3176_; lean_object* v___f_3177_; lean_object* v___x_3178_; lean_object* v___f_3179_; lean_object* v___x_3180_; 
v_toApplicative_3174_ = lean_ctor_get(v_inst_3170_, 0);
lean_inc_ref(v_toApplicative_3174_);
v_toBind_3175_ = lean_ctor_get(v_inst_3170_, 1);
lean_inc_n(v_toBind_3175_, 2);
lean_dec_ref(v_inst_3170_);
v_toPure_3176_ = lean_ctor_get(v_toApplicative_3174_, 1);
lean_inc(v_toPure_3176_);
lean_dec_ref(v_toApplicative_3174_);
v___f_3177_ = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3177_, 0, v_f_3171_);
v___x_3178_ = lean_apply_1(v_self_3172_, v_a_3173_);
v___f_3179_ = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3179_, 0, v_toPure_3176_);
lean_closure_set(v___f_3179_, 1, v_toBind_3175_);
lean_closure_set(v___f_3179_, 2, v___f_3177_);
v___x_3180_ = lean_apply_4(v_toBind_3175_, lean_box(0), lean_box(0), v___x_3178_, v___f_3179_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog(lean_object* v_m_3181_, lean_object* v_00_u03b1_3182_, lean_object* v_inst_3183_, lean_object* v_f_3184_, lean_object* v_self_3185_, lean_object* v_a_3186_){
_start:
{
lean_object* v_toApplicative_3187_; lean_object* v_toBind_3188_; lean_object* v_toPure_3189_; lean_object* v___f_3190_; lean_object* v___x_3191_; lean_object* v___f_3192_; lean_object* v___x_3193_; 
v_toApplicative_3187_ = lean_ctor_get(v_inst_3183_, 0);
lean_inc_ref(v_toApplicative_3187_);
v_toBind_3188_ = lean_ctor_get(v_inst_3183_, 1);
lean_inc_n(v_toBind_3188_, 2);
lean_dec_ref(v_inst_3183_);
v_toPure_3189_ = lean_ctor_get(v_toApplicative_3187_, 1);
lean_inc(v_toPure_3189_);
lean_dec_ref(v_toApplicative_3187_);
v___f_3190_ = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3190_, 0, v_f_3184_);
v___x_3191_ = lean_apply_1(v_self_3185_, v_a_3186_);
v___f_3192_ = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3192_, 0, v_toPure_3189_);
lean_closure_set(v___f_3192_, 1, v_toBind_3188_);
lean_closure_set(v___f_3192_, 2, v___f_3190_);
v___x_3193_ = lean_apply_4(v_toBind_3188_, lean_box(0), lean_box(0), v___x_3191_, v___f_3192_);
return v___x_3193_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__1(lean_object* v_toPure_3194_, lean_object* v_a_3195_, lean_object* v_____r_3196_){
_start:
{
lean_object* v___x_3197_; 
v___x_3197_ = lean_apply_2(v_toPure_3194_, lean_box(0), v_a_3195_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__0(lean_object* v_inst_3198_, lean_object* v_a_3199_, lean_object* v_____r_3200_){
_start:
{
lean_object* v_throw_3201_; lean_object* v___x_3202_; 
v_throw_3201_ = lean_ctor_get(v_inst_3198_, 0);
lean_inc(v_throw_3201_);
lean_dec_ref(v_inst_3198_);
v___x_3202_ = lean_apply_2(v_throw_3201_, lean_box(0), v_a_3199_);
return v___x_3202_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__2(lean_object* v_toPure_3203_, lean_object* v_set_3204_, lean_object* v_toBind_3205_, lean_object* v_inst_3206_, lean_object* v_____do__lift_3207_){
_start:
{
if (lean_obj_tag(v_____do__lift_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v_a_3209_; lean_object* v___f_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
lean_dec_ref(v_inst_3206_);
v_a_3208_ = lean_ctor_get(v_____do__lift_3207_, 0);
lean_inc(v_a_3208_);
v_a_3209_ = lean_ctor_get(v_____do__lift_3207_, 1);
lean_inc(v_a_3209_);
lean_dec_ref_known(v_____do__lift_3207_, 2);
v___f_3210_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3210_, 0, v_toPure_3203_);
lean_closure_set(v___f_3210_, 1, v_a_3208_);
v___x_3211_ = lean_apply_1(v_set_3204_, v_a_3209_);
v___x_3212_ = lean_apply_4(v_toBind_3205_, lean_box(0), lean_box(0), v___x_3211_, v___f_3210_);
return v___x_3212_;
}
else
{
lean_object* v_a_3213_; lean_object* v_a_3214_; lean_object* v___f_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
lean_dec(v_toPure_3203_);
v_a_3213_ = lean_ctor_get(v_____do__lift_3207_, 0);
lean_inc(v_a_3213_);
v_a_3214_ = lean_ctor_get(v_____do__lift_3207_, 1);
lean_inc(v_a_3214_);
lean_dec_ref_known(v_____do__lift_3207_, 2);
v___f_3215_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3215_, 0, v_inst_3206_);
lean_closure_set(v___f_3215_, 1, v_a_3213_);
v___x_3216_ = lean_apply_1(v_set_3204_, v_a_3214_);
v___x_3217_ = lean_apply_4(v_toBind_3205_, lean_box(0), lean_box(0), v___x_3216_, v___f_3215_);
return v___x_3217_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__3(lean_object* v_self_3218_, lean_object* v_inst_3219_, lean_object* v_toBind_3220_, lean_object* v___f_3221_, lean_object* v_____do__lift_3222_){
_start:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3223_ = lean_apply_1(v_self_3218_, v_____do__lift_3222_);
v___x_3224_ = lean_apply_2(v_inst_3219_, lean_box(0), v___x_3223_);
v___x_3225_ = lean_apply_4(v_toBind_3220_, lean_box(0), lean_box(0), v___x_3224_, v___f_3221_);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg(lean_object* v_inst_3226_, lean_object* v_inst_3227_, lean_object* v_inst_3228_, lean_object* v_inst_3229_, lean_object* v_self_3230_){
_start:
{
lean_object* v_toApplicative_3231_; lean_object* v_toBind_3232_; lean_object* v_set_3233_; lean_object* v_modifyGet_3234_; lean_object* v_toPure_3235_; lean_object* v___f_3236_; lean_object* v___x_3237_; lean_object* v___f_3238_; lean_object* v___f_3239_; lean_object* v___x_3240_; 
v_toApplicative_3231_ = lean_ctor_get(v_inst_3226_, 0);
lean_inc_ref(v_toApplicative_3231_);
v_toBind_3232_ = lean_ctor_get(v_inst_3226_, 1);
lean_inc_n(v_toBind_3232_, 3);
lean_dec_ref(v_inst_3226_);
v_set_3233_ = lean_ctor_get(v_inst_3227_, 1);
lean_inc(v_set_3233_);
v_modifyGet_3234_ = lean_ctor_get(v_inst_3227_, 2);
lean_inc(v_modifyGet_3234_);
lean_dec_ref(v_inst_3227_);
v_toPure_3235_ = lean_ctor_get(v_toApplicative_3231_, 1);
lean_inc(v_toPure_3235_);
lean_dec_ref(v_toApplicative_3231_);
v___f_3236_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_3237_ = lean_apply_2(v_modifyGet_3234_, lean_box(0), v___f_3236_);
v___f_3238_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3238_, 0, v_toPure_3235_);
lean_closure_set(v___f_3238_, 1, v_set_3233_);
lean_closure_set(v___f_3238_, 2, v_toBind_3232_);
lean_closure_set(v___f_3238_, 3, v_inst_3228_);
v___f_3239_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3239_, 0, v_self_3230_);
lean_closure_set(v___f_3239_, 1, v_inst_3229_);
lean_closure_set(v___f_3239_, 2, v_toBind_3232_);
lean_closure_set(v___f_3239_, 3, v___f_3238_);
v___x_3240_ = lean_apply_4(v_toBind_3232_, lean_box(0), lean_box(0), v___x_3237_, v___f_3239_);
return v___x_3240_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun(lean_object* v_n_3241_, lean_object* v_m_3242_, lean_object* v_00_u03b1_3243_, lean_object* v_inst_3244_, lean_object* v_inst_3245_, lean_object* v_inst_3246_, lean_object* v_inst_3247_, lean_object* v_self_3248_){
_start:
{
lean_object* v_toApplicative_3249_; lean_object* v_toBind_3250_; lean_object* v_set_3251_; lean_object* v_modifyGet_3252_; lean_object* v_toPure_3253_; lean_object* v___f_3254_; lean_object* v___x_3255_; lean_object* v___f_3256_; lean_object* v___f_3257_; lean_object* v___x_3258_; 
v_toApplicative_3249_ = lean_ctor_get(v_inst_3244_, 0);
lean_inc_ref(v_toApplicative_3249_);
v_toBind_3250_ = lean_ctor_get(v_inst_3244_, 1);
lean_inc_n(v_toBind_3250_, 3);
lean_dec_ref(v_inst_3244_);
v_set_3251_ = lean_ctor_get(v_inst_3245_, 1);
lean_inc(v_set_3251_);
v_modifyGet_3252_ = lean_ctor_get(v_inst_3245_, 2);
lean_inc(v_modifyGet_3252_);
lean_dec_ref(v_inst_3245_);
v_toPure_3253_ = lean_ctor_get(v_toApplicative_3249_, 1);
lean_inc(v_toPure_3253_);
lean_dec_ref(v_toApplicative_3249_);
v___f_3254_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_3255_ = lean_apply_2(v_modifyGet_3252_, lean_box(0), v___f_3254_);
v___f_3256_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3256_, 0, v_toPure_3253_);
lean_closure_set(v___f_3256_, 1, v_set_3251_);
lean_closure_set(v___f_3256_, 2, v_toBind_3250_);
lean_closure_set(v___f_3256_, 3, v_inst_3246_);
v___f_3257_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3257_, 0, v_self_3248_);
lean_closure_set(v___f_3257_, 1, v_inst_3247_);
lean_closure_set(v___f_3257_, 2, v_toBind_3250_);
lean_closure_set(v___f_3257_, 3, v___f_3256_);
v___x_3258_ = lean_apply_4(v_toBind_3250_, lean_box(0), lean_box(0), v___x_3255_, v___f_3257_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__2(lean_object* v_toPure_3259_, lean_object* v_x_3260_){
_start:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3261_ = lean_box(0);
v___x_3262_ = lean_apply_2(v_toPure_3259_, lean_box(0), v___x_3261_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__0(lean_object* v_a_3263_, lean_object* v_toPure_3264_, lean_object* v_x_3265_){
_start:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3266_, 0, v_a_3263_);
v___x_3267_ = lean_apply_2(v_toPure_3264_, lean_box(0), v___x_3266_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__1(lean_object* v_toPure_3268_, lean_object* v___x_3269_, lean_object* v_toSeqRight_3270_, lean_object* v_inst_3271_, lean_object* v___f_3272_, lean_object* v___f_3273_, lean_object* v___f_3274_, lean_object* v_____do__lift_3275_){
_start:
{
if (lean_obj_tag(v_____do__lift_3275_) == 0)
{
lean_object* v_a_3276_; lean_object* v_a_3277_; lean_object* v___f_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; uint8_t v___x_3281_; 
lean_dec(v___f_3274_);
lean_dec(v___f_3273_);
v_a_3276_ = lean_ctor_get(v_____do__lift_3275_, 0);
lean_inc(v_a_3276_);
v_a_3277_ = lean_ctor_get(v_____do__lift_3275_, 1);
lean_inc(v_a_3277_);
lean_dec_ref_known(v_____do__lift_3275_, 2);
lean_inc(v_toPure_3268_);
v___f_3278_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3278_, 0, v_a_3276_);
lean_closure_set(v___f_3278_, 1, v_toPure_3268_);
v___x_3279_ = lean_array_get_size(v_a_3277_);
v___x_3280_ = lean_box(0);
v___x_3281_ = lean_nat_dec_lt(v___x_3269_, v___x_3279_);
if (v___x_3281_ == 0)
{
lean_object* v___x_3282_; lean_object* v___x_3283_; 
lean_dec(v_a_3277_);
lean_dec(v___f_3272_);
lean_dec_ref(v_inst_3271_);
v___x_3282_ = lean_apply_2(v_toPure_3268_, lean_box(0), v___x_3280_);
v___x_3283_ = lean_apply_4(v_toSeqRight_3270_, lean_box(0), lean_box(0), v___x_3282_, v___f_3278_);
return v___x_3283_;
}
else
{
uint8_t v___x_3284_; 
v___x_3284_ = lean_nat_dec_le(v___x_3279_, v___x_3279_);
if (v___x_3284_ == 0)
{
if (v___x_3281_ == 0)
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
lean_dec(v_a_3277_);
lean_dec(v___f_3272_);
lean_dec_ref(v_inst_3271_);
v___x_3285_ = lean_apply_2(v_toPure_3268_, lean_box(0), v___x_3280_);
v___x_3286_ = lean_apply_4(v_toSeqRight_3270_, lean_box(0), lean_box(0), v___x_3285_, v___f_3278_);
return v___x_3286_;
}
else
{
size_t v___x_3287_; size_t v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
lean_dec(v_toPure_3268_);
v___x_3287_ = ((size_t)0ULL);
v___x_3288_ = lean_usize_of_nat(v___x_3279_);
v___x_3289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3271_, v___f_3272_, v_a_3277_, v___x_3287_, v___x_3288_, v___x_3280_);
v___x_3290_ = lean_apply_4(v_toSeqRight_3270_, lean_box(0), lean_box(0), v___x_3289_, v___f_3278_);
return v___x_3290_;
}
}
else
{
size_t v___x_3291_; size_t v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
lean_dec(v_toPure_3268_);
v___x_3291_ = ((size_t)0ULL);
v___x_3292_ = lean_usize_of_nat(v___x_3279_);
v___x_3293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3271_, v___f_3272_, v_a_3277_, v___x_3291_, v___x_3292_, v___x_3280_);
v___x_3294_ = lean_apply_4(v_toSeqRight_3270_, lean_box(0), lean_box(0), v___x_3293_, v___f_3278_);
return v___x_3294_;
}
}
}
else
{
lean_object* v_a_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; uint8_t v___x_3298_; 
lean_dec(v___f_3272_);
v_a_3295_ = lean_ctor_get(v_____do__lift_3275_, 1);
lean_inc(v_a_3295_);
lean_dec_ref_known(v_____do__lift_3275_, 2);
v___x_3296_ = lean_array_get_size(v_a_3295_);
v___x_3297_ = lean_box(0);
v___x_3298_ = lean_nat_dec_lt(v___x_3269_, v___x_3296_);
if (v___x_3298_ == 0)
{
lean_object* v___x_3299_; lean_object* v___x_3300_; 
lean_dec(v_a_3295_);
lean_dec(v___f_3274_);
lean_dec_ref(v_inst_3271_);
v___x_3299_ = lean_apply_2(v_toPure_3268_, lean_box(0), v___x_3297_);
v___x_3300_ = lean_apply_4(v_toSeqRight_3270_, lean_box(0), lean_box(0), v___x_3299_, v___f_3273_);
return v___x_3300_;
}
else
{
uint8_t v___x_3301_; 
v___x_3301_ = lean_nat_dec_le(v___x_3296_, v___x_3296_);
if (v___x_3301_ == 0)
{
if (v___x_3298_ == 0)
{
lean_object* v___x_3302_; lean_object* v___x_3303_; 
lean_dec(v_a_3295_);
lean_dec(v___f_3274_);
lean_dec_ref(v_inst_3271_);
v___x_3302_ = lean_apply_2(v_toPure_3268_, lean_box(0), v___x_3297_);
v___x_3303_ = lean_apply_4(v_toSeqRight_3270_, lean_box(0), lean_box(0), v___x_3302_, v___f_3273_);
return v___x_3303_;
}
else
{
size_t v___x_3304_; size_t v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
lean_dec(v_toPure_3268_);
v___x_3304_ = ((size_t)0ULL);
v___x_3305_ = lean_usize_of_nat(v___x_3296_);
v___x_3306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3271_, v___f_3274_, v_a_3295_, v___x_3304_, v___x_3305_, v___x_3297_);
v___x_3307_ = lean_apply_4(v_toSeqRight_3270_, lean_box(0), lean_box(0), v___x_3306_, v___f_3273_);
return v___x_3307_;
}
}
else
{
size_t v___x_3308_; size_t v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
lean_dec(v_toPure_3268_);
v___x_3308_ = ((size_t)0ULL);
v___x_3309_ = lean_usize_of_nat(v___x_3296_);
v___x_3310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3271_, v___f_3274_, v_a_3295_, v___x_3308_, v___x_3309_, v___x_3297_);
v___x_3311_ = lean_apply_4(v_toSeqRight_3270_, lean_box(0), lean_box(0), v___x_3310_, v___f_3273_);
return v___x_3311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed(lean_object* v_toPure_3312_, lean_object* v___x_3313_, lean_object* v_toSeqRight_3314_, lean_object* v_inst_3315_, lean_object* v___f_3316_, lean_object* v___f_3317_, lean_object* v___f_3318_, lean_object* v_____do__lift_3319_){
_start:
{
lean_object* v_res_3320_; 
v_res_3320_ = l_Lake_ELogT_replayLog_x3f___redArg___lam__1(v_toPure_3312_, v___x_3313_, v_toSeqRight_3314_, v_inst_3315_, v___f_3316_, v___f_3317_, v___f_3318_, v_____do__lift_3319_);
lean_dec(v___x_3313_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg(lean_object* v_inst_3321_, lean_object* v_logger_3322_, lean_object* v_inst_3323_, lean_object* v_self_3324_){
_start:
{
lean_object* v_toApplicative_3325_; lean_object* v_toBind_3326_; lean_object* v_toPure_3327_; lean_object* v_toSeqRight_3328_; lean_object* v___f_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___f_3334_; lean_object* v___f_3335_; lean_object* v___x_3336_; 
v_toApplicative_3325_ = lean_ctor_get(v_inst_3321_, 0);
v_toBind_3326_ = lean_ctor_get(v_inst_3321_, 1);
lean_inc(v_toBind_3326_);
v_toPure_3327_ = lean_ctor_get(v_toApplicative_3325_, 1);
lean_inc_n(v_toPure_3327_, 2);
v_toSeqRight_3328_ = lean_ctor_get(v_toApplicative_3325_, 4);
lean_inc(v_toSeqRight_3328_);
v___f_3329_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3329_, 0, v_logger_3322_);
v___x_3330_ = lean_unsigned_to_nat(0u);
v___x_3331_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3332_ = lean_apply_1(v_self_3324_, v___x_3331_);
v___x_3333_ = lean_apply_2(v_inst_3323_, lean_box(0), v___x_3332_);
v___f_3334_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3334_, 0, v_toPure_3327_);
lean_inc_ref(v___f_3329_);
v___f_3335_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_3335_, 0, v_toPure_3327_);
lean_closure_set(v___f_3335_, 1, v___x_3330_);
lean_closure_set(v___f_3335_, 2, v_toSeqRight_3328_);
lean_closure_set(v___f_3335_, 3, v_inst_3321_);
lean_closure_set(v___f_3335_, 4, v___f_3329_);
lean_closure_set(v___f_3335_, 5, v___f_3334_);
lean_closure_set(v___f_3335_, 6, v___f_3329_);
v___x_3336_ = lean_apply_4(v_toBind_3326_, lean_box(0), lean_box(0), v___x_3333_, v___f_3335_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f(lean_object* v_n_3337_, lean_object* v_m_3338_, lean_object* v_00_u03b1_3339_, lean_object* v_inst_3340_, lean_object* v_logger_3341_, lean_object* v_inst_3342_, lean_object* v_self_3343_){
_start:
{
lean_object* v_toApplicative_3344_; lean_object* v_toBind_3345_; lean_object* v_toPure_3346_; lean_object* v_toSeqRight_3347_; lean_object* v___f_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___f_3353_; lean_object* v___f_3354_; lean_object* v___x_3355_; 
v_toApplicative_3344_ = lean_ctor_get(v_inst_3340_, 0);
v_toBind_3345_ = lean_ctor_get(v_inst_3340_, 1);
lean_inc(v_toBind_3345_);
v_toPure_3346_ = lean_ctor_get(v_toApplicative_3344_, 1);
lean_inc_n(v_toPure_3346_, 2);
v_toSeqRight_3347_ = lean_ctor_get(v_toApplicative_3344_, 4);
lean_inc(v_toSeqRight_3347_);
v___f_3348_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3348_, 0, v_logger_3341_);
v___x_3349_ = lean_unsigned_to_nat(0u);
v___x_3350_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3351_ = lean_apply_1(v_self_3343_, v___x_3350_);
v___x_3352_ = lean_apply_2(v_inst_3342_, lean_box(0), v___x_3351_);
v___f_3353_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3353_, 0, v_toPure_3346_);
lean_inc_ref(v___f_3348_);
v___f_3354_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_3354_, 0, v_toPure_3346_);
lean_closure_set(v___f_3354_, 1, v___x_3349_);
lean_closure_set(v___f_3354_, 2, v_toSeqRight_3347_);
lean_closure_set(v___f_3354_, 3, v_inst_3340_);
lean_closure_set(v___f_3354_, 4, v___f_3348_);
lean_closure_set(v___f_3354_, 5, v___f_3353_);
lean_closure_set(v___f_3354_, 6, v___f_3348_);
v___x_3355_ = lean_apply_4(v_toBind_3345_, lean_box(0), lean_box(0), v___x_3352_, v___f_3354_);
return v___x_3355_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg___lam__3(lean_object* v_toPure_3356_, lean_object* v_a_3357_, lean_object* v_x_3358_){
_start:
{
lean_object* v___x_3359_; 
v___x_3359_ = lean_apply_2(v_toPure_3356_, lean_box(0), v_a_3357_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg___lam__0(lean_object* v_toPure_3360_, lean_object* v___x_3361_, lean_object* v_toApplicative_3362_, lean_object* v_toSeqRight_3363_, lean_object* v_inst_3364_, lean_object* v___f_3365_, lean_object* v___f_3366_, lean_object* v___f_3367_, lean_object* v_____do__lift_3368_){
_start:
{
if (lean_obj_tag(v_____do__lift_3368_) == 0)
{
lean_object* v_a_3369_; lean_object* v_a_3370_; lean_object* v___f_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; uint8_t v___x_3374_; 
lean_dec(v___f_3367_);
lean_dec(v___f_3366_);
v_a_3369_ = lean_ctor_get(v_____do__lift_3368_, 0);
lean_inc(v_a_3369_);
v_a_3370_ = lean_ctor_get(v_____do__lift_3368_, 1);
lean_inc(v_a_3370_);
lean_dec_ref_known(v_____do__lift_3368_, 2);
v___f_3371_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog___redArg___lam__3), 3, 2);
lean_closure_set(v___f_3371_, 0, v_toPure_3360_);
lean_closure_set(v___f_3371_, 1, v_a_3369_);
v___x_3372_ = lean_array_get_size(v_a_3370_);
v___x_3373_ = lean_box(0);
v___x_3374_ = lean_nat_dec_lt(v___x_3361_, v___x_3372_);
if (v___x_3374_ == 0)
{
lean_object* v_toPure_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
lean_dec(v_a_3370_);
lean_dec(v___f_3365_);
lean_dec_ref(v_inst_3364_);
v_toPure_3375_ = lean_ctor_get(v_toApplicative_3362_, 1);
lean_inc(v_toPure_3375_);
lean_dec_ref(v_toApplicative_3362_);
v___x_3376_ = lean_apply_2(v_toPure_3375_, lean_box(0), v___x_3373_);
v___x_3377_ = lean_apply_4(v_toSeqRight_3363_, lean_box(0), lean_box(0), v___x_3376_, v___f_3371_);
return v___x_3377_;
}
else
{
uint8_t v___x_3378_; 
v___x_3378_ = lean_nat_dec_le(v___x_3372_, v___x_3372_);
if (v___x_3378_ == 0)
{
if (v___x_3374_ == 0)
{
lean_object* v_toPure_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
lean_dec(v_a_3370_);
lean_dec(v___f_3365_);
lean_dec_ref(v_inst_3364_);
v_toPure_3379_ = lean_ctor_get(v_toApplicative_3362_, 1);
lean_inc(v_toPure_3379_);
lean_dec_ref(v_toApplicative_3362_);
v___x_3380_ = lean_apply_2(v_toPure_3379_, lean_box(0), v___x_3373_);
v___x_3381_ = lean_apply_4(v_toSeqRight_3363_, lean_box(0), lean_box(0), v___x_3380_, v___f_3371_);
return v___x_3381_;
}
else
{
size_t v___x_3382_; size_t v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
lean_dec_ref(v_toApplicative_3362_);
v___x_3382_ = ((size_t)0ULL);
v___x_3383_ = lean_usize_of_nat(v___x_3372_);
v___x_3384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3364_, v___f_3365_, v_a_3370_, v___x_3382_, v___x_3383_, v___x_3373_);
v___x_3385_ = lean_apply_4(v_toSeqRight_3363_, lean_box(0), lean_box(0), v___x_3384_, v___f_3371_);
return v___x_3385_;
}
}
else
{
size_t v___x_3386_; size_t v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
lean_dec_ref(v_toApplicative_3362_);
v___x_3386_ = ((size_t)0ULL);
v___x_3387_ = lean_usize_of_nat(v___x_3372_);
v___x_3388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3364_, v___f_3365_, v_a_3370_, v___x_3386_, v___x_3387_, v___x_3373_);
v___x_3389_ = lean_apply_4(v_toSeqRight_3363_, lean_box(0), lean_box(0), v___x_3388_, v___f_3371_);
return v___x_3389_;
}
}
}
else
{
lean_object* v_a_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; uint8_t v___x_3393_; 
lean_dec(v___f_3365_);
lean_dec(v_toPure_3360_);
v_a_3390_ = lean_ctor_get(v_____do__lift_3368_, 1);
lean_inc(v_a_3390_);
lean_dec_ref_known(v_____do__lift_3368_, 2);
v___x_3391_ = lean_array_get_size(v_a_3390_);
v___x_3392_ = lean_box(0);
v___x_3393_ = lean_nat_dec_lt(v___x_3361_, v___x_3391_);
if (v___x_3393_ == 0)
{
lean_object* v_toPure_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
lean_dec(v_a_3390_);
lean_dec(v___f_3367_);
lean_dec_ref(v_inst_3364_);
v_toPure_3394_ = lean_ctor_get(v_toApplicative_3362_, 1);
lean_inc(v_toPure_3394_);
lean_dec_ref(v_toApplicative_3362_);
v___x_3395_ = lean_apply_2(v_toPure_3394_, lean_box(0), v___x_3392_);
v___x_3396_ = lean_apply_4(v_toSeqRight_3363_, lean_box(0), lean_box(0), v___x_3395_, v___f_3366_);
return v___x_3396_;
}
else
{
uint8_t v___x_3397_; 
v___x_3397_ = lean_nat_dec_le(v___x_3391_, v___x_3391_);
if (v___x_3397_ == 0)
{
if (v___x_3393_ == 0)
{
lean_object* v_toPure_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
lean_dec(v_a_3390_);
lean_dec(v___f_3367_);
lean_dec_ref(v_inst_3364_);
v_toPure_3398_ = lean_ctor_get(v_toApplicative_3362_, 1);
lean_inc(v_toPure_3398_);
lean_dec_ref(v_toApplicative_3362_);
v___x_3399_ = lean_apply_2(v_toPure_3398_, lean_box(0), v___x_3392_);
v___x_3400_ = lean_apply_4(v_toSeqRight_3363_, lean_box(0), lean_box(0), v___x_3399_, v___f_3366_);
return v___x_3400_;
}
else
{
size_t v___x_3401_; size_t v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
lean_dec_ref(v_toApplicative_3362_);
v___x_3401_ = ((size_t)0ULL);
v___x_3402_ = lean_usize_of_nat(v___x_3391_);
v___x_3403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3364_, v___f_3367_, v_a_3390_, v___x_3401_, v___x_3402_, v___x_3392_);
v___x_3404_ = lean_apply_4(v_toSeqRight_3363_, lean_box(0), lean_box(0), v___x_3403_, v___f_3366_);
return v___x_3404_;
}
}
else
{
size_t v___x_3405_; size_t v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
lean_dec_ref(v_toApplicative_3362_);
v___x_3405_ = ((size_t)0ULL);
v___x_3406_ = lean_usize_of_nat(v___x_3391_);
v___x_3407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3364_, v___f_3367_, v_a_3390_, v___x_3405_, v___x_3406_, v___x_3392_);
v___x_3408_ = lean_apply_4(v_toSeqRight_3363_, lean_box(0), lean_box(0), v___x_3407_, v___f_3366_);
return v___x_3408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg___lam__0___boxed(lean_object* v_toPure_3409_, lean_object* v___x_3410_, lean_object* v_toApplicative_3411_, lean_object* v_toSeqRight_3412_, lean_object* v_inst_3413_, lean_object* v___f_3414_, lean_object* v___f_3415_, lean_object* v___f_3416_, lean_object* v_____do__lift_3417_){
_start:
{
lean_object* v_res_3418_; 
v_res_3418_ = l_Lake_ELogT_replayLog___redArg___lam__0(v_toPure_3409_, v___x_3410_, v_toApplicative_3411_, v_toSeqRight_3412_, v_inst_3413_, v___f_3414_, v___f_3415_, v___f_3416_, v_____do__lift_3417_);
lean_dec(v___x_3410_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg(lean_object* v_inst_3419_, lean_object* v_inst_3420_, lean_object* v_logger_3421_, lean_object* v_inst_3422_, lean_object* v_self_3423_){
_start:
{
lean_object* v_toApplicative_3424_; lean_object* v_toApplicative_3425_; lean_object* v_toBind_3426_; lean_object* v_failure_3427_; lean_object* v_toPure_3428_; lean_object* v_toSeqRight_3429_; lean_object* v___f_3430_; lean_object* v___f_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___f_3436_; lean_object* v___x_3437_; 
v_toApplicative_3424_ = lean_ctor_get(v_inst_3419_, 0);
lean_inc_ref(v_toApplicative_3424_);
v_toApplicative_3425_ = lean_ctor_get(v_inst_3420_, 0);
lean_inc_ref(v_toApplicative_3425_);
v_toBind_3426_ = lean_ctor_get(v_inst_3420_, 1);
lean_inc(v_toBind_3426_);
v_failure_3427_ = lean_ctor_get(v_inst_3419_, 1);
lean_inc(v_failure_3427_);
lean_dec_ref(v_inst_3419_);
v_toPure_3428_ = lean_ctor_get(v_toApplicative_3424_, 1);
lean_inc(v_toPure_3428_);
v_toSeqRight_3429_ = lean_ctor_get(v_toApplicative_3424_, 4);
lean_inc(v_toSeqRight_3429_);
lean_dec_ref(v_toApplicative_3424_);
v___f_3430_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3430_, 0, v_logger_3421_);
v___f_3431_ = lean_alloc_closure((void*)(l_Lake_MonadLog_error___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3431_, 0, v_failure_3427_);
v___x_3432_ = lean_unsigned_to_nat(0u);
v___x_3433_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3434_ = lean_apply_1(v_self_3423_, v___x_3433_);
v___x_3435_ = lean_apply_2(v_inst_3422_, lean_box(0), v___x_3434_);
lean_inc_ref(v___f_3430_);
v___f_3436_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3436_, 0, v_toPure_3428_);
lean_closure_set(v___f_3436_, 1, v___x_3432_);
lean_closure_set(v___f_3436_, 2, v_toApplicative_3425_);
lean_closure_set(v___f_3436_, 3, v_toSeqRight_3429_);
lean_closure_set(v___f_3436_, 4, v_inst_3420_);
lean_closure_set(v___f_3436_, 5, v___f_3430_);
lean_closure_set(v___f_3436_, 6, v___f_3431_);
lean_closure_set(v___f_3436_, 7, v___f_3430_);
v___x_3437_ = lean_apply_4(v_toBind_3426_, lean_box(0), lean_box(0), v___x_3435_, v___f_3436_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog(lean_object* v_n_3438_, lean_object* v_m_3439_, lean_object* v_00_u03b1_3440_, lean_object* v_inst_3441_, lean_object* v_inst_3442_, lean_object* v_logger_3443_, lean_object* v_inst_3444_, lean_object* v_self_3445_){
_start:
{
lean_object* v_toApplicative_3446_; lean_object* v_toApplicative_3447_; lean_object* v_toBind_3448_; lean_object* v_failure_3449_; lean_object* v_toPure_3450_; lean_object* v_toSeqRight_3451_; lean_object* v___f_3452_; lean_object* v___f_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___f_3458_; lean_object* v___x_3459_; 
v_toApplicative_3446_ = lean_ctor_get(v_inst_3441_, 0);
lean_inc_ref(v_toApplicative_3446_);
v_toApplicative_3447_ = lean_ctor_get(v_inst_3442_, 0);
lean_inc_ref(v_toApplicative_3447_);
v_toBind_3448_ = lean_ctor_get(v_inst_3442_, 1);
lean_inc(v_toBind_3448_);
v_failure_3449_ = lean_ctor_get(v_inst_3441_, 1);
lean_inc(v_failure_3449_);
lean_dec_ref(v_inst_3441_);
v_toPure_3450_ = lean_ctor_get(v_toApplicative_3446_, 1);
lean_inc(v_toPure_3450_);
v_toSeqRight_3451_ = lean_ctor_get(v_toApplicative_3446_, 4);
lean_inc(v_toSeqRight_3451_);
lean_dec_ref(v_toApplicative_3446_);
v___f_3452_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3452_, 0, v_logger_3443_);
v___f_3453_ = lean_alloc_closure((void*)(l_Lake_MonadLog_error___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3453_, 0, v_failure_3449_);
v___x_3454_ = lean_unsigned_to_nat(0u);
v___x_3455_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3456_ = lean_apply_1(v_self_3445_, v___x_3455_);
v___x_3457_ = lean_apply_2(v_inst_3444_, lean_box(0), v___x_3456_);
lean_inc_ref(v___f_3452_);
v___f_3458_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3458_, 0, v_toPure_3450_);
lean_closure_set(v___f_3458_, 1, v___x_3454_);
lean_closure_set(v___f_3458_, 2, v_toApplicative_3447_);
lean_closure_set(v___f_3458_, 3, v_toSeqRight_3451_);
lean_closure_set(v___f_3458_, 4, v_inst_3442_);
lean_closure_set(v___f_3458_, 5, v___f_3452_);
lean_closure_set(v___f_3458_, 6, v___f_3453_);
lean_closure_set(v___f_3458_, 7, v___f_3452_);
v___x_3459_ = lean_apply_4(v_toBind_3448_, lean_box(0), lean_box(0), v___x_3457_, v___f_3458_);
return v___x_3459_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___redArg___lam__0(lean_object* v_val_3460_, uint8_t v_outLv_3461_, uint8_t v_val_3462_, lean_object* v_inst_3463_, lean_object* v_e_3464_){
_start:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3465_ = lean_box(v_outLv_3461_);
v___x_3466_ = lean_box(v_val_3462_);
v___x_3467_ = lean_alloc_closure((void*)(l_Lake_logToStream___boxed), 5, 4);
lean_closure_set(v___x_3467_, 0, v_e_3464_);
lean_closure_set(v___x_3467_, 1, v_val_3460_);
lean_closure_set(v___x_3467_, 2, v___x_3465_);
lean_closure_set(v___x_3467_, 3, v___x_3466_);
v___x_3468_ = lean_apply_2(v_inst_3463_, lean_box(0), v___x_3467_);
return v___x_3468_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___redArg___lam__0___boxed(lean_object* v_val_3469_, lean_object* v_outLv_3470_, lean_object* v_val_3471_, lean_object* v_inst_3472_, lean_object* v_e_3473_){
_start:
{
uint8_t v_outLv_boxed_3474_; uint8_t v_val_44__boxed_3475_; lean_object* v_res_3476_; 
v_outLv_boxed_3474_ = lean_unbox(v_outLv_3470_);
v_val_44__boxed_3475_ = lean_unbox(v_val_3471_);
v_res_3476_ = l_Lake_LogConfig_getLogger___redArg___lam__0(v_val_3469_, v_outLv_boxed_3474_, v_val_44__boxed_3475_, v_inst_3472_, v_e_3473_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___redArg(lean_object* v_inst_3477_, lean_object* v_self_3478_){
_start:
{
uint8_t v_outLv_3480_; uint8_t v_ansiMode_3481_; lean_object* v_out_3482_; lean_object* v___x_3483_; uint8_t v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___f_3487_; 
v_outLv_3480_ = lean_ctor_get_uint8(v_self_3478_, sizeof(void*)*1 + 1);
v_ansiMode_3481_ = lean_ctor_get_uint8(v_self_3478_, sizeof(void*)*1 + 2);
v_out_3482_ = lean_ctor_get(v_self_3478_, 0);
v___x_3483_ = l_Lake_OutStream_get(v_out_3482_);
lean_inc_ref(v___x_3483_);
v___x_3484_ = l_Lake_AnsiMode_isEnabled(v___x_3483_, v_ansiMode_3481_);
v___x_3485_ = lean_box(v_outLv_3480_);
v___x_3486_ = lean_box(v___x_3484_);
v___f_3487_ = lean_alloc_closure((void*)(l_Lake_LogConfig_getLogger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3487_, 0, v___x_3483_);
lean_closure_set(v___f_3487_, 1, v___x_3485_);
lean_closure_set(v___f_3487_, 2, v___x_3486_);
lean_closure_set(v___f_3487_, 3, v_inst_3477_);
return v___f_3487_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___redArg___boxed(lean_object* v_inst_3488_, lean_object* v_self_3489_, lean_object* v_a_3490_){
_start:
{
lean_object* v_res_3491_; 
v_res_3491_ = l_Lake_LogConfig_getLogger___redArg(v_inst_3488_, v_self_3489_);
lean_dec_ref(v_self_3489_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger(lean_object* v_m_3492_, lean_object* v_inst_3493_, lean_object* v_self_3494_){
_start:
{
uint8_t v_outLv_3496_; uint8_t v_ansiMode_3497_; lean_object* v_out_3498_; lean_object* v___x_3499_; uint8_t v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___f_3503_; 
v_outLv_3496_ = lean_ctor_get_uint8(v_self_3494_, sizeof(void*)*1 + 1);
v_ansiMode_3497_ = lean_ctor_get_uint8(v_self_3494_, sizeof(void*)*1 + 2);
v_out_3498_ = lean_ctor_get(v_self_3494_, 0);
v___x_3499_ = l_Lake_OutStream_get(v_out_3498_);
lean_inc_ref(v___x_3499_);
v___x_3500_ = l_Lake_AnsiMode_isEnabled(v___x_3499_, v_ansiMode_3497_);
v___x_3501_ = lean_box(v_outLv_3496_);
v___x_3502_ = lean_box(v___x_3500_);
v___f_3503_ = lean_alloc_closure((void*)(l_Lake_LogConfig_getLogger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3503_, 0, v___x_3499_);
lean_closure_set(v___f_3503_, 1, v___x_3501_);
lean_closure_set(v___f_3503_, 2, v___x_3502_);
lean_closure_set(v___f_3503_, 3, v_inst_3493_);
return v___f_3503_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___boxed(lean_object* v_m_3504_, lean_object* v_inst_3505_, lean_object* v_self_3506_, lean_object* v_a_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l_Lake_LogConfig_getLogger(v_m_3504_, v_inst_3505_, v_self_3506_);
lean_dec_ref(v_self_3506_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_instMonadLiftIO___lam__0(lean_object* v_00_u03b1_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
lean_object* v___x_3513_; 
v___x_3513_ = lean_apply_1(v___y_3510_, lean_box(0));
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3515_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref_known(v___x_3513_, 1);
v___x_3515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3515_, 0, v_a_3514_);
lean_ctor_set(v___x_3515_, 1, v___y_3511_);
return v___x_3515_;
}
else
{
lean_object* v_a_3516_; lean_object* v___x_3517_; uint8_t v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
v_a_3516_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3516_);
lean_dec_ref_known(v___x_3513_, 1);
v___x_3517_ = lean_io_error_to_string(v_a_3516_);
v___x_3518_ = 3;
v___x_3519_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3519_, 0, v___x_3517_);
lean_ctor_set_uint8(v___x_3519_, sizeof(void*)*1, v___x_3518_);
v___x_3520_ = lean_array_get_size(v___y_3511_);
v___x_3521_ = lean_array_push(v___y_3511_, v___x_3519_);
v___x_3522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3520_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
return v___x_3522_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_instMonadLiftIO___lam__0___boxed(lean_object* v_00_u03b1_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = l_Lake_LogIO_instMonadLiftIO___lam__0(v_00_u03b1_3523_, v___y_3524_, v___y_3525_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg___lam__0(lean_object* v_val_3530_, uint8_t v___y_3531_, uint8_t v_val_3532_, lean_object* v_x_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v___x_3536_; 
v___x_3536_ = l_Lake_logToStream(v___y_3534_, v_val_3530_, v___y_3531_, v_val_3532_);
return v___x_3536_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed(lean_object* v_val_3537_, lean_object* v___y_3538_, lean_object* v_val_3539_, lean_object* v_x_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_){
_start:
{
uint8_t v___y_862__boxed_3543_; uint8_t v_val_863__boxed_3544_; lean_object* v_res_3545_; 
v___y_862__boxed_3543_ = lean_unbox(v___y_3538_);
v_val_863__boxed_3544_ = lean_unbox(v_val_3539_);
v_res_3545_ = l_Lake_LogIO_toBaseIO___redArg___lam__0(v_val_3537_, v___y_862__boxed_3543_, v_val_863__boxed_3544_, v_x_3540_, v___y_3541_);
lean_dec_ref(v___y_3541_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg(lean_object* v_self_3546_, lean_object* v_cfg_3547_){
_start:
{
uint8_t v___y_3550_; lean_object* v___y_3551_; uint8_t v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___x_3557_; uint8_t v___y_3559_; lean_object* v___y_3560_; lean_object* v___y_3561_; uint8_t v___y_3562_; lean_object* v___y_3584_; lean_object* v___y_3585_; uint8_t v___y_3586_; lean_object* v___x_3588_; lean_object* v___x_3589_; 
v___x_3557_ = l_instMonadBaseIO;
v___x_3588_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3589_ = lean_apply_2(v_self_3546_, v___x_3588_, lean_box(0));
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_object* v_a_3590_; lean_object* v_a_3591_; uint8_t v_failLv_3592_; uint8_t v_outLv_3593_; lean_object* v___x_3594_; uint8_t v___x_3595_; uint8_t v___x_3596_; 
v_a_3590_ = lean_ctor_get(v___x_3589_, 0);
lean_inc(v_a_3590_);
v_a_3591_ = lean_ctor_get(v___x_3589_, 1);
lean_inc(v_a_3591_);
lean_dec_ref_known(v___x_3589_, 2);
v_failLv_3592_ = lean_ctor_get_uint8(v_cfg_3547_, sizeof(void*)*1);
v_outLv_3593_ = lean_ctor_get_uint8(v_cfg_3547_, sizeof(void*)*1 + 1);
v___x_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3594_, 0, v_a_3590_);
v___x_3595_ = l_Lake_Log_maxLv(v_a_3591_);
v___x_3596_ = l_Lake_instOrdLogLevel_ord(v_failLv_3592_, v___x_3595_);
if (v___x_3596_ == 2)
{
uint8_t v___x_3597_; 
v___x_3597_ = 0;
v___y_3559_ = v___x_3597_;
v___y_3560_ = v___x_3594_;
v___y_3561_ = v_a_3591_;
v___y_3562_ = v_outLv_3593_;
goto v___jp_3558_;
}
else
{
uint8_t v___x_3598_; 
v___x_3598_ = 1;
v___y_3584_ = v_a_3591_;
v___y_3585_ = v___x_3594_;
v___y_3586_ = v___x_3598_;
goto v___jp_3583_;
}
}
else
{
lean_object* v_a_3599_; lean_object* v___x_3600_; uint8_t v___x_3601_; 
v_a_3599_ = lean_ctor_get(v___x_3589_, 1);
lean_inc(v_a_3599_);
lean_dec_ref_known(v___x_3589_, 2);
v___x_3600_ = lean_box(0);
v___x_3601_ = 1;
v___y_3584_ = v_a_3599_;
v___y_3585_ = v___x_3600_;
v___y_3586_ = v___x_3601_;
goto v___jp_3583_;
}
v___jp_3549_:
{
if (v___y_3550_ == 0)
{
return v___y_3551_;
}
else
{
lean_object* v___x_3552_; 
lean_dec(v___y_3551_);
v___x_3552_ = lean_box(0);
return v___x_3552_;
}
}
v___jp_3553_:
{
v___y_3550_ = v___y_3554_;
v___y_3551_ = v___y_3555_;
goto v___jp_3549_;
}
v___jp_3558_:
{
uint8_t v_ansiMode_3563_; lean_object* v_out_3564_; lean_object* v___x_3565_; uint8_t v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; uint8_t v___x_3569_; 
v_ansiMode_3563_ = lean_ctor_get_uint8(v_cfg_3547_, sizeof(void*)*1 + 2);
v_out_3564_ = lean_ctor_get(v_cfg_3547_, 0);
v___x_3565_ = l_Lake_OutStream_get(v_out_3564_);
lean_inc_ref(v___x_3565_);
v___x_3566_ = l_Lake_AnsiMode_isEnabled(v___x_3565_, v_ansiMode_3563_);
v___x_3567_ = lean_unsigned_to_nat(0u);
v___x_3568_ = lean_array_get_size(v___y_3561_);
v___x_3569_ = lean_nat_dec_lt(v___x_3567_, v___x_3568_);
if (v___x_3569_ == 0)
{
lean_dec_ref(v___x_3565_);
lean_dec_ref(v___y_3561_);
v___y_3550_ = v___y_3559_;
v___y_3551_ = v___y_3560_;
goto v___jp_3549_;
}
else
{
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___f_3572_; lean_object* v___x_3573_; uint8_t v___x_3574_; 
v___x_3570_ = lean_box(v___y_3562_);
v___x_3571_ = lean_box(v___x_3566_);
v___f_3572_ = lean_alloc_closure((void*)(l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_3572_, 0, v___x_3565_);
lean_closure_set(v___f_3572_, 1, v___x_3570_);
lean_closure_set(v___f_3572_, 2, v___x_3571_);
v___x_3573_ = lean_box(0);
v___x_3574_ = lean_nat_dec_le(v___x_3568_, v___x_3568_);
if (v___x_3574_ == 0)
{
if (v___x_3569_ == 0)
{
lean_dec_ref(v___f_3572_);
lean_dec_ref(v___y_3561_);
v___y_3550_ = v___y_3559_;
v___y_3551_ = v___y_3560_;
goto v___jp_3549_;
}
else
{
size_t v___x_3575_; size_t v___x_3576_; lean_object* v___x_652__overap_3577_; lean_object* v___x_3578_; 
v___x_3575_ = ((size_t)0ULL);
v___x_3576_ = lean_usize_of_nat(v___x_3568_);
v___x_652__overap_3577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3557_, v___f_3572_, v___y_3561_, v___x_3575_, v___x_3576_, v___x_3573_);
v___x_3578_ = lean_apply_1(v___x_652__overap_3577_, lean_box(0));
v___y_3554_ = v___y_3559_;
v___y_3555_ = v___y_3560_;
v___y_3556_ = v___x_3578_;
goto v___jp_3553_;
}
}
else
{
size_t v___x_3579_; size_t v___x_3580_; lean_object* v___x_656__overap_3581_; lean_object* v___x_3582_; 
v___x_3579_ = ((size_t)0ULL);
v___x_3580_ = lean_usize_of_nat(v___x_3568_);
v___x_656__overap_3581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3557_, v___f_3572_, v___y_3561_, v___x_3579_, v___x_3580_, v___x_3573_);
v___x_3582_ = lean_apply_1(v___x_656__overap_3581_, lean_box(0));
v___y_3554_ = v___y_3559_;
v___y_3555_ = v___y_3560_;
v___y_3556_ = v___x_3582_;
goto v___jp_3553_;
}
}
}
v___jp_3583_:
{
uint8_t v___x_3587_; 
v___x_3587_ = 0;
v___y_3559_ = v___y_3586_;
v___y_3560_ = v___y_3585_;
v___y_3561_ = v___y_3584_;
v___y_3562_ = v___x_3587_;
goto v___jp_3558_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg___boxed(lean_object* v_self_3602_, lean_object* v_cfg_3603_, lean_object* v_a_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l_Lake_LogIO_toBaseIO___redArg(v_self_3602_, v_cfg_3603_);
lean_dec_ref(v_cfg_3603_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO(lean_object* v_00_u03b1_3606_, lean_object* v_self_3607_, lean_object* v_cfg_3608_){
_start:
{
uint8_t v___y_3611_; lean_object* v___y_3612_; uint8_t v___y_3615_; lean_object* v___y_3616_; lean_object* v___y_3617_; lean_object* v___x_3618_; uint8_t v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; uint8_t v___y_3623_; lean_object* v___y_3645_; lean_object* v___y_3646_; uint8_t v___y_3647_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3618_ = l_instMonadBaseIO;
v___x_3649_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3650_ = lean_apply_2(v_self_3607_, v___x_3649_, lean_box(0));
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v_a_3651_; lean_object* v_a_3652_; uint8_t v_failLv_3653_; uint8_t v_outLv_3654_; lean_object* v___x_3655_; uint8_t v___x_3656_; uint8_t v___x_3657_; 
v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
lean_inc(v_a_3651_);
v_a_3652_ = lean_ctor_get(v___x_3650_, 1);
lean_inc(v_a_3652_);
lean_dec_ref_known(v___x_3650_, 2);
v_failLv_3653_ = lean_ctor_get_uint8(v_cfg_3608_, sizeof(void*)*1);
v_outLv_3654_ = lean_ctor_get_uint8(v_cfg_3608_, sizeof(void*)*1 + 1);
v___x_3655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3655_, 0, v_a_3651_);
v___x_3656_ = l_Lake_Log_maxLv(v_a_3652_);
v___x_3657_ = l_Lake_instOrdLogLevel_ord(v_failLv_3653_, v___x_3656_);
if (v___x_3657_ == 2)
{
uint8_t v___x_3658_; 
v___x_3658_ = 0;
v___y_3620_ = v___x_3658_;
v___y_3621_ = v___x_3655_;
v___y_3622_ = v_a_3652_;
v___y_3623_ = v_outLv_3654_;
goto v___jp_3619_;
}
else
{
uint8_t v___x_3659_; 
v___x_3659_ = 1;
v___y_3645_ = v_a_3652_;
v___y_3646_ = v___x_3655_;
v___y_3647_ = v___x_3659_;
goto v___jp_3644_;
}
}
else
{
lean_object* v_a_3660_; lean_object* v___x_3661_; uint8_t v___x_3662_; 
v_a_3660_ = lean_ctor_get(v___x_3650_, 1);
lean_inc(v_a_3660_);
lean_dec_ref_known(v___x_3650_, 2);
v___x_3661_ = lean_box(0);
v___x_3662_ = 1;
v___y_3645_ = v_a_3660_;
v___y_3646_ = v___x_3661_;
v___y_3647_ = v___x_3662_;
goto v___jp_3644_;
}
v___jp_3610_:
{
if (v___y_3611_ == 0)
{
return v___y_3612_;
}
else
{
lean_object* v___x_3613_; 
lean_dec(v___y_3612_);
v___x_3613_ = lean_box(0);
return v___x_3613_;
}
}
v___jp_3614_:
{
v___y_3611_ = v___y_3615_;
v___y_3612_ = v___y_3616_;
goto v___jp_3610_;
}
v___jp_3619_:
{
uint8_t v_ansiMode_3624_; lean_object* v_out_3625_; lean_object* v___x_3626_; uint8_t v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; uint8_t v___x_3630_; 
v_ansiMode_3624_ = lean_ctor_get_uint8(v_cfg_3608_, sizeof(void*)*1 + 2);
v_out_3625_ = lean_ctor_get(v_cfg_3608_, 0);
v___x_3626_ = l_Lake_OutStream_get(v_out_3625_);
lean_inc_ref(v___x_3626_);
v___x_3627_ = l_Lake_AnsiMode_isEnabled(v___x_3626_, v_ansiMode_3624_);
v___x_3628_ = lean_unsigned_to_nat(0u);
v___x_3629_ = lean_array_get_size(v___y_3622_);
v___x_3630_ = lean_nat_dec_lt(v___x_3628_, v___x_3629_);
if (v___x_3630_ == 0)
{
lean_dec_ref(v___x_3626_);
lean_dec_ref(v___y_3622_);
v___y_3611_ = v___y_3620_;
v___y_3612_ = v___y_3621_;
goto v___jp_3610_;
}
else
{
lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___f_3633_; lean_object* v___x_3634_; uint8_t v___x_3635_; 
v___x_3631_ = lean_box(v___y_3623_);
v___x_3632_ = lean_box(v___x_3627_);
v___f_3633_ = lean_alloc_closure((void*)(l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_3633_, 0, v___x_3626_);
lean_closure_set(v___f_3633_, 1, v___x_3631_);
lean_closure_set(v___f_3633_, 2, v___x_3632_);
v___x_3634_ = lean_box(0);
v___x_3635_ = lean_nat_dec_le(v___x_3629_, v___x_3629_);
if (v___x_3635_ == 0)
{
if (v___x_3630_ == 0)
{
lean_dec_ref(v___f_3633_);
lean_dec_ref(v___y_3622_);
v___y_3611_ = v___y_3620_;
v___y_3612_ = v___y_3621_;
goto v___jp_3610_;
}
else
{
size_t v___x_3636_; size_t v___x_3637_; lean_object* v___x_791__overap_3638_; lean_object* v___x_3639_; 
v___x_3636_ = ((size_t)0ULL);
v___x_3637_ = lean_usize_of_nat(v___x_3629_);
v___x_791__overap_3638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3618_, v___f_3633_, v___y_3622_, v___x_3636_, v___x_3637_, v___x_3634_);
v___x_3639_ = lean_apply_1(v___x_791__overap_3638_, lean_box(0));
v___y_3615_ = v___y_3620_;
v___y_3616_ = v___y_3621_;
v___y_3617_ = v___x_3639_;
goto v___jp_3614_;
}
}
else
{
size_t v___x_3640_; size_t v___x_3641_; lean_object* v___x_794__overap_3642_; lean_object* v___x_3643_; 
v___x_3640_ = ((size_t)0ULL);
v___x_3641_ = lean_usize_of_nat(v___x_3629_);
v___x_794__overap_3642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3618_, v___f_3633_, v___y_3622_, v___x_3640_, v___x_3641_, v___x_3634_);
v___x_3643_ = lean_apply_1(v___x_794__overap_3642_, lean_box(0));
v___y_3615_ = v___y_3620_;
v___y_3616_ = v___y_3621_;
v___y_3617_ = v___x_3643_;
goto v___jp_3614_;
}
}
}
v___jp_3644_:
{
uint8_t v___x_3648_; 
v___x_3648_ = 0;
v___y_3620_ = v___y_3647_;
v___y_3621_ = v___y_3646_;
v___y_3622_ = v___y_3645_;
v___y_3623_ = v___x_3648_;
goto v___jp_3619_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___boxed(lean_object* v_00_u03b1_3663_, lean_object* v_self_3664_, lean_object* v_cfg_3665_, lean_object* v_a_3666_){
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l_Lake_LogIO_toBaseIO(v_00_u03b1_3663_, v_self_3664_, v_cfg_3665_);
lean_dec_ref(v_cfg_3665_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_captureLog___redArg(lean_object* v_inst_3668_, lean_object* v_self_3669_, lean_object* v_log_3670_){
_start:
{
lean_object* v_map_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v_map_3671_ = lean_ctor_get(v_inst_3668_, 0);
lean_inc(v_map_3671_);
lean_dec_ref(v_inst_3668_);
v___x_3672_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3673_ = lean_apply_1(v_self_3669_, v_log_3670_);
v___x_3674_ = lean_apply_4(v_map_3671_, lean_box(0), lean_box(0), v___x_3672_, v___x_3673_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_captureLog(lean_object* v_m_3675_, lean_object* v_00_u03b1_3676_, lean_object* v_inst_3677_, lean_object* v_self_3678_, lean_object* v_log_3679_){
_start:
{
lean_object* v_map_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; 
v_map_3680_ = lean_ctor_get(v_inst_3677_, 0);
lean_inc(v_map_3680_);
lean_dec_ref(v_inst_3677_);
v___x_3681_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3682_ = lean_apply_1(v_self_3678_, v_log_3679_);
v___x_3683_ = lean_apply_4(v_map_3680_, lean_box(0), lean_box(0), v___x_3681_, v___x_3682_);
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadError___lam__0(lean_object* v_00_u03b1_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_){
_start:
{
uint8_t v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___x_3688_ = 3;
v___x_3689_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3689_, 0, v___y_3685_);
lean_ctor_set_uint8(v___x_3689_, sizeof(void*)*1, v___x_3688_);
lean_inc_ref(v___y_3686_);
v___x_3690_ = lean_apply_2(v___y_3686_, v___x_3689_, lean_box(0));
v___x_3691_ = lean_box(0);
v___x_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3691_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadError___lam__0___boxed(lean_object* v_00_u03b1_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v_res_3697_; 
v_res_3697_ = l_Lake_LoggerIO_instMonadError___lam__0(v_00_u03b1_3693_, v___y_3694_, v___y_3695_);
lean_dec_ref(v___y_3695_);
return v_res_3697_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftIO___lam__0(lean_object* v_00_u03b1_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_){
_start:
{
lean_object* v___x_3704_; 
v___x_3704_ = lean_apply_1(v___y_3701_, lean_box(0));
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v_a_3705_; lean_object* v___x_3707_; uint8_t v_isShared_3708_; uint8_t v_isSharedCheck_3712_; 
v_a_3705_ = lean_ctor_get(v___x_3704_, 0);
v_isSharedCheck_3712_ = !lean_is_exclusive(v___x_3704_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3707_ = v___x_3704_;
v_isShared_3708_ = v_isSharedCheck_3712_;
goto v_resetjp_3706_;
}
else
{
lean_inc(v_a_3705_);
lean_dec(v___x_3704_);
v___x_3707_ = lean_box(0);
v_isShared_3708_ = v_isSharedCheck_3712_;
goto v_resetjp_3706_;
}
v_resetjp_3706_:
{
lean_object* v___x_3710_; 
if (v_isShared_3708_ == 0)
{
v___x_3710_ = v___x_3707_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_a_3705_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
}
else
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3725_; 
v_a_3713_ = lean_ctor_get(v___x_3704_, 0);
v_isSharedCheck_3725_ = !lean_is_exclusive(v___x_3704_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3715_ = v___x_3704_;
v_isShared_3716_ = v_isSharedCheck_3725_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3704_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3725_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3717_; uint8_t v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3723_; 
v___x_3717_ = lean_io_error_to_string(v_a_3713_);
v___x_3718_ = 3;
v___x_3719_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3719_, 0, v___x_3717_);
lean_ctor_set_uint8(v___x_3719_, sizeof(void*)*1, v___x_3718_);
lean_inc_ref(v___y_3702_);
v___x_3720_ = lean_apply_2(v___y_3702_, v___x_3719_, lean_box(0));
v___x_3721_ = lean_box(0);
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v___x_3721_);
v___x_3723_ = v___x_3715_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v___x_3721_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftIO___lam__0___boxed(lean_object* v_00_u03b1_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l_Lake_LoggerIO_instMonadLiftIO___lam__0(v_00_u03b1_3726_, v___y_3727_, v___y_3728_);
lean_dec_ref(v___y_3728_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__0(lean_object* v_x_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_){
_start:
{
lean_object* v___x_3737_; lean_object* v___x_3738_; 
lean_inc_ref(v___y_3735_);
v___x_3737_ = lean_apply_2(v___y_3735_, v___y_3734_, lean_box(0));
v___x_3738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3737_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__0___boxed(lean_object* v_x_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_){
_start:
{
lean_object* v_res_3743_; 
v_res_3743_ = l_Lake_LoggerIO_instMonadLiftLogIO___lam__0(v_x_3739_, v___y_3740_, v___y_3741_);
lean_dec_ref(v___y_3741_);
return v_res_3743_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__2(lean_object* v___x_3744_, lean_object* v___f_3745_, lean_object* v___f_3746_, lean_object* v_00_u03b1_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; 
v___x_3754_ = lean_unsigned_to_nat(0u);
v___x_3755_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3756_ = lean_apply_2(v___y_3748_, v___x_3755_, lean_box(0));
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_object* v_a_3757_; lean_object* v_a_3758_; lean_object* v___x_3759_; uint8_t v___x_3760_; 
lean_dec_ref(v___f_3746_);
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
lean_inc(v_a_3757_);
v_a_3758_ = lean_ctor_get(v___x_3756_, 1);
lean_inc(v_a_3758_);
lean_dec_ref_known(v___x_3756_, 2);
v___x_3759_ = lean_array_get_size(v_a_3758_);
v___x_3760_ = lean_nat_dec_lt(v___x_3754_, v___x_3759_);
if (v___x_3760_ == 0)
{
lean_object* v___x_3761_; 
lean_dec(v_a_3758_);
lean_dec_ref(v___f_3745_);
lean_dec_ref(v___x_3744_);
v___x_3761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3761_, 0, v_a_3757_);
return v___x_3761_;
}
else
{
lean_object* v___x_3762_; uint8_t v___x_3763_; 
v___x_3762_ = lean_box(0);
v___x_3763_ = lean_nat_dec_le(v___x_3759_, v___x_3759_);
if (v___x_3763_ == 0)
{
if (v___x_3760_ == 0)
{
lean_object* v___x_3764_; 
lean_dec(v_a_3758_);
lean_dec_ref(v___f_3745_);
lean_dec_ref(v___x_3744_);
v___x_3764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3764_, 0, v_a_3757_);
return v___x_3764_;
}
else
{
size_t v___x_3765_; size_t v___x_3766_; lean_object* v___x_1796__overap_3767_; lean_object* v___x_3768_; 
v___x_3765_ = ((size_t)0ULL);
v___x_3766_ = lean_usize_of_nat(v___x_3759_);
v___x_1796__overap_3767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3744_, v___f_3745_, v_a_3758_, v___x_3765_, v___x_3766_, v___x_3762_);
lean_inc_ref(v___y_3749_);
v___x_3768_ = lean_apply_2(v___x_1796__overap_3767_, v___y_3749_, lean_box(0));
if (lean_obj_tag(v___x_3768_) == 0)
{
lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3775_ == 0)
{
lean_object* v_unused_3776_; 
v_unused_3776_ = lean_ctor_get(v___x_3768_, 0);
lean_dec(v_unused_3776_);
v___x_3770_ = v___x_3768_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_dec(v___x_3768_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
lean_ctor_set(v___x_3770_, 0, v_a_3757_);
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3757_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
lean_dec(v_a_3757_);
v_a_3777_ = lean_ctor_get(v___x_3768_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___x_3768_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3768_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
}
else
{
size_t v___x_3785_; size_t v___x_3786_; lean_object* v___x_1805__overap_3787_; lean_object* v___x_3788_; 
v___x_3785_ = ((size_t)0ULL);
v___x_3786_ = lean_usize_of_nat(v___x_3759_);
v___x_1805__overap_3787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3744_, v___f_3745_, v_a_3758_, v___x_3785_, v___x_3786_, v___x_3762_);
lean_inc_ref(v___y_3749_);
v___x_3788_ = lean_apply_2(v___x_1805__overap_3787_, v___y_3749_, lean_box(0));
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3795_ == 0)
{
lean_object* v_unused_3796_; 
v_unused_3796_ = lean_ctor_get(v___x_3788_, 0);
lean_dec(v_unused_3796_);
v___x_3790_ = v___x_3788_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_dec(v___x_3788_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
lean_ctor_set(v___x_3790_, 0, v_a_3757_);
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3757_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
else
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
lean_dec(v_a_3757_);
v_a_3797_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3799_ = v___x_3788_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3788_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3797_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
}
}
}
else
{
lean_object* v_a_3805_; lean_object* v___x_3806_; uint8_t v___x_3807_; 
lean_dec_ref(v___f_3745_);
v_a_3805_ = lean_ctor_get(v___x_3756_, 1);
lean_inc(v_a_3805_);
lean_dec_ref_known(v___x_3756_, 2);
v___x_3806_ = lean_array_get_size(v_a_3805_);
v___x_3807_ = lean_nat_dec_lt(v___x_3754_, v___x_3806_);
if (v___x_3807_ == 0)
{
lean_object* v___x_3808_; lean_object* v___x_3809_; 
lean_dec(v_a_3805_);
lean_dec_ref(v___f_3746_);
lean_dec_ref(v___x_3744_);
v___x_3808_ = lean_box(0);
v___x_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3808_);
return v___x_3809_;
}
else
{
lean_object* v___x_3810_; uint8_t v___x_3811_; 
v___x_3810_ = lean_box(0);
v___x_3811_ = lean_nat_dec_le(v___x_3806_, v___x_3806_);
if (v___x_3811_ == 0)
{
if (v___x_3807_ == 0)
{
lean_dec(v_a_3805_);
lean_dec_ref(v___f_3746_);
lean_dec_ref(v___x_3744_);
goto v___jp_3751_;
}
else
{
size_t v___x_3812_; size_t v___x_3813_; lean_object* v___x_1826__overap_3814_; lean_object* v___x_3815_; 
v___x_3812_ = ((size_t)0ULL);
v___x_3813_ = lean_usize_of_nat(v___x_3806_);
v___x_1826__overap_3814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3744_, v___f_3746_, v_a_3805_, v___x_3812_, v___x_3813_, v___x_3810_);
lean_inc_ref(v___y_3749_);
v___x_3815_ = lean_apply_2(v___x_1826__overap_3814_, v___y_3749_, lean_box(0));
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_dec_ref_known(v___x_3815_, 1);
goto v___jp_3751_;
}
else
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3823_; 
v_a_3816_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3818_ = v___x_3815_;
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3815_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3821_; 
if (v_isShared_3819_ == 0)
{
v___x_3821_ = v___x_3818_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_a_3816_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
}
}
}
else
{
size_t v___x_3824_; size_t v___x_3825_; lean_object* v___x_1834__overap_3826_; lean_object* v___x_3827_; 
v___x_3824_ = ((size_t)0ULL);
v___x_3825_ = lean_usize_of_nat(v___x_3806_);
v___x_1834__overap_3826_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3744_, v___f_3746_, v_a_3805_, v___x_3824_, v___x_3825_, v___x_3810_);
lean_inc_ref(v___y_3749_);
v___x_3827_ = lean_apply_2(v___x_1834__overap_3826_, v___y_3749_, lean_box(0));
if (lean_obj_tag(v___x_3827_) == 0)
{
lean_dec_ref_known(v___x_3827_, 1);
goto v___jp_3751_;
}
else
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
v_a_3828_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3830_ = v___x_3827_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3827_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3828_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
}
}
}
v___jp_3751_:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3752_ = lean_box(0);
v___x_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3752_);
return v___x_3753_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__2___boxed(lean_object* v___x_3836_, lean_object* v___f_3837_, lean_object* v___f_3838_, lean_object* v_00_u03b1_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_){
_start:
{
lean_object* v_res_3843_; 
v_res_3843_ = l_Lake_LoggerIO_instMonadLiftLogIO___lam__2(v___x_3836_, v___f_3837_, v___f_3838_, v_00_u03b1_3839_, v___y_3840_, v___y_3841_);
lean_dec_ref(v___y_3841_);
return v_res_3843_;
}
}
static lean_object* _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__1(void){
_start:
{
lean_object* v___x_3845_; 
v___x_3845_ = l_instMonadEIO(lean_box(0));
return v___x_3845_;
}
}
static lean_object* _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__2(void){
_start:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; 
v___x_3846_ = lean_obj_once(&l_Lake_LoggerIO_instMonadLiftLogIO___closed__1, &l_Lake_LoggerIO_instMonadLiftLogIO___closed__1_once, _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__1);
v___x_3847_ = l_ReaderT_instMonad___redArg(v___x_3846_);
return v___x_3847_;
}
}
static lean_object* _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__3(void){
_start:
{
lean_object* v___f_3848_; lean_object* v___x_3849_; lean_object* v___f_3850_; 
v___f_3848_ = ((lean_object*)(l_Lake_LoggerIO_instMonadLiftLogIO___closed__0));
v___x_3849_ = lean_obj_once(&l_Lake_LoggerIO_instMonadLiftLogIO___closed__2, &l_Lake_LoggerIO_instMonadLiftLogIO___closed__2_once, _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__2);
v___f_3850_ = lean_alloc_closure((void*)(l_Lake_LoggerIO_instMonadLiftLogIO___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3850_, 0, v___x_3849_);
lean_closure_set(v___f_3850_, 1, v___f_3848_);
lean_closure_set(v___f_3850_, 2, v___f_3848_);
return v___f_3850_;
}
}
static lean_object* _init_l_Lake_LoggerIO_instMonadLiftLogIO(void){
_start:
{
lean_object* v___f_3851_; 
v___f_3851_ = lean_obj_once(&l_Lake_LoggerIO_instMonadLiftLogIO___closed__3, &l_Lake_LoggerIO_instMonadLiftLogIO___closed__3_once, _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__3);
return v___f_3851_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg___lam__0(lean_object* v_val_3852_, uint8_t v_outLv_3853_, uint8_t v_val_3854_, lean_object* v_e_3855_){
_start:
{
lean_object* v___x_3857_; 
v___x_3857_ = l_Lake_logToStream(v_e_3855_, v_val_3852_, v_outLv_3853_, v_val_3854_);
return v___x_3857_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg___lam__0___boxed(lean_object* v_val_3858_, lean_object* v_outLv_3859_, lean_object* v_val_3860_, lean_object* v_e_3861_, lean_object* v___y_3862_){
_start:
{
uint8_t v_outLv_boxed_3863_; uint8_t v_val_178__boxed_3864_; lean_object* v_res_3865_; 
v_outLv_boxed_3863_ = lean_unbox(v_outLv_3859_);
v_val_178__boxed_3864_ = lean_unbox(v_val_3860_);
v_res_3865_ = l_Lake_LoggerIO_toBaseIO___redArg___lam__0(v_val_3858_, v_outLv_boxed_3863_, v_val_178__boxed_3864_, v_e_3861_);
lean_dec_ref(v_e_3861_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg(lean_object* v_self_3866_, lean_object* v_cfg_3867_){
_start:
{
uint8_t v_outLv_3869_; uint8_t v_ansiMode_3870_; lean_object* v_out_3871_; lean_object* v___x_3872_; uint8_t v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___f_3876_; lean_object* v___x_3877_; 
v_outLv_3869_ = lean_ctor_get_uint8(v_cfg_3867_, sizeof(void*)*1 + 1);
v_ansiMode_3870_ = lean_ctor_get_uint8(v_cfg_3867_, sizeof(void*)*1 + 2);
v_out_3871_ = lean_ctor_get(v_cfg_3867_, 0);
v___x_3872_ = l_Lake_OutStream_get(v_out_3871_);
lean_inc_ref(v___x_3872_);
v___x_3873_ = l_Lake_AnsiMode_isEnabled(v___x_3872_, v_ansiMode_3870_);
v___x_3874_ = lean_box(v_outLv_3869_);
v___x_3875_ = lean_box(v___x_3873_);
v___f_3876_ = lean_alloc_closure((void*)(l_Lake_LoggerIO_toBaseIO___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3876_, 0, v___x_3872_);
lean_closure_set(v___f_3876_, 1, v___x_3874_);
lean_closure_set(v___f_3876_, 2, v___x_3875_);
v___x_3877_ = lean_apply_2(v_self_3866_, v___f_3876_, lean_box(0));
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3877_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3877_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
lean_ctor_set_tag(v___x_3880_, 1);
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
else
{
lean_object* v___x_3886_; 
lean_dec_ref_known(v___x_3877_, 1);
v___x_3886_ = lean_box(0);
return v___x_3886_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg___boxed(lean_object* v_self_3887_, lean_object* v_cfg_3888_, lean_object* v_a_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l_Lake_LoggerIO_toBaseIO___redArg(v_self_3887_, v_cfg_3888_);
lean_dec_ref(v_cfg_3888_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO(lean_object* v_00_u03b1_3891_, lean_object* v_self_3892_, lean_object* v_cfg_3893_){
_start:
{
uint8_t v_outLv_3895_; uint8_t v_ansiMode_3896_; lean_object* v_out_3897_; lean_object* v___x_3898_; uint8_t v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___f_3902_; lean_object* v___x_3903_; 
v_outLv_3895_ = lean_ctor_get_uint8(v_cfg_3893_, sizeof(void*)*1 + 1);
v_ansiMode_3896_ = lean_ctor_get_uint8(v_cfg_3893_, sizeof(void*)*1 + 2);
v_out_3897_ = lean_ctor_get(v_cfg_3893_, 0);
v___x_3898_ = l_Lake_OutStream_get(v_out_3897_);
lean_inc_ref(v___x_3898_);
v___x_3899_ = l_Lake_AnsiMode_isEnabled(v___x_3898_, v_ansiMode_3896_);
v___x_3900_ = lean_box(v_outLv_3895_);
v___x_3901_ = lean_box(v___x_3899_);
v___f_3902_ = lean_alloc_closure((void*)(l_Lake_LoggerIO_toBaseIO___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3902_, 0, v___x_3898_);
lean_closure_set(v___f_3902_, 1, v___x_3900_);
lean_closure_set(v___f_3902_, 2, v___x_3901_);
v___x_3903_ = lean_apply_2(v_self_3892_, v___f_3902_, lean_box(0));
if (lean_obj_tag(v___x_3903_) == 0)
{
lean_object* v_a_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3911_; 
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3906_ = v___x_3903_;
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_a_3904_);
lean_dec(v___x_3903_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3909_; 
if (v_isShared_3907_ == 0)
{
lean_ctor_set_tag(v___x_3906_, 1);
v___x_3909_ = v___x_3906_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v_a_3904_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
}
else
{
lean_object* v___x_3912_; 
lean_dec_ref_known(v___x_3903_, 1);
v___x_3912_ = lean_box(0);
return v___x_3912_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___boxed(lean_object* v_00_u03b1_3913_, lean_object* v_self_3914_, lean_object* v_cfg_3915_, lean_object* v_a_3916_){
_start:
{
lean_object* v_res_3917_; 
v_res_3917_ = l_Lake_LoggerIO_toBaseIO(v_00_u03b1_3913_, v_self_3914_, v_cfg_3915_);
lean_dec_ref(v_cfg_3915_);
return v_res_3917_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg___lam__0(lean_object* v_val_3918_, lean_object* v_e_3919_){
_start:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3921_ = lean_st_ref_take(v_val_3918_);
v___x_3922_ = lean_array_push(v___x_3921_, v_e_3919_);
v___x_3923_ = lean_st_ref_set(v_val_3918_, v___x_3922_);
return v___x_3923_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg___lam__0___boxed(lean_object* v_val_3924_, lean_object* v_e_3925_, lean_object* v___y_3926_){
_start:
{
lean_object* v_res_3927_; 
v_res_3927_ = l_Lake_LoggerIO_captureLog___redArg___lam__0(v_val_3924_, v_e_3925_);
lean_dec(v_val_3924_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg(lean_object* v_self_3928_){
_start:
{
lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v_val_3937_; lean_object* v___f_3948_; lean_object* v___x_3949_; 
v___x_3934_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3935_ = lean_st_mk_ref(v___x_3934_);
lean_inc(v___x_3935_);
v___f_3948_ = lean_alloc_closure((void*)(l_Lake_LoggerIO_captureLog___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3948_, 0, v___x_3935_);
v___x_3949_ = lean_apply_2(v_self_3928_, v___f_3948_, lean_box(0));
if (lean_obj_tag(v___x_3949_) == 0)
{
lean_object* v_a_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3957_; 
v_a_3950_ = lean_ctor_get(v___x_3949_, 0);
v_isSharedCheck_3957_ = !lean_is_exclusive(v___x_3949_);
if (v_isSharedCheck_3957_ == 0)
{
v___x_3952_ = v___x_3949_;
v_isShared_3953_ = v_isSharedCheck_3957_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_a_3950_);
lean_dec(v___x_3949_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3957_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___x_3955_; 
if (v_isShared_3953_ == 0)
{
lean_ctor_set_tag(v___x_3952_, 1);
v___x_3955_ = v___x_3952_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v_a_3950_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
v_val_3937_ = v___x_3955_;
goto v___jp_3936_;
}
}
}
else
{
lean_object* v_a_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3965_; 
v_a_3958_ = lean_ctor_get(v___x_3949_, 0);
v_isSharedCheck_3965_ = !lean_is_exclusive(v___x_3949_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3960_ = v___x_3949_;
v_isShared_3961_ = v_isSharedCheck_3965_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_a_3958_);
lean_dec(v___x_3949_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3965_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v___x_3963_; 
if (v_isShared_3961_ == 0)
{
lean_ctor_set_tag(v___x_3960_, 0);
v___x_3963_ = v___x_3960_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_a_3958_);
v___x_3963_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
v_val_3937_ = v___x_3963_;
goto v___jp_3936_;
}
}
}
v___jp_3930_:
{
lean_object* v___x_3933_; 
v___x_3933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3933_, 0, v___y_3932_);
lean_ctor_set(v___x_3933_, 1, v___y_3931_);
return v___x_3933_;
}
v___jp_3936_:
{
lean_object* v___x_3938_; 
v___x_3938_ = lean_st_ref_get(v___x_3935_);
lean_dec(v___x_3935_);
if (lean_obj_tag(v_val_3937_) == 0)
{
lean_object* v___x_3939_; 
lean_dec_ref_known(v_val_3937_, 1);
v___x_3939_ = lean_box(0);
v___y_3931_ = v___x_3938_;
v___y_3932_ = v___x_3939_;
goto v___jp_3930_;
}
else
{
lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3947_; 
v_a_3940_ = lean_ctor_get(v_val_3937_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v_val_3937_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3942_ = v_val_3937_;
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_dec(v_val_3937_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3945_; 
if (v_isShared_3943_ == 0)
{
v___x_3945_ = v___x_3942_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_a_3940_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
v___y_3931_ = v___x_3938_;
v___y_3932_ = v___x_3945_;
goto v___jp_3930_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg___boxed(lean_object* v_self_3966_, lean_object* v_a_3967_){
_start:
{
lean_object* v_res_3968_; 
v_res_3968_ = l_Lake_LoggerIO_captureLog___redArg(v_self_3966_);
return v_res_3968_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog(lean_object* v_00_u03b1_3969_, lean_object* v_self_3970_){
_start:
{
lean_object* v___x_3972_; 
v___x_3972_ = l_Lake_LoggerIO_captureLog___redArg(v_self_3970_);
return v___x_3972_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___boxed(lean_object* v_00_u03b1_3973_, lean_object* v_self_3974_, lean_object* v_a_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l_Lake_LoggerIO_captureLog(v_00_u03b1_3973_, v_self_3974_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f___redArg(lean_object* v_self_3977_){
_start:
{
lean_object* v___x_3979_; 
v___x_3979_ = l_Lake_LoggerIO_captureLog___redArg(v_self_3977_);
return v___x_3979_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f___redArg___boxed(lean_object* v_self_3980_, lean_object* v_a_3981_){
_start:
{
lean_object* v_res_3982_; 
v_res_3982_ = l_Lake_LoggerIO_run_x3f___redArg(v_self_3980_);
return v_res_3982_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f(lean_object* v_00_u03b1_3983_, lean_object* v_self_3984_){
_start:
{
lean_object* v___x_3986_; 
v___x_3986_ = l_Lake_LoggerIO_captureLog___redArg(v_self_3984_);
return v___x_3986_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f___boxed(lean_object* v_00_u03b1_3987_, lean_object* v_self_3988_, lean_object* v_a_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l_Lake_LoggerIO_run_x3f(v_00_u03b1_3987_, v_self_3988_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27___redArg(lean_object* v_self_3991_, lean_object* v_logger_3992_){
_start:
{
lean_object* v___x_3994_; 
v___x_3994_ = lean_apply_2(v_self_3991_, v_logger_3992_, lean_box(0));
if (lean_obj_tag(v___x_3994_) == 0)
{
lean_object* v_a_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4002_; 
v_a_3995_ = lean_ctor_get(v___x_3994_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3997_ = v___x_3994_;
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_a_3995_);
lean_dec(v___x_3994_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v___x_4000_; 
if (v_isShared_3998_ == 0)
{
lean_ctor_set_tag(v___x_3997_, 1);
v___x_4000_ = v___x_3997_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v_a_3995_);
v___x_4000_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
return v___x_4000_;
}
}
}
else
{
lean_object* v___x_4003_; 
lean_dec_ref_known(v___x_3994_, 1);
v___x_4003_ = lean_box(0);
return v___x_4003_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27___redArg___boxed(lean_object* v_self_4004_, lean_object* v_logger_4005_, lean_object* v_a_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l_Lake_LoggerIO_run_x3f_x27___redArg(v_self_4004_, v_logger_4005_);
return v_res_4007_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27(lean_object* v_00_u03b1_4008_, lean_object* v_self_4009_, lean_object* v_logger_4010_){
_start:
{
lean_object* v___x_4012_; 
v___x_4012_ = lean_apply_2(v_self_4009_, v_logger_4010_, lean_box(0));
if (lean_obj_tag(v___x_4012_) == 0)
{
lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4020_; 
v_a_4013_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4015_ = v___x_4012_;
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v___x_4012_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4018_; 
if (v_isShared_4016_ == 0)
{
lean_ctor_set_tag(v___x_4015_, 1);
v___x_4018_ = v___x_4015_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4013_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
}
else
{
lean_object* v___x_4021_; 
lean_dec_ref_known(v___x_4012_, 1);
v___x_4021_ = lean_box(0);
return v___x_4021_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27___boxed(lean_object* v_00_u03b1_4022_, lean_object* v_self_4023_, lean_object* v_logger_4024_, lean_object* v_a_4025_){
_start:
{
lean_object* v_res_4026_; 
v_res_4026_ = l_Lake_LoggerIO_run_x3f_x27(v_00_u03b1_4022_, v_self_4023_, v_logger_4024_);
return v_res_4026_;
}
}
lean_object* runtime_initialize_Lean_Data_Json(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Error(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_EStateT(uint8_t builtin);
lean_object* runtime_initialize_Lean_Message(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Lift(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Log(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lean_Data_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_EStateT(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Lift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instLTVerbosity = _init_l_Lake_instLTVerbosity();
lean_mark_persistent(l_Lake_instLTVerbosity);
l_Lake_instLEVerbosity = _init_l_Lake_instLEVerbosity();
lean_mark_persistent(l_Lake_instLEVerbosity);
l_Lake_instInhabitedVerbosity = _init_l_Lake_instInhabitedVerbosity();
l_Lake_instInhabitedLogLevel_default = _init_l_Lake_instInhabitedLogLevel_default();
l_Lake_instInhabitedLogLevel = _init_l_Lake_instInhabitedLogLevel();
l_Lake_instLTLogLevel = _init_l_Lake_instLTLogLevel();
lean_mark_persistent(l_Lake_instLTLogLevel);
l_Lake_instLELogLevel = _init_l_Lake_instLELogLevel();
lean_mark_persistent(l_Lake_instLELogLevel);
l_Lake_Log_instInhabitedPos_default = _init_l_Lake_Log_instInhabitedPos_default();
lean_mark_persistent(l_Lake_Log_instInhabitedPos_default);
l_Lake_Log_instInhabitedPos = _init_l_Lake_Log_instInhabitedPos();
lean_mark_persistent(l_Lake_Log_instInhabitedPos);
l_Lake_instOfNatPos = _init_l_Lake_instOfNatPos();
lean_mark_persistent(l_Lake_instOfNatPos);
l_Lake_instLTPos = _init_l_Lake_instLTPos();
lean_mark_persistent(l_Lake_instLTPos);
l_Lake_instLEPos = _init_l_Lake_instLEPos();
lean_mark_persistent(l_Lake_instLEPos);
l_Lake_LoggerIO_instMonadLiftLogIO = _init_l_Lake_LoggerIO_instMonadLiftLogIO();
lean_mark_persistent(l_Lake_LoggerIO_instMonadLiftLogIO);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Log(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Json(uint8_t builtin);
lean_object* initialize_Lake_Util_Error(uint8_t builtin);
lean_object* initialize_Lake_Util_EStateT(uint8_t builtin);
lean_object* initialize_Lean_Message(uint8_t builtin);
lean_object* initialize_Lake_Util_Lift(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Modify(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Log(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_EStateT(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Lift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Log(builtin);
}
#ifdef __cplusplus
}
#endif
