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
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*);
lean_object* l_Lean_mkErrorStringWithPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lake_EResult_result_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_get_stdout();
lean_object* lean_get_stderr();
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorIdx___impl___boxed(lean_object*);
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
lean_object* l_Lake_Verbosity_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lake_Verbosity_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lake_Verbosity_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lake_Verbosity_ctorIdx___impl(v_x_4__boxed_6_);
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
lean_object* l_Lake_Verbosity_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lake_Verbosity_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lake_Verbosity_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lake_Verbosity_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_quiet_elim___redArg(lean_object* v_quiet_24_){
_start:
{
lean_inc(v_quiet_24_);
return v_quiet_24_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_quiet_elim___redArg___boxed(lean_object* v_quiet_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lake_Verbosity_quiet_elim___redArg(v_quiet_25_);
lean_dec(v_quiet_25_);
return v_res_26_;
}
}
lean_object* l_Lake_Verbosity_quiet_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_quiet_30_){
_start:
{
lean_inc(v_quiet_30_);
return v_quiet_30_;
}
}
LEAN_EXPORT void l_Lake_Verbosity_quiet_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_quiet_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lake_Verbosity_quiet_elim(lean_box(0), v_t_28_, lean_box(0), v_quiet_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_quiet_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_quiet_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lake_Verbosity_quiet_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_quiet_35_);
lean_dec(v_quiet_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_normal_elim___redArg(lean_object* v_normal_38_){
_start:
{
lean_inc(v_normal_38_);
return v_normal_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_normal_elim___redArg___boxed(lean_object* v_normal_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lake_Verbosity_normal_elim___redArg(v_normal_39_);
lean_dec(v_normal_39_);
return v_res_40_;
}
}
lean_object* l_Lake_Verbosity_normal_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_normal_44_){
_start:
{
lean_inc(v_normal_44_);
return v_normal_44_;
}
}
LEAN_EXPORT void l_Lake_Verbosity_normal_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_normal_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lake_Verbosity_normal_elim(lean_box(0), v_t_42_, lean_box(0), v_normal_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_normal_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_normal_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lake_Verbosity_normal_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_normal_49_);
lean_dec(v_normal_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_verbose_elim___redArg(lean_object* v_verbose_52_){
_start:
{
lean_inc(v_verbose_52_);
return v_verbose_52_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_verbose_elim___redArg___boxed(lean_object* v_verbose_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lake_Verbosity_verbose_elim___redArg(v_verbose_53_);
lean_dec(v_verbose_53_);
return v_res_54_;
}
}
lean_object* l_Lake_Verbosity_verbose_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_verbose_58_){
_start:
{
lean_inc(v_verbose_58_);
return v_verbose_58_;
}
}
LEAN_EXPORT void l_Lake_Verbosity_verbose_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_verbose_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lake_Verbosity_verbose_elim(lean_box(0), v_t_56_, lean_box(0), v_verbose_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_verbose_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_verbose_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Lake_Verbosity_verbose_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_verbose_63_);
lean_dec(v_verbose_63_);
return v_res_65_;
}
}
static lean_object* _init_l_Lake_instReprVerbosity_repr___closed__6(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_unsigned_to_nat(2u);
v___x_76_ = lean_nat_to_int(v___x_75_);
return v___x_76_;
}
}
static lean_object* _init_l_Lake_instReprVerbosity_repr___closed__7(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_to_int(v___x_77_);
return v___x_78_;
}
}
lean_object* l_Lake_instReprVerbosity_repr(uint8_t v_x_79_, lean_object* v_prec_80_){
_start:
{
lean_object* v___y_82_; lean_object* v___y_89_; lean_object* v___y_96_; 
switch(v_x_79_)
{
case 0:
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = lean_unsigned_to_nat(1024u);
v___x_103_ = lean_nat_dec_le(v___x_102_, v_prec_80_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; 
v___x_104_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_82_ = v___x_104_;
goto v___jp_81_;
}
else
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_82_ = v___x_105_;
goto v___jp_81_;
}
}
case 1:
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = lean_unsigned_to_nat(1024u);
v___x_107_ = lean_nat_dec_le(v___x_106_, v_prec_80_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_89_ = v___x_108_;
goto v___jp_88_;
}
else
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_89_ = v___x_109_;
goto v___jp_88_;
}
}
default: 
{
lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_110_ = lean_unsigned_to_nat(1024u);
v___x_111_ = lean_nat_dec_le(v___x_110_, v_prec_80_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; 
v___x_112_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_96_ = v___x_112_;
goto v___jp_95_;
}
else
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_96_ = v___x_113_;
goto v___jp_95_;
}
}
}
v___jp_81_:
{
lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_83_ = ((lean_object*)(l_Lake_instReprVerbosity_repr___closed__1));
lean_inc(v___y_82_);
v___x_84_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_84_, 0, v___y_82_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = 0;
v___x_86_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_86_, 0, v___x_84_);
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*1, v___x_85_);
v___x_87_ = l_Repr_addAppParen(v___x_86_, v_prec_80_);
return v___x_87_;
}
v___jp_88_:
{
lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_90_ = ((lean_object*)(l_Lake_instReprVerbosity_repr___closed__3));
lean_inc(v___y_89_);
v___x_91_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_91_, 0, v___y_89_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = 0;
v___x_93_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_93_, 0, v___x_91_);
lean_ctor_set_uint8(v___x_93_, sizeof(void*)*1, v___x_92_);
v___x_94_ = l_Repr_addAppParen(v___x_93_, v_prec_80_);
return v___x_94_;
}
v___jp_95_:
{
lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_97_ = ((lean_object*)(l_Lake_instReprVerbosity_repr___closed__5));
lean_inc(v___y_96_);
v___x_98_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_98_, 0, v___y_96_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
v___x_99_ = 0;
v___x_100_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_100_, 0, v___x_98_);
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*1, v___x_99_);
v___x_101_ = l_Repr_addAppParen(v___x_100_, v_prec_80_);
return v___x_101_;
}
}
}
LEAN_EXPORT void l_Lake_instReprVerbosity_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_79_ = stack[0].m_num;
lean_object* v_prec_80_ = stack[1].m_obj;
lean_object* v_res_114_;
v_res_114_ = l_Lake_instReprVerbosity_repr(v_x_79_, v_prec_80_);
stack->m_obj
 = v_res_114_;
}
LEAN_EXPORT lean_object* l_Lake_instReprVerbosity_repr___boxed(lean_object* v_x_115_, lean_object* v_prec_116_){
_start:
{
uint8_t v_x_171__boxed_117_; lean_object* v_res_118_; 
v_x_171__boxed_117_ = lean_unbox(v_x_115_);
v_res_118_ = l_Lake_instReprVerbosity_repr(v_x_171__boxed_117_, v_prec_116_);
lean_dec(v_prec_116_);
return v_res_118_;
}
}
uint8_t l_Lake_Verbosity_ofNat(lean_object* v_n_121_){
_start:
{
lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = lean_nat_dec_le(v_n_121_, v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(1u);
v___x_125_ = lean_nat_dec_le(v_n_121_, v___x_124_);
if (v___x_125_ == 0)
{
uint8_t v___x_126_; 
v___x_126_ = 2;
return v___x_126_;
}
else
{
uint8_t v___x_127_; 
v___x_127_ = 1;
return v___x_127_;
}
}
else
{
uint8_t v___x_128_; 
v___x_128_ = 0;
return v___x_128_;
}
}
}
LEAN_EXPORT void l_Lake_Verbosity_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_121_ = stack[0].m_obj;
uint8_t v_res_129_;
v_res_129_ = l_Lake_Verbosity_ofNat(v_n_121_);
stack->m_num = v_res_129_;
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_ofNat___boxed(lean_object* v_n_130_){
_start:
{
uint8_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = l_Lake_Verbosity_ofNat(v_n_130_);
lean_dec(v_n_130_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t v_x_133_, uint8_t v_y_134_){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_135_ = lean_box(v_x_133_);
v___x_136_ = lean_obj_tag_nat(v___x_135_);
lean_dec(v___x_135_);
v___x_137_ = lean_box(v_y_134_);
v___x_138_ = lean_obj_tag_nat(v___x_137_);
lean_dec(v___x_137_);
v___x_139_ = lean_nat_dec_eq(v___x_136_, v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT void l_Lake_instDecidableEqVerbosity_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_133_ = stack[0].m_num;
uint8_t v_y_134_ = stack[1].m_num;
uint8_t v_res_140_;
v_res_140_ = l_Lake_instDecidableEqVerbosity(v_x_133_, v_y_134_);
stack->m_num = v_res_140_;
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqVerbosity___boxed(lean_object* v_x_141_, lean_object* v_y_142_){
_start:
{
uint8_t v_x_23__boxed_143_; uint8_t v_y_24__boxed_144_; uint8_t v_res_145_; lean_object* v_r_146_; 
v_x_23__boxed_143_ = lean_unbox(v_x_141_);
v_y_24__boxed_144_ = lean_unbox(v_y_142_);
v_res_145_ = l_Lake_instDecidableEqVerbosity(v_x_23__boxed_143_, v_y_24__boxed_144_);
v_r_146_ = lean_box(v_res_145_);
return v_r_146_;
}
}
uint8_t l_Lake_instOrdVerbosity_ord(uint8_t v_x_147_, uint8_t v_y_148_){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_149_ = lean_box(v_x_147_);
v___x_150_ = lean_obj_tag_nat(v___x_149_);
lean_dec(v___x_149_);
v___x_151_ = lean_box(v_y_148_);
v___x_152_ = lean_obj_tag_nat(v___x_151_);
lean_dec(v___x_151_);
v___x_153_ = lean_nat_dec_lt(v___x_150_, v___x_152_);
if (v___x_153_ == 0)
{
uint8_t v___x_154_; 
v___x_154_ = lean_nat_dec_eq(v___x_150_, v___x_152_);
if (v___x_154_ == 0)
{
uint8_t v___x_155_; 
v___x_155_ = 2;
return v___x_155_;
}
else
{
uint8_t v___x_156_; 
v___x_156_ = 1;
return v___x_156_;
}
}
else
{
uint8_t v___x_157_; 
v___x_157_ = 0;
return v___x_157_;
}
}
}
LEAN_EXPORT void l_Lake_instOrdVerbosity_ord_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_147_ = stack[0].m_num;
uint8_t v_y_148_ = stack[1].m_num;
uint8_t v_res_158_;
v_res_158_ = l_Lake_instOrdVerbosity_ord(v_x_147_, v_y_148_);
stack->m_num = v_res_158_;
}
LEAN_EXPORT lean_object* l_Lake_instOrdVerbosity_ord___boxed(lean_object* v_x_159_, lean_object* v_y_160_){
_start:
{
uint8_t v_x_33__boxed_161_; uint8_t v_y_34__boxed_162_; uint8_t v_res_163_; lean_object* v_r_164_; 
v_x_33__boxed_161_ = lean_unbox(v_x_159_);
v_y_34__boxed_162_ = lean_unbox(v_y_160_);
v_res_163_ = l_Lake_instOrdVerbosity_ord(v_x_33__boxed_161_, v_y_34__boxed_162_);
v_r_164_ = lean_box(v_res_163_);
return v_r_164_;
}
}
static lean_object* _init_l_Lake_instLTVerbosity(void){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_box(0);
return v___x_167_;
}
}
static lean_object* _init_l_Lake_instLEVerbosity(void){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = lean_box(0);
return v___x_168_;
}
}
uint8_t l_Lake_instMinVerbosity___lam__0(uint8_t v_x_169_, uint8_t v_y_170_){
_start:
{
uint8_t v___x_171_; 
v___x_171_ = l_Lake_instOrdVerbosity_ord(v_x_169_, v_y_170_);
if (v___x_171_ == 2)
{
return v_y_170_;
}
else
{
return v_x_169_;
}
}
}
LEAN_EXPORT void l_Lake_instMinVerbosity___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_169_ = stack[0].m_num;
uint8_t v_y_170_ = stack[1].m_num;
uint8_t v_res_172_;
v_res_172_ = l_Lake_instMinVerbosity___lam__0(v_x_169_, v_y_170_);
stack->m_num = v_res_172_;
}
LEAN_EXPORT lean_object* l_Lake_instMinVerbosity___lam__0___boxed(lean_object* v_x_173_, lean_object* v_y_174_){
_start:
{
uint8_t v_x_boxed_175_; uint8_t v_y_boxed_176_; uint8_t v_res_177_; lean_object* v_r_178_; 
v_x_boxed_175_ = lean_unbox(v_x_173_);
v_y_boxed_176_ = lean_unbox(v_y_174_);
v_res_177_ = l_Lake_instMinVerbosity___lam__0(v_x_boxed_175_, v_y_boxed_176_);
v_r_178_ = lean_box(v_res_177_);
return v_r_178_;
}
}
uint8_t l_Lake_instMaxVerbosity___lam__0(uint8_t v_x_181_, uint8_t v_y_182_){
_start:
{
uint8_t v___x_183_; 
v___x_183_ = l_Lake_instOrdVerbosity_ord(v_x_181_, v_y_182_);
if (v___x_183_ == 2)
{
return v_x_181_;
}
else
{
return v_y_182_;
}
}
}
LEAN_EXPORT void l_Lake_instMaxVerbosity___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_181_ = stack[0].m_num;
uint8_t v_y_182_ = stack[1].m_num;
uint8_t v_res_184_;
v_res_184_ = l_Lake_instMaxVerbosity___lam__0(v_x_181_, v_y_182_);
stack->m_num = v_res_184_;
}
LEAN_EXPORT lean_object* l_Lake_instMaxVerbosity___lam__0___boxed(lean_object* v_x_185_, lean_object* v_y_186_){
_start:
{
uint8_t v_x_boxed_187_; uint8_t v_y_boxed_188_; uint8_t v_res_189_; lean_object* v_r_190_; 
v_x_boxed_187_ = lean_unbox(v_x_185_);
v_y_boxed_188_ = lean_unbox(v_y_186_);
v_res_189_ = l_Lake_instMaxVerbosity___lam__0(v_x_boxed_187_, v_y_boxed_188_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
static uint8_t _init_l_Lake_instInhabitedVerbosity(void){
_start:
{
uint8_t v___x_193_; 
v___x_193_ = 1;
return v___x_193_;
}
}
lean_object* l_Lake_AnsiMode_ctorIdx___impl(uint8_t v_x_194_){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_box(v_x_194_);
v___x_196_ = lean_obj_tag_nat(v___x_195_);
lean_dec(v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT void l_Lake_AnsiMode_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_194_ = stack[0].m_num;
lean_object* v_res_197_;
v_res_197_ = l_Lake_AnsiMode_ctorIdx___impl(v_x_194_);
stack->m_obj
 = v_res_197_;
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorIdx___impl___boxed(lean_object* v_x_198_){
_start:
{
uint8_t v_x_4__boxed_199_; lean_object* v_res_200_; 
v_x_4__boxed_199_ = lean_unbox(v_x_198_);
v_res_200_ = l_Lake_AnsiMode_ctorIdx___impl(v_x_4__boxed_199_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorElim___redArg(lean_object* v_k_201_){
_start:
{
lean_inc(v_k_201_);
return v_k_201_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorElim___redArg___boxed(lean_object* v_k_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lake_AnsiMode_ctorElim___redArg(v_k_202_);
lean_dec(v_k_202_);
return v_res_203_;
}
}
lean_object* l_Lake_AnsiMode_ctorElim(lean_object* v_motive_204_, lean_object* v_ctorIdx_205_, uint8_t v_t_206_, lean_object* v_h_207_, lean_object* v_k_208_){
_start:
{
lean_inc(v_k_208_);
return v_k_208_;
}
}
LEAN_EXPORT void l_Lake_AnsiMode_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_205_ = stack[1].m_obj;
uint8_t v_t_206_ = stack[2].m_num;
lean_object* v_k_208_ = stack[4].m_obj;
lean_object* v_res_209_;
v_res_209_ = l_Lake_AnsiMode_ctorElim(lean_box(0), v_ctorIdx_205_, v_t_206_, lean_box(0), v_k_208_);
stack->m_obj
 = v_res_209_;
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorElim___boxed(lean_object* v_motive_210_, lean_object* v_ctorIdx_211_, lean_object* v_t_212_, lean_object* v_h_213_, lean_object* v_k_214_){
_start:
{
uint8_t v_t_boxed_215_; lean_object* v_res_216_; 
v_t_boxed_215_ = lean_unbox(v_t_212_);
v_res_216_ = l_Lake_AnsiMode_ctorElim(v_motive_210_, v_ctorIdx_211_, v_t_boxed_215_, v_h_213_, v_k_214_);
lean_dec(v_k_214_);
lean_dec(v_ctorIdx_211_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_auto_elim___redArg(lean_object* v_auto_217_){
_start:
{
lean_inc(v_auto_217_);
return v_auto_217_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_auto_elim___redArg___boxed(lean_object* v_auto_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lake_AnsiMode_auto_elim___redArg(v_auto_218_);
lean_dec(v_auto_218_);
return v_res_219_;
}
}
lean_object* l_Lake_AnsiMode_auto_elim(lean_object* v_motive_220_, uint8_t v_t_221_, lean_object* v_h_222_, lean_object* v_auto_223_){
_start:
{
lean_inc(v_auto_223_);
return v_auto_223_;
}
}
LEAN_EXPORT void l_Lake_AnsiMode_auto_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_221_ = stack[1].m_num;
lean_object* v_auto_223_ = stack[3].m_obj;
lean_object* v_res_224_;
v_res_224_ = l_Lake_AnsiMode_auto_elim(lean_box(0), v_t_221_, lean_box(0), v_auto_223_);
stack->m_obj
 = v_res_224_;
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_auto_elim___boxed(lean_object* v_motive_225_, lean_object* v_t_226_, lean_object* v_h_227_, lean_object* v_auto_228_){
_start:
{
uint8_t v_t_boxed_229_; lean_object* v_res_230_; 
v_t_boxed_229_ = lean_unbox(v_t_226_);
v_res_230_ = l_Lake_AnsiMode_auto_elim(v_motive_225_, v_t_boxed_229_, v_h_227_, v_auto_228_);
lean_dec(v_auto_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ansi_elim___redArg(lean_object* v_ansi_231_){
_start:
{
lean_inc(v_ansi_231_);
return v_ansi_231_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ansi_elim___redArg___boxed(lean_object* v_ansi_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lake_AnsiMode_ansi_elim___redArg(v_ansi_232_);
lean_dec(v_ansi_232_);
return v_res_233_;
}
}
lean_object* l_Lake_AnsiMode_ansi_elim(lean_object* v_motive_234_, uint8_t v_t_235_, lean_object* v_h_236_, lean_object* v_ansi_237_){
_start:
{
lean_inc(v_ansi_237_);
return v_ansi_237_;
}
}
LEAN_EXPORT void l_Lake_AnsiMode_ansi_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_235_ = stack[1].m_num;
lean_object* v_ansi_237_ = stack[3].m_obj;
lean_object* v_res_238_;
v_res_238_ = l_Lake_AnsiMode_ansi_elim(lean_box(0), v_t_235_, lean_box(0), v_ansi_237_);
stack->m_obj
 = v_res_238_;
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ansi_elim___boxed(lean_object* v_motive_239_, lean_object* v_t_240_, lean_object* v_h_241_, lean_object* v_ansi_242_){
_start:
{
uint8_t v_t_boxed_243_; lean_object* v_res_244_; 
v_t_boxed_243_ = lean_unbox(v_t_240_);
v_res_244_ = l_Lake_AnsiMode_ansi_elim(v_motive_239_, v_t_boxed_243_, v_h_241_, v_ansi_242_);
lean_dec(v_ansi_242_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noAnsi_elim___redArg(lean_object* v_noAnsi_245_){
_start:
{
lean_inc(v_noAnsi_245_);
return v_noAnsi_245_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noAnsi_elim___redArg___boxed(lean_object* v_noAnsi_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lake_AnsiMode_noAnsi_elim___redArg(v_noAnsi_246_);
lean_dec(v_noAnsi_246_);
return v_res_247_;
}
}
lean_object* l_Lake_AnsiMode_noAnsi_elim(lean_object* v_motive_248_, uint8_t v_t_249_, lean_object* v_h_250_, lean_object* v_noAnsi_251_){
_start:
{
lean_inc(v_noAnsi_251_);
return v_noAnsi_251_;
}
}
LEAN_EXPORT void l_Lake_AnsiMode_noAnsi_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_249_ = stack[1].m_num;
lean_object* v_noAnsi_251_ = stack[3].m_obj;
lean_object* v_res_252_;
v_res_252_ = l_Lake_AnsiMode_noAnsi_elim(lean_box(0), v_t_249_, lean_box(0), v_noAnsi_251_);
stack->m_obj
 = v_res_252_;
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noAnsi_elim___boxed(lean_object* v_motive_253_, lean_object* v_t_254_, lean_object* v_h_255_, lean_object* v_noAnsi_256_){
_start:
{
uint8_t v_t_boxed_257_; lean_object* v_res_258_; 
v_t_boxed_257_ = lean_unbox(v_t_254_);
v_res_258_ = l_Lake_AnsiMode_noAnsi_elim(v_motive_253_, v_t_boxed_257_, v_h_255_, v_noAnsi_256_);
lean_dec(v_noAnsi_256_);
return v_res_258_;
}
}
lean_object* l_Lake_instReprAnsiMode_repr(uint8_t v_x_268_, lean_object* v_prec_269_){
_start:
{
lean_object* v___y_271_; lean_object* v___y_278_; lean_object* v___y_285_; 
switch(v_x_268_)
{
case 0:
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = lean_unsigned_to_nat(1024u);
v___x_292_ = lean_nat_dec_le(v___x_291_, v_prec_269_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; 
v___x_293_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_271_ = v___x_293_;
goto v___jp_270_;
}
else
{
lean_object* v___x_294_; 
v___x_294_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_271_ = v___x_294_;
goto v___jp_270_;
}
}
case 1:
{
lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = lean_unsigned_to_nat(1024u);
v___x_296_ = lean_nat_dec_le(v___x_295_, v_prec_269_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; 
v___x_297_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_278_ = v___x_297_;
goto v___jp_277_;
}
else
{
lean_object* v___x_298_; 
v___x_298_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_278_ = v___x_298_;
goto v___jp_277_;
}
}
default: 
{
lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_299_ = lean_unsigned_to_nat(1024u);
v___x_300_ = lean_nat_dec_le(v___x_299_, v_prec_269_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; 
v___x_301_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_285_ = v___x_301_;
goto v___jp_284_;
}
else
{
lean_object* v___x_302_; 
v___x_302_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_285_ = v___x_302_;
goto v___jp_284_;
}
}
}
v___jp_270_:
{
lean_object* v___x_272_; lean_object* v___x_273_; uint8_t v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_272_ = ((lean_object*)(l_Lake_instReprAnsiMode_repr___closed__1));
lean_inc(v___y_271_);
v___x_273_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_273_, 0, v___y_271_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
v___x_274_ = 0;
v___x_275_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_275_, 0, v___x_273_);
lean_ctor_set_uint8(v___x_275_, sizeof(void*)*1, v___x_274_);
v___x_276_ = l_Repr_addAppParen(v___x_275_, v_prec_269_);
return v___x_276_;
}
v___jp_277_:
{
lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_279_ = ((lean_object*)(l_Lake_instReprAnsiMode_repr___closed__3));
lean_inc(v___y_278_);
v___x_280_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_280_, 0, v___y_278_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = 0;
v___x_282_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_282_, 0, v___x_280_);
lean_ctor_set_uint8(v___x_282_, sizeof(void*)*1, v___x_281_);
v___x_283_ = l_Repr_addAppParen(v___x_282_, v_prec_269_);
return v___x_283_;
}
v___jp_284_:
{
lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_286_ = ((lean_object*)(l_Lake_instReprAnsiMode_repr___closed__5));
lean_inc(v___y_285_);
v___x_287_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_287_, 0, v___y_285_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = 0;
v___x_289_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_289_, 0, v___x_287_);
lean_ctor_set_uint8(v___x_289_, sizeof(void*)*1, v___x_288_);
v___x_290_ = l_Repr_addAppParen(v___x_289_, v_prec_269_);
return v___x_290_;
}
}
}
LEAN_EXPORT void l_Lake_instReprAnsiMode_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_268_ = stack[0].m_num;
lean_object* v_prec_269_ = stack[1].m_obj;
lean_object* v_res_303_;
v_res_303_ = l_Lake_instReprAnsiMode_repr(v_x_268_, v_prec_269_);
stack->m_obj
 = v_res_303_;
}
LEAN_EXPORT lean_object* l_Lake_instReprAnsiMode_repr___boxed(lean_object* v_x_304_, lean_object* v_prec_305_){
_start:
{
uint8_t v_x_167__boxed_306_; lean_object* v_res_307_; 
v_x_167__boxed_306_ = lean_unbox(v_x_304_);
v_res_307_ = l_Lake_instReprAnsiMode_repr(v_x_167__boxed_306_, v_prec_305_);
lean_dec(v_prec_305_);
return v_res_307_;
}
}
uint8_t l_Lake_AnsiMode_isEnabled(lean_object* v_out_310_, uint8_t v_x_311_){
_start:
{
switch(v_x_311_)
{
case 0:
{
lean_object* v_isTty_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v_isTty_313_ = lean_ctor_get(v_out_310_, 5);
lean_inc_ref(v_isTty_313_);
lean_dec_ref(v_out_310_);
v___x_314_ = lean_apply_1(v_isTty_313_, lean_box(0));
v___x_315_ = lean_unbox(v___x_314_);
return v___x_315_;
}
case 1:
{
uint8_t v___x_316_; 
lean_dec_ref(v_out_310_);
v___x_316_ = 1;
return v___x_316_;
}
default: 
{
uint8_t v___x_317_; 
lean_dec_ref(v_out_310_);
v___x_317_ = 0;
return v___x_317_;
}
}
}
}
LEAN_EXPORT void l_Lake_AnsiMode_isEnabled_0interp(lean_interpreter_value* stack)
{
lean_object* v_out_310_ = stack[0].m_obj;
uint8_t v_x_311_ = stack[1].m_num;
uint8_t v_res_318_;
v_res_318_ = l_Lake_AnsiMode_isEnabled(v_out_310_, v_x_311_);
stack->m_num = v_res_318_;
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_isEnabled___boxed(lean_object* v_out_319_, lean_object* v_x_320_, lean_object* v_a_321_){
_start:
{
uint8_t v_x_91__boxed_322_; uint8_t v_res_323_; lean_object* v_r_324_; 
v_x_91__boxed_322_ = lean_unbox(v_x_320_);
v_res_323_ = l_Lake_AnsiMode_isEnabled(v_out_319_, v_x_91__boxed_322_);
v_r_324_ = lean_box(v_res_323_);
return v_r_324_;
}
}
LEAN_EXPORT lean_object* l_Lake_Ansi_chalk(lean_object* v_colorCode_328_, lean_object* v_text_329_){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_330_ = ((lean_object*)(l_Lake_Ansi_chalk___closed__0));
v___x_331_ = lean_string_append(v___x_330_, v_colorCode_328_);
v___x_332_ = ((lean_object*)(l_Lake_Ansi_chalk___closed__1));
v___x_333_ = lean_string_append(v___x_331_, v___x_332_);
v___x_334_ = lean_string_append(v___x_333_, v_text_329_);
v___x_335_ = ((lean_object*)(l_Lake_Ansi_chalk___closed__2));
v___x_336_ = lean_string_append(v___x_334_, v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lake_Ansi_chalk___boxed(lean_object* v_colorCode_337_, lean_object* v_text_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lake_Ansi_chalk(v_colorCode_337_, v_text_338_);
lean_dec_ref(v_text_338_);
lean_dec_ref(v_colorCode_337_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorIdx___impl(lean_object* v_x_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = lean_obj_tag_nat(v_x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorIdx___impl___boxed(lean_object* v_x_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lake_OutStream_ctorIdx___impl(v_x_342_);
lean_dec(v_x_342_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorElim___redArg(lean_object* v_t_344_, lean_object* v_k_345_){
_start:
{
if (lean_obj_tag(v_t_344_) == 2)
{
lean_object* v_s_346_; lean_object* v___x_347_; 
v_s_346_ = lean_ctor_get(v_t_344_, 0);
lean_inc_ref(v_s_346_);
lean_dec_ref_known(v_t_344_, 1);
v___x_347_ = lean_apply_1(v_k_345_, v_s_346_);
return v___x_347_;
}
else
{
lean_dec(v_t_344_);
return v_k_345_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorElim(lean_object* v_motive_348_, lean_object* v_ctorIdx_349_, lean_object* v_t_350_, lean_object* v_h_351_, lean_object* v_k_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lake_OutStream_ctorElim___redArg(v_t_350_, v_k_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorElim___boxed(lean_object* v_motive_354_, lean_object* v_ctorIdx_355_, lean_object* v_t_356_, lean_object* v_h_357_, lean_object* v_k_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lake_OutStream_ctorElim(v_motive_354_, v_ctorIdx_355_, v_t_356_, v_h_357_, v_k_358_);
lean_dec(v_ctorIdx_355_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_stdout_elim___redArg(lean_object* v_t_360_, lean_object* v_stdout_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lake_OutStream_ctorElim___redArg(v_t_360_, v_stdout_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_stdout_elim(lean_object* v_motive_363_, lean_object* v_t_364_, lean_object* v_h_365_, lean_object* v_stdout_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lake_OutStream_ctorElim___redArg(v_t_364_, v_stdout_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_stderr_elim___redArg(lean_object* v_t_368_, lean_object* v_stderr_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lake_OutStream_ctorElim___redArg(v_t_368_, v_stderr_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_stderr_elim(lean_object* v_motive_371_, lean_object* v_t_372_, lean_object* v_h_373_, lean_object* v_stderr_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lake_OutStream_ctorElim___redArg(v_t_372_, v_stderr_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_stream_elim___redArg(lean_object* v_t_376_, lean_object* v_stream_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lake_OutStream_ctorElim___redArg(v_t_376_, v_stream_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_stream_elim(lean_object* v_motive_379_, lean_object* v_t_380_, lean_object* v_h_381_, lean_object* v_stream_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lake_OutStream_ctorElim___redArg(v_t_380_, v_stream_382_);
return v___x_383_;
}
}
lean_object* l_Lake_OutStream_get(lean_object* v_x_384_){
_start:
{
switch(lean_obj_tag(v_x_384_))
{
case 0:
{
lean_object* v___x_386_; 
v___x_386_ = lean_get_stdout();
return v___x_386_;
}
case 1:
{
lean_object* v___x_387_; 
v___x_387_ = lean_get_stderr();
return v___x_387_;
}
default: 
{
lean_object* v_s_388_; 
v_s_388_ = lean_ctor_get(v_x_384_, 0);
lean_inc_ref(v_s_388_);
return v_s_388_;
}
}
}
}
LEAN_EXPORT void l_Lake_OutStream_get_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_384_ = stack[0].m_obj;
lean_object* v_res_389_;
v_res_389_ = l_Lake_OutStream_get(v_x_384_);
stack->m_obj
 = v_res_389_;
}
LEAN_EXPORT lean_object* l_Lake_OutStream_get___boxed(lean_object* v_x_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lake_OutStream_get(v_x_390_);
lean_dec(v_x_390_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeStreamOutStream___lam__0(lean_object* v_s_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_394_, 0, v_s_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeHandleOutStream___lam__0(lean_object* v_h_397_){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = lean_stream_of_handle(v_h_397_);
v___x_399_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
return v___x_399_;
}
}
lean_object* l_Lake_LogLevel_ctorIdx___impl(uint8_t v_x_402_){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_box(v_x_402_);
v___x_404_ = lean_obj_tag_nat(v___x_403_);
lean_dec(v___x_403_);
return v___x_404_;
}
}
LEAN_EXPORT void l_Lake_LogLevel_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_402_ = stack[0].m_num;
lean_object* v_res_405_;
v_res_405_ = l_Lake_LogLevel_ctorIdx___impl(v_x_402_);
stack->m_obj
 = v_res_405_;
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorIdx___impl___boxed(lean_object* v_x_406_){
_start:
{
uint8_t v_x_4__boxed_407_; lean_object* v_res_408_; 
v_x_4__boxed_407_ = lean_unbox(v_x_406_);
v_res_408_ = l_Lake_LogLevel_ctorIdx___impl(v_x_4__boxed_407_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorElim___redArg(lean_object* v_k_409_){
_start:
{
lean_inc(v_k_409_);
return v_k_409_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorElim___redArg___boxed(lean_object* v_k_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lake_LogLevel_ctorElim___redArg(v_k_410_);
lean_dec(v_k_410_);
return v_res_411_;
}
}
lean_object* l_Lake_LogLevel_ctorElim(lean_object* v_motive_412_, lean_object* v_ctorIdx_413_, uint8_t v_t_414_, lean_object* v_h_415_, lean_object* v_k_416_){
_start:
{
lean_inc(v_k_416_);
return v_k_416_;
}
}
LEAN_EXPORT void l_Lake_LogLevel_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_413_ = stack[1].m_obj;
uint8_t v_t_414_ = stack[2].m_num;
lean_object* v_k_416_ = stack[4].m_obj;
lean_object* v_res_417_;
v_res_417_ = l_Lake_LogLevel_ctorElim(lean_box(0), v_ctorIdx_413_, v_t_414_, lean_box(0), v_k_416_);
stack->m_obj
 = v_res_417_;
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorElim___boxed(lean_object* v_motive_418_, lean_object* v_ctorIdx_419_, lean_object* v_t_420_, lean_object* v_h_421_, lean_object* v_k_422_){
_start:
{
uint8_t v_t_boxed_423_; lean_object* v_res_424_; 
v_t_boxed_423_ = lean_unbox(v_t_420_);
v_res_424_ = l_Lake_LogLevel_ctorElim(v_motive_418_, v_ctorIdx_419_, v_t_boxed_423_, v_h_421_, v_k_422_);
lean_dec(v_k_422_);
lean_dec(v_ctorIdx_419_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_trace_elim___redArg(lean_object* v_trace_425_){
_start:
{
lean_inc(v_trace_425_);
return v_trace_425_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_trace_elim___redArg___boxed(lean_object* v_trace_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lake_LogLevel_trace_elim___redArg(v_trace_426_);
lean_dec(v_trace_426_);
return v_res_427_;
}
}
lean_object* l_Lake_LogLevel_trace_elim(lean_object* v_motive_428_, uint8_t v_t_429_, lean_object* v_h_430_, lean_object* v_trace_431_){
_start:
{
lean_inc(v_trace_431_);
return v_trace_431_;
}
}
LEAN_EXPORT void l_Lake_LogLevel_trace_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_429_ = stack[1].m_num;
lean_object* v_trace_431_ = stack[3].m_obj;
lean_object* v_res_432_;
v_res_432_ = l_Lake_LogLevel_trace_elim(lean_box(0), v_t_429_, lean_box(0), v_trace_431_);
stack->m_obj
 = v_res_432_;
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_trace_elim___boxed(lean_object* v_motive_433_, lean_object* v_t_434_, lean_object* v_h_435_, lean_object* v_trace_436_){
_start:
{
uint8_t v_t_boxed_437_; lean_object* v_res_438_; 
v_t_boxed_437_ = lean_unbox(v_t_434_);
v_res_438_ = l_Lake_LogLevel_trace_elim(v_motive_433_, v_t_boxed_437_, v_h_435_, v_trace_436_);
lean_dec(v_trace_436_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_info_elim___redArg(lean_object* v_info_439_){
_start:
{
lean_inc(v_info_439_);
return v_info_439_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_info_elim___redArg___boxed(lean_object* v_info_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lake_LogLevel_info_elim___redArg(v_info_440_);
lean_dec(v_info_440_);
return v_res_441_;
}
}
lean_object* l_Lake_LogLevel_info_elim(lean_object* v_motive_442_, uint8_t v_t_443_, lean_object* v_h_444_, lean_object* v_info_445_){
_start:
{
lean_inc(v_info_445_);
return v_info_445_;
}
}
LEAN_EXPORT void l_Lake_LogLevel_info_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_443_ = stack[1].m_num;
lean_object* v_info_445_ = stack[3].m_obj;
lean_object* v_res_446_;
v_res_446_ = l_Lake_LogLevel_info_elim(lean_box(0), v_t_443_, lean_box(0), v_info_445_);
stack->m_obj
 = v_res_446_;
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_info_elim___boxed(lean_object* v_motive_447_, lean_object* v_t_448_, lean_object* v_h_449_, lean_object* v_info_450_){
_start:
{
uint8_t v_t_boxed_451_; lean_object* v_res_452_; 
v_t_boxed_451_ = lean_unbox(v_t_448_);
v_res_452_ = l_Lake_LogLevel_info_elim(v_motive_447_, v_t_boxed_451_, v_h_449_, v_info_450_);
lean_dec(v_info_450_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_warning_elim___redArg(lean_object* v_warning_453_){
_start:
{
lean_inc(v_warning_453_);
return v_warning_453_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_warning_elim___redArg___boxed(lean_object* v_warning_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lake_LogLevel_warning_elim___redArg(v_warning_454_);
lean_dec(v_warning_454_);
return v_res_455_;
}
}
lean_object* l_Lake_LogLevel_warning_elim(lean_object* v_motive_456_, uint8_t v_t_457_, lean_object* v_h_458_, lean_object* v_warning_459_){
_start:
{
lean_inc(v_warning_459_);
return v_warning_459_;
}
}
LEAN_EXPORT void l_Lake_LogLevel_warning_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_457_ = stack[1].m_num;
lean_object* v_warning_459_ = stack[3].m_obj;
lean_object* v_res_460_;
v_res_460_ = l_Lake_LogLevel_warning_elim(lean_box(0), v_t_457_, lean_box(0), v_warning_459_);
stack->m_obj
 = v_res_460_;
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_warning_elim___boxed(lean_object* v_motive_461_, lean_object* v_t_462_, lean_object* v_h_463_, lean_object* v_warning_464_){
_start:
{
uint8_t v_t_boxed_465_; lean_object* v_res_466_; 
v_t_boxed_465_ = lean_unbox(v_t_462_);
v_res_466_ = l_Lake_LogLevel_warning_elim(v_motive_461_, v_t_boxed_465_, v_h_463_, v_warning_464_);
lean_dec(v_warning_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_error_elim___redArg(lean_object* v_error_467_){
_start:
{
lean_inc(v_error_467_);
return v_error_467_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_error_elim___redArg___boxed(lean_object* v_error_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lake_LogLevel_error_elim___redArg(v_error_468_);
lean_dec(v_error_468_);
return v_res_469_;
}
}
lean_object* l_Lake_LogLevel_error_elim(lean_object* v_motive_470_, uint8_t v_t_471_, lean_object* v_h_472_, lean_object* v_error_473_){
_start:
{
lean_inc(v_error_473_);
return v_error_473_;
}
}
LEAN_EXPORT void l_Lake_LogLevel_error_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_471_ = stack[1].m_num;
lean_object* v_error_473_ = stack[3].m_obj;
lean_object* v_res_474_;
v_res_474_ = l_Lake_LogLevel_error_elim(lean_box(0), v_t_471_, lean_box(0), v_error_473_);
stack->m_obj
 = v_res_474_;
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_error_elim___boxed(lean_object* v_motive_475_, lean_object* v_t_476_, lean_object* v_h_477_, lean_object* v_error_478_){
_start:
{
uint8_t v_t_boxed_479_; lean_object* v_res_480_; 
v_t_boxed_479_ = lean_unbox(v_t_476_);
v_res_480_ = l_Lake_LogLevel_error_elim(v_motive_475_, v_t_boxed_479_, v_h_477_, v_error_478_);
lean_dec(v_error_478_);
return v_res_480_;
}
}
static uint8_t _init_l_Lake_instInhabitedLogLevel_default(void){
_start:
{
uint8_t v___x_481_; 
v___x_481_ = 0;
return v___x_481_;
}
}
static uint8_t _init_l_Lake_instInhabitedLogLevel(void){
_start:
{
uint8_t v___x_482_; 
v___x_482_ = 0;
return v___x_482_;
}
}
lean_object* l_Lake_instReprLogLevel_repr(uint8_t v_x_495_, lean_object* v_prec_496_){
_start:
{
lean_object* v___y_498_; lean_object* v___y_505_; lean_object* v___y_512_; lean_object* v___y_519_; 
switch(v_x_495_)
{
case 0:
{
lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_525_ = lean_unsigned_to_nat(1024u);
v___x_526_ = lean_nat_dec_le(v___x_525_, v_prec_496_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; 
v___x_527_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_498_ = v___x_527_;
goto v___jp_497_;
}
else
{
lean_object* v___x_528_; 
v___x_528_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_498_ = v___x_528_;
goto v___jp_497_;
}
}
case 1:
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = lean_unsigned_to_nat(1024u);
v___x_530_ = lean_nat_dec_le(v___x_529_, v_prec_496_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; 
v___x_531_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_505_ = v___x_531_;
goto v___jp_504_;
}
else
{
lean_object* v___x_532_; 
v___x_532_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_505_ = v___x_532_;
goto v___jp_504_;
}
}
case 2:
{
lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = lean_unsigned_to_nat(1024u);
v___x_534_ = lean_nat_dec_le(v___x_533_, v_prec_496_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; 
v___x_535_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_512_ = v___x_535_;
goto v___jp_511_;
}
else
{
lean_object* v___x_536_; 
v___x_536_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_512_ = v___x_536_;
goto v___jp_511_;
}
}
default: 
{
lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_537_ = lean_unsigned_to_nat(1024u);
v___x_538_ = lean_nat_dec_le(v___x_537_, v_prec_496_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; 
v___x_539_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_519_ = v___x_539_;
goto v___jp_518_;
}
else
{
lean_object* v___x_540_; 
v___x_540_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_519_ = v___x_540_;
goto v___jp_518_;
}
}
}
v___jp_497_:
{
lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_499_ = ((lean_object*)(l_Lake_instReprLogLevel_repr___closed__1));
lean_inc(v___y_498_);
v___x_500_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_500_, 0, v___y_498_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
v___x_501_ = 0;
v___x_502_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_502_, 0, v___x_500_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*1, v___x_501_);
v___x_503_ = l_Repr_addAppParen(v___x_502_, v_prec_496_);
return v___x_503_;
}
v___jp_504_:
{
lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_506_ = ((lean_object*)(l_Lake_instReprLogLevel_repr___closed__3));
lean_inc(v___y_505_);
v___x_507_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_507_, 0, v___y_505_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
v___x_508_ = 0;
v___x_509_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_509_, 0, v___x_507_);
lean_ctor_set_uint8(v___x_509_, sizeof(void*)*1, v___x_508_);
v___x_510_ = l_Repr_addAppParen(v___x_509_, v_prec_496_);
return v___x_510_;
}
v___jp_511_:
{
lean_object* v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_513_ = ((lean_object*)(l_Lake_instReprLogLevel_repr___closed__5));
lean_inc(v___y_512_);
v___x_514_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_514_, 0, v___y_512_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
v___x_515_ = 0;
v___x_516_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_516_, 0, v___x_514_);
lean_ctor_set_uint8(v___x_516_, sizeof(void*)*1, v___x_515_);
v___x_517_ = l_Repr_addAppParen(v___x_516_, v_prec_496_);
return v___x_517_;
}
v___jp_518_:
{
lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_520_ = ((lean_object*)(l_Lake_instReprLogLevel_repr___closed__7));
lean_inc(v___y_519_);
v___x_521_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_521_, 0, v___y_519_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = 0;
v___x_523_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_523_, 0, v___x_521_);
lean_ctor_set_uint8(v___x_523_, sizeof(void*)*1, v___x_522_);
v___x_524_ = l_Repr_addAppParen(v___x_523_, v_prec_496_);
return v___x_524_;
}
}
}
LEAN_EXPORT void l_Lake_instReprLogLevel_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_495_ = stack[0].m_num;
lean_object* v_prec_496_ = stack[1].m_obj;
lean_object* v_res_541_;
v_res_541_ = l_Lake_instReprLogLevel_repr(v_x_495_, v_prec_496_);
stack->m_obj
 = v_res_541_;
}
LEAN_EXPORT lean_object* l_Lake_instReprLogLevel_repr___boxed(lean_object* v_x_542_, lean_object* v_prec_543_){
_start:
{
uint8_t v_x_221__boxed_544_; lean_object* v_res_545_; 
v_x_221__boxed_544_ = lean_unbox(v_x_542_);
v_res_545_ = l_Lake_instReprLogLevel_repr(v_x_221__boxed_544_, v_prec_543_);
lean_dec(v_prec_543_);
return v_res_545_;
}
}
uint8_t l_Lake_LogLevel_ofNat(lean_object* v_n_548_){
_start:
{
lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_549_ = lean_unsigned_to_nat(1u);
v___x_550_ = lean_nat_dec_le(v_n_548_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_551_ = lean_unsigned_to_nat(2u);
v___x_552_ = lean_nat_dec_le(v_n_548_, v___x_551_);
if (v___x_552_ == 0)
{
uint8_t v___x_553_; 
v___x_553_ = 3;
return v___x_553_;
}
else
{
uint8_t v___x_554_; 
v___x_554_ = 2;
return v___x_554_;
}
}
else
{
lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_555_ = lean_unsigned_to_nat(0u);
v___x_556_ = lean_nat_dec_le(v_n_548_, v___x_555_);
if (v___x_556_ == 0)
{
uint8_t v___x_557_; 
v___x_557_ = 1;
return v___x_557_;
}
else
{
uint8_t v___x_558_; 
v___x_558_ = 0;
return v___x_558_;
}
}
}
}
LEAN_EXPORT void l_Lake_LogLevel_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_548_ = stack[0].m_obj;
uint8_t v_res_559_;
v_res_559_ = l_Lake_LogLevel_ofNat(v_n_548_);
stack->m_num = v_res_559_;
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ofNat___boxed(lean_object* v_n_560_){
_start:
{
uint8_t v_res_561_; lean_object* v_r_562_; 
v_res_561_ = l_Lake_LogLevel_ofNat(v_n_560_);
lean_dec(v_n_560_);
v_r_562_ = lean_box(v_res_561_);
return v_r_562_;
}
}
uint8_t l_Lake_instDecidableEqLogLevel(uint8_t v_x_563_, uint8_t v_y_564_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_565_ = lean_box(v_x_563_);
v___x_566_ = lean_obj_tag_nat(v___x_565_);
lean_dec(v___x_565_);
v___x_567_ = lean_box(v_y_564_);
v___x_568_ = lean_obj_tag_nat(v___x_567_);
lean_dec(v___x_567_);
v___x_569_ = lean_nat_dec_eq(v___x_566_, v___x_568_);
return v___x_569_;
}
}
LEAN_EXPORT void l_Lake_instDecidableEqLogLevel_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_563_ = stack[0].m_num;
uint8_t v_y_564_ = stack[1].m_num;
uint8_t v_res_570_;
v_res_570_ = l_Lake_instDecidableEqLogLevel(v_x_563_, v_y_564_);
stack->m_num = v_res_570_;
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqLogLevel___boxed(lean_object* v_x_571_, lean_object* v_y_572_){
_start:
{
uint8_t v_x_23__boxed_573_; uint8_t v_y_24__boxed_574_; uint8_t v_res_575_; lean_object* v_r_576_; 
v_x_23__boxed_573_ = lean_unbox(v_x_571_);
v_y_24__boxed_574_ = lean_unbox(v_y_572_);
v_res_575_ = l_Lake_instDecidableEqLogLevel(v_x_23__boxed_573_, v_y_24__boxed_574_);
v_r_576_ = lean_box(v_res_575_);
return v_r_576_;
}
}
uint8_t l_Lake_instOrdLogLevel_ord(uint8_t v_x_577_, uint8_t v_y_578_){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_579_ = lean_box(v_x_577_);
v___x_580_ = lean_obj_tag_nat(v___x_579_);
lean_dec(v___x_579_);
v___x_581_ = lean_box(v_y_578_);
v___x_582_ = lean_obj_tag_nat(v___x_581_);
lean_dec(v___x_581_);
v___x_583_ = lean_nat_dec_lt(v___x_580_, v___x_582_);
if (v___x_583_ == 0)
{
uint8_t v___x_584_; 
v___x_584_ = lean_nat_dec_eq(v___x_580_, v___x_582_);
if (v___x_584_ == 0)
{
uint8_t v___x_585_; 
v___x_585_ = 2;
return v___x_585_;
}
else
{
uint8_t v___x_586_; 
v___x_586_ = 1;
return v___x_586_;
}
}
else
{
uint8_t v___x_587_; 
v___x_587_ = 0;
return v___x_587_;
}
}
}
LEAN_EXPORT void l_Lake_instOrdLogLevel_ord_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_577_ = stack[0].m_num;
uint8_t v_y_578_ = stack[1].m_num;
uint8_t v_res_588_;
v_res_588_ = l_Lake_instOrdLogLevel_ord(v_x_577_, v_y_578_);
stack->m_num = v_res_588_;
}
LEAN_EXPORT lean_object* l_Lake_instOrdLogLevel_ord___boxed(lean_object* v_x_589_, lean_object* v_y_590_){
_start:
{
uint8_t v_x_33__boxed_591_; uint8_t v_y_34__boxed_592_; uint8_t v_res_593_; lean_object* v_r_594_; 
v_x_33__boxed_591_ = lean_unbox(v_x_589_);
v_y_34__boxed_592_ = lean_unbox(v_y_590_);
v_res_593_ = l_Lake_instOrdLogLevel_ord(v_x_33__boxed_591_, v_y_34__boxed_592_);
v_r_594_ = lean_box(v_res_593_);
return v_r_594_;
}
}
lean_object* l_Lake_instToJsonLogLevel_toJson(uint8_t v_x_609_){
_start:
{
switch(v_x_609_)
{
case 0:
{
lean_object* v___x_610_; 
v___x_610_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__1));
return v___x_610_;
}
case 1:
{
lean_object* v___x_611_; 
v___x_611_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__3));
return v___x_611_;
}
case 2:
{
lean_object* v___x_612_; 
v___x_612_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__5));
return v___x_612_;
}
default: 
{
lean_object* v___x_613_; 
v___x_613_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__7));
return v___x_613_;
}
}
}
}
LEAN_EXPORT void l_Lake_instToJsonLogLevel_toJson_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_609_ = stack[0].m_num;
lean_object* v_res_614_;
v_res_614_ = l_Lake_instToJsonLogLevel_toJson(v_x_609_);
stack->m_obj
 = v_res_614_;
}
LEAN_EXPORT lean_object* l_Lake_instToJsonLogLevel_toJson___boxed(lean_object* v_x_615_){
_start:
{
uint8_t v_x_88__boxed_616_; lean_object* v_res_617_; 
v_x_88__boxed_616_ = lean_unbox(v_x_615_);
v_res_617_ = l_Lake_instToJsonLogLevel_toJson(v_x_88__boxed_616_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonLogLevel_fromJson(lean_object* v_json_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Lean_Json_getTag_x3f(v_json_638_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v___x_640_; 
v___x_640_ = ((lean_object*)(l_Lake_instFromJsonLogLevel_fromJson___closed__1));
return v___x_640_;
}
else
{
lean_object* v_val_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v_val_641_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_val_641_);
lean_dec_ref_known(v___x_639_, 1);
v___x_642_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__6));
v___x_643_ = lean_string_dec_eq(v_val_641_, v___x_642_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_644_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__0));
v___x_645_ = lean_string_dec_eq(v_val_641_, v___x_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_646_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__2));
v___x_647_ = lean_string_dec_eq(v_val_641_, v___x_646_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_648_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__4));
v___x_649_ = lean_string_dec_eq(v_val_641_, v___x_648_);
lean_dec(v_val_641_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; 
v___x_650_ = ((lean_object*)(l_Lake_instFromJsonLogLevel_fromJson___closed__3));
return v___x_650_;
}
else
{
lean_object* v___x_651_; 
v___x_651_ = ((lean_object*)(l_Lake_instFromJsonLogLevel_fromJson___closed__4));
return v___x_651_;
}
}
else
{
lean_object* v___x_652_; 
lean_dec(v_val_641_);
v___x_652_ = ((lean_object*)(l_Lake_instFromJsonLogLevel_fromJson___closed__5));
return v___x_652_;
}
}
else
{
lean_object* v___x_653_; 
lean_dec(v_val_641_);
v___x_653_ = ((lean_object*)(l_Lake_instFromJsonLogLevel_fromJson___closed__6));
return v___x_653_;
}
}
else
{
lean_object* v___x_654_; 
lean_dec(v_val_641_);
v___x_654_ = ((lean_object*)(l_Lake_instFromJsonLogLevel_fromJson___closed__7));
return v___x_654_;
}
}
}
}
static lean_object* _init_l_Lake_instLTLogLevel(void){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = lean_box(0);
return v___x_657_;
}
}
static lean_object* _init_l_Lake_instLELogLevel(void){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = lean_box(0);
return v___x_658_;
}
}
uint8_t l_Lake_instMinLogLevel___lam__0(uint8_t v_x_659_, uint8_t v_y_660_){
_start:
{
uint8_t v___x_661_; 
v___x_661_ = l_Lake_instOrdLogLevel_ord(v_x_659_, v_y_660_);
if (v___x_661_ == 2)
{
return v_y_660_;
}
else
{
return v_x_659_;
}
}
}
LEAN_EXPORT void l_Lake_instMinLogLevel___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_659_ = stack[0].m_num;
uint8_t v_y_660_ = stack[1].m_num;
uint8_t v_res_662_;
v_res_662_ = l_Lake_instMinLogLevel___lam__0(v_x_659_, v_y_660_);
stack->m_num = v_res_662_;
}
LEAN_EXPORT lean_object* l_Lake_instMinLogLevel___lam__0___boxed(lean_object* v_x_663_, lean_object* v_y_664_){
_start:
{
uint8_t v_x_boxed_665_; uint8_t v_y_boxed_666_; uint8_t v_res_667_; lean_object* v_r_668_; 
v_x_boxed_665_ = lean_unbox(v_x_663_);
v_y_boxed_666_ = lean_unbox(v_y_664_);
v_res_667_ = l_Lake_instMinLogLevel___lam__0(v_x_boxed_665_, v_y_boxed_666_);
v_r_668_ = lean_box(v_res_667_);
return v_r_668_;
}
}
uint8_t l_Lake_instMaxLogLevel___lam__0(uint8_t v_x_671_, uint8_t v_y_672_){
_start:
{
uint8_t v___x_673_; 
v___x_673_ = l_Lake_instOrdLogLevel_ord(v_x_671_, v_y_672_);
if (v___x_673_ == 2)
{
return v_x_671_;
}
else
{
return v_y_672_;
}
}
}
LEAN_EXPORT void l_Lake_instMaxLogLevel___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_671_ = stack[0].m_num;
uint8_t v_y_672_ = stack[1].m_num;
uint8_t v_res_674_;
v_res_674_ = l_Lake_instMaxLogLevel___lam__0(v_x_671_, v_y_672_);
stack->m_num = v_res_674_;
}
LEAN_EXPORT lean_object* l_Lake_instMaxLogLevel___lam__0___boxed(lean_object* v_x_675_, lean_object* v_y_676_){
_start:
{
uint8_t v_x_boxed_677_; uint8_t v_y_boxed_678_; uint8_t v_res_679_; lean_object* v_r_680_; 
v_x_boxed_677_ = lean_unbox(v_x_675_);
v_y_boxed_678_ = lean_unbox(v_y_676_);
v_res_679_ = l_Lake_instMaxLogLevel___lam__0(v_x_boxed_677_, v_y_boxed_678_);
v_r_680_ = lean_box(v_res_679_);
return v_r_680_;
}
}
uint32_t l_Lake_LogLevel_icon(uint8_t v_x_683_){
_start:
{
switch(v_x_683_)
{
case 2:
{
uint32_t v___x_684_; 
v___x_684_ = 9888;
return v___x_684_;
}
case 3:
{
uint32_t v___x_685_; 
v___x_685_ = 10006;
return v___x_685_;
}
default: 
{
uint32_t v___x_686_; 
v___x_686_ = 8505;
return v___x_686_;
}
}
}
}
LEAN_EXPORT void l_Lake_LogLevel_icon_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_683_ = stack[0].m_num;
uint32_t v_res_687_;
v_res_687_ = l_Lake_LogLevel_icon(v_x_683_);
stack->m_num = v_res_687_;
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_icon___boxed(lean_object* v_x_688_){
_start:
{
uint8_t v_x_35__boxed_689_; uint32_t v_res_690_; lean_object* v_r_691_; 
v_x_35__boxed_689_ = lean_unbox(v_x_688_);
v_res_690_ = l_Lake_LogLevel_icon(v_x_35__boxed_689_);
v_r_691_ = lean_box_uint32(v_res_690_);
return v_r_691_;
}
}
lean_object* l_Lake_LogLevel_ansiColor(uint8_t v_x_695_){
_start:
{
switch(v_x_695_)
{
case 2:
{
lean_object* v___x_696_; 
v___x_696_ = ((lean_object*)(l_Lake_LogLevel_ansiColor___closed__0));
return v___x_696_;
}
case 3:
{
lean_object* v___x_697_; 
v___x_697_ = ((lean_object*)(l_Lake_LogLevel_ansiColor___closed__1));
return v___x_697_;
}
default: 
{
lean_object* v___x_698_; 
v___x_698_ = ((lean_object*)(l_Lake_LogLevel_ansiColor___closed__2));
return v___x_698_;
}
}
}
}
LEAN_EXPORT void l_Lake_LogLevel_ansiColor_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_695_ = stack[0].m_num;
lean_object* v_res_699_;
v_res_699_ = l_Lake_LogLevel_ansiColor(v_x_695_);
stack->m_obj
 = v_res_699_;
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ansiColor___boxed(lean_object* v_x_700_){
_start:
{
uint8_t v_x_36__boxed_701_; lean_object* v_res_702_; 
v_x_36__boxed_701_ = lean_unbox(v_x_700_);
v_res_702_ = l_Lake_LogLevel_ansiColor(v_x_36__boxed_701_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00Lake_LogLevel_ofString_x3f_spec__0(lean_object* v_s_703_, lean_object* v_p_704_){
_start:
{
uint32_t v___y_706_; lean_object* v___x_711_; uint8_t v_decide_712_; 
v___x_711_ = lean_string_utf8_byte_size(v_s_703_);
v_decide_712_ = lean_nat_dec_eq(v_p_704_, v___x_711_);
if (v_decide_712_ == 0)
{
uint32_t v___x_713_; uint32_t v___x_714_; uint8_t v___x_715_; 
v___x_713_ = lean_string_utf8_get_fast(v_s_703_, v_p_704_);
v___x_714_ = 65;
v___x_715_ = lean_uint32_dec_le(v___x_714_, v___x_713_);
if (v___x_715_ == 0)
{
v___y_706_ = v___x_713_;
goto v___jp_705_;
}
else
{
uint32_t v___x_716_; uint8_t v___x_717_; 
v___x_716_ = 90;
v___x_717_ = lean_uint32_dec_le(v___x_713_, v___x_716_);
if (v___x_717_ == 0)
{
v___y_706_ = v___x_713_;
goto v___jp_705_;
}
else
{
uint32_t v___x_718_; uint32_t v___x_719_; 
v___x_718_ = 32;
v___x_719_ = lean_uint32_add(v___x_713_, v___x_718_);
v___y_706_ = v___x_719_;
goto v___jp_705_;
}
}
}
else
{
lean_dec(v_p_704_);
return v_s_703_;
}
v___jp_705_:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
lean_inc(v_p_704_);
v___x_707_ = lean_string_utf8_set(v_s_703_, v_p_704_, v___y_706_);
v___x_708_ = l_Char_utf8Size(v___y_706_);
v___x_709_ = lean_nat_add(v_p_704_, v___x_708_);
lean_dec(v___x_708_);
lean_dec(v_p_704_);
v_s_703_ = v___x_707_;
v_p_704_ = v___x_709_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ofString_x3f(lean_object* v_s_734_){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = l_String_mapAux___at___00Lake_LogLevel_ofString_x3f_spec__0(v_s_734_, v___x_739_);
v___x_741_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__0));
v___x_742_ = lean_string_dec_eq(v___x_740_, v___x_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_743_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__2));
v___x_744_ = lean_string_dec_eq(v___x_740_, v___x_743_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_745_ = ((lean_object*)(l_Lake_LogLevel_ofString_x3f___closed__2));
v___x_746_ = lean_string_dec_eq(v___x_740_, v___x_745_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; uint8_t v___x_748_; 
v___x_747_ = ((lean_object*)(l_Lake_LogLevel_ofString_x3f___closed__3));
v___x_748_ = lean_string_dec_eq(v___x_740_, v___x_747_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_749_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__4));
v___x_750_ = lean_string_dec_eq(v___x_740_, v___x_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_751_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__6));
v___x_752_ = lean_string_dec_eq(v___x_740_, v___x_751_);
lean_dec_ref(v___x_740_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; 
v___x_753_ = lean_box(0);
return v___x_753_;
}
else
{
lean_object* v___x_754_; 
v___x_754_ = ((lean_object*)(l_Lake_LogLevel_ofString_x3f___closed__4));
return v___x_754_;
}
}
else
{
lean_dec_ref(v___x_740_);
goto v___jp_737_;
}
}
else
{
lean_dec_ref(v___x_740_);
goto v___jp_737_;
}
}
else
{
lean_dec_ref(v___x_740_);
goto v___jp_735_;
}
}
else
{
lean_dec_ref(v___x_740_);
goto v___jp_735_;
}
}
else
{
lean_object* v___x_755_; 
lean_dec_ref(v___x_740_);
v___x_755_ = ((lean_object*)(l_Lake_LogLevel_ofString_x3f___closed__5));
return v___x_755_;
}
v___jp_735_:
{
lean_object* v___x_736_; 
v___x_736_ = ((lean_object*)(l_Lake_LogLevel_ofString_x3f___closed__0));
return v___x_736_;
}
v___jp_737_:
{
lean_object* v___x_738_; 
v___x_738_ = ((lean_object*)(l_Lake_LogLevel_ofString_x3f___closed__1));
return v___x_738_;
}
}
}
lean_object* l_Lake_LogLevel_toString(uint8_t v_x_756_){
_start:
{
switch(v_x_756_)
{
case 0:
{
lean_object* v___x_757_; 
v___x_757_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__0));
return v___x_757_;
}
case 1:
{
lean_object* v___x_758_; 
v___x_758_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__2));
return v___x_758_;
}
case 2:
{
lean_object* v___x_759_; 
v___x_759_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__4));
return v___x_759_;
}
default: 
{
lean_object* v___x_760_; 
v___x_760_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__6));
return v___x_760_;
}
}
}
}
LEAN_EXPORT void l_Lake_LogLevel_toString_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_756_ = stack[0].m_num;
lean_object* v_res_761_;
v_res_761_ = l_Lake_LogLevel_toString(v_x_756_);
stack->m_obj
 = v_res_761_;
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_toString___boxed(lean_object* v_x_762_){
_start:
{
uint8_t v_x_36__boxed_763_; lean_object* v_res_764_; 
v_x_36__boxed_763_ = lean_unbox(v_x_762_);
v_res_764_ = l_Lake_LogLevel_toString(v_x_36__boxed_763_);
return v_res_764_;
}
}
uint8_t l_Lake_LogLevel_ofMessageSeverity(uint8_t v_x_767_){
_start:
{
switch(v_x_767_)
{
case 0:
{
uint8_t v___x_768_; 
v___x_768_ = 1;
return v___x_768_;
}
case 1:
{
uint8_t v___x_769_; 
v___x_769_ = 2;
return v___x_769_;
}
default: 
{
uint8_t v___x_770_; 
v___x_770_ = 3;
return v___x_770_;
}
}
}
}
LEAN_EXPORT void l_Lake_LogLevel_ofMessageSeverity_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_767_ = stack[0].m_num;
uint8_t v_res_771_;
v_res_771_ = l_Lake_LogLevel_ofMessageSeverity(v_x_767_);
stack->m_num = v_res_771_;
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ofMessageSeverity___boxed(lean_object* v_x_772_){
_start:
{
uint8_t v_x_25__boxed_773_; uint8_t v_res_774_; lean_object* v_r_775_; 
v_x_25__boxed_773_ = lean_unbox(v_x_772_);
v_res_774_ = l_Lake_LogLevel_ofMessageSeverity(v_x_25__boxed_773_);
v_r_775_ = lean_box(v_res_774_);
return v_r_775_;
}
}
uint8_t l_Lake_LogLevel_toMessageSeverity(uint8_t v_x_776_){
_start:
{
switch(v_x_776_)
{
case 2:
{
uint8_t v___x_777_; 
v___x_777_ = 1;
return v___x_777_;
}
case 3:
{
uint8_t v___x_778_; 
v___x_778_ = 2;
return v___x_778_;
}
default: 
{
uint8_t v___x_779_; 
v___x_779_ = 0;
return v___x_779_;
}
}
}
}
LEAN_EXPORT void l_Lake_LogLevel_toMessageSeverity_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_776_ = stack[0].m_num;
uint8_t v_res_780_;
v_res_780_ = l_Lake_LogLevel_toMessageSeverity(v_x_776_);
stack->m_num = v_res_780_;
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_toMessageSeverity___boxed(lean_object* v_x_781_){
_start:
{
uint8_t v_x_30__boxed_782_; uint8_t v_res_783_; lean_object* v_r_784_; 
v_x_30__boxed_782_ = lean_unbox(v_x_781_);
v_res_783_ = l_Lake_LogLevel_toMessageSeverity(v_x_30__boxed_782_);
v_r_784_ = lean_box(v_res_783_);
return v_r_784_;
}
}
uint8_t l_Lake_Verbosity_minLogLv(uint8_t v_x_785_){
_start:
{
switch(v_x_785_)
{
case 0:
{
uint8_t v___x_786_; 
v___x_786_ = 2;
return v___x_786_;
}
case 1:
{
uint8_t v___x_787_; 
v___x_787_ = 1;
return v___x_787_;
}
default: 
{
uint8_t v___x_788_; 
v___x_788_ = 0;
return v___x_788_;
}
}
}
}
LEAN_EXPORT void l_Lake_Verbosity_minLogLv_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_785_ = stack[0].m_num;
uint8_t v_res_789_;
v_res_789_ = l_Lake_Verbosity_minLogLv(v_x_785_);
stack->m_num = v_res_789_;
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_minLogLv___boxed(lean_object* v_x_790_){
_start:
{
uint8_t v_x_25__boxed_791_; uint8_t v_res_792_; lean_object* v_r_793_; 
v_x_25__boxed_791_ = lean_unbox(v_x_790_);
v_res_792_ = l_Lake_Verbosity_minLogLv(v_x_25__boxed_791_);
v_r_793_ = lean_box(v_res_792_);
return v_r_793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_instToJsonLogEntry_toJson_spec__0(lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
if (lean_obj_tag(v_a_800_) == 0)
{
lean_object* v___x_802_; 
v___x_802_ = lean_array_to_list(v_a_801_);
return v___x_802_;
}
else
{
lean_object* v_head_803_; lean_object* v_tail_804_; lean_object* v___x_805_; 
v_head_803_ = lean_ctor_get(v_a_800_, 0);
lean_inc(v_head_803_);
v_tail_804_ = lean_ctor_get(v_a_800_, 1);
lean_inc(v_tail_804_);
lean_dec_ref_known(v_a_800_, 2);
v___x_805_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_801_, v_head_803_);
v_a_800_ = v_tail_804_;
v_a_801_ = v___x_805_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonLogEntry_toJson(lean_object* v_x_811_){
_start:
{
uint8_t v_level_812_; lean_object* v_message_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v_level_812_ = lean_ctor_get_uint8(v_x_811_, sizeof(void*)*1);
v_message_813_ = lean_ctor_get(v_x_811_, 0);
v___x_814_ = ((lean_object*)(l_Lake_instToJsonLogEntry_toJson___closed__0));
v___x_815_ = l_Lake_instToJsonLogLevel_toJson(v_level_812_);
v___x_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = lean_box(0);
v___x_818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = ((lean_object*)(l_Lake_instToJsonLogEntry_toJson___closed__1));
lean_inc_ref(v_message_813_);
v___x_820_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_820_, 0, v_message_813_);
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_819_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
lean_ctor_set(v___x_822_, 1, v___x_817_);
v___x_823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set(v___x_823_, 1, v___x_817_);
v___x_824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_818_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
v___x_825_ = ((lean_object*)(l_Lake_instToJsonLogEntry_toJson___closed__2));
v___x_826_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_instToJsonLogEntry_toJson_spec__0(v___x_824_, v___x_825_);
v___x_827_ = l_Lean_Json_mkObj(v___x_826_);
lean_dec(v___x_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonLogEntry_toJson___boxed(lean_object* v_x_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lake_instToJsonLogEntry_toJson(v_x_828_);
lean_dec_ref(v_x_828_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__0(lean_object* v_j_832_, lean_object* v_k_833_){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = l_Lean_Json_getObjValD(v_j_832_, v_k_833_);
v___x_835_ = l_Lake_instFromJsonLogLevel_fromJson(v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__0___boxed(lean_object* v_j_836_, lean_object* v_k_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__0(v_j_836_, v_k_837_);
lean_dec_ref(v_k_837_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1(lean_object* v_j_839_, lean_object* v_k_840_){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = l_Lean_Json_getObjValD(v_j_839_, v_k_840_);
v___x_842_ = l_Lean_Json_getStr_x3f(v___x_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1___boxed(lean_object* v_j_843_, lean_object* v_k_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1(v_j_843_, v_k_844_);
lean_dec_ref(v_k_844_);
return v_res_845_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__3(void){
_start:
{
uint8_t v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_851_ = 1;
v___x_852_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__2));
v___x_853_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_852_, v___x_851_);
return v___x_853_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__5(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_855_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__4));
v___x_856_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__3, &l_Lake_instFromJsonLogEntry_fromJson___closed__3_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__3);
v___x_857_ = lean_string_append(v___x_856_, v___x_855_);
return v___x_857_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__7(void){
_start:
{
uint8_t v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_860_ = 1;
v___x_861_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__6));
v___x_862_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_861_, v___x_860_);
return v___x_862_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__8(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_863_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__7, &l_Lake_instFromJsonLogEntry_fromJson___closed__7_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__7);
v___x_864_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__5, &l_Lake_instFromJsonLogEntry_fromJson___closed__5_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__5);
v___x_865_ = lean_string_append(v___x_864_, v___x_863_);
return v___x_865_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__10(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_867_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__9));
v___x_868_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__8, &l_Lake_instFromJsonLogEntry_fromJson___closed__8_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__8);
v___x_869_ = lean_string_append(v___x_868_, v___x_867_);
return v___x_869_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__12(void){
_start:
{
uint8_t v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_872_ = 1;
v___x_873_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__11));
v___x_874_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_873_, v___x_872_);
return v___x_874_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__13(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_875_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__12, &l_Lake_instFromJsonLogEntry_fromJson___closed__12_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__12);
v___x_876_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__5, &l_Lake_instFromJsonLogEntry_fromJson___closed__5_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__5);
v___x_877_ = lean_string_append(v___x_876_, v___x_875_);
return v___x_877_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__14(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_878_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__9));
v___x_879_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__13, &l_Lake_instFromJsonLogEntry_fromJson___closed__13_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__13);
v___x_880_ = lean_string_append(v___x_879_, v___x_878_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonLogEntry_fromJson(lean_object* v_json_881_){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = ((lean_object*)(l_Lake_instToJsonLogEntry_toJson___closed__0));
lean_inc(v_json_881_);
v___x_883_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__0(v_json_881_, v___x_882_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_893_; 
lean_dec(v_json_881_);
v_a_884_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_893_ == 0)
{
v___x_886_ = v___x_883_;
v_isShared_887_ = v_isSharedCheck_893_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_883_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_893_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_891_; 
v___x_888_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__10, &l_Lake_instFromJsonLogEntry_fromJson___closed__10_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__10);
v___x_889_ = lean_string_append(v___x_888_, v_a_884_);
lean_dec(v_a_884_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v___x_889_);
v___x_891_ = v___x_886_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
else
{
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec(v_json_881_);
v_a_894_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_883_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_883_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
lean_ctor_set_tag(v___x_896_, 0);
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v_a_902_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_902_);
lean_dec_ref_known(v___x_883_, 1);
v___x_903_ = ((lean_object*)(l_Lake_instToJsonLogEntry_toJson___closed__1));
v___x_904_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1(v_json_881_, v___x_903_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_914_; 
lean_dec(v_a_902_);
v_a_905_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_914_ == 0)
{
v___x_907_ = v___x_904_;
v_isShared_908_ = v_isSharedCheck_914_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_904_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_914_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_912_; 
v___x_909_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__14, &l_Lake_instFromJsonLogEntry_fromJson___closed__14_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__14);
v___x_910_ = lean_string_append(v___x_909_, v_a_905_);
lean_dec(v_a_905_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v___x_910_);
v___x_912_ = v___x_907_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
else
{
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec(v_a_902_);
v_a_915_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_904_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_904_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
lean_ctor_set_tag(v___x_917_, 0);
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_932_; 
v_a_923_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_932_ == 0)
{
v___x_925_ = v___x_904_;
v_isShared_926_ = v_isSharedCheck_932_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_904_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_932_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; uint8_t v___x_928_; lean_object* v___x_930_; 
v___x_927_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_927_, 0, v_a_923_);
v___x_928_ = lean_unbox(v_a_902_);
lean_dec(v_a_902_);
lean_ctor_set_uint8(v___x_927_, sizeof(void*)*1, v___x_928_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v___x_927_);
v___x_930_ = v___x_925_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_927_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
}
}
}
lean_object* l_Lake_LogEntry_toString(lean_object* v_self_937_, uint8_t v_useAnsi_938_){
_start:
{
if (v_useAnsi_938_ == 0)
{
uint8_t v_level_939_; lean_object* v_message_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v_level_939_ = lean_ctor_get_uint8(v_self_937_, sizeof(void*)*1);
v_message_940_ = lean_ctor_get(v_self_937_, 0);
v___x_941_ = l_Lake_LogLevel_toString(v_level_939_);
v___x_942_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__9));
v___x_943_ = lean_string_append(v___x_941_, v___x_942_);
v___x_944_ = lean_string_append(v___x_943_, v_message_940_);
return v___x_944_;
}
else
{
uint8_t v_level_945_; lean_object* v_message_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v_pre_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v_level_945_ = lean_ctor_get_uint8(v_self_937_, sizeof(void*)*1);
v_message_946_ = lean_ctor_get(v_self_937_, 0);
v___x_947_ = l_Lake_LogLevel_ansiColor(v_level_945_);
v___x_948_ = l_Lake_LogLevel_toString(v_level_945_);
v___x_949_ = ((lean_object*)(l_Lake_LogEntry_toString___closed__0));
v___x_950_ = lean_string_append(v___x_948_, v___x_949_);
v_pre_951_ = l_Lake_Ansi_chalk(v___x_947_, v___x_950_);
lean_dec_ref(v___x_950_);
lean_dec_ref(v___x_947_);
v___x_952_ = ((lean_object*)(l_Lake_LogEntry_toString___closed__1));
v___x_953_ = lean_string_append(v_pre_951_, v___x_952_);
v___x_954_ = lean_string_append(v___x_953_, v_message_946_);
return v___x_954_;
}
}
}
LEAN_EXPORT void l_Lake_LogEntry_toString_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_937_ = stack[0].m_obj;
uint8_t v_useAnsi_938_ = stack[1].m_num;
lean_object* v_res_955_;
v_res_955_ = l_Lake_LogEntry_toString(v_self_937_, v_useAnsi_938_);
stack->m_obj
 = v_res_955_;
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_toString___boxed(lean_object* v_self_956_, lean_object* v_useAnsi_957_){
_start:
{
uint8_t v_useAnsi_boxed_958_; lean_object* v_res_959_; 
v_useAnsi_boxed_958_ = lean_unbox(v_useAnsi_957_);
v_res_959_ = l_Lake_LogEntry_toString(v_self_956_, v_useAnsi_boxed_958_);
lean_dec_ref(v_self_956_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToStringLogEntry___lam__0(lean_object* v_self_960_){
_start:
{
uint8_t v___x_961_; lean_object* v___x_962_; 
v___x_961_ = 0;
v___x_962_ = l_Lake_LogEntry_toString(v_self_960_, v___x_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToStringLogEntry___lam__0___boxed(lean_object* v_self_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lake_instToStringLogEntry___lam__0(v_self_963_);
lean_dec_ref(v_self_963_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_trace(lean_object* v_message_967_){
_start:
{
uint8_t v___x_968_; lean_object* v___x_969_; 
v___x_968_ = 0;
v___x_969_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_969_, 0, v_message_967_);
lean_ctor_set_uint8(v___x_969_, sizeof(void*)*1, v___x_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_info(lean_object* v_message_970_){
_start:
{
uint8_t v___x_971_; lean_object* v___x_972_; 
v___x_971_ = 1;
v___x_972_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_972_, 0, v_message_970_);
lean_ctor_set_uint8(v___x_972_, sizeof(void*)*1, v___x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_warning(lean_object* v_message_973_){
_start:
{
uint8_t v___x_974_; lean_object* v___x_975_; 
v___x_974_ = 2;
v___x_975_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_975_, 0, v_message_973_);
lean_ctor_set_uint8(v___x_975_, sizeof(void*)*1, v___x_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_error(lean_object* v_message_976_){
_start:
{
uint8_t v___x_977_; lean_object* v___x_978_; 
v___x_977_ = 3;
v___x_978_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_978_, 0, v_message_976_);
lean_ctor_set_uint8(v___x_978_, sizeof(void*)*1, v___x_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_ofSerialMessage(lean_object* v_msg_980_){
_start:
{
lean_object* v_toBaseMessage_981_; lean_object* v_fileName_982_; lean_object* v_pos_983_; uint8_t v_severity_984_; lean_object* v_caption_985_; lean_object* v_data_986_; lean_object* v___y_988_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v_startInclusive_997_; lean_object* v_endExclusive_998_; lean_object* v___x_999_; uint8_t v___x_1000_; 
v_toBaseMessage_981_ = lean_ctor_get(v_msg_980_, 0);
lean_inc_ref(v_toBaseMessage_981_);
lean_dec_ref(v_msg_980_);
v_fileName_982_ = lean_ctor_get(v_toBaseMessage_981_, 0);
lean_inc_ref(v_fileName_982_);
v_pos_983_ = lean_ctor_get(v_toBaseMessage_981_, 1);
lean_inc_ref(v_pos_983_);
v_severity_984_ = lean_ctor_get_uint8(v_toBaseMessage_981_, sizeof(void*)*5 + 1);
v_caption_985_ = lean_ctor_get(v_toBaseMessage_981_, 3);
lean_inc_ref(v_caption_985_);
v_data_986_ = lean_ctor_get(v_toBaseMessage_981_, 4);
lean_inc(v_data_986_);
lean_dec_ref(v_toBaseMessage_981_);
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = lean_string_utf8_byte_size(v_caption_985_);
v___x_995_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_995_, 0, v_caption_985_);
lean_ctor_set(v___x_995_, 1, v___x_993_);
lean_ctor_set(v___x_995_, 2, v___x_994_);
v___x_996_ = l_String_Slice_trimAscii(v___x_995_);
v_startInclusive_997_ = lean_ctor_get(v___x_996_, 1);
v_endExclusive_998_ = lean_ctor_get(v___x_996_, 2);
v___x_999_ = lean_nat_sub(v_endExclusive_998_, v_startInclusive_997_);
v___x_1000_ = lean_nat_dec_eq(v___x_999_, v___x_993_);
lean_dec(v___x_999_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1014_; 
v___x_1001_ = l_String_Slice_toString(v___x_996_);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1014_ == 0)
{
lean_object* v_unused_1015_; lean_object* v_unused_1016_; lean_object* v_unused_1017_; 
v_unused_1015_ = lean_ctor_get(v___x_996_, 2);
lean_dec(v_unused_1015_);
v_unused_1016_ = lean_ctor_get(v___x_996_, 1);
lean_dec(v_unused_1016_);
v_unused_1017_ = lean_ctor_get(v___x_996_, 0);
lean_dec(v_unused_1017_);
v___x_1003_ = v___x_996_;
v_isShared_1004_ = v_isSharedCheck_1014_;
goto v_resetjp_1002_;
}
else
{
lean_dec(v___x_996_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1014_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1009_; 
v___x_1005_ = ((lean_object*)(l_Lake_LogEntry_ofSerialMessage___closed__0));
v___x_1006_ = lean_string_append(v___x_1001_, v___x_1005_);
v___x_1007_ = lean_string_utf8_byte_size(v_data_986_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 2, v___x_1007_);
lean_ctor_set(v___x_1003_, 1, v___x_993_);
lean_ctor_set(v___x_1003_, 0, v_data_986_);
v___x_1009_ = v___x_1003_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_data_986_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_1013_, 2, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = l_String_Slice_trimAscii(v___x_1009_);
v___x_1011_ = l_String_Slice_toString(v___x_1010_);
lean_dec_ref(v___x_1010_);
v___x_1012_ = lean_string_append(v___x_1006_, v___x_1011_);
lean_dec_ref(v___x_1011_);
v___y_988_ = v___x_1012_;
goto v___jp_987_;
}
}
}
else
{
lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1030_; 
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1030_ == 0)
{
lean_object* v_unused_1031_; lean_object* v_unused_1032_; lean_object* v_unused_1033_; 
v_unused_1031_ = lean_ctor_get(v___x_996_, 2);
lean_dec(v_unused_1031_);
v_unused_1032_ = lean_ctor_get(v___x_996_, 1);
lean_dec(v_unused_1032_);
v_unused_1033_ = lean_ctor_get(v___x_996_, 0);
lean_dec(v_unused_1033_);
v___x_1019_ = v___x_996_;
v_isShared_1020_ = v_isSharedCheck_1030_;
goto v_resetjp_1018_;
}
else
{
lean_dec(v___x_996_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1030_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1021_ = lean_string_utf8_byte_size(v_data_986_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 2, v___x_1021_);
lean_ctor_set(v___x_1019_, 1, v___x_993_);
lean_ctor_set(v___x_1019_, 0, v_data_986_);
v___x_1023_ = v___x_1019_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_data_986_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_1029_, 2, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1024_; lean_object* v_str_1025_; lean_object* v_startInclusive_1026_; lean_object* v_endExclusive_1027_; lean_object* v___x_1028_; 
v___x_1024_ = l_String_Slice_trimAscii(v___x_1023_);
v_str_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc_ref(v_str_1025_);
v_startInclusive_1026_ = lean_ctor_get(v___x_1024_, 1);
lean_inc(v_startInclusive_1026_);
v_endExclusive_1027_ = lean_ctor_get(v___x_1024_, 2);
lean_inc(v_endExclusive_1027_);
lean_dec_ref(v___x_1024_);
v___x_1028_ = lean_string_utf8_extract_fast(v_str_1025_, v_startInclusive_1026_, v_endExclusive_1027_);
lean_dec(v_endExclusive_1027_);
lean_dec(v_startInclusive_1026_);
lean_dec_ref(v_str_1025_);
v___y_988_ = v___x_1028_;
goto v___jp_987_;
}
}
}
v___jp_987_:
{
uint8_t v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_989_ = l_Lake_LogLevel_ofMessageSeverity(v_severity_984_);
v___x_990_ = lean_box(0);
v___x_991_ = l_Lean_mkErrorStringWithPos(v_fileName_982_, v_pos_983_, v___y_988_, v___x_990_, v___x_990_, v___x_990_);
lean_dec_ref(v___y_988_);
v___x_992_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_992_, 0, v___x_991_);
lean_ctor_set_uint8(v___x_992_, sizeof(void*)*1, v___x_989_);
return v___x_992_;
}
}
}
lean_object* l_Lake_LogEntry_ofMessage(lean_object* v_msg_1034_){
_start:
{
lean_object* v_fileName_1036_; lean_object* v_pos_1037_; uint8_t v_severity_1038_; lean_object* v_caption_1039_; lean_object* v_data_1040_; lean_object* v___x_1041_; lean_object* v___y_1043_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v_startInclusive_1052_; lean_object* v_endExclusive_1053_; lean_object* v___x_1054_; uint8_t v___x_1055_; 
v_fileName_1036_ = lean_ctor_get(v_msg_1034_, 0);
lean_inc_ref(v_fileName_1036_);
v_pos_1037_ = lean_ctor_get(v_msg_1034_, 1);
lean_inc_ref(v_pos_1037_);
v_severity_1038_ = lean_ctor_get_uint8(v_msg_1034_, sizeof(void*)*5 + 1);
v_caption_1039_ = lean_ctor_get(v_msg_1034_, 3);
lean_inc_ref(v_caption_1039_);
v_data_1040_ = lean_ctor_get(v_msg_1034_, 4);
lean_inc(v_data_1040_);
lean_dec_ref(v_msg_1034_);
v___x_1041_ = l_Lean_MessageData_toString(v_data_1040_);
v___x_1048_ = lean_unsigned_to_nat(0u);
v___x_1049_ = lean_string_utf8_byte_size(v_caption_1039_);
v___x_1050_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1050_, 0, v_caption_1039_);
lean_ctor_set(v___x_1050_, 1, v___x_1048_);
lean_ctor_set(v___x_1050_, 2, v___x_1049_);
v___x_1051_ = l_String_Slice_trimAscii(v___x_1050_);
v_startInclusive_1052_ = lean_ctor_get(v___x_1051_, 1);
v_endExclusive_1053_ = lean_ctor_get(v___x_1051_, 2);
v___x_1054_ = lean_nat_sub(v_endExclusive_1053_, v_startInclusive_1052_);
v___x_1055_ = lean_nat_dec_eq(v___x_1054_, v___x_1048_);
lean_dec(v___x_1054_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1069_; 
v___x_1056_ = l_String_Slice_toString(v___x_1051_);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1069_ == 0)
{
lean_object* v_unused_1070_; lean_object* v_unused_1071_; lean_object* v_unused_1072_; 
v_unused_1070_ = lean_ctor_get(v___x_1051_, 2);
lean_dec(v_unused_1070_);
v_unused_1071_ = lean_ctor_get(v___x_1051_, 1);
lean_dec(v_unused_1071_);
v_unused_1072_ = lean_ctor_get(v___x_1051_, 0);
lean_dec(v_unused_1072_);
v___x_1058_ = v___x_1051_;
v_isShared_1059_ = v_isSharedCheck_1069_;
goto v_resetjp_1057_;
}
else
{
lean_dec(v___x_1051_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1069_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1064_; 
v___x_1060_ = ((lean_object*)(l_Lake_LogEntry_ofSerialMessage___closed__0));
v___x_1061_ = lean_string_append(v___x_1056_, v___x_1060_);
v___x_1062_ = lean_string_utf8_byte_size(v___x_1041_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 2, v___x_1062_);
lean_ctor_set(v___x_1058_, 1, v___x_1048_);
lean_ctor_set(v___x_1058_, 0, v___x_1041_);
v___x_1064_ = v___x_1058_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1068_, 2, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1065_ = l_String_Slice_trimAscii(v___x_1064_);
v___x_1066_ = l_String_Slice_toString(v___x_1065_);
lean_dec_ref(v___x_1065_);
v___x_1067_ = lean_string_append(v___x_1061_, v___x_1066_);
lean_dec_ref(v___x_1066_);
v___y_1043_ = v___x_1067_;
goto v___jp_1042_;
}
}
}
else
{
lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1085_; 
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1085_ == 0)
{
lean_object* v_unused_1086_; lean_object* v_unused_1087_; lean_object* v_unused_1088_; 
v_unused_1086_ = lean_ctor_get(v___x_1051_, 2);
lean_dec(v_unused_1086_);
v_unused_1087_ = lean_ctor_get(v___x_1051_, 1);
lean_dec(v_unused_1087_);
v_unused_1088_ = lean_ctor_get(v___x_1051_, 0);
lean_dec(v_unused_1088_);
v___x_1074_ = v___x_1051_;
v_isShared_1075_ = v_isSharedCheck_1085_;
goto v_resetjp_1073_;
}
else
{
lean_dec(v___x_1051_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1085_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1076_; lean_object* v___x_1078_; 
v___x_1076_ = lean_string_utf8_byte_size(v___x_1041_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 2, v___x_1076_);
lean_ctor_set(v___x_1074_, 1, v___x_1048_);
lean_ctor_set(v___x_1074_, 0, v___x_1041_);
v___x_1078_ = v___x_1074_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1084_, 2, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1079_; lean_object* v_str_1080_; lean_object* v_startInclusive_1081_; lean_object* v_endExclusive_1082_; lean_object* v___x_1083_; 
v___x_1079_ = l_String_Slice_trimAscii(v___x_1078_);
v_str_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc_ref(v_str_1080_);
v_startInclusive_1081_ = lean_ctor_get(v___x_1079_, 1);
lean_inc(v_startInclusive_1081_);
v_endExclusive_1082_ = lean_ctor_get(v___x_1079_, 2);
lean_inc(v_endExclusive_1082_);
lean_dec_ref(v___x_1079_);
v___x_1083_ = lean_string_utf8_extract_fast(v_str_1080_, v_startInclusive_1081_, v_endExclusive_1082_);
lean_dec(v_endExclusive_1082_);
lean_dec(v_startInclusive_1081_);
lean_dec_ref(v_str_1080_);
v___y_1043_ = v___x_1083_;
goto v___jp_1042_;
}
}
}
v___jp_1042_:
{
uint8_t v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1044_ = l_Lake_LogLevel_ofMessageSeverity(v_severity_1038_);
v___x_1045_ = lean_box(0);
v___x_1046_ = l_Lean_mkErrorStringWithPos(v_fileName_1036_, v_pos_1037_, v___y_1043_, v___x_1045_, v___x_1045_, v___x_1045_);
lean_dec_ref(v___y_1043_);
v___x_1047_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set_uint8(v___x_1047_, sizeof(void*)*1, v___x_1044_);
return v___x_1047_;
}
}
}
LEAN_EXPORT void l_Lake_LogEntry_ofMessage_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1034_ = stack[0].m_obj;
lean_object* v_res_1089_;
v_res_1089_ = l_Lake_LogEntry_ofMessage(v_msg_1034_);
stack->m_obj
 = v_res_1089_;
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_ofMessage___boxed(lean_object* v_msg_1090_, lean_object* v_a_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lake_LogEntry_ofMessage(v_msg_1090_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lake_logVerbose___redArg(lean_object* v_inst_1093_, lean_object* v_message_1094_){
_start:
{
uint8_t v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1095_ = 0;
v___x_1096_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1096_, 0, v_message_1094_);
lean_ctor_set_uint8(v___x_1096_, sizeof(void*)*1, v___x_1095_);
v___x_1097_ = lean_apply_1(v_inst_1093_, v___x_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lake_logVerbose(lean_object* v_m_1098_, lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_message_1101_){
_start:
{
uint8_t v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1102_ = 0;
v___x_1103_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1103_, 0, v_message_1101_);
lean_ctor_set_uint8(v___x_1103_, sizeof(void*)*1, v___x_1102_);
v___x_1104_ = lean_apply_1(v_inst_1100_, v___x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lake_logVerbose___boxed(lean_object* v_m_1105_, lean_object* v_inst_1106_, lean_object* v_inst_1107_, lean_object* v_message_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Lake_logVerbose(v_m_1105_, v_inst_1106_, v_inst_1107_, v_message_1108_);
lean_dec_ref(v_inst_1106_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lake_logInfo___redArg(lean_object* v_inst_1110_, lean_object* v_message_1111_){
_start:
{
uint8_t v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1112_ = 1;
v___x_1113_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1113_, 0, v_message_1111_);
lean_ctor_set_uint8(v___x_1113_, sizeof(void*)*1, v___x_1112_);
v___x_1114_ = lean_apply_1(v_inst_1110_, v___x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lake_logInfo(lean_object* v_m_1115_, lean_object* v_inst_1116_, lean_object* v_inst_1117_, lean_object* v_message_1118_){
_start:
{
uint8_t v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1119_ = 1;
v___x_1120_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1120_, 0, v_message_1118_);
lean_ctor_set_uint8(v___x_1120_, sizeof(void*)*1, v___x_1119_);
v___x_1121_ = lean_apply_1(v_inst_1117_, v___x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lake_logInfo___boxed(lean_object* v_m_1122_, lean_object* v_inst_1123_, lean_object* v_inst_1124_, lean_object* v_message_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lake_logInfo(v_m_1122_, v_inst_1123_, v_inst_1124_, v_message_1125_);
lean_dec_ref(v_inst_1123_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lake_logWarning___redArg(lean_object* v_inst_1127_, lean_object* v_message_1128_){
_start:
{
uint8_t v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1129_ = 2;
v___x_1130_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1130_, 0, v_message_1128_);
lean_ctor_set_uint8(v___x_1130_, sizeof(void*)*1, v___x_1129_);
v___x_1131_ = lean_apply_1(v_inst_1127_, v___x_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lake_logWarning(lean_object* v_m_1132_, lean_object* v_inst_1133_, lean_object* v_message_1134_){
_start:
{
uint8_t v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1135_ = 2;
v___x_1136_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1136_, 0, v_message_1134_);
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*1, v___x_1135_);
v___x_1137_ = lean_apply_1(v_inst_1133_, v___x_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lake_logError___redArg(lean_object* v_inst_1138_, lean_object* v_message_1139_){
_start:
{
uint8_t v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = 3;
v___x_1141_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1141_, 0, v_message_1139_);
lean_ctor_set_uint8(v___x_1141_, sizeof(void*)*1, v___x_1140_);
v___x_1142_ = lean_apply_1(v_inst_1138_, v___x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lake_logError(lean_object* v_m_1143_, lean_object* v_inst_1144_, lean_object* v_message_1145_){
_start:
{
uint8_t v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1146_ = 3;
v___x_1147_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1147_, 0, v_message_1145_);
lean_ctor_set_uint8(v___x_1147_, sizeof(void*)*1, v___x_1146_);
v___x_1148_ = lean_apply_1(v_inst_1144_, v___x_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lake_logSerialMessage___redArg(lean_object* v_msg_1149_, lean_object* v_inst_1150_, lean_object* v_inst_1151_){
_start:
{
lean_object* v_toBaseMessage_1152_; lean_object* v_toApplicative_1153_; uint8_t v_isSilent_1154_; 
v_toBaseMessage_1152_ = lean_ctor_get(v_msg_1149_, 0);
v_toApplicative_1153_ = lean_ctor_get(v_inst_1150_, 0);
lean_inc_ref(v_toApplicative_1153_);
lean_dec_ref(v_inst_1150_);
v_isSilent_1154_ = lean_ctor_get_uint8(v_toBaseMessage_1152_, sizeof(void*)*5 + 2);
if (v_isSilent_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
lean_dec_ref(v_toApplicative_1153_);
v___x_1155_ = l_Lake_LogEntry_ofSerialMessage(v_msg_1149_);
v___x_1156_ = lean_apply_1(v_inst_1151_, v___x_1155_);
return v___x_1156_;
}
else
{
lean_object* v_toPure_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
lean_dec(v_inst_1151_);
lean_dec_ref(v_msg_1149_);
v_toPure_1157_ = lean_ctor_get(v_toApplicative_1153_, 1);
lean_inc(v_toPure_1157_);
lean_dec_ref(v_toApplicative_1153_);
v___x_1158_ = lean_box(0);
v___x_1159_ = lean_apply_2(v_toPure_1157_, lean_box(0), v___x_1158_);
return v___x_1159_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logSerialMessage(lean_object* v_m_1160_, lean_object* v_msg_1161_, lean_object* v_inst_1162_, lean_object* v_inst_1163_){
_start:
{
lean_object* v_toBaseMessage_1164_; lean_object* v_toApplicative_1165_; uint8_t v_isSilent_1166_; 
v_toBaseMessage_1164_ = lean_ctor_get(v_msg_1161_, 0);
v_toApplicative_1165_ = lean_ctor_get(v_inst_1162_, 0);
lean_inc_ref(v_toApplicative_1165_);
lean_dec_ref(v_inst_1162_);
v_isSilent_1166_ = lean_ctor_get_uint8(v_toBaseMessage_1164_, sizeof(void*)*5 + 2);
if (v_isSilent_1166_ == 0)
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_dec_ref(v_toApplicative_1165_);
v___x_1167_ = l_Lake_LogEntry_ofSerialMessage(v_msg_1161_);
v___x_1168_ = lean_apply_1(v_inst_1163_, v___x_1167_);
return v___x_1168_;
}
else
{
lean_object* v_toPure_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
lean_dec(v_inst_1163_);
lean_dec_ref(v_msg_1161_);
v_toPure_1169_ = lean_ctor_get(v_toApplicative_1165_, 1);
lean_inc(v_toPure_1169_);
lean_dec_ref(v_toApplicative_1165_);
v___x_1170_ = lean_box(0);
v___x_1171_ = lean_apply_2(v_toPure_1169_, lean_box(0), v___x_1170_);
return v___x_1171_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logMessage___redArg___lam__0(lean_object* v_inst_1172_, lean_object* v_____do__lift_1173_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = lean_apply_1(v_inst_1172_, v_____do__lift_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lake_logMessage___redArg(lean_object* v_msg_1175_, lean_object* v_inst_1176_, lean_object* v_inst_1177_, lean_object* v_inst_1178_){
_start:
{
uint8_t v_isSilent_1179_; 
v_isSilent_1179_ = lean_ctor_get_uint8(v_msg_1175_, sizeof(void*)*5 + 2);
if (v_isSilent_1179_ == 0)
{
lean_object* v_toBind_1180_; lean_object* v___f_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v_toBind_1180_ = lean_ctor_get(v_inst_1176_, 1);
lean_inc(v_toBind_1180_);
lean_dec_ref(v_inst_1176_);
v___f_1181_ = lean_alloc_closure((void*)(l_Lake_logMessage___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1181_, 0, v_inst_1177_);
v___x_1182_ = lean_alloc_closure((void*)(l_Lake_LogEntry_ofMessage___boxed), 2, 1);
lean_closure_set(v___x_1182_, 0, v_msg_1175_);
v___x_1183_ = lean_apply_2(v_inst_1178_, lean_box(0), v___x_1182_);
v___x_1184_ = lean_apply_4(v_toBind_1180_, lean_box(0), lean_box(0), v___x_1183_, v___f_1181_);
return v___x_1184_;
}
else
{
lean_object* v_toApplicative_1185_; lean_object* v_toPure_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v_toApplicative_1185_ = lean_ctor_get(v_inst_1176_, 0);
lean_inc_ref(v_toApplicative_1185_);
lean_dec(v_inst_1178_);
lean_dec(v_inst_1177_);
lean_dec_ref(v_inst_1176_);
lean_dec_ref(v_msg_1175_);
v_toPure_1186_ = lean_ctor_get(v_toApplicative_1185_, 1);
lean_inc(v_toPure_1186_);
lean_dec_ref(v_toApplicative_1185_);
v___x_1187_ = lean_box(0);
v___x_1188_ = lean_apply_2(v_toPure_1186_, lean_box(0), v___x_1187_);
return v___x_1188_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logMessage(lean_object* v_m_1189_, lean_object* v_msg_1190_, lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_inst_1193_){
_start:
{
uint8_t v_isSilent_1194_; 
v_isSilent_1194_ = lean_ctor_get_uint8(v_msg_1190_, sizeof(void*)*5 + 2);
if (v_isSilent_1194_ == 0)
{
lean_object* v_toBind_1195_; lean_object* v___f_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v_toBind_1195_ = lean_ctor_get(v_inst_1191_, 1);
lean_inc(v_toBind_1195_);
lean_dec_ref(v_inst_1191_);
v___f_1196_ = lean_alloc_closure((void*)(l_Lake_logMessage___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1196_, 0, v_inst_1192_);
v___x_1197_ = lean_alloc_closure((void*)(l_Lake_LogEntry_ofMessage___boxed), 2, 1);
lean_closure_set(v___x_1197_, 0, v_msg_1190_);
v___x_1198_ = lean_apply_2(v_inst_1193_, lean_box(0), v___x_1197_);
v___x_1199_ = lean_apply_4(v_toBind_1195_, lean_box(0), lean_box(0), v___x_1198_, v___f_1196_);
return v___x_1199_;
}
else
{
lean_object* v_toApplicative_1200_; lean_object* v_toPure_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v_toApplicative_1200_ = lean_ctor_get(v_inst_1191_, 0);
lean_inc_ref(v_toApplicative_1200_);
lean_dec(v_inst_1193_);
lean_dec(v_inst_1192_);
lean_dec_ref(v_inst_1191_);
lean_dec_ref(v_msg_1190_);
v_toPure_1201_ = lean_ctor_get(v_toApplicative_1200_, 1);
lean_inc(v_toPure_1201_);
lean_dec_ref(v_toApplicative_1200_);
v___x_1202_ = lean_box(0);
v___x_1203_ = lean_apply_2(v_toPure_1201_, lean_box(0), v___x_1202_);
return v___x_1203_;
}
}
}
lean_object* l_Lake_logToStream(lean_object* v_e_1204_, lean_object* v_out_1205_, uint8_t v_minLv_1206_, uint8_t v_useAnsi_1207_){
_start:
{
uint8_t v_level_1209_; uint8_t v___x_1210_; 
v_level_1209_ = lean_ctor_get_uint8(v_e_1204_, sizeof(void*)*1);
v___x_1210_ = l_Lake_instOrdLogLevel_ord(v_minLv_1206_, v_level_1209_);
if (v___x_1210_ == 2)
{
lean_object* v___x_1211_; 
lean_dec_ref(v_out_1205_);
v___x_1211_ = lean_box(0);
return v___x_1211_;
}
else
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = l_Lake_LogEntry_toString(v_e_1204_, v_useAnsi_1207_);
v___x_1213_ = l_IO_FS_Stream_putStrLn(v_out_1205_, v___x_1212_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_a_1214_);
lean_dec_ref_known(v___x_1213_, 1);
return v_a_1214_;
}
else
{
lean_object* v___x_1215_; 
lean_dec_ref_known(v___x_1213_, 1);
v___x_1215_ = lean_box(0);
return v___x_1215_;
}
}
}
}
LEAN_EXPORT void l_Lake_logToStream_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1204_ = stack[0].m_obj;
lean_object* v_out_1205_ = stack[1].m_obj;
uint8_t v_minLv_1206_ = stack[2].m_num;
uint8_t v_useAnsi_1207_ = stack[3].m_num;
lean_object* v_res_1216_;
v_res_1216_ = l_Lake_logToStream(v_e_1204_, v_out_1205_, v_minLv_1206_, v_useAnsi_1207_);
stack->m_obj
 = v_res_1216_;
}
LEAN_EXPORT lean_object* l_Lake_logToStream___boxed(lean_object* v_e_1217_, lean_object* v_out_1218_, lean_object* v_minLv_1219_, lean_object* v_useAnsi_1220_, lean_object* v_a_1221_){
_start:
{
uint8_t v_minLv_boxed_1222_; uint8_t v_useAnsi_boxed_1223_; lean_object* v_res_1224_; 
v_minLv_boxed_1222_ = lean_unbox(v_minLv_1219_);
v_useAnsi_boxed_1223_ = lean_unbox(v_useAnsi_1220_);
v_res_1224_ = l_Lake_logToStream(v_e_1217_, v_out_1218_, v_minLv_boxed_1222_, v_useAnsi_boxed_1223_);
lean_dec_ref(v_e_1217_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___redArg___lam__0(lean_object* v_inst_1225_, lean_object* v_x_1226_){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = lean_box(0);
v___x_1228_ = lean_apply_2(v_inst_1225_, lean_box(0), v___x_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___redArg___lam__0___boxed(lean_object* v_inst_1229_, lean_object* v_x_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lake_MonadLog_nop___redArg___lam__0(v_inst_1229_, v_x_1230_);
lean_dec_ref(v_x_1230_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___redArg(lean_object* v_inst_1232_){
_start:
{
lean_object* v___f_1233_; 
v___f_1233_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1233_, 0, v_inst_1232_);
return v___f_1233_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop(lean_object* v_m_1234_, lean_object* v_inst_1235_){
_start:
{
lean_object* v___f_1236_; 
v___f_1236_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1236_, 0, v_inst_1235_);
return v___f_1236_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instInhabitedOfPure___redArg(lean_object* v_inst_1237_){
_start:
{
lean_object* v___f_1238_; 
v___f_1238_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1238_, 0, v_inst_1237_);
return v___f_1238_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instInhabitedOfPure(lean_object* v_m_1239_, lean_object* v_inst_1240_){
_start:
{
lean_object* v___f_1241_; 
v___f_1241_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1241_, 0, v_inst_1240_);
return v___f_1241_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift___redArg___lam__0(lean_object* v_self_1242_, lean_object* v_inst_1243_, lean_object* v_e_1244_){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = lean_apply_1(v_self_1242_, v_e_1244_);
v___x_1246_ = lean_apply_2(v_inst_1243_, lean_box(0), v___x_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift___redArg(lean_object* v_inst_1247_, lean_object* v_self_1248_){
_start:
{
lean_object* v___f_1249_; 
v___f_1249_ = lean_alloc_closure((void*)(l_Lake_MonadLog_lift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1249_, 0, v_self_1248_);
lean_closure_set(v___f_1249_, 1, v_inst_1247_);
return v___f_1249_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift(lean_object* v_m_1250_, lean_object* v_n_1251_, lean_object* v_inst_1252_, lean_object* v_self_1253_){
_start:
{
lean_object* v___f_1254_; 
v___f_1254_ = lean_alloc_closure((void*)(l_Lake_MonadLog_lift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1254_, 0, v_self_1253_);
lean_closure_set(v___f_1254_, 1, v_inst_1252_);
return v___f_1254_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift___redArg___lam__0(lean_object* v_methods_1255_, lean_object* v_inst_1256_, lean_object* v_e_1257_){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = lean_apply_1(v_methods_1255_, v_e_1257_);
v___x_1259_ = lean_apply_2(v_inst_1256_, lean_box(0), v___x_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift___redArg(lean_object* v_inst_1260_, lean_object* v_methods_1261_){
_start:
{
lean_object* v___f_1262_; 
v___f_1262_ = lean_alloc_closure((void*)(l_Lake_MonadLog_instOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1262_, 0, v_methods_1261_);
lean_closure_set(v___f_1262_, 1, v_inst_1260_);
return v___f_1262_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift(lean_object* v_m_1263_, lean_object* v_n_1264_, lean_object* v_inst_1265_, lean_object* v_methods_1266_){
_start:
{
lean_object* v___f_1267_; 
v___f_1267_ = lean_alloc_closure((void*)(l_Lake_MonadLog_instOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1267_, 0, v_methods_1266_);
lean_closure_set(v___f_1267_, 1, v_inst_1265_);
return v___f_1267_;
}
}
lean_object* l_Lake_MonadLog_stream___redArg___lam__0(lean_object* v_out_1268_, uint8_t v_minLv_1269_, uint8_t v_useAnsi_1270_, lean_object* v_inst_1271_, lean_object* v_e_1272_){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1273_ = lean_box(v_minLv_1269_);
v___x_1274_ = lean_box(v_useAnsi_1270_);
v___x_1275_ = lean_alloc_closure((void*)(l_Lake_logToStream___boxed), 5, 4);
lean_closure_set(v___x_1275_, 0, v_e_1272_);
lean_closure_set(v___x_1275_, 1, v_out_1268_);
lean_closure_set(v___x_1275_, 2, v___x_1273_);
lean_closure_set(v___x_1275_, 3, v___x_1274_);
v___x_1276_ = lean_apply_2(v_inst_1271_, lean_box(0), v___x_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT void l_Lake_MonadLog_stream___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_out_1268_ = stack[0].m_obj;
uint8_t v_minLv_1269_ = stack[1].m_num;
uint8_t v_useAnsi_1270_ = stack[2].m_num;
lean_object* v_inst_1271_ = stack[3].m_obj;
lean_object* v_e_1272_ = stack[4].m_obj;
lean_object* v_res_1277_;
v_res_1277_ = l_Lake_MonadLog_stream___redArg___lam__0(v_out_1268_, v_minLv_1269_, v_useAnsi_1270_, v_inst_1271_, v_e_1272_);
stack->m_obj
 = v_res_1277_;
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg___lam__0___boxed(lean_object* v_out_1278_, lean_object* v_minLv_1279_, lean_object* v_useAnsi_1280_, lean_object* v_inst_1281_, lean_object* v_e_1282_){
_start:
{
uint8_t v_minLv_boxed_1283_; uint8_t v_useAnsi_boxed_1284_; lean_object* v_res_1285_; 
v_minLv_boxed_1283_ = lean_unbox(v_minLv_1279_);
v_useAnsi_boxed_1284_ = lean_unbox(v_useAnsi_1280_);
v_res_1285_ = l_Lake_MonadLog_stream___redArg___lam__0(v_out_1278_, v_minLv_boxed_1283_, v_useAnsi_boxed_1284_, v_inst_1281_, v_e_1282_);
return v_res_1285_;
}
}
lean_object* l_Lake_MonadLog_stream___redArg(lean_object* v_inst_1286_, lean_object* v_out_1287_, uint8_t v_minLv_1288_, uint8_t v_useAnsi_1289_){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___f_1292_; 
v___x_1290_ = lean_box(v_minLv_1288_);
v___x_1291_ = lean_box(v_useAnsi_1289_);
v___f_1292_ = lean_alloc_closure((void*)(l_Lake_MonadLog_stream___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1292_, 0, v_out_1287_);
lean_closure_set(v___f_1292_, 1, v___x_1290_);
lean_closure_set(v___f_1292_, 2, v___x_1291_);
lean_closure_set(v___f_1292_, 3, v_inst_1286_);
return v___f_1292_;
}
}
LEAN_EXPORT void l_Lake_MonadLog_stream___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1286_ = stack[0].m_obj;
lean_object* v_out_1287_ = stack[1].m_obj;
uint8_t v_minLv_1288_ = stack[2].m_num;
uint8_t v_useAnsi_1289_ = stack[3].m_num;
lean_object* v_res_1293_;
v_res_1293_ = l_Lake_MonadLog_stream___redArg(v_inst_1286_, v_out_1287_, v_minLv_1288_, v_useAnsi_1289_);
stack->m_obj
 = v_res_1293_;
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg___boxed(lean_object* v_inst_1294_, lean_object* v_out_1295_, lean_object* v_minLv_1296_, lean_object* v_useAnsi_1297_){
_start:
{
uint8_t v_minLv_boxed_1298_; uint8_t v_useAnsi_boxed_1299_; lean_object* v_res_1300_; 
v_minLv_boxed_1298_ = lean_unbox(v_minLv_1296_);
v_useAnsi_boxed_1299_ = lean_unbox(v_useAnsi_1297_);
v_res_1300_ = l_Lake_MonadLog_stream___redArg(v_inst_1294_, v_out_1295_, v_minLv_boxed_1298_, v_useAnsi_boxed_1299_);
return v_res_1300_;
}
}
lean_object* l_Lake_MonadLog_stream(lean_object* v_m_1301_, lean_object* v_inst_1302_, lean_object* v_out_1303_, uint8_t v_minLv_1304_, uint8_t v_useAnsi_1305_){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___f_1308_; 
v___x_1306_ = lean_box(v_minLv_1304_);
v___x_1307_ = lean_box(v_useAnsi_1305_);
v___f_1308_ = lean_alloc_closure((void*)(l_Lake_MonadLog_stream___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1308_, 0, v_out_1303_);
lean_closure_set(v___f_1308_, 1, v___x_1306_);
lean_closure_set(v___f_1308_, 2, v___x_1307_);
lean_closure_set(v___f_1308_, 3, v_inst_1302_);
return v___f_1308_;
}
}
LEAN_EXPORT void l_Lake_MonadLog_stream_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1302_ = stack[1].m_obj;
lean_object* v_out_1303_ = stack[2].m_obj;
uint8_t v_minLv_1304_ = stack[3].m_num;
uint8_t v_useAnsi_1305_ = stack[4].m_num;
lean_object* v_res_1309_;
v_res_1309_ = l_Lake_MonadLog_stream(lean_box(0), v_inst_1302_, v_out_1303_, v_minLv_1304_, v_useAnsi_1305_);
stack->m_obj
 = v_res_1309_;
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___boxed(lean_object* v_m_1310_, lean_object* v_inst_1311_, lean_object* v_out_1312_, lean_object* v_minLv_1313_, lean_object* v_useAnsi_1314_){
_start:
{
uint8_t v_minLv_boxed_1315_; uint8_t v_useAnsi_boxed_1316_; lean_object* v_res_1317_; 
v_minLv_boxed_1315_ = lean_unbox(v_minLv_1313_);
v_useAnsi_boxed_1316_ = lean_unbox(v_useAnsi_1314_);
v_res_1317_ = l_Lake_MonadLog_stream(v_m_1310_, v_inst_1311_, v_out_1312_, v_minLv_boxed_1315_, v_useAnsi_boxed_1316_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_error___redArg___lam__0(lean_object* v_failure_1318_, lean_object* v_x_1319_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = lean_apply_1(v_failure_1318_, lean_box(0));
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_error___redArg(lean_object* v_inst_1321_, lean_object* v_inst_1322_, lean_object* v_msg_1323_){
_start:
{
lean_object* v_toApplicative_1324_; lean_object* v_failure_1325_; lean_object* v_toSeqRight_1326_; lean_object* v___f_1327_; uint8_t v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v_toApplicative_1324_ = lean_ctor_get(v_inst_1321_, 0);
lean_inc_ref(v_toApplicative_1324_);
v_failure_1325_ = lean_ctor_get(v_inst_1321_, 1);
lean_inc(v_failure_1325_);
lean_dec_ref(v_inst_1321_);
v_toSeqRight_1326_ = lean_ctor_get(v_toApplicative_1324_, 4);
lean_inc(v_toSeqRight_1326_);
lean_dec_ref(v_toApplicative_1324_);
v___f_1327_ = lean_alloc_closure((void*)(l_Lake_MonadLog_error___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1327_, 0, v_failure_1325_);
v___x_1328_ = 3;
v___x_1329_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1329_, 0, v_msg_1323_);
lean_ctor_set_uint8(v___x_1329_, sizeof(void*)*1, v___x_1328_);
v___x_1330_ = lean_apply_1(v_inst_1322_, v___x_1329_);
v___x_1331_ = lean_apply_4(v_toSeqRight_1326_, lean_box(0), lean_box(0), v___x_1330_, v___f_1327_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_error(lean_object* v_m_1332_, lean_object* v_00_u03b1_1333_, lean_object* v_inst_1334_, lean_object* v_inst_1335_, lean_object* v_msg_1336_){
_start:
{
lean_object* v_toApplicative_1337_; lean_object* v_failure_1338_; lean_object* v_toSeqRight_1339_; lean_object* v___f_1340_; uint8_t v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v_toApplicative_1337_ = lean_ctor_get(v_inst_1334_, 0);
lean_inc_ref(v_toApplicative_1337_);
v_failure_1338_ = lean_ctor_get(v_inst_1334_, 1);
lean_inc(v_failure_1338_);
lean_dec_ref(v_inst_1334_);
v_toSeqRight_1339_ = lean_ctor_get(v_toApplicative_1337_, 4);
lean_inc(v_toSeqRight_1339_);
lean_dec_ref(v_toApplicative_1337_);
v___f_1340_ = lean_alloc_closure((void*)(l_Lake_MonadLog_error___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1340_, 0, v_failure_1338_);
v___x_1341_ = 3;
v___x_1342_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1342_, 0, v_msg_1336_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*1, v___x_1341_);
v___x_1343_ = lean_apply_1(v_inst_1335_, v___x_1342_);
v___x_1344_ = lean_apply_4(v_toSeqRight_1339_, lean_box(0), lean_box(0), v___x_1343_, v___f_1340_);
return v___x_1344_;
}
}
lean_object* l_Lake_OutStream_logEntry(lean_object* v_self_1345_, lean_object* v_e_1346_, uint8_t v_minLv_1347_, uint8_t v_ansiMode_1348_){
_start:
{
lean_object* v___x_1350_; uint8_t v___x_1351_; lean_object* v___x_1352_; 
v___x_1350_ = l_Lake_OutStream_get(v_self_1345_);
lean_inc_ref(v___x_1350_);
v___x_1351_ = l_Lake_AnsiMode_isEnabled(v___x_1350_, v_ansiMode_1348_);
v___x_1352_ = l_Lake_logToStream(v_e_1346_, v___x_1350_, v_minLv_1347_, v___x_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT void l_Lake_OutStream_logEntry_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1345_ = stack[0].m_obj;
lean_object* v_e_1346_ = stack[1].m_obj;
uint8_t v_minLv_1347_ = stack[2].m_num;
uint8_t v_ansiMode_1348_ = stack[3].m_num;
lean_object* v_res_1353_;
v_res_1353_ = l_Lake_OutStream_logEntry(v_self_1345_, v_e_1346_, v_minLv_1347_, v_ansiMode_1348_);
stack->m_obj
 = v_res_1353_;
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logEntry___boxed(lean_object* v_self_1354_, lean_object* v_e_1355_, lean_object* v_minLv_1356_, lean_object* v_ansiMode_1357_, lean_object* v_a_1358_){
_start:
{
uint8_t v_minLv_boxed_1359_; uint8_t v_ansiMode_boxed_1360_; lean_object* v_res_1361_; 
v_minLv_boxed_1359_ = lean_unbox(v_minLv_1356_);
v_ansiMode_boxed_1360_ = lean_unbox(v_ansiMode_1357_);
v_res_1361_ = l_Lake_OutStream_logEntry(v_self_1354_, v_e_1355_, v_minLv_boxed_1359_, v_ansiMode_boxed_1360_);
lean_dec_ref(v_e_1355_);
lean_dec(v_self_1354_);
return v_res_1361_;
}
}
lean_object* l_Lake_OutStream_logger___redArg___lam__0(lean_object* v_out_1362_, uint8_t v_minLv_1363_, uint8_t v_ansiMode_1364_, lean_object* v_inst_1365_, lean_object* v_e_1366_){
_start:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1367_ = lean_box(v_minLv_1363_);
v___x_1368_ = lean_box(v_ansiMode_1364_);
v___x_1369_ = lean_alloc_closure((void*)(l_Lake_OutStream_logEntry___boxed), 5, 4);
lean_closure_set(v___x_1369_, 0, v_out_1362_);
lean_closure_set(v___x_1369_, 1, v_e_1366_);
lean_closure_set(v___x_1369_, 2, v___x_1367_);
lean_closure_set(v___x_1369_, 3, v___x_1368_);
v___x_1370_ = lean_apply_2(v_inst_1365_, lean_box(0), v___x_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT void l_Lake_OutStream_logger___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_out_1362_ = stack[0].m_obj;
uint8_t v_minLv_1363_ = stack[1].m_num;
uint8_t v_ansiMode_1364_ = stack[2].m_num;
lean_object* v_inst_1365_ = stack[3].m_obj;
lean_object* v_e_1366_ = stack[4].m_obj;
lean_object* v_res_1371_;
v_res_1371_ = l_Lake_OutStream_logger___redArg___lam__0(v_out_1362_, v_minLv_1363_, v_ansiMode_1364_, v_inst_1365_, v_e_1366_);
stack->m_obj
 = v_res_1371_;
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg___lam__0___boxed(lean_object* v_out_1372_, lean_object* v_minLv_1373_, lean_object* v_ansiMode_1374_, lean_object* v_inst_1375_, lean_object* v_e_1376_){
_start:
{
uint8_t v_minLv_boxed_1377_; uint8_t v_ansiMode_boxed_1378_; lean_object* v_res_1379_; 
v_minLv_boxed_1377_ = lean_unbox(v_minLv_1373_);
v_ansiMode_boxed_1378_ = lean_unbox(v_ansiMode_1374_);
v_res_1379_ = l_Lake_OutStream_logger___redArg___lam__0(v_out_1372_, v_minLv_boxed_1377_, v_ansiMode_boxed_1378_, v_inst_1375_, v_e_1376_);
return v_res_1379_;
}
}
lean_object* l_Lake_OutStream_logger___redArg(lean_object* v_inst_1380_, lean_object* v_out_1381_, uint8_t v_minLv_1382_, uint8_t v_ansiMode_1383_){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___f_1386_; 
v___x_1384_ = lean_box(v_minLv_1382_);
v___x_1385_ = lean_box(v_ansiMode_1383_);
v___f_1386_ = lean_alloc_closure((void*)(l_Lake_OutStream_logger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1386_, 0, v_out_1381_);
lean_closure_set(v___f_1386_, 1, v___x_1384_);
lean_closure_set(v___f_1386_, 2, v___x_1385_);
lean_closure_set(v___f_1386_, 3, v_inst_1380_);
return v___f_1386_;
}
}
LEAN_EXPORT void l_Lake_OutStream_logger___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1380_ = stack[0].m_obj;
lean_object* v_out_1381_ = stack[1].m_obj;
uint8_t v_minLv_1382_ = stack[2].m_num;
uint8_t v_ansiMode_1383_ = stack[3].m_num;
lean_object* v_res_1387_;
v_res_1387_ = l_Lake_OutStream_logger___redArg(v_inst_1380_, v_out_1381_, v_minLv_1382_, v_ansiMode_1383_);
stack->m_obj
 = v_res_1387_;
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg___boxed(lean_object* v_inst_1388_, lean_object* v_out_1389_, lean_object* v_minLv_1390_, lean_object* v_ansiMode_1391_){
_start:
{
uint8_t v_minLv_boxed_1392_; uint8_t v_ansiMode_boxed_1393_; lean_object* v_res_1394_; 
v_minLv_boxed_1392_ = lean_unbox(v_minLv_1390_);
v_ansiMode_boxed_1393_ = lean_unbox(v_ansiMode_1391_);
v_res_1394_ = l_Lake_OutStream_logger___redArg(v_inst_1388_, v_out_1389_, v_minLv_boxed_1392_, v_ansiMode_boxed_1393_);
return v_res_1394_;
}
}
lean_object* l_Lake_OutStream_logger(lean_object* v_m_1395_, lean_object* v_inst_1396_, lean_object* v_out_1397_, uint8_t v_minLv_1398_, uint8_t v_ansiMode_1399_){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___f_1402_; 
v___x_1400_ = lean_box(v_minLv_1398_);
v___x_1401_ = lean_box(v_ansiMode_1399_);
v___f_1402_ = lean_alloc_closure((void*)(l_Lake_OutStream_logger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1402_, 0, v_out_1397_);
lean_closure_set(v___f_1402_, 1, v___x_1400_);
lean_closure_set(v___f_1402_, 2, v___x_1401_);
lean_closure_set(v___f_1402_, 3, v_inst_1396_);
return v___f_1402_;
}
}
LEAN_EXPORT void l_Lake_OutStream_logger_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1396_ = stack[1].m_obj;
lean_object* v_out_1397_ = stack[2].m_obj;
uint8_t v_minLv_1398_ = stack[3].m_num;
uint8_t v_ansiMode_1399_ = stack[4].m_num;
lean_object* v_res_1403_;
v_res_1403_ = l_Lake_OutStream_logger(lean_box(0), v_inst_1396_, v_out_1397_, v_minLv_1398_, v_ansiMode_1399_);
stack->m_obj
 = v_res_1403_;
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___boxed(lean_object* v_m_1404_, lean_object* v_inst_1405_, lean_object* v_out_1406_, lean_object* v_minLv_1407_, lean_object* v_ansiMode_1408_){
_start:
{
uint8_t v_minLv_boxed_1409_; uint8_t v_ansiMode_boxed_1410_; lean_object* v_res_1411_; 
v_minLv_boxed_1409_ = lean_unbox(v_minLv_1407_);
v_ansiMode_boxed_1410_ = lean_unbox(v_ansiMode_1408_);
v_res_1411_ = l_Lake_OutStream_logger(v_m_1404_, v_inst_1405_, v_out_1406_, v_minLv_boxed_1409_, v_ansiMode_boxed_1410_);
return v_res_1411_;
}
}
lean_object* l_Lake_MonadLog_stdout___redArg___lam__0(lean_object* v___x_1412_, uint8_t v_minLv_1413_, uint8_t v_ansiMode_1414_, lean_object* v_inst_1415_, lean_object* v_e_1416_){
_start:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1417_ = lean_box(v_minLv_1413_);
v___x_1418_ = lean_box(v_ansiMode_1414_);
v___x_1419_ = lean_alloc_closure((void*)(l_Lake_OutStream_logEntry___boxed), 5, 4);
lean_closure_set(v___x_1419_, 0, v___x_1412_);
lean_closure_set(v___x_1419_, 1, v_e_1416_);
lean_closure_set(v___x_1419_, 2, v___x_1417_);
lean_closure_set(v___x_1419_, 3, v___x_1418_);
v___x_1420_ = lean_apply_2(v_inst_1415_, lean_box(0), v___x_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT void l_Lake_MonadLog_stdout___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1412_ = stack[0].m_obj;
uint8_t v_minLv_1413_ = stack[1].m_num;
uint8_t v_ansiMode_1414_ = stack[2].m_num;
lean_object* v_inst_1415_ = stack[3].m_obj;
lean_object* v_e_1416_ = stack[4].m_obj;
lean_object* v_res_1421_;
v_res_1421_ = l_Lake_MonadLog_stdout___redArg___lam__0(v___x_1412_, v_minLv_1413_, v_ansiMode_1414_, v_inst_1415_, v_e_1416_);
stack->m_obj
 = v_res_1421_;
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg___lam__0___boxed(lean_object* v___x_1422_, lean_object* v_minLv_1423_, lean_object* v_ansiMode_1424_, lean_object* v_inst_1425_, lean_object* v_e_1426_){
_start:
{
uint8_t v_minLv_boxed_1427_; uint8_t v_ansiMode_boxed_1428_; lean_object* v_res_1429_; 
v_minLv_boxed_1427_ = lean_unbox(v_minLv_1423_);
v_ansiMode_boxed_1428_ = lean_unbox(v_ansiMode_1424_);
v_res_1429_ = l_Lake_MonadLog_stdout___redArg___lam__0(v___x_1422_, v_minLv_boxed_1427_, v_ansiMode_boxed_1428_, v_inst_1425_, v_e_1426_);
return v_res_1429_;
}
}
lean_object* l_Lake_MonadLog_stdout___redArg(lean_object* v_inst_1430_, uint8_t v_minLv_1431_, uint8_t v_ansiMode_1432_){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___f_1436_; 
v___x_1433_ = lean_box(0);
v___x_1434_ = lean_box(v_minLv_1431_);
v___x_1435_ = lean_box(v_ansiMode_1432_);
v___f_1436_ = lean_alloc_closure((void*)(l_Lake_MonadLog_stdout___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1436_, 0, v___x_1433_);
lean_closure_set(v___f_1436_, 1, v___x_1434_);
lean_closure_set(v___f_1436_, 2, v___x_1435_);
lean_closure_set(v___f_1436_, 3, v_inst_1430_);
return v___f_1436_;
}
}
LEAN_EXPORT void l_Lake_MonadLog_stdout___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1430_ = stack[0].m_obj;
uint8_t v_minLv_1431_ = stack[1].m_num;
uint8_t v_ansiMode_1432_ = stack[2].m_num;
lean_object* v_res_1437_;
v_res_1437_ = l_Lake_MonadLog_stdout___redArg(v_inst_1430_, v_minLv_1431_, v_ansiMode_1432_);
stack->m_obj
 = v_res_1437_;
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg___boxed(lean_object* v_inst_1438_, lean_object* v_minLv_1439_, lean_object* v_ansiMode_1440_){
_start:
{
uint8_t v_minLv_boxed_1441_; uint8_t v_ansiMode_boxed_1442_; lean_object* v_res_1443_; 
v_minLv_boxed_1441_ = lean_unbox(v_minLv_1439_);
v_ansiMode_boxed_1442_ = lean_unbox(v_ansiMode_1440_);
v_res_1443_ = l_Lake_MonadLog_stdout___redArg(v_inst_1438_, v_minLv_boxed_1441_, v_ansiMode_boxed_1442_);
return v_res_1443_;
}
}
lean_object* l_Lake_MonadLog_stdout(lean_object* v_m_1444_, lean_object* v_inst_1445_, uint8_t v_minLv_1446_, uint8_t v_ansiMode_1447_){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___f_1451_; 
v___x_1448_ = lean_box(0);
v___x_1449_ = lean_box(v_minLv_1446_);
v___x_1450_ = lean_box(v_ansiMode_1447_);
v___f_1451_ = lean_alloc_closure((void*)(l_Lake_MonadLog_stdout___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1451_, 0, v___x_1448_);
lean_closure_set(v___f_1451_, 1, v___x_1449_);
lean_closure_set(v___f_1451_, 2, v___x_1450_);
lean_closure_set(v___f_1451_, 3, v_inst_1445_);
return v___f_1451_;
}
}
LEAN_EXPORT void l_Lake_MonadLog_stdout_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1445_ = stack[1].m_obj;
uint8_t v_minLv_1446_ = stack[2].m_num;
uint8_t v_ansiMode_1447_ = stack[3].m_num;
lean_object* v_res_1452_;
v_res_1452_ = l_Lake_MonadLog_stdout(lean_box(0), v_inst_1445_, v_minLv_1446_, v_ansiMode_1447_);
stack->m_obj
 = v_res_1452_;
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___boxed(lean_object* v_m_1453_, lean_object* v_inst_1454_, lean_object* v_minLv_1455_, lean_object* v_ansiMode_1456_){
_start:
{
uint8_t v_minLv_boxed_1457_; uint8_t v_ansiMode_boxed_1458_; lean_object* v_res_1459_; 
v_minLv_boxed_1457_ = lean_unbox(v_minLv_1455_);
v_ansiMode_boxed_1458_ = lean_unbox(v_ansiMode_1456_);
v_res_1459_ = l_Lake_MonadLog_stdout(v_m_1453_, v_inst_1454_, v_minLv_boxed_1457_, v_ansiMode_boxed_1458_);
return v_res_1459_;
}
}
lean_object* l_Lake_MonadLog_stderr___redArg(lean_object* v_inst_1460_, uint8_t v_minLv_1461_, uint8_t v_ansiMode_1462_){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___f_1466_; 
v___x_1463_ = lean_box(1);
v___x_1464_ = lean_box(v_minLv_1461_);
v___x_1465_ = lean_box(v_ansiMode_1462_);
v___f_1466_ = lean_alloc_closure((void*)(l_Lake_MonadLog_stdout___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1466_, 0, v___x_1463_);
lean_closure_set(v___f_1466_, 1, v___x_1464_);
lean_closure_set(v___f_1466_, 2, v___x_1465_);
lean_closure_set(v___f_1466_, 3, v_inst_1460_);
return v___f_1466_;
}
}
LEAN_EXPORT void l_Lake_MonadLog_stderr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1460_ = stack[0].m_obj;
uint8_t v_minLv_1461_ = stack[1].m_num;
uint8_t v_ansiMode_1462_ = stack[2].m_num;
lean_object* v_res_1467_;
v_res_1467_ = l_Lake_MonadLog_stderr___redArg(v_inst_1460_, v_minLv_1461_, v_ansiMode_1462_);
stack->m_obj
 = v_res_1467_;
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___redArg___boxed(lean_object* v_inst_1468_, lean_object* v_minLv_1469_, lean_object* v_ansiMode_1470_){
_start:
{
uint8_t v_minLv_boxed_1471_; uint8_t v_ansiMode_boxed_1472_; lean_object* v_res_1473_; 
v_minLv_boxed_1471_ = lean_unbox(v_minLv_1469_);
v_ansiMode_boxed_1472_ = lean_unbox(v_ansiMode_1470_);
v_res_1473_ = l_Lake_MonadLog_stderr___redArg(v_inst_1468_, v_minLv_boxed_1471_, v_ansiMode_boxed_1472_);
return v_res_1473_;
}
}
lean_object* l_Lake_MonadLog_stderr(lean_object* v_m_1474_, lean_object* v_inst_1475_, uint8_t v_minLv_1476_, uint8_t v_ansiMode_1477_){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___f_1481_; 
v___x_1478_ = lean_box(1);
v___x_1479_ = lean_box(v_minLv_1476_);
v___x_1480_ = lean_box(v_ansiMode_1477_);
v___f_1481_ = lean_alloc_closure((void*)(l_Lake_MonadLog_stdout___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1481_, 0, v___x_1478_);
lean_closure_set(v___f_1481_, 1, v___x_1479_);
lean_closure_set(v___f_1481_, 2, v___x_1480_);
lean_closure_set(v___f_1481_, 3, v_inst_1475_);
return v___f_1481_;
}
}
LEAN_EXPORT void l_Lake_MonadLog_stderr_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1475_ = stack[1].m_obj;
uint8_t v_minLv_1476_ = stack[2].m_num;
uint8_t v_ansiMode_1477_ = stack[3].m_num;
lean_object* v_res_1482_;
v_res_1482_ = l_Lake_MonadLog_stderr(lean_box(0), v_inst_1475_, v_minLv_1476_, v_ansiMode_1477_);
stack->m_obj
 = v_res_1482_;
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___boxed(lean_object* v_m_1483_, lean_object* v_inst_1484_, lean_object* v_minLv_1485_, lean_object* v_ansiMode_1486_){
_start:
{
uint8_t v_minLv_boxed_1487_; uint8_t v_ansiMode_boxed_1488_; lean_object* v_res_1489_; 
v_minLv_boxed_1487_ = lean_unbox(v_minLv_1485_);
v_ansiMode_boxed_1488_ = lean_unbox(v_ansiMode_1486_);
v_res_1489_ = l_Lake_MonadLog_stderr(v_m_1483_, v_inst_1484_, v_minLv_boxed_1487_, v_ansiMode_boxed_1488_);
return v_res_1489_;
}
}
lean_object* l_Lake_OutStream_getLogger___redArg___lam__0(lean_object* v_val_1490_, uint8_t v_minLv_1491_, uint8_t v_val_1492_, lean_object* v_inst_1493_, lean_object* v_e_1494_){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1495_ = lean_box(v_minLv_1491_);
v___x_1496_ = lean_box(v_val_1492_);
v___x_1497_ = lean_alloc_closure((void*)(l_Lake_logToStream___boxed), 5, 4);
lean_closure_set(v___x_1497_, 0, v_e_1494_);
lean_closure_set(v___x_1497_, 1, v_val_1490_);
lean_closure_set(v___x_1497_, 2, v___x_1495_);
lean_closure_set(v___x_1497_, 3, v___x_1496_);
v___x_1498_ = lean_apply_2(v_inst_1493_, lean_box(0), v___x_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT void l_Lake_OutStream_getLogger___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1490_ = stack[0].m_obj;
uint8_t v_minLv_1491_ = stack[1].m_num;
uint8_t v_val_1492_ = stack[2].m_num;
lean_object* v_inst_1493_ = stack[3].m_obj;
lean_object* v_e_1494_ = stack[4].m_obj;
lean_object* v_res_1499_;
v_res_1499_ = l_Lake_OutStream_getLogger___redArg___lam__0(v_val_1490_, v_minLv_1491_, v_val_1492_, v_inst_1493_, v_e_1494_);
stack->m_obj
 = v_res_1499_;
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg___lam__0___boxed(lean_object* v_val_1500_, lean_object* v_minLv_1501_, lean_object* v_val_1502_, lean_object* v_inst_1503_, lean_object* v_e_1504_){
_start:
{
uint8_t v_minLv_boxed_1505_; uint8_t v_val_105__boxed_1506_; lean_object* v_res_1507_; 
v_minLv_boxed_1505_ = lean_unbox(v_minLv_1501_);
v_val_105__boxed_1506_ = lean_unbox(v_val_1502_);
v_res_1507_ = l_Lake_OutStream_getLogger___redArg___lam__0(v_val_1500_, v_minLv_boxed_1505_, v_val_105__boxed_1506_, v_inst_1503_, v_e_1504_);
return v_res_1507_;
}
}
lean_object* l_Lake_OutStream_getLogger___redArg(lean_object* v_inst_1508_, lean_object* v_out_1509_, uint8_t v_minLv_1510_, uint8_t v_ansiMode_1511_){
_start:
{
lean_object* v___x_1513_; uint8_t v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___f_1517_; 
v___x_1513_ = l_Lake_OutStream_get(v_out_1509_);
lean_inc_ref(v___x_1513_);
v___x_1514_ = l_Lake_AnsiMode_isEnabled(v___x_1513_, v_ansiMode_1511_);
v___x_1515_ = lean_box(v_minLv_1510_);
v___x_1516_ = lean_box(v___x_1514_);
v___f_1517_ = lean_alloc_closure((void*)(l_Lake_OutStream_getLogger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1517_, 0, v___x_1513_);
lean_closure_set(v___f_1517_, 1, v___x_1515_);
lean_closure_set(v___f_1517_, 2, v___x_1516_);
lean_closure_set(v___f_1517_, 3, v_inst_1508_);
return v___f_1517_;
}
}
LEAN_EXPORT void l_Lake_OutStream_getLogger___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1508_ = stack[0].m_obj;
lean_object* v_out_1509_ = stack[1].m_obj;
uint8_t v_minLv_1510_ = stack[2].m_num;
uint8_t v_ansiMode_1511_ = stack[3].m_num;
lean_object* v_res_1518_;
v_res_1518_ = l_Lake_OutStream_getLogger___redArg(v_inst_1508_, v_out_1509_, v_minLv_1510_, v_ansiMode_1511_);
stack->m_obj
 = v_res_1518_;
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg___boxed(lean_object* v_inst_1519_, lean_object* v_out_1520_, lean_object* v_minLv_1521_, lean_object* v_ansiMode_1522_, lean_object* v_a_1523_){
_start:
{
uint8_t v_minLv_boxed_1524_; uint8_t v_ansiMode_boxed_1525_; lean_object* v_res_1526_; 
v_minLv_boxed_1524_ = lean_unbox(v_minLv_1521_);
v_ansiMode_boxed_1525_ = lean_unbox(v_ansiMode_1522_);
v_res_1526_ = l_Lake_OutStream_getLogger___redArg(v_inst_1519_, v_out_1520_, v_minLv_boxed_1524_, v_ansiMode_boxed_1525_);
lean_dec(v_out_1520_);
return v_res_1526_;
}
}
lean_object* l_Lake_OutStream_getLogger(lean_object* v_m_1527_, lean_object* v_inst_1528_, lean_object* v_out_1529_, uint8_t v_minLv_1530_, uint8_t v_ansiMode_1531_){
_start:
{
lean_object* v___x_1533_; uint8_t v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___f_1537_; 
v___x_1533_ = l_Lake_OutStream_get(v_out_1529_);
lean_inc_ref(v___x_1533_);
v___x_1534_ = l_Lake_AnsiMode_isEnabled(v___x_1533_, v_ansiMode_1531_);
v___x_1535_ = lean_box(v_minLv_1530_);
v___x_1536_ = lean_box(v___x_1534_);
v___f_1537_ = lean_alloc_closure((void*)(l_Lake_OutStream_getLogger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1537_, 0, v___x_1533_);
lean_closure_set(v___f_1537_, 1, v___x_1535_);
lean_closure_set(v___f_1537_, 2, v___x_1536_);
lean_closure_set(v___f_1537_, 3, v_inst_1528_);
return v___f_1537_;
}
}
LEAN_EXPORT void l_Lake_OutStream_getLogger_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1528_ = stack[1].m_obj;
lean_object* v_out_1529_ = stack[2].m_obj;
uint8_t v_minLv_1530_ = stack[3].m_num;
uint8_t v_ansiMode_1531_ = stack[4].m_num;
lean_object* v_res_1538_;
v_res_1538_ = l_Lake_OutStream_getLogger(lean_box(0), v_inst_1528_, v_out_1529_, v_minLv_1530_, v_ansiMode_1531_);
stack->m_obj
 = v_res_1538_;
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___boxed(lean_object* v_m_1539_, lean_object* v_inst_1540_, lean_object* v_out_1541_, lean_object* v_minLv_1542_, lean_object* v_ansiMode_1543_, lean_object* v_a_1544_){
_start:
{
uint8_t v_minLv_boxed_1545_; uint8_t v_ansiMode_boxed_1546_; lean_object* v_res_1547_; 
v_minLv_boxed_1545_ = lean_unbox(v_minLv_1542_);
v_ansiMode_boxed_1546_ = lean_unbox(v_ansiMode_1543_);
v_res_1547_ = l_Lake_OutStream_getLogger(v_m_1539_, v_inst_1540_, v_out_1541_, v_minLv_boxed_1545_, v_ansiMode_boxed_1546_);
lean_dec(v_out_1541_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0(lean_object* v_inst_1548_, lean_object* v_inst_1549_, lean_object* v_x_1550_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = lean_apply_2(v_inst_1548_, lean_box(0), v_inst_1549_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0___boxed(lean_object* v_inst_1552_, lean_object* v_inst_1553_, lean_object* v_x_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0(v_inst_1552_, v_inst_1553_, v_x_1554_);
lean_dec(v_x_1554_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___redArg(lean_object* v_inst_1556_, lean_object* v_inst_1557_){
_start:
{
lean_object* v___f_1558_; 
v___f_1558_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1558_, 0, v_inst_1556_);
lean_closure_set(v___f_1558_, 1, v_inst_1557_);
return v___f_1558_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure(lean_object* v_n_1559_, lean_object* v_00_u03b1_1560_, lean_object* v_m_1561_, lean_object* v_inst_1562_, lean_object* v_inst_1563_){
_start:
{
lean_object* v___f_1564_; 
v___f_1564_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1564_, 0, v_inst_1562_);
lean_closure_set(v___f_1564_, 1, v_inst_1563_);
return v___f_1564_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__0(lean_object* v_e_1565_, lean_object* v_inst_1566_, lean_object* v_a_1567_){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = lean_apply_1(v_a_1567_, v_e_1565_);
v___x_1569_ = lean_apply_2(v_inst_1566_, lean_box(0), v___x_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1(lean_object* v_inst_1570_, lean_object* v_inst_1571_, lean_object* v_e_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_toApplicative_1574_; lean_object* v_toBind_1575_; lean_object* v_toPure_1576_; lean_object* v___f_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v_toApplicative_1574_ = lean_ctor_get(v_inst_1570_, 0);
lean_inc_ref(v_toApplicative_1574_);
v_toBind_1575_ = lean_ctor_get(v_inst_1570_, 1);
lean_inc(v_toBind_1575_);
lean_dec_ref(v_inst_1570_);
v_toPure_1576_ = lean_ctor_get(v_toApplicative_1574_, 1);
lean_inc(v_toPure_1576_);
lean_dec_ref(v_toApplicative_1574_);
v___f_1577_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1577_, 0, v_e_1572_);
lean_closure_set(v___f_1577_, 1, v_inst_1571_);
lean_inc(v___y_1573_);
v___x_1578_ = lean_apply_2(v_toPure_1576_, lean_box(0), v___y_1573_);
v___x_1579_ = lean_apply_4(v_toBind_1575_, lean_box(0), lean_box(0), v___x_1578_, v___f_1577_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1___boxed(lean_object* v_inst_1580_, lean_object* v_inst_1581_, lean_object* v_e_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1(v_inst_1580_, v_inst_1581_, v_e_1582_, v___y_1583_);
lean_dec(v___y_1583_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg(lean_object* v_inst_1585_, lean_object* v_inst_1586_){
_start:
{
lean_object* v___f_1587_; 
v___f_1587_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1587_, 0, v_inst_1585_);
lean_closure_set(v___f_1587_, 1, v_inst_1586_);
return v___f_1587_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT(lean_object* v_n_1588_, lean_object* v_m_1589_, lean_object* v_inst_1590_, lean_object* v_inst_1591_){
_start:
{
lean_object* v___f_1592_; 
v___f_1592_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1592_, 0, v_inst_1590_);
lean_closure_set(v___f_1592_, 1, v_inst_1591_);
return v___f_1592_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___redArg(lean_object* v_f_1593_, lean_object* v_self_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
lean_inc(v_a_1595_);
v___x_1596_ = lean_apply_1(v_f_1593_, v_a_1595_);
v___x_1597_ = lean_apply_1(v_self_1594_, v___x_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___redArg___boxed(lean_object* v_f_1598_, lean_object* v_self_1599_, lean_object* v_a_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Lake_MonadLogT_adaptMethods___redArg(v_f_1598_, v_self_1599_, v_a_1600_);
lean_dec(v_a_1600_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods(lean_object* v_n_1602_, lean_object* v_m_1603_, lean_object* v_m_x27_1604_, lean_object* v_00_u03b1_1605_, lean_object* v_inst_1606_, lean_object* v_f_1607_, lean_object* v_self_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_inc(v_a_1609_);
v___x_1610_ = lean_apply_1(v_f_1607_, v_a_1609_);
v___x_1611_ = lean_apply_1(v_self_1608_, v___x_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___boxed(lean_object* v_n_1612_, lean_object* v_m_1613_, lean_object* v_m_x27_1614_, lean_object* v_00_u03b1_1615_, lean_object* v_inst_1616_, lean_object* v_f_1617_, lean_object* v_self_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lake_MonadLogT_adaptMethods(v_n_1612_, v_m_1613_, v_m_x27_1614_, v_00_u03b1_1615_, v_inst_1616_, v_f_1617_, v_self_1618_, v_a_1619_);
lean_dec(v_a_1619_);
lean_dec_ref(v_inst_1616_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog___redArg(lean_object* v_inst_1621_, lean_object* v_self_1622_){
_start:
{
lean_object* v___f_1623_; lean_object* v___x_1624_; 
v___f_1623_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1623_, 0, v_inst_1621_);
v___x_1624_ = lean_apply_1(v_self_1622_, v___f_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog(lean_object* v_m_1625_, lean_object* v_n_1626_, lean_object* v_00_u03b1_1627_, lean_object* v_inst_1628_, lean_object* v_self_1629_){
_start:
{
lean_object* v___f_1630_; lean_object* v___x_1631_; 
v___f_1630_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1630_, 0, v_inst_1628_);
v___x_1631_ = lean_apply_1(v_self_1629_, v___f_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonLog___lam__0(lean_object* v___x_1636_, lean_object* v_x_1637_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_Array_toJson___redArg(v___x_1636_, v_x_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonLog___lam__0(lean_object* v___x_1642_, lean_object* v_x_1643_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_Array_fromJson_x3f___redArg(v___x_1642_, v_x_1643_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1644_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1644_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
v_a_1653_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1644_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1644_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
}
static lean_object* _init_l_Lake_Log_instInhabitedPos_default(void){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_unsigned_to_nat(0u);
return v___x_1664_;
}
}
static lean_object* _init_l_Lake_Log_instInhabitedPos(void){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = lean_unsigned_to_nat(0u);
return v___x_1665_;
}
}
uint8_t l_Lake_Log_instDecidableEqPos_decEq(lean_object* v_x_1666_, lean_object* v_x_1667_){
_start:
{
uint8_t v___x_1668_; 
v___x_1668_ = lean_nat_dec_eq(v_x_1666_, v_x_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT void l_Lake_Log_instDecidableEqPos_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1666_ = stack[0].m_obj;
lean_object* v_x_1667_ = stack[1].m_obj;
uint8_t v_res_1669_;
v_res_1669_ = l_Lake_Log_instDecidableEqPos_decEq(v_x_1666_, v_x_1667_);
stack->m_num = v_res_1669_;
}
LEAN_EXPORT lean_object* l_Lake_Log_instDecidableEqPos_decEq___boxed(lean_object* v_x_1670_, lean_object* v_x_1671_){
_start:
{
uint8_t v_res_1672_; lean_object* v_r_1673_; 
v_res_1672_ = l_Lake_Log_instDecidableEqPos_decEq(v_x_1670_, v_x_1671_);
lean_dec(v_x_1671_);
lean_dec(v_x_1670_);
v_r_1673_ = lean_box(v_res_1672_);
return v_r_1673_;
}
}
uint8_t l_Lake_Log_instDecidableEqPos(lean_object* v_x_1674_, lean_object* v_x_1675_){
_start:
{
uint8_t v___x_1676_; 
v___x_1676_ = lean_nat_dec_eq(v_x_1674_, v_x_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT void l_Lake_Log_instDecidableEqPos_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1674_ = stack[0].m_obj;
lean_object* v_x_1675_ = stack[1].m_obj;
uint8_t v_res_1677_;
v_res_1677_ = l_Lake_Log_instDecidableEqPos(v_x_1674_, v_x_1675_);
stack->m_num = v_res_1677_;
}
LEAN_EXPORT lean_object* l_Lake_Log_instDecidableEqPos___boxed(lean_object* v_x_1678_, lean_object* v_x_1679_){
_start:
{
uint8_t v_res_1680_; lean_object* v_r_1681_; 
v_res_1680_ = l_Lake_Log_instDecidableEqPos(v_x_1678_, v_x_1679_);
lean_dec(v_x_1679_);
lean_dec(v_x_1678_);
v_r_1681_ = lean_box(v_res_1680_);
return v_r_1681_;
}
}
static lean_object* _init_l_Lake_instOfNatPos(void){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_unsigned_to_nat(0u);
return v___x_1682_;
}
}
uint8_t l_Lake_instOrdPos___lam__0(lean_object* v_x1_1683_, lean_object* v_x2_1684_){
_start:
{
uint8_t v___x_1685_; 
v___x_1685_ = lean_nat_dec_lt(v_x1_1683_, v_x2_1684_);
if (v___x_1685_ == 0)
{
uint8_t v___x_1686_; 
v___x_1686_ = lean_nat_dec_eq(v_x1_1683_, v_x2_1684_);
if (v___x_1686_ == 0)
{
uint8_t v___x_1687_; 
v___x_1687_ = 2;
return v___x_1687_;
}
else
{
uint8_t v___x_1688_; 
v___x_1688_ = 1;
return v___x_1688_;
}
}
else
{
uint8_t v___x_1689_; 
v___x_1689_ = 0;
return v___x_1689_;
}
}
}
LEAN_EXPORT void l_Lake_instOrdPos___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_1683_ = stack[0].m_obj;
lean_object* v_x2_1684_ = stack[1].m_obj;
uint8_t v_res_1690_;
v_res_1690_ = l_Lake_instOrdPos___lam__0(v_x1_1683_, v_x2_1684_);
stack->m_num = v_res_1690_;
}
LEAN_EXPORT lean_object* l_Lake_instOrdPos___lam__0___boxed(lean_object* v_x1_1691_, lean_object* v_x2_1692_){
_start:
{
uint8_t v_res_1693_; lean_object* v_r_1694_; 
v_res_1693_ = l_Lake_instOrdPos___lam__0(v_x1_1691_, v_x2_1692_);
lean_dec(v_x2_1692_);
lean_dec(v_x1_1691_);
v_r_1694_ = lean_box(v_res_1693_);
return v_r_1694_;
}
}
static lean_object* _init_l_Lake_instLTPos(void){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = lean_box(0);
return v___x_1697_;
}
}
uint8_t l_Lake_instDecidableRelPosLt(lean_object* v_a_1698_, lean_object* v_b_1699_){
_start:
{
uint8_t v___x_1700_; 
v___x_1700_ = lean_nat_dec_lt(v_a_1698_, v_b_1699_);
return v___x_1700_;
}
}
LEAN_EXPORT void l_Lake_instDecidableRelPosLt_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1698_ = stack[0].m_obj;
lean_object* v_b_1699_ = stack[1].m_obj;
uint8_t v_res_1701_;
v_res_1701_ = l_Lake_instDecidableRelPosLt(v_a_1698_, v_b_1699_);
stack->m_num = v_res_1701_;
}
LEAN_EXPORT lean_object* l_Lake_instDecidableRelPosLt___boxed(lean_object* v_a_1702_, lean_object* v_b_1703_){
_start:
{
uint8_t v_res_1704_; lean_object* v_r_1705_; 
v_res_1704_ = l_Lake_instDecidableRelPosLt(v_a_1702_, v_b_1703_);
lean_dec(v_b_1703_);
lean_dec(v_a_1702_);
v_r_1705_ = lean_box(v_res_1704_);
return v_r_1705_;
}
}
static lean_object* _init_l_Lake_instLEPos(void){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = lean_box(0);
return v___x_1706_;
}
}
uint8_t l_Lake_instDecidableRelPosLe(lean_object* v_a_1707_, lean_object* v_b_1708_){
_start:
{
uint8_t v___x_1709_; 
v___x_1709_ = lean_nat_dec_le(v_a_1707_, v_b_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT void l_Lake_instDecidableRelPosLe_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1707_ = stack[0].m_obj;
lean_object* v_b_1708_ = stack[1].m_obj;
uint8_t v_res_1710_;
v_res_1710_ = l_Lake_instDecidableRelPosLe(v_a_1707_, v_b_1708_);
stack->m_num = v_res_1710_;
}
LEAN_EXPORT lean_object* l_Lake_instDecidableRelPosLe___boxed(lean_object* v_a_1711_, lean_object* v_b_1712_){
_start:
{
uint8_t v_res_1713_; lean_object* v_r_1714_; 
v_res_1713_ = l_Lake_instDecidableRelPosLe(v_a_1711_, v_b_1712_);
lean_dec(v_b_1712_);
lean_dec(v_a_1711_);
v_r_1714_ = lean_box(v_res_1713_);
return v_r_1714_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMinPos___lam__0(lean_object* v_x_1715_, lean_object* v_y_1716_){
_start:
{
uint8_t v___x_1717_; 
v___x_1717_ = lean_nat_dec_le(v_x_1715_, v_y_1716_);
if (v___x_1717_ == 0)
{
lean_inc(v_y_1716_);
return v_y_1716_;
}
else
{
lean_inc(v_x_1715_);
return v_x_1715_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMinPos___lam__0___boxed(lean_object* v_x_1718_, lean_object* v_y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lake_instMinPos___lam__0(v_x_1718_, v_y_1719_);
lean_dec(v_y_1719_);
lean_dec(v_x_1718_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxPos___lam__0(lean_object* v_x_1723_, lean_object* v_y_1724_){
_start:
{
uint8_t v___x_1725_; 
v___x_1725_ = lean_nat_dec_le(v_x_1723_, v_y_1724_);
if (v___x_1725_ == 0)
{
lean_inc(v_x_1723_);
return v_x_1723_;
}
else
{
lean_inc(v_y_1724_);
return v_y_1724_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxPos___lam__0___boxed(lean_object* v_x_1726_, lean_object* v_y_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Lake_instMaxPos___lam__0(v_x_1726_, v_y_1727_);
lean_dec(v_y_1727_);
lean_dec(v_x_1726_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_size(lean_object* v_log_1735_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = lean_array_get_size(v_log_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_size___boxed(lean_object* v_log_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lake_Log_size(v_log_1737_);
lean_dec_ref(v_log_1737_);
return v_res_1738_;
}
}
uint8_t l_Lake_Log_isEmpty(lean_object* v_log_1739_){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; uint8_t v___x_1742_; 
v___x_1740_ = lean_array_get_size(v_log_1739_);
v___x_1741_ = lean_unsigned_to_nat(0u);
v___x_1742_ = lean_nat_dec_eq(v___x_1740_, v___x_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT void l_Lake_Log_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_log_1739_ = stack[0].m_obj;
uint8_t v_res_1743_;
v_res_1743_ = l_Lake_Log_isEmpty(v_log_1739_);
stack->m_num = v_res_1743_;
}
LEAN_EXPORT lean_object* l_Lake_Log_isEmpty___boxed(lean_object* v_log_1744_){
_start:
{
uint8_t v_res_1745_; lean_object* v_r_1746_; 
v_res_1745_ = l_Lake_Log_isEmpty(v_log_1744_);
lean_dec_ref(v_log_1744_);
v_r_1746_ = lean_box(v_res_1745_);
return v_r_1746_;
}
}
uint8_t l_Lake_Log_hasEntries(lean_object* v_log_1747_){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; 
v___x_1748_ = lean_array_get_size(v_log_1747_);
v___x_1749_ = lean_unsigned_to_nat(0u);
v___x_1750_ = lean_nat_dec_eq(v___x_1748_, v___x_1749_);
if (v___x_1750_ == 0)
{
uint8_t v___x_1751_; 
v___x_1751_ = 1;
return v___x_1751_;
}
else
{
uint8_t v___x_1752_; 
v___x_1752_ = 0;
return v___x_1752_;
}
}
}
LEAN_EXPORT void l_Lake_Log_hasEntries_0interp(lean_interpreter_value* stack)
{
lean_object* v_log_1747_ = stack[0].m_obj;
uint8_t v_res_1753_;
v_res_1753_ = l_Lake_Log_hasEntries(v_log_1747_);
stack->m_num = v_res_1753_;
}
LEAN_EXPORT lean_object* l_Lake_Log_hasEntries___boxed(lean_object* v_log_1754_){
_start:
{
uint8_t v_res_1755_; lean_object* v_r_1756_; 
v_res_1755_ = l_Lake_Log_hasEntries(v_log_1754_);
lean_dec_ref(v_log_1754_);
v_r_1756_ = lean_box(v_res_1755_);
return v_r_1756_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_endPos(lean_object* v_log_1757_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = lean_array_get_size(v_log_1757_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_endPos___boxed(lean_object* v_log_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Lake_Log_endPos(v_log_1759_);
lean_dec_ref(v_log_1759_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_push(lean_object* v_log_1761_, lean_object* v_e_1762_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = lean_array_push(v_log_1761_, v_e_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_append(lean_object* v_log_1764_, lean_object* v_o_1765_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Array_append___redArg(v_log_1764_, v_o_1765_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_append___boxed(lean_object* v_log_1767_, lean_object* v_o_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Lake_Log_append(v_log_1767_, v_o_1768_);
lean_dec_ref(v_o_1768_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_extract(lean_object* v_log_1772_, lean_object* v_start_1773_, lean_object* v_stop_1774_){
_start:
{
lean_object* v___x_1775_; 
v___x_1775_ = l_Array_extract___redArg(v_log_1772_, v_start_1773_, v_stop_1774_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_extract___boxed(lean_object* v_log_1776_, lean_object* v_start_1777_, lean_object* v_stop_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Lake_Log_extract(v_log_1776_, v_start_1777_, v_stop_1778_);
lean_dec_ref(v_log_1776_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_dropFrom(lean_object* v_log_1780_, lean_object* v_pos_1781_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Array_shrink___redArg(v_log_1780_, v_pos_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_dropFrom___boxed(lean_object* v_log_1783_, lean_object* v_pos_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Lake_Log_dropFrom(v_log_1783_, v_pos_1784_);
lean_dec(v_pos_1784_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_takeFrom(lean_object* v_log_1786_, lean_object* v_pos_1787_){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = lean_array_get_size(v_log_1786_);
v___x_1789_ = l_Array_extract___redArg(v_log_1786_, v_pos_1787_, v___x_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_takeFrom___boxed(lean_object* v_log_1790_, lean_object* v_pos_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Lake_Log_takeFrom(v_log_1790_, v_pos_1791_);
lean_dec_ref(v_log_1790_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_split(lean_object* v_log_1793_, lean_object* v_pos_1794_){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
lean_inc_ref(v_log_1793_);
v___x_1795_ = l_Array_shrink___redArg(v_log_1793_, v_pos_1794_);
v___x_1796_ = lean_array_get_size(v_log_1793_);
v___x_1797_ = l_Array_extract___redArg(v_log_1793_, v_pos_1794_, v___x_1796_);
lean_dec_ref(v_log_1793_);
v___x_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1795_);
lean_ctor_set(v___x_1798_, 1, v___x_1797_);
return v___x_1798_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(lean_object* v_as_1800_, size_t v_i_1801_, size_t v_stop_1802_, lean_object* v_b_1803_){
_start:
{
uint8_t v___x_1804_; 
v___x_1804_ = lean_usize_dec_eq(v_i_1801_, v_stop_1802_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; size_t v___x_1810_; size_t v___x_1811_; 
v___x_1805_ = lean_array_uget_borrowed(v_as_1800_, v_i_1801_);
v___x_1806_ = l_Lake_LogEntry_toString(v___x_1805_, v___x_1804_);
v___x_1807_ = lean_string_append(v_b_1803_, v___x_1806_);
lean_dec_ref(v___x_1806_);
v___x_1808_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0___closed__0));
v___x_1809_ = lean_string_append(v___x_1807_, v___x_1808_);
v___x_1810_ = ((size_t)1ULL);
v___x_1811_ = lean_usize_add(v_i_1801_, v___x_1810_);
v_i_1801_ = v___x_1811_;
v_b_1803_ = v___x_1809_;
goto _start;
}
else
{
return v_b_1803_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1800_ = stack[0].m_obj;
size_t v_i_1801_ = stack[1].m_num;
size_t v_stop_1802_ = stack[2].m_num;
lean_object* v_b_1803_ = stack[3].m_obj;
lean_object* v_res_1813_;
v_res_1813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(v_as_1800_, v_i_1801_, v_stop_1802_, v_b_1803_);
stack->m_obj
 = v_res_1813_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0___boxed(lean_object* v_as_1814_, lean_object* v_i_1815_, lean_object* v_stop_1816_, lean_object* v_b_1817_){
_start:
{
size_t v_i_boxed_1818_; size_t v_stop_boxed_1819_; lean_object* v_res_1820_; 
v_i_boxed_1818_ = lean_unbox_usize(v_i_1815_);
lean_dec(v_i_1815_);
v_stop_boxed_1819_ = lean_unbox_usize(v_stop_1816_);
lean_dec(v_stop_1816_);
v_res_1820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(v_as_1814_, v_i_boxed_1818_, v_stop_boxed_1819_, v_b_1817_);
lean_dec_ref(v_as_1814_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_toString(lean_object* v_log_1821_){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1822_ = ((lean_object*)(l_Lake_instInhabitedLogEntry_default___closed__0));
v___x_1823_ = lean_unsigned_to_nat(0u);
v___x_1824_ = lean_array_get_size(v_log_1821_);
v___x_1825_ = lean_nat_dec_lt(v___x_1823_, v___x_1824_);
if (v___x_1825_ == 0)
{
return v___x_1822_;
}
else
{
uint8_t v___x_1826_; 
v___x_1826_ = lean_nat_dec_le(v___x_1824_, v___x_1824_);
if (v___x_1826_ == 0)
{
if (v___x_1825_ == 0)
{
return v___x_1822_;
}
else
{
size_t v___x_1827_; size_t v___x_1828_; lean_object* v___x_1829_; 
v___x_1827_ = ((size_t)0ULL);
v___x_1828_ = lean_usize_of_nat(v___x_1824_);
v___x_1829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(v_log_1821_, v___x_1827_, v___x_1828_, v___x_1822_);
return v___x_1829_;
}
}
else
{
size_t v___x_1830_; size_t v___x_1831_; lean_object* v___x_1832_; 
v___x_1830_ = ((size_t)0ULL);
v___x_1831_ = lean_usize_of_nat(v___x_1824_);
v___x_1832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(v_log_1821_, v___x_1830_, v___x_1831_, v___x_1822_);
return v___x_1832_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_toString___boxed(lean_object* v_log_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Lake_Log_toString(v_log_1833_);
lean_dec_ref(v_log_1833_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_replay___redArg___lam__0(lean_object* v_logger_1837_, lean_object* v_x_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = lean_apply_1(v_logger_1837_, v___y_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_replay___redArg(lean_object* v_inst_1841_, lean_object* v_logger_1842_, lean_object* v_log_1843_){
_start:
{
lean_object* v_toApplicative_1844_; lean_object* v_toPure_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; 
v_toApplicative_1844_ = lean_ctor_get(v_inst_1841_, 0);
v_toPure_1845_ = lean_ctor_get(v_toApplicative_1844_, 1);
v___x_1846_ = lean_unsigned_to_nat(0u);
v___x_1847_ = lean_array_get_size(v_log_1843_);
v___x_1848_ = lean_box(0);
v___x_1849_ = lean_nat_dec_lt(v___x_1846_, v___x_1847_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; 
lean_inc(v_toPure_1845_);
lean_dec_ref(v_log_1843_);
lean_dec(v_logger_1842_);
lean_dec_ref(v_inst_1841_);
v___x_1850_ = lean_apply_2(v_toPure_1845_, lean_box(0), v___x_1848_);
return v___x_1850_;
}
else
{
lean_object* v___f_1851_; uint8_t v___x_1852_; 
v___f_1851_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1851_, 0, v_logger_1842_);
v___x_1852_ = lean_nat_dec_le(v___x_1847_, v___x_1847_);
if (v___x_1852_ == 0)
{
if (v___x_1849_ == 0)
{
lean_object* v___x_1853_; 
lean_inc(v_toPure_1845_);
lean_dec_ref(v___f_1851_);
lean_dec_ref(v_log_1843_);
lean_dec_ref(v_inst_1841_);
v___x_1853_ = lean_apply_2(v_toPure_1845_, lean_box(0), v___x_1848_);
return v___x_1853_;
}
else
{
size_t v___x_1854_; size_t v___x_1855_; lean_object* v___x_1856_; 
v___x_1854_ = ((size_t)0ULL);
v___x_1855_ = lean_usize_of_nat(v___x_1847_);
v___x_1856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1841_, v___f_1851_, v_log_1843_, v___x_1854_, v___x_1855_, v___x_1848_);
return v___x_1856_;
}
}
else
{
size_t v___x_1857_; size_t v___x_1858_; lean_object* v___x_1859_; 
v___x_1857_ = ((size_t)0ULL);
v___x_1858_ = lean_usize_of_nat(v___x_1847_);
v___x_1859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1841_, v___f_1851_, v_log_1843_, v___x_1857_, v___x_1858_, v___x_1848_);
return v___x_1859_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_replay(lean_object* v_m_1860_, lean_object* v_inst_1861_, lean_object* v_logger_1862_, lean_object* v_log_1863_){
_start:
{
lean_object* v_toApplicative_1864_; lean_object* v_toPure_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; uint8_t v___x_1869_; 
v_toApplicative_1864_ = lean_ctor_get(v_inst_1861_, 0);
v_toPure_1865_ = lean_ctor_get(v_toApplicative_1864_, 1);
v___x_1866_ = lean_unsigned_to_nat(0u);
v___x_1867_ = lean_array_get_size(v_log_1863_);
v___x_1868_ = lean_box(0);
v___x_1869_ = lean_nat_dec_lt(v___x_1866_, v___x_1867_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; 
lean_inc(v_toPure_1865_);
lean_dec_ref(v_log_1863_);
lean_dec(v_logger_1862_);
lean_dec_ref(v_inst_1861_);
v___x_1870_ = lean_apply_2(v_toPure_1865_, lean_box(0), v___x_1868_);
return v___x_1870_;
}
else
{
lean_object* v___f_1871_; uint8_t v___x_1872_; 
v___f_1871_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1871_, 0, v_logger_1862_);
v___x_1872_ = lean_nat_dec_le(v___x_1867_, v___x_1867_);
if (v___x_1872_ == 0)
{
if (v___x_1869_ == 0)
{
lean_object* v___x_1873_; 
lean_inc(v_toPure_1865_);
lean_dec_ref(v___f_1871_);
lean_dec_ref(v_log_1863_);
lean_dec_ref(v_inst_1861_);
v___x_1873_ = lean_apply_2(v_toPure_1865_, lean_box(0), v___x_1868_);
return v___x_1873_;
}
else
{
size_t v___x_1874_; size_t v___x_1875_; lean_object* v___x_1876_; 
v___x_1874_ = ((size_t)0ULL);
v___x_1875_ = lean_usize_of_nat(v___x_1867_);
v___x_1876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1861_, v___f_1871_, v_log_1863_, v___x_1874_, v___x_1875_, v___x_1868_);
return v___x_1876_;
}
}
else
{
size_t v___x_1877_; size_t v___x_1878_; lean_object* v___x_1879_; 
v___x_1877_ = ((size_t)0ULL);
v___x_1878_ = lean_usize_of_nat(v___x_1867_);
v___x_1879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1861_, v___f_1871_, v_log_1863_, v___x_1877_, v___x_1878_, v___x_1868_);
return v___x_1879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_filter___lam__0(lean_object* v_f_1880_, lean_object* v_x1_1881_, lean_object* v_x2_1882_){
_start:
{
lean_object* v___x_1883_; uint8_t v___x_1884_; 
lean_inc_ref(v_x2_1882_);
v___x_1883_ = lean_apply_1(v_f_1880_, v_x2_1882_);
v___x_1884_ = lean_unbox(v___x_1883_);
if (v___x_1884_ == 0)
{
lean_dec_ref(v_x2_1882_);
return v_x1_1881_;
}
else
{
lean_object* v___x_1885_; 
v___x_1885_ = lean_array_push(v_x1_1881_, v_x2_1882_);
return v___x_1885_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_filter(lean_object* v_f_1905_, lean_object* v_log_1906_){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; 
v___x_1907_ = lean_unsigned_to_nat(0u);
v___x_1908_ = lean_array_get_size(v_log_1906_);
v___x_1909_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_1910_ = ((lean_object*)(l_Lake_Log_filter___closed__9));
v___x_1911_ = lean_nat_dec_lt(v___x_1907_, v___x_1908_);
if (v___x_1911_ == 0)
{
lean_dec_ref(v_log_1906_);
lean_dec_ref(v_f_1905_);
return v___x_1909_;
}
else
{
lean_object* v___f_1912_; uint8_t v___x_1913_; 
v___f_1912_ = lean_alloc_closure((void*)(l_Lake_Log_filter___lam__0), 3, 1);
lean_closure_set(v___f_1912_, 0, v_f_1905_);
v___x_1913_ = lean_nat_dec_le(v___x_1908_, v___x_1908_);
if (v___x_1913_ == 0)
{
if (v___x_1911_ == 0)
{
lean_dec_ref(v___f_1912_);
lean_dec_ref(v_log_1906_);
return v___x_1909_;
}
else
{
size_t v___x_1914_; size_t v___x_1915_; lean_object* v___x_1916_; 
v___x_1914_ = ((size_t)0ULL);
v___x_1915_ = lean_usize_of_nat(v___x_1908_);
v___x_1916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1910_, v___f_1912_, v_log_1906_, v___x_1914_, v___x_1915_, v___x_1909_);
return v___x_1916_;
}
}
else
{
size_t v___x_1917_; size_t v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = ((size_t)0ULL);
v___x_1918_ = lean_usize_of_nat(v___x_1908_);
v___x_1919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1910_, v___f_1912_, v_log_1906_, v___x_1917_, v___x_1918_, v___x_1909_);
return v___x_1919_;
}
}
}
}
uint8_t l_Lake_Log_any___lam__0(lean_object* v_f_1920_, lean_object* v_x_1921_){
_start:
{
lean_object* v___x_1922_; uint8_t v___x_1923_; 
v___x_1922_ = lean_apply_1(v_f_1920_, v_x_1921_);
v___x_1923_ = lean_unbox(v___x_1922_);
return v___x_1923_;
}
}
LEAN_EXPORT void l_Lake_Log_any___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1920_ = stack[0].m_obj;
lean_object* v_x_1921_ = stack[1].m_obj;
uint8_t v_res_1924_;
v_res_1924_ = l_Lake_Log_any___lam__0(v_f_1920_, v_x_1921_);
stack->m_num = v_res_1924_;
}
LEAN_EXPORT lean_object* l_Lake_Log_any___lam__0___boxed(lean_object* v_f_1925_, lean_object* v_x_1926_){
_start:
{
uint8_t v_res_1927_; lean_object* v_r_1928_; 
v_res_1927_ = l_Lake_Log_any___lam__0(v_f_1925_, v_x_1926_);
v_r_1928_ = lean_box(v_res_1927_);
return v_r_1928_;
}
}
uint8_t l_Lake_Log_any(lean_object* v_f_1929_, lean_object* v_log_1930_){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; uint8_t v___x_1934_; 
v___x_1931_ = lean_unsigned_to_nat(0u);
v___x_1932_ = lean_array_get_size(v_log_1930_);
v___x_1933_ = ((lean_object*)(l_Lake_Log_filter___closed__9));
v___x_1934_ = lean_nat_dec_lt(v___x_1931_, v___x_1932_);
if (v___x_1934_ == 0)
{
lean_dec_ref(v_log_1930_);
lean_dec_ref(v_f_1929_);
return v___x_1934_;
}
else
{
if (v___x_1934_ == 0)
{
lean_dec_ref(v_log_1930_);
lean_dec_ref(v_f_1929_);
return v___x_1934_;
}
else
{
lean_object* v___f_1935_; size_t v___x_1936_; size_t v___x_1937_; lean_object* v___x_1938_; uint8_t v___x_1939_; 
v___f_1935_ = lean_alloc_closure((void*)(l_Lake_Log_any___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1935_, 0, v_f_1929_);
v___x_1936_ = ((size_t)0ULL);
v___x_1937_ = lean_usize_of_nat(v___x_1932_);
v___x_1938_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_1933_, v___f_1935_, v_log_1930_, v___x_1936_, v___x_1937_);
v___x_1939_ = lean_unbox(v___x_1938_);
lean_dec(v___x_1938_);
return v___x_1939_;
}
}
}
}
LEAN_EXPORT void l_Lake_Log_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1929_ = stack[0].m_obj;
lean_object* v_log_1930_ = stack[1].m_obj;
uint8_t v_res_1940_;
v_res_1940_ = l_Lake_Log_any(v_f_1929_, v_log_1930_);
stack->m_num = v_res_1940_;
}
LEAN_EXPORT lean_object* l_Lake_Log_any___boxed(lean_object* v_f_1941_, lean_object* v_log_1942_){
_start:
{
uint8_t v_res_1943_; lean_object* v_r_1944_; 
v_res_1943_ = l_Lake_Log_any(v_f_1941_, v_log_1942_);
v_r_1944_ = lean_box(v_res_1943_);
return v_r_1944_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(lean_object* v_as_1945_, size_t v_i_1946_, size_t v_stop_1947_, uint8_t v_b_1948_){
_start:
{
uint8_t v___y_1950_; uint8_t v___x_1954_; 
v___x_1954_ = lean_usize_dec_eq(v_i_1946_, v_stop_1947_);
if (v___x_1954_ == 0)
{
lean_object* v___x_1955_; uint8_t v_level_1956_; uint8_t v___x_1957_; 
v___x_1955_ = lean_array_uget_borrowed(v_as_1945_, v_i_1946_);
v_level_1956_ = lean_ctor_get_uint8(v___x_1955_, sizeof(void*)*1);
v___x_1957_ = l_Lake_instOrdLogLevel_ord(v_b_1948_, v_level_1956_);
if (v___x_1957_ == 2)
{
if (v___x_1954_ == 0)
{
v___y_1950_ = v_b_1948_;
goto v___jp_1949_;
}
else
{
v___y_1950_ = v_level_1956_;
goto v___jp_1949_;
}
}
else
{
v___y_1950_ = v_level_1956_;
goto v___jp_1949_;
}
}
else
{
return v_b_1948_;
}
v___jp_1949_:
{
size_t v___x_1951_; size_t v___x_1952_; 
v___x_1951_ = ((size_t)1ULL);
v___x_1952_ = lean_usize_add(v_i_1946_, v___x_1951_);
v_i_1946_ = v___x_1952_;
v_b_1948_ = v___y_1950_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1945_ = stack[0].m_obj;
size_t v_i_1946_ = stack[1].m_num;
size_t v_stop_1947_ = stack[2].m_num;
uint8_t v_b_1948_ = stack[3].m_num;
uint8_t v_res_1958_;
v_res_1958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(v_as_1945_, v_i_1946_, v_stop_1947_, v_b_1948_);
stack->m_num = v_res_1958_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0___boxed(lean_object* v_as_1959_, lean_object* v_i_1960_, lean_object* v_stop_1961_, lean_object* v_b_1962_){
_start:
{
size_t v_i_boxed_1963_; size_t v_stop_boxed_1964_; uint8_t v_b_boxed_1965_; uint8_t v_res_1966_; lean_object* v_r_1967_; 
v_i_boxed_1963_ = lean_unbox_usize(v_i_1960_);
lean_dec(v_i_1960_);
v_stop_boxed_1964_ = lean_unbox_usize(v_stop_1961_);
lean_dec(v_stop_1961_);
v_b_boxed_1965_ = lean_unbox(v_b_1962_);
v_res_1966_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(v_as_1959_, v_i_boxed_1963_, v_stop_boxed_1964_, v_b_boxed_1965_);
lean_dec_ref(v_as_1959_);
v_r_1967_ = lean_box(v_res_1966_);
return v_r_1967_;
}
}
uint8_t l_Lake_Log_maxLv(lean_object* v_log_1968_){
_start:
{
uint8_t v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
v___x_1969_ = 0;
v___x_1970_ = lean_unsigned_to_nat(0u);
v___x_1971_ = lean_array_get_size(v_log_1968_);
v___x_1972_ = lean_nat_dec_lt(v___x_1970_, v___x_1971_);
if (v___x_1972_ == 0)
{
return v___x_1969_;
}
else
{
uint8_t v___x_1973_; 
v___x_1973_ = lean_nat_dec_le(v___x_1971_, v___x_1971_);
if (v___x_1973_ == 0)
{
if (v___x_1972_ == 0)
{
return v___x_1969_;
}
else
{
size_t v___x_1974_; size_t v___x_1975_; uint8_t v___x_1976_; 
v___x_1974_ = ((size_t)0ULL);
v___x_1975_ = lean_usize_of_nat(v___x_1971_);
v___x_1976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(v_log_1968_, v___x_1974_, v___x_1975_, v___x_1969_);
return v___x_1976_;
}
}
else
{
size_t v___x_1977_; size_t v___x_1978_; uint8_t v___x_1979_; 
v___x_1977_ = ((size_t)0ULL);
v___x_1978_ = lean_usize_of_nat(v___x_1971_);
v___x_1979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(v_log_1968_, v___x_1977_, v___x_1978_, v___x_1969_);
return v___x_1979_;
}
}
}
}
LEAN_EXPORT void l_Lake_Log_maxLv_0interp(lean_interpreter_value* stack)
{
lean_object* v_log_1968_ = stack[0].m_obj;
uint8_t v_res_1980_;
v_res_1980_ = l_Lake_Log_maxLv(v_log_1968_);
stack->m_num = v_res_1980_;
}
LEAN_EXPORT lean_object* l_Lake_Log_maxLv___boxed(lean_object* v_log_1981_){
_start:
{
uint8_t v_res_1982_; lean_object* v_r_1983_; 
v_res_1982_ = l_Lake_Log_maxLv(v_log_1981_);
lean_dec_ref(v_log_1981_);
v_r_1983_ = lean_box(v_res_1982_);
return v_r_1983_;
}
}
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___redArg___lam__0(lean_object* v_e_1984_, lean_object* v_s_1985_){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1986_ = lean_box(0);
v___x_1987_ = lean_array_push(v_s_1985_, v_e_1984_);
v___x_1988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1986_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___redArg(lean_object* v_inst_1989_, lean_object* v_e_1990_){
_start:
{
lean_object* v_modifyGet_1991_; lean_object* v___f_1992_; lean_object* v___x_1993_; 
v_modifyGet_1991_ = lean_ctor_get(v_inst_1989_, 2);
lean_inc(v_modifyGet_1991_);
lean_dec_ref(v_inst_1989_);
v___f_1992_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1992_, 0, v_e_1990_);
v___x_1993_ = lean_apply_2(v_modifyGet_1991_, lean_box(0), v___f_1992_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lake_pushLogEntry(lean_object* v_m_1994_, lean_object* v_inst_1995_, lean_object* v_e_1996_){
_start:
{
lean_object* v_modifyGet_1997_; lean_object* v___f_1998_; lean_object* v___x_1999_; 
v_modifyGet_1997_ = lean_ctor_get(v_inst_1995_, 2);
lean_inc(v_modifyGet_1997_);
lean_dec_ref(v_inst_1995_);
v___f_1998_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1998_, 0, v_e_1996_);
v___x_1999_ = lean_apply_2(v_modifyGet_1997_, lean_box(0), v___f_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_ofMonadState___redArg(lean_object* v_inst_2000_){
_start:
{
lean_object* v___x_2001_; 
v___x_2001_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(v___x_2001_, 0, lean_box(0));
lean_closure_set(v___x_2001_, 1, v_inst_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_ofMonadState(lean_object* v_m_2002_, lean_object* v_inst_2003_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(v___x_2004_, 0, lean_box(0));
lean_closure_set(v___x_2004_, 1, v_inst_2003_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog___redArg(lean_object* v_inst_2005_){
_start:
{
lean_object* v_get_2006_; 
v_get_2006_ = lean_ctor_get(v_inst_2005_, 0);
lean_inc(v_get_2006_);
return v_get_2006_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog___redArg___boxed(lean_object* v_inst_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Lake_getLog___redArg(v_inst_2007_);
lean_dec_ref(v_inst_2007_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog(lean_object* v_m_2009_, lean_object* v_inst_2010_){
_start:
{
lean_object* v_get_2011_; 
v_get_2011_ = lean_ctor_get(v_inst_2010_, 0);
lean_inc(v_get_2011_);
return v_get_2011_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog___boxed(lean_object* v_m_2012_, lean_object* v_inst_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lake_getLog(v_m_2012_, v_inst_2013_);
lean_dec_ref(v_inst_2013_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg___lam__0(lean_object* v_x_2015_){
_start:
{
lean_object* v___x_2016_; 
v___x_2016_ = lean_array_get_size(v_x_2015_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg___lam__0___boxed(lean_object* v_x_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Lake_getLogPos___redArg___lam__0(v_x_2017_);
lean_dec_ref(v_x_2017_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg(lean_object* v_inst_2020_, lean_object* v_inst_2021_){
_start:
{
lean_object* v_map_2022_; lean_object* v_get_2023_; lean_object* v___f_2024_; lean_object* v___x_2025_; 
v_map_2022_ = lean_ctor_get(v_inst_2020_, 0);
lean_inc(v_map_2022_);
lean_dec_ref(v_inst_2020_);
v_get_2023_ = lean_ctor_get(v_inst_2021_, 0);
lean_inc(v_get_2023_);
lean_dec_ref(v_inst_2021_);
v___f_2024_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_2025_ = lean_apply_4(v_map_2022_, lean_box(0), lean_box(0), v___f_2024_, v_get_2023_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos(lean_object* v_m_2026_, lean_object* v_inst_2027_, lean_object* v_inst_2028_){
_start:
{
lean_object* v_map_2029_; lean_object* v_get_2030_; lean_object* v___f_2031_; lean_object* v___x_2032_; 
v_map_2029_ = lean_ctor_get(v_inst_2027_, 0);
lean_inc(v_map_2029_);
lean_dec_ref(v_inst_2027_);
v_get_2030_ = lean_ctor_get(v_inst_2028_, 0);
lean_inc(v_get_2030_);
lean_dec_ref(v_inst_2028_);
v___f_2031_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_2032_ = lean_apply_4(v_map_2029_, lean_box(0), lean_box(0), v___f_2031_, v_get_2030_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLog___redArg___lam__0(lean_object* v_log_2033_){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2035_, 0, v_log_2033_);
lean_ctor_set(v___x_2035_, 1, v___x_2034_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLog___redArg(lean_object* v_inst_2037_){
_start:
{
lean_object* v_modifyGet_2038_; lean_object* v___f_2039_; lean_object* v___x_2040_; 
v_modifyGet_2038_ = lean_ctor_get(v_inst_2037_, 2);
lean_inc(v_modifyGet_2038_);
lean_dec_ref(v_inst_2037_);
v___f_2039_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_2040_ = lean_apply_2(v_modifyGet_2038_, lean_box(0), v___f_2039_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLog(lean_object* v_m_2041_, lean_object* v_inst_2042_){
_start:
{
lean_object* v_modifyGet_2043_; lean_object* v___f_2044_; lean_object* v___x_2045_; 
v_modifyGet_2043_ = lean_ctor_get(v_inst_2042_, 2);
lean_inc(v_modifyGet_2043_);
lean_dec_ref(v_inst_2042_);
v___f_2044_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_2045_ = lean_apply_2(v_modifyGet_2043_, lean_box(0), v___f_2044_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLogFrom___redArg___lam__0(lean_object* v_pos_2046_, lean_object* v_log_2047_){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2048_ = lean_array_get_size(v_log_2047_);
lean_inc(v_pos_2046_);
v___x_2049_ = l_Array_extract___redArg(v_log_2047_, v_pos_2046_, v___x_2048_);
v___x_2050_ = l_Array_shrink___redArg(v_log_2047_, v_pos_2046_);
lean_dec(v_pos_2046_);
v___x_2051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2049_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLogFrom___redArg(lean_object* v_inst_2052_, lean_object* v_pos_2053_){
_start:
{
lean_object* v_modifyGet_2054_; lean_object* v___f_2055_; lean_object* v___x_2056_; 
v_modifyGet_2054_ = lean_ctor_get(v_inst_2052_, 2);
lean_inc(v_modifyGet_2054_);
lean_dec_ref(v_inst_2052_);
v___f_2055_ = lean_alloc_closure((void*)(l_Lake_takeLogFrom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2055_, 0, v_pos_2053_);
v___x_2056_ = lean_apply_2(v_modifyGet_2054_, lean_box(0), v___f_2055_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLogFrom(lean_object* v_m_2057_, lean_object* v_inst_2058_, lean_object* v_pos_2059_){
_start:
{
lean_object* v_modifyGet_2060_; lean_object* v___f_2061_; lean_object* v___x_2062_; 
v_modifyGet_2060_ = lean_ctor_get(v_inst_2058_, 2);
lean_inc(v_modifyGet_2060_);
lean_dec_ref(v_inst_2058_);
v___f_2061_ = lean_alloc_closure((void*)(l_Lake_takeLogFrom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2061_, 0, v_pos_2059_);
v___x_2062_ = lean_apply_2(v_modifyGet_2060_, lean_box(0), v___f_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg___lam__0(lean_object* v_pos_2063_, lean_object* v_s_2064_){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2065_ = lean_box(0);
v___x_2066_ = l_Array_shrink___redArg(v_s_2064_, v_pos_2063_);
v___x_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2065_);
lean_ctor_set(v___x_2067_, 1, v___x_2066_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg___lam__0___boxed(lean_object* v_pos_2068_, lean_object* v_s_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Lake_dropLogFrom___redArg___lam__0(v_pos_2068_, v_s_2069_);
lean_dec(v_pos_2068_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg(lean_object* v_inst_2071_, lean_object* v_pos_2072_){
_start:
{
lean_object* v_modifyGet_2073_; lean_object* v___f_2074_; lean_object* v___x_2075_; 
v_modifyGet_2073_ = lean_ctor_get(v_inst_2071_, 2);
lean_inc(v_modifyGet_2073_);
lean_dec_ref(v_inst_2071_);
v___f_2074_ = lean_alloc_closure((void*)(l_Lake_dropLogFrom___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2074_, 0, v_pos_2072_);
v___x_2075_ = lean_apply_2(v_modifyGet_2073_, lean_box(0), v___f_2074_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom(lean_object* v_m_2076_, lean_object* v_inst_2077_, lean_object* v_pos_2078_){
_start:
{
lean_object* v_modifyGet_2079_; lean_object* v___f_2080_; lean_object* v___x_2081_; 
v_modifyGet_2079_ = lean_ctor_get(v_inst_2077_, 2);
lean_inc(v_modifyGet_2079_);
lean_dec_ref(v_inst_2077_);
v___f_2080_ = lean_alloc_closure((void*)(l_Lake_dropLogFrom___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2080_, 0, v_pos_2078_);
v___x_2081_ = lean_apply_2(v_modifyGet_2079_, lean_box(0), v___f_2080_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__1(lean_object* v_iniPos_2082_, lean_object* v_toPure_2083_, lean_object* v_log_2084_){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2085_ = lean_array_get_size(v_log_2084_);
v___x_2086_ = l_Array_extract___redArg(v_log_2084_, v_iniPos_2082_, v___x_2085_);
v___x_2087_ = lean_apply_2(v_toPure_2083_, lean_box(0), v___x_2086_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__1___boxed(lean_object* v_iniPos_2088_, lean_object* v_toPure_2089_, lean_object* v_log_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Lake_extractLog___redArg___lam__1(v_iniPos_2088_, v_toPure_2089_, v_log_2090_);
lean_dec_ref(v_log_2090_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__0(lean_object* v_toBind_2092_, lean_object* v_get_2093_, lean_object* v___f_2094_, lean_object* v_____r_2095_){
_start:
{
lean_object* v___x_2096_; 
v___x_2096_ = lean_apply_4(v_toBind_2092_, lean_box(0), lean_box(0), v_get_2093_, v___f_2094_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__2(lean_object* v_toPure_2097_, lean_object* v_toBind_2098_, lean_object* v_get_2099_, lean_object* v_x_2100_, lean_object* v_iniPos_2101_){
_start:
{
lean_object* v___f_2102_; lean_object* v___f_2103_; lean_object* v___x_2104_; 
v___f_2102_ = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2102_, 0, v_iniPos_2101_);
lean_closure_set(v___f_2102_, 1, v_toPure_2097_);
lean_inc(v_toBind_2098_);
v___f_2103_ = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2103_, 0, v_toBind_2098_);
lean_closure_set(v___f_2103_, 1, v_get_2099_);
lean_closure_set(v___f_2103_, 2, v___f_2102_);
v___x_2104_ = lean_apply_4(v_toBind_2098_, lean_box(0), lean_box(0), v_x_2100_, v___f_2103_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg(lean_object* v_inst_2105_, lean_object* v_inst_2106_, lean_object* v_x_2107_){
_start:
{
lean_object* v_toApplicative_2108_; lean_object* v_toFunctor_2109_; lean_object* v_toBind_2110_; lean_object* v_toPure_2111_; lean_object* v_map_2112_; lean_object* v_get_2113_; lean_object* v___f_2114_; lean_object* v___f_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v_toApplicative_2108_ = lean_ctor_get(v_inst_2105_, 0);
lean_inc_ref(v_toApplicative_2108_);
v_toFunctor_2109_ = lean_ctor_get(v_toApplicative_2108_, 0);
lean_inc_ref(v_toFunctor_2109_);
v_toBind_2110_ = lean_ctor_get(v_inst_2105_, 1);
lean_inc_n(v_toBind_2110_, 2);
lean_dec_ref(v_inst_2105_);
v_toPure_2111_ = lean_ctor_get(v_toApplicative_2108_, 1);
lean_inc(v_toPure_2111_);
lean_dec_ref(v_toApplicative_2108_);
v_map_2112_ = lean_ctor_get(v_toFunctor_2109_, 0);
lean_inc(v_map_2112_);
lean_dec_ref(v_toFunctor_2109_);
v_get_2113_ = lean_ctor_get(v_inst_2106_, 0);
lean_inc_n(v_get_2113_, 2);
lean_dec_ref(v_inst_2106_);
v___f_2114_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2115_ = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2115_, 0, v_toPure_2111_);
lean_closure_set(v___f_2115_, 1, v_toBind_2110_);
lean_closure_set(v___f_2115_, 2, v_get_2113_);
lean_closure_set(v___f_2115_, 3, v_x_2107_);
v___x_2116_ = lean_apply_4(v_map_2112_, lean_box(0), lean_box(0), v___f_2114_, v_get_2113_);
v___x_2117_ = lean_apply_4(v_toBind_2110_, lean_box(0), lean_box(0), v___x_2116_, v___f_2115_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog(lean_object* v_m_2118_, lean_object* v_inst_2119_, lean_object* v_inst_2120_, lean_object* v_x_2121_){
_start:
{
lean_object* v_toApplicative_2122_; lean_object* v_toFunctor_2123_; lean_object* v_toBind_2124_; lean_object* v_toPure_2125_; lean_object* v_map_2126_; lean_object* v_get_2127_; lean_object* v___f_2128_; lean_object* v___f_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v_toApplicative_2122_ = lean_ctor_get(v_inst_2119_, 0);
lean_inc_ref(v_toApplicative_2122_);
v_toFunctor_2123_ = lean_ctor_get(v_toApplicative_2122_, 0);
lean_inc_ref(v_toFunctor_2123_);
v_toBind_2124_ = lean_ctor_get(v_inst_2119_, 1);
lean_inc_n(v_toBind_2124_, 2);
lean_dec_ref(v_inst_2119_);
v_toPure_2125_ = lean_ctor_get(v_toApplicative_2122_, 1);
lean_inc(v_toPure_2125_);
lean_dec_ref(v_toApplicative_2122_);
v_map_2126_ = lean_ctor_get(v_toFunctor_2123_, 0);
lean_inc(v_map_2126_);
lean_dec_ref(v_toFunctor_2123_);
v_get_2127_ = lean_ctor_get(v_inst_2120_, 0);
lean_inc_n(v_get_2127_, 2);
lean_dec_ref(v_inst_2120_);
v___f_2128_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2129_ = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2129_, 0, v_toPure_2125_);
lean_closure_set(v___f_2129_, 1, v_toBind_2124_);
lean_closure_set(v___f_2129_, 2, v_get_2127_);
lean_closure_set(v___f_2129_, 3, v_x_2121_);
v___x_2130_ = lean_apply_4(v_map_2126_, lean_box(0), lean_box(0), v___f_2128_, v_get_2127_);
v___x_2131_ = lean_apply_4(v_toBind_2124_, lean_box(0), lean_box(0), v___x_2130_, v___f_2129_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__1(lean_object* v_iniPos_2132_, lean_object* v_a_2133_, lean_object* v_toPure_2134_, lean_object* v_log_2135_){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2136_ = lean_array_get_size(v_log_2135_);
v___x_2137_ = l_Array_extract___redArg(v_log_2135_, v_iniPos_2132_, v___x_2136_);
v___x_2138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2138_, 0, v_a_2133_);
lean_ctor_set(v___x_2138_, 1, v___x_2137_);
v___x_2139_ = lean_apply_2(v_toPure_2134_, lean_box(0), v___x_2138_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__1___boxed(lean_object* v_iniPos_2140_, lean_object* v_a_2141_, lean_object* v_toPure_2142_, lean_object* v_log_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Lake_withExtractLog___redArg___lam__1(v_iniPos_2140_, v_a_2141_, v_toPure_2142_, v_log_2143_);
lean_dec_ref(v_log_2143_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__0(lean_object* v_iniPos_2145_, lean_object* v_toPure_2146_, lean_object* v_toBind_2147_, lean_object* v_get_2148_, lean_object* v_a_2149_){
_start:
{
lean_object* v___f_2150_; lean_object* v___x_2151_; 
v___f_2150_ = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2150_, 0, v_iniPos_2145_);
lean_closure_set(v___f_2150_, 1, v_a_2149_);
lean_closure_set(v___f_2150_, 2, v_toPure_2146_);
v___x_2151_ = lean_apply_4(v_toBind_2147_, lean_box(0), lean_box(0), v_get_2148_, v___f_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__2(lean_object* v_toPure_2152_, lean_object* v_toBind_2153_, lean_object* v_get_2154_, lean_object* v_x_2155_, lean_object* v_iniPos_2156_){
_start:
{
lean_object* v___f_2157_; lean_object* v___x_2158_; 
lean_inc(v_toBind_2153_);
v___f_2157_ = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2157_, 0, v_iniPos_2156_);
lean_closure_set(v___f_2157_, 1, v_toPure_2152_);
lean_closure_set(v___f_2157_, 2, v_toBind_2153_);
lean_closure_set(v___f_2157_, 3, v_get_2154_);
v___x_2158_ = lean_apply_4(v_toBind_2153_, lean_box(0), lean_box(0), v_x_2155_, v___f_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg(lean_object* v_inst_2159_, lean_object* v_inst_2160_, lean_object* v_x_2161_){
_start:
{
lean_object* v_toApplicative_2162_; lean_object* v_toFunctor_2163_; lean_object* v_toBind_2164_; lean_object* v_toPure_2165_; lean_object* v_map_2166_; lean_object* v_get_2167_; lean_object* v___f_2168_; lean_object* v___f_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v_toApplicative_2162_ = lean_ctor_get(v_inst_2159_, 0);
lean_inc_ref(v_toApplicative_2162_);
v_toFunctor_2163_ = lean_ctor_get(v_toApplicative_2162_, 0);
lean_inc_ref(v_toFunctor_2163_);
v_toBind_2164_ = lean_ctor_get(v_inst_2159_, 1);
lean_inc_n(v_toBind_2164_, 2);
lean_dec_ref(v_inst_2159_);
v_toPure_2165_ = lean_ctor_get(v_toApplicative_2162_, 1);
lean_inc(v_toPure_2165_);
lean_dec_ref(v_toApplicative_2162_);
v_map_2166_ = lean_ctor_get(v_toFunctor_2163_, 0);
lean_inc(v_map_2166_);
lean_dec_ref(v_toFunctor_2163_);
v_get_2167_ = lean_ctor_get(v_inst_2160_, 0);
lean_inc_n(v_get_2167_, 2);
lean_dec_ref(v_inst_2160_);
v___f_2168_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2169_ = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2169_, 0, v_toPure_2165_);
lean_closure_set(v___f_2169_, 1, v_toBind_2164_);
lean_closure_set(v___f_2169_, 2, v_get_2167_);
lean_closure_set(v___f_2169_, 3, v_x_2161_);
v___x_2170_ = lean_apply_4(v_map_2166_, lean_box(0), lean_box(0), v___f_2168_, v_get_2167_);
v___x_2171_ = lean_apply_4(v_toBind_2164_, lean_box(0), lean_box(0), v___x_2170_, v___f_2169_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog(lean_object* v_m_2172_, lean_object* v_00_u03b1_2173_, lean_object* v_inst_2174_, lean_object* v_inst_2175_, lean_object* v_x_2176_){
_start:
{
lean_object* v_toApplicative_2177_; lean_object* v_toFunctor_2178_; lean_object* v_toBind_2179_; lean_object* v_toPure_2180_; lean_object* v_map_2181_; lean_object* v_get_2182_; lean_object* v___f_2183_; lean_object* v___f_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v_toApplicative_2177_ = lean_ctor_get(v_inst_2174_, 0);
lean_inc_ref(v_toApplicative_2177_);
v_toFunctor_2178_ = lean_ctor_get(v_toApplicative_2177_, 0);
lean_inc_ref(v_toFunctor_2178_);
v_toBind_2179_ = lean_ctor_get(v_inst_2174_, 1);
lean_inc_n(v_toBind_2179_, 2);
lean_dec_ref(v_inst_2174_);
v_toPure_2180_ = lean_ctor_get(v_toApplicative_2177_, 1);
lean_inc(v_toPure_2180_);
lean_dec_ref(v_toApplicative_2177_);
v_map_2181_ = lean_ctor_get(v_toFunctor_2178_, 0);
lean_inc(v_map_2181_);
lean_dec_ref(v_toFunctor_2178_);
v_get_2182_ = lean_ctor_get(v_inst_2175_, 0);
lean_inc_n(v_get_2182_, 2);
lean_dec_ref(v_inst_2175_);
v___f_2183_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2184_ = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2184_, 0, v_toPure_2180_);
lean_closure_set(v___f_2184_, 1, v_toBind_2179_);
lean_closure_set(v___f_2184_, 2, v_get_2182_);
lean_closure_set(v___f_2184_, 3, v_x_2176_);
v___x_2185_ = lean_apply_4(v_map_2181_, lean_box(0), lean_box(0), v___f_2183_, v_get_2182_);
v___x_2186_ = lean_apply_4(v_toBind_2179_, lean_box(0), lean_box(0), v___x_2185_, v___f_2184_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__1(lean_object* v_iniPos_2187_, lean_object* v_inst_2188_, lean_object* v_toPure_2189_, lean_object* v_a_2190_, lean_object* v_endPos_2191_){
_start:
{
uint8_t v___x_2192_; 
v___x_2192_ = lean_nat_dec_eq(v_iniPos_2187_, v_endPos_2191_);
if (v___x_2192_ == 0)
{
lean_object* v_throw_2193_; lean_object* v___x_2194_; 
lean_dec(v_a_2190_);
lean_dec(v_toPure_2189_);
v_throw_2193_ = lean_ctor_get(v_inst_2188_, 0);
lean_inc(v_throw_2193_);
lean_dec_ref(v_inst_2188_);
v___x_2194_ = lean_apply_2(v_throw_2193_, lean_box(0), v_iniPos_2187_);
return v___x_2194_;
}
else
{
lean_object* v___x_2195_; 
lean_dec_ref(v_inst_2188_);
lean_dec(v_iniPos_2187_);
v___x_2195_ = lean_apply_2(v_toPure_2189_, lean_box(0), v_a_2190_);
return v___x_2195_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__1___boxed(lean_object* v_iniPos_2196_, lean_object* v_inst_2197_, lean_object* v_toPure_2198_, lean_object* v_a_2199_, lean_object* v_endPos_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lake_throwIfLogs___redArg___lam__1(v_iniPos_2196_, v_inst_2197_, v_toPure_2198_, v_a_2199_, v_endPos_2200_);
lean_dec(v_endPos_2200_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__0(lean_object* v_iniPos_2202_, lean_object* v_inst_2203_, lean_object* v_toPure_2204_, lean_object* v_toBind_2205_, lean_object* v___x_2206_, lean_object* v_a_2207_){
_start:
{
lean_object* v___f_2208_; lean_object* v___x_2209_; 
v___f_2208_ = lean_alloc_closure((void*)(l_Lake_throwIfLogs___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2208_, 0, v_iniPos_2202_);
lean_closure_set(v___f_2208_, 1, v_inst_2203_);
lean_closure_set(v___f_2208_, 2, v_toPure_2204_);
lean_closure_set(v___f_2208_, 3, v_a_2207_);
v___x_2209_ = lean_apply_4(v_toBind_2205_, lean_box(0), lean_box(0), v___x_2206_, v___f_2208_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__2(lean_object* v_inst_2210_, lean_object* v_toPure_2211_, lean_object* v_toBind_2212_, lean_object* v___x_2213_, lean_object* v_x_2214_, lean_object* v_iniPos_2215_){
_start:
{
lean_object* v___f_2216_; lean_object* v___x_2217_; 
lean_inc(v_toBind_2212_);
v___f_2216_ = lean_alloc_closure((void*)(l_Lake_throwIfLogs___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2216_, 0, v_iniPos_2215_);
lean_closure_set(v___f_2216_, 1, v_inst_2210_);
lean_closure_set(v___f_2216_, 2, v_toPure_2211_);
lean_closure_set(v___f_2216_, 3, v_toBind_2212_);
lean_closure_set(v___f_2216_, 4, v___x_2213_);
v___x_2217_ = lean_apply_4(v_toBind_2212_, lean_box(0), lean_box(0), v_x_2214_, v___f_2216_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg(lean_object* v_inst_2218_, lean_object* v_inst_2219_, lean_object* v_inst_2220_, lean_object* v_x_2221_){
_start:
{
lean_object* v_toApplicative_2222_; lean_object* v_toFunctor_2223_; lean_object* v_toBind_2224_; lean_object* v_toPure_2225_; lean_object* v_map_2226_; lean_object* v_get_2227_; lean_object* v___f_2228_; lean_object* v___x_2229_; lean_object* v___f_2230_; lean_object* v___x_2231_; 
v_toApplicative_2222_ = lean_ctor_get(v_inst_2218_, 0);
lean_inc_ref(v_toApplicative_2222_);
v_toFunctor_2223_ = lean_ctor_get(v_toApplicative_2222_, 0);
lean_inc_ref(v_toFunctor_2223_);
v_toBind_2224_ = lean_ctor_get(v_inst_2218_, 1);
lean_inc_n(v_toBind_2224_, 2);
lean_dec_ref(v_inst_2218_);
v_toPure_2225_ = lean_ctor_get(v_toApplicative_2222_, 1);
lean_inc(v_toPure_2225_);
lean_dec_ref(v_toApplicative_2222_);
v_map_2226_ = lean_ctor_get(v_toFunctor_2223_, 0);
lean_inc(v_map_2226_);
lean_dec_ref(v_toFunctor_2223_);
v_get_2227_ = lean_ctor_get(v_inst_2219_, 0);
lean_inc(v_get_2227_);
lean_dec_ref(v_inst_2219_);
v___f_2228_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_2229_ = lean_apply_4(v_map_2226_, lean_box(0), lean_box(0), v___f_2228_, v_get_2227_);
lean_inc(v___x_2229_);
v___f_2230_ = lean_alloc_closure((void*)(l_Lake_throwIfLogs___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2230_, 0, v_inst_2220_);
lean_closure_set(v___f_2230_, 1, v_toPure_2225_);
lean_closure_set(v___f_2230_, 2, v_toBind_2224_);
lean_closure_set(v___f_2230_, 3, v___x_2229_);
lean_closure_set(v___f_2230_, 4, v_x_2221_);
v___x_2231_ = lean_apply_4(v_toBind_2224_, lean_box(0), lean_box(0), v___x_2229_, v___f_2230_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs(lean_object* v_m_2232_, lean_object* v_00_u03b1_2233_, lean_object* v_inst_2234_, lean_object* v_inst_2235_, lean_object* v_inst_2236_, lean_object* v_x_2237_){
_start:
{
lean_object* v_toApplicative_2238_; lean_object* v_toFunctor_2239_; lean_object* v_toBind_2240_; lean_object* v_toPure_2241_; lean_object* v_map_2242_; lean_object* v_get_2243_; lean_object* v___f_2244_; lean_object* v___x_2245_; lean_object* v___f_2246_; lean_object* v___x_2247_; 
v_toApplicative_2238_ = lean_ctor_get(v_inst_2234_, 0);
lean_inc_ref(v_toApplicative_2238_);
v_toFunctor_2239_ = lean_ctor_get(v_toApplicative_2238_, 0);
lean_inc_ref(v_toFunctor_2239_);
v_toBind_2240_ = lean_ctor_get(v_inst_2234_, 1);
lean_inc_n(v_toBind_2240_, 2);
lean_dec_ref(v_inst_2234_);
v_toPure_2241_ = lean_ctor_get(v_toApplicative_2238_, 1);
lean_inc(v_toPure_2241_);
lean_dec_ref(v_toApplicative_2238_);
v_map_2242_ = lean_ctor_get(v_toFunctor_2239_, 0);
lean_inc(v_map_2242_);
lean_dec_ref(v_toFunctor_2239_);
v_get_2243_ = lean_ctor_get(v_inst_2235_, 0);
lean_inc(v_get_2243_);
lean_dec_ref(v_inst_2235_);
v___f_2244_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_2245_ = lean_apply_4(v_map_2242_, lean_box(0), lean_box(0), v___f_2244_, v_get_2243_);
lean_inc(v___x_2245_);
v___f_2246_ = lean_alloc_closure((void*)(l_Lake_throwIfLogs___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2246_, 0, v_inst_2236_);
lean_closure_set(v___f_2246_, 1, v_toPure_2241_);
lean_closure_set(v___f_2246_, 2, v_toBind_2240_);
lean_closure_set(v___f_2246_, 3, v___x_2245_);
lean_closure_set(v___f_2246_, 4, v_x_2237_);
v___x_2247_ = lean_apply_4(v_toBind_2240_, lean_box(0), lean_box(0), v___x_2245_, v___f_2246_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__1(lean_object* v_throw_2248_, lean_object* v_iniPos_2249_, lean_object* v_x_2250_){
_start:
{
lean_object* v___x_2251_; 
v___x_2251_ = lean_apply_2(v_throw_2248_, lean_box(0), v_iniPos_2249_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__1___boxed(lean_object* v_throw_2252_, lean_object* v_iniPos_2253_, lean_object* v_x_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Lake_withLogErrorPos___redArg___lam__1(v_throw_2252_, v_iniPos_2253_, v_x_2254_);
lean_dec(v_x_2254_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__0(lean_object* v_inst_2256_, lean_object* v_self_2257_, lean_object* v_iniPos_2258_){
_start:
{
lean_object* v_throw_2259_; lean_object* v_tryCatch_2260_; lean_object* v___f_2261_; lean_object* v___x_2262_; 
v_throw_2259_ = lean_ctor_get(v_inst_2256_, 0);
lean_inc(v_throw_2259_);
v_tryCatch_2260_ = lean_ctor_get(v_inst_2256_, 1);
lean_inc(v_tryCatch_2260_);
lean_dec_ref(v_inst_2256_);
v___f_2261_ = lean_alloc_closure((void*)(l_Lake_withLogErrorPos___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2261_, 0, v_throw_2259_);
lean_closure_set(v___f_2261_, 1, v_iniPos_2258_);
v___x_2262_ = lean_apply_3(v_tryCatch_2260_, lean_box(0), v_self_2257_, v___f_2261_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg(lean_object* v_inst_2263_, lean_object* v_inst_2264_, lean_object* v_inst_2265_, lean_object* v_self_2266_){
_start:
{
lean_object* v_toApplicative_2267_; lean_object* v_toFunctor_2268_; lean_object* v_toBind_2269_; lean_object* v_map_2270_; lean_object* v_get_2271_; lean_object* v___f_2272_; lean_object* v___f_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v_toApplicative_2267_ = lean_ctor_get(v_inst_2263_, 0);
v_toFunctor_2268_ = lean_ctor_get(v_toApplicative_2267_, 0);
lean_inc_ref(v_toFunctor_2268_);
v_toBind_2269_ = lean_ctor_get(v_inst_2263_, 1);
lean_inc(v_toBind_2269_);
lean_dec_ref(v_inst_2263_);
v_map_2270_ = lean_ctor_get(v_toFunctor_2268_, 0);
lean_inc(v_map_2270_);
lean_dec_ref(v_toFunctor_2268_);
v_get_2271_ = lean_ctor_get(v_inst_2264_, 0);
lean_inc(v_get_2271_);
lean_dec_ref(v_inst_2264_);
v___f_2272_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2273_ = lean_alloc_closure((void*)(l_Lake_withLogErrorPos___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2273_, 0, v_inst_2265_);
lean_closure_set(v___f_2273_, 1, v_self_2266_);
v___x_2274_ = lean_apply_4(v_map_2270_, lean_box(0), lean_box(0), v___f_2272_, v_get_2271_);
v___x_2275_ = lean_apply_4(v_toBind_2269_, lean_box(0), lean_box(0), v___x_2274_, v___f_2273_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos(lean_object* v_m_2276_, lean_object* v_00_u03b1_2277_, lean_object* v_inst_2278_, lean_object* v_inst_2279_, lean_object* v_inst_2280_, lean_object* v_self_2281_){
_start:
{
lean_object* v_toApplicative_2282_; lean_object* v_toFunctor_2283_; lean_object* v_toBind_2284_; lean_object* v_map_2285_; lean_object* v_get_2286_; lean_object* v___f_2287_; lean_object* v___f_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v_toApplicative_2282_ = lean_ctor_get(v_inst_2278_, 0);
v_toFunctor_2283_ = lean_ctor_get(v_toApplicative_2282_, 0);
lean_inc_ref(v_toFunctor_2283_);
v_toBind_2284_ = lean_ctor_get(v_inst_2278_, 1);
lean_inc(v_toBind_2284_);
lean_dec_ref(v_inst_2278_);
v_map_2285_ = lean_ctor_get(v_toFunctor_2283_, 0);
lean_inc(v_map_2285_);
lean_dec_ref(v_toFunctor_2283_);
v_get_2286_ = lean_ctor_get(v_inst_2279_, 0);
lean_inc(v_get_2286_);
lean_dec_ref(v_inst_2279_);
v___f_2287_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2288_ = lean_alloc_closure((void*)(l_Lake_withLogErrorPos___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2288_, 0, v_inst_2280_);
lean_closure_set(v___f_2288_, 1, v_self_2281_);
v___x_2289_ = lean_apply_4(v_map_2285_, lean_box(0), lean_box(0), v___f_2287_, v_get_2286_);
v___x_2290_ = lean_apply_4(v_toBind_2284_, lean_box(0), lean_box(0), v___x_2289_, v___f_2288_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__1(lean_object* v_toPure_2291_, lean_object* v_x_2292_){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = lean_box(0);
v___x_2294_ = lean_apply_2(v_toPure_2291_, lean_box(0), v___x_2293_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__1___boxed(lean_object* v_toPure_2295_, lean_object* v_x_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Lake_errorWithLog___redArg___lam__1(v_toPure_2295_, v_x_2296_);
lean_dec(v_x_2296_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__0(lean_object* v_throw_2298_, lean_object* v_iniPos_2299_, lean_object* v_____r_2300_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = lean_apply_2(v_throw_2298_, lean_box(0), v_iniPos_2299_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__2(lean_object* v_inst_2302_, lean_object* v_self_2303_, lean_object* v___f_2304_, lean_object* v_toBind_2305_, lean_object* v_iniPos_2306_){
_start:
{
lean_object* v_throw_2307_; lean_object* v_tryCatch_2308_; lean_object* v___f_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v_throw_2307_ = lean_ctor_get(v_inst_2302_, 0);
lean_inc(v_throw_2307_);
v_tryCatch_2308_ = lean_ctor_get(v_inst_2302_, 1);
lean_inc(v_tryCatch_2308_);
lean_dec_ref(v_inst_2302_);
v___f_2309_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2309_, 0, v_throw_2307_);
lean_closure_set(v___f_2309_, 1, v_iniPos_2306_);
v___x_2310_ = lean_apply_3(v_tryCatch_2308_, lean_box(0), v_self_2303_, v___f_2304_);
v___x_2311_ = lean_apply_4(v_toBind_2305_, lean_box(0), lean_box(0), v___x_2310_, v___f_2309_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg(lean_object* v_inst_2312_, lean_object* v_inst_2313_, lean_object* v_inst_2314_, lean_object* v_self_2315_){
_start:
{
lean_object* v_toApplicative_2316_; lean_object* v_toFunctor_2317_; lean_object* v_toBind_2318_; lean_object* v_toPure_2319_; lean_object* v_map_2320_; lean_object* v_get_2321_; lean_object* v___f_2322_; lean_object* v___f_2323_; lean_object* v___f_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v_toApplicative_2316_ = lean_ctor_get(v_inst_2312_, 0);
lean_inc_ref(v_toApplicative_2316_);
v_toFunctor_2317_ = lean_ctor_get(v_toApplicative_2316_, 0);
lean_inc_ref(v_toFunctor_2317_);
v_toBind_2318_ = lean_ctor_get(v_inst_2312_, 1);
lean_inc_n(v_toBind_2318_, 2);
lean_dec_ref(v_inst_2312_);
v_toPure_2319_ = lean_ctor_get(v_toApplicative_2316_, 1);
lean_inc(v_toPure_2319_);
lean_dec_ref(v_toApplicative_2316_);
v_map_2320_ = lean_ctor_get(v_toFunctor_2317_, 0);
lean_inc(v_map_2320_);
lean_dec_ref(v_toFunctor_2317_);
v_get_2321_ = lean_ctor_get(v_inst_2313_, 0);
lean_inc(v_get_2321_);
lean_dec_ref(v_inst_2313_);
v___f_2322_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2323_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2323_, 0, v_toPure_2319_);
v___f_2324_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2324_, 0, v_inst_2314_);
lean_closure_set(v___f_2324_, 1, v_self_2315_);
lean_closure_set(v___f_2324_, 2, v___f_2323_);
lean_closure_set(v___f_2324_, 3, v_toBind_2318_);
v___x_2325_ = lean_apply_4(v_map_2320_, lean_box(0), lean_box(0), v___f_2322_, v_get_2321_);
v___x_2326_ = lean_apply_4(v_toBind_2318_, lean_box(0), lean_box(0), v___x_2325_, v___f_2324_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog(lean_object* v_m_2327_, lean_object* v_00_u03b2_2328_, lean_object* v_inst_2329_, lean_object* v_inst_2330_, lean_object* v_inst_2331_, lean_object* v_self_2332_){
_start:
{
lean_object* v_toApplicative_2333_; lean_object* v_toFunctor_2334_; lean_object* v_toBind_2335_; lean_object* v_toPure_2336_; lean_object* v_map_2337_; lean_object* v_get_2338_; lean_object* v___f_2339_; lean_object* v___f_2340_; lean_object* v___f_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v_toApplicative_2333_ = lean_ctor_get(v_inst_2329_, 0);
lean_inc_ref(v_toApplicative_2333_);
v_toFunctor_2334_ = lean_ctor_get(v_toApplicative_2333_, 0);
lean_inc_ref(v_toFunctor_2334_);
v_toBind_2335_ = lean_ctor_get(v_inst_2329_, 1);
lean_inc_n(v_toBind_2335_, 2);
lean_dec_ref(v_inst_2329_);
v_toPure_2336_ = lean_ctor_get(v_toApplicative_2333_, 1);
lean_inc(v_toPure_2336_);
lean_dec_ref(v_toApplicative_2333_);
v_map_2337_ = lean_ctor_get(v_toFunctor_2334_, 0);
lean_inc(v_map_2337_);
lean_dec_ref(v_toFunctor_2334_);
v_get_2338_ = lean_ctor_get(v_inst_2330_, 0);
lean_inc(v_get_2338_);
lean_dec_ref(v_inst_2330_);
v___f_2339_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2340_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2340_, 0, v_toPure_2336_);
v___f_2341_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2341_, 0, v_inst_2331_);
lean_closure_set(v___f_2341_, 1, v_self_2332_);
lean_closure_set(v___f_2341_, 2, v___f_2340_);
lean_closure_set(v___f_2341_, 3, v_toBind_2335_);
v___x_2342_ = lean_apply_4(v_map_2337_, lean_box(0), lean_box(0), v___f_2339_, v_get_2338_);
v___x_2343_ = lean_apply_4(v_toBind_2335_, lean_box(0), lean_box(0), v___x_2342_, v___f_2341_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__0(lean_object* v_x_2344_){
_start:
{
lean_object* v_fst_2345_; 
v_fst_2345_ = lean_ctor_get(v_x_2344_, 0);
lean_inc(v_fst_2345_);
return v_fst_2345_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__0___boxed(lean_object* v_x_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lake_withLoggedIO___redArg___lam__0(v_x_2346_);
lean_dec_ref(v_x_2346_);
return v_res_2347_;
}
}
lean_object* l_Lake_withLoggedIO___redArg___lam__1(lean_object* v_buf_2348_){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = lean_st_ref_get(v_buf_2348_);
return v___x_2350_;
}
}
LEAN_EXPORT void l_Lake_withLoggedIO___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_buf_2348_ = stack[0].m_obj;
lean_object* v_res_2351_;
v_res_2351_ = l_Lake_withLoggedIO___redArg___lam__1(v_buf_2348_);
stack->m_obj
 = v_res_2351_;
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__1___boxed(lean_object* v_buf_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lake_withLoggedIO___redArg___lam__1(v_buf_2352_);
lean_dec(v_buf_2352_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__2(lean_object* v_toPure_2355_, lean_object* v_a_2356_, lean_object* v_____r_2357_){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = lean_apply_2(v_toPure_2355_, lean_box(0), v_a_2356_);
return v___x_2358_;
}
}
static lean_object* _init_l_Lake_withLoggedIO___redArg___lam__3___closed__4(void){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2363_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___lam__3___closed__3));
v___x_2364_ = lean_unsigned_to_nat(46u);
v___x_2365_ = lean_unsigned_to_nat(193u);
v___x_2366_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___lam__3___closed__2));
v___x_2367_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___lam__3___closed__1));
v___x_2368_ = l_mkPanicMessageWithDecl(v___x_2367_, v___x_2366_, v___x_2365_, v___x_2364_, v___x_2363_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__3(lean_object* v___x_2369_, lean_object* v_inst_2370_, lean_object* v_toBind_2371_, lean_object* v___f_2372_, lean_object* v_toPure_2373_, lean_object* v_a_2374_, lean_object* v_buf_2375_){
_start:
{
lean_object* v___y_2377_; lean_object* v_data_2390_; uint8_t v___x_2391_; 
v_data_2390_ = lean_ctor_get(v_buf_2375_, 0);
lean_inc_ref(v_data_2390_);
lean_dec_ref(v_buf_2375_);
v___x_2391_ = lean_string_validate_utf8(v_data_2390_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
lean_dec_ref(v_data_2390_);
v___x_2392_ = ((lean_object*)(l_Lake_instInhabitedLogEntry_default___closed__0));
v___x_2393_ = lean_obj_once(&l_Lake_withLoggedIO___redArg___lam__3___closed__4, &l_Lake_withLoggedIO___redArg___lam__3___closed__4_once, _init_l_Lake_withLoggedIO___redArg___lam__3___closed__4);
v___x_2394_ = l_panic___redArg(v___x_2392_, v___x_2393_);
v___y_2377_ = v___x_2394_;
goto v___jp_2376_;
}
else
{
lean_object* v___x_2395_; 
v___x_2395_ = lean_string_from_utf8_unchecked(v_data_2390_);
v___y_2377_ = v___x_2395_;
goto v___jp_2376_;
}
v___jp_2376_:
{
lean_object* v___x_2378_; uint8_t v___x_2379_; 
v___x_2378_ = lean_string_utf8_byte_size(v___y_2377_);
v___x_2379_ = lean_nat_dec_eq(v___x_2378_, v___x_2369_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
lean_dec(v_a_2374_);
lean_dec(v_toPure_2373_);
v___x_2380_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___lam__3___closed__0));
v___x_2381_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2381_, 0, v___y_2377_);
lean_ctor_set(v___x_2381_, 1, v___x_2369_);
lean_ctor_set(v___x_2381_, 2, v___x_2378_);
v___x_2382_ = l_String_Slice_trimAscii(v___x_2381_);
v___x_2383_ = l_String_Slice_toString(v___x_2382_);
lean_dec_ref(v___x_2382_);
v___x_2384_ = lean_string_append(v___x_2380_, v___x_2383_);
lean_dec_ref(v___x_2383_);
v___x_2385_ = 1;
v___x_2386_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2386_, 0, v___x_2384_);
lean_ctor_set_uint8(v___x_2386_, sizeof(void*)*1, v___x_2385_);
v___x_2387_ = lean_apply_1(v_inst_2370_, v___x_2386_);
v___x_2388_ = lean_apply_4(v_toBind_2371_, lean_box(0), lean_box(0), v___x_2387_, v___f_2372_);
return v___x_2388_;
}
else
{
lean_object* v___x_2389_; 
lean_dec_ref(v___y_2377_);
lean_dec(v___f_2372_);
lean_dec(v_toBind_2371_);
lean_dec(v_inst_2370_);
lean_dec(v___x_2369_);
v___x_2389_ = lean_apply_2(v_toPure_2373_, lean_box(0), v_a_2374_);
return v___x_2389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__4(lean_object* v_toPure_2396_, lean_object* v___x_2397_, lean_object* v_inst_2398_, lean_object* v_toBind_2399_, lean_object* v_inst_2400_, lean_object* v___f_2401_, lean_object* v_a_2402_){
_start:
{
lean_object* v___f_2403_; lean_object* v___f_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
lean_inc(v_a_2402_);
lean_inc(v_toPure_2396_);
v___f_2403_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2403_, 0, v_toPure_2396_);
lean_closure_set(v___f_2403_, 1, v_a_2402_);
lean_inc(v_toBind_2399_);
v___f_2404_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__3), 7, 6);
lean_closure_set(v___f_2404_, 0, v___x_2397_);
lean_closure_set(v___f_2404_, 1, v_inst_2398_);
lean_closure_set(v___f_2404_, 2, v_toBind_2399_);
lean_closure_set(v___f_2404_, 3, v___f_2403_);
lean_closure_set(v___f_2404_, 4, v_toPure_2396_);
lean_closure_set(v___f_2404_, 5, v_a_2402_);
v___x_2405_ = lean_apply_2(v_inst_2400_, lean_box(0), v___f_2401_);
v___x_2406_ = lean_apply_4(v_toBind_2399_, lean_box(0), lean_box(0), v___x_2405_, v___f_2404_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__5(lean_object* v_stderr_2407_, lean_object* v_inst_2408_, lean_object* v_mapConst_2409_, lean_object* v_____r_2410_){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2411_ = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(v___x_2411_, 0, v_stderr_2407_);
v___x_2412_ = lean_apply_2(v_inst_2408_, lean_box(0), v___x_2411_);
v___x_2413_ = lean_box(0);
v___x_2414_ = lean_apply_4(v_mapConst_2409_, lean_box(0), lean_box(0), v___x_2413_, v___x_2412_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__6(lean_object* v___x_2415_, lean_object* v_x_2416_){
_start:
{
lean_inc(v___x_2415_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__6___boxed(lean_object* v___x_2417_, lean_object* v_x_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Lake_withLoggedIO___redArg___lam__6(v___x_2417_, v_x_2418_);
lean_dec(v_x_2418_);
lean_dec(v___x_2417_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__7(lean_object* v_toFunctor_2420_, lean_object* v_inst_2421_, lean_object* v_stdout_2422_, lean_object* v_toBind_2423_, lean_object* v_inst_2424_, lean_object* v_x_2425_, lean_object* v___f_2426_, lean_object* v___f_2427_, lean_object* v_stderr_2428_){
_start:
{
lean_object* v_map_2429_; lean_object* v_mapConst_2430_; lean_object* v___f_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___f_2437_; lean_object* v_y_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v_map_2429_ = lean_ctor_get(v_toFunctor_2420_, 0);
lean_inc(v_map_2429_);
v_mapConst_2430_ = lean_ctor_get(v_toFunctor_2420_, 1);
lean_inc_n(v_mapConst_2430_, 2);
lean_dec_ref(v_toFunctor_2420_);
lean_inc(v_inst_2421_);
v___f_2431_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__5), 4, 3);
lean_closure_set(v___f_2431_, 0, v_stderr_2428_);
lean_closure_set(v___f_2431_, 1, v_inst_2421_);
lean_closure_set(v___f_2431_, 2, v_mapConst_2430_);
v___x_2432_ = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(v___x_2432_, 0, v_stdout_2422_);
v___x_2433_ = lean_apply_2(v_inst_2421_, lean_box(0), v___x_2432_);
v___x_2434_ = lean_box(0);
v___x_2435_ = lean_apply_4(v_mapConst_2430_, lean_box(0), lean_box(0), v___x_2434_, v___x_2433_);
lean_inc(v_toBind_2423_);
v___x_2436_ = lean_apply_4(v_toBind_2423_, lean_box(0), lean_box(0), v___x_2435_, v___f_2431_);
v___f_2437_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__6___boxed), 2, 1);
lean_closure_set(v___f_2437_, 0, v___x_2436_);
v_y_2438_ = lean_apply_4(v_inst_2424_, lean_box(0), lean_box(0), v_x_2425_, v___f_2437_);
v___x_2439_ = lean_apply_4(v_map_2429_, lean_box(0), lean_box(0), v___f_2426_, v_y_2438_);
v___x_2440_ = lean_apply_4(v_toBind_2423_, lean_box(0), lean_box(0), v___x_2439_, v___f_2427_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__8(lean_object* v_toFunctor_2441_, lean_object* v_inst_2442_, lean_object* v_toBind_2443_, lean_object* v_inst_2444_, lean_object* v_x_2445_, lean_object* v___f_2446_, lean_object* v___f_2447_, lean_object* v___x_2448_, lean_object* v_stdout_2449_){
_start:
{
lean_object* v___f_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
lean_inc(v_toBind_2443_);
lean_inc(v_inst_2442_);
v___f_2450_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__7), 9, 8);
lean_closure_set(v___f_2450_, 0, v_toFunctor_2441_);
lean_closure_set(v___f_2450_, 1, v_inst_2442_);
lean_closure_set(v___f_2450_, 2, v_stdout_2449_);
lean_closure_set(v___f_2450_, 3, v_toBind_2443_);
lean_closure_set(v___f_2450_, 4, v_inst_2444_);
lean_closure_set(v___f_2450_, 5, v_x_2445_);
lean_closure_set(v___f_2450_, 6, v___f_2446_);
lean_closure_set(v___f_2450_, 7, v___f_2447_);
v___x_2451_ = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(v___x_2451_, 0, v___x_2448_);
v___x_2452_ = lean_apply_2(v_inst_2442_, lean_box(0), v___x_2451_);
v___x_2453_ = lean_apply_4(v_toBind_2443_, lean_box(0), lean_box(0), v___x_2452_, v___f_2450_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__9(lean_object* v_toPure_2454_, lean_object* v___x_2455_, lean_object* v_inst_2456_, lean_object* v_toBind_2457_, lean_object* v_inst_2458_, lean_object* v_toFunctor_2459_, lean_object* v_inst_2460_, lean_object* v_x_2461_, lean_object* v___f_2462_, lean_object* v_buf_2463_){
_start:
{
lean_object* v___f_2464_; lean_object* v___f_2465_; lean_object* v___x_2466_; lean_object* v___f_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
lean_inc(v_buf_2463_);
v___f_2464_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2464_, 0, v_buf_2463_);
lean_inc_n(v_inst_2458_, 2);
lean_inc_n(v_toBind_2457_, 2);
v___f_2465_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__4), 7, 6);
lean_closure_set(v___f_2465_, 0, v_toPure_2454_);
lean_closure_set(v___f_2465_, 1, v___x_2455_);
lean_closure_set(v___f_2465_, 2, v_inst_2456_);
lean_closure_set(v___f_2465_, 3, v_toBind_2457_);
lean_closure_set(v___f_2465_, 4, v_inst_2458_);
lean_closure_set(v___f_2465_, 5, v___f_2464_);
v___x_2466_ = l_IO_FS_Stream_ofBuffer(v_buf_2463_);
lean_inc_ref(v___x_2466_);
v___f_2467_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__8), 9, 8);
lean_closure_set(v___f_2467_, 0, v_toFunctor_2459_);
lean_closure_set(v___f_2467_, 1, v_inst_2458_);
lean_closure_set(v___f_2467_, 2, v_toBind_2457_);
lean_closure_set(v___f_2467_, 3, v_inst_2460_);
lean_closure_set(v___f_2467_, 4, v_x_2461_);
lean_closure_set(v___f_2467_, 5, v___f_2462_);
lean_closure_set(v___f_2467_, 6, v___f_2465_);
lean_closure_set(v___f_2467_, 7, v___x_2466_);
v___x_2468_ = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(v___x_2468_, 0, v___x_2466_);
v___x_2469_ = lean_apply_2(v_inst_2458_, lean_box(0), v___x_2468_);
v___x_2470_ = lean_apply_4(v_toBind_2457_, lean_box(0), lean_box(0), v___x_2469_, v___f_2467_);
return v___x_2470_;
}
}
static lean_object* _init_l_Lake_withLoggedIO___redArg___closed__1(void){
_start:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2472_ = lean_unsigned_to_nat(0u);
v___x_2473_ = l_ByteArray_empty;
v___x_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2473_);
lean_ctor_set(v___x_2474_, 1, v___x_2472_);
return v___x_2474_;
}
}
static lean_object* _init_l_Lake_withLoggedIO___redArg___closed__2(void){
_start:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2475_ = lean_obj_once(&l_Lake_withLoggedIO___redArg___closed__1, &l_Lake_withLoggedIO___redArg___closed__1_once, _init_l_Lake_withLoggedIO___redArg___closed__1);
v___x_2476_ = lean_alloc_closure((void*)(l_IO_mkRef___boxed), 3, 2);
lean_closure_set(v___x_2476_, 0, lean_box(0));
lean_closure_set(v___x_2476_, 1, v___x_2475_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg(lean_object* v_inst_2477_, lean_object* v_inst_2478_, lean_object* v_inst_2479_, lean_object* v_inst_2480_, lean_object* v_x_2481_){
_start:
{
lean_object* v_toApplicative_2482_; lean_object* v_toBind_2483_; lean_object* v_toFunctor_2484_; lean_object* v_toPure_2485_; lean_object* v___f_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___f_2490_; lean_object* v___x_2491_; 
v_toApplicative_2482_ = lean_ctor_get(v_inst_2477_, 0);
lean_inc_ref(v_toApplicative_2482_);
v_toBind_2483_ = lean_ctor_get(v_inst_2477_, 1);
lean_inc_n(v_toBind_2483_, 2);
lean_dec_ref(v_inst_2477_);
v_toFunctor_2484_ = lean_ctor_get(v_toApplicative_2482_, 0);
lean_inc_ref(v_toFunctor_2484_);
v_toPure_2485_ = lean_ctor_get(v_toApplicative_2482_, 1);
lean_inc(v_toPure_2485_);
lean_dec_ref(v_toApplicative_2482_);
v___f_2486_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___closed__0));
v___x_2487_ = lean_unsigned_to_nat(0u);
v___x_2488_ = lean_obj_once(&l_Lake_withLoggedIO___redArg___closed__2, &l_Lake_withLoggedIO___redArg___closed__2_once, _init_l_Lake_withLoggedIO___redArg___closed__2);
lean_inc(v_inst_2478_);
v___x_2489_ = lean_apply_2(v_inst_2478_, lean_box(0), v___x_2488_);
v___f_2490_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__9), 10, 9);
lean_closure_set(v___f_2490_, 0, v_toPure_2485_);
lean_closure_set(v___f_2490_, 1, v___x_2487_);
lean_closure_set(v___f_2490_, 2, v_inst_2479_);
lean_closure_set(v___f_2490_, 3, v_toBind_2483_);
lean_closure_set(v___f_2490_, 4, v_inst_2478_);
lean_closure_set(v___f_2490_, 5, v_toFunctor_2484_);
lean_closure_set(v___f_2490_, 6, v_inst_2480_);
lean_closure_set(v___f_2490_, 7, v_x_2481_);
lean_closure_set(v___f_2490_, 8, v___f_2486_);
v___x_2491_ = lean_apply_4(v_toBind_2483_, lean_box(0), lean_box(0), v___x_2489_, v___f_2490_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO(lean_object* v_m_2492_, lean_object* v_00_u03b1_2493_, lean_object* v_inst_2494_, lean_object* v_inst_2495_, lean_object* v_inst_2496_, lean_object* v_inst_2497_, lean_object* v_x_2498_){
_start:
{
lean_object* v_toApplicative_2499_; lean_object* v_toBind_2500_; lean_object* v_toFunctor_2501_; lean_object* v_toPure_2502_; lean_object* v___f_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___f_2507_; lean_object* v___x_2508_; 
v_toApplicative_2499_ = lean_ctor_get(v_inst_2494_, 0);
lean_inc_ref(v_toApplicative_2499_);
v_toBind_2500_ = lean_ctor_get(v_inst_2494_, 1);
lean_inc_n(v_toBind_2500_, 2);
lean_dec_ref(v_inst_2494_);
v_toFunctor_2501_ = lean_ctor_get(v_toApplicative_2499_, 0);
lean_inc_ref(v_toFunctor_2501_);
v_toPure_2502_ = lean_ctor_get(v_toApplicative_2499_, 1);
lean_inc(v_toPure_2502_);
lean_dec_ref(v_toApplicative_2499_);
v___f_2503_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___closed__0));
v___x_2504_ = lean_unsigned_to_nat(0u);
v___x_2505_ = lean_obj_once(&l_Lake_withLoggedIO___redArg___closed__2, &l_Lake_withLoggedIO___redArg___closed__2_once, _init_l_Lake_withLoggedIO___redArg___closed__2);
lean_inc(v_inst_2495_);
v___x_2506_ = lean_apply_2(v_inst_2495_, lean_box(0), v___x_2505_);
v___f_2507_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__9), 10, 9);
lean_closure_set(v___f_2507_, 0, v_toPure_2502_);
lean_closure_set(v___f_2507_, 1, v___x_2504_);
lean_closure_set(v___f_2507_, 2, v_inst_2496_);
lean_closure_set(v___f_2507_, 3, v_toBind_2500_);
lean_closure_set(v___f_2507_, 4, v_inst_2495_);
lean_closure_set(v___f_2507_, 5, v_toFunctor_2501_);
lean_closure_set(v___f_2507_, 6, v_inst_2497_);
lean_closure_set(v___f_2507_, 7, v_x_2498_);
lean_closure_set(v___f_2507_, 8, v___f_2503_);
v___x_2508_ = lean_apply_4(v_toBind_2500_, lean_box(0), lean_box(0), v___x_2506_, v___f_2507_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_error___redArg___lam__3(lean_object* v_inst_2509_, lean_object* v___x_2510_, lean_object* v___f_2511_, lean_object* v_toBind_2512_, lean_object* v_iniPos_2513_){
_start:
{
lean_object* v_throw_2514_; lean_object* v_tryCatch_2515_; lean_object* v___f_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v_throw_2514_ = lean_ctor_get(v_inst_2509_, 0);
lean_inc(v_throw_2514_);
v_tryCatch_2515_ = lean_ctor_get(v_inst_2509_, 1);
lean_inc(v_tryCatch_2515_);
lean_dec_ref(v_inst_2509_);
v___f_2516_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2516_, 0, v_throw_2514_);
lean_closure_set(v___f_2516_, 1, v_iniPos_2513_);
v___x_2517_ = lean_apply_3(v_tryCatch_2515_, lean_box(0), v___x_2510_, v___f_2511_);
v___x_2518_ = lean_apply_4(v_toBind_2512_, lean_box(0), lean_box(0), v___x_2517_, v___f_2516_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_error___redArg(lean_object* v_inst_2519_, lean_object* v_inst_2520_, lean_object* v_inst_2521_, lean_object* v_inst_2522_, lean_object* v_msg_2523_){
_start:
{
lean_object* v_toApplicative_2524_; lean_object* v_toFunctor_2525_; lean_object* v_toBind_2526_; lean_object* v_toPure_2527_; lean_object* v_map_2528_; lean_object* v_get_2529_; lean_object* v___f_2530_; uint8_t v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___f_2534_; lean_object* v___f_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v_toApplicative_2524_ = lean_ctor_get(v_inst_2519_, 0);
lean_inc_ref(v_toApplicative_2524_);
v_toFunctor_2525_ = lean_ctor_get(v_toApplicative_2524_, 0);
lean_inc_ref(v_toFunctor_2525_);
v_toBind_2526_ = lean_ctor_get(v_inst_2519_, 1);
lean_inc_n(v_toBind_2526_, 2);
lean_dec_ref(v_inst_2519_);
v_toPure_2527_ = lean_ctor_get(v_toApplicative_2524_, 1);
lean_inc(v_toPure_2527_);
lean_dec_ref(v_toApplicative_2524_);
v_map_2528_ = lean_ctor_get(v_toFunctor_2525_, 0);
lean_inc(v_map_2528_);
lean_dec_ref(v_toFunctor_2525_);
v_get_2529_ = lean_ctor_get(v_inst_2521_, 0);
lean_inc(v_get_2529_);
lean_dec_ref(v_inst_2521_);
v___f_2530_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_2531_ = 3;
v___x_2532_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2532_, 0, v_msg_2523_);
lean_ctor_set_uint8(v___x_2532_, sizeof(void*)*1, v___x_2531_);
v___x_2533_ = lean_apply_1(v_inst_2520_, v___x_2532_);
v___f_2534_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2534_, 0, v_toPure_2527_);
v___f_2535_ = lean_alloc_closure((void*)(l_Lake_ELog_error___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2535_, 0, v_inst_2522_);
lean_closure_set(v___f_2535_, 1, v___x_2533_);
lean_closure_set(v___f_2535_, 2, v___f_2534_);
lean_closure_set(v___f_2535_, 3, v_toBind_2526_);
v___x_2536_ = lean_apply_4(v_map_2528_, lean_box(0), lean_box(0), v___f_2530_, v_get_2529_);
v___x_2537_ = lean_apply_4(v_toBind_2526_, lean_box(0), lean_box(0), v___x_2536_, v___f_2535_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_error(lean_object* v_m_2538_, lean_object* v_00_u03b1_2539_, lean_object* v_inst_2540_, lean_object* v_inst_2541_, lean_object* v_inst_2542_, lean_object* v_inst_2543_, lean_object* v_msg_2544_){
_start:
{
lean_object* v_toApplicative_2545_; lean_object* v_toFunctor_2546_; lean_object* v_toBind_2547_; lean_object* v_toPure_2548_; lean_object* v_map_2549_; lean_object* v_get_2550_; lean_object* v___f_2551_; uint8_t v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___f_2555_; lean_object* v___f_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v_toApplicative_2545_ = lean_ctor_get(v_inst_2540_, 0);
lean_inc_ref(v_toApplicative_2545_);
v_toFunctor_2546_ = lean_ctor_get(v_toApplicative_2545_, 0);
lean_inc_ref(v_toFunctor_2546_);
v_toBind_2547_ = lean_ctor_get(v_inst_2540_, 1);
lean_inc_n(v_toBind_2547_, 2);
lean_dec_ref(v_inst_2540_);
v_toPure_2548_ = lean_ctor_get(v_toApplicative_2545_, 1);
lean_inc(v_toPure_2548_);
lean_dec_ref(v_toApplicative_2545_);
v_map_2549_ = lean_ctor_get(v_toFunctor_2546_, 0);
lean_inc(v_map_2549_);
lean_dec_ref(v_toFunctor_2546_);
v_get_2550_ = lean_ctor_get(v_inst_2542_, 0);
lean_inc(v_get_2550_);
lean_dec_ref(v_inst_2542_);
v___f_2551_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_2552_ = 3;
v___x_2553_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2553_, 0, v_msg_2544_);
lean_ctor_set_uint8(v___x_2553_, sizeof(void*)*1, v___x_2552_);
v___x_2554_ = lean_apply_1(v_inst_2541_, v___x_2553_);
v___f_2555_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2555_, 0, v_toPure_2548_);
v___f_2556_ = lean_alloc_closure((void*)(l_Lake_ELog_error___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2556_, 0, v_inst_2543_);
lean_closure_set(v___f_2556_, 1, v___x_2554_);
lean_closure_set(v___f_2556_, 2, v___f_2555_);
lean_closure_set(v___f_2556_, 3, v_toBind_2547_);
v___x_2557_ = lean_apply_4(v_map_2549_, lean_box(0), lean_box(0), v___f_2551_, v_get_2550_);
v___x_2558_ = lean_apply_4(v_toBind_2547_, lean_box(0), lean_box(0), v___x_2557_, v___f_2556_);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_monadError___redArg___lam__4(lean_object* v_inst_2559_, lean_object* v_inst_2560_, lean_object* v_inst_2561_, lean_object* v_inst_2562_, lean_object* v___f_2563_, lean_object* v_00_u03b1_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v_toApplicative_2566_; lean_object* v_toFunctor_2567_; lean_object* v_toBind_2568_; lean_object* v_toPure_2569_; lean_object* v_map_2570_; lean_object* v_get_2571_; uint8_t v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___f_2575_; lean_object* v___f_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v_toApplicative_2566_ = lean_ctor_get(v_inst_2559_, 0);
lean_inc_ref(v_toApplicative_2566_);
v_toFunctor_2567_ = lean_ctor_get(v_toApplicative_2566_, 0);
lean_inc_ref(v_toFunctor_2567_);
v_toBind_2568_ = lean_ctor_get(v_inst_2559_, 1);
lean_inc_n(v_toBind_2568_, 2);
lean_dec_ref(v_inst_2559_);
v_toPure_2569_ = lean_ctor_get(v_toApplicative_2566_, 1);
lean_inc(v_toPure_2569_);
lean_dec_ref(v_toApplicative_2566_);
v_map_2570_ = lean_ctor_get(v_toFunctor_2567_, 0);
lean_inc(v_map_2570_);
lean_dec_ref(v_toFunctor_2567_);
v_get_2571_ = lean_ctor_get(v_inst_2560_, 0);
lean_inc(v_get_2571_);
lean_dec_ref(v_inst_2560_);
v___x_2572_ = 3;
v___x_2573_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2573_, 0, v___y_2565_);
lean_ctor_set_uint8(v___x_2573_, sizeof(void*)*1, v___x_2572_);
v___x_2574_ = lean_apply_1(v_inst_2561_, v___x_2573_);
v___f_2575_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2575_, 0, v_toPure_2569_);
v___f_2576_ = lean_alloc_closure((void*)(l_Lake_ELog_error___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2576_, 0, v_inst_2562_);
lean_closure_set(v___f_2576_, 1, v___x_2574_);
lean_closure_set(v___f_2576_, 2, v___f_2575_);
lean_closure_set(v___f_2576_, 3, v_toBind_2568_);
v___x_2577_ = lean_apply_4(v_map_2570_, lean_box(0), lean_box(0), v___f_2563_, v_get_2571_);
v___x_2578_ = lean_apply_4(v_toBind_2568_, lean_box(0), lean_box(0), v___x_2577_, v___f_2576_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_monadError___redArg(lean_object* v_inst_2579_, lean_object* v_inst_2580_, lean_object* v_inst_2581_, lean_object* v_inst_2582_){
_start:
{
lean_object* v___f_2583_; lean_object* v___f_2584_; 
v___f_2583_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2584_ = lean_alloc_closure((void*)(l_Lake_ELog_monadError___redArg___lam__4), 7, 5);
lean_closure_set(v___f_2584_, 0, v_inst_2579_);
lean_closure_set(v___f_2584_, 1, v_inst_2581_);
lean_closure_set(v___f_2584_, 2, v_inst_2580_);
lean_closure_set(v___f_2584_, 3, v_inst_2582_);
lean_closure_set(v___f_2584_, 4, v___f_2583_);
return v___f_2584_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_monadError(lean_object* v_m_2585_, lean_object* v_inst_2586_, lean_object* v_inst_2587_, lean_object* v_inst_2588_, lean_object* v_inst_2589_){
_start:
{
lean_object* v___f_2590_; lean_object* v___f_2591_; 
v___f_2590_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2591_ = lean_alloc_closure((void*)(l_Lake_ELog_monadError___redArg___lam__4), 7, 5);
lean_closure_set(v___f_2591_, 0, v_inst_2586_);
lean_closure_set(v___f_2591_, 1, v_inst_2588_);
lean_closure_set(v___f_2591_, 2, v_inst_2587_);
lean_closure_set(v___f_2591_, 3, v_inst_2589_);
lean_closure_set(v___f_2591_, 4, v___f_2590_);
return v___f_2591_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_failure___redArg___lam__1(lean_object* v_inst_2592_, lean_object* v_____do__lift_2593_){
_start:
{
lean_object* v_throw_2594_; lean_object* v___x_2595_; 
v_throw_2594_ = lean_ctor_get(v_inst_2592_, 0);
lean_inc(v_throw_2594_);
lean_dec_ref(v_inst_2592_);
v___x_2595_ = lean_apply_2(v_throw_2594_, lean_box(0), v_____do__lift_2593_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_failure___redArg(lean_object* v_inst_2596_, lean_object* v_inst_2597_, lean_object* v_inst_2598_){
_start:
{
lean_object* v_toApplicative_2599_; lean_object* v_toFunctor_2600_; lean_object* v_toBind_2601_; lean_object* v_map_2602_; lean_object* v_get_2603_; lean_object* v___f_2604_; lean_object* v___f_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v_toApplicative_2599_ = lean_ctor_get(v_inst_2596_, 0);
v_toFunctor_2600_ = lean_ctor_get(v_toApplicative_2599_, 0);
lean_inc_ref(v_toFunctor_2600_);
v_toBind_2601_ = lean_ctor_get(v_inst_2596_, 1);
lean_inc(v_toBind_2601_);
lean_dec_ref(v_inst_2596_);
v_map_2602_ = lean_ctor_get(v_toFunctor_2600_, 0);
lean_inc(v_map_2602_);
lean_dec_ref(v_toFunctor_2600_);
v_get_2603_ = lean_ctor_get(v_inst_2597_, 0);
lean_inc(v_get_2603_);
lean_dec_ref(v_inst_2597_);
v___f_2604_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2605_ = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2605_, 0, v_inst_2598_);
v___x_2606_ = lean_apply_4(v_map_2602_, lean_box(0), lean_box(0), v___f_2604_, v_get_2603_);
v___x_2607_ = lean_apply_4(v_toBind_2601_, lean_box(0), lean_box(0), v___x_2606_, v___f_2605_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_failure(lean_object* v_m_2608_, lean_object* v_00_u03b1_2609_, lean_object* v_inst_2610_, lean_object* v_inst_2611_, lean_object* v_inst_2612_){
_start:
{
lean_object* v_toApplicative_2613_; lean_object* v_toFunctor_2614_; lean_object* v_toBind_2615_; lean_object* v_map_2616_; lean_object* v_get_2617_; lean_object* v___f_2618_; lean_object* v___f_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v_toApplicative_2613_ = lean_ctor_get(v_inst_2610_, 0);
v_toFunctor_2614_ = lean_ctor_get(v_toApplicative_2613_, 0);
lean_inc_ref(v_toFunctor_2614_);
v_toBind_2615_ = lean_ctor_get(v_inst_2610_, 1);
lean_inc(v_toBind_2615_);
lean_dec_ref(v_inst_2610_);
v_map_2616_ = lean_ctor_get(v_toFunctor_2614_, 0);
lean_inc(v_map_2616_);
lean_dec_ref(v_toFunctor_2614_);
v_get_2617_ = lean_ctor_get(v_inst_2611_, 0);
lean_inc(v_get_2617_);
lean_dec_ref(v_inst_2611_);
v___f_2618_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2619_ = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2619_, 0, v_inst_2612_);
v___x_2620_ = lean_apply_4(v_map_2616_, lean_box(0), lean_box(0), v___f_2618_, v_get_2617_);
v___x_2621_ = lean_apply_4(v_toBind_2615_, lean_box(0), lean_box(0), v___x_2620_, v___f_2619_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__0(lean_object* v_y_2622_, lean_object* v_____r_2623_){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = lean_box(0);
v___x_2625_ = lean_apply_1(v_y_2622_, v___x_2624_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__1(lean_object* v_errPos_2626_, lean_object* v_s_2627_){
_start:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2628_ = lean_box(0);
v___x_2629_ = l_Array_shrink___redArg(v_s_2627_, v_errPos_2626_);
v___x_2630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2628_);
lean_ctor_set(v___x_2630_, 1, v___x_2629_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__1___boxed(lean_object* v_errPos_2631_, lean_object* v_s_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Lake_ELog_orElse___redArg___lam__1(v_errPos_2631_, v_s_2632_);
lean_dec(v_errPos_2631_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__2(lean_object* v_inst_2634_, lean_object* v_toBind_2635_, lean_object* v___f_2636_, lean_object* v_errPos_2637_){
_start:
{
lean_object* v_modifyGet_2638_; lean_object* v___f_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v_modifyGet_2638_ = lean_ctor_get(v_inst_2634_, 2);
lean_inc(v_modifyGet_2638_);
lean_dec_ref(v_inst_2634_);
v___f_2639_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2639_, 0, v_errPos_2637_);
v___x_2640_ = lean_apply_2(v_modifyGet_2638_, lean_box(0), v___f_2639_);
v___x_2641_ = lean_apply_4(v_toBind_2635_, lean_box(0), lean_box(0), v___x_2640_, v___f_2636_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg(lean_object* v_inst_2642_, lean_object* v_inst_2643_, lean_object* v_inst_2644_, lean_object* v_x_2645_, lean_object* v_y_2646_){
_start:
{
lean_object* v_toBind_2647_; lean_object* v_tryCatch_2648_; lean_object* v___f_2649_; lean_object* v___f_2650_; lean_object* v___x_2651_; 
v_toBind_2647_ = lean_ctor_get(v_inst_2642_, 1);
lean_inc(v_toBind_2647_);
lean_dec_ref(v_inst_2642_);
v_tryCatch_2648_ = lean_ctor_get(v_inst_2644_, 1);
lean_inc(v_tryCatch_2648_);
lean_dec_ref(v_inst_2644_);
v___f_2649_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2649_, 0, v_y_2646_);
v___f_2650_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2650_, 0, v_inst_2643_);
lean_closure_set(v___f_2650_, 1, v_toBind_2647_);
lean_closure_set(v___f_2650_, 2, v___f_2649_);
v___x_2651_ = lean_apply_3(v_tryCatch_2648_, lean_box(0), v_x_2645_, v___f_2650_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse(lean_object* v_m_2652_, lean_object* v_00_u03b1_2653_, lean_object* v_inst_2654_, lean_object* v_inst_2655_, lean_object* v_inst_2656_, lean_object* v_x_2657_, lean_object* v_y_2658_){
_start:
{
lean_object* v_toBind_2659_; lean_object* v_tryCatch_2660_; lean_object* v___f_2661_; lean_object* v___f_2662_; lean_object* v___x_2663_; 
v_toBind_2659_ = lean_ctor_get(v_inst_2654_, 1);
lean_inc(v_toBind_2659_);
lean_dec_ref(v_inst_2654_);
v_tryCatch_2660_ = lean_ctor_get(v_inst_2656_, 1);
lean_inc(v_tryCatch_2660_);
lean_dec_ref(v_inst_2656_);
v___f_2661_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2661_, 0, v_y_2658_);
v___f_2662_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2662_, 0, v_inst_2655_);
lean_closure_set(v___f_2662_, 1, v_toBind_2659_);
lean_closure_set(v___f_2662_, 2, v___f_2661_);
v___x_2663_ = lean_apply_3(v_tryCatch_2660_, lean_box(0), v_x_2657_, v___f_2662_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__2(lean_object* v_toApplicative_2664_, lean_object* v_inst_2665_, lean_object* v___f_2666_, lean_object* v_toBind_2667_, lean_object* v___f_2668_, lean_object* v_00_u03b1_2669_){
_start:
{
lean_object* v_toFunctor_2670_; lean_object* v_map_2671_; lean_object* v_get_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v_toFunctor_2670_ = lean_ctor_get(v_toApplicative_2664_, 0);
lean_inc_ref(v_toFunctor_2670_);
lean_dec_ref(v_toApplicative_2664_);
v_map_2671_ = lean_ctor_get(v_toFunctor_2670_, 0);
lean_inc(v_map_2671_);
lean_dec_ref(v_toFunctor_2670_);
v_get_2672_ = lean_ctor_get(v_inst_2665_, 0);
lean_inc(v_get_2672_);
lean_dec_ref(v_inst_2665_);
v___x_2673_ = lean_apply_4(v_map_2671_, lean_box(0), lean_box(0), v___f_2666_, v_get_2672_);
v___x_2674_ = lean_apply_4(v_toBind_2667_, lean_box(0), lean_box(0), v___x_2673_, v___f_2668_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__0(lean_object* v___y_2675_, lean_object* v_____r_2676_){
_start:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2677_ = lean_box(0);
v___x_2678_ = lean_apply_1(v___y_2675_, v___x_2677_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__4(lean_object* v_inst_2679_, lean_object* v_inst_2680_, lean_object* v_toBind_2681_, lean_object* v_00_u03b1_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v_tryCatch_2685_; lean_object* v___f_2686_; lean_object* v___f_2687_; lean_object* v___x_2688_; 
v_tryCatch_2685_ = lean_ctor_get(v_inst_2679_, 1);
lean_inc(v_tryCatch_2685_);
lean_dec_ref(v_inst_2679_);
v___f_2686_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2686_, 0, v___y_2684_);
v___f_2687_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2687_, 0, v_inst_2680_);
lean_closure_set(v___f_2687_, 1, v_toBind_2681_);
lean_closure_set(v___f_2687_, 2, v___f_2686_);
v___x_2688_ = lean_apply_3(v_tryCatch_2685_, lean_box(0), v___y_2683_, v___f_2687_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg(lean_object* v_inst_2689_, lean_object* v_inst_2690_, lean_object* v_inst_2691_){
_start:
{
lean_object* v_toApplicative_2692_; lean_object* v_toBind_2693_; lean_object* v___f_2694_; lean_object* v___f_2695_; lean_object* v___f_2696_; lean_object* v___f_2697_; lean_object* v___x_2698_; 
v_toApplicative_2692_ = lean_ctor_get(v_inst_2689_, 0);
lean_inc_ref_n(v_toApplicative_2692_, 2);
v_toBind_2693_ = lean_ctor_get(v_inst_2689_, 1);
lean_inc_n(v_toBind_2693_, 2);
lean_dec_ref(v_inst_2689_);
v___f_2694_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
lean_inc_ref(v_inst_2691_);
v___f_2695_ = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2695_, 0, v_inst_2691_);
lean_inc_ref(v_inst_2690_);
v___f_2696_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2696_, 0, v_toApplicative_2692_);
lean_closure_set(v___f_2696_, 1, v_inst_2690_);
lean_closure_set(v___f_2696_, 2, v___f_2694_);
lean_closure_set(v___f_2696_, 3, v_toBind_2693_);
lean_closure_set(v___f_2696_, 4, v___f_2695_);
v___f_2697_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__4), 6, 3);
lean_closure_set(v___f_2697_, 0, v_inst_2691_);
lean_closure_set(v___f_2697_, 1, v_inst_2690_);
lean_closure_set(v___f_2697_, 2, v_toBind_2693_);
v___x_2698_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2698_, 0, v_toApplicative_2692_);
lean_ctor_set(v___x_2698_, 1, v___f_2696_);
lean_ctor_set(v___x_2698_, 2, v___f_2697_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative(lean_object* v_m_2699_, lean_object* v_inst_2700_, lean_object* v_inst_2701_, lean_object* v_inst_2702_){
_start:
{
lean_object* v_toApplicative_2703_; lean_object* v_toBind_2704_; lean_object* v___f_2705_; lean_object* v___f_2706_; lean_object* v___f_2707_; lean_object* v___f_2708_; lean_object* v___x_2709_; 
v_toApplicative_2703_ = lean_ctor_get(v_inst_2700_, 0);
lean_inc_ref_n(v_toApplicative_2703_, 2);
v_toBind_2704_ = lean_ctor_get(v_inst_2700_, 1);
lean_inc_n(v_toBind_2704_, 2);
lean_dec_ref(v_inst_2700_);
v___f_2705_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
lean_inc_ref(v_inst_2702_);
v___f_2706_ = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2706_, 0, v_inst_2702_);
lean_inc_ref(v_inst_2701_);
v___f_2707_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2707_, 0, v_toApplicative_2703_);
lean_closure_set(v___f_2707_, 1, v_inst_2701_);
lean_closure_set(v___f_2707_, 2, v___f_2705_);
lean_closure_set(v___f_2707_, 3, v_toBind_2704_);
lean_closure_set(v___f_2707_, 4, v___f_2706_);
v___f_2708_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__4), 6, 3);
lean_closure_set(v___f_2708_, 0, v_inst_2702_);
lean_closure_set(v___f_2708_, 1, v_inst_2701_);
lean_closure_set(v___f_2708_, 2, v_toBind_2704_);
v___x_2709_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2709_, 0, v_toApplicative_2703_);
lean_ctor_set(v___x_2709_, 1, v___f_2707_);
lean_ctor_set(v___x_2709_, 2, v___f_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogLogTOfMonad___redArg(lean_object* v_inst_2710_){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2711_ = l_instMonadStateOfStateTOfMonad___redArg(v_inst_2710_);
v___x_2712_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(v___x_2712_, 0, lean_box(0));
lean_closure_set(v___x_2712_, 1, v___x_2711_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogLogTOfMonad(lean_object* v_m_2713_, lean_object* v_inst_2714_){
_start:
{
lean_object* v___x_2715_; 
v___x_2715_ = l_Lake_instMonadLogLogTOfMonad___redArg(v_inst_2714_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run___redArg(lean_object* v_self_2716_, lean_object* v_log_2717_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = lean_apply_1(v_self_2716_, v_log_2717_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run(lean_object* v_m_2719_, lean_object* v_00_u03b1_2720_, lean_object* v_self_2721_, lean_object* v_log_2722_){
_start:
{
lean_object* v___x_2723_; 
v___x_2723_ = lean_apply_1(v_self_2721_, v_log_2722_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg___lam__0(lean_object* v_x_2724_){
_start:
{
lean_object* v_fst_2725_; 
v_fst_2725_ = lean_ctor_get(v_x_2724_, 0);
lean_inc(v_fst_2725_);
return v_fst_2725_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg___lam__0___boxed(lean_object* v_x_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l_Lake_LogT_run_x27___redArg___lam__0(v_x_2726_);
lean_dec_ref(v_x_2726_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg(lean_object* v_inst_2729_, lean_object* v_self_2730_, lean_object* v_log_2731_){
_start:
{
lean_object* v_map_2732_; lean_object* v___f_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v_map_2732_ = lean_ctor_get(v_inst_2729_, 0);
lean_inc(v_map_2732_);
lean_dec_ref(v_inst_2729_);
v___f_2733_ = ((lean_object*)(l_Lake_LogT_run_x27___redArg___closed__0));
v___x_2734_ = lean_apply_1(v_self_2730_, v_log_2731_);
v___x_2735_ = lean_apply_4(v_map_2732_, lean_box(0), lean_box(0), v___f_2733_, v___x_2734_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27(lean_object* v_m_2736_, lean_object* v_00_u03b1_2737_, lean_object* v_inst_2738_, lean_object* v_self_2739_, lean_object* v_log_2740_){
_start:
{
lean_object* v_map_2741_; lean_object* v___f_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
v_map_2741_ = lean_ctor_get(v_inst_2738_, 0);
lean_inc(v_map_2741_);
lean_dec_ref(v_inst_2738_);
v___f_2742_ = ((lean_object*)(l_Lake_LogT_run_x27___redArg___closed__0));
v___x_2743_ = lean_apply_1(v_self_2739_, v_log_2740_);
v___x_2744_ = lean_apply_4(v_map_2741_, lean_box(0), lean_box(0), v___f_2742_, v___x_2743_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__1(lean_object* v_toPure_2745_, lean_object* v_fst_2746_, lean_object* v_____r_2747_){
_start:
{
lean_object* v___x_2748_; 
v___x_2748_ = lean_apply_2(v_toPure_2745_, lean_box(0), v_fst_2746_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__0(lean_object* v_toPure_2749_, lean_object* v_set_2750_, lean_object* v_toBind_2751_, lean_object* v_____x_2752_){
_start:
{
lean_object* v_fst_2753_; lean_object* v_snd_2754_; lean_object* v___f_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
v_fst_2753_ = lean_ctor_get(v_____x_2752_, 0);
lean_inc(v_fst_2753_);
v_snd_2754_ = lean_ctor_get(v_____x_2752_, 1);
lean_inc(v_snd_2754_);
lean_dec_ref(v_____x_2752_);
v___f_2755_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2755_, 0, v_toPure_2749_);
lean_closure_set(v___f_2755_, 1, v_fst_2753_);
v___x_2756_ = lean_apply_1(v_set_2750_, v_snd_2754_);
v___x_2757_ = lean_apply_4(v_toBind_2751_, lean_box(0), lean_box(0), v___x_2756_, v___f_2755_);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__2(lean_object* v_self_2758_, lean_object* v_inst_2759_, lean_object* v_toBind_2760_, lean_object* v___f_2761_, lean_object* v_____do__lift_2762_){
_start:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2763_ = lean_apply_1(v_self_2758_, v_____do__lift_2762_);
v___x_2764_ = lean_apply_2(v_inst_2759_, lean_box(0), v___x_2763_);
v___x_2765_ = lean_apply_4(v_toBind_2760_, lean_box(0), lean_box(0), v___x_2764_, v___f_2761_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg(lean_object* v_inst_2766_, lean_object* v_inst_2767_, lean_object* v_inst_2768_, lean_object* v_self_2769_){
_start:
{
lean_object* v_toApplicative_2770_; lean_object* v_toBind_2771_; lean_object* v_set_2772_; lean_object* v_modifyGet_2773_; lean_object* v_toPure_2774_; lean_object* v___f_2775_; lean_object* v___x_2776_; lean_object* v___f_2777_; lean_object* v___f_2778_; lean_object* v___x_2779_; 
v_toApplicative_2770_ = lean_ctor_get(v_inst_2766_, 0);
lean_inc_ref(v_toApplicative_2770_);
v_toBind_2771_ = lean_ctor_get(v_inst_2766_, 1);
lean_inc_n(v_toBind_2771_, 3);
lean_dec_ref(v_inst_2766_);
v_set_2772_ = lean_ctor_get(v_inst_2767_, 1);
lean_inc(v_set_2772_);
v_modifyGet_2773_ = lean_ctor_get(v_inst_2767_, 2);
lean_inc(v_modifyGet_2773_);
lean_dec_ref(v_inst_2767_);
v_toPure_2774_ = lean_ctor_get(v_toApplicative_2770_, 1);
lean_inc(v_toPure_2774_);
lean_dec_ref(v_toApplicative_2770_);
v___f_2775_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_2776_ = lean_apply_2(v_modifyGet_2773_, lean_box(0), v___f_2775_);
v___f_2777_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2777_, 0, v_toPure_2774_);
lean_closure_set(v___f_2777_, 1, v_set_2772_);
lean_closure_set(v___f_2777_, 2, v_toBind_2771_);
v___f_2778_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2778_, 0, v_self_2769_);
lean_closure_set(v___f_2778_, 1, v_inst_2768_);
lean_closure_set(v___f_2778_, 2, v_toBind_2771_);
lean_closure_set(v___f_2778_, 3, v___f_2777_);
v___x_2779_ = lean_apply_4(v_toBind_2771_, lean_box(0), lean_box(0), v___x_2776_, v___f_2778_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun(lean_object* v_n_2780_, lean_object* v_m_2781_, lean_object* v_00_u03b1_2782_, lean_object* v_inst_2783_, lean_object* v_inst_2784_, lean_object* v_inst_2785_, lean_object* v_inst_2786_, lean_object* v_self_2787_){
_start:
{
lean_object* v_toApplicative_2788_; lean_object* v_toBind_2789_; lean_object* v_set_2790_; lean_object* v_modifyGet_2791_; lean_object* v_toPure_2792_; lean_object* v___f_2793_; lean_object* v___x_2794_; lean_object* v___f_2795_; lean_object* v___f_2796_; lean_object* v___x_2797_; 
v_toApplicative_2788_ = lean_ctor_get(v_inst_2783_, 0);
lean_inc_ref(v_toApplicative_2788_);
v_toBind_2789_ = lean_ctor_get(v_inst_2783_, 1);
lean_inc_n(v_toBind_2789_, 3);
lean_dec_ref(v_inst_2783_);
v_set_2790_ = lean_ctor_get(v_inst_2784_, 1);
lean_inc(v_set_2790_);
v_modifyGet_2791_ = lean_ctor_get(v_inst_2784_, 2);
lean_inc(v_modifyGet_2791_);
lean_dec_ref(v_inst_2784_);
v_toPure_2792_ = lean_ctor_get(v_toApplicative_2788_, 1);
lean_inc(v_toPure_2792_);
lean_dec_ref(v_toApplicative_2788_);
v___f_2793_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_2794_ = lean_apply_2(v_modifyGet_2791_, lean_box(0), v___f_2793_);
v___f_2795_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2795_, 0, v_toPure_2792_);
lean_closure_set(v___f_2795_, 1, v_set_2790_);
lean_closure_set(v___f_2795_, 2, v_toBind_2789_);
v___f_2796_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2796_, 0, v_self_2787_);
lean_closure_set(v___f_2796_, 1, v_inst_2785_);
lean_closure_set(v___f_2796_, 2, v_toBind_2789_);
lean_closure_set(v___f_2796_, 3, v___f_2795_);
v___x_2797_ = lean_apply_4(v_toBind_2789_, lean_box(0), lean_box(0), v___x_2794_, v___f_2796_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___boxed(lean_object* v_n_2798_, lean_object* v_m_2799_, lean_object* v_00_u03b1_2800_, lean_object* v_inst_2801_, lean_object* v_inst_2802_, lean_object* v_inst_2803_, lean_object* v_inst_2804_, lean_object* v_self_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Lake_LogT_takeAndRun(v_n_2798_, v_m_2799_, v_00_u03b1_2800_, v_inst_2801_, v_inst_2802_, v_inst_2803_, v_inst_2804_, v_self_2805_);
lean_dec(v_inst_2804_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg___lam__2(lean_object* v_toPure_2807_, lean_object* v___x_2808_, lean_object* v_toBind_2809_, lean_object* v_inst_2810_, lean_object* v___f_2811_, lean_object* v_____x_2812_){
_start:
{
lean_object* v_fst_2813_; lean_object* v_snd_2814_; lean_object* v___f_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; uint8_t v___x_2818_; 
v_fst_2813_ = lean_ctor_get(v_____x_2812_, 0);
lean_inc(v_fst_2813_);
v_snd_2814_ = lean_ctor_get(v_____x_2812_, 1);
lean_inc(v_snd_2814_);
lean_dec_ref(v_____x_2812_);
lean_inc(v_toPure_2807_);
v___f_2815_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2815_, 0, v_toPure_2807_);
lean_closure_set(v___f_2815_, 1, v_fst_2813_);
v___x_2816_ = lean_array_get_size(v_snd_2814_);
v___x_2817_ = lean_box(0);
v___x_2818_ = lean_nat_dec_lt(v___x_2808_, v___x_2816_);
if (v___x_2818_ == 0)
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
lean_dec(v_snd_2814_);
lean_dec(v___f_2811_);
lean_dec_ref(v_inst_2810_);
v___x_2819_ = lean_apply_2(v_toPure_2807_, lean_box(0), v___x_2817_);
v___x_2820_ = lean_apply_4(v_toBind_2809_, lean_box(0), lean_box(0), v___x_2819_, v___f_2815_);
return v___x_2820_;
}
else
{
size_t v___x_2821_; size_t v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
lean_dec(v_toPure_2807_);
v___x_2821_ = ((size_t)0ULL);
v___x_2822_ = lean_usize_of_nat(v___x_2816_);
v___x_2823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2810_, v___f_2811_, v_snd_2814_, v___x_2821_, v___x_2822_, v___x_2817_);
v___x_2824_ = lean_apply_4(v_toBind_2809_, lean_box(0), lean_box(0), v___x_2823_, v___f_2815_);
return v___x_2824_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg___lam__2___boxed(lean_object* v_toPure_2825_, lean_object* v___x_2826_, lean_object* v_toBind_2827_, lean_object* v_inst_2828_, lean_object* v___f_2829_, lean_object* v_____x_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l_Lake_LogT_replayLog___redArg___lam__2(v_toPure_2825_, v___x_2826_, v_toBind_2827_, v_inst_2828_, v___f_2829_, v_____x_2830_);
lean_dec(v___x_2826_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg(lean_object* v_inst_2832_, lean_object* v_logger_2833_, lean_object* v_inst_2834_, lean_object* v_self_2835_){
_start:
{
lean_object* v_toApplicative_2836_; lean_object* v_toBind_2837_; lean_object* v_toPure_2838_; lean_object* v___f_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___f_2844_; lean_object* v___x_2845_; 
v_toApplicative_2836_ = lean_ctor_get(v_inst_2832_, 0);
v_toBind_2837_ = lean_ctor_get(v_inst_2832_, 1);
lean_inc_n(v_toBind_2837_, 2);
v_toPure_2838_ = lean_ctor_get(v_toApplicative_2836_, 1);
lean_inc(v_toPure_2838_);
v___f_2839_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2839_, 0, v_logger_2833_);
v___x_2840_ = lean_unsigned_to_nat(0u);
v___x_2841_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_2842_ = lean_apply_1(v_self_2835_, v___x_2841_);
v___x_2843_ = lean_apply_2(v_inst_2834_, lean_box(0), v___x_2842_);
v___f_2844_ = lean_alloc_closure((void*)(l_Lake_LogT_replayLog___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_2844_, 0, v_toPure_2838_);
lean_closure_set(v___f_2844_, 1, v___x_2840_);
lean_closure_set(v___f_2844_, 2, v_toBind_2837_);
lean_closure_set(v___f_2844_, 3, v_inst_2832_);
lean_closure_set(v___f_2844_, 4, v___f_2839_);
v___x_2845_ = lean_apply_4(v_toBind_2837_, lean_box(0), lean_box(0), v___x_2843_, v___f_2844_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog(lean_object* v_n_2846_, lean_object* v_m_2847_, lean_object* v_00_u03b1_2848_, lean_object* v_inst_2849_, lean_object* v_logger_2850_, lean_object* v_inst_2851_, lean_object* v_self_2852_){
_start:
{
lean_object* v_toApplicative_2853_; lean_object* v_toBind_2854_; lean_object* v_toPure_2855_; lean_object* v___f_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___f_2861_; lean_object* v___x_2862_; 
v_toApplicative_2853_ = lean_ctor_get(v_inst_2849_, 0);
v_toBind_2854_ = lean_ctor_get(v_inst_2849_, 1);
lean_inc_n(v_toBind_2854_, 2);
v_toPure_2855_ = lean_ctor_get(v_toApplicative_2853_, 1);
lean_inc(v_toPure_2855_);
v___f_2856_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2856_, 0, v_logger_2850_);
v___x_2857_ = lean_unsigned_to_nat(0u);
v___x_2858_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_2859_ = lean_apply_1(v_self_2852_, v___x_2858_);
v___x_2860_ = lean_apply_2(v_inst_2851_, lean_box(0), v___x_2859_);
v___f_2861_ = lean_alloc_closure((void*)(l_Lake_LogT_replayLog___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_2861_, 0, v_toPure_2855_);
lean_closure_set(v___f_2861_, 1, v___x_2857_);
lean_closure_set(v___f_2861_, 2, v_toBind_2854_);
lean_closure_set(v___f_2861_, 3, v_inst_2849_);
lean_closure_set(v___f_2861_, 4, v___f_2856_);
v___x_2862_ = lean_apply_4(v_toBind_2854_, lean_box(0), lean_box(0), v___x_2860_, v___f_2861_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogELogTOfMonad___redArg(lean_object* v_inst_2863_){
_start:
{
lean_object* v_toApplicative_2864_; lean_object* v_toPure_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v_toApplicative_2864_ = lean_ctor_get(v_inst_2863_, 0);
lean_inc_ref(v_toApplicative_2864_);
lean_dec_ref(v_inst_2863_);
v_toPure_2865_ = lean_ctor_get(v_toApplicative_2864_, 1);
lean_inc(v_toPure_2865_);
lean_dec_ref(v_toApplicative_2864_);
v___x_2866_ = l_Lake_EStateT_instMonadStateOfOfPure___redArg(v_toPure_2865_);
v___x_2867_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(v___x_2867_, 0, lean_box(0));
lean_closure_set(v___x_2867_, 1, v___x_2866_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogELogTOfMonad(lean_object* v_m_2868_, lean_object* v_inst_2869_){
_start:
{
lean_object* v___x_2870_; 
v___x_2870_ = l_Lake_instMonadLogELogTOfMonad___redArg(v_inst_2869_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__0(lean_object* v_x_2871_){
_start:
{
if (lean_obj_tag(v_x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2881_; 
v_a_2872_ = lean_ctor_get(v_x_2871_, 0);
v_a_2873_ = lean_ctor_get(v_x_2871_, 1);
v_isSharedCheck_2881_ = !lean_is_exclusive(v_x_2871_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2875_ = v_x_2871_;
v_isShared_2876_ = v_isSharedCheck_2881_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_inc(v_a_2872_);
lean_dec(v_x_2871_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2881_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2877_; lean_object* v___x_2879_; 
v___x_2877_ = lean_array_get_size(v_a_2872_);
lean_dec(v_a_2872_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 0, v___x_2877_);
v___x_2879_ = v___x_2875_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2877_);
lean_ctor_set(v_reuseFailAlloc_2880_, 1, v_a_2873_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
else
{
lean_object* v_a_2882_; lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
v_a_2882_ = lean_ctor_get(v_x_2871_, 0);
v_a_2883_ = lean_ctor_get(v_x_2871_, 1);
v_isSharedCheck_2890_ = !lean_is_exclusive(v_x_2871_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2885_ = v_x_2871_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_inc(v_a_2882_);
lean_dec(v_x_2871_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2882_);
lean_ctor_set(v_reuseFailAlloc_2889_, 1, v_a_2883_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__1(lean_object* v_a_2891_, lean_object* v_toPure_2892_, lean_object* v_____do__lift_2893_){
_start:
{
if (lean_obj_tag(v_____do__lift_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2902_; 
v_a_2894_ = lean_ctor_get(v_____do__lift_2893_, 1);
v_isSharedCheck_2902_ = !lean_is_exclusive(v_____do__lift_2893_);
if (v_isSharedCheck_2902_ == 0)
{
lean_object* v_unused_2903_; 
v_unused_2903_ = lean_ctor_get(v_____do__lift_2893_, 0);
lean_dec(v_unused_2903_);
v___x_2896_ = v_____do__lift_2893_;
v_isShared_2897_ = v_isSharedCheck_2902_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v_____do__lift_2893_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2902_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
lean_ctor_set_tag(v___x_2896_, 1);
lean_ctor_set(v___x_2896_, 0, v_a_2891_);
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2891_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
lean_object* v___x_2900_; 
v___x_2900_ = lean_apply_2(v_toPure_2892_, lean_box(0), v___x_2899_);
return v___x_2900_;
}
}
}
else
{
lean_object* v_a_2904_; lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2913_; 
lean_dec(v_a_2891_);
v_a_2904_ = lean_ctor_get(v_____do__lift_2893_, 0);
v_a_2905_ = lean_ctor_get(v_____do__lift_2893_, 1);
v_isSharedCheck_2913_ = !lean_is_exclusive(v_____do__lift_2893_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2907_ = v_____do__lift_2893_;
v_isShared_2908_ = v_isSharedCheck_2913_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_inc(v_a_2904_);
lean_dec(v_____do__lift_2893_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2913_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2904_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v_a_2905_);
v___x_2910_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
lean_object* v___x_2911_; 
v___x_2911_ = lean_apply_2(v_toPure_2892_, lean_box(0), v___x_2910_);
return v___x_2911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__2(lean_object* v_toPure_2914_, lean_object* v___x_2915_, lean_object* v_____do__lift_2916_){
_start:
{
if (lean_obj_tag(v_____do__lift_2916_) == 0)
{
lean_object* v___x_2917_; 
v___x_2917_ = lean_apply_2(v_toPure_2914_, lean_box(0), v_____do__lift_2916_);
return v___x_2917_;
}
else
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2926_; 
v_a_2918_ = lean_ctor_get(v_____do__lift_2916_, 1);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_____do__lift_2916_);
if (v_isSharedCheck_2926_ == 0)
{
lean_object* v_unused_2927_; 
v_unused_2927_ = lean_ctor_get(v_____do__lift_2916_, 0);
lean_dec(v_unused_2927_);
v___x_2920_ = v_____do__lift_2916_;
v_isShared_2921_ = v_isSharedCheck_2926_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v_____do__lift_2916_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2926_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
lean_ctor_set_tag(v___x_2920_, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2915_);
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2915_);
lean_ctor_set(v_reuseFailAlloc_2925_, 1, v_a_2918_);
v___x_2923_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
lean_object* v___x_2924_; 
v___x_2924_ = lean_apply_2(v_toPure_2914_, lean_box(0), v___x_2923_);
return v___x_2924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__3(lean_object* v_toPure_2928_, lean_object* v___x_2929_, lean_object* v_toBind_2930_, lean_object* v_____do__lift_2931_){
_start:
{
if (lean_obj_tag(v_____do__lift_2931_) == 0)
{
lean_object* v_a_2932_; lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2947_; 
v_a_2932_ = lean_ctor_get(v_____do__lift_2931_, 0);
v_a_2933_ = lean_ctor_get(v_____do__lift_2931_, 1);
v_isSharedCheck_2947_ = !lean_is_exclusive(v_____do__lift_2931_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2935_ = v_____do__lift_2931_;
v_isShared_2936_ = v_isSharedCheck_2947_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_inc(v_a_2932_);
lean_dec(v_____do__lift_2931_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2947_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___f_2937_; lean_object* v___x_2938_; lean_object* v___f_2939_; lean_object* v___x_2940_; lean_object* v___x_2942_; 
lean_inc_n(v_toPure_2928_, 2);
v___f_2937_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2937_, 0, v_a_2932_);
lean_closure_set(v___f_2937_, 1, v_toPure_2928_);
v___x_2938_ = lean_box(0);
v___f_2939_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2939_, 0, v_toPure_2928_);
lean_closure_set(v___f_2939_, 1, v___x_2938_);
v___x_2940_ = lean_array_push(v_a_2933_, v___x_2929_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 1, v___x_2940_);
lean_ctor_set(v___x_2935_, 0, v___x_2938_);
v___x_2942_ = v___x_2935_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___x_2938_);
lean_ctor_set(v_reuseFailAlloc_2946_, 1, v___x_2940_);
v___x_2942_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2943_ = lean_apply_2(v_toPure_2928_, lean_box(0), v___x_2942_);
lean_inc(v_toBind_2930_);
v___x_2944_ = lean_apply_4(v_toBind_2930_, lean_box(0), lean_box(0), v___x_2943_, v___f_2939_);
v___x_2945_ = lean_apply_4(v_toBind_2930_, lean_box(0), lean_box(0), v___x_2944_, v___f_2937_);
return v___x_2945_;
}
}
}
else
{
lean_object* v_a_2948_; lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2957_; 
lean_dec(v_toBind_2930_);
lean_dec_ref(v___x_2929_);
v_a_2948_ = lean_ctor_get(v_____do__lift_2931_, 0);
v_a_2949_ = lean_ctor_get(v_____do__lift_2931_, 1);
v_isSharedCheck_2957_ = !lean_is_exclusive(v_____do__lift_2931_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2951_ = v_____do__lift_2931_;
v_isShared_2952_ = v_isSharedCheck_2957_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_inc(v_a_2948_);
lean_dec(v_____do__lift_2931_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2957_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2948_);
lean_ctor_set(v_reuseFailAlloc_2956_, 1, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_object* v___x_2955_; 
v___x_2955_ = lean_apply_2(v_toPure_2928_, lean_box(0), v___x_2954_);
return v___x_2955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__4(lean_object* v_toFunctor_2958_, lean_object* v_toPure_2959_, lean_object* v_toBind_2960_, lean_object* v___f_2961_, lean_object* v_00_u03b1_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v_map_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2978_; 
v_map_2965_ = lean_ctor_get(v_toFunctor_2958_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v_toFunctor_2958_);
if (v_isSharedCheck_2978_ == 0)
{
lean_object* v_unused_2979_; 
v_unused_2979_ = lean_ctor_get(v_toFunctor_2958_, 1);
lean_dec(v_unused_2979_);
v___x_2967_ = v_toFunctor_2958_;
v_isShared_2968_ = v_isSharedCheck_2978_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_map_2965_);
lean_dec(v_toFunctor_2958_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2978_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
uint8_t v___x_2969_; lean_object* v___x_2970_; lean_object* v___f_2971_; lean_object* v___x_2973_; 
v___x_2969_ = 3;
v___x_2970_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2970_, 0, v___y_2963_);
lean_ctor_set_uint8(v___x_2970_, sizeof(void*)*1, v___x_2969_);
lean_inc(v_toBind_2960_);
lean_inc(v_toPure_2959_);
v___f_2971_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__3), 4, 3);
lean_closure_set(v___f_2971_, 0, v_toPure_2959_);
lean_closure_set(v___f_2971_, 1, v___x_2970_);
lean_closure_set(v___f_2971_, 2, v_toBind_2960_);
lean_inc_ref(v___y_2964_);
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 1, v___y_2964_);
lean_ctor_set(v___x_2967_, 0, v___y_2964_);
v___x_2973_ = v___x_2967_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___y_2964_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v___y_2964_);
v___x_2973_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2974_ = lean_apply_2(v_toPure_2959_, lean_box(0), v___x_2973_);
v___x_2975_ = lean_apply_4(v_map_2965_, lean_box(0), lean_box(0), v___f_2961_, v___x_2974_);
v___x_2976_ = lean_apply_4(v_toBind_2960_, lean_box(0), lean_box(0), v___x_2975_, v___f_2971_);
return v___x_2976_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg(lean_object* v_inst_2981_){
_start:
{
lean_object* v_toApplicative_2982_; lean_object* v_toBind_2983_; lean_object* v_toFunctor_2984_; lean_object* v_toPure_2985_; lean_object* v___f_2986_; lean_object* v___f_2987_; 
v_toApplicative_2982_ = lean_ctor_get(v_inst_2981_, 0);
lean_inc_ref(v_toApplicative_2982_);
v_toBind_2983_ = lean_ctor_get(v_inst_2981_, 1);
lean_inc(v_toBind_2983_);
lean_dec_ref(v_inst_2981_);
v_toFunctor_2984_ = lean_ctor_get(v_toApplicative_2982_, 0);
lean_inc_ref(v_toFunctor_2984_);
v_toPure_2985_ = lean_ctor_get(v_toApplicative_2982_, 1);
lean_inc(v_toPure_2985_);
lean_dec_ref(v_toApplicative_2982_);
v___f_2986_ = ((lean_object*)(l_Lake_instMonadErrorELogTOfMonad___redArg___closed__0));
v___f_2987_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__4), 7, 4);
lean_closure_set(v___f_2987_, 0, v_toFunctor_2984_);
lean_closure_set(v___f_2987_, 1, v_toPure_2985_);
lean_closure_set(v___f_2987_, 2, v_toBind_2983_);
lean_closure_set(v___f_2987_, 3, v___f_2986_);
return v___f_2987_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad(lean_object* v_m_2988_, lean_object* v_inst_2989_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l_Lake_instMonadErrorELogTOfMonad___redArg(v_inst_2989_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__1(lean_object* v___y_2991_, lean_object* v___x_2992_, lean_object* v_toPure_2993_, lean_object* v_____do__lift_2994_){
_start:
{
if (lean_obj_tag(v_____do__lift_2994_) == 0)
{
lean_object* v_a_2995_; lean_object* v___x_2996_; 
lean_dec(v_toPure_2993_);
v_a_2995_ = lean_ctor_get(v_____do__lift_2994_, 1);
lean_inc(v_a_2995_);
lean_dec_ref_known(v_____do__lift_2994_, 2);
v___x_2996_ = lean_apply_2(v___y_2991_, v___x_2992_, v_a_2995_);
return v___x_2996_;
}
else
{
lean_object* v_a_2997_; lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3006_; 
lean_dec(v___y_2991_);
v_a_2997_ = lean_ctor_get(v_____do__lift_2994_, 0);
v_a_2998_ = lean_ctor_get(v_____do__lift_2994_, 1);
v_isSharedCheck_3006_ = !lean_is_exclusive(v_____do__lift_2994_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3000_ = v_____do__lift_2994_;
v_isShared_3001_ = v_isSharedCheck_3006_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_inc(v_a_2997_);
lean_dec(v_____do__lift_2994_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3006_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2997_);
lean_ctor_set(v_reuseFailAlloc_3005_, 1, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
lean_object* v___x_3004_; 
v___x_3004_ = lean_apply_2(v_toPure_2993_, lean_box(0), v___x_3003_);
return v___x_3004_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__0(lean_object* v_toPure_3007_, lean_object* v___y_3008_, lean_object* v_toBind_3009_, lean_object* v_____do__lift_3010_){
_start:
{
if (lean_obj_tag(v_____do__lift_3010_) == 0)
{
lean_object* v___x_3011_; 
lean_dec(v_toBind_3009_);
lean_dec(v___y_3008_);
v___x_3011_ = lean_apply_2(v_toPure_3007_, lean_box(0), v_____do__lift_3010_);
return v___x_3011_;
}
else
{
lean_object* v_a_3012_; lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3025_; 
v_a_3012_ = lean_ctor_get(v_____do__lift_3010_, 0);
v_a_3013_ = lean_ctor_get(v_____do__lift_3010_, 1);
v_isSharedCheck_3025_ = !lean_is_exclusive(v_____do__lift_3010_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3015_ = v_____do__lift_3010_;
v_isShared_3016_ = v_isSharedCheck_3025_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_inc(v_a_3012_);
lean_dec(v_____do__lift_3010_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3025_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3017_; lean_object* v___f_3018_; lean_object* v___x_3019_; lean_object* v___x_3021_; 
v___x_3017_ = lean_box(0);
lean_inc(v_toPure_3007_);
v___f_3018_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3018_, 0, v___y_3008_);
lean_closure_set(v___f_3018_, 1, v___x_3017_);
lean_closure_set(v___f_3018_, 2, v_toPure_3007_);
v___x_3019_ = l_Array_shrink___redArg(v_a_3013_, v_a_3012_);
lean_dec(v_a_3012_);
if (v_isShared_3016_ == 0)
{
lean_ctor_set_tag(v___x_3015_, 0);
lean_ctor_set(v___x_3015_, 1, v___x_3019_);
lean_ctor_set(v___x_3015_, 0, v___x_3017_);
v___x_3021_ = v___x_3015_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v___x_3017_);
lean_ctor_set(v_reuseFailAlloc_3024_, 1, v___x_3019_);
v___x_3021_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = lean_apply_2(v_toPure_3007_, lean_box(0), v___x_3021_);
v___x_3023_ = lean_apply_4(v_toBind_3009_, lean_box(0), lean_box(0), v___x_3022_, v___f_3018_);
return v___x_3023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__2(lean_object* v_toPure_3026_, lean_object* v_toBind_3027_, lean_object* v_00_u03b1_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v___f_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
lean_inc(v_toBind_3027_);
v___f_3032_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3032_, 0, v_toPure_3026_);
lean_closure_set(v___f_3032_, 1, v___y_3030_);
lean_closure_set(v___f_3032_, 2, v_toBind_3027_);
v___x_3033_ = lean_apply_1(v___y_3029_, v___y_3031_);
v___x_3034_ = lean_apply_4(v_toBind_3027_, lean_box(0), lean_box(0), v___x_3033_, v___f_3032_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__3(lean_object* v_toPure_3035_, lean_object* v_____do__lift_3036_){
_start:
{
if (lean_obj_tag(v_____do__lift_3036_) == 0)
{
lean_object* v_a_3037_; lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3046_; 
v_a_3037_ = lean_ctor_get(v_____do__lift_3036_, 0);
v_a_3038_ = lean_ctor_get(v_____do__lift_3036_, 1);
v_isSharedCheck_3046_ = !lean_is_exclusive(v_____do__lift_3036_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3040_ = v_____do__lift_3036_;
v_isShared_3041_ = v_isSharedCheck_3046_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_inc(v_a_3037_);
lean_dec(v_____do__lift_3036_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3046_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
lean_ctor_set_tag(v___x_3040_, 1);
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_a_3037_);
lean_ctor_set(v_reuseFailAlloc_3045_, 1, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
lean_object* v___x_3044_; 
v___x_3044_ = lean_apply_2(v_toPure_3035_, lean_box(0), v___x_3043_);
return v___x_3044_;
}
}
}
else
{
lean_object* v_a_3047_; lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3056_; 
v_a_3047_ = lean_ctor_get(v_____do__lift_3036_, 0);
v_a_3048_ = lean_ctor_get(v_____do__lift_3036_, 1);
v_isSharedCheck_3056_ = !lean_is_exclusive(v_____do__lift_3036_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3050_ = v_____do__lift_3036_;
v_isShared_3051_ = v_isSharedCheck_3056_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_inc(v_a_3047_);
lean_dec(v_____do__lift_3036_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3056_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3047_);
lean_ctor_set(v_reuseFailAlloc_3055_, 1, v_a_3048_);
v___x_3053_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
lean_object* v___x_3054_; 
v___x_3054_ = lean_apply_2(v_toPure_3035_, lean_box(0), v___x_3053_);
return v___x_3054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__4(lean_object* v_toFunctor_3057_, lean_object* v_toPure_3058_, lean_object* v___f_3059_, lean_object* v_toBind_3060_, lean_object* v___f_3061_, lean_object* v_00_u03b1_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v_map_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3074_; 
v_map_3064_ = lean_ctor_get(v_toFunctor_3057_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v_toFunctor_3057_);
if (v_isSharedCheck_3074_ == 0)
{
lean_object* v_unused_3075_; 
v_unused_3075_ = lean_ctor_get(v_toFunctor_3057_, 1);
lean_dec(v_unused_3075_);
v___x_3066_ = v_toFunctor_3057_;
v_isShared_3067_ = v_isSharedCheck_3074_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_map_3064_);
lean_dec(v_toFunctor_3057_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3074_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
lean_inc_ref(v___y_3063_);
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 1, v___y_3063_);
lean_ctor_set(v___x_3066_, 0, v___y_3063_);
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v___y_3063_);
lean_ctor_set(v_reuseFailAlloc_3073_, 1, v___y_3063_);
v___x_3069_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3070_ = lean_apply_2(v_toPure_3058_, lean_box(0), v___x_3069_);
v___x_3071_ = lean_apply_4(v_map_3064_, lean_box(0), lean_box(0), v___f_3059_, v___x_3070_);
v___x_3072_ = lean_apply_4(v_toBind_3060_, lean_box(0), lean_box(0), v___x_3071_, v___f_3061_);
return v___x_3072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg(lean_object* v_inst_3076_){
_start:
{
lean_object* v_toApplicative_3077_; lean_object* v_toBind_3078_; lean_object* v_toFunctor_3079_; lean_object* v_toPure_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3098_; 
v_toApplicative_3077_ = lean_ctor_get(v_inst_3076_, 0);
lean_inc_ref(v_toApplicative_3077_);
v_toBind_3078_ = lean_ctor_get(v_inst_3076_, 1);
lean_inc(v_toBind_3078_);
lean_dec_ref(v_inst_3076_);
v_toFunctor_3079_ = lean_ctor_get(v_toApplicative_3077_, 0);
v_toPure_3080_ = lean_ctor_get(v_toApplicative_3077_, 1);
v_isSharedCheck_3098_ = !lean_is_exclusive(v_toApplicative_3077_);
if (v_isSharedCheck_3098_ == 0)
{
lean_object* v_unused_3099_; lean_object* v_unused_3100_; lean_object* v_unused_3101_; 
v_unused_3099_ = lean_ctor_get(v_toApplicative_3077_, 4);
lean_dec(v_unused_3099_);
v_unused_3100_ = lean_ctor_get(v_toApplicative_3077_, 3);
lean_dec(v_unused_3100_);
v_unused_3101_ = lean_ctor_get(v_toApplicative_3077_, 2);
lean_dec(v_unused_3101_);
v___x_3082_ = v_toApplicative_3077_;
v_isShared_3083_ = v_isSharedCheck_3098_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_toPure_3080_);
lean_inc(v_toFunctor_3079_);
lean_dec(v_toApplicative_3077_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3098_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___f_3084_; lean_object* v___f_3085_; lean_object* v___f_3086_; lean_object* v___f_3087_; lean_object* v___f_3088_; lean_object* v___f_3089_; lean_object* v___f_3090_; lean_object* v___f_3091_; lean_object* v___x_3092_; lean_object* v___f_3093_; lean_object* v___x_3095_; 
v___f_3084_ = ((lean_object*)(l_Lake_instMonadErrorELogTOfMonad___redArg___closed__0));
lean_inc_n(v_toBind_3078_, 4);
lean_inc_n(v_toPure_3080_, 7);
v___f_3085_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__2), 6, 2);
lean_closure_set(v___f_3085_, 0, v_toPure_3080_);
lean_closure_set(v___f_3085_, 1, v_toBind_3078_);
v___f_3086_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3086_, 0, v_toPure_3080_);
lean_inc_ref_n(v_toFunctor_3079_, 2);
v___f_3087_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__4), 7, 5);
lean_closure_set(v___f_3087_, 0, v_toFunctor_3079_);
lean_closure_set(v___f_3087_, 1, v_toPure_3080_);
lean_closure_set(v___f_3087_, 2, v___f_3084_);
lean_closure_set(v___f_3087_, 3, v_toBind_3078_);
lean_closure_set(v___f_3087_, 4, v___f_3086_);
v___f_3088_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_3088_, 0, v_toPure_3080_);
lean_closure_set(v___f_3088_, 1, v_toBind_3078_);
v___f_3089_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_3089_, 0, v_toPure_3080_);
lean_closure_set(v___f_3089_, 1, v_toBind_3078_);
v___f_3090_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_3090_, 0, v_toPure_3080_);
lean_closure_set(v___f_3090_, 1, v___f_3088_);
v___f_3091_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_3091_, 0, v_toFunctor_3079_);
lean_closure_set(v___f_3091_, 1, v_toPure_3080_);
lean_closure_set(v___f_3091_, 2, v_toBind_3078_);
v___x_3092_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_3079_);
v___f_3093_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3093_, 0, v_toPure_3080_);
if (v_isShared_3083_ == 0)
{
lean_ctor_set(v___x_3082_, 4, v___f_3089_);
lean_ctor_set(v___x_3082_, 3, v___f_3090_);
lean_ctor_set(v___x_3082_, 2, v___f_3091_);
lean_ctor_set(v___x_3082_, 1, v___f_3093_);
lean_ctor_set(v___x_3082_, 0, v___x_3092_);
v___x_3095_ = v___x_3082_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3092_);
lean_ctor_set(v_reuseFailAlloc_3097_, 1, v___f_3093_);
lean_ctor_set(v_reuseFailAlloc_3097_, 2, v___f_3091_);
lean_ctor_set(v_reuseFailAlloc_3097_, 3, v___f_3090_);
lean_ctor_set(v_reuseFailAlloc_3097_, 4, v___f_3089_);
v___x_3095_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
lean_object* v___x_3096_; 
v___x_3096_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3095_);
lean_ctor_set(v___x_3096_, 1, v___f_3087_);
lean_ctor_set(v___x_3096_, 2, v___f_3085_);
return v___x_3096_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad(lean_object* v_m_3102_, lean_object* v_inst_3103_){
_start:
{
lean_object* v___x_3104_; 
v___x_3104_ = l_Lake_instAlternativeELogTOfMonad___redArg(v_inst_3103_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run___redArg(lean_object* v_self_3105_, lean_object* v_log_3106_){
_start:
{
lean_object* v___x_3107_; 
v___x_3107_ = lean_apply_1(v_self_3105_, v_log_3106_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run(lean_object* v_m_3108_, lean_object* v_00_u03b1_3109_, lean_object* v_self_3110_, lean_object* v_log_3111_){
_start:
{
lean_object* v___x_3112_; 
v___x_3112_ = lean_apply_1(v_self_3110_, v_log_3111_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x27___redArg(lean_object* v_inst_3114_, lean_object* v_self_3115_, lean_object* v_log_3116_){
_start:
{
lean_object* v_map_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v_map_3117_ = lean_ctor_get(v_inst_3114_, 0);
lean_inc(v_map_3117_);
lean_dec_ref(v_inst_3114_);
v___x_3118_ = ((lean_object*)(l_Lake_ELogT_run_x27___redArg___closed__0));
v___x_3119_ = lean_apply_1(v_self_3115_, v_log_3116_);
v___x_3120_ = lean_apply_4(v_map_3117_, lean_box(0), lean_box(0), v___x_3118_, v___x_3119_);
return v___x_3120_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x27(lean_object* v_m_3121_, lean_object* v_00_u03b1_3122_, lean_object* v_inst_3123_, lean_object* v_self_3124_, lean_object* v_log_3125_){
_start:
{
lean_object* v_map_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v_map_3126_ = lean_ctor_get(v_inst_3123_, 0);
lean_inc(v_map_3126_);
lean_dec_ref(v_inst_3123_);
v___x_3127_ = ((lean_object*)(l_Lake_ELogT_run_x27___redArg___closed__0));
v___x_3128_ = lean_apply_1(v_self_3124_, v_log_3125_);
v___x_3129_ = lean_apply_4(v_map_3126_, lean_box(0), lean_box(0), v___x_3127_, v___x_3128_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT___redArg(lean_object* v_inst_3131_, lean_object* v_self_3132_, lean_object* v_a_3133_){
_start:
{
lean_object* v_map_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v_map_3134_ = lean_ctor_get(v_inst_3131_, 0);
lean_inc(v_map_3134_);
lean_dec_ref(v_inst_3131_);
v___x_3135_ = ((lean_object*)(l_Lake_ELogT_toLogT___redArg___closed__0));
v___x_3136_ = lean_apply_1(v_self_3132_, v_a_3133_);
v___x_3137_ = lean_apply_4(v_map_3134_, lean_box(0), lean_box(0), v___x_3135_, v___x_3136_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT(lean_object* v_m_3138_, lean_object* v_00_u03b1_3139_, lean_object* v_inst_3140_, lean_object* v_self_3141_, lean_object* v_a_3142_){
_start:
{
lean_object* v_map_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
v_map_3143_ = lean_ctor_get(v_inst_3140_, 0);
lean_inc(v_map_3143_);
lean_dec_ref(v_inst_3140_);
v___x_3144_ = ((lean_object*)(l_Lake_ELogT_toLogT___redArg___closed__0));
v___x_3145_ = lean_apply_1(v_self_3141_, v_a_3142_);
v___x_3146_ = lean_apply_4(v_map_3143_, lean_box(0), lean_box(0), v___x_3144_, v___x_3145_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT_x3f___redArg(lean_object* v_inst_3148_, lean_object* v_self_3149_, lean_object* v_a_3150_){
_start:
{
lean_object* v_map_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v_map_3151_ = lean_ctor_get(v_inst_3148_, 0);
lean_inc(v_map_3151_);
lean_dec_ref(v_inst_3148_);
v___x_3152_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3153_ = lean_apply_1(v_self_3149_, v_a_3150_);
v___x_3154_ = lean_apply_4(v_map_3151_, lean_box(0), lean_box(0), v___x_3152_, v___x_3153_);
return v___x_3154_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT_x3f(lean_object* v_m_3155_, lean_object* v_00_u03b1_3156_, lean_object* v_inst_3157_, lean_object* v_self_3158_, lean_object* v_a_3159_){
_start:
{
lean_object* v_map_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v_map_3160_ = lean_ctor_get(v_inst_3157_, 0);
lean_inc(v_map_3160_);
lean_dec_ref(v_inst_3157_);
v___x_3161_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3162_ = lean_apply_1(v_self_3158_, v_a_3159_);
v___x_3163_ = lean_apply_4(v_map_3160_, lean_box(0), lean_box(0), v___x_3161_, v___x_3162_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f___redArg(lean_object* v_inst_3164_, lean_object* v_self_3165_, lean_object* v_log_3166_){
_start:
{
lean_object* v_map_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v_map_3167_ = lean_ctor_get(v_inst_3164_, 0);
lean_inc(v_map_3167_);
lean_dec_ref(v_inst_3164_);
v___x_3168_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3169_ = lean_apply_1(v_self_3165_, v_log_3166_);
v___x_3170_ = lean_apply_4(v_map_3167_, lean_box(0), lean_box(0), v___x_3168_, v___x_3169_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f(lean_object* v_m_3171_, lean_object* v_00_u03b1_3172_, lean_object* v_inst_3173_, lean_object* v_self_3174_, lean_object* v_log_3175_){
_start:
{
lean_object* v_map_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v_map_3176_ = lean_ctor_get(v_inst_3173_, 0);
lean_inc(v_map_3176_);
lean_dec_ref(v_inst_3173_);
v___x_3177_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3178_ = lean_apply_1(v_self_3174_, v_log_3175_);
v___x_3179_ = lean_apply_4(v_map_3176_, lean_box(0), lean_box(0), v___x_3177_, v___x_3178_);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f_x27___redArg(lean_object* v_inst_3181_, lean_object* v_self_3182_, lean_object* v_log_3183_){
_start:
{
lean_object* v_map_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v_map_3184_ = lean_ctor_get(v_inst_3181_, 0);
lean_inc(v_map_3184_);
lean_dec_ref(v_inst_3181_);
v___x_3185_ = ((lean_object*)(l_Lake_ELogT_run_x3f_x27___redArg___closed__0));
v___x_3186_ = lean_apply_1(v_self_3182_, v_log_3183_);
v___x_3187_ = lean_apply_4(v_map_3184_, lean_box(0), lean_box(0), v___x_3185_, v___x_3186_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f_x27(lean_object* v_m_3188_, lean_object* v_00_u03b1_3189_, lean_object* v_inst_3190_, lean_object* v_self_3191_, lean_object* v_log_3192_){
_start:
{
lean_object* v_map_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v_map_3193_ = lean_ctor_get(v_inst_3190_, 0);
lean_inc(v_map_3193_);
lean_dec_ref(v_inst_3190_);
v___x_3194_ = ((lean_object*)(l_Lake_ELogT_run_x3f_x27___redArg___closed__0));
v___x_3195_ = lean_apply_1(v_self_3191_, v_log_3192_);
v___x_3196_ = lean_apply_4(v_map_3193_, lean_box(0), lean_box(0), v___x_3194_, v___x_3195_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg___lam__0(lean_object* v_f_3197_, lean_object* v_____x_3198_){
_start:
{
lean_object* v_fst_3199_; lean_object* v_snd_3200_; lean_object* v___x_3201_; 
v_fst_3199_ = lean_ctor_get(v_____x_3198_, 0);
lean_inc(v_fst_3199_);
v_snd_3200_ = lean_ctor_get(v_____x_3198_, 1);
lean_inc(v_snd_3200_);
lean_dec_ref(v_____x_3198_);
v___x_3201_ = lean_apply_2(v_f_3197_, v_fst_3199_, v_snd_3200_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg___lam__1(lean_object* v_toPure_3202_, lean_object* v_toBind_3203_, lean_object* v___f_3204_, lean_object* v_____do__lift_3205_){
_start:
{
if (lean_obj_tag(v_____do__lift_3205_) == 0)
{
lean_object* v_a_3206_; lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3215_; 
lean_dec(v___f_3204_);
lean_dec(v_toBind_3203_);
v_a_3206_ = lean_ctor_get(v_____do__lift_3205_, 0);
v_a_3207_ = lean_ctor_get(v_____do__lift_3205_, 1);
v_isSharedCheck_3215_ = !lean_is_exclusive(v_____do__lift_3205_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3209_ = v_____do__lift_3205_;
v_isShared_3210_ = v_isSharedCheck_3215_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_inc(v_a_3206_);
lean_dec(v_____do__lift_3205_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3215_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3212_; 
if (v_isShared_3210_ == 0)
{
v___x_3212_ = v___x_3209_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_3206_);
lean_ctor_set(v_reuseFailAlloc_3214_, 1, v_a_3207_);
v___x_3212_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
lean_object* v___x_3213_; 
v___x_3213_ = lean_apply_2(v_toPure_3202_, lean_box(0), v___x_3212_);
return v___x_3213_;
}
}
}
else
{
lean_object* v_a_3216_; lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3229_; 
v_a_3216_ = lean_ctor_get(v_____do__lift_3205_, 0);
v_a_3217_ = lean_ctor_get(v_____do__lift_3205_, 1);
v_isSharedCheck_3229_ = !lean_is_exclusive(v_____do__lift_3205_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3219_ = v_____do__lift_3205_;
v_isShared_3220_ = v_isSharedCheck_3229_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_inc(v_a_3216_);
lean_dec(v_____do__lift_3205_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3229_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3225_; 
v___x_3221_ = lean_array_get_size(v_a_3217_);
lean_inc(v_a_3216_);
v___x_3222_ = l_Array_extract___redArg(v_a_3217_, v_a_3216_, v___x_3221_);
v___x_3223_ = l_Array_shrink___redArg(v_a_3217_, v_a_3216_);
lean_dec(v_a_3216_);
if (v_isShared_3220_ == 0)
{
lean_ctor_set_tag(v___x_3219_, 0);
lean_ctor_set(v___x_3219_, 1, v___x_3223_);
lean_ctor_set(v___x_3219_, 0, v___x_3222_);
v___x_3225_ = v___x_3219_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3222_);
lean_ctor_set(v_reuseFailAlloc_3228_, 1, v___x_3223_);
v___x_3225_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = lean_apply_2(v_toPure_3202_, lean_box(0), v___x_3225_);
v___x_3227_ = lean_apply_4(v_toBind_3203_, lean_box(0), lean_box(0), v___x_3226_, v___f_3204_);
return v___x_3227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg(lean_object* v_inst_3230_, lean_object* v_f_3231_, lean_object* v_self_3232_, lean_object* v_a_3233_){
_start:
{
lean_object* v_toApplicative_3234_; lean_object* v_toBind_3235_; lean_object* v_toPure_3236_; lean_object* v___f_3237_; lean_object* v___x_3238_; lean_object* v___f_3239_; lean_object* v___x_3240_; 
v_toApplicative_3234_ = lean_ctor_get(v_inst_3230_, 0);
lean_inc_ref(v_toApplicative_3234_);
v_toBind_3235_ = lean_ctor_get(v_inst_3230_, 1);
lean_inc_n(v_toBind_3235_, 2);
lean_dec_ref(v_inst_3230_);
v_toPure_3236_ = lean_ctor_get(v_toApplicative_3234_, 1);
lean_inc(v_toPure_3236_);
lean_dec_ref(v_toApplicative_3234_);
v___f_3237_ = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3237_, 0, v_f_3231_);
v___x_3238_ = lean_apply_1(v_self_3232_, v_a_3233_);
v___f_3239_ = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3239_, 0, v_toPure_3236_);
lean_closure_set(v___f_3239_, 1, v_toBind_3235_);
lean_closure_set(v___f_3239_, 2, v___f_3237_);
v___x_3240_ = lean_apply_4(v_toBind_3235_, lean_box(0), lean_box(0), v___x_3238_, v___f_3239_);
return v___x_3240_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog(lean_object* v_m_3241_, lean_object* v_00_u03b1_3242_, lean_object* v_inst_3243_, lean_object* v_f_3244_, lean_object* v_self_3245_, lean_object* v_a_3246_){
_start:
{
lean_object* v_toApplicative_3247_; lean_object* v_toBind_3248_; lean_object* v_toPure_3249_; lean_object* v___f_3250_; lean_object* v___x_3251_; lean_object* v___f_3252_; lean_object* v___x_3253_; 
v_toApplicative_3247_ = lean_ctor_get(v_inst_3243_, 0);
lean_inc_ref(v_toApplicative_3247_);
v_toBind_3248_ = lean_ctor_get(v_inst_3243_, 1);
lean_inc_n(v_toBind_3248_, 2);
lean_dec_ref(v_inst_3243_);
v_toPure_3249_ = lean_ctor_get(v_toApplicative_3247_, 1);
lean_inc(v_toPure_3249_);
lean_dec_ref(v_toApplicative_3247_);
v___f_3250_ = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3250_, 0, v_f_3244_);
v___x_3251_ = lean_apply_1(v_self_3245_, v_a_3246_);
v___f_3252_ = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3252_, 0, v_toPure_3249_);
lean_closure_set(v___f_3252_, 1, v_toBind_3248_);
lean_closure_set(v___f_3252_, 2, v___f_3250_);
v___x_3253_ = lean_apply_4(v_toBind_3248_, lean_box(0), lean_box(0), v___x_3251_, v___f_3252_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__1(lean_object* v_toPure_3254_, lean_object* v_a_3255_, lean_object* v_____r_3256_){
_start:
{
lean_object* v___x_3257_; 
v___x_3257_ = lean_apply_2(v_toPure_3254_, lean_box(0), v_a_3255_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__0(lean_object* v_inst_3258_, lean_object* v_a_3259_, lean_object* v_____r_3260_){
_start:
{
lean_object* v_throw_3261_; lean_object* v___x_3262_; 
v_throw_3261_ = lean_ctor_get(v_inst_3258_, 0);
lean_inc(v_throw_3261_);
lean_dec_ref(v_inst_3258_);
v___x_3262_ = lean_apply_2(v_throw_3261_, lean_box(0), v_a_3259_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__2(lean_object* v_toPure_3263_, lean_object* v_set_3264_, lean_object* v_toBind_3265_, lean_object* v_inst_3266_, lean_object* v_____do__lift_3267_){
_start:
{
if (lean_obj_tag(v_____do__lift_3267_) == 0)
{
lean_object* v_a_3268_; lean_object* v_a_3269_; lean_object* v___f_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
lean_dec_ref(v_inst_3266_);
v_a_3268_ = lean_ctor_get(v_____do__lift_3267_, 0);
lean_inc(v_a_3268_);
v_a_3269_ = lean_ctor_get(v_____do__lift_3267_, 1);
lean_inc(v_a_3269_);
lean_dec_ref_known(v_____do__lift_3267_, 2);
v___f_3270_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3270_, 0, v_toPure_3263_);
lean_closure_set(v___f_3270_, 1, v_a_3268_);
v___x_3271_ = lean_apply_1(v_set_3264_, v_a_3269_);
v___x_3272_ = lean_apply_4(v_toBind_3265_, lean_box(0), lean_box(0), v___x_3271_, v___f_3270_);
return v___x_3272_;
}
else
{
lean_object* v_a_3273_; lean_object* v_a_3274_; lean_object* v___f_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
lean_dec(v_toPure_3263_);
v_a_3273_ = lean_ctor_get(v_____do__lift_3267_, 0);
lean_inc(v_a_3273_);
v_a_3274_ = lean_ctor_get(v_____do__lift_3267_, 1);
lean_inc(v_a_3274_);
lean_dec_ref_known(v_____do__lift_3267_, 2);
v___f_3275_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3275_, 0, v_inst_3266_);
lean_closure_set(v___f_3275_, 1, v_a_3273_);
v___x_3276_ = lean_apply_1(v_set_3264_, v_a_3274_);
v___x_3277_ = lean_apply_4(v_toBind_3265_, lean_box(0), lean_box(0), v___x_3276_, v___f_3275_);
return v___x_3277_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__3(lean_object* v_self_3278_, lean_object* v_inst_3279_, lean_object* v_toBind_3280_, lean_object* v___f_3281_, lean_object* v_____do__lift_3282_){
_start:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3283_ = lean_apply_1(v_self_3278_, v_____do__lift_3282_);
v___x_3284_ = lean_apply_2(v_inst_3279_, lean_box(0), v___x_3283_);
v___x_3285_ = lean_apply_4(v_toBind_3280_, lean_box(0), lean_box(0), v___x_3284_, v___f_3281_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg(lean_object* v_inst_3286_, lean_object* v_inst_3287_, lean_object* v_inst_3288_, lean_object* v_inst_3289_, lean_object* v_self_3290_){
_start:
{
lean_object* v_toApplicative_3291_; lean_object* v_toBind_3292_; lean_object* v_set_3293_; lean_object* v_modifyGet_3294_; lean_object* v_toPure_3295_; lean_object* v___f_3296_; lean_object* v___x_3297_; lean_object* v___f_3298_; lean_object* v___f_3299_; lean_object* v___x_3300_; 
v_toApplicative_3291_ = lean_ctor_get(v_inst_3286_, 0);
lean_inc_ref(v_toApplicative_3291_);
v_toBind_3292_ = lean_ctor_get(v_inst_3286_, 1);
lean_inc_n(v_toBind_3292_, 3);
lean_dec_ref(v_inst_3286_);
v_set_3293_ = lean_ctor_get(v_inst_3287_, 1);
lean_inc(v_set_3293_);
v_modifyGet_3294_ = lean_ctor_get(v_inst_3287_, 2);
lean_inc(v_modifyGet_3294_);
lean_dec_ref(v_inst_3287_);
v_toPure_3295_ = lean_ctor_get(v_toApplicative_3291_, 1);
lean_inc(v_toPure_3295_);
lean_dec_ref(v_toApplicative_3291_);
v___f_3296_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_3297_ = lean_apply_2(v_modifyGet_3294_, lean_box(0), v___f_3296_);
v___f_3298_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3298_, 0, v_toPure_3295_);
lean_closure_set(v___f_3298_, 1, v_set_3293_);
lean_closure_set(v___f_3298_, 2, v_toBind_3292_);
lean_closure_set(v___f_3298_, 3, v_inst_3288_);
v___f_3299_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3299_, 0, v_self_3290_);
lean_closure_set(v___f_3299_, 1, v_inst_3289_);
lean_closure_set(v___f_3299_, 2, v_toBind_3292_);
lean_closure_set(v___f_3299_, 3, v___f_3298_);
v___x_3300_ = lean_apply_4(v_toBind_3292_, lean_box(0), lean_box(0), v___x_3297_, v___f_3299_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun(lean_object* v_n_3301_, lean_object* v_m_3302_, lean_object* v_00_u03b1_3303_, lean_object* v_inst_3304_, lean_object* v_inst_3305_, lean_object* v_inst_3306_, lean_object* v_inst_3307_, lean_object* v_self_3308_){
_start:
{
lean_object* v_toApplicative_3309_; lean_object* v_toBind_3310_; lean_object* v_set_3311_; lean_object* v_modifyGet_3312_; lean_object* v_toPure_3313_; lean_object* v___f_3314_; lean_object* v___x_3315_; lean_object* v___f_3316_; lean_object* v___f_3317_; lean_object* v___x_3318_; 
v_toApplicative_3309_ = lean_ctor_get(v_inst_3304_, 0);
lean_inc_ref(v_toApplicative_3309_);
v_toBind_3310_ = lean_ctor_get(v_inst_3304_, 1);
lean_inc_n(v_toBind_3310_, 3);
lean_dec_ref(v_inst_3304_);
v_set_3311_ = lean_ctor_get(v_inst_3305_, 1);
lean_inc(v_set_3311_);
v_modifyGet_3312_ = lean_ctor_get(v_inst_3305_, 2);
lean_inc(v_modifyGet_3312_);
lean_dec_ref(v_inst_3305_);
v_toPure_3313_ = lean_ctor_get(v_toApplicative_3309_, 1);
lean_inc(v_toPure_3313_);
lean_dec_ref(v_toApplicative_3309_);
v___f_3314_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_3315_ = lean_apply_2(v_modifyGet_3312_, lean_box(0), v___f_3314_);
v___f_3316_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3316_, 0, v_toPure_3313_);
lean_closure_set(v___f_3316_, 1, v_set_3311_);
lean_closure_set(v___f_3316_, 2, v_toBind_3310_);
lean_closure_set(v___f_3316_, 3, v_inst_3306_);
v___f_3317_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3317_, 0, v_self_3308_);
lean_closure_set(v___f_3317_, 1, v_inst_3307_);
lean_closure_set(v___f_3317_, 2, v_toBind_3310_);
lean_closure_set(v___f_3317_, 3, v___f_3316_);
v___x_3318_ = lean_apply_4(v_toBind_3310_, lean_box(0), lean_box(0), v___x_3315_, v___f_3317_);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__2(lean_object* v_toPure_3319_, lean_object* v_x_3320_){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3321_ = lean_box(0);
v___x_3322_ = lean_apply_2(v_toPure_3319_, lean_box(0), v___x_3321_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__0(lean_object* v_a_3323_, lean_object* v_toPure_3324_, lean_object* v_x_3325_){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3326_, 0, v_a_3323_);
v___x_3327_ = lean_apply_2(v_toPure_3324_, lean_box(0), v___x_3326_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__1(lean_object* v_toPure_3328_, lean_object* v___x_3329_, lean_object* v_toSeqRight_3330_, lean_object* v_inst_3331_, lean_object* v___f_3332_, lean_object* v___f_3333_, lean_object* v___f_3334_, lean_object* v_____do__lift_3335_){
_start:
{
if (lean_obj_tag(v_____do__lift_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v_a_3337_; lean_object* v___f_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; uint8_t v___x_3341_; 
lean_dec(v___f_3334_);
lean_dec(v___f_3333_);
v_a_3336_ = lean_ctor_get(v_____do__lift_3335_, 0);
lean_inc(v_a_3336_);
v_a_3337_ = lean_ctor_get(v_____do__lift_3335_, 1);
lean_inc(v_a_3337_);
lean_dec_ref_known(v_____do__lift_3335_, 2);
lean_inc(v_toPure_3328_);
v___f_3338_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3338_, 0, v_a_3336_);
lean_closure_set(v___f_3338_, 1, v_toPure_3328_);
v___x_3339_ = lean_array_get_size(v_a_3337_);
v___x_3340_ = lean_box(0);
v___x_3341_ = lean_nat_dec_lt(v___x_3329_, v___x_3339_);
if (v___x_3341_ == 0)
{
lean_object* v___x_3342_; lean_object* v___x_3343_; 
lean_dec(v_a_3337_);
lean_dec(v___f_3332_);
lean_dec_ref(v_inst_3331_);
v___x_3342_ = lean_apply_2(v_toPure_3328_, lean_box(0), v___x_3340_);
v___x_3343_ = lean_apply_4(v_toSeqRight_3330_, lean_box(0), lean_box(0), v___x_3342_, v___f_3338_);
return v___x_3343_;
}
else
{
size_t v___x_3344_; size_t v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
lean_dec(v_toPure_3328_);
v___x_3344_ = ((size_t)0ULL);
v___x_3345_ = lean_usize_of_nat(v___x_3339_);
v___x_3346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3331_, v___f_3332_, v_a_3337_, v___x_3344_, v___x_3345_, v___x_3340_);
v___x_3347_ = lean_apply_4(v_toSeqRight_3330_, lean_box(0), lean_box(0), v___x_3346_, v___f_3338_);
return v___x_3347_;
}
}
else
{
lean_object* v_a_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; uint8_t v___x_3351_; 
lean_dec(v___f_3332_);
v_a_3348_ = lean_ctor_get(v_____do__lift_3335_, 1);
lean_inc(v_a_3348_);
lean_dec_ref_known(v_____do__lift_3335_, 2);
v___x_3349_ = lean_array_get_size(v_a_3348_);
v___x_3350_ = lean_box(0);
v___x_3351_ = lean_nat_dec_lt(v___x_3329_, v___x_3349_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3352_; lean_object* v___x_3353_; 
lean_dec(v_a_3348_);
lean_dec(v___f_3334_);
lean_dec_ref(v_inst_3331_);
v___x_3352_ = lean_apply_2(v_toPure_3328_, lean_box(0), v___x_3350_);
v___x_3353_ = lean_apply_4(v_toSeqRight_3330_, lean_box(0), lean_box(0), v___x_3352_, v___f_3333_);
return v___x_3353_;
}
else
{
size_t v___x_3354_; size_t v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
lean_dec(v_toPure_3328_);
v___x_3354_ = ((size_t)0ULL);
v___x_3355_ = lean_usize_of_nat(v___x_3349_);
v___x_3356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3331_, v___f_3334_, v_a_3348_, v___x_3354_, v___x_3355_, v___x_3350_);
v___x_3357_ = lean_apply_4(v_toSeqRight_3330_, lean_box(0), lean_box(0), v___x_3356_, v___f_3333_);
return v___x_3357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed(lean_object* v_toPure_3358_, lean_object* v___x_3359_, lean_object* v_toSeqRight_3360_, lean_object* v_inst_3361_, lean_object* v___f_3362_, lean_object* v___f_3363_, lean_object* v___f_3364_, lean_object* v_____do__lift_3365_){
_start:
{
lean_object* v_res_3366_; 
v_res_3366_ = l_Lake_ELogT_replayLog_x3f___redArg___lam__1(v_toPure_3358_, v___x_3359_, v_toSeqRight_3360_, v_inst_3361_, v___f_3362_, v___f_3363_, v___f_3364_, v_____do__lift_3365_);
lean_dec(v___x_3359_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg(lean_object* v_inst_3367_, lean_object* v_logger_3368_, lean_object* v_inst_3369_, lean_object* v_self_3370_){
_start:
{
lean_object* v_toApplicative_3371_; lean_object* v_toBind_3372_; lean_object* v_toPure_3373_; lean_object* v_toSeqRight_3374_; lean_object* v___f_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___f_3380_; lean_object* v___f_3381_; lean_object* v___x_3382_; 
v_toApplicative_3371_ = lean_ctor_get(v_inst_3367_, 0);
v_toBind_3372_ = lean_ctor_get(v_inst_3367_, 1);
lean_inc(v_toBind_3372_);
v_toPure_3373_ = lean_ctor_get(v_toApplicative_3371_, 1);
lean_inc_n(v_toPure_3373_, 2);
v_toSeqRight_3374_ = lean_ctor_get(v_toApplicative_3371_, 4);
lean_inc(v_toSeqRight_3374_);
v___f_3375_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3375_, 0, v_logger_3368_);
v___x_3376_ = lean_unsigned_to_nat(0u);
v___x_3377_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3378_ = lean_apply_1(v_self_3370_, v___x_3377_);
v___x_3379_ = lean_apply_2(v_inst_3369_, lean_box(0), v___x_3378_);
v___f_3380_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3380_, 0, v_toPure_3373_);
lean_inc_ref(v___f_3375_);
v___f_3381_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_3381_, 0, v_toPure_3373_);
lean_closure_set(v___f_3381_, 1, v___x_3376_);
lean_closure_set(v___f_3381_, 2, v_toSeqRight_3374_);
lean_closure_set(v___f_3381_, 3, v_inst_3367_);
lean_closure_set(v___f_3381_, 4, v___f_3375_);
lean_closure_set(v___f_3381_, 5, v___f_3380_);
lean_closure_set(v___f_3381_, 6, v___f_3375_);
v___x_3382_ = lean_apply_4(v_toBind_3372_, lean_box(0), lean_box(0), v___x_3379_, v___f_3381_);
return v___x_3382_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f(lean_object* v_n_3383_, lean_object* v_m_3384_, lean_object* v_00_u03b1_3385_, lean_object* v_inst_3386_, lean_object* v_logger_3387_, lean_object* v_inst_3388_, lean_object* v_self_3389_){
_start:
{
lean_object* v_toApplicative_3390_; lean_object* v_toBind_3391_; lean_object* v_toPure_3392_; lean_object* v_toSeqRight_3393_; lean_object* v___f_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___f_3399_; lean_object* v___f_3400_; lean_object* v___x_3401_; 
v_toApplicative_3390_ = lean_ctor_get(v_inst_3386_, 0);
v_toBind_3391_ = lean_ctor_get(v_inst_3386_, 1);
lean_inc(v_toBind_3391_);
v_toPure_3392_ = lean_ctor_get(v_toApplicative_3390_, 1);
lean_inc_n(v_toPure_3392_, 2);
v_toSeqRight_3393_ = lean_ctor_get(v_toApplicative_3390_, 4);
lean_inc(v_toSeqRight_3393_);
v___f_3394_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3394_, 0, v_logger_3387_);
v___x_3395_ = lean_unsigned_to_nat(0u);
v___x_3396_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3397_ = lean_apply_1(v_self_3389_, v___x_3396_);
v___x_3398_ = lean_apply_2(v_inst_3388_, lean_box(0), v___x_3397_);
v___f_3399_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3399_, 0, v_toPure_3392_);
lean_inc_ref(v___f_3394_);
v___f_3400_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_3400_, 0, v_toPure_3392_);
lean_closure_set(v___f_3400_, 1, v___x_3395_);
lean_closure_set(v___f_3400_, 2, v_toSeqRight_3393_);
lean_closure_set(v___f_3400_, 3, v_inst_3386_);
lean_closure_set(v___f_3400_, 4, v___f_3394_);
lean_closure_set(v___f_3400_, 5, v___f_3399_);
lean_closure_set(v___f_3400_, 6, v___f_3394_);
v___x_3401_ = lean_apply_4(v_toBind_3391_, lean_box(0), lean_box(0), v___x_3398_, v___f_3400_);
return v___x_3401_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg___lam__3(lean_object* v_toPure_3402_, lean_object* v_a_3403_, lean_object* v_x_3404_){
_start:
{
lean_object* v___x_3405_; 
v___x_3405_ = lean_apply_2(v_toPure_3402_, lean_box(0), v_a_3403_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg___lam__0(lean_object* v_toApplicative_3406_, lean_object* v_toPure_3407_, lean_object* v___x_3408_, lean_object* v_toSeqRight_3409_, lean_object* v_inst_3410_, lean_object* v___f_3411_, lean_object* v___f_3412_, lean_object* v___f_3413_, lean_object* v_____do__lift_3414_){
_start:
{
if (lean_obj_tag(v_____do__lift_3414_) == 0)
{
lean_object* v_a_3415_; lean_object* v_a_3416_; lean_object* v_toPure_3417_; lean_object* v___f_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; uint8_t v___x_3421_; 
lean_dec(v___f_3413_);
lean_dec(v___f_3412_);
v_a_3415_ = lean_ctor_get(v_____do__lift_3414_, 0);
lean_inc(v_a_3415_);
v_a_3416_ = lean_ctor_get(v_____do__lift_3414_, 1);
lean_inc(v_a_3416_);
lean_dec_ref_known(v_____do__lift_3414_, 2);
v_toPure_3417_ = lean_ctor_get(v_toApplicative_3406_, 1);
lean_inc(v_toPure_3417_);
lean_dec_ref(v_toApplicative_3406_);
v___f_3418_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog___redArg___lam__3), 3, 2);
lean_closure_set(v___f_3418_, 0, v_toPure_3407_);
lean_closure_set(v___f_3418_, 1, v_a_3415_);
v___x_3419_ = lean_array_get_size(v_a_3416_);
v___x_3420_ = lean_box(0);
v___x_3421_ = lean_nat_dec_lt(v___x_3408_, v___x_3419_);
if (v___x_3421_ == 0)
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
lean_dec(v_a_3416_);
lean_dec(v___f_3411_);
lean_dec_ref(v_inst_3410_);
v___x_3422_ = lean_apply_2(v_toPure_3417_, lean_box(0), v___x_3420_);
v___x_3423_ = lean_apply_4(v_toSeqRight_3409_, lean_box(0), lean_box(0), v___x_3422_, v___f_3418_);
return v___x_3423_;
}
else
{
size_t v___x_3424_; size_t v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
lean_dec(v_toPure_3417_);
v___x_3424_ = ((size_t)0ULL);
v___x_3425_ = lean_usize_of_nat(v___x_3419_);
v___x_3426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3410_, v___f_3411_, v_a_3416_, v___x_3424_, v___x_3425_, v___x_3420_);
v___x_3427_ = lean_apply_4(v_toSeqRight_3409_, lean_box(0), lean_box(0), v___x_3426_, v___f_3418_);
return v___x_3427_;
}
}
else
{
lean_object* v_a_3428_; lean_object* v_toPure_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; uint8_t v___x_3432_; 
lean_dec(v___f_3411_);
lean_dec(v_toPure_3407_);
v_a_3428_ = lean_ctor_get(v_____do__lift_3414_, 1);
lean_inc(v_a_3428_);
lean_dec_ref_known(v_____do__lift_3414_, 2);
v_toPure_3429_ = lean_ctor_get(v_toApplicative_3406_, 1);
lean_inc(v_toPure_3429_);
lean_dec_ref(v_toApplicative_3406_);
v___x_3430_ = lean_array_get_size(v_a_3428_);
v___x_3431_ = lean_box(0);
v___x_3432_ = lean_nat_dec_lt(v___x_3408_, v___x_3430_);
if (v___x_3432_ == 0)
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
lean_dec(v_a_3428_);
lean_dec(v___f_3413_);
lean_dec_ref(v_inst_3410_);
v___x_3433_ = lean_apply_2(v_toPure_3429_, lean_box(0), v___x_3431_);
v___x_3434_ = lean_apply_4(v_toSeqRight_3409_, lean_box(0), lean_box(0), v___x_3433_, v___f_3412_);
return v___x_3434_;
}
else
{
size_t v___x_3435_; size_t v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
lean_dec(v_toPure_3429_);
v___x_3435_ = ((size_t)0ULL);
v___x_3436_ = lean_usize_of_nat(v___x_3430_);
v___x_3437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3410_, v___f_3413_, v_a_3428_, v___x_3435_, v___x_3436_, v___x_3431_);
v___x_3438_ = lean_apply_4(v_toSeqRight_3409_, lean_box(0), lean_box(0), v___x_3437_, v___f_3412_);
return v___x_3438_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg___lam__0___boxed(lean_object* v_toApplicative_3439_, lean_object* v_toPure_3440_, lean_object* v___x_3441_, lean_object* v_toSeqRight_3442_, lean_object* v_inst_3443_, lean_object* v___f_3444_, lean_object* v___f_3445_, lean_object* v___f_3446_, lean_object* v_____do__lift_3447_){
_start:
{
lean_object* v_res_3448_; 
v_res_3448_ = l_Lake_ELogT_replayLog___redArg___lam__0(v_toApplicative_3439_, v_toPure_3440_, v___x_3441_, v_toSeqRight_3442_, v_inst_3443_, v___f_3444_, v___f_3445_, v___f_3446_, v_____do__lift_3447_);
lean_dec(v___x_3441_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg(lean_object* v_inst_3449_, lean_object* v_inst_3450_, lean_object* v_logger_3451_, lean_object* v_inst_3452_, lean_object* v_self_3453_){
_start:
{
lean_object* v_toApplicative_3454_; lean_object* v_toApplicative_3455_; lean_object* v_toBind_3456_; lean_object* v_failure_3457_; lean_object* v_toPure_3458_; lean_object* v_toSeqRight_3459_; lean_object* v___f_3460_; lean_object* v___f_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___f_3466_; lean_object* v___x_3467_; 
v_toApplicative_3454_ = lean_ctor_get(v_inst_3449_, 0);
lean_inc_ref(v_toApplicative_3454_);
v_toApplicative_3455_ = lean_ctor_get(v_inst_3450_, 0);
lean_inc_ref(v_toApplicative_3455_);
v_toBind_3456_ = lean_ctor_get(v_inst_3450_, 1);
lean_inc(v_toBind_3456_);
v_failure_3457_ = lean_ctor_get(v_inst_3449_, 1);
lean_inc(v_failure_3457_);
lean_dec_ref(v_inst_3449_);
v_toPure_3458_ = lean_ctor_get(v_toApplicative_3454_, 1);
lean_inc(v_toPure_3458_);
v_toSeqRight_3459_ = lean_ctor_get(v_toApplicative_3454_, 4);
lean_inc(v_toSeqRight_3459_);
lean_dec_ref(v_toApplicative_3454_);
v___f_3460_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3460_, 0, v_logger_3451_);
v___f_3461_ = lean_alloc_closure((void*)(l_Lake_MonadLog_error___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3461_, 0, v_failure_3457_);
v___x_3462_ = lean_unsigned_to_nat(0u);
v___x_3463_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3464_ = lean_apply_1(v_self_3453_, v___x_3463_);
v___x_3465_ = lean_apply_2(v_inst_3452_, lean_box(0), v___x_3464_);
lean_inc_ref(v___f_3460_);
v___f_3466_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3466_, 0, v_toApplicative_3455_);
lean_closure_set(v___f_3466_, 1, v_toPure_3458_);
lean_closure_set(v___f_3466_, 2, v___x_3462_);
lean_closure_set(v___f_3466_, 3, v_toSeqRight_3459_);
lean_closure_set(v___f_3466_, 4, v_inst_3450_);
lean_closure_set(v___f_3466_, 5, v___f_3460_);
lean_closure_set(v___f_3466_, 6, v___f_3461_);
lean_closure_set(v___f_3466_, 7, v___f_3460_);
v___x_3467_ = lean_apply_4(v_toBind_3456_, lean_box(0), lean_box(0), v___x_3465_, v___f_3466_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog(lean_object* v_n_3468_, lean_object* v_m_3469_, lean_object* v_00_u03b1_3470_, lean_object* v_inst_3471_, lean_object* v_inst_3472_, lean_object* v_logger_3473_, lean_object* v_inst_3474_, lean_object* v_self_3475_){
_start:
{
lean_object* v_toApplicative_3476_; lean_object* v_toApplicative_3477_; lean_object* v_toBind_3478_; lean_object* v_failure_3479_; lean_object* v_toPure_3480_; lean_object* v_toSeqRight_3481_; lean_object* v___f_3482_; lean_object* v___f_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___f_3488_; lean_object* v___x_3489_; 
v_toApplicative_3476_ = lean_ctor_get(v_inst_3471_, 0);
lean_inc_ref(v_toApplicative_3476_);
v_toApplicative_3477_ = lean_ctor_get(v_inst_3472_, 0);
lean_inc_ref(v_toApplicative_3477_);
v_toBind_3478_ = lean_ctor_get(v_inst_3472_, 1);
lean_inc(v_toBind_3478_);
v_failure_3479_ = lean_ctor_get(v_inst_3471_, 1);
lean_inc(v_failure_3479_);
lean_dec_ref(v_inst_3471_);
v_toPure_3480_ = lean_ctor_get(v_toApplicative_3476_, 1);
lean_inc(v_toPure_3480_);
v_toSeqRight_3481_ = lean_ctor_get(v_toApplicative_3476_, 4);
lean_inc(v_toSeqRight_3481_);
lean_dec_ref(v_toApplicative_3476_);
v___f_3482_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3482_, 0, v_logger_3473_);
v___f_3483_ = lean_alloc_closure((void*)(l_Lake_MonadLog_error___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3483_, 0, v_failure_3479_);
v___x_3484_ = lean_unsigned_to_nat(0u);
v___x_3485_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3486_ = lean_apply_1(v_self_3475_, v___x_3485_);
v___x_3487_ = lean_apply_2(v_inst_3474_, lean_box(0), v___x_3486_);
lean_inc_ref(v___f_3482_);
v___f_3488_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3488_, 0, v_toApplicative_3477_);
lean_closure_set(v___f_3488_, 1, v_toPure_3480_);
lean_closure_set(v___f_3488_, 2, v___x_3484_);
lean_closure_set(v___f_3488_, 3, v_toSeqRight_3481_);
lean_closure_set(v___f_3488_, 4, v_inst_3472_);
lean_closure_set(v___f_3488_, 5, v___f_3482_);
lean_closure_set(v___f_3488_, 6, v___f_3483_);
lean_closure_set(v___f_3488_, 7, v___f_3482_);
v___x_3489_ = lean_apply_4(v_toBind_3478_, lean_box(0), lean_box(0), v___x_3487_, v___f_3488_);
return v___x_3489_;
}
}
lean_object* l_Lake_LogConfig_getLogger___redArg___lam__0(lean_object* v_val_3490_, uint8_t v_outLv_3491_, uint8_t v_val_3492_, lean_object* v_inst_3493_, lean_object* v_e_3494_){
_start:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3495_ = lean_box(v_outLv_3491_);
v___x_3496_ = lean_box(v_val_3492_);
v___x_3497_ = lean_alloc_closure((void*)(l_Lake_logToStream___boxed), 5, 4);
lean_closure_set(v___x_3497_, 0, v_e_3494_);
lean_closure_set(v___x_3497_, 1, v_val_3490_);
lean_closure_set(v___x_3497_, 2, v___x_3495_);
lean_closure_set(v___x_3497_, 3, v___x_3496_);
v___x_3498_ = lean_apply_2(v_inst_3493_, lean_box(0), v___x_3497_);
return v___x_3498_;
}
}
LEAN_EXPORT void l_Lake_LogConfig_getLogger___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_3490_ = stack[0].m_obj;
uint8_t v_outLv_3491_ = stack[1].m_num;
uint8_t v_val_3492_ = stack[2].m_num;
lean_object* v_inst_3493_ = stack[3].m_obj;
lean_object* v_e_3494_ = stack[4].m_obj;
lean_object* v_res_3499_;
v_res_3499_ = l_Lake_LogConfig_getLogger___redArg___lam__0(v_val_3490_, v_outLv_3491_, v_val_3492_, v_inst_3493_, v_e_3494_);
stack->m_obj
 = v_res_3499_;
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___redArg___lam__0___boxed(lean_object* v_val_3500_, lean_object* v_outLv_3501_, lean_object* v_val_3502_, lean_object* v_inst_3503_, lean_object* v_e_3504_){
_start:
{
uint8_t v_outLv_boxed_3505_; uint8_t v_val_44__boxed_3506_; lean_object* v_res_3507_; 
v_outLv_boxed_3505_ = lean_unbox(v_outLv_3501_);
v_val_44__boxed_3506_ = lean_unbox(v_val_3502_);
v_res_3507_ = l_Lake_LogConfig_getLogger___redArg___lam__0(v_val_3500_, v_outLv_boxed_3505_, v_val_44__boxed_3506_, v_inst_3503_, v_e_3504_);
return v_res_3507_;
}
}
lean_object* l_Lake_LogConfig_getLogger___redArg(lean_object* v_inst_3508_, lean_object* v_self_3509_){
_start:
{
uint8_t v_outLv_3511_; uint8_t v_ansiMode_3512_; lean_object* v_out_3513_; lean_object* v___x_3514_; uint8_t v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___f_3518_; 
v_outLv_3511_ = lean_ctor_get_uint8(v_self_3509_, sizeof(void*)*1 + 1);
v_ansiMode_3512_ = lean_ctor_get_uint8(v_self_3509_, sizeof(void*)*1 + 2);
v_out_3513_ = lean_ctor_get(v_self_3509_, 0);
v___x_3514_ = l_Lake_OutStream_get(v_out_3513_);
lean_inc_ref(v___x_3514_);
v___x_3515_ = l_Lake_AnsiMode_isEnabled(v___x_3514_, v_ansiMode_3512_);
v___x_3516_ = lean_box(v_outLv_3511_);
v___x_3517_ = lean_box(v___x_3515_);
v___f_3518_ = lean_alloc_closure((void*)(l_Lake_LogConfig_getLogger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3518_, 0, v___x_3514_);
lean_closure_set(v___f_3518_, 1, v___x_3516_);
lean_closure_set(v___f_3518_, 2, v___x_3517_);
lean_closure_set(v___f_3518_, 3, v_inst_3508_);
return v___f_3518_;
}
}
LEAN_EXPORT void l_Lake_LogConfig_getLogger___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3508_ = stack[0].m_obj;
lean_object* v_self_3509_ = stack[1].m_obj;
lean_object* v_res_3519_;
v_res_3519_ = l_Lake_LogConfig_getLogger___redArg(v_inst_3508_, v_self_3509_);
stack->m_obj
 = v_res_3519_;
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___redArg___boxed(lean_object* v_inst_3520_, lean_object* v_self_3521_, lean_object* v_a_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = l_Lake_LogConfig_getLogger___redArg(v_inst_3520_, v_self_3521_);
lean_dec_ref(v_self_3521_);
return v_res_3523_;
}
}
lean_object* l_Lake_LogConfig_getLogger(lean_object* v_m_3524_, lean_object* v_inst_3525_, lean_object* v_self_3526_){
_start:
{
uint8_t v_outLv_3528_; uint8_t v_ansiMode_3529_; lean_object* v_out_3530_; lean_object* v___x_3531_; uint8_t v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___f_3535_; 
v_outLv_3528_ = lean_ctor_get_uint8(v_self_3526_, sizeof(void*)*1 + 1);
v_ansiMode_3529_ = lean_ctor_get_uint8(v_self_3526_, sizeof(void*)*1 + 2);
v_out_3530_ = lean_ctor_get(v_self_3526_, 0);
v___x_3531_ = l_Lake_OutStream_get(v_out_3530_);
lean_inc_ref(v___x_3531_);
v___x_3532_ = l_Lake_AnsiMode_isEnabled(v___x_3531_, v_ansiMode_3529_);
v___x_3533_ = lean_box(v_outLv_3528_);
v___x_3534_ = lean_box(v___x_3532_);
v___f_3535_ = lean_alloc_closure((void*)(l_Lake_LogConfig_getLogger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3535_, 0, v___x_3531_);
lean_closure_set(v___f_3535_, 1, v___x_3533_);
lean_closure_set(v___f_3535_, 2, v___x_3534_);
lean_closure_set(v___f_3535_, 3, v_inst_3525_);
return v___f_3535_;
}
}
LEAN_EXPORT void l_Lake_LogConfig_getLogger_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3525_ = stack[1].m_obj;
lean_object* v_self_3526_ = stack[2].m_obj;
lean_object* v_res_3536_;
v_res_3536_ = l_Lake_LogConfig_getLogger(lean_box(0), v_inst_3525_, v_self_3526_);
stack->m_obj
 = v_res_3536_;
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___boxed(lean_object* v_m_3537_, lean_object* v_inst_3538_, lean_object* v_self_3539_, lean_object* v_a_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l_Lake_LogConfig_getLogger(v_m_3537_, v_inst_3538_, v_self_3539_);
lean_dec_ref(v_self_3539_);
return v_res_3541_;
}
}
lean_object* l_Lake_LogIO_instMonadLiftIO___lam__0(lean_object* v_00_u03b1_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
lean_object* v___x_3546_; 
v___x_3546_ = lean_apply_1(v___y_3543_, lean_box(0));
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_a_3547_; lean_object* v___x_3548_; 
v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_a_3547_);
lean_dec_ref_known(v___x_3546_, 1);
v___x_3548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3548_, 0, v_a_3547_);
lean_ctor_set(v___x_3548_, 1, v___y_3544_);
return v___x_3548_;
}
else
{
lean_object* v_a_3549_; lean_object* v___x_3550_; uint8_t v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v_a_3549_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_a_3549_);
lean_dec_ref_known(v___x_3546_, 1);
v___x_3550_ = lean_io_error_to_string(v_a_3549_);
v___x_3551_ = 3;
v___x_3552_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3552_, 0, v___x_3550_);
lean_ctor_set_uint8(v___x_3552_, sizeof(void*)*1, v___x_3551_);
v___x_3553_ = lean_array_get_size(v___y_3544_);
v___x_3554_ = lean_array_push(v___y_3544_, v___x_3552_);
v___x_3555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3553_);
lean_ctor_set(v___x_3555_, 1, v___x_3554_);
return v___x_3555_;
}
}
}
LEAN_EXPORT void l_Lake_LogIO_instMonadLiftIO___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3543_ = stack[1].m_obj;
lean_object* v___y_3544_ = stack[2].m_obj;
lean_object* v_res_3556_;
v_res_3556_ = l_Lake_LogIO_instMonadLiftIO___lam__0(lean_box(0), v___y_3543_, v___y_3544_);
stack->m_obj
 = v_res_3556_;
}
LEAN_EXPORT lean_object* l_Lake_LogIO_instMonadLiftIO___lam__0___boxed(lean_object* v_00_u03b1_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_){
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l_Lake_LogIO_instMonadLiftIO___lam__0(v_00_u03b1_3557_, v___y_3558_, v___y_3559_);
return v_res_3561_;
}
}
lean_object* l_Lake_LogIO_toBaseIO___redArg___lam__0(lean_object* v_val_3564_, uint8_t v___y_3565_, uint8_t v_val_3566_, lean_object* v_x_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v___x_3570_; 
v___x_3570_ = l_Lake_logToStream(v___y_3568_, v_val_3564_, v___y_3565_, v_val_3566_);
return v___x_3570_;
}
}
LEAN_EXPORT void l_Lake_LogIO_toBaseIO___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_3564_ = stack[0].m_obj;
uint8_t v___y_3565_ = stack[1].m_num;
uint8_t v_val_3566_ = stack[2].m_num;
lean_object* v_x_3567_ = stack[3].m_obj;
lean_object* v___y_3568_ = stack[4].m_obj;
lean_object* v_res_3571_;
v_res_3571_ = l_Lake_LogIO_toBaseIO___redArg___lam__0(v_val_3564_, v___y_3565_, v_val_3566_, v_x_3567_, v___y_3568_);
stack->m_obj
 = v_res_3571_;
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed(lean_object* v_val_3572_, lean_object* v___y_3573_, lean_object* v_val_3574_, lean_object* v_x_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_){
_start:
{
uint8_t v___y_740__boxed_3578_; uint8_t v_val_741__boxed_3579_; lean_object* v_res_3580_; 
v___y_740__boxed_3578_ = lean_unbox(v___y_3573_);
v_val_741__boxed_3579_ = lean_unbox(v_val_3574_);
v_res_3580_ = l_Lake_LogIO_toBaseIO___redArg___lam__0(v_val_3572_, v___y_740__boxed_3578_, v_val_741__boxed_3579_, v_x_3575_, v___y_3576_);
lean_dec_ref(v___y_3576_);
return v_res_3580_;
}
}
lean_object* l_Lake_LogIO_toBaseIO___redArg(lean_object* v_self_3581_, lean_object* v_cfg_3582_){
_start:
{
lean_object* v___y_3585_; uint8_t v___y_3586_; lean_object* v___x_3588_; lean_object* v___y_3590_; uint8_t v___y_3591_; lean_object* v___y_3592_; uint8_t v___y_3593_; lean_object* v___y_3610_; lean_object* v___y_3611_; uint8_t v___y_3612_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3588_ = l_instMonadBaseIO;
v___x_3614_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3615_ = lean_apply_2(v_self_3581_, v___x_3614_, lean_box(0));
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v_a_3616_; lean_object* v_a_3617_; uint8_t v_failLv_3618_; uint8_t v_outLv_3619_; lean_object* v___x_3620_; uint8_t v___x_3621_; uint8_t v___x_3622_; 
v_a_3616_ = lean_ctor_get(v___x_3615_, 0);
lean_inc(v_a_3616_);
v_a_3617_ = lean_ctor_get(v___x_3615_, 1);
lean_inc(v_a_3617_);
lean_dec_ref_known(v___x_3615_, 2);
v_failLv_3618_ = lean_ctor_get_uint8(v_cfg_3582_, sizeof(void*)*1);
v_outLv_3619_ = lean_ctor_get_uint8(v_cfg_3582_, sizeof(void*)*1 + 1);
v___x_3620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3620_, 0, v_a_3616_);
v___x_3621_ = l_Lake_Log_maxLv(v_a_3617_);
v___x_3622_ = l_Lake_instOrdLogLevel_ord(v_failLv_3618_, v___x_3621_);
if (v___x_3622_ == 2)
{
uint8_t v___x_3623_; 
v___x_3623_ = 0;
v___y_3590_ = v___x_3620_;
v___y_3591_ = v___x_3623_;
v___y_3592_ = v_a_3617_;
v___y_3593_ = v_outLv_3619_;
goto v___jp_3589_;
}
else
{
uint8_t v___x_3624_; 
v___x_3624_ = 1;
v___y_3610_ = v___x_3620_;
v___y_3611_ = v_a_3617_;
v___y_3612_ = v___x_3624_;
goto v___jp_3609_;
}
}
else
{
lean_object* v_a_3625_; lean_object* v___x_3626_; uint8_t v___x_3627_; 
v_a_3625_ = lean_ctor_get(v___x_3615_, 1);
lean_inc(v_a_3625_);
lean_dec_ref_known(v___x_3615_, 2);
v___x_3626_ = lean_box(0);
v___x_3627_ = 1;
v___y_3610_ = v___x_3626_;
v___y_3611_ = v_a_3625_;
v___y_3612_ = v___x_3627_;
goto v___jp_3609_;
}
v___jp_3584_:
{
if (v___y_3586_ == 0)
{
return v___y_3585_;
}
else
{
lean_object* v___x_3587_; 
lean_dec(v___y_3585_);
v___x_3587_ = lean_box(0);
return v___x_3587_;
}
}
v___jp_3589_:
{
uint8_t v_ansiMode_3594_; lean_object* v_out_3595_; lean_object* v___x_3596_; uint8_t v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; uint8_t v___x_3600_; 
v_ansiMode_3594_ = lean_ctor_get_uint8(v_cfg_3582_, sizeof(void*)*1 + 2);
v_out_3595_ = lean_ctor_get(v_cfg_3582_, 0);
v___x_3596_ = l_Lake_OutStream_get(v_out_3595_);
lean_inc_ref(v___x_3596_);
v___x_3597_ = l_Lake_AnsiMode_isEnabled(v___x_3596_, v_ansiMode_3594_);
v___x_3598_ = lean_unsigned_to_nat(0u);
v___x_3599_ = lean_array_get_size(v___y_3592_);
v___x_3600_ = lean_nat_dec_lt(v___x_3598_, v___x_3599_);
if (v___x_3600_ == 0)
{
lean_dec_ref(v___x_3596_);
lean_dec_ref(v___y_3592_);
v___y_3585_ = v___y_3590_;
v___y_3586_ = v___y_3591_;
goto v___jp_3584_;
}
else
{
lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___f_3603_; lean_object* v___x_3604_; size_t v___x_3605_; size_t v___x_3606_; lean_object* v___x_521__overap_3607_; lean_object* v___x_3608_; 
v___x_3601_ = lean_box(v___y_3593_);
v___x_3602_ = lean_box(v___x_3597_);
v___f_3603_ = lean_alloc_closure((void*)(l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_3603_, 0, v___x_3596_);
lean_closure_set(v___f_3603_, 1, v___x_3601_);
lean_closure_set(v___f_3603_, 2, v___x_3602_);
v___x_3604_ = lean_box(0);
v___x_3605_ = ((size_t)0ULL);
v___x_3606_ = lean_usize_of_nat(v___x_3599_);
v___x_521__overap_3607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3588_, v___f_3603_, v___y_3592_, v___x_3605_, v___x_3606_, v___x_3604_);
v___x_3608_ = lean_apply_1(v___x_521__overap_3607_, lean_box(0));
v___y_3585_ = v___y_3590_;
v___y_3586_ = v___y_3591_;
goto v___jp_3584_;
}
}
v___jp_3609_:
{
uint8_t v___x_3613_; 
v___x_3613_ = 0;
v___y_3590_ = v___y_3610_;
v___y_3591_ = v___y_3612_;
v___y_3592_ = v___y_3611_;
v___y_3593_ = v___x_3613_;
goto v___jp_3589_;
}
}
}
LEAN_EXPORT void l_Lake_LogIO_toBaseIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_3581_ = stack[0].m_obj;
lean_object* v_cfg_3582_ = stack[1].m_obj;
lean_object* v_res_3628_;
v_res_3628_ = l_Lake_LogIO_toBaseIO___redArg(v_self_3581_, v_cfg_3582_);
stack->m_obj
 = v_res_3628_;
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg___boxed(lean_object* v_self_3629_, lean_object* v_cfg_3630_, lean_object* v_a_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l_Lake_LogIO_toBaseIO___redArg(v_self_3629_, v_cfg_3630_);
lean_dec_ref(v_cfg_3630_);
return v_res_3632_;
}
}
lean_object* l_Lake_LogIO_toBaseIO(lean_object* v_00_u03b1_3633_, lean_object* v_self_3634_, lean_object* v_cfg_3635_){
_start:
{
lean_object* v___y_3638_; uint8_t v___y_3639_; lean_object* v___x_3641_; lean_object* v___y_3643_; uint8_t v___y_3644_; lean_object* v___y_3645_; uint8_t v___y_3646_; lean_object* v___y_3663_; lean_object* v___y_3664_; uint8_t v___y_3665_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3641_ = l_instMonadBaseIO;
v___x_3667_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3668_ = lean_apply_2(v_self_3634_, v___x_3667_, lean_box(0));
if (lean_obj_tag(v___x_3668_) == 0)
{
lean_object* v_a_3669_; lean_object* v_a_3670_; uint8_t v_failLv_3671_; uint8_t v_outLv_3672_; lean_object* v___x_3673_; uint8_t v___x_3674_; uint8_t v___x_3675_; 
v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
lean_inc(v_a_3669_);
v_a_3670_ = lean_ctor_get(v___x_3668_, 1);
lean_inc(v_a_3670_);
lean_dec_ref_known(v___x_3668_, 2);
v_failLv_3671_ = lean_ctor_get_uint8(v_cfg_3635_, sizeof(void*)*1);
v_outLv_3672_ = lean_ctor_get_uint8(v_cfg_3635_, sizeof(void*)*1 + 1);
v___x_3673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3673_, 0, v_a_3669_);
v___x_3674_ = l_Lake_Log_maxLv(v_a_3670_);
v___x_3675_ = l_Lake_instOrdLogLevel_ord(v_failLv_3671_, v___x_3674_);
if (v___x_3675_ == 2)
{
uint8_t v___x_3676_; 
v___x_3676_ = 0;
v___y_3643_ = v___x_3673_;
v___y_3644_ = v___x_3676_;
v___y_3645_ = v_a_3670_;
v___y_3646_ = v_outLv_3672_;
goto v___jp_3642_;
}
else
{
uint8_t v___x_3677_; 
v___x_3677_ = 1;
v___y_3663_ = v___x_3673_;
v___y_3664_ = v_a_3670_;
v___y_3665_ = v___x_3677_;
goto v___jp_3662_;
}
}
else
{
lean_object* v_a_3678_; lean_object* v___x_3679_; uint8_t v___x_3680_; 
v_a_3678_ = lean_ctor_get(v___x_3668_, 1);
lean_inc(v_a_3678_);
lean_dec_ref_known(v___x_3668_, 2);
v___x_3679_ = lean_box(0);
v___x_3680_ = 1;
v___y_3663_ = v___x_3679_;
v___y_3664_ = v_a_3678_;
v___y_3665_ = v___x_3680_;
goto v___jp_3662_;
}
v___jp_3637_:
{
if (v___y_3639_ == 0)
{
return v___y_3638_;
}
else
{
lean_object* v___x_3640_; 
lean_dec(v___y_3638_);
v___x_3640_ = lean_box(0);
return v___x_3640_;
}
}
v___jp_3642_:
{
uint8_t v_ansiMode_3647_; lean_object* v_out_3648_; lean_object* v___x_3649_; uint8_t v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; uint8_t v___x_3653_; 
v_ansiMode_3647_ = lean_ctor_get_uint8(v_cfg_3635_, sizeof(void*)*1 + 2);
v_out_3648_ = lean_ctor_get(v_cfg_3635_, 0);
v___x_3649_ = l_Lake_OutStream_get(v_out_3648_);
lean_inc_ref(v___x_3649_);
v___x_3650_ = l_Lake_AnsiMode_isEnabled(v___x_3649_, v_ansiMode_3647_);
v___x_3651_ = lean_unsigned_to_nat(0u);
v___x_3652_ = lean_array_get_size(v___y_3645_);
v___x_3653_ = lean_nat_dec_lt(v___x_3651_, v___x_3652_);
if (v___x_3653_ == 0)
{
lean_dec_ref(v___x_3649_);
lean_dec_ref(v___y_3645_);
v___y_3638_ = v___y_3643_;
v___y_3639_ = v___y_3644_;
goto v___jp_3637_;
}
else
{
lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___f_3656_; lean_object* v___x_3657_; size_t v___x_3658_; size_t v___x_3659_; lean_object* v___x_665__overap_3660_; lean_object* v___x_3661_; 
v___x_3654_ = lean_box(v___y_3646_);
v___x_3655_ = lean_box(v___x_3650_);
v___f_3656_ = lean_alloc_closure((void*)(l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_3656_, 0, v___x_3649_);
lean_closure_set(v___f_3656_, 1, v___x_3654_);
lean_closure_set(v___f_3656_, 2, v___x_3655_);
v___x_3657_ = lean_box(0);
v___x_3658_ = ((size_t)0ULL);
v___x_3659_ = lean_usize_of_nat(v___x_3652_);
v___x_665__overap_3660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3641_, v___f_3656_, v___y_3645_, v___x_3658_, v___x_3659_, v___x_3657_);
v___x_3661_ = lean_apply_1(v___x_665__overap_3660_, lean_box(0));
v___y_3638_ = v___y_3643_;
v___y_3639_ = v___y_3644_;
goto v___jp_3637_;
}
}
v___jp_3662_:
{
uint8_t v___x_3666_; 
v___x_3666_ = 0;
v___y_3643_ = v___y_3663_;
v___y_3644_ = v___y_3665_;
v___y_3645_ = v___y_3664_;
v___y_3646_ = v___x_3666_;
goto v___jp_3642_;
}
}
}
LEAN_EXPORT void l_Lake_LogIO_toBaseIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_3634_ = stack[1].m_obj;
lean_object* v_cfg_3635_ = stack[2].m_obj;
lean_object* v_res_3681_;
v_res_3681_ = l_Lake_LogIO_toBaseIO(lean_box(0), v_self_3634_, v_cfg_3635_);
stack->m_obj
 = v_res_3681_;
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___boxed(lean_object* v_00_u03b1_3682_, lean_object* v_self_3683_, lean_object* v_cfg_3684_, lean_object* v_a_3685_){
_start:
{
lean_object* v_res_3686_; 
v_res_3686_ = l_Lake_LogIO_toBaseIO(v_00_u03b1_3682_, v_self_3683_, v_cfg_3684_);
lean_dec_ref(v_cfg_3684_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_captureLog___redArg(lean_object* v_inst_3687_, lean_object* v_self_3688_, lean_object* v_log_3689_){
_start:
{
lean_object* v_map_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
v_map_3690_ = lean_ctor_get(v_inst_3687_, 0);
lean_inc(v_map_3690_);
lean_dec_ref(v_inst_3687_);
v___x_3691_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3692_ = lean_apply_1(v_self_3688_, v_log_3689_);
v___x_3693_ = lean_apply_4(v_map_3690_, lean_box(0), lean_box(0), v___x_3691_, v___x_3692_);
return v___x_3693_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_captureLog(lean_object* v_m_3694_, lean_object* v_00_u03b1_3695_, lean_object* v_inst_3696_, lean_object* v_self_3697_, lean_object* v_log_3698_){
_start:
{
lean_object* v_map_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
v_map_3699_ = lean_ctor_get(v_inst_3696_, 0);
lean_inc(v_map_3699_);
lean_dec_ref(v_inst_3696_);
v___x_3700_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3701_ = lean_apply_1(v_self_3697_, v_log_3698_);
v___x_3702_ = lean_apply_4(v_map_3699_, lean_box(0), lean_box(0), v___x_3700_, v___x_3701_);
return v___x_3702_;
}
}
lean_object* l_Lake_LoggerIO_instMonadError___lam__0(lean_object* v_00_u03b1_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_){
_start:
{
uint8_t v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3707_ = 3;
v___x_3708_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3708_, 0, v___y_3704_);
lean_ctor_set_uint8(v___x_3708_, sizeof(void*)*1, v___x_3707_);
lean_inc_ref(v___y_3705_);
v___x_3709_ = lean_apply_2(v___y_3705_, v___x_3708_, lean_box(0));
v___x_3710_ = lean_box(0);
v___x_3711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3710_);
return v___x_3711_;
}
}
LEAN_EXPORT void l_Lake_LoggerIO_instMonadError___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3704_ = stack[1].m_obj;
lean_object* v___y_3705_ = stack[2].m_obj;
lean_object* v_res_3712_;
v_res_3712_ = l_Lake_LoggerIO_instMonadError___lam__0(lean_box(0), v___y_3704_, v___y_3705_);
stack->m_obj
 = v_res_3712_;
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadError___lam__0___boxed(lean_object* v_00_u03b1_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
lean_object* v_res_3717_; 
v_res_3717_ = l_Lake_LoggerIO_instMonadError___lam__0(v_00_u03b1_3713_, v___y_3714_, v___y_3715_);
lean_dec_ref(v___y_3715_);
return v_res_3717_;
}
}
lean_object* l_Lake_LoggerIO_instMonadLiftIO___lam__0(lean_object* v_00_u03b1_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_){
_start:
{
lean_object* v___x_3724_; 
v___x_3724_ = lean_apply_1(v___y_3721_, lean_box(0));
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v_a_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3732_; 
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3727_ = v___x_3724_;
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_a_3725_);
lean_dec(v___x_3724_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3730_; 
if (v_isShared_3728_ == 0)
{
v___x_3730_ = v___x_3727_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_a_3725_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
else
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3745_; 
v_a_3733_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3735_ = v___x_3724_;
v_isShared_3736_ = v_isSharedCheck_3745_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3724_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3745_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3737_; uint8_t v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3743_; 
v___x_3737_ = lean_io_error_to_string(v_a_3733_);
v___x_3738_ = 3;
v___x_3739_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3739_, 0, v___x_3737_);
lean_ctor_set_uint8(v___x_3739_, sizeof(void*)*1, v___x_3738_);
lean_inc_ref(v___y_3722_);
v___x_3740_ = lean_apply_2(v___y_3722_, v___x_3739_, lean_box(0));
v___x_3741_ = lean_box(0);
if (v_isShared_3736_ == 0)
{
lean_ctor_set(v___x_3735_, 0, v___x_3741_);
v___x_3743_ = v___x_3735_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v___x_3741_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_LoggerIO_instMonadLiftIO___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3721_ = stack[1].m_obj;
lean_object* v___y_3722_ = stack[2].m_obj;
lean_object* v_res_3746_;
v_res_3746_ = l_Lake_LoggerIO_instMonadLiftIO___lam__0(lean_box(0), v___y_3721_, v___y_3722_);
stack->m_obj
 = v_res_3746_;
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftIO___lam__0___boxed(lean_object* v_00_u03b1_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_){
_start:
{
lean_object* v_res_3751_; 
v_res_3751_ = l_Lake_LoggerIO_instMonadLiftIO___lam__0(v_00_u03b1_3747_, v___y_3748_, v___y_3749_);
lean_dec_ref(v___y_3749_);
return v_res_3751_;
}
}
lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__0(lean_object* v_x_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v___x_3758_; lean_object* v___x_3759_; 
lean_inc_ref(v___y_3756_);
v___x_3758_ = lean_apply_2(v___y_3756_, v___y_3755_, lean_box(0));
v___x_3759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3758_);
return v___x_3759_;
}
}
LEAN_EXPORT void l_Lake_LoggerIO_instMonadLiftLogIO___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3754_ = stack[0].m_obj;
lean_object* v___y_3755_ = stack[1].m_obj;
lean_object* v___y_3756_ = stack[2].m_obj;
lean_object* v_res_3760_;
v_res_3760_ = l_Lake_LoggerIO_instMonadLiftLogIO___lam__0(v_x_3754_, v___y_3755_, v___y_3756_);
stack->m_obj
 = v_res_3760_;
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__0___boxed(lean_object* v_x_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
lean_object* v_res_3765_; 
v_res_3765_ = l_Lake_LoggerIO_instMonadLiftLogIO___lam__0(v_x_3761_, v___y_3762_, v___y_3763_);
lean_dec_ref(v___y_3763_);
return v_res_3765_;
}
}
lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__2(lean_object* v___x_3766_, lean_object* v___f_3767_, lean_object* v___f_3768_, lean_object* v_00_u03b1_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
v___x_3773_ = lean_unsigned_to_nat(0u);
v___x_3774_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3775_ = lean_apply_2(v___y_3770_, v___x_3774_, lean_box(0));
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v_a_3776_; lean_object* v_a_3777_; lean_object* v___x_3778_; uint8_t v___x_3779_; 
lean_dec_ref(v___f_3768_);
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
lean_inc(v_a_3776_);
v_a_3777_ = lean_ctor_get(v___x_3775_, 1);
lean_inc(v_a_3777_);
lean_dec_ref_known(v___x_3775_, 2);
v___x_3778_ = lean_array_get_size(v_a_3777_);
v___x_3779_ = lean_nat_dec_lt(v___x_3773_, v___x_3778_);
if (v___x_3779_ == 0)
{
lean_object* v___x_3780_; 
lean_dec(v_a_3777_);
lean_dec_ref(v___f_3767_);
lean_dec_ref(v___x_3766_);
v___x_3780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3780_, 0, v_a_3776_);
return v___x_3780_;
}
else
{
lean_object* v___x_3781_; size_t v___x_3782_; size_t v___x_3783_; lean_object* v___x_1294__overap_3784_; lean_object* v___x_3785_; 
v___x_3781_ = lean_box(0);
v___x_3782_ = ((size_t)0ULL);
v___x_3783_ = lean_usize_of_nat(v___x_3778_);
v___x_1294__overap_3784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3766_, v___f_3767_, v_a_3777_, v___x_3782_, v___x_3783_, v___x_3781_);
lean_inc_ref(v___y_3771_);
v___x_3785_ = lean_apply_2(v___x_1294__overap_3784_, v___y_3771_, lean_box(0));
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3792_; 
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3792_ == 0)
{
lean_object* v_unused_3793_; 
v_unused_3793_ = lean_ctor_get(v___x_3785_, 0);
lean_dec(v_unused_3793_);
v___x_3787_ = v___x_3785_;
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
else
{
lean_dec(v___x_3785_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3790_; 
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 0, v_a_3776_);
v___x_3790_ = v___x_3787_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_a_3776_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
}
else
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3801_; 
lean_dec(v_a_3776_);
v_a_3794_ = lean_ctor_get(v___x_3785_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3796_ = v___x_3785_;
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3785_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3799_; 
if (v_isShared_3797_ == 0)
{
v___x_3799_ = v___x_3796_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_a_3794_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
}
else
{
lean_object* v_a_3802_; lean_object* v___x_3803_; uint8_t v___x_3804_; 
lean_dec_ref(v___f_3767_);
v_a_3802_ = lean_ctor_get(v___x_3775_, 1);
lean_inc(v_a_3802_);
lean_dec_ref_known(v___x_3775_, 2);
v___x_3803_ = lean_array_get_size(v_a_3802_);
v___x_3804_ = lean_nat_dec_lt(v___x_3773_, v___x_3803_);
if (v___x_3804_ == 0)
{
lean_object* v___x_3805_; lean_object* v___x_3806_; 
lean_dec(v_a_3802_);
lean_dec_ref(v___f_3768_);
lean_dec_ref(v___x_3766_);
v___x_3805_ = lean_box(0);
v___x_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3805_);
return v___x_3806_;
}
else
{
lean_object* v___x_3807_; size_t v___x_3808_; size_t v___x_3809_; lean_object* v___x_1310__overap_3810_; lean_object* v___x_3811_; 
v___x_3807_ = lean_box(0);
v___x_3808_ = ((size_t)0ULL);
v___x_3809_ = lean_usize_of_nat(v___x_3803_);
v___x_1310__overap_3810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3766_, v___f_3768_, v_a_3802_, v___x_3808_, v___x_3809_, v___x_3807_);
lean_inc_ref(v___y_3771_);
v___x_3811_ = lean_apply_2(v___x_1310__overap_3810_, v___y_3771_, lean_box(0));
if (lean_obj_tag(v___x_3811_) == 0)
{
lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3811_);
if (v_isSharedCheck_3818_ == 0)
{
lean_object* v_unused_3819_; 
v_unused_3819_ = lean_ctor_get(v___x_3811_, 0);
lean_dec(v_unused_3819_);
v___x_3813_ = v___x_3811_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_dec(v___x_3811_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3816_; 
if (v_isShared_3814_ == 0)
{
lean_ctor_set_tag(v___x_3813_, 1);
lean_ctor_set(v___x_3813_, 0, v___x_3807_);
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v___x_3807_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
else
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3827_; 
v_a_3820_ = lean_ctor_get(v___x_3811_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3811_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3822_ = v___x_3811_;
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3811_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3825_; 
if (v_isShared_3823_ == 0)
{
v___x_3825_ = v___x_3822_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_a_3820_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_LoggerIO_instMonadLiftLogIO___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3766_ = stack[0].m_obj;
lean_object* v___f_3767_ = stack[1].m_obj;
lean_object* v___f_3768_ = stack[2].m_obj;
lean_object* v___y_3770_ = stack[4].m_obj;
lean_object* v___y_3771_ = stack[5].m_obj;
lean_object* v_res_3828_;
v_res_3828_ = l_Lake_LoggerIO_instMonadLiftLogIO___lam__2(v___x_3766_, v___f_3767_, v___f_3768_, lean_box(0), v___y_3770_, v___y_3771_);
stack->m_obj
 = v_res_3828_;
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__2___boxed(lean_object* v___x_3829_, lean_object* v___f_3830_, lean_object* v___f_3831_, lean_object* v_00_u03b1_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_){
_start:
{
lean_object* v_res_3836_; 
v_res_3836_ = l_Lake_LoggerIO_instMonadLiftLogIO___lam__2(v___x_3829_, v___f_3830_, v___f_3831_, v_00_u03b1_3832_, v___y_3833_, v___y_3834_);
lean_dec_ref(v___y_3834_);
return v_res_3836_;
}
}
static lean_object* _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__1(void){
_start:
{
lean_object* v___x_3838_; 
v___x_3838_ = l_instMonadEIO___redArg();
return v___x_3838_;
}
}
static lean_object* _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__2(void){
_start:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; 
v___x_3839_ = lean_obj_once(&l_Lake_LoggerIO_instMonadLiftLogIO___closed__1, &l_Lake_LoggerIO_instMonadLiftLogIO___closed__1_once, _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__1);
v___x_3840_ = l_ReaderT_instMonad___redArg(v___x_3839_);
return v___x_3840_;
}
}
static lean_object* _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__3(void){
_start:
{
lean_object* v___f_3841_; lean_object* v___x_3842_; lean_object* v___f_3843_; 
v___f_3841_ = ((lean_object*)(l_Lake_LoggerIO_instMonadLiftLogIO___closed__0));
v___x_3842_ = lean_obj_once(&l_Lake_LoggerIO_instMonadLiftLogIO___closed__2, &l_Lake_LoggerIO_instMonadLiftLogIO___closed__2_once, _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__2);
v___f_3843_ = lean_alloc_closure((void*)(l_Lake_LoggerIO_instMonadLiftLogIO___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3843_, 0, v___x_3842_);
lean_closure_set(v___f_3843_, 1, v___f_3841_);
lean_closure_set(v___f_3843_, 2, v___f_3841_);
return v___f_3843_;
}
}
static lean_object* _init_l_Lake_LoggerIO_instMonadLiftLogIO(void){
_start:
{
lean_object* v___f_3844_; 
v___f_3844_ = lean_obj_once(&l_Lake_LoggerIO_instMonadLiftLogIO___closed__3, &l_Lake_LoggerIO_instMonadLiftLogIO___closed__3_once, _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__3);
return v___f_3844_;
}
}
lean_object* l_Lake_LoggerIO_toBaseIO___redArg___lam__0(lean_object* v_val_3845_, uint8_t v_outLv_3846_, uint8_t v_val_3847_, lean_object* v_e_3848_){
_start:
{
lean_object* v___x_3850_; 
v___x_3850_ = l_Lake_logToStream(v_e_3848_, v_val_3845_, v_outLv_3846_, v_val_3847_);
return v___x_3850_;
}
}
LEAN_EXPORT void l_Lake_LoggerIO_toBaseIO___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_3845_ = stack[0].m_obj;
uint8_t v_outLv_3846_ = stack[1].m_num;
uint8_t v_val_3847_ = stack[2].m_num;
lean_object* v_e_3848_ = stack[3].m_obj;
lean_object* v_res_3851_;
v_res_3851_ = l_Lake_LoggerIO_toBaseIO___redArg___lam__0(v_val_3845_, v_outLv_3846_, v_val_3847_, v_e_3848_);
stack->m_obj
 = v_res_3851_;
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg___lam__0___boxed(lean_object* v_val_3852_, lean_object* v_outLv_3853_, lean_object* v_val_3854_, lean_object* v_e_3855_, lean_object* v___y_3856_){
_start:
{
uint8_t v_outLv_boxed_3857_; uint8_t v_val_178__boxed_3858_; lean_object* v_res_3859_; 
v_outLv_boxed_3857_ = lean_unbox(v_outLv_3853_);
v_val_178__boxed_3858_ = lean_unbox(v_val_3854_);
v_res_3859_ = l_Lake_LoggerIO_toBaseIO___redArg___lam__0(v_val_3852_, v_outLv_boxed_3857_, v_val_178__boxed_3858_, v_e_3855_);
lean_dec_ref(v_e_3855_);
return v_res_3859_;
}
}
lean_object* l_Lake_LoggerIO_toBaseIO___redArg(lean_object* v_self_3860_, lean_object* v_cfg_3861_){
_start:
{
uint8_t v_outLv_3863_; uint8_t v_ansiMode_3864_; lean_object* v_out_3865_; lean_object* v___x_3866_; uint8_t v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___f_3870_; lean_object* v___x_3871_; 
v_outLv_3863_ = lean_ctor_get_uint8(v_cfg_3861_, sizeof(void*)*1 + 1);
v_ansiMode_3864_ = lean_ctor_get_uint8(v_cfg_3861_, sizeof(void*)*1 + 2);
v_out_3865_ = lean_ctor_get(v_cfg_3861_, 0);
v___x_3866_ = l_Lake_OutStream_get(v_out_3865_);
lean_inc_ref(v___x_3866_);
v___x_3867_ = l_Lake_AnsiMode_isEnabled(v___x_3866_, v_ansiMode_3864_);
v___x_3868_ = lean_box(v_outLv_3863_);
v___x_3869_ = lean_box(v___x_3867_);
v___f_3870_ = lean_alloc_closure((void*)(l_Lake_LoggerIO_toBaseIO___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3870_, 0, v___x_3866_);
lean_closure_set(v___f_3870_, 1, v___x_3868_);
lean_closure_set(v___f_3870_, 2, v___x_3869_);
v___x_3871_ = lean_apply_2(v_self_3860_, v___f_3870_, lean_box(0));
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3879_; 
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3874_ = v___x_3871_;
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3871_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3877_; 
if (v_isShared_3875_ == 0)
{
lean_ctor_set_tag(v___x_3874_, 1);
v___x_3877_ = v___x_3874_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_a_3872_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
}
else
{
lean_object* v___x_3880_; 
lean_dec_ref_known(v___x_3871_, 1);
v___x_3880_ = lean_box(0);
return v___x_3880_;
}
}
}
LEAN_EXPORT void l_Lake_LoggerIO_toBaseIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_3860_ = stack[0].m_obj;
lean_object* v_cfg_3861_ = stack[1].m_obj;
lean_object* v_res_3881_;
v_res_3881_ = l_Lake_LoggerIO_toBaseIO___redArg(v_self_3860_, v_cfg_3861_);
stack->m_obj
 = v_res_3881_;
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg___boxed(lean_object* v_self_3882_, lean_object* v_cfg_3883_, lean_object* v_a_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l_Lake_LoggerIO_toBaseIO___redArg(v_self_3882_, v_cfg_3883_);
lean_dec_ref(v_cfg_3883_);
return v_res_3885_;
}
}
lean_object* l_Lake_LoggerIO_toBaseIO(lean_object* v_00_u03b1_3886_, lean_object* v_self_3887_, lean_object* v_cfg_3888_){
_start:
{
uint8_t v_outLv_3890_; uint8_t v_ansiMode_3891_; lean_object* v_out_3892_; lean_object* v___x_3893_; uint8_t v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___f_3897_; lean_object* v___x_3898_; 
v_outLv_3890_ = lean_ctor_get_uint8(v_cfg_3888_, sizeof(void*)*1 + 1);
v_ansiMode_3891_ = lean_ctor_get_uint8(v_cfg_3888_, sizeof(void*)*1 + 2);
v_out_3892_ = lean_ctor_get(v_cfg_3888_, 0);
v___x_3893_ = l_Lake_OutStream_get(v_out_3892_);
lean_inc_ref(v___x_3893_);
v___x_3894_ = l_Lake_AnsiMode_isEnabled(v___x_3893_, v_ansiMode_3891_);
v___x_3895_ = lean_box(v_outLv_3890_);
v___x_3896_ = lean_box(v___x_3894_);
v___f_3897_ = lean_alloc_closure((void*)(l_Lake_LoggerIO_toBaseIO___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3897_, 0, v___x_3893_);
lean_closure_set(v___f_3897_, 1, v___x_3895_);
lean_closure_set(v___f_3897_, 2, v___x_3896_);
v___x_3898_ = lean_apply_2(v_self_3887_, v___f_3897_, lean_box(0));
if (lean_obj_tag(v___x_3898_) == 0)
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3906_; 
v_a_3899_ = lean_ctor_get(v___x_3898_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3901_ = v___x_3898_;
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3898_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3904_; 
if (v_isShared_3902_ == 0)
{
lean_ctor_set_tag(v___x_3901_, 1);
v___x_3904_ = v___x_3901_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_a_3899_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
else
{
lean_object* v___x_3907_; 
lean_dec_ref_known(v___x_3898_, 1);
v___x_3907_ = lean_box(0);
return v___x_3907_;
}
}
}
LEAN_EXPORT void l_Lake_LoggerIO_toBaseIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_3887_ = stack[1].m_obj;
lean_object* v_cfg_3888_ = stack[2].m_obj;
lean_object* v_res_3908_;
v_res_3908_ = l_Lake_LoggerIO_toBaseIO(lean_box(0), v_self_3887_, v_cfg_3888_);
stack->m_obj
 = v_res_3908_;
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___boxed(lean_object* v_00_u03b1_3909_, lean_object* v_self_3910_, lean_object* v_cfg_3911_, lean_object* v_a_3912_){
_start:
{
lean_object* v_res_3913_; 
v_res_3913_ = l_Lake_LoggerIO_toBaseIO(v_00_u03b1_3909_, v_self_3910_, v_cfg_3911_);
lean_dec_ref(v_cfg_3911_);
return v_res_3913_;
}
}
lean_object* l_Lake_LoggerIO_captureLog___redArg___lam__0(lean_object* v_val_3914_, lean_object* v_e_3915_){
_start:
{
lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
v___x_3917_ = lean_st_ref_take(v_val_3914_);
v___x_3918_ = lean_array_push(v___x_3917_, v_e_3915_);
v___x_3919_ = lean_st_ref_put(v_val_3914_, v___x_3918_);
return v___x_3919_;
}
}
LEAN_EXPORT void l_Lake_LoggerIO_captureLog___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_3914_ = stack[0].m_obj;
lean_object* v_e_3915_ = stack[1].m_obj;
lean_object* v_res_3920_;
v_res_3920_ = l_Lake_LoggerIO_captureLog___redArg___lam__0(v_val_3914_, v_e_3915_);
stack->m_obj
 = v_res_3920_;
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg___lam__0___boxed(lean_object* v_val_3921_, lean_object* v_e_3922_, lean_object* v___y_3923_){
_start:
{
lean_object* v_res_3924_; 
v_res_3924_ = l_Lake_LoggerIO_captureLog___redArg___lam__0(v_val_3921_, v_e_3922_);
lean_dec(v_val_3921_);
return v_res_3924_;
}
}
lean_object* l_Lake_LoggerIO_captureLog___redArg(lean_object* v_self_3925_){
_start:
{
lean_object* v___y_3928_; lean_object* v___y_3929_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v_val_3934_; lean_object* v___f_3945_; lean_object* v___x_3946_; 
v___x_3931_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3932_ = lean_st_mk_ref(v___x_3931_);
lean_inc(v___x_3932_);
v___f_3945_ = lean_alloc_closure((void*)(l_Lake_LoggerIO_captureLog___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3945_, 0, v___x_3932_);
v___x_3946_ = lean_apply_2(v_self_3925_, v___f_3945_, lean_box(0));
if (lean_obj_tag(v___x_3946_) == 0)
{
lean_object* v_a_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3954_; 
v_a_3947_ = lean_ctor_get(v___x_3946_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3946_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3949_ = v___x_3946_;
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_a_3947_);
lean_dec(v___x_3946_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3952_; 
if (v_isShared_3950_ == 0)
{
lean_ctor_set_tag(v___x_3949_, 1);
v___x_3952_ = v___x_3949_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3947_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
v_val_3934_ = v___x_3952_;
goto v___jp_3933_;
}
}
}
else
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
v_a_3955_ = lean_ctor_get(v___x_3946_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3946_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v___x_3946_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3946_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
lean_ctor_set_tag(v___x_3957_, 0);
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
v_val_3934_ = v___x_3960_;
goto v___jp_3933_;
}
}
}
v___jp_3927_:
{
lean_object* v___x_3930_; 
v___x_3930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3930_, 0, v___y_3929_);
lean_ctor_set(v___x_3930_, 1, v___y_3928_);
return v___x_3930_;
}
v___jp_3933_:
{
lean_object* v___x_3935_; 
v___x_3935_ = lean_st_ref_get(v___x_3932_);
lean_dec(v___x_3932_);
if (lean_obj_tag(v_val_3934_) == 0)
{
lean_object* v___x_3936_; 
lean_dec_ref_known(v_val_3934_, 1);
v___x_3936_ = lean_box(0);
v___y_3928_ = v___x_3935_;
v___y_3929_ = v___x_3936_;
goto v___jp_3927_;
}
else
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3944_; 
v_a_3937_ = lean_ctor_get(v_val_3934_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v_val_3934_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3939_ = v_val_3934_;
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v_val_3934_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3942_; 
if (v_isShared_3940_ == 0)
{
v___x_3942_ = v___x_3939_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_a_3937_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
v___y_3928_ = v___x_3935_;
v___y_3929_ = v___x_3942_;
goto v___jp_3927_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_LoggerIO_captureLog___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_3925_ = stack[0].m_obj;
lean_object* v_res_3963_;
v_res_3963_ = l_Lake_LoggerIO_captureLog___redArg(v_self_3925_);
stack->m_obj
 = v_res_3963_;
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg___boxed(lean_object* v_self_3964_, lean_object* v_a_3965_){
_start:
{
lean_object* v_res_3966_; 
v_res_3966_ = l_Lake_LoggerIO_captureLog___redArg(v_self_3964_);
return v_res_3966_;
}
}
lean_object* l_Lake_LoggerIO_captureLog(lean_object* v_00_u03b1_3967_, lean_object* v_self_3968_){
_start:
{
lean_object* v___x_3970_; 
v___x_3970_ = l_Lake_LoggerIO_captureLog___redArg(v_self_3968_);
return v___x_3970_;
}
}
LEAN_EXPORT void l_Lake_LoggerIO_captureLog_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_3968_ = stack[1].m_obj;
lean_object* v_res_3971_;
v_res_3971_ = l_Lake_LoggerIO_captureLog(lean_box(0), v_self_3968_);
stack->m_obj
 = v_res_3971_;
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___boxed(lean_object* v_00_u03b1_3972_, lean_object* v_self_3973_, lean_object* v_a_3974_){
_start:
{
lean_object* v_res_3975_; 
v_res_3975_ = l_Lake_LoggerIO_captureLog(v_00_u03b1_3972_, v_self_3973_);
return v_res_3975_;
}
}
lean_object* l_Lake_LoggerIO_run_x3f___redArg(lean_object* v_self_3976_){
_start:
{
lean_object* v___x_3978_; 
v___x_3978_ = l_Lake_LoggerIO_captureLog___redArg(v_self_3976_);
return v___x_3978_;
}
}
LEAN_EXPORT void l_Lake_LoggerIO_run_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_3976_ = stack[0].m_obj;
lean_object* v_res_3979_;
v_res_3979_ = l_Lake_LoggerIO_run_x3f___redArg(v_self_3976_);
stack->m_obj
 = v_res_3979_;
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f___redArg___boxed(lean_object* v_self_3980_, lean_object* v_a_3981_){
_start:
{
lean_object* v_res_3982_; 
v_res_3982_ = l_Lake_LoggerIO_run_x3f___redArg(v_self_3980_);
return v_res_3982_;
}
}
lean_object* l_Lake_LoggerIO_run_x3f(lean_object* v_00_u03b1_3983_, lean_object* v_self_3984_){
_start:
{
lean_object* v___x_3986_; 
v___x_3986_ = l_Lake_LoggerIO_captureLog___redArg(v_self_3984_);
return v___x_3986_;
}
}
LEAN_EXPORT void l_Lake_LoggerIO_run_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_3984_ = stack[1].m_obj;
lean_object* v_res_3987_;
v_res_3987_ = l_Lake_LoggerIO_run_x3f(lean_box(0), v_self_3984_);
stack->m_obj
 = v_res_3987_;
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f___boxed(lean_object* v_00_u03b1_3988_, lean_object* v_self_3989_, lean_object* v_a_3990_){
_start:
{
lean_object* v_res_3991_; 
v_res_3991_ = l_Lake_LoggerIO_run_x3f(v_00_u03b1_3988_, v_self_3989_);
return v_res_3991_;
}
}
lean_object* l_Lake_LoggerIO_run_x3f_x27___redArg(lean_object* v_self_3992_, lean_object* v_logger_3993_){
_start:
{
lean_object* v___x_3995_; 
v___x_3995_ = lean_apply_2(v_self_3992_, v_logger_3993_, lean_box(0));
if (lean_obj_tag(v___x_3995_) == 0)
{
lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4003_; 
v_a_3996_ = lean_ctor_get(v___x_3995_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3995_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3998_ = v___x_3995_;
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_dec(v___x_3995_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4001_; 
if (v_isShared_3999_ == 0)
{
lean_ctor_set_tag(v___x_3998_, 1);
v___x_4001_ = v___x_3998_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3996_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
else
{
lean_object* v___x_4004_; 
lean_dec_ref_known(v___x_3995_, 1);
v___x_4004_ = lean_box(0);
return v___x_4004_;
}
}
}
LEAN_EXPORT void l_Lake_LoggerIO_run_x3f_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_3992_ = stack[0].m_obj;
lean_object* v_logger_3993_ = stack[1].m_obj;
lean_object* v_res_4005_;
v_res_4005_ = l_Lake_LoggerIO_run_x3f_x27___redArg(v_self_3992_, v_logger_3993_);
stack->m_obj
 = v_res_4005_;
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27___redArg___boxed(lean_object* v_self_4006_, lean_object* v_logger_4007_, lean_object* v_a_4008_){
_start:
{
lean_object* v_res_4009_; 
v_res_4009_ = l_Lake_LoggerIO_run_x3f_x27___redArg(v_self_4006_, v_logger_4007_);
return v_res_4009_;
}
}
lean_object* l_Lake_LoggerIO_run_x3f_x27(lean_object* v_00_u03b1_4010_, lean_object* v_self_4011_, lean_object* v_logger_4012_){
_start:
{
lean_object* v___x_4014_; 
v___x_4014_ = lean_apply_2(v_self_4011_, v_logger_4012_, lean_box(0));
if (lean_obj_tag(v___x_4014_) == 0)
{
lean_object* v_a_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4022_; 
v_a_4015_ = lean_ctor_get(v___x_4014_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4017_ = v___x_4014_;
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_a_4015_);
lean_dec(v___x_4014_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4020_; 
if (v_isShared_4018_ == 0)
{
lean_ctor_set_tag(v___x_4017_, 1);
v___x_4020_ = v___x_4017_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_a_4015_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
}
else
{
lean_object* v___x_4023_; 
lean_dec_ref_known(v___x_4014_, 1);
v___x_4023_ = lean_box(0);
return v___x_4023_;
}
}
}
LEAN_EXPORT void l_Lake_LoggerIO_run_x3f_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_4011_ = stack[1].m_obj;
lean_object* v_logger_4012_ = stack[2].m_obj;
lean_object* v_res_4024_;
v_res_4024_ = l_Lake_LoggerIO_run_x3f_x27(lean_box(0), v_self_4011_, v_logger_4012_);
stack->m_obj
 = v_res_4024_;
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27___boxed(lean_object* v_00_u03b1_4025_, lean_object* v_self_4026_, lean_object* v_logger_4027_, lean_object* v_a_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l_Lake_LoggerIO_run_x3f_x27(v_00_u03b1_4025_, v_self_4026_, v_logger_4027_);
return v_res_4029_;
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
