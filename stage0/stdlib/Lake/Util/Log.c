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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lake_Verbosity_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lake_Verbosity_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lake_Verbosity_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_quiet_elim___redArg(lean_object* v_quiet_22_){
_start:
{
lean_inc(v_quiet_22_);
return v_quiet_22_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_quiet_elim___redArg___boxed(lean_object* v_quiet_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lake_Verbosity_quiet_elim___redArg(v_quiet_23_);
lean_dec(v_quiet_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_quiet_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_quiet_28_){
_start:
{
lean_inc(v_quiet_28_);
return v_quiet_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_quiet_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_quiet_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lake_Verbosity_quiet_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_quiet_32_);
lean_dec(v_quiet_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_normal_elim___redArg(lean_object* v_normal_35_){
_start:
{
lean_inc(v_normal_35_);
return v_normal_35_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_normal_elim___redArg___boxed(lean_object* v_normal_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lake_Verbosity_normal_elim___redArg(v_normal_36_);
lean_dec(v_normal_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_normal_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_normal_41_){
_start:
{
lean_inc(v_normal_41_);
return v_normal_41_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_normal_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_normal_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lake_Verbosity_normal_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_normal_45_);
lean_dec(v_normal_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_verbose_elim___redArg(lean_object* v_verbose_48_){
_start:
{
lean_inc(v_verbose_48_);
return v_verbose_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_verbose_elim___redArg___boxed(lean_object* v_verbose_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lake_Verbosity_verbose_elim___redArg(v_verbose_49_);
lean_dec(v_verbose_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_verbose_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_verbose_54_){
_start:
{
lean_inc(v_verbose_54_);
return v_verbose_54_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_verbose_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_verbose_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lake_Verbosity_verbose_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_verbose_58_);
lean_dec(v_verbose_58_);
return v_res_60_;
}
}
static lean_object* _init_l_Lake_instReprVerbosity_repr___closed__6(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_unsigned_to_nat(2u);
v___x_71_ = lean_nat_to_int(v___x_70_);
return v___x_71_;
}
}
static lean_object* _init_l_Lake_instReprVerbosity_repr___closed__7(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_to_int(v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerbosity_repr(uint8_t v_x_74_, lean_object* v_prec_75_){
_start:
{
lean_object* v___y_77_; lean_object* v___y_84_; lean_object* v___y_91_; 
switch(v_x_74_)
{
case 0:
{
lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = lean_unsigned_to_nat(1024u);
v___x_98_ = lean_nat_dec_le(v___x_97_, v_prec_75_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; 
v___x_99_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_77_ = v___x_99_;
goto v___jp_76_;
}
else
{
lean_object* v___x_100_; 
v___x_100_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_77_ = v___x_100_;
goto v___jp_76_;
}
}
case 1:
{
lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_101_ = lean_unsigned_to_nat(1024u);
v___x_102_ = lean_nat_dec_le(v___x_101_, v_prec_75_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; 
v___x_103_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_84_ = v___x_103_;
goto v___jp_83_;
}
else
{
lean_object* v___x_104_; 
v___x_104_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_84_ = v___x_104_;
goto v___jp_83_;
}
}
default: 
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = lean_unsigned_to_nat(1024u);
v___x_106_ = lean_nat_dec_le(v___x_105_, v_prec_75_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_91_ = v___x_107_;
goto v___jp_90_;
}
else
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_91_ = v___x_108_;
goto v___jp_90_;
}
}
}
v___jp_76_:
{
lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_78_ = ((lean_object*)(l_Lake_instReprVerbosity_repr___closed__1));
lean_inc(v___y_77_);
v___x_79_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_79_, 0, v___y_77_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v___x_80_ = 0;
v___x_81_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_81_, 0, v___x_79_);
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*1, v___x_80_);
v___x_82_ = l_Repr_addAppParen(v___x_81_, v_prec_75_);
return v___x_82_;
}
v___jp_83_:
{
lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_85_ = ((lean_object*)(l_Lake_instReprVerbosity_repr___closed__3));
lean_inc(v___y_84_);
v___x_86_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_86_, 0, v___y_84_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = 0;
v___x_88_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_88_, 0, v___x_86_);
lean_ctor_set_uint8(v___x_88_, sizeof(void*)*1, v___x_87_);
v___x_89_ = l_Repr_addAppParen(v___x_88_, v_prec_75_);
return v___x_89_;
}
v___jp_90_:
{
lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_92_ = ((lean_object*)(l_Lake_instReprVerbosity_repr___closed__5));
lean_inc(v___y_91_);
v___x_93_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_93_, 0, v___y_91_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = 0;
v___x_95_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_95_, 0, v___x_93_);
lean_ctor_set_uint8(v___x_95_, sizeof(void*)*1, v___x_94_);
v___x_96_ = l_Repr_addAppParen(v___x_95_, v_prec_75_);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerbosity_repr___boxed(lean_object* v_x_109_, lean_object* v_prec_110_){
_start:
{
uint8_t v_x_171__boxed_111_; lean_object* v_res_112_; 
v_x_171__boxed_111_ = lean_unbox(v_x_109_);
v_res_112_ = l_Lake_instReprVerbosity_repr(v_x_171__boxed_111_, v_prec_110_);
lean_dec(v_prec_110_);
return v_res_112_;
}
}
LEAN_EXPORT uint8_t l_Lake_Verbosity_ofNat(lean_object* v_n_115_){
_start:
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = lean_nat_dec_le(v_n_115_, v___x_116_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = lean_unsigned_to_nat(1u);
v___x_119_ = lean_nat_dec_le(v_n_115_, v___x_118_);
if (v___x_119_ == 0)
{
uint8_t v___x_120_; 
v___x_120_ = 2;
return v___x_120_;
}
else
{
uint8_t v___x_121_; 
v___x_121_ = 1;
return v___x_121_;
}
}
else
{
uint8_t v___x_122_; 
v___x_122_ = 0;
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_ofNat___boxed(lean_object* v_n_123_){
_start:
{
uint8_t v_res_124_; lean_object* v_r_125_; 
v_res_124_ = l_Lake_Verbosity_ofNat(v_n_123_);
lean_dec(v_n_123_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqVerbosity(uint8_t v_x_126_, uint8_t v_y_127_){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_128_ = lean_box(v_x_126_);
v___x_129_ = lean_obj_tag_nat(v___x_128_);
lean_dec(v___x_128_);
v___x_130_ = lean_box(v_y_127_);
v___x_131_ = lean_obj_tag_nat(v___x_130_);
lean_dec(v___x_130_);
v___x_132_ = lean_nat_dec_eq(v___x_129_, v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqVerbosity___boxed(lean_object* v_x_133_, lean_object* v_y_134_){
_start:
{
uint8_t v_x_23__boxed_135_; uint8_t v_y_24__boxed_136_; uint8_t v_res_137_; lean_object* v_r_138_; 
v_x_23__boxed_135_ = lean_unbox(v_x_133_);
v_y_24__boxed_136_ = lean_unbox(v_y_134_);
v_res_137_ = l_Lake_instDecidableEqVerbosity(v_x_23__boxed_135_, v_y_24__boxed_136_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
LEAN_EXPORT uint8_t l_Lake_instOrdVerbosity_ord(uint8_t v_x_139_, uint8_t v_y_140_){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_141_ = lean_box(v_x_139_);
v___x_142_ = lean_obj_tag_nat(v___x_141_);
lean_dec(v___x_141_);
v___x_143_ = lean_box(v_y_140_);
v___x_144_ = lean_obj_tag_nat(v___x_143_);
lean_dec(v___x_143_);
v___x_145_ = lean_nat_dec_lt(v___x_142_, v___x_144_);
if (v___x_145_ == 0)
{
uint8_t v___x_146_; 
v___x_146_ = lean_nat_dec_eq(v___x_142_, v___x_144_);
if (v___x_146_ == 0)
{
uint8_t v___x_147_; 
v___x_147_ = 2;
return v___x_147_;
}
else
{
uint8_t v___x_148_; 
v___x_148_ = 1;
return v___x_148_;
}
}
else
{
uint8_t v___x_149_; 
v___x_149_ = 0;
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instOrdVerbosity_ord___boxed(lean_object* v_x_150_, lean_object* v_y_151_){
_start:
{
uint8_t v_x_33__boxed_152_; uint8_t v_y_34__boxed_153_; uint8_t v_res_154_; lean_object* v_r_155_; 
v_x_33__boxed_152_ = lean_unbox(v_x_150_);
v_y_34__boxed_153_ = lean_unbox(v_y_151_);
v_res_154_ = l_Lake_instOrdVerbosity_ord(v_x_33__boxed_152_, v_y_34__boxed_153_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
static lean_object* _init_l_Lake_instLTVerbosity(void){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = lean_box(0);
return v___x_158_;
}
}
static lean_object* _init_l_Lake_instLEVerbosity(void){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = lean_box(0);
return v___x_159_;
}
}
LEAN_EXPORT uint8_t l_Lake_instMinVerbosity___lam__0(uint8_t v_x_160_, uint8_t v_y_161_){
_start:
{
uint8_t v___x_162_; 
v___x_162_ = l_Lake_instOrdVerbosity_ord(v_x_160_, v_y_161_);
if (v___x_162_ == 2)
{
return v_y_161_;
}
else
{
return v_x_160_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMinVerbosity___lam__0___boxed(lean_object* v_x_163_, lean_object* v_y_164_){
_start:
{
uint8_t v_x_boxed_165_; uint8_t v_y_boxed_166_; uint8_t v_res_167_; lean_object* v_r_168_; 
v_x_boxed_165_ = lean_unbox(v_x_163_);
v_y_boxed_166_ = lean_unbox(v_y_164_);
v_res_167_ = l_Lake_instMinVerbosity___lam__0(v_x_boxed_165_, v_y_boxed_166_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
LEAN_EXPORT uint8_t l_Lake_instMaxVerbosity___lam__0(uint8_t v_x_171_, uint8_t v_y_172_){
_start:
{
uint8_t v___x_173_; 
v___x_173_ = l_Lake_instOrdVerbosity_ord(v_x_171_, v_y_172_);
if (v___x_173_ == 2)
{
return v_x_171_;
}
else
{
return v_y_172_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxVerbosity___lam__0___boxed(lean_object* v_x_174_, lean_object* v_y_175_){
_start:
{
uint8_t v_x_boxed_176_; uint8_t v_y_boxed_177_; uint8_t v_res_178_; lean_object* v_r_179_; 
v_x_boxed_176_ = lean_unbox(v_x_174_);
v_y_boxed_177_ = lean_unbox(v_y_175_);
v_res_178_ = l_Lake_instMaxVerbosity___lam__0(v_x_boxed_176_, v_y_boxed_177_);
v_r_179_ = lean_box(v_res_178_);
return v_r_179_;
}
}
static uint8_t _init_l_Lake_instInhabitedVerbosity(void){
_start:
{
uint8_t v___x_182_; 
v___x_182_ = 1;
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorIdx___impl(uint8_t v_x_183_){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_box(v_x_183_);
v___x_185_ = lean_obj_tag_nat(v___x_184_);
lean_dec(v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorIdx___impl___boxed(lean_object* v_x_186_){
_start:
{
uint8_t v_x_4__boxed_187_; lean_object* v_res_188_; 
v_x_4__boxed_187_ = lean_unbox(v_x_186_);
v_res_188_ = l_Lake_AnsiMode_ctorIdx___impl(v_x_4__boxed_187_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorElim___redArg(lean_object* v_k_189_){
_start:
{
lean_inc(v_k_189_);
return v_k_189_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorElim___redArg___boxed(lean_object* v_k_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lake_AnsiMode_ctorElim___redArg(v_k_190_);
lean_dec(v_k_190_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorElim(lean_object* v_motive_192_, lean_object* v_ctorIdx_193_, uint8_t v_t_194_, lean_object* v_h_195_, lean_object* v_k_196_){
_start:
{
lean_inc(v_k_196_);
return v_k_196_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorElim___boxed(lean_object* v_motive_197_, lean_object* v_ctorIdx_198_, lean_object* v_t_199_, lean_object* v_h_200_, lean_object* v_k_201_){
_start:
{
uint8_t v_t_boxed_202_; lean_object* v_res_203_; 
v_t_boxed_202_ = lean_unbox(v_t_199_);
v_res_203_ = l_Lake_AnsiMode_ctorElim(v_motive_197_, v_ctorIdx_198_, v_t_boxed_202_, v_h_200_, v_k_201_);
lean_dec(v_k_201_);
lean_dec(v_ctorIdx_198_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_auto_elim___redArg(lean_object* v_auto_204_){
_start:
{
lean_inc(v_auto_204_);
return v_auto_204_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_auto_elim___redArg___boxed(lean_object* v_auto_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lake_AnsiMode_auto_elim___redArg(v_auto_205_);
lean_dec(v_auto_205_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_auto_elim(lean_object* v_motive_207_, uint8_t v_t_208_, lean_object* v_h_209_, lean_object* v_auto_210_){
_start:
{
lean_inc(v_auto_210_);
return v_auto_210_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_auto_elim___boxed(lean_object* v_motive_211_, lean_object* v_t_212_, lean_object* v_h_213_, lean_object* v_auto_214_){
_start:
{
uint8_t v_t_boxed_215_; lean_object* v_res_216_; 
v_t_boxed_215_ = lean_unbox(v_t_212_);
v_res_216_ = l_Lake_AnsiMode_auto_elim(v_motive_211_, v_t_boxed_215_, v_h_213_, v_auto_214_);
lean_dec(v_auto_214_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ansi_elim___redArg(lean_object* v_ansi_217_){
_start:
{
lean_inc(v_ansi_217_);
return v_ansi_217_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ansi_elim___redArg___boxed(lean_object* v_ansi_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lake_AnsiMode_ansi_elim___redArg(v_ansi_218_);
lean_dec(v_ansi_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ansi_elim(lean_object* v_motive_220_, uint8_t v_t_221_, lean_object* v_h_222_, lean_object* v_ansi_223_){
_start:
{
lean_inc(v_ansi_223_);
return v_ansi_223_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ansi_elim___boxed(lean_object* v_motive_224_, lean_object* v_t_225_, lean_object* v_h_226_, lean_object* v_ansi_227_){
_start:
{
uint8_t v_t_boxed_228_; lean_object* v_res_229_; 
v_t_boxed_228_ = lean_unbox(v_t_225_);
v_res_229_ = l_Lake_AnsiMode_ansi_elim(v_motive_224_, v_t_boxed_228_, v_h_226_, v_ansi_227_);
lean_dec(v_ansi_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noAnsi_elim___redArg(lean_object* v_noAnsi_230_){
_start:
{
lean_inc(v_noAnsi_230_);
return v_noAnsi_230_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noAnsi_elim___redArg___boxed(lean_object* v_noAnsi_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lake_AnsiMode_noAnsi_elim___redArg(v_noAnsi_231_);
lean_dec(v_noAnsi_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noAnsi_elim(lean_object* v_motive_233_, uint8_t v_t_234_, lean_object* v_h_235_, lean_object* v_noAnsi_236_){
_start:
{
lean_inc(v_noAnsi_236_);
return v_noAnsi_236_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noAnsi_elim___boxed(lean_object* v_motive_237_, lean_object* v_t_238_, lean_object* v_h_239_, lean_object* v_noAnsi_240_){
_start:
{
uint8_t v_t_boxed_241_; lean_object* v_res_242_; 
v_t_boxed_241_ = lean_unbox(v_t_238_);
v_res_242_ = l_Lake_AnsiMode_noAnsi_elim(v_motive_237_, v_t_boxed_241_, v_h_239_, v_noAnsi_240_);
lean_dec(v_noAnsi_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprAnsiMode_repr(uint8_t v_x_252_, lean_object* v_prec_253_){
_start:
{
lean_object* v___y_255_; lean_object* v___y_262_; lean_object* v___y_269_; 
switch(v_x_252_)
{
case 0:
{
lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_275_ = lean_unsigned_to_nat(1024u);
v___x_276_ = lean_nat_dec_le(v___x_275_, v_prec_253_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; 
v___x_277_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_255_ = v___x_277_;
goto v___jp_254_;
}
else
{
lean_object* v___x_278_; 
v___x_278_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_255_ = v___x_278_;
goto v___jp_254_;
}
}
case 1:
{
lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_279_ = lean_unsigned_to_nat(1024u);
v___x_280_ = lean_nat_dec_le(v___x_279_, v_prec_253_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; 
v___x_281_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_262_ = v___x_281_;
goto v___jp_261_;
}
else
{
lean_object* v___x_282_; 
v___x_282_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_262_ = v___x_282_;
goto v___jp_261_;
}
}
default: 
{
lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_283_ = lean_unsigned_to_nat(1024u);
v___x_284_ = lean_nat_dec_le(v___x_283_, v_prec_253_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; 
v___x_285_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_269_ = v___x_285_;
goto v___jp_268_;
}
else
{
lean_object* v___x_286_; 
v___x_286_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_269_ = v___x_286_;
goto v___jp_268_;
}
}
}
v___jp_254_:
{
lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_256_ = ((lean_object*)(l_Lake_instReprAnsiMode_repr___closed__1));
lean_inc(v___y_255_);
v___x_257_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_257_, 0, v___y_255_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = 0;
v___x_259_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_259_, 0, v___x_257_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*1, v___x_258_);
v___x_260_ = l_Repr_addAppParen(v___x_259_, v_prec_253_);
return v___x_260_;
}
v___jp_261_:
{
lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_263_ = ((lean_object*)(l_Lake_instReprAnsiMode_repr___closed__3));
lean_inc(v___y_262_);
v___x_264_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_264_, 0, v___y_262_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = 0;
v___x_266_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_266_, 0, v___x_264_);
lean_ctor_set_uint8(v___x_266_, sizeof(void*)*1, v___x_265_);
v___x_267_ = l_Repr_addAppParen(v___x_266_, v_prec_253_);
return v___x_267_;
}
v___jp_268_:
{
lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_270_ = ((lean_object*)(l_Lake_instReprAnsiMode_repr___closed__5));
lean_inc(v___y_269_);
v___x_271_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_271_, 0, v___y_269_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
v___x_272_ = 0;
v___x_273_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_273_, 0, v___x_271_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*1, v___x_272_);
v___x_274_ = l_Repr_addAppParen(v___x_273_, v_prec_253_);
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprAnsiMode_repr___boxed(lean_object* v_x_287_, lean_object* v_prec_288_){
_start:
{
uint8_t v_x_167__boxed_289_; lean_object* v_res_290_; 
v_x_167__boxed_289_ = lean_unbox(v_x_287_);
v_res_290_ = l_Lake_instReprAnsiMode_repr(v_x_167__boxed_289_, v_prec_288_);
lean_dec(v_prec_288_);
return v_res_290_;
}
}
LEAN_EXPORT uint8_t l_Lake_AnsiMode_isEnabled(lean_object* v_out_293_, uint8_t v_x_294_){
_start:
{
switch(v_x_294_)
{
case 0:
{
lean_object* v_isTty_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v_isTty_296_ = lean_ctor_get(v_out_293_, 5);
lean_inc_ref(v_isTty_296_);
lean_dec_ref(v_out_293_);
v___x_297_ = lean_apply_1(v_isTty_296_, lean_box(0));
v___x_298_ = lean_unbox(v___x_297_);
return v___x_298_;
}
case 1:
{
uint8_t v___x_299_; 
lean_dec_ref(v_out_293_);
v___x_299_ = 1;
return v___x_299_;
}
default: 
{
uint8_t v___x_300_; 
lean_dec_ref(v_out_293_);
v___x_300_ = 0;
return v___x_300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_isEnabled___boxed(lean_object* v_out_301_, lean_object* v_x_302_, lean_object* v_a_303_){
_start:
{
uint8_t v_x_91__boxed_304_; uint8_t v_res_305_; lean_object* v_r_306_; 
v_x_91__boxed_304_ = lean_unbox(v_x_302_);
v_res_305_ = l_Lake_AnsiMode_isEnabled(v_out_301_, v_x_91__boxed_304_);
v_r_306_ = lean_box(v_res_305_);
return v_r_306_;
}
}
LEAN_EXPORT lean_object* l_Lake_Ansi_chalk(lean_object* v_colorCode_310_, lean_object* v_text_311_){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_312_ = ((lean_object*)(l_Lake_Ansi_chalk___closed__0));
v___x_313_ = lean_string_append(v___x_312_, v_colorCode_310_);
v___x_314_ = ((lean_object*)(l_Lake_Ansi_chalk___closed__1));
v___x_315_ = lean_string_append(v___x_313_, v___x_314_);
v___x_316_ = lean_string_append(v___x_315_, v_text_311_);
v___x_317_ = ((lean_object*)(l_Lake_Ansi_chalk___closed__2));
v___x_318_ = lean_string_append(v___x_316_, v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lake_Ansi_chalk___boxed(lean_object* v_colorCode_319_, lean_object* v_text_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lake_Ansi_chalk(v_colorCode_319_, v_text_320_);
lean_dec_ref(v_text_320_);
lean_dec_ref(v_colorCode_319_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorIdx___impl(lean_object* v_x_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = lean_obj_tag_nat(v_x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorIdx___impl___boxed(lean_object* v_x_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lake_OutStream_ctorIdx___impl(v_x_324_);
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
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorIdx___impl(uint8_t v_x_383_){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_box(v_x_383_);
v___x_385_ = lean_obj_tag_nat(v___x_384_);
lean_dec(v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorIdx___impl___boxed(lean_object* v_x_386_){
_start:
{
uint8_t v_x_4__boxed_387_; lean_object* v_res_388_; 
v_x_4__boxed_387_ = lean_unbox(v_x_386_);
v_res_388_ = l_Lake_LogLevel_ctorIdx___impl(v_x_4__boxed_387_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorElim___redArg(lean_object* v_k_389_){
_start:
{
lean_inc(v_k_389_);
return v_k_389_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorElim___redArg___boxed(lean_object* v_k_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lake_LogLevel_ctorElim___redArg(v_k_390_);
lean_dec(v_k_390_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorElim(lean_object* v_motive_392_, lean_object* v_ctorIdx_393_, uint8_t v_t_394_, lean_object* v_h_395_, lean_object* v_k_396_){
_start:
{
lean_inc(v_k_396_);
return v_k_396_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorElim___boxed(lean_object* v_motive_397_, lean_object* v_ctorIdx_398_, lean_object* v_t_399_, lean_object* v_h_400_, lean_object* v_k_401_){
_start:
{
uint8_t v_t_boxed_402_; lean_object* v_res_403_; 
v_t_boxed_402_ = lean_unbox(v_t_399_);
v_res_403_ = l_Lake_LogLevel_ctorElim(v_motive_397_, v_ctorIdx_398_, v_t_boxed_402_, v_h_400_, v_k_401_);
lean_dec(v_k_401_);
lean_dec(v_ctorIdx_398_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_trace_elim___redArg(lean_object* v_trace_404_){
_start:
{
lean_inc(v_trace_404_);
return v_trace_404_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_trace_elim___redArg___boxed(lean_object* v_trace_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lake_LogLevel_trace_elim___redArg(v_trace_405_);
lean_dec(v_trace_405_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_trace_elim(lean_object* v_motive_407_, uint8_t v_t_408_, lean_object* v_h_409_, lean_object* v_trace_410_){
_start:
{
lean_inc(v_trace_410_);
return v_trace_410_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_trace_elim___boxed(lean_object* v_motive_411_, lean_object* v_t_412_, lean_object* v_h_413_, lean_object* v_trace_414_){
_start:
{
uint8_t v_t_boxed_415_; lean_object* v_res_416_; 
v_t_boxed_415_ = lean_unbox(v_t_412_);
v_res_416_ = l_Lake_LogLevel_trace_elim(v_motive_411_, v_t_boxed_415_, v_h_413_, v_trace_414_);
lean_dec(v_trace_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_info_elim___redArg(lean_object* v_info_417_){
_start:
{
lean_inc(v_info_417_);
return v_info_417_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_info_elim___redArg___boxed(lean_object* v_info_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lake_LogLevel_info_elim___redArg(v_info_418_);
lean_dec(v_info_418_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_info_elim(lean_object* v_motive_420_, uint8_t v_t_421_, lean_object* v_h_422_, lean_object* v_info_423_){
_start:
{
lean_inc(v_info_423_);
return v_info_423_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_info_elim___boxed(lean_object* v_motive_424_, lean_object* v_t_425_, lean_object* v_h_426_, lean_object* v_info_427_){
_start:
{
uint8_t v_t_boxed_428_; lean_object* v_res_429_; 
v_t_boxed_428_ = lean_unbox(v_t_425_);
v_res_429_ = l_Lake_LogLevel_info_elim(v_motive_424_, v_t_boxed_428_, v_h_426_, v_info_427_);
lean_dec(v_info_427_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_warning_elim___redArg(lean_object* v_warning_430_){
_start:
{
lean_inc(v_warning_430_);
return v_warning_430_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_warning_elim___redArg___boxed(lean_object* v_warning_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lake_LogLevel_warning_elim___redArg(v_warning_431_);
lean_dec(v_warning_431_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_warning_elim(lean_object* v_motive_433_, uint8_t v_t_434_, lean_object* v_h_435_, lean_object* v_warning_436_){
_start:
{
lean_inc(v_warning_436_);
return v_warning_436_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_warning_elim___boxed(lean_object* v_motive_437_, lean_object* v_t_438_, lean_object* v_h_439_, lean_object* v_warning_440_){
_start:
{
uint8_t v_t_boxed_441_; lean_object* v_res_442_; 
v_t_boxed_441_ = lean_unbox(v_t_438_);
v_res_442_ = l_Lake_LogLevel_warning_elim(v_motive_437_, v_t_boxed_441_, v_h_439_, v_warning_440_);
lean_dec(v_warning_440_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_error_elim___redArg(lean_object* v_error_443_){
_start:
{
lean_inc(v_error_443_);
return v_error_443_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_error_elim___redArg___boxed(lean_object* v_error_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lake_LogLevel_error_elim___redArg(v_error_444_);
lean_dec(v_error_444_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_error_elim(lean_object* v_motive_446_, uint8_t v_t_447_, lean_object* v_h_448_, lean_object* v_error_449_){
_start:
{
lean_inc(v_error_449_);
return v_error_449_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_error_elim___boxed(lean_object* v_motive_450_, lean_object* v_t_451_, lean_object* v_h_452_, lean_object* v_error_453_){
_start:
{
uint8_t v_t_boxed_454_; lean_object* v_res_455_; 
v_t_boxed_454_ = lean_unbox(v_t_451_);
v_res_455_ = l_Lake_LogLevel_error_elim(v_motive_450_, v_t_boxed_454_, v_h_452_, v_error_453_);
lean_dec(v_error_453_);
return v_res_455_;
}
}
static uint8_t _init_l_Lake_instInhabitedLogLevel_default(void){
_start:
{
uint8_t v___x_456_; 
v___x_456_ = 0;
return v___x_456_;
}
}
static uint8_t _init_l_Lake_instInhabitedLogLevel(void){
_start:
{
uint8_t v___x_457_; 
v___x_457_ = 0;
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLogLevel_repr(uint8_t v_x_470_, lean_object* v_prec_471_){
_start:
{
lean_object* v___y_473_; lean_object* v___y_480_; lean_object* v___y_487_; lean_object* v___y_494_; 
switch(v_x_470_)
{
case 0:
{
lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_500_ = lean_unsigned_to_nat(1024u);
v___x_501_ = lean_nat_dec_le(v___x_500_, v_prec_471_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; 
v___x_502_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_473_ = v___x_502_;
goto v___jp_472_;
}
else
{
lean_object* v___x_503_; 
v___x_503_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_473_ = v___x_503_;
goto v___jp_472_;
}
}
case 1:
{
lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_504_ = lean_unsigned_to_nat(1024u);
v___x_505_ = lean_nat_dec_le(v___x_504_, v_prec_471_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; 
v___x_506_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_480_ = v___x_506_;
goto v___jp_479_;
}
else
{
lean_object* v___x_507_; 
v___x_507_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_480_ = v___x_507_;
goto v___jp_479_;
}
}
case 2:
{
lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_508_ = lean_unsigned_to_nat(1024u);
v___x_509_ = lean_nat_dec_le(v___x_508_, v_prec_471_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; 
v___x_510_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_487_ = v___x_510_;
goto v___jp_486_;
}
else
{
lean_object* v___x_511_; 
v___x_511_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_487_ = v___x_511_;
goto v___jp_486_;
}
}
default: 
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = lean_unsigned_to_nat(1024u);
v___x_513_ = lean_nat_dec_le(v___x_512_, v_prec_471_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; 
v___x_514_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_494_ = v___x_514_;
goto v___jp_493_;
}
else
{
lean_object* v___x_515_; 
v___x_515_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_494_ = v___x_515_;
goto v___jp_493_;
}
}
}
v___jp_472_:
{
lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_474_ = ((lean_object*)(l_Lake_instReprLogLevel_repr___closed__1));
lean_inc(v___y_473_);
v___x_475_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_475_, 0, v___y_473_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
v___x_476_ = 0;
v___x_477_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_477_, 0, v___x_475_);
lean_ctor_set_uint8(v___x_477_, sizeof(void*)*1, v___x_476_);
v___x_478_ = l_Repr_addAppParen(v___x_477_, v_prec_471_);
return v___x_478_;
}
v___jp_479_:
{
lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_481_ = ((lean_object*)(l_Lake_instReprLogLevel_repr___closed__3));
lean_inc(v___y_480_);
v___x_482_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_482_, 0, v___y_480_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
v___x_483_ = 0;
v___x_484_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_484_, 0, v___x_482_);
lean_ctor_set_uint8(v___x_484_, sizeof(void*)*1, v___x_483_);
v___x_485_ = l_Repr_addAppParen(v___x_484_, v_prec_471_);
return v___x_485_;
}
v___jp_486_:
{
lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_488_ = ((lean_object*)(l_Lake_instReprLogLevel_repr___closed__5));
lean_inc(v___y_487_);
v___x_489_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_489_, 0, v___y_487_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = 0;
v___x_491_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_491_, 0, v___x_489_);
lean_ctor_set_uint8(v___x_491_, sizeof(void*)*1, v___x_490_);
v___x_492_ = l_Repr_addAppParen(v___x_491_, v_prec_471_);
return v___x_492_;
}
v___jp_493_:
{
lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_495_ = ((lean_object*)(l_Lake_instReprLogLevel_repr___closed__7));
lean_inc(v___y_494_);
v___x_496_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_496_, 0, v___y_494_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
v___x_497_ = 0;
v___x_498_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_498_, 0, v___x_496_);
lean_ctor_set_uint8(v___x_498_, sizeof(void*)*1, v___x_497_);
v___x_499_ = l_Repr_addAppParen(v___x_498_, v_prec_471_);
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLogLevel_repr___boxed(lean_object* v_x_516_, lean_object* v_prec_517_){
_start:
{
uint8_t v_x_221__boxed_518_; lean_object* v_res_519_; 
v_x_221__boxed_518_ = lean_unbox(v_x_516_);
v_res_519_ = l_Lake_instReprLogLevel_repr(v_x_221__boxed_518_, v_prec_517_);
lean_dec(v_prec_517_);
return v_res_519_;
}
}
LEAN_EXPORT uint8_t l_Lake_LogLevel_ofNat(lean_object* v_n_522_){
_start:
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = lean_nat_dec_le(v_n_522_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_525_ = lean_unsigned_to_nat(2u);
v___x_526_ = lean_nat_dec_le(v_n_522_, v___x_525_);
if (v___x_526_ == 0)
{
uint8_t v___x_527_; 
v___x_527_ = 3;
return v___x_527_;
}
else
{
uint8_t v___x_528_; 
v___x_528_ = 2;
return v___x_528_;
}
}
else
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = lean_nat_dec_le(v_n_522_, v___x_529_);
if (v___x_530_ == 0)
{
uint8_t v___x_531_; 
v___x_531_ = 1;
return v___x_531_;
}
else
{
uint8_t v___x_532_; 
v___x_532_ = 0;
return v___x_532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ofNat___boxed(lean_object* v_n_533_){
_start:
{
uint8_t v_res_534_; lean_object* v_r_535_; 
v_res_534_ = l_Lake_LogLevel_ofNat(v_n_533_);
lean_dec(v_n_533_);
v_r_535_ = lean_box(v_res_534_);
return v_r_535_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqLogLevel(uint8_t v_x_536_, uint8_t v_y_537_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_538_ = lean_box(v_x_536_);
v___x_539_ = lean_obj_tag_nat(v___x_538_);
lean_dec(v___x_538_);
v___x_540_ = lean_box(v_y_537_);
v___x_541_ = lean_obj_tag_nat(v___x_540_);
lean_dec(v___x_540_);
v___x_542_ = lean_nat_dec_eq(v___x_539_, v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqLogLevel___boxed(lean_object* v_x_543_, lean_object* v_y_544_){
_start:
{
uint8_t v_x_23__boxed_545_; uint8_t v_y_24__boxed_546_; uint8_t v_res_547_; lean_object* v_r_548_; 
v_x_23__boxed_545_ = lean_unbox(v_x_543_);
v_y_24__boxed_546_ = lean_unbox(v_y_544_);
v_res_547_ = l_Lake_instDecidableEqLogLevel(v_x_23__boxed_545_, v_y_24__boxed_546_);
v_r_548_ = lean_box(v_res_547_);
return v_r_548_;
}
}
LEAN_EXPORT uint8_t l_Lake_instOrdLogLevel_ord(uint8_t v_x_549_, uint8_t v_y_550_){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_551_ = lean_box(v_x_549_);
v___x_552_ = lean_obj_tag_nat(v___x_551_);
lean_dec(v___x_551_);
v___x_553_ = lean_box(v_y_550_);
v___x_554_ = lean_obj_tag_nat(v___x_553_);
lean_dec(v___x_553_);
v___x_555_ = lean_nat_dec_lt(v___x_552_, v___x_554_);
if (v___x_555_ == 0)
{
uint8_t v___x_556_; 
v___x_556_ = lean_nat_dec_eq(v___x_552_, v___x_554_);
if (v___x_556_ == 0)
{
uint8_t v___x_557_; 
v___x_557_ = 2;
return v___x_557_;
}
else
{
uint8_t v___x_558_; 
v___x_558_ = 1;
return v___x_558_;
}
}
else
{
uint8_t v___x_559_; 
v___x_559_ = 0;
return v___x_559_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instOrdLogLevel_ord___boxed(lean_object* v_x_560_, lean_object* v_y_561_){
_start:
{
uint8_t v_x_33__boxed_562_; uint8_t v_y_34__boxed_563_; uint8_t v_res_564_; lean_object* v_r_565_; 
v_x_33__boxed_562_ = lean_unbox(v_x_560_);
v_y_34__boxed_563_ = lean_unbox(v_y_561_);
v_res_564_ = l_Lake_instOrdLogLevel_ord(v_x_33__boxed_562_, v_y_34__boxed_563_);
v_r_565_ = lean_box(v_res_564_);
return v_r_565_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonLogLevel_toJson(uint8_t v_x_580_){
_start:
{
switch(v_x_580_)
{
case 0:
{
lean_object* v___x_581_; 
v___x_581_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__1));
return v___x_581_;
}
case 1:
{
lean_object* v___x_582_; 
v___x_582_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__3));
return v___x_582_;
}
case 2:
{
lean_object* v___x_583_; 
v___x_583_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__5));
return v___x_583_;
}
default: 
{
lean_object* v___x_584_; 
v___x_584_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__7));
return v___x_584_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonLogLevel_toJson___boxed(lean_object* v_x_585_){
_start:
{
uint8_t v_x_88__boxed_586_; lean_object* v_res_587_; 
v_x_88__boxed_586_ = lean_unbox(v_x_585_);
v_res_587_ = l_Lake_instToJsonLogLevel_toJson(v_x_88__boxed_586_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonLogLevel_fromJson(lean_object* v_json_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_Json_getTag_x3f(v_json_608_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v___x_610_; 
v___x_610_ = ((lean_object*)(l_Lake_instFromJsonLogLevel_fromJson___closed__1));
return v___x_610_;
}
else
{
lean_object* v_val_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v_val_611_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_val_611_);
lean_dec_ref_known(v___x_609_, 1);
v___x_612_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__6));
v___x_613_ = lean_string_dec_eq(v_val_611_, v___x_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_614_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__0));
v___x_615_ = lean_string_dec_eq(v_val_611_, v___x_614_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__2));
v___x_617_ = lean_string_dec_eq(v_val_611_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__4));
v___x_619_ = lean_string_dec_eq(v_val_611_, v___x_618_);
lean_dec(v_val_611_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
v___x_620_ = ((lean_object*)(l_Lake_instFromJsonLogLevel_fromJson___closed__3));
return v___x_620_;
}
else
{
lean_object* v___x_621_; 
v___x_621_ = ((lean_object*)(l_Lake_instFromJsonLogLevel_fromJson___closed__4));
return v___x_621_;
}
}
else
{
lean_object* v___x_622_; 
lean_dec(v_val_611_);
v___x_622_ = ((lean_object*)(l_Lake_instFromJsonLogLevel_fromJson___closed__5));
return v___x_622_;
}
}
else
{
lean_object* v___x_623_; 
lean_dec(v_val_611_);
v___x_623_ = ((lean_object*)(l_Lake_instFromJsonLogLevel_fromJson___closed__6));
return v___x_623_;
}
}
else
{
lean_object* v___x_624_; 
lean_dec(v_val_611_);
v___x_624_ = ((lean_object*)(l_Lake_instFromJsonLogLevel_fromJson___closed__7));
return v___x_624_;
}
}
}
}
static lean_object* _init_l_Lake_instLTLogLevel(void){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = lean_box(0);
return v___x_627_;
}
}
static lean_object* _init_l_Lake_instLELogLevel(void){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = lean_box(0);
return v___x_628_;
}
}
LEAN_EXPORT uint8_t l_Lake_instMinLogLevel___lam__0(uint8_t v_x_629_, uint8_t v_y_630_){
_start:
{
uint8_t v___x_631_; 
v___x_631_ = l_Lake_instOrdLogLevel_ord(v_x_629_, v_y_630_);
if (v___x_631_ == 2)
{
return v_y_630_;
}
else
{
return v_x_629_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMinLogLevel___lam__0___boxed(lean_object* v_x_632_, lean_object* v_y_633_){
_start:
{
uint8_t v_x_boxed_634_; uint8_t v_y_boxed_635_; uint8_t v_res_636_; lean_object* v_r_637_; 
v_x_boxed_634_ = lean_unbox(v_x_632_);
v_y_boxed_635_ = lean_unbox(v_y_633_);
v_res_636_ = l_Lake_instMinLogLevel___lam__0(v_x_boxed_634_, v_y_boxed_635_);
v_r_637_ = lean_box(v_res_636_);
return v_r_637_;
}
}
LEAN_EXPORT uint8_t l_Lake_instMaxLogLevel___lam__0(uint8_t v_x_640_, uint8_t v_y_641_){
_start:
{
uint8_t v___x_642_; 
v___x_642_ = l_Lake_instOrdLogLevel_ord(v_x_640_, v_y_641_);
if (v___x_642_ == 2)
{
return v_x_640_;
}
else
{
return v_y_641_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxLogLevel___lam__0___boxed(lean_object* v_x_643_, lean_object* v_y_644_){
_start:
{
uint8_t v_x_boxed_645_; uint8_t v_y_boxed_646_; uint8_t v_res_647_; lean_object* v_r_648_; 
v_x_boxed_645_ = lean_unbox(v_x_643_);
v_y_boxed_646_ = lean_unbox(v_y_644_);
v_res_647_ = l_Lake_instMaxLogLevel___lam__0(v_x_boxed_645_, v_y_boxed_646_);
v_r_648_ = lean_box(v_res_647_);
return v_r_648_;
}
}
LEAN_EXPORT uint32_t l_Lake_LogLevel_icon(uint8_t v_x_651_){
_start:
{
switch(v_x_651_)
{
case 2:
{
uint32_t v___x_652_; 
v___x_652_ = 9888;
return v___x_652_;
}
case 3:
{
uint32_t v___x_653_; 
v___x_653_ = 10006;
return v___x_653_;
}
default: 
{
uint32_t v___x_654_; 
v___x_654_ = 8505;
return v___x_654_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_icon___boxed(lean_object* v_x_655_){
_start:
{
uint8_t v_x_35__boxed_656_; uint32_t v_res_657_; lean_object* v_r_658_; 
v_x_35__boxed_656_ = lean_unbox(v_x_655_);
v_res_657_ = l_Lake_LogLevel_icon(v_x_35__boxed_656_);
v_r_658_ = lean_box_uint32(v_res_657_);
return v_r_658_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ansiColor(uint8_t v_x_662_){
_start:
{
switch(v_x_662_)
{
case 2:
{
lean_object* v___x_663_; 
v___x_663_ = ((lean_object*)(l_Lake_LogLevel_ansiColor___closed__0));
return v___x_663_;
}
case 3:
{
lean_object* v___x_664_; 
v___x_664_ = ((lean_object*)(l_Lake_LogLevel_ansiColor___closed__1));
return v___x_664_;
}
default: 
{
lean_object* v___x_665_; 
v___x_665_ = ((lean_object*)(l_Lake_LogLevel_ansiColor___closed__2));
return v___x_665_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ansiColor___boxed(lean_object* v_x_666_){
_start:
{
uint8_t v_x_36__boxed_667_; lean_object* v_res_668_; 
v_x_36__boxed_667_ = lean_unbox(v_x_666_);
v_res_668_ = l_Lake_LogLevel_ansiColor(v_x_36__boxed_667_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00Lake_LogLevel_ofString_x3f_spec__0(lean_object* v_s_669_, lean_object* v_p_670_){
_start:
{
lean_object* v___y_672_; lean_object* v___y_673_; uint32_t v___y_677_; lean_object* v___x_689_; uint8_t v_decide_690_; 
v___x_689_ = lean_string_utf8_byte_size(v_s_669_);
v_decide_690_ = lean_nat_dec_eq(v_p_670_, v___x_689_);
if (v_decide_690_ == 0)
{
uint32_t v___x_691_; uint32_t v___x_692_; uint8_t v___x_693_; 
v___x_691_ = lean_string_utf8_get_fast(v_s_669_, v_p_670_);
v___x_692_ = 65;
v___x_693_ = lean_uint32_dec_le(v___x_692_, v___x_691_);
if (v___x_693_ == 0)
{
v___y_677_ = v___x_691_;
goto v___jp_676_;
}
else
{
uint32_t v___x_694_; uint8_t v___x_695_; 
v___x_694_ = 90;
v___x_695_ = lean_uint32_dec_le(v___x_691_, v___x_694_);
if (v___x_695_ == 0)
{
v___y_677_ = v___x_691_;
goto v___jp_676_;
}
else
{
uint32_t v___x_696_; uint32_t v___x_697_; 
v___x_696_ = 32;
v___x_697_ = lean_uint32_add(v___x_691_, v___x_696_);
v___y_677_ = v___x_697_;
goto v___jp_676_;
}
}
}
else
{
lean_dec(v_p_670_);
return v_s_669_;
}
v___jp_671_:
{
lean_object* v___x_674_; 
v___x_674_ = lean_nat_add(v_p_670_, v___y_673_);
lean_dec(v_p_670_);
v_s_669_ = v___y_672_;
v_p_670_ = v___x_674_;
goto _start;
}
v___jp_676_:
{
lean_object* v___x_678_; uint32_t v___x_679_; uint8_t v___x_680_; 
lean_inc(v_p_670_);
v___x_678_ = lean_string_utf8_set(v_s_669_, v_p_670_, v___y_677_);
v___x_679_ = 127;
v___x_680_ = lean_uint32_dec_le(v___y_677_, v___x_679_);
if (v___x_680_ == 0)
{
uint32_t v___x_681_; uint8_t v___x_682_; 
v___x_681_ = 2047;
v___x_682_ = lean_uint32_dec_le(v___y_677_, v___x_681_);
if (v___x_682_ == 0)
{
uint32_t v___x_683_; uint8_t v___x_684_; 
v___x_683_ = 65535;
v___x_684_ = lean_uint32_dec_le(v___y_677_, v___x_683_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; 
v___x_685_ = lean_unsigned_to_nat(4u);
v___y_672_ = v___x_678_;
v___y_673_ = v___x_685_;
goto v___jp_671_;
}
else
{
lean_object* v___x_686_; 
v___x_686_ = lean_unsigned_to_nat(3u);
v___y_672_ = v___x_678_;
v___y_673_ = v___x_686_;
goto v___jp_671_;
}
}
else
{
lean_object* v___x_687_; 
v___x_687_ = lean_unsigned_to_nat(2u);
v___y_672_ = v___x_678_;
v___y_673_ = v___x_687_;
goto v___jp_671_;
}
}
else
{
lean_object* v___x_688_; 
v___x_688_ = lean_unsigned_to_nat(1u);
v___y_672_ = v___x_678_;
v___y_673_ = v___x_688_;
goto v___jp_671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ofString_x3f(lean_object* v_s_712_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_717_ = lean_unsigned_to_nat(0u);
v___x_718_ = l_String_mapAux___at___00Lake_LogLevel_ofString_x3f_spec__0(v_s_712_, v___x_717_);
v___x_719_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__0));
v___x_720_ = lean_string_dec_eq(v___x_718_, v___x_719_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_721_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__2));
v___x_722_ = lean_string_dec_eq(v___x_718_, v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_723_ = ((lean_object*)(l_Lake_LogLevel_ofString_x3f___closed__2));
v___x_724_ = lean_string_dec_eq(v___x_718_, v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_725_ = ((lean_object*)(l_Lake_LogLevel_ofString_x3f___closed__3));
v___x_726_ = lean_string_dec_eq(v___x_718_, v___x_725_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_727_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__4));
v___x_728_ = lean_string_dec_eq(v___x_718_, v___x_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_729_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__6));
v___x_730_ = lean_string_dec_eq(v___x_718_, v___x_729_);
lean_dec_ref(v___x_718_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; 
v___x_731_ = lean_box(0);
return v___x_731_;
}
else
{
lean_object* v___x_732_; 
v___x_732_ = ((lean_object*)(l_Lake_LogLevel_ofString_x3f___closed__4));
return v___x_732_;
}
}
else
{
lean_dec_ref(v___x_718_);
goto v___jp_715_;
}
}
else
{
lean_dec_ref(v___x_718_);
goto v___jp_715_;
}
}
else
{
lean_dec_ref(v___x_718_);
goto v___jp_713_;
}
}
else
{
lean_dec_ref(v___x_718_);
goto v___jp_713_;
}
}
else
{
lean_object* v___x_733_; 
lean_dec_ref(v___x_718_);
v___x_733_ = ((lean_object*)(l_Lake_LogLevel_ofString_x3f___closed__5));
return v___x_733_;
}
v___jp_713_:
{
lean_object* v___x_714_; 
v___x_714_ = ((lean_object*)(l_Lake_LogLevel_ofString_x3f___closed__0));
return v___x_714_;
}
v___jp_715_:
{
lean_object* v___x_716_; 
v___x_716_ = ((lean_object*)(l_Lake_LogLevel_ofString_x3f___closed__1));
return v___x_716_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_toString(uint8_t v_x_734_){
_start:
{
switch(v_x_734_)
{
case 0:
{
lean_object* v___x_735_; 
v___x_735_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__0));
return v___x_735_;
}
case 1:
{
lean_object* v___x_736_; 
v___x_736_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__2));
return v___x_736_;
}
case 2:
{
lean_object* v___x_737_; 
v___x_737_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__4));
return v___x_737_;
}
default: 
{
lean_object* v___x_738_; 
v___x_738_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__6));
return v___x_738_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_toString___boxed(lean_object* v_x_739_){
_start:
{
uint8_t v_x_36__boxed_740_; lean_object* v_res_741_; 
v_x_36__boxed_740_ = lean_unbox(v_x_739_);
v_res_741_ = l_Lake_LogLevel_toString(v_x_36__boxed_740_);
return v_res_741_;
}
}
LEAN_EXPORT uint8_t l_Lake_LogLevel_ofMessageSeverity(uint8_t v_x_744_){
_start:
{
switch(v_x_744_)
{
case 0:
{
uint8_t v___x_745_; 
v___x_745_ = 1;
return v___x_745_;
}
case 1:
{
uint8_t v___x_746_; 
v___x_746_ = 2;
return v___x_746_;
}
default: 
{
uint8_t v___x_747_; 
v___x_747_ = 3;
return v___x_747_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ofMessageSeverity___boxed(lean_object* v_x_748_){
_start:
{
uint8_t v_x_25__boxed_749_; uint8_t v_res_750_; lean_object* v_r_751_; 
v_x_25__boxed_749_ = lean_unbox(v_x_748_);
v_res_750_ = l_Lake_LogLevel_ofMessageSeverity(v_x_25__boxed_749_);
v_r_751_ = lean_box(v_res_750_);
return v_r_751_;
}
}
LEAN_EXPORT uint8_t l_Lake_LogLevel_toMessageSeverity(uint8_t v_x_752_){
_start:
{
switch(v_x_752_)
{
case 2:
{
uint8_t v___x_753_; 
v___x_753_ = 1;
return v___x_753_;
}
case 3:
{
uint8_t v___x_754_; 
v___x_754_ = 2;
return v___x_754_;
}
default: 
{
uint8_t v___x_755_; 
v___x_755_ = 0;
return v___x_755_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_toMessageSeverity___boxed(lean_object* v_x_756_){
_start:
{
uint8_t v_x_30__boxed_757_; uint8_t v_res_758_; lean_object* v_r_759_; 
v_x_30__boxed_757_ = lean_unbox(v_x_756_);
v_res_758_ = l_Lake_LogLevel_toMessageSeverity(v_x_30__boxed_757_);
v_r_759_ = lean_box(v_res_758_);
return v_r_759_;
}
}
LEAN_EXPORT uint8_t l_Lake_Verbosity_minLogLv(uint8_t v_x_760_){
_start:
{
switch(v_x_760_)
{
case 0:
{
uint8_t v___x_761_; 
v___x_761_ = 2;
return v___x_761_;
}
case 1:
{
uint8_t v___x_762_; 
v___x_762_ = 1;
return v___x_762_;
}
default: 
{
uint8_t v___x_763_; 
v___x_763_ = 0;
return v___x_763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_minLogLv___boxed(lean_object* v_x_764_){
_start:
{
uint8_t v_x_25__boxed_765_; uint8_t v_res_766_; lean_object* v_r_767_; 
v_x_25__boxed_765_ = lean_unbox(v_x_764_);
v_res_766_ = l_Lake_Verbosity_minLogLv(v_x_25__boxed_765_);
v_r_767_ = lean_box(v_res_766_);
return v_r_767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_instToJsonLogEntry_toJson_spec__0(lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
if (lean_obj_tag(v_a_774_) == 0)
{
lean_object* v___x_776_; 
v___x_776_ = lean_array_to_list(v_a_775_);
return v___x_776_;
}
else
{
lean_object* v_head_777_; lean_object* v_tail_778_; lean_object* v___x_779_; 
v_head_777_ = lean_ctor_get(v_a_774_, 0);
lean_inc(v_head_777_);
v_tail_778_ = lean_ctor_get(v_a_774_, 1);
lean_inc(v_tail_778_);
lean_dec_ref_known(v_a_774_, 2);
v___x_779_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_775_, v_head_777_);
v_a_774_ = v_tail_778_;
v_a_775_ = v___x_779_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonLogEntry_toJson(lean_object* v_x_785_){
_start:
{
uint8_t v_level_786_; lean_object* v_message_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_level_786_ = lean_ctor_get_uint8(v_x_785_, sizeof(void*)*1);
v_message_787_ = lean_ctor_get(v_x_785_, 0);
v___x_788_ = ((lean_object*)(l_Lake_instToJsonLogEntry_toJson___closed__0));
v___x_789_ = l_Lake_instToJsonLogLevel_toJson(v_level_786_);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_788_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
v___x_791_ = lean_box(0);
v___x_792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_790_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
v___x_793_ = ((lean_object*)(l_Lake_instToJsonLogEntry_toJson___closed__1));
lean_inc_ref(v_message_787_);
v___x_794_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_794_, 0, v_message_787_);
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_793_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
lean_ctor_set(v___x_796_, 1, v___x_791_);
v___x_797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
lean_ctor_set(v___x_797_, 1, v___x_791_);
v___x_798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_792_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = ((lean_object*)(l_Lake_instToJsonLogEntry_toJson___closed__2));
v___x_800_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_instToJsonLogEntry_toJson_spec__0(v___x_798_, v___x_799_);
v___x_801_ = l_Lean_Json_mkObj(v___x_800_);
lean_dec(v___x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonLogEntry_toJson___boxed(lean_object* v_x_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lake_instToJsonLogEntry_toJson(v_x_802_);
lean_dec_ref(v_x_802_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__0(lean_object* v_j_806_, lean_object* v_k_807_){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = l_Lean_Json_getObjValD(v_j_806_, v_k_807_);
v___x_809_ = l_Lake_instFromJsonLogLevel_fromJson(v___x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__0___boxed(lean_object* v_j_810_, lean_object* v_k_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__0(v_j_810_, v_k_811_);
lean_dec_ref(v_k_811_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1(lean_object* v_j_813_, lean_object* v_k_814_){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = l_Lean_Json_getObjValD(v_j_813_, v_k_814_);
v___x_816_ = l_Lean_Json_getStr_x3f(v___x_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1___boxed(lean_object* v_j_817_, lean_object* v_k_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1(v_j_817_, v_k_818_);
lean_dec_ref(v_k_818_);
return v_res_819_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__3(void){
_start:
{
uint8_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_825_ = 1;
v___x_826_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__2));
v___x_827_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_826_, v___x_825_);
return v___x_827_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__5(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_829_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__4));
v___x_830_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__3, &l_Lake_instFromJsonLogEntry_fromJson___closed__3_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__3);
v___x_831_ = lean_string_append(v___x_830_, v___x_829_);
return v___x_831_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__7(void){
_start:
{
uint8_t v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_834_ = 1;
v___x_835_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__6));
v___x_836_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_835_, v___x_834_);
return v___x_836_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__8(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_837_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__7, &l_Lake_instFromJsonLogEntry_fromJson___closed__7_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__7);
v___x_838_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__5, &l_Lake_instFromJsonLogEntry_fromJson___closed__5_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__5);
v___x_839_ = lean_string_append(v___x_838_, v___x_837_);
return v___x_839_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__10(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_841_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__9));
v___x_842_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__8, &l_Lake_instFromJsonLogEntry_fromJson___closed__8_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__8);
v___x_843_ = lean_string_append(v___x_842_, v___x_841_);
return v___x_843_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__12(void){
_start:
{
uint8_t v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_846_ = 1;
v___x_847_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__11));
v___x_848_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_847_, v___x_846_);
return v___x_848_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__13(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_849_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__12, &l_Lake_instFromJsonLogEntry_fromJson___closed__12_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__12);
v___x_850_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__5, &l_Lake_instFromJsonLogEntry_fromJson___closed__5_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__5);
v___x_851_ = lean_string_append(v___x_850_, v___x_849_);
return v___x_851_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__14(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_852_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__9));
v___x_853_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__13, &l_Lake_instFromJsonLogEntry_fromJson___closed__13_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__13);
v___x_854_ = lean_string_append(v___x_853_, v___x_852_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonLogEntry_fromJson(lean_object* v_json_855_){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = ((lean_object*)(l_Lake_instToJsonLogEntry_toJson___closed__0));
lean_inc(v_json_855_);
v___x_857_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__0(v_json_855_, v___x_856_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_867_; 
lean_dec(v_json_855_);
v_a_858_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_867_ == 0)
{
v___x_860_ = v___x_857_;
v_isShared_861_ = v_isSharedCheck_867_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_857_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_867_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_865_; 
v___x_862_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__10, &l_Lake_instFromJsonLogEntry_fromJson___closed__10_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__10);
v___x_863_ = lean_string_append(v___x_862_, v_a_858_);
lean_dec(v_a_858_);
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 0, v___x_863_);
v___x_865_ = v___x_860_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
else
{
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec(v_json_855_);
v_a_868_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_857_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_857_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
lean_ctor_set_tag(v___x_870_, 0);
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v_a_876_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_876_);
lean_dec_ref_known(v___x_857_, 1);
v___x_877_ = ((lean_object*)(l_Lake_instToJsonLogEntry_toJson___closed__1));
v___x_878_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1(v_json_855_, v___x_877_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_888_; 
lean_dec(v_a_876_);
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_888_ == 0)
{
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_888_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_888_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_883_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__14, &l_Lake_instFromJsonLogEntry_fromJson___closed__14_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__14);
v___x_884_ = lean_string_append(v___x_883_, v_a_879_);
lean_dec(v_a_879_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_884_);
v___x_886_ = v___x_881_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
else
{
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_dec(v_a_876_);
v_a_889_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_878_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_878_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
lean_ctor_set_tag(v___x_891_, 0);
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
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_906_; 
v_a_897_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_906_ == 0)
{
v___x_899_ = v___x_878_;
v_isShared_900_ = v_isSharedCheck_906_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_878_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_906_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; uint8_t v___x_902_; lean_object* v___x_904_; 
v___x_901_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_901_, 0, v_a_897_);
v___x_902_ = lean_unbox(v_a_876_);
lean_dec(v_a_876_);
lean_ctor_set_uint8(v___x_901_, sizeof(void*)*1, v___x_902_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_901_);
v___x_904_ = v___x_899_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_901_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_toString(lean_object* v_self_911_, uint8_t v_useAnsi_912_){
_start:
{
if (v_useAnsi_912_ == 0)
{
uint8_t v_level_913_; lean_object* v_message_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v_level_913_ = lean_ctor_get_uint8(v_self_911_, sizeof(void*)*1);
v_message_914_ = lean_ctor_get(v_self_911_, 0);
v___x_915_ = l_Lake_LogLevel_toString(v_level_913_);
v___x_916_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__9));
v___x_917_ = lean_string_append(v___x_915_, v___x_916_);
v___x_918_ = lean_string_append(v___x_917_, v_message_914_);
return v___x_918_;
}
else
{
uint8_t v_level_919_; lean_object* v_message_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v_pre_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v_level_919_ = lean_ctor_get_uint8(v_self_911_, sizeof(void*)*1);
v_message_920_ = lean_ctor_get(v_self_911_, 0);
v___x_921_ = l_Lake_LogLevel_ansiColor(v_level_919_);
v___x_922_ = l_Lake_LogLevel_toString(v_level_919_);
v___x_923_ = ((lean_object*)(l_Lake_LogEntry_toString___closed__0));
v___x_924_ = lean_string_append(v___x_922_, v___x_923_);
v_pre_925_ = l_Lake_Ansi_chalk(v___x_921_, v___x_924_);
lean_dec_ref(v___x_924_);
lean_dec_ref(v___x_921_);
v___x_926_ = ((lean_object*)(l_Lake_LogEntry_toString___closed__1));
v___x_927_ = lean_string_append(v_pre_925_, v___x_926_);
v___x_928_ = lean_string_append(v___x_927_, v_message_920_);
return v___x_928_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_toString___boxed(lean_object* v_self_929_, lean_object* v_useAnsi_930_){
_start:
{
uint8_t v_useAnsi_boxed_931_; lean_object* v_res_932_; 
v_useAnsi_boxed_931_ = lean_unbox(v_useAnsi_930_);
v_res_932_ = l_Lake_LogEntry_toString(v_self_929_, v_useAnsi_boxed_931_);
lean_dec_ref(v_self_929_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToStringLogEntry___lam__0(lean_object* v_self_933_){
_start:
{
uint8_t v___x_934_; lean_object* v___x_935_; 
v___x_934_ = 0;
v___x_935_ = l_Lake_LogEntry_toString(v_self_933_, v___x_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToStringLogEntry___lam__0___boxed(lean_object* v_self_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lake_instToStringLogEntry___lam__0(v_self_936_);
lean_dec_ref(v_self_936_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_trace(lean_object* v_message_940_){
_start:
{
uint8_t v___x_941_; lean_object* v___x_942_; 
v___x_941_ = 0;
v___x_942_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_942_, 0, v_message_940_);
lean_ctor_set_uint8(v___x_942_, sizeof(void*)*1, v___x_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_info(lean_object* v_message_943_){
_start:
{
uint8_t v___x_944_; lean_object* v___x_945_; 
v___x_944_ = 1;
v___x_945_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_945_, 0, v_message_943_);
lean_ctor_set_uint8(v___x_945_, sizeof(void*)*1, v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_warning(lean_object* v_message_946_){
_start:
{
uint8_t v___x_947_; lean_object* v___x_948_; 
v___x_947_ = 2;
v___x_948_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_948_, 0, v_message_946_);
lean_ctor_set_uint8(v___x_948_, sizeof(void*)*1, v___x_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_error(lean_object* v_message_949_){
_start:
{
uint8_t v___x_950_; lean_object* v___x_951_; 
v___x_950_ = 3;
v___x_951_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_951_, 0, v_message_949_);
lean_ctor_set_uint8(v___x_951_, sizeof(void*)*1, v___x_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_ofSerialMessage(lean_object* v_msg_953_){
_start:
{
lean_object* v_toBaseMessage_954_; lean_object* v_fileName_955_; lean_object* v_pos_956_; uint8_t v_severity_957_; lean_object* v_caption_958_; lean_object* v_data_959_; lean_object* v___y_961_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v_startInclusive_970_; lean_object* v_endExclusive_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v_toBaseMessage_954_ = lean_ctor_get(v_msg_953_, 0);
lean_inc_ref(v_toBaseMessage_954_);
lean_dec_ref(v_msg_953_);
v_fileName_955_ = lean_ctor_get(v_toBaseMessage_954_, 0);
lean_inc_ref(v_fileName_955_);
v_pos_956_ = lean_ctor_get(v_toBaseMessage_954_, 1);
lean_inc_ref(v_pos_956_);
v_severity_957_ = lean_ctor_get_uint8(v_toBaseMessage_954_, sizeof(void*)*5 + 1);
v_caption_958_ = lean_ctor_get(v_toBaseMessage_954_, 3);
lean_inc_ref(v_caption_958_);
v_data_959_ = lean_ctor_get(v_toBaseMessage_954_, 4);
lean_inc(v_data_959_);
lean_dec_ref(v_toBaseMessage_954_);
v___x_966_ = lean_unsigned_to_nat(0u);
v___x_967_ = lean_string_utf8_byte_size(v_caption_958_);
v___x_968_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_968_, 0, v_caption_958_);
lean_ctor_set(v___x_968_, 1, v___x_966_);
lean_ctor_set(v___x_968_, 2, v___x_967_);
v___x_969_ = l_String_Slice_trimAscii(v___x_968_);
v_startInclusive_970_ = lean_ctor_get(v___x_969_, 1);
v_endExclusive_971_ = lean_ctor_get(v___x_969_, 2);
v___x_972_ = lean_nat_sub(v_endExclusive_971_, v_startInclusive_970_);
v___x_973_ = lean_nat_dec_eq(v___x_972_, v___x_966_);
lean_dec(v___x_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_987_; 
v___x_974_ = l_String_Slice_toString(v___x_969_);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_987_ == 0)
{
lean_object* v_unused_988_; lean_object* v_unused_989_; lean_object* v_unused_990_; 
v_unused_988_ = lean_ctor_get(v___x_969_, 2);
lean_dec(v_unused_988_);
v_unused_989_ = lean_ctor_get(v___x_969_, 1);
lean_dec(v_unused_989_);
v_unused_990_ = lean_ctor_get(v___x_969_, 0);
lean_dec(v_unused_990_);
v___x_976_ = v___x_969_;
v_isShared_977_ = v_isSharedCheck_987_;
goto v_resetjp_975_;
}
else
{
lean_dec(v___x_969_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_987_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_978_ = ((lean_object*)(l_Lake_LogEntry_ofSerialMessage___closed__0));
v___x_979_ = lean_string_append(v___x_974_, v___x_978_);
v___x_980_ = lean_string_utf8_byte_size(v_data_959_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 2, v___x_980_);
lean_ctor_set(v___x_976_, 1, v___x_966_);
lean_ctor_set(v___x_976_, 0, v_data_959_);
v___x_982_ = v___x_976_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_data_959_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_986_, 2, v___x_980_);
v___x_982_ = v_reuseFailAlloc_986_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_983_ = l_String_Slice_trimAscii(v___x_982_);
v___x_984_ = l_String_Slice_toString(v___x_983_);
lean_dec_ref(v___x_983_);
v___x_985_ = lean_string_append(v___x_979_, v___x_984_);
lean_dec_ref(v___x_984_);
v___y_961_ = v___x_985_;
goto v___jp_960_;
}
}
}
else
{
lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1003_; 
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1003_ == 0)
{
lean_object* v_unused_1004_; lean_object* v_unused_1005_; lean_object* v_unused_1006_; 
v_unused_1004_ = lean_ctor_get(v___x_969_, 2);
lean_dec(v_unused_1004_);
v_unused_1005_ = lean_ctor_get(v___x_969_, 1);
lean_dec(v_unused_1005_);
v_unused_1006_ = lean_ctor_get(v___x_969_, 0);
lean_dec(v_unused_1006_);
v___x_992_ = v___x_969_;
v_isShared_993_ = v_isSharedCheck_1003_;
goto v_resetjp_991_;
}
else
{
lean_dec(v___x_969_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1003_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_994_ = lean_string_utf8_byte_size(v_data_959_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 2, v___x_994_);
lean_ctor_set(v___x_992_, 1, v___x_966_);
lean_ctor_set(v___x_992_, 0, v_data_959_);
v___x_996_ = v___x_992_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_data_959_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_1002_, 2, v___x_994_);
v___x_996_ = v_reuseFailAlloc_1002_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_997_; lean_object* v_str_998_; lean_object* v_startInclusive_999_; lean_object* v_endExclusive_1000_; lean_object* v___x_1001_; 
v___x_997_ = l_String_Slice_trimAscii(v___x_996_);
v_str_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc_ref(v_str_998_);
v_startInclusive_999_ = lean_ctor_get(v___x_997_, 1);
lean_inc(v_startInclusive_999_);
v_endExclusive_1000_ = lean_ctor_get(v___x_997_, 2);
lean_inc(v_endExclusive_1000_);
lean_dec_ref(v___x_997_);
v___x_1001_ = lean_string_utf8_extract_fast(v_str_998_, v_startInclusive_999_, v_endExclusive_1000_);
lean_dec(v_endExclusive_1000_);
lean_dec(v_startInclusive_999_);
lean_dec_ref(v_str_998_);
v___y_961_ = v___x_1001_;
goto v___jp_960_;
}
}
}
v___jp_960_:
{
uint8_t v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_962_ = l_Lake_LogLevel_ofMessageSeverity(v_severity_957_);
v___x_963_ = lean_box(0);
v___x_964_ = l_Lean_mkErrorStringWithPos(v_fileName_955_, v_pos_956_, v___y_961_, v___x_963_, v___x_963_, v___x_963_);
lean_dec_ref(v___y_961_);
v___x_965_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_965_, 0, v___x_964_);
lean_ctor_set_uint8(v___x_965_, sizeof(void*)*1, v___x_962_);
return v___x_965_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_ofMessage(lean_object* v_msg_1007_){
_start:
{
lean_object* v_fileName_1009_; lean_object* v_pos_1010_; uint8_t v_severity_1011_; lean_object* v_caption_1012_; lean_object* v_data_1013_; lean_object* v___x_1014_; lean_object* v___y_1016_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v_startInclusive_1025_; lean_object* v_endExclusive_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
v_fileName_1009_ = lean_ctor_get(v_msg_1007_, 0);
lean_inc_ref(v_fileName_1009_);
v_pos_1010_ = lean_ctor_get(v_msg_1007_, 1);
lean_inc_ref(v_pos_1010_);
v_severity_1011_ = lean_ctor_get_uint8(v_msg_1007_, sizeof(void*)*5 + 1);
v_caption_1012_ = lean_ctor_get(v_msg_1007_, 3);
lean_inc_ref(v_caption_1012_);
v_data_1013_ = lean_ctor_get(v_msg_1007_, 4);
lean_inc(v_data_1013_);
lean_dec_ref(v_msg_1007_);
v___x_1014_ = l_Lean_MessageData_toString(v_data_1013_);
v___x_1021_ = lean_unsigned_to_nat(0u);
v___x_1022_ = lean_string_utf8_byte_size(v_caption_1012_);
v___x_1023_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1023_, 0, v_caption_1012_);
lean_ctor_set(v___x_1023_, 1, v___x_1021_);
lean_ctor_set(v___x_1023_, 2, v___x_1022_);
v___x_1024_ = l_String_Slice_trimAscii(v___x_1023_);
v_startInclusive_1025_ = lean_ctor_get(v___x_1024_, 1);
v_endExclusive_1026_ = lean_ctor_get(v___x_1024_, 2);
v___x_1027_ = lean_nat_sub(v_endExclusive_1026_, v_startInclusive_1025_);
v___x_1028_ = lean_nat_dec_eq(v___x_1027_, v___x_1021_);
lean_dec(v___x_1027_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1042_; 
v___x_1029_ = l_String_Slice_toString(v___x_1024_);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1042_ == 0)
{
lean_object* v_unused_1043_; lean_object* v_unused_1044_; lean_object* v_unused_1045_; 
v_unused_1043_ = lean_ctor_get(v___x_1024_, 2);
lean_dec(v_unused_1043_);
v_unused_1044_ = lean_ctor_get(v___x_1024_, 1);
lean_dec(v_unused_1044_);
v_unused_1045_ = lean_ctor_get(v___x_1024_, 0);
lean_dec(v_unused_1045_);
v___x_1031_ = v___x_1024_;
v_isShared_1032_ = v_isSharedCheck_1042_;
goto v_resetjp_1030_;
}
else
{
lean_dec(v___x_1024_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1042_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1033_ = ((lean_object*)(l_Lake_LogEntry_ofSerialMessage___closed__0));
v___x_1034_ = lean_string_append(v___x_1029_, v___x_1033_);
v___x_1035_ = lean_string_utf8_byte_size(v___x_1014_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 2, v___x_1035_);
lean_ctor_set(v___x_1031_, 1, v___x_1021_);
lean_ctor_set(v___x_1031_, 0, v___x_1014_);
v___x_1037_ = v___x_1031_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v___x_1021_);
lean_ctor_set(v_reuseFailAlloc_1041_, 2, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1038_ = l_String_Slice_trimAscii(v___x_1037_);
v___x_1039_ = l_String_Slice_toString(v___x_1038_);
lean_dec_ref(v___x_1038_);
v___x_1040_ = lean_string_append(v___x_1034_, v___x_1039_);
lean_dec_ref(v___x_1039_);
v___y_1016_ = v___x_1040_;
goto v___jp_1015_;
}
}
}
else
{
lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1058_; 
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1058_ == 0)
{
lean_object* v_unused_1059_; lean_object* v_unused_1060_; lean_object* v_unused_1061_; 
v_unused_1059_ = lean_ctor_get(v___x_1024_, 2);
lean_dec(v_unused_1059_);
v_unused_1060_ = lean_ctor_get(v___x_1024_, 1);
lean_dec(v_unused_1060_);
v_unused_1061_ = lean_ctor_get(v___x_1024_, 0);
lean_dec(v_unused_1061_);
v___x_1047_ = v___x_1024_;
v_isShared_1048_ = v_isSharedCheck_1058_;
goto v_resetjp_1046_;
}
else
{
lean_dec(v___x_1024_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1058_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1049_ = lean_string_utf8_byte_size(v___x_1014_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 2, v___x_1049_);
lean_ctor_set(v___x_1047_, 1, v___x_1021_);
lean_ctor_set(v___x_1047_, 0, v___x_1014_);
v___x_1051_ = v___x_1047_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v___x_1021_);
lean_ctor_set(v_reuseFailAlloc_1057_, 2, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1052_; lean_object* v_str_1053_; lean_object* v_startInclusive_1054_; lean_object* v_endExclusive_1055_; lean_object* v___x_1056_; 
v___x_1052_ = l_String_Slice_trimAscii(v___x_1051_);
v_str_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc_ref(v_str_1053_);
v_startInclusive_1054_ = lean_ctor_get(v___x_1052_, 1);
lean_inc(v_startInclusive_1054_);
v_endExclusive_1055_ = lean_ctor_get(v___x_1052_, 2);
lean_inc(v_endExclusive_1055_);
lean_dec_ref(v___x_1052_);
v___x_1056_ = lean_string_utf8_extract_fast(v_str_1053_, v_startInclusive_1054_, v_endExclusive_1055_);
lean_dec(v_endExclusive_1055_);
lean_dec(v_startInclusive_1054_);
lean_dec_ref(v_str_1053_);
v___y_1016_ = v___x_1056_;
goto v___jp_1015_;
}
}
}
v___jp_1015_:
{
uint8_t v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1017_ = l_Lake_LogLevel_ofMessageSeverity(v_severity_1011_);
v___x_1018_ = lean_box(0);
v___x_1019_ = l_Lean_mkErrorStringWithPos(v_fileName_1009_, v_pos_1010_, v___y_1016_, v___x_1018_, v___x_1018_, v___x_1018_);
lean_dec_ref(v___y_1016_);
v___x_1020_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set_uint8(v___x_1020_, sizeof(void*)*1, v___x_1017_);
return v___x_1020_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_ofMessage___boxed(lean_object* v_msg_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lake_LogEntry_ofMessage(v_msg_1062_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lake_logVerbose___redArg(lean_object* v_inst_1065_, lean_object* v_message_1066_){
_start:
{
uint8_t v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1067_ = 0;
v___x_1068_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1068_, 0, v_message_1066_);
lean_ctor_set_uint8(v___x_1068_, sizeof(void*)*1, v___x_1067_);
v___x_1069_ = lean_apply_1(v_inst_1065_, v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lake_logVerbose(lean_object* v_m_1070_, lean_object* v_inst_1071_, lean_object* v_inst_1072_, lean_object* v_message_1073_){
_start:
{
uint8_t v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1074_ = 0;
v___x_1075_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1075_, 0, v_message_1073_);
lean_ctor_set_uint8(v___x_1075_, sizeof(void*)*1, v___x_1074_);
v___x_1076_ = lean_apply_1(v_inst_1072_, v___x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lake_logVerbose___boxed(lean_object* v_m_1077_, lean_object* v_inst_1078_, lean_object* v_inst_1079_, lean_object* v_message_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lake_logVerbose(v_m_1077_, v_inst_1078_, v_inst_1079_, v_message_1080_);
lean_dec_ref(v_inst_1078_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lake_logInfo___redArg(lean_object* v_inst_1082_, lean_object* v_message_1083_){
_start:
{
uint8_t v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1084_ = 1;
v___x_1085_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1085_, 0, v_message_1083_);
lean_ctor_set_uint8(v___x_1085_, sizeof(void*)*1, v___x_1084_);
v___x_1086_ = lean_apply_1(v_inst_1082_, v___x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lake_logInfo(lean_object* v_m_1087_, lean_object* v_inst_1088_, lean_object* v_inst_1089_, lean_object* v_message_1090_){
_start:
{
uint8_t v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = 1;
v___x_1092_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1092_, 0, v_message_1090_);
lean_ctor_set_uint8(v___x_1092_, sizeof(void*)*1, v___x_1091_);
v___x_1093_ = lean_apply_1(v_inst_1089_, v___x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lake_logInfo___boxed(lean_object* v_m_1094_, lean_object* v_inst_1095_, lean_object* v_inst_1096_, lean_object* v_message_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Lake_logInfo(v_m_1094_, v_inst_1095_, v_inst_1096_, v_message_1097_);
lean_dec_ref(v_inst_1095_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Lake_logWarning___redArg(lean_object* v_inst_1099_, lean_object* v_message_1100_){
_start:
{
uint8_t v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1101_ = 2;
v___x_1102_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1102_, 0, v_message_1100_);
lean_ctor_set_uint8(v___x_1102_, sizeof(void*)*1, v___x_1101_);
v___x_1103_ = lean_apply_1(v_inst_1099_, v___x_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lake_logWarning(lean_object* v_m_1104_, lean_object* v_inst_1105_, lean_object* v_message_1106_){
_start:
{
uint8_t v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1107_ = 2;
v___x_1108_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1108_, 0, v_message_1106_);
lean_ctor_set_uint8(v___x_1108_, sizeof(void*)*1, v___x_1107_);
v___x_1109_ = lean_apply_1(v_inst_1105_, v___x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lake_logError___redArg(lean_object* v_inst_1110_, lean_object* v_message_1111_){
_start:
{
uint8_t v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1112_ = 3;
v___x_1113_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1113_, 0, v_message_1111_);
lean_ctor_set_uint8(v___x_1113_, sizeof(void*)*1, v___x_1112_);
v___x_1114_ = lean_apply_1(v_inst_1110_, v___x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lake_logError(lean_object* v_m_1115_, lean_object* v_inst_1116_, lean_object* v_message_1117_){
_start:
{
uint8_t v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = 3;
v___x_1119_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1119_, 0, v_message_1117_);
lean_ctor_set_uint8(v___x_1119_, sizeof(void*)*1, v___x_1118_);
v___x_1120_ = lean_apply_1(v_inst_1116_, v___x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lake_logSerialMessage___redArg(lean_object* v_msg_1121_, lean_object* v_inst_1122_, lean_object* v_inst_1123_){
_start:
{
lean_object* v_toBaseMessage_1124_; lean_object* v_toApplicative_1125_; uint8_t v_isSilent_1126_; 
v_toBaseMessage_1124_ = lean_ctor_get(v_msg_1121_, 0);
v_toApplicative_1125_ = lean_ctor_get(v_inst_1122_, 0);
lean_inc_ref(v_toApplicative_1125_);
lean_dec_ref(v_inst_1122_);
v_isSilent_1126_ = lean_ctor_get_uint8(v_toBaseMessage_1124_, sizeof(void*)*5 + 2);
if (v_isSilent_1126_ == 0)
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_dec_ref(v_toApplicative_1125_);
v___x_1127_ = l_Lake_LogEntry_ofSerialMessage(v_msg_1121_);
v___x_1128_ = lean_apply_1(v_inst_1123_, v___x_1127_);
return v___x_1128_;
}
else
{
lean_object* v_toPure_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_dec(v_inst_1123_);
lean_dec_ref(v_msg_1121_);
v_toPure_1129_ = lean_ctor_get(v_toApplicative_1125_, 1);
lean_inc(v_toPure_1129_);
lean_dec_ref(v_toApplicative_1125_);
v___x_1130_ = lean_box(0);
v___x_1131_ = lean_apply_2(v_toPure_1129_, lean_box(0), v___x_1130_);
return v___x_1131_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logSerialMessage(lean_object* v_m_1132_, lean_object* v_msg_1133_, lean_object* v_inst_1134_, lean_object* v_inst_1135_){
_start:
{
lean_object* v_toBaseMessage_1136_; lean_object* v_toApplicative_1137_; uint8_t v_isSilent_1138_; 
v_toBaseMessage_1136_ = lean_ctor_get(v_msg_1133_, 0);
v_toApplicative_1137_ = lean_ctor_get(v_inst_1134_, 0);
lean_inc_ref(v_toApplicative_1137_);
lean_dec_ref(v_inst_1134_);
v_isSilent_1138_ = lean_ctor_get_uint8(v_toBaseMessage_1136_, sizeof(void*)*5 + 2);
if (v_isSilent_1138_ == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_dec_ref(v_toApplicative_1137_);
v___x_1139_ = l_Lake_LogEntry_ofSerialMessage(v_msg_1133_);
v___x_1140_ = lean_apply_1(v_inst_1135_, v___x_1139_);
return v___x_1140_;
}
else
{
lean_object* v_toPure_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
lean_dec(v_inst_1135_);
lean_dec_ref(v_msg_1133_);
v_toPure_1141_ = lean_ctor_get(v_toApplicative_1137_, 1);
lean_inc(v_toPure_1141_);
lean_dec_ref(v_toApplicative_1137_);
v___x_1142_ = lean_box(0);
v___x_1143_ = lean_apply_2(v_toPure_1141_, lean_box(0), v___x_1142_);
return v___x_1143_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logMessage___redArg___lam__0(lean_object* v_inst_1144_, lean_object* v_____do__lift_1145_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = lean_apply_1(v_inst_1144_, v_____do__lift_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lake_logMessage___redArg(lean_object* v_msg_1147_, lean_object* v_inst_1148_, lean_object* v_inst_1149_, lean_object* v_inst_1150_){
_start:
{
uint8_t v_isSilent_1151_; 
v_isSilent_1151_ = lean_ctor_get_uint8(v_msg_1147_, sizeof(void*)*5 + 2);
if (v_isSilent_1151_ == 0)
{
lean_object* v_toBind_1152_; lean_object* v___f_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v_toBind_1152_ = lean_ctor_get(v_inst_1148_, 1);
lean_inc(v_toBind_1152_);
lean_dec_ref(v_inst_1148_);
v___f_1153_ = lean_alloc_closure((void*)(l_Lake_logMessage___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1153_, 0, v_inst_1149_);
v___x_1154_ = lean_alloc_closure((void*)(l_Lake_LogEntry_ofMessage___boxed), 2, 1);
lean_closure_set(v___x_1154_, 0, v_msg_1147_);
v___x_1155_ = lean_apply_2(v_inst_1150_, lean_box(0), v___x_1154_);
v___x_1156_ = lean_apply_4(v_toBind_1152_, lean_box(0), lean_box(0), v___x_1155_, v___f_1153_);
return v___x_1156_;
}
else
{
lean_object* v_toApplicative_1157_; lean_object* v_toPure_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v_toApplicative_1157_ = lean_ctor_get(v_inst_1148_, 0);
lean_inc_ref(v_toApplicative_1157_);
lean_dec(v_inst_1150_);
lean_dec(v_inst_1149_);
lean_dec_ref(v_inst_1148_);
lean_dec_ref(v_msg_1147_);
v_toPure_1158_ = lean_ctor_get(v_toApplicative_1157_, 1);
lean_inc(v_toPure_1158_);
lean_dec_ref(v_toApplicative_1157_);
v___x_1159_ = lean_box(0);
v___x_1160_ = lean_apply_2(v_toPure_1158_, lean_box(0), v___x_1159_);
return v___x_1160_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logMessage(lean_object* v_m_1161_, lean_object* v_msg_1162_, lean_object* v_inst_1163_, lean_object* v_inst_1164_, lean_object* v_inst_1165_){
_start:
{
uint8_t v_isSilent_1166_; 
v_isSilent_1166_ = lean_ctor_get_uint8(v_msg_1162_, sizeof(void*)*5 + 2);
if (v_isSilent_1166_ == 0)
{
lean_object* v_toBind_1167_; lean_object* v___f_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v_toBind_1167_ = lean_ctor_get(v_inst_1163_, 1);
lean_inc(v_toBind_1167_);
lean_dec_ref(v_inst_1163_);
v___f_1168_ = lean_alloc_closure((void*)(l_Lake_logMessage___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1168_, 0, v_inst_1164_);
v___x_1169_ = lean_alloc_closure((void*)(l_Lake_LogEntry_ofMessage___boxed), 2, 1);
lean_closure_set(v___x_1169_, 0, v_msg_1162_);
v___x_1170_ = lean_apply_2(v_inst_1165_, lean_box(0), v___x_1169_);
v___x_1171_ = lean_apply_4(v_toBind_1167_, lean_box(0), lean_box(0), v___x_1170_, v___f_1168_);
return v___x_1171_;
}
else
{
lean_object* v_toApplicative_1172_; lean_object* v_toPure_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v_toApplicative_1172_ = lean_ctor_get(v_inst_1163_, 0);
lean_inc_ref(v_toApplicative_1172_);
lean_dec(v_inst_1165_);
lean_dec(v_inst_1164_);
lean_dec_ref(v_inst_1163_);
lean_dec_ref(v_msg_1162_);
v_toPure_1173_ = lean_ctor_get(v_toApplicative_1172_, 1);
lean_inc(v_toPure_1173_);
lean_dec_ref(v_toApplicative_1172_);
v___x_1174_ = lean_box(0);
v___x_1175_ = lean_apply_2(v_toPure_1173_, lean_box(0), v___x_1174_);
return v___x_1175_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logToStream(lean_object* v_e_1176_, lean_object* v_out_1177_, uint8_t v_minLv_1178_, uint8_t v_useAnsi_1179_){
_start:
{
uint8_t v_level_1181_; uint8_t v___x_1182_; 
v_level_1181_ = lean_ctor_get_uint8(v_e_1176_, sizeof(void*)*1);
v___x_1182_ = l_Lake_instOrdLogLevel_ord(v_minLv_1178_, v_level_1181_);
if (v___x_1182_ == 2)
{
lean_object* v___x_1183_; 
lean_dec_ref(v_out_1177_);
v___x_1183_ = lean_box(0);
return v___x_1183_;
}
else
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = l_Lake_LogEntry_toString(v_e_1176_, v_useAnsi_1179_);
v___x_1185_ = l_IO_FS_Stream_putStrLn(v_out_1177_, v___x_1184_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1186_);
lean_dec_ref_known(v___x_1185_, 1);
return v_a_1186_;
}
else
{
lean_object* v___x_1187_; 
lean_dec_ref_known(v___x_1185_, 1);
v___x_1187_ = lean_box(0);
return v___x_1187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_logToStream___boxed(lean_object* v_e_1188_, lean_object* v_out_1189_, lean_object* v_minLv_1190_, lean_object* v_useAnsi_1191_, lean_object* v_a_1192_){
_start:
{
uint8_t v_minLv_boxed_1193_; uint8_t v_useAnsi_boxed_1194_; lean_object* v_res_1195_; 
v_minLv_boxed_1193_ = lean_unbox(v_minLv_1190_);
v_useAnsi_boxed_1194_ = lean_unbox(v_useAnsi_1191_);
v_res_1195_ = l_Lake_logToStream(v_e_1188_, v_out_1189_, v_minLv_boxed_1193_, v_useAnsi_boxed_1194_);
lean_dec_ref(v_e_1188_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___redArg___lam__0(lean_object* v_inst_1196_, lean_object* v_x_1197_){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = lean_box(0);
v___x_1199_ = lean_apply_2(v_inst_1196_, lean_box(0), v___x_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___redArg___lam__0___boxed(lean_object* v_inst_1200_, lean_object* v_x_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lake_MonadLog_nop___redArg___lam__0(v_inst_1200_, v_x_1201_);
lean_dec_ref(v_x_1201_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___redArg(lean_object* v_inst_1203_){
_start:
{
lean_object* v___f_1204_; 
v___f_1204_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1204_, 0, v_inst_1203_);
return v___f_1204_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop(lean_object* v_m_1205_, lean_object* v_inst_1206_){
_start:
{
lean_object* v___f_1207_; 
v___f_1207_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1207_, 0, v_inst_1206_);
return v___f_1207_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instInhabitedOfPure___redArg(lean_object* v_inst_1208_){
_start:
{
lean_object* v___f_1209_; 
v___f_1209_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1209_, 0, v_inst_1208_);
return v___f_1209_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instInhabitedOfPure(lean_object* v_m_1210_, lean_object* v_inst_1211_){
_start:
{
lean_object* v___f_1212_; 
v___f_1212_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1212_, 0, v_inst_1211_);
return v___f_1212_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift___redArg___lam__0(lean_object* v_self_1213_, lean_object* v_inst_1214_, lean_object* v_e_1215_){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = lean_apply_1(v_self_1213_, v_e_1215_);
v___x_1217_ = lean_apply_2(v_inst_1214_, lean_box(0), v___x_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift___redArg(lean_object* v_inst_1218_, lean_object* v_self_1219_){
_start:
{
lean_object* v___f_1220_; 
v___f_1220_ = lean_alloc_closure((void*)(l_Lake_MonadLog_lift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1220_, 0, v_self_1219_);
lean_closure_set(v___f_1220_, 1, v_inst_1218_);
return v___f_1220_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift(lean_object* v_m_1221_, lean_object* v_n_1222_, lean_object* v_inst_1223_, lean_object* v_self_1224_){
_start:
{
lean_object* v___f_1225_; 
v___f_1225_ = lean_alloc_closure((void*)(l_Lake_MonadLog_lift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1225_, 0, v_self_1224_);
lean_closure_set(v___f_1225_, 1, v_inst_1223_);
return v___f_1225_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift___redArg___lam__0(lean_object* v_methods_1226_, lean_object* v_inst_1227_, lean_object* v_e_1228_){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = lean_apply_1(v_methods_1226_, v_e_1228_);
v___x_1230_ = lean_apply_2(v_inst_1227_, lean_box(0), v___x_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift___redArg(lean_object* v_inst_1231_, lean_object* v_methods_1232_){
_start:
{
lean_object* v___f_1233_; 
v___f_1233_ = lean_alloc_closure((void*)(l_Lake_MonadLog_instOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1233_, 0, v_methods_1232_);
lean_closure_set(v___f_1233_, 1, v_inst_1231_);
return v___f_1233_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift(lean_object* v_m_1234_, lean_object* v_n_1235_, lean_object* v_inst_1236_, lean_object* v_methods_1237_){
_start:
{
lean_object* v___f_1238_; 
v___f_1238_ = lean_alloc_closure((void*)(l_Lake_MonadLog_instOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1238_, 0, v_methods_1237_);
lean_closure_set(v___f_1238_, 1, v_inst_1236_);
return v___f_1238_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg___lam__0(lean_object* v_out_1239_, uint8_t v_minLv_1240_, uint8_t v_useAnsi_1241_, lean_object* v_inst_1242_, lean_object* v_e_1243_){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1244_ = lean_box(v_minLv_1240_);
v___x_1245_ = lean_box(v_useAnsi_1241_);
v___x_1246_ = lean_alloc_closure((void*)(l_Lake_logToStream___boxed), 5, 4);
lean_closure_set(v___x_1246_, 0, v_e_1243_);
lean_closure_set(v___x_1246_, 1, v_out_1239_);
lean_closure_set(v___x_1246_, 2, v___x_1244_);
lean_closure_set(v___x_1246_, 3, v___x_1245_);
v___x_1247_ = lean_apply_2(v_inst_1242_, lean_box(0), v___x_1246_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg___lam__0___boxed(lean_object* v_out_1248_, lean_object* v_minLv_1249_, lean_object* v_useAnsi_1250_, lean_object* v_inst_1251_, lean_object* v_e_1252_){
_start:
{
uint8_t v_minLv_boxed_1253_; uint8_t v_useAnsi_boxed_1254_; lean_object* v_res_1255_; 
v_minLv_boxed_1253_ = lean_unbox(v_minLv_1249_);
v_useAnsi_boxed_1254_ = lean_unbox(v_useAnsi_1250_);
v_res_1255_ = l_Lake_MonadLog_stream___redArg___lam__0(v_out_1248_, v_minLv_boxed_1253_, v_useAnsi_boxed_1254_, v_inst_1251_, v_e_1252_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg(lean_object* v_inst_1256_, lean_object* v_out_1257_, uint8_t v_minLv_1258_, uint8_t v_useAnsi_1259_){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___f_1262_; 
v___x_1260_ = lean_box(v_minLv_1258_);
v___x_1261_ = lean_box(v_useAnsi_1259_);
v___f_1262_ = lean_alloc_closure((void*)(l_Lake_MonadLog_stream___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1262_, 0, v_out_1257_);
lean_closure_set(v___f_1262_, 1, v___x_1260_);
lean_closure_set(v___f_1262_, 2, v___x_1261_);
lean_closure_set(v___f_1262_, 3, v_inst_1256_);
return v___f_1262_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg___boxed(lean_object* v_inst_1263_, lean_object* v_out_1264_, lean_object* v_minLv_1265_, lean_object* v_useAnsi_1266_){
_start:
{
uint8_t v_minLv_boxed_1267_; uint8_t v_useAnsi_boxed_1268_; lean_object* v_res_1269_; 
v_minLv_boxed_1267_ = lean_unbox(v_minLv_1265_);
v_useAnsi_boxed_1268_ = lean_unbox(v_useAnsi_1266_);
v_res_1269_ = l_Lake_MonadLog_stream___redArg(v_inst_1263_, v_out_1264_, v_minLv_boxed_1267_, v_useAnsi_boxed_1268_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream(lean_object* v_m_1270_, lean_object* v_inst_1271_, lean_object* v_out_1272_, uint8_t v_minLv_1273_, uint8_t v_useAnsi_1274_){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___f_1277_; 
v___x_1275_ = lean_box(v_minLv_1273_);
v___x_1276_ = lean_box(v_useAnsi_1274_);
v___f_1277_ = lean_alloc_closure((void*)(l_Lake_MonadLog_stream___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1277_, 0, v_out_1272_);
lean_closure_set(v___f_1277_, 1, v___x_1275_);
lean_closure_set(v___f_1277_, 2, v___x_1276_);
lean_closure_set(v___f_1277_, 3, v_inst_1271_);
return v___f_1277_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___boxed(lean_object* v_m_1278_, lean_object* v_inst_1279_, lean_object* v_out_1280_, lean_object* v_minLv_1281_, lean_object* v_useAnsi_1282_){
_start:
{
uint8_t v_minLv_boxed_1283_; uint8_t v_useAnsi_boxed_1284_; lean_object* v_res_1285_; 
v_minLv_boxed_1283_ = lean_unbox(v_minLv_1281_);
v_useAnsi_boxed_1284_ = lean_unbox(v_useAnsi_1282_);
v_res_1285_ = l_Lake_MonadLog_stream(v_m_1278_, v_inst_1279_, v_out_1280_, v_minLv_boxed_1283_, v_useAnsi_boxed_1284_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_error___redArg___lam__0(lean_object* v_failure_1286_, lean_object* v_x_1287_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = lean_apply_1(v_failure_1286_, lean_box(0));
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_error___redArg(lean_object* v_inst_1289_, lean_object* v_inst_1290_, lean_object* v_msg_1291_){
_start:
{
lean_object* v_toApplicative_1292_; lean_object* v_failure_1293_; lean_object* v_toSeqRight_1294_; lean_object* v___f_1295_; uint8_t v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v_toApplicative_1292_ = lean_ctor_get(v_inst_1289_, 0);
lean_inc_ref(v_toApplicative_1292_);
v_failure_1293_ = lean_ctor_get(v_inst_1289_, 1);
lean_inc(v_failure_1293_);
lean_dec_ref(v_inst_1289_);
v_toSeqRight_1294_ = lean_ctor_get(v_toApplicative_1292_, 4);
lean_inc(v_toSeqRight_1294_);
lean_dec_ref(v_toApplicative_1292_);
v___f_1295_ = lean_alloc_closure((void*)(l_Lake_MonadLog_error___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1295_, 0, v_failure_1293_);
v___x_1296_ = 3;
v___x_1297_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1297_, 0, v_msg_1291_);
lean_ctor_set_uint8(v___x_1297_, sizeof(void*)*1, v___x_1296_);
v___x_1298_ = lean_apply_1(v_inst_1290_, v___x_1297_);
v___x_1299_ = lean_apply_4(v_toSeqRight_1294_, lean_box(0), lean_box(0), v___x_1298_, v___f_1295_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_error(lean_object* v_m_1300_, lean_object* v_00_u03b1_1301_, lean_object* v_inst_1302_, lean_object* v_inst_1303_, lean_object* v_msg_1304_){
_start:
{
lean_object* v_toApplicative_1305_; lean_object* v_failure_1306_; lean_object* v_toSeqRight_1307_; lean_object* v___f_1308_; uint8_t v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v_toApplicative_1305_ = lean_ctor_get(v_inst_1302_, 0);
lean_inc_ref(v_toApplicative_1305_);
v_failure_1306_ = lean_ctor_get(v_inst_1302_, 1);
lean_inc(v_failure_1306_);
lean_dec_ref(v_inst_1302_);
v_toSeqRight_1307_ = lean_ctor_get(v_toApplicative_1305_, 4);
lean_inc(v_toSeqRight_1307_);
lean_dec_ref(v_toApplicative_1305_);
v___f_1308_ = lean_alloc_closure((void*)(l_Lake_MonadLog_error___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1308_, 0, v_failure_1306_);
v___x_1309_ = 3;
v___x_1310_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1310_, 0, v_msg_1304_);
lean_ctor_set_uint8(v___x_1310_, sizeof(void*)*1, v___x_1309_);
v___x_1311_ = lean_apply_1(v_inst_1303_, v___x_1310_);
v___x_1312_ = lean_apply_4(v_toSeqRight_1307_, lean_box(0), lean_box(0), v___x_1311_, v___f_1308_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logEntry(lean_object* v_self_1313_, lean_object* v_e_1314_, uint8_t v_minLv_1315_, uint8_t v_ansiMode_1316_){
_start:
{
lean_object* v___x_1318_; uint8_t v___x_1319_; lean_object* v___x_1320_; 
v___x_1318_ = l_Lake_OutStream_get(v_self_1313_);
lean_inc_ref(v___x_1318_);
v___x_1319_ = l_Lake_AnsiMode_isEnabled(v___x_1318_, v_ansiMode_1316_);
v___x_1320_ = l_Lake_logToStream(v_e_1314_, v___x_1318_, v_minLv_1315_, v___x_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logEntry___boxed(lean_object* v_self_1321_, lean_object* v_e_1322_, lean_object* v_minLv_1323_, lean_object* v_ansiMode_1324_, lean_object* v_a_1325_){
_start:
{
uint8_t v_minLv_boxed_1326_; uint8_t v_ansiMode_boxed_1327_; lean_object* v_res_1328_; 
v_minLv_boxed_1326_ = lean_unbox(v_minLv_1323_);
v_ansiMode_boxed_1327_ = lean_unbox(v_ansiMode_1324_);
v_res_1328_ = l_Lake_OutStream_logEntry(v_self_1321_, v_e_1322_, v_minLv_boxed_1326_, v_ansiMode_boxed_1327_);
lean_dec_ref(v_e_1322_);
lean_dec(v_self_1321_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg___lam__0(lean_object* v_out_1329_, uint8_t v_minLv_1330_, uint8_t v_ansiMode_1331_, lean_object* v_inst_1332_, lean_object* v_e_1333_){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1334_ = lean_box(v_minLv_1330_);
v___x_1335_ = lean_box(v_ansiMode_1331_);
v___x_1336_ = lean_alloc_closure((void*)(l_Lake_OutStream_logEntry___boxed), 5, 4);
lean_closure_set(v___x_1336_, 0, v_out_1329_);
lean_closure_set(v___x_1336_, 1, v_e_1333_);
lean_closure_set(v___x_1336_, 2, v___x_1334_);
lean_closure_set(v___x_1336_, 3, v___x_1335_);
v___x_1337_ = lean_apply_2(v_inst_1332_, lean_box(0), v___x_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg___lam__0___boxed(lean_object* v_out_1338_, lean_object* v_minLv_1339_, lean_object* v_ansiMode_1340_, lean_object* v_inst_1341_, lean_object* v_e_1342_){
_start:
{
uint8_t v_minLv_boxed_1343_; uint8_t v_ansiMode_boxed_1344_; lean_object* v_res_1345_; 
v_minLv_boxed_1343_ = lean_unbox(v_minLv_1339_);
v_ansiMode_boxed_1344_ = lean_unbox(v_ansiMode_1340_);
v_res_1345_ = l_Lake_OutStream_logger___redArg___lam__0(v_out_1338_, v_minLv_boxed_1343_, v_ansiMode_boxed_1344_, v_inst_1341_, v_e_1342_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg(lean_object* v_inst_1346_, lean_object* v_out_1347_, uint8_t v_minLv_1348_, uint8_t v_ansiMode_1349_){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___f_1352_; 
v___x_1350_ = lean_box(v_minLv_1348_);
v___x_1351_ = lean_box(v_ansiMode_1349_);
v___f_1352_ = lean_alloc_closure((void*)(l_Lake_OutStream_logger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1352_, 0, v_out_1347_);
lean_closure_set(v___f_1352_, 1, v___x_1350_);
lean_closure_set(v___f_1352_, 2, v___x_1351_);
lean_closure_set(v___f_1352_, 3, v_inst_1346_);
return v___f_1352_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg___boxed(lean_object* v_inst_1353_, lean_object* v_out_1354_, lean_object* v_minLv_1355_, lean_object* v_ansiMode_1356_){
_start:
{
uint8_t v_minLv_boxed_1357_; uint8_t v_ansiMode_boxed_1358_; lean_object* v_res_1359_; 
v_minLv_boxed_1357_ = lean_unbox(v_minLv_1355_);
v_ansiMode_boxed_1358_ = lean_unbox(v_ansiMode_1356_);
v_res_1359_ = l_Lake_OutStream_logger___redArg(v_inst_1353_, v_out_1354_, v_minLv_boxed_1357_, v_ansiMode_boxed_1358_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger(lean_object* v_m_1360_, lean_object* v_inst_1361_, lean_object* v_out_1362_, uint8_t v_minLv_1363_, uint8_t v_ansiMode_1364_){
_start:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___f_1367_; 
v___x_1365_ = lean_box(v_minLv_1363_);
v___x_1366_ = lean_box(v_ansiMode_1364_);
v___f_1367_ = lean_alloc_closure((void*)(l_Lake_OutStream_logger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1367_, 0, v_out_1362_);
lean_closure_set(v___f_1367_, 1, v___x_1365_);
lean_closure_set(v___f_1367_, 2, v___x_1366_);
lean_closure_set(v___f_1367_, 3, v_inst_1361_);
return v___f_1367_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___boxed(lean_object* v_m_1368_, lean_object* v_inst_1369_, lean_object* v_out_1370_, lean_object* v_minLv_1371_, lean_object* v_ansiMode_1372_){
_start:
{
uint8_t v_minLv_boxed_1373_; uint8_t v_ansiMode_boxed_1374_; lean_object* v_res_1375_; 
v_minLv_boxed_1373_ = lean_unbox(v_minLv_1371_);
v_ansiMode_boxed_1374_ = lean_unbox(v_ansiMode_1372_);
v_res_1375_ = l_Lake_OutStream_logger(v_m_1368_, v_inst_1369_, v_out_1370_, v_minLv_boxed_1373_, v_ansiMode_boxed_1374_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg___lam__0(lean_object* v___x_1376_, uint8_t v_minLv_1377_, uint8_t v_ansiMode_1378_, lean_object* v_inst_1379_, lean_object* v_e_1380_){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1381_ = lean_box(v_minLv_1377_);
v___x_1382_ = lean_box(v_ansiMode_1378_);
v___x_1383_ = lean_alloc_closure((void*)(l_Lake_OutStream_logEntry___boxed), 5, 4);
lean_closure_set(v___x_1383_, 0, v___x_1376_);
lean_closure_set(v___x_1383_, 1, v_e_1380_);
lean_closure_set(v___x_1383_, 2, v___x_1381_);
lean_closure_set(v___x_1383_, 3, v___x_1382_);
v___x_1384_ = lean_apply_2(v_inst_1379_, lean_box(0), v___x_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg___lam__0___boxed(lean_object* v___x_1385_, lean_object* v_minLv_1386_, lean_object* v_ansiMode_1387_, lean_object* v_inst_1388_, lean_object* v_e_1389_){
_start:
{
uint8_t v_minLv_boxed_1390_; uint8_t v_ansiMode_boxed_1391_; lean_object* v_res_1392_; 
v_minLv_boxed_1390_ = lean_unbox(v_minLv_1386_);
v_ansiMode_boxed_1391_ = lean_unbox(v_ansiMode_1387_);
v_res_1392_ = l_Lake_MonadLog_stdout___redArg___lam__0(v___x_1385_, v_minLv_boxed_1390_, v_ansiMode_boxed_1391_, v_inst_1388_, v_e_1389_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg(lean_object* v_inst_1393_, uint8_t v_minLv_1394_, uint8_t v_ansiMode_1395_){
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
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg___boxed(lean_object* v_inst_1400_, lean_object* v_minLv_1401_, lean_object* v_ansiMode_1402_){
_start:
{
uint8_t v_minLv_boxed_1403_; uint8_t v_ansiMode_boxed_1404_; lean_object* v_res_1405_; 
v_minLv_boxed_1403_ = lean_unbox(v_minLv_1401_);
v_ansiMode_boxed_1404_ = lean_unbox(v_ansiMode_1402_);
v_res_1405_ = l_Lake_MonadLog_stdout___redArg(v_inst_1400_, v_minLv_boxed_1403_, v_ansiMode_boxed_1404_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout(lean_object* v_m_1406_, lean_object* v_inst_1407_, uint8_t v_minLv_1408_, uint8_t v_ansiMode_1409_){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___f_1413_; 
v___x_1410_ = lean_box(0);
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
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___boxed(lean_object* v_m_1414_, lean_object* v_inst_1415_, lean_object* v_minLv_1416_, lean_object* v_ansiMode_1417_){
_start:
{
uint8_t v_minLv_boxed_1418_; uint8_t v_ansiMode_boxed_1419_; lean_object* v_res_1420_; 
v_minLv_boxed_1418_ = lean_unbox(v_minLv_1416_);
v_ansiMode_boxed_1419_ = lean_unbox(v_ansiMode_1417_);
v_res_1420_ = l_Lake_MonadLog_stdout(v_m_1414_, v_inst_1415_, v_minLv_boxed_1418_, v_ansiMode_boxed_1419_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___redArg(lean_object* v_inst_1421_, uint8_t v_minLv_1422_, uint8_t v_ansiMode_1423_){
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
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___redArg___boxed(lean_object* v_inst_1428_, lean_object* v_minLv_1429_, lean_object* v_ansiMode_1430_){
_start:
{
uint8_t v_minLv_boxed_1431_; uint8_t v_ansiMode_boxed_1432_; lean_object* v_res_1433_; 
v_minLv_boxed_1431_ = lean_unbox(v_minLv_1429_);
v_ansiMode_boxed_1432_ = lean_unbox(v_ansiMode_1430_);
v_res_1433_ = l_Lake_MonadLog_stderr___redArg(v_inst_1428_, v_minLv_boxed_1431_, v_ansiMode_boxed_1432_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr(lean_object* v_m_1434_, lean_object* v_inst_1435_, uint8_t v_minLv_1436_, uint8_t v_ansiMode_1437_){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___f_1441_; 
v___x_1438_ = lean_box(1);
v___x_1439_ = lean_box(v_minLv_1436_);
v___x_1440_ = lean_box(v_ansiMode_1437_);
v___f_1441_ = lean_alloc_closure((void*)(l_Lake_MonadLog_stdout___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1441_, 0, v___x_1438_);
lean_closure_set(v___f_1441_, 1, v___x_1439_);
lean_closure_set(v___f_1441_, 2, v___x_1440_);
lean_closure_set(v___f_1441_, 3, v_inst_1435_);
return v___f_1441_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___boxed(lean_object* v_m_1442_, lean_object* v_inst_1443_, lean_object* v_minLv_1444_, lean_object* v_ansiMode_1445_){
_start:
{
uint8_t v_minLv_boxed_1446_; uint8_t v_ansiMode_boxed_1447_; lean_object* v_res_1448_; 
v_minLv_boxed_1446_ = lean_unbox(v_minLv_1444_);
v_ansiMode_boxed_1447_ = lean_unbox(v_ansiMode_1445_);
v_res_1448_ = l_Lake_MonadLog_stderr(v_m_1442_, v_inst_1443_, v_minLv_boxed_1446_, v_ansiMode_boxed_1447_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg___lam__0(lean_object* v_val_1449_, uint8_t v_minLv_1450_, uint8_t v_val_1451_, lean_object* v_inst_1452_, lean_object* v_e_1453_){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1454_ = lean_box(v_minLv_1450_);
v___x_1455_ = lean_box(v_val_1451_);
v___x_1456_ = lean_alloc_closure((void*)(l_Lake_logToStream___boxed), 5, 4);
lean_closure_set(v___x_1456_, 0, v_e_1453_);
lean_closure_set(v___x_1456_, 1, v_val_1449_);
lean_closure_set(v___x_1456_, 2, v___x_1454_);
lean_closure_set(v___x_1456_, 3, v___x_1455_);
v___x_1457_ = lean_apply_2(v_inst_1452_, lean_box(0), v___x_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg___lam__0___boxed(lean_object* v_val_1458_, lean_object* v_minLv_1459_, lean_object* v_val_1460_, lean_object* v_inst_1461_, lean_object* v_e_1462_){
_start:
{
uint8_t v_minLv_boxed_1463_; uint8_t v_val_105__boxed_1464_; lean_object* v_res_1465_; 
v_minLv_boxed_1463_ = lean_unbox(v_minLv_1459_);
v_val_105__boxed_1464_ = lean_unbox(v_val_1460_);
v_res_1465_ = l_Lake_OutStream_getLogger___redArg___lam__0(v_val_1458_, v_minLv_boxed_1463_, v_val_105__boxed_1464_, v_inst_1461_, v_e_1462_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg(lean_object* v_inst_1466_, lean_object* v_out_1467_, uint8_t v_minLv_1468_, uint8_t v_ansiMode_1469_){
_start:
{
lean_object* v___x_1471_; uint8_t v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___f_1475_; 
v___x_1471_ = l_Lake_OutStream_get(v_out_1467_);
lean_inc_ref(v___x_1471_);
v___x_1472_ = l_Lake_AnsiMode_isEnabled(v___x_1471_, v_ansiMode_1469_);
v___x_1473_ = lean_box(v_minLv_1468_);
v___x_1474_ = lean_box(v___x_1472_);
v___f_1475_ = lean_alloc_closure((void*)(l_Lake_OutStream_getLogger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1475_, 0, v___x_1471_);
lean_closure_set(v___f_1475_, 1, v___x_1473_);
lean_closure_set(v___f_1475_, 2, v___x_1474_);
lean_closure_set(v___f_1475_, 3, v_inst_1466_);
return v___f_1475_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg___boxed(lean_object* v_inst_1476_, lean_object* v_out_1477_, lean_object* v_minLv_1478_, lean_object* v_ansiMode_1479_, lean_object* v_a_1480_){
_start:
{
uint8_t v_minLv_boxed_1481_; uint8_t v_ansiMode_boxed_1482_; lean_object* v_res_1483_; 
v_minLv_boxed_1481_ = lean_unbox(v_minLv_1478_);
v_ansiMode_boxed_1482_ = lean_unbox(v_ansiMode_1479_);
v_res_1483_ = l_Lake_OutStream_getLogger___redArg(v_inst_1476_, v_out_1477_, v_minLv_boxed_1481_, v_ansiMode_boxed_1482_);
lean_dec(v_out_1477_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger(lean_object* v_m_1484_, lean_object* v_inst_1485_, lean_object* v_out_1486_, uint8_t v_minLv_1487_, uint8_t v_ansiMode_1488_){
_start:
{
lean_object* v___x_1490_; uint8_t v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___f_1494_; 
v___x_1490_ = l_Lake_OutStream_get(v_out_1486_);
lean_inc_ref(v___x_1490_);
v___x_1491_ = l_Lake_AnsiMode_isEnabled(v___x_1490_, v_ansiMode_1488_);
v___x_1492_ = lean_box(v_minLv_1487_);
v___x_1493_ = lean_box(v___x_1491_);
v___f_1494_ = lean_alloc_closure((void*)(l_Lake_OutStream_getLogger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1494_, 0, v___x_1490_);
lean_closure_set(v___f_1494_, 1, v___x_1492_);
lean_closure_set(v___f_1494_, 2, v___x_1493_);
lean_closure_set(v___f_1494_, 3, v_inst_1485_);
return v___f_1494_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___boxed(lean_object* v_m_1495_, lean_object* v_inst_1496_, lean_object* v_out_1497_, lean_object* v_minLv_1498_, lean_object* v_ansiMode_1499_, lean_object* v_a_1500_){
_start:
{
uint8_t v_minLv_boxed_1501_; uint8_t v_ansiMode_boxed_1502_; lean_object* v_res_1503_; 
v_minLv_boxed_1501_ = lean_unbox(v_minLv_1498_);
v_ansiMode_boxed_1502_ = lean_unbox(v_ansiMode_1499_);
v_res_1503_ = l_Lake_OutStream_getLogger(v_m_1495_, v_inst_1496_, v_out_1497_, v_minLv_boxed_1501_, v_ansiMode_boxed_1502_);
lean_dec(v_out_1497_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0(lean_object* v_inst_1504_, lean_object* v_inst_1505_, lean_object* v_x_1506_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = lean_apply_2(v_inst_1504_, lean_box(0), v_inst_1505_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0___boxed(lean_object* v_inst_1508_, lean_object* v_inst_1509_, lean_object* v_x_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0(v_inst_1508_, v_inst_1509_, v_x_1510_);
lean_dec(v_x_1510_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___redArg(lean_object* v_inst_1512_, lean_object* v_inst_1513_){
_start:
{
lean_object* v___f_1514_; 
v___f_1514_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1514_, 0, v_inst_1512_);
lean_closure_set(v___f_1514_, 1, v_inst_1513_);
return v___f_1514_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure(lean_object* v_n_1515_, lean_object* v_00_u03b1_1516_, lean_object* v_m_1517_, lean_object* v_inst_1518_, lean_object* v_inst_1519_){
_start:
{
lean_object* v___f_1520_; 
v___f_1520_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1520_, 0, v_inst_1518_);
lean_closure_set(v___f_1520_, 1, v_inst_1519_);
return v___f_1520_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__0(lean_object* v_e_1521_, lean_object* v_inst_1522_, lean_object* v_a_1523_){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1524_ = lean_apply_1(v_a_1523_, v_e_1521_);
v___x_1525_ = lean_apply_2(v_inst_1522_, lean_box(0), v___x_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1(lean_object* v_inst_1526_, lean_object* v_inst_1527_, lean_object* v_e_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v_toApplicative_1530_; lean_object* v_toBind_1531_; lean_object* v_toPure_1532_; lean_object* v___f_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v_toApplicative_1530_ = lean_ctor_get(v_inst_1526_, 0);
lean_inc_ref(v_toApplicative_1530_);
v_toBind_1531_ = lean_ctor_get(v_inst_1526_, 1);
lean_inc(v_toBind_1531_);
lean_dec_ref(v_inst_1526_);
v_toPure_1532_ = lean_ctor_get(v_toApplicative_1530_, 1);
lean_inc(v_toPure_1532_);
lean_dec_ref(v_toApplicative_1530_);
v___f_1533_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1533_, 0, v_e_1528_);
lean_closure_set(v___f_1533_, 1, v_inst_1527_);
lean_inc(v___y_1529_);
v___x_1534_ = lean_apply_2(v_toPure_1532_, lean_box(0), v___y_1529_);
v___x_1535_ = lean_apply_4(v_toBind_1531_, lean_box(0), lean_box(0), v___x_1534_, v___f_1533_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1___boxed(lean_object* v_inst_1536_, lean_object* v_inst_1537_, lean_object* v_e_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1(v_inst_1536_, v_inst_1537_, v_e_1538_, v___y_1539_);
lean_dec(v___y_1539_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg(lean_object* v_inst_1541_, lean_object* v_inst_1542_){
_start:
{
lean_object* v___f_1543_; 
v___f_1543_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1543_, 0, v_inst_1541_);
lean_closure_set(v___f_1543_, 1, v_inst_1542_);
return v___f_1543_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT(lean_object* v_n_1544_, lean_object* v_m_1545_, lean_object* v_inst_1546_, lean_object* v_inst_1547_){
_start:
{
lean_object* v___f_1548_; 
v___f_1548_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1548_, 0, v_inst_1546_);
lean_closure_set(v___f_1548_, 1, v_inst_1547_);
return v___f_1548_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___redArg(lean_object* v_f_1549_, lean_object* v_self_1550_, lean_object* v_a_1551_){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
lean_inc(v_a_1551_);
v___x_1552_ = lean_apply_1(v_f_1549_, v_a_1551_);
v___x_1553_ = lean_apply_1(v_self_1550_, v___x_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___redArg___boxed(lean_object* v_f_1554_, lean_object* v_self_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Lake_MonadLogT_adaptMethods___redArg(v_f_1554_, v_self_1555_, v_a_1556_);
lean_dec(v_a_1556_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods(lean_object* v_n_1558_, lean_object* v_m_1559_, lean_object* v_m_x27_1560_, lean_object* v_00_u03b1_1561_, lean_object* v_inst_1562_, lean_object* v_f_1563_, lean_object* v_self_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
lean_inc(v_a_1565_);
v___x_1566_ = lean_apply_1(v_f_1563_, v_a_1565_);
v___x_1567_ = lean_apply_1(v_self_1564_, v___x_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___boxed(lean_object* v_n_1568_, lean_object* v_m_1569_, lean_object* v_m_x27_1570_, lean_object* v_00_u03b1_1571_, lean_object* v_inst_1572_, lean_object* v_f_1573_, lean_object* v_self_1574_, lean_object* v_a_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_Lake_MonadLogT_adaptMethods(v_n_1568_, v_m_1569_, v_m_x27_1570_, v_00_u03b1_1571_, v_inst_1572_, v_f_1573_, v_self_1574_, v_a_1575_);
lean_dec(v_a_1575_);
lean_dec_ref(v_inst_1572_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog___redArg(lean_object* v_inst_1577_, lean_object* v_self_1578_){
_start:
{
lean_object* v___f_1579_; lean_object* v___x_1580_; 
v___f_1579_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1579_, 0, v_inst_1577_);
v___x_1580_ = lean_apply_1(v_self_1578_, v___f_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog(lean_object* v_m_1581_, lean_object* v_n_1582_, lean_object* v_00_u03b1_1583_, lean_object* v_inst_1584_, lean_object* v_self_1585_){
_start:
{
lean_object* v___f_1586_; lean_object* v___x_1587_; 
v___f_1586_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1586_, 0, v_inst_1584_);
v___x_1587_ = lean_apply_1(v_self_1585_, v___f_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonLog___lam__0(lean_object* v___x_1592_, lean_object* v_x_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_Array_toJson___redArg(v___x_1592_, v_x_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonLog___lam__0(lean_object* v___x_1598_, lean_object* v_x_1599_){
_start:
{
lean_object* v___x_1600_; 
v___x_1600_ = l_Lean_Array_fromJson_x3f___redArg(v___x_1598_, v_x_1599_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1600_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1600_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
v_a_1609_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1600_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1600_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
}
static lean_object* _init_l_Lake_Log_instInhabitedPos_default(void){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = lean_unsigned_to_nat(0u);
return v___x_1620_;
}
}
static lean_object* _init_l_Lake_Log_instInhabitedPos(void){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_unsigned_to_nat(0u);
return v___x_1621_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_instDecidableEqPos_decEq(lean_object* v_x_1622_, lean_object* v_x_1623_){
_start:
{
uint8_t v___x_1624_; 
v___x_1624_ = lean_nat_dec_eq(v_x_1622_, v_x_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_instDecidableEqPos_decEq___boxed(lean_object* v_x_1625_, lean_object* v_x_1626_){
_start:
{
uint8_t v_res_1627_; lean_object* v_r_1628_; 
v_res_1627_ = l_Lake_Log_instDecidableEqPos_decEq(v_x_1625_, v_x_1626_);
lean_dec(v_x_1626_);
lean_dec(v_x_1625_);
v_r_1628_ = lean_box(v_res_1627_);
return v_r_1628_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_instDecidableEqPos(lean_object* v_x_1629_, lean_object* v_x_1630_){
_start:
{
uint8_t v___x_1631_; 
v___x_1631_ = lean_nat_dec_eq(v_x_1629_, v_x_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_instDecidableEqPos___boxed(lean_object* v_x_1632_, lean_object* v_x_1633_){
_start:
{
uint8_t v_res_1634_; lean_object* v_r_1635_; 
v_res_1634_ = l_Lake_Log_instDecidableEqPos(v_x_1632_, v_x_1633_);
lean_dec(v_x_1633_);
lean_dec(v_x_1632_);
v_r_1635_ = lean_box(v_res_1634_);
return v_r_1635_;
}
}
static lean_object* _init_l_Lake_instOfNatPos(void){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = lean_unsigned_to_nat(0u);
return v___x_1636_;
}
}
LEAN_EXPORT uint8_t l_Lake_instOrdPos___lam__0(lean_object* v_x1_1637_, lean_object* v_x2_1638_){
_start:
{
uint8_t v___x_1639_; 
v___x_1639_ = lean_nat_dec_lt(v_x1_1637_, v_x2_1638_);
if (v___x_1639_ == 0)
{
uint8_t v___x_1640_; 
v___x_1640_ = lean_nat_dec_eq(v_x1_1637_, v_x2_1638_);
if (v___x_1640_ == 0)
{
uint8_t v___x_1641_; 
v___x_1641_ = 2;
return v___x_1641_;
}
else
{
uint8_t v___x_1642_; 
v___x_1642_ = 1;
return v___x_1642_;
}
}
else
{
uint8_t v___x_1643_; 
v___x_1643_ = 0;
return v___x_1643_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instOrdPos___lam__0___boxed(lean_object* v_x1_1644_, lean_object* v_x2_1645_){
_start:
{
uint8_t v_res_1646_; lean_object* v_r_1647_; 
v_res_1646_ = l_Lake_instOrdPos___lam__0(v_x1_1644_, v_x2_1645_);
lean_dec(v_x2_1645_);
lean_dec(v_x1_1644_);
v_r_1647_ = lean_box(v_res_1646_);
return v_r_1647_;
}
}
static lean_object* _init_l_Lake_instLTPos(void){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = lean_box(0);
return v___x_1650_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableRelPosLt(lean_object* v_a_1651_, lean_object* v_b_1652_){
_start:
{
uint8_t v___x_1653_; 
v___x_1653_ = lean_nat_dec_lt(v_a_1651_, v_b_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableRelPosLt___boxed(lean_object* v_a_1654_, lean_object* v_b_1655_){
_start:
{
uint8_t v_res_1656_; lean_object* v_r_1657_; 
v_res_1656_ = l_Lake_instDecidableRelPosLt(v_a_1654_, v_b_1655_);
lean_dec(v_b_1655_);
lean_dec(v_a_1654_);
v_r_1657_ = lean_box(v_res_1656_);
return v_r_1657_;
}
}
static lean_object* _init_l_Lake_instLEPos(void){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_box(0);
return v___x_1658_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableRelPosLe(lean_object* v_a_1659_, lean_object* v_b_1660_){
_start:
{
uint8_t v___x_1661_; 
v___x_1661_ = lean_nat_dec_le(v_a_1659_, v_b_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableRelPosLe___boxed(lean_object* v_a_1662_, lean_object* v_b_1663_){
_start:
{
uint8_t v_res_1664_; lean_object* v_r_1665_; 
v_res_1664_ = l_Lake_instDecidableRelPosLe(v_a_1662_, v_b_1663_);
lean_dec(v_b_1663_);
lean_dec(v_a_1662_);
v_r_1665_ = lean_box(v_res_1664_);
return v_r_1665_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMinPos___lam__0(lean_object* v_x_1666_, lean_object* v_y_1667_){
_start:
{
uint8_t v___x_1668_; 
v___x_1668_ = lean_nat_dec_le(v_x_1666_, v_y_1667_);
if (v___x_1668_ == 0)
{
lean_inc(v_y_1667_);
return v_y_1667_;
}
else
{
lean_inc(v_x_1666_);
return v_x_1666_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMinPos___lam__0___boxed(lean_object* v_x_1669_, lean_object* v_y_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Lake_instMinPos___lam__0(v_x_1669_, v_y_1670_);
lean_dec(v_y_1670_);
lean_dec(v_x_1669_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxPos___lam__0(lean_object* v_x_1674_, lean_object* v_y_1675_){
_start:
{
uint8_t v___x_1676_; 
v___x_1676_ = lean_nat_dec_le(v_x_1674_, v_y_1675_);
if (v___x_1676_ == 0)
{
lean_inc(v_x_1674_);
return v_x_1674_;
}
else
{
lean_inc(v_y_1675_);
return v_y_1675_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxPos___lam__0___boxed(lean_object* v_x_1677_, lean_object* v_y_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lake_instMaxPos___lam__0(v_x_1677_, v_y_1678_);
lean_dec(v_y_1678_);
lean_dec(v_x_1677_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_size(lean_object* v_log_1686_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = lean_array_get_size(v_log_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_size___boxed(lean_object* v_log_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Lake_Log_size(v_log_1688_);
lean_dec_ref(v_log_1688_);
return v_res_1689_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_isEmpty(lean_object* v_log_1690_){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; 
v___x_1691_ = lean_array_get_size(v_log_1690_);
v___x_1692_ = lean_unsigned_to_nat(0u);
v___x_1693_ = lean_nat_dec_eq(v___x_1691_, v___x_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_isEmpty___boxed(lean_object* v_log_1694_){
_start:
{
uint8_t v_res_1695_; lean_object* v_r_1696_; 
v_res_1695_ = l_Lake_Log_isEmpty(v_log_1694_);
lean_dec_ref(v_log_1694_);
v_r_1696_ = lean_box(v_res_1695_);
return v_r_1696_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_hasEntries(lean_object* v_log_1697_){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
v___x_1698_ = lean_array_get_size(v_log_1697_);
v___x_1699_ = lean_unsigned_to_nat(0u);
v___x_1700_ = lean_nat_dec_eq(v___x_1698_, v___x_1699_);
if (v___x_1700_ == 0)
{
uint8_t v___x_1701_; 
v___x_1701_ = 1;
return v___x_1701_;
}
else
{
uint8_t v___x_1702_; 
v___x_1702_ = 0;
return v___x_1702_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_hasEntries___boxed(lean_object* v_log_1703_){
_start:
{
uint8_t v_res_1704_; lean_object* v_r_1705_; 
v_res_1704_ = l_Lake_Log_hasEntries(v_log_1703_);
lean_dec_ref(v_log_1703_);
v_r_1705_ = lean_box(v_res_1704_);
return v_r_1705_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_endPos(lean_object* v_log_1706_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = lean_array_get_size(v_log_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_endPos___boxed(lean_object* v_log_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lake_Log_endPos(v_log_1708_);
lean_dec_ref(v_log_1708_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_push(lean_object* v_log_1710_, lean_object* v_e_1711_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = lean_array_push(v_log_1710_, v_e_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_append(lean_object* v_log_1713_, lean_object* v_o_1714_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Array_append___redArg(v_log_1713_, v_o_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_append___boxed(lean_object* v_log_1716_, lean_object* v_o_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lake_Log_append(v_log_1716_, v_o_1717_);
lean_dec_ref(v_o_1717_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_extract(lean_object* v_log_1721_, lean_object* v_start_1722_, lean_object* v_stop_1723_){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = l_Array_extract___redArg(v_log_1721_, v_start_1722_, v_stop_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_extract___boxed(lean_object* v_log_1725_, lean_object* v_start_1726_, lean_object* v_stop_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Lake_Log_extract(v_log_1725_, v_start_1726_, v_stop_1727_);
lean_dec_ref(v_log_1725_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_dropFrom(lean_object* v_log_1729_, lean_object* v_pos_1730_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Array_shrink___redArg(v_log_1729_, v_pos_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_dropFrom___boxed(lean_object* v_log_1732_, lean_object* v_pos_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Lake_Log_dropFrom(v_log_1732_, v_pos_1733_);
lean_dec(v_pos_1733_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_takeFrom(lean_object* v_log_1735_, lean_object* v_pos_1736_){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1737_ = lean_array_get_size(v_log_1735_);
v___x_1738_ = l_Array_extract___redArg(v_log_1735_, v_pos_1736_, v___x_1737_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_takeFrom___boxed(lean_object* v_log_1739_, lean_object* v_pos_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lake_Log_takeFrom(v_log_1739_, v_pos_1740_);
lean_dec_ref(v_log_1739_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_split(lean_object* v_log_1742_, lean_object* v_pos_1743_){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_inc_ref(v_log_1742_);
v___x_1744_ = l_Array_shrink___redArg(v_log_1742_, v_pos_1743_);
v___x_1745_ = lean_array_get_size(v_log_1742_);
v___x_1746_ = l_Array_extract___redArg(v_log_1742_, v_pos_1743_, v___x_1745_);
lean_dec_ref(v_log_1742_);
v___x_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1744_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(lean_object* v_as_1749_, size_t v_i_1750_, size_t v_stop_1751_, lean_object* v_b_1752_){
_start:
{
uint8_t v___x_1753_; 
v___x_1753_ = lean_usize_dec_eq(v_i_1750_, v_stop_1751_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; size_t v___x_1759_; size_t v___x_1760_; 
v___x_1754_ = lean_array_uget_borrowed(v_as_1749_, v_i_1750_);
v___x_1755_ = l_Lake_LogEntry_toString(v___x_1754_, v___x_1753_);
v___x_1756_ = lean_string_append(v_b_1752_, v___x_1755_);
lean_dec_ref(v___x_1755_);
v___x_1757_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0___closed__0));
v___x_1758_ = lean_string_append(v___x_1756_, v___x_1757_);
v___x_1759_ = ((size_t)1ULL);
v___x_1760_ = lean_usize_add(v_i_1750_, v___x_1759_);
v_i_1750_ = v___x_1760_;
v_b_1752_ = v___x_1758_;
goto _start;
}
else
{
return v_b_1752_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0___boxed(lean_object* v_as_1762_, lean_object* v_i_1763_, lean_object* v_stop_1764_, lean_object* v_b_1765_){
_start:
{
size_t v_i_boxed_1766_; size_t v_stop_boxed_1767_; lean_object* v_res_1768_; 
v_i_boxed_1766_ = lean_unbox_usize(v_i_1763_);
lean_dec(v_i_1763_);
v_stop_boxed_1767_ = lean_unbox_usize(v_stop_1764_);
lean_dec(v_stop_1764_);
v_res_1768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(v_as_1762_, v_i_boxed_1766_, v_stop_boxed_1767_, v_b_1765_);
lean_dec_ref(v_as_1762_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_toString(lean_object* v_log_1769_){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1770_ = ((lean_object*)(l_Lake_instInhabitedLogEntry_default___closed__0));
v___x_1771_ = lean_unsigned_to_nat(0u);
v___x_1772_ = lean_array_get_size(v_log_1769_);
v___x_1773_ = lean_nat_dec_lt(v___x_1771_, v___x_1772_);
if (v___x_1773_ == 0)
{
return v___x_1770_;
}
else
{
uint8_t v___x_1774_; 
v___x_1774_ = lean_nat_dec_le(v___x_1772_, v___x_1772_);
if (v___x_1774_ == 0)
{
if (v___x_1773_ == 0)
{
return v___x_1770_;
}
else
{
size_t v___x_1775_; size_t v___x_1776_; lean_object* v___x_1777_; 
v___x_1775_ = ((size_t)0ULL);
v___x_1776_ = lean_usize_of_nat(v___x_1772_);
v___x_1777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(v_log_1769_, v___x_1775_, v___x_1776_, v___x_1770_);
return v___x_1777_;
}
}
else
{
size_t v___x_1778_; size_t v___x_1779_; lean_object* v___x_1780_; 
v___x_1778_ = ((size_t)0ULL);
v___x_1779_ = lean_usize_of_nat(v___x_1772_);
v___x_1780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(v_log_1769_, v___x_1778_, v___x_1779_, v___x_1770_);
return v___x_1780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_toString___boxed(lean_object* v_log_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Lake_Log_toString(v_log_1781_);
lean_dec_ref(v_log_1781_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_replay___redArg___lam__0(lean_object* v_logger_1785_, lean_object* v_x_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = lean_apply_1(v_logger_1785_, v___y_1787_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_replay___redArg(lean_object* v_inst_1789_, lean_object* v_logger_1790_, lean_object* v_log_1791_){
_start:
{
lean_object* v_toApplicative_1792_; lean_object* v_toPure_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v_toApplicative_1792_ = lean_ctor_get(v_inst_1789_, 0);
v_toPure_1793_ = lean_ctor_get(v_toApplicative_1792_, 1);
v___x_1794_ = lean_unsigned_to_nat(0u);
v___x_1795_ = lean_array_get_size(v_log_1791_);
v___x_1796_ = lean_box(0);
v___x_1797_ = lean_nat_dec_lt(v___x_1794_, v___x_1795_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; 
lean_inc(v_toPure_1793_);
lean_dec_ref(v_log_1791_);
lean_dec(v_logger_1790_);
lean_dec_ref(v_inst_1789_);
v___x_1798_ = lean_apply_2(v_toPure_1793_, lean_box(0), v___x_1796_);
return v___x_1798_;
}
else
{
lean_object* v___f_1799_; uint8_t v___x_1800_; 
v___f_1799_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1799_, 0, v_logger_1790_);
v___x_1800_ = lean_nat_dec_le(v___x_1795_, v___x_1795_);
if (v___x_1800_ == 0)
{
if (v___x_1797_ == 0)
{
lean_object* v___x_1801_; 
lean_inc(v_toPure_1793_);
lean_dec_ref(v___f_1799_);
lean_dec_ref(v_log_1791_);
lean_dec_ref(v_inst_1789_);
v___x_1801_ = lean_apply_2(v_toPure_1793_, lean_box(0), v___x_1796_);
return v___x_1801_;
}
else
{
size_t v___x_1802_; size_t v___x_1803_; lean_object* v___x_1804_; 
v___x_1802_ = ((size_t)0ULL);
v___x_1803_ = lean_usize_of_nat(v___x_1795_);
v___x_1804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1789_, v___f_1799_, v_log_1791_, v___x_1802_, v___x_1803_, v___x_1796_);
return v___x_1804_;
}
}
else
{
size_t v___x_1805_; size_t v___x_1806_; lean_object* v___x_1807_; 
v___x_1805_ = ((size_t)0ULL);
v___x_1806_ = lean_usize_of_nat(v___x_1795_);
v___x_1807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1789_, v___f_1799_, v_log_1791_, v___x_1805_, v___x_1806_, v___x_1796_);
return v___x_1807_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_replay(lean_object* v_m_1808_, lean_object* v_inst_1809_, lean_object* v_logger_1810_, lean_object* v_log_1811_){
_start:
{
lean_object* v_toApplicative_1812_; lean_object* v_toPure_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; uint8_t v___x_1817_; 
v_toApplicative_1812_ = lean_ctor_get(v_inst_1809_, 0);
v_toPure_1813_ = lean_ctor_get(v_toApplicative_1812_, 1);
v___x_1814_ = lean_unsigned_to_nat(0u);
v___x_1815_ = lean_array_get_size(v_log_1811_);
v___x_1816_ = lean_box(0);
v___x_1817_ = lean_nat_dec_lt(v___x_1814_, v___x_1815_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; 
lean_inc(v_toPure_1813_);
lean_dec_ref(v_log_1811_);
lean_dec(v_logger_1810_);
lean_dec_ref(v_inst_1809_);
v___x_1818_ = lean_apply_2(v_toPure_1813_, lean_box(0), v___x_1816_);
return v___x_1818_;
}
else
{
lean_object* v___f_1819_; uint8_t v___x_1820_; 
v___f_1819_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1819_, 0, v_logger_1810_);
v___x_1820_ = lean_nat_dec_le(v___x_1815_, v___x_1815_);
if (v___x_1820_ == 0)
{
if (v___x_1817_ == 0)
{
lean_object* v___x_1821_; 
lean_inc(v_toPure_1813_);
lean_dec_ref(v___f_1819_);
lean_dec_ref(v_log_1811_);
lean_dec_ref(v_inst_1809_);
v___x_1821_ = lean_apply_2(v_toPure_1813_, lean_box(0), v___x_1816_);
return v___x_1821_;
}
else
{
size_t v___x_1822_; size_t v___x_1823_; lean_object* v___x_1824_; 
v___x_1822_ = ((size_t)0ULL);
v___x_1823_ = lean_usize_of_nat(v___x_1815_);
v___x_1824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1809_, v___f_1819_, v_log_1811_, v___x_1822_, v___x_1823_, v___x_1816_);
return v___x_1824_;
}
}
else
{
size_t v___x_1825_; size_t v___x_1826_; lean_object* v___x_1827_; 
v___x_1825_ = ((size_t)0ULL);
v___x_1826_ = lean_usize_of_nat(v___x_1815_);
v___x_1827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1809_, v___f_1819_, v_log_1811_, v___x_1825_, v___x_1826_, v___x_1816_);
return v___x_1827_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_filter___lam__0(lean_object* v_f_1828_, lean_object* v_x1_1829_, lean_object* v_x2_1830_){
_start:
{
lean_object* v___x_1831_; uint8_t v___x_1832_; 
lean_inc_ref(v_x2_1830_);
v___x_1831_ = lean_apply_1(v_f_1828_, v_x2_1830_);
v___x_1832_ = lean_unbox(v___x_1831_);
if (v___x_1832_ == 0)
{
lean_dec_ref(v_x2_1830_);
return v_x1_1829_;
}
else
{
lean_object* v___x_1833_; 
v___x_1833_ = lean_array_push(v_x1_1829_, v_x2_1830_);
return v___x_1833_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_filter(lean_object* v_f_1853_, lean_object* v_log_1854_){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; uint8_t v___x_1859_; 
v___x_1855_ = lean_unsigned_to_nat(0u);
v___x_1856_ = lean_array_get_size(v_log_1854_);
v___x_1857_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_1858_ = ((lean_object*)(l_Lake_Log_filter___closed__9));
v___x_1859_ = lean_nat_dec_lt(v___x_1855_, v___x_1856_);
if (v___x_1859_ == 0)
{
lean_dec_ref(v_log_1854_);
lean_dec_ref(v_f_1853_);
return v___x_1857_;
}
else
{
lean_object* v___f_1860_; uint8_t v___x_1861_; 
v___f_1860_ = lean_alloc_closure((void*)(l_Lake_Log_filter___lam__0), 3, 1);
lean_closure_set(v___f_1860_, 0, v_f_1853_);
v___x_1861_ = lean_nat_dec_le(v___x_1856_, v___x_1856_);
if (v___x_1861_ == 0)
{
if (v___x_1859_ == 0)
{
lean_dec_ref(v___f_1860_);
lean_dec_ref(v_log_1854_);
return v___x_1857_;
}
else
{
size_t v___x_1862_; size_t v___x_1863_; lean_object* v___x_1864_; 
v___x_1862_ = ((size_t)0ULL);
v___x_1863_ = lean_usize_of_nat(v___x_1856_);
v___x_1864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1858_, v___f_1860_, v_log_1854_, v___x_1862_, v___x_1863_, v___x_1857_);
return v___x_1864_;
}
}
else
{
size_t v___x_1865_; size_t v___x_1866_; lean_object* v___x_1867_; 
v___x_1865_ = ((size_t)0ULL);
v___x_1866_ = lean_usize_of_nat(v___x_1856_);
v___x_1867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1858_, v___f_1860_, v_log_1854_, v___x_1865_, v___x_1866_, v___x_1857_);
return v___x_1867_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_Log_any___lam__0(lean_object* v_f_1868_, lean_object* v_x_1869_){
_start:
{
lean_object* v___x_1870_; uint8_t v___x_1871_; 
v___x_1870_ = lean_apply_1(v_f_1868_, v_x_1869_);
v___x_1871_ = lean_unbox(v___x_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_any___lam__0___boxed(lean_object* v_f_1872_, lean_object* v_x_1873_){
_start:
{
uint8_t v_res_1874_; lean_object* v_r_1875_; 
v_res_1874_ = l_Lake_Log_any___lam__0(v_f_1872_, v_x_1873_);
v_r_1875_ = lean_box(v_res_1874_);
return v_r_1875_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_any(lean_object* v_f_1876_, lean_object* v_log_1877_){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; uint8_t v___x_1881_; 
v___x_1878_ = lean_unsigned_to_nat(0u);
v___x_1879_ = lean_array_get_size(v_log_1877_);
v___x_1880_ = ((lean_object*)(l_Lake_Log_filter___closed__9));
v___x_1881_ = lean_nat_dec_lt(v___x_1878_, v___x_1879_);
if (v___x_1881_ == 0)
{
lean_dec_ref(v_log_1877_);
lean_dec_ref(v_f_1876_);
return v___x_1881_;
}
else
{
if (v___x_1881_ == 0)
{
lean_dec_ref(v_log_1877_);
lean_dec_ref(v_f_1876_);
return v___x_1881_;
}
else
{
lean_object* v___f_1882_; size_t v___x_1883_; size_t v___x_1884_; lean_object* v___x_1885_; uint8_t v___x_1886_; 
v___f_1882_ = lean_alloc_closure((void*)(l_Lake_Log_any___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1882_, 0, v_f_1876_);
v___x_1883_ = ((size_t)0ULL);
v___x_1884_ = lean_usize_of_nat(v___x_1879_);
v___x_1885_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_1880_, v___f_1882_, v_log_1877_, v___x_1883_, v___x_1884_);
v___x_1886_ = lean_unbox(v___x_1885_);
lean_dec(v___x_1885_);
return v___x_1886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_any___boxed(lean_object* v_f_1887_, lean_object* v_log_1888_){
_start:
{
uint8_t v_res_1889_; lean_object* v_r_1890_; 
v_res_1889_ = l_Lake_Log_any(v_f_1887_, v_log_1888_);
v_r_1890_ = lean_box(v_res_1889_);
return v_r_1890_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(lean_object* v_as_1891_, size_t v_i_1892_, size_t v_stop_1893_, uint8_t v_b_1894_){
_start:
{
uint8_t v___y_1896_; uint8_t v___x_1900_; 
v___x_1900_ = lean_usize_dec_eq(v_i_1892_, v_stop_1893_);
if (v___x_1900_ == 0)
{
lean_object* v___x_1901_; uint8_t v_level_1902_; uint8_t v___x_1903_; 
v___x_1901_ = lean_array_uget_borrowed(v_as_1891_, v_i_1892_);
v_level_1902_ = lean_ctor_get_uint8(v___x_1901_, sizeof(void*)*1);
v___x_1903_ = l_Lake_instOrdLogLevel_ord(v_b_1894_, v_level_1902_);
if (v___x_1903_ == 2)
{
if (v___x_1900_ == 0)
{
v___y_1896_ = v_b_1894_;
goto v___jp_1895_;
}
else
{
v___y_1896_ = v_level_1902_;
goto v___jp_1895_;
}
}
else
{
v___y_1896_ = v_level_1902_;
goto v___jp_1895_;
}
}
else
{
return v_b_1894_;
}
v___jp_1895_:
{
size_t v___x_1897_; size_t v___x_1898_; 
v___x_1897_ = ((size_t)1ULL);
v___x_1898_ = lean_usize_add(v_i_1892_, v___x_1897_);
v_i_1892_ = v___x_1898_;
v_b_1894_ = v___y_1896_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0___boxed(lean_object* v_as_1904_, lean_object* v_i_1905_, lean_object* v_stop_1906_, lean_object* v_b_1907_){
_start:
{
size_t v_i_boxed_1908_; size_t v_stop_boxed_1909_; uint8_t v_b_boxed_1910_; uint8_t v_res_1911_; lean_object* v_r_1912_; 
v_i_boxed_1908_ = lean_unbox_usize(v_i_1905_);
lean_dec(v_i_1905_);
v_stop_boxed_1909_ = lean_unbox_usize(v_stop_1906_);
lean_dec(v_stop_1906_);
v_b_boxed_1910_ = lean_unbox(v_b_1907_);
v_res_1911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(v_as_1904_, v_i_boxed_1908_, v_stop_boxed_1909_, v_b_boxed_1910_);
lean_dec_ref(v_as_1904_);
v_r_1912_ = lean_box(v_res_1911_);
return v_r_1912_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_maxLv(lean_object* v_log_1913_){
_start:
{
uint8_t v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1914_ = 0;
v___x_1915_ = lean_unsigned_to_nat(0u);
v___x_1916_ = lean_array_get_size(v_log_1913_);
v___x_1917_ = lean_nat_dec_lt(v___x_1915_, v___x_1916_);
if (v___x_1917_ == 0)
{
return v___x_1914_;
}
else
{
uint8_t v___x_1918_; 
v___x_1918_ = lean_nat_dec_le(v___x_1916_, v___x_1916_);
if (v___x_1918_ == 0)
{
if (v___x_1917_ == 0)
{
return v___x_1914_;
}
else
{
size_t v___x_1919_; size_t v___x_1920_; uint8_t v___x_1921_; 
v___x_1919_ = ((size_t)0ULL);
v___x_1920_ = lean_usize_of_nat(v___x_1916_);
v___x_1921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(v_log_1913_, v___x_1919_, v___x_1920_, v___x_1914_);
return v___x_1921_;
}
}
else
{
size_t v___x_1922_; size_t v___x_1923_; uint8_t v___x_1924_; 
v___x_1922_ = ((size_t)0ULL);
v___x_1923_ = lean_usize_of_nat(v___x_1916_);
v___x_1924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(v_log_1913_, v___x_1922_, v___x_1923_, v___x_1914_);
return v___x_1924_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_maxLv___boxed(lean_object* v_log_1925_){
_start:
{
uint8_t v_res_1926_; lean_object* v_r_1927_; 
v_res_1926_ = l_Lake_Log_maxLv(v_log_1925_);
lean_dec_ref(v_log_1925_);
v_r_1927_ = lean_box(v_res_1926_);
return v_r_1927_;
}
}
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___redArg___lam__0(lean_object* v_e_1928_, lean_object* v_s_1929_){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1930_ = lean_box(0);
v___x_1931_ = lean_array_push(v_s_1929_, v_e_1928_);
v___x_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1930_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___redArg(lean_object* v_inst_1933_, lean_object* v_e_1934_){
_start:
{
lean_object* v_modifyGet_1935_; lean_object* v___f_1936_; lean_object* v___x_1937_; 
v_modifyGet_1935_ = lean_ctor_get(v_inst_1933_, 2);
lean_inc(v_modifyGet_1935_);
lean_dec_ref(v_inst_1933_);
v___f_1936_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1936_, 0, v_e_1934_);
v___x_1937_ = lean_apply_2(v_modifyGet_1935_, lean_box(0), v___f_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Lake_pushLogEntry(lean_object* v_m_1938_, lean_object* v_inst_1939_, lean_object* v_e_1940_){
_start:
{
lean_object* v_modifyGet_1941_; lean_object* v___f_1942_; lean_object* v___x_1943_; 
v_modifyGet_1941_ = lean_ctor_get(v_inst_1939_, 2);
lean_inc(v_modifyGet_1941_);
lean_dec_ref(v_inst_1939_);
v___f_1942_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1942_, 0, v_e_1940_);
v___x_1943_ = lean_apply_2(v_modifyGet_1941_, lean_box(0), v___f_1942_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_ofMonadState___redArg(lean_object* v_inst_1944_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(v___x_1945_, 0, lean_box(0));
lean_closure_set(v___x_1945_, 1, v_inst_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_ofMonadState(lean_object* v_m_1946_, lean_object* v_inst_1947_){
_start:
{
lean_object* v___x_1948_; 
v___x_1948_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(v___x_1948_, 0, lean_box(0));
lean_closure_set(v___x_1948_, 1, v_inst_1947_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog___redArg(lean_object* v_inst_1949_){
_start:
{
lean_object* v_get_1950_; 
v_get_1950_ = lean_ctor_get(v_inst_1949_, 0);
lean_inc(v_get_1950_);
return v_get_1950_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog___redArg___boxed(lean_object* v_inst_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_Lake_getLog___redArg(v_inst_1951_);
lean_dec_ref(v_inst_1951_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog(lean_object* v_m_1953_, lean_object* v_inst_1954_){
_start:
{
lean_object* v_get_1955_; 
v_get_1955_ = lean_ctor_get(v_inst_1954_, 0);
lean_inc(v_get_1955_);
return v_get_1955_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog___boxed(lean_object* v_m_1956_, lean_object* v_inst_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lake_getLog(v_m_1956_, v_inst_1957_);
lean_dec_ref(v_inst_1957_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg___lam__0(lean_object* v_x_1959_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = lean_array_get_size(v_x_1959_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg___lam__0___boxed(lean_object* v_x_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_Lake_getLogPos___redArg___lam__0(v_x_1961_);
lean_dec_ref(v_x_1961_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg(lean_object* v_inst_1964_, lean_object* v_inst_1965_){
_start:
{
lean_object* v_map_1966_; lean_object* v_get_1967_; lean_object* v___f_1968_; lean_object* v___x_1969_; 
v_map_1966_ = lean_ctor_get(v_inst_1964_, 0);
lean_inc(v_map_1966_);
lean_dec_ref(v_inst_1964_);
v_get_1967_ = lean_ctor_get(v_inst_1965_, 0);
lean_inc(v_get_1967_);
lean_dec_ref(v_inst_1965_);
v___f_1968_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_1969_ = lean_apply_4(v_map_1966_, lean_box(0), lean_box(0), v___f_1968_, v_get_1967_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos(lean_object* v_m_1970_, lean_object* v_inst_1971_, lean_object* v_inst_1972_){
_start:
{
lean_object* v_map_1973_; lean_object* v_get_1974_; lean_object* v___f_1975_; lean_object* v___x_1976_; 
v_map_1973_ = lean_ctor_get(v_inst_1971_, 0);
lean_inc(v_map_1973_);
lean_dec_ref(v_inst_1971_);
v_get_1974_ = lean_ctor_get(v_inst_1972_, 0);
lean_inc(v_get_1974_);
lean_dec_ref(v_inst_1972_);
v___f_1975_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_1976_ = lean_apply_4(v_map_1973_, lean_box(0), lean_box(0), v___f_1975_, v_get_1974_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLog___redArg___lam__0(lean_object* v_log_1977_){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_1979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1979_, 0, v_log_1977_);
lean_ctor_set(v___x_1979_, 1, v___x_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLog___redArg(lean_object* v_inst_1981_){
_start:
{
lean_object* v_modifyGet_1982_; lean_object* v___f_1983_; lean_object* v___x_1984_; 
v_modifyGet_1982_ = lean_ctor_get(v_inst_1981_, 2);
lean_inc(v_modifyGet_1982_);
lean_dec_ref(v_inst_1981_);
v___f_1983_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_1984_ = lean_apply_2(v_modifyGet_1982_, lean_box(0), v___f_1983_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLog(lean_object* v_m_1985_, lean_object* v_inst_1986_){
_start:
{
lean_object* v_modifyGet_1987_; lean_object* v___f_1988_; lean_object* v___x_1989_; 
v_modifyGet_1987_ = lean_ctor_get(v_inst_1986_, 2);
lean_inc(v_modifyGet_1987_);
lean_dec_ref(v_inst_1986_);
v___f_1988_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_1989_ = lean_apply_2(v_modifyGet_1987_, lean_box(0), v___f_1988_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLogFrom___redArg___lam__0(lean_object* v_pos_1990_, lean_object* v_log_1991_){
_start:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1992_ = lean_array_get_size(v_log_1991_);
lean_inc(v_pos_1990_);
v___x_1993_ = l_Array_extract___redArg(v_log_1991_, v_pos_1990_, v___x_1992_);
v___x_1994_ = l_Array_shrink___redArg(v_log_1991_, v_pos_1990_);
lean_dec(v_pos_1990_);
v___x_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1993_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLogFrom___redArg(lean_object* v_inst_1996_, lean_object* v_pos_1997_){
_start:
{
lean_object* v_modifyGet_1998_; lean_object* v___f_1999_; lean_object* v___x_2000_; 
v_modifyGet_1998_ = lean_ctor_get(v_inst_1996_, 2);
lean_inc(v_modifyGet_1998_);
lean_dec_ref(v_inst_1996_);
v___f_1999_ = lean_alloc_closure((void*)(l_Lake_takeLogFrom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1999_, 0, v_pos_1997_);
v___x_2000_ = lean_apply_2(v_modifyGet_1998_, lean_box(0), v___f_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLogFrom(lean_object* v_m_2001_, lean_object* v_inst_2002_, lean_object* v_pos_2003_){
_start:
{
lean_object* v_modifyGet_2004_; lean_object* v___f_2005_; lean_object* v___x_2006_; 
v_modifyGet_2004_ = lean_ctor_get(v_inst_2002_, 2);
lean_inc(v_modifyGet_2004_);
lean_dec_ref(v_inst_2002_);
v___f_2005_ = lean_alloc_closure((void*)(l_Lake_takeLogFrom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2005_, 0, v_pos_2003_);
v___x_2006_ = lean_apply_2(v_modifyGet_2004_, lean_box(0), v___f_2005_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg___lam__0(lean_object* v_pos_2007_, lean_object* v_s_2008_){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2009_ = lean_box(0);
v___x_2010_ = l_Array_shrink___redArg(v_s_2008_, v_pos_2007_);
v___x_2011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2009_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg___lam__0___boxed(lean_object* v_pos_2012_, lean_object* v_s_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lake_dropLogFrom___redArg___lam__0(v_pos_2012_, v_s_2013_);
lean_dec(v_pos_2012_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg(lean_object* v_inst_2015_, lean_object* v_pos_2016_){
_start:
{
lean_object* v_modifyGet_2017_; lean_object* v___f_2018_; lean_object* v___x_2019_; 
v_modifyGet_2017_ = lean_ctor_get(v_inst_2015_, 2);
lean_inc(v_modifyGet_2017_);
lean_dec_ref(v_inst_2015_);
v___f_2018_ = lean_alloc_closure((void*)(l_Lake_dropLogFrom___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2018_, 0, v_pos_2016_);
v___x_2019_ = lean_apply_2(v_modifyGet_2017_, lean_box(0), v___f_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom(lean_object* v_m_2020_, lean_object* v_inst_2021_, lean_object* v_pos_2022_){
_start:
{
lean_object* v_modifyGet_2023_; lean_object* v___f_2024_; lean_object* v___x_2025_; 
v_modifyGet_2023_ = lean_ctor_get(v_inst_2021_, 2);
lean_inc(v_modifyGet_2023_);
lean_dec_ref(v_inst_2021_);
v___f_2024_ = lean_alloc_closure((void*)(l_Lake_dropLogFrom___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2024_, 0, v_pos_2022_);
v___x_2025_ = lean_apply_2(v_modifyGet_2023_, lean_box(0), v___f_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__1(lean_object* v_iniPos_2026_, lean_object* v_toPure_2027_, lean_object* v_log_2028_){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2029_ = lean_array_get_size(v_log_2028_);
v___x_2030_ = l_Array_extract___redArg(v_log_2028_, v_iniPos_2026_, v___x_2029_);
v___x_2031_ = lean_apply_2(v_toPure_2027_, lean_box(0), v___x_2030_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__1___boxed(lean_object* v_iniPos_2032_, lean_object* v_toPure_2033_, lean_object* v_log_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Lake_extractLog___redArg___lam__1(v_iniPos_2032_, v_toPure_2033_, v_log_2034_);
lean_dec_ref(v_log_2034_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__0(lean_object* v_toBind_2036_, lean_object* v_get_2037_, lean_object* v___f_2038_, lean_object* v_____r_2039_){
_start:
{
lean_object* v___x_2040_; 
v___x_2040_ = lean_apply_4(v_toBind_2036_, lean_box(0), lean_box(0), v_get_2037_, v___f_2038_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__2(lean_object* v_toPure_2041_, lean_object* v_toBind_2042_, lean_object* v_get_2043_, lean_object* v_x_2044_, lean_object* v_iniPos_2045_){
_start:
{
lean_object* v___f_2046_; lean_object* v___f_2047_; lean_object* v___x_2048_; 
v___f_2046_ = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2046_, 0, v_iniPos_2045_);
lean_closure_set(v___f_2046_, 1, v_toPure_2041_);
lean_inc(v_toBind_2042_);
v___f_2047_ = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2047_, 0, v_toBind_2042_);
lean_closure_set(v___f_2047_, 1, v_get_2043_);
lean_closure_set(v___f_2047_, 2, v___f_2046_);
v___x_2048_ = lean_apply_4(v_toBind_2042_, lean_box(0), lean_box(0), v_x_2044_, v___f_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg(lean_object* v_inst_2049_, lean_object* v_inst_2050_, lean_object* v_x_2051_){
_start:
{
lean_object* v_toApplicative_2052_; lean_object* v_toFunctor_2053_; lean_object* v_toBind_2054_; lean_object* v_toPure_2055_; lean_object* v_map_2056_; lean_object* v_get_2057_; lean_object* v___f_2058_; lean_object* v___f_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v_toApplicative_2052_ = lean_ctor_get(v_inst_2049_, 0);
lean_inc_ref(v_toApplicative_2052_);
v_toFunctor_2053_ = lean_ctor_get(v_toApplicative_2052_, 0);
lean_inc_ref(v_toFunctor_2053_);
v_toBind_2054_ = lean_ctor_get(v_inst_2049_, 1);
lean_inc_n(v_toBind_2054_, 2);
lean_dec_ref(v_inst_2049_);
v_toPure_2055_ = lean_ctor_get(v_toApplicative_2052_, 1);
lean_inc(v_toPure_2055_);
lean_dec_ref(v_toApplicative_2052_);
v_map_2056_ = lean_ctor_get(v_toFunctor_2053_, 0);
lean_inc(v_map_2056_);
lean_dec_ref(v_toFunctor_2053_);
v_get_2057_ = lean_ctor_get(v_inst_2050_, 0);
lean_inc_n(v_get_2057_, 2);
lean_dec_ref(v_inst_2050_);
v___f_2058_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2059_ = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2059_, 0, v_toPure_2055_);
lean_closure_set(v___f_2059_, 1, v_toBind_2054_);
lean_closure_set(v___f_2059_, 2, v_get_2057_);
lean_closure_set(v___f_2059_, 3, v_x_2051_);
v___x_2060_ = lean_apply_4(v_map_2056_, lean_box(0), lean_box(0), v___f_2058_, v_get_2057_);
v___x_2061_ = lean_apply_4(v_toBind_2054_, lean_box(0), lean_box(0), v___x_2060_, v___f_2059_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog(lean_object* v_m_2062_, lean_object* v_inst_2063_, lean_object* v_inst_2064_, lean_object* v_x_2065_){
_start:
{
lean_object* v_toApplicative_2066_; lean_object* v_toFunctor_2067_; lean_object* v_toBind_2068_; lean_object* v_toPure_2069_; lean_object* v_map_2070_; lean_object* v_get_2071_; lean_object* v___f_2072_; lean_object* v___f_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v_toApplicative_2066_ = lean_ctor_get(v_inst_2063_, 0);
lean_inc_ref(v_toApplicative_2066_);
v_toFunctor_2067_ = lean_ctor_get(v_toApplicative_2066_, 0);
lean_inc_ref(v_toFunctor_2067_);
v_toBind_2068_ = lean_ctor_get(v_inst_2063_, 1);
lean_inc_n(v_toBind_2068_, 2);
lean_dec_ref(v_inst_2063_);
v_toPure_2069_ = lean_ctor_get(v_toApplicative_2066_, 1);
lean_inc(v_toPure_2069_);
lean_dec_ref(v_toApplicative_2066_);
v_map_2070_ = lean_ctor_get(v_toFunctor_2067_, 0);
lean_inc(v_map_2070_);
lean_dec_ref(v_toFunctor_2067_);
v_get_2071_ = lean_ctor_get(v_inst_2064_, 0);
lean_inc_n(v_get_2071_, 2);
lean_dec_ref(v_inst_2064_);
v___f_2072_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2073_ = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2073_, 0, v_toPure_2069_);
lean_closure_set(v___f_2073_, 1, v_toBind_2068_);
lean_closure_set(v___f_2073_, 2, v_get_2071_);
lean_closure_set(v___f_2073_, 3, v_x_2065_);
v___x_2074_ = lean_apply_4(v_map_2070_, lean_box(0), lean_box(0), v___f_2072_, v_get_2071_);
v___x_2075_ = lean_apply_4(v_toBind_2068_, lean_box(0), lean_box(0), v___x_2074_, v___f_2073_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__1(lean_object* v_iniPos_2076_, lean_object* v_a_2077_, lean_object* v_toPure_2078_, lean_object* v_log_2079_){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2080_ = lean_array_get_size(v_log_2079_);
v___x_2081_ = l_Array_extract___redArg(v_log_2079_, v_iniPos_2076_, v___x_2080_);
v___x_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2082_, 0, v_a_2077_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
v___x_2083_ = lean_apply_2(v_toPure_2078_, lean_box(0), v___x_2082_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__1___boxed(lean_object* v_iniPos_2084_, lean_object* v_a_2085_, lean_object* v_toPure_2086_, lean_object* v_log_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l_Lake_withExtractLog___redArg___lam__1(v_iniPos_2084_, v_a_2085_, v_toPure_2086_, v_log_2087_);
lean_dec_ref(v_log_2087_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__0(lean_object* v_iniPos_2089_, lean_object* v_toPure_2090_, lean_object* v_toBind_2091_, lean_object* v_get_2092_, lean_object* v_a_2093_){
_start:
{
lean_object* v___f_2094_; lean_object* v___x_2095_; 
v___f_2094_ = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2094_, 0, v_iniPos_2089_);
lean_closure_set(v___f_2094_, 1, v_a_2093_);
lean_closure_set(v___f_2094_, 2, v_toPure_2090_);
v___x_2095_ = lean_apply_4(v_toBind_2091_, lean_box(0), lean_box(0), v_get_2092_, v___f_2094_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__2(lean_object* v_toPure_2096_, lean_object* v_toBind_2097_, lean_object* v_get_2098_, lean_object* v_x_2099_, lean_object* v_iniPos_2100_){
_start:
{
lean_object* v___f_2101_; lean_object* v___x_2102_; 
lean_inc(v_toBind_2097_);
v___f_2101_ = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2101_, 0, v_iniPos_2100_);
lean_closure_set(v___f_2101_, 1, v_toPure_2096_);
lean_closure_set(v___f_2101_, 2, v_toBind_2097_);
lean_closure_set(v___f_2101_, 3, v_get_2098_);
v___x_2102_ = lean_apply_4(v_toBind_2097_, lean_box(0), lean_box(0), v_x_2099_, v___f_2101_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg(lean_object* v_inst_2103_, lean_object* v_inst_2104_, lean_object* v_x_2105_){
_start:
{
lean_object* v_toApplicative_2106_; lean_object* v_toFunctor_2107_; lean_object* v_toBind_2108_; lean_object* v_toPure_2109_; lean_object* v_map_2110_; lean_object* v_get_2111_; lean_object* v___f_2112_; lean_object* v___f_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v_toApplicative_2106_ = lean_ctor_get(v_inst_2103_, 0);
lean_inc_ref(v_toApplicative_2106_);
v_toFunctor_2107_ = lean_ctor_get(v_toApplicative_2106_, 0);
lean_inc_ref(v_toFunctor_2107_);
v_toBind_2108_ = lean_ctor_get(v_inst_2103_, 1);
lean_inc_n(v_toBind_2108_, 2);
lean_dec_ref(v_inst_2103_);
v_toPure_2109_ = lean_ctor_get(v_toApplicative_2106_, 1);
lean_inc(v_toPure_2109_);
lean_dec_ref(v_toApplicative_2106_);
v_map_2110_ = lean_ctor_get(v_toFunctor_2107_, 0);
lean_inc(v_map_2110_);
lean_dec_ref(v_toFunctor_2107_);
v_get_2111_ = lean_ctor_get(v_inst_2104_, 0);
lean_inc_n(v_get_2111_, 2);
lean_dec_ref(v_inst_2104_);
v___f_2112_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2113_ = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2113_, 0, v_toPure_2109_);
lean_closure_set(v___f_2113_, 1, v_toBind_2108_);
lean_closure_set(v___f_2113_, 2, v_get_2111_);
lean_closure_set(v___f_2113_, 3, v_x_2105_);
v___x_2114_ = lean_apply_4(v_map_2110_, lean_box(0), lean_box(0), v___f_2112_, v_get_2111_);
v___x_2115_ = lean_apply_4(v_toBind_2108_, lean_box(0), lean_box(0), v___x_2114_, v___f_2113_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog(lean_object* v_m_2116_, lean_object* v_00_u03b1_2117_, lean_object* v_inst_2118_, lean_object* v_inst_2119_, lean_object* v_x_2120_){
_start:
{
lean_object* v_toApplicative_2121_; lean_object* v_toFunctor_2122_; lean_object* v_toBind_2123_; lean_object* v_toPure_2124_; lean_object* v_map_2125_; lean_object* v_get_2126_; lean_object* v___f_2127_; lean_object* v___f_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v_toApplicative_2121_ = lean_ctor_get(v_inst_2118_, 0);
lean_inc_ref(v_toApplicative_2121_);
v_toFunctor_2122_ = lean_ctor_get(v_toApplicative_2121_, 0);
lean_inc_ref(v_toFunctor_2122_);
v_toBind_2123_ = lean_ctor_get(v_inst_2118_, 1);
lean_inc_n(v_toBind_2123_, 2);
lean_dec_ref(v_inst_2118_);
v_toPure_2124_ = lean_ctor_get(v_toApplicative_2121_, 1);
lean_inc(v_toPure_2124_);
lean_dec_ref(v_toApplicative_2121_);
v_map_2125_ = lean_ctor_get(v_toFunctor_2122_, 0);
lean_inc(v_map_2125_);
lean_dec_ref(v_toFunctor_2122_);
v_get_2126_ = lean_ctor_get(v_inst_2119_, 0);
lean_inc_n(v_get_2126_, 2);
lean_dec_ref(v_inst_2119_);
v___f_2127_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2128_ = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2128_, 0, v_toPure_2124_);
lean_closure_set(v___f_2128_, 1, v_toBind_2123_);
lean_closure_set(v___f_2128_, 2, v_get_2126_);
lean_closure_set(v___f_2128_, 3, v_x_2120_);
v___x_2129_ = lean_apply_4(v_map_2125_, lean_box(0), lean_box(0), v___f_2127_, v_get_2126_);
v___x_2130_ = lean_apply_4(v_toBind_2123_, lean_box(0), lean_box(0), v___x_2129_, v___f_2128_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__1(lean_object* v_iniPos_2131_, lean_object* v_inst_2132_, lean_object* v_toPure_2133_, lean_object* v_a_2134_, lean_object* v_endPos_2135_){
_start:
{
uint8_t v___x_2136_; 
v___x_2136_ = lean_nat_dec_eq(v_iniPos_2131_, v_endPos_2135_);
if (v___x_2136_ == 0)
{
lean_object* v_throw_2137_; lean_object* v___x_2138_; 
lean_dec(v_a_2134_);
lean_dec(v_toPure_2133_);
v_throw_2137_ = lean_ctor_get(v_inst_2132_, 0);
lean_inc(v_throw_2137_);
lean_dec_ref(v_inst_2132_);
v___x_2138_ = lean_apply_2(v_throw_2137_, lean_box(0), v_iniPos_2131_);
return v___x_2138_;
}
else
{
lean_object* v___x_2139_; 
lean_dec_ref(v_inst_2132_);
lean_dec(v_iniPos_2131_);
v___x_2139_ = lean_apply_2(v_toPure_2133_, lean_box(0), v_a_2134_);
return v___x_2139_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__1___boxed(lean_object* v_iniPos_2140_, lean_object* v_inst_2141_, lean_object* v_toPure_2142_, lean_object* v_a_2143_, lean_object* v_endPos_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l_Lake_throwIfLogs___redArg___lam__1(v_iniPos_2140_, v_inst_2141_, v_toPure_2142_, v_a_2143_, v_endPos_2144_);
lean_dec(v_endPos_2144_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__0(lean_object* v_iniPos_2146_, lean_object* v_inst_2147_, lean_object* v_toPure_2148_, lean_object* v_toBind_2149_, lean_object* v___x_2150_, lean_object* v_a_2151_){
_start:
{
lean_object* v___f_2152_; lean_object* v___x_2153_; 
v___f_2152_ = lean_alloc_closure((void*)(l_Lake_throwIfLogs___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2152_, 0, v_iniPos_2146_);
lean_closure_set(v___f_2152_, 1, v_inst_2147_);
lean_closure_set(v___f_2152_, 2, v_toPure_2148_);
lean_closure_set(v___f_2152_, 3, v_a_2151_);
v___x_2153_ = lean_apply_4(v_toBind_2149_, lean_box(0), lean_box(0), v___x_2150_, v___f_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__2(lean_object* v_inst_2154_, lean_object* v_toPure_2155_, lean_object* v_toBind_2156_, lean_object* v___x_2157_, lean_object* v_x_2158_, lean_object* v_iniPos_2159_){
_start:
{
lean_object* v___f_2160_; lean_object* v___x_2161_; 
lean_inc(v_toBind_2156_);
v___f_2160_ = lean_alloc_closure((void*)(l_Lake_throwIfLogs___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2160_, 0, v_iniPos_2159_);
lean_closure_set(v___f_2160_, 1, v_inst_2154_);
lean_closure_set(v___f_2160_, 2, v_toPure_2155_);
lean_closure_set(v___f_2160_, 3, v_toBind_2156_);
lean_closure_set(v___f_2160_, 4, v___x_2157_);
v___x_2161_ = lean_apply_4(v_toBind_2156_, lean_box(0), lean_box(0), v_x_2158_, v___f_2160_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg(lean_object* v_inst_2162_, lean_object* v_inst_2163_, lean_object* v_inst_2164_, lean_object* v_x_2165_){
_start:
{
lean_object* v_toApplicative_2166_; lean_object* v_toFunctor_2167_; lean_object* v_toBind_2168_; lean_object* v_toPure_2169_; lean_object* v_map_2170_; lean_object* v_get_2171_; lean_object* v___f_2172_; lean_object* v___x_2173_; lean_object* v___f_2174_; lean_object* v___x_2175_; 
v_toApplicative_2166_ = lean_ctor_get(v_inst_2162_, 0);
lean_inc_ref(v_toApplicative_2166_);
v_toFunctor_2167_ = lean_ctor_get(v_toApplicative_2166_, 0);
lean_inc_ref(v_toFunctor_2167_);
v_toBind_2168_ = lean_ctor_get(v_inst_2162_, 1);
lean_inc_n(v_toBind_2168_, 2);
lean_dec_ref(v_inst_2162_);
v_toPure_2169_ = lean_ctor_get(v_toApplicative_2166_, 1);
lean_inc(v_toPure_2169_);
lean_dec_ref(v_toApplicative_2166_);
v_map_2170_ = lean_ctor_get(v_toFunctor_2167_, 0);
lean_inc(v_map_2170_);
lean_dec_ref(v_toFunctor_2167_);
v_get_2171_ = lean_ctor_get(v_inst_2163_, 0);
lean_inc(v_get_2171_);
lean_dec_ref(v_inst_2163_);
v___f_2172_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_2173_ = lean_apply_4(v_map_2170_, lean_box(0), lean_box(0), v___f_2172_, v_get_2171_);
lean_inc(v___x_2173_);
v___f_2174_ = lean_alloc_closure((void*)(l_Lake_throwIfLogs___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2174_, 0, v_inst_2164_);
lean_closure_set(v___f_2174_, 1, v_toPure_2169_);
lean_closure_set(v___f_2174_, 2, v_toBind_2168_);
lean_closure_set(v___f_2174_, 3, v___x_2173_);
lean_closure_set(v___f_2174_, 4, v_x_2165_);
v___x_2175_ = lean_apply_4(v_toBind_2168_, lean_box(0), lean_box(0), v___x_2173_, v___f_2174_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs(lean_object* v_m_2176_, lean_object* v_00_u03b1_2177_, lean_object* v_inst_2178_, lean_object* v_inst_2179_, lean_object* v_inst_2180_, lean_object* v_x_2181_){
_start:
{
lean_object* v_toApplicative_2182_; lean_object* v_toFunctor_2183_; lean_object* v_toBind_2184_; lean_object* v_toPure_2185_; lean_object* v_map_2186_; lean_object* v_get_2187_; lean_object* v___f_2188_; lean_object* v___x_2189_; lean_object* v___f_2190_; lean_object* v___x_2191_; 
v_toApplicative_2182_ = lean_ctor_get(v_inst_2178_, 0);
lean_inc_ref(v_toApplicative_2182_);
v_toFunctor_2183_ = lean_ctor_get(v_toApplicative_2182_, 0);
lean_inc_ref(v_toFunctor_2183_);
v_toBind_2184_ = lean_ctor_get(v_inst_2178_, 1);
lean_inc_n(v_toBind_2184_, 2);
lean_dec_ref(v_inst_2178_);
v_toPure_2185_ = lean_ctor_get(v_toApplicative_2182_, 1);
lean_inc(v_toPure_2185_);
lean_dec_ref(v_toApplicative_2182_);
v_map_2186_ = lean_ctor_get(v_toFunctor_2183_, 0);
lean_inc(v_map_2186_);
lean_dec_ref(v_toFunctor_2183_);
v_get_2187_ = lean_ctor_get(v_inst_2179_, 0);
lean_inc(v_get_2187_);
lean_dec_ref(v_inst_2179_);
v___f_2188_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_2189_ = lean_apply_4(v_map_2186_, lean_box(0), lean_box(0), v___f_2188_, v_get_2187_);
lean_inc(v___x_2189_);
v___f_2190_ = lean_alloc_closure((void*)(l_Lake_throwIfLogs___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2190_, 0, v_inst_2180_);
lean_closure_set(v___f_2190_, 1, v_toPure_2185_);
lean_closure_set(v___f_2190_, 2, v_toBind_2184_);
lean_closure_set(v___f_2190_, 3, v___x_2189_);
lean_closure_set(v___f_2190_, 4, v_x_2181_);
v___x_2191_ = lean_apply_4(v_toBind_2184_, lean_box(0), lean_box(0), v___x_2189_, v___f_2190_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__1(lean_object* v_throw_2192_, lean_object* v_iniPos_2193_, lean_object* v_x_2194_){
_start:
{
lean_object* v___x_2195_; 
v___x_2195_ = lean_apply_2(v_throw_2192_, lean_box(0), v_iniPos_2193_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__1___boxed(lean_object* v_throw_2196_, lean_object* v_iniPos_2197_, lean_object* v_x_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lake_withLogErrorPos___redArg___lam__1(v_throw_2196_, v_iniPos_2197_, v_x_2198_);
lean_dec(v_x_2198_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__0(lean_object* v_inst_2200_, lean_object* v_self_2201_, lean_object* v_iniPos_2202_){
_start:
{
lean_object* v_throw_2203_; lean_object* v_tryCatch_2204_; lean_object* v___f_2205_; lean_object* v___x_2206_; 
v_throw_2203_ = lean_ctor_get(v_inst_2200_, 0);
lean_inc(v_throw_2203_);
v_tryCatch_2204_ = lean_ctor_get(v_inst_2200_, 1);
lean_inc(v_tryCatch_2204_);
lean_dec_ref(v_inst_2200_);
v___f_2205_ = lean_alloc_closure((void*)(l_Lake_withLogErrorPos___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2205_, 0, v_throw_2203_);
lean_closure_set(v___f_2205_, 1, v_iniPos_2202_);
v___x_2206_ = lean_apply_3(v_tryCatch_2204_, lean_box(0), v_self_2201_, v___f_2205_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg(lean_object* v_inst_2207_, lean_object* v_inst_2208_, lean_object* v_inst_2209_, lean_object* v_self_2210_){
_start:
{
lean_object* v_toApplicative_2211_; lean_object* v_toFunctor_2212_; lean_object* v_toBind_2213_; lean_object* v_map_2214_; lean_object* v_get_2215_; lean_object* v___f_2216_; lean_object* v___f_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v_toApplicative_2211_ = lean_ctor_get(v_inst_2207_, 0);
v_toFunctor_2212_ = lean_ctor_get(v_toApplicative_2211_, 0);
lean_inc_ref(v_toFunctor_2212_);
v_toBind_2213_ = lean_ctor_get(v_inst_2207_, 1);
lean_inc(v_toBind_2213_);
lean_dec_ref(v_inst_2207_);
v_map_2214_ = lean_ctor_get(v_toFunctor_2212_, 0);
lean_inc(v_map_2214_);
lean_dec_ref(v_toFunctor_2212_);
v_get_2215_ = lean_ctor_get(v_inst_2208_, 0);
lean_inc(v_get_2215_);
lean_dec_ref(v_inst_2208_);
v___f_2216_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2217_ = lean_alloc_closure((void*)(l_Lake_withLogErrorPos___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2217_, 0, v_inst_2209_);
lean_closure_set(v___f_2217_, 1, v_self_2210_);
v___x_2218_ = lean_apply_4(v_map_2214_, lean_box(0), lean_box(0), v___f_2216_, v_get_2215_);
v___x_2219_ = lean_apply_4(v_toBind_2213_, lean_box(0), lean_box(0), v___x_2218_, v___f_2217_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos(lean_object* v_m_2220_, lean_object* v_00_u03b1_2221_, lean_object* v_inst_2222_, lean_object* v_inst_2223_, lean_object* v_inst_2224_, lean_object* v_self_2225_){
_start:
{
lean_object* v_toApplicative_2226_; lean_object* v_toFunctor_2227_; lean_object* v_toBind_2228_; lean_object* v_map_2229_; lean_object* v_get_2230_; lean_object* v___f_2231_; lean_object* v___f_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v_toApplicative_2226_ = lean_ctor_get(v_inst_2222_, 0);
v_toFunctor_2227_ = lean_ctor_get(v_toApplicative_2226_, 0);
lean_inc_ref(v_toFunctor_2227_);
v_toBind_2228_ = lean_ctor_get(v_inst_2222_, 1);
lean_inc(v_toBind_2228_);
lean_dec_ref(v_inst_2222_);
v_map_2229_ = lean_ctor_get(v_toFunctor_2227_, 0);
lean_inc(v_map_2229_);
lean_dec_ref(v_toFunctor_2227_);
v_get_2230_ = lean_ctor_get(v_inst_2223_, 0);
lean_inc(v_get_2230_);
lean_dec_ref(v_inst_2223_);
v___f_2231_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2232_ = lean_alloc_closure((void*)(l_Lake_withLogErrorPos___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2232_, 0, v_inst_2224_);
lean_closure_set(v___f_2232_, 1, v_self_2225_);
v___x_2233_ = lean_apply_4(v_map_2229_, lean_box(0), lean_box(0), v___f_2231_, v_get_2230_);
v___x_2234_ = lean_apply_4(v_toBind_2228_, lean_box(0), lean_box(0), v___x_2233_, v___f_2232_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__1(lean_object* v_toPure_2235_, lean_object* v_x_2236_){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = lean_box(0);
v___x_2238_ = lean_apply_2(v_toPure_2235_, lean_box(0), v___x_2237_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__1___boxed(lean_object* v_toPure_2239_, lean_object* v_x_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lake_errorWithLog___redArg___lam__1(v_toPure_2239_, v_x_2240_);
lean_dec(v_x_2240_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__0(lean_object* v_throw_2242_, lean_object* v_iniPos_2243_, lean_object* v_____r_2244_){
_start:
{
lean_object* v___x_2245_; 
v___x_2245_ = lean_apply_2(v_throw_2242_, lean_box(0), v_iniPos_2243_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__2(lean_object* v_inst_2246_, lean_object* v_self_2247_, lean_object* v___f_2248_, lean_object* v_toBind_2249_, lean_object* v_iniPos_2250_){
_start:
{
lean_object* v_throw_2251_; lean_object* v_tryCatch_2252_; lean_object* v___f_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v_throw_2251_ = lean_ctor_get(v_inst_2246_, 0);
lean_inc(v_throw_2251_);
v_tryCatch_2252_ = lean_ctor_get(v_inst_2246_, 1);
lean_inc(v_tryCatch_2252_);
lean_dec_ref(v_inst_2246_);
v___f_2253_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2253_, 0, v_throw_2251_);
lean_closure_set(v___f_2253_, 1, v_iniPos_2250_);
v___x_2254_ = lean_apply_3(v_tryCatch_2252_, lean_box(0), v_self_2247_, v___f_2248_);
v___x_2255_ = lean_apply_4(v_toBind_2249_, lean_box(0), lean_box(0), v___x_2254_, v___f_2253_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg(lean_object* v_inst_2256_, lean_object* v_inst_2257_, lean_object* v_inst_2258_, lean_object* v_self_2259_){
_start:
{
lean_object* v_toApplicative_2260_; lean_object* v_toFunctor_2261_; lean_object* v_toBind_2262_; lean_object* v_toPure_2263_; lean_object* v_map_2264_; lean_object* v_get_2265_; lean_object* v___f_2266_; lean_object* v___f_2267_; lean_object* v___f_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v_toApplicative_2260_ = lean_ctor_get(v_inst_2256_, 0);
lean_inc_ref(v_toApplicative_2260_);
v_toFunctor_2261_ = lean_ctor_get(v_toApplicative_2260_, 0);
lean_inc_ref(v_toFunctor_2261_);
v_toBind_2262_ = lean_ctor_get(v_inst_2256_, 1);
lean_inc_n(v_toBind_2262_, 2);
lean_dec_ref(v_inst_2256_);
v_toPure_2263_ = lean_ctor_get(v_toApplicative_2260_, 1);
lean_inc(v_toPure_2263_);
lean_dec_ref(v_toApplicative_2260_);
v_map_2264_ = lean_ctor_get(v_toFunctor_2261_, 0);
lean_inc(v_map_2264_);
lean_dec_ref(v_toFunctor_2261_);
v_get_2265_ = lean_ctor_get(v_inst_2257_, 0);
lean_inc(v_get_2265_);
lean_dec_ref(v_inst_2257_);
v___f_2266_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2267_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2267_, 0, v_toPure_2263_);
v___f_2268_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2268_, 0, v_inst_2258_);
lean_closure_set(v___f_2268_, 1, v_self_2259_);
lean_closure_set(v___f_2268_, 2, v___f_2267_);
lean_closure_set(v___f_2268_, 3, v_toBind_2262_);
v___x_2269_ = lean_apply_4(v_map_2264_, lean_box(0), lean_box(0), v___f_2266_, v_get_2265_);
v___x_2270_ = lean_apply_4(v_toBind_2262_, lean_box(0), lean_box(0), v___x_2269_, v___f_2268_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog(lean_object* v_m_2271_, lean_object* v_00_u03b2_2272_, lean_object* v_inst_2273_, lean_object* v_inst_2274_, lean_object* v_inst_2275_, lean_object* v_self_2276_){
_start:
{
lean_object* v_toApplicative_2277_; lean_object* v_toFunctor_2278_; lean_object* v_toBind_2279_; lean_object* v_toPure_2280_; lean_object* v_map_2281_; lean_object* v_get_2282_; lean_object* v___f_2283_; lean_object* v___f_2284_; lean_object* v___f_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v_toApplicative_2277_ = lean_ctor_get(v_inst_2273_, 0);
lean_inc_ref(v_toApplicative_2277_);
v_toFunctor_2278_ = lean_ctor_get(v_toApplicative_2277_, 0);
lean_inc_ref(v_toFunctor_2278_);
v_toBind_2279_ = lean_ctor_get(v_inst_2273_, 1);
lean_inc_n(v_toBind_2279_, 2);
lean_dec_ref(v_inst_2273_);
v_toPure_2280_ = lean_ctor_get(v_toApplicative_2277_, 1);
lean_inc(v_toPure_2280_);
lean_dec_ref(v_toApplicative_2277_);
v_map_2281_ = lean_ctor_get(v_toFunctor_2278_, 0);
lean_inc(v_map_2281_);
lean_dec_ref(v_toFunctor_2278_);
v_get_2282_ = lean_ctor_get(v_inst_2274_, 0);
lean_inc(v_get_2282_);
lean_dec_ref(v_inst_2274_);
v___f_2283_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2284_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2284_, 0, v_toPure_2280_);
v___f_2285_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2285_, 0, v_inst_2275_);
lean_closure_set(v___f_2285_, 1, v_self_2276_);
lean_closure_set(v___f_2285_, 2, v___f_2284_);
lean_closure_set(v___f_2285_, 3, v_toBind_2279_);
v___x_2286_ = lean_apply_4(v_map_2281_, lean_box(0), lean_box(0), v___f_2283_, v_get_2282_);
v___x_2287_ = lean_apply_4(v_toBind_2279_, lean_box(0), lean_box(0), v___x_2286_, v___f_2285_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__0(lean_object* v_x_2288_){
_start:
{
lean_object* v_fst_2289_; 
v_fst_2289_ = lean_ctor_get(v_x_2288_, 0);
lean_inc(v_fst_2289_);
return v_fst_2289_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__0___boxed(lean_object* v_x_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lake_withLoggedIO___redArg___lam__0(v_x_2290_);
lean_dec_ref(v_x_2290_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__1(lean_object* v_buf_2292_){
_start:
{
lean_object* v___x_2294_; 
v___x_2294_ = lean_st_ref_get(v_buf_2292_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__1___boxed(lean_object* v_buf_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Lake_withLoggedIO___redArg___lam__1(v_buf_2295_);
lean_dec(v_buf_2295_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__2(lean_object* v_toPure_2298_, lean_object* v_a_2299_, lean_object* v_____r_2300_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = lean_apply_2(v_toPure_2298_, lean_box(0), v_a_2299_);
return v___x_2301_;
}
}
static lean_object* _init_l_Lake_withLoggedIO___redArg___lam__3___closed__4(void){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2306_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___lam__3___closed__3));
v___x_2307_ = lean_unsigned_to_nat(46u);
v___x_2308_ = lean_unsigned_to_nat(193u);
v___x_2309_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___lam__3___closed__2));
v___x_2310_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___lam__3___closed__1));
v___x_2311_ = l_mkPanicMessageWithDecl(v___x_2310_, v___x_2309_, v___x_2308_, v___x_2307_, v___x_2306_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__3(lean_object* v___x_2312_, lean_object* v_inst_2313_, lean_object* v_toBind_2314_, lean_object* v___f_2315_, lean_object* v_toPure_2316_, lean_object* v_a_2317_, lean_object* v_buf_2318_){
_start:
{
lean_object* v___y_2320_; lean_object* v_data_2333_; uint8_t v___x_2334_; 
v_data_2333_ = lean_ctor_get(v_buf_2318_, 0);
lean_inc_ref(v_data_2333_);
lean_dec_ref(v_buf_2318_);
v___x_2334_ = lean_string_validate_utf8(v_data_2333_);
if (v___x_2334_ == 0)
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_dec_ref(v_data_2333_);
v___x_2335_ = ((lean_object*)(l_Lake_instInhabitedLogEntry_default___closed__0));
v___x_2336_ = lean_obj_once(&l_Lake_withLoggedIO___redArg___lam__3___closed__4, &l_Lake_withLoggedIO___redArg___lam__3___closed__4_once, _init_l_Lake_withLoggedIO___redArg___lam__3___closed__4);
v___x_2337_ = l_panic___redArg(v___x_2335_, v___x_2336_);
v___y_2320_ = v___x_2337_;
goto v___jp_2319_;
}
else
{
lean_object* v___x_2338_; 
v___x_2338_ = lean_string_from_utf8_unchecked(v_data_2333_);
v___y_2320_ = v___x_2338_;
goto v___jp_2319_;
}
v___jp_2319_:
{
lean_object* v___x_2321_; uint8_t v___x_2322_; 
v___x_2321_ = lean_string_utf8_byte_size(v___y_2320_);
v___x_2322_ = lean_nat_dec_eq(v___x_2321_, v___x_2312_);
if (v___x_2322_ == 0)
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; uint8_t v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
lean_dec(v_a_2317_);
lean_dec(v_toPure_2316_);
v___x_2323_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___lam__3___closed__0));
v___x_2324_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2324_, 0, v___y_2320_);
lean_ctor_set(v___x_2324_, 1, v___x_2312_);
lean_ctor_set(v___x_2324_, 2, v___x_2321_);
v___x_2325_ = l_String_Slice_trimAscii(v___x_2324_);
v___x_2326_ = l_String_Slice_toString(v___x_2325_);
lean_dec_ref(v___x_2325_);
v___x_2327_ = lean_string_append(v___x_2323_, v___x_2326_);
lean_dec_ref(v___x_2326_);
v___x_2328_ = 1;
v___x_2329_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2329_, 0, v___x_2327_);
lean_ctor_set_uint8(v___x_2329_, sizeof(void*)*1, v___x_2328_);
v___x_2330_ = lean_apply_1(v_inst_2313_, v___x_2329_);
v___x_2331_ = lean_apply_4(v_toBind_2314_, lean_box(0), lean_box(0), v___x_2330_, v___f_2315_);
return v___x_2331_;
}
else
{
lean_object* v___x_2332_; 
lean_dec_ref(v___y_2320_);
lean_dec(v___f_2315_);
lean_dec(v_toBind_2314_);
lean_dec(v_inst_2313_);
lean_dec(v___x_2312_);
v___x_2332_ = lean_apply_2(v_toPure_2316_, lean_box(0), v_a_2317_);
return v___x_2332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__4(lean_object* v_toPure_2339_, lean_object* v___x_2340_, lean_object* v_inst_2341_, lean_object* v_toBind_2342_, lean_object* v_inst_2343_, lean_object* v___f_2344_, lean_object* v_a_2345_){
_start:
{
lean_object* v___f_2346_; lean_object* v___f_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
lean_inc(v_a_2345_);
lean_inc(v_toPure_2339_);
v___f_2346_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2346_, 0, v_toPure_2339_);
lean_closure_set(v___f_2346_, 1, v_a_2345_);
lean_inc(v_toBind_2342_);
v___f_2347_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__3), 7, 6);
lean_closure_set(v___f_2347_, 0, v___x_2340_);
lean_closure_set(v___f_2347_, 1, v_inst_2341_);
lean_closure_set(v___f_2347_, 2, v_toBind_2342_);
lean_closure_set(v___f_2347_, 3, v___f_2346_);
lean_closure_set(v___f_2347_, 4, v_toPure_2339_);
lean_closure_set(v___f_2347_, 5, v_a_2345_);
v___x_2348_ = lean_apply_2(v_inst_2343_, lean_box(0), v___f_2344_);
v___x_2349_ = lean_apply_4(v_toBind_2342_, lean_box(0), lean_box(0), v___x_2348_, v___f_2347_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__5(lean_object* v_stderr_2350_, lean_object* v_inst_2351_, lean_object* v_mapConst_2352_, lean_object* v_____r_2353_){
_start:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2354_ = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(v___x_2354_, 0, v_stderr_2350_);
v___x_2355_ = lean_apply_2(v_inst_2351_, lean_box(0), v___x_2354_);
v___x_2356_ = lean_box(0);
v___x_2357_ = lean_apply_4(v_mapConst_2352_, lean_box(0), lean_box(0), v___x_2356_, v___x_2355_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__6(lean_object* v___x_2358_, lean_object* v_x_2359_){
_start:
{
lean_inc(v___x_2358_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__6___boxed(lean_object* v___x_2360_, lean_object* v_x_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_Lake_withLoggedIO___redArg___lam__6(v___x_2360_, v_x_2361_);
lean_dec(v_x_2361_);
lean_dec(v___x_2360_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__7(lean_object* v_toFunctor_2363_, lean_object* v_inst_2364_, lean_object* v_stdout_2365_, lean_object* v_toBind_2366_, lean_object* v_inst_2367_, lean_object* v_x_2368_, lean_object* v___f_2369_, lean_object* v___f_2370_, lean_object* v_stderr_2371_){
_start:
{
lean_object* v_map_2372_; lean_object* v_mapConst_2373_; lean_object* v___f_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___f_2380_; lean_object* v_y_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v_map_2372_ = lean_ctor_get(v_toFunctor_2363_, 0);
lean_inc(v_map_2372_);
v_mapConst_2373_ = lean_ctor_get(v_toFunctor_2363_, 1);
lean_inc_n(v_mapConst_2373_, 2);
lean_dec_ref(v_toFunctor_2363_);
lean_inc(v_inst_2364_);
v___f_2374_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__5), 4, 3);
lean_closure_set(v___f_2374_, 0, v_stderr_2371_);
lean_closure_set(v___f_2374_, 1, v_inst_2364_);
lean_closure_set(v___f_2374_, 2, v_mapConst_2373_);
v___x_2375_ = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(v___x_2375_, 0, v_stdout_2365_);
v___x_2376_ = lean_apply_2(v_inst_2364_, lean_box(0), v___x_2375_);
v___x_2377_ = lean_box(0);
v___x_2378_ = lean_apply_4(v_mapConst_2373_, lean_box(0), lean_box(0), v___x_2377_, v___x_2376_);
lean_inc(v_toBind_2366_);
v___x_2379_ = lean_apply_4(v_toBind_2366_, lean_box(0), lean_box(0), v___x_2378_, v___f_2374_);
v___f_2380_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__6___boxed), 2, 1);
lean_closure_set(v___f_2380_, 0, v___x_2379_);
v_y_2381_ = lean_apply_4(v_inst_2367_, lean_box(0), lean_box(0), v_x_2368_, v___f_2380_);
v___x_2382_ = lean_apply_4(v_map_2372_, lean_box(0), lean_box(0), v___f_2369_, v_y_2381_);
v___x_2383_ = lean_apply_4(v_toBind_2366_, lean_box(0), lean_box(0), v___x_2382_, v___f_2370_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__8(lean_object* v_toFunctor_2384_, lean_object* v_inst_2385_, lean_object* v_toBind_2386_, lean_object* v_inst_2387_, lean_object* v_x_2388_, lean_object* v___f_2389_, lean_object* v___f_2390_, lean_object* v___x_2391_, lean_object* v_stdout_2392_){
_start:
{
lean_object* v___f_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
lean_inc(v_toBind_2386_);
lean_inc(v_inst_2385_);
v___f_2393_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__7), 9, 8);
lean_closure_set(v___f_2393_, 0, v_toFunctor_2384_);
lean_closure_set(v___f_2393_, 1, v_inst_2385_);
lean_closure_set(v___f_2393_, 2, v_stdout_2392_);
lean_closure_set(v___f_2393_, 3, v_toBind_2386_);
lean_closure_set(v___f_2393_, 4, v_inst_2387_);
lean_closure_set(v___f_2393_, 5, v_x_2388_);
lean_closure_set(v___f_2393_, 6, v___f_2389_);
lean_closure_set(v___f_2393_, 7, v___f_2390_);
v___x_2394_ = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(v___x_2394_, 0, v___x_2391_);
v___x_2395_ = lean_apply_2(v_inst_2385_, lean_box(0), v___x_2394_);
v___x_2396_ = lean_apply_4(v_toBind_2386_, lean_box(0), lean_box(0), v___x_2395_, v___f_2393_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__9(lean_object* v_toPure_2397_, lean_object* v___x_2398_, lean_object* v_inst_2399_, lean_object* v_toBind_2400_, lean_object* v_inst_2401_, lean_object* v_toFunctor_2402_, lean_object* v_inst_2403_, lean_object* v_x_2404_, lean_object* v___f_2405_, lean_object* v_buf_2406_){
_start:
{
lean_object* v___f_2407_; lean_object* v___f_2408_; lean_object* v___x_2409_; lean_object* v___f_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
lean_inc(v_buf_2406_);
v___f_2407_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2407_, 0, v_buf_2406_);
lean_inc_n(v_inst_2401_, 2);
lean_inc_n(v_toBind_2400_, 2);
v___f_2408_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__4), 7, 6);
lean_closure_set(v___f_2408_, 0, v_toPure_2397_);
lean_closure_set(v___f_2408_, 1, v___x_2398_);
lean_closure_set(v___f_2408_, 2, v_inst_2399_);
lean_closure_set(v___f_2408_, 3, v_toBind_2400_);
lean_closure_set(v___f_2408_, 4, v_inst_2401_);
lean_closure_set(v___f_2408_, 5, v___f_2407_);
v___x_2409_ = l_IO_FS_Stream_ofBuffer(v_buf_2406_);
lean_inc_ref(v___x_2409_);
v___f_2410_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__8), 9, 8);
lean_closure_set(v___f_2410_, 0, v_toFunctor_2402_);
lean_closure_set(v___f_2410_, 1, v_inst_2401_);
lean_closure_set(v___f_2410_, 2, v_toBind_2400_);
lean_closure_set(v___f_2410_, 3, v_inst_2403_);
lean_closure_set(v___f_2410_, 4, v_x_2404_);
lean_closure_set(v___f_2410_, 5, v___f_2405_);
lean_closure_set(v___f_2410_, 6, v___f_2408_);
lean_closure_set(v___f_2410_, 7, v___x_2409_);
v___x_2411_ = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(v___x_2411_, 0, v___x_2409_);
v___x_2412_ = lean_apply_2(v_inst_2401_, lean_box(0), v___x_2411_);
v___x_2413_ = lean_apply_4(v_toBind_2400_, lean_box(0), lean_box(0), v___x_2412_, v___f_2410_);
return v___x_2413_;
}
}
static lean_object* _init_l_Lake_withLoggedIO___redArg___closed__1(void){
_start:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2415_ = lean_unsigned_to_nat(0u);
v___x_2416_ = l_ByteArray_empty;
v___x_2417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2416_);
lean_ctor_set(v___x_2417_, 1, v___x_2415_);
return v___x_2417_;
}
}
static lean_object* _init_l_Lake_withLoggedIO___redArg___closed__2(void){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = lean_obj_once(&l_Lake_withLoggedIO___redArg___closed__1, &l_Lake_withLoggedIO___redArg___closed__1_once, _init_l_Lake_withLoggedIO___redArg___closed__1);
v___x_2419_ = lean_alloc_closure((void*)(l_IO_mkRef___boxed), 3, 2);
lean_closure_set(v___x_2419_, 0, lean_box(0));
lean_closure_set(v___x_2419_, 1, v___x_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg(lean_object* v_inst_2420_, lean_object* v_inst_2421_, lean_object* v_inst_2422_, lean_object* v_inst_2423_, lean_object* v_x_2424_){
_start:
{
lean_object* v_toApplicative_2425_; lean_object* v_toBind_2426_; lean_object* v_toFunctor_2427_; lean_object* v_toPure_2428_; lean_object* v___f_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___f_2433_; lean_object* v___x_2434_; 
v_toApplicative_2425_ = lean_ctor_get(v_inst_2420_, 0);
lean_inc_ref(v_toApplicative_2425_);
v_toBind_2426_ = lean_ctor_get(v_inst_2420_, 1);
lean_inc_n(v_toBind_2426_, 2);
lean_dec_ref(v_inst_2420_);
v_toFunctor_2427_ = lean_ctor_get(v_toApplicative_2425_, 0);
lean_inc_ref(v_toFunctor_2427_);
v_toPure_2428_ = lean_ctor_get(v_toApplicative_2425_, 1);
lean_inc(v_toPure_2428_);
lean_dec_ref(v_toApplicative_2425_);
v___f_2429_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___closed__0));
v___x_2430_ = lean_unsigned_to_nat(0u);
v___x_2431_ = lean_obj_once(&l_Lake_withLoggedIO___redArg___closed__2, &l_Lake_withLoggedIO___redArg___closed__2_once, _init_l_Lake_withLoggedIO___redArg___closed__2);
lean_inc(v_inst_2421_);
v___x_2432_ = lean_apply_2(v_inst_2421_, lean_box(0), v___x_2431_);
v___f_2433_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__9), 10, 9);
lean_closure_set(v___f_2433_, 0, v_toPure_2428_);
lean_closure_set(v___f_2433_, 1, v___x_2430_);
lean_closure_set(v___f_2433_, 2, v_inst_2422_);
lean_closure_set(v___f_2433_, 3, v_toBind_2426_);
lean_closure_set(v___f_2433_, 4, v_inst_2421_);
lean_closure_set(v___f_2433_, 5, v_toFunctor_2427_);
lean_closure_set(v___f_2433_, 6, v_inst_2423_);
lean_closure_set(v___f_2433_, 7, v_x_2424_);
lean_closure_set(v___f_2433_, 8, v___f_2429_);
v___x_2434_ = lean_apply_4(v_toBind_2426_, lean_box(0), lean_box(0), v___x_2432_, v___f_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO(lean_object* v_m_2435_, lean_object* v_00_u03b1_2436_, lean_object* v_inst_2437_, lean_object* v_inst_2438_, lean_object* v_inst_2439_, lean_object* v_inst_2440_, lean_object* v_x_2441_){
_start:
{
lean_object* v_toApplicative_2442_; lean_object* v_toBind_2443_; lean_object* v_toFunctor_2444_; lean_object* v_toPure_2445_; lean_object* v___f_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___f_2450_; lean_object* v___x_2451_; 
v_toApplicative_2442_ = lean_ctor_get(v_inst_2437_, 0);
lean_inc_ref(v_toApplicative_2442_);
v_toBind_2443_ = lean_ctor_get(v_inst_2437_, 1);
lean_inc_n(v_toBind_2443_, 2);
lean_dec_ref(v_inst_2437_);
v_toFunctor_2444_ = lean_ctor_get(v_toApplicative_2442_, 0);
lean_inc_ref(v_toFunctor_2444_);
v_toPure_2445_ = lean_ctor_get(v_toApplicative_2442_, 1);
lean_inc(v_toPure_2445_);
lean_dec_ref(v_toApplicative_2442_);
v___f_2446_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___closed__0));
v___x_2447_ = lean_unsigned_to_nat(0u);
v___x_2448_ = lean_obj_once(&l_Lake_withLoggedIO___redArg___closed__2, &l_Lake_withLoggedIO___redArg___closed__2_once, _init_l_Lake_withLoggedIO___redArg___closed__2);
lean_inc(v_inst_2438_);
v___x_2449_ = lean_apply_2(v_inst_2438_, lean_box(0), v___x_2448_);
v___f_2450_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__9), 10, 9);
lean_closure_set(v___f_2450_, 0, v_toPure_2445_);
lean_closure_set(v___f_2450_, 1, v___x_2447_);
lean_closure_set(v___f_2450_, 2, v_inst_2439_);
lean_closure_set(v___f_2450_, 3, v_toBind_2443_);
lean_closure_set(v___f_2450_, 4, v_inst_2438_);
lean_closure_set(v___f_2450_, 5, v_toFunctor_2444_);
lean_closure_set(v___f_2450_, 6, v_inst_2440_);
lean_closure_set(v___f_2450_, 7, v_x_2441_);
lean_closure_set(v___f_2450_, 8, v___f_2446_);
v___x_2451_ = lean_apply_4(v_toBind_2443_, lean_box(0), lean_box(0), v___x_2449_, v___f_2450_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_error___redArg___lam__3(lean_object* v_inst_2452_, lean_object* v___x_2453_, lean_object* v___f_2454_, lean_object* v_toBind_2455_, lean_object* v_iniPos_2456_){
_start:
{
lean_object* v_throw_2457_; lean_object* v_tryCatch_2458_; lean_object* v___f_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v_throw_2457_ = lean_ctor_get(v_inst_2452_, 0);
lean_inc(v_throw_2457_);
v_tryCatch_2458_ = lean_ctor_get(v_inst_2452_, 1);
lean_inc(v_tryCatch_2458_);
lean_dec_ref(v_inst_2452_);
v___f_2459_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2459_, 0, v_throw_2457_);
lean_closure_set(v___f_2459_, 1, v_iniPos_2456_);
v___x_2460_ = lean_apply_3(v_tryCatch_2458_, lean_box(0), v___x_2453_, v___f_2454_);
v___x_2461_ = lean_apply_4(v_toBind_2455_, lean_box(0), lean_box(0), v___x_2460_, v___f_2459_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_error___redArg(lean_object* v_inst_2462_, lean_object* v_inst_2463_, lean_object* v_inst_2464_, lean_object* v_inst_2465_, lean_object* v_msg_2466_){
_start:
{
lean_object* v_toApplicative_2467_; lean_object* v_toFunctor_2468_; lean_object* v_toBind_2469_; lean_object* v_toPure_2470_; lean_object* v_map_2471_; lean_object* v_get_2472_; lean_object* v___f_2473_; uint8_t v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___f_2477_; lean_object* v___f_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v_toApplicative_2467_ = lean_ctor_get(v_inst_2462_, 0);
lean_inc_ref(v_toApplicative_2467_);
v_toFunctor_2468_ = lean_ctor_get(v_toApplicative_2467_, 0);
lean_inc_ref(v_toFunctor_2468_);
v_toBind_2469_ = lean_ctor_get(v_inst_2462_, 1);
lean_inc_n(v_toBind_2469_, 2);
lean_dec_ref(v_inst_2462_);
v_toPure_2470_ = lean_ctor_get(v_toApplicative_2467_, 1);
lean_inc(v_toPure_2470_);
lean_dec_ref(v_toApplicative_2467_);
v_map_2471_ = lean_ctor_get(v_toFunctor_2468_, 0);
lean_inc(v_map_2471_);
lean_dec_ref(v_toFunctor_2468_);
v_get_2472_ = lean_ctor_get(v_inst_2464_, 0);
lean_inc(v_get_2472_);
lean_dec_ref(v_inst_2464_);
v___f_2473_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_2474_ = 3;
v___x_2475_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2475_, 0, v_msg_2466_);
lean_ctor_set_uint8(v___x_2475_, sizeof(void*)*1, v___x_2474_);
v___x_2476_ = lean_apply_1(v_inst_2463_, v___x_2475_);
v___f_2477_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2477_, 0, v_toPure_2470_);
v___f_2478_ = lean_alloc_closure((void*)(l_Lake_ELog_error___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2478_, 0, v_inst_2465_);
lean_closure_set(v___f_2478_, 1, v___x_2476_);
lean_closure_set(v___f_2478_, 2, v___f_2477_);
lean_closure_set(v___f_2478_, 3, v_toBind_2469_);
v___x_2479_ = lean_apply_4(v_map_2471_, lean_box(0), lean_box(0), v___f_2473_, v_get_2472_);
v___x_2480_ = lean_apply_4(v_toBind_2469_, lean_box(0), lean_box(0), v___x_2479_, v___f_2478_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_error(lean_object* v_m_2481_, lean_object* v_00_u03b1_2482_, lean_object* v_inst_2483_, lean_object* v_inst_2484_, lean_object* v_inst_2485_, lean_object* v_inst_2486_, lean_object* v_msg_2487_){
_start:
{
lean_object* v_toApplicative_2488_; lean_object* v_toFunctor_2489_; lean_object* v_toBind_2490_; lean_object* v_toPure_2491_; lean_object* v_map_2492_; lean_object* v_get_2493_; lean_object* v___f_2494_; uint8_t v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___f_2498_; lean_object* v___f_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v_toApplicative_2488_ = lean_ctor_get(v_inst_2483_, 0);
lean_inc_ref(v_toApplicative_2488_);
v_toFunctor_2489_ = lean_ctor_get(v_toApplicative_2488_, 0);
lean_inc_ref(v_toFunctor_2489_);
v_toBind_2490_ = lean_ctor_get(v_inst_2483_, 1);
lean_inc_n(v_toBind_2490_, 2);
lean_dec_ref(v_inst_2483_);
v_toPure_2491_ = lean_ctor_get(v_toApplicative_2488_, 1);
lean_inc(v_toPure_2491_);
lean_dec_ref(v_toApplicative_2488_);
v_map_2492_ = lean_ctor_get(v_toFunctor_2489_, 0);
lean_inc(v_map_2492_);
lean_dec_ref(v_toFunctor_2489_);
v_get_2493_ = lean_ctor_get(v_inst_2485_, 0);
lean_inc(v_get_2493_);
lean_dec_ref(v_inst_2485_);
v___f_2494_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_2495_ = 3;
v___x_2496_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2496_, 0, v_msg_2487_);
lean_ctor_set_uint8(v___x_2496_, sizeof(void*)*1, v___x_2495_);
v___x_2497_ = lean_apply_1(v_inst_2484_, v___x_2496_);
v___f_2498_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2498_, 0, v_toPure_2491_);
v___f_2499_ = lean_alloc_closure((void*)(l_Lake_ELog_error___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2499_, 0, v_inst_2486_);
lean_closure_set(v___f_2499_, 1, v___x_2497_);
lean_closure_set(v___f_2499_, 2, v___f_2498_);
lean_closure_set(v___f_2499_, 3, v_toBind_2490_);
v___x_2500_ = lean_apply_4(v_map_2492_, lean_box(0), lean_box(0), v___f_2494_, v_get_2493_);
v___x_2501_ = lean_apply_4(v_toBind_2490_, lean_box(0), lean_box(0), v___x_2500_, v___f_2499_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_monadError___redArg___lam__4(lean_object* v_inst_2502_, lean_object* v_inst_2503_, lean_object* v_inst_2504_, lean_object* v_inst_2505_, lean_object* v___f_2506_, lean_object* v_00_u03b1_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v_toApplicative_2509_; lean_object* v_toFunctor_2510_; lean_object* v_toBind_2511_; lean_object* v_toPure_2512_; lean_object* v_map_2513_; lean_object* v_get_2514_; uint8_t v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___f_2518_; lean_object* v___f_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v_toApplicative_2509_ = lean_ctor_get(v_inst_2502_, 0);
lean_inc_ref(v_toApplicative_2509_);
v_toFunctor_2510_ = lean_ctor_get(v_toApplicative_2509_, 0);
lean_inc_ref(v_toFunctor_2510_);
v_toBind_2511_ = lean_ctor_get(v_inst_2502_, 1);
lean_inc_n(v_toBind_2511_, 2);
lean_dec_ref(v_inst_2502_);
v_toPure_2512_ = lean_ctor_get(v_toApplicative_2509_, 1);
lean_inc(v_toPure_2512_);
lean_dec_ref(v_toApplicative_2509_);
v_map_2513_ = lean_ctor_get(v_toFunctor_2510_, 0);
lean_inc(v_map_2513_);
lean_dec_ref(v_toFunctor_2510_);
v_get_2514_ = lean_ctor_get(v_inst_2503_, 0);
lean_inc(v_get_2514_);
lean_dec_ref(v_inst_2503_);
v___x_2515_ = 3;
v___x_2516_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2516_, 0, v___y_2508_);
lean_ctor_set_uint8(v___x_2516_, sizeof(void*)*1, v___x_2515_);
v___x_2517_ = lean_apply_1(v_inst_2504_, v___x_2516_);
v___f_2518_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2518_, 0, v_toPure_2512_);
v___f_2519_ = lean_alloc_closure((void*)(l_Lake_ELog_error___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2519_, 0, v_inst_2505_);
lean_closure_set(v___f_2519_, 1, v___x_2517_);
lean_closure_set(v___f_2519_, 2, v___f_2518_);
lean_closure_set(v___f_2519_, 3, v_toBind_2511_);
v___x_2520_ = lean_apply_4(v_map_2513_, lean_box(0), lean_box(0), v___f_2506_, v_get_2514_);
v___x_2521_ = lean_apply_4(v_toBind_2511_, lean_box(0), lean_box(0), v___x_2520_, v___f_2519_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_monadError___redArg(lean_object* v_inst_2522_, lean_object* v_inst_2523_, lean_object* v_inst_2524_, lean_object* v_inst_2525_){
_start:
{
lean_object* v___f_2526_; lean_object* v___f_2527_; 
v___f_2526_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2527_ = lean_alloc_closure((void*)(l_Lake_ELog_monadError___redArg___lam__4), 7, 5);
lean_closure_set(v___f_2527_, 0, v_inst_2522_);
lean_closure_set(v___f_2527_, 1, v_inst_2524_);
lean_closure_set(v___f_2527_, 2, v_inst_2523_);
lean_closure_set(v___f_2527_, 3, v_inst_2525_);
lean_closure_set(v___f_2527_, 4, v___f_2526_);
return v___f_2527_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_monadError(lean_object* v_m_2528_, lean_object* v_inst_2529_, lean_object* v_inst_2530_, lean_object* v_inst_2531_, lean_object* v_inst_2532_){
_start:
{
lean_object* v___f_2533_; lean_object* v___f_2534_; 
v___f_2533_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2534_ = lean_alloc_closure((void*)(l_Lake_ELog_monadError___redArg___lam__4), 7, 5);
lean_closure_set(v___f_2534_, 0, v_inst_2529_);
lean_closure_set(v___f_2534_, 1, v_inst_2531_);
lean_closure_set(v___f_2534_, 2, v_inst_2530_);
lean_closure_set(v___f_2534_, 3, v_inst_2532_);
lean_closure_set(v___f_2534_, 4, v___f_2533_);
return v___f_2534_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_failure___redArg___lam__1(lean_object* v_inst_2535_, lean_object* v_____do__lift_2536_){
_start:
{
lean_object* v_throw_2537_; lean_object* v___x_2538_; 
v_throw_2537_ = lean_ctor_get(v_inst_2535_, 0);
lean_inc(v_throw_2537_);
lean_dec_ref(v_inst_2535_);
v___x_2538_ = lean_apply_2(v_throw_2537_, lean_box(0), v_____do__lift_2536_);
return v___x_2538_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_failure___redArg(lean_object* v_inst_2539_, lean_object* v_inst_2540_, lean_object* v_inst_2541_){
_start:
{
lean_object* v_toApplicative_2542_; lean_object* v_toFunctor_2543_; lean_object* v_toBind_2544_; lean_object* v_map_2545_; lean_object* v_get_2546_; lean_object* v___f_2547_; lean_object* v___f_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v_toApplicative_2542_ = lean_ctor_get(v_inst_2539_, 0);
v_toFunctor_2543_ = lean_ctor_get(v_toApplicative_2542_, 0);
lean_inc_ref(v_toFunctor_2543_);
v_toBind_2544_ = lean_ctor_get(v_inst_2539_, 1);
lean_inc(v_toBind_2544_);
lean_dec_ref(v_inst_2539_);
v_map_2545_ = lean_ctor_get(v_toFunctor_2543_, 0);
lean_inc(v_map_2545_);
lean_dec_ref(v_toFunctor_2543_);
v_get_2546_ = lean_ctor_get(v_inst_2540_, 0);
lean_inc(v_get_2546_);
lean_dec_ref(v_inst_2540_);
v___f_2547_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2548_ = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2548_, 0, v_inst_2541_);
v___x_2549_ = lean_apply_4(v_map_2545_, lean_box(0), lean_box(0), v___f_2547_, v_get_2546_);
v___x_2550_ = lean_apply_4(v_toBind_2544_, lean_box(0), lean_box(0), v___x_2549_, v___f_2548_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_failure(lean_object* v_m_2551_, lean_object* v_00_u03b1_2552_, lean_object* v_inst_2553_, lean_object* v_inst_2554_, lean_object* v_inst_2555_){
_start:
{
lean_object* v_toApplicative_2556_; lean_object* v_toFunctor_2557_; lean_object* v_toBind_2558_; lean_object* v_map_2559_; lean_object* v_get_2560_; lean_object* v___f_2561_; lean_object* v___f_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v_toApplicative_2556_ = lean_ctor_get(v_inst_2553_, 0);
v_toFunctor_2557_ = lean_ctor_get(v_toApplicative_2556_, 0);
lean_inc_ref(v_toFunctor_2557_);
v_toBind_2558_ = lean_ctor_get(v_inst_2553_, 1);
lean_inc(v_toBind_2558_);
lean_dec_ref(v_inst_2553_);
v_map_2559_ = lean_ctor_get(v_toFunctor_2557_, 0);
lean_inc(v_map_2559_);
lean_dec_ref(v_toFunctor_2557_);
v_get_2560_ = lean_ctor_get(v_inst_2554_, 0);
lean_inc(v_get_2560_);
lean_dec_ref(v_inst_2554_);
v___f_2561_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2562_ = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2562_, 0, v_inst_2555_);
v___x_2563_ = lean_apply_4(v_map_2559_, lean_box(0), lean_box(0), v___f_2561_, v_get_2560_);
v___x_2564_ = lean_apply_4(v_toBind_2558_, lean_box(0), lean_box(0), v___x_2563_, v___f_2562_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__0(lean_object* v_y_2565_, lean_object* v_____r_2566_){
_start:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2567_ = lean_box(0);
v___x_2568_ = lean_apply_1(v_y_2565_, v___x_2567_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__1(lean_object* v_errPos_2569_, lean_object* v_s_2570_){
_start:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2571_ = lean_box(0);
v___x_2572_ = l_Array_shrink___redArg(v_s_2570_, v_errPos_2569_);
v___x_2573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2571_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__1___boxed(lean_object* v_errPos_2574_, lean_object* v_s_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l_Lake_ELog_orElse___redArg___lam__1(v_errPos_2574_, v_s_2575_);
lean_dec(v_errPos_2574_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__2(lean_object* v_inst_2577_, lean_object* v_toBind_2578_, lean_object* v___f_2579_, lean_object* v_errPos_2580_){
_start:
{
lean_object* v_modifyGet_2581_; lean_object* v___f_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v_modifyGet_2581_ = lean_ctor_get(v_inst_2577_, 2);
lean_inc(v_modifyGet_2581_);
lean_dec_ref(v_inst_2577_);
v___f_2582_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2582_, 0, v_errPos_2580_);
v___x_2583_ = lean_apply_2(v_modifyGet_2581_, lean_box(0), v___f_2582_);
v___x_2584_ = lean_apply_4(v_toBind_2578_, lean_box(0), lean_box(0), v___x_2583_, v___f_2579_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg(lean_object* v_inst_2585_, lean_object* v_inst_2586_, lean_object* v_inst_2587_, lean_object* v_x_2588_, lean_object* v_y_2589_){
_start:
{
lean_object* v_toBind_2590_; lean_object* v_tryCatch_2591_; lean_object* v___f_2592_; lean_object* v___f_2593_; lean_object* v___x_2594_; 
v_toBind_2590_ = lean_ctor_get(v_inst_2585_, 1);
lean_inc(v_toBind_2590_);
lean_dec_ref(v_inst_2585_);
v_tryCatch_2591_ = lean_ctor_get(v_inst_2587_, 1);
lean_inc(v_tryCatch_2591_);
lean_dec_ref(v_inst_2587_);
v___f_2592_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2592_, 0, v_y_2589_);
v___f_2593_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2593_, 0, v_inst_2586_);
lean_closure_set(v___f_2593_, 1, v_toBind_2590_);
lean_closure_set(v___f_2593_, 2, v___f_2592_);
v___x_2594_ = lean_apply_3(v_tryCatch_2591_, lean_box(0), v_x_2588_, v___f_2593_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse(lean_object* v_m_2595_, lean_object* v_00_u03b1_2596_, lean_object* v_inst_2597_, lean_object* v_inst_2598_, lean_object* v_inst_2599_, lean_object* v_x_2600_, lean_object* v_y_2601_){
_start:
{
lean_object* v_toBind_2602_; lean_object* v_tryCatch_2603_; lean_object* v___f_2604_; lean_object* v___f_2605_; lean_object* v___x_2606_; 
v_toBind_2602_ = lean_ctor_get(v_inst_2597_, 1);
lean_inc(v_toBind_2602_);
lean_dec_ref(v_inst_2597_);
v_tryCatch_2603_ = lean_ctor_get(v_inst_2599_, 1);
lean_inc(v_tryCatch_2603_);
lean_dec_ref(v_inst_2599_);
v___f_2604_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2604_, 0, v_y_2601_);
v___f_2605_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2605_, 0, v_inst_2598_);
lean_closure_set(v___f_2605_, 1, v_toBind_2602_);
lean_closure_set(v___f_2605_, 2, v___f_2604_);
v___x_2606_ = lean_apply_3(v_tryCatch_2603_, lean_box(0), v_x_2600_, v___f_2605_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__2(lean_object* v_toApplicative_2607_, lean_object* v_inst_2608_, lean_object* v___f_2609_, lean_object* v_toBind_2610_, lean_object* v___f_2611_, lean_object* v_00_u03b1_2612_){
_start:
{
lean_object* v_toFunctor_2613_; lean_object* v_map_2614_; lean_object* v_get_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v_toFunctor_2613_ = lean_ctor_get(v_toApplicative_2607_, 0);
lean_inc_ref(v_toFunctor_2613_);
lean_dec_ref(v_toApplicative_2607_);
v_map_2614_ = lean_ctor_get(v_toFunctor_2613_, 0);
lean_inc(v_map_2614_);
lean_dec_ref(v_toFunctor_2613_);
v_get_2615_ = lean_ctor_get(v_inst_2608_, 0);
lean_inc(v_get_2615_);
lean_dec_ref(v_inst_2608_);
v___x_2616_ = lean_apply_4(v_map_2614_, lean_box(0), lean_box(0), v___f_2609_, v_get_2615_);
v___x_2617_ = lean_apply_4(v_toBind_2610_, lean_box(0), lean_box(0), v___x_2616_, v___f_2611_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__0(lean_object* v___y_2618_, lean_object* v_____r_2619_){
_start:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2620_ = lean_box(0);
v___x_2621_ = lean_apply_1(v___y_2618_, v___x_2620_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__4(lean_object* v_inst_2622_, lean_object* v_inst_2623_, lean_object* v_toBind_2624_, lean_object* v_00_u03b1_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v_tryCatch_2628_; lean_object* v___f_2629_; lean_object* v___f_2630_; lean_object* v___x_2631_; 
v_tryCatch_2628_ = lean_ctor_get(v_inst_2622_, 1);
lean_inc(v_tryCatch_2628_);
lean_dec_ref(v_inst_2622_);
v___f_2629_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2629_, 0, v___y_2627_);
v___f_2630_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2630_, 0, v_inst_2623_);
lean_closure_set(v___f_2630_, 1, v_toBind_2624_);
lean_closure_set(v___f_2630_, 2, v___f_2629_);
v___x_2631_ = lean_apply_3(v_tryCatch_2628_, lean_box(0), v___y_2626_, v___f_2630_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg(lean_object* v_inst_2632_, lean_object* v_inst_2633_, lean_object* v_inst_2634_){
_start:
{
lean_object* v_toApplicative_2635_; lean_object* v_toBind_2636_; lean_object* v___f_2637_; lean_object* v___f_2638_; lean_object* v___f_2639_; lean_object* v___f_2640_; lean_object* v___x_2641_; 
v_toApplicative_2635_ = lean_ctor_get(v_inst_2632_, 0);
lean_inc_ref_n(v_toApplicative_2635_, 2);
v_toBind_2636_ = lean_ctor_get(v_inst_2632_, 1);
lean_inc_n(v_toBind_2636_, 2);
lean_dec_ref(v_inst_2632_);
v___f_2637_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
lean_inc_ref(v_inst_2634_);
v___f_2638_ = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2638_, 0, v_inst_2634_);
lean_inc_ref(v_inst_2633_);
v___f_2639_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2639_, 0, v_toApplicative_2635_);
lean_closure_set(v___f_2639_, 1, v_inst_2633_);
lean_closure_set(v___f_2639_, 2, v___f_2637_);
lean_closure_set(v___f_2639_, 3, v_toBind_2636_);
lean_closure_set(v___f_2639_, 4, v___f_2638_);
v___f_2640_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__4), 6, 3);
lean_closure_set(v___f_2640_, 0, v_inst_2634_);
lean_closure_set(v___f_2640_, 1, v_inst_2633_);
lean_closure_set(v___f_2640_, 2, v_toBind_2636_);
v___x_2641_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2641_, 0, v_toApplicative_2635_);
lean_ctor_set(v___x_2641_, 1, v___f_2639_);
lean_ctor_set(v___x_2641_, 2, v___f_2640_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative(lean_object* v_m_2642_, lean_object* v_inst_2643_, lean_object* v_inst_2644_, lean_object* v_inst_2645_){
_start:
{
lean_object* v_toApplicative_2646_; lean_object* v_toBind_2647_; lean_object* v___f_2648_; lean_object* v___f_2649_; lean_object* v___f_2650_; lean_object* v___f_2651_; lean_object* v___x_2652_; 
v_toApplicative_2646_ = lean_ctor_get(v_inst_2643_, 0);
lean_inc_ref_n(v_toApplicative_2646_, 2);
v_toBind_2647_ = lean_ctor_get(v_inst_2643_, 1);
lean_inc_n(v_toBind_2647_, 2);
lean_dec_ref(v_inst_2643_);
v___f_2648_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
lean_inc_ref(v_inst_2645_);
v___f_2649_ = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2649_, 0, v_inst_2645_);
lean_inc_ref(v_inst_2644_);
v___f_2650_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2650_, 0, v_toApplicative_2646_);
lean_closure_set(v___f_2650_, 1, v_inst_2644_);
lean_closure_set(v___f_2650_, 2, v___f_2648_);
lean_closure_set(v___f_2650_, 3, v_toBind_2647_);
lean_closure_set(v___f_2650_, 4, v___f_2649_);
v___f_2651_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__4), 6, 3);
lean_closure_set(v___f_2651_, 0, v_inst_2645_);
lean_closure_set(v___f_2651_, 1, v_inst_2644_);
lean_closure_set(v___f_2651_, 2, v_toBind_2647_);
v___x_2652_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2652_, 0, v_toApplicative_2646_);
lean_ctor_set(v___x_2652_, 1, v___f_2650_);
lean_ctor_set(v___x_2652_, 2, v___f_2651_);
return v___x_2652_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogLogTOfMonad___redArg(lean_object* v_inst_2653_){
_start:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = l_instMonadStateOfStateTOfMonad___redArg(v_inst_2653_);
v___x_2655_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(v___x_2655_, 0, lean_box(0));
lean_closure_set(v___x_2655_, 1, v___x_2654_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogLogTOfMonad(lean_object* v_m_2656_, lean_object* v_inst_2657_){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = l_Lake_instMonadLogLogTOfMonad___redArg(v_inst_2657_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run___redArg(lean_object* v_self_2659_, lean_object* v_log_2660_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = lean_apply_1(v_self_2659_, v_log_2660_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run(lean_object* v_m_2662_, lean_object* v_00_u03b1_2663_, lean_object* v_self_2664_, lean_object* v_log_2665_){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = lean_apply_1(v_self_2664_, v_log_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg___lam__0(lean_object* v_x_2667_){
_start:
{
lean_object* v_fst_2668_; 
v_fst_2668_ = lean_ctor_get(v_x_2667_, 0);
lean_inc(v_fst_2668_);
return v_fst_2668_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg___lam__0___boxed(lean_object* v_x_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l_Lake_LogT_run_x27___redArg___lam__0(v_x_2669_);
lean_dec_ref(v_x_2669_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg(lean_object* v_inst_2672_, lean_object* v_self_2673_, lean_object* v_log_2674_){
_start:
{
lean_object* v_map_2675_; lean_object* v___f_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v_map_2675_ = lean_ctor_get(v_inst_2672_, 0);
lean_inc(v_map_2675_);
lean_dec_ref(v_inst_2672_);
v___f_2676_ = ((lean_object*)(l_Lake_LogT_run_x27___redArg___closed__0));
v___x_2677_ = lean_apply_1(v_self_2673_, v_log_2674_);
v___x_2678_ = lean_apply_4(v_map_2675_, lean_box(0), lean_box(0), v___f_2676_, v___x_2677_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27(lean_object* v_m_2679_, lean_object* v_00_u03b1_2680_, lean_object* v_inst_2681_, lean_object* v_self_2682_, lean_object* v_log_2683_){
_start:
{
lean_object* v_map_2684_; lean_object* v___f_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v_map_2684_ = lean_ctor_get(v_inst_2681_, 0);
lean_inc(v_map_2684_);
lean_dec_ref(v_inst_2681_);
v___f_2685_ = ((lean_object*)(l_Lake_LogT_run_x27___redArg___closed__0));
v___x_2686_ = lean_apply_1(v_self_2682_, v_log_2683_);
v___x_2687_ = lean_apply_4(v_map_2684_, lean_box(0), lean_box(0), v___f_2685_, v___x_2686_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__1(lean_object* v_toPure_2688_, lean_object* v_fst_2689_, lean_object* v_____r_2690_){
_start:
{
lean_object* v___x_2691_; 
v___x_2691_ = lean_apply_2(v_toPure_2688_, lean_box(0), v_fst_2689_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__0(lean_object* v_toPure_2692_, lean_object* v_set_2693_, lean_object* v_toBind_2694_, lean_object* v_____x_2695_){
_start:
{
lean_object* v_fst_2696_; lean_object* v_snd_2697_; lean_object* v___f_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v_fst_2696_ = lean_ctor_get(v_____x_2695_, 0);
lean_inc(v_fst_2696_);
v_snd_2697_ = lean_ctor_get(v_____x_2695_, 1);
lean_inc(v_snd_2697_);
lean_dec_ref(v_____x_2695_);
v___f_2698_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2698_, 0, v_toPure_2692_);
lean_closure_set(v___f_2698_, 1, v_fst_2696_);
v___x_2699_ = lean_apply_1(v_set_2693_, v_snd_2697_);
v___x_2700_ = lean_apply_4(v_toBind_2694_, lean_box(0), lean_box(0), v___x_2699_, v___f_2698_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__2(lean_object* v_self_2701_, lean_object* v_inst_2702_, lean_object* v_toBind_2703_, lean_object* v___f_2704_, lean_object* v_____do__lift_2705_){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2706_ = lean_apply_1(v_self_2701_, v_____do__lift_2705_);
v___x_2707_ = lean_apply_2(v_inst_2702_, lean_box(0), v___x_2706_);
v___x_2708_ = lean_apply_4(v_toBind_2703_, lean_box(0), lean_box(0), v___x_2707_, v___f_2704_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg(lean_object* v_inst_2709_, lean_object* v_inst_2710_, lean_object* v_inst_2711_, lean_object* v_self_2712_){
_start:
{
lean_object* v_toApplicative_2713_; lean_object* v_toBind_2714_; lean_object* v_set_2715_; lean_object* v_modifyGet_2716_; lean_object* v_toPure_2717_; lean_object* v___f_2718_; lean_object* v___x_2719_; lean_object* v___f_2720_; lean_object* v___f_2721_; lean_object* v___x_2722_; 
v_toApplicative_2713_ = lean_ctor_get(v_inst_2709_, 0);
lean_inc_ref(v_toApplicative_2713_);
v_toBind_2714_ = lean_ctor_get(v_inst_2709_, 1);
lean_inc_n(v_toBind_2714_, 3);
lean_dec_ref(v_inst_2709_);
v_set_2715_ = lean_ctor_get(v_inst_2710_, 1);
lean_inc(v_set_2715_);
v_modifyGet_2716_ = lean_ctor_get(v_inst_2710_, 2);
lean_inc(v_modifyGet_2716_);
lean_dec_ref(v_inst_2710_);
v_toPure_2717_ = lean_ctor_get(v_toApplicative_2713_, 1);
lean_inc(v_toPure_2717_);
lean_dec_ref(v_toApplicative_2713_);
v___f_2718_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_2719_ = lean_apply_2(v_modifyGet_2716_, lean_box(0), v___f_2718_);
v___f_2720_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2720_, 0, v_toPure_2717_);
lean_closure_set(v___f_2720_, 1, v_set_2715_);
lean_closure_set(v___f_2720_, 2, v_toBind_2714_);
v___f_2721_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2721_, 0, v_self_2712_);
lean_closure_set(v___f_2721_, 1, v_inst_2711_);
lean_closure_set(v___f_2721_, 2, v_toBind_2714_);
lean_closure_set(v___f_2721_, 3, v___f_2720_);
v___x_2722_ = lean_apply_4(v_toBind_2714_, lean_box(0), lean_box(0), v___x_2719_, v___f_2721_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun(lean_object* v_n_2723_, lean_object* v_m_2724_, lean_object* v_00_u03b1_2725_, lean_object* v_inst_2726_, lean_object* v_inst_2727_, lean_object* v_inst_2728_, lean_object* v_inst_2729_, lean_object* v_self_2730_){
_start:
{
lean_object* v_toApplicative_2731_; lean_object* v_toBind_2732_; lean_object* v_set_2733_; lean_object* v_modifyGet_2734_; lean_object* v_toPure_2735_; lean_object* v___f_2736_; lean_object* v___x_2737_; lean_object* v___f_2738_; lean_object* v___f_2739_; lean_object* v___x_2740_; 
v_toApplicative_2731_ = lean_ctor_get(v_inst_2726_, 0);
lean_inc_ref(v_toApplicative_2731_);
v_toBind_2732_ = lean_ctor_get(v_inst_2726_, 1);
lean_inc_n(v_toBind_2732_, 3);
lean_dec_ref(v_inst_2726_);
v_set_2733_ = lean_ctor_get(v_inst_2727_, 1);
lean_inc(v_set_2733_);
v_modifyGet_2734_ = lean_ctor_get(v_inst_2727_, 2);
lean_inc(v_modifyGet_2734_);
lean_dec_ref(v_inst_2727_);
v_toPure_2735_ = lean_ctor_get(v_toApplicative_2731_, 1);
lean_inc(v_toPure_2735_);
lean_dec_ref(v_toApplicative_2731_);
v___f_2736_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_2737_ = lean_apply_2(v_modifyGet_2734_, lean_box(0), v___f_2736_);
v___f_2738_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2738_, 0, v_toPure_2735_);
lean_closure_set(v___f_2738_, 1, v_set_2733_);
lean_closure_set(v___f_2738_, 2, v_toBind_2732_);
v___f_2739_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2739_, 0, v_self_2730_);
lean_closure_set(v___f_2739_, 1, v_inst_2728_);
lean_closure_set(v___f_2739_, 2, v_toBind_2732_);
lean_closure_set(v___f_2739_, 3, v___f_2738_);
v___x_2740_ = lean_apply_4(v_toBind_2732_, lean_box(0), lean_box(0), v___x_2737_, v___f_2739_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___boxed(lean_object* v_n_2741_, lean_object* v_m_2742_, lean_object* v_00_u03b1_2743_, lean_object* v_inst_2744_, lean_object* v_inst_2745_, lean_object* v_inst_2746_, lean_object* v_inst_2747_, lean_object* v_self_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_Lake_LogT_takeAndRun(v_n_2741_, v_m_2742_, v_00_u03b1_2743_, v_inst_2744_, v_inst_2745_, v_inst_2746_, v_inst_2747_, v_self_2748_);
lean_dec(v_inst_2747_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg___lam__2(lean_object* v_toPure_2750_, lean_object* v___x_2751_, lean_object* v_toBind_2752_, lean_object* v_inst_2753_, lean_object* v___f_2754_, lean_object* v_____x_2755_){
_start:
{
lean_object* v_fst_2756_; lean_object* v_snd_2757_; lean_object* v___f_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; uint8_t v___x_2761_; 
v_fst_2756_ = lean_ctor_get(v_____x_2755_, 0);
lean_inc(v_fst_2756_);
v_snd_2757_ = lean_ctor_get(v_____x_2755_, 1);
lean_inc(v_snd_2757_);
lean_dec_ref(v_____x_2755_);
lean_inc(v_toPure_2750_);
v___f_2758_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2758_, 0, v_toPure_2750_);
lean_closure_set(v___f_2758_, 1, v_fst_2756_);
v___x_2759_ = lean_array_get_size(v_snd_2757_);
v___x_2760_ = lean_box(0);
v___x_2761_ = lean_nat_dec_lt(v___x_2751_, v___x_2759_);
if (v___x_2761_ == 0)
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
lean_dec(v_snd_2757_);
lean_dec(v___f_2754_);
lean_dec_ref(v_inst_2753_);
v___x_2762_ = lean_apply_2(v_toPure_2750_, lean_box(0), v___x_2760_);
v___x_2763_ = lean_apply_4(v_toBind_2752_, lean_box(0), lean_box(0), v___x_2762_, v___f_2758_);
return v___x_2763_;
}
else
{
size_t v___x_2764_; size_t v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
lean_dec(v_toPure_2750_);
v___x_2764_ = ((size_t)0ULL);
v___x_2765_ = lean_usize_of_nat(v___x_2759_);
v___x_2766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2753_, v___f_2754_, v_snd_2757_, v___x_2764_, v___x_2765_, v___x_2760_);
v___x_2767_ = lean_apply_4(v_toBind_2752_, lean_box(0), lean_box(0), v___x_2766_, v___f_2758_);
return v___x_2767_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg___lam__2___boxed(lean_object* v_toPure_2768_, lean_object* v___x_2769_, lean_object* v_toBind_2770_, lean_object* v_inst_2771_, lean_object* v___f_2772_, lean_object* v_____x_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l_Lake_LogT_replayLog___redArg___lam__2(v_toPure_2768_, v___x_2769_, v_toBind_2770_, v_inst_2771_, v___f_2772_, v_____x_2773_);
lean_dec(v___x_2769_);
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg(lean_object* v_inst_2775_, lean_object* v_logger_2776_, lean_object* v_inst_2777_, lean_object* v_self_2778_){
_start:
{
lean_object* v_toApplicative_2779_; lean_object* v_toBind_2780_; lean_object* v_toPure_2781_; lean_object* v___f_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___f_2787_; lean_object* v___x_2788_; 
v_toApplicative_2779_ = lean_ctor_get(v_inst_2775_, 0);
v_toBind_2780_ = lean_ctor_get(v_inst_2775_, 1);
lean_inc_n(v_toBind_2780_, 2);
v_toPure_2781_ = lean_ctor_get(v_toApplicative_2779_, 1);
lean_inc(v_toPure_2781_);
v___f_2782_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2782_, 0, v_logger_2776_);
v___x_2783_ = lean_unsigned_to_nat(0u);
v___x_2784_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_2785_ = lean_apply_1(v_self_2778_, v___x_2784_);
v___x_2786_ = lean_apply_2(v_inst_2777_, lean_box(0), v___x_2785_);
v___f_2787_ = lean_alloc_closure((void*)(l_Lake_LogT_replayLog___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_2787_, 0, v_toPure_2781_);
lean_closure_set(v___f_2787_, 1, v___x_2783_);
lean_closure_set(v___f_2787_, 2, v_toBind_2780_);
lean_closure_set(v___f_2787_, 3, v_inst_2775_);
lean_closure_set(v___f_2787_, 4, v___f_2782_);
v___x_2788_ = lean_apply_4(v_toBind_2780_, lean_box(0), lean_box(0), v___x_2786_, v___f_2787_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog(lean_object* v_n_2789_, lean_object* v_m_2790_, lean_object* v_00_u03b1_2791_, lean_object* v_inst_2792_, lean_object* v_logger_2793_, lean_object* v_inst_2794_, lean_object* v_self_2795_){
_start:
{
lean_object* v_toApplicative_2796_; lean_object* v_toBind_2797_; lean_object* v_toPure_2798_; lean_object* v___f_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___f_2804_; lean_object* v___x_2805_; 
v_toApplicative_2796_ = lean_ctor_get(v_inst_2792_, 0);
v_toBind_2797_ = lean_ctor_get(v_inst_2792_, 1);
lean_inc_n(v_toBind_2797_, 2);
v_toPure_2798_ = lean_ctor_get(v_toApplicative_2796_, 1);
lean_inc(v_toPure_2798_);
v___f_2799_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2799_, 0, v_logger_2793_);
v___x_2800_ = lean_unsigned_to_nat(0u);
v___x_2801_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_2802_ = lean_apply_1(v_self_2795_, v___x_2801_);
v___x_2803_ = lean_apply_2(v_inst_2794_, lean_box(0), v___x_2802_);
v___f_2804_ = lean_alloc_closure((void*)(l_Lake_LogT_replayLog___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_2804_, 0, v_toPure_2798_);
lean_closure_set(v___f_2804_, 1, v___x_2800_);
lean_closure_set(v___f_2804_, 2, v_toBind_2797_);
lean_closure_set(v___f_2804_, 3, v_inst_2792_);
lean_closure_set(v___f_2804_, 4, v___f_2799_);
v___x_2805_ = lean_apply_4(v_toBind_2797_, lean_box(0), lean_box(0), v___x_2803_, v___f_2804_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogELogTOfMonad___redArg(lean_object* v_inst_2806_){
_start:
{
lean_object* v_toApplicative_2807_; lean_object* v_toPure_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v_toApplicative_2807_ = lean_ctor_get(v_inst_2806_, 0);
lean_inc_ref(v_toApplicative_2807_);
lean_dec_ref(v_inst_2806_);
v_toPure_2808_ = lean_ctor_get(v_toApplicative_2807_, 1);
lean_inc(v_toPure_2808_);
lean_dec_ref(v_toApplicative_2807_);
v___x_2809_ = l_Lake_EStateT_instMonadStateOfOfPure___redArg(v_toPure_2808_);
v___x_2810_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(v___x_2810_, 0, lean_box(0));
lean_closure_set(v___x_2810_, 1, v___x_2809_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogELogTOfMonad(lean_object* v_m_2811_, lean_object* v_inst_2812_){
_start:
{
lean_object* v___x_2813_; 
v___x_2813_ = l_Lake_instMonadLogELogTOfMonad___redArg(v_inst_2812_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__0(lean_object* v_x_2814_){
_start:
{
if (lean_obj_tag(v_x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2824_; 
v_a_2815_ = lean_ctor_get(v_x_2814_, 0);
v_a_2816_ = lean_ctor_get(v_x_2814_, 1);
v_isSharedCheck_2824_ = !lean_is_exclusive(v_x_2814_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2818_ = v_x_2814_;
v_isShared_2819_ = v_isSharedCheck_2824_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_inc(v_a_2815_);
lean_dec(v_x_2814_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2824_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2820_; lean_object* v___x_2822_; 
v___x_2820_ = lean_array_get_size(v_a_2815_);
lean_dec(v_a_2815_);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 0, v___x_2820_);
v___x_2822_ = v___x_2818_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v___x_2820_);
lean_ctor_set(v_reuseFailAlloc_2823_, 1, v_a_2816_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
else
{
lean_object* v_a_2825_; lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
v_a_2825_ = lean_ctor_get(v_x_2814_, 0);
v_a_2826_ = lean_ctor_get(v_x_2814_, 1);
v_isSharedCheck_2833_ = !lean_is_exclusive(v_x_2814_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v_x_2814_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_inc(v_a_2825_);
lean_dec(v_x_2814_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2825_);
lean_ctor_set(v_reuseFailAlloc_2832_, 1, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__1(lean_object* v_a_2834_, lean_object* v_toPure_2835_, lean_object* v_____do__lift_2836_){
_start:
{
if (lean_obj_tag(v_____do__lift_2836_) == 0)
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2845_; 
v_a_2837_ = lean_ctor_get(v_____do__lift_2836_, 1);
v_isSharedCheck_2845_ = !lean_is_exclusive(v_____do__lift_2836_);
if (v_isSharedCheck_2845_ == 0)
{
lean_object* v_unused_2846_; 
v_unused_2846_ = lean_ctor_get(v_____do__lift_2836_, 0);
lean_dec(v_unused_2846_);
v___x_2839_ = v_____do__lift_2836_;
v_isShared_2840_ = v_isSharedCheck_2845_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v_____do__lift_2836_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2845_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
lean_ctor_set_tag(v___x_2839_, 1);
lean_ctor_set(v___x_2839_, 0, v_a_2834_);
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2834_);
lean_ctor_set(v_reuseFailAlloc_2844_, 1, v_a_2837_);
v___x_2842_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
lean_object* v___x_2843_; 
v___x_2843_ = lean_apply_2(v_toPure_2835_, lean_box(0), v___x_2842_);
return v___x_2843_;
}
}
}
else
{
lean_object* v_a_2847_; lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2856_; 
lean_dec(v_a_2834_);
v_a_2847_ = lean_ctor_get(v_____do__lift_2836_, 0);
v_a_2848_ = lean_ctor_get(v_____do__lift_2836_, 1);
v_isSharedCheck_2856_ = !lean_is_exclusive(v_____do__lift_2836_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2850_ = v_____do__lift_2836_;
v_isShared_2851_ = v_isSharedCheck_2856_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_inc(v_a_2847_);
lean_dec(v_____do__lift_2836_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2856_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2847_);
lean_ctor_set(v_reuseFailAlloc_2855_, 1, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
lean_object* v___x_2854_; 
v___x_2854_ = lean_apply_2(v_toPure_2835_, lean_box(0), v___x_2853_);
return v___x_2854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__2(lean_object* v_toPure_2857_, lean_object* v___x_2858_, lean_object* v_____do__lift_2859_){
_start:
{
if (lean_obj_tag(v_____do__lift_2859_) == 0)
{
lean_object* v___x_2860_; 
v___x_2860_ = lean_apply_2(v_toPure_2857_, lean_box(0), v_____do__lift_2859_);
return v___x_2860_;
}
else
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2869_; 
v_a_2861_ = lean_ctor_get(v_____do__lift_2859_, 1);
v_isSharedCheck_2869_ = !lean_is_exclusive(v_____do__lift_2859_);
if (v_isSharedCheck_2869_ == 0)
{
lean_object* v_unused_2870_; 
v_unused_2870_ = lean_ctor_get(v_____do__lift_2859_, 0);
lean_dec(v_unused_2870_);
v___x_2863_ = v_____do__lift_2859_;
v_isShared_2864_ = v_isSharedCheck_2869_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v_____do__lift_2859_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2869_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
lean_ctor_set_tag(v___x_2863_, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2858_);
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2858_);
lean_ctor_set(v_reuseFailAlloc_2868_, 1, v_a_2861_);
v___x_2866_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
lean_object* v___x_2867_; 
v___x_2867_ = lean_apply_2(v_toPure_2857_, lean_box(0), v___x_2866_);
return v___x_2867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__3(lean_object* v_toPure_2871_, lean_object* v___x_2872_, lean_object* v_toBind_2873_, lean_object* v_____do__lift_2874_){
_start:
{
if (lean_obj_tag(v_____do__lift_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2890_; 
v_a_2875_ = lean_ctor_get(v_____do__lift_2874_, 0);
v_a_2876_ = lean_ctor_get(v_____do__lift_2874_, 1);
v_isSharedCheck_2890_ = !lean_is_exclusive(v_____do__lift_2874_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2878_ = v_____do__lift_2874_;
v_isShared_2879_ = v_isSharedCheck_2890_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_inc(v_a_2875_);
lean_dec(v_____do__lift_2874_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2890_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___f_2880_; lean_object* v___x_2881_; lean_object* v___f_2882_; lean_object* v___x_2883_; lean_object* v___x_2885_; 
lean_inc_n(v_toPure_2871_, 2);
v___f_2880_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2880_, 0, v_a_2875_);
lean_closure_set(v___f_2880_, 1, v_toPure_2871_);
v___x_2881_ = lean_box(0);
v___f_2882_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2882_, 0, v_toPure_2871_);
lean_closure_set(v___f_2882_, 1, v___x_2881_);
v___x_2883_ = lean_array_push(v_a_2876_, v___x_2872_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 1, v___x_2883_);
lean_ctor_set(v___x_2878_, 0, v___x_2881_);
v___x_2885_ = v___x_2878_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2881_);
lean_ctor_set(v_reuseFailAlloc_2889_, 1, v___x_2883_);
v___x_2885_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
v___x_2886_ = lean_apply_2(v_toPure_2871_, lean_box(0), v___x_2885_);
lean_inc(v_toBind_2873_);
v___x_2887_ = lean_apply_4(v_toBind_2873_, lean_box(0), lean_box(0), v___x_2886_, v___f_2882_);
v___x_2888_ = lean_apply_4(v_toBind_2873_, lean_box(0), lean_box(0), v___x_2887_, v___f_2880_);
return v___x_2888_;
}
}
}
else
{
lean_object* v_a_2891_; lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2900_; 
lean_dec(v_toBind_2873_);
lean_dec_ref(v___x_2872_);
v_a_2891_ = lean_ctor_get(v_____do__lift_2874_, 0);
v_a_2892_ = lean_ctor_get(v_____do__lift_2874_, 1);
v_isSharedCheck_2900_ = !lean_is_exclusive(v_____do__lift_2874_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2894_ = v_____do__lift_2874_;
v_isShared_2895_ = v_isSharedCheck_2900_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_inc(v_a_2891_);
lean_dec(v_____do__lift_2874_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2900_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2891_);
lean_ctor_set(v_reuseFailAlloc_2899_, 1, v_a_2892_);
v___x_2897_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
lean_object* v___x_2898_; 
v___x_2898_ = lean_apply_2(v_toPure_2871_, lean_box(0), v___x_2897_);
return v___x_2898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__4(lean_object* v_toFunctor_2901_, lean_object* v_toPure_2902_, lean_object* v_toBind_2903_, lean_object* v___f_2904_, lean_object* v_00_u03b1_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_){
_start:
{
lean_object* v_map_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2921_; 
v_map_2908_ = lean_ctor_get(v_toFunctor_2901_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v_toFunctor_2901_);
if (v_isSharedCheck_2921_ == 0)
{
lean_object* v_unused_2922_; 
v_unused_2922_ = lean_ctor_get(v_toFunctor_2901_, 1);
lean_dec(v_unused_2922_);
v___x_2910_ = v_toFunctor_2901_;
v_isShared_2911_ = v_isSharedCheck_2921_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_map_2908_);
lean_dec(v_toFunctor_2901_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2921_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
uint8_t v___x_2912_; lean_object* v___x_2913_; lean_object* v___f_2914_; lean_object* v___x_2916_; 
v___x_2912_ = 3;
v___x_2913_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2913_, 0, v___y_2906_);
lean_ctor_set_uint8(v___x_2913_, sizeof(void*)*1, v___x_2912_);
lean_inc(v_toBind_2903_);
lean_inc(v_toPure_2902_);
v___f_2914_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__3), 4, 3);
lean_closure_set(v___f_2914_, 0, v_toPure_2902_);
lean_closure_set(v___f_2914_, 1, v___x_2913_);
lean_closure_set(v___f_2914_, 2, v_toBind_2903_);
lean_inc_ref(v___y_2907_);
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 1, v___y_2907_);
lean_ctor_set(v___x_2910_, 0, v___y_2907_);
v___x_2916_ = v___x_2910_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v___y_2907_);
lean_ctor_set(v_reuseFailAlloc_2920_, 1, v___y_2907_);
v___x_2916_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2917_ = lean_apply_2(v_toPure_2902_, lean_box(0), v___x_2916_);
v___x_2918_ = lean_apply_4(v_map_2908_, lean_box(0), lean_box(0), v___f_2904_, v___x_2917_);
v___x_2919_ = lean_apply_4(v_toBind_2903_, lean_box(0), lean_box(0), v___x_2918_, v___f_2914_);
return v___x_2919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg(lean_object* v_inst_2924_){
_start:
{
lean_object* v_toApplicative_2925_; lean_object* v_toBind_2926_; lean_object* v_toFunctor_2927_; lean_object* v_toPure_2928_; lean_object* v___f_2929_; lean_object* v___f_2930_; 
v_toApplicative_2925_ = lean_ctor_get(v_inst_2924_, 0);
lean_inc_ref(v_toApplicative_2925_);
v_toBind_2926_ = lean_ctor_get(v_inst_2924_, 1);
lean_inc(v_toBind_2926_);
lean_dec_ref(v_inst_2924_);
v_toFunctor_2927_ = lean_ctor_get(v_toApplicative_2925_, 0);
lean_inc_ref(v_toFunctor_2927_);
v_toPure_2928_ = lean_ctor_get(v_toApplicative_2925_, 1);
lean_inc(v_toPure_2928_);
lean_dec_ref(v_toApplicative_2925_);
v___f_2929_ = ((lean_object*)(l_Lake_instMonadErrorELogTOfMonad___redArg___closed__0));
v___f_2930_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__4), 7, 4);
lean_closure_set(v___f_2930_, 0, v_toFunctor_2927_);
lean_closure_set(v___f_2930_, 1, v_toPure_2928_);
lean_closure_set(v___f_2930_, 2, v_toBind_2926_);
lean_closure_set(v___f_2930_, 3, v___f_2929_);
return v___f_2930_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad(lean_object* v_m_2931_, lean_object* v_inst_2932_){
_start:
{
lean_object* v___x_2933_; 
v___x_2933_ = l_Lake_instMonadErrorELogTOfMonad___redArg(v_inst_2932_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__1(lean_object* v___y_2934_, lean_object* v___x_2935_, lean_object* v_toPure_2936_, lean_object* v_____do__lift_2937_){
_start:
{
if (lean_obj_tag(v_____do__lift_2937_) == 0)
{
lean_object* v_a_2938_; lean_object* v___x_2939_; 
lean_dec(v_toPure_2936_);
v_a_2938_ = lean_ctor_get(v_____do__lift_2937_, 1);
lean_inc(v_a_2938_);
lean_dec_ref_known(v_____do__lift_2937_, 2);
v___x_2939_ = lean_apply_2(v___y_2934_, v___x_2935_, v_a_2938_);
return v___x_2939_;
}
else
{
lean_object* v_a_2940_; lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2949_; 
lean_dec(v___y_2934_);
v_a_2940_ = lean_ctor_get(v_____do__lift_2937_, 0);
v_a_2941_ = lean_ctor_get(v_____do__lift_2937_, 1);
v_isSharedCheck_2949_ = !lean_is_exclusive(v_____do__lift_2937_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2943_ = v_____do__lift_2937_;
v_isShared_2944_ = v_isSharedCheck_2949_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_inc(v_a_2940_);
lean_dec(v_____do__lift_2937_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2949_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2940_);
lean_ctor_set(v_reuseFailAlloc_2948_, 1, v_a_2941_);
v___x_2946_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
lean_object* v___x_2947_; 
v___x_2947_ = lean_apply_2(v_toPure_2936_, lean_box(0), v___x_2946_);
return v___x_2947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__0(lean_object* v_toPure_2950_, lean_object* v___y_2951_, lean_object* v_toBind_2952_, lean_object* v_____do__lift_2953_){
_start:
{
if (lean_obj_tag(v_____do__lift_2953_) == 0)
{
lean_object* v___x_2954_; 
lean_dec(v_toBind_2952_);
lean_dec(v___y_2951_);
v___x_2954_ = lean_apply_2(v_toPure_2950_, lean_box(0), v_____do__lift_2953_);
return v___x_2954_;
}
else
{
lean_object* v_a_2955_; lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2968_; 
v_a_2955_ = lean_ctor_get(v_____do__lift_2953_, 0);
v_a_2956_ = lean_ctor_get(v_____do__lift_2953_, 1);
v_isSharedCheck_2968_ = !lean_is_exclusive(v_____do__lift_2953_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2958_ = v_____do__lift_2953_;
v_isShared_2959_ = v_isSharedCheck_2968_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_inc(v_a_2955_);
lean_dec(v_____do__lift_2953_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2968_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2960_; lean_object* v___f_2961_; lean_object* v___x_2962_; lean_object* v___x_2964_; 
v___x_2960_ = lean_box(0);
lean_inc(v_toPure_2950_);
v___f_2961_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2961_, 0, v___y_2951_);
lean_closure_set(v___f_2961_, 1, v___x_2960_);
lean_closure_set(v___f_2961_, 2, v_toPure_2950_);
v___x_2962_ = l_Array_shrink___redArg(v_a_2956_, v_a_2955_);
lean_dec(v_a_2955_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set_tag(v___x_2958_, 0);
lean_ctor_set(v___x_2958_, 1, v___x_2962_);
lean_ctor_set(v___x_2958_, 0, v___x_2960_);
v___x_2964_ = v___x_2958_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2960_);
lean_ctor_set(v_reuseFailAlloc_2967_, 1, v___x_2962_);
v___x_2964_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2965_ = lean_apply_2(v_toPure_2950_, lean_box(0), v___x_2964_);
v___x_2966_ = lean_apply_4(v_toBind_2952_, lean_box(0), lean_box(0), v___x_2965_, v___f_2961_);
return v___x_2966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__2(lean_object* v_toPure_2969_, lean_object* v_toBind_2970_, lean_object* v_00_u03b1_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
lean_object* v___f_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
lean_inc(v_toBind_2970_);
v___f_2975_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2975_, 0, v_toPure_2969_);
lean_closure_set(v___f_2975_, 1, v___y_2973_);
lean_closure_set(v___f_2975_, 2, v_toBind_2970_);
v___x_2976_ = lean_apply_1(v___y_2972_, v___y_2974_);
v___x_2977_ = lean_apply_4(v_toBind_2970_, lean_box(0), lean_box(0), v___x_2976_, v___f_2975_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__3(lean_object* v_toPure_2978_, lean_object* v_____do__lift_2979_){
_start:
{
if (lean_obj_tag(v_____do__lift_2979_) == 0)
{
lean_object* v_a_2980_; lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2989_; 
v_a_2980_ = lean_ctor_get(v_____do__lift_2979_, 0);
v_a_2981_ = lean_ctor_get(v_____do__lift_2979_, 1);
v_isSharedCheck_2989_ = !lean_is_exclusive(v_____do__lift_2979_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2983_ = v_____do__lift_2979_;
v_isShared_2984_ = v_isSharedCheck_2989_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_inc(v_a_2980_);
lean_dec(v_____do__lift_2979_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2989_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
lean_ctor_set_tag(v___x_2983_, 1);
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_a_2980_);
lean_ctor_set(v_reuseFailAlloc_2988_, 1, v_a_2981_);
v___x_2986_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
lean_object* v___x_2987_; 
v___x_2987_ = lean_apply_2(v_toPure_2978_, lean_box(0), v___x_2986_);
return v___x_2987_;
}
}
}
else
{
lean_object* v_a_2990_; lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2999_; 
v_a_2990_ = lean_ctor_get(v_____do__lift_2979_, 0);
v_a_2991_ = lean_ctor_get(v_____do__lift_2979_, 1);
v_isSharedCheck_2999_ = !lean_is_exclusive(v_____do__lift_2979_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2993_ = v_____do__lift_2979_;
v_isShared_2994_ = v_isSharedCheck_2999_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_inc(v_a_2990_);
lean_dec(v_____do__lift_2979_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2999_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2990_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v_a_2991_);
v___x_2996_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
lean_object* v___x_2997_; 
v___x_2997_ = lean_apply_2(v_toPure_2978_, lean_box(0), v___x_2996_);
return v___x_2997_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__4(lean_object* v_toFunctor_3000_, lean_object* v_toPure_3001_, lean_object* v___f_3002_, lean_object* v_toBind_3003_, lean_object* v___f_3004_, lean_object* v_00_u03b1_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v_map_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3017_; 
v_map_3007_ = lean_ctor_get(v_toFunctor_3000_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v_toFunctor_3000_);
if (v_isSharedCheck_3017_ == 0)
{
lean_object* v_unused_3018_; 
v_unused_3018_ = lean_ctor_get(v_toFunctor_3000_, 1);
lean_dec(v_unused_3018_);
v___x_3009_ = v_toFunctor_3000_;
v_isShared_3010_ = v_isSharedCheck_3017_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_map_3007_);
lean_dec(v_toFunctor_3000_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3017_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
lean_inc_ref(v___y_3006_);
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 1, v___y_3006_);
lean_ctor_set(v___x_3009_, 0, v___y_3006_);
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___y_3006_);
lean_ctor_set(v_reuseFailAlloc_3016_, 1, v___y_3006_);
v___x_3012_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3013_ = lean_apply_2(v_toPure_3001_, lean_box(0), v___x_3012_);
v___x_3014_ = lean_apply_4(v_map_3007_, lean_box(0), lean_box(0), v___f_3002_, v___x_3013_);
v___x_3015_ = lean_apply_4(v_toBind_3003_, lean_box(0), lean_box(0), v___x_3014_, v___f_3004_);
return v___x_3015_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg(lean_object* v_inst_3019_){
_start:
{
lean_object* v_toApplicative_3020_; lean_object* v_toBind_3021_; lean_object* v_toFunctor_3022_; lean_object* v_toPure_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3041_; 
v_toApplicative_3020_ = lean_ctor_get(v_inst_3019_, 0);
lean_inc_ref(v_toApplicative_3020_);
v_toBind_3021_ = lean_ctor_get(v_inst_3019_, 1);
lean_inc(v_toBind_3021_);
lean_dec_ref(v_inst_3019_);
v_toFunctor_3022_ = lean_ctor_get(v_toApplicative_3020_, 0);
v_toPure_3023_ = lean_ctor_get(v_toApplicative_3020_, 1);
v_isSharedCheck_3041_ = !lean_is_exclusive(v_toApplicative_3020_);
if (v_isSharedCheck_3041_ == 0)
{
lean_object* v_unused_3042_; lean_object* v_unused_3043_; lean_object* v_unused_3044_; 
v_unused_3042_ = lean_ctor_get(v_toApplicative_3020_, 4);
lean_dec(v_unused_3042_);
v_unused_3043_ = lean_ctor_get(v_toApplicative_3020_, 3);
lean_dec(v_unused_3043_);
v_unused_3044_ = lean_ctor_get(v_toApplicative_3020_, 2);
lean_dec(v_unused_3044_);
v___x_3025_ = v_toApplicative_3020_;
v_isShared_3026_ = v_isSharedCheck_3041_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_toPure_3023_);
lean_inc(v_toFunctor_3022_);
lean_dec(v_toApplicative_3020_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3041_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___f_3027_; lean_object* v___f_3028_; lean_object* v___f_3029_; lean_object* v___f_3030_; lean_object* v___f_3031_; lean_object* v___f_3032_; lean_object* v___f_3033_; lean_object* v___f_3034_; lean_object* v___x_3035_; lean_object* v___f_3036_; lean_object* v___x_3038_; 
v___f_3027_ = ((lean_object*)(l_Lake_instMonadErrorELogTOfMonad___redArg___closed__0));
lean_inc_n(v_toBind_3021_, 4);
lean_inc_n(v_toPure_3023_, 7);
v___f_3028_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__2), 6, 2);
lean_closure_set(v___f_3028_, 0, v_toPure_3023_);
lean_closure_set(v___f_3028_, 1, v_toBind_3021_);
v___f_3029_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3029_, 0, v_toPure_3023_);
lean_inc_ref_n(v_toFunctor_3022_, 2);
v___f_3030_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__4), 7, 5);
lean_closure_set(v___f_3030_, 0, v_toFunctor_3022_);
lean_closure_set(v___f_3030_, 1, v_toPure_3023_);
lean_closure_set(v___f_3030_, 2, v___f_3027_);
lean_closure_set(v___f_3030_, 3, v_toBind_3021_);
lean_closure_set(v___f_3030_, 4, v___f_3029_);
v___f_3031_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_3031_, 0, v_toPure_3023_);
lean_closure_set(v___f_3031_, 1, v_toBind_3021_);
v___f_3032_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_3032_, 0, v_toPure_3023_);
lean_closure_set(v___f_3032_, 1, v_toBind_3021_);
v___f_3033_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_3033_, 0, v_toPure_3023_);
lean_closure_set(v___f_3033_, 1, v___f_3031_);
v___f_3034_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_3034_, 0, v_toFunctor_3022_);
lean_closure_set(v___f_3034_, 1, v_toPure_3023_);
lean_closure_set(v___f_3034_, 2, v_toBind_3021_);
v___x_3035_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_3022_);
v___f_3036_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3036_, 0, v_toPure_3023_);
if (v_isShared_3026_ == 0)
{
lean_ctor_set(v___x_3025_, 4, v___f_3032_);
lean_ctor_set(v___x_3025_, 3, v___f_3033_);
lean_ctor_set(v___x_3025_, 2, v___f_3034_);
lean_ctor_set(v___x_3025_, 1, v___f_3036_);
lean_ctor_set(v___x_3025_, 0, v___x_3035_);
v___x_3038_ = v___x_3025_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3035_);
lean_ctor_set(v_reuseFailAlloc_3040_, 1, v___f_3036_);
lean_ctor_set(v_reuseFailAlloc_3040_, 2, v___f_3034_);
lean_ctor_set(v_reuseFailAlloc_3040_, 3, v___f_3033_);
lean_ctor_set(v_reuseFailAlloc_3040_, 4, v___f_3032_);
v___x_3038_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
lean_object* v___x_3039_; 
v___x_3039_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3038_);
lean_ctor_set(v___x_3039_, 1, v___f_3030_);
lean_ctor_set(v___x_3039_, 2, v___f_3028_);
return v___x_3039_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad(lean_object* v_m_3045_, lean_object* v_inst_3046_){
_start:
{
lean_object* v___x_3047_; 
v___x_3047_ = l_Lake_instAlternativeELogTOfMonad___redArg(v_inst_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run___redArg(lean_object* v_self_3048_, lean_object* v_log_3049_){
_start:
{
lean_object* v___x_3050_; 
v___x_3050_ = lean_apply_1(v_self_3048_, v_log_3049_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run(lean_object* v_m_3051_, lean_object* v_00_u03b1_3052_, lean_object* v_self_3053_, lean_object* v_log_3054_){
_start:
{
lean_object* v___x_3055_; 
v___x_3055_ = lean_apply_1(v_self_3053_, v_log_3054_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x27___redArg(lean_object* v_inst_3057_, lean_object* v_self_3058_, lean_object* v_log_3059_){
_start:
{
lean_object* v_map_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v_map_3060_ = lean_ctor_get(v_inst_3057_, 0);
lean_inc(v_map_3060_);
lean_dec_ref(v_inst_3057_);
v___x_3061_ = ((lean_object*)(l_Lake_ELogT_run_x27___redArg___closed__0));
v___x_3062_ = lean_apply_1(v_self_3058_, v_log_3059_);
v___x_3063_ = lean_apply_4(v_map_3060_, lean_box(0), lean_box(0), v___x_3061_, v___x_3062_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x27(lean_object* v_m_3064_, lean_object* v_00_u03b1_3065_, lean_object* v_inst_3066_, lean_object* v_self_3067_, lean_object* v_log_3068_){
_start:
{
lean_object* v_map_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v_map_3069_ = lean_ctor_get(v_inst_3066_, 0);
lean_inc(v_map_3069_);
lean_dec_ref(v_inst_3066_);
v___x_3070_ = ((lean_object*)(l_Lake_ELogT_run_x27___redArg___closed__0));
v___x_3071_ = lean_apply_1(v_self_3067_, v_log_3068_);
v___x_3072_ = lean_apply_4(v_map_3069_, lean_box(0), lean_box(0), v___x_3070_, v___x_3071_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT___redArg(lean_object* v_inst_3074_, lean_object* v_self_3075_, lean_object* v_a_3076_){
_start:
{
lean_object* v_map_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v_map_3077_ = lean_ctor_get(v_inst_3074_, 0);
lean_inc(v_map_3077_);
lean_dec_ref(v_inst_3074_);
v___x_3078_ = ((lean_object*)(l_Lake_ELogT_toLogT___redArg___closed__0));
v___x_3079_ = lean_apply_1(v_self_3075_, v_a_3076_);
v___x_3080_ = lean_apply_4(v_map_3077_, lean_box(0), lean_box(0), v___x_3078_, v___x_3079_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT(lean_object* v_m_3081_, lean_object* v_00_u03b1_3082_, lean_object* v_inst_3083_, lean_object* v_self_3084_, lean_object* v_a_3085_){
_start:
{
lean_object* v_map_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v_map_3086_ = lean_ctor_get(v_inst_3083_, 0);
lean_inc(v_map_3086_);
lean_dec_ref(v_inst_3083_);
v___x_3087_ = ((lean_object*)(l_Lake_ELogT_toLogT___redArg___closed__0));
v___x_3088_ = lean_apply_1(v_self_3084_, v_a_3085_);
v___x_3089_ = lean_apply_4(v_map_3086_, lean_box(0), lean_box(0), v___x_3087_, v___x_3088_);
return v___x_3089_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT_x3f___redArg(lean_object* v_inst_3091_, lean_object* v_self_3092_, lean_object* v_a_3093_){
_start:
{
lean_object* v_map_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v_map_3094_ = lean_ctor_get(v_inst_3091_, 0);
lean_inc(v_map_3094_);
lean_dec_ref(v_inst_3091_);
v___x_3095_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3096_ = lean_apply_1(v_self_3092_, v_a_3093_);
v___x_3097_ = lean_apply_4(v_map_3094_, lean_box(0), lean_box(0), v___x_3095_, v___x_3096_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT_x3f(lean_object* v_m_3098_, lean_object* v_00_u03b1_3099_, lean_object* v_inst_3100_, lean_object* v_self_3101_, lean_object* v_a_3102_){
_start:
{
lean_object* v_map_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v_map_3103_ = lean_ctor_get(v_inst_3100_, 0);
lean_inc(v_map_3103_);
lean_dec_ref(v_inst_3100_);
v___x_3104_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3105_ = lean_apply_1(v_self_3101_, v_a_3102_);
v___x_3106_ = lean_apply_4(v_map_3103_, lean_box(0), lean_box(0), v___x_3104_, v___x_3105_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f___redArg(lean_object* v_inst_3107_, lean_object* v_self_3108_, lean_object* v_log_3109_){
_start:
{
lean_object* v_map_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v_map_3110_ = lean_ctor_get(v_inst_3107_, 0);
lean_inc(v_map_3110_);
lean_dec_ref(v_inst_3107_);
v___x_3111_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3112_ = lean_apply_1(v_self_3108_, v_log_3109_);
v___x_3113_ = lean_apply_4(v_map_3110_, lean_box(0), lean_box(0), v___x_3111_, v___x_3112_);
return v___x_3113_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f(lean_object* v_m_3114_, lean_object* v_00_u03b1_3115_, lean_object* v_inst_3116_, lean_object* v_self_3117_, lean_object* v_log_3118_){
_start:
{
lean_object* v_map_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v_map_3119_ = lean_ctor_get(v_inst_3116_, 0);
lean_inc(v_map_3119_);
lean_dec_ref(v_inst_3116_);
v___x_3120_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3121_ = lean_apply_1(v_self_3117_, v_log_3118_);
v___x_3122_ = lean_apply_4(v_map_3119_, lean_box(0), lean_box(0), v___x_3120_, v___x_3121_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f_x27___redArg(lean_object* v_inst_3124_, lean_object* v_self_3125_, lean_object* v_log_3126_){
_start:
{
lean_object* v_map_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v_map_3127_ = lean_ctor_get(v_inst_3124_, 0);
lean_inc(v_map_3127_);
lean_dec_ref(v_inst_3124_);
v___x_3128_ = ((lean_object*)(l_Lake_ELogT_run_x3f_x27___redArg___closed__0));
v___x_3129_ = lean_apply_1(v_self_3125_, v_log_3126_);
v___x_3130_ = lean_apply_4(v_map_3127_, lean_box(0), lean_box(0), v___x_3128_, v___x_3129_);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f_x27(lean_object* v_m_3131_, lean_object* v_00_u03b1_3132_, lean_object* v_inst_3133_, lean_object* v_self_3134_, lean_object* v_log_3135_){
_start:
{
lean_object* v_map_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v_map_3136_ = lean_ctor_get(v_inst_3133_, 0);
lean_inc(v_map_3136_);
lean_dec_ref(v_inst_3133_);
v___x_3137_ = ((lean_object*)(l_Lake_ELogT_run_x3f_x27___redArg___closed__0));
v___x_3138_ = lean_apply_1(v_self_3134_, v_log_3135_);
v___x_3139_ = lean_apply_4(v_map_3136_, lean_box(0), lean_box(0), v___x_3137_, v___x_3138_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg___lam__0(lean_object* v_f_3140_, lean_object* v_____x_3141_){
_start:
{
lean_object* v_fst_3142_; lean_object* v_snd_3143_; lean_object* v___x_3144_; 
v_fst_3142_ = lean_ctor_get(v_____x_3141_, 0);
lean_inc(v_fst_3142_);
v_snd_3143_ = lean_ctor_get(v_____x_3141_, 1);
lean_inc(v_snd_3143_);
lean_dec_ref(v_____x_3141_);
v___x_3144_ = lean_apply_2(v_f_3140_, v_fst_3142_, v_snd_3143_);
return v___x_3144_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg___lam__1(lean_object* v_toPure_3145_, lean_object* v_toBind_3146_, lean_object* v___f_3147_, lean_object* v_____do__lift_3148_){
_start:
{
if (lean_obj_tag(v_____do__lift_3148_) == 0)
{
lean_object* v_a_3149_; lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3158_; 
lean_dec(v___f_3147_);
lean_dec(v_toBind_3146_);
v_a_3149_ = lean_ctor_get(v_____do__lift_3148_, 0);
v_a_3150_ = lean_ctor_get(v_____do__lift_3148_, 1);
v_isSharedCheck_3158_ = !lean_is_exclusive(v_____do__lift_3148_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3152_ = v_____do__lift_3148_;
v_isShared_3153_ = v_isSharedCheck_3158_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_inc(v_a_3149_);
lean_dec(v_____do__lift_3148_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3158_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v_a_3149_);
lean_ctor_set(v_reuseFailAlloc_3157_, 1, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
lean_object* v___x_3156_; 
v___x_3156_ = lean_apply_2(v_toPure_3145_, lean_box(0), v___x_3155_);
return v___x_3156_;
}
}
}
else
{
lean_object* v_a_3159_; lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3172_; 
v_a_3159_ = lean_ctor_get(v_____do__lift_3148_, 0);
v_a_3160_ = lean_ctor_get(v_____do__lift_3148_, 1);
v_isSharedCheck_3172_ = !lean_is_exclusive(v_____do__lift_3148_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3162_ = v_____do__lift_3148_;
v_isShared_3163_ = v_isSharedCheck_3172_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_inc(v_a_3159_);
lean_dec(v_____do__lift_3148_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3172_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3168_; 
v___x_3164_ = lean_array_get_size(v_a_3160_);
lean_inc(v_a_3159_);
v___x_3165_ = l_Array_extract___redArg(v_a_3160_, v_a_3159_, v___x_3164_);
v___x_3166_ = l_Array_shrink___redArg(v_a_3160_, v_a_3159_);
lean_dec(v_a_3159_);
if (v_isShared_3163_ == 0)
{
lean_ctor_set_tag(v___x_3162_, 0);
lean_ctor_set(v___x_3162_, 1, v___x_3166_);
lean_ctor_set(v___x_3162_, 0, v___x_3165_);
v___x_3168_ = v___x_3162_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v___x_3165_);
lean_ctor_set(v_reuseFailAlloc_3171_, 1, v___x_3166_);
v___x_3168_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3169_ = lean_apply_2(v_toPure_3145_, lean_box(0), v___x_3168_);
v___x_3170_ = lean_apply_4(v_toBind_3146_, lean_box(0), lean_box(0), v___x_3169_, v___f_3147_);
return v___x_3170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg(lean_object* v_inst_3173_, lean_object* v_f_3174_, lean_object* v_self_3175_, lean_object* v_a_3176_){
_start:
{
lean_object* v_toApplicative_3177_; lean_object* v_toBind_3178_; lean_object* v_toPure_3179_; lean_object* v___f_3180_; lean_object* v___x_3181_; lean_object* v___f_3182_; lean_object* v___x_3183_; 
v_toApplicative_3177_ = lean_ctor_get(v_inst_3173_, 0);
lean_inc_ref(v_toApplicative_3177_);
v_toBind_3178_ = lean_ctor_get(v_inst_3173_, 1);
lean_inc_n(v_toBind_3178_, 2);
lean_dec_ref(v_inst_3173_);
v_toPure_3179_ = lean_ctor_get(v_toApplicative_3177_, 1);
lean_inc(v_toPure_3179_);
lean_dec_ref(v_toApplicative_3177_);
v___f_3180_ = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3180_, 0, v_f_3174_);
v___x_3181_ = lean_apply_1(v_self_3175_, v_a_3176_);
v___f_3182_ = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3182_, 0, v_toPure_3179_);
lean_closure_set(v___f_3182_, 1, v_toBind_3178_);
lean_closure_set(v___f_3182_, 2, v___f_3180_);
v___x_3183_ = lean_apply_4(v_toBind_3178_, lean_box(0), lean_box(0), v___x_3181_, v___f_3182_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog(lean_object* v_m_3184_, lean_object* v_00_u03b1_3185_, lean_object* v_inst_3186_, lean_object* v_f_3187_, lean_object* v_self_3188_, lean_object* v_a_3189_){
_start:
{
lean_object* v_toApplicative_3190_; lean_object* v_toBind_3191_; lean_object* v_toPure_3192_; lean_object* v___f_3193_; lean_object* v___x_3194_; lean_object* v___f_3195_; lean_object* v___x_3196_; 
v_toApplicative_3190_ = lean_ctor_get(v_inst_3186_, 0);
lean_inc_ref(v_toApplicative_3190_);
v_toBind_3191_ = lean_ctor_get(v_inst_3186_, 1);
lean_inc_n(v_toBind_3191_, 2);
lean_dec_ref(v_inst_3186_);
v_toPure_3192_ = lean_ctor_get(v_toApplicative_3190_, 1);
lean_inc(v_toPure_3192_);
lean_dec_ref(v_toApplicative_3190_);
v___f_3193_ = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3193_, 0, v_f_3187_);
v___x_3194_ = lean_apply_1(v_self_3188_, v_a_3189_);
v___f_3195_ = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3195_, 0, v_toPure_3192_);
lean_closure_set(v___f_3195_, 1, v_toBind_3191_);
lean_closure_set(v___f_3195_, 2, v___f_3193_);
v___x_3196_ = lean_apply_4(v_toBind_3191_, lean_box(0), lean_box(0), v___x_3194_, v___f_3195_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__1(lean_object* v_toPure_3197_, lean_object* v_a_3198_, lean_object* v_____r_3199_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = lean_apply_2(v_toPure_3197_, lean_box(0), v_a_3198_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__0(lean_object* v_inst_3201_, lean_object* v_a_3202_, lean_object* v_____r_3203_){
_start:
{
lean_object* v_throw_3204_; lean_object* v___x_3205_; 
v_throw_3204_ = lean_ctor_get(v_inst_3201_, 0);
lean_inc(v_throw_3204_);
lean_dec_ref(v_inst_3201_);
v___x_3205_ = lean_apply_2(v_throw_3204_, lean_box(0), v_a_3202_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__2(lean_object* v_toPure_3206_, lean_object* v_set_3207_, lean_object* v_toBind_3208_, lean_object* v_inst_3209_, lean_object* v_____do__lift_3210_){
_start:
{
if (lean_obj_tag(v_____do__lift_3210_) == 0)
{
lean_object* v_a_3211_; lean_object* v_a_3212_; lean_object* v___f_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
lean_dec_ref(v_inst_3209_);
v_a_3211_ = lean_ctor_get(v_____do__lift_3210_, 0);
lean_inc(v_a_3211_);
v_a_3212_ = lean_ctor_get(v_____do__lift_3210_, 1);
lean_inc(v_a_3212_);
lean_dec_ref_known(v_____do__lift_3210_, 2);
v___f_3213_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3213_, 0, v_toPure_3206_);
lean_closure_set(v___f_3213_, 1, v_a_3211_);
v___x_3214_ = lean_apply_1(v_set_3207_, v_a_3212_);
v___x_3215_ = lean_apply_4(v_toBind_3208_, lean_box(0), lean_box(0), v___x_3214_, v___f_3213_);
return v___x_3215_;
}
else
{
lean_object* v_a_3216_; lean_object* v_a_3217_; lean_object* v___f_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
lean_dec(v_toPure_3206_);
v_a_3216_ = lean_ctor_get(v_____do__lift_3210_, 0);
lean_inc(v_a_3216_);
v_a_3217_ = lean_ctor_get(v_____do__lift_3210_, 1);
lean_inc(v_a_3217_);
lean_dec_ref_known(v_____do__lift_3210_, 2);
v___f_3218_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3218_, 0, v_inst_3209_);
lean_closure_set(v___f_3218_, 1, v_a_3216_);
v___x_3219_ = lean_apply_1(v_set_3207_, v_a_3217_);
v___x_3220_ = lean_apply_4(v_toBind_3208_, lean_box(0), lean_box(0), v___x_3219_, v___f_3218_);
return v___x_3220_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__3(lean_object* v_self_3221_, lean_object* v_inst_3222_, lean_object* v_toBind_3223_, lean_object* v___f_3224_, lean_object* v_____do__lift_3225_){
_start:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3226_ = lean_apply_1(v_self_3221_, v_____do__lift_3225_);
v___x_3227_ = lean_apply_2(v_inst_3222_, lean_box(0), v___x_3226_);
v___x_3228_ = lean_apply_4(v_toBind_3223_, lean_box(0), lean_box(0), v___x_3227_, v___f_3224_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg(lean_object* v_inst_3229_, lean_object* v_inst_3230_, lean_object* v_inst_3231_, lean_object* v_inst_3232_, lean_object* v_self_3233_){
_start:
{
lean_object* v_toApplicative_3234_; lean_object* v_toBind_3235_; lean_object* v_set_3236_; lean_object* v_modifyGet_3237_; lean_object* v_toPure_3238_; lean_object* v___f_3239_; lean_object* v___x_3240_; lean_object* v___f_3241_; lean_object* v___f_3242_; lean_object* v___x_3243_; 
v_toApplicative_3234_ = lean_ctor_get(v_inst_3229_, 0);
lean_inc_ref(v_toApplicative_3234_);
v_toBind_3235_ = lean_ctor_get(v_inst_3229_, 1);
lean_inc_n(v_toBind_3235_, 3);
lean_dec_ref(v_inst_3229_);
v_set_3236_ = lean_ctor_get(v_inst_3230_, 1);
lean_inc(v_set_3236_);
v_modifyGet_3237_ = lean_ctor_get(v_inst_3230_, 2);
lean_inc(v_modifyGet_3237_);
lean_dec_ref(v_inst_3230_);
v_toPure_3238_ = lean_ctor_get(v_toApplicative_3234_, 1);
lean_inc(v_toPure_3238_);
lean_dec_ref(v_toApplicative_3234_);
v___f_3239_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_3240_ = lean_apply_2(v_modifyGet_3237_, lean_box(0), v___f_3239_);
v___f_3241_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3241_, 0, v_toPure_3238_);
lean_closure_set(v___f_3241_, 1, v_set_3236_);
lean_closure_set(v___f_3241_, 2, v_toBind_3235_);
lean_closure_set(v___f_3241_, 3, v_inst_3231_);
v___f_3242_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3242_, 0, v_self_3233_);
lean_closure_set(v___f_3242_, 1, v_inst_3232_);
lean_closure_set(v___f_3242_, 2, v_toBind_3235_);
lean_closure_set(v___f_3242_, 3, v___f_3241_);
v___x_3243_ = lean_apply_4(v_toBind_3235_, lean_box(0), lean_box(0), v___x_3240_, v___f_3242_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun(lean_object* v_n_3244_, lean_object* v_m_3245_, lean_object* v_00_u03b1_3246_, lean_object* v_inst_3247_, lean_object* v_inst_3248_, lean_object* v_inst_3249_, lean_object* v_inst_3250_, lean_object* v_self_3251_){
_start:
{
lean_object* v_toApplicative_3252_; lean_object* v_toBind_3253_; lean_object* v_set_3254_; lean_object* v_modifyGet_3255_; lean_object* v_toPure_3256_; lean_object* v___f_3257_; lean_object* v___x_3258_; lean_object* v___f_3259_; lean_object* v___f_3260_; lean_object* v___x_3261_; 
v_toApplicative_3252_ = lean_ctor_get(v_inst_3247_, 0);
lean_inc_ref(v_toApplicative_3252_);
v_toBind_3253_ = lean_ctor_get(v_inst_3247_, 1);
lean_inc_n(v_toBind_3253_, 3);
lean_dec_ref(v_inst_3247_);
v_set_3254_ = lean_ctor_get(v_inst_3248_, 1);
lean_inc(v_set_3254_);
v_modifyGet_3255_ = lean_ctor_get(v_inst_3248_, 2);
lean_inc(v_modifyGet_3255_);
lean_dec_ref(v_inst_3248_);
v_toPure_3256_ = lean_ctor_get(v_toApplicative_3252_, 1);
lean_inc(v_toPure_3256_);
lean_dec_ref(v_toApplicative_3252_);
v___f_3257_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_3258_ = lean_apply_2(v_modifyGet_3255_, lean_box(0), v___f_3257_);
v___f_3259_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3259_, 0, v_toPure_3256_);
lean_closure_set(v___f_3259_, 1, v_set_3254_);
lean_closure_set(v___f_3259_, 2, v_toBind_3253_);
lean_closure_set(v___f_3259_, 3, v_inst_3249_);
v___f_3260_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3260_, 0, v_self_3251_);
lean_closure_set(v___f_3260_, 1, v_inst_3250_);
lean_closure_set(v___f_3260_, 2, v_toBind_3253_);
lean_closure_set(v___f_3260_, 3, v___f_3259_);
v___x_3261_ = lean_apply_4(v_toBind_3253_, lean_box(0), lean_box(0), v___x_3258_, v___f_3260_);
return v___x_3261_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__2(lean_object* v_toPure_3262_, lean_object* v_x_3263_){
_start:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3264_ = lean_box(0);
v___x_3265_ = lean_apply_2(v_toPure_3262_, lean_box(0), v___x_3264_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__0(lean_object* v_a_3266_, lean_object* v_toPure_3267_, lean_object* v_x_3268_){
_start:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3269_, 0, v_a_3266_);
v___x_3270_ = lean_apply_2(v_toPure_3267_, lean_box(0), v___x_3269_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__1(lean_object* v_toPure_3271_, lean_object* v___x_3272_, lean_object* v_toSeqRight_3273_, lean_object* v_inst_3274_, lean_object* v___f_3275_, lean_object* v___f_3276_, lean_object* v___f_3277_, lean_object* v_____do__lift_3278_){
_start:
{
if (lean_obj_tag(v_____do__lift_3278_) == 0)
{
lean_object* v_a_3279_; lean_object* v_a_3280_; lean_object* v___f_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; uint8_t v___x_3284_; 
lean_dec(v___f_3277_);
lean_dec(v___f_3276_);
v_a_3279_ = lean_ctor_get(v_____do__lift_3278_, 0);
lean_inc(v_a_3279_);
v_a_3280_ = lean_ctor_get(v_____do__lift_3278_, 1);
lean_inc(v_a_3280_);
lean_dec_ref_known(v_____do__lift_3278_, 2);
lean_inc(v_toPure_3271_);
v___f_3281_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3281_, 0, v_a_3279_);
lean_closure_set(v___f_3281_, 1, v_toPure_3271_);
v___x_3282_ = lean_array_get_size(v_a_3280_);
v___x_3283_ = lean_box(0);
v___x_3284_ = lean_nat_dec_lt(v___x_3272_, v___x_3282_);
if (v___x_3284_ == 0)
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
lean_dec(v_a_3280_);
lean_dec(v___f_3275_);
lean_dec_ref(v_inst_3274_);
v___x_3285_ = lean_apply_2(v_toPure_3271_, lean_box(0), v___x_3283_);
v___x_3286_ = lean_apply_4(v_toSeqRight_3273_, lean_box(0), lean_box(0), v___x_3285_, v___f_3281_);
return v___x_3286_;
}
else
{
size_t v___x_3287_; size_t v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
lean_dec(v_toPure_3271_);
v___x_3287_ = ((size_t)0ULL);
v___x_3288_ = lean_usize_of_nat(v___x_3282_);
v___x_3289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3274_, v___f_3275_, v_a_3280_, v___x_3287_, v___x_3288_, v___x_3283_);
v___x_3290_ = lean_apply_4(v_toSeqRight_3273_, lean_box(0), lean_box(0), v___x_3289_, v___f_3281_);
return v___x_3290_;
}
}
else
{
lean_object* v_a_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; uint8_t v___x_3294_; 
lean_dec(v___f_3275_);
v_a_3291_ = lean_ctor_get(v_____do__lift_3278_, 1);
lean_inc(v_a_3291_);
lean_dec_ref_known(v_____do__lift_3278_, 2);
v___x_3292_ = lean_array_get_size(v_a_3291_);
v___x_3293_ = lean_box(0);
v___x_3294_ = lean_nat_dec_lt(v___x_3272_, v___x_3292_);
if (v___x_3294_ == 0)
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
lean_dec(v_a_3291_);
lean_dec(v___f_3277_);
lean_dec_ref(v_inst_3274_);
v___x_3295_ = lean_apply_2(v_toPure_3271_, lean_box(0), v___x_3293_);
v___x_3296_ = lean_apply_4(v_toSeqRight_3273_, lean_box(0), lean_box(0), v___x_3295_, v___f_3276_);
return v___x_3296_;
}
else
{
size_t v___x_3297_; size_t v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
lean_dec(v_toPure_3271_);
v___x_3297_ = ((size_t)0ULL);
v___x_3298_ = lean_usize_of_nat(v___x_3292_);
v___x_3299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3274_, v___f_3277_, v_a_3291_, v___x_3297_, v___x_3298_, v___x_3293_);
v___x_3300_ = lean_apply_4(v_toSeqRight_3273_, lean_box(0), lean_box(0), v___x_3299_, v___f_3276_);
return v___x_3300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed(lean_object* v_toPure_3301_, lean_object* v___x_3302_, lean_object* v_toSeqRight_3303_, lean_object* v_inst_3304_, lean_object* v___f_3305_, lean_object* v___f_3306_, lean_object* v___f_3307_, lean_object* v_____do__lift_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l_Lake_ELogT_replayLog_x3f___redArg___lam__1(v_toPure_3301_, v___x_3302_, v_toSeqRight_3303_, v_inst_3304_, v___f_3305_, v___f_3306_, v___f_3307_, v_____do__lift_3308_);
lean_dec(v___x_3302_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg(lean_object* v_inst_3310_, lean_object* v_logger_3311_, lean_object* v_inst_3312_, lean_object* v_self_3313_){
_start:
{
lean_object* v_toApplicative_3314_; lean_object* v_toBind_3315_; lean_object* v_toPure_3316_; lean_object* v_toSeqRight_3317_; lean_object* v___f_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___f_3323_; lean_object* v___f_3324_; lean_object* v___x_3325_; 
v_toApplicative_3314_ = lean_ctor_get(v_inst_3310_, 0);
v_toBind_3315_ = lean_ctor_get(v_inst_3310_, 1);
lean_inc(v_toBind_3315_);
v_toPure_3316_ = lean_ctor_get(v_toApplicative_3314_, 1);
lean_inc_n(v_toPure_3316_, 2);
v_toSeqRight_3317_ = lean_ctor_get(v_toApplicative_3314_, 4);
lean_inc(v_toSeqRight_3317_);
v___f_3318_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3318_, 0, v_logger_3311_);
v___x_3319_ = lean_unsigned_to_nat(0u);
v___x_3320_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3321_ = lean_apply_1(v_self_3313_, v___x_3320_);
v___x_3322_ = lean_apply_2(v_inst_3312_, lean_box(0), v___x_3321_);
v___f_3323_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3323_, 0, v_toPure_3316_);
lean_inc_ref(v___f_3318_);
v___f_3324_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_3324_, 0, v_toPure_3316_);
lean_closure_set(v___f_3324_, 1, v___x_3319_);
lean_closure_set(v___f_3324_, 2, v_toSeqRight_3317_);
lean_closure_set(v___f_3324_, 3, v_inst_3310_);
lean_closure_set(v___f_3324_, 4, v___f_3318_);
lean_closure_set(v___f_3324_, 5, v___f_3323_);
lean_closure_set(v___f_3324_, 6, v___f_3318_);
v___x_3325_ = lean_apply_4(v_toBind_3315_, lean_box(0), lean_box(0), v___x_3322_, v___f_3324_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f(lean_object* v_n_3326_, lean_object* v_m_3327_, lean_object* v_00_u03b1_3328_, lean_object* v_inst_3329_, lean_object* v_logger_3330_, lean_object* v_inst_3331_, lean_object* v_self_3332_){
_start:
{
lean_object* v_toApplicative_3333_; lean_object* v_toBind_3334_; lean_object* v_toPure_3335_; lean_object* v_toSeqRight_3336_; lean_object* v___f_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___f_3342_; lean_object* v___f_3343_; lean_object* v___x_3344_; 
v_toApplicative_3333_ = lean_ctor_get(v_inst_3329_, 0);
v_toBind_3334_ = lean_ctor_get(v_inst_3329_, 1);
lean_inc(v_toBind_3334_);
v_toPure_3335_ = lean_ctor_get(v_toApplicative_3333_, 1);
lean_inc_n(v_toPure_3335_, 2);
v_toSeqRight_3336_ = lean_ctor_get(v_toApplicative_3333_, 4);
lean_inc(v_toSeqRight_3336_);
v___f_3337_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3337_, 0, v_logger_3330_);
v___x_3338_ = lean_unsigned_to_nat(0u);
v___x_3339_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3340_ = lean_apply_1(v_self_3332_, v___x_3339_);
v___x_3341_ = lean_apply_2(v_inst_3331_, lean_box(0), v___x_3340_);
v___f_3342_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3342_, 0, v_toPure_3335_);
lean_inc_ref(v___f_3337_);
v___f_3343_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_3343_, 0, v_toPure_3335_);
lean_closure_set(v___f_3343_, 1, v___x_3338_);
lean_closure_set(v___f_3343_, 2, v_toSeqRight_3336_);
lean_closure_set(v___f_3343_, 3, v_inst_3329_);
lean_closure_set(v___f_3343_, 4, v___f_3337_);
lean_closure_set(v___f_3343_, 5, v___f_3342_);
lean_closure_set(v___f_3343_, 6, v___f_3337_);
v___x_3344_ = lean_apply_4(v_toBind_3334_, lean_box(0), lean_box(0), v___x_3341_, v___f_3343_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg___lam__3(lean_object* v_toPure_3345_, lean_object* v_a_3346_, lean_object* v_x_3347_){
_start:
{
lean_object* v___x_3348_; 
v___x_3348_ = lean_apply_2(v_toPure_3345_, lean_box(0), v_a_3346_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg___lam__0(lean_object* v_toApplicative_3349_, lean_object* v_toPure_3350_, lean_object* v___x_3351_, lean_object* v_toSeqRight_3352_, lean_object* v_inst_3353_, lean_object* v___f_3354_, lean_object* v___f_3355_, lean_object* v___f_3356_, lean_object* v_____do__lift_3357_){
_start:
{
if (lean_obj_tag(v_____do__lift_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v_a_3359_; lean_object* v_toPure_3360_; lean_object* v___f_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; uint8_t v___x_3364_; 
lean_dec(v___f_3356_);
lean_dec(v___f_3355_);
v_a_3358_ = lean_ctor_get(v_____do__lift_3357_, 0);
lean_inc(v_a_3358_);
v_a_3359_ = lean_ctor_get(v_____do__lift_3357_, 1);
lean_inc(v_a_3359_);
lean_dec_ref_known(v_____do__lift_3357_, 2);
v_toPure_3360_ = lean_ctor_get(v_toApplicative_3349_, 1);
lean_inc(v_toPure_3360_);
lean_dec_ref(v_toApplicative_3349_);
v___f_3361_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog___redArg___lam__3), 3, 2);
lean_closure_set(v___f_3361_, 0, v_toPure_3350_);
lean_closure_set(v___f_3361_, 1, v_a_3358_);
v___x_3362_ = lean_array_get_size(v_a_3359_);
v___x_3363_ = lean_box(0);
v___x_3364_ = lean_nat_dec_lt(v___x_3351_, v___x_3362_);
if (v___x_3364_ == 0)
{
lean_object* v___x_3365_; lean_object* v___x_3366_; 
lean_dec(v_a_3359_);
lean_dec(v___f_3354_);
lean_dec_ref(v_inst_3353_);
v___x_3365_ = lean_apply_2(v_toPure_3360_, lean_box(0), v___x_3363_);
v___x_3366_ = lean_apply_4(v_toSeqRight_3352_, lean_box(0), lean_box(0), v___x_3365_, v___f_3361_);
return v___x_3366_;
}
else
{
size_t v___x_3367_; size_t v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
lean_dec(v_toPure_3360_);
v___x_3367_ = ((size_t)0ULL);
v___x_3368_ = lean_usize_of_nat(v___x_3362_);
v___x_3369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3353_, v___f_3354_, v_a_3359_, v___x_3367_, v___x_3368_, v___x_3363_);
v___x_3370_ = lean_apply_4(v_toSeqRight_3352_, lean_box(0), lean_box(0), v___x_3369_, v___f_3361_);
return v___x_3370_;
}
}
else
{
lean_object* v_a_3371_; lean_object* v_toPure_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; uint8_t v___x_3375_; 
lean_dec(v___f_3354_);
lean_dec(v_toPure_3350_);
v_a_3371_ = lean_ctor_get(v_____do__lift_3357_, 1);
lean_inc(v_a_3371_);
lean_dec_ref_known(v_____do__lift_3357_, 2);
v_toPure_3372_ = lean_ctor_get(v_toApplicative_3349_, 1);
lean_inc(v_toPure_3372_);
lean_dec_ref(v_toApplicative_3349_);
v___x_3373_ = lean_array_get_size(v_a_3371_);
v___x_3374_ = lean_box(0);
v___x_3375_ = lean_nat_dec_lt(v___x_3351_, v___x_3373_);
if (v___x_3375_ == 0)
{
lean_object* v___x_3376_; lean_object* v___x_3377_; 
lean_dec(v_a_3371_);
lean_dec(v___f_3356_);
lean_dec_ref(v_inst_3353_);
v___x_3376_ = lean_apply_2(v_toPure_3372_, lean_box(0), v___x_3374_);
v___x_3377_ = lean_apply_4(v_toSeqRight_3352_, lean_box(0), lean_box(0), v___x_3376_, v___f_3355_);
return v___x_3377_;
}
else
{
size_t v___x_3378_; size_t v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
lean_dec(v_toPure_3372_);
v___x_3378_ = ((size_t)0ULL);
v___x_3379_ = lean_usize_of_nat(v___x_3373_);
v___x_3380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3353_, v___f_3356_, v_a_3371_, v___x_3378_, v___x_3379_, v___x_3374_);
v___x_3381_ = lean_apply_4(v_toSeqRight_3352_, lean_box(0), lean_box(0), v___x_3380_, v___f_3355_);
return v___x_3381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg___lam__0___boxed(lean_object* v_toApplicative_3382_, lean_object* v_toPure_3383_, lean_object* v___x_3384_, lean_object* v_toSeqRight_3385_, lean_object* v_inst_3386_, lean_object* v___f_3387_, lean_object* v___f_3388_, lean_object* v___f_3389_, lean_object* v_____do__lift_3390_){
_start:
{
lean_object* v_res_3391_; 
v_res_3391_ = l_Lake_ELogT_replayLog___redArg___lam__0(v_toApplicative_3382_, v_toPure_3383_, v___x_3384_, v_toSeqRight_3385_, v_inst_3386_, v___f_3387_, v___f_3388_, v___f_3389_, v_____do__lift_3390_);
lean_dec(v___x_3384_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg(lean_object* v_inst_3392_, lean_object* v_inst_3393_, lean_object* v_logger_3394_, lean_object* v_inst_3395_, lean_object* v_self_3396_){
_start:
{
lean_object* v_toApplicative_3397_; lean_object* v_toApplicative_3398_; lean_object* v_toBind_3399_; lean_object* v_failure_3400_; lean_object* v_toPure_3401_; lean_object* v_toSeqRight_3402_; lean_object* v___f_3403_; lean_object* v___f_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___f_3409_; lean_object* v___x_3410_; 
v_toApplicative_3397_ = lean_ctor_get(v_inst_3392_, 0);
lean_inc_ref(v_toApplicative_3397_);
v_toApplicative_3398_ = lean_ctor_get(v_inst_3393_, 0);
lean_inc_ref(v_toApplicative_3398_);
v_toBind_3399_ = lean_ctor_get(v_inst_3393_, 1);
lean_inc(v_toBind_3399_);
v_failure_3400_ = lean_ctor_get(v_inst_3392_, 1);
lean_inc(v_failure_3400_);
lean_dec_ref(v_inst_3392_);
v_toPure_3401_ = lean_ctor_get(v_toApplicative_3397_, 1);
lean_inc(v_toPure_3401_);
v_toSeqRight_3402_ = lean_ctor_get(v_toApplicative_3397_, 4);
lean_inc(v_toSeqRight_3402_);
lean_dec_ref(v_toApplicative_3397_);
v___f_3403_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3403_, 0, v_logger_3394_);
v___f_3404_ = lean_alloc_closure((void*)(l_Lake_MonadLog_error___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3404_, 0, v_failure_3400_);
v___x_3405_ = lean_unsigned_to_nat(0u);
v___x_3406_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3407_ = lean_apply_1(v_self_3396_, v___x_3406_);
v___x_3408_ = lean_apply_2(v_inst_3395_, lean_box(0), v___x_3407_);
lean_inc_ref(v___f_3403_);
v___f_3409_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3409_, 0, v_toApplicative_3398_);
lean_closure_set(v___f_3409_, 1, v_toPure_3401_);
lean_closure_set(v___f_3409_, 2, v___x_3405_);
lean_closure_set(v___f_3409_, 3, v_toSeqRight_3402_);
lean_closure_set(v___f_3409_, 4, v_inst_3393_);
lean_closure_set(v___f_3409_, 5, v___f_3403_);
lean_closure_set(v___f_3409_, 6, v___f_3404_);
lean_closure_set(v___f_3409_, 7, v___f_3403_);
v___x_3410_ = lean_apply_4(v_toBind_3399_, lean_box(0), lean_box(0), v___x_3408_, v___f_3409_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog(lean_object* v_n_3411_, lean_object* v_m_3412_, lean_object* v_00_u03b1_3413_, lean_object* v_inst_3414_, lean_object* v_inst_3415_, lean_object* v_logger_3416_, lean_object* v_inst_3417_, lean_object* v_self_3418_){
_start:
{
lean_object* v_toApplicative_3419_; lean_object* v_toApplicative_3420_; lean_object* v_toBind_3421_; lean_object* v_failure_3422_; lean_object* v_toPure_3423_; lean_object* v_toSeqRight_3424_; lean_object* v___f_3425_; lean_object* v___f_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___f_3431_; lean_object* v___x_3432_; 
v_toApplicative_3419_ = lean_ctor_get(v_inst_3414_, 0);
lean_inc_ref(v_toApplicative_3419_);
v_toApplicative_3420_ = lean_ctor_get(v_inst_3415_, 0);
lean_inc_ref(v_toApplicative_3420_);
v_toBind_3421_ = lean_ctor_get(v_inst_3415_, 1);
lean_inc(v_toBind_3421_);
v_failure_3422_ = lean_ctor_get(v_inst_3414_, 1);
lean_inc(v_failure_3422_);
lean_dec_ref(v_inst_3414_);
v_toPure_3423_ = lean_ctor_get(v_toApplicative_3419_, 1);
lean_inc(v_toPure_3423_);
v_toSeqRight_3424_ = lean_ctor_get(v_toApplicative_3419_, 4);
lean_inc(v_toSeqRight_3424_);
lean_dec_ref(v_toApplicative_3419_);
v___f_3425_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3425_, 0, v_logger_3416_);
v___f_3426_ = lean_alloc_closure((void*)(l_Lake_MonadLog_error___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3426_, 0, v_failure_3422_);
v___x_3427_ = lean_unsigned_to_nat(0u);
v___x_3428_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3429_ = lean_apply_1(v_self_3418_, v___x_3428_);
v___x_3430_ = lean_apply_2(v_inst_3417_, lean_box(0), v___x_3429_);
lean_inc_ref(v___f_3425_);
v___f_3431_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3431_, 0, v_toApplicative_3420_);
lean_closure_set(v___f_3431_, 1, v_toPure_3423_);
lean_closure_set(v___f_3431_, 2, v___x_3427_);
lean_closure_set(v___f_3431_, 3, v_toSeqRight_3424_);
lean_closure_set(v___f_3431_, 4, v_inst_3415_);
lean_closure_set(v___f_3431_, 5, v___f_3425_);
lean_closure_set(v___f_3431_, 6, v___f_3426_);
lean_closure_set(v___f_3431_, 7, v___f_3425_);
v___x_3432_ = lean_apply_4(v_toBind_3421_, lean_box(0), lean_box(0), v___x_3430_, v___f_3431_);
return v___x_3432_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___redArg___lam__0(lean_object* v_val_3433_, uint8_t v_outLv_3434_, uint8_t v_val_3435_, lean_object* v_inst_3436_, lean_object* v_e_3437_){
_start:
{
lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3438_ = lean_box(v_outLv_3434_);
v___x_3439_ = lean_box(v_val_3435_);
v___x_3440_ = lean_alloc_closure((void*)(l_Lake_logToStream___boxed), 5, 4);
lean_closure_set(v___x_3440_, 0, v_e_3437_);
lean_closure_set(v___x_3440_, 1, v_val_3433_);
lean_closure_set(v___x_3440_, 2, v___x_3438_);
lean_closure_set(v___x_3440_, 3, v___x_3439_);
v___x_3441_ = lean_apply_2(v_inst_3436_, lean_box(0), v___x_3440_);
return v___x_3441_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___redArg___lam__0___boxed(lean_object* v_val_3442_, lean_object* v_outLv_3443_, lean_object* v_val_3444_, lean_object* v_inst_3445_, lean_object* v_e_3446_){
_start:
{
uint8_t v_outLv_boxed_3447_; uint8_t v_val_44__boxed_3448_; lean_object* v_res_3449_; 
v_outLv_boxed_3447_ = lean_unbox(v_outLv_3443_);
v_val_44__boxed_3448_ = lean_unbox(v_val_3444_);
v_res_3449_ = l_Lake_LogConfig_getLogger___redArg___lam__0(v_val_3442_, v_outLv_boxed_3447_, v_val_44__boxed_3448_, v_inst_3445_, v_e_3446_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___redArg(lean_object* v_inst_3450_, lean_object* v_self_3451_){
_start:
{
uint8_t v_outLv_3453_; uint8_t v_ansiMode_3454_; lean_object* v_out_3455_; lean_object* v___x_3456_; uint8_t v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___f_3460_; 
v_outLv_3453_ = lean_ctor_get_uint8(v_self_3451_, sizeof(void*)*1 + 1);
v_ansiMode_3454_ = lean_ctor_get_uint8(v_self_3451_, sizeof(void*)*1 + 2);
v_out_3455_ = lean_ctor_get(v_self_3451_, 0);
v___x_3456_ = l_Lake_OutStream_get(v_out_3455_);
lean_inc_ref(v___x_3456_);
v___x_3457_ = l_Lake_AnsiMode_isEnabled(v___x_3456_, v_ansiMode_3454_);
v___x_3458_ = lean_box(v_outLv_3453_);
v___x_3459_ = lean_box(v___x_3457_);
v___f_3460_ = lean_alloc_closure((void*)(l_Lake_LogConfig_getLogger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3460_, 0, v___x_3456_);
lean_closure_set(v___f_3460_, 1, v___x_3458_);
lean_closure_set(v___f_3460_, 2, v___x_3459_);
lean_closure_set(v___f_3460_, 3, v_inst_3450_);
return v___f_3460_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___redArg___boxed(lean_object* v_inst_3461_, lean_object* v_self_3462_, lean_object* v_a_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l_Lake_LogConfig_getLogger___redArg(v_inst_3461_, v_self_3462_);
lean_dec_ref(v_self_3462_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger(lean_object* v_m_3465_, lean_object* v_inst_3466_, lean_object* v_self_3467_){
_start:
{
uint8_t v_outLv_3469_; uint8_t v_ansiMode_3470_; lean_object* v_out_3471_; lean_object* v___x_3472_; uint8_t v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___f_3476_; 
v_outLv_3469_ = lean_ctor_get_uint8(v_self_3467_, sizeof(void*)*1 + 1);
v_ansiMode_3470_ = lean_ctor_get_uint8(v_self_3467_, sizeof(void*)*1 + 2);
v_out_3471_ = lean_ctor_get(v_self_3467_, 0);
v___x_3472_ = l_Lake_OutStream_get(v_out_3471_);
lean_inc_ref(v___x_3472_);
v___x_3473_ = l_Lake_AnsiMode_isEnabled(v___x_3472_, v_ansiMode_3470_);
v___x_3474_ = lean_box(v_outLv_3469_);
v___x_3475_ = lean_box(v___x_3473_);
v___f_3476_ = lean_alloc_closure((void*)(l_Lake_LogConfig_getLogger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3476_, 0, v___x_3472_);
lean_closure_set(v___f_3476_, 1, v___x_3474_);
lean_closure_set(v___f_3476_, 2, v___x_3475_);
lean_closure_set(v___f_3476_, 3, v_inst_3466_);
return v___f_3476_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___boxed(lean_object* v_m_3477_, lean_object* v_inst_3478_, lean_object* v_self_3479_, lean_object* v_a_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Lake_LogConfig_getLogger(v_m_3477_, v_inst_3478_, v_self_3479_);
lean_dec_ref(v_self_3479_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_instMonadLiftIO___lam__0(lean_object* v_00_u03b1_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
lean_object* v___x_3486_; 
v___x_3486_ = lean_apply_1(v___y_3483_, lean_box(0));
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; lean_object* v___x_3488_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_a_3487_);
lean_dec_ref_known(v___x_3486_, 1);
v___x_3488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3488_, 0, v_a_3487_);
lean_ctor_set(v___x_3488_, 1, v___y_3484_);
return v___x_3488_;
}
else
{
lean_object* v_a_3489_; lean_object* v___x_3490_; uint8_t v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v_a_3489_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_a_3489_);
lean_dec_ref_known(v___x_3486_, 1);
v___x_3490_ = lean_io_error_to_string(v_a_3489_);
v___x_3491_ = 3;
v___x_3492_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3492_, 0, v___x_3490_);
lean_ctor_set_uint8(v___x_3492_, sizeof(void*)*1, v___x_3491_);
v___x_3493_ = lean_array_get_size(v___y_3484_);
v___x_3494_ = lean_array_push(v___y_3484_, v___x_3492_);
v___x_3495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3493_);
lean_ctor_set(v___x_3495_, 1, v___x_3494_);
return v___x_3495_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_instMonadLiftIO___lam__0___boxed(lean_object* v_00_u03b1_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l_Lake_LogIO_instMonadLiftIO___lam__0(v_00_u03b1_3496_, v___y_3497_, v___y_3498_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg___lam__0(lean_object* v_val_3503_, uint8_t v___y_3504_, uint8_t v_val_3505_, lean_object* v_x_3506_, lean_object* v___y_3507_){
_start:
{
lean_object* v___x_3509_; 
v___x_3509_ = l_Lake_logToStream(v___y_3507_, v_val_3503_, v___y_3504_, v_val_3505_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed(lean_object* v_val_3510_, lean_object* v___y_3511_, lean_object* v_val_3512_, lean_object* v_x_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
uint8_t v___y_740__boxed_3516_; uint8_t v_val_741__boxed_3517_; lean_object* v_res_3518_; 
v___y_740__boxed_3516_ = lean_unbox(v___y_3511_);
v_val_741__boxed_3517_ = lean_unbox(v_val_3512_);
v_res_3518_ = l_Lake_LogIO_toBaseIO___redArg___lam__0(v_val_3510_, v___y_740__boxed_3516_, v_val_741__boxed_3517_, v_x_3513_, v___y_3514_);
lean_dec_ref(v___y_3514_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg(lean_object* v_self_3519_, lean_object* v_cfg_3520_){
_start:
{
lean_object* v___y_3523_; uint8_t v___y_3524_; lean_object* v___x_3526_; lean_object* v___y_3528_; uint8_t v___y_3529_; lean_object* v___y_3530_; uint8_t v___y_3531_; lean_object* v___y_3548_; lean_object* v___y_3549_; uint8_t v___y_3550_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3526_ = l_instMonadBaseIO;
v___x_3552_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3553_ = lean_apply_2(v_self_3519_, v___x_3552_, lean_box(0));
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; lean_object* v_a_3555_; uint8_t v_failLv_3556_; uint8_t v_outLv_3557_; lean_object* v___x_3558_; uint8_t v___x_3559_; uint8_t v___x_3560_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_a_3554_);
v_a_3555_ = lean_ctor_get(v___x_3553_, 1);
lean_inc(v_a_3555_);
lean_dec_ref_known(v___x_3553_, 2);
v_failLv_3556_ = lean_ctor_get_uint8(v_cfg_3520_, sizeof(void*)*1);
v_outLv_3557_ = lean_ctor_get_uint8(v_cfg_3520_, sizeof(void*)*1 + 1);
v___x_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3558_, 0, v_a_3554_);
v___x_3559_ = l_Lake_Log_maxLv(v_a_3555_);
v___x_3560_ = l_Lake_instOrdLogLevel_ord(v_failLv_3556_, v___x_3559_);
if (v___x_3560_ == 2)
{
uint8_t v___x_3561_; 
v___x_3561_ = 0;
v___y_3528_ = v___x_3558_;
v___y_3529_ = v___x_3561_;
v___y_3530_ = v_a_3555_;
v___y_3531_ = v_outLv_3557_;
goto v___jp_3527_;
}
else
{
uint8_t v___x_3562_; 
v___x_3562_ = 1;
v___y_3548_ = v___x_3558_;
v___y_3549_ = v_a_3555_;
v___y_3550_ = v___x_3562_;
goto v___jp_3547_;
}
}
else
{
lean_object* v_a_3563_; lean_object* v___x_3564_; uint8_t v___x_3565_; 
v_a_3563_ = lean_ctor_get(v___x_3553_, 1);
lean_inc(v_a_3563_);
lean_dec_ref_known(v___x_3553_, 2);
v___x_3564_ = lean_box(0);
v___x_3565_ = 1;
v___y_3548_ = v___x_3564_;
v___y_3549_ = v_a_3563_;
v___y_3550_ = v___x_3565_;
goto v___jp_3547_;
}
v___jp_3522_:
{
if (v___y_3524_ == 0)
{
return v___y_3523_;
}
else
{
lean_object* v___x_3525_; 
lean_dec(v___y_3523_);
v___x_3525_ = lean_box(0);
return v___x_3525_;
}
}
v___jp_3527_:
{
uint8_t v_ansiMode_3532_; lean_object* v_out_3533_; lean_object* v___x_3534_; uint8_t v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; uint8_t v___x_3538_; 
v_ansiMode_3532_ = lean_ctor_get_uint8(v_cfg_3520_, sizeof(void*)*1 + 2);
v_out_3533_ = lean_ctor_get(v_cfg_3520_, 0);
v___x_3534_ = l_Lake_OutStream_get(v_out_3533_);
lean_inc_ref(v___x_3534_);
v___x_3535_ = l_Lake_AnsiMode_isEnabled(v___x_3534_, v_ansiMode_3532_);
v___x_3536_ = lean_unsigned_to_nat(0u);
v___x_3537_ = lean_array_get_size(v___y_3530_);
v___x_3538_ = lean_nat_dec_lt(v___x_3536_, v___x_3537_);
if (v___x_3538_ == 0)
{
lean_dec_ref(v___x_3534_);
lean_dec_ref(v___y_3530_);
v___y_3523_ = v___y_3528_;
v___y_3524_ = v___y_3529_;
goto v___jp_3522_;
}
else
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___f_3541_; lean_object* v___x_3542_; size_t v___x_3543_; size_t v___x_3544_; lean_object* v___x_521__overap_3545_; lean_object* v___x_3546_; 
v___x_3539_ = lean_box(v___y_3531_);
v___x_3540_ = lean_box(v___x_3535_);
v___f_3541_ = lean_alloc_closure((void*)(l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_3541_, 0, v___x_3534_);
lean_closure_set(v___f_3541_, 1, v___x_3539_);
lean_closure_set(v___f_3541_, 2, v___x_3540_);
v___x_3542_ = lean_box(0);
v___x_3543_ = ((size_t)0ULL);
v___x_3544_ = lean_usize_of_nat(v___x_3537_);
v___x_521__overap_3545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3526_, v___f_3541_, v___y_3530_, v___x_3543_, v___x_3544_, v___x_3542_);
v___x_3546_ = lean_apply_1(v___x_521__overap_3545_, lean_box(0));
v___y_3523_ = v___y_3528_;
v___y_3524_ = v___y_3529_;
goto v___jp_3522_;
}
}
v___jp_3547_:
{
uint8_t v___x_3551_; 
v___x_3551_ = 0;
v___y_3528_ = v___y_3548_;
v___y_3529_ = v___y_3550_;
v___y_3530_ = v___y_3549_;
v___y_3531_ = v___x_3551_;
goto v___jp_3527_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg___boxed(lean_object* v_self_3566_, lean_object* v_cfg_3567_, lean_object* v_a_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l_Lake_LogIO_toBaseIO___redArg(v_self_3566_, v_cfg_3567_);
lean_dec_ref(v_cfg_3567_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO(lean_object* v_00_u03b1_3570_, lean_object* v_self_3571_, lean_object* v_cfg_3572_){
_start:
{
lean_object* v___y_3575_; uint8_t v___y_3576_; lean_object* v___x_3578_; lean_object* v___y_3580_; uint8_t v___y_3581_; lean_object* v___y_3582_; uint8_t v___y_3583_; lean_object* v___y_3600_; lean_object* v___y_3601_; uint8_t v___y_3602_; lean_object* v___x_3604_; lean_object* v___x_3605_; 
v___x_3578_ = l_instMonadBaseIO;
v___x_3604_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3605_ = lean_apply_2(v_self_3571_, v___x_3604_, lean_box(0));
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v_a_3606_; lean_object* v_a_3607_; uint8_t v_failLv_3608_; uint8_t v_outLv_3609_; lean_object* v___x_3610_; uint8_t v___x_3611_; uint8_t v___x_3612_; 
v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
lean_inc(v_a_3606_);
v_a_3607_ = lean_ctor_get(v___x_3605_, 1);
lean_inc(v_a_3607_);
lean_dec_ref_known(v___x_3605_, 2);
v_failLv_3608_ = lean_ctor_get_uint8(v_cfg_3572_, sizeof(void*)*1);
v_outLv_3609_ = lean_ctor_get_uint8(v_cfg_3572_, sizeof(void*)*1 + 1);
v___x_3610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3610_, 0, v_a_3606_);
v___x_3611_ = l_Lake_Log_maxLv(v_a_3607_);
v___x_3612_ = l_Lake_instOrdLogLevel_ord(v_failLv_3608_, v___x_3611_);
if (v___x_3612_ == 2)
{
uint8_t v___x_3613_; 
v___x_3613_ = 0;
v___y_3580_ = v___x_3610_;
v___y_3581_ = v___x_3613_;
v___y_3582_ = v_a_3607_;
v___y_3583_ = v_outLv_3609_;
goto v___jp_3579_;
}
else
{
uint8_t v___x_3614_; 
v___x_3614_ = 1;
v___y_3600_ = v___x_3610_;
v___y_3601_ = v_a_3607_;
v___y_3602_ = v___x_3614_;
goto v___jp_3599_;
}
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3616_; uint8_t v___x_3617_; 
v_a_3615_ = lean_ctor_get(v___x_3605_, 1);
lean_inc(v_a_3615_);
lean_dec_ref_known(v___x_3605_, 2);
v___x_3616_ = lean_box(0);
v___x_3617_ = 1;
v___y_3600_ = v___x_3616_;
v___y_3601_ = v_a_3615_;
v___y_3602_ = v___x_3617_;
goto v___jp_3599_;
}
v___jp_3574_:
{
if (v___y_3576_ == 0)
{
return v___y_3575_;
}
else
{
lean_object* v___x_3577_; 
lean_dec(v___y_3575_);
v___x_3577_ = lean_box(0);
return v___x_3577_;
}
}
v___jp_3579_:
{
uint8_t v_ansiMode_3584_; lean_object* v_out_3585_; lean_object* v___x_3586_; uint8_t v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; uint8_t v___x_3590_; 
v_ansiMode_3584_ = lean_ctor_get_uint8(v_cfg_3572_, sizeof(void*)*1 + 2);
v_out_3585_ = lean_ctor_get(v_cfg_3572_, 0);
v___x_3586_ = l_Lake_OutStream_get(v_out_3585_);
lean_inc_ref(v___x_3586_);
v___x_3587_ = l_Lake_AnsiMode_isEnabled(v___x_3586_, v_ansiMode_3584_);
v___x_3588_ = lean_unsigned_to_nat(0u);
v___x_3589_ = lean_array_get_size(v___y_3582_);
v___x_3590_ = lean_nat_dec_lt(v___x_3588_, v___x_3589_);
if (v___x_3590_ == 0)
{
lean_dec_ref(v___x_3586_);
lean_dec_ref(v___y_3582_);
v___y_3575_ = v___y_3580_;
v___y_3576_ = v___y_3581_;
goto v___jp_3574_;
}
else
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___f_3593_; lean_object* v___x_3594_; size_t v___x_3595_; size_t v___x_3596_; lean_object* v___x_665__overap_3597_; lean_object* v___x_3598_; 
v___x_3591_ = lean_box(v___y_3583_);
v___x_3592_ = lean_box(v___x_3587_);
v___f_3593_ = lean_alloc_closure((void*)(l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_3593_, 0, v___x_3586_);
lean_closure_set(v___f_3593_, 1, v___x_3591_);
lean_closure_set(v___f_3593_, 2, v___x_3592_);
v___x_3594_ = lean_box(0);
v___x_3595_ = ((size_t)0ULL);
v___x_3596_ = lean_usize_of_nat(v___x_3589_);
v___x_665__overap_3597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3578_, v___f_3593_, v___y_3582_, v___x_3595_, v___x_3596_, v___x_3594_);
v___x_3598_ = lean_apply_1(v___x_665__overap_3597_, lean_box(0));
v___y_3575_ = v___y_3580_;
v___y_3576_ = v___y_3581_;
goto v___jp_3574_;
}
}
v___jp_3599_:
{
uint8_t v___x_3603_; 
v___x_3603_ = 0;
v___y_3580_ = v___y_3600_;
v___y_3581_ = v___y_3602_;
v___y_3582_ = v___y_3601_;
v___y_3583_ = v___x_3603_;
goto v___jp_3579_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___boxed(lean_object* v_00_u03b1_3618_, lean_object* v_self_3619_, lean_object* v_cfg_3620_, lean_object* v_a_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Lake_LogIO_toBaseIO(v_00_u03b1_3618_, v_self_3619_, v_cfg_3620_);
lean_dec_ref(v_cfg_3620_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_captureLog___redArg(lean_object* v_inst_3623_, lean_object* v_self_3624_, lean_object* v_log_3625_){
_start:
{
lean_object* v_map_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; 
v_map_3626_ = lean_ctor_get(v_inst_3623_, 0);
lean_inc(v_map_3626_);
lean_dec_ref(v_inst_3623_);
v___x_3627_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3628_ = lean_apply_1(v_self_3624_, v_log_3625_);
v___x_3629_ = lean_apply_4(v_map_3626_, lean_box(0), lean_box(0), v___x_3627_, v___x_3628_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_captureLog(lean_object* v_m_3630_, lean_object* v_00_u03b1_3631_, lean_object* v_inst_3632_, lean_object* v_self_3633_, lean_object* v_log_3634_){
_start:
{
lean_object* v_map_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v_map_3635_ = lean_ctor_get(v_inst_3632_, 0);
lean_inc(v_map_3635_);
lean_dec_ref(v_inst_3632_);
v___x_3636_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3637_ = lean_apply_1(v_self_3633_, v_log_3634_);
v___x_3638_ = lean_apply_4(v_map_3635_, lean_box(0), lean_box(0), v___x_3636_, v___x_3637_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadError___lam__0(lean_object* v_00_u03b1_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
uint8_t v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3643_ = 3;
v___x_3644_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3644_, 0, v___y_3640_);
lean_ctor_set_uint8(v___x_3644_, sizeof(void*)*1, v___x_3643_);
lean_inc_ref(v___y_3641_);
v___x_3645_ = lean_apply_2(v___y_3641_, v___x_3644_, lean_box(0));
v___x_3646_ = lean_box(0);
v___x_3647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3646_);
return v___x_3647_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadError___lam__0___boxed(lean_object* v_00_u03b1_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
lean_object* v_res_3652_; 
v_res_3652_ = l_Lake_LoggerIO_instMonadError___lam__0(v_00_u03b1_3648_, v___y_3649_, v___y_3650_);
lean_dec_ref(v___y_3650_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftIO___lam__0(lean_object* v_00_u03b1_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_){
_start:
{
lean_object* v___x_3659_; 
v___x_3659_ = lean_apply_1(v___y_3656_, lean_box(0));
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3667_; 
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3662_ = v___x_3659_;
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3659_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3665_; 
if (v_isShared_3663_ == 0)
{
v___x_3665_ = v___x_3662_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3660_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
else
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3680_; 
v_a_3668_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3670_ = v___x_3659_;
v_isShared_3671_ = v_isSharedCheck_3680_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3659_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3680_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3672_; uint8_t v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3678_; 
v___x_3672_ = lean_io_error_to_string(v_a_3668_);
v___x_3673_ = 3;
v___x_3674_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3674_, 0, v___x_3672_);
lean_ctor_set_uint8(v___x_3674_, sizeof(void*)*1, v___x_3673_);
lean_inc_ref(v___y_3657_);
v___x_3675_ = lean_apply_2(v___y_3657_, v___x_3674_, lean_box(0));
v___x_3676_ = lean_box(0);
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 0, v___x_3676_);
v___x_3678_ = v___x_3670_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3676_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftIO___lam__0___boxed(lean_object* v_00_u03b1_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_){
_start:
{
lean_object* v_res_3685_; 
v_res_3685_ = l_Lake_LoggerIO_instMonadLiftIO___lam__0(v_00_u03b1_3681_, v___y_3682_, v___y_3683_);
lean_dec_ref(v___y_3683_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__0(lean_object* v_x_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; 
lean_inc_ref(v___y_3690_);
v___x_3692_ = lean_apply_2(v___y_3690_, v___y_3689_, lean_box(0));
v___x_3693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3692_);
return v___x_3693_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__0___boxed(lean_object* v_x_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_){
_start:
{
lean_object* v_res_3698_; 
v_res_3698_ = l_Lake_LoggerIO_instMonadLiftLogIO___lam__0(v_x_3694_, v___y_3695_, v___y_3696_);
lean_dec_ref(v___y_3696_);
return v_res_3698_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__2(lean_object* v___x_3699_, lean_object* v___f_3700_, lean_object* v___f_3701_, lean_object* v_00_u03b1_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3706_ = lean_unsigned_to_nat(0u);
v___x_3707_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3708_ = lean_apply_2(v___y_3703_, v___x_3707_, lean_box(0));
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_a_3709_; lean_object* v_a_3710_; lean_object* v___x_3711_; uint8_t v___x_3712_; 
lean_dec_ref(v___f_3701_);
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
lean_inc(v_a_3709_);
v_a_3710_ = lean_ctor_get(v___x_3708_, 1);
lean_inc(v_a_3710_);
lean_dec_ref_known(v___x_3708_, 2);
v___x_3711_ = lean_array_get_size(v_a_3710_);
v___x_3712_ = lean_nat_dec_lt(v___x_3706_, v___x_3711_);
if (v___x_3712_ == 0)
{
lean_object* v___x_3713_; 
lean_dec(v_a_3710_);
lean_dec_ref(v___f_3700_);
lean_dec_ref(v___x_3699_);
v___x_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3713_, 0, v_a_3709_);
return v___x_3713_;
}
else
{
lean_object* v___x_3714_; size_t v___x_3715_; size_t v___x_3716_; lean_object* v___x_1294__overap_3717_; lean_object* v___x_3718_; 
v___x_3714_ = lean_box(0);
v___x_3715_ = ((size_t)0ULL);
v___x_3716_ = lean_usize_of_nat(v___x_3711_);
v___x_1294__overap_3717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3699_, v___f_3700_, v_a_3710_, v___x_3715_, v___x_3716_, v___x_3714_);
lean_inc_ref(v___y_3704_);
v___x_3718_ = lean_apply_2(v___x_1294__overap_3717_, v___y_3704_, lean_box(0));
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3725_; 
v_isSharedCheck_3725_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3725_ == 0)
{
lean_object* v_unused_3726_; 
v_unused_3726_ = lean_ctor_get(v___x_3718_, 0);
lean_dec(v_unused_3726_);
v___x_3720_ = v___x_3718_;
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
else
{
lean_dec(v___x_3718_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___x_3723_; 
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 0, v_a_3709_);
v___x_3723_ = v___x_3720_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_a_3709_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
}
else
{
lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3734_; 
lean_dec(v_a_3709_);
v_a_3727_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3729_ = v___x_3718_;
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_a_3727_);
lean_dec(v___x_3718_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3732_; 
if (v_isShared_3730_ == 0)
{
v___x_3732_ = v___x_3729_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_a_3727_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
}
}
else
{
lean_object* v_a_3735_; lean_object* v___x_3736_; uint8_t v___x_3737_; 
lean_dec_ref(v___f_3700_);
v_a_3735_ = lean_ctor_get(v___x_3708_, 1);
lean_inc(v_a_3735_);
lean_dec_ref_known(v___x_3708_, 2);
v___x_3736_ = lean_array_get_size(v_a_3735_);
v___x_3737_ = lean_nat_dec_lt(v___x_3706_, v___x_3736_);
if (v___x_3737_ == 0)
{
lean_object* v___x_3738_; lean_object* v___x_3739_; 
lean_dec(v_a_3735_);
lean_dec_ref(v___f_3701_);
lean_dec_ref(v___x_3699_);
v___x_3738_ = lean_box(0);
v___x_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3738_);
return v___x_3739_;
}
else
{
lean_object* v___x_3740_; size_t v___x_3741_; size_t v___x_3742_; lean_object* v___x_1310__overap_3743_; lean_object* v___x_3744_; 
v___x_3740_ = lean_box(0);
v___x_3741_ = ((size_t)0ULL);
v___x_3742_ = lean_usize_of_nat(v___x_3736_);
v___x_1310__overap_3743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3699_, v___f_3701_, v_a_3735_, v___x_3741_, v___x_3742_, v___x_3740_);
lean_inc_ref(v___y_3704_);
v___x_3744_ = lean_apply_2(v___x_1310__overap_3743_, v___y_3704_, lean_box(0));
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3751_; 
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3751_ == 0)
{
lean_object* v_unused_3752_; 
v_unused_3752_ = lean_ctor_get(v___x_3744_, 0);
lean_dec(v_unused_3752_);
v___x_3746_ = v___x_3744_;
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
else
{
lean_dec(v___x_3744_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v___x_3749_; 
if (v_isShared_3747_ == 0)
{
lean_ctor_set_tag(v___x_3746_, 1);
lean_ctor_set(v___x_3746_, 0, v___x_3740_);
v___x_3749_ = v___x_3746_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3740_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
else
{
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
v_a_3753_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3755_ = v___x_3744_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3744_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3758_; 
if (v_isShared_3756_ == 0)
{
v___x_3758_ = v___x_3755_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_a_3753_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__2___boxed(lean_object* v___x_3761_, lean_object* v___f_3762_, lean_object* v___f_3763_, lean_object* v_00_u03b1_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l_Lake_LoggerIO_instMonadLiftLogIO___lam__2(v___x_3761_, v___f_3762_, v___f_3763_, v_00_u03b1_3764_, v___y_3765_, v___y_3766_);
lean_dec_ref(v___y_3766_);
return v_res_3768_;
}
}
static lean_object* _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__1(void){
_start:
{
lean_object* v___x_3770_; 
v___x_3770_ = l_instMonadEIO___redArg();
return v___x_3770_;
}
}
static lean_object* _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__2(void){
_start:
{
lean_object* v___x_3771_; lean_object* v___x_3772_; 
v___x_3771_ = lean_obj_once(&l_Lake_LoggerIO_instMonadLiftLogIO___closed__1, &l_Lake_LoggerIO_instMonadLiftLogIO___closed__1_once, _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__1);
v___x_3772_ = l_ReaderT_instMonad___redArg(v___x_3771_);
return v___x_3772_;
}
}
static lean_object* _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__3(void){
_start:
{
lean_object* v___f_3773_; lean_object* v___x_3774_; lean_object* v___f_3775_; 
v___f_3773_ = ((lean_object*)(l_Lake_LoggerIO_instMonadLiftLogIO___closed__0));
v___x_3774_ = lean_obj_once(&l_Lake_LoggerIO_instMonadLiftLogIO___closed__2, &l_Lake_LoggerIO_instMonadLiftLogIO___closed__2_once, _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__2);
v___f_3775_ = lean_alloc_closure((void*)(l_Lake_LoggerIO_instMonadLiftLogIO___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3775_, 0, v___x_3774_);
lean_closure_set(v___f_3775_, 1, v___f_3773_);
lean_closure_set(v___f_3775_, 2, v___f_3773_);
return v___f_3775_;
}
}
static lean_object* _init_l_Lake_LoggerIO_instMonadLiftLogIO(void){
_start:
{
lean_object* v___f_3776_; 
v___f_3776_ = lean_obj_once(&l_Lake_LoggerIO_instMonadLiftLogIO___closed__3, &l_Lake_LoggerIO_instMonadLiftLogIO___closed__3_once, _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__3);
return v___f_3776_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg___lam__0(lean_object* v_val_3777_, uint8_t v_outLv_3778_, uint8_t v_val_3779_, lean_object* v_e_3780_){
_start:
{
lean_object* v___x_3782_; 
v___x_3782_ = l_Lake_logToStream(v_e_3780_, v_val_3777_, v_outLv_3778_, v_val_3779_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg___lam__0___boxed(lean_object* v_val_3783_, lean_object* v_outLv_3784_, lean_object* v_val_3785_, lean_object* v_e_3786_, lean_object* v___y_3787_){
_start:
{
uint8_t v_outLv_boxed_3788_; uint8_t v_val_178__boxed_3789_; lean_object* v_res_3790_; 
v_outLv_boxed_3788_ = lean_unbox(v_outLv_3784_);
v_val_178__boxed_3789_ = lean_unbox(v_val_3785_);
v_res_3790_ = l_Lake_LoggerIO_toBaseIO___redArg___lam__0(v_val_3783_, v_outLv_boxed_3788_, v_val_178__boxed_3789_, v_e_3786_);
lean_dec_ref(v_e_3786_);
return v_res_3790_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg(lean_object* v_self_3791_, lean_object* v_cfg_3792_){
_start:
{
uint8_t v_outLv_3794_; uint8_t v_ansiMode_3795_; lean_object* v_out_3796_; lean_object* v___x_3797_; uint8_t v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___f_3801_; lean_object* v___x_3802_; 
v_outLv_3794_ = lean_ctor_get_uint8(v_cfg_3792_, sizeof(void*)*1 + 1);
v_ansiMode_3795_ = lean_ctor_get_uint8(v_cfg_3792_, sizeof(void*)*1 + 2);
v_out_3796_ = lean_ctor_get(v_cfg_3792_, 0);
v___x_3797_ = l_Lake_OutStream_get(v_out_3796_);
lean_inc_ref(v___x_3797_);
v___x_3798_ = l_Lake_AnsiMode_isEnabled(v___x_3797_, v_ansiMode_3795_);
v___x_3799_ = lean_box(v_outLv_3794_);
v___x_3800_ = lean_box(v___x_3798_);
v___f_3801_ = lean_alloc_closure((void*)(l_Lake_LoggerIO_toBaseIO___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3801_, 0, v___x_3797_);
lean_closure_set(v___f_3801_, 1, v___x_3799_);
lean_closure_set(v___f_3801_, 2, v___x_3800_);
v___x_3802_ = lean_apply_2(v_self_3791_, v___f_3801_, lean_box(0));
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3810_; 
v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3805_ = v___x_3802_;
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3802_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3808_; 
if (v_isShared_3806_ == 0)
{
lean_ctor_set_tag(v___x_3805_, 1);
v___x_3808_ = v___x_3805_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_a_3803_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
else
{
lean_object* v___x_3811_; 
lean_dec_ref_known(v___x_3802_, 1);
v___x_3811_ = lean_box(0);
return v___x_3811_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg___boxed(lean_object* v_self_3812_, lean_object* v_cfg_3813_, lean_object* v_a_3814_){
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l_Lake_LoggerIO_toBaseIO___redArg(v_self_3812_, v_cfg_3813_);
lean_dec_ref(v_cfg_3813_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO(lean_object* v_00_u03b1_3816_, lean_object* v_self_3817_, lean_object* v_cfg_3818_){
_start:
{
uint8_t v_outLv_3820_; uint8_t v_ansiMode_3821_; lean_object* v_out_3822_; lean_object* v___x_3823_; uint8_t v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___f_3827_; lean_object* v___x_3828_; 
v_outLv_3820_ = lean_ctor_get_uint8(v_cfg_3818_, sizeof(void*)*1 + 1);
v_ansiMode_3821_ = lean_ctor_get_uint8(v_cfg_3818_, sizeof(void*)*1 + 2);
v_out_3822_ = lean_ctor_get(v_cfg_3818_, 0);
v___x_3823_ = l_Lake_OutStream_get(v_out_3822_);
lean_inc_ref(v___x_3823_);
v___x_3824_ = l_Lake_AnsiMode_isEnabled(v___x_3823_, v_ansiMode_3821_);
v___x_3825_ = lean_box(v_outLv_3820_);
v___x_3826_ = lean_box(v___x_3824_);
v___f_3827_ = lean_alloc_closure((void*)(l_Lake_LoggerIO_toBaseIO___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3827_, 0, v___x_3823_);
lean_closure_set(v___f_3827_, 1, v___x_3825_);
lean_closure_set(v___f_3827_, 2, v___x_3826_);
v___x_3828_ = lean_apply_2(v_self_3817_, v___f_3827_, lean_box(0));
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3836_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3831_ = v___x_3828_;
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___x_3828_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3834_; 
if (v_isShared_3832_ == 0)
{
lean_ctor_set_tag(v___x_3831_, 1);
v___x_3834_ = v___x_3831_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_a_3829_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
else
{
lean_object* v___x_3837_; 
lean_dec_ref_known(v___x_3828_, 1);
v___x_3837_ = lean_box(0);
return v___x_3837_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___boxed(lean_object* v_00_u03b1_3838_, lean_object* v_self_3839_, lean_object* v_cfg_3840_, lean_object* v_a_3841_){
_start:
{
lean_object* v_res_3842_; 
v_res_3842_ = l_Lake_LoggerIO_toBaseIO(v_00_u03b1_3838_, v_self_3839_, v_cfg_3840_);
lean_dec_ref(v_cfg_3840_);
return v_res_3842_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg___lam__0(lean_object* v_val_3843_, lean_object* v_e_3844_){
_start:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3846_ = lean_st_ref_take(v_val_3843_);
v___x_3847_ = lean_array_push(v___x_3846_, v_e_3844_);
v___x_3848_ = lean_st_ref_put(v_val_3843_, v___x_3847_);
return v___x_3848_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg___lam__0___boxed(lean_object* v_val_3849_, lean_object* v_e_3850_, lean_object* v___y_3851_){
_start:
{
lean_object* v_res_3852_; 
v_res_3852_ = l_Lake_LoggerIO_captureLog___redArg___lam__0(v_val_3849_, v_e_3850_);
lean_dec(v_val_3849_);
return v_res_3852_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg(lean_object* v_self_3853_){
_start:
{
lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v_val_3862_; lean_object* v___f_3873_; lean_object* v___x_3874_; 
v___x_3859_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3860_ = lean_st_mk_ref(v___x_3859_);
lean_inc(v___x_3860_);
v___f_3873_ = lean_alloc_closure((void*)(l_Lake_LoggerIO_captureLog___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3873_, 0, v___x_3860_);
v___x_3874_ = lean_apply_2(v_self_3853_, v___f_3873_, lean_box(0));
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3882_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3882_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3877_ = v___x_3874_;
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___x_3874_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3880_; 
if (v_isShared_3878_ == 0)
{
lean_ctor_set_tag(v___x_3877_, 1);
v___x_3880_ = v___x_3877_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_a_3875_);
v___x_3880_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
v_val_3862_ = v___x_3880_;
goto v___jp_3861_;
}
}
}
else
{
lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3890_; 
v_a_3883_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3885_ = v___x_3874_;
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v___x_3874_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3888_; 
if (v_isShared_3886_ == 0)
{
lean_ctor_set_tag(v___x_3885_, 0);
v___x_3888_ = v___x_3885_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_a_3883_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
v_val_3862_ = v___x_3888_;
goto v___jp_3861_;
}
}
}
v___jp_3855_:
{
lean_object* v___x_3858_; 
v___x_3858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3858_, 0, v___y_3857_);
lean_ctor_set(v___x_3858_, 1, v___y_3856_);
return v___x_3858_;
}
v___jp_3861_:
{
lean_object* v___x_3863_; 
v___x_3863_ = lean_st_ref_get(v___x_3860_);
lean_dec(v___x_3860_);
if (lean_obj_tag(v_val_3862_) == 0)
{
lean_object* v___x_3864_; 
lean_dec_ref_known(v_val_3862_, 1);
v___x_3864_ = lean_box(0);
v___y_3856_ = v___x_3863_;
v___y_3857_ = v___x_3864_;
goto v___jp_3855_;
}
else
{
lean_object* v_a_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3872_; 
v_a_3865_ = lean_ctor_get(v_val_3862_, 0);
v_isSharedCheck_3872_ = !lean_is_exclusive(v_val_3862_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3867_ = v_val_3862_;
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_a_3865_);
lean_dec(v_val_3862_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3870_; 
if (v_isShared_3868_ == 0)
{
v___x_3870_ = v___x_3867_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_a_3865_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
v___y_3856_ = v___x_3863_;
v___y_3857_ = v___x_3870_;
goto v___jp_3855_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg___boxed(lean_object* v_self_3891_, lean_object* v_a_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l_Lake_LoggerIO_captureLog___redArg(v_self_3891_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog(lean_object* v_00_u03b1_3894_, lean_object* v_self_3895_){
_start:
{
lean_object* v___x_3897_; 
v___x_3897_ = l_Lake_LoggerIO_captureLog___redArg(v_self_3895_);
return v___x_3897_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___boxed(lean_object* v_00_u03b1_3898_, lean_object* v_self_3899_, lean_object* v_a_3900_){
_start:
{
lean_object* v_res_3901_; 
v_res_3901_ = l_Lake_LoggerIO_captureLog(v_00_u03b1_3898_, v_self_3899_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f___redArg(lean_object* v_self_3902_){
_start:
{
lean_object* v___x_3904_; 
v___x_3904_ = l_Lake_LoggerIO_captureLog___redArg(v_self_3902_);
return v___x_3904_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f___redArg___boxed(lean_object* v_self_3905_, lean_object* v_a_3906_){
_start:
{
lean_object* v_res_3907_; 
v_res_3907_ = l_Lake_LoggerIO_run_x3f___redArg(v_self_3905_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f(lean_object* v_00_u03b1_3908_, lean_object* v_self_3909_){
_start:
{
lean_object* v___x_3911_; 
v___x_3911_ = l_Lake_LoggerIO_captureLog___redArg(v_self_3909_);
return v___x_3911_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f___boxed(lean_object* v_00_u03b1_3912_, lean_object* v_self_3913_, lean_object* v_a_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_Lake_LoggerIO_run_x3f(v_00_u03b1_3912_, v_self_3913_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27___redArg(lean_object* v_self_3916_, lean_object* v_logger_3917_){
_start:
{
lean_object* v___x_3919_; 
v___x_3919_ = lean_apply_2(v_self_3916_, v_logger_3917_, lean_box(0));
if (lean_obj_tag(v___x_3919_) == 0)
{
lean_object* v_a_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3927_; 
v_a_3920_ = lean_ctor_get(v___x_3919_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3919_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3922_ = v___x_3919_;
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_a_3920_);
lean_dec(v___x_3919_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3925_; 
if (v_isShared_3923_ == 0)
{
lean_ctor_set_tag(v___x_3922_, 1);
v___x_3925_ = v___x_3922_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3920_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
else
{
lean_object* v___x_3928_; 
lean_dec_ref_known(v___x_3919_, 1);
v___x_3928_ = lean_box(0);
return v___x_3928_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27___redArg___boxed(lean_object* v_self_3929_, lean_object* v_logger_3930_, lean_object* v_a_3931_){
_start:
{
lean_object* v_res_3932_; 
v_res_3932_ = l_Lake_LoggerIO_run_x3f_x27___redArg(v_self_3929_, v_logger_3930_);
return v_res_3932_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27(lean_object* v_00_u03b1_3933_, lean_object* v_self_3934_, lean_object* v_logger_3935_){
_start:
{
lean_object* v___x_3937_; 
v___x_3937_ = lean_apply_2(v_self_3934_, v_logger_3935_, lean_box(0));
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v_a_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3945_; 
v_a_3938_ = lean_ctor_get(v___x_3937_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3940_ = v___x_3937_;
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_a_3938_);
lean_dec(v___x_3937_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3943_; 
if (v_isShared_3941_ == 0)
{
lean_ctor_set_tag(v___x_3940_, 1);
v___x_3943_ = v___x_3940_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_a_3938_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
}
else
{
lean_object* v___x_3946_; 
lean_dec_ref_known(v___x_3937_, 1);
v___x_3946_ = lean_box(0);
return v___x_3946_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27___boxed(lean_object* v_00_u03b1_3947_, lean_object* v_self_3948_, lean_object* v_logger_3949_, lean_object* v_a_3950_){
_start:
{
lean_object* v_res_3951_; 
v_res_3951_ = l_Lake_LoggerIO_run_x3f_x27(v_00_u03b1_3947_, v_self_3948_, v_logger_3949_);
return v_res_3951_;
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
