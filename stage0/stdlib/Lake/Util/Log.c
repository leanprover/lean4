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
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* v_a_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_a_868_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_857_, 1);
v___x_869_ = ((lean_object*)(l_Lake_instToJsonLogEntry_toJson___closed__1));
v___x_870_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1(v_json_855_, v___x_869_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_880_; 
lean_dec(v_a_868_);
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_880_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_880_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_880_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_875_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__14, &l_Lake_instFromJsonLogEntry_fromJson___closed__14_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__14);
v___x_876_ = lean_string_append(v___x_875_, v_a_871_);
lean_dec(v_a_871_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_876_);
v___x_878_ = v___x_873_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_890_; 
v_a_881_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_890_ == 0)
{
v___x_883_ = v___x_870_;
v_isShared_884_ = v_isSharedCheck_890_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_870_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_890_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; uint8_t v___x_886_; lean_object* v___x_888_; 
v___x_885_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_885_, 0, v_a_881_);
v___x_886_ = lean_unbox(v_a_868_);
lean_dec(v_a_868_);
lean_ctor_set_uint8(v___x_885_, sizeof(void*)*1, v___x_886_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_885_);
v___x_888_ = v___x_883_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_885_);
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
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_toString(lean_object* v_self_895_, uint8_t v_useAnsi_896_){
_start:
{
if (v_useAnsi_896_ == 0)
{
uint8_t v_level_897_; lean_object* v_message_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_level_897_ = lean_ctor_get_uint8(v_self_895_, sizeof(void*)*1);
v_message_898_ = lean_ctor_get(v_self_895_, 0);
v___x_899_ = l_Lake_LogLevel_toString(v_level_897_);
v___x_900_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__9));
v___x_901_ = lean_string_append(v___x_899_, v___x_900_);
v___x_902_ = lean_string_append(v___x_901_, v_message_898_);
return v___x_902_;
}
else
{
uint8_t v_level_903_; lean_object* v_message_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v_pre_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_level_903_ = lean_ctor_get_uint8(v_self_895_, sizeof(void*)*1);
v_message_904_ = lean_ctor_get(v_self_895_, 0);
v___x_905_ = l_Lake_LogLevel_ansiColor(v_level_903_);
v___x_906_ = l_Lake_LogLevel_toString(v_level_903_);
v___x_907_ = ((lean_object*)(l_Lake_LogEntry_toString___closed__0));
v___x_908_ = lean_string_append(v___x_906_, v___x_907_);
v_pre_909_ = l_Lake_Ansi_chalk(v___x_905_, v___x_908_);
lean_dec_ref(v___x_908_);
lean_dec_ref(v___x_905_);
v___x_910_ = ((lean_object*)(l_Lake_LogEntry_toString___closed__1));
v___x_911_ = lean_string_append(v_pre_909_, v___x_910_);
v___x_912_ = lean_string_append(v___x_911_, v_message_904_);
return v___x_912_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_toString___boxed(lean_object* v_self_913_, lean_object* v_useAnsi_914_){
_start:
{
uint8_t v_useAnsi_boxed_915_; lean_object* v_res_916_; 
v_useAnsi_boxed_915_ = lean_unbox(v_useAnsi_914_);
v_res_916_ = l_Lake_LogEntry_toString(v_self_913_, v_useAnsi_boxed_915_);
lean_dec_ref(v_self_913_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToStringLogEntry___lam__0(lean_object* v_self_917_){
_start:
{
uint8_t v___x_918_; lean_object* v___x_919_; 
v___x_918_ = 0;
v___x_919_ = l_Lake_LogEntry_toString(v_self_917_, v___x_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToStringLogEntry___lam__0___boxed(lean_object* v_self_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lake_instToStringLogEntry___lam__0(v_self_920_);
lean_dec_ref(v_self_920_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_trace(lean_object* v_message_924_){
_start:
{
uint8_t v___x_925_; lean_object* v___x_926_; 
v___x_925_ = 0;
v___x_926_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_926_, 0, v_message_924_);
lean_ctor_set_uint8(v___x_926_, sizeof(void*)*1, v___x_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_info(lean_object* v_message_927_){
_start:
{
uint8_t v___x_928_; lean_object* v___x_929_; 
v___x_928_ = 1;
v___x_929_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_929_, 0, v_message_927_);
lean_ctor_set_uint8(v___x_929_, sizeof(void*)*1, v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_warning(lean_object* v_message_930_){
_start:
{
uint8_t v___x_931_; lean_object* v___x_932_; 
v___x_931_ = 2;
v___x_932_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_932_, 0, v_message_930_);
lean_ctor_set_uint8(v___x_932_, sizeof(void*)*1, v___x_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_error(lean_object* v_message_933_){
_start:
{
uint8_t v___x_934_; lean_object* v___x_935_; 
v___x_934_ = 3;
v___x_935_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_935_, 0, v_message_933_);
lean_ctor_set_uint8(v___x_935_, sizeof(void*)*1, v___x_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_ofSerialMessage(lean_object* v_msg_937_){
_start:
{
lean_object* v_toBaseMessage_938_; lean_object* v_fileName_939_; lean_object* v_pos_940_; uint8_t v_severity_941_; lean_object* v_caption_942_; lean_object* v_data_943_; lean_object* v___y_945_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v_startInclusive_954_; lean_object* v_endExclusive_955_; lean_object* v___x_956_; uint8_t v___x_957_; 
v_toBaseMessage_938_ = lean_ctor_get(v_msg_937_, 0);
lean_inc_ref(v_toBaseMessage_938_);
lean_dec_ref(v_msg_937_);
v_fileName_939_ = lean_ctor_get(v_toBaseMessage_938_, 0);
lean_inc_ref(v_fileName_939_);
v_pos_940_ = lean_ctor_get(v_toBaseMessage_938_, 1);
lean_inc_ref(v_pos_940_);
v_severity_941_ = lean_ctor_get_uint8(v_toBaseMessage_938_, sizeof(void*)*5 + 1);
v_caption_942_ = lean_ctor_get(v_toBaseMessage_938_, 3);
lean_inc_ref(v_caption_942_);
v_data_943_ = lean_ctor_get(v_toBaseMessage_938_, 4);
lean_inc(v_data_943_);
lean_dec_ref(v_toBaseMessage_938_);
v___x_950_ = lean_unsigned_to_nat(0u);
v___x_951_ = lean_string_utf8_byte_size(v_caption_942_);
v___x_952_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_952_, 0, v_caption_942_);
lean_ctor_set(v___x_952_, 1, v___x_950_);
lean_ctor_set(v___x_952_, 2, v___x_951_);
v___x_953_ = l_String_Slice_trimAscii(v___x_952_);
v_startInclusive_954_ = lean_ctor_get(v___x_953_, 1);
v_endExclusive_955_ = lean_ctor_get(v___x_953_, 2);
v___x_956_ = lean_nat_sub(v_endExclusive_955_, v_startInclusive_954_);
v___x_957_ = lean_nat_dec_eq(v___x_956_, v___x_950_);
lean_dec(v___x_956_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_971_; 
v___x_958_ = l_String_Slice_toString(v___x_953_);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_971_ == 0)
{
lean_object* v_unused_972_; lean_object* v_unused_973_; lean_object* v_unused_974_; 
v_unused_972_ = lean_ctor_get(v___x_953_, 2);
lean_dec(v_unused_972_);
v_unused_973_ = lean_ctor_get(v___x_953_, 1);
lean_dec(v_unused_973_);
v_unused_974_ = lean_ctor_get(v___x_953_, 0);
lean_dec(v_unused_974_);
v___x_960_ = v___x_953_;
v_isShared_961_ = v_isSharedCheck_971_;
goto v_resetjp_959_;
}
else
{
lean_dec(v___x_953_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_971_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_966_; 
v___x_962_ = ((lean_object*)(l_Lake_LogEntry_ofSerialMessage___closed__0));
v___x_963_ = lean_string_append(v___x_958_, v___x_962_);
v___x_964_ = lean_string_utf8_byte_size(v_data_943_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 2, v___x_964_);
lean_ctor_set(v___x_960_, 1, v___x_950_);
lean_ctor_set(v___x_960_, 0, v_data_943_);
v___x_966_ = v___x_960_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_data_943_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v___x_950_);
lean_ctor_set(v_reuseFailAlloc_970_, 2, v___x_964_);
v___x_966_ = v_reuseFailAlloc_970_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_967_ = l_String_Slice_trimAscii(v___x_966_);
v___x_968_ = l_String_Slice_toString(v___x_967_);
lean_dec_ref(v___x_967_);
v___x_969_ = lean_string_append(v___x_963_, v___x_968_);
lean_dec_ref(v___x_968_);
v___y_945_ = v___x_969_;
goto v___jp_944_;
}
}
}
else
{
lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_987_; 
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_987_ == 0)
{
lean_object* v_unused_988_; lean_object* v_unused_989_; lean_object* v_unused_990_; 
v_unused_988_ = lean_ctor_get(v___x_953_, 2);
lean_dec(v_unused_988_);
v_unused_989_ = lean_ctor_get(v___x_953_, 1);
lean_dec(v_unused_989_);
v_unused_990_ = lean_ctor_get(v___x_953_, 0);
lean_dec(v_unused_990_);
v___x_976_ = v___x_953_;
v_isShared_977_ = v_isSharedCheck_987_;
goto v_resetjp_975_;
}
else
{
lean_dec(v___x_953_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_987_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_978_ = lean_string_utf8_byte_size(v_data_943_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 2, v___x_978_);
lean_ctor_set(v___x_976_, 1, v___x_950_);
lean_ctor_set(v___x_976_, 0, v_data_943_);
v___x_980_ = v___x_976_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_data_943_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v___x_950_);
lean_ctor_set(v_reuseFailAlloc_986_, 2, v___x_978_);
v___x_980_ = v_reuseFailAlloc_986_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_981_; lean_object* v_str_982_; lean_object* v_startInclusive_983_; lean_object* v_endExclusive_984_; lean_object* v___x_985_; 
v___x_981_ = l_String_Slice_trimAscii(v___x_980_);
v_str_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc_ref(v_str_982_);
v_startInclusive_983_ = lean_ctor_get(v___x_981_, 1);
lean_inc(v_startInclusive_983_);
v_endExclusive_984_ = lean_ctor_get(v___x_981_, 2);
lean_inc(v_endExclusive_984_);
lean_dec_ref(v___x_981_);
v___x_985_ = lean_string_utf8_extract_fast(v_str_982_, v_startInclusive_983_, v_endExclusive_984_);
lean_dec(v_endExclusive_984_);
lean_dec(v_startInclusive_983_);
lean_dec_ref(v_str_982_);
v___y_945_ = v___x_985_;
goto v___jp_944_;
}
}
}
v___jp_944_:
{
uint8_t v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_946_ = l_Lake_LogLevel_ofMessageSeverity(v_severity_941_);
v___x_947_ = lean_box(0);
v___x_948_ = l_Lean_mkErrorStringWithPos(v_fileName_939_, v_pos_940_, v___y_945_, v___x_947_, v___x_947_, v___x_947_);
lean_dec_ref(v___y_945_);
v___x_949_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set_uint8(v___x_949_, sizeof(void*)*1, v___x_946_);
return v___x_949_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_ofMessage(lean_object* v_msg_991_){
_start:
{
lean_object* v_fileName_993_; lean_object* v_pos_994_; uint8_t v_severity_995_; lean_object* v_caption_996_; lean_object* v_data_997_; lean_object* v___x_998_; lean_object* v___y_1000_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v_startInclusive_1009_; lean_object* v_endExclusive_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v_fileName_993_ = lean_ctor_get(v_msg_991_, 0);
lean_inc_ref(v_fileName_993_);
v_pos_994_ = lean_ctor_get(v_msg_991_, 1);
lean_inc_ref(v_pos_994_);
v_severity_995_ = lean_ctor_get_uint8(v_msg_991_, sizeof(void*)*5 + 1);
v_caption_996_ = lean_ctor_get(v_msg_991_, 3);
lean_inc_ref(v_caption_996_);
v_data_997_ = lean_ctor_get(v_msg_991_, 4);
lean_inc(v_data_997_);
lean_dec_ref(v_msg_991_);
v___x_998_ = l_Lean_MessageData_toString(v_data_997_);
v___x_1005_ = lean_unsigned_to_nat(0u);
v___x_1006_ = lean_string_utf8_byte_size(v_caption_996_);
v___x_1007_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1007_, 0, v_caption_996_);
lean_ctor_set(v___x_1007_, 1, v___x_1005_);
lean_ctor_set(v___x_1007_, 2, v___x_1006_);
v___x_1008_ = l_String_Slice_trimAscii(v___x_1007_);
v_startInclusive_1009_ = lean_ctor_get(v___x_1008_, 1);
v_endExclusive_1010_ = lean_ctor_get(v___x_1008_, 2);
v___x_1011_ = lean_nat_sub(v_endExclusive_1010_, v_startInclusive_1009_);
v___x_1012_ = lean_nat_dec_eq(v___x_1011_, v___x_1005_);
lean_dec(v___x_1011_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1026_; 
v___x_1013_ = l_String_Slice_toString(v___x_1008_);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1026_ == 0)
{
lean_object* v_unused_1027_; lean_object* v_unused_1028_; lean_object* v_unused_1029_; 
v_unused_1027_ = lean_ctor_get(v___x_1008_, 2);
lean_dec(v_unused_1027_);
v_unused_1028_ = lean_ctor_get(v___x_1008_, 1);
lean_dec(v_unused_1028_);
v_unused_1029_ = lean_ctor_get(v___x_1008_, 0);
lean_dec(v_unused_1029_);
v___x_1015_ = v___x_1008_;
v_isShared_1016_ = v_isSharedCheck_1026_;
goto v_resetjp_1014_;
}
else
{
lean_dec(v___x_1008_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1026_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1021_; 
v___x_1017_ = ((lean_object*)(l_Lake_LogEntry_ofSerialMessage___closed__0));
v___x_1018_ = lean_string_append(v___x_1013_, v___x_1017_);
v___x_1019_ = lean_string_utf8_byte_size(v___x_998_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 2, v___x_1019_);
lean_ctor_set(v___x_1015_, 1, v___x_1005_);
lean_ctor_set(v___x_1015_, 0, v___x_998_);
v___x_1021_ = v___x_1015_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1025_, 2, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1022_ = l_String_Slice_trimAscii(v___x_1021_);
v___x_1023_ = l_String_Slice_toString(v___x_1022_);
lean_dec_ref(v___x_1022_);
v___x_1024_ = lean_string_append(v___x_1018_, v___x_1023_);
lean_dec_ref(v___x_1023_);
v___y_1000_ = v___x_1024_;
goto v___jp_999_;
}
}
}
else
{
lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1042_; 
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1042_ == 0)
{
lean_object* v_unused_1043_; lean_object* v_unused_1044_; lean_object* v_unused_1045_; 
v_unused_1043_ = lean_ctor_get(v___x_1008_, 2);
lean_dec(v_unused_1043_);
v_unused_1044_ = lean_ctor_get(v___x_1008_, 1);
lean_dec(v_unused_1044_);
v_unused_1045_ = lean_ctor_get(v___x_1008_, 0);
lean_dec(v_unused_1045_);
v___x_1031_ = v___x_1008_;
v_isShared_1032_ = v_isSharedCheck_1042_;
goto v_resetjp_1030_;
}
else
{
lean_dec(v___x_1008_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1042_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; lean_object* v___x_1035_; 
v___x_1033_ = lean_string_utf8_byte_size(v___x_998_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 2, v___x_1033_);
lean_ctor_set(v___x_1031_, 1, v___x_1005_);
lean_ctor_set(v___x_1031_, 0, v___x_998_);
v___x_1035_ = v___x_1031_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1041_, 2, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1036_; lean_object* v_str_1037_; lean_object* v_startInclusive_1038_; lean_object* v_endExclusive_1039_; lean_object* v___x_1040_; 
v___x_1036_ = l_String_Slice_trimAscii(v___x_1035_);
v_str_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc_ref(v_str_1037_);
v_startInclusive_1038_ = lean_ctor_get(v___x_1036_, 1);
lean_inc(v_startInclusive_1038_);
v_endExclusive_1039_ = lean_ctor_get(v___x_1036_, 2);
lean_inc(v_endExclusive_1039_);
lean_dec_ref(v___x_1036_);
v___x_1040_ = lean_string_utf8_extract_fast(v_str_1037_, v_startInclusive_1038_, v_endExclusive_1039_);
lean_dec(v_endExclusive_1039_);
lean_dec(v_startInclusive_1038_);
lean_dec_ref(v_str_1037_);
v___y_1000_ = v___x_1040_;
goto v___jp_999_;
}
}
}
v___jp_999_:
{
uint8_t v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1001_ = l_Lake_LogLevel_ofMessageSeverity(v_severity_995_);
v___x_1002_ = lean_box(0);
v___x_1003_ = l_Lean_mkErrorStringWithPos(v_fileName_993_, v_pos_994_, v___y_1000_, v___x_1002_, v___x_1002_, v___x_1002_);
lean_dec_ref(v___y_1000_);
v___x_1004_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
lean_ctor_set_uint8(v___x_1004_, sizeof(void*)*1, v___x_1001_);
return v___x_1004_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_ofMessage___boxed(lean_object* v_msg_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lake_LogEntry_ofMessage(v_msg_1046_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lake_logVerbose___redArg(lean_object* v_inst_1049_, lean_object* v_message_1050_){
_start:
{
uint8_t v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1051_ = 0;
v___x_1052_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1052_, 0, v_message_1050_);
lean_ctor_set_uint8(v___x_1052_, sizeof(void*)*1, v___x_1051_);
v___x_1053_ = lean_apply_1(v_inst_1049_, v___x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lake_logVerbose(lean_object* v_m_1054_, lean_object* v_inst_1055_, lean_object* v_inst_1056_, lean_object* v_message_1057_){
_start:
{
uint8_t v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1058_ = 0;
v___x_1059_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1059_, 0, v_message_1057_);
lean_ctor_set_uint8(v___x_1059_, sizeof(void*)*1, v___x_1058_);
v___x_1060_ = lean_apply_1(v_inst_1056_, v___x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lake_logVerbose___boxed(lean_object* v_m_1061_, lean_object* v_inst_1062_, lean_object* v_inst_1063_, lean_object* v_message_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lake_logVerbose(v_m_1061_, v_inst_1062_, v_inst_1063_, v_message_1064_);
lean_dec_ref(v_inst_1062_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lake_logInfo___redArg(lean_object* v_inst_1066_, lean_object* v_message_1067_){
_start:
{
uint8_t v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1068_ = 1;
v___x_1069_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1069_, 0, v_message_1067_);
lean_ctor_set_uint8(v___x_1069_, sizeof(void*)*1, v___x_1068_);
v___x_1070_ = lean_apply_1(v_inst_1066_, v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lake_logInfo(lean_object* v_m_1071_, lean_object* v_inst_1072_, lean_object* v_inst_1073_, lean_object* v_message_1074_){
_start:
{
uint8_t v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1075_ = 1;
v___x_1076_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1076_, 0, v_message_1074_);
lean_ctor_set_uint8(v___x_1076_, sizeof(void*)*1, v___x_1075_);
v___x_1077_ = lean_apply_1(v_inst_1073_, v___x_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Lake_logInfo___boxed(lean_object* v_m_1078_, lean_object* v_inst_1079_, lean_object* v_inst_1080_, lean_object* v_message_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lake_logInfo(v_m_1078_, v_inst_1079_, v_inst_1080_, v_message_1081_);
lean_dec_ref(v_inst_1079_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lake_logWarning___redArg(lean_object* v_inst_1083_, lean_object* v_message_1084_){
_start:
{
uint8_t v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1085_ = 2;
v___x_1086_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1086_, 0, v_message_1084_);
lean_ctor_set_uint8(v___x_1086_, sizeof(void*)*1, v___x_1085_);
v___x_1087_ = lean_apply_1(v_inst_1083_, v___x_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lake_logWarning(lean_object* v_m_1088_, lean_object* v_inst_1089_, lean_object* v_message_1090_){
_start:
{
uint8_t v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = 2;
v___x_1092_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1092_, 0, v_message_1090_);
lean_ctor_set_uint8(v___x_1092_, sizeof(void*)*1, v___x_1091_);
v___x_1093_ = lean_apply_1(v_inst_1089_, v___x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lake_logError___redArg(lean_object* v_inst_1094_, lean_object* v_message_1095_){
_start:
{
uint8_t v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1096_ = 3;
v___x_1097_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1097_, 0, v_message_1095_);
lean_ctor_set_uint8(v___x_1097_, sizeof(void*)*1, v___x_1096_);
v___x_1098_ = lean_apply_1(v_inst_1094_, v___x_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lake_logError(lean_object* v_m_1099_, lean_object* v_inst_1100_, lean_object* v_message_1101_){
_start:
{
uint8_t v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1102_ = 3;
v___x_1103_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1103_, 0, v_message_1101_);
lean_ctor_set_uint8(v___x_1103_, sizeof(void*)*1, v___x_1102_);
v___x_1104_ = lean_apply_1(v_inst_1100_, v___x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lake_logSerialMessage___redArg(lean_object* v_msg_1105_, lean_object* v_inst_1106_, lean_object* v_inst_1107_){
_start:
{
lean_object* v_toBaseMessage_1108_; lean_object* v_toApplicative_1109_; uint8_t v_isSilent_1110_; 
v_toBaseMessage_1108_ = lean_ctor_get(v_msg_1105_, 0);
v_toApplicative_1109_ = lean_ctor_get(v_inst_1106_, 0);
lean_inc_ref(v_toApplicative_1109_);
lean_dec_ref(v_inst_1106_);
v_isSilent_1110_ = lean_ctor_get_uint8(v_toBaseMessage_1108_, sizeof(void*)*5 + 2);
if (v_isSilent_1110_ == 0)
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
lean_dec_ref(v_toApplicative_1109_);
v___x_1111_ = l_Lake_LogEntry_ofSerialMessage(v_msg_1105_);
v___x_1112_ = lean_apply_1(v_inst_1107_, v___x_1111_);
return v___x_1112_;
}
else
{
lean_object* v_toPure_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_dec(v_inst_1107_);
lean_dec_ref(v_msg_1105_);
v_toPure_1113_ = lean_ctor_get(v_toApplicative_1109_, 1);
lean_inc(v_toPure_1113_);
lean_dec_ref(v_toApplicative_1109_);
v___x_1114_ = lean_box(0);
v___x_1115_ = lean_apply_2(v_toPure_1113_, lean_box(0), v___x_1114_);
return v___x_1115_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logSerialMessage(lean_object* v_m_1116_, lean_object* v_msg_1117_, lean_object* v_inst_1118_, lean_object* v_inst_1119_){
_start:
{
lean_object* v_toBaseMessage_1120_; lean_object* v_toApplicative_1121_; uint8_t v_isSilent_1122_; 
v_toBaseMessage_1120_ = lean_ctor_get(v_msg_1117_, 0);
v_toApplicative_1121_ = lean_ctor_get(v_inst_1118_, 0);
lean_inc_ref(v_toApplicative_1121_);
lean_dec_ref(v_inst_1118_);
v_isSilent_1122_ = lean_ctor_get_uint8(v_toBaseMessage_1120_, sizeof(void*)*5 + 2);
if (v_isSilent_1122_ == 0)
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
lean_dec_ref(v_toApplicative_1121_);
v___x_1123_ = l_Lake_LogEntry_ofSerialMessage(v_msg_1117_);
v___x_1124_ = lean_apply_1(v_inst_1119_, v___x_1123_);
return v___x_1124_;
}
else
{
lean_object* v_toPure_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_dec(v_inst_1119_);
lean_dec_ref(v_msg_1117_);
v_toPure_1125_ = lean_ctor_get(v_toApplicative_1121_, 1);
lean_inc(v_toPure_1125_);
lean_dec_ref(v_toApplicative_1121_);
v___x_1126_ = lean_box(0);
v___x_1127_ = lean_apply_2(v_toPure_1125_, lean_box(0), v___x_1126_);
return v___x_1127_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logMessage___redArg___lam__0(lean_object* v_inst_1128_, lean_object* v_____do__lift_1129_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_apply_1(v_inst_1128_, v_____do__lift_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lake_logMessage___redArg(lean_object* v_msg_1131_, lean_object* v_inst_1132_, lean_object* v_inst_1133_, lean_object* v_inst_1134_){
_start:
{
uint8_t v_isSilent_1135_; 
v_isSilent_1135_ = lean_ctor_get_uint8(v_msg_1131_, sizeof(void*)*5 + 2);
if (v_isSilent_1135_ == 0)
{
lean_object* v_toBind_1136_; lean_object* v___f_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v_toBind_1136_ = lean_ctor_get(v_inst_1132_, 1);
lean_inc(v_toBind_1136_);
lean_dec_ref(v_inst_1132_);
v___f_1137_ = lean_alloc_closure((void*)(l_Lake_logMessage___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1137_, 0, v_inst_1133_);
v___x_1138_ = lean_alloc_closure((void*)(l_Lake_LogEntry_ofMessage___boxed), 2, 1);
lean_closure_set(v___x_1138_, 0, v_msg_1131_);
v___x_1139_ = lean_apply_2(v_inst_1134_, lean_box(0), v___x_1138_);
v___x_1140_ = lean_apply_4(v_toBind_1136_, lean_box(0), lean_box(0), v___x_1139_, v___f_1137_);
return v___x_1140_;
}
else
{
lean_object* v_toApplicative_1141_; lean_object* v_toPure_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v_toApplicative_1141_ = lean_ctor_get(v_inst_1132_, 0);
lean_inc_ref(v_toApplicative_1141_);
lean_dec(v_inst_1134_);
lean_dec(v_inst_1133_);
lean_dec_ref(v_inst_1132_);
lean_dec_ref(v_msg_1131_);
v_toPure_1142_ = lean_ctor_get(v_toApplicative_1141_, 1);
lean_inc(v_toPure_1142_);
lean_dec_ref(v_toApplicative_1141_);
v___x_1143_ = lean_box(0);
v___x_1144_ = lean_apply_2(v_toPure_1142_, lean_box(0), v___x_1143_);
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logMessage(lean_object* v_m_1145_, lean_object* v_msg_1146_, lean_object* v_inst_1147_, lean_object* v_inst_1148_, lean_object* v_inst_1149_){
_start:
{
uint8_t v_isSilent_1150_; 
v_isSilent_1150_ = lean_ctor_get_uint8(v_msg_1146_, sizeof(void*)*5 + 2);
if (v_isSilent_1150_ == 0)
{
lean_object* v_toBind_1151_; lean_object* v___f_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v_toBind_1151_ = lean_ctor_get(v_inst_1147_, 1);
lean_inc(v_toBind_1151_);
lean_dec_ref(v_inst_1147_);
v___f_1152_ = lean_alloc_closure((void*)(l_Lake_logMessage___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1152_, 0, v_inst_1148_);
v___x_1153_ = lean_alloc_closure((void*)(l_Lake_LogEntry_ofMessage___boxed), 2, 1);
lean_closure_set(v___x_1153_, 0, v_msg_1146_);
v___x_1154_ = lean_apply_2(v_inst_1149_, lean_box(0), v___x_1153_);
v___x_1155_ = lean_apply_4(v_toBind_1151_, lean_box(0), lean_box(0), v___x_1154_, v___f_1152_);
return v___x_1155_;
}
else
{
lean_object* v_toApplicative_1156_; lean_object* v_toPure_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v_toApplicative_1156_ = lean_ctor_get(v_inst_1147_, 0);
lean_inc_ref(v_toApplicative_1156_);
lean_dec(v_inst_1149_);
lean_dec(v_inst_1148_);
lean_dec_ref(v_inst_1147_);
lean_dec_ref(v_msg_1146_);
v_toPure_1157_ = lean_ctor_get(v_toApplicative_1156_, 1);
lean_inc(v_toPure_1157_);
lean_dec_ref(v_toApplicative_1156_);
v___x_1158_ = lean_box(0);
v___x_1159_ = lean_apply_2(v_toPure_1157_, lean_box(0), v___x_1158_);
return v___x_1159_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logToStream(lean_object* v_e_1160_, lean_object* v_out_1161_, uint8_t v_minLv_1162_, uint8_t v_useAnsi_1163_){
_start:
{
uint8_t v_level_1165_; uint8_t v___x_1166_; 
v_level_1165_ = lean_ctor_get_uint8(v_e_1160_, sizeof(void*)*1);
v___x_1166_ = l_Lake_instOrdLogLevel_ord(v_minLv_1162_, v_level_1165_);
if (v___x_1166_ == 2)
{
lean_object* v___x_1167_; 
lean_dec_ref(v_out_1161_);
v___x_1167_ = lean_box(0);
return v___x_1167_;
}
else
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = l_Lake_LogEntry_toString(v_e_1160_, v_useAnsi_1163_);
v___x_1169_ = l_IO_FS_Stream_putStrLn(v_out_1161_, v___x_1168_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref_known(v___x_1169_, 1);
return v_a_1170_;
}
else
{
lean_object* v___x_1171_; 
lean_dec_ref_known(v___x_1169_, 1);
v___x_1171_ = lean_box(0);
return v___x_1171_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_logToStream___boxed(lean_object* v_e_1172_, lean_object* v_out_1173_, lean_object* v_minLv_1174_, lean_object* v_useAnsi_1175_, lean_object* v_a_1176_){
_start:
{
uint8_t v_minLv_boxed_1177_; uint8_t v_useAnsi_boxed_1178_; lean_object* v_res_1179_; 
v_minLv_boxed_1177_ = lean_unbox(v_minLv_1174_);
v_useAnsi_boxed_1178_ = lean_unbox(v_useAnsi_1175_);
v_res_1179_ = l_Lake_logToStream(v_e_1172_, v_out_1173_, v_minLv_boxed_1177_, v_useAnsi_boxed_1178_);
lean_dec_ref(v_e_1172_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___redArg___lam__0(lean_object* v_inst_1180_, lean_object* v_x_1181_){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = lean_box(0);
v___x_1183_ = lean_apply_2(v_inst_1180_, lean_box(0), v___x_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___redArg___lam__0___boxed(lean_object* v_inst_1184_, lean_object* v_x_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lake_MonadLog_nop___redArg___lam__0(v_inst_1184_, v_x_1185_);
lean_dec_ref(v_x_1185_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___redArg(lean_object* v_inst_1187_){
_start:
{
lean_object* v___f_1188_; 
v___f_1188_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1188_, 0, v_inst_1187_);
return v___f_1188_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop(lean_object* v_m_1189_, lean_object* v_inst_1190_){
_start:
{
lean_object* v___f_1191_; 
v___f_1191_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1191_, 0, v_inst_1190_);
return v___f_1191_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instInhabitedOfPure___redArg(lean_object* v_inst_1192_){
_start:
{
lean_object* v___f_1193_; 
v___f_1193_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1193_, 0, v_inst_1192_);
return v___f_1193_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instInhabitedOfPure(lean_object* v_m_1194_, lean_object* v_inst_1195_){
_start:
{
lean_object* v___f_1196_; 
v___f_1196_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1196_, 0, v_inst_1195_);
return v___f_1196_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift___redArg___lam__0(lean_object* v_self_1197_, lean_object* v_inst_1198_, lean_object* v_e_1199_){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_apply_1(v_self_1197_, v_e_1199_);
v___x_1201_ = lean_apply_2(v_inst_1198_, lean_box(0), v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift___redArg(lean_object* v_inst_1202_, lean_object* v_self_1203_){
_start:
{
lean_object* v___f_1204_; 
v___f_1204_ = lean_alloc_closure((void*)(l_Lake_MonadLog_lift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1204_, 0, v_self_1203_);
lean_closure_set(v___f_1204_, 1, v_inst_1202_);
return v___f_1204_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift(lean_object* v_m_1205_, lean_object* v_n_1206_, lean_object* v_inst_1207_, lean_object* v_self_1208_){
_start:
{
lean_object* v___f_1209_; 
v___f_1209_ = lean_alloc_closure((void*)(l_Lake_MonadLog_lift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1209_, 0, v_self_1208_);
lean_closure_set(v___f_1209_, 1, v_inst_1207_);
return v___f_1209_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift___redArg___lam__0(lean_object* v_methods_1210_, lean_object* v_inst_1211_, lean_object* v_e_1212_){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = lean_apply_1(v_methods_1210_, v_e_1212_);
v___x_1214_ = lean_apply_2(v_inst_1211_, lean_box(0), v___x_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift___redArg(lean_object* v_inst_1215_, lean_object* v_methods_1216_){
_start:
{
lean_object* v___f_1217_; 
v___f_1217_ = lean_alloc_closure((void*)(l_Lake_MonadLog_instOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1217_, 0, v_methods_1216_);
lean_closure_set(v___f_1217_, 1, v_inst_1215_);
return v___f_1217_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift(lean_object* v_m_1218_, lean_object* v_n_1219_, lean_object* v_inst_1220_, lean_object* v_methods_1221_){
_start:
{
lean_object* v___f_1222_; 
v___f_1222_ = lean_alloc_closure((void*)(l_Lake_MonadLog_instOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1222_, 0, v_methods_1221_);
lean_closure_set(v___f_1222_, 1, v_inst_1220_);
return v___f_1222_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg___lam__0(lean_object* v_out_1223_, uint8_t v_minLv_1224_, uint8_t v_useAnsi_1225_, lean_object* v_inst_1226_, lean_object* v_e_1227_){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1228_ = lean_box(v_minLv_1224_);
v___x_1229_ = lean_box(v_useAnsi_1225_);
v___x_1230_ = lean_alloc_closure((void*)(l_Lake_logToStream___boxed), 5, 4);
lean_closure_set(v___x_1230_, 0, v_e_1227_);
lean_closure_set(v___x_1230_, 1, v_out_1223_);
lean_closure_set(v___x_1230_, 2, v___x_1228_);
lean_closure_set(v___x_1230_, 3, v___x_1229_);
v___x_1231_ = lean_apply_2(v_inst_1226_, lean_box(0), v___x_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg___lam__0___boxed(lean_object* v_out_1232_, lean_object* v_minLv_1233_, lean_object* v_useAnsi_1234_, lean_object* v_inst_1235_, lean_object* v_e_1236_){
_start:
{
uint8_t v_minLv_boxed_1237_; uint8_t v_useAnsi_boxed_1238_; lean_object* v_res_1239_; 
v_minLv_boxed_1237_ = lean_unbox(v_minLv_1233_);
v_useAnsi_boxed_1238_ = lean_unbox(v_useAnsi_1234_);
v_res_1239_ = l_Lake_MonadLog_stream___redArg___lam__0(v_out_1232_, v_minLv_boxed_1237_, v_useAnsi_boxed_1238_, v_inst_1235_, v_e_1236_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg(lean_object* v_inst_1240_, lean_object* v_out_1241_, uint8_t v_minLv_1242_, uint8_t v_useAnsi_1243_){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___f_1246_; 
v___x_1244_ = lean_box(v_minLv_1242_);
v___x_1245_ = lean_box(v_useAnsi_1243_);
v___f_1246_ = lean_alloc_closure((void*)(l_Lake_MonadLog_stream___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1246_, 0, v_out_1241_);
lean_closure_set(v___f_1246_, 1, v___x_1244_);
lean_closure_set(v___f_1246_, 2, v___x_1245_);
lean_closure_set(v___f_1246_, 3, v_inst_1240_);
return v___f_1246_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg___boxed(lean_object* v_inst_1247_, lean_object* v_out_1248_, lean_object* v_minLv_1249_, lean_object* v_useAnsi_1250_){
_start:
{
uint8_t v_minLv_boxed_1251_; uint8_t v_useAnsi_boxed_1252_; lean_object* v_res_1253_; 
v_minLv_boxed_1251_ = lean_unbox(v_minLv_1249_);
v_useAnsi_boxed_1252_ = lean_unbox(v_useAnsi_1250_);
v_res_1253_ = l_Lake_MonadLog_stream___redArg(v_inst_1247_, v_out_1248_, v_minLv_boxed_1251_, v_useAnsi_boxed_1252_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream(lean_object* v_m_1254_, lean_object* v_inst_1255_, lean_object* v_out_1256_, uint8_t v_minLv_1257_, uint8_t v_useAnsi_1258_){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___f_1261_; 
v___x_1259_ = lean_box(v_minLv_1257_);
v___x_1260_ = lean_box(v_useAnsi_1258_);
v___f_1261_ = lean_alloc_closure((void*)(l_Lake_MonadLog_stream___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1261_, 0, v_out_1256_);
lean_closure_set(v___f_1261_, 1, v___x_1259_);
lean_closure_set(v___f_1261_, 2, v___x_1260_);
lean_closure_set(v___f_1261_, 3, v_inst_1255_);
return v___f_1261_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___boxed(lean_object* v_m_1262_, lean_object* v_inst_1263_, lean_object* v_out_1264_, lean_object* v_minLv_1265_, lean_object* v_useAnsi_1266_){
_start:
{
uint8_t v_minLv_boxed_1267_; uint8_t v_useAnsi_boxed_1268_; lean_object* v_res_1269_; 
v_minLv_boxed_1267_ = lean_unbox(v_minLv_1265_);
v_useAnsi_boxed_1268_ = lean_unbox(v_useAnsi_1266_);
v_res_1269_ = l_Lake_MonadLog_stream(v_m_1262_, v_inst_1263_, v_out_1264_, v_minLv_boxed_1267_, v_useAnsi_boxed_1268_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_error___redArg___lam__0(lean_object* v_failure_1270_, lean_object* v_x_1271_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = lean_apply_1(v_failure_1270_, lean_box(0));
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_error___redArg(lean_object* v_inst_1273_, lean_object* v_inst_1274_, lean_object* v_msg_1275_){
_start:
{
lean_object* v_toApplicative_1276_; lean_object* v_failure_1277_; lean_object* v_toSeqRight_1278_; lean_object* v___f_1279_; uint8_t v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v_toApplicative_1276_ = lean_ctor_get(v_inst_1273_, 0);
lean_inc_ref(v_toApplicative_1276_);
v_failure_1277_ = lean_ctor_get(v_inst_1273_, 1);
lean_inc(v_failure_1277_);
lean_dec_ref(v_inst_1273_);
v_toSeqRight_1278_ = lean_ctor_get(v_toApplicative_1276_, 4);
lean_inc(v_toSeqRight_1278_);
lean_dec_ref(v_toApplicative_1276_);
v___f_1279_ = lean_alloc_closure((void*)(l_Lake_MonadLog_error___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1279_, 0, v_failure_1277_);
v___x_1280_ = 3;
v___x_1281_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1281_, 0, v_msg_1275_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*1, v___x_1280_);
v___x_1282_ = lean_apply_1(v_inst_1274_, v___x_1281_);
v___x_1283_ = lean_apply_4(v_toSeqRight_1278_, lean_box(0), lean_box(0), v___x_1282_, v___f_1279_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_error(lean_object* v_m_1284_, lean_object* v_00_u03b1_1285_, lean_object* v_inst_1286_, lean_object* v_inst_1287_, lean_object* v_msg_1288_){
_start:
{
lean_object* v_toApplicative_1289_; lean_object* v_failure_1290_; lean_object* v_toSeqRight_1291_; lean_object* v___f_1292_; uint8_t v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v_toApplicative_1289_ = lean_ctor_get(v_inst_1286_, 0);
lean_inc_ref(v_toApplicative_1289_);
v_failure_1290_ = lean_ctor_get(v_inst_1286_, 1);
lean_inc(v_failure_1290_);
lean_dec_ref(v_inst_1286_);
v_toSeqRight_1291_ = lean_ctor_get(v_toApplicative_1289_, 4);
lean_inc(v_toSeqRight_1291_);
lean_dec_ref(v_toApplicative_1289_);
v___f_1292_ = lean_alloc_closure((void*)(l_Lake_MonadLog_error___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1292_, 0, v_failure_1290_);
v___x_1293_ = 3;
v___x_1294_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1294_, 0, v_msg_1288_);
lean_ctor_set_uint8(v___x_1294_, sizeof(void*)*1, v___x_1293_);
v___x_1295_ = lean_apply_1(v_inst_1287_, v___x_1294_);
v___x_1296_ = lean_apply_4(v_toSeqRight_1291_, lean_box(0), lean_box(0), v___x_1295_, v___f_1292_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logEntry(lean_object* v_self_1297_, lean_object* v_e_1298_, uint8_t v_minLv_1299_, uint8_t v_ansiMode_1300_){
_start:
{
lean_object* v___x_1302_; uint8_t v___x_1303_; lean_object* v___x_1304_; 
v___x_1302_ = l_Lake_OutStream_get(v_self_1297_);
lean_inc_ref(v___x_1302_);
v___x_1303_ = l_Lake_AnsiMode_isEnabled(v___x_1302_, v_ansiMode_1300_);
v___x_1304_ = l_Lake_logToStream(v_e_1298_, v___x_1302_, v_minLv_1299_, v___x_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logEntry___boxed(lean_object* v_self_1305_, lean_object* v_e_1306_, lean_object* v_minLv_1307_, lean_object* v_ansiMode_1308_, lean_object* v_a_1309_){
_start:
{
uint8_t v_minLv_boxed_1310_; uint8_t v_ansiMode_boxed_1311_; lean_object* v_res_1312_; 
v_minLv_boxed_1310_ = lean_unbox(v_minLv_1307_);
v_ansiMode_boxed_1311_ = lean_unbox(v_ansiMode_1308_);
v_res_1312_ = l_Lake_OutStream_logEntry(v_self_1305_, v_e_1306_, v_minLv_boxed_1310_, v_ansiMode_boxed_1311_);
lean_dec_ref(v_e_1306_);
lean_dec(v_self_1305_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg___lam__0(lean_object* v_out_1313_, uint8_t v_minLv_1314_, uint8_t v_ansiMode_1315_, lean_object* v_inst_1316_, lean_object* v_e_1317_){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1318_ = lean_box(v_minLv_1314_);
v___x_1319_ = lean_box(v_ansiMode_1315_);
v___x_1320_ = lean_alloc_closure((void*)(l_Lake_OutStream_logEntry___boxed), 5, 4);
lean_closure_set(v___x_1320_, 0, v_out_1313_);
lean_closure_set(v___x_1320_, 1, v_e_1317_);
lean_closure_set(v___x_1320_, 2, v___x_1318_);
lean_closure_set(v___x_1320_, 3, v___x_1319_);
v___x_1321_ = lean_apply_2(v_inst_1316_, lean_box(0), v___x_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg___lam__0___boxed(lean_object* v_out_1322_, lean_object* v_minLv_1323_, lean_object* v_ansiMode_1324_, lean_object* v_inst_1325_, lean_object* v_e_1326_){
_start:
{
uint8_t v_minLv_boxed_1327_; uint8_t v_ansiMode_boxed_1328_; lean_object* v_res_1329_; 
v_minLv_boxed_1327_ = lean_unbox(v_minLv_1323_);
v_ansiMode_boxed_1328_ = lean_unbox(v_ansiMode_1324_);
v_res_1329_ = l_Lake_OutStream_logger___redArg___lam__0(v_out_1322_, v_minLv_boxed_1327_, v_ansiMode_boxed_1328_, v_inst_1325_, v_e_1326_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg(lean_object* v_inst_1330_, lean_object* v_out_1331_, uint8_t v_minLv_1332_, uint8_t v_ansiMode_1333_){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___f_1336_; 
v___x_1334_ = lean_box(v_minLv_1332_);
v___x_1335_ = lean_box(v_ansiMode_1333_);
v___f_1336_ = lean_alloc_closure((void*)(l_Lake_OutStream_logger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1336_, 0, v_out_1331_);
lean_closure_set(v___f_1336_, 1, v___x_1334_);
lean_closure_set(v___f_1336_, 2, v___x_1335_);
lean_closure_set(v___f_1336_, 3, v_inst_1330_);
return v___f_1336_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg___boxed(lean_object* v_inst_1337_, lean_object* v_out_1338_, lean_object* v_minLv_1339_, lean_object* v_ansiMode_1340_){
_start:
{
uint8_t v_minLv_boxed_1341_; uint8_t v_ansiMode_boxed_1342_; lean_object* v_res_1343_; 
v_minLv_boxed_1341_ = lean_unbox(v_minLv_1339_);
v_ansiMode_boxed_1342_ = lean_unbox(v_ansiMode_1340_);
v_res_1343_ = l_Lake_OutStream_logger___redArg(v_inst_1337_, v_out_1338_, v_minLv_boxed_1341_, v_ansiMode_boxed_1342_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger(lean_object* v_m_1344_, lean_object* v_inst_1345_, lean_object* v_out_1346_, uint8_t v_minLv_1347_, uint8_t v_ansiMode_1348_){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___f_1351_; 
v___x_1349_ = lean_box(v_minLv_1347_);
v___x_1350_ = lean_box(v_ansiMode_1348_);
v___f_1351_ = lean_alloc_closure((void*)(l_Lake_OutStream_logger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1351_, 0, v_out_1346_);
lean_closure_set(v___f_1351_, 1, v___x_1349_);
lean_closure_set(v___f_1351_, 2, v___x_1350_);
lean_closure_set(v___f_1351_, 3, v_inst_1345_);
return v___f_1351_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___boxed(lean_object* v_m_1352_, lean_object* v_inst_1353_, lean_object* v_out_1354_, lean_object* v_minLv_1355_, lean_object* v_ansiMode_1356_){
_start:
{
uint8_t v_minLv_boxed_1357_; uint8_t v_ansiMode_boxed_1358_; lean_object* v_res_1359_; 
v_minLv_boxed_1357_ = lean_unbox(v_minLv_1355_);
v_ansiMode_boxed_1358_ = lean_unbox(v_ansiMode_1356_);
v_res_1359_ = l_Lake_OutStream_logger(v_m_1352_, v_inst_1353_, v_out_1354_, v_minLv_boxed_1357_, v_ansiMode_boxed_1358_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg___lam__0(lean_object* v___x_1360_, uint8_t v_minLv_1361_, uint8_t v_ansiMode_1362_, lean_object* v_inst_1363_, lean_object* v_e_1364_){
_start:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1365_ = lean_box(v_minLv_1361_);
v___x_1366_ = lean_box(v_ansiMode_1362_);
v___x_1367_ = lean_alloc_closure((void*)(l_Lake_OutStream_logEntry___boxed), 5, 4);
lean_closure_set(v___x_1367_, 0, v___x_1360_);
lean_closure_set(v___x_1367_, 1, v_e_1364_);
lean_closure_set(v___x_1367_, 2, v___x_1365_);
lean_closure_set(v___x_1367_, 3, v___x_1366_);
v___x_1368_ = lean_apply_2(v_inst_1363_, lean_box(0), v___x_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg___lam__0___boxed(lean_object* v___x_1369_, lean_object* v_minLv_1370_, lean_object* v_ansiMode_1371_, lean_object* v_inst_1372_, lean_object* v_e_1373_){
_start:
{
uint8_t v_minLv_boxed_1374_; uint8_t v_ansiMode_boxed_1375_; lean_object* v_res_1376_; 
v_minLv_boxed_1374_ = lean_unbox(v_minLv_1370_);
v_ansiMode_boxed_1375_ = lean_unbox(v_ansiMode_1371_);
v_res_1376_ = l_Lake_MonadLog_stdout___redArg___lam__0(v___x_1369_, v_minLv_boxed_1374_, v_ansiMode_boxed_1375_, v_inst_1372_, v_e_1373_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg(lean_object* v_inst_1377_, uint8_t v_minLv_1378_, uint8_t v_ansiMode_1379_){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___f_1383_; 
v___x_1380_ = lean_box(0);
v___x_1381_ = lean_box(v_minLv_1378_);
v___x_1382_ = lean_box(v_ansiMode_1379_);
v___f_1383_ = lean_alloc_closure((void*)(l_Lake_MonadLog_stdout___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1383_, 0, v___x_1380_);
lean_closure_set(v___f_1383_, 1, v___x_1381_);
lean_closure_set(v___f_1383_, 2, v___x_1382_);
lean_closure_set(v___f_1383_, 3, v_inst_1377_);
return v___f_1383_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg___boxed(lean_object* v_inst_1384_, lean_object* v_minLv_1385_, lean_object* v_ansiMode_1386_){
_start:
{
uint8_t v_minLv_boxed_1387_; uint8_t v_ansiMode_boxed_1388_; lean_object* v_res_1389_; 
v_minLv_boxed_1387_ = lean_unbox(v_minLv_1385_);
v_ansiMode_boxed_1388_ = lean_unbox(v_ansiMode_1386_);
v_res_1389_ = l_Lake_MonadLog_stdout___redArg(v_inst_1384_, v_minLv_boxed_1387_, v_ansiMode_boxed_1388_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout(lean_object* v_m_1390_, lean_object* v_inst_1391_, uint8_t v_minLv_1392_, uint8_t v_ansiMode_1393_){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___f_1397_; 
v___x_1394_ = lean_box(0);
v___x_1395_ = lean_box(v_minLv_1392_);
v___x_1396_ = lean_box(v_ansiMode_1393_);
v___f_1397_ = lean_alloc_closure((void*)(l_Lake_MonadLog_stdout___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1397_, 0, v___x_1394_);
lean_closure_set(v___f_1397_, 1, v___x_1395_);
lean_closure_set(v___f_1397_, 2, v___x_1396_);
lean_closure_set(v___f_1397_, 3, v_inst_1391_);
return v___f_1397_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___boxed(lean_object* v_m_1398_, lean_object* v_inst_1399_, lean_object* v_minLv_1400_, lean_object* v_ansiMode_1401_){
_start:
{
uint8_t v_minLv_boxed_1402_; uint8_t v_ansiMode_boxed_1403_; lean_object* v_res_1404_; 
v_minLv_boxed_1402_ = lean_unbox(v_minLv_1400_);
v_ansiMode_boxed_1403_ = lean_unbox(v_ansiMode_1401_);
v_res_1404_ = l_Lake_MonadLog_stdout(v_m_1398_, v_inst_1399_, v_minLv_boxed_1402_, v_ansiMode_boxed_1403_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___redArg(lean_object* v_inst_1405_, uint8_t v_minLv_1406_, uint8_t v_ansiMode_1407_){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___f_1411_; 
v___x_1408_ = lean_box(1);
v___x_1409_ = lean_box(v_minLv_1406_);
v___x_1410_ = lean_box(v_ansiMode_1407_);
v___f_1411_ = lean_alloc_closure((void*)(l_Lake_MonadLog_stdout___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1411_, 0, v___x_1408_);
lean_closure_set(v___f_1411_, 1, v___x_1409_);
lean_closure_set(v___f_1411_, 2, v___x_1410_);
lean_closure_set(v___f_1411_, 3, v_inst_1405_);
return v___f_1411_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___redArg___boxed(lean_object* v_inst_1412_, lean_object* v_minLv_1413_, lean_object* v_ansiMode_1414_){
_start:
{
uint8_t v_minLv_boxed_1415_; uint8_t v_ansiMode_boxed_1416_; lean_object* v_res_1417_; 
v_minLv_boxed_1415_ = lean_unbox(v_minLv_1413_);
v_ansiMode_boxed_1416_ = lean_unbox(v_ansiMode_1414_);
v_res_1417_ = l_Lake_MonadLog_stderr___redArg(v_inst_1412_, v_minLv_boxed_1415_, v_ansiMode_boxed_1416_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr(lean_object* v_m_1418_, lean_object* v_inst_1419_, uint8_t v_minLv_1420_, uint8_t v_ansiMode_1421_){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___f_1425_; 
v___x_1422_ = lean_box(1);
v___x_1423_ = lean_box(v_minLv_1420_);
v___x_1424_ = lean_box(v_ansiMode_1421_);
v___f_1425_ = lean_alloc_closure((void*)(l_Lake_MonadLog_stdout___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1425_, 0, v___x_1422_);
lean_closure_set(v___f_1425_, 1, v___x_1423_);
lean_closure_set(v___f_1425_, 2, v___x_1424_);
lean_closure_set(v___f_1425_, 3, v_inst_1419_);
return v___f_1425_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___boxed(lean_object* v_m_1426_, lean_object* v_inst_1427_, lean_object* v_minLv_1428_, lean_object* v_ansiMode_1429_){
_start:
{
uint8_t v_minLv_boxed_1430_; uint8_t v_ansiMode_boxed_1431_; lean_object* v_res_1432_; 
v_minLv_boxed_1430_ = lean_unbox(v_minLv_1428_);
v_ansiMode_boxed_1431_ = lean_unbox(v_ansiMode_1429_);
v_res_1432_ = l_Lake_MonadLog_stderr(v_m_1426_, v_inst_1427_, v_minLv_boxed_1430_, v_ansiMode_boxed_1431_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg___lam__0(lean_object* v_val_1433_, uint8_t v_minLv_1434_, uint8_t v_val_1435_, lean_object* v_inst_1436_, lean_object* v_e_1437_){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1438_ = lean_box(v_minLv_1434_);
v___x_1439_ = lean_box(v_val_1435_);
v___x_1440_ = lean_alloc_closure((void*)(l_Lake_logToStream___boxed), 5, 4);
lean_closure_set(v___x_1440_, 0, v_e_1437_);
lean_closure_set(v___x_1440_, 1, v_val_1433_);
lean_closure_set(v___x_1440_, 2, v___x_1438_);
lean_closure_set(v___x_1440_, 3, v___x_1439_);
v___x_1441_ = lean_apply_2(v_inst_1436_, lean_box(0), v___x_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg___lam__0___boxed(lean_object* v_val_1442_, lean_object* v_minLv_1443_, lean_object* v_val_1444_, lean_object* v_inst_1445_, lean_object* v_e_1446_){
_start:
{
uint8_t v_minLv_boxed_1447_; uint8_t v_val_105__boxed_1448_; lean_object* v_res_1449_; 
v_minLv_boxed_1447_ = lean_unbox(v_minLv_1443_);
v_val_105__boxed_1448_ = lean_unbox(v_val_1444_);
v_res_1449_ = l_Lake_OutStream_getLogger___redArg___lam__0(v_val_1442_, v_minLv_boxed_1447_, v_val_105__boxed_1448_, v_inst_1445_, v_e_1446_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg(lean_object* v_inst_1450_, lean_object* v_out_1451_, uint8_t v_minLv_1452_, uint8_t v_ansiMode_1453_){
_start:
{
lean_object* v___x_1455_; uint8_t v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___f_1459_; 
v___x_1455_ = l_Lake_OutStream_get(v_out_1451_);
lean_inc_ref(v___x_1455_);
v___x_1456_ = l_Lake_AnsiMode_isEnabled(v___x_1455_, v_ansiMode_1453_);
v___x_1457_ = lean_box(v_minLv_1452_);
v___x_1458_ = lean_box(v___x_1456_);
v___f_1459_ = lean_alloc_closure((void*)(l_Lake_OutStream_getLogger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1459_, 0, v___x_1455_);
lean_closure_set(v___f_1459_, 1, v___x_1457_);
lean_closure_set(v___f_1459_, 2, v___x_1458_);
lean_closure_set(v___f_1459_, 3, v_inst_1450_);
return v___f_1459_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg___boxed(lean_object* v_inst_1460_, lean_object* v_out_1461_, lean_object* v_minLv_1462_, lean_object* v_ansiMode_1463_, lean_object* v_a_1464_){
_start:
{
uint8_t v_minLv_boxed_1465_; uint8_t v_ansiMode_boxed_1466_; lean_object* v_res_1467_; 
v_minLv_boxed_1465_ = lean_unbox(v_minLv_1462_);
v_ansiMode_boxed_1466_ = lean_unbox(v_ansiMode_1463_);
v_res_1467_ = l_Lake_OutStream_getLogger___redArg(v_inst_1460_, v_out_1461_, v_minLv_boxed_1465_, v_ansiMode_boxed_1466_);
lean_dec(v_out_1461_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger(lean_object* v_m_1468_, lean_object* v_inst_1469_, lean_object* v_out_1470_, uint8_t v_minLv_1471_, uint8_t v_ansiMode_1472_){
_start:
{
lean_object* v___x_1474_; uint8_t v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___f_1478_; 
v___x_1474_ = l_Lake_OutStream_get(v_out_1470_);
lean_inc_ref(v___x_1474_);
v___x_1475_ = l_Lake_AnsiMode_isEnabled(v___x_1474_, v_ansiMode_1472_);
v___x_1476_ = lean_box(v_minLv_1471_);
v___x_1477_ = lean_box(v___x_1475_);
v___f_1478_ = lean_alloc_closure((void*)(l_Lake_OutStream_getLogger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1478_, 0, v___x_1474_);
lean_closure_set(v___f_1478_, 1, v___x_1476_);
lean_closure_set(v___f_1478_, 2, v___x_1477_);
lean_closure_set(v___f_1478_, 3, v_inst_1469_);
return v___f_1478_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___boxed(lean_object* v_m_1479_, lean_object* v_inst_1480_, lean_object* v_out_1481_, lean_object* v_minLv_1482_, lean_object* v_ansiMode_1483_, lean_object* v_a_1484_){
_start:
{
uint8_t v_minLv_boxed_1485_; uint8_t v_ansiMode_boxed_1486_; lean_object* v_res_1487_; 
v_minLv_boxed_1485_ = lean_unbox(v_minLv_1482_);
v_ansiMode_boxed_1486_ = lean_unbox(v_ansiMode_1483_);
v_res_1487_ = l_Lake_OutStream_getLogger(v_m_1479_, v_inst_1480_, v_out_1481_, v_minLv_boxed_1485_, v_ansiMode_boxed_1486_);
lean_dec(v_out_1481_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0(lean_object* v_inst_1488_, lean_object* v_inst_1489_, lean_object* v_x_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_apply_2(v_inst_1488_, lean_box(0), v_inst_1489_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0___boxed(lean_object* v_inst_1492_, lean_object* v_inst_1493_, lean_object* v_x_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0(v_inst_1492_, v_inst_1493_, v_x_1494_);
lean_dec(v_x_1494_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___redArg(lean_object* v_inst_1496_, lean_object* v_inst_1497_){
_start:
{
lean_object* v___f_1498_; 
v___f_1498_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1498_, 0, v_inst_1496_);
lean_closure_set(v___f_1498_, 1, v_inst_1497_);
return v___f_1498_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure(lean_object* v_n_1499_, lean_object* v_00_u03b1_1500_, lean_object* v_m_1501_, lean_object* v_inst_1502_, lean_object* v_inst_1503_){
_start:
{
lean_object* v___f_1504_; 
v___f_1504_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1504_, 0, v_inst_1502_);
lean_closure_set(v___f_1504_, 1, v_inst_1503_);
return v___f_1504_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__0(lean_object* v_e_1505_, lean_object* v_inst_1506_, lean_object* v_a_1507_){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = lean_apply_1(v_a_1507_, v_e_1505_);
v___x_1509_ = lean_apply_2(v_inst_1506_, lean_box(0), v___x_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1(lean_object* v_inst_1510_, lean_object* v_inst_1511_, lean_object* v_e_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_toApplicative_1514_; lean_object* v_toBind_1515_; lean_object* v_toPure_1516_; lean_object* v___f_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v_toApplicative_1514_ = lean_ctor_get(v_inst_1510_, 0);
lean_inc_ref(v_toApplicative_1514_);
v_toBind_1515_ = lean_ctor_get(v_inst_1510_, 1);
lean_inc(v_toBind_1515_);
lean_dec_ref(v_inst_1510_);
v_toPure_1516_ = lean_ctor_get(v_toApplicative_1514_, 1);
lean_inc(v_toPure_1516_);
lean_dec_ref(v_toApplicative_1514_);
v___f_1517_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1517_, 0, v_e_1512_);
lean_closure_set(v___f_1517_, 1, v_inst_1511_);
lean_inc(v___y_1513_);
v___x_1518_ = lean_apply_2(v_toPure_1516_, lean_box(0), v___y_1513_);
v___x_1519_ = lean_apply_4(v_toBind_1515_, lean_box(0), lean_box(0), v___x_1518_, v___f_1517_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1___boxed(lean_object* v_inst_1520_, lean_object* v_inst_1521_, lean_object* v_e_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1(v_inst_1520_, v_inst_1521_, v_e_1522_, v___y_1523_);
lean_dec(v___y_1523_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg(lean_object* v_inst_1525_, lean_object* v_inst_1526_){
_start:
{
lean_object* v___f_1527_; 
v___f_1527_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1527_, 0, v_inst_1525_);
lean_closure_set(v___f_1527_, 1, v_inst_1526_);
return v___f_1527_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT(lean_object* v_n_1528_, lean_object* v_m_1529_, lean_object* v_inst_1530_, lean_object* v_inst_1531_){
_start:
{
lean_object* v___f_1532_; 
v___f_1532_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1532_, 0, v_inst_1530_);
lean_closure_set(v___f_1532_, 1, v_inst_1531_);
return v___f_1532_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___redArg(lean_object* v_f_1533_, lean_object* v_self_1534_, lean_object* v_a_1535_){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_inc(v_a_1535_);
v___x_1536_ = lean_apply_1(v_f_1533_, v_a_1535_);
v___x_1537_ = lean_apply_1(v_self_1534_, v___x_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___redArg___boxed(lean_object* v_f_1538_, lean_object* v_self_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lake_MonadLogT_adaptMethods___redArg(v_f_1538_, v_self_1539_, v_a_1540_);
lean_dec(v_a_1540_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods(lean_object* v_n_1542_, lean_object* v_m_1543_, lean_object* v_m_x27_1544_, lean_object* v_00_u03b1_1545_, lean_object* v_inst_1546_, lean_object* v_f_1547_, lean_object* v_self_1548_, lean_object* v_a_1549_){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
lean_inc(v_a_1549_);
v___x_1550_ = lean_apply_1(v_f_1547_, v_a_1549_);
v___x_1551_ = lean_apply_1(v_self_1548_, v___x_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___boxed(lean_object* v_n_1552_, lean_object* v_m_1553_, lean_object* v_m_x27_1554_, lean_object* v_00_u03b1_1555_, lean_object* v_inst_1556_, lean_object* v_f_1557_, lean_object* v_self_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_Lake_MonadLogT_adaptMethods(v_n_1552_, v_m_1553_, v_m_x27_1554_, v_00_u03b1_1555_, v_inst_1556_, v_f_1557_, v_self_1558_, v_a_1559_);
lean_dec(v_a_1559_);
lean_dec_ref(v_inst_1556_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog___redArg(lean_object* v_inst_1561_, lean_object* v_self_1562_){
_start:
{
lean_object* v___f_1563_; lean_object* v___x_1564_; 
v___f_1563_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1563_, 0, v_inst_1561_);
v___x_1564_ = lean_apply_1(v_self_1562_, v___f_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog(lean_object* v_m_1565_, lean_object* v_n_1566_, lean_object* v_00_u03b1_1567_, lean_object* v_inst_1568_, lean_object* v_self_1569_){
_start:
{
lean_object* v___f_1570_; lean_object* v___x_1571_; 
v___f_1570_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1570_, 0, v_inst_1568_);
v___x_1571_ = lean_apply_1(v_self_1569_, v___f_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonLog___lam__0(lean_object* v___x_1576_, lean_object* v_x_1577_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Lean_Array_toJson___redArg(v___x_1576_, v_x_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonLog___lam__0(lean_object* v___x_1582_, lean_object* v_x_1583_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Lean_Array_fromJson_x3f___redArg(v___x_1582_, v_x_1583_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
v_a_1593_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1584_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1584_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
}
static lean_object* _init_l_Lake_Log_instInhabitedPos_default(void){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = lean_unsigned_to_nat(0u);
return v___x_1604_;
}
}
static lean_object* _init_l_Lake_Log_instInhabitedPos(void){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = lean_unsigned_to_nat(0u);
return v___x_1605_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_instDecidableEqPos_decEq(lean_object* v_x_1606_, lean_object* v_x_1607_){
_start:
{
uint8_t v___x_1608_; 
v___x_1608_ = lean_nat_dec_eq(v_x_1606_, v_x_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_instDecidableEqPos_decEq___boxed(lean_object* v_x_1609_, lean_object* v_x_1610_){
_start:
{
uint8_t v_res_1611_; lean_object* v_r_1612_; 
v_res_1611_ = l_Lake_Log_instDecidableEqPos_decEq(v_x_1609_, v_x_1610_);
lean_dec(v_x_1610_);
lean_dec(v_x_1609_);
v_r_1612_ = lean_box(v_res_1611_);
return v_r_1612_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_instDecidableEqPos(lean_object* v_x_1613_, lean_object* v_x_1614_){
_start:
{
uint8_t v___x_1615_; 
v___x_1615_ = lean_nat_dec_eq(v_x_1613_, v_x_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_instDecidableEqPos___boxed(lean_object* v_x_1616_, lean_object* v_x_1617_){
_start:
{
uint8_t v_res_1618_; lean_object* v_r_1619_; 
v_res_1618_ = l_Lake_Log_instDecidableEqPos(v_x_1616_, v_x_1617_);
lean_dec(v_x_1617_);
lean_dec(v_x_1616_);
v_r_1619_ = lean_box(v_res_1618_);
return v_r_1619_;
}
}
static lean_object* _init_l_Lake_instOfNatPos(void){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = lean_unsigned_to_nat(0u);
return v___x_1620_;
}
}
LEAN_EXPORT uint8_t l_Lake_instOrdPos___lam__0(lean_object* v_x1_1621_, lean_object* v_x2_1622_){
_start:
{
uint8_t v___x_1623_; 
v___x_1623_ = lean_nat_dec_lt(v_x1_1621_, v_x2_1622_);
if (v___x_1623_ == 0)
{
uint8_t v___x_1624_; 
v___x_1624_ = lean_nat_dec_eq(v_x1_1621_, v_x2_1622_);
if (v___x_1624_ == 0)
{
uint8_t v___x_1625_; 
v___x_1625_ = 2;
return v___x_1625_;
}
else
{
uint8_t v___x_1626_; 
v___x_1626_ = 1;
return v___x_1626_;
}
}
else
{
uint8_t v___x_1627_; 
v___x_1627_ = 0;
return v___x_1627_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instOrdPos___lam__0___boxed(lean_object* v_x1_1628_, lean_object* v_x2_1629_){
_start:
{
uint8_t v_res_1630_; lean_object* v_r_1631_; 
v_res_1630_ = l_Lake_instOrdPos___lam__0(v_x1_1628_, v_x2_1629_);
lean_dec(v_x2_1629_);
lean_dec(v_x1_1628_);
v_r_1631_ = lean_box(v_res_1630_);
return v_r_1631_;
}
}
static lean_object* _init_l_Lake_instLTPos(void){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = lean_box(0);
return v___x_1634_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableRelPosLt(lean_object* v_a_1635_, lean_object* v_b_1636_){
_start:
{
uint8_t v___x_1637_; 
v___x_1637_ = lean_nat_dec_lt(v_a_1635_, v_b_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableRelPosLt___boxed(lean_object* v_a_1638_, lean_object* v_b_1639_){
_start:
{
uint8_t v_res_1640_; lean_object* v_r_1641_; 
v_res_1640_ = l_Lake_instDecidableRelPosLt(v_a_1638_, v_b_1639_);
lean_dec(v_b_1639_);
lean_dec(v_a_1638_);
v_r_1641_ = lean_box(v_res_1640_);
return v_r_1641_;
}
}
static lean_object* _init_l_Lake_instLEPos(void){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = lean_box(0);
return v___x_1642_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableRelPosLe(lean_object* v_a_1643_, lean_object* v_b_1644_){
_start:
{
uint8_t v___x_1645_; 
v___x_1645_ = lean_nat_dec_le(v_a_1643_, v_b_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableRelPosLe___boxed(lean_object* v_a_1646_, lean_object* v_b_1647_){
_start:
{
uint8_t v_res_1648_; lean_object* v_r_1649_; 
v_res_1648_ = l_Lake_instDecidableRelPosLe(v_a_1646_, v_b_1647_);
lean_dec(v_b_1647_);
lean_dec(v_a_1646_);
v_r_1649_ = lean_box(v_res_1648_);
return v_r_1649_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMinPos___lam__0(lean_object* v_x_1650_, lean_object* v_y_1651_){
_start:
{
uint8_t v___x_1652_; 
v___x_1652_ = lean_nat_dec_le(v_x_1650_, v_y_1651_);
if (v___x_1652_ == 0)
{
lean_inc(v_y_1651_);
return v_y_1651_;
}
else
{
lean_inc(v_x_1650_);
return v_x_1650_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMinPos___lam__0___boxed(lean_object* v_x_1653_, lean_object* v_y_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lake_instMinPos___lam__0(v_x_1653_, v_y_1654_);
lean_dec(v_y_1654_);
lean_dec(v_x_1653_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxPos___lam__0(lean_object* v_x_1658_, lean_object* v_y_1659_){
_start:
{
uint8_t v___x_1660_; 
v___x_1660_ = lean_nat_dec_le(v_x_1658_, v_y_1659_);
if (v___x_1660_ == 0)
{
lean_inc(v_x_1658_);
return v_x_1658_;
}
else
{
lean_inc(v_y_1659_);
return v_y_1659_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxPos___lam__0___boxed(lean_object* v_x_1661_, lean_object* v_y_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Lake_instMaxPos___lam__0(v_x_1661_, v_y_1662_);
lean_dec(v_y_1662_);
lean_dec(v_x_1661_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_size(lean_object* v_log_1670_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = lean_array_get_size(v_log_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_size___boxed(lean_object* v_log_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lake_Log_size(v_log_1672_);
lean_dec_ref(v_log_1672_);
return v_res_1673_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_isEmpty(lean_object* v_log_1674_){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; uint8_t v___x_1677_; 
v___x_1675_ = lean_array_get_size(v_log_1674_);
v___x_1676_ = lean_unsigned_to_nat(0u);
v___x_1677_ = lean_nat_dec_eq(v___x_1675_, v___x_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_isEmpty___boxed(lean_object* v_log_1678_){
_start:
{
uint8_t v_res_1679_; lean_object* v_r_1680_; 
v_res_1679_ = l_Lake_Log_isEmpty(v_log_1678_);
lean_dec_ref(v_log_1678_);
v_r_1680_ = lean_box(v_res_1679_);
return v_r_1680_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_hasEntries(lean_object* v_log_1681_){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; uint8_t v___x_1684_; 
v___x_1682_ = lean_array_get_size(v_log_1681_);
v___x_1683_ = lean_unsigned_to_nat(0u);
v___x_1684_ = lean_nat_dec_eq(v___x_1682_, v___x_1683_);
if (v___x_1684_ == 0)
{
uint8_t v___x_1685_; 
v___x_1685_ = 1;
return v___x_1685_;
}
else
{
uint8_t v___x_1686_; 
v___x_1686_ = 0;
return v___x_1686_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_hasEntries___boxed(lean_object* v_log_1687_){
_start:
{
uint8_t v_res_1688_; lean_object* v_r_1689_; 
v_res_1688_ = l_Lake_Log_hasEntries(v_log_1687_);
lean_dec_ref(v_log_1687_);
v_r_1689_ = lean_box(v_res_1688_);
return v_r_1689_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_endPos(lean_object* v_log_1690_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = lean_array_get_size(v_log_1690_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_endPos___boxed(lean_object* v_log_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lake_Log_endPos(v_log_1692_);
lean_dec_ref(v_log_1692_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_push(lean_object* v_log_1694_, lean_object* v_e_1695_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = lean_array_push(v_log_1694_, v_e_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_append(lean_object* v_log_1697_, lean_object* v_o_1698_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Array_append___redArg(v_log_1697_, v_o_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_append___boxed(lean_object* v_log_1700_, lean_object* v_o_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lake_Log_append(v_log_1700_, v_o_1701_);
lean_dec_ref(v_o_1701_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_extract(lean_object* v_log_1705_, lean_object* v_start_1706_, lean_object* v_stop_1707_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Array_extract___redArg(v_log_1705_, v_start_1706_, v_stop_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_extract___boxed(lean_object* v_log_1709_, lean_object* v_start_1710_, lean_object* v_stop_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lake_Log_extract(v_log_1709_, v_start_1710_, v_stop_1711_);
lean_dec_ref(v_log_1709_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_dropFrom(lean_object* v_log_1713_, lean_object* v_pos_1714_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Array_shrink___redArg(v_log_1713_, v_pos_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_dropFrom___boxed(lean_object* v_log_1716_, lean_object* v_pos_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lake_Log_dropFrom(v_log_1716_, v_pos_1717_);
lean_dec(v_pos_1717_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_takeFrom(lean_object* v_log_1719_, lean_object* v_pos_1720_){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = lean_array_get_size(v_log_1719_);
v___x_1722_ = l_Array_extract___redArg(v_log_1719_, v_pos_1720_, v___x_1721_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_takeFrom___boxed(lean_object* v_log_1723_, lean_object* v_pos_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lake_Log_takeFrom(v_log_1723_, v_pos_1724_);
lean_dec_ref(v_log_1723_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_split(lean_object* v_log_1726_, lean_object* v_pos_1727_){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_inc_ref(v_log_1726_);
v___x_1728_ = l_Array_shrink___redArg(v_log_1726_, v_pos_1727_);
v___x_1729_ = lean_array_get_size(v_log_1726_);
v___x_1730_ = l_Array_extract___redArg(v_log_1726_, v_pos_1727_, v___x_1729_);
lean_dec_ref(v_log_1726_);
v___x_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1728_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(lean_object* v_as_1733_, size_t v_i_1734_, size_t v_stop_1735_, lean_object* v_b_1736_){
_start:
{
uint8_t v___x_1737_; 
v___x_1737_ = lean_usize_dec_eq(v_i_1734_, v_stop_1735_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; size_t v___x_1743_; size_t v___x_1744_; 
v___x_1738_ = lean_array_uget_borrowed(v_as_1733_, v_i_1734_);
v___x_1739_ = l_Lake_LogEntry_toString(v___x_1738_, v___x_1737_);
v___x_1740_ = lean_string_append(v_b_1736_, v___x_1739_);
lean_dec_ref(v___x_1739_);
v___x_1741_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0___closed__0));
v___x_1742_ = lean_string_append(v___x_1740_, v___x_1741_);
v___x_1743_ = ((size_t)1ULL);
v___x_1744_ = lean_usize_add(v_i_1734_, v___x_1743_);
v_i_1734_ = v___x_1744_;
v_b_1736_ = v___x_1742_;
goto _start;
}
else
{
return v_b_1736_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0___boxed(lean_object* v_as_1746_, lean_object* v_i_1747_, lean_object* v_stop_1748_, lean_object* v_b_1749_){
_start:
{
size_t v_i_boxed_1750_; size_t v_stop_boxed_1751_; lean_object* v_res_1752_; 
v_i_boxed_1750_ = lean_unbox_usize(v_i_1747_);
lean_dec(v_i_1747_);
v_stop_boxed_1751_ = lean_unbox_usize(v_stop_1748_);
lean_dec(v_stop_1748_);
v_res_1752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(v_as_1746_, v_i_boxed_1750_, v_stop_boxed_1751_, v_b_1749_);
lean_dec_ref(v_as_1746_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_toString(lean_object* v_log_1753_){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; 
v___x_1754_ = ((lean_object*)(l_Lake_instInhabitedLogEntry_default___closed__0));
v___x_1755_ = lean_unsigned_to_nat(0u);
v___x_1756_ = lean_array_get_size(v_log_1753_);
v___x_1757_ = lean_nat_dec_lt(v___x_1755_, v___x_1756_);
if (v___x_1757_ == 0)
{
return v___x_1754_;
}
else
{
size_t v___x_1758_; size_t v___x_1759_; lean_object* v___x_1760_; 
v___x_1758_ = ((size_t)0ULL);
v___x_1759_ = lean_usize_of_nat(v___x_1756_);
v___x_1760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(v_log_1753_, v___x_1758_, v___x_1759_, v___x_1754_);
return v___x_1760_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_toString___boxed(lean_object* v_log_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Lake_Log_toString(v_log_1761_);
lean_dec_ref(v_log_1761_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_replay___redArg___lam__0(lean_object* v_logger_1765_, lean_object* v_x_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = lean_apply_1(v_logger_1765_, v___y_1767_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_replay___redArg(lean_object* v_inst_1769_, lean_object* v_logger_1770_, lean_object* v_log_1771_){
_start:
{
lean_object* v_toApplicative_1772_; lean_object* v_toPure_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; 
v_toApplicative_1772_ = lean_ctor_get(v_inst_1769_, 0);
v_toPure_1773_ = lean_ctor_get(v_toApplicative_1772_, 1);
v___x_1774_ = lean_unsigned_to_nat(0u);
v___x_1775_ = lean_array_get_size(v_log_1771_);
v___x_1776_ = lean_box(0);
v___x_1777_ = lean_nat_dec_lt(v___x_1774_, v___x_1775_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; 
lean_inc(v_toPure_1773_);
lean_dec_ref(v_log_1771_);
lean_dec(v_logger_1770_);
lean_dec_ref(v_inst_1769_);
v___x_1778_ = lean_apply_2(v_toPure_1773_, lean_box(0), v___x_1776_);
return v___x_1778_;
}
else
{
lean_object* v___f_1779_; size_t v___x_1780_; size_t v___x_1781_; lean_object* v___x_1782_; 
v___f_1779_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1779_, 0, v_logger_1770_);
v___x_1780_ = ((size_t)0ULL);
v___x_1781_ = lean_usize_of_nat(v___x_1775_);
v___x_1782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1769_, v___f_1779_, v_log_1771_, v___x_1780_, v___x_1781_, v___x_1776_);
return v___x_1782_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_replay(lean_object* v_m_1783_, lean_object* v_inst_1784_, lean_object* v_logger_1785_, lean_object* v_log_1786_){
_start:
{
lean_object* v_toApplicative_1787_; lean_object* v_toPure_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
v_toApplicative_1787_ = lean_ctor_get(v_inst_1784_, 0);
v_toPure_1788_ = lean_ctor_get(v_toApplicative_1787_, 1);
v___x_1789_ = lean_unsigned_to_nat(0u);
v___x_1790_ = lean_array_get_size(v_log_1786_);
v___x_1791_ = lean_box(0);
v___x_1792_ = lean_nat_dec_lt(v___x_1789_, v___x_1790_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1793_; 
lean_inc(v_toPure_1788_);
lean_dec_ref(v_log_1786_);
lean_dec(v_logger_1785_);
lean_dec_ref(v_inst_1784_);
v___x_1793_ = lean_apply_2(v_toPure_1788_, lean_box(0), v___x_1791_);
return v___x_1793_;
}
else
{
lean_object* v___f_1794_; size_t v___x_1795_; size_t v___x_1796_; lean_object* v___x_1797_; 
v___f_1794_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1794_, 0, v_logger_1785_);
v___x_1795_ = ((size_t)0ULL);
v___x_1796_ = lean_usize_of_nat(v___x_1790_);
v___x_1797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1784_, v___f_1794_, v_log_1786_, v___x_1795_, v___x_1796_, v___x_1791_);
return v___x_1797_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_filter___lam__0(lean_object* v_f_1798_, lean_object* v_x1_1799_, lean_object* v_x2_1800_){
_start:
{
lean_object* v___x_1801_; uint8_t v___x_1802_; 
lean_inc_ref(v_x2_1800_);
v___x_1801_ = lean_apply_1(v_f_1798_, v_x2_1800_);
v___x_1802_ = lean_unbox(v___x_1801_);
if (v___x_1802_ == 0)
{
lean_dec_ref(v_x2_1800_);
return v_x1_1799_;
}
else
{
lean_object* v___x_1803_; 
v___x_1803_ = lean_array_push(v_x1_1799_, v_x2_1800_);
return v___x_1803_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_filter(lean_object* v_f_1823_, lean_object* v_log_1824_){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
v___x_1825_ = lean_unsigned_to_nat(0u);
v___x_1826_ = lean_array_get_size(v_log_1824_);
v___x_1827_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_1828_ = ((lean_object*)(l_Lake_Log_filter___closed__9));
v___x_1829_ = lean_nat_dec_lt(v___x_1825_, v___x_1826_);
if (v___x_1829_ == 0)
{
lean_dec_ref(v_log_1824_);
lean_dec_ref(v_f_1823_);
return v___x_1827_;
}
else
{
lean_object* v___f_1830_; size_t v___x_1831_; size_t v___x_1832_; lean_object* v___x_1833_; 
v___f_1830_ = lean_alloc_closure((void*)(l_Lake_Log_filter___lam__0), 3, 1);
lean_closure_set(v___f_1830_, 0, v_f_1823_);
v___x_1831_ = ((size_t)0ULL);
v___x_1832_ = lean_usize_of_nat(v___x_1826_);
v___x_1833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1828_, v___f_1830_, v_log_1824_, v___x_1831_, v___x_1832_, v___x_1827_);
return v___x_1833_;
}
}
}
LEAN_EXPORT uint8_t l_Lake_Log_any___lam__0(lean_object* v_f_1834_, lean_object* v_x_1835_){
_start:
{
lean_object* v___x_1836_; uint8_t v___x_1837_; 
v___x_1836_ = lean_apply_1(v_f_1834_, v_x_1835_);
v___x_1837_ = lean_unbox(v___x_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_any___lam__0___boxed(lean_object* v_f_1838_, lean_object* v_x_1839_){
_start:
{
uint8_t v_res_1840_; lean_object* v_r_1841_; 
v_res_1840_ = l_Lake_Log_any___lam__0(v_f_1838_, v_x_1839_);
v_r_1841_ = lean_box(v_res_1840_);
return v_r_1841_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_any(lean_object* v_f_1842_, lean_object* v_log_1843_){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; 
v___x_1844_ = lean_unsigned_to_nat(0u);
v___x_1845_ = lean_array_get_size(v_log_1843_);
v___x_1846_ = ((lean_object*)(l_Lake_Log_filter___closed__9));
v___x_1847_ = lean_nat_dec_lt(v___x_1844_, v___x_1845_);
if (v___x_1847_ == 0)
{
lean_dec_ref(v_log_1843_);
lean_dec_ref(v_f_1842_);
return v___x_1847_;
}
else
{
if (v___x_1847_ == 0)
{
lean_dec_ref(v_log_1843_);
lean_dec_ref(v_f_1842_);
return v___x_1847_;
}
else
{
lean_object* v___f_1848_; size_t v___x_1849_; size_t v___x_1850_; lean_object* v___x_1851_; uint8_t v___x_1852_; 
v___f_1848_ = lean_alloc_closure((void*)(l_Lake_Log_any___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1848_, 0, v_f_1842_);
v___x_1849_ = ((size_t)0ULL);
v___x_1850_ = lean_usize_of_nat(v___x_1845_);
v___x_1851_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_1846_, v___f_1848_, v_log_1843_, v___x_1849_, v___x_1850_);
v___x_1852_ = lean_unbox(v___x_1851_);
lean_dec(v___x_1851_);
return v___x_1852_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_any___boxed(lean_object* v_f_1853_, lean_object* v_log_1854_){
_start:
{
uint8_t v_res_1855_; lean_object* v_r_1856_; 
v_res_1855_ = l_Lake_Log_any(v_f_1853_, v_log_1854_);
v_r_1856_ = lean_box(v_res_1855_);
return v_r_1856_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(lean_object* v_as_1857_, size_t v_i_1858_, size_t v_stop_1859_, uint8_t v_b_1860_){
_start:
{
uint8_t v___y_1862_; uint8_t v___x_1866_; 
v___x_1866_ = lean_usize_dec_eq(v_i_1858_, v_stop_1859_);
if (v___x_1866_ == 0)
{
lean_object* v___x_1867_; uint8_t v_level_1868_; uint8_t v___x_1869_; 
v___x_1867_ = lean_array_uget_borrowed(v_as_1857_, v_i_1858_);
v_level_1868_ = lean_ctor_get_uint8(v___x_1867_, sizeof(void*)*1);
v___x_1869_ = l_Lake_instOrdLogLevel_ord(v_b_1860_, v_level_1868_);
if (v___x_1869_ == 2)
{
v___y_1862_ = v_b_1860_;
goto v___jp_1861_;
}
else
{
v___y_1862_ = v_level_1868_;
goto v___jp_1861_;
}
}
else
{
return v_b_1860_;
}
v___jp_1861_:
{
size_t v___x_1863_; size_t v___x_1864_; 
v___x_1863_ = ((size_t)1ULL);
v___x_1864_ = lean_usize_add(v_i_1858_, v___x_1863_);
v_i_1858_ = v___x_1864_;
v_b_1860_ = v___y_1862_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0___boxed(lean_object* v_as_1870_, lean_object* v_i_1871_, lean_object* v_stop_1872_, lean_object* v_b_1873_){
_start:
{
size_t v_i_boxed_1874_; size_t v_stop_boxed_1875_; uint8_t v_b_boxed_1876_; uint8_t v_res_1877_; lean_object* v_r_1878_; 
v_i_boxed_1874_ = lean_unbox_usize(v_i_1871_);
lean_dec(v_i_1871_);
v_stop_boxed_1875_ = lean_unbox_usize(v_stop_1872_);
lean_dec(v_stop_1872_);
v_b_boxed_1876_ = lean_unbox(v_b_1873_);
v_res_1877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(v_as_1870_, v_i_boxed_1874_, v_stop_boxed_1875_, v_b_boxed_1876_);
lean_dec_ref(v_as_1870_);
v_r_1878_ = lean_box(v_res_1877_);
return v_r_1878_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_maxLv(lean_object* v_log_1879_){
_start:
{
uint8_t v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; uint8_t v___x_1883_; 
v___x_1880_ = 0;
v___x_1881_ = lean_unsigned_to_nat(0u);
v___x_1882_ = lean_array_get_size(v_log_1879_);
v___x_1883_ = lean_nat_dec_lt(v___x_1881_, v___x_1882_);
if (v___x_1883_ == 0)
{
return v___x_1880_;
}
else
{
size_t v___x_1884_; size_t v___x_1885_; uint8_t v___x_1886_; 
v___x_1884_ = ((size_t)0ULL);
v___x_1885_ = lean_usize_of_nat(v___x_1882_);
v___x_1886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(v_log_1879_, v___x_1884_, v___x_1885_, v___x_1880_);
return v___x_1886_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_maxLv___boxed(lean_object* v_log_1887_){
_start:
{
uint8_t v_res_1888_; lean_object* v_r_1889_; 
v_res_1888_ = l_Lake_Log_maxLv(v_log_1887_);
lean_dec_ref(v_log_1887_);
v_r_1889_ = lean_box(v_res_1888_);
return v_r_1889_;
}
}
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___redArg___lam__0(lean_object* v_e_1890_, lean_object* v_s_1891_){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = lean_box(0);
v___x_1893_ = lean_array_push(v_s_1891_, v_e_1890_);
v___x_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1892_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___redArg(lean_object* v_inst_1895_, lean_object* v_e_1896_){
_start:
{
lean_object* v_modifyGet_1897_; lean_object* v___f_1898_; lean_object* v___x_1899_; 
v_modifyGet_1897_ = lean_ctor_get(v_inst_1895_, 2);
lean_inc(v_modifyGet_1897_);
lean_dec_ref(v_inst_1895_);
v___f_1898_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1898_, 0, v_e_1896_);
v___x_1899_ = lean_apply_2(v_modifyGet_1897_, lean_box(0), v___f_1898_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lake_pushLogEntry(lean_object* v_m_1900_, lean_object* v_inst_1901_, lean_object* v_e_1902_){
_start:
{
lean_object* v_modifyGet_1903_; lean_object* v___f_1904_; lean_object* v___x_1905_; 
v_modifyGet_1903_ = lean_ctor_get(v_inst_1901_, 2);
lean_inc(v_modifyGet_1903_);
lean_dec_ref(v_inst_1901_);
v___f_1904_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1904_, 0, v_e_1902_);
v___x_1905_ = lean_apply_2(v_modifyGet_1903_, lean_box(0), v___f_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_ofMonadState___redArg(lean_object* v_inst_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(v___x_1907_, 0, lean_box(0));
lean_closure_set(v___x_1907_, 1, v_inst_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_ofMonadState(lean_object* v_m_1908_, lean_object* v_inst_1909_){
_start:
{
lean_object* v___x_1910_; 
v___x_1910_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(v___x_1910_, 0, lean_box(0));
lean_closure_set(v___x_1910_, 1, v_inst_1909_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog___redArg(lean_object* v_inst_1911_){
_start:
{
lean_object* v_get_1912_; 
v_get_1912_ = lean_ctor_get(v_inst_1911_, 0);
lean_inc(v_get_1912_);
return v_get_1912_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog___redArg___boxed(lean_object* v_inst_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Lake_getLog___redArg(v_inst_1913_);
lean_dec_ref(v_inst_1913_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog(lean_object* v_m_1915_, lean_object* v_inst_1916_){
_start:
{
lean_object* v_get_1917_; 
v_get_1917_ = lean_ctor_get(v_inst_1916_, 0);
lean_inc(v_get_1917_);
return v_get_1917_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog___boxed(lean_object* v_m_1918_, lean_object* v_inst_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Lake_getLog(v_m_1918_, v_inst_1919_);
lean_dec_ref(v_inst_1919_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg___lam__0(lean_object* v_x_1921_){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = lean_array_get_size(v_x_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg___lam__0___boxed(lean_object* v_x_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Lake_getLogPos___redArg___lam__0(v_x_1923_);
lean_dec_ref(v_x_1923_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg(lean_object* v_inst_1926_, lean_object* v_inst_1927_){
_start:
{
lean_object* v_map_1928_; lean_object* v_get_1929_; lean_object* v___f_1930_; lean_object* v___x_1931_; 
v_map_1928_ = lean_ctor_get(v_inst_1926_, 0);
lean_inc(v_map_1928_);
lean_dec_ref(v_inst_1926_);
v_get_1929_ = lean_ctor_get(v_inst_1927_, 0);
lean_inc(v_get_1929_);
lean_dec_ref(v_inst_1927_);
v___f_1930_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_1931_ = lean_apply_4(v_map_1928_, lean_box(0), lean_box(0), v___f_1930_, v_get_1929_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos(lean_object* v_m_1932_, lean_object* v_inst_1933_, lean_object* v_inst_1934_){
_start:
{
lean_object* v_map_1935_; lean_object* v_get_1936_; lean_object* v___f_1937_; lean_object* v___x_1938_; 
v_map_1935_ = lean_ctor_get(v_inst_1933_, 0);
lean_inc(v_map_1935_);
lean_dec_ref(v_inst_1933_);
v_get_1936_ = lean_ctor_get(v_inst_1934_, 0);
lean_inc(v_get_1936_);
lean_dec_ref(v_inst_1934_);
v___f_1937_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_1938_ = lean_apply_4(v_map_1935_, lean_box(0), lean_box(0), v___f_1937_, v_get_1936_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLog___redArg___lam__0(lean_object* v_log_1939_){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1940_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1941_, 0, v_log_1939_);
lean_ctor_set(v___x_1941_, 1, v___x_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLog___redArg(lean_object* v_inst_1943_){
_start:
{
lean_object* v_modifyGet_1944_; lean_object* v___f_1945_; lean_object* v___x_1946_; 
v_modifyGet_1944_ = lean_ctor_get(v_inst_1943_, 2);
lean_inc(v_modifyGet_1944_);
lean_dec_ref(v_inst_1943_);
v___f_1945_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_1946_ = lean_apply_2(v_modifyGet_1944_, lean_box(0), v___f_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLog(lean_object* v_m_1947_, lean_object* v_inst_1948_){
_start:
{
lean_object* v_modifyGet_1949_; lean_object* v___f_1950_; lean_object* v___x_1951_; 
v_modifyGet_1949_ = lean_ctor_get(v_inst_1948_, 2);
lean_inc(v_modifyGet_1949_);
lean_dec_ref(v_inst_1948_);
v___f_1950_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_1951_ = lean_apply_2(v_modifyGet_1949_, lean_box(0), v___f_1950_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLogFrom___redArg___lam__0(lean_object* v_pos_1952_, lean_object* v_log_1953_){
_start:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1954_ = lean_array_get_size(v_log_1953_);
lean_inc(v_pos_1952_);
v___x_1955_ = l_Array_extract___redArg(v_log_1953_, v_pos_1952_, v___x_1954_);
v___x_1956_ = l_Array_shrink___redArg(v_log_1953_, v_pos_1952_);
lean_dec(v_pos_1952_);
v___x_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1955_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLogFrom___redArg(lean_object* v_inst_1958_, lean_object* v_pos_1959_){
_start:
{
lean_object* v_modifyGet_1960_; lean_object* v___f_1961_; lean_object* v___x_1962_; 
v_modifyGet_1960_ = lean_ctor_get(v_inst_1958_, 2);
lean_inc(v_modifyGet_1960_);
lean_dec_ref(v_inst_1958_);
v___f_1961_ = lean_alloc_closure((void*)(l_Lake_takeLogFrom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1961_, 0, v_pos_1959_);
v___x_1962_ = lean_apply_2(v_modifyGet_1960_, lean_box(0), v___f_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLogFrom(lean_object* v_m_1963_, lean_object* v_inst_1964_, lean_object* v_pos_1965_){
_start:
{
lean_object* v_modifyGet_1966_; lean_object* v___f_1967_; lean_object* v___x_1968_; 
v_modifyGet_1966_ = lean_ctor_get(v_inst_1964_, 2);
lean_inc(v_modifyGet_1966_);
lean_dec_ref(v_inst_1964_);
v___f_1967_ = lean_alloc_closure((void*)(l_Lake_takeLogFrom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1967_, 0, v_pos_1965_);
v___x_1968_ = lean_apply_2(v_modifyGet_1966_, lean_box(0), v___f_1967_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg___lam__0(lean_object* v_pos_1969_, lean_object* v_s_1970_){
_start:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1971_ = lean_box(0);
v___x_1972_ = l_Array_shrink___redArg(v_s_1970_, v_pos_1969_);
v___x_1973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1971_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg___lam__0___boxed(lean_object* v_pos_1974_, lean_object* v_s_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lake_dropLogFrom___redArg___lam__0(v_pos_1974_, v_s_1975_);
lean_dec(v_pos_1974_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg(lean_object* v_inst_1977_, lean_object* v_pos_1978_){
_start:
{
lean_object* v_modifyGet_1979_; lean_object* v___f_1980_; lean_object* v___x_1981_; 
v_modifyGet_1979_ = lean_ctor_get(v_inst_1977_, 2);
lean_inc(v_modifyGet_1979_);
lean_dec_ref(v_inst_1977_);
v___f_1980_ = lean_alloc_closure((void*)(l_Lake_dropLogFrom___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1980_, 0, v_pos_1978_);
v___x_1981_ = lean_apply_2(v_modifyGet_1979_, lean_box(0), v___f_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom(lean_object* v_m_1982_, lean_object* v_inst_1983_, lean_object* v_pos_1984_){
_start:
{
lean_object* v_modifyGet_1985_; lean_object* v___f_1986_; lean_object* v___x_1987_; 
v_modifyGet_1985_ = lean_ctor_get(v_inst_1983_, 2);
lean_inc(v_modifyGet_1985_);
lean_dec_ref(v_inst_1983_);
v___f_1986_ = lean_alloc_closure((void*)(l_Lake_dropLogFrom___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1986_, 0, v_pos_1984_);
v___x_1987_ = lean_apply_2(v_modifyGet_1985_, lean_box(0), v___f_1986_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__1(lean_object* v_iniPos_1988_, lean_object* v_toPure_1989_, lean_object* v_log_1990_){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1991_ = lean_array_get_size(v_log_1990_);
v___x_1992_ = l_Array_extract___redArg(v_log_1990_, v_iniPos_1988_, v___x_1991_);
v___x_1993_ = lean_apply_2(v_toPure_1989_, lean_box(0), v___x_1992_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__1___boxed(lean_object* v_iniPos_1994_, lean_object* v_toPure_1995_, lean_object* v_log_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lake_extractLog___redArg___lam__1(v_iniPos_1994_, v_toPure_1995_, v_log_1996_);
lean_dec_ref(v_log_1996_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__0(lean_object* v_toBind_1998_, lean_object* v_get_1999_, lean_object* v___f_2000_, lean_object* v_____r_2001_){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = lean_apply_4(v_toBind_1998_, lean_box(0), lean_box(0), v_get_1999_, v___f_2000_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__2(lean_object* v_toPure_2003_, lean_object* v_toBind_2004_, lean_object* v_get_2005_, lean_object* v_x_2006_, lean_object* v_iniPos_2007_){
_start:
{
lean_object* v___f_2008_; lean_object* v___f_2009_; lean_object* v___x_2010_; 
v___f_2008_ = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2008_, 0, v_iniPos_2007_);
lean_closure_set(v___f_2008_, 1, v_toPure_2003_);
lean_inc(v_toBind_2004_);
v___f_2009_ = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2009_, 0, v_toBind_2004_);
lean_closure_set(v___f_2009_, 1, v_get_2005_);
lean_closure_set(v___f_2009_, 2, v___f_2008_);
v___x_2010_ = lean_apply_4(v_toBind_2004_, lean_box(0), lean_box(0), v_x_2006_, v___f_2009_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg(lean_object* v_inst_2011_, lean_object* v_inst_2012_, lean_object* v_x_2013_){
_start:
{
lean_object* v_toApplicative_2014_; lean_object* v_toFunctor_2015_; lean_object* v_toBind_2016_; lean_object* v_toPure_2017_; lean_object* v_map_2018_; lean_object* v_get_2019_; lean_object* v___f_2020_; lean_object* v___f_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v_toApplicative_2014_ = lean_ctor_get(v_inst_2011_, 0);
lean_inc_ref(v_toApplicative_2014_);
v_toFunctor_2015_ = lean_ctor_get(v_toApplicative_2014_, 0);
lean_inc_ref(v_toFunctor_2015_);
v_toBind_2016_ = lean_ctor_get(v_inst_2011_, 1);
lean_inc_n(v_toBind_2016_, 2);
lean_dec_ref(v_inst_2011_);
v_toPure_2017_ = lean_ctor_get(v_toApplicative_2014_, 1);
lean_inc(v_toPure_2017_);
lean_dec_ref(v_toApplicative_2014_);
v_map_2018_ = lean_ctor_get(v_toFunctor_2015_, 0);
lean_inc(v_map_2018_);
lean_dec_ref(v_toFunctor_2015_);
v_get_2019_ = lean_ctor_get(v_inst_2012_, 0);
lean_inc_n(v_get_2019_, 2);
lean_dec_ref(v_inst_2012_);
v___f_2020_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2021_ = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2021_, 0, v_toPure_2017_);
lean_closure_set(v___f_2021_, 1, v_toBind_2016_);
lean_closure_set(v___f_2021_, 2, v_get_2019_);
lean_closure_set(v___f_2021_, 3, v_x_2013_);
v___x_2022_ = lean_apply_4(v_map_2018_, lean_box(0), lean_box(0), v___f_2020_, v_get_2019_);
v___x_2023_ = lean_apply_4(v_toBind_2016_, lean_box(0), lean_box(0), v___x_2022_, v___f_2021_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog(lean_object* v_m_2024_, lean_object* v_inst_2025_, lean_object* v_inst_2026_, lean_object* v_x_2027_){
_start:
{
lean_object* v_toApplicative_2028_; lean_object* v_toFunctor_2029_; lean_object* v_toBind_2030_; lean_object* v_toPure_2031_; lean_object* v_map_2032_; lean_object* v_get_2033_; lean_object* v___f_2034_; lean_object* v___f_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v_toApplicative_2028_ = lean_ctor_get(v_inst_2025_, 0);
lean_inc_ref(v_toApplicative_2028_);
v_toFunctor_2029_ = lean_ctor_get(v_toApplicative_2028_, 0);
lean_inc_ref(v_toFunctor_2029_);
v_toBind_2030_ = lean_ctor_get(v_inst_2025_, 1);
lean_inc_n(v_toBind_2030_, 2);
lean_dec_ref(v_inst_2025_);
v_toPure_2031_ = lean_ctor_get(v_toApplicative_2028_, 1);
lean_inc(v_toPure_2031_);
lean_dec_ref(v_toApplicative_2028_);
v_map_2032_ = lean_ctor_get(v_toFunctor_2029_, 0);
lean_inc(v_map_2032_);
lean_dec_ref(v_toFunctor_2029_);
v_get_2033_ = lean_ctor_get(v_inst_2026_, 0);
lean_inc_n(v_get_2033_, 2);
lean_dec_ref(v_inst_2026_);
v___f_2034_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2035_ = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2035_, 0, v_toPure_2031_);
lean_closure_set(v___f_2035_, 1, v_toBind_2030_);
lean_closure_set(v___f_2035_, 2, v_get_2033_);
lean_closure_set(v___f_2035_, 3, v_x_2027_);
v___x_2036_ = lean_apply_4(v_map_2032_, lean_box(0), lean_box(0), v___f_2034_, v_get_2033_);
v___x_2037_ = lean_apply_4(v_toBind_2030_, lean_box(0), lean_box(0), v___x_2036_, v___f_2035_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__1(lean_object* v_iniPos_2038_, lean_object* v_a_2039_, lean_object* v_toPure_2040_, lean_object* v_log_2041_){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2042_ = lean_array_get_size(v_log_2041_);
v___x_2043_ = l_Array_extract___redArg(v_log_2041_, v_iniPos_2038_, v___x_2042_);
v___x_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2044_, 0, v_a_2039_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
v___x_2045_ = lean_apply_2(v_toPure_2040_, lean_box(0), v___x_2044_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__1___boxed(lean_object* v_iniPos_2046_, lean_object* v_a_2047_, lean_object* v_toPure_2048_, lean_object* v_log_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_Lake_withExtractLog___redArg___lam__1(v_iniPos_2046_, v_a_2047_, v_toPure_2048_, v_log_2049_);
lean_dec_ref(v_log_2049_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__0(lean_object* v_iniPos_2051_, lean_object* v_toPure_2052_, lean_object* v_toBind_2053_, lean_object* v_get_2054_, lean_object* v_a_2055_){
_start:
{
lean_object* v___f_2056_; lean_object* v___x_2057_; 
v___f_2056_ = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2056_, 0, v_iniPos_2051_);
lean_closure_set(v___f_2056_, 1, v_a_2055_);
lean_closure_set(v___f_2056_, 2, v_toPure_2052_);
v___x_2057_ = lean_apply_4(v_toBind_2053_, lean_box(0), lean_box(0), v_get_2054_, v___f_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__2(lean_object* v_toPure_2058_, lean_object* v_toBind_2059_, lean_object* v_get_2060_, lean_object* v_x_2061_, lean_object* v_iniPos_2062_){
_start:
{
lean_object* v___f_2063_; lean_object* v___x_2064_; 
lean_inc(v_toBind_2059_);
v___f_2063_ = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2063_, 0, v_iniPos_2062_);
lean_closure_set(v___f_2063_, 1, v_toPure_2058_);
lean_closure_set(v___f_2063_, 2, v_toBind_2059_);
lean_closure_set(v___f_2063_, 3, v_get_2060_);
v___x_2064_ = lean_apply_4(v_toBind_2059_, lean_box(0), lean_box(0), v_x_2061_, v___f_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg(lean_object* v_inst_2065_, lean_object* v_inst_2066_, lean_object* v_x_2067_){
_start:
{
lean_object* v_toApplicative_2068_; lean_object* v_toFunctor_2069_; lean_object* v_toBind_2070_; lean_object* v_toPure_2071_; lean_object* v_map_2072_; lean_object* v_get_2073_; lean_object* v___f_2074_; lean_object* v___f_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v_toApplicative_2068_ = lean_ctor_get(v_inst_2065_, 0);
lean_inc_ref(v_toApplicative_2068_);
v_toFunctor_2069_ = lean_ctor_get(v_toApplicative_2068_, 0);
lean_inc_ref(v_toFunctor_2069_);
v_toBind_2070_ = lean_ctor_get(v_inst_2065_, 1);
lean_inc_n(v_toBind_2070_, 2);
lean_dec_ref(v_inst_2065_);
v_toPure_2071_ = lean_ctor_get(v_toApplicative_2068_, 1);
lean_inc(v_toPure_2071_);
lean_dec_ref(v_toApplicative_2068_);
v_map_2072_ = lean_ctor_get(v_toFunctor_2069_, 0);
lean_inc(v_map_2072_);
lean_dec_ref(v_toFunctor_2069_);
v_get_2073_ = lean_ctor_get(v_inst_2066_, 0);
lean_inc_n(v_get_2073_, 2);
lean_dec_ref(v_inst_2066_);
v___f_2074_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2075_ = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2075_, 0, v_toPure_2071_);
lean_closure_set(v___f_2075_, 1, v_toBind_2070_);
lean_closure_set(v___f_2075_, 2, v_get_2073_);
lean_closure_set(v___f_2075_, 3, v_x_2067_);
v___x_2076_ = lean_apply_4(v_map_2072_, lean_box(0), lean_box(0), v___f_2074_, v_get_2073_);
v___x_2077_ = lean_apply_4(v_toBind_2070_, lean_box(0), lean_box(0), v___x_2076_, v___f_2075_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog(lean_object* v_m_2078_, lean_object* v_00_u03b1_2079_, lean_object* v_inst_2080_, lean_object* v_inst_2081_, lean_object* v_x_2082_){
_start:
{
lean_object* v_toApplicative_2083_; lean_object* v_toFunctor_2084_; lean_object* v_toBind_2085_; lean_object* v_toPure_2086_; lean_object* v_map_2087_; lean_object* v_get_2088_; lean_object* v___f_2089_; lean_object* v___f_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v_toApplicative_2083_ = lean_ctor_get(v_inst_2080_, 0);
lean_inc_ref(v_toApplicative_2083_);
v_toFunctor_2084_ = lean_ctor_get(v_toApplicative_2083_, 0);
lean_inc_ref(v_toFunctor_2084_);
v_toBind_2085_ = lean_ctor_get(v_inst_2080_, 1);
lean_inc_n(v_toBind_2085_, 2);
lean_dec_ref(v_inst_2080_);
v_toPure_2086_ = lean_ctor_get(v_toApplicative_2083_, 1);
lean_inc(v_toPure_2086_);
lean_dec_ref(v_toApplicative_2083_);
v_map_2087_ = lean_ctor_get(v_toFunctor_2084_, 0);
lean_inc(v_map_2087_);
lean_dec_ref(v_toFunctor_2084_);
v_get_2088_ = lean_ctor_get(v_inst_2081_, 0);
lean_inc_n(v_get_2088_, 2);
lean_dec_ref(v_inst_2081_);
v___f_2089_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2090_ = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2090_, 0, v_toPure_2086_);
lean_closure_set(v___f_2090_, 1, v_toBind_2085_);
lean_closure_set(v___f_2090_, 2, v_get_2088_);
lean_closure_set(v___f_2090_, 3, v_x_2082_);
v___x_2091_ = lean_apply_4(v_map_2087_, lean_box(0), lean_box(0), v___f_2089_, v_get_2088_);
v___x_2092_ = lean_apply_4(v_toBind_2085_, lean_box(0), lean_box(0), v___x_2091_, v___f_2090_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__1(lean_object* v_iniPos_2093_, lean_object* v_inst_2094_, lean_object* v_toPure_2095_, lean_object* v_a_2096_, lean_object* v_endPos_2097_){
_start:
{
uint8_t v___x_2098_; 
v___x_2098_ = lean_nat_dec_eq(v_iniPos_2093_, v_endPos_2097_);
if (v___x_2098_ == 0)
{
lean_object* v_throw_2099_; lean_object* v___x_2100_; 
lean_dec(v_a_2096_);
lean_dec(v_toPure_2095_);
v_throw_2099_ = lean_ctor_get(v_inst_2094_, 0);
lean_inc(v_throw_2099_);
lean_dec_ref(v_inst_2094_);
v___x_2100_ = lean_apply_2(v_throw_2099_, lean_box(0), v_iniPos_2093_);
return v___x_2100_;
}
else
{
lean_object* v___x_2101_; 
lean_dec_ref(v_inst_2094_);
lean_dec(v_iniPos_2093_);
v___x_2101_ = lean_apply_2(v_toPure_2095_, lean_box(0), v_a_2096_);
return v___x_2101_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__1___boxed(lean_object* v_iniPos_2102_, lean_object* v_inst_2103_, lean_object* v_toPure_2104_, lean_object* v_a_2105_, lean_object* v_endPos_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l_Lake_throwIfLogs___redArg___lam__1(v_iniPos_2102_, v_inst_2103_, v_toPure_2104_, v_a_2105_, v_endPos_2106_);
lean_dec(v_endPos_2106_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__0(lean_object* v_iniPos_2108_, lean_object* v_inst_2109_, lean_object* v_toPure_2110_, lean_object* v_toBind_2111_, lean_object* v___x_2112_, lean_object* v_a_2113_){
_start:
{
lean_object* v___f_2114_; lean_object* v___x_2115_; 
v___f_2114_ = lean_alloc_closure((void*)(l_Lake_throwIfLogs___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2114_, 0, v_iniPos_2108_);
lean_closure_set(v___f_2114_, 1, v_inst_2109_);
lean_closure_set(v___f_2114_, 2, v_toPure_2110_);
lean_closure_set(v___f_2114_, 3, v_a_2113_);
v___x_2115_ = lean_apply_4(v_toBind_2111_, lean_box(0), lean_box(0), v___x_2112_, v___f_2114_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__2(lean_object* v_inst_2116_, lean_object* v_toPure_2117_, lean_object* v_toBind_2118_, lean_object* v___x_2119_, lean_object* v_x_2120_, lean_object* v_iniPos_2121_){
_start:
{
lean_object* v___f_2122_; lean_object* v___x_2123_; 
lean_inc(v_toBind_2118_);
v___f_2122_ = lean_alloc_closure((void*)(l_Lake_throwIfLogs___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2122_, 0, v_iniPos_2121_);
lean_closure_set(v___f_2122_, 1, v_inst_2116_);
lean_closure_set(v___f_2122_, 2, v_toPure_2117_);
lean_closure_set(v___f_2122_, 3, v_toBind_2118_);
lean_closure_set(v___f_2122_, 4, v___x_2119_);
v___x_2123_ = lean_apply_4(v_toBind_2118_, lean_box(0), lean_box(0), v_x_2120_, v___f_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg(lean_object* v_inst_2124_, lean_object* v_inst_2125_, lean_object* v_inst_2126_, lean_object* v_x_2127_){
_start:
{
lean_object* v_toApplicative_2128_; lean_object* v_toFunctor_2129_; lean_object* v_toBind_2130_; lean_object* v_toPure_2131_; lean_object* v_map_2132_; lean_object* v_get_2133_; lean_object* v___f_2134_; lean_object* v___x_2135_; lean_object* v___f_2136_; lean_object* v___x_2137_; 
v_toApplicative_2128_ = lean_ctor_get(v_inst_2124_, 0);
lean_inc_ref(v_toApplicative_2128_);
v_toFunctor_2129_ = lean_ctor_get(v_toApplicative_2128_, 0);
lean_inc_ref(v_toFunctor_2129_);
v_toBind_2130_ = lean_ctor_get(v_inst_2124_, 1);
lean_inc_n(v_toBind_2130_, 2);
lean_dec_ref(v_inst_2124_);
v_toPure_2131_ = lean_ctor_get(v_toApplicative_2128_, 1);
lean_inc(v_toPure_2131_);
lean_dec_ref(v_toApplicative_2128_);
v_map_2132_ = lean_ctor_get(v_toFunctor_2129_, 0);
lean_inc(v_map_2132_);
lean_dec_ref(v_toFunctor_2129_);
v_get_2133_ = lean_ctor_get(v_inst_2125_, 0);
lean_inc(v_get_2133_);
lean_dec_ref(v_inst_2125_);
v___f_2134_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_2135_ = lean_apply_4(v_map_2132_, lean_box(0), lean_box(0), v___f_2134_, v_get_2133_);
lean_inc(v___x_2135_);
v___f_2136_ = lean_alloc_closure((void*)(l_Lake_throwIfLogs___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2136_, 0, v_inst_2126_);
lean_closure_set(v___f_2136_, 1, v_toPure_2131_);
lean_closure_set(v___f_2136_, 2, v_toBind_2130_);
lean_closure_set(v___f_2136_, 3, v___x_2135_);
lean_closure_set(v___f_2136_, 4, v_x_2127_);
v___x_2137_ = lean_apply_4(v_toBind_2130_, lean_box(0), lean_box(0), v___x_2135_, v___f_2136_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs(lean_object* v_m_2138_, lean_object* v_00_u03b1_2139_, lean_object* v_inst_2140_, lean_object* v_inst_2141_, lean_object* v_inst_2142_, lean_object* v_x_2143_){
_start:
{
lean_object* v_toApplicative_2144_; lean_object* v_toFunctor_2145_; lean_object* v_toBind_2146_; lean_object* v_toPure_2147_; lean_object* v_map_2148_; lean_object* v_get_2149_; lean_object* v___f_2150_; lean_object* v___x_2151_; lean_object* v___f_2152_; lean_object* v___x_2153_; 
v_toApplicative_2144_ = lean_ctor_get(v_inst_2140_, 0);
lean_inc_ref(v_toApplicative_2144_);
v_toFunctor_2145_ = lean_ctor_get(v_toApplicative_2144_, 0);
lean_inc_ref(v_toFunctor_2145_);
v_toBind_2146_ = lean_ctor_get(v_inst_2140_, 1);
lean_inc_n(v_toBind_2146_, 2);
lean_dec_ref(v_inst_2140_);
v_toPure_2147_ = lean_ctor_get(v_toApplicative_2144_, 1);
lean_inc(v_toPure_2147_);
lean_dec_ref(v_toApplicative_2144_);
v_map_2148_ = lean_ctor_get(v_toFunctor_2145_, 0);
lean_inc(v_map_2148_);
lean_dec_ref(v_toFunctor_2145_);
v_get_2149_ = lean_ctor_get(v_inst_2141_, 0);
lean_inc(v_get_2149_);
lean_dec_ref(v_inst_2141_);
v___f_2150_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_2151_ = lean_apply_4(v_map_2148_, lean_box(0), lean_box(0), v___f_2150_, v_get_2149_);
lean_inc(v___x_2151_);
v___f_2152_ = lean_alloc_closure((void*)(l_Lake_throwIfLogs___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2152_, 0, v_inst_2142_);
lean_closure_set(v___f_2152_, 1, v_toPure_2147_);
lean_closure_set(v___f_2152_, 2, v_toBind_2146_);
lean_closure_set(v___f_2152_, 3, v___x_2151_);
lean_closure_set(v___f_2152_, 4, v_x_2143_);
v___x_2153_ = lean_apply_4(v_toBind_2146_, lean_box(0), lean_box(0), v___x_2151_, v___f_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__1(lean_object* v_throw_2154_, lean_object* v_iniPos_2155_, lean_object* v_x_2156_){
_start:
{
lean_object* v___x_2157_; 
v___x_2157_ = lean_apply_2(v_throw_2154_, lean_box(0), v_iniPos_2155_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__1___boxed(lean_object* v_throw_2158_, lean_object* v_iniPos_2159_, lean_object* v_x_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_Lake_withLogErrorPos___redArg___lam__1(v_throw_2158_, v_iniPos_2159_, v_x_2160_);
lean_dec(v_x_2160_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__0(lean_object* v_inst_2162_, lean_object* v_self_2163_, lean_object* v_iniPos_2164_){
_start:
{
lean_object* v_throw_2165_; lean_object* v_tryCatch_2166_; lean_object* v___f_2167_; lean_object* v___x_2168_; 
v_throw_2165_ = lean_ctor_get(v_inst_2162_, 0);
lean_inc(v_throw_2165_);
v_tryCatch_2166_ = lean_ctor_get(v_inst_2162_, 1);
lean_inc(v_tryCatch_2166_);
lean_dec_ref(v_inst_2162_);
v___f_2167_ = lean_alloc_closure((void*)(l_Lake_withLogErrorPos___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2167_, 0, v_throw_2165_);
lean_closure_set(v___f_2167_, 1, v_iniPos_2164_);
v___x_2168_ = lean_apply_3(v_tryCatch_2166_, lean_box(0), v_self_2163_, v___f_2167_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg(lean_object* v_inst_2169_, lean_object* v_inst_2170_, lean_object* v_inst_2171_, lean_object* v_self_2172_){
_start:
{
lean_object* v_toApplicative_2173_; lean_object* v_toFunctor_2174_; lean_object* v_toBind_2175_; lean_object* v_map_2176_; lean_object* v_get_2177_; lean_object* v___f_2178_; lean_object* v___f_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v_toApplicative_2173_ = lean_ctor_get(v_inst_2169_, 0);
v_toFunctor_2174_ = lean_ctor_get(v_toApplicative_2173_, 0);
lean_inc_ref(v_toFunctor_2174_);
v_toBind_2175_ = lean_ctor_get(v_inst_2169_, 1);
lean_inc(v_toBind_2175_);
lean_dec_ref(v_inst_2169_);
v_map_2176_ = lean_ctor_get(v_toFunctor_2174_, 0);
lean_inc(v_map_2176_);
lean_dec_ref(v_toFunctor_2174_);
v_get_2177_ = lean_ctor_get(v_inst_2170_, 0);
lean_inc(v_get_2177_);
lean_dec_ref(v_inst_2170_);
v___f_2178_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2179_ = lean_alloc_closure((void*)(l_Lake_withLogErrorPos___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2179_, 0, v_inst_2171_);
lean_closure_set(v___f_2179_, 1, v_self_2172_);
v___x_2180_ = lean_apply_4(v_map_2176_, lean_box(0), lean_box(0), v___f_2178_, v_get_2177_);
v___x_2181_ = lean_apply_4(v_toBind_2175_, lean_box(0), lean_box(0), v___x_2180_, v___f_2179_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos(lean_object* v_m_2182_, lean_object* v_00_u03b1_2183_, lean_object* v_inst_2184_, lean_object* v_inst_2185_, lean_object* v_inst_2186_, lean_object* v_self_2187_){
_start:
{
lean_object* v_toApplicative_2188_; lean_object* v_toFunctor_2189_; lean_object* v_toBind_2190_; lean_object* v_map_2191_; lean_object* v_get_2192_; lean_object* v___f_2193_; lean_object* v___f_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v_toApplicative_2188_ = lean_ctor_get(v_inst_2184_, 0);
v_toFunctor_2189_ = lean_ctor_get(v_toApplicative_2188_, 0);
lean_inc_ref(v_toFunctor_2189_);
v_toBind_2190_ = lean_ctor_get(v_inst_2184_, 1);
lean_inc(v_toBind_2190_);
lean_dec_ref(v_inst_2184_);
v_map_2191_ = lean_ctor_get(v_toFunctor_2189_, 0);
lean_inc(v_map_2191_);
lean_dec_ref(v_toFunctor_2189_);
v_get_2192_ = lean_ctor_get(v_inst_2185_, 0);
lean_inc(v_get_2192_);
lean_dec_ref(v_inst_2185_);
v___f_2193_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2194_ = lean_alloc_closure((void*)(l_Lake_withLogErrorPos___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2194_, 0, v_inst_2186_);
lean_closure_set(v___f_2194_, 1, v_self_2187_);
v___x_2195_ = lean_apply_4(v_map_2191_, lean_box(0), lean_box(0), v___f_2193_, v_get_2192_);
v___x_2196_ = lean_apply_4(v_toBind_2190_, lean_box(0), lean_box(0), v___x_2195_, v___f_2194_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__1(lean_object* v_toPure_2197_, lean_object* v_x_2198_){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2199_ = lean_box(0);
v___x_2200_ = lean_apply_2(v_toPure_2197_, lean_box(0), v___x_2199_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__1___boxed(lean_object* v_toPure_2201_, lean_object* v_x_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lake_errorWithLog___redArg___lam__1(v_toPure_2201_, v_x_2202_);
lean_dec(v_x_2202_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__0(lean_object* v_throw_2204_, lean_object* v_iniPos_2205_, lean_object* v_____r_2206_){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = lean_apply_2(v_throw_2204_, lean_box(0), v_iniPos_2205_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__2(lean_object* v_inst_2208_, lean_object* v_self_2209_, lean_object* v___f_2210_, lean_object* v_toBind_2211_, lean_object* v_iniPos_2212_){
_start:
{
lean_object* v_throw_2213_; lean_object* v_tryCatch_2214_; lean_object* v___f_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v_throw_2213_ = lean_ctor_get(v_inst_2208_, 0);
lean_inc(v_throw_2213_);
v_tryCatch_2214_ = lean_ctor_get(v_inst_2208_, 1);
lean_inc(v_tryCatch_2214_);
lean_dec_ref(v_inst_2208_);
v___f_2215_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2215_, 0, v_throw_2213_);
lean_closure_set(v___f_2215_, 1, v_iniPos_2212_);
v___x_2216_ = lean_apply_3(v_tryCatch_2214_, lean_box(0), v_self_2209_, v___f_2210_);
v___x_2217_ = lean_apply_4(v_toBind_2211_, lean_box(0), lean_box(0), v___x_2216_, v___f_2215_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg(lean_object* v_inst_2218_, lean_object* v_inst_2219_, lean_object* v_inst_2220_, lean_object* v_self_2221_){
_start:
{
lean_object* v_toApplicative_2222_; lean_object* v_toFunctor_2223_; lean_object* v_toBind_2224_; lean_object* v_toPure_2225_; lean_object* v_map_2226_; lean_object* v_get_2227_; lean_object* v___f_2228_; lean_object* v___f_2229_; lean_object* v___f_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
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
v___f_2229_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2229_, 0, v_toPure_2225_);
v___f_2230_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2230_, 0, v_inst_2220_);
lean_closure_set(v___f_2230_, 1, v_self_2221_);
lean_closure_set(v___f_2230_, 2, v___f_2229_);
lean_closure_set(v___f_2230_, 3, v_toBind_2224_);
v___x_2231_ = lean_apply_4(v_map_2226_, lean_box(0), lean_box(0), v___f_2228_, v_get_2227_);
v___x_2232_ = lean_apply_4(v_toBind_2224_, lean_box(0), lean_box(0), v___x_2231_, v___f_2230_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog(lean_object* v_m_2233_, lean_object* v_00_u03b2_2234_, lean_object* v_inst_2235_, lean_object* v_inst_2236_, lean_object* v_inst_2237_, lean_object* v_self_2238_){
_start:
{
lean_object* v_toApplicative_2239_; lean_object* v_toFunctor_2240_; lean_object* v_toBind_2241_; lean_object* v_toPure_2242_; lean_object* v_map_2243_; lean_object* v_get_2244_; lean_object* v___f_2245_; lean_object* v___f_2246_; lean_object* v___f_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v_toApplicative_2239_ = lean_ctor_get(v_inst_2235_, 0);
lean_inc_ref(v_toApplicative_2239_);
v_toFunctor_2240_ = lean_ctor_get(v_toApplicative_2239_, 0);
lean_inc_ref(v_toFunctor_2240_);
v_toBind_2241_ = lean_ctor_get(v_inst_2235_, 1);
lean_inc_n(v_toBind_2241_, 2);
lean_dec_ref(v_inst_2235_);
v_toPure_2242_ = lean_ctor_get(v_toApplicative_2239_, 1);
lean_inc(v_toPure_2242_);
lean_dec_ref(v_toApplicative_2239_);
v_map_2243_ = lean_ctor_get(v_toFunctor_2240_, 0);
lean_inc(v_map_2243_);
lean_dec_ref(v_toFunctor_2240_);
v_get_2244_ = lean_ctor_get(v_inst_2236_, 0);
lean_inc(v_get_2244_);
lean_dec_ref(v_inst_2236_);
v___f_2245_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2246_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2246_, 0, v_toPure_2242_);
v___f_2247_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2247_, 0, v_inst_2237_);
lean_closure_set(v___f_2247_, 1, v_self_2238_);
lean_closure_set(v___f_2247_, 2, v___f_2246_);
lean_closure_set(v___f_2247_, 3, v_toBind_2241_);
v___x_2248_ = lean_apply_4(v_map_2243_, lean_box(0), lean_box(0), v___f_2245_, v_get_2244_);
v___x_2249_ = lean_apply_4(v_toBind_2241_, lean_box(0), lean_box(0), v___x_2248_, v___f_2247_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__0(lean_object* v_x_2250_){
_start:
{
lean_object* v_fst_2251_; 
v_fst_2251_ = lean_ctor_get(v_x_2250_, 0);
lean_inc(v_fst_2251_);
return v_fst_2251_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__0___boxed(lean_object* v_x_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_Lake_withLoggedIO___redArg___lam__0(v_x_2252_);
lean_dec_ref(v_x_2252_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__1(lean_object* v_buf_2254_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = lean_st_ref_get(v_buf_2254_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__1___boxed(lean_object* v_buf_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Lake_withLoggedIO___redArg___lam__1(v_buf_2257_);
lean_dec(v_buf_2257_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__2(lean_object* v_toPure_2260_, lean_object* v_a_2261_, lean_object* v_____r_2262_){
_start:
{
lean_object* v___x_2263_; 
v___x_2263_ = lean_apply_2(v_toPure_2260_, lean_box(0), v_a_2261_);
return v___x_2263_;
}
}
static lean_object* _init_l_Lake_withLoggedIO___redArg___lam__3___closed__4(void){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2268_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___lam__3___closed__3));
v___x_2269_ = lean_unsigned_to_nat(46u);
v___x_2270_ = lean_unsigned_to_nat(193u);
v___x_2271_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___lam__3___closed__2));
v___x_2272_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___lam__3___closed__1));
v___x_2273_ = l_mkPanicMessageWithDecl(v___x_2272_, v___x_2271_, v___x_2270_, v___x_2269_, v___x_2268_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__3(lean_object* v___x_2274_, lean_object* v_inst_2275_, lean_object* v_toBind_2276_, lean_object* v___f_2277_, lean_object* v_toPure_2278_, lean_object* v_a_2279_, lean_object* v_buf_2280_){
_start:
{
lean_object* v___y_2282_; lean_object* v_data_2295_; uint8_t v___x_2296_; 
v_data_2295_ = lean_ctor_get(v_buf_2280_, 0);
lean_inc_ref(v_data_2295_);
lean_dec_ref(v_buf_2280_);
v___x_2296_ = lean_string_validate_utf8(v_data_2295_);
if (v___x_2296_ == 0)
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
lean_dec_ref(v_data_2295_);
v___x_2297_ = ((lean_object*)(l_Lake_instInhabitedLogEntry_default___closed__0));
v___x_2298_ = lean_obj_once(&l_Lake_withLoggedIO___redArg___lam__3___closed__4, &l_Lake_withLoggedIO___redArg___lam__3___closed__4_once, _init_l_Lake_withLoggedIO___redArg___lam__3___closed__4);
v___x_2299_ = l_panic___redArg(v___x_2297_, v___x_2298_);
v___y_2282_ = v___x_2299_;
goto v___jp_2281_;
}
else
{
lean_object* v___x_2300_; 
v___x_2300_ = lean_string_from_utf8_unchecked(v_data_2295_);
v___y_2282_ = v___x_2300_;
goto v___jp_2281_;
}
v___jp_2281_:
{
lean_object* v___x_2283_; uint8_t v___x_2284_; 
v___x_2283_ = lean_string_utf8_byte_size(v___y_2282_);
v___x_2284_ = lean_nat_dec_eq(v___x_2283_, v___x_2274_);
if (v___x_2284_ == 0)
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; uint8_t v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
lean_dec(v_a_2279_);
lean_dec(v_toPure_2278_);
v___x_2285_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___lam__3___closed__0));
v___x_2286_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2286_, 0, v___y_2282_);
lean_ctor_set(v___x_2286_, 1, v___x_2274_);
lean_ctor_set(v___x_2286_, 2, v___x_2283_);
v___x_2287_ = l_String_Slice_trimAscii(v___x_2286_);
v___x_2288_ = l_String_Slice_toString(v___x_2287_);
lean_dec_ref(v___x_2287_);
v___x_2289_ = lean_string_append(v___x_2285_, v___x_2288_);
lean_dec_ref(v___x_2288_);
v___x_2290_ = 1;
v___x_2291_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2291_, 0, v___x_2289_);
lean_ctor_set_uint8(v___x_2291_, sizeof(void*)*1, v___x_2290_);
v___x_2292_ = lean_apply_1(v_inst_2275_, v___x_2291_);
v___x_2293_ = lean_apply_4(v_toBind_2276_, lean_box(0), lean_box(0), v___x_2292_, v___f_2277_);
return v___x_2293_;
}
else
{
lean_object* v___x_2294_; 
lean_dec_ref(v___y_2282_);
lean_dec(v___f_2277_);
lean_dec(v_toBind_2276_);
lean_dec(v_inst_2275_);
lean_dec(v___x_2274_);
v___x_2294_ = lean_apply_2(v_toPure_2278_, lean_box(0), v_a_2279_);
return v___x_2294_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__4(lean_object* v_toPure_2301_, lean_object* v___x_2302_, lean_object* v_inst_2303_, lean_object* v_toBind_2304_, lean_object* v_inst_2305_, lean_object* v___f_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v___f_2308_; lean_object* v___f_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
lean_inc(v_a_2307_);
lean_inc(v_toPure_2301_);
v___f_2308_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2308_, 0, v_toPure_2301_);
lean_closure_set(v___f_2308_, 1, v_a_2307_);
lean_inc(v_toBind_2304_);
v___f_2309_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__3), 7, 6);
lean_closure_set(v___f_2309_, 0, v___x_2302_);
lean_closure_set(v___f_2309_, 1, v_inst_2303_);
lean_closure_set(v___f_2309_, 2, v_toBind_2304_);
lean_closure_set(v___f_2309_, 3, v___f_2308_);
lean_closure_set(v___f_2309_, 4, v_toPure_2301_);
lean_closure_set(v___f_2309_, 5, v_a_2307_);
v___x_2310_ = lean_apply_2(v_inst_2305_, lean_box(0), v___f_2306_);
v___x_2311_ = lean_apply_4(v_toBind_2304_, lean_box(0), lean_box(0), v___x_2310_, v___f_2309_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__5(lean_object* v_stderr_2312_, lean_object* v_inst_2313_, lean_object* v_mapConst_2314_, lean_object* v_____r_2315_){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2316_ = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(v___x_2316_, 0, v_stderr_2312_);
v___x_2317_ = lean_apply_2(v_inst_2313_, lean_box(0), v___x_2316_);
v___x_2318_ = lean_box(0);
v___x_2319_ = lean_apply_4(v_mapConst_2314_, lean_box(0), lean_box(0), v___x_2318_, v___x_2317_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__6(lean_object* v___x_2320_, lean_object* v_x_2321_){
_start:
{
lean_inc(v___x_2320_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__6___boxed(lean_object* v___x_2322_, lean_object* v_x_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Lake_withLoggedIO___redArg___lam__6(v___x_2322_, v_x_2323_);
lean_dec(v_x_2323_);
lean_dec(v___x_2322_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__7(lean_object* v_toFunctor_2325_, lean_object* v_inst_2326_, lean_object* v_stdout_2327_, lean_object* v_toBind_2328_, lean_object* v_inst_2329_, lean_object* v_x_2330_, lean_object* v___f_2331_, lean_object* v___f_2332_, lean_object* v_stderr_2333_){
_start:
{
lean_object* v_map_2334_; lean_object* v_mapConst_2335_; lean_object* v___f_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___f_2342_; lean_object* v_y_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v_map_2334_ = lean_ctor_get(v_toFunctor_2325_, 0);
lean_inc(v_map_2334_);
v_mapConst_2335_ = lean_ctor_get(v_toFunctor_2325_, 1);
lean_inc_n(v_mapConst_2335_, 2);
lean_dec_ref(v_toFunctor_2325_);
lean_inc(v_inst_2326_);
v___f_2336_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__5), 4, 3);
lean_closure_set(v___f_2336_, 0, v_stderr_2333_);
lean_closure_set(v___f_2336_, 1, v_inst_2326_);
lean_closure_set(v___f_2336_, 2, v_mapConst_2335_);
v___x_2337_ = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(v___x_2337_, 0, v_stdout_2327_);
v___x_2338_ = lean_apply_2(v_inst_2326_, lean_box(0), v___x_2337_);
v___x_2339_ = lean_box(0);
v___x_2340_ = lean_apply_4(v_mapConst_2335_, lean_box(0), lean_box(0), v___x_2339_, v___x_2338_);
lean_inc(v_toBind_2328_);
v___x_2341_ = lean_apply_4(v_toBind_2328_, lean_box(0), lean_box(0), v___x_2340_, v___f_2336_);
v___f_2342_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__6___boxed), 2, 1);
lean_closure_set(v___f_2342_, 0, v___x_2341_);
v_y_2343_ = lean_apply_4(v_inst_2329_, lean_box(0), lean_box(0), v_x_2330_, v___f_2342_);
v___x_2344_ = lean_apply_4(v_map_2334_, lean_box(0), lean_box(0), v___f_2331_, v_y_2343_);
v___x_2345_ = lean_apply_4(v_toBind_2328_, lean_box(0), lean_box(0), v___x_2344_, v___f_2332_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__8(lean_object* v_toFunctor_2346_, lean_object* v_inst_2347_, lean_object* v_toBind_2348_, lean_object* v_inst_2349_, lean_object* v_x_2350_, lean_object* v___f_2351_, lean_object* v___f_2352_, lean_object* v___x_2353_, lean_object* v_stdout_2354_){
_start:
{
lean_object* v___f_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
lean_inc(v_toBind_2348_);
lean_inc(v_inst_2347_);
v___f_2355_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__7), 9, 8);
lean_closure_set(v___f_2355_, 0, v_toFunctor_2346_);
lean_closure_set(v___f_2355_, 1, v_inst_2347_);
lean_closure_set(v___f_2355_, 2, v_stdout_2354_);
lean_closure_set(v___f_2355_, 3, v_toBind_2348_);
lean_closure_set(v___f_2355_, 4, v_inst_2349_);
lean_closure_set(v___f_2355_, 5, v_x_2350_);
lean_closure_set(v___f_2355_, 6, v___f_2351_);
lean_closure_set(v___f_2355_, 7, v___f_2352_);
v___x_2356_ = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(v___x_2356_, 0, v___x_2353_);
v___x_2357_ = lean_apply_2(v_inst_2347_, lean_box(0), v___x_2356_);
v___x_2358_ = lean_apply_4(v_toBind_2348_, lean_box(0), lean_box(0), v___x_2357_, v___f_2355_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__9(lean_object* v_toPure_2359_, lean_object* v___x_2360_, lean_object* v_inst_2361_, lean_object* v_toBind_2362_, lean_object* v_inst_2363_, lean_object* v_toFunctor_2364_, lean_object* v_inst_2365_, lean_object* v_x_2366_, lean_object* v___f_2367_, lean_object* v_buf_2368_){
_start:
{
lean_object* v___f_2369_; lean_object* v___f_2370_; lean_object* v___x_2371_; lean_object* v___f_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
lean_inc(v_buf_2368_);
v___f_2369_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2369_, 0, v_buf_2368_);
lean_inc_n(v_inst_2363_, 2);
lean_inc_n(v_toBind_2362_, 2);
v___f_2370_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__4), 7, 6);
lean_closure_set(v___f_2370_, 0, v_toPure_2359_);
lean_closure_set(v___f_2370_, 1, v___x_2360_);
lean_closure_set(v___f_2370_, 2, v_inst_2361_);
lean_closure_set(v___f_2370_, 3, v_toBind_2362_);
lean_closure_set(v___f_2370_, 4, v_inst_2363_);
lean_closure_set(v___f_2370_, 5, v___f_2369_);
v___x_2371_ = l_IO_FS_Stream_ofBuffer(v_buf_2368_);
lean_inc_ref(v___x_2371_);
v___f_2372_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__8), 9, 8);
lean_closure_set(v___f_2372_, 0, v_toFunctor_2364_);
lean_closure_set(v___f_2372_, 1, v_inst_2363_);
lean_closure_set(v___f_2372_, 2, v_toBind_2362_);
lean_closure_set(v___f_2372_, 3, v_inst_2365_);
lean_closure_set(v___f_2372_, 4, v_x_2366_);
lean_closure_set(v___f_2372_, 5, v___f_2367_);
lean_closure_set(v___f_2372_, 6, v___f_2370_);
lean_closure_set(v___f_2372_, 7, v___x_2371_);
v___x_2373_ = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(v___x_2373_, 0, v___x_2371_);
v___x_2374_ = lean_apply_2(v_inst_2363_, lean_box(0), v___x_2373_);
v___x_2375_ = lean_apply_4(v_toBind_2362_, lean_box(0), lean_box(0), v___x_2374_, v___f_2372_);
return v___x_2375_;
}
}
static lean_object* _init_l_Lake_withLoggedIO___redArg___closed__1(void){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2377_ = lean_unsigned_to_nat(0u);
v___x_2378_ = l_ByteArray_empty;
v___x_2379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2378_);
lean_ctor_set(v___x_2379_, 1, v___x_2377_);
return v___x_2379_;
}
}
static lean_object* _init_l_Lake_withLoggedIO___redArg___closed__2(void){
_start:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2380_ = lean_obj_once(&l_Lake_withLoggedIO___redArg___closed__1, &l_Lake_withLoggedIO___redArg___closed__1_once, _init_l_Lake_withLoggedIO___redArg___closed__1);
v___x_2381_ = lean_alloc_closure((void*)(l_IO_mkRef___boxed), 3, 2);
lean_closure_set(v___x_2381_, 0, lean_box(0));
lean_closure_set(v___x_2381_, 1, v___x_2380_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg(lean_object* v_inst_2382_, lean_object* v_inst_2383_, lean_object* v_inst_2384_, lean_object* v_inst_2385_, lean_object* v_x_2386_){
_start:
{
lean_object* v_toApplicative_2387_; lean_object* v_toBind_2388_; lean_object* v_toFunctor_2389_; lean_object* v_toPure_2390_; lean_object* v___f_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___f_2395_; lean_object* v___x_2396_; 
v_toApplicative_2387_ = lean_ctor_get(v_inst_2382_, 0);
lean_inc_ref(v_toApplicative_2387_);
v_toBind_2388_ = lean_ctor_get(v_inst_2382_, 1);
lean_inc_n(v_toBind_2388_, 2);
lean_dec_ref(v_inst_2382_);
v_toFunctor_2389_ = lean_ctor_get(v_toApplicative_2387_, 0);
lean_inc_ref(v_toFunctor_2389_);
v_toPure_2390_ = lean_ctor_get(v_toApplicative_2387_, 1);
lean_inc(v_toPure_2390_);
lean_dec_ref(v_toApplicative_2387_);
v___f_2391_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___closed__0));
v___x_2392_ = lean_unsigned_to_nat(0u);
v___x_2393_ = lean_obj_once(&l_Lake_withLoggedIO___redArg___closed__2, &l_Lake_withLoggedIO___redArg___closed__2_once, _init_l_Lake_withLoggedIO___redArg___closed__2);
lean_inc(v_inst_2383_);
v___x_2394_ = lean_apply_2(v_inst_2383_, lean_box(0), v___x_2393_);
v___f_2395_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__9), 10, 9);
lean_closure_set(v___f_2395_, 0, v_toPure_2390_);
lean_closure_set(v___f_2395_, 1, v___x_2392_);
lean_closure_set(v___f_2395_, 2, v_inst_2384_);
lean_closure_set(v___f_2395_, 3, v_toBind_2388_);
lean_closure_set(v___f_2395_, 4, v_inst_2383_);
lean_closure_set(v___f_2395_, 5, v_toFunctor_2389_);
lean_closure_set(v___f_2395_, 6, v_inst_2385_);
lean_closure_set(v___f_2395_, 7, v_x_2386_);
lean_closure_set(v___f_2395_, 8, v___f_2391_);
v___x_2396_ = lean_apply_4(v_toBind_2388_, lean_box(0), lean_box(0), v___x_2394_, v___f_2395_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO(lean_object* v_m_2397_, lean_object* v_00_u03b1_2398_, lean_object* v_inst_2399_, lean_object* v_inst_2400_, lean_object* v_inst_2401_, lean_object* v_inst_2402_, lean_object* v_x_2403_){
_start:
{
lean_object* v_toApplicative_2404_; lean_object* v_toBind_2405_; lean_object* v_toFunctor_2406_; lean_object* v_toPure_2407_; lean_object* v___f_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___f_2412_; lean_object* v___x_2413_; 
v_toApplicative_2404_ = lean_ctor_get(v_inst_2399_, 0);
lean_inc_ref(v_toApplicative_2404_);
v_toBind_2405_ = lean_ctor_get(v_inst_2399_, 1);
lean_inc_n(v_toBind_2405_, 2);
lean_dec_ref(v_inst_2399_);
v_toFunctor_2406_ = lean_ctor_get(v_toApplicative_2404_, 0);
lean_inc_ref(v_toFunctor_2406_);
v_toPure_2407_ = lean_ctor_get(v_toApplicative_2404_, 1);
lean_inc(v_toPure_2407_);
lean_dec_ref(v_toApplicative_2404_);
v___f_2408_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___closed__0));
v___x_2409_ = lean_unsigned_to_nat(0u);
v___x_2410_ = lean_obj_once(&l_Lake_withLoggedIO___redArg___closed__2, &l_Lake_withLoggedIO___redArg___closed__2_once, _init_l_Lake_withLoggedIO___redArg___closed__2);
lean_inc(v_inst_2400_);
v___x_2411_ = lean_apply_2(v_inst_2400_, lean_box(0), v___x_2410_);
v___f_2412_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__9), 10, 9);
lean_closure_set(v___f_2412_, 0, v_toPure_2407_);
lean_closure_set(v___f_2412_, 1, v___x_2409_);
lean_closure_set(v___f_2412_, 2, v_inst_2401_);
lean_closure_set(v___f_2412_, 3, v_toBind_2405_);
lean_closure_set(v___f_2412_, 4, v_inst_2400_);
lean_closure_set(v___f_2412_, 5, v_toFunctor_2406_);
lean_closure_set(v___f_2412_, 6, v_inst_2402_);
lean_closure_set(v___f_2412_, 7, v_x_2403_);
lean_closure_set(v___f_2412_, 8, v___f_2408_);
v___x_2413_ = lean_apply_4(v_toBind_2405_, lean_box(0), lean_box(0), v___x_2411_, v___f_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_error___redArg___lam__3(lean_object* v_inst_2414_, lean_object* v___x_2415_, lean_object* v___f_2416_, lean_object* v_toBind_2417_, lean_object* v_iniPos_2418_){
_start:
{
lean_object* v_throw_2419_; lean_object* v_tryCatch_2420_; lean_object* v___f_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v_throw_2419_ = lean_ctor_get(v_inst_2414_, 0);
lean_inc(v_throw_2419_);
v_tryCatch_2420_ = lean_ctor_get(v_inst_2414_, 1);
lean_inc(v_tryCatch_2420_);
lean_dec_ref(v_inst_2414_);
v___f_2421_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2421_, 0, v_throw_2419_);
lean_closure_set(v___f_2421_, 1, v_iniPos_2418_);
v___x_2422_ = lean_apply_3(v_tryCatch_2420_, lean_box(0), v___x_2415_, v___f_2416_);
v___x_2423_ = lean_apply_4(v_toBind_2417_, lean_box(0), lean_box(0), v___x_2422_, v___f_2421_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_error___redArg(lean_object* v_inst_2424_, lean_object* v_inst_2425_, lean_object* v_inst_2426_, lean_object* v_inst_2427_, lean_object* v_msg_2428_){
_start:
{
lean_object* v_toApplicative_2429_; lean_object* v_toFunctor_2430_; lean_object* v_toBind_2431_; lean_object* v_toPure_2432_; lean_object* v_map_2433_; lean_object* v_get_2434_; lean_object* v___f_2435_; uint8_t v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___f_2439_; lean_object* v___f_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v_toApplicative_2429_ = lean_ctor_get(v_inst_2424_, 0);
lean_inc_ref(v_toApplicative_2429_);
v_toFunctor_2430_ = lean_ctor_get(v_toApplicative_2429_, 0);
lean_inc_ref(v_toFunctor_2430_);
v_toBind_2431_ = lean_ctor_get(v_inst_2424_, 1);
lean_inc_n(v_toBind_2431_, 2);
lean_dec_ref(v_inst_2424_);
v_toPure_2432_ = lean_ctor_get(v_toApplicative_2429_, 1);
lean_inc(v_toPure_2432_);
lean_dec_ref(v_toApplicative_2429_);
v_map_2433_ = lean_ctor_get(v_toFunctor_2430_, 0);
lean_inc(v_map_2433_);
lean_dec_ref(v_toFunctor_2430_);
v_get_2434_ = lean_ctor_get(v_inst_2426_, 0);
lean_inc(v_get_2434_);
lean_dec_ref(v_inst_2426_);
v___f_2435_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_2436_ = 3;
v___x_2437_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2437_, 0, v_msg_2428_);
lean_ctor_set_uint8(v___x_2437_, sizeof(void*)*1, v___x_2436_);
v___x_2438_ = lean_apply_1(v_inst_2425_, v___x_2437_);
v___f_2439_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2439_, 0, v_toPure_2432_);
v___f_2440_ = lean_alloc_closure((void*)(l_Lake_ELog_error___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2440_, 0, v_inst_2427_);
lean_closure_set(v___f_2440_, 1, v___x_2438_);
lean_closure_set(v___f_2440_, 2, v___f_2439_);
lean_closure_set(v___f_2440_, 3, v_toBind_2431_);
v___x_2441_ = lean_apply_4(v_map_2433_, lean_box(0), lean_box(0), v___f_2435_, v_get_2434_);
v___x_2442_ = lean_apply_4(v_toBind_2431_, lean_box(0), lean_box(0), v___x_2441_, v___f_2440_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_error(lean_object* v_m_2443_, lean_object* v_00_u03b1_2444_, lean_object* v_inst_2445_, lean_object* v_inst_2446_, lean_object* v_inst_2447_, lean_object* v_inst_2448_, lean_object* v_msg_2449_){
_start:
{
lean_object* v_toApplicative_2450_; lean_object* v_toFunctor_2451_; lean_object* v_toBind_2452_; lean_object* v_toPure_2453_; lean_object* v_map_2454_; lean_object* v_get_2455_; lean_object* v___f_2456_; uint8_t v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___f_2460_; lean_object* v___f_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v_toApplicative_2450_ = lean_ctor_get(v_inst_2445_, 0);
lean_inc_ref(v_toApplicative_2450_);
v_toFunctor_2451_ = lean_ctor_get(v_toApplicative_2450_, 0);
lean_inc_ref(v_toFunctor_2451_);
v_toBind_2452_ = lean_ctor_get(v_inst_2445_, 1);
lean_inc_n(v_toBind_2452_, 2);
lean_dec_ref(v_inst_2445_);
v_toPure_2453_ = lean_ctor_get(v_toApplicative_2450_, 1);
lean_inc(v_toPure_2453_);
lean_dec_ref(v_toApplicative_2450_);
v_map_2454_ = lean_ctor_get(v_toFunctor_2451_, 0);
lean_inc(v_map_2454_);
lean_dec_ref(v_toFunctor_2451_);
v_get_2455_ = lean_ctor_get(v_inst_2447_, 0);
lean_inc(v_get_2455_);
lean_dec_ref(v_inst_2447_);
v___f_2456_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_2457_ = 3;
v___x_2458_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2458_, 0, v_msg_2449_);
lean_ctor_set_uint8(v___x_2458_, sizeof(void*)*1, v___x_2457_);
v___x_2459_ = lean_apply_1(v_inst_2446_, v___x_2458_);
v___f_2460_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2460_, 0, v_toPure_2453_);
v___f_2461_ = lean_alloc_closure((void*)(l_Lake_ELog_error___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2461_, 0, v_inst_2448_);
lean_closure_set(v___f_2461_, 1, v___x_2459_);
lean_closure_set(v___f_2461_, 2, v___f_2460_);
lean_closure_set(v___f_2461_, 3, v_toBind_2452_);
v___x_2462_ = lean_apply_4(v_map_2454_, lean_box(0), lean_box(0), v___f_2456_, v_get_2455_);
v___x_2463_ = lean_apply_4(v_toBind_2452_, lean_box(0), lean_box(0), v___x_2462_, v___f_2461_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_monadError___redArg___lam__4(lean_object* v_inst_2464_, lean_object* v_inst_2465_, lean_object* v_inst_2466_, lean_object* v_inst_2467_, lean_object* v___f_2468_, lean_object* v_00_u03b1_2469_, lean_object* v___y_2470_){
_start:
{
lean_object* v_toApplicative_2471_; lean_object* v_toFunctor_2472_; lean_object* v_toBind_2473_; lean_object* v_toPure_2474_; lean_object* v_map_2475_; lean_object* v_get_2476_; uint8_t v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___f_2480_; lean_object* v___f_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v_toApplicative_2471_ = lean_ctor_get(v_inst_2464_, 0);
lean_inc_ref(v_toApplicative_2471_);
v_toFunctor_2472_ = lean_ctor_get(v_toApplicative_2471_, 0);
lean_inc_ref(v_toFunctor_2472_);
v_toBind_2473_ = lean_ctor_get(v_inst_2464_, 1);
lean_inc_n(v_toBind_2473_, 2);
lean_dec_ref(v_inst_2464_);
v_toPure_2474_ = lean_ctor_get(v_toApplicative_2471_, 1);
lean_inc(v_toPure_2474_);
lean_dec_ref(v_toApplicative_2471_);
v_map_2475_ = lean_ctor_get(v_toFunctor_2472_, 0);
lean_inc(v_map_2475_);
lean_dec_ref(v_toFunctor_2472_);
v_get_2476_ = lean_ctor_get(v_inst_2465_, 0);
lean_inc(v_get_2476_);
lean_dec_ref(v_inst_2465_);
v___x_2477_ = 3;
v___x_2478_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2478_, 0, v___y_2470_);
lean_ctor_set_uint8(v___x_2478_, sizeof(void*)*1, v___x_2477_);
v___x_2479_ = lean_apply_1(v_inst_2466_, v___x_2478_);
v___f_2480_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2480_, 0, v_toPure_2474_);
v___f_2481_ = lean_alloc_closure((void*)(l_Lake_ELog_error___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2481_, 0, v_inst_2467_);
lean_closure_set(v___f_2481_, 1, v___x_2479_);
lean_closure_set(v___f_2481_, 2, v___f_2480_);
lean_closure_set(v___f_2481_, 3, v_toBind_2473_);
v___x_2482_ = lean_apply_4(v_map_2475_, lean_box(0), lean_box(0), v___f_2468_, v_get_2476_);
v___x_2483_ = lean_apply_4(v_toBind_2473_, lean_box(0), lean_box(0), v___x_2482_, v___f_2481_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_monadError___redArg(lean_object* v_inst_2484_, lean_object* v_inst_2485_, lean_object* v_inst_2486_, lean_object* v_inst_2487_){
_start:
{
lean_object* v___f_2488_; lean_object* v___f_2489_; 
v___f_2488_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2489_ = lean_alloc_closure((void*)(l_Lake_ELog_monadError___redArg___lam__4), 7, 5);
lean_closure_set(v___f_2489_, 0, v_inst_2484_);
lean_closure_set(v___f_2489_, 1, v_inst_2486_);
lean_closure_set(v___f_2489_, 2, v_inst_2485_);
lean_closure_set(v___f_2489_, 3, v_inst_2487_);
lean_closure_set(v___f_2489_, 4, v___f_2488_);
return v___f_2489_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_monadError(lean_object* v_m_2490_, lean_object* v_inst_2491_, lean_object* v_inst_2492_, lean_object* v_inst_2493_, lean_object* v_inst_2494_){
_start:
{
lean_object* v___f_2495_; lean_object* v___f_2496_; 
v___f_2495_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2496_ = lean_alloc_closure((void*)(l_Lake_ELog_monadError___redArg___lam__4), 7, 5);
lean_closure_set(v___f_2496_, 0, v_inst_2491_);
lean_closure_set(v___f_2496_, 1, v_inst_2493_);
lean_closure_set(v___f_2496_, 2, v_inst_2492_);
lean_closure_set(v___f_2496_, 3, v_inst_2494_);
lean_closure_set(v___f_2496_, 4, v___f_2495_);
return v___f_2496_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_failure___redArg___lam__1(lean_object* v_inst_2497_, lean_object* v_____do__lift_2498_){
_start:
{
lean_object* v_throw_2499_; lean_object* v___x_2500_; 
v_throw_2499_ = lean_ctor_get(v_inst_2497_, 0);
lean_inc(v_throw_2499_);
lean_dec_ref(v_inst_2497_);
v___x_2500_ = lean_apply_2(v_throw_2499_, lean_box(0), v_____do__lift_2498_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_failure___redArg(lean_object* v_inst_2501_, lean_object* v_inst_2502_, lean_object* v_inst_2503_){
_start:
{
lean_object* v_toApplicative_2504_; lean_object* v_toFunctor_2505_; lean_object* v_toBind_2506_; lean_object* v_map_2507_; lean_object* v_get_2508_; lean_object* v___f_2509_; lean_object* v___f_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v_toApplicative_2504_ = lean_ctor_get(v_inst_2501_, 0);
v_toFunctor_2505_ = lean_ctor_get(v_toApplicative_2504_, 0);
lean_inc_ref(v_toFunctor_2505_);
v_toBind_2506_ = lean_ctor_get(v_inst_2501_, 1);
lean_inc(v_toBind_2506_);
lean_dec_ref(v_inst_2501_);
v_map_2507_ = lean_ctor_get(v_toFunctor_2505_, 0);
lean_inc(v_map_2507_);
lean_dec_ref(v_toFunctor_2505_);
v_get_2508_ = lean_ctor_get(v_inst_2502_, 0);
lean_inc(v_get_2508_);
lean_dec_ref(v_inst_2502_);
v___f_2509_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2510_ = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2510_, 0, v_inst_2503_);
v___x_2511_ = lean_apply_4(v_map_2507_, lean_box(0), lean_box(0), v___f_2509_, v_get_2508_);
v___x_2512_ = lean_apply_4(v_toBind_2506_, lean_box(0), lean_box(0), v___x_2511_, v___f_2510_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_failure(lean_object* v_m_2513_, lean_object* v_00_u03b1_2514_, lean_object* v_inst_2515_, lean_object* v_inst_2516_, lean_object* v_inst_2517_){
_start:
{
lean_object* v_toApplicative_2518_; lean_object* v_toFunctor_2519_; lean_object* v_toBind_2520_; lean_object* v_map_2521_; lean_object* v_get_2522_; lean_object* v___f_2523_; lean_object* v___f_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v_toApplicative_2518_ = lean_ctor_get(v_inst_2515_, 0);
v_toFunctor_2519_ = lean_ctor_get(v_toApplicative_2518_, 0);
lean_inc_ref(v_toFunctor_2519_);
v_toBind_2520_ = lean_ctor_get(v_inst_2515_, 1);
lean_inc(v_toBind_2520_);
lean_dec_ref(v_inst_2515_);
v_map_2521_ = lean_ctor_get(v_toFunctor_2519_, 0);
lean_inc(v_map_2521_);
lean_dec_ref(v_toFunctor_2519_);
v_get_2522_ = lean_ctor_get(v_inst_2516_, 0);
lean_inc(v_get_2522_);
lean_dec_ref(v_inst_2516_);
v___f_2523_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2524_ = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2524_, 0, v_inst_2517_);
v___x_2525_ = lean_apply_4(v_map_2521_, lean_box(0), lean_box(0), v___f_2523_, v_get_2522_);
v___x_2526_ = lean_apply_4(v_toBind_2520_, lean_box(0), lean_box(0), v___x_2525_, v___f_2524_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__0(lean_object* v_y_2527_, lean_object* v_____r_2528_){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = lean_box(0);
v___x_2530_ = lean_apply_1(v_y_2527_, v___x_2529_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__1(lean_object* v_errPos_2531_, lean_object* v_s_2532_){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2533_ = lean_box(0);
v___x_2534_ = l_Array_shrink___redArg(v_s_2532_, v_errPos_2531_);
v___x_2535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2533_);
lean_ctor_set(v___x_2535_, 1, v___x_2534_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__1___boxed(lean_object* v_errPos_2536_, lean_object* v_s_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Lake_ELog_orElse___redArg___lam__1(v_errPos_2536_, v_s_2537_);
lean_dec(v_errPos_2536_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__2(lean_object* v_inst_2539_, lean_object* v_toBind_2540_, lean_object* v___f_2541_, lean_object* v_errPos_2542_){
_start:
{
lean_object* v_modifyGet_2543_; lean_object* v___f_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v_modifyGet_2543_ = lean_ctor_get(v_inst_2539_, 2);
lean_inc(v_modifyGet_2543_);
lean_dec_ref(v_inst_2539_);
v___f_2544_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2544_, 0, v_errPos_2542_);
v___x_2545_ = lean_apply_2(v_modifyGet_2543_, lean_box(0), v___f_2544_);
v___x_2546_ = lean_apply_4(v_toBind_2540_, lean_box(0), lean_box(0), v___x_2545_, v___f_2541_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg(lean_object* v_inst_2547_, lean_object* v_inst_2548_, lean_object* v_inst_2549_, lean_object* v_x_2550_, lean_object* v_y_2551_){
_start:
{
lean_object* v_toBind_2552_; lean_object* v_tryCatch_2553_; lean_object* v___f_2554_; lean_object* v___f_2555_; lean_object* v___x_2556_; 
v_toBind_2552_ = lean_ctor_get(v_inst_2547_, 1);
lean_inc(v_toBind_2552_);
lean_dec_ref(v_inst_2547_);
v_tryCatch_2553_ = lean_ctor_get(v_inst_2549_, 1);
lean_inc(v_tryCatch_2553_);
lean_dec_ref(v_inst_2549_);
v___f_2554_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2554_, 0, v_y_2551_);
v___f_2555_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2555_, 0, v_inst_2548_);
lean_closure_set(v___f_2555_, 1, v_toBind_2552_);
lean_closure_set(v___f_2555_, 2, v___f_2554_);
v___x_2556_ = lean_apply_3(v_tryCatch_2553_, lean_box(0), v_x_2550_, v___f_2555_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse(lean_object* v_m_2557_, lean_object* v_00_u03b1_2558_, lean_object* v_inst_2559_, lean_object* v_inst_2560_, lean_object* v_inst_2561_, lean_object* v_x_2562_, lean_object* v_y_2563_){
_start:
{
lean_object* v_toBind_2564_; lean_object* v_tryCatch_2565_; lean_object* v___f_2566_; lean_object* v___f_2567_; lean_object* v___x_2568_; 
v_toBind_2564_ = lean_ctor_get(v_inst_2559_, 1);
lean_inc(v_toBind_2564_);
lean_dec_ref(v_inst_2559_);
v_tryCatch_2565_ = lean_ctor_get(v_inst_2561_, 1);
lean_inc(v_tryCatch_2565_);
lean_dec_ref(v_inst_2561_);
v___f_2566_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2566_, 0, v_y_2563_);
v___f_2567_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2567_, 0, v_inst_2560_);
lean_closure_set(v___f_2567_, 1, v_toBind_2564_);
lean_closure_set(v___f_2567_, 2, v___f_2566_);
v___x_2568_ = lean_apply_3(v_tryCatch_2565_, lean_box(0), v_x_2562_, v___f_2567_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__2(lean_object* v_toApplicative_2569_, lean_object* v_inst_2570_, lean_object* v___f_2571_, lean_object* v_toBind_2572_, lean_object* v___f_2573_, lean_object* v_00_u03b1_2574_){
_start:
{
lean_object* v_toFunctor_2575_; lean_object* v_map_2576_; lean_object* v_get_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v_toFunctor_2575_ = lean_ctor_get(v_toApplicative_2569_, 0);
lean_inc_ref(v_toFunctor_2575_);
lean_dec_ref(v_toApplicative_2569_);
v_map_2576_ = lean_ctor_get(v_toFunctor_2575_, 0);
lean_inc(v_map_2576_);
lean_dec_ref(v_toFunctor_2575_);
v_get_2577_ = lean_ctor_get(v_inst_2570_, 0);
lean_inc(v_get_2577_);
lean_dec_ref(v_inst_2570_);
v___x_2578_ = lean_apply_4(v_map_2576_, lean_box(0), lean_box(0), v___f_2571_, v_get_2577_);
v___x_2579_ = lean_apply_4(v_toBind_2572_, lean_box(0), lean_box(0), v___x_2578_, v___f_2573_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__0(lean_object* v___y_2580_, lean_object* v_____r_2581_){
_start:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2582_ = lean_box(0);
v___x_2583_ = lean_apply_1(v___y_2580_, v___x_2582_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__4(lean_object* v_inst_2584_, lean_object* v_inst_2585_, lean_object* v_toBind_2586_, lean_object* v_00_u03b1_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v_tryCatch_2590_; lean_object* v___f_2591_; lean_object* v___f_2592_; lean_object* v___x_2593_; 
v_tryCatch_2590_ = lean_ctor_get(v_inst_2584_, 1);
lean_inc(v_tryCatch_2590_);
lean_dec_ref(v_inst_2584_);
v___f_2591_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2591_, 0, v___y_2589_);
v___f_2592_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2592_, 0, v_inst_2585_);
lean_closure_set(v___f_2592_, 1, v_toBind_2586_);
lean_closure_set(v___f_2592_, 2, v___f_2591_);
v___x_2593_ = lean_apply_3(v_tryCatch_2590_, lean_box(0), v___y_2588_, v___f_2592_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg(lean_object* v_inst_2594_, lean_object* v_inst_2595_, lean_object* v_inst_2596_){
_start:
{
lean_object* v_toApplicative_2597_; lean_object* v_toBind_2598_; lean_object* v___f_2599_; lean_object* v___f_2600_; lean_object* v___f_2601_; lean_object* v___f_2602_; lean_object* v___x_2603_; 
v_toApplicative_2597_ = lean_ctor_get(v_inst_2594_, 0);
lean_inc_ref_n(v_toApplicative_2597_, 2);
v_toBind_2598_ = lean_ctor_get(v_inst_2594_, 1);
lean_inc_n(v_toBind_2598_, 2);
lean_dec_ref(v_inst_2594_);
v___f_2599_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
lean_inc_ref(v_inst_2596_);
v___f_2600_ = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2600_, 0, v_inst_2596_);
lean_inc_ref(v_inst_2595_);
v___f_2601_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2601_, 0, v_toApplicative_2597_);
lean_closure_set(v___f_2601_, 1, v_inst_2595_);
lean_closure_set(v___f_2601_, 2, v___f_2599_);
lean_closure_set(v___f_2601_, 3, v_toBind_2598_);
lean_closure_set(v___f_2601_, 4, v___f_2600_);
v___f_2602_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__4), 6, 3);
lean_closure_set(v___f_2602_, 0, v_inst_2596_);
lean_closure_set(v___f_2602_, 1, v_inst_2595_);
lean_closure_set(v___f_2602_, 2, v_toBind_2598_);
v___x_2603_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2603_, 0, v_toApplicative_2597_);
lean_ctor_set(v___x_2603_, 1, v___f_2601_);
lean_ctor_set(v___x_2603_, 2, v___f_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative(lean_object* v_m_2604_, lean_object* v_inst_2605_, lean_object* v_inst_2606_, lean_object* v_inst_2607_){
_start:
{
lean_object* v_toApplicative_2608_; lean_object* v_toBind_2609_; lean_object* v___f_2610_; lean_object* v___f_2611_; lean_object* v___f_2612_; lean_object* v___f_2613_; lean_object* v___x_2614_; 
v_toApplicative_2608_ = lean_ctor_get(v_inst_2605_, 0);
lean_inc_ref_n(v_toApplicative_2608_, 2);
v_toBind_2609_ = lean_ctor_get(v_inst_2605_, 1);
lean_inc_n(v_toBind_2609_, 2);
lean_dec_ref(v_inst_2605_);
v___f_2610_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
lean_inc_ref(v_inst_2607_);
v___f_2611_ = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2611_, 0, v_inst_2607_);
lean_inc_ref(v_inst_2606_);
v___f_2612_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2612_, 0, v_toApplicative_2608_);
lean_closure_set(v___f_2612_, 1, v_inst_2606_);
lean_closure_set(v___f_2612_, 2, v___f_2610_);
lean_closure_set(v___f_2612_, 3, v_toBind_2609_);
lean_closure_set(v___f_2612_, 4, v___f_2611_);
v___f_2613_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__4), 6, 3);
lean_closure_set(v___f_2613_, 0, v_inst_2607_);
lean_closure_set(v___f_2613_, 1, v_inst_2606_);
lean_closure_set(v___f_2613_, 2, v_toBind_2609_);
v___x_2614_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2614_, 0, v_toApplicative_2608_);
lean_ctor_set(v___x_2614_, 1, v___f_2612_);
lean_ctor_set(v___x_2614_, 2, v___f_2613_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogLogTOfMonad___redArg(lean_object* v_inst_2615_){
_start:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2616_ = l_instMonadStateOfStateTOfMonad___redArg(v_inst_2615_);
v___x_2617_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(v___x_2617_, 0, lean_box(0));
lean_closure_set(v___x_2617_, 1, v___x_2616_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogLogTOfMonad(lean_object* v_m_2618_, lean_object* v_inst_2619_){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = l_Lake_instMonadLogLogTOfMonad___redArg(v_inst_2619_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run___redArg(lean_object* v_self_2621_, lean_object* v_log_2622_){
_start:
{
lean_object* v___x_2623_; 
v___x_2623_ = lean_apply_1(v_self_2621_, v_log_2622_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run(lean_object* v_m_2624_, lean_object* v_00_u03b1_2625_, lean_object* v_self_2626_, lean_object* v_log_2627_){
_start:
{
lean_object* v___x_2628_; 
v___x_2628_ = lean_apply_1(v_self_2626_, v_log_2627_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg___lam__0(lean_object* v_x_2629_){
_start:
{
lean_object* v_fst_2630_; 
v_fst_2630_ = lean_ctor_get(v_x_2629_, 0);
lean_inc(v_fst_2630_);
return v_fst_2630_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg___lam__0___boxed(lean_object* v_x_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_Lake_LogT_run_x27___redArg___lam__0(v_x_2631_);
lean_dec_ref(v_x_2631_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg(lean_object* v_inst_2634_, lean_object* v_self_2635_, lean_object* v_log_2636_){
_start:
{
lean_object* v_map_2637_; lean_object* v___f_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v_map_2637_ = lean_ctor_get(v_inst_2634_, 0);
lean_inc(v_map_2637_);
lean_dec_ref(v_inst_2634_);
v___f_2638_ = ((lean_object*)(l_Lake_LogT_run_x27___redArg___closed__0));
v___x_2639_ = lean_apply_1(v_self_2635_, v_log_2636_);
v___x_2640_ = lean_apply_4(v_map_2637_, lean_box(0), lean_box(0), v___f_2638_, v___x_2639_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27(lean_object* v_m_2641_, lean_object* v_00_u03b1_2642_, lean_object* v_inst_2643_, lean_object* v_self_2644_, lean_object* v_log_2645_){
_start:
{
lean_object* v_map_2646_; lean_object* v___f_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v_map_2646_ = lean_ctor_get(v_inst_2643_, 0);
lean_inc(v_map_2646_);
lean_dec_ref(v_inst_2643_);
v___f_2647_ = ((lean_object*)(l_Lake_LogT_run_x27___redArg___closed__0));
v___x_2648_ = lean_apply_1(v_self_2644_, v_log_2645_);
v___x_2649_ = lean_apply_4(v_map_2646_, lean_box(0), lean_box(0), v___f_2647_, v___x_2648_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__1(lean_object* v_toPure_2650_, lean_object* v_fst_2651_, lean_object* v_____r_2652_){
_start:
{
lean_object* v___x_2653_; 
v___x_2653_ = lean_apply_2(v_toPure_2650_, lean_box(0), v_fst_2651_);
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__0(lean_object* v_toPure_2654_, lean_object* v_set_2655_, lean_object* v_toBind_2656_, lean_object* v_____x_2657_){
_start:
{
lean_object* v_fst_2658_; lean_object* v_snd_2659_; lean_object* v___f_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v_fst_2658_ = lean_ctor_get(v_____x_2657_, 0);
lean_inc(v_fst_2658_);
v_snd_2659_ = lean_ctor_get(v_____x_2657_, 1);
lean_inc(v_snd_2659_);
lean_dec_ref(v_____x_2657_);
v___f_2660_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2660_, 0, v_toPure_2654_);
lean_closure_set(v___f_2660_, 1, v_fst_2658_);
v___x_2661_ = lean_apply_1(v_set_2655_, v_snd_2659_);
v___x_2662_ = lean_apply_4(v_toBind_2656_, lean_box(0), lean_box(0), v___x_2661_, v___f_2660_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__2(lean_object* v_self_2663_, lean_object* v_inst_2664_, lean_object* v_toBind_2665_, lean_object* v___f_2666_, lean_object* v_____do__lift_2667_){
_start:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2668_ = lean_apply_1(v_self_2663_, v_____do__lift_2667_);
v___x_2669_ = lean_apply_2(v_inst_2664_, lean_box(0), v___x_2668_);
v___x_2670_ = lean_apply_4(v_toBind_2665_, lean_box(0), lean_box(0), v___x_2669_, v___f_2666_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg(lean_object* v_inst_2671_, lean_object* v_inst_2672_, lean_object* v_inst_2673_, lean_object* v_self_2674_){
_start:
{
lean_object* v_toApplicative_2675_; lean_object* v_toBind_2676_; lean_object* v_set_2677_; lean_object* v_modifyGet_2678_; lean_object* v_toPure_2679_; lean_object* v___f_2680_; lean_object* v___x_2681_; lean_object* v___f_2682_; lean_object* v___f_2683_; lean_object* v___x_2684_; 
v_toApplicative_2675_ = lean_ctor_get(v_inst_2671_, 0);
lean_inc_ref(v_toApplicative_2675_);
v_toBind_2676_ = lean_ctor_get(v_inst_2671_, 1);
lean_inc_n(v_toBind_2676_, 3);
lean_dec_ref(v_inst_2671_);
v_set_2677_ = lean_ctor_get(v_inst_2672_, 1);
lean_inc(v_set_2677_);
v_modifyGet_2678_ = lean_ctor_get(v_inst_2672_, 2);
lean_inc(v_modifyGet_2678_);
lean_dec_ref(v_inst_2672_);
v_toPure_2679_ = lean_ctor_get(v_toApplicative_2675_, 1);
lean_inc(v_toPure_2679_);
lean_dec_ref(v_toApplicative_2675_);
v___f_2680_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_2681_ = lean_apply_2(v_modifyGet_2678_, lean_box(0), v___f_2680_);
v___f_2682_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2682_, 0, v_toPure_2679_);
lean_closure_set(v___f_2682_, 1, v_set_2677_);
lean_closure_set(v___f_2682_, 2, v_toBind_2676_);
v___f_2683_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2683_, 0, v_self_2674_);
lean_closure_set(v___f_2683_, 1, v_inst_2673_);
lean_closure_set(v___f_2683_, 2, v_toBind_2676_);
lean_closure_set(v___f_2683_, 3, v___f_2682_);
v___x_2684_ = lean_apply_4(v_toBind_2676_, lean_box(0), lean_box(0), v___x_2681_, v___f_2683_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun(lean_object* v_n_2685_, lean_object* v_m_2686_, lean_object* v_00_u03b1_2687_, lean_object* v_inst_2688_, lean_object* v_inst_2689_, lean_object* v_inst_2690_, lean_object* v_inst_2691_, lean_object* v_self_2692_){
_start:
{
lean_object* v_toApplicative_2693_; lean_object* v_toBind_2694_; lean_object* v_set_2695_; lean_object* v_modifyGet_2696_; lean_object* v_toPure_2697_; lean_object* v___f_2698_; lean_object* v___x_2699_; lean_object* v___f_2700_; lean_object* v___f_2701_; lean_object* v___x_2702_; 
v_toApplicative_2693_ = lean_ctor_get(v_inst_2688_, 0);
lean_inc_ref(v_toApplicative_2693_);
v_toBind_2694_ = lean_ctor_get(v_inst_2688_, 1);
lean_inc_n(v_toBind_2694_, 3);
lean_dec_ref(v_inst_2688_);
v_set_2695_ = lean_ctor_get(v_inst_2689_, 1);
lean_inc(v_set_2695_);
v_modifyGet_2696_ = lean_ctor_get(v_inst_2689_, 2);
lean_inc(v_modifyGet_2696_);
lean_dec_ref(v_inst_2689_);
v_toPure_2697_ = lean_ctor_get(v_toApplicative_2693_, 1);
lean_inc(v_toPure_2697_);
lean_dec_ref(v_toApplicative_2693_);
v___f_2698_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_2699_ = lean_apply_2(v_modifyGet_2696_, lean_box(0), v___f_2698_);
v___f_2700_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2700_, 0, v_toPure_2697_);
lean_closure_set(v___f_2700_, 1, v_set_2695_);
lean_closure_set(v___f_2700_, 2, v_toBind_2694_);
v___f_2701_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2701_, 0, v_self_2692_);
lean_closure_set(v___f_2701_, 1, v_inst_2690_);
lean_closure_set(v___f_2701_, 2, v_toBind_2694_);
lean_closure_set(v___f_2701_, 3, v___f_2700_);
v___x_2702_ = lean_apply_4(v_toBind_2694_, lean_box(0), lean_box(0), v___x_2699_, v___f_2701_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___boxed(lean_object* v_n_2703_, lean_object* v_m_2704_, lean_object* v_00_u03b1_2705_, lean_object* v_inst_2706_, lean_object* v_inst_2707_, lean_object* v_inst_2708_, lean_object* v_inst_2709_, lean_object* v_self_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_Lake_LogT_takeAndRun(v_n_2703_, v_m_2704_, v_00_u03b1_2705_, v_inst_2706_, v_inst_2707_, v_inst_2708_, v_inst_2709_, v_self_2710_);
lean_dec(v_inst_2709_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg___lam__2(lean_object* v_toPure_2712_, lean_object* v___x_2713_, lean_object* v_toBind_2714_, lean_object* v_inst_2715_, lean_object* v___f_2716_, lean_object* v_____x_2717_){
_start:
{
lean_object* v_fst_2718_; lean_object* v_snd_2719_; lean_object* v___f_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; uint8_t v___x_2723_; 
v_fst_2718_ = lean_ctor_get(v_____x_2717_, 0);
lean_inc(v_fst_2718_);
v_snd_2719_ = lean_ctor_get(v_____x_2717_, 1);
lean_inc(v_snd_2719_);
lean_dec_ref(v_____x_2717_);
lean_inc(v_toPure_2712_);
v___f_2720_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2720_, 0, v_toPure_2712_);
lean_closure_set(v___f_2720_, 1, v_fst_2718_);
v___x_2721_ = lean_array_get_size(v_snd_2719_);
v___x_2722_ = lean_box(0);
v___x_2723_ = lean_nat_dec_lt(v___x_2713_, v___x_2721_);
if (v___x_2723_ == 0)
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
lean_dec(v_snd_2719_);
lean_dec(v___f_2716_);
lean_dec_ref(v_inst_2715_);
v___x_2724_ = lean_apply_2(v_toPure_2712_, lean_box(0), v___x_2722_);
v___x_2725_ = lean_apply_4(v_toBind_2714_, lean_box(0), lean_box(0), v___x_2724_, v___f_2720_);
return v___x_2725_;
}
else
{
size_t v___x_2726_; size_t v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
lean_dec(v_toPure_2712_);
v___x_2726_ = ((size_t)0ULL);
v___x_2727_ = lean_usize_of_nat(v___x_2721_);
v___x_2728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2715_, v___f_2716_, v_snd_2719_, v___x_2726_, v___x_2727_, v___x_2722_);
v___x_2729_ = lean_apply_4(v_toBind_2714_, lean_box(0), lean_box(0), v___x_2728_, v___f_2720_);
return v___x_2729_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg___lam__2___boxed(lean_object* v_toPure_2730_, lean_object* v___x_2731_, lean_object* v_toBind_2732_, lean_object* v_inst_2733_, lean_object* v___f_2734_, lean_object* v_____x_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Lake_LogT_replayLog___redArg___lam__2(v_toPure_2730_, v___x_2731_, v_toBind_2732_, v_inst_2733_, v___f_2734_, v_____x_2735_);
lean_dec(v___x_2731_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg(lean_object* v_inst_2737_, lean_object* v_logger_2738_, lean_object* v_inst_2739_, lean_object* v_self_2740_){
_start:
{
lean_object* v_toApplicative_2741_; lean_object* v_toBind_2742_; lean_object* v_toPure_2743_; lean_object* v___f_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___f_2749_; lean_object* v___x_2750_; 
v_toApplicative_2741_ = lean_ctor_get(v_inst_2737_, 0);
v_toBind_2742_ = lean_ctor_get(v_inst_2737_, 1);
lean_inc_n(v_toBind_2742_, 2);
v_toPure_2743_ = lean_ctor_get(v_toApplicative_2741_, 1);
lean_inc(v_toPure_2743_);
v___f_2744_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2744_, 0, v_logger_2738_);
v___x_2745_ = lean_unsigned_to_nat(0u);
v___x_2746_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_2747_ = lean_apply_1(v_self_2740_, v___x_2746_);
v___x_2748_ = lean_apply_2(v_inst_2739_, lean_box(0), v___x_2747_);
v___f_2749_ = lean_alloc_closure((void*)(l_Lake_LogT_replayLog___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_2749_, 0, v_toPure_2743_);
lean_closure_set(v___f_2749_, 1, v___x_2745_);
lean_closure_set(v___f_2749_, 2, v_toBind_2742_);
lean_closure_set(v___f_2749_, 3, v_inst_2737_);
lean_closure_set(v___f_2749_, 4, v___f_2744_);
v___x_2750_ = lean_apply_4(v_toBind_2742_, lean_box(0), lean_box(0), v___x_2748_, v___f_2749_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog(lean_object* v_n_2751_, lean_object* v_m_2752_, lean_object* v_00_u03b1_2753_, lean_object* v_inst_2754_, lean_object* v_logger_2755_, lean_object* v_inst_2756_, lean_object* v_self_2757_){
_start:
{
lean_object* v_toApplicative_2758_; lean_object* v_toBind_2759_; lean_object* v_toPure_2760_; lean_object* v___f_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___f_2766_; lean_object* v___x_2767_; 
v_toApplicative_2758_ = lean_ctor_get(v_inst_2754_, 0);
v_toBind_2759_ = lean_ctor_get(v_inst_2754_, 1);
lean_inc_n(v_toBind_2759_, 2);
v_toPure_2760_ = lean_ctor_get(v_toApplicative_2758_, 1);
lean_inc(v_toPure_2760_);
v___f_2761_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2761_, 0, v_logger_2755_);
v___x_2762_ = lean_unsigned_to_nat(0u);
v___x_2763_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_2764_ = lean_apply_1(v_self_2757_, v___x_2763_);
v___x_2765_ = lean_apply_2(v_inst_2756_, lean_box(0), v___x_2764_);
v___f_2766_ = lean_alloc_closure((void*)(l_Lake_LogT_replayLog___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_2766_, 0, v_toPure_2760_);
lean_closure_set(v___f_2766_, 1, v___x_2762_);
lean_closure_set(v___f_2766_, 2, v_toBind_2759_);
lean_closure_set(v___f_2766_, 3, v_inst_2754_);
lean_closure_set(v___f_2766_, 4, v___f_2761_);
v___x_2767_ = lean_apply_4(v_toBind_2759_, lean_box(0), lean_box(0), v___x_2765_, v___f_2766_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogELogTOfMonad___redArg(lean_object* v_inst_2768_){
_start:
{
lean_object* v_toApplicative_2769_; lean_object* v_toPure_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v_toApplicative_2769_ = lean_ctor_get(v_inst_2768_, 0);
lean_inc_ref(v_toApplicative_2769_);
lean_dec_ref(v_inst_2768_);
v_toPure_2770_ = lean_ctor_get(v_toApplicative_2769_, 1);
lean_inc(v_toPure_2770_);
lean_dec_ref(v_toApplicative_2769_);
v___x_2771_ = l_Lake_EStateT_instMonadStateOfOfPure___redArg(v_toPure_2770_);
v___x_2772_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(v___x_2772_, 0, lean_box(0));
lean_closure_set(v___x_2772_, 1, v___x_2771_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogELogTOfMonad(lean_object* v_m_2773_, lean_object* v_inst_2774_){
_start:
{
lean_object* v___x_2775_; 
v___x_2775_ = l_Lake_instMonadLogELogTOfMonad___redArg(v_inst_2774_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__0(lean_object* v_x_2776_){
_start:
{
if (lean_obj_tag(v_x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2786_; 
v_a_2777_ = lean_ctor_get(v_x_2776_, 0);
v_a_2778_ = lean_ctor_get(v_x_2776_, 1);
v_isSharedCheck_2786_ = !lean_is_exclusive(v_x_2776_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2780_ = v_x_2776_;
v_isShared_2781_ = v_isSharedCheck_2786_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_inc(v_a_2777_);
lean_dec(v_x_2776_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2786_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2782_; lean_object* v___x_2784_; 
v___x_2782_ = lean_array_get_size(v_a_2777_);
lean_dec(v_a_2777_);
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v___x_2782_);
v___x_2784_ = v___x_2780_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v___x_2782_);
lean_ctor_set(v_reuseFailAlloc_2785_, 1, v_a_2778_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
else
{
lean_object* v_a_2787_; lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
v_a_2787_ = lean_ctor_get(v_x_2776_, 0);
v_a_2788_ = lean_ctor_get(v_x_2776_, 1);
v_isSharedCheck_2795_ = !lean_is_exclusive(v_x_2776_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v_x_2776_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_inc(v_a_2787_);
lean_dec(v_x_2776_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2787_);
lean_ctor_set(v_reuseFailAlloc_2794_, 1, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__1(lean_object* v_a_2796_, lean_object* v_toPure_2797_, lean_object* v_____do__lift_2798_){
_start:
{
if (lean_obj_tag(v_____do__lift_2798_) == 0)
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2807_; 
v_a_2799_ = lean_ctor_get(v_____do__lift_2798_, 1);
v_isSharedCheck_2807_ = !lean_is_exclusive(v_____do__lift_2798_);
if (v_isSharedCheck_2807_ == 0)
{
lean_object* v_unused_2808_; 
v_unused_2808_ = lean_ctor_get(v_____do__lift_2798_, 0);
lean_dec(v_unused_2808_);
v___x_2801_ = v_____do__lift_2798_;
v_isShared_2802_ = v_isSharedCheck_2807_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v_____do__lift_2798_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2807_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
lean_ctor_set_tag(v___x_2801_, 1);
lean_ctor_set(v___x_2801_, 0, v_a_2796_);
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2796_);
lean_ctor_set(v_reuseFailAlloc_2806_, 1, v_a_2799_);
v___x_2804_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
lean_object* v___x_2805_; 
v___x_2805_ = lean_apply_2(v_toPure_2797_, lean_box(0), v___x_2804_);
return v___x_2805_;
}
}
}
else
{
lean_object* v_a_2809_; lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2818_; 
lean_dec(v_a_2796_);
v_a_2809_ = lean_ctor_get(v_____do__lift_2798_, 0);
v_a_2810_ = lean_ctor_get(v_____do__lift_2798_, 1);
v_isSharedCheck_2818_ = !lean_is_exclusive(v_____do__lift_2798_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2812_ = v_____do__lift_2798_;
v_isShared_2813_ = v_isSharedCheck_2818_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_inc(v_a_2809_);
lean_dec(v_____do__lift_2798_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2818_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2809_);
lean_ctor_set(v_reuseFailAlloc_2817_, 1, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
lean_object* v___x_2816_; 
v___x_2816_ = lean_apply_2(v_toPure_2797_, lean_box(0), v___x_2815_);
return v___x_2816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__2(lean_object* v_toPure_2819_, lean_object* v___x_2820_, lean_object* v_____do__lift_2821_){
_start:
{
if (lean_obj_tag(v_____do__lift_2821_) == 0)
{
lean_object* v___x_2822_; 
v___x_2822_ = lean_apply_2(v_toPure_2819_, lean_box(0), v_____do__lift_2821_);
return v___x_2822_;
}
else
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2831_; 
v_a_2823_ = lean_ctor_get(v_____do__lift_2821_, 1);
v_isSharedCheck_2831_ = !lean_is_exclusive(v_____do__lift_2821_);
if (v_isSharedCheck_2831_ == 0)
{
lean_object* v_unused_2832_; 
v_unused_2832_ = lean_ctor_get(v_____do__lift_2821_, 0);
lean_dec(v_unused_2832_);
v___x_2825_ = v_____do__lift_2821_;
v_isShared_2826_ = v_isSharedCheck_2831_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v_____do__lift_2821_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2831_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
lean_ctor_set_tag(v___x_2825_, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2820_);
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2820_);
lean_ctor_set(v_reuseFailAlloc_2830_, 1, v_a_2823_);
v___x_2828_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
lean_object* v___x_2829_; 
v___x_2829_ = lean_apply_2(v_toPure_2819_, lean_box(0), v___x_2828_);
return v___x_2829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__3(lean_object* v_toPure_2833_, lean_object* v___x_2834_, lean_object* v_toBind_2835_, lean_object* v_____do__lift_2836_){
_start:
{
if (lean_obj_tag(v_____do__lift_2836_) == 0)
{
lean_object* v_a_2837_; lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2852_; 
v_a_2837_ = lean_ctor_get(v_____do__lift_2836_, 0);
v_a_2838_ = lean_ctor_get(v_____do__lift_2836_, 1);
v_isSharedCheck_2852_ = !lean_is_exclusive(v_____do__lift_2836_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2840_ = v_____do__lift_2836_;
v_isShared_2841_ = v_isSharedCheck_2852_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_inc(v_a_2837_);
lean_dec(v_____do__lift_2836_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2852_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___f_2842_; lean_object* v___x_2843_; lean_object* v___f_2844_; lean_object* v___x_2845_; lean_object* v___x_2847_; 
lean_inc_n(v_toPure_2833_, 2);
v___f_2842_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2842_, 0, v_a_2837_);
lean_closure_set(v___f_2842_, 1, v_toPure_2833_);
v___x_2843_ = lean_box(0);
v___f_2844_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2844_, 0, v_toPure_2833_);
lean_closure_set(v___f_2844_, 1, v___x_2843_);
v___x_2845_ = lean_array_push(v_a_2838_, v___x_2834_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 1, v___x_2845_);
lean_ctor_set(v___x_2840_, 0, v___x_2843_);
v___x_2847_ = v___x_2840_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2843_);
lean_ctor_set(v_reuseFailAlloc_2851_, 1, v___x_2845_);
v___x_2847_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2848_ = lean_apply_2(v_toPure_2833_, lean_box(0), v___x_2847_);
lean_inc(v_toBind_2835_);
v___x_2849_ = lean_apply_4(v_toBind_2835_, lean_box(0), lean_box(0), v___x_2848_, v___f_2844_);
v___x_2850_ = lean_apply_4(v_toBind_2835_, lean_box(0), lean_box(0), v___x_2849_, v___f_2842_);
return v___x_2850_;
}
}
}
else
{
lean_object* v_a_2853_; lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2862_; 
lean_dec(v_toBind_2835_);
lean_dec_ref(v___x_2834_);
v_a_2853_ = lean_ctor_get(v_____do__lift_2836_, 0);
v_a_2854_ = lean_ctor_get(v_____do__lift_2836_, 1);
v_isSharedCheck_2862_ = !lean_is_exclusive(v_____do__lift_2836_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2856_ = v_____do__lift_2836_;
v_isShared_2857_ = v_isSharedCheck_2862_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_inc(v_a_2853_);
lean_dec(v_____do__lift_2836_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2862_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2853_);
lean_ctor_set(v_reuseFailAlloc_2861_, 1, v_a_2854_);
v___x_2859_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
lean_object* v___x_2860_; 
v___x_2860_ = lean_apply_2(v_toPure_2833_, lean_box(0), v___x_2859_);
return v___x_2860_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__4(lean_object* v_toFunctor_2863_, lean_object* v_toPure_2864_, lean_object* v_toBind_2865_, lean_object* v___f_2866_, lean_object* v_00_u03b1_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v_map_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2883_; 
v_map_2870_ = lean_ctor_get(v_toFunctor_2863_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v_toFunctor_2863_);
if (v_isSharedCheck_2883_ == 0)
{
lean_object* v_unused_2884_; 
v_unused_2884_ = lean_ctor_get(v_toFunctor_2863_, 1);
lean_dec(v_unused_2884_);
v___x_2872_ = v_toFunctor_2863_;
v_isShared_2873_ = v_isSharedCheck_2883_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_map_2870_);
lean_dec(v_toFunctor_2863_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2883_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
uint8_t v___x_2874_; lean_object* v___x_2875_; lean_object* v___f_2876_; lean_object* v___x_2878_; 
v___x_2874_ = 3;
v___x_2875_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2875_, 0, v___y_2868_);
lean_ctor_set_uint8(v___x_2875_, sizeof(void*)*1, v___x_2874_);
lean_inc(v_toBind_2865_);
lean_inc(v_toPure_2864_);
v___f_2876_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__3), 4, 3);
lean_closure_set(v___f_2876_, 0, v_toPure_2864_);
lean_closure_set(v___f_2876_, 1, v___x_2875_);
lean_closure_set(v___f_2876_, 2, v_toBind_2865_);
lean_inc_ref(v___y_2869_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 1, v___y_2869_);
lean_ctor_set(v___x_2872_, 0, v___y_2869_);
v___x_2878_ = v___x_2872_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___y_2869_);
lean_ctor_set(v_reuseFailAlloc_2882_, 1, v___y_2869_);
v___x_2878_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2879_ = lean_apply_2(v_toPure_2864_, lean_box(0), v___x_2878_);
v___x_2880_ = lean_apply_4(v_map_2870_, lean_box(0), lean_box(0), v___f_2866_, v___x_2879_);
v___x_2881_ = lean_apply_4(v_toBind_2865_, lean_box(0), lean_box(0), v___x_2880_, v___f_2876_);
return v___x_2881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg(lean_object* v_inst_2886_){
_start:
{
lean_object* v_toApplicative_2887_; lean_object* v_toBind_2888_; lean_object* v_toFunctor_2889_; lean_object* v_toPure_2890_; lean_object* v___f_2891_; lean_object* v___f_2892_; 
v_toApplicative_2887_ = lean_ctor_get(v_inst_2886_, 0);
lean_inc_ref(v_toApplicative_2887_);
v_toBind_2888_ = lean_ctor_get(v_inst_2886_, 1);
lean_inc(v_toBind_2888_);
lean_dec_ref(v_inst_2886_);
v_toFunctor_2889_ = lean_ctor_get(v_toApplicative_2887_, 0);
lean_inc_ref(v_toFunctor_2889_);
v_toPure_2890_ = lean_ctor_get(v_toApplicative_2887_, 1);
lean_inc(v_toPure_2890_);
lean_dec_ref(v_toApplicative_2887_);
v___f_2891_ = ((lean_object*)(l_Lake_instMonadErrorELogTOfMonad___redArg___closed__0));
v___f_2892_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__4), 7, 4);
lean_closure_set(v___f_2892_, 0, v_toFunctor_2889_);
lean_closure_set(v___f_2892_, 1, v_toPure_2890_);
lean_closure_set(v___f_2892_, 2, v_toBind_2888_);
lean_closure_set(v___f_2892_, 3, v___f_2891_);
return v___f_2892_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad(lean_object* v_m_2893_, lean_object* v_inst_2894_){
_start:
{
lean_object* v___x_2895_; 
v___x_2895_ = l_Lake_instMonadErrorELogTOfMonad___redArg(v_inst_2894_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__1(lean_object* v___y_2896_, lean_object* v___x_2897_, lean_object* v_toPure_2898_, lean_object* v_____do__lift_2899_){
_start:
{
if (lean_obj_tag(v_____do__lift_2899_) == 0)
{
lean_object* v_a_2900_; lean_object* v___x_2901_; 
lean_dec(v_toPure_2898_);
v_a_2900_ = lean_ctor_get(v_____do__lift_2899_, 1);
lean_inc(v_a_2900_);
lean_dec_ref_known(v_____do__lift_2899_, 2);
v___x_2901_ = lean_apply_2(v___y_2896_, v___x_2897_, v_a_2900_);
return v___x_2901_;
}
else
{
lean_object* v_a_2902_; lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2911_; 
lean_dec(v___y_2896_);
v_a_2902_ = lean_ctor_get(v_____do__lift_2899_, 0);
v_a_2903_ = lean_ctor_get(v_____do__lift_2899_, 1);
v_isSharedCheck_2911_ = !lean_is_exclusive(v_____do__lift_2899_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2905_ = v_____do__lift_2899_;
v_isShared_2906_ = v_isSharedCheck_2911_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_inc(v_a_2902_);
lean_dec(v_____do__lift_2899_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2911_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2908_; 
if (v_isShared_2906_ == 0)
{
v___x_2908_ = v___x_2905_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2902_);
lean_ctor_set(v_reuseFailAlloc_2910_, 1, v_a_2903_);
v___x_2908_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
lean_object* v___x_2909_; 
v___x_2909_ = lean_apply_2(v_toPure_2898_, lean_box(0), v___x_2908_);
return v___x_2909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__0(lean_object* v_toPure_2912_, lean_object* v___y_2913_, lean_object* v_toBind_2914_, lean_object* v_____do__lift_2915_){
_start:
{
if (lean_obj_tag(v_____do__lift_2915_) == 0)
{
lean_object* v___x_2916_; 
lean_dec(v_toBind_2914_);
lean_dec(v___y_2913_);
v___x_2916_ = lean_apply_2(v_toPure_2912_, lean_box(0), v_____do__lift_2915_);
return v___x_2916_;
}
else
{
lean_object* v_a_2917_; lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2930_; 
v_a_2917_ = lean_ctor_get(v_____do__lift_2915_, 0);
v_a_2918_ = lean_ctor_get(v_____do__lift_2915_, 1);
v_isSharedCheck_2930_ = !lean_is_exclusive(v_____do__lift_2915_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2920_ = v_____do__lift_2915_;
v_isShared_2921_ = v_isSharedCheck_2930_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_inc(v_a_2917_);
lean_dec(v_____do__lift_2915_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2930_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2922_; lean_object* v___f_2923_; lean_object* v___x_2924_; lean_object* v___x_2926_; 
v___x_2922_ = lean_box(0);
lean_inc(v_toPure_2912_);
v___f_2923_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2923_, 0, v___y_2913_);
lean_closure_set(v___f_2923_, 1, v___x_2922_);
lean_closure_set(v___f_2923_, 2, v_toPure_2912_);
v___x_2924_ = l_Array_shrink___redArg(v_a_2918_, v_a_2917_);
lean_dec(v_a_2917_);
if (v_isShared_2921_ == 0)
{
lean_ctor_set_tag(v___x_2920_, 0);
lean_ctor_set(v___x_2920_, 1, v___x_2924_);
lean_ctor_set(v___x_2920_, 0, v___x_2922_);
v___x_2926_ = v___x_2920_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v___x_2922_);
lean_ctor_set(v_reuseFailAlloc_2929_, 1, v___x_2924_);
v___x_2926_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2927_ = lean_apply_2(v_toPure_2912_, lean_box(0), v___x_2926_);
v___x_2928_ = lean_apply_4(v_toBind_2914_, lean_box(0), lean_box(0), v___x_2927_, v___f_2923_);
return v___x_2928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__2(lean_object* v_toPure_2931_, lean_object* v_toBind_2932_, lean_object* v_00_u03b1_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v___f_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
lean_inc(v_toBind_2932_);
v___f_2937_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2937_, 0, v_toPure_2931_);
lean_closure_set(v___f_2937_, 1, v___y_2935_);
lean_closure_set(v___f_2937_, 2, v_toBind_2932_);
v___x_2938_ = lean_apply_1(v___y_2934_, v___y_2936_);
v___x_2939_ = lean_apply_4(v_toBind_2932_, lean_box(0), lean_box(0), v___x_2938_, v___f_2937_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__3(lean_object* v_toPure_2940_, lean_object* v_____do__lift_2941_){
_start:
{
if (lean_obj_tag(v_____do__lift_2941_) == 0)
{
lean_object* v_a_2942_; lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2951_; 
v_a_2942_ = lean_ctor_get(v_____do__lift_2941_, 0);
v_a_2943_ = lean_ctor_get(v_____do__lift_2941_, 1);
v_isSharedCheck_2951_ = !lean_is_exclusive(v_____do__lift_2941_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2945_ = v_____do__lift_2941_;
v_isShared_2946_ = v_isSharedCheck_2951_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_inc(v_a_2942_);
lean_dec(v_____do__lift_2941_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2951_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
lean_ctor_set_tag(v___x_2945_, 1);
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2942_);
lean_ctor_set(v_reuseFailAlloc_2950_, 1, v_a_2943_);
v___x_2948_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
lean_object* v___x_2949_; 
v___x_2949_ = lean_apply_2(v_toPure_2940_, lean_box(0), v___x_2948_);
return v___x_2949_;
}
}
}
else
{
lean_object* v_a_2952_; lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2961_; 
v_a_2952_ = lean_ctor_get(v_____do__lift_2941_, 0);
v_a_2953_ = lean_ctor_get(v_____do__lift_2941_, 1);
v_isSharedCheck_2961_ = !lean_is_exclusive(v_____do__lift_2941_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2955_ = v_____do__lift_2941_;
v_isShared_2956_ = v_isSharedCheck_2961_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_inc(v_a_2952_);
lean_dec(v_____do__lift_2941_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2961_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2958_; 
if (v_isShared_2956_ == 0)
{
v___x_2958_ = v___x_2955_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2952_);
lean_ctor_set(v_reuseFailAlloc_2960_, 1, v_a_2953_);
v___x_2958_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
lean_object* v___x_2959_; 
v___x_2959_ = lean_apply_2(v_toPure_2940_, lean_box(0), v___x_2958_);
return v___x_2959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__4(lean_object* v_toFunctor_2962_, lean_object* v_toPure_2963_, lean_object* v___f_2964_, lean_object* v_toBind_2965_, lean_object* v___f_2966_, lean_object* v_00_u03b1_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v_map_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2979_; 
v_map_2969_ = lean_ctor_get(v_toFunctor_2962_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v_toFunctor_2962_);
if (v_isSharedCheck_2979_ == 0)
{
lean_object* v_unused_2980_; 
v_unused_2980_ = lean_ctor_get(v_toFunctor_2962_, 1);
lean_dec(v_unused_2980_);
v___x_2971_ = v_toFunctor_2962_;
v_isShared_2972_ = v_isSharedCheck_2979_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_map_2969_);
lean_dec(v_toFunctor_2962_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2979_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2974_; 
lean_inc_ref(v___y_2968_);
if (v_isShared_2972_ == 0)
{
lean_ctor_set(v___x_2971_, 1, v___y_2968_);
lean_ctor_set(v___x_2971_, 0, v___y_2968_);
v___x_2974_ = v___x_2971_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v___y_2968_);
lean_ctor_set(v_reuseFailAlloc_2978_, 1, v___y_2968_);
v___x_2974_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2975_ = lean_apply_2(v_toPure_2963_, lean_box(0), v___x_2974_);
v___x_2976_ = lean_apply_4(v_map_2969_, lean_box(0), lean_box(0), v___f_2964_, v___x_2975_);
v___x_2977_ = lean_apply_4(v_toBind_2965_, lean_box(0), lean_box(0), v___x_2976_, v___f_2966_);
return v___x_2977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg(lean_object* v_inst_2981_){
_start:
{
lean_object* v_toApplicative_2982_; lean_object* v_toBind_2983_; lean_object* v_toFunctor_2984_; lean_object* v_toPure_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3003_; 
v_toApplicative_2982_ = lean_ctor_get(v_inst_2981_, 0);
lean_inc_ref(v_toApplicative_2982_);
v_toBind_2983_ = lean_ctor_get(v_inst_2981_, 1);
lean_inc(v_toBind_2983_);
lean_dec_ref(v_inst_2981_);
v_toFunctor_2984_ = lean_ctor_get(v_toApplicative_2982_, 0);
v_toPure_2985_ = lean_ctor_get(v_toApplicative_2982_, 1);
v_isSharedCheck_3003_ = !lean_is_exclusive(v_toApplicative_2982_);
if (v_isSharedCheck_3003_ == 0)
{
lean_object* v_unused_3004_; lean_object* v_unused_3005_; lean_object* v_unused_3006_; 
v_unused_3004_ = lean_ctor_get(v_toApplicative_2982_, 4);
lean_dec(v_unused_3004_);
v_unused_3005_ = lean_ctor_get(v_toApplicative_2982_, 3);
lean_dec(v_unused_3005_);
v_unused_3006_ = lean_ctor_get(v_toApplicative_2982_, 2);
lean_dec(v_unused_3006_);
v___x_2987_ = v_toApplicative_2982_;
v_isShared_2988_ = v_isSharedCheck_3003_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_toPure_2985_);
lean_inc(v_toFunctor_2984_);
lean_dec(v_toApplicative_2982_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3003_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___f_2989_; lean_object* v___f_2990_; lean_object* v___f_2991_; lean_object* v___f_2992_; lean_object* v___f_2993_; lean_object* v___f_2994_; lean_object* v___f_2995_; lean_object* v___f_2996_; lean_object* v___x_2997_; lean_object* v___f_2998_; lean_object* v___x_3000_; 
v___f_2989_ = ((lean_object*)(l_Lake_instMonadErrorELogTOfMonad___redArg___closed__0));
lean_inc_n(v_toBind_2983_, 4);
lean_inc_n(v_toPure_2985_, 7);
v___f_2990_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__2), 6, 2);
lean_closure_set(v___f_2990_, 0, v_toPure_2985_);
lean_closure_set(v___f_2990_, 1, v_toBind_2983_);
v___f_2991_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2991_, 0, v_toPure_2985_);
lean_inc_ref_n(v_toFunctor_2984_, 2);
v___f_2992_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__4), 7, 5);
lean_closure_set(v___f_2992_, 0, v_toFunctor_2984_);
lean_closure_set(v___f_2992_, 1, v_toPure_2985_);
lean_closure_set(v___f_2992_, 2, v___f_2989_);
lean_closure_set(v___f_2992_, 3, v_toBind_2983_);
lean_closure_set(v___f_2992_, 4, v___f_2991_);
v___f_2993_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_2993_, 0, v_toPure_2985_);
lean_closure_set(v___f_2993_, 1, v_toBind_2983_);
v___f_2994_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_2994_, 0, v_toPure_2985_);
lean_closure_set(v___f_2994_, 1, v_toBind_2983_);
v___f_2995_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_2995_, 0, v_toPure_2985_);
lean_closure_set(v___f_2995_, 1, v___f_2993_);
v___f_2996_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_2996_, 0, v_toFunctor_2984_);
lean_closure_set(v___f_2996_, 1, v_toPure_2985_);
lean_closure_set(v___f_2996_, 2, v_toBind_2983_);
v___x_2997_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_2984_);
v___f_2998_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2998_, 0, v_toPure_2985_);
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 4, v___f_2994_);
lean_ctor_set(v___x_2987_, 3, v___f_2995_);
lean_ctor_set(v___x_2987_, 2, v___f_2996_);
lean_ctor_set(v___x_2987_, 1, v___f_2998_);
lean_ctor_set(v___x_2987_, 0, v___x_2997_);
v___x_3000_ = v___x_2987_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v___x_2997_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v___f_2998_);
lean_ctor_set(v_reuseFailAlloc_3002_, 2, v___f_2996_);
lean_ctor_set(v_reuseFailAlloc_3002_, 3, v___f_2995_);
lean_ctor_set(v_reuseFailAlloc_3002_, 4, v___f_2994_);
v___x_3000_ = v_reuseFailAlloc_3002_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
lean_object* v___x_3001_; 
v___x_3001_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
lean_ctor_set(v___x_3001_, 1, v___f_2992_);
lean_ctor_set(v___x_3001_, 2, v___f_2990_);
return v___x_3001_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad(lean_object* v_m_3007_, lean_object* v_inst_3008_){
_start:
{
lean_object* v___x_3009_; 
v___x_3009_ = l_Lake_instAlternativeELogTOfMonad___redArg(v_inst_3008_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run___redArg(lean_object* v_self_3010_, lean_object* v_log_3011_){
_start:
{
lean_object* v___x_3012_; 
v___x_3012_ = lean_apply_1(v_self_3010_, v_log_3011_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run(lean_object* v_m_3013_, lean_object* v_00_u03b1_3014_, lean_object* v_self_3015_, lean_object* v_log_3016_){
_start:
{
lean_object* v___x_3017_; 
v___x_3017_ = lean_apply_1(v_self_3015_, v_log_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x27___redArg(lean_object* v_inst_3019_, lean_object* v_self_3020_, lean_object* v_log_3021_){
_start:
{
lean_object* v_map_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v_map_3022_ = lean_ctor_get(v_inst_3019_, 0);
lean_inc(v_map_3022_);
lean_dec_ref(v_inst_3019_);
v___x_3023_ = ((lean_object*)(l_Lake_ELogT_run_x27___redArg___closed__0));
v___x_3024_ = lean_apply_1(v_self_3020_, v_log_3021_);
v___x_3025_ = lean_apply_4(v_map_3022_, lean_box(0), lean_box(0), v___x_3023_, v___x_3024_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x27(lean_object* v_m_3026_, lean_object* v_00_u03b1_3027_, lean_object* v_inst_3028_, lean_object* v_self_3029_, lean_object* v_log_3030_){
_start:
{
lean_object* v_map_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v_map_3031_ = lean_ctor_get(v_inst_3028_, 0);
lean_inc(v_map_3031_);
lean_dec_ref(v_inst_3028_);
v___x_3032_ = ((lean_object*)(l_Lake_ELogT_run_x27___redArg___closed__0));
v___x_3033_ = lean_apply_1(v_self_3029_, v_log_3030_);
v___x_3034_ = lean_apply_4(v_map_3031_, lean_box(0), lean_box(0), v___x_3032_, v___x_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT___redArg(lean_object* v_inst_3036_, lean_object* v_self_3037_, lean_object* v_a_3038_){
_start:
{
lean_object* v_map_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v_map_3039_ = lean_ctor_get(v_inst_3036_, 0);
lean_inc(v_map_3039_);
lean_dec_ref(v_inst_3036_);
v___x_3040_ = ((lean_object*)(l_Lake_ELogT_toLogT___redArg___closed__0));
v___x_3041_ = lean_apply_1(v_self_3037_, v_a_3038_);
v___x_3042_ = lean_apply_4(v_map_3039_, lean_box(0), lean_box(0), v___x_3040_, v___x_3041_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT(lean_object* v_m_3043_, lean_object* v_00_u03b1_3044_, lean_object* v_inst_3045_, lean_object* v_self_3046_, lean_object* v_a_3047_){
_start:
{
lean_object* v_map_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v_map_3048_ = lean_ctor_get(v_inst_3045_, 0);
lean_inc(v_map_3048_);
lean_dec_ref(v_inst_3045_);
v___x_3049_ = ((lean_object*)(l_Lake_ELogT_toLogT___redArg___closed__0));
v___x_3050_ = lean_apply_1(v_self_3046_, v_a_3047_);
v___x_3051_ = lean_apply_4(v_map_3048_, lean_box(0), lean_box(0), v___x_3049_, v___x_3050_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT_x3f___redArg(lean_object* v_inst_3053_, lean_object* v_self_3054_, lean_object* v_a_3055_){
_start:
{
lean_object* v_map_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v_map_3056_ = lean_ctor_get(v_inst_3053_, 0);
lean_inc(v_map_3056_);
lean_dec_ref(v_inst_3053_);
v___x_3057_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3058_ = lean_apply_1(v_self_3054_, v_a_3055_);
v___x_3059_ = lean_apply_4(v_map_3056_, lean_box(0), lean_box(0), v___x_3057_, v___x_3058_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT_x3f(lean_object* v_m_3060_, lean_object* v_00_u03b1_3061_, lean_object* v_inst_3062_, lean_object* v_self_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v_map_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v_map_3065_ = lean_ctor_get(v_inst_3062_, 0);
lean_inc(v_map_3065_);
lean_dec_ref(v_inst_3062_);
v___x_3066_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3067_ = lean_apply_1(v_self_3063_, v_a_3064_);
v___x_3068_ = lean_apply_4(v_map_3065_, lean_box(0), lean_box(0), v___x_3066_, v___x_3067_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f___redArg(lean_object* v_inst_3069_, lean_object* v_self_3070_, lean_object* v_log_3071_){
_start:
{
lean_object* v_map_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v_map_3072_ = lean_ctor_get(v_inst_3069_, 0);
lean_inc(v_map_3072_);
lean_dec_ref(v_inst_3069_);
v___x_3073_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3074_ = lean_apply_1(v_self_3070_, v_log_3071_);
v___x_3075_ = lean_apply_4(v_map_3072_, lean_box(0), lean_box(0), v___x_3073_, v___x_3074_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f(lean_object* v_m_3076_, lean_object* v_00_u03b1_3077_, lean_object* v_inst_3078_, lean_object* v_self_3079_, lean_object* v_log_3080_){
_start:
{
lean_object* v_map_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v_map_3081_ = lean_ctor_get(v_inst_3078_, 0);
lean_inc(v_map_3081_);
lean_dec_ref(v_inst_3078_);
v___x_3082_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3083_ = lean_apply_1(v_self_3079_, v_log_3080_);
v___x_3084_ = lean_apply_4(v_map_3081_, lean_box(0), lean_box(0), v___x_3082_, v___x_3083_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f_x27___redArg(lean_object* v_inst_3086_, lean_object* v_self_3087_, lean_object* v_log_3088_){
_start:
{
lean_object* v_map_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v_map_3089_ = lean_ctor_get(v_inst_3086_, 0);
lean_inc(v_map_3089_);
lean_dec_ref(v_inst_3086_);
v___x_3090_ = ((lean_object*)(l_Lake_ELogT_run_x3f_x27___redArg___closed__0));
v___x_3091_ = lean_apply_1(v_self_3087_, v_log_3088_);
v___x_3092_ = lean_apply_4(v_map_3089_, lean_box(0), lean_box(0), v___x_3090_, v___x_3091_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f_x27(lean_object* v_m_3093_, lean_object* v_00_u03b1_3094_, lean_object* v_inst_3095_, lean_object* v_self_3096_, lean_object* v_log_3097_){
_start:
{
lean_object* v_map_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v_map_3098_ = lean_ctor_get(v_inst_3095_, 0);
lean_inc(v_map_3098_);
lean_dec_ref(v_inst_3095_);
v___x_3099_ = ((lean_object*)(l_Lake_ELogT_run_x3f_x27___redArg___closed__0));
v___x_3100_ = lean_apply_1(v_self_3096_, v_log_3097_);
v___x_3101_ = lean_apply_4(v_map_3098_, lean_box(0), lean_box(0), v___x_3099_, v___x_3100_);
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg___lam__0(lean_object* v_f_3102_, lean_object* v_____x_3103_){
_start:
{
lean_object* v_fst_3104_; lean_object* v_snd_3105_; lean_object* v___x_3106_; 
v_fst_3104_ = lean_ctor_get(v_____x_3103_, 0);
lean_inc(v_fst_3104_);
v_snd_3105_ = lean_ctor_get(v_____x_3103_, 1);
lean_inc(v_snd_3105_);
lean_dec_ref(v_____x_3103_);
v___x_3106_ = lean_apply_2(v_f_3102_, v_fst_3104_, v_snd_3105_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg___lam__1(lean_object* v_toPure_3107_, lean_object* v_toBind_3108_, lean_object* v___f_3109_, lean_object* v_____do__lift_3110_){
_start:
{
if (lean_obj_tag(v_____do__lift_3110_) == 0)
{
lean_object* v_a_3111_; lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3120_; 
lean_dec(v___f_3109_);
lean_dec(v_toBind_3108_);
v_a_3111_ = lean_ctor_get(v_____do__lift_3110_, 0);
v_a_3112_ = lean_ctor_get(v_____do__lift_3110_, 1);
v_isSharedCheck_3120_ = !lean_is_exclusive(v_____do__lift_3110_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3114_ = v_____do__lift_3110_;
v_isShared_3115_ = v_isSharedCheck_3120_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_inc(v_a_3111_);
lean_dec(v_____do__lift_3110_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3120_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3111_);
lean_ctor_set(v_reuseFailAlloc_3119_, 1, v_a_3112_);
v___x_3117_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
lean_object* v___x_3118_; 
v___x_3118_ = lean_apply_2(v_toPure_3107_, lean_box(0), v___x_3117_);
return v___x_3118_;
}
}
}
else
{
lean_object* v_a_3121_; lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3134_; 
v_a_3121_ = lean_ctor_get(v_____do__lift_3110_, 0);
v_a_3122_ = lean_ctor_get(v_____do__lift_3110_, 1);
v_isSharedCheck_3134_ = !lean_is_exclusive(v_____do__lift_3110_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3124_ = v_____do__lift_3110_;
v_isShared_3125_ = v_isSharedCheck_3134_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_inc(v_a_3121_);
lean_dec(v_____do__lift_3110_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3134_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3130_; 
v___x_3126_ = lean_array_get_size(v_a_3122_);
lean_inc(v_a_3121_);
v___x_3127_ = l_Array_extract___redArg(v_a_3122_, v_a_3121_, v___x_3126_);
v___x_3128_ = l_Array_shrink___redArg(v_a_3122_, v_a_3121_);
lean_dec(v_a_3121_);
if (v_isShared_3125_ == 0)
{
lean_ctor_set_tag(v___x_3124_, 0);
lean_ctor_set(v___x_3124_, 1, v___x_3128_);
lean_ctor_set(v___x_3124_, 0, v___x_3127_);
v___x_3130_ = v___x_3124_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v___x_3127_);
lean_ctor_set(v_reuseFailAlloc_3133_, 1, v___x_3128_);
v___x_3130_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3131_ = lean_apply_2(v_toPure_3107_, lean_box(0), v___x_3130_);
v___x_3132_ = lean_apply_4(v_toBind_3108_, lean_box(0), lean_box(0), v___x_3131_, v___f_3109_);
return v___x_3132_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg(lean_object* v_inst_3135_, lean_object* v_f_3136_, lean_object* v_self_3137_, lean_object* v_a_3138_){
_start:
{
lean_object* v_toApplicative_3139_; lean_object* v_toBind_3140_; lean_object* v_toPure_3141_; lean_object* v___f_3142_; lean_object* v___x_3143_; lean_object* v___f_3144_; lean_object* v___x_3145_; 
v_toApplicative_3139_ = lean_ctor_get(v_inst_3135_, 0);
lean_inc_ref(v_toApplicative_3139_);
v_toBind_3140_ = lean_ctor_get(v_inst_3135_, 1);
lean_inc_n(v_toBind_3140_, 2);
lean_dec_ref(v_inst_3135_);
v_toPure_3141_ = lean_ctor_get(v_toApplicative_3139_, 1);
lean_inc(v_toPure_3141_);
lean_dec_ref(v_toApplicative_3139_);
v___f_3142_ = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3142_, 0, v_f_3136_);
v___x_3143_ = lean_apply_1(v_self_3137_, v_a_3138_);
v___f_3144_ = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3144_, 0, v_toPure_3141_);
lean_closure_set(v___f_3144_, 1, v_toBind_3140_);
lean_closure_set(v___f_3144_, 2, v___f_3142_);
v___x_3145_ = lean_apply_4(v_toBind_3140_, lean_box(0), lean_box(0), v___x_3143_, v___f_3144_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog(lean_object* v_m_3146_, lean_object* v_00_u03b1_3147_, lean_object* v_inst_3148_, lean_object* v_f_3149_, lean_object* v_self_3150_, lean_object* v_a_3151_){
_start:
{
lean_object* v_toApplicative_3152_; lean_object* v_toBind_3153_; lean_object* v_toPure_3154_; lean_object* v___f_3155_; lean_object* v___x_3156_; lean_object* v___f_3157_; lean_object* v___x_3158_; 
v_toApplicative_3152_ = lean_ctor_get(v_inst_3148_, 0);
lean_inc_ref(v_toApplicative_3152_);
v_toBind_3153_ = lean_ctor_get(v_inst_3148_, 1);
lean_inc_n(v_toBind_3153_, 2);
lean_dec_ref(v_inst_3148_);
v_toPure_3154_ = lean_ctor_get(v_toApplicative_3152_, 1);
lean_inc(v_toPure_3154_);
lean_dec_ref(v_toApplicative_3152_);
v___f_3155_ = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3155_, 0, v_f_3149_);
v___x_3156_ = lean_apply_1(v_self_3150_, v_a_3151_);
v___f_3157_ = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3157_, 0, v_toPure_3154_);
lean_closure_set(v___f_3157_, 1, v_toBind_3153_);
lean_closure_set(v___f_3157_, 2, v___f_3155_);
v___x_3158_ = lean_apply_4(v_toBind_3153_, lean_box(0), lean_box(0), v___x_3156_, v___f_3157_);
return v___x_3158_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__1(lean_object* v_toPure_3159_, lean_object* v_a_3160_, lean_object* v_____r_3161_){
_start:
{
lean_object* v___x_3162_; 
v___x_3162_ = lean_apply_2(v_toPure_3159_, lean_box(0), v_a_3160_);
return v___x_3162_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__0(lean_object* v_inst_3163_, lean_object* v_a_3164_, lean_object* v_____r_3165_){
_start:
{
lean_object* v_throw_3166_; lean_object* v___x_3167_; 
v_throw_3166_ = lean_ctor_get(v_inst_3163_, 0);
lean_inc(v_throw_3166_);
lean_dec_ref(v_inst_3163_);
v___x_3167_ = lean_apply_2(v_throw_3166_, lean_box(0), v_a_3164_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__2(lean_object* v_toPure_3168_, lean_object* v_set_3169_, lean_object* v_toBind_3170_, lean_object* v_inst_3171_, lean_object* v_____do__lift_3172_){
_start:
{
if (lean_obj_tag(v_____do__lift_3172_) == 0)
{
lean_object* v_a_3173_; lean_object* v_a_3174_; lean_object* v___f_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
lean_dec_ref(v_inst_3171_);
v_a_3173_ = lean_ctor_get(v_____do__lift_3172_, 0);
lean_inc(v_a_3173_);
v_a_3174_ = lean_ctor_get(v_____do__lift_3172_, 1);
lean_inc(v_a_3174_);
lean_dec_ref_known(v_____do__lift_3172_, 2);
v___f_3175_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3175_, 0, v_toPure_3168_);
lean_closure_set(v___f_3175_, 1, v_a_3173_);
v___x_3176_ = lean_apply_1(v_set_3169_, v_a_3174_);
v___x_3177_ = lean_apply_4(v_toBind_3170_, lean_box(0), lean_box(0), v___x_3176_, v___f_3175_);
return v___x_3177_;
}
else
{
lean_object* v_a_3178_; lean_object* v_a_3179_; lean_object* v___f_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
lean_dec(v_toPure_3168_);
v_a_3178_ = lean_ctor_get(v_____do__lift_3172_, 0);
lean_inc(v_a_3178_);
v_a_3179_ = lean_ctor_get(v_____do__lift_3172_, 1);
lean_inc(v_a_3179_);
lean_dec_ref_known(v_____do__lift_3172_, 2);
v___f_3180_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3180_, 0, v_inst_3171_);
lean_closure_set(v___f_3180_, 1, v_a_3178_);
v___x_3181_ = lean_apply_1(v_set_3169_, v_a_3179_);
v___x_3182_ = lean_apply_4(v_toBind_3170_, lean_box(0), lean_box(0), v___x_3181_, v___f_3180_);
return v___x_3182_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__3(lean_object* v_self_3183_, lean_object* v_inst_3184_, lean_object* v_toBind_3185_, lean_object* v___f_3186_, lean_object* v_____do__lift_3187_){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3188_ = lean_apply_1(v_self_3183_, v_____do__lift_3187_);
v___x_3189_ = lean_apply_2(v_inst_3184_, lean_box(0), v___x_3188_);
v___x_3190_ = lean_apply_4(v_toBind_3185_, lean_box(0), lean_box(0), v___x_3189_, v___f_3186_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg(lean_object* v_inst_3191_, lean_object* v_inst_3192_, lean_object* v_inst_3193_, lean_object* v_inst_3194_, lean_object* v_self_3195_){
_start:
{
lean_object* v_toApplicative_3196_; lean_object* v_toBind_3197_; lean_object* v_set_3198_; lean_object* v_modifyGet_3199_; lean_object* v_toPure_3200_; lean_object* v___f_3201_; lean_object* v___x_3202_; lean_object* v___f_3203_; lean_object* v___f_3204_; lean_object* v___x_3205_; 
v_toApplicative_3196_ = lean_ctor_get(v_inst_3191_, 0);
lean_inc_ref(v_toApplicative_3196_);
v_toBind_3197_ = lean_ctor_get(v_inst_3191_, 1);
lean_inc_n(v_toBind_3197_, 3);
lean_dec_ref(v_inst_3191_);
v_set_3198_ = lean_ctor_get(v_inst_3192_, 1);
lean_inc(v_set_3198_);
v_modifyGet_3199_ = lean_ctor_get(v_inst_3192_, 2);
lean_inc(v_modifyGet_3199_);
lean_dec_ref(v_inst_3192_);
v_toPure_3200_ = lean_ctor_get(v_toApplicative_3196_, 1);
lean_inc(v_toPure_3200_);
lean_dec_ref(v_toApplicative_3196_);
v___f_3201_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_3202_ = lean_apply_2(v_modifyGet_3199_, lean_box(0), v___f_3201_);
v___f_3203_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3203_, 0, v_toPure_3200_);
lean_closure_set(v___f_3203_, 1, v_set_3198_);
lean_closure_set(v___f_3203_, 2, v_toBind_3197_);
lean_closure_set(v___f_3203_, 3, v_inst_3193_);
v___f_3204_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3204_, 0, v_self_3195_);
lean_closure_set(v___f_3204_, 1, v_inst_3194_);
lean_closure_set(v___f_3204_, 2, v_toBind_3197_);
lean_closure_set(v___f_3204_, 3, v___f_3203_);
v___x_3205_ = lean_apply_4(v_toBind_3197_, lean_box(0), lean_box(0), v___x_3202_, v___f_3204_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun(lean_object* v_n_3206_, lean_object* v_m_3207_, lean_object* v_00_u03b1_3208_, lean_object* v_inst_3209_, lean_object* v_inst_3210_, lean_object* v_inst_3211_, lean_object* v_inst_3212_, lean_object* v_self_3213_){
_start:
{
lean_object* v_toApplicative_3214_; lean_object* v_toBind_3215_; lean_object* v_set_3216_; lean_object* v_modifyGet_3217_; lean_object* v_toPure_3218_; lean_object* v___f_3219_; lean_object* v___x_3220_; lean_object* v___f_3221_; lean_object* v___f_3222_; lean_object* v___x_3223_; 
v_toApplicative_3214_ = lean_ctor_get(v_inst_3209_, 0);
lean_inc_ref(v_toApplicative_3214_);
v_toBind_3215_ = lean_ctor_get(v_inst_3209_, 1);
lean_inc_n(v_toBind_3215_, 3);
lean_dec_ref(v_inst_3209_);
v_set_3216_ = lean_ctor_get(v_inst_3210_, 1);
lean_inc(v_set_3216_);
v_modifyGet_3217_ = lean_ctor_get(v_inst_3210_, 2);
lean_inc(v_modifyGet_3217_);
lean_dec_ref(v_inst_3210_);
v_toPure_3218_ = lean_ctor_get(v_toApplicative_3214_, 1);
lean_inc(v_toPure_3218_);
lean_dec_ref(v_toApplicative_3214_);
v___f_3219_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_3220_ = lean_apply_2(v_modifyGet_3217_, lean_box(0), v___f_3219_);
v___f_3221_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3221_, 0, v_toPure_3218_);
lean_closure_set(v___f_3221_, 1, v_set_3216_);
lean_closure_set(v___f_3221_, 2, v_toBind_3215_);
lean_closure_set(v___f_3221_, 3, v_inst_3211_);
v___f_3222_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3222_, 0, v_self_3213_);
lean_closure_set(v___f_3222_, 1, v_inst_3212_);
lean_closure_set(v___f_3222_, 2, v_toBind_3215_);
lean_closure_set(v___f_3222_, 3, v___f_3221_);
v___x_3223_ = lean_apply_4(v_toBind_3215_, lean_box(0), lean_box(0), v___x_3220_, v___f_3222_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__2(lean_object* v_toPure_3224_, lean_object* v_x_3225_){
_start:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = lean_box(0);
v___x_3227_ = lean_apply_2(v_toPure_3224_, lean_box(0), v___x_3226_);
return v___x_3227_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__0(lean_object* v_a_3228_, lean_object* v_toPure_3229_, lean_object* v_x_3230_){
_start:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3231_, 0, v_a_3228_);
v___x_3232_ = lean_apply_2(v_toPure_3229_, lean_box(0), v___x_3231_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__1(lean_object* v_toPure_3233_, lean_object* v___x_3234_, lean_object* v_toSeqRight_3235_, lean_object* v_inst_3236_, lean_object* v___f_3237_, lean_object* v___f_3238_, lean_object* v___f_3239_, lean_object* v_____do__lift_3240_){
_start:
{
if (lean_obj_tag(v_____do__lift_3240_) == 0)
{
lean_object* v_a_3241_; lean_object* v_a_3242_; lean_object* v___f_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; uint8_t v___x_3246_; 
lean_dec(v___f_3239_);
lean_dec(v___f_3238_);
v_a_3241_ = lean_ctor_get(v_____do__lift_3240_, 0);
lean_inc(v_a_3241_);
v_a_3242_ = lean_ctor_get(v_____do__lift_3240_, 1);
lean_inc(v_a_3242_);
lean_dec_ref_known(v_____do__lift_3240_, 2);
lean_inc(v_toPure_3233_);
v___f_3243_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3243_, 0, v_a_3241_);
lean_closure_set(v___f_3243_, 1, v_toPure_3233_);
v___x_3244_ = lean_array_get_size(v_a_3242_);
v___x_3245_ = lean_box(0);
v___x_3246_ = lean_nat_dec_lt(v___x_3234_, v___x_3244_);
if (v___x_3246_ == 0)
{
lean_object* v___x_3247_; lean_object* v___x_3248_; 
lean_dec(v_a_3242_);
lean_dec(v___f_3237_);
lean_dec_ref(v_inst_3236_);
v___x_3247_ = lean_apply_2(v_toPure_3233_, lean_box(0), v___x_3245_);
v___x_3248_ = lean_apply_4(v_toSeqRight_3235_, lean_box(0), lean_box(0), v___x_3247_, v___f_3243_);
return v___x_3248_;
}
else
{
size_t v___x_3249_; size_t v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
lean_dec(v_toPure_3233_);
v___x_3249_ = ((size_t)0ULL);
v___x_3250_ = lean_usize_of_nat(v___x_3244_);
v___x_3251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3236_, v___f_3237_, v_a_3242_, v___x_3249_, v___x_3250_, v___x_3245_);
v___x_3252_ = lean_apply_4(v_toSeqRight_3235_, lean_box(0), lean_box(0), v___x_3251_, v___f_3243_);
return v___x_3252_;
}
}
else
{
lean_object* v_a_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; uint8_t v___x_3256_; 
lean_dec(v___f_3237_);
v_a_3253_ = lean_ctor_get(v_____do__lift_3240_, 1);
lean_inc(v_a_3253_);
lean_dec_ref_known(v_____do__lift_3240_, 2);
v___x_3254_ = lean_array_get_size(v_a_3253_);
v___x_3255_ = lean_box(0);
v___x_3256_ = lean_nat_dec_lt(v___x_3234_, v___x_3254_);
if (v___x_3256_ == 0)
{
lean_object* v___x_3257_; lean_object* v___x_3258_; 
lean_dec(v_a_3253_);
lean_dec(v___f_3239_);
lean_dec_ref(v_inst_3236_);
v___x_3257_ = lean_apply_2(v_toPure_3233_, lean_box(0), v___x_3255_);
v___x_3258_ = lean_apply_4(v_toSeqRight_3235_, lean_box(0), lean_box(0), v___x_3257_, v___f_3238_);
return v___x_3258_;
}
else
{
size_t v___x_3259_; size_t v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
lean_dec(v_toPure_3233_);
v___x_3259_ = ((size_t)0ULL);
v___x_3260_ = lean_usize_of_nat(v___x_3254_);
v___x_3261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3236_, v___f_3239_, v_a_3253_, v___x_3259_, v___x_3260_, v___x_3255_);
v___x_3262_ = lean_apply_4(v_toSeqRight_3235_, lean_box(0), lean_box(0), v___x_3261_, v___f_3238_);
return v___x_3262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed(lean_object* v_toPure_3263_, lean_object* v___x_3264_, lean_object* v_toSeqRight_3265_, lean_object* v_inst_3266_, lean_object* v___f_3267_, lean_object* v___f_3268_, lean_object* v___f_3269_, lean_object* v_____do__lift_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l_Lake_ELogT_replayLog_x3f___redArg___lam__1(v_toPure_3263_, v___x_3264_, v_toSeqRight_3265_, v_inst_3266_, v___f_3267_, v___f_3268_, v___f_3269_, v_____do__lift_3270_);
lean_dec(v___x_3264_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg(lean_object* v_inst_3272_, lean_object* v_logger_3273_, lean_object* v_inst_3274_, lean_object* v_self_3275_){
_start:
{
lean_object* v_toApplicative_3276_; lean_object* v_toBind_3277_; lean_object* v_toPure_3278_; lean_object* v_toSeqRight_3279_; lean_object* v___f_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___f_3285_; lean_object* v___f_3286_; lean_object* v___x_3287_; 
v_toApplicative_3276_ = lean_ctor_get(v_inst_3272_, 0);
v_toBind_3277_ = lean_ctor_get(v_inst_3272_, 1);
lean_inc(v_toBind_3277_);
v_toPure_3278_ = lean_ctor_get(v_toApplicative_3276_, 1);
lean_inc_n(v_toPure_3278_, 2);
v_toSeqRight_3279_ = lean_ctor_get(v_toApplicative_3276_, 4);
lean_inc(v_toSeqRight_3279_);
v___f_3280_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3280_, 0, v_logger_3273_);
v___x_3281_ = lean_unsigned_to_nat(0u);
v___x_3282_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3283_ = lean_apply_1(v_self_3275_, v___x_3282_);
v___x_3284_ = lean_apply_2(v_inst_3274_, lean_box(0), v___x_3283_);
v___f_3285_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3285_, 0, v_toPure_3278_);
lean_inc_ref(v___f_3280_);
v___f_3286_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_3286_, 0, v_toPure_3278_);
lean_closure_set(v___f_3286_, 1, v___x_3281_);
lean_closure_set(v___f_3286_, 2, v_toSeqRight_3279_);
lean_closure_set(v___f_3286_, 3, v_inst_3272_);
lean_closure_set(v___f_3286_, 4, v___f_3280_);
lean_closure_set(v___f_3286_, 5, v___f_3285_);
lean_closure_set(v___f_3286_, 6, v___f_3280_);
v___x_3287_ = lean_apply_4(v_toBind_3277_, lean_box(0), lean_box(0), v___x_3284_, v___f_3286_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f(lean_object* v_n_3288_, lean_object* v_m_3289_, lean_object* v_00_u03b1_3290_, lean_object* v_inst_3291_, lean_object* v_logger_3292_, lean_object* v_inst_3293_, lean_object* v_self_3294_){
_start:
{
lean_object* v_toApplicative_3295_; lean_object* v_toBind_3296_; lean_object* v_toPure_3297_; lean_object* v_toSeqRight_3298_; lean_object* v___f_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___f_3304_; lean_object* v___f_3305_; lean_object* v___x_3306_; 
v_toApplicative_3295_ = lean_ctor_get(v_inst_3291_, 0);
v_toBind_3296_ = lean_ctor_get(v_inst_3291_, 1);
lean_inc(v_toBind_3296_);
v_toPure_3297_ = lean_ctor_get(v_toApplicative_3295_, 1);
lean_inc_n(v_toPure_3297_, 2);
v_toSeqRight_3298_ = lean_ctor_get(v_toApplicative_3295_, 4);
lean_inc(v_toSeqRight_3298_);
v___f_3299_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3299_, 0, v_logger_3292_);
v___x_3300_ = lean_unsigned_to_nat(0u);
v___x_3301_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3302_ = lean_apply_1(v_self_3294_, v___x_3301_);
v___x_3303_ = lean_apply_2(v_inst_3293_, lean_box(0), v___x_3302_);
v___f_3304_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3304_, 0, v_toPure_3297_);
lean_inc_ref(v___f_3299_);
v___f_3305_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_3305_, 0, v_toPure_3297_);
lean_closure_set(v___f_3305_, 1, v___x_3300_);
lean_closure_set(v___f_3305_, 2, v_toSeqRight_3298_);
lean_closure_set(v___f_3305_, 3, v_inst_3291_);
lean_closure_set(v___f_3305_, 4, v___f_3299_);
lean_closure_set(v___f_3305_, 5, v___f_3304_);
lean_closure_set(v___f_3305_, 6, v___f_3299_);
v___x_3306_ = lean_apply_4(v_toBind_3296_, lean_box(0), lean_box(0), v___x_3303_, v___f_3305_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg___lam__3(lean_object* v_toPure_3307_, lean_object* v_a_3308_, lean_object* v_x_3309_){
_start:
{
lean_object* v___x_3310_; 
v___x_3310_ = lean_apply_2(v_toPure_3307_, lean_box(0), v_a_3308_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg___lam__0(lean_object* v_toApplicative_3311_, lean_object* v_toPure_3312_, lean_object* v___x_3313_, lean_object* v_toSeqRight_3314_, lean_object* v_inst_3315_, lean_object* v___f_3316_, lean_object* v___f_3317_, lean_object* v___f_3318_, lean_object* v_____do__lift_3319_){
_start:
{
if (lean_obj_tag(v_____do__lift_3319_) == 0)
{
lean_object* v_a_3320_; lean_object* v_a_3321_; lean_object* v_toPure_3322_; lean_object* v___f_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; uint8_t v___x_3326_; 
lean_dec(v___f_3318_);
lean_dec(v___f_3317_);
v_a_3320_ = lean_ctor_get(v_____do__lift_3319_, 0);
lean_inc(v_a_3320_);
v_a_3321_ = lean_ctor_get(v_____do__lift_3319_, 1);
lean_inc(v_a_3321_);
lean_dec_ref_known(v_____do__lift_3319_, 2);
v_toPure_3322_ = lean_ctor_get(v_toApplicative_3311_, 1);
lean_inc(v_toPure_3322_);
lean_dec_ref(v_toApplicative_3311_);
v___f_3323_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog___redArg___lam__3), 3, 2);
lean_closure_set(v___f_3323_, 0, v_toPure_3312_);
lean_closure_set(v___f_3323_, 1, v_a_3320_);
v___x_3324_ = lean_array_get_size(v_a_3321_);
v___x_3325_ = lean_box(0);
v___x_3326_ = lean_nat_dec_lt(v___x_3313_, v___x_3324_);
if (v___x_3326_ == 0)
{
lean_object* v___x_3327_; lean_object* v___x_3328_; 
lean_dec(v_a_3321_);
lean_dec(v___f_3316_);
lean_dec_ref(v_inst_3315_);
v___x_3327_ = lean_apply_2(v_toPure_3322_, lean_box(0), v___x_3325_);
v___x_3328_ = lean_apply_4(v_toSeqRight_3314_, lean_box(0), lean_box(0), v___x_3327_, v___f_3323_);
return v___x_3328_;
}
else
{
size_t v___x_3329_; size_t v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
lean_dec(v_toPure_3322_);
v___x_3329_ = ((size_t)0ULL);
v___x_3330_ = lean_usize_of_nat(v___x_3324_);
v___x_3331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3315_, v___f_3316_, v_a_3321_, v___x_3329_, v___x_3330_, v___x_3325_);
v___x_3332_ = lean_apply_4(v_toSeqRight_3314_, lean_box(0), lean_box(0), v___x_3331_, v___f_3323_);
return v___x_3332_;
}
}
else
{
lean_object* v_a_3333_; lean_object* v_toPure_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; uint8_t v___x_3337_; 
lean_dec(v___f_3316_);
lean_dec(v_toPure_3312_);
v_a_3333_ = lean_ctor_get(v_____do__lift_3319_, 1);
lean_inc(v_a_3333_);
lean_dec_ref_known(v_____do__lift_3319_, 2);
v_toPure_3334_ = lean_ctor_get(v_toApplicative_3311_, 1);
lean_inc(v_toPure_3334_);
lean_dec_ref(v_toApplicative_3311_);
v___x_3335_ = lean_array_get_size(v_a_3333_);
v___x_3336_ = lean_box(0);
v___x_3337_ = lean_nat_dec_lt(v___x_3313_, v___x_3335_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3338_; lean_object* v___x_3339_; 
lean_dec(v_a_3333_);
lean_dec(v___f_3318_);
lean_dec_ref(v_inst_3315_);
v___x_3338_ = lean_apply_2(v_toPure_3334_, lean_box(0), v___x_3336_);
v___x_3339_ = lean_apply_4(v_toSeqRight_3314_, lean_box(0), lean_box(0), v___x_3338_, v___f_3317_);
return v___x_3339_;
}
else
{
size_t v___x_3340_; size_t v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
lean_dec(v_toPure_3334_);
v___x_3340_ = ((size_t)0ULL);
v___x_3341_ = lean_usize_of_nat(v___x_3335_);
v___x_3342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3315_, v___f_3318_, v_a_3333_, v___x_3340_, v___x_3341_, v___x_3336_);
v___x_3343_ = lean_apply_4(v_toSeqRight_3314_, lean_box(0), lean_box(0), v___x_3342_, v___f_3317_);
return v___x_3343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg___lam__0___boxed(lean_object* v_toApplicative_3344_, lean_object* v_toPure_3345_, lean_object* v___x_3346_, lean_object* v_toSeqRight_3347_, lean_object* v_inst_3348_, lean_object* v___f_3349_, lean_object* v___f_3350_, lean_object* v___f_3351_, lean_object* v_____do__lift_3352_){
_start:
{
lean_object* v_res_3353_; 
v_res_3353_ = l_Lake_ELogT_replayLog___redArg___lam__0(v_toApplicative_3344_, v_toPure_3345_, v___x_3346_, v_toSeqRight_3347_, v_inst_3348_, v___f_3349_, v___f_3350_, v___f_3351_, v_____do__lift_3352_);
lean_dec(v___x_3346_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg(lean_object* v_inst_3354_, lean_object* v_inst_3355_, lean_object* v_logger_3356_, lean_object* v_inst_3357_, lean_object* v_self_3358_){
_start:
{
lean_object* v_toApplicative_3359_; lean_object* v_toApplicative_3360_; lean_object* v_toBind_3361_; lean_object* v_failure_3362_; lean_object* v_toPure_3363_; lean_object* v_toSeqRight_3364_; lean_object* v___f_3365_; lean_object* v___f_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___f_3371_; lean_object* v___x_3372_; 
v_toApplicative_3359_ = lean_ctor_get(v_inst_3354_, 0);
lean_inc_ref(v_toApplicative_3359_);
v_toApplicative_3360_ = lean_ctor_get(v_inst_3355_, 0);
lean_inc_ref(v_toApplicative_3360_);
v_toBind_3361_ = lean_ctor_get(v_inst_3355_, 1);
lean_inc(v_toBind_3361_);
v_failure_3362_ = lean_ctor_get(v_inst_3354_, 1);
lean_inc(v_failure_3362_);
lean_dec_ref(v_inst_3354_);
v_toPure_3363_ = lean_ctor_get(v_toApplicative_3359_, 1);
lean_inc(v_toPure_3363_);
v_toSeqRight_3364_ = lean_ctor_get(v_toApplicative_3359_, 4);
lean_inc(v_toSeqRight_3364_);
lean_dec_ref(v_toApplicative_3359_);
v___f_3365_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3365_, 0, v_logger_3356_);
v___f_3366_ = lean_alloc_closure((void*)(l_Lake_MonadLog_error___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3366_, 0, v_failure_3362_);
v___x_3367_ = lean_unsigned_to_nat(0u);
v___x_3368_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3369_ = lean_apply_1(v_self_3358_, v___x_3368_);
v___x_3370_ = lean_apply_2(v_inst_3357_, lean_box(0), v___x_3369_);
lean_inc_ref(v___f_3365_);
v___f_3371_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3371_, 0, v_toApplicative_3360_);
lean_closure_set(v___f_3371_, 1, v_toPure_3363_);
lean_closure_set(v___f_3371_, 2, v___x_3367_);
lean_closure_set(v___f_3371_, 3, v_toSeqRight_3364_);
lean_closure_set(v___f_3371_, 4, v_inst_3355_);
lean_closure_set(v___f_3371_, 5, v___f_3365_);
lean_closure_set(v___f_3371_, 6, v___f_3366_);
lean_closure_set(v___f_3371_, 7, v___f_3365_);
v___x_3372_ = lean_apply_4(v_toBind_3361_, lean_box(0), lean_box(0), v___x_3370_, v___f_3371_);
return v___x_3372_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog(lean_object* v_n_3373_, lean_object* v_m_3374_, lean_object* v_00_u03b1_3375_, lean_object* v_inst_3376_, lean_object* v_inst_3377_, lean_object* v_logger_3378_, lean_object* v_inst_3379_, lean_object* v_self_3380_){
_start:
{
lean_object* v_toApplicative_3381_; lean_object* v_toApplicative_3382_; lean_object* v_toBind_3383_; lean_object* v_failure_3384_; lean_object* v_toPure_3385_; lean_object* v_toSeqRight_3386_; lean_object* v___f_3387_; lean_object* v___f_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___f_3393_; lean_object* v___x_3394_; 
v_toApplicative_3381_ = lean_ctor_get(v_inst_3376_, 0);
lean_inc_ref(v_toApplicative_3381_);
v_toApplicative_3382_ = lean_ctor_get(v_inst_3377_, 0);
lean_inc_ref(v_toApplicative_3382_);
v_toBind_3383_ = lean_ctor_get(v_inst_3377_, 1);
lean_inc(v_toBind_3383_);
v_failure_3384_ = lean_ctor_get(v_inst_3376_, 1);
lean_inc(v_failure_3384_);
lean_dec_ref(v_inst_3376_);
v_toPure_3385_ = lean_ctor_get(v_toApplicative_3381_, 1);
lean_inc(v_toPure_3385_);
v_toSeqRight_3386_ = lean_ctor_get(v_toApplicative_3381_, 4);
lean_inc(v_toSeqRight_3386_);
lean_dec_ref(v_toApplicative_3381_);
v___f_3387_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3387_, 0, v_logger_3378_);
v___f_3388_ = lean_alloc_closure((void*)(l_Lake_MonadLog_error___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3388_, 0, v_failure_3384_);
v___x_3389_ = lean_unsigned_to_nat(0u);
v___x_3390_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3391_ = lean_apply_1(v_self_3380_, v___x_3390_);
v___x_3392_ = lean_apply_2(v_inst_3379_, lean_box(0), v___x_3391_);
lean_inc_ref(v___f_3387_);
v___f_3393_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3393_, 0, v_toApplicative_3382_);
lean_closure_set(v___f_3393_, 1, v_toPure_3385_);
lean_closure_set(v___f_3393_, 2, v___x_3389_);
lean_closure_set(v___f_3393_, 3, v_toSeqRight_3386_);
lean_closure_set(v___f_3393_, 4, v_inst_3377_);
lean_closure_set(v___f_3393_, 5, v___f_3387_);
lean_closure_set(v___f_3393_, 6, v___f_3388_);
lean_closure_set(v___f_3393_, 7, v___f_3387_);
v___x_3394_ = lean_apply_4(v_toBind_3383_, lean_box(0), lean_box(0), v___x_3392_, v___f_3393_);
return v___x_3394_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___redArg___lam__0(lean_object* v_val_3395_, uint8_t v_outLv_3396_, uint8_t v_val_3397_, lean_object* v_inst_3398_, lean_object* v_e_3399_){
_start:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3400_ = lean_box(v_outLv_3396_);
v___x_3401_ = lean_box(v_val_3397_);
v___x_3402_ = lean_alloc_closure((void*)(l_Lake_logToStream___boxed), 5, 4);
lean_closure_set(v___x_3402_, 0, v_e_3399_);
lean_closure_set(v___x_3402_, 1, v_val_3395_);
lean_closure_set(v___x_3402_, 2, v___x_3400_);
lean_closure_set(v___x_3402_, 3, v___x_3401_);
v___x_3403_ = lean_apply_2(v_inst_3398_, lean_box(0), v___x_3402_);
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___redArg___lam__0___boxed(lean_object* v_val_3404_, lean_object* v_outLv_3405_, lean_object* v_val_3406_, lean_object* v_inst_3407_, lean_object* v_e_3408_){
_start:
{
uint8_t v_outLv_boxed_3409_; uint8_t v_val_44__boxed_3410_; lean_object* v_res_3411_; 
v_outLv_boxed_3409_ = lean_unbox(v_outLv_3405_);
v_val_44__boxed_3410_ = lean_unbox(v_val_3406_);
v_res_3411_ = l_Lake_LogConfig_getLogger___redArg___lam__0(v_val_3404_, v_outLv_boxed_3409_, v_val_44__boxed_3410_, v_inst_3407_, v_e_3408_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___redArg(lean_object* v_inst_3412_, lean_object* v_self_3413_){
_start:
{
uint8_t v_outLv_3415_; uint8_t v_ansiMode_3416_; lean_object* v_out_3417_; lean_object* v___x_3418_; uint8_t v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___f_3422_; 
v_outLv_3415_ = lean_ctor_get_uint8(v_self_3413_, sizeof(void*)*1 + 1);
v_ansiMode_3416_ = lean_ctor_get_uint8(v_self_3413_, sizeof(void*)*1 + 2);
v_out_3417_ = lean_ctor_get(v_self_3413_, 0);
v___x_3418_ = l_Lake_OutStream_get(v_out_3417_);
lean_inc_ref(v___x_3418_);
v___x_3419_ = l_Lake_AnsiMode_isEnabled(v___x_3418_, v_ansiMode_3416_);
v___x_3420_ = lean_box(v_outLv_3415_);
v___x_3421_ = lean_box(v___x_3419_);
v___f_3422_ = lean_alloc_closure((void*)(l_Lake_LogConfig_getLogger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3422_, 0, v___x_3418_);
lean_closure_set(v___f_3422_, 1, v___x_3420_);
lean_closure_set(v___f_3422_, 2, v___x_3421_);
lean_closure_set(v___f_3422_, 3, v_inst_3412_);
return v___f_3422_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___redArg___boxed(lean_object* v_inst_3423_, lean_object* v_self_3424_, lean_object* v_a_3425_){
_start:
{
lean_object* v_res_3426_; 
v_res_3426_ = l_Lake_LogConfig_getLogger___redArg(v_inst_3423_, v_self_3424_);
lean_dec_ref(v_self_3424_);
return v_res_3426_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger(lean_object* v_m_3427_, lean_object* v_inst_3428_, lean_object* v_self_3429_){
_start:
{
uint8_t v_outLv_3431_; uint8_t v_ansiMode_3432_; lean_object* v_out_3433_; lean_object* v___x_3434_; uint8_t v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___f_3438_; 
v_outLv_3431_ = lean_ctor_get_uint8(v_self_3429_, sizeof(void*)*1 + 1);
v_ansiMode_3432_ = lean_ctor_get_uint8(v_self_3429_, sizeof(void*)*1 + 2);
v_out_3433_ = lean_ctor_get(v_self_3429_, 0);
v___x_3434_ = l_Lake_OutStream_get(v_out_3433_);
lean_inc_ref(v___x_3434_);
v___x_3435_ = l_Lake_AnsiMode_isEnabled(v___x_3434_, v_ansiMode_3432_);
v___x_3436_ = lean_box(v_outLv_3431_);
v___x_3437_ = lean_box(v___x_3435_);
v___f_3438_ = lean_alloc_closure((void*)(l_Lake_LogConfig_getLogger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3438_, 0, v___x_3434_);
lean_closure_set(v___f_3438_, 1, v___x_3436_);
lean_closure_set(v___f_3438_, 2, v___x_3437_);
lean_closure_set(v___f_3438_, 3, v_inst_3428_);
return v___f_3438_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___boxed(lean_object* v_m_3439_, lean_object* v_inst_3440_, lean_object* v_self_3441_, lean_object* v_a_3442_){
_start:
{
lean_object* v_res_3443_; 
v_res_3443_ = l_Lake_LogConfig_getLogger(v_m_3439_, v_inst_3440_, v_self_3441_);
lean_dec_ref(v_self_3441_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_instMonadLiftIO___lam__0(lean_object* v_00_u03b1_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_){
_start:
{
lean_object* v___x_3448_; 
v___x_3448_ = lean_apply_1(v___y_3445_, lean_box(0));
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; lean_object* v___x_3450_; 
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
lean_inc(v_a_3449_);
lean_dec_ref_known(v___x_3448_, 1);
v___x_3450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3450_, 0, v_a_3449_);
lean_ctor_set(v___x_3450_, 1, v___y_3446_);
return v___x_3450_;
}
else
{
lean_object* v_a_3451_; lean_object* v___x_3452_; uint8_t v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v_a_3451_ = lean_ctor_get(v___x_3448_, 0);
lean_inc(v_a_3451_);
lean_dec_ref_known(v___x_3448_, 1);
v___x_3452_ = lean_io_error_to_string(v_a_3451_);
v___x_3453_ = 3;
v___x_3454_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3454_, 0, v___x_3452_);
lean_ctor_set_uint8(v___x_3454_, sizeof(void*)*1, v___x_3453_);
v___x_3455_ = lean_array_get_size(v___y_3446_);
v___x_3456_ = lean_array_push(v___y_3446_, v___x_3454_);
v___x_3457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3455_);
lean_ctor_set(v___x_3457_, 1, v___x_3456_);
return v___x_3457_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_instMonadLiftIO___lam__0___boxed(lean_object* v_00_u03b1_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_){
_start:
{
lean_object* v_res_3462_; 
v_res_3462_ = l_Lake_LogIO_instMonadLiftIO___lam__0(v_00_u03b1_3458_, v___y_3459_, v___y_3460_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg___lam__0(lean_object* v_val_3465_, uint8_t v___y_3466_, uint8_t v_val_3467_, lean_object* v_x_3468_, lean_object* v___y_3469_){
_start:
{
lean_object* v___x_3471_; 
v___x_3471_ = l_Lake_logToStream(v___y_3469_, v_val_3465_, v___y_3466_, v_val_3467_);
return v___x_3471_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed(lean_object* v_val_3472_, lean_object* v___y_3473_, lean_object* v_val_3474_, lean_object* v_x_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
uint8_t v___y_740__boxed_3478_; uint8_t v_val_741__boxed_3479_; lean_object* v_res_3480_; 
v___y_740__boxed_3478_ = lean_unbox(v___y_3473_);
v_val_741__boxed_3479_ = lean_unbox(v_val_3474_);
v_res_3480_ = l_Lake_LogIO_toBaseIO___redArg___lam__0(v_val_3472_, v___y_740__boxed_3478_, v_val_741__boxed_3479_, v_x_3475_, v___y_3476_);
lean_dec_ref(v___y_3476_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg(lean_object* v_self_3481_, lean_object* v_cfg_3482_){
_start:
{
uint8_t v___y_3485_; lean_object* v___y_3486_; lean_object* v___x_3488_; uint8_t v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; uint8_t v___y_3493_; lean_object* v___y_3510_; lean_object* v___y_3511_; uint8_t v___y_3512_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3488_ = l_instMonadBaseIO;
v___x_3514_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3515_ = lean_apply_2(v_self_3481_, v___x_3514_, lean_box(0));
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v_a_3517_; uint8_t v_failLv_3518_; uint8_t v_outLv_3519_; lean_object* v___x_3520_; uint8_t v___x_3521_; uint8_t v___x_3522_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3516_);
v_a_3517_ = lean_ctor_get(v___x_3515_, 1);
lean_inc(v_a_3517_);
lean_dec_ref_known(v___x_3515_, 2);
v_failLv_3518_ = lean_ctor_get_uint8(v_cfg_3482_, sizeof(void*)*1);
v_outLv_3519_ = lean_ctor_get_uint8(v_cfg_3482_, sizeof(void*)*1 + 1);
v___x_3520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3520_, 0, v_a_3516_);
v___x_3521_ = l_Lake_Log_maxLv(v_a_3517_);
v___x_3522_ = l_Lake_instOrdLogLevel_ord(v_failLv_3518_, v___x_3521_);
if (v___x_3522_ == 2)
{
uint8_t v___x_3523_; 
v___x_3523_ = 0;
v___y_3490_ = v___x_3523_;
v___y_3491_ = v___x_3520_;
v___y_3492_ = v_a_3517_;
v___y_3493_ = v_outLv_3519_;
goto v___jp_3489_;
}
else
{
uint8_t v___x_3524_; 
v___x_3524_ = 1;
v___y_3510_ = v___x_3520_;
v___y_3511_ = v_a_3517_;
v___y_3512_ = v___x_3524_;
goto v___jp_3509_;
}
}
else
{
lean_object* v_a_3525_; lean_object* v___x_3526_; uint8_t v___x_3527_; 
v_a_3525_ = lean_ctor_get(v___x_3515_, 1);
lean_inc(v_a_3525_);
lean_dec_ref_known(v___x_3515_, 2);
v___x_3526_ = lean_box(0);
v___x_3527_ = 1;
v___y_3510_ = v___x_3526_;
v___y_3511_ = v_a_3525_;
v___y_3512_ = v___x_3527_;
goto v___jp_3509_;
}
v___jp_3484_:
{
if (v___y_3485_ == 0)
{
return v___y_3486_;
}
else
{
lean_object* v___x_3487_; 
lean_dec(v___y_3486_);
v___x_3487_ = lean_box(0);
return v___x_3487_;
}
}
v___jp_3489_:
{
uint8_t v_ansiMode_3494_; lean_object* v_out_3495_; lean_object* v___x_3496_; uint8_t v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; uint8_t v___x_3500_; 
v_ansiMode_3494_ = lean_ctor_get_uint8(v_cfg_3482_, sizeof(void*)*1 + 2);
v_out_3495_ = lean_ctor_get(v_cfg_3482_, 0);
v___x_3496_ = l_Lake_OutStream_get(v_out_3495_);
lean_inc_ref(v___x_3496_);
v___x_3497_ = l_Lake_AnsiMode_isEnabled(v___x_3496_, v_ansiMode_3494_);
v___x_3498_ = lean_unsigned_to_nat(0u);
v___x_3499_ = lean_array_get_size(v___y_3492_);
v___x_3500_ = lean_nat_dec_lt(v___x_3498_, v___x_3499_);
if (v___x_3500_ == 0)
{
lean_dec_ref(v___x_3496_);
lean_dec_ref(v___y_3492_);
v___y_3485_ = v___y_3490_;
v___y_3486_ = v___y_3491_;
goto v___jp_3484_;
}
else
{
lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___f_3503_; lean_object* v___x_3504_; size_t v___x_3505_; size_t v___x_3506_; lean_object* v___x_521__overap_3507_; lean_object* v___x_3508_; 
v___x_3501_ = lean_box(v___y_3493_);
v___x_3502_ = lean_box(v___x_3497_);
v___f_3503_ = lean_alloc_closure((void*)(l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_3503_, 0, v___x_3496_);
lean_closure_set(v___f_3503_, 1, v___x_3501_);
lean_closure_set(v___f_3503_, 2, v___x_3502_);
v___x_3504_ = lean_box(0);
v___x_3505_ = ((size_t)0ULL);
v___x_3506_ = lean_usize_of_nat(v___x_3499_);
v___x_521__overap_3507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3488_, v___f_3503_, v___y_3492_, v___x_3505_, v___x_3506_, v___x_3504_);
v___x_3508_ = lean_apply_1(v___x_521__overap_3507_, lean_box(0));
v___y_3485_ = v___y_3490_;
v___y_3486_ = v___y_3491_;
goto v___jp_3484_;
}
}
v___jp_3509_:
{
uint8_t v___x_3513_; 
v___x_3513_ = 0;
v___y_3490_ = v___y_3512_;
v___y_3491_ = v___y_3510_;
v___y_3492_ = v___y_3511_;
v___y_3493_ = v___x_3513_;
goto v___jp_3489_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg___boxed(lean_object* v_self_3528_, lean_object* v_cfg_3529_, lean_object* v_a_3530_){
_start:
{
lean_object* v_res_3531_; 
v_res_3531_ = l_Lake_LogIO_toBaseIO___redArg(v_self_3528_, v_cfg_3529_);
lean_dec_ref(v_cfg_3529_);
return v_res_3531_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO(lean_object* v_00_u03b1_3532_, lean_object* v_self_3533_, lean_object* v_cfg_3534_){
_start:
{
uint8_t v___y_3537_; lean_object* v___y_3538_; lean_object* v___x_3540_; uint8_t v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; uint8_t v___y_3545_; lean_object* v___y_3562_; lean_object* v___y_3563_; uint8_t v___y_3564_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3540_ = l_instMonadBaseIO;
v___x_3566_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3567_ = lean_apply_2(v_self_3533_, v___x_3566_, lean_box(0));
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; lean_object* v_a_3569_; uint8_t v_failLv_3570_; uint8_t v_outLv_3571_; lean_object* v___x_3572_; uint8_t v___x_3573_; uint8_t v___x_3574_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
lean_inc(v_a_3568_);
v_a_3569_ = lean_ctor_get(v___x_3567_, 1);
lean_inc(v_a_3569_);
lean_dec_ref_known(v___x_3567_, 2);
v_failLv_3570_ = lean_ctor_get_uint8(v_cfg_3534_, sizeof(void*)*1);
v_outLv_3571_ = lean_ctor_get_uint8(v_cfg_3534_, sizeof(void*)*1 + 1);
v___x_3572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3572_, 0, v_a_3568_);
v___x_3573_ = l_Lake_Log_maxLv(v_a_3569_);
v___x_3574_ = l_Lake_instOrdLogLevel_ord(v_failLv_3570_, v___x_3573_);
if (v___x_3574_ == 2)
{
uint8_t v___x_3575_; 
v___x_3575_ = 0;
v___y_3542_ = v___x_3575_;
v___y_3543_ = v___x_3572_;
v___y_3544_ = v_a_3569_;
v___y_3545_ = v_outLv_3571_;
goto v___jp_3541_;
}
else
{
uint8_t v___x_3576_; 
v___x_3576_ = 1;
v___y_3562_ = v___x_3572_;
v___y_3563_ = v_a_3569_;
v___y_3564_ = v___x_3576_;
goto v___jp_3561_;
}
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3578_; uint8_t v___x_3579_; 
v_a_3577_ = lean_ctor_get(v___x_3567_, 1);
lean_inc(v_a_3577_);
lean_dec_ref_known(v___x_3567_, 2);
v___x_3578_ = lean_box(0);
v___x_3579_ = 1;
v___y_3562_ = v___x_3578_;
v___y_3563_ = v_a_3577_;
v___y_3564_ = v___x_3579_;
goto v___jp_3561_;
}
v___jp_3536_:
{
if (v___y_3537_ == 0)
{
return v___y_3538_;
}
else
{
lean_object* v___x_3539_; 
lean_dec(v___y_3538_);
v___x_3539_ = lean_box(0);
return v___x_3539_;
}
}
v___jp_3541_:
{
uint8_t v_ansiMode_3546_; lean_object* v_out_3547_; lean_object* v___x_3548_; uint8_t v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; uint8_t v___x_3552_; 
v_ansiMode_3546_ = lean_ctor_get_uint8(v_cfg_3534_, sizeof(void*)*1 + 2);
v_out_3547_ = lean_ctor_get(v_cfg_3534_, 0);
v___x_3548_ = l_Lake_OutStream_get(v_out_3547_);
lean_inc_ref(v___x_3548_);
v___x_3549_ = l_Lake_AnsiMode_isEnabled(v___x_3548_, v_ansiMode_3546_);
v___x_3550_ = lean_unsigned_to_nat(0u);
v___x_3551_ = lean_array_get_size(v___y_3544_);
v___x_3552_ = lean_nat_dec_lt(v___x_3550_, v___x_3551_);
if (v___x_3552_ == 0)
{
lean_dec_ref(v___x_3548_);
lean_dec_ref(v___y_3544_);
v___y_3537_ = v___y_3542_;
v___y_3538_ = v___y_3543_;
goto v___jp_3536_;
}
else
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___f_3555_; lean_object* v___x_3556_; size_t v___x_3557_; size_t v___x_3558_; lean_object* v___x_665__overap_3559_; lean_object* v___x_3560_; 
v___x_3553_ = lean_box(v___y_3545_);
v___x_3554_ = lean_box(v___x_3549_);
v___f_3555_ = lean_alloc_closure((void*)(l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_3555_, 0, v___x_3548_);
lean_closure_set(v___f_3555_, 1, v___x_3553_);
lean_closure_set(v___f_3555_, 2, v___x_3554_);
v___x_3556_ = lean_box(0);
v___x_3557_ = ((size_t)0ULL);
v___x_3558_ = lean_usize_of_nat(v___x_3551_);
v___x_665__overap_3559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3540_, v___f_3555_, v___y_3544_, v___x_3557_, v___x_3558_, v___x_3556_);
v___x_3560_ = lean_apply_1(v___x_665__overap_3559_, lean_box(0));
v___y_3537_ = v___y_3542_;
v___y_3538_ = v___y_3543_;
goto v___jp_3536_;
}
}
v___jp_3561_:
{
uint8_t v___x_3565_; 
v___x_3565_ = 0;
v___y_3542_ = v___y_3564_;
v___y_3543_ = v___y_3562_;
v___y_3544_ = v___y_3563_;
v___y_3545_ = v___x_3565_;
goto v___jp_3541_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___boxed(lean_object* v_00_u03b1_3580_, lean_object* v_self_3581_, lean_object* v_cfg_3582_, lean_object* v_a_3583_){
_start:
{
lean_object* v_res_3584_; 
v_res_3584_ = l_Lake_LogIO_toBaseIO(v_00_u03b1_3580_, v_self_3581_, v_cfg_3582_);
lean_dec_ref(v_cfg_3582_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_captureLog___redArg(lean_object* v_inst_3585_, lean_object* v_self_3586_, lean_object* v_log_3587_){
_start:
{
lean_object* v_map_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; 
v_map_3588_ = lean_ctor_get(v_inst_3585_, 0);
lean_inc(v_map_3588_);
lean_dec_ref(v_inst_3585_);
v___x_3589_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3590_ = lean_apply_1(v_self_3586_, v_log_3587_);
v___x_3591_ = lean_apply_4(v_map_3588_, lean_box(0), lean_box(0), v___x_3589_, v___x_3590_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_captureLog(lean_object* v_m_3592_, lean_object* v_00_u03b1_3593_, lean_object* v_inst_3594_, lean_object* v_self_3595_, lean_object* v_log_3596_){
_start:
{
lean_object* v_map_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
v_map_3597_ = lean_ctor_get(v_inst_3594_, 0);
lean_inc(v_map_3597_);
lean_dec_ref(v_inst_3594_);
v___x_3598_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3599_ = lean_apply_1(v_self_3595_, v_log_3596_);
v___x_3600_ = lean_apply_4(v_map_3597_, lean_box(0), lean_box(0), v___x_3598_, v___x_3599_);
return v___x_3600_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadError___lam__0(lean_object* v_00_u03b1_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
uint8_t v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3605_ = 3;
v___x_3606_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3606_, 0, v___y_3602_);
lean_ctor_set_uint8(v___x_3606_, sizeof(void*)*1, v___x_3605_);
lean_inc_ref(v___y_3603_);
v___x_3607_ = lean_apply_2(v___y_3603_, v___x_3606_, lean_box(0));
v___x_3608_ = lean_box(0);
v___x_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3608_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadError___lam__0___boxed(lean_object* v_00_u03b1_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l_Lake_LoggerIO_instMonadError___lam__0(v_00_u03b1_3610_, v___y_3611_, v___y_3612_);
lean_dec_ref(v___y_3612_);
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftIO___lam__0(lean_object* v_00_u03b1_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
lean_object* v___x_3621_; 
v___x_3621_ = lean_apply_1(v___y_3618_, lean_box(0));
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3629_; 
v_a_3622_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3624_ = v___x_3621_;
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___x_3621_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3627_; 
if (v_isShared_3625_ == 0)
{
v___x_3627_ = v___x_3624_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_a_3622_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
}
else
{
lean_object* v_a_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3642_; 
v_a_3630_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3632_ = v___x_3621_;
v_isShared_3633_ = v_isSharedCheck_3642_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_a_3630_);
lean_dec(v___x_3621_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3642_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___x_3634_; uint8_t v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3640_; 
v___x_3634_ = lean_io_error_to_string(v_a_3630_);
v___x_3635_ = 3;
v___x_3636_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3636_, 0, v___x_3634_);
lean_ctor_set_uint8(v___x_3636_, sizeof(void*)*1, v___x_3635_);
lean_inc_ref(v___y_3619_);
v___x_3637_ = lean_apply_2(v___y_3619_, v___x_3636_, lean_box(0));
v___x_3638_ = lean_box(0);
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 0, v___x_3638_);
v___x_3640_ = v___x_3632_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v___x_3638_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftIO___lam__0___boxed(lean_object* v_00_u03b1_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
lean_object* v_res_3647_; 
v_res_3647_ = l_Lake_LoggerIO_instMonadLiftIO___lam__0(v_00_u03b1_3643_, v___y_3644_, v___y_3645_);
lean_dec_ref(v___y_3645_);
return v_res_3647_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__0(lean_object* v_x_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
lean_inc_ref(v___y_3652_);
v___x_3654_ = lean_apply_2(v___y_3652_, v___y_3651_, lean_box(0));
v___x_3655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3654_);
return v___x_3655_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__0___boxed(lean_object* v_x_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
lean_object* v_res_3660_; 
v_res_3660_ = l_Lake_LoggerIO_instMonadLiftLogIO___lam__0(v_x_3656_, v___y_3657_, v___y_3658_);
lean_dec_ref(v___y_3658_);
return v_res_3660_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__2(lean_object* v___x_3661_, lean_object* v___f_3662_, lean_object* v___f_3663_, lean_object* v_00_u03b1_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3668_ = lean_unsigned_to_nat(0u);
v___x_3669_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3670_ = lean_apply_2(v___y_3665_, v___x_3669_, lean_box(0));
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_a_3671_; lean_object* v_a_3672_; lean_object* v___x_3673_; uint8_t v___x_3674_; 
lean_dec_ref(v___f_3663_);
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
lean_inc(v_a_3671_);
v_a_3672_ = lean_ctor_get(v___x_3670_, 1);
lean_inc(v_a_3672_);
lean_dec_ref_known(v___x_3670_, 2);
v___x_3673_ = lean_array_get_size(v_a_3672_);
v___x_3674_ = lean_nat_dec_lt(v___x_3668_, v___x_3673_);
if (v___x_3674_ == 0)
{
lean_object* v___x_3675_; 
lean_dec(v_a_3672_);
lean_dec_ref(v___f_3662_);
lean_dec_ref(v___x_3661_);
v___x_3675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3675_, 0, v_a_3671_);
return v___x_3675_;
}
else
{
lean_object* v___x_3676_; size_t v___x_3677_; size_t v___x_3678_; lean_object* v___x_1294__overap_3679_; lean_object* v___x_3680_; 
v___x_3676_ = lean_box(0);
v___x_3677_ = ((size_t)0ULL);
v___x_3678_ = lean_usize_of_nat(v___x_3673_);
v___x_1294__overap_3679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3661_, v___f_3662_, v_a_3672_, v___x_3677_, v___x_3678_, v___x_3676_);
lean_inc_ref(v___y_3666_);
v___x_3680_ = lean_apply_2(v___x_1294__overap_3679_, v___y_3666_, lean_box(0));
if (lean_obj_tag(v___x_3680_) == 0)
{
lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3687_; 
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3687_ == 0)
{
lean_object* v_unused_3688_; 
v_unused_3688_ = lean_ctor_get(v___x_3680_, 0);
lean_dec(v_unused_3688_);
v___x_3682_ = v___x_3680_;
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
else
{
lean_dec(v___x_3680_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3685_; 
if (v_isShared_3683_ == 0)
{
lean_ctor_set(v___x_3682_, 0, v_a_3671_);
v___x_3685_ = v___x_3682_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3671_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
else
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3696_; 
lean_dec(v_a_3671_);
v_a_3689_ = lean_ctor_get(v___x_3680_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3691_ = v___x_3680_;
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3680_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3694_; 
if (v_isShared_3692_ == 0)
{
v___x_3694_ = v___x_3691_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_a_3689_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
}
}
}
else
{
lean_object* v_a_3697_; lean_object* v___x_3698_; uint8_t v___x_3699_; 
lean_dec_ref(v___f_3662_);
v_a_3697_ = lean_ctor_get(v___x_3670_, 1);
lean_inc(v_a_3697_);
lean_dec_ref_known(v___x_3670_, 2);
v___x_3698_ = lean_array_get_size(v_a_3697_);
v___x_3699_ = lean_nat_dec_lt(v___x_3668_, v___x_3698_);
if (v___x_3699_ == 0)
{
lean_object* v___x_3700_; lean_object* v___x_3701_; 
lean_dec(v_a_3697_);
lean_dec_ref(v___f_3663_);
lean_dec_ref(v___x_3661_);
v___x_3700_ = lean_box(0);
v___x_3701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3700_);
return v___x_3701_;
}
else
{
lean_object* v___x_3702_; size_t v___x_3703_; size_t v___x_3704_; lean_object* v___x_1310__overap_3705_; lean_object* v___x_3706_; 
v___x_3702_ = lean_box(0);
v___x_3703_ = ((size_t)0ULL);
v___x_3704_ = lean_usize_of_nat(v___x_3698_);
v___x_1310__overap_3705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3661_, v___f_3663_, v_a_3697_, v___x_3703_, v___x_3704_, v___x_3702_);
lean_inc_ref(v___y_3666_);
v___x_3706_ = lean_apply_2(v___x_1310__overap_3705_, v___y_3666_, lean_box(0));
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3713_; 
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3713_ == 0)
{
lean_object* v_unused_3714_; 
v_unused_3714_ = lean_ctor_get(v___x_3706_, 0);
lean_dec(v_unused_3714_);
v___x_3708_ = v___x_3706_;
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
else
{
lean_dec(v___x_3706_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3711_; 
if (v_isShared_3709_ == 0)
{
lean_ctor_set_tag(v___x_3708_, 1);
lean_ctor_set(v___x_3708_, 0, v___x_3702_);
v___x_3711_ = v___x_3708_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v___x_3702_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
}
else
{
lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3722_; 
v_a_3715_ = lean_ctor_get(v___x_3706_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3717_ = v___x_3706_;
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v___x_3706_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3718_ == 0)
{
v___x_3720_ = v___x_3717_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_a_3715_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__2___boxed(lean_object* v___x_3723_, lean_object* v___f_3724_, lean_object* v___f_3725_, lean_object* v_00_u03b1_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l_Lake_LoggerIO_instMonadLiftLogIO___lam__2(v___x_3723_, v___f_3724_, v___f_3725_, v_00_u03b1_3726_, v___y_3727_, v___y_3728_);
lean_dec_ref(v___y_3728_);
return v_res_3730_;
}
}
static lean_object* _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__1(void){
_start:
{
lean_object* v___x_3732_; 
v___x_3732_ = l_instMonadEIO___redArg();
return v___x_3732_;
}
}
static lean_object* _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__2(void){
_start:
{
lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3733_ = lean_obj_once(&l_Lake_LoggerIO_instMonadLiftLogIO___closed__1, &l_Lake_LoggerIO_instMonadLiftLogIO___closed__1_once, _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__1);
v___x_3734_ = l_ReaderT_instMonad___redArg(v___x_3733_);
return v___x_3734_;
}
}
static lean_object* _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__3(void){
_start:
{
lean_object* v___f_3735_; lean_object* v___x_3736_; lean_object* v___f_3737_; 
v___f_3735_ = ((lean_object*)(l_Lake_LoggerIO_instMonadLiftLogIO___closed__0));
v___x_3736_ = lean_obj_once(&l_Lake_LoggerIO_instMonadLiftLogIO___closed__2, &l_Lake_LoggerIO_instMonadLiftLogIO___closed__2_once, _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__2);
v___f_3737_ = lean_alloc_closure((void*)(l_Lake_LoggerIO_instMonadLiftLogIO___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3737_, 0, v___x_3736_);
lean_closure_set(v___f_3737_, 1, v___f_3735_);
lean_closure_set(v___f_3737_, 2, v___f_3735_);
return v___f_3737_;
}
}
static lean_object* _init_l_Lake_LoggerIO_instMonadLiftLogIO(void){
_start:
{
lean_object* v___f_3738_; 
v___f_3738_ = lean_obj_once(&l_Lake_LoggerIO_instMonadLiftLogIO___closed__3, &l_Lake_LoggerIO_instMonadLiftLogIO___closed__3_once, _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__3);
return v___f_3738_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg___lam__0(lean_object* v_val_3739_, uint8_t v_outLv_3740_, uint8_t v_val_3741_, lean_object* v_e_3742_){
_start:
{
lean_object* v___x_3744_; 
v___x_3744_ = l_Lake_logToStream(v_e_3742_, v_val_3739_, v_outLv_3740_, v_val_3741_);
return v___x_3744_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg___lam__0___boxed(lean_object* v_val_3745_, lean_object* v_outLv_3746_, lean_object* v_val_3747_, lean_object* v_e_3748_, lean_object* v___y_3749_){
_start:
{
uint8_t v_outLv_boxed_3750_; uint8_t v_val_178__boxed_3751_; lean_object* v_res_3752_; 
v_outLv_boxed_3750_ = lean_unbox(v_outLv_3746_);
v_val_178__boxed_3751_ = lean_unbox(v_val_3747_);
v_res_3752_ = l_Lake_LoggerIO_toBaseIO___redArg___lam__0(v_val_3745_, v_outLv_boxed_3750_, v_val_178__boxed_3751_, v_e_3748_);
lean_dec_ref(v_e_3748_);
return v_res_3752_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg(lean_object* v_self_3753_, lean_object* v_cfg_3754_){
_start:
{
uint8_t v_outLv_3756_; uint8_t v_ansiMode_3757_; lean_object* v_out_3758_; lean_object* v___x_3759_; uint8_t v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___f_3763_; lean_object* v___x_3764_; 
v_outLv_3756_ = lean_ctor_get_uint8(v_cfg_3754_, sizeof(void*)*1 + 1);
v_ansiMode_3757_ = lean_ctor_get_uint8(v_cfg_3754_, sizeof(void*)*1 + 2);
v_out_3758_ = lean_ctor_get(v_cfg_3754_, 0);
v___x_3759_ = l_Lake_OutStream_get(v_out_3758_);
lean_inc_ref(v___x_3759_);
v___x_3760_ = l_Lake_AnsiMode_isEnabled(v___x_3759_, v_ansiMode_3757_);
v___x_3761_ = lean_box(v_outLv_3756_);
v___x_3762_ = lean_box(v___x_3760_);
v___f_3763_ = lean_alloc_closure((void*)(l_Lake_LoggerIO_toBaseIO___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3763_, 0, v___x_3759_);
lean_closure_set(v___f_3763_, 1, v___x_3761_);
lean_closure_set(v___f_3763_, 2, v___x_3762_);
v___x_3764_ = lean_apply_2(v_self_3753_, v___f_3763_, lean_box(0));
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3772_; 
v_a_3765_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3767_ = v___x_3764_;
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3764_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3770_; 
if (v_isShared_3768_ == 0)
{
lean_ctor_set_tag(v___x_3767_, 1);
v___x_3770_ = v___x_3767_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_a_3765_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
else
{
lean_object* v___x_3773_; 
lean_dec_ref_known(v___x_3764_, 1);
v___x_3773_ = lean_box(0);
return v___x_3773_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg___boxed(lean_object* v_self_3774_, lean_object* v_cfg_3775_, lean_object* v_a_3776_){
_start:
{
lean_object* v_res_3777_; 
v_res_3777_ = l_Lake_LoggerIO_toBaseIO___redArg(v_self_3774_, v_cfg_3775_);
lean_dec_ref(v_cfg_3775_);
return v_res_3777_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO(lean_object* v_00_u03b1_3778_, lean_object* v_self_3779_, lean_object* v_cfg_3780_){
_start:
{
uint8_t v_outLv_3782_; uint8_t v_ansiMode_3783_; lean_object* v_out_3784_; lean_object* v___x_3785_; uint8_t v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___f_3789_; lean_object* v___x_3790_; 
v_outLv_3782_ = lean_ctor_get_uint8(v_cfg_3780_, sizeof(void*)*1 + 1);
v_ansiMode_3783_ = lean_ctor_get_uint8(v_cfg_3780_, sizeof(void*)*1 + 2);
v_out_3784_ = lean_ctor_get(v_cfg_3780_, 0);
v___x_3785_ = l_Lake_OutStream_get(v_out_3784_);
lean_inc_ref(v___x_3785_);
v___x_3786_ = l_Lake_AnsiMode_isEnabled(v___x_3785_, v_ansiMode_3783_);
v___x_3787_ = lean_box(v_outLv_3782_);
v___x_3788_ = lean_box(v___x_3786_);
v___f_3789_ = lean_alloc_closure((void*)(l_Lake_LoggerIO_toBaseIO___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3789_, 0, v___x_3785_);
lean_closure_set(v___f_3789_, 1, v___x_3787_);
lean_closure_set(v___f_3789_, 2, v___x_3788_);
v___x_3790_ = lean_apply_2(v_self_3779_, v___f_3789_, lean_box(0));
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3798_; 
v_a_3791_ = lean_ctor_get(v___x_3790_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3793_ = v___x_3790_;
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v___x_3790_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3796_; 
if (v_isShared_3794_ == 0)
{
lean_ctor_set_tag(v___x_3793_, 1);
v___x_3796_ = v___x_3793_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_a_3791_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
else
{
lean_object* v___x_3799_; 
lean_dec_ref_known(v___x_3790_, 1);
v___x_3799_ = lean_box(0);
return v___x_3799_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___boxed(lean_object* v_00_u03b1_3800_, lean_object* v_self_3801_, lean_object* v_cfg_3802_, lean_object* v_a_3803_){
_start:
{
lean_object* v_res_3804_; 
v_res_3804_ = l_Lake_LoggerIO_toBaseIO(v_00_u03b1_3800_, v_self_3801_, v_cfg_3802_);
lean_dec_ref(v_cfg_3802_);
return v_res_3804_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg___lam__0(lean_object* v_val_3805_, lean_object* v_e_3806_){
_start:
{
lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; 
v___x_3808_ = lean_st_ref_take(v_val_3805_);
v___x_3809_ = lean_array_push(v___x_3808_, v_e_3806_);
v___x_3810_ = lean_st_ref_put(v_val_3805_, v___x_3809_);
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg___lam__0___boxed(lean_object* v_val_3811_, lean_object* v_e_3812_, lean_object* v___y_3813_){
_start:
{
lean_object* v_res_3814_; 
v_res_3814_ = l_Lake_LoggerIO_captureLog___redArg___lam__0(v_val_3811_, v_e_3812_);
lean_dec(v_val_3811_);
return v_res_3814_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg(lean_object* v_self_3815_){
_start:
{
lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v_val_3824_; lean_object* v___f_3835_; lean_object* v___x_3836_; 
v___x_3821_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3822_ = lean_st_mk_ref(v___x_3821_);
lean_inc(v___x_3822_);
v___f_3835_ = lean_alloc_closure((void*)(l_Lake_LoggerIO_captureLog___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3835_, 0, v___x_3822_);
v___x_3836_ = lean_apply_2(v_self_3815_, v___f_3835_, lean_box(0));
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3844_; 
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3839_ = v___x_3836_;
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3836_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3840_ == 0)
{
lean_ctor_set_tag(v___x_3839_, 1);
v___x_3842_ = v___x_3839_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
v_val_3824_ = v___x_3842_;
goto v___jp_3823_;
}
}
}
else
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3852_; 
v_a_3845_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3847_ = v___x_3836_;
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3836_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3850_; 
if (v_isShared_3848_ == 0)
{
lean_ctor_set_tag(v___x_3847_, 0);
v___x_3850_ = v___x_3847_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
v_val_3824_ = v___x_3850_;
goto v___jp_3823_;
}
}
}
v___jp_3817_:
{
lean_object* v___x_3820_; 
v___x_3820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3820_, 0, v___y_3819_);
lean_ctor_set(v___x_3820_, 1, v___y_3818_);
return v___x_3820_;
}
v___jp_3823_:
{
lean_object* v___x_3825_; 
v___x_3825_ = lean_st_ref_get(v___x_3822_);
lean_dec(v___x_3822_);
if (lean_obj_tag(v_val_3824_) == 0)
{
lean_object* v___x_3826_; 
lean_dec_ref_known(v_val_3824_, 1);
v___x_3826_ = lean_box(0);
v___y_3818_ = v___x_3825_;
v___y_3819_ = v___x_3826_;
goto v___jp_3817_;
}
else
{
lean_object* v_a_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3834_; 
v_a_3827_ = lean_ctor_get(v_val_3824_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v_val_3824_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3829_ = v_val_3824_;
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_a_3827_);
lean_dec(v_val_3824_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3832_; 
if (v_isShared_3830_ == 0)
{
v___x_3832_ = v___x_3829_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_a_3827_);
v___x_3832_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
v___y_3818_ = v___x_3825_;
v___y_3819_ = v___x_3832_;
goto v___jp_3817_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg___boxed(lean_object* v_self_3853_, lean_object* v_a_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l_Lake_LoggerIO_captureLog___redArg(v_self_3853_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog(lean_object* v_00_u03b1_3856_, lean_object* v_self_3857_){
_start:
{
lean_object* v___x_3859_; 
v___x_3859_ = l_Lake_LoggerIO_captureLog___redArg(v_self_3857_);
return v___x_3859_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___boxed(lean_object* v_00_u03b1_3860_, lean_object* v_self_3861_, lean_object* v_a_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l_Lake_LoggerIO_captureLog(v_00_u03b1_3860_, v_self_3861_);
return v_res_3863_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f___redArg(lean_object* v_self_3864_){
_start:
{
lean_object* v___x_3866_; 
v___x_3866_ = l_Lake_LoggerIO_captureLog___redArg(v_self_3864_);
return v___x_3866_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f___redArg___boxed(lean_object* v_self_3867_, lean_object* v_a_3868_){
_start:
{
lean_object* v_res_3869_; 
v_res_3869_ = l_Lake_LoggerIO_run_x3f___redArg(v_self_3867_);
return v_res_3869_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f(lean_object* v_00_u03b1_3870_, lean_object* v_self_3871_){
_start:
{
lean_object* v___x_3873_; 
v___x_3873_ = l_Lake_LoggerIO_captureLog___redArg(v_self_3871_);
return v___x_3873_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f___boxed(lean_object* v_00_u03b1_3874_, lean_object* v_self_3875_, lean_object* v_a_3876_){
_start:
{
lean_object* v_res_3877_; 
v_res_3877_ = l_Lake_LoggerIO_run_x3f(v_00_u03b1_3874_, v_self_3875_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27___redArg(lean_object* v_self_3878_, lean_object* v_logger_3879_){
_start:
{
lean_object* v___x_3881_; 
v___x_3881_ = lean_apply_2(v_self_3878_, v_logger_3879_, lean_box(0));
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3889_; 
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3889_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3884_ = v___x_3881_;
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3881_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3887_; 
if (v_isShared_3885_ == 0)
{
lean_ctor_set_tag(v___x_3884_, 1);
v___x_3887_ = v___x_3884_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_a_3882_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
}
else
{
lean_object* v___x_3890_; 
lean_dec_ref_known(v___x_3881_, 1);
v___x_3890_ = lean_box(0);
return v___x_3890_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27___redArg___boxed(lean_object* v_self_3891_, lean_object* v_logger_3892_, lean_object* v_a_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l_Lake_LoggerIO_run_x3f_x27___redArg(v_self_3891_, v_logger_3892_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27(lean_object* v_00_u03b1_3895_, lean_object* v_self_3896_, lean_object* v_logger_3897_){
_start:
{
lean_object* v___x_3899_; 
v___x_3899_ = lean_apply_2(v_self_3896_, v_logger_3897_, lean_box(0));
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3907_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3902_ = v___x_3899_;
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3899_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3905_; 
if (v_isShared_3903_ == 0)
{
lean_ctor_set_tag(v___x_3902_, 1);
v___x_3905_ = v___x_3902_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_a_3900_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
}
else
{
lean_object* v___x_3908_; 
lean_dec_ref_known(v___x_3899_, 1);
v___x_3908_ = lean_box(0);
return v___x_3908_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27___boxed(lean_object* v_00_u03b1_3909_, lean_object* v_self_3910_, lean_object* v_logger_3911_, lean_object* v_a_3912_){
_start:
{
lean_object* v_res_3913_; 
v_res_3913_ = l_Lake_LoggerIO_run_x3f_x27(v_00_u03b1_3909_, v_self_3910_, v_logger_3911_);
return v_res_3913_;
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
