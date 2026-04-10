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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_toJson___redArg(lean_object*, lean_object*);
lean_object* l_Array_fromJson_x3f___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Verbosity_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_Verbosity_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_AnsiMode_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_toCtorIdx___boxed(lean_object*);
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
static const lean_string_object l_Lake_Ansi_chalk___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\x1b[1;"};
static const lean_object* l_Lake_Ansi_chalk___closed__0 = (const lean_object*)&l_Lake_Ansi_chalk___closed__0_value;
static const lean_string_object l_Lake_Ansi_chalk___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "m"};
static const lean_object* l_Lake_Ansi_chalk___closed__1 = (const lean_object*)&l_Lake_Ansi_chalk___closed__1_value;
static const lean_string_object l_Lake_Ansi_chalk___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "\x1b[m"};
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
LEAN_EXPORT lean_object* l_Lake_LogLevel_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_LogLevel_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Verbosity_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lake_Verbosity_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Lake_Verbosity_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lake_Verbosity_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Lake_Verbosity_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_quiet_elim___redArg(lean_object* v_quiet_28_){
_start:
{
lean_inc(v_quiet_28_);
return v_quiet_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_quiet_elim___redArg___boxed(lean_object* v_quiet_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lake_Verbosity_quiet_elim___redArg(v_quiet_29_);
lean_dec(v_quiet_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_quiet_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_quiet_34_){
_start:
{
lean_inc(v_quiet_34_);
return v_quiet_34_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_quiet_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_quiet_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lake_Verbosity_quiet_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_quiet_38_);
lean_dec(v_quiet_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_normal_elim___redArg(lean_object* v_normal_41_){
_start:
{
lean_inc(v_normal_41_);
return v_normal_41_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_normal_elim___redArg___boxed(lean_object* v_normal_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lake_Verbosity_normal_elim___redArg(v_normal_42_);
lean_dec(v_normal_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_normal_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_normal_47_){
_start:
{
lean_inc(v_normal_47_);
return v_normal_47_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_normal_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_normal_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Lake_Verbosity_normal_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_normal_51_);
lean_dec(v_normal_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_verbose_elim___redArg(lean_object* v_verbose_54_){
_start:
{
lean_inc(v_verbose_54_);
return v_verbose_54_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_verbose_elim___redArg___boxed(lean_object* v_verbose_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lake_Verbosity_verbose_elim___redArg(v_verbose_55_);
lean_dec(v_verbose_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_verbose_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_verbose_60_){
_start:
{
lean_inc(v_verbose_60_);
return v_verbose_60_;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_verbose_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_verbose_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lake_Verbosity_verbose_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_verbose_64_);
lean_dec(v_verbose_64_);
return v_res_66_;
}
}
static lean_object* _init_l_Lake_instReprVerbosity_repr___closed__6(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_unsigned_to_nat(2u);
v___x_77_ = lean_nat_to_int(v___x_76_);
return v___x_77_;
}
}
static lean_object* _init_l_Lake_instReprVerbosity_repr___closed__7(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(1u);
v___x_79_ = lean_nat_to_int(v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerbosity_repr(uint8_t v_x_80_, lean_object* v_prec_81_){
_start:
{
lean_object* v___y_83_; lean_object* v___y_90_; lean_object* v___y_97_; 
switch(v_x_80_)
{
case 0:
{
lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_103_ = lean_unsigned_to_nat(1024u);
v___x_104_ = lean_nat_dec_le(v___x_103_, v_prec_81_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_83_ = v___x_105_;
goto v___jp_82_;
}
else
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_83_ = v___x_106_;
goto v___jp_82_;
}
}
case 1:
{
lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_107_ = lean_unsigned_to_nat(1024u);
v___x_108_ = lean_nat_dec_le(v___x_107_, v_prec_81_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_90_ = v___x_109_;
goto v___jp_89_;
}
else
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_90_ = v___x_110_;
goto v___jp_89_;
}
}
default: 
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = lean_unsigned_to_nat(1024u);
v___x_112_ = lean_nat_dec_le(v___x_111_, v_prec_81_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_97_ = v___x_113_;
goto v___jp_96_;
}
else
{
lean_object* v___x_114_; 
v___x_114_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_97_ = v___x_114_;
goto v___jp_96_;
}
}
}
v___jp_82_:
{
lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_84_ = ((lean_object*)(l_Lake_instReprVerbosity_repr___closed__1));
lean_inc(v___y_83_);
v___x_85_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_85_, 0, v___y_83_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = 0;
v___x_87_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_87_, 0, v___x_85_);
lean_ctor_set_uint8(v___x_87_, sizeof(void*)*1, v___x_86_);
v___x_88_ = l_Repr_addAppParen(v___x_87_, v_prec_81_);
return v___x_88_;
}
v___jp_89_:
{
lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_91_ = ((lean_object*)(l_Lake_instReprVerbosity_repr___closed__3));
lean_inc(v___y_90_);
v___x_92_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_92_, 0, v___y_90_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
v___x_93_ = 0;
v___x_94_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_94_, 0, v___x_92_);
lean_ctor_set_uint8(v___x_94_, sizeof(void*)*1, v___x_93_);
v___x_95_ = l_Repr_addAppParen(v___x_94_, v_prec_81_);
return v___x_95_;
}
v___jp_96_:
{
lean_object* v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_98_ = ((lean_object*)(l_Lake_instReprVerbosity_repr___closed__5));
lean_inc(v___y_97_);
v___x_99_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_99_, 0, v___y_97_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
v___x_100_ = 0;
v___x_101_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_101_, 0, v___x_99_);
lean_ctor_set_uint8(v___x_101_, sizeof(void*)*1, v___x_100_);
v___x_102_ = l_Repr_addAppParen(v___x_101_, v_prec_81_);
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerbosity_repr___boxed(lean_object* v_x_115_, lean_object* v_prec_116_){
_start:
{
uint8_t v_x_177__boxed_117_; lean_object* v_res_118_; 
v_x_177__boxed_117_ = lean_unbox(v_x_115_);
v_res_118_ = l_Lake_instReprVerbosity_repr(v_x_177__boxed_117_, v_prec_116_);
lean_dec(v_prec_116_);
return v_res_118_;
}
}
LEAN_EXPORT uint8_t l_Lake_Verbosity_ofNat(lean_object* v_n_121_){
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
LEAN_EXPORT lean_object* l_Lake_Verbosity_ofNat___boxed(lean_object* v_n_129_){
_start:
{
uint8_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = l_Lake_Verbosity_ofNat(v_n_129_);
lean_dec(v_n_129_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqVerbosity(uint8_t v_x_132_, uint8_t v_y_133_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_134_ = l_Lake_Verbosity_ctorIdx(v_x_132_);
v___x_135_ = l_Lake_Verbosity_ctorIdx(v_y_133_);
v___x_136_ = lean_nat_dec_eq(v___x_134_, v___x_135_);
lean_dec(v___x_135_);
lean_dec(v___x_134_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqVerbosity___boxed(lean_object* v_x_137_, lean_object* v_y_138_){
_start:
{
uint8_t v_x_13__boxed_139_; uint8_t v_y_14__boxed_140_; uint8_t v_res_141_; lean_object* v_r_142_; 
v_x_13__boxed_139_ = lean_unbox(v_x_137_);
v_y_14__boxed_140_ = lean_unbox(v_y_138_);
v_res_141_ = l_Lake_instDecidableEqVerbosity(v_x_13__boxed_139_, v_y_14__boxed_140_);
v_r_142_ = lean_box(v_res_141_);
return v_r_142_;
}
}
LEAN_EXPORT uint8_t l_Lake_instOrdVerbosity_ord(uint8_t v_x_143_, uint8_t v_y_144_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_145_ = l_Lake_Verbosity_ctorIdx(v_x_143_);
v___x_146_ = l_Lake_Verbosity_ctorIdx(v_y_144_);
v___x_147_ = lean_nat_dec_lt(v___x_145_, v___x_146_);
if (v___x_147_ == 0)
{
uint8_t v___x_148_; 
v___x_148_ = lean_nat_dec_eq(v___x_145_, v___x_146_);
lean_dec(v___x_146_);
lean_dec(v___x_145_);
if (v___x_148_ == 0)
{
uint8_t v___x_149_; 
v___x_149_ = 2;
return v___x_149_;
}
else
{
uint8_t v___x_150_; 
v___x_150_ = 1;
return v___x_150_;
}
}
else
{
uint8_t v___x_151_; 
lean_dec(v___x_146_);
lean_dec(v___x_145_);
v___x_151_ = 0;
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instOrdVerbosity_ord___boxed(lean_object* v_x_152_, lean_object* v_y_153_){
_start:
{
uint8_t v_x_30__boxed_154_; uint8_t v_y_31__boxed_155_; uint8_t v_res_156_; lean_object* v_r_157_; 
v_x_30__boxed_154_ = lean_unbox(v_x_152_);
v_y_31__boxed_155_ = lean_unbox(v_y_153_);
v_res_156_ = l_Lake_instOrdVerbosity_ord(v_x_30__boxed_154_, v_y_31__boxed_155_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
static lean_object* _init_l_Lake_instLTVerbosity(void){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lean_box(0);
return v___x_160_;
}
}
static lean_object* _init_l_Lake_instLEVerbosity(void){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = lean_box(0);
return v___x_161_;
}
}
LEAN_EXPORT uint8_t l_Lake_instMinVerbosity___lam__0(uint8_t v_x_162_, uint8_t v_y_163_){
_start:
{
uint8_t v___x_164_; 
v___x_164_ = l_Lake_instOrdVerbosity_ord(v_x_162_, v_y_163_);
if (v___x_164_ == 2)
{
return v_y_163_;
}
else
{
return v_x_162_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMinVerbosity___lam__0___boxed(lean_object* v_x_165_, lean_object* v_y_166_){
_start:
{
uint8_t v_x_boxed_167_; uint8_t v_y_boxed_168_; uint8_t v_res_169_; lean_object* v_r_170_; 
v_x_boxed_167_ = lean_unbox(v_x_165_);
v_y_boxed_168_ = lean_unbox(v_y_166_);
v_res_169_ = l_Lake_instMinVerbosity___lam__0(v_x_boxed_167_, v_y_boxed_168_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT uint8_t l_Lake_instMaxVerbosity___lam__0(uint8_t v_x_173_, uint8_t v_y_174_){
_start:
{
uint8_t v___x_175_; 
v___x_175_ = l_Lake_instOrdVerbosity_ord(v_x_173_, v_y_174_);
if (v___x_175_ == 2)
{
return v_x_173_;
}
else
{
return v_y_174_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxVerbosity___lam__0___boxed(lean_object* v_x_176_, lean_object* v_y_177_){
_start:
{
uint8_t v_x_boxed_178_; uint8_t v_y_boxed_179_; uint8_t v_res_180_; lean_object* v_r_181_; 
v_x_boxed_178_ = lean_unbox(v_x_176_);
v_y_boxed_179_ = lean_unbox(v_y_177_);
v_res_180_ = l_Lake_instMaxVerbosity___lam__0(v_x_boxed_178_, v_y_boxed_179_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
static uint8_t _init_l_Lake_instInhabitedVerbosity(void){
_start:
{
uint8_t v___x_184_; 
v___x_184_ = 1;
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorIdx(uint8_t v_x_185_){
_start:
{
switch(v_x_185_)
{
case 0:
{
lean_object* v___x_186_; 
v___x_186_ = lean_unsigned_to_nat(0u);
return v___x_186_;
}
case 1:
{
lean_object* v___x_187_; 
v___x_187_ = lean_unsigned_to_nat(1u);
return v___x_187_;
}
default: 
{
lean_object* v___x_188_; 
v___x_188_ = lean_unsigned_to_nat(2u);
return v___x_188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorIdx___boxed(lean_object* v_x_189_){
_start:
{
uint8_t v_x_boxed_190_; lean_object* v_res_191_; 
v_x_boxed_190_ = lean_unbox(v_x_189_);
v_res_191_ = l_Lake_AnsiMode_ctorIdx(v_x_boxed_190_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_toCtorIdx(uint8_t v_x_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lake_AnsiMode_ctorIdx(v_x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_toCtorIdx___boxed(lean_object* v_x_194_){
_start:
{
uint8_t v_x_4__boxed_195_; lean_object* v_res_196_; 
v_x_4__boxed_195_ = lean_unbox(v_x_194_);
v_res_196_ = l_Lake_AnsiMode_toCtorIdx(v_x_4__boxed_195_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorElim___redArg(lean_object* v_k_197_){
_start:
{
lean_inc(v_k_197_);
return v_k_197_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorElim___redArg___boxed(lean_object* v_k_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lake_AnsiMode_ctorElim___redArg(v_k_198_);
lean_dec(v_k_198_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorElim(lean_object* v_motive_200_, lean_object* v_ctorIdx_201_, uint8_t v_t_202_, lean_object* v_h_203_, lean_object* v_k_204_){
_start:
{
lean_inc(v_k_204_);
return v_k_204_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorElim___boxed(lean_object* v_motive_205_, lean_object* v_ctorIdx_206_, lean_object* v_t_207_, lean_object* v_h_208_, lean_object* v_k_209_){
_start:
{
uint8_t v_t_boxed_210_; lean_object* v_res_211_; 
v_t_boxed_210_ = lean_unbox(v_t_207_);
v_res_211_ = l_Lake_AnsiMode_ctorElim(v_motive_205_, v_ctorIdx_206_, v_t_boxed_210_, v_h_208_, v_k_209_);
lean_dec(v_k_209_);
lean_dec(v_ctorIdx_206_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_auto_elim___redArg(lean_object* v_auto_212_){
_start:
{
lean_inc(v_auto_212_);
return v_auto_212_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_auto_elim___redArg___boxed(lean_object* v_auto_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lake_AnsiMode_auto_elim___redArg(v_auto_213_);
lean_dec(v_auto_213_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_auto_elim(lean_object* v_motive_215_, uint8_t v_t_216_, lean_object* v_h_217_, lean_object* v_auto_218_){
_start:
{
lean_inc(v_auto_218_);
return v_auto_218_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_auto_elim___boxed(lean_object* v_motive_219_, lean_object* v_t_220_, lean_object* v_h_221_, lean_object* v_auto_222_){
_start:
{
uint8_t v_t_boxed_223_; lean_object* v_res_224_; 
v_t_boxed_223_ = lean_unbox(v_t_220_);
v_res_224_ = l_Lake_AnsiMode_auto_elim(v_motive_219_, v_t_boxed_223_, v_h_221_, v_auto_222_);
lean_dec(v_auto_222_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ansi_elim___redArg(lean_object* v_ansi_225_){
_start:
{
lean_inc(v_ansi_225_);
return v_ansi_225_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ansi_elim___redArg___boxed(lean_object* v_ansi_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lake_AnsiMode_ansi_elim___redArg(v_ansi_226_);
lean_dec(v_ansi_226_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ansi_elim(lean_object* v_motive_228_, uint8_t v_t_229_, lean_object* v_h_230_, lean_object* v_ansi_231_){
_start:
{
lean_inc(v_ansi_231_);
return v_ansi_231_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ansi_elim___boxed(lean_object* v_motive_232_, lean_object* v_t_233_, lean_object* v_h_234_, lean_object* v_ansi_235_){
_start:
{
uint8_t v_t_boxed_236_; lean_object* v_res_237_; 
v_t_boxed_236_ = lean_unbox(v_t_233_);
v_res_237_ = l_Lake_AnsiMode_ansi_elim(v_motive_232_, v_t_boxed_236_, v_h_234_, v_ansi_235_);
lean_dec(v_ansi_235_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noAnsi_elim___redArg(lean_object* v_noAnsi_238_){
_start:
{
lean_inc(v_noAnsi_238_);
return v_noAnsi_238_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noAnsi_elim___redArg___boxed(lean_object* v_noAnsi_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lake_AnsiMode_noAnsi_elim___redArg(v_noAnsi_239_);
lean_dec(v_noAnsi_239_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noAnsi_elim(lean_object* v_motive_241_, uint8_t v_t_242_, lean_object* v_h_243_, lean_object* v_noAnsi_244_){
_start:
{
lean_inc(v_noAnsi_244_);
return v_noAnsi_244_;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noAnsi_elim___boxed(lean_object* v_motive_245_, lean_object* v_t_246_, lean_object* v_h_247_, lean_object* v_noAnsi_248_){
_start:
{
uint8_t v_t_boxed_249_; lean_object* v_res_250_; 
v_t_boxed_249_ = lean_unbox(v_t_246_);
v_res_250_ = l_Lake_AnsiMode_noAnsi_elim(v_motive_245_, v_t_boxed_249_, v_h_247_, v_noAnsi_248_);
lean_dec(v_noAnsi_248_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprAnsiMode_repr(uint8_t v_x_260_, lean_object* v_prec_261_){
_start:
{
lean_object* v___y_263_; lean_object* v___y_270_; lean_object* v___y_277_; 
switch(v_x_260_)
{
case 0:
{
lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_283_ = lean_unsigned_to_nat(1024u);
v___x_284_ = lean_nat_dec_le(v___x_283_, v_prec_261_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; 
v___x_285_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_263_ = v___x_285_;
goto v___jp_262_;
}
else
{
lean_object* v___x_286_; 
v___x_286_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_263_ = v___x_286_;
goto v___jp_262_;
}
}
case 1:
{
lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_287_ = lean_unsigned_to_nat(1024u);
v___x_288_ = lean_nat_dec_le(v___x_287_, v_prec_261_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; 
v___x_289_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_270_ = v___x_289_;
goto v___jp_269_;
}
else
{
lean_object* v___x_290_; 
v___x_290_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_270_ = v___x_290_;
goto v___jp_269_;
}
}
default: 
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = lean_unsigned_to_nat(1024u);
v___x_292_ = lean_nat_dec_le(v___x_291_, v_prec_261_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; 
v___x_293_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_277_ = v___x_293_;
goto v___jp_276_;
}
else
{
lean_object* v___x_294_; 
v___x_294_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_277_ = v___x_294_;
goto v___jp_276_;
}
}
}
v___jp_262_:
{
lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_264_ = ((lean_object*)(l_Lake_instReprAnsiMode_repr___closed__1));
lean_inc(v___y_263_);
v___x_265_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_265_, 0, v___y_263_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = 0;
v___x_267_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_267_, 0, v___x_265_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*1, v___x_266_);
v___x_268_ = l_Repr_addAppParen(v___x_267_, v_prec_261_);
return v___x_268_;
}
v___jp_269_:
{
lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_271_ = ((lean_object*)(l_Lake_instReprAnsiMode_repr___closed__3));
lean_inc(v___y_270_);
v___x_272_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_272_, 0, v___y_270_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = 0;
v___x_274_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_274_, 0, v___x_272_);
lean_ctor_set_uint8(v___x_274_, sizeof(void*)*1, v___x_273_);
v___x_275_ = l_Repr_addAppParen(v___x_274_, v_prec_261_);
return v___x_275_;
}
v___jp_276_:
{
lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_278_ = ((lean_object*)(l_Lake_instReprAnsiMode_repr___closed__5));
lean_inc(v___y_277_);
v___x_279_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_279_, 0, v___y_277_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v___x_280_ = 0;
v___x_281_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_281_, 0, v___x_279_);
lean_ctor_set_uint8(v___x_281_, sizeof(void*)*1, v___x_280_);
v___x_282_ = l_Repr_addAppParen(v___x_281_, v_prec_261_);
return v___x_282_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprAnsiMode_repr___boxed(lean_object* v_x_295_, lean_object* v_prec_296_){
_start:
{
uint8_t v_x_173__boxed_297_; lean_object* v_res_298_; 
v_x_173__boxed_297_ = lean_unbox(v_x_295_);
v_res_298_ = l_Lake_instReprAnsiMode_repr(v_x_173__boxed_297_, v_prec_296_);
lean_dec(v_prec_296_);
return v_res_298_;
}
}
LEAN_EXPORT uint8_t l_Lake_AnsiMode_isEnabled(lean_object* v_out_301_, uint8_t v_x_302_){
_start:
{
switch(v_x_302_)
{
case 0:
{
lean_object* v_isTty_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v_isTty_304_ = lean_ctor_get(v_out_301_, 5);
lean_inc_ref(v_isTty_304_);
lean_dec_ref(v_out_301_);
v___x_305_ = lean_apply_1(v_isTty_304_, lean_box(0));
v___x_306_ = lean_unbox(v___x_305_);
return v___x_306_;
}
case 1:
{
uint8_t v___x_307_; 
lean_dec_ref(v_out_301_);
v___x_307_ = 1;
return v___x_307_;
}
default: 
{
uint8_t v___x_308_; 
lean_dec_ref(v_out_301_);
v___x_308_ = 0;
return v___x_308_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_isEnabled___boxed(lean_object* v_out_309_, lean_object* v_x_310_, lean_object* v_a_311_){
_start:
{
uint8_t v_x_146__boxed_312_; uint8_t v_res_313_; lean_object* v_r_314_; 
v_x_146__boxed_312_ = lean_unbox(v_x_310_);
v_res_313_ = l_Lake_AnsiMode_isEnabled(v_out_309_, v_x_146__boxed_312_);
v_r_314_ = lean_box(v_res_313_);
return v_r_314_;
}
}
LEAN_EXPORT lean_object* l_Lake_Ansi_chalk(lean_object* v_colorCode_318_, lean_object* v_text_319_){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_320_ = ((lean_object*)(l_Lake_Ansi_chalk___closed__0));
v___x_321_ = lean_string_append(v___x_320_, v_colorCode_318_);
v___x_322_ = ((lean_object*)(l_Lake_Ansi_chalk___closed__1));
v___x_323_ = lean_string_append(v___x_321_, v___x_322_);
v___x_324_ = lean_string_append(v___x_323_, v_text_319_);
v___x_325_ = ((lean_object*)(l_Lake_Ansi_chalk___closed__2));
v___x_326_ = lean_string_append(v___x_324_, v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lake_Ansi_chalk___boxed(lean_object* v_colorCode_327_, lean_object* v_text_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lake_Ansi_chalk(v_colorCode_327_, v_text_328_);
lean_dec_ref(v_text_328_);
lean_dec_ref(v_colorCode_327_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorIdx(lean_object* v_x_330_){
_start:
{
switch(lean_obj_tag(v_x_330_))
{
case 0:
{
lean_object* v___x_331_; 
v___x_331_ = lean_unsigned_to_nat(0u);
return v___x_331_;
}
case 1:
{
lean_object* v___x_332_; 
v___x_332_ = lean_unsigned_to_nat(1u);
return v___x_332_;
}
default: 
{
lean_object* v___x_333_; 
v___x_333_ = lean_unsigned_to_nat(2u);
return v___x_333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorIdx___boxed(lean_object* v_x_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lake_OutStream_ctorIdx(v_x_334_);
lean_dec(v_x_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorElim___redArg(lean_object* v_t_336_, lean_object* v_k_337_){
_start:
{
if (lean_obj_tag(v_t_336_) == 2)
{
lean_object* v_s_338_; lean_object* v___x_339_; 
v_s_338_ = lean_ctor_get(v_t_336_, 0);
lean_inc_ref(v_s_338_);
lean_dec_ref(v_t_336_);
v___x_339_ = lean_apply_1(v_k_337_, v_s_338_);
return v___x_339_;
}
else
{
lean_dec(v_t_336_);
return v_k_337_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorElim(lean_object* v_motive_340_, lean_object* v_ctorIdx_341_, lean_object* v_t_342_, lean_object* v_h_343_, lean_object* v_k_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Lake_OutStream_ctorElim___redArg(v_t_342_, v_k_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorElim___boxed(lean_object* v_motive_346_, lean_object* v_ctorIdx_347_, lean_object* v_t_348_, lean_object* v_h_349_, lean_object* v_k_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lake_OutStream_ctorElim(v_motive_346_, v_ctorIdx_347_, v_t_348_, v_h_349_, v_k_350_);
lean_dec(v_ctorIdx_347_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_stdout_elim___redArg(lean_object* v_t_352_, lean_object* v_stdout_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lake_OutStream_ctorElim___redArg(v_t_352_, v_stdout_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_stdout_elim(lean_object* v_motive_355_, lean_object* v_t_356_, lean_object* v_h_357_, lean_object* v_stdout_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lake_OutStream_ctorElim___redArg(v_t_356_, v_stdout_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_stderr_elim___redArg(lean_object* v_t_360_, lean_object* v_stderr_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lake_OutStream_ctorElim___redArg(v_t_360_, v_stderr_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_stderr_elim(lean_object* v_motive_363_, lean_object* v_t_364_, lean_object* v_h_365_, lean_object* v_stderr_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lake_OutStream_ctorElim___redArg(v_t_364_, v_stderr_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_stream_elim___redArg(lean_object* v_t_368_, lean_object* v_stream_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lake_OutStream_ctorElim___redArg(v_t_368_, v_stream_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_stream_elim(lean_object* v_motive_371_, lean_object* v_t_372_, lean_object* v_h_373_, lean_object* v_stream_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lake_OutStream_ctorElim___redArg(v_t_372_, v_stream_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_get(lean_object* v_x_376_){
_start:
{
switch(lean_obj_tag(v_x_376_))
{
case 0:
{
lean_object* v___x_378_; 
v___x_378_ = lean_get_stdout();
return v___x_378_;
}
case 1:
{
lean_object* v___x_379_; 
v___x_379_ = lean_get_stderr();
return v___x_379_;
}
default: 
{
lean_object* v_s_380_; 
v_s_380_ = lean_ctor_get(v_x_376_, 0);
lean_inc_ref(v_s_380_);
return v_s_380_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_get___boxed(lean_object* v_x_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lake_OutStream_get(v_x_381_);
lean_dec(v_x_381_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeStreamOutStream___lam__0(lean_object* v_s_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_385_, 0, v_s_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeHandleOutStream___lam__0(lean_object* v_h_388_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_stream_of_handle(v_h_388_);
v___x_390_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorIdx(uint8_t v_x_393_){
_start:
{
switch(v_x_393_)
{
case 0:
{
lean_object* v___x_394_; 
v___x_394_ = lean_unsigned_to_nat(0u);
return v___x_394_;
}
case 1:
{
lean_object* v___x_395_; 
v___x_395_ = lean_unsigned_to_nat(1u);
return v___x_395_;
}
case 2:
{
lean_object* v___x_396_; 
v___x_396_ = lean_unsigned_to_nat(2u);
return v___x_396_;
}
default: 
{
lean_object* v___x_397_; 
v___x_397_ = lean_unsigned_to_nat(3u);
return v___x_397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorIdx___boxed(lean_object* v_x_398_){
_start:
{
uint8_t v_x_boxed_399_; lean_object* v_res_400_; 
v_x_boxed_399_ = lean_unbox(v_x_398_);
v_res_400_ = l_Lake_LogLevel_ctorIdx(v_x_boxed_399_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_toCtorIdx(uint8_t v_x_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lake_LogLevel_ctorIdx(v_x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_toCtorIdx___boxed(lean_object* v_x_403_){
_start:
{
uint8_t v_x_4__boxed_404_; lean_object* v_res_405_; 
v_x_4__boxed_404_ = lean_unbox(v_x_403_);
v_res_405_ = l_Lake_LogLevel_toCtorIdx(v_x_4__boxed_404_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorElim___redArg(lean_object* v_k_406_){
_start:
{
lean_inc(v_k_406_);
return v_k_406_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorElim___redArg___boxed(lean_object* v_k_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lake_LogLevel_ctorElim___redArg(v_k_407_);
lean_dec(v_k_407_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorElim(lean_object* v_motive_409_, lean_object* v_ctorIdx_410_, uint8_t v_t_411_, lean_object* v_h_412_, lean_object* v_k_413_){
_start:
{
lean_inc(v_k_413_);
return v_k_413_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorElim___boxed(lean_object* v_motive_414_, lean_object* v_ctorIdx_415_, lean_object* v_t_416_, lean_object* v_h_417_, lean_object* v_k_418_){
_start:
{
uint8_t v_t_boxed_419_; lean_object* v_res_420_; 
v_t_boxed_419_ = lean_unbox(v_t_416_);
v_res_420_ = l_Lake_LogLevel_ctorElim(v_motive_414_, v_ctorIdx_415_, v_t_boxed_419_, v_h_417_, v_k_418_);
lean_dec(v_k_418_);
lean_dec(v_ctorIdx_415_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_trace_elim___redArg(lean_object* v_trace_421_){
_start:
{
lean_inc(v_trace_421_);
return v_trace_421_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_trace_elim___redArg___boxed(lean_object* v_trace_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lake_LogLevel_trace_elim___redArg(v_trace_422_);
lean_dec(v_trace_422_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_trace_elim(lean_object* v_motive_424_, uint8_t v_t_425_, lean_object* v_h_426_, lean_object* v_trace_427_){
_start:
{
lean_inc(v_trace_427_);
return v_trace_427_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_trace_elim___boxed(lean_object* v_motive_428_, lean_object* v_t_429_, lean_object* v_h_430_, lean_object* v_trace_431_){
_start:
{
uint8_t v_t_boxed_432_; lean_object* v_res_433_; 
v_t_boxed_432_ = lean_unbox(v_t_429_);
v_res_433_ = l_Lake_LogLevel_trace_elim(v_motive_428_, v_t_boxed_432_, v_h_430_, v_trace_431_);
lean_dec(v_trace_431_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_info_elim___redArg(lean_object* v_info_434_){
_start:
{
lean_inc(v_info_434_);
return v_info_434_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_info_elim___redArg___boxed(lean_object* v_info_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lake_LogLevel_info_elim___redArg(v_info_435_);
lean_dec(v_info_435_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_info_elim(lean_object* v_motive_437_, uint8_t v_t_438_, lean_object* v_h_439_, lean_object* v_info_440_){
_start:
{
lean_inc(v_info_440_);
return v_info_440_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_info_elim___boxed(lean_object* v_motive_441_, lean_object* v_t_442_, lean_object* v_h_443_, lean_object* v_info_444_){
_start:
{
uint8_t v_t_boxed_445_; lean_object* v_res_446_; 
v_t_boxed_445_ = lean_unbox(v_t_442_);
v_res_446_ = l_Lake_LogLevel_info_elim(v_motive_441_, v_t_boxed_445_, v_h_443_, v_info_444_);
lean_dec(v_info_444_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_warning_elim___redArg(lean_object* v_warning_447_){
_start:
{
lean_inc(v_warning_447_);
return v_warning_447_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_warning_elim___redArg___boxed(lean_object* v_warning_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lake_LogLevel_warning_elim___redArg(v_warning_448_);
lean_dec(v_warning_448_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_warning_elim(lean_object* v_motive_450_, uint8_t v_t_451_, lean_object* v_h_452_, lean_object* v_warning_453_){
_start:
{
lean_inc(v_warning_453_);
return v_warning_453_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_warning_elim___boxed(lean_object* v_motive_454_, lean_object* v_t_455_, lean_object* v_h_456_, lean_object* v_warning_457_){
_start:
{
uint8_t v_t_boxed_458_; lean_object* v_res_459_; 
v_t_boxed_458_ = lean_unbox(v_t_455_);
v_res_459_ = l_Lake_LogLevel_warning_elim(v_motive_454_, v_t_boxed_458_, v_h_456_, v_warning_457_);
lean_dec(v_warning_457_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_error_elim___redArg(lean_object* v_error_460_){
_start:
{
lean_inc(v_error_460_);
return v_error_460_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_error_elim___redArg___boxed(lean_object* v_error_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lake_LogLevel_error_elim___redArg(v_error_461_);
lean_dec(v_error_461_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_error_elim(lean_object* v_motive_463_, uint8_t v_t_464_, lean_object* v_h_465_, lean_object* v_error_466_){
_start:
{
lean_inc(v_error_466_);
return v_error_466_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_error_elim___boxed(lean_object* v_motive_467_, lean_object* v_t_468_, lean_object* v_h_469_, lean_object* v_error_470_){
_start:
{
uint8_t v_t_boxed_471_; lean_object* v_res_472_; 
v_t_boxed_471_ = lean_unbox(v_t_468_);
v_res_472_ = l_Lake_LogLevel_error_elim(v_motive_467_, v_t_boxed_471_, v_h_469_, v_error_470_);
lean_dec(v_error_470_);
return v_res_472_;
}
}
static uint8_t _init_l_Lake_instInhabitedLogLevel_default(void){
_start:
{
uint8_t v___x_473_; 
v___x_473_ = 0;
return v___x_473_;
}
}
static uint8_t _init_l_Lake_instInhabitedLogLevel(void){
_start:
{
uint8_t v___x_474_; 
v___x_474_ = 0;
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLogLevel_repr(uint8_t v_x_487_, lean_object* v_prec_488_){
_start:
{
lean_object* v___y_490_; lean_object* v___y_497_; lean_object* v___y_504_; lean_object* v___y_511_; 
switch(v_x_487_)
{
case 0:
{
lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_517_ = lean_unsigned_to_nat(1024u);
v___x_518_ = lean_nat_dec_le(v___x_517_, v_prec_488_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; 
v___x_519_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_490_ = v___x_519_;
goto v___jp_489_;
}
else
{
lean_object* v___x_520_; 
v___x_520_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_490_ = v___x_520_;
goto v___jp_489_;
}
}
case 1:
{
lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_521_ = lean_unsigned_to_nat(1024u);
v___x_522_ = lean_nat_dec_le(v___x_521_, v_prec_488_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; 
v___x_523_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_497_ = v___x_523_;
goto v___jp_496_;
}
else
{
lean_object* v___x_524_; 
v___x_524_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_497_ = v___x_524_;
goto v___jp_496_;
}
}
case 2:
{
lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_525_ = lean_unsigned_to_nat(1024u);
v___x_526_ = lean_nat_dec_le(v___x_525_, v_prec_488_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; 
v___x_527_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_504_ = v___x_527_;
goto v___jp_503_;
}
else
{
lean_object* v___x_528_; 
v___x_528_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_504_ = v___x_528_;
goto v___jp_503_;
}
}
default: 
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = lean_unsigned_to_nat(1024u);
v___x_530_ = lean_nat_dec_le(v___x_529_, v_prec_488_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; 
v___x_531_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__6, &l_Lake_instReprVerbosity_repr___closed__6_once, _init_l_Lake_instReprVerbosity_repr___closed__6);
v___y_511_ = v___x_531_;
goto v___jp_510_;
}
else
{
lean_object* v___x_532_; 
v___x_532_ = lean_obj_once(&l_Lake_instReprVerbosity_repr___closed__7, &l_Lake_instReprVerbosity_repr___closed__7_once, _init_l_Lake_instReprVerbosity_repr___closed__7);
v___y_511_ = v___x_532_;
goto v___jp_510_;
}
}
}
v___jp_489_:
{
lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_491_ = ((lean_object*)(l_Lake_instReprLogLevel_repr___closed__1));
lean_inc(v___y_490_);
v___x_492_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_492_, 0, v___y_490_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
v___x_493_ = 0;
v___x_494_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set_uint8(v___x_494_, sizeof(void*)*1, v___x_493_);
v___x_495_ = l_Repr_addAppParen(v___x_494_, v_prec_488_);
return v___x_495_;
}
v___jp_496_:
{
lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_498_ = ((lean_object*)(l_Lake_instReprLogLevel_repr___closed__3));
lean_inc(v___y_497_);
v___x_499_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_499_, 0, v___y_497_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
v___x_500_ = 0;
v___x_501_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_501_, 0, v___x_499_);
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*1, v___x_500_);
v___x_502_ = l_Repr_addAppParen(v___x_501_, v_prec_488_);
return v___x_502_;
}
v___jp_503_:
{
lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_505_ = ((lean_object*)(l_Lake_instReprLogLevel_repr___closed__5));
lean_inc(v___y_504_);
v___x_506_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_506_, 0, v___y_504_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
v___x_507_ = 0;
v___x_508_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_508_, 0, v___x_506_);
lean_ctor_set_uint8(v___x_508_, sizeof(void*)*1, v___x_507_);
v___x_509_ = l_Repr_addAppParen(v___x_508_, v_prec_488_);
return v___x_509_;
}
v___jp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_512_ = ((lean_object*)(l_Lake_instReprLogLevel_repr___closed__7));
lean_inc(v___y_511_);
v___x_513_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_513_, 0, v___y_511_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v___x_514_ = 0;
v___x_515_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set_uint8(v___x_515_, sizeof(void*)*1, v___x_514_);
v___x_516_ = l_Repr_addAppParen(v___x_515_, v_prec_488_);
return v___x_516_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLogLevel_repr___boxed(lean_object* v_x_533_, lean_object* v_prec_534_){
_start:
{
uint8_t v_x_229__boxed_535_; lean_object* v_res_536_; 
v_x_229__boxed_535_ = lean_unbox(v_x_533_);
v_res_536_ = l_Lake_instReprLogLevel_repr(v_x_229__boxed_535_, v_prec_534_);
lean_dec(v_prec_534_);
return v_res_536_;
}
}
LEAN_EXPORT uint8_t l_Lake_LogLevel_ofNat(lean_object* v_n_539_){
_start:
{
lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_540_ = lean_unsigned_to_nat(1u);
v___x_541_ = lean_nat_dec_le(v_n_539_, v___x_540_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_542_ = lean_unsigned_to_nat(2u);
v___x_543_ = lean_nat_dec_le(v_n_539_, v___x_542_);
if (v___x_543_ == 0)
{
uint8_t v___x_544_; 
v___x_544_ = 3;
return v___x_544_;
}
else
{
uint8_t v___x_545_; 
v___x_545_ = 2;
return v___x_545_;
}
}
else
{
lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = lean_nat_dec_le(v_n_539_, v___x_546_);
if (v___x_547_ == 0)
{
uint8_t v___x_548_; 
v___x_548_ = 1;
return v___x_548_;
}
else
{
uint8_t v___x_549_; 
v___x_549_ = 0;
return v___x_549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ofNat___boxed(lean_object* v_n_550_){
_start:
{
uint8_t v_res_551_; lean_object* v_r_552_; 
v_res_551_ = l_Lake_LogLevel_ofNat(v_n_550_);
lean_dec(v_n_550_);
v_r_552_ = lean_box(v_res_551_);
return v_r_552_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqLogLevel(uint8_t v_x_553_, uint8_t v_y_554_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_555_ = l_Lake_LogLevel_ctorIdx(v_x_553_);
v___x_556_ = l_Lake_LogLevel_ctorIdx(v_y_554_);
v___x_557_ = lean_nat_dec_eq(v___x_555_, v___x_556_);
lean_dec(v___x_556_);
lean_dec(v___x_555_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqLogLevel___boxed(lean_object* v_x_558_, lean_object* v_y_559_){
_start:
{
uint8_t v_x_13__boxed_560_; uint8_t v_y_14__boxed_561_; uint8_t v_res_562_; lean_object* v_r_563_; 
v_x_13__boxed_560_ = lean_unbox(v_x_558_);
v_y_14__boxed_561_ = lean_unbox(v_y_559_);
v_res_562_ = l_Lake_instDecidableEqLogLevel(v_x_13__boxed_560_, v_y_14__boxed_561_);
v_r_563_ = lean_box(v_res_562_);
return v_r_563_;
}
}
LEAN_EXPORT uint8_t l_Lake_instOrdLogLevel_ord(uint8_t v_x_564_, uint8_t v_y_565_){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_566_ = l_Lake_LogLevel_ctorIdx(v_x_564_);
v___x_567_ = l_Lake_LogLevel_ctorIdx(v_y_565_);
v___x_568_ = lean_nat_dec_lt(v___x_566_, v___x_567_);
if (v___x_568_ == 0)
{
uint8_t v___x_569_; 
v___x_569_ = lean_nat_dec_eq(v___x_566_, v___x_567_);
lean_dec(v___x_567_);
lean_dec(v___x_566_);
if (v___x_569_ == 0)
{
uint8_t v___x_570_; 
v___x_570_ = 2;
return v___x_570_;
}
else
{
uint8_t v___x_571_; 
v___x_571_ = 1;
return v___x_571_;
}
}
else
{
uint8_t v___x_572_; 
lean_dec(v___x_567_);
lean_dec(v___x_566_);
v___x_572_ = 0;
return v___x_572_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instOrdLogLevel_ord___boxed(lean_object* v_x_573_, lean_object* v_y_574_){
_start:
{
uint8_t v_x_30__boxed_575_; uint8_t v_y_31__boxed_576_; uint8_t v_res_577_; lean_object* v_r_578_; 
v_x_30__boxed_575_ = lean_unbox(v_x_573_);
v_y_31__boxed_576_ = lean_unbox(v_y_574_);
v_res_577_ = l_Lake_instOrdLogLevel_ord(v_x_30__boxed_575_, v_y_31__boxed_576_);
v_r_578_ = lean_box(v_res_577_);
return v_r_578_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonLogLevel_toJson(uint8_t v_x_593_){
_start:
{
switch(v_x_593_)
{
case 0:
{
lean_object* v___x_594_; 
v___x_594_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__1));
return v___x_594_;
}
case 1:
{
lean_object* v___x_595_; 
v___x_595_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__3));
return v___x_595_;
}
case 2:
{
lean_object* v___x_596_; 
v___x_596_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__5));
return v___x_596_;
}
default: 
{
lean_object* v___x_597_; 
v___x_597_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__7));
return v___x_597_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonLogLevel_toJson___boxed(lean_object* v_x_598_){
_start:
{
uint8_t v_x_88__boxed_599_; lean_object* v_res_600_; 
v_x_88__boxed_599_ = lean_unbox(v_x_598_);
v_res_600_ = l_Lake_instToJsonLogLevel_toJson(v_x_88__boxed_599_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonLogLevel_fromJson(lean_object* v_json_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_Json_getTag_x3f(v_json_621_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v___x_623_; 
v___x_623_ = ((lean_object*)(l_Lake_instFromJsonLogLevel_fromJson___closed__1));
return v___x_623_;
}
else
{
lean_object* v_val_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v_val_624_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_val_624_);
lean_dec_ref(v___x_622_);
v___x_625_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__6));
v___x_626_ = lean_string_dec_eq(v_val_624_, v___x_625_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_627_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__0));
v___x_628_ = lean_string_dec_eq(v_val_624_, v___x_627_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_629_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__2));
v___x_630_ = lean_string_dec_eq(v_val_624_, v___x_629_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_631_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__4));
v___x_632_ = lean_string_dec_eq(v_val_624_, v___x_631_);
lean_dec(v_val_624_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; 
v___x_633_ = ((lean_object*)(l_Lake_instFromJsonLogLevel_fromJson___closed__3));
return v___x_633_;
}
else
{
lean_object* v___x_634_; 
v___x_634_ = ((lean_object*)(l_Lake_instFromJsonLogLevel_fromJson___closed__4));
return v___x_634_;
}
}
else
{
lean_object* v___x_635_; 
lean_dec(v_val_624_);
v___x_635_ = ((lean_object*)(l_Lake_instFromJsonLogLevel_fromJson___closed__5));
return v___x_635_;
}
}
else
{
lean_object* v___x_636_; 
lean_dec(v_val_624_);
v___x_636_ = ((lean_object*)(l_Lake_instFromJsonLogLevel_fromJson___closed__6));
return v___x_636_;
}
}
else
{
lean_object* v___x_637_; 
lean_dec(v_val_624_);
v___x_637_ = ((lean_object*)(l_Lake_instFromJsonLogLevel_fromJson___closed__7));
return v___x_637_;
}
}
}
}
static lean_object* _init_l_Lake_instLTLogLevel(void){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = lean_box(0);
return v___x_640_;
}
}
static lean_object* _init_l_Lake_instLELogLevel(void){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = lean_box(0);
return v___x_641_;
}
}
LEAN_EXPORT uint8_t l_Lake_instMinLogLevel___lam__0(uint8_t v_x_642_, uint8_t v_y_643_){
_start:
{
uint8_t v___x_644_; 
v___x_644_ = l_Lake_instOrdLogLevel_ord(v_x_642_, v_y_643_);
if (v___x_644_ == 2)
{
return v_y_643_;
}
else
{
return v_x_642_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMinLogLevel___lam__0___boxed(lean_object* v_x_645_, lean_object* v_y_646_){
_start:
{
uint8_t v_x_boxed_647_; uint8_t v_y_boxed_648_; uint8_t v_res_649_; lean_object* v_r_650_; 
v_x_boxed_647_ = lean_unbox(v_x_645_);
v_y_boxed_648_ = lean_unbox(v_y_646_);
v_res_649_ = l_Lake_instMinLogLevel___lam__0(v_x_boxed_647_, v_y_boxed_648_);
v_r_650_ = lean_box(v_res_649_);
return v_r_650_;
}
}
LEAN_EXPORT uint8_t l_Lake_instMaxLogLevel___lam__0(uint8_t v_x_653_, uint8_t v_y_654_){
_start:
{
uint8_t v___x_655_; 
v___x_655_ = l_Lake_instOrdLogLevel_ord(v_x_653_, v_y_654_);
if (v___x_655_ == 2)
{
return v_x_653_;
}
else
{
return v_y_654_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxLogLevel___lam__0___boxed(lean_object* v_x_656_, lean_object* v_y_657_){
_start:
{
uint8_t v_x_boxed_658_; uint8_t v_y_boxed_659_; uint8_t v_res_660_; lean_object* v_r_661_; 
v_x_boxed_658_ = lean_unbox(v_x_656_);
v_y_boxed_659_ = lean_unbox(v_y_657_);
v_res_660_ = l_Lake_instMaxLogLevel___lam__0(v_x_boxed_658_, v_y_boxed_659_);
v_r_661_ = lean_box(v_res_660_);
return v_r_661_;
}
}
LEAN_EXPORT uint32_t l_Lake_LogLevel_icon(uint8_t v_x_664_){
_start:
{
switch(v_x_664_)
{
case 2:
{
uint32_t v___x_665_; 
v___x_665_ = 9888;
return v___x_665_;
}
case 3:
{
uint32_t v___x_666_; 
v___x_666_ = 10006;
return v___x_666_;
}
default: 
{
uint32_t v___x_667_; 
v___x_667_ = 8505;
return v___x_667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_icon___boxed(lean_object* v_x_668_){
_start:
{
uint8_t v_x_33__boxed_669_; uint32_t v_res_670_; lean_object* v_r_671_; 
v_x_33__boxed_669_ = lean_unbox(v_x_668_);
v_res_670_ = l_Lake_LogLevel_icon(v_x_33__boxed_669_);
v_r_671_ = lean_box_uint32(v_res_670_);
return v_r_671_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ansiColor(uint8_t v_x_675_){
_start:
{
switch(v_x_675_)
{
case 2:
{
lean_object* v___x_676_; 
v___x_676_ = ((lean_object*)(l_Lake_LogLevel_ansiColor___closed__0));
return v___x_676_;
}
case 3:
{
lean_object* v___x_677_; 
v___x_677_ = ((lean_object*)(l_Lake_LogLevel_ansiColor___closed__1));
return v___x_677_;
}
default: 
{
lean_object* v___x_678_; 
v___x_678_ = ((lean_object*)(l_Lake_LogLevel_ansiColor___closed__2));
return v___x_678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ansiColor___boxed(lean_object* v_x_679_){
_start:
{
uint8_t v_x_36__boxed_680_; lean_object* v_res_681_; 
v_x_36__boxed_680_ = lean_unbox(v_x_679_);
v_res_681_ = l_Lake_LogLevel_ansiColor(v_x_36__boxed_680_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00Lake_LogLevel_ofString_x3f_spec__0(lean_object* v_s_682_, lean_object* v_p_683_){
_start:
{
uint32_t v___y_685_; lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_690_ = lean_string_utf8_byte_size(v_s_682_);
v___x_691_ = lean_nat_dec_eq(v_p_683_, v___x_690_);
if (v___x_691_ == 0)
{
uint32_t v___x_692_; uint32_t v___x_693_; uint8_t v___x_694_; 
v___x_692_ = lean_string_utf8_get_fast(v_s_682_, v_p_683_);
v___x_693_ = 65;
v___x_694_ = lean_uint32_dec_le(v___x_693_, v___x_692_);
if (v___x_694_ == 0)
{
v___y_685_ = v___x_692_;
goto v___jp_684_;
}
else
{
uint32_t v___x_695_; uint8_t v___x_696_; 
v___x_695_ = 90;
v___x_696_ = lean_uint32_dec_le(v___x_692_, v___x_695_);
if (v___x_696_ == 0)
{
v___y_685_ = v___x_692_;
goto v___jp_684_;
}
else
{
uint32_t v___x_697_; uint32_t v___x_698_; 
v___x_697_ = 32;
v___x_698_ = lean_uint32_add(v___x_692_, v___x_697_);
v___y_685_ = v___x_698_;
goto v___jp_684_;
}
}
}
else
{
lean_dec(v_p_683_);
return v_s_682_;
}
v___jp_684_:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
lean_inc(v_p_683_);
v___x_686_ = lean_string_utf8_set(v_s_682_, v_p_683_, v___y_685_);
v___x_687_ = l_Char_utf8Size(v___y_685_);
v___x_688_ = lean_nat_add(v_p_683_, v___x_687_);
lean_dec(v___x_687_);
lean_dec(v_p_683_);
v_s_682_ = v___x_686_;
v_p_683_ = v___x_688_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ofString_x3f(lean_object* v_s_713_){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_718_ = lean_unsigned_to_nat(0u);
v___x_719_ = l_String_mapAux___at___00Lake_LogLevel_ofString_x3f_spec__0(v_s_713_, v___x_718_);
v___x_720_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__0));
v___x_721_ = lean_string_dec_eq(v___x_719_, v___x_720_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_722_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__2));
v___x_723_ = lean_string_dec_eq(v___x_719_, v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_724_ = ((lean_object*)(l_Lake_LogLevel_ofString_x3f___closed__2));
v___x_725_ = lean_string_dec_eq(v___x_719_, v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = ((lean_object*)(l_Lake_LogLevel_ofString_x3f___closed__3));
v___x_727_ = lean_string_dec_eq(v___x_719_, v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__4));
v___x_729_ = lean_string_dec_eq(v___x_719_, v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_730_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__6));
v___x_731_ = lean_string_dec_eq(v___x_719_, v___x_730_);
lean_dec_ref(v___x_719_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; 
v___x_732_ = lean_box(0);
return v___x_732_;
}
else
{
lean_object* v___x_733_; 
v___x_733_ = ((lean_object*)(l_Lake_LogLevel_ofString_x3f___closed__4));
return v___x_733_;
}
}
else
{
lean_dec_ref(v___x_719_);
goto v___jp_716_;
}
}
else
{
lean_dec_ref(v___x_719_);
goto v___jp_716_;
}
}
else
{
lean_dec_ref(v___x_719_);
goto v___jp_714_;
}
}
else
{
lean_dec_ref(v___x_719_);
goto v___jp_714_;
}
}
else
{
lean_object* v___x_734_; 
lean_dec_ref(v___x_719_);
v___x_734_ = ((lean_object*)(l_Lake_LogLevel_ofString_x3f___closed__5));
return v___x_734_;
}
v___jp_714_:
{
lean_object* v___x_715_; 
v___x_715_ = ((lean_object*)(l_Lake_LogLevel_ofString_x3f___closed__0));
return v___x_715_;
}
v___jp_716_:
{
lean_object* v___x_717_; 
v___x_717_ = ((lean_object*)(l_Lake_LogLevel_ofString_x3f___closed__1));
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_toString(uint8_t v_x_735_){
_start:
{
switch(v_x_735_)
{
case 0:
{
lean_object* v___x_736_; 
v___x_736_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__0));
return v___x_736_;
}
case 1:
{
lean_object* v___x_737_; 
v___x_737_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__2));
return v___x_737_;
}
case 2:
{
lean_object* v___x_738_; 
v___x_738_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__4));
return v___x_738_;
}
default: 
{
lean_object* v___x_739_; 
v___x_739_ = ((lean_object*)(l_Lake_instToJsonLogLevel_toJson___closed__6));
return v___x_739_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_toString___boxed(lean_object* v_x_740_){
_start:
{
uint8_t v_x_36__boxed_741_; lean_object* v_res_742_; 
v_x_36__boxed_741_ = lean_unbox(v_x_740_);
v_res_742_ = l_Lake_LogLevel_toString(v_x_36__boxed_741_);
return v_res_742_;
}
}
LEAN_EXPORT uint8_t l_Lake_LogLevel_ofMessageSeverity(uint8_t v_x_745_){
_start:
{
switch(v_x_745_)
{
case 0:
{
uint8_t v___x_746_; 
v___x_746_ = 1;
return v___x_746_;
}
case 1:
{
uint8_t v___x_747_; 
v___x_747_ = 2;
return v___x_747_;
}
default: 
{
uint8_t v___x_748_; 
v___x_748_ = 3;
return v___x_748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ofMessageSeverity___boxed(lean_object* v_x_749_){
_start:
{
uint8_t v_x_25__boxed_750_; uint8_t v_res_751_; lean_object* v_r_752_; 
v_x_25__boxed_750_ = lean_unbox(v_x_749_);
v_res_751_ = l_Lake_LogLevel_ofMessageSeverity(v_x_25__boxed_750_);
v_r_752_ = lean_box(v_res_751_);
return v_r_752_;
}
}
LEAN_EXPORT uint8_t l_Lake_LogLevel_toMessageSeverity(uint8_t v_x_753_){
_start:
{
switch(v_x_753_)
{
case 2:
{
uint8_t v___x_754_; 
v___x_754_ = 1;
return v___x_754_;
}
case 3:
{
uint8_t v___x_755_; 
v___x_755_ = 2;
return v___x_755_;
}
default: 
{
uint8_t v___x_756_; 
v___x_756_ = 0;
return v___x_756_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_toMessageSeverity___boxed(lean_object* v_x_757_){
_start:
{
uint8_t v_x_30__boxed_758_; uint8_t v_res_759_; lean_object* v_r_760_; 
v_x_30__boxed_758_ = lean_unbox(v_x_757_);
v_res_759_ = l_Lake_LogLevel_toMessageSeverity(v_x_30__boxed_758_);
v_r_760_ = lean_box(v_res_759_);
return v_r_760_;
}
}
LEAN_EXPORT uint8_t l_Lake_Verbosity_minLogLv(uint8_t v_x_761_){
_start:
{
switch(v_x_761_)
{
case 0:
{
uint8_t v___x_762_; 
v___x_762_ = 2;
return v___x_762_;
}
case 1:
{
uint8_t v___x_763_; 
v___x_763_ = 1;
return v___x_763_;
}
default: 
{
uint8_t v___x_764_; 
v___x_764_ = 0;
return v___x_764_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_minLogLv___boxed(lean_object* v_x_765_){
_start:
{
uint8_t v_x_25__boxed_766_; uint8_t v_res_767_; lean_object* v_r_768_; 
v_x_25__boxed_766_ = lean_unbox(v_x_765_);
v_res_767_ = l_Lake_Verbosity_minLogLv(v_x_25__boxed_766_);
v_r_768_ = lean_box(v_res_767_);
return v_r_768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_instToJsonLogEntry_toJson_spec__0(lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
if (lean_obj_tag(v_a_775_) == 0)
{
lean_object* v___x_777_; 
v___x_777_ = lean_array_to_list(v_a_776_);
return v___x_777_;
}
else
{
lean_object* v_head_778_; lean_object* v_tail_779_; lean_object* v___x_780_; 
v_head_778_ = lean_ctor_get(v_a_775_, 0);
lean_inc(v_head_778_);
v_tail_779_ = lean_ctor_get(v_a_775_, 1);
lean_inc(v_tail_779_);
lean_dec_ref(v_a_775_);
v___x_780_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_776_, v_head_778_);
v_a_775_ = v_tail_779_;
v_a_776_ = v___x_780_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonLogEntry_toJson(lean_object* v_x_786_){
_start:
{
uint8_t v_level_787_; lean_object* v_message_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v_level_787_ = lean_ctor_get_uint8(v_x_786_, sizeof(void*)*1);
v_message_788_ = lean_ctor_get(v_x_786_, 0);
v___x_789_ = ((lean_object*)(l_Lake_instToJsonLogEntry_toJson___closed__0));
v___x_790_ = l_Lake_instToJsonLogLevel_toJson(v_level_787_);
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_789_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
v___x_792_ = lean_box(0);
v___x_793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_791_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = ((lean_object*)(l_Lake_instToJsonLogEntry_toJson___closed__1));
lean_inc_ref(v_message_788_);
v___x_795_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_795_, 0, v_message_788_);
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_794_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
lean_ctor_set(v___x_797_, 1, v___x_792_);
v___x_798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
lean_ctor_set(v___x_798_, 1, v___x_792_);
v___x_799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_793_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = ((lean_object*)(l_Lake_instToJsonLogEntry_toJson___closed__2));
v___x_801_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_instToJsonLogEntry_toJson_spec__0(v___x_799_, v___x_800_);
v___x_802_ = l_Lean_Json_mkObj(v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonLogEntry_toJson___boxed(lean_object* v_x_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lake_instToJsonLogEntry_toJson(v_x_803_);
lean_dec_ref(v_x_803_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__0(lean_object* v_j_807_, lean_object* v_k_808_){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = l_Lean_Json_getObjValD(v_j_807_, v_k_808_);
v___x_810_ = l_Lake_instFromJsonLogLevel_fromJson(v___x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__0___boxed(lean_object* v_j_811_, lean_object* v_k_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__0(v_j_811_, v_k_812_);
lean_dec_ref(v_k_812_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1(lean_object* v_j_814_, lean_object* v_k_815_){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = l_Lean_Json_getObjValD(v_j_814_, v_k_815_);
v___x_817_ = l_Lean_Json_getStr_x3f(v___x_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1___boxed(lean_object* v_j_818_, lean_object* v_k_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1(v_j_818_, v_k_819_);
lean_dec_ref(v_k_819_);
return v_res_820_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__3(void){
_start:
{
uint8_t v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_826_ = 1;
v___x_827_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__2));
v___x_828_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_827_, v___x_826_);
return v___x_828_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__5(void){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_830_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__4));
v___x_831_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__3, &l_Lake_instFromJsonLogEntry_fromJson___closed__3_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__3);
v___x_832_ = lean_string_append(v___x_831_, v___x_830_);
return v___x_832_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__7(void){
_start:
{
uint8_t v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_835_ = 1;
v___x_836_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__6));
v___x_837_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_836_, v___x_835_);
return v___x_837_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__8(void){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_838_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__7, &l_Lake_instFromJsonLogEntry_fromJson___closed__7_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__7);
v___x_839_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__5, &l_Lake_instFromJsonLogEntry_fromJson___closed__5_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__5);
v___x_840_ = lean_string_append(v___x_839_, v___x_838_);
return v___x_840_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__10(void){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_842_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__9));
v___x_843_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__8, &l_Lake_instFromJsonLogEntry_fromJson___closed__8_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__8);
v___x_844_ = lean_string_append(v___x_843_, v___x_842_);
return v___x_844_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__12(void){
_start:
{
uint8_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_847_ = 1;
v___x_848_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__11));
v___x_849_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_848_, v___x_847_);
return v___x_849_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__13(void){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_850_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__12, &l_Lake_instFromJsonLogEntry_fromJson___closed__12_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__12);
v___x_851_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__5, &l_Lake_instFromJsonLogEntry_fromJson___closed__5_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__5);
v___x_852_ = lean_string_append(v___x_851_, v___x_850_);
return v___x_852_;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry_fromJson___closed__14(void){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_853_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__9));
v___x_854_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__13, &l_Lake_instFromJsonLogEntry_fromJson___closed__13_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__13);
v___x_855_ = lean_string_append(v___x_854_, v___x_853_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonLogEntry_fromJson(lean_object* v_json_856_){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = ((lean_object*)(l_Lake_instToJsonLogEntry_toJson___closed__0));
lean_inc(v_json_856_);
v___x_858_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__0(v_json_856_, v___x_857_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_868_; 
lean_dec(v_json_856_);
v_a_859_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_868_ == 0)
{
v___x_861_ = v___x_858_;
v_isShared_862_ = v_isSharedCheck_868_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_858_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_868_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_863_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__10, &l_Lake_instFromJsonLogEntry_fromJson___closed__10_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__10);
v___x_864_ = lean_string_append(v___x_863_, v_a_859_);
lean_dec(v_a_859_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_864_);
v___x_866_ = v___x_861_;
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
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
lean_dec(v_json_856_);
v_a_869_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_858_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_858_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
lean_ctor_set_tag(v___x_871_, 0);
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v_a_877_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_877_);
lean_dec_ref(v___x_858_);
v___x_878_ = ((lean_object*)(l_Lake_instToJsonLogEntry_toJson___closed__1));
v___x_879_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1(v_json_856_, v___x_878_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_889_; 
lean_dec(v_a_877_);
v_a_880_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_889_ == 0)
{
v___x_882_ = v___x_879_;
v_isShared_883_ = v_isSharedCheck_889_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_879_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_889_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_884_ = lean_obj_once(&l_Lake_instFromJsonLogEntry_fromJson___closed__14, &l_Lake_instFromJsonLogEntry_fromJson___closed__14_once, _init_l_Lake_instFromJsonLogEntry_fromJson___closed__14);
v___x_885_ = lean_string_append(v___x_884_, v_a_880_);
lean_dec(v_a_880_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_885_);
v___x_887_ = v___x_882_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
else
{
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
lean_dec(v_a_877_);
v_a_890_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_879_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_879_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set_tag(v___x_892_, 0);
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
else
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_907_; 
v_a_898_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_907_ == 0)
{
v___x_900_ = v___x_879_;
v_isShared_901_ = v_isSharedCheck_907_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_879_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_907_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; uint8_t v___x_903_; lean_object* v___x_905_; 
v___x_902_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_902_, 0, v_a_898_);
v___x_903_ = lean_unbox(v_a_877_);
lean_dec(v_a_877_);
lean_ctor_set_uint8(v___x_902_, sizeof(void*)*1, v___x_903_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v___x_902_);
v___x_905_ = v___x_900_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_902_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_toString(lean_object* v_self_912_, uint8_t v_useAnsi_913_){
_start:
{
if (v_useAnsi_913_ == 0)
{
uint8_t v_level_914_; lean_object* v_message_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v_level_914_ = lean_ctor_get_uint8(v_self_912_, sizeof(void*)*1);
v_message_915_ = lean_ctor_get(v_self_912_, 0);
v___x_916_ = l_Lake_LogLevel_toString(v_level_914_);
v___x_917_ = ((lean_object*)(l_Lake_instFromJsonLogEntry_fromJson___closed__9));
v___x_918_ = lean_string_append(v___x_916_, v___x_917_);
v___x_919_ = lean_string_append(v___x_918_, v_message_915_);
return v___x_919_;
}
else
{
uint8_t v_level_920_; lean_object* v_message_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v_pre_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v_level_920_ = lean_ctor_get_uint8(v_self_912_, sizeof(void*)*1);
v_message_921_ = lean_ctor_get(v_self_912_, 0);
v___x_922_ = l_Lake_LogLevel_ansiColor(v_level_920_);
v___x_923_ = l_Lake_LogLevel_toString(v_level_920_);
v___x_924_ = ((lean_object*)(l_Lake_LogEntry_toString___closed__0));
v___x_925_ = lean_string_append(v___x_923_, v___x_924_);
v_pre_926_ = l_Lake_Ansi_chalk(v___x_922_, v___x_925_);
lean_dec_ref(v___x_925_);
lean_dec_ref(v___x_922_);
v___x_927_ = ((lean_object*)(l_Lake_LogEntry_toString___closed__1));
v___x_928_ = lean_string_append(v_pre_926_, v___x_927_);
v___x_929_ = lean_string_append(v___x_928_, v_message_921_);
return v___x_929_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_toString___boxed(lean_object* v_self_930_, lean_object* v_useAnsi_931_){
_start:
{
uint8_t v_useAnsi_boxed_932_; lean_object* v_res_933_; 
v_useAnsi_boxed_932_ = lean_unbox(v_useAnsi_931_);
v_res_933_ = l_Lake_LogEntry_toString(v_self_930_, v_useAnsi_boxed_932_);
lean_dec_ref(v_self_930_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToStringLogEntry___lam__0(lean_object* v_self_934_){
_start:
{
uint8_t v___x_935_; lean_object* v___x_936_; 
v___x_935_ = 0;
v___x_936_ = l_Lake_LogEntry_toString(v_self_934_, v___x_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToStringLogEntry___lam__0___boxed(lean_object* v_self_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lake_instToStringLogEntry___lam__0(v_self_937_);
lean_dec_ref(v_self_937_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_trace(lean_object* v_message_941_){
_start:
{
uint8_t v___x_942_; lean_object* v___x_943_; 
v___x_942_ = 0;
v___x_943_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_943_, 0, v_message_941_);
lean_ctor_set_uint8(v___x_943_, sizeof(void*)*1, v___x_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_info(lean_object* v_message_944_){
_start:
{
uint8_t v___x_945_; lean_object* v___x_946_; 
v___x_945_ = 1;
v___x_946_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_946_, 0, v_message_944_);
lean_ctor_set_uint8(v___x_946_, sizeof(void*)*1, v___x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_warning(lean_object* v_message_947_){
_start:
{
uint8_t v___x_948_; lean_object* v___x_949_; 
v___x_948_ = 2;
v___x_949_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_949_, 0, v_message_947_);
lean_ctor_set_uint8(v___x_949_, sizeof(void*)*1, v___x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_error(lean_object* v_message_950_){
_start:
{
uint8_t v___x_951_; lean_object* v___x_952_; 
v___x_951_ = 3;
v___x_952_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_952_, 0, v_message_950_);
lean_ctor_set_uint8(v___x_952_, sizeof(void*)*1, v___x_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_ofSerialMessage(lean_object* v_msg_954_){
_start:
{
lean_object* v_toBaseMessage_955_; lean_object* v_fileName_956_; lean_object* v_pos_957_; uint8_t v_severity_958_; lean_object* v_caption_959_; lean_object* v_data_960_; lean_object* v___y_962_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v_startInclusive_971_; lean_object* v_endExclusive_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v_toBaseMessage_955_ = lean_ctor_get(v_msg_954_, 0);
lean_inc_ref(v_toBaseMessage_955_);
lean_dec_ref(v_msg_954_);
v_fileName_956_ = lean_ctor_get(v_toBaseMessage_955_, 0);
lean_inc_ref(v_fileName_956_);
v_pos_957_ = lean_ctor_get(v_toBaseMessage_955_, 1);
lean_inc_ref(v_pos_957_);
v_severity_958_ = lean_ctor_get_uint8(v_toBaseMessage_955_, sizeof(void*)*5 + 1);
v_caption_959_ = lean_ctor_get(v_toBaseMessage_955_, 3);
lean_inc_ref(v_caption_959_);
v_data_960_ = lean_ctor_get(v_toBaseMessage_955_, 4);
lean_inc(v_data_960_);
lean_dec_ref(v_toBaseMessage_955_);
v___x_967_ = lean_unsigned_to_nat(0u);
v___x_968_ = lean_string_utf8_byte_size(v_caption_959_);
v___x_969_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_969_, 0, v_caption_959_);
lean_ctor_set(v___x_969_, 1, v___x_967_);
lean_ctor_set(v___x_969_, 2, v___x_968_);
v___x_970_ = l_String_Slice_trimAscii(v___x_969_);
v_startInclusive_971_ = lean_ctor_get(v___x_970_, 1);
lean_inc(v_startInclusive_971_);
v_endExclusive_972_ = lean_ctor_get(v___x_970_, 2);
lean_inc(v_endExclusive_972_);
v___x_973_ = lean_nat_sub(v_endExclusive_972_, v_startInclusive_971_);
lean_dec(v_startInclusive_971_);
lean_dec(v_endExclusive_972_);
v___x_974_ = lean_nat_dec_eq(v___x_973_, v___x_967_);
lean_dec(v___x_973_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_988_; 
v___x_975_ = l_String_Slice_toString(v___x_970_);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_988_ == 0)
{
lean_object* v_unused_989_; lean_object* v_unused_990_; lean_object* v_unused_991_; 
v_unused_989_ = lean_ctor_get(v___x_970_, 2);
lean_dec(v_unused_989_);
v_unused_990_ = lean_ctor_get(v___x_970_, 1);
lean_dec(v_unused_990_);
v_unused_991_ = lean_ctor_get(v___x_970_, 0);
lean_dec(v_unused_991_);
v___x_977_ = v___x_970_;
v_isShared_978_ = v_isSharedCheck_988_;
goto v_resetjp_976_;
}
else
{
lean_dec(v___x_970_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_988_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_983_; 
v___x_979_ = ((lean_object*)(l_Lake_LogEntry_ofSerialMessage___closed__0));
v___x_980_ = lean_string_append(v___x_975_, v___x_979_);
v___x_981_ = lean_string_utf8_byte_size(v_data_960_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 2, v___x_981_);
lean_ctor_set(v___x_977_, 1, v___x_967_);
lean_ctor_set(v___x_977_, 0, v_data_960_);
v___x_983_ = v___x_977_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_data_960_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v___x_967_);
lean_ctor_set(v_reuseFailAlloc_987_, 2, v___x_981_);
v___x_983_ = v_reuseFailAlloc_987_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_984_ = l_String_Slice_trimAscii(v___x_983_);
v___x_985_ = l_String_Slice_toString(v___x_984_);
lean_dec_ref(v___x_984_);
v___x_986_ = lean_string_append(v___x_980_, v___x_985_);
lean_dec_ref(v___x_985_);
v___y_962_ = v___x_986_;
goto v___jp_961_;
}
}
}
else
{
lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1004_; 
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1004_ == 0)
{
lean_object* v_unused_1005_; lean_object* v_unused_1006_; lean_object* v_unused_1007_; 
v_unused_1005_ = lean_ctor_get(v___x_970_, 2);
lean_dec(v_unused_1005_);
v_unused_1006_ = lean_ctor_get(v___x_970_, 1);
lean_dec(v_unused_1006_);
v_unused_1007_ = lean_ctor_get(v___x_970_, 0);
lean_dec(v_unused_1007_);
v___x_993_ = v___x_970_;
v_isShared_994_ = v_isSharedCheck_1004_;
goto v_resetjp_992_;
}
else
{
lean_dec(v___x_970_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1004_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_995_ = lean_string_utf8_byte_size(v_data_960_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 2, v___x_995_);
lean_ctor_set(v___x_993_, 1, v___x_967_);
lean_ctor_set(v___x_993_, 0, v_data_960_);
v___x_997_ = v___x_993_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_data_960_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v___x_967_);
lean_ctor_set(v_reuseFailAlloc_1003_, 2, v___x_995_);
v___x_997_ = v_reuseFailAlloc_1003_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_998_; lean_object* v_str_999_; lean_object* v_startInclusive_1000_; lean_object* v_endExclusive_1001_; lean_object* v___x_1002_; 
v___x_998_ = l_String_Slice_trimAscii(v___x_997_);
v_str_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc_ref(v_str_999_);
v_startInclusive_1000_ = lean_ctor_get(v___x_998_, 1);
lean_inc(v_startInclusive_1000_);
v_endExclusive_1001_ = lean_ctor_get(v___x_998_, 2);
lean_inc(v_endExclusive_1001_);
lean_dec_ref(v___x_998_);
v___x_1002_ = lean_string_utf8_extract(v_str_999_, v_startInclusive_1000_, v_endExclusive_1001_);
lean_dec(v_endExclusive_1001_);
lean_dec(v_startInclusive_1000_);
lean_dec_ref(v_str_999_);
v___y_962_ = v___x_1002_;
goto v___jp_961_;
}
}
}
v___jp_961_:
{
uint8_t v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_963_ = l_Lake_LogLevel_ofMessageSeverity(v_severity_958_);
v___x_964_ = lean_box(0);
v___x_965_ = l_Lean_mkErrorStringWithPos(v_fileName_956_, v_pos_957_, v___y_962_, v___x_964_, v___x_964_, v___x_964_);
lean_dec_ref(v___y_962_);
v___x_966_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_966_, 0, v___x_965_);
lean_ctor_set_uint8(v___x_966_, sizeof(void*)*1, v___x_963_);
return v___x_966_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_ofMessage(lean_object* v_msg_1008_){
_start:
{
lean_object* v_fileName_1010_; lean_object* v_pos_1011_; uint8_t v_severity_1012_; lean_object* v_caption_1013_; lean_object* v_data_1014_; lean_object* v___x_1015_; lean_object* v___y_1017_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v_startInclusive_1026_; lean_object* v_endExclusive_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; 
v_fileName_1010_ = lean_ctor_get(v_msg_1008_, 0);
lean_inc_ref(v_fileName_1010_);
v_pos_1011_ = lean_ctor_get(v_msg_1008_, 1);
lean_inc_ref(v_pos_1011_);
v_severity_1012_ = lean_ctor_get_uint8(v_msg_1008_, sizeof(void*)*5 + 1);
v_caption_1013_ = lean_ctor_get(v_msg_1008_, 3);
lean_inc_ref(v_caption_1013_);
v_data_1014_ = lean_ctor_get(v_msg_1008_, 4);
lean_inc(v_data_1014_);
lean_dec_ref(v_msg_1008_);
v___x_1015_ = l_Lean_MessageData_toString(v_data_1014_);
v___x_1022_ = lean_unsigned_to_nat(0u);
v___x_1023_ = lean_string_utf8_byte_size(v_caption_1013_);
v___x_1024_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1024_, 0, v_caption_1013_);
lean_ctor_set(v___x_1024_, 1, v___x_1022_);
lean_ctor_set(v___x_1024_, 2, v___x_1023_);
v___x_1025_ = l_String_Slice_trimAscii(v___x_1024_);
v_startInclusive_1026_ = lean_ctor_get(v___x_1025_, 1);
lean_inc(v_startInclusive_1026_);
v_endExclusive_1027_ = lean_ctor_get(v___x_1025_, 2);
lean_inc(v_endExclusive_1027_);
v___x_1028_ = lean_nat_sub(v_endExclusive_1027_, v_startInclusive_1026_);
lean_dec(v_startInclusive_1026_);
lean_dec(v_endExclusive_1027_);
v___x_1029_ = lean_nat_dec_eq(v___x_1028_, v___x_1022_);
lean_dec(v___x_1028_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1043_; 
v___x_1030_ = l_String_Slice_toString(v___x_1025_);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1043_ == 0)
{
lean_object* v_unused_1044_; lean_object* v_unused_1045_; lean_object* v_unused_1046_; 
v_unused_1044_ = lean_ctor_get(v___x_1025_, 2);
lean_dec(v_unused_1044_);
v_unused_1045_ = lean_ctor_get(v___x_1025_, 1);
lean_dec(v_unused_1045_);
v_unused_1046_ = lean_ctor_get(v___x_1025_, 0);
lean_dec(v_unused_1046_);
v___x_1032_ = v___x_1025_;
v_isShared_1033_ = v_isSharedCheck_1043_;
goto v_resetjp_1031_;
}
else
{
lean_dec(v___x_1025_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1043_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1034_ = ((lean_object*)(l_Lake_LogEntry_ofSerialMessage___closed__0));
v___x_1035_ = lean_string_append(v___x_1030_, v___x_1034_);
v___x_1036_ = lean_string_utf8_byte_size(v___x_1015_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 2, v___x_1036_);
lean_ctor_set(v___x_1032_, 1, v___x_1022_);
lean_ctor_set(v___x_1032_, 0, v___x_1015_);
v___x_1038_ = v___x_1032_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v___x_1022_);
lean_ctor_set(v_reuseFailAlloc_1042_, 2, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1039_ = l_String_Slice_trimAscii(v___x_1038_);
v___x_1040_ = l_String_Slice_toString(v___x_1039_);
lean_dec_ref(v___x_1039_);
v___x_1041_ = lean_string_append(v___x_1035_, v___x_1040_);
lean_dec_ref(v___x_1040_);
v___y_1017_ = v___x_1041_;
goto v___jp_1016_;
}
}
}
else
{
lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1059_; 
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1059_ == 0)
{
lean_object* v_unused_1060_; lean_object* v_unused_1061_; lean_object* v_unused_1062_; 
v_unused_1060_ = lean_ctor_get(v___x_1025_, 2);
lean_dec(v_unused_1060_);
v_unused_1061_ = lean_ctor_get(v___x_1025_, 1);
lean_dec(v_unused_1061_);
v_unused_1062_ = lean_ctor_get(v___x_1025_, 0);
lean_dec(v_unused_1062_);
v___x_1048_ = v___x_1025_;
v_isShared_1049_ = v_isSharedCheck_1059_;
goto v_resetjp_1047_;
}
else
{
lean_dec(v___x_1025_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1059_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1050_ = lean_string_utf8_byte_size(v___x_1015_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 2, v___x_1050_);
lean_ctor_set(v___x_1048_, 1, v___x_1022_);
lean_ctor_set(v___x_1048_, 0, v___x_1015_);
v___x_1052_ = v___x_1048_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v___x_1022_);
lean_ctor_set(v_reuseFailAlloc_1058_, 2, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1053_; lean_object* v_str_1054_; lean_object* v_startInclusive_1055_; lean_object* v_endExclusive_1056_; lean_object* v___x_1057_; 
v___x_1053_ = l_String_Slice_trimAscii(v___x_1052_);
v_str_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc_ref(v_str_1054_);
v_startInclusive_1055_ = lean_ctor_get(v___x_1053_, 1);
lean_inc(v_startInclusive_1055_);
v_endExclusive_1056_ = lean_ctor_get(v___x_1053_, 2);
lean_inc(v_endExclusive_1056_);
lean_dec_ref(v___x_1053_);
v___x_1057_ = lean_string_utf8_extract(v_str_1054_, v_startInclusive_1055_, v_endExclusive_1056_);
lean_dec(v_endExclusive_1056_);
lean_dec(v_startInclusive_1055_);
lean_dec_ref(v_str_1054_);
v___y_1017_ = v___x_1057_;
goto v___jp_1016_;
}
}
}
v___jp_1016_:
{
uint8_t v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1018_ = l_Lake_LogLevel_ofMessageSeverity(v_severity_1012_);
v___x_1019_ = lean_box(0);
v___x_1020_ = l_Lean_mkErrorStringWithPos(v_fileName_1010_, v_pos_1011_, v___y_1017_, v___x_1019_, v___x_1019_, v___x_1019_);
lean_dec_ref(v___y_1017_);
v___x_1021_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
lean_ctor_set_uint8(v___x_1021_, sizeof(void*)*1, v___x_1018_);
return v___x_1021_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_ofMessage___boxed(lean_object* v_msg_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lake_LogEntry_ofMessage(v_msg_1063_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lake_logVerbose___redArg(lean_object* v_inst_1066_, lean_object* v_message_1067_){
_start:
{
uint8_t v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1068_ = 0;
v___x_1069_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1069_, 0, v_message_1067_);
lean_ctor_set_uint8(v___x_1069_, sizeof(void*)*1, v___x_1068_);
v___x_1070_ = lean_apply_1(v_inst_1066_, v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lake_logVerbose(lean_object* v_m_1071_, lean_object* v_inst_1072_, lean_object* v_inst_1073_, lean_object* v_message_1074_){
_start:
{
uint8_t v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1075_ = 0;
v___x_1076_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1076_, 0, v_message_1074_);
lean_ctor_set_uint8(v___x_1076_, sizeof(void*)*1, v___x_1075_);
v___x_1077_ = lean_apply_1(v_inst_1073_, v___x_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Lake_logVerbose___boxed(lean_object* v_m_1078_, lean_object* v_inst_1079_, lean_object* v_inst_1080_, lean_object* v_message_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lake_logVerbose(v_m_1078_, v_inst_1079_, v_inst_1080_, v_message_1081_);
lean_dec_ref(v_inst_1079_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lake_logInfo___redArg(lean_object* v_inst_1083_, lean_object* v_message_1084_){
_start:
{
uint8_t v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1085_ = 1;
v___x_1086_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1086_, 0, v_message_1084_);
lean_ctor_set_uint8(v___x_1086_, sizeof(void*)*1, v___x_1085_);
v___x_1087_ = lean_apply_1(v_inst_1083_, v___x_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lake_logInfo(lean_object* v_m_1088_, lean_object* v_inst_1089_, lean_object* v_inst_1090_, lean_object* v_message_1091_){
_start:
{
uint8_t v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1092_ = 1;
v___x_1093_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1093_, 0, v_message_1091_);
lean_ctor_set_uint8(v___x_1093_, sizeof(void*)*1, v___x_1092_);
v___x_1094_ = lean_apply_1(v_inst_1090_, v___x_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lake_logInfo___boxed(lean_object* v_m_1095_, lean_object* v_inst_1096_, lean_object* v_inst_1097_, lean_object* v_message_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lake_logInfo(v_m_1095_, v_inst_1096_, v_inst_1097_, v_message_1098_);
lean_dec_ref(v_inst_1096_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lake_logWarning___redArg(lean_object* v_inst_1100_, lean_object* v_message_1101_){
_start:
{
uint8_t v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1102_ = 2;
v___x_1103_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1103_, 0, v_message_1101_);
lean_ctor_set_uint8(v___x_1103_, sizeof(void*)*1, v___x_1102_);
v___x_1104_ = lean_apply_1(v_inst_1100_, v___x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lake_logWarning(lean_object* v_m_1105_, lean_object* v_inst_1106_, lean_object* v_message_1107_){
_start:
{
uint8_t v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1108_ = 2;
v___x_1109_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1109_, 0, v_message_1107_);
lean_ctor_set_uint8(v___x_1109_, sizeof(void*)*1, v___x_1108_);
v___x_1110_ = lean_apply_1(v_inst_1106_, v___x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lake_logError___redArg(lean_object* v_inst_1111_, lean_object* v_message_1112_){
_start:
{
uint8_t v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = 3;
v___x_1114_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1114_, 0, v_message_1112_);
lean_ctor_set_uint8(v___x_1114_, sizeof(void*)*1, v___x_1113_);
v___x_1115_ = lean_apply_1(v_inst_1111_, v___x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lake_logError(lean_object* v_m_1116_, lean_object* v_inst_1117_, lean_object* v_message_1118_){
_start:
{
uint8_t v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1119_ = 3;
v___x_1120_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1120_, 0, v_message_1118_);
lean_ctor_set_uint8(v___x_1120_, sizeof(void*)*1, v___x_1119_);
v___x_1121_ = lean_apply_1(v_inst_1117_, v___x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lake_logSerialMessage___redArg(lean_object* v_msg_1122_, lean_object* v_inst_1123_, lean_object* v_inst_1124_){
_start:
{
lean_object* v_toBaseMessage_1125_; uint8_t v_isSilent_1126_; 
v_toBaseMessage_1125_ = lean_ctor_get(v_msg_1122_, 0);
v_isSilent_1126_ = lean_ctor_get_uint8(v_toBaseMessage_1125_, sizeof(void*)*5 + 2);
if (v_isSilent_1126_ == 0)
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_dec_ref(v_inst_1123_);
v___x_1127_ = l_Lake_LogEntry_ofSerialMessage(v_msg_1122_);
v___x_1128_ = lean_apply_1(v_inst_1124_, v___x_1127_);
return v___x_1128_;
}
else
{
lean_object* v_toApplicative_1129_; lean_object* v_toPure_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
lean_dec(v_inst_1124_);
lean_dec_ref(v_msg_1122_);
v_toApplicative_1129_ = lean_ctor_get(v_inst_1123_, 0);
lean_inc_ref(v_toApplicative_1129_);
lean_dec_ref(v_inst_1123_);
v_toPure_1130_ = lean_ctor_get(v_toApplicative_1129_, 1);
lean_inc(v_toPure_1130_);
lean_dec_ref(v_toApplicative_1129_);
v___x_1131_ = lean_box(0);
v___x_1132_ = lean_apply_2(v_toPure_1130_, lean_box(0), v___x_1131_);
return v___x_1132_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logSerialMessage(lean_object* v_m_1133_, lean_object* v_msg_1134_, lean_object* v_inst_1135_, lean_object* v_inst_1136_){
_start:
{
lean_object* v_toBaseMessage_1137_; uint8_t v_isSilent_1138_; 
v_toBaseMessage_1137_ = lean_ctor_get(v_msg_1134_, 0);
v_isSilent_1138_ = lean_ctor_get_uint8(v_toBaseMessage_1137_, sizeof(void*)*5 + 2);
if (v_isSilent_1138_ == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_dec_ref(v_inst_1135_);
v___x_1139_ = l_Lake_LogEntry_ofSerialMessage(v_msg_1134_);
v___x_1140_ = lean_apply_1(v_inst_1136_, v___x_1139_);
return v___x_1140_;
}
else
{
lean_object* v_toApplicative_1141_; lean_object* v_toPure_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_dec(v_inst_1136_);
lean_dec_ref(v_msg_1134_);
v_toApplicative_1141_ = lean_ctor_get(v_inst_1135_, 0);
lean_inc_ref(v_toApplicative_1141_);
lean_dec_ref(v_inst_1135_);
v_toPure_1142_ = lean_ctor_get(v_toApplicative_1141_, 1);
lean_inc(v_toPure_1142_);
lean_dec_ref(v_toApplicative_1141_);
v___x_1143_ = lean_box(0);
v___x_1144_ = lean_apply_2(v_toPure_1142_, lean_box(0), v___x_1143_);
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logMessage___redArg___lam__0(lean_object* v_inst_1145_, lean_object* v_____do__lift_1146_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_apply_1(v_inst_1145_, v_____do__lift_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lake_logMessage___redArg(lean_object* v_msg_1148_, lean_object* v_inst_1149_, lean_object* v_inst_1150_, lean_object* v_inst_1151_){
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
LEAN_EXPORT lean_object* l_Lake_logMessage(lean_object* v_m_1162_, lean_object* v_msg_1163_, lean_object* v_inst_1164_, lean_object* v_inst_1165_, lean_object* v_inst_1166_){
_start:
{
uint8_t v_isSilent_1167_; 
v_isSilent_1167_ = lean_ctor_get_uint8(v_msg_1163_, sizeof(void*)*5 + 2);
if (v_isSilent_1167_ == 0)
{
lean_object* v_toBind_1168_; lean_object* v___f_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v_toBind_1168_ = lean_ctor_get(v_inst_1164_, 1);
lean_inc(v_toBind_1168_);
lean_dec_ref(v_inst_1164_);
v___f_1169_ = lean_alloc_closure((void*)(l_Lake_logMessage___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1169_, 0, v_inst_1165_);
v___x_1170_ = lean_alloc_closure((void*)(l_Lake_LogEntry_ofMessage___boxed), 2, 1);
lean_closure_set(v___x_1170_, 0, v_msg_1163_);
v___x_1171_ = lean_apply_2(v_inst_1166_, lean_box(0), v___x_1170_);
v___x_1172_ = lean_apply_4(v_toBind_1168_, lean_box(0), lean_box(0), v___x_1171_, v___f_1169_);
return v___x_1172_;
}
else
{
lean_object* v_toApplicative_1173_; lean_object* v_toPure_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
lean_dec(v_inst_1166_);
lean_dec(v_inst_1165_);
lean_dec_ref(v_msg_1163_);
v_toApplicative_1173_ = lean_ctor_get(v_inst_1164_, 0);
lean_inc_ref(v_toApplicative_1173_);
lean_dec_ref(v_inst_1164_);
v_toPure_1174_ = lean_ctor_get(v_toApplicative_1173_, 1);
lean_inc(v_toPure_1174_);
lean_dec_ref(v_toApplicative_1173_);
v___x_1175_ = lean_box(0);
v___x_1176_ = lean_apply_2(v_toPure_1174_, lean_box(0), v___x_1175_);
return v___x_1176_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logToStream(lean_object* v_e_1177_, lean_object* v_out_1178_, uint8_t v_minLv_1179_, uint8_t v_useAnsi_1180_){
_start:
{
uint8_t v_level_1182_; uint8_t v___x_1183_; 
v_level_1182_ = lean_ctor_get_uint8(v_e_1177_, sizeof(void*)*1);
v___x_1183_ = l_Lake_instOrdLogLevel_ord(v_minLv_1179_, v_level_1182_);
if (v___x_1183_ == 2)
{
lean_object* v___x_1184_; 
lean_dec_ref(v_out_1178_);
v___x_1184_ = lean_box(0);
return v___x_1184_;
}
else
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = l_Lake_LogEntry_toString(v_e_1177_, v_useAnsi_1180_);
v___x_1186_ = l_IO_FS_Stream_putStrLn(v_out_1178_, v___x_1185_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref(v___x_1186_);
return v_a_1187_;
}
else
{
lean_object* v___x_1188_; 
lean_dec_ref(v___x_1186_);
v___x_1188_ = lean_box(0);
return v___x_1188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_logToStream___boxed(lean_object* v_e_1189_, lean_object* v_out_1190_, lean_object* v_minLv_1191_, lean_object* v_useAnsi_1192_, lean_object* v_a_1193_){
_start:
{
uint8_t v_minLv_boxed_1194_; uint8_t v_useAnsi_boxed_1195_; lean_object* v_res_1196_; 
v_minLv_boxed_1194_ = lean_unbox(v_minLv_1191_);
v_useAnsi_boxed_1195_ = lean_unbox(v_useAnsi_1192_);
v_res_1196_ = l_Lake_logToStream(v_e_1189_, v_out_1190_, v_minLv_boxed_1194_, v_useAnsi_boxed_1195_);
lean_dec_ref(v_e_1189_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___redArg___lam__0(lean_object* v_inst_1197_, lean_object* v_x_1198_){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = lean_box(0);
v___x_1200_ = lean_apply_2(v_inst_1197_, lean_box(0), v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___redArg___lam__0___boxed(lean_object* v_inst_1201_, lean_object* v_x_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lake_MonadLog_nop___redArg___lam__0(v_inst_1201_, v_x_1202_);
lean_dec_ref(v_x_1202_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___redArg(lean_object* v_inst_1204_){
_start:
{
lean_object* v___f_1205_; 
v___f_1205_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1205_, 0, v_inst_1204_);
return v___f_1205_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop(lean_object* v_m_1206_, lean_object* v_inst_1207_){
_start:
{
lean_object* v___f_1208_; 
v___f_1208_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1208_, 0, v_inst_1207_);
return v___f_1208_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instInhabitedOfPure___redArg(lean_object* v_inst_1209_){
_start:
{
lean_object* v___f_1210_; 
v___f_1210_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1210_, 0, v_inst_1209_);
return v___f_1210_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instInhabitedOfPure(lean_object* v_m_1211_, lean_object* v_inst_1212_){
_start:
{
lean_object* v___f_1213_; 
v___f_1213_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1213_, 0, v_inst_1212_);
return v___f_1213_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift___redArg___lam__0(lean_object* v_self_1214_, lean_object* v_inst_1215_, lean_object* v_e_1216_){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = lean_apply_1(v_self_1214_, v_e_1216_);
v___x_1218_ = lean_apply_2(v_inst_1215_, lean_box(0), v___x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift___redArg(lean_object* v_inst_1219_, lean_object* v_self_1220_){
_start:
{
lean_object* v___f_1221_; 
v___f_1221_ = lean_alloc_closure((void*)(l_Lake_MonadLog_lift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1221_, 0, v_self_1220_);
lean_closure_set(v___f_1221_, 1, v_inst_1219_);
return v___f_1221_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift(lean_object* v_m_1222_, lean_object* v_n_1223_, lean_object* v_inst_1224_, lean_object* v_self_1225_){
_start:
{
lean_object* v___f_1226_; 
v___f_1226_ = lean_alloc_closure((void*)(l_Lake_MonadLog_lift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1226_, 0, v_self_1225_);
lean_closure_set(v___f_1226_, 1, v_inst_1224_);
return v___f_1226_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift___redArg___lam__0(lean_object* v_methods_1227_, lean_object* v_inst_1228_, lean_object* v_e_1229_){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = lean_apply_1(v_methods_1227_, v_e_1229_);
v___x_1231_ = lean_apply_2(v_inst_1228_, lean_box(0), v___x_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift___redArg(lean_object* v_inst_1232_, lean_object* v_methods_1233_){
_start:
{
lean_object* v___f_1234_; 
v___f_1234_ = lean_alloc_closure((void*)(l_Lake_MonadLog_instOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1234_, 0, v_methods_1233_);
lean_closure_set(v___f_1234_, 1, v_inst_1232_);
return v___f_1234_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift(lean_object* v_m_1235_, lean_object* v_n_1236_, lean_object* v_inst_1237_, lean_object* v_methods_1238_){
_start:
{
lean_object* v___f_1239_; 
v___f_1239_ = lean_alloc_closure((void*)(l_Lake_MonadLog_instOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1239_, 0, v_methods_1238_);
lean_closure_set(v___f_1239_, 1, v_inst_1237_);
return v___f_1239_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg___lam__0(lean_object* v_out_1240_, uint8_t v_minLv_1241_, uint8_t v_useAnsi_1242_, lean_object* v_inst_1243_, lean_object* v_e_1244_){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1245_ = lean_box(v_minLv_1241_);
v___x_1246_ = lean_box(v_useAnsi_1242_);
v___x_1247_ = lean_alloc_closure((void*)(l_Lake_logToStream___boxed), 5, 4);
lean_closure_set(v___x_1247_, 0, v_e_1244_);
lean_closure_set(v___x_1247_, 1, v_out_1240_);
lean_closure_set(v___x_1247_, 2, v___x_1245_);
lean_closure_set(v___x_1247_, 3, v___x_1246_);
v___x_1248_ = lean_apply_2(v_inst_1243_, lean_box(0), v___x_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg___lam__0___boxed(lean_object* v_out_1249_, lean_object* v_minLv_1250_, lean_object* v_useAnsi_1251_, lean_object* v_inst_1252_, lean_object* v_e_1253_){
_start:
{
uint8_t v_minLv_boxed_1254_; uint8_t v_useAnsi_boxed_1255_; lean_object* v_res_1256_; 
v_minLv_boxed_1254_ = lean_unbox(v_minLv_1250_);
v_useAnsi_boxed_1255_ = lean_unbox(v_useAnsi_1251_);
v_res_1256_ = l_Lake_MonadLog_stream___redArg___lam__0(v_out_1249_, v_minLv_boxed_1254_, v_useAnsi_boxed_1255_, v_inst_1252_, v_e_1253_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg(lean_object* v_inst_1257_, lean_object* v_out_1258_, uint8_t v_minLv_1259_, uint8_t v_useAnsi_1260_){
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
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg___boxed(lean_object* v_inst_1264_, lean_object* v_out_1265_, lean_object* v_minLv_1266_, lean_object* v_useAnsi_1267_){
_start:
{
uint8_t v_minLv_boxed_1268_; uint8_t v_useAnsi_boxed_1269_; lean_object* v_res_1270_; 
v_minLv_boxed_1268_ = lean_unbox(v_minLv_1266_);
v_useAnsi_boxed_1269_ = lean_unbox(v_useAnsi_1267_);
v_res_1270_ = l_Lake_MonadLog_stream___redArg(v_inst_1264_, v_out_1265_, v_minLv_boxed_1268_, v_useAnsi_boxed_1269_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream(lean_object* v_m_1271_, lean_object* v_inst_1272_, lean_object* v_out_1273_, uint8_t v_minLv_1274_, uint8_t v_useAnsi_1275_){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___f_1278_; 
v___x_1276_ = lean_box(v_minLv_1274_);
v___x_1277_ = lean_box(v_useAnsi_1275_);
v___f_1278_ = lean_alloc_closure((void*)(l_Lake_MonadLog_stream___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1278_, 0, v_out_1273_);
lean_closure_set(v___f_1278_, 1, v___x_1276_);
lean_closure_set(v___f_1278_, 2, v___x_1277_);
lean_closure_set(v___f_1278_, 3, v_inst_1272_);
return v___f_1278_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___boxed(lean_object* v_m_1279_, lean_object* v_inst_1280_, lean_object* v_out_1281_, lean_object* v_minLv_1282_, lean_object* v_useAnsi_1283_){
_start:
{
uint8_t v_minLv_boxed_1284_; uint8_t v_useAnsi_boxed_1285_; lean_object* v_res_1286_; 
v_minLv_boxed_1284_ = lean_unbox(v_minLv_1282_);
v_useAnsi_boxed_1285_ = lean_unbox(v_useAnsi_1283_);
v_res_1286_ = l_Lake_MonadLog_stream(v_m_1279_, v_inst_1280_, v_out_1281_, v_minLv_boxed_1284_, v_useAnsi_boxed_1285_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_error___redArg___lam__0(lean_object* v_failure_1287_, lean_object* v_x_1288_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = lean_apply_1(v_failure_1287_, lean_box(0));
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_error___redArg(lean_object* v_inst_1290_, lean_object* v_inst_1291_, lean_object* v_msg_1292_){
_start:
{
lean_object* v_toApplicative_1293_; lean_object* v_failure_1294_; lean_object* v_toSeqRight_1295_; lean_object* v___f_1296_; uint8_t v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v_toApplicative_1293_ = lean_ctor_get(v_inst_1290_, 0);
lean_inc_ref(v_toApplicative_1293_);
v_failure_1294_ = lean_ctor_get(v_inst_1290_, 1);
lean_inc(v_failure_1294_);
lean_dec_ref(v_inst_1290_);
v_toSeqRight_1295_ = lean_ctor_get(v_toApplicative_1293_, 4);
lean_inc(v_toSeqRight_1295_);
lean_dec_ref(v_toApplicative_1293_);
v___f_1296_ = lean_alloc_closure((void*)(l_Lake_MonadLog_error___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1296_, 0, v_failure_1294_);
v___x_1297_ = 3;
v___x_1298_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1298_, 0, v_msg_1292_);
lean_ctor_set_uint8(v___x_1298_, sizeof(void*)*1, v___x_1297_);
v___x_1299_ = lean_apply_1(v_inst_1291_, v___x_1298_);
v___x_1300_ = lean_apply_4(v_toSeqRight_1295_, lean_box(0), lean_box(0), v___x_1299_, v___f_1296_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_error(lean_object* v_m_1301_, lean_object* v_00_u03b1_1302_, lean_object* v_inst_1303_, lean_object* v_inst_1304_, lean_object* v_msg_1305_){
_start:
{
lean_object* v_toApplicative_1306_; lean_object* v_failure_1307_; lean_object* v_toSeqRight_1308_; lean_object* v___f_1309_; uint8_t v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v_toApplicative_1306_ = lean_ctor_get(v_inst_1303_, 0);
lean_inc_ref(v_toApplicative_1306_);
v_failure_1307_ = lean_ctor_get(v_inst_1303_, 1);
lean_inc(v_failure_1307_);
lean_dec_ref(v_inst_1303_);
v_toSeqRight_1308_ = lean_ctor_get(v_toApplicative_1306_, 4);
lean_inc(v_toSeqRight_1308_);
lean_dec_ref(v_toApplicative_1306_);
v___f_1309_ = lean_alloc_closure((void*)(l_Lake_MonadLog_error___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1309_, 0, v_failure_1307_);
v___x_1310_ = 3;
v___x_1311_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1311_, 0, v_msg_1305_);
lean_ctor_set_uint8(v___x_1311_, sizeof(void*)*1, v___x_1310_);
v___x_1312_ = lean_apply_1(v_inst_1304_, v___x_1311_);
v___x_1313_ = lean_apply_4(v_toSeqRight_1308_, lean_box(0), lean_box(0), v___x_1312_, v___f_1309_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logEntry(lean_object* v_self_1314_, lean_object* v_e_1315_, uint8_t v_minLv_1316_, uint8_t v_ansiMode_1317_){
_start:
{
lean_object* v___x_1319_; uint8_t v___x_1320_; lean_object* v___x_1321_; 
v___x_1319_ = l_Lake_OutStream_get(v_self_1314_);
lean_inc_ref(v___x_1319_);
v___x_1320_ = l_Lake_AnsiMode_isEnabled(v___x_1319_, v_ansiMode_1317_);
v___x_1321_ = l_Lake_logToStream(v_e_1315_, v___x_1319_, v_minLv_1316_, v___x_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logEntry___boxed(lean_object* v_self_1322_, lean_object* v_e_1323_, lean_object* v_minLv_1324_, lean_object* v_ansiMode_1325_, lean_object* v_a_1326_){
_start:
{
uint8_t v_minLv_boxed_1327_; uint8_t v_ansiMode_boxed_1328_; lean_object* v_res_1329_; 
v_minLv_boxed_1327_ = lean_unbox(v_minLv_1324_);
v_ansiMode_boxed_1328_ = lean_unbox(v_ansiMode_1325_);
v_res_1329_ = l_Lake_OutStream_logEntry(v_self_1322_, v_e_1323_, v_minLv_boxed_1327_, v_ansiMode_boxed_1328_);
lean_dec_ref(v_e_1323_);
lean_dec(v_self_1322_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg___lam__0(lean_object* v_out_1330_, uint8_t v_minLv_1331_, uint8_t v_ansiMode_1332_, lean_object* v_inst_1333_, lean_object* v_e_1334_){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1335_ = lean_box(v_minLv_1331_);
v___x_1336_ = lean_box(v_ansiMode_1332_);
v___x_1337_ = lean_alloc_closure((void*)(l_Lake_OutStream_logEntry___boxed), 5, 4);
lean_closure_set(v___x_1337_, 0, v_out_1330_);
lean_closure_set(v___x_1337_, 1, v_e_1334_);
lean_closure_set(v___x_1337_, 2, v___x_1335_);
lean_closure_set(v___x_1337_, 3, v___x_1336_);
v___x_1338_ = lean_apply_2(v_inst_1333_, lean_box(0), v___x_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg___lam__0___boxed(lean_object* v_out_1339_, lean_object* v_minLv_1340_, lean_object* v_ansiMode_1341_, lean_object* v_inst_1342_, lean_object* v_e_1343_){
_start:
{
uint8_t v_minLv_boxed_1344_; uint8_t v_ansiMode_boxed_1345_; lean_object* v_res_1346_; 
v_minLv_boxed_1344_ = lean_unbox(v_minLv_1340_);
v_ansiMode_boxed_1345_ = lean_unbox(v_ansiMode_1341_);
v_res_1346_ = l_Lake_OutStream_logger___redArg___lam__0(v_out_1339_, v_minLv_boxed_1344_, v_ansiMode_boxed_1345_, v_inst_1342_, v_e_1343_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg(lean_object* v_inst_1347_, lean_object* v_out_1348_, uint8_t v_minLv_1349_, uint8_t v_ansiMode_1350_){
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
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg___boxed(lean_object* v_inst_1354_, lean_object* v_out_1355_, lean_object* v_minLv_1356_, lean_object* v_ansiMode_1357_){
_start:
{
uint8_t v_minLv_boxed_1358_; uint8_t v_ansiMode_boxed_1359_; lean_object* v_res_1360_; 
v_minLv_boxed_1358_ = lean_unbox(v_minLv_1356_);
v_ansiMode_boxed_1359_ = lean_unbox(v_ansiMode_1357_);
v_res_1360_ = l_Lake_OutStream_logger___redArg(v_inst_1354_, v_out_1355_, v_minLv_boxed_1358_, v_ansiMode_boxed_1359_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger(lean_object* v_m_1361_, lean_object* v_inst_1362_, lean_object* v_out_1363_, uint8_t v_minLv_1364_, uint8_t v_ansiMode_1365_){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___f_1368_; 
v___x_1366_ = lean_box(v_minLv_1364_);
v___x_1367_ = lean_box(v_ansiMode_1365_);
v___f_1368_ = lean_alloc_closure((void*)(l_Lake_OutStream_logger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1368_, 0, v_out_1363_);
lean_closure_set(v___f_1368_, 1, v___x_1366_);
lean_closure_set(v___f_1368_, 2, v___x_1367_);
lean_closure_set(v___f_1368_, 3, v_inst_1362_);
return v___f_1368_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___boxed(lean_object* v_m_1369_, lean_object* v_inst_1370_, lean_object* v_out_1371_, lean_object* v_minLv_1372_, lean_object* v_ansiMode_1373_){
_start:
{
uint8_t v_minLv_boxed_1374_; uint8_t v_ansiMode_boxed_1375_; lean_object* v_res_1376_; 
v_minLv_boxed_1374_ = lean_unbox(v_minLv_1372_);
v_ansiMode_boxed_1375_ = lean_unbox(v_ansiMode_1373_);
v_res_1376_ = l_Lake_OutStream_logger(v_m_1369_, v_inst_1370_, v_out_1371_, v_minLv_boxed_1374_, v_ansiMode_boxed_1375_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg___lam__0(lean_object* v___x_1377_, uint8_t v_minLv_1378_, uint8_t v_ansiMode_1379_, lean_object* v_inst_1380_, lean_object* v_e_1381_){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1382_ = lean_box(v_minLv_1378_);
v___x_1383_ = lean_box(v_ansiMode_1379_);
v___x_1384_ = lean_alloc_closure((void*)(l_Lake_OutStream_logEntry___boxed), 5, 4);
lean_closure_set(v___x_1384_, 0, v___x_1377_);
lean_closure_set(v___x_1384_, 1, v_e_1381_);
lean_closure_set(v___x_1384_, 2, v___x_1382_);
lean_closure_set(v___x_1384_, 3, v___x_1383_);
v___x_1385_ = lean_apply_2(v_inst_1380_, lean_box(0), v___x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg___lam__0___boxed(lean_object* v___x_1386_, lean_object* v_minLv_1387_, lean_object* v_ansiMode_1388_, lean_object* v_inst_1389_, lean_object* v_e_1390_){
_start:
{
uint8_t v_minLv_boxed_1391_; uint8_t v_ansiMode_boxed_1392_; lean_object* v_res_1393_; 
v_minLv_boxed_1391_ = lean_unbox(v_minLv_1387_);
v_ansiMode_boxed_1392_ = lean_unbox(v_ansiMode_1388_);
v_res_1393_ = l_Lake_MonadLog_stdout___redArg___lam__0(v___x_1386_, v_minLv_boxed_1391_, v_ansiMode_boxed_1392_, v_inst_1389_, v_e_1390_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg(lean_object* v_inst_1394_, uint8_t v_minLv_1395_, uint8_t v_ansiMode_1396_){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___f_1400_; 
v___x_1397_ = lean_box(0);
v___x_1398_ = lean_box(v_minLv_1395_);
v___x_1399_ = lean_box(v_ansiMode_1396_);
v___f_1400_ = lean_alloc_closure((void*)(l_Lake_MonadLog_stdout___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1400_, 0, v___x_1397_);
lean_closure_set(v___f_1400_, 1, v___x_1398_);
lean_closure_set(v___f_1400_, 2, v___x_1399_);
lean_closure_set(v___f_1400_, 3, v_inst_1394_);
return v___f_1400_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg___boxed(lean_object* v_inst_1401_, lean_object* v_minLv_1402_, lean_object* v_ansiMode_1403_){
_start:
{
uint8_t v_minLv_boxed_1404_; uint8_t v_ansiMode_boxed_1405_; lean_object* v_res_1406_; 
v_minLv_boxed_1404_ = lean_unbox(v_minLv_1402_);
v_ansiMode_boxed_1405_ = lean_unbox(v_ansiMode_1403_);
v_res_1406_ = l_Lake_MonadLog_stdout___redArg(v_inst_1401_, v_minLv_boxed_1404_, v_ansiMode_boxed_1405_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout(lean_object* v_m_1407_, lean_object* v_inst_1408_, uint8_t v_minLv_1409_, uint8_t v_ansiMode_1410_){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___f_1414_; 
v___x_1411_ = lean_box(0);
v___x_1412_ = lean_box(v_minLv_1409_);
v___x_1413_ = lean_box(v_ansiMode_1410_);
v___f_1414_ = lean_alloc_closure((void*)(l_Lake_MonadLog_stdout___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1414_, 0, v___x_1411_);
lean_closure_set(v___f_1414_, 1, v___x_1412_);
lean_closure_set(v___f_1414_, 2, v___x_1413_);
lean_closure_set(v___f_1414_, 3, v_inst_1408_);
return v___f_1414_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___boxed(lean_object* v_m_1415_, lean_object* v_inst_1416_, lean_object* v_minLv_1417_, lean_object* v_ansiMode_1418_){
_start:
{
uint8_t v_minLv_boxed_1419_; uint8_t v_ansiMode_boxed_1420_; lean_object* v_res_1421_; 
v_minLv_boxed_1419_ = lean_unbox(v_minLv_1417_);
v_ansiMode_boxed_1420_ = lean_unbox(v_ansiMode_1418_);
v_res_1421_ = l_Lake_MonadLog_stdout(v_m_1415_, v_inst_1416_, v_minLv_boxed_1419_, v_ansiMode_boxed_1420_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___redArg(lean_object* v_inst_1422_, uint8_t v_minLv_1423_, uint8_t v_ansiMode_1424_){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___f_1428_; 
v___x_1425_ = lean_box(1);
v___x_1426_ = lean_box(v_minLv_1423_);
v___x_1427_ = lean_box(v_ansiMode_1424_);
v___f_1428_ = lean_alloc_closure((void*)(l_Lake_MonadLog_stdout___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1428_, 0, v___x_1425_);
lean_closure_set(v___f_1428_, 1, v___x_1426_);
lean_closure_set(v___f_1428_, 2, v___x_1427_);
lean_closure_set(v___f_1428_, 3, v_inst_1422_);
return v___f_1428_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___redArg___boxed(lean_object* v_inst_1429_, lean_object* v_minLv_1430_, lean_object* v_ansiMode_1431_){
_start:
{
uint8_t v_minLv_boxed_1432_; uint8_t v_ansiMode_boxed_1433_; lean_object* v_res_1434_; 
v_minLv_boxed_1432_ = lean_unbox(v_minLv_1430_);
v_ansiMode_boxed_1433_ = lean_unbox(v_ansiMode_1431_);
v_res_1434_ = l_Lake_MonadLog_stderr___redArg(v_inst_1429_, v_minLv_boxed_1432_, v_ansiMode_boxed_1433_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr(lean_object* v_m_1435_, lean_object* v_inst_1436_, uint8_t v_minLv_1437_, uint8_t v_ansiMode_1438_){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___f_1442_; 
v___x_1439_ = lean_box(1);
v___x_1440_ = lean_box(v_minLv_1437_);
v___x_1441_ = lean_box(v_ansiMode_1438_);
v___f_1442_ = lean_alloc_closure((void*)(l_Lake_MonadLog_stdout___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1442_, 0, v___x_1439_);
lean_closure_set(v___f_1442_, 1, v___x_1440_);
lean_closure_set(v___f_1442_, 2, v___x_1441_);
lean_closure_set(v___f_1442_, 3, v_inst_1436_);
return v___f_1442_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___boxed(lean_object* v_m_1443_, lean_object* v_inst_1444_, lean_object* v_minLv_1445_, lean_object* v_ansiMode_1446_){
_start:
{
uint8_t v_minLv_boxed_1447_; uint8_t v_ansiMode_boxed_1448_; lean_object* v_res_1449_; 
v_minLv_boxed_1447_ = lean_unbox(v_minLv_1445_);
v_ansiMode_boxed_1448_ = lean_unbox(v_ansiMode_1446_);
v_res_1449_ = l_Lake_MonadLog_stderr(v_m_1443_, v_inst_1444_, v_minLv_boxed_1447_, v_ansiMode_boxed_1448_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg___lam__0(lean_object* v_val_1450_, uint8_t v_minLv_1451_, uint8_t v_val_1452_, lean_object* v_inst_1453_, lean_object* v_e_1454_){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1455_ = lean_box(v_minLv_1451_);
v___x_1456_ = lean_box(v_val_1452_);
v___x_1457_ = lean_alloc_closure((void*)(l_Lake_logToStream___boxed), 5, 4);
lean_closure_set(v___x_1457_, 0, v_e_1454_);
lean_closure_set(v___x_1457_, 1, v_val_1450_);
lean_closure_set(v___x_1457_, 2, v___x_1455_);
lean_closure_set(v___x_1457_, 3, v___x_1456_);
v___x_1458_ = lean_apply_2(v_inst_1453_, lean_box(0), v___x_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg___lam__0___boxed(lean_object* v_val_1459_, lean_object* v_minLv_1460_, lean_object* v_val_1461_, lean_object* v_inst_1462_, lean_object* v_e_1463_){
_start:
{
uint8_t v_minLv_boxed_1464_; uint8_t v_val_105__boxed_1465_; lean_object* v_res_1466_; 
v_minLv_boxed_1464_ = lean_unbox(v_minLv_1460_);
v_val_105__boxed_1465_ = lean_unbox(v_val_1461_);
v_res_1466_ = l_Lake_OutStream_getLogger___redArg___lam__0(v_val_1459_, v_minLv_boxed_1464_, v_val_105__boxed_1465_, v_inst_1462_, v_e_1463_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg(lean_object* v_inst_1467_, lean_object* v_out_1468_, uint8_t v_minLv_1469_, uint8_t v_ansiMode_1470_){
_start:
{
lean_object* v___x_1472_; uint8_t v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___f_1476_; 
v___x_1472_ = l_Lake_OutStream_get(v_out_1468_);
lean_inc_ref(v___x_1472_);
v___x_1473_ = l_Lake_AnsiMode_isEnabled(v___x_1472_, v_ansiMode_1470_);
v___x_1474_ = lean_box(v_minLv_1469_);
v___x_1475_ = lean_box(v___x_1473_);
v___f_1476_ = lean_alloc_closure((void*)(l_Lake_OutStream_getLogger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1476_, 0, v___x_1472_);
lean_closure_set(v___f_1476_, 1, v___x_1474_);
lean_closure_set(v___f_1476_, 2, v___x_1475_);
lean_closure_set(v___f_1476_, 3, v_inst_1467_);
return v___f_1476_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg___boxed(lean_object* v_inst_1477_, lean_object* v_out_1478_, lean_object* v_minLv_1479_, lean_object* v_ansiMode_1480_, lean_object* v_a_1481_){
_start:
{
uint8_t v_minLv_boxed_1482_; uint8_t v_ansiMode_boxed_1483_; lean_object* v_res_1484_; 
v_minLv_boxed_1482_ = lean_unbox(v_minLv_1479_);
v_ansiMode_boxed_1483_ = lean_unbox(v_ansiMode_1480_);
v_res_1484_ = l_Lake_OutStream_getLogger___redArg(v_inst_1477_, v_out_1478_, v_minLv_boxed_1482_, v_ansiMode_boxed_1483_);
lean_dec(v_out_1478_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger(lean_object* v_m_1485_, lean_object* v_inst_1486_, lean_object* v_out_1487_, uint8_t v_minLv_1488_, uint8_t v_ansiMode_1489_){
_start:
{
lean_object* v___x_1491_; uint8_t v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___f_1495_; 
v___x_1491_ = l_Lake_OutStream_get(v_out_1487_);
lean_inc_ref(v___x_1491_);
v___x_1492_ = l_Lake_AnsiMode_isEnabled(v___x_1491_, v_ansiMode_1489_);
v___x_1493_ = lean_box(v_minLv_1488_);
v___x_1494_ = lean_box(v___x_1492_);
v___f_1495_ = lean_alloc_closure((void*)(l_Lake_OutStream_getLogger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1495_, 0, v___x_1491_);
lean_closure_set(v___f_1495_, 1, v___x_1493_);
lean_closure_set(v___f_1495_, 2, v___x_1494_);
lean_closure_set(v___f_1495_, 3, v_inst_1486_);
return v___f_1495_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___boxed(lean_object* v_m_1496_, lean_object* v_inst_1497_, lean_object* v_out_1498_, lean_object* v_minLv_1499_, lean_object* v_ansiMode_1500_, lean_object* v_a_1501_){
_start:
{
uint8_t v_minLv_boxed_1502_; uint8_t v_ansiMode_boxed_1503_; lean_object* v_res_1504_; 
v_minLv_boxed_1502_ = lean_unbox(v_minLv_1499_);
v_ansiMode_boxed_1503_ = lean_unbox(v_ansiMode_1500_);
v_res_1504_ = l_Lake_OutStream_getLogger(v_m_1496_, v_inst_1497_, v_out_1498_, v_minLv_boxed_1502_, v_ansiMode_boxed_1503_);
lean_dec(v_out_1498_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0(lean_object* v_inst_1505_, lean_object* v_inst_1506_, lean_object* v_x_1507_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = lean_apply_2(v_inst_1505_, lean_box(0), v_inst_1506_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0___boxed(lean_object* v_inst_1509_, lean_object* v_inst_1510_, lean_object* v_x_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0(v_inst_1509_, v_inst_1510_, v_x_1511_);
lean_dec(v_x_1511_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___redArg(lean_object* v_inst_1513_, lean_object* v_inst_1514_){
_start:
{
lean_object* v___f_1515_; 
v___f_1515_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1515_, 0, v_inst_1513_);
lean_closure_set(v___f_1515_, 1, v_inst_1514_);
return v___f_1515_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure(lean_object* v_n_1516_, lean_object* v_00_u03b1_1517_, lean_object* v_m_1518_, lean_object* v_inst_1519_, lean_object* v_inst_1520_){
_start:
{
lean_object* v___f_1521_; 
v___f_1521_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1521_, 0, v_inst_1519_);
lean_closure_set(v___f_1521_, 1, v_inst_1520_);
return v___f_1521_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__0(lean_object* v_e_1522_, lean_object* v_inst_1523_, lean_object* v_a_1524_){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = lean_apply_1(v_a_1524_, v_e_1522_);
v___x_1526_ = lean_apply_2(v_inst_1523_, lean_box(0), v___x_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1(lean_object* v_inst_1527_, lean_object* v_inst_1528_, lean_object* v_e_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_toApplicative_1531_; lean_object* v_toBind_1532_; lean_object* v_toPure_1533_; lean_object* v___f_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v_toApplicative_1531_ = lean_ctor_get(v_inst_1527_, 0);
lean_inc_ref(v_toApplicative_1531_);
v_toBind_1532_ = lean_ctor_get(v_inst_1527_, 1);
lean_inc(v_toBind_1532_);
lean_dec_ref(v_inst_1527_);
v_toPure_1533_ = lean_ctor_get(v_toApplicative_1531_, 1);
lean_inc(v_toPure_1533_);
lean_dec_ref(v_toApplicative_1531_);
v___f_1534_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1534_, 0, v_e_1529_);
lean_closure_set(v___f_1534_, 1, v_inst_1528_);
lean_inc(v___y_1530_);
v___x_1535_ = lean_apply_2(v_toPure_1533_, lean_box(0), v___y_1530_);
v___x_1536_ = lean_apply_4(v_toBind_1532_, lean_box(0), lean_box(0), v___x_1535_, v___f_1534_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1___boxed(lean_object* v_inst_1537_, lean_object* v_inst_1538_, lean_object* v_e_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1(v_inst_1537_, v_inst_1538_, v_e_1539_, v___y_1540_);
lean_dec(v___y_1540_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg(lean_object* v_inst_1542_, lean_object* v_inst_1543_){
_start:
{
lean_object* v___f_1544_; 
v___f_1544_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1544_, 0, v_inst_1542_);
lean_closure_set(v___f_1544_, 1, v_inst_1543_);
return v___f_1544_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT(lean_object* v_n_1545_, lean_object* v_m_1546_, lean_object* v_inst_1547_, lean_object* v_inst_1548_){
_start:
{
lean_object* v___f_1549_; 
v___f_1549_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1549_, 0, v_inst_1547_);
lean_closure_set(v___f_1549_, 1, v_inst_1548_);
return v___f_1549_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___redArg(lean_object* v_f_1550_, lean_object* v_self_1551_, lean_object* v_a_1552_){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
lean_inc(v_a_1552_);
v___x_1553_ = lean_apply_1(v_f_1550_, v_a_1552_);
v___x_1554_ = lean_apply_1(v_self_1551_, v___x_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___redArg___boxed(lean_object* v_f_1555_, lean_object* v_self_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lake_MonadLogT_adaptMethods___redArg(v_f_1555_, v_self_1556_, v_a_1557_);
lean_dec(v_a_1557_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods(lean_object* v_n_1559_, lean_object* v_m_1560_, lean_object* v_m_x27_1561_, lean_object* v_00_u03b1_1562_, lean_object* v_inst_1563_, lean_object* v_f_1564_, lean_object* v_self_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
lean_inc(v_a_1566_);
v___x_1567_ = lean_apply_1(v_f_1564_, v_a_1566_);
v___x_1568_ = lean_apply_1(v_self_1565_, v___x_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___boxed(lean_object* v_n_1569_, lean_object* v_m_1570_, lean_object* v_m_x27_1571_, lean_object* v_00_u03b1_1572_, lean_object* v_inst_1573_, lean_object* v_f_1574_, lean_object* v_self_1575_, lean_object* v_a_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l_Lake_MonadLogT_adaptMethods(v_n_1569_, v_m_1570_, v_m_x27_1571_, v_00_u03b1_1572_, v_inst_1573_, v_f_1574_, v_self_1575_, v_a_1576_);
lean_dec(v_a_1576_);
lean_dec_ref(v_inst_1573_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog___redArg(lean_object* v_inst_1578_, lean_object* v_self_1579_){
_start:
{
lean_object* v___f_1580_; lean_object* v___x_1581_; 
v___f_1580_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1580_, 0, v_inst_1578_);
v___x_1581_ = lean_apply_1(v_self_1579_, v___f_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog(lean_object* v_m_1582_, lean_object* v_n_1583_, lean_object* v_00_u03b1_1584_, lean_object* v_inst_1585_, lean_object* v_self_1586_){
_start:
{
lean_object* v___f_1587_; lean_object* v___x_1588_; 
v___f_1587_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1587_, 0, v_inst_1585_);
v___x_1588_ = lean_apply_1(v_self_1586_, v___f_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonLog___lam__0(lean_object* v___x_1593_, lean_object* v_x_1594_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Array_toJson___redArg(v___x_1593_, v_x_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonLog___lam__0(lean_object* v___x_1599_, lean_object* v_x_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Array_fromJson_x3f___redArg(v___x_1599_, v_x_1600_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
v_a_1610_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1601_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1601_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
}
static lean_object* _init_l_Lake_Log_instInhabitedPos_default(void){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_unsigned_to_nat(0u);
return v___x_1621_;
}
}
static lean_object* _init_l_Lake_Log_instInhabitedPos(void){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_unsigned_to_nat(0u);
return v___x_1622_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_instDecidableEqPos_decEq(lean_object* v_x_1623_, lean_object* v_x_1624_){
_start:
{
uint8_t v___x_1625_; 
v___x_1625_ = lean_nat_dec_eq(v_x_1623_, v_x_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_instDecidableEqPos_decEq___boxed(lean_object* v_x_1626_, lean_object* v_x_1627_){
_start:
{
uint8_t v_res_1628_; lean_object* v_r_1629_; 
v_res_1628_ = l_Lake_Log_instDecidableEqPos_decEq(v_x_1626_, v_x_1627_);
lean_dec(v_x_1627_);
lean_dec(v_x_1626_);
v_r_1629_ = lean_box(v_res_1628_);
return v_r_1629_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_instDecidableEqPos(lean_object* v_x_1630_, lean_object* v_x_1631_){
_start:
{
uint8_t v___x_1632_; 
v___x_1632_ = lean_nat_dec_eq(v_x_1630_, v_x_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_instDecidableEqPos___boxed(lean_object* v_x_1633_, lean_object* v_x_1634_){
_start:
{
uint8_t v_res_1635_; lean_object* v_r_1636_; 
v_res_1635_ = l_Lake_Log_instDecidableEqPos(v_x_1633_, v_x_1634_);
lean_dec(v_x_1634_);
lean_dec(v_x_1633_);
v_r_1636_ = lean_box(v_res_1635_);
return v_r_1636_;
}
}
static lean_object* _init_l_Lake_instOfNatPos(void){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = lean_unsigned_to_nat(0u);
return v___x_1637_;
}
}
LEAN_EXPORT uint8_t l_Lake_instOrdPos___lam__0(lean_object* v_x1_1638_, lean_object* v_x2_1639_){
_start:
{
uint8_t v___x_1640_; 
v___x_1640_ = lean_nat_dec_lt(v_x1_1638_, v_x2_1639_);
if (v___x_1640_ == 0)
{
uint8_t v___x_1641_; 
v___x_1641_ = lean_nat_dec_eq(v_x1_1638_, v_x2_1639_);
if (v___x_1641_ == 0)
{
uint8_t v___x_1642_; 
v___x_1642_ = 2;
return v___x_1642_;
}
else
{
uint8_t v___x_1643_; 
v___x_1643_ = 1;
return v___x_1643_;
}
}
else
{
uint8_t v___x_1644_; 
v___x_1644_ = 0;
return v___x_1644_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instOrdPos___lam__0___boxed(lean_object* v_x1_1645_, lean_object* v_x2_1646_){
_start:
{
uint8_t v_res_1647_; lean_object* v_r_1648_; 
v_res_1647_ = l_Lake_instOrdPos___lam__0(v_x1_1645_, v_x2_1646_);
lean_dec(v_x2_1646_);
lean_dec(v_x1_1645_);
v_r_1648_ = lean_box(v_res_1647_);
return v_r_1648_;
}
}
static lean_object* _init_l_Lake_instLTPos(void){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = lean_box(0);
return v___x_1651_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableRelPosLt(lean_object* v_a_1652_, lean_object* v_b_1653_){
_start:
{
uint8_t v___x_1654_; 
v___x_1654_ = lean_nat_dec_lt(v_a_1652_, v_b_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableRelPosLt___boxed(lean_object* v_a_1655_, lean_object* v_b_1656_){
_start:
{
uint8_t v_res_1657_; lean_object* v_r_1658_; 
v_res_1657_ = l_Lake_instDecidableRelPosLt(v_a_1655_, v_b_1656_);
lean_dec(v_b_1656_);
lean_dec(v_a_1655_);
v_r_1658_ = lean_box(v_res_1657_);
return v_r_1658_;
}
}
static lean_object* _init_l_Lake_instLEPos(void){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = lean_box(0);
return v___x_1659_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableRelPosLe(lean_object* v_a_1660_, lean_object* v_b_1661_){
_start:
{
uint8_t v___x_1662_; 
v___x_1662_ = lean_nat_dec_le(v_a_1660_, v_b_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableRelPosLe___boxed(lean_object* v_a_1663_, lean_object* v_b_1664_){
_start:
{
uint8_t v_res_1665_; lean_object* v_r_1666_; 
v_res_1665_ = l_Lake_instDecidableRelPosLe(v_a_1663_, v_b_1664_);
lean_dec(v_b_1664_);
lean_dec(v_a_1663_);
v_r_1666_ = lean_box(v_res_1665_);
return v_r_1666_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMinPos___lam__0(lean_object* v_x_1667_, lean_object* v_y_1668_){
_start:
{
uint8_t v___x_1669_; 
v___x_1669_ = lean_nat_dec_le(v_x_1667_, v_y_1668_);
if (v___x_1669_ == 0)
{
lean_inc(v_y_1668_);
return v_y_1668_;
}
else
{
lean_inc(v_x_1667_);
return v_x_1667_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMinPos___lam__0___boxed(lean_object* v_x_1670_, lean_object* v_y_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lake_instMinPos___lam__0(v_x_1670_, v_y_1671_);
lean_dec(v_y_1671_);
lean_dec(v_x_1670_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxPos___lam__0(lean_object* v_x_1675_, lean_object* v_y_1676_){
_start:
{
uint8_t v___x_1677_; 
v___x_1677_ = lean_nat_dec_le(v_x_1675_, v_y_1676_);
if (v___x_1677_ == 0)
{
lean_inc(v_x_1675_);
return v_x_1675_;
}
else
{
lean_inc(v_y_1676_);
return v_y_1676_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxPos___lam__0___boxed(lean_object* v_x_1678_, lean_object* v_y_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lake_instMaxPos___lam__0(v_x_1678_, v_y_1679_);
lean_dec(v_y_1679_);
lean_dec(v_x_1678_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_size(lean_object* v_log_1687_){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = lean_array_get_size(v_log_1687_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_size___boxed(lean_object* v_log_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lake_Log_size(v_log_1689_);
lean_dec_ref(v_log_1689_);
return v_res_1690_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_isEmpty(lean_object* v_log_1691_){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; uint8_t v___x_1694_; 
v___x_1692_ = lean_array_get_size(v_log_1691_);
v___x_1693_ = lean_unsigned_to_nat(0u);
v___x_1694_ = lean_nat_dec_eq(v___x_1692_, v___x_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_isEmpty___boxed(lean_object* v_log_1695_){
_start:
{
uint8_t v_res_1696_; lean_object* v_r_1697_; 
v_res_1696_ = l_Lake_Log_isEmpty(v_log_1695_);
lean_dec_ref(v_log_1695_);
v_r_1697_ = lean_box(v_res_1696_);
return v_r_1697_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_hasEntries(lean_object* v_log_1698_){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; uint8_t v___x_1701_; 
v___x_1699_ = lean_array_get_size(v_log_1698_);
v___x_1700_ = lean_unsigned_to_nat(0u);
v___x_1701_ = lean_nat_dec_eq(v___x_1699_, v___x_1700_);
if (v___x_1701_ == 0)
{
uint8_t v___x_1702_; 
v___x_1702_ = 1;
return v___x_1702_;
}
else
{
uint8_t v___x_1703_; 
v___x_1703_ = 0;
return v___x_1703_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_hasEntries___boxed(lean_object* v_log_1704_){
_start:
{
uint8_t v_res_1705_; lean_object* v_r_1706_; 
v_res_1705_ = l_Lake_Log_hasEntries(v_log_1704_);
lean_dec_ref(v_log_1704_);
v_r_1706_ = lean_box(v_res_1705_);
return v_r_1706_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_endPos(lean_object* v_log_1707_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = lean_array_get_size(v_log_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_endPos___boxed(lean_object* v_log_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lake_Log_endPos(v_log_1709_);
lean_dec_ref(v_log_1709_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_push(lean_object* v_log_1711_, lean_object* v_e_1712_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = lean_array_push(v_log_1711_, v_e_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_append(lean_object* v_log_1714_, lean_object* v_o_1715_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l_Array_append___redArg(v_log_1714_, v_o_1715_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_append___boxed(lean_object* v_log_1717_, lean_object* v_o_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Lake_Log_append(v_log_1717_, v_o_1718_);
lean_dec_ref(v_o_1718_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_extract(lean_object* v_log_1722_, lean_object* v_start_1723_, lean_object* v_stop_1724_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Array_extract___redArg(v_log_1722_, v_start_1723_, v_stop_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_extract___boxed(lean_object* v_log_1726_, lean_object* v_start_1727_, lean_object* v_stop_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lake_Log_extract(v_log_1726_, v_start_1727_, v_stop_1728_);
lean_dec_ref(v_log_1726_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_dropFrom(lean_object* v_log_1730_, lean_object* v_pos_1731_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Array_shrink___redArg(v_log_1730_, v_pos_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_dropFrom___boxed(lean_object* v_log_1733_, lean_object* v_pos_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lake_Log_dropFrom(v_log_1733_, v_pos_1734_);
lean_dec(v_pos_1734_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_takeFrom(lean_object* v_log_1736_, lean_object* v_pos_1737_){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = lean_array_get_size(v_log_1736_);
v___x_1739_ = l_Array_extract___redArg(v_log_1736_, v_pos_1737_, v___x_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_takeFrom___boxed(lean_object* v_log_1740_, lean_object* v_pos_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lake_Log_takeFrom(v_log_1740_, v_pos_1741_);
lean_dec_ref(v_log_1740_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_split(lean_object* v_log_1743_, lean_object* v_pos_1744_){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
lean_inc_ref(v_log_1743_);
v___x_1745_ = l_Array_shrink___redArg(v_log_1743_, v_pos_1744_);
v___x_1746_ = lean_array_get_size(v_log_1743_);
v___x_1747_ = l_Array_extract___redArg(v_log_1743_, v_pos_1744_, v___x_1746_);
lean_dec_ref(v_log_1743_);
v___x_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1745_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(lean_object* v_as_1750_, size_t v_i_1751_, size_t v_stop_1752_, lean_object* v_b_1753_){
_start:
{
uint8_t v___x_1754_; 
v___x_1754_ = lean_usize_dec_eq(v_i_1751_, v_stop_1752_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; size_t v___x_1760_; size_t v___x_1761_; 
v___x_1755_ = lean_array_uget_borrowed(v_as_1750_, v_i_1751_);
v___x_1756_ = l_Lake_LogEntry_toString(v___x_1755_, v___x_1754_);
v___x_1757_ = lean_string_append(v_b_1753_, v___x_1756_);
lean_dec_ref(v___x_1756_);
v___x_1758_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0___closed__0));
v___x_1759_ = lean_string_append(v___x_1757_, v___x_1758_);
v___x_1760_ = ((size_t)1ULL);
v___x_1761_ = lean_usize_add(v_i_1751_, v___x_1760_);
v_i_1751_ = v___x_1761_;
v_b_1753_ = v___x_1759_;
goto _start;
}
else
{
return v_b_1753_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0___boxed(lean_object* v_as_1763_, lean_object* v_i_1764_, lean_object* v_stop_1765_, lean_object* v_b_1766_){
_start:
{
size_t v_i_boxed_1767_; size_t v_stop_boxed_1768_; lean_object* v_res_1769_; 
v_i_boxed_1767_ = lean_unbox_usize(v_i_1764_);
lean_dec(v_i_1764_);
v_stop_boxed_1768_ = lean_unbox_usize(v_stop_1765_);
lean_dec(v_stop_1765_);
v_res_1769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(v_as_1763_, v_i_boxed_1767_, v_stop_boxed_1768_, v_b_1766_);
lean_dec_ref(v_as_1763_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_toString(lean_object* v_log_1770_){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1771_ = ((lean_object*)(l_Lake_instInhabitedLogEntry_default___closed__0));
v___x_1772_ = lean_unsigned_to_nat(0u);
v___x_1773_ = lean_array_get_size(v_log_1770_);
v___x_1774_ = lean_nat_dec_lt(v___x_1772_, v___x_1773_);
if (v___x_1774_ == 0)
{
return v___x_1771_;
}
else
{
uint8_t v___x_1775_; 
v___x_1775_ = lean_nat_dec_le(v___x_1773_, v___x_1773_);
if (v___x_1775_ == 0)
{
if (v___x_1774_ == 0)
{
return v___x_1771_;
}
else
{
size_t v___x_1776_; size_t v___x_1777_; lean_object* v___x_1778_; 
v___x_1776_ = ((size_t)0ULL);
v___x_1777_ = lean_usize_of_nat(v___x_1773_);
v___x_1778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(v_log_1770_, v___x_1776_, v___x_1777_, v___x_1771_);
return v___x_1778_;
}
}
else
{
size_t v___x_1779_; size_t v___x_1780_; lean_object* v___x_1781_; 
v___x_1779_ = ((size_t)0ULL);
v___x_1780_ = lean_usize_of_nat(v___x_1773_);
v___x_1781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(v_log_1770_, v___x_1779_, v___x_1780_, v___x_1771_);
return v___x_1781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_toString___boxed(lean_object* v_log_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Lake_Log_toString(v_log_1782_);
lean_dec_ref(v_log_1782_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_replay___redArg___lam__0(lean_object* v_logger_1786_, lean_object* v_x_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = lean_apply_1(v_logger_1786_, v___y_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_replay___redArg(lean_object* v_inst_1790_, lean_object* v_logger_1791_, lean_object* v_log_1792_){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1793_ = lean_unsigned_to_nat(0u);
v___x_1794_ = lean_array_get_size(v_log_1792_);
v___x_1795_ = lean_box(0);
v___x_1796_ = lean_nat_dec_lt(v___x_1793_, v___x_1794_);
if (v___x_1796_ == 0)
{
lean_object* v_toApplicative_1797_; lean_object* v_toPure_1798_; lean_object* v___x_1799_; 
lean_dec_ref(v_log_1792_);
lean_dec(v_logger_1791_);
v_toApplicative_1797_ = lean_ctor_get(v_inst_1790_, 0);
lean_inc_ref(v_toApplicative_1797_);
lean_dec_ref(v_inst_1790_);
v_toPure_1798_ = lean_ctor_get(v_toApplicative_1797_, 1);
lean_inc(v_toPure_1798_);
lean_dec_ref(v_toApplicative_1797_);
v___x_1799_ = lean_apply_2(v_toPure_1798_, lean_box(0), v___x_1795_);
return v___x_1799_;
}
else
{
lean_object* v___f_1800_; uint8_t v___x_1801_; 
v___f_1800_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1800_, 0, v_logger_1791_);
v___x_1801_ = lean_nat_dec_le(v___x_1794_, v___x_1794_);
if (v___x_1801_ == 0)
{
if (v___x_1796_ == 0)
{
lean_object* v_toApplicative_1802_; lean_object* v_toPure_1803_; lean_object* v___x_1804_; 
lean_dec_ref(v___f_1800_);
lean_dec_ref(v_log_1792_);
v_toApplicative_1802_ = lean_ctor_get(v_inst_1790_, 0);
lean_inc_ref(v_toApplicative_1802_);
lean_dec_ref(v_inst_1790_);
v_toPure_1803_ = lean_ctor_get(v_toApplicative_1802_, 1);
lean_inc(v_toPure_1803_);
lean_dec_ref(v_toApplicative_1802_);
v___x_1804_ = lean_apply_2(v_toPure_1803_, lean_box(0), v___x_1795_);
return v___x_1804_;
}
else
{
size_t v___x_1805_; size_t v___x_1806_; lean_object* v___x_1807_; 
v___x_1805_ = ((size_t)0ULL);
v___x_1806_ = lean_usize_of_nat(v___x_1794_);
v___x_1807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1790_, v___f_1800_, v_log_1792_, v___x_1805_, v___x_1806_, v___x_1795_);
return v___x_1807_;
}
}
else
{
size_t v___x_1808_; size_t v___x_1809_; lean_object* v___x_1810_; 
v___x_1808_ = ((size_t)0ULL);
v___x_1809_ = lean_usize_of_nat(v___x_1794_);
v___x_1810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1790_, v___f_1800_, v_log_1792_, v___x_1808_, v___x_1809_, v___x_1795_);
return v___x_1810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_replay(lean_object* v_m_1811_, lean_object* v_inst_1812_, lean_object* v_logger_1813_, lean_object* v_log_1814_){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1815_ = lean_unsigned_to_nat(0u);
v___x_1816_ = lean_array_get_size(v_log_1814_);
v___x_1817_ = lean_box(0);
v___x_1818_ = lean_nat_dec_lt(v___x_1815_, v___x_1816_);
if (v___x_1818_ == 0)
{
lean_object* v_toApplicative_1819_; lean_object* v_toPure_1820_; lean_object* v___x_1821_; 
lean_dec_ref(v_log_1814_);
lean_dec(v_logger_1813_);
v_toApplicative_1819_ = lean_ctor_get(v_inst_1812_, 0);
lean_inc_ref(v_toApplicative_1819_);
lean_dec_ref(v_inst_1812_);
v_toPure_1820_ = lean_ctor_get(v_toApplicative_1819_, 1);
lean_inc(v_toPure_1820_);
lean_dec_ref(v_toApplicative_1819_);
v___x_1821_ = lean_apply_2(v_toPure_1820_, lean_box(0), v___x_1817_);
return v___x_1821_;
}
else
{
lean_object* v___f_1822_; uint8_t v___x_1823_; 
v___f_1822_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1822_, 0, v_logger_1813_);
v___x_1823_ = lean_nat_dec_le(v___x_1816_, v___x_1816_);
if (v___x_1823_ == 0)
{
if (v___x_1818_ == 0)
{
lean_object* v_toApplicative_1824_; lean_object* v_toPure_1825_; lean_object* v___x_1826_; 
lean_dec_ref(v___f_1822_);
lean_dec_ref(v_log_1814_);
v_toApplicative_1824_ = lean_ctor_get(v_inst_1812_, 0);
lean_inc_ref(v_toApplicative_1824_);
lean_dec_ref(v_inst_1812_);
v_toPure_1825_ = lean_ctor_get(v_toApplicative_1824_, 1);
lean_inc(v_toPure_1825_);
lean_dec_ref(v_toApplicative_1824_);
v___x_1826_ = lean_apply_2(v_toPure_1825_, lean_box(0), v___x_1817_);
return v___x_1826_;
}
else
{
size_t v___x_1827_; size_t v___x_1828_; lean_object* v___x_1829_; 
v___x_1827_ = ((size_t)0ULL);
v___x_1828_ = lean_usize_of_nat(v___x_1816_);
v___x_1829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1812_, v___f_1822_, v_log_1814_, v___x_1827_, v___x_1828_, v___x_1817_);
return v___x_1829_;
}
}
else
{
size_t v___x_1830_; size_t v___x_1831_; lean_object* v___x_1832_; 
v___x_1830_ = ((size_t)0ULL);
v___x_1831_ = lean_usize_of_nat(v___x_1816_);
v___x_1832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1812_, v___f_1822_, v_log_1814_, v___x_1830_, v___x_1831_, v___x_1817_);
return v___x_1832_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_filter___lam__0(lean_object* v_f_1833_, lean_object* v_x1_1834_, lean_object* v_x2_1835_){
_start:
{
lean_object* v___x_1836_; uint8_t v___x_1837_; 
lean_inc_ref(v_x2_1835_);
v___x_1836_ = lean_apply_1(v_f_1833_, v_x2_1835_);
v___x_1837_ = lean_unbox(v___x_1836_);
if (v___x_1837_ == 0)
{
lean_dec_ref(v_x2_1835_);
return v_x1_1834_;
}
else
{
lean_object* v___x_1838_; 
v___x_1838_ = lean_array_push(v_x1_1834_, v_x2_1835_);
return v___x_1838_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_filter(lean_object* v_f_1858_, lean_object* v_log_1859_){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; uint8_t v___x_1864_; 
v___x_1860_ = lean_unsigned_to_nat(0u);
v___x_1861_ = lean_array_get_size(v_log_1859_);
v___x_1862_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_1863_ = ((lean_object*)(l_Lake_Log_filter___closed__9));
v___x_1864_ = lean_nat_dec_lt(v___x_1860_, v___x_1861_);
if (v___x_1864_ == 0)
{
lean_dec_ref(v_log_1859_);
lean_dec_ref(v_f_1858_);
return v___x_1862_;
}
else
{
lean_object* v___f_1865_; uint8_t v___x_1866_; 
v___f_1865_ = lean_alloc_closure((void*)(l_Lake_Log_filter___lam__0), 3, 1);
lean_closure_set(v___f_1865_, 0, v_f_1858_);
v___x_1866_ = lean_nat_dec_le(v___x_1861_, v___x_1861_);
if (v___x_1866_ == 0)
{
if (v___x_1864_ == 0)
{
lean_dec_ref(v___f_1865_);
lean_dec_ref(v_log_1859_);
return v___x_1862_;
}
else
{
size_t v___x_1867_; size_t v___x_1868_; lean_object* v___x_1869_; 
v___x_1867_ = ((size_t)0ULL);
v___x_1868_ = lean_usize_of_nat(v___x_1861_);
v___x_1869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1863_, v___f_1865_, v_log_1859_, v___x_1867_, v___x_1868_, v___x_1862_);
return v___x_1869_;
}
}
else
{
size_t v___x_1870_; size_t v___x_1871_; lean_object* v___x_1872_; 
v___x_1870_ = ((size_t)0ULL);
v___x_1871_ = lean_usize_of_nat(v___x_1861_);
v___x_1872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1863_, v___f_1865_, v_log_1859_, v___x_1870_, v___x_1871_, v___x_1862_);
return v___x_1872_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_Log_any___lam__0(lean_object* v_f_1873_, lean_object* v_x_1874_){
_start:
{
lean_object* v___x_1875_; uint8_t v___x_1876_; 
v___x_1875_ = lean_apply_1(v_f_1873_, v_x_1874_);
v___x_1876_ = lean_unbox(v___x_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_any___lam__0___boxed(lean_object* v_f_1877_, lean_object* v_x_1878_){
_start:
{
uint8_t v_res_1879_; lean_object* v_r_1880_; 
v_res_1879_ = l_Lake_Log_any___lam__0(v_f_1877_, v_x_1878_);
v_r_1880_ = lean_box(v_res_1879_);
return v_r_1880_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_any(lean_object* v_f_1881_, lean_object* v_log_1882_){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; uint8_t v___x_1886_; 
v___x_1883_ = lean_unsigned_to_nat(0u);
v___x_1884_ = lean_array_get_size(v_log_1882_);
v___x_1885_ = ((lean_object*)(l_Lake_Log_filter___closed__9));
v___x_1886_ = lean_nat_dec_lt(v___x_1883_, v___x_1884_);
if (v___x_1886_ == 0)
{
lean_dec_ref(v_log_1882_);
lean_dec_ref(v_f_1881_);
return v___x_1886_;
}
else
{
if (v___x_1886_ == 0)
{
lean_dec_ref(v_log_1882_);
lean_dec_ref(v_f_1881_);
return v___x_1886_;
}
else
{
lean_object* v___f_1887_; size_t v___x_1888_; size_t v___x_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; 
v___f_1887_ = lean_alloc_closure((void*)(l_Lake_Log_any___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1887_, 0, v_f_1881_);
v___x_1888_ = ((size_t)0ULL);
v___x_1889_ = lean_usize_of_nat(v___x_1884_);
v___x_1890_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_1885_, v___f_1887_, v_log_1882_, v___x_1888_, v___x_1889_);
v___x_1891_ = lean_unbox(v___x_1890_);
lean_dec(v___x_1890_);
return v___x_1891_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_any___boxed(lean_object* v_f_1892_, lean_object* v_log_1893_){
_start:
{
uint8_t v_res_1894_; lean_object* v_r_1895_; 
v_res_1894_ = l_Lake_Log_any(v_f_1892_, v_log_1893_);
v_r_1895_ = lean_box(v_res_1894_);
return v_r_1895_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(lean_object* v_as_1896_, size_t v_i_1897_, size_t v_stop_1898_, uint8_t v_b_1899_){
_start:
{
uint8_t v___y_1901_; uint8_t v___x_1905_; 
v___x_1905_ = lean_usize_dec_eq(v_i_1897_, v_stop_1898_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; uint8_t v_level_1907_; uint8_t v___x_1908_; 
v___x_1906_ = lean_array_uget_borrowed(v_as_1896_, v_i_1897_);
v_level_1907_ = lean_ctor_get_uint8(v___x_1906_, sizeof(void*)*1);
v___x_1908_ = l_Lake_instOrdLogLevel_ord(v_b_1899_, v_level_1907_);
if (v___x_1908_ == 2)
{
if (v___x_1905_ == 0)
{
v___y_1901_ = v_b_1899_;
goto v___jp_1900_;
}
else
{
v___y_1901_ = v_level_1907_;
goto v___jp_1900_;
}
}
else
{
v___y_1901_ = v_level_1907_;
goto v___jp_1900_;
}
}
else
{
return v_b_1899_;
}
v___jp_1900_:
{
size_t v___x_1902_; size_t v___x_1903_; 
v___x_1902_ = ((size_t)1ULL);
v___x_1903_ = lean_usize_add(v_i_1897_, v___x_1902_);
v_i_1897_ = v___x_1903_;
v_b_1899_ = v___y_1901_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0___boxed(lean_object* v_as_1909_, lean_object* v_i_1910_, lean_object* v_stop_1911_, lean_object* v_b_1912_){
_start:
{
size_t v_i_boxed_1913_; size_t v_stop_boxed_1914_; uint8_t v_b_boxed_1915_; uint8_t v_res_1916_; lean_object* v_r_1917_; 
v_i_boxed_1913_ = lean_unbox_usize(v_i_1910_);
lean_dec(v_i_1910_);
v_stop_boxed_1914_ = lean_unbox_usize(v_stop_1911_);
lean_dec(v_stop_1911_);
v_b_boxed_1915_ = lean_unbox(v_b_1912_);
v_res_1916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(v_as_1909_, v_i_boxed_1913_, v_stop_boxed_1914_, v_b_boxed_1915_);
lean_dec_ref(v_as_1909_);
v_r_1917_ = lean_box(v_res_1916_);
return v_r_1917_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_maxLv(lean_object* v_log_1918_){
_start:
{
uint8_t v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; 
v___x_1919_ = 0;
v___x_1920_ = lean_unsigned_to_nat(0u);
v___x_1921_ = lean_array_get_size(v_log_1918_);
v___x_1922_ = lean_nat_dec_lt(v___x_1920_, v___x_1921_);
if (v___x_1922_ == 0)
{
return v___x_1919_;
}
else
{
uint8_t v___x_1923_; 
v___x_1923_ = lean_nat_dec_le(v___x_1921_, v___x_1921_);
if (v___x_1923_ == 0)
{
if (v___x_1922_ == 0)
{
return v___x_1919_;
}
else
{
size_t v___x_1924_; size_t v___x_1925_; uint8_t v___x_1926_; 
v___x_1924_ = ((size_t)0ULL);
v___x_1925_ = lean_usize_of_nat(v___x_1921_);
v___x_1926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(v_log_1918_, v___x_1924_, v___x_1925_, v___x_1919_);
return v___x_1926_;
}
}
else
{
size_t v___x_1927_; size_t v___x_1928_; uint8_t v___x_1929_; 
v___x_1927_ = ((size_t)0ULL);
v___x_1928_ = lean_usize_of_nat(v___x_1921_);
v___x_1929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(v_log_1918_, v___x_1927_, v___x_1928_, v___x_1919_);
return v___x_1929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_maxLv___boxed(lean_object* v_log_1930_){
_start:
{
uint8_t v_res_1931_; lean_object* v_r_1932_; 
v_res_1931_ = l_Lake_Log_maxLv(v_log_1930_);
lean_dec_ref(v_log_1930_);
v_r_1932_ = lean_box(v_res_1931_);
return v_r_1932_;
}
}
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___redArg___lam__0(lean_object* v_e_1933_, lean_object* v_s_1934_){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1935_ = lean_box(0);
v___x_1936_ = lean_array_push(v_s_1934_, v_e_1933_);
v___x_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1935_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___redArg(lean_object* v_inst_1938_, lean_object* v_e_1939_){
_start:
{
lean_object* v_modifyGet_1940_; lean_object* v___f_1941_; lean_object* v___x_1942_; 
v_modifyGet_1940_ = lean_ctor_get(v_inst_1938_, 2);
lean_inc(v_modifyGet_1940_);
lean_dec_ref(v_inst_1938_);
v___f_1941_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1941_, 0, v_e_1939_);
v___x_1942_ = lean_apply_2(v_modifyGet_1940_, lean_box(0), v___f_1941_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Lake_pushLogEntry(lean_object* v_m_1943_, lean_object* v_inst_1944_, lean_object* v_e_1945_){
_start:
{
lean_object* v_modifyGet_1946_; lean_object* v___f_1947_; lean_object* v___x_1948_; 
v_modifyGet_1946_ = lean_ctor_get(v_inst_1944_, 2);
lean_inc(v_modifyGet_1946_);
lean_dec_ref(v_inst_1944_);
v___f_1947_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1947_, 0, v_e_1945_);
v___x_1948_ = lean_apply_2(v_modifyGet_1946_, lean_box(0), v___f_1947_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_ofMonadState___redArg(lean_object* v_inst_1949_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(v___x_1950_, 0, lean_box(0));
lean_closure_set(v___x_1950_, 1, v_inst_1949_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_ofMonadState(lean_object* v_m_1951_, lean_object* v_inst_1952_){
_start:
{
lean_object* v___x_1953_; 
v___x_1953_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(v___x_1953_, 0, lean_box(0));
lean_closure_set(v___x_1953_, 1, v_inst_1952_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog___redArg(lean_object* v_inst_1954_){
_start:
{
lean_object* v_get_1955_; 
v_get_1955_ = lean_ctor_get(v_inst_1954_, 0);
lean_inc(v_get_1955_);
return v_get_1955_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog___redArg___boxed(lean_object* v_inst_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_Lake_getLog___redArg(v_inst_1956_);
lean_dec_ref(v_inst_1956_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog(lean_object* v_m_1958_, lean_object* v_inst_1959_){
_start:
{
lean_object* v_get_1960_; 
v_get_1960_ = lean_ctor_get(v_inst_1959_, 0);
lean_inc(v_get_1960_);
return v_get_1960_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog___boxed(lean_object* v_m_1961_, lean_object* v_inst_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lake_getLog(v_m_1961_, v_inst_1962_);
lean_dec_ref(v_inst_1962_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg___lam__0(lean_object* v_x_1964_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = lean_array_get_size(v_x_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg___lam__0___boxed(lean_object* v_x_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lake_getLogPos___redArg___lam__0(v_x_1966_);
lean_dec_ref(v_x_1966_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg(lean_object* v_inst_1969_, lean_object* v_inst_1970_){
_start:
{
lean_object* v_map_1971_; lean_object* v_get_1972_; lean_object* v___f_1973_; lean_object* v___x_1974_; 
v_map_1971_ = lean_ctor_get(v_inst_1969_, 0);
lean_inc(v_map_1971_);
lean_dec_ref(v_inst_1969_);
v_get_1972_ = lean_ctor_get(v_inst_1970_, 0);
lean_inc(v_get_1972_);
lean_dec_ref(v_inst_1970_);
v___f_1973_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_1974_ = lean_apply_4(v_map_1971_, lean_box(0), lean_box(0), v___f_1973_, v_get_1972_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos(lean_object* v_m_1975_, lean_object* v_inst_1976_, lean_object* v_inst_1977_){
_start:
{
lean_object* v_map_1978_; lean_object* v_get_1979_; lean_object* v___f_1980_; lean_object* v___x_1981_; 
v_map_1978_ = lean_ctor_get(v_inst_1976_, 0);
lean_inc(v_map_1978_);
lean_dec_ref(v_inst_1976_);
v_get_1979_ = lean_ctor_get(v_inst_1977_, 0);
lean_inc(v_get_1979_);
lean_dec_ref(v_inst_1977_);
v___f_1980_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_1981_ = lean_apply_4(v_map_1978_, lean_box(0), lean_box(0), v___f_1980_, v_get_1979_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLog___redArg___lam__0(lean_object* v_log_1982_){
_start:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1983_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1984_, 0, v_log_1982_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLog___redArg(lean_object* v_inst_1986_){
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
LEAN_EXPORT lean_object* l_Lake_takeLog(lean_object* v_m_1990_, lean_object* v_inst_1991_){
_start:
{
lean_object* v_modifyGet_1992_; lean_object* v___f_1993_; lean_object* v___x_1994_; 
v_modifyGet_1992_ = lean_ctor_get(v_inst_1991_, 2);
lean_inc(v_modifyGet_1992_);
lean_dec_ref(v_inst_1991_);
v___f_1993_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_1994_ = lean_apply_2(v_modifyGet_1992_, lean_box(0), v___f_1993_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLogFrom___redArg___lam__0(lean_object* v_pos_1995_, lean_object* v_log_1996_){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1997_ = lean_array_get_size(v_log_1996_);
lean_inc(v_pos_1995_);
v___x_1998_ = l_Array_extract___redArg(v_log_1996_, v_pos_1995_, v___x_1997_);
v___x_1999_ = l_Array_shrink___redArg(v_log_1996_, v_pos_1995_);
lean_dec(v_pos_1995_);
v___x_2000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1998_);
lean_ctor_set(v___x_2000_, 1, v___x_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLogFrom___redArg(lean_object* v_inst_2001_, lean_object* v_pos_2002_){
_start:
{
lean_object* v_modifyGet_2003_; lean_object* v___f_2004_; lean_object* v___x_2005_; 
v_modifyGet_2003_ = lean_ctor_get(v_inst_2001_, 2);
lean_inc(v_modifyGet_2003_);
lean_dec_ref(v_inst_2001_);
v___f_2004_ = lean_alloc_closure((void*)(l_Lake_takeLogFrom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2004_, 0, v_pos_2002_);
v___x_2005_ = lean_apply_2(v_modifyGet_2003_, lean_box(0), v___f_2004_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLogFrom(lean_object* v_m_2006_, lean_object* v_inst_2007_, lean_object* v_pos_2008_){
_start:
{
lean_object* v_modifyGet_2009_; lean_object* v___f_2010_; lean_object* v___x_2011_; 
v_modifyGet_2009_ = lean_ctor_get(v_inst_2007_, 2);
lean_inc(v_modifyGet_2009_);
lean_dec_ref(v_inst_2007_);
v___f_2010_ = lean_alloc_closure((void*)(l_Lake_takeLogFrom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2010_, 0, v_pos_2008_);
v___x_2011_ = lean_apply_2(v_modifyGet_2009_, lean_box(0), v___f_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg___lam__0(lean_object* v_pos_2012_, lean_object* v_s_2013_){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2014_ = lean_box(0);
v___x_2015_ = l_Array_shrink___redArg(v_s_2013_, v_pos_2012_);
v___x_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2014_);
lean_ctor_set(v___x_2016_, 1, v___x_2015_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg___lam__0___boxed(lean_object* v_pos_2017_, lean_object* v_s_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Lake_dropLogFrom___redArg___lam__0(v_pos_2017_, v_s_2018_);
lean_dec(v_pos_2017_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg(lean_object* v_inst_2020_, lean_object* v_pos_2021_){
_start:
{
lean_object* v_modifyGet_2022_; lean_object* v___f_2023_; lean_object* v___x_2024_; 
v_modifyGet_2022_ = lean_ctor_get(v_inst_2020_, 2);
lean_inc(v_modifyGet_2022_);
lean_dec_ref(v_inst_2020_);
v___f_2023_ = lean_alloc_closure((void*)(l_Lake_dropLogFrom___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2023_, 0, v_pos_2021_);
v___x_2024_ = lean_apply_2(v_modifyGet_2022_, lean_box(0), v___f_2023_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom(lean_object* v_m_2025_, lean_object* v_inst_2026_, lean_object* v_pos_2027_){
_start:
{
lean_object* v_modifyGet_2028_; lean_object* v___f_2029_; lean_object* v___x_2030_; 
v_modifyGet_2028_ = lean_ctor_get(v_inst_2026_, 2);
lean_inc(v_modifyGet_2028_);
lean_dec_ref(v_inst_2026_);
v___f_2029_ = lean_alloc_closure((void*)(l_Lake_dropLogFrom___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2029_, 0, v_pos_2027_);
v___x_2030_ = lean_apply_2(v_modifyGet_2028_, lean_box(0), v___f_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__1(lean_object* v_iniPos_2031_, lean_object* v_toPure_2032_, lean_object* v_log_2033_){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2034_ = lean_array_get_size(v_log_2033_);
v___x_2035_ = l_Array_extract___redArg(v_log_2033_, v_iniPos_2031_, v___x_2034_);
v___x_2036_ = lean_apply_2(v_toPure_2032_, lean_box(0), v___x_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__1___boxed(lean_object* v_iniPos_2037_, lean_object* v_toPure_2038_, lean_object* v_log_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Lake_extractLog___redArg___lam__1(v_iniPos_2037_, v_toPure_2038_, v_log_2039_);
lean_dec_ref(v_log_2039_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__0(lean_object* v_toBind_2041_, lean_object* v_get_2042_, lean_object* v___f_2043_, lean_object* v_____r_2044_){
_start:
{
lean_object* v___x_2045_; 
v___x_2045_ = lean_apply_4(v_toBind_2041_, lean_box(0), lean_box(0), v_get_2042_, v___f_2043_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__2(lean_object* v_toPure_2046_, lean_object* v_toBind_2047_, lean_object* v_get_2048_, lean_object* v_x_2049_, lean_object* v_iniPos_2050_){
_start:
{
lean_object* v___f_2051_; lean_object* v___f_2052_; lean_object* v___x_2053_; 
v___f_2051_ = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2051_, 0, v_iniPos_2050_);
lean_closure_set(v___f_2051_, 1, v_toPure_2046_);
lean_inc(v_toBind_2047_);
v___f_2052_ = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2052_, 0, v_toBind_2047_);
lean_closure_set(v___f_2052_, 1, v_get_2048_);
lean_closure_set(v___f_2052_, 2, v___f_2051_);
v___x_2053_ = lean_apply_4(v_toBind_2047_, lean_box(0), lean_box(0), v_x_2049_, v___f_2052_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg(lean_object* v_inst_2054_, lean_object* v_inst_2055_, lean_object* v_x_2056_){
_start:
{
lean_object* v_toApplicative_2057_; lean_object* v_toFunctor_2058_; lean_object* v_toBind_2059_; lean_object* v_toPure_2060_; lean_object* v_map_2061_; lean_object* v_get_2062_; lean_object* v___f_2063_; lean_object* v___f_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v_toApplicative_2057_ = lean_ctor_get(v_inst_2054_, 0);
lean_inc_ref(v_toApplicative_2057_);
v_toFunctor_2058_ = lean_ctor_get(v_toApplicative_2057_, 0);
lean_inc_ref(v_toFunctor_2058_);
v_toBind_2059_ = lean_ctor_get(v_inst_2054_, 1);
lean_inc_n(v_toBind_2059_, 2);
lean_dec_ref(v_inst_2054_);
v_toPure_2060_ = lean_ctor_get(v_toApplicative_2057_, 1);
lean_inc(v_toPure_2060_);
lean_dec_ref(v_toApplicative_2057_);
v_map_2061_ = lean_ctor_get(v_toFunctor_2058_, 0);
lean_inc(v_map_2061_);
lean_dec_ref(v_toFunctor_2058_);
v_get_2062_ = lean_ctor_get(v_inst_2055_, 0);
lean_inc_n(v_get_2062_, 2);
lean_dec_ref(v_inst_2055_);
v___f_2063_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2064_ = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2064_, 0, v_toPure_2060_);
lean_closure_set(v___f_2064_, 1, v_toBind_2059_);
lean_closure_set(v___f_2064_, 2, v_get_2062_);
lean_closure_set(v___f_2064_, 3, v_x_2056_);
v___x_2065_ = lean_apply_4(v_map_2061_, lean_box(0), lean_box(0), v___f_2063_, v_get_2062_);
v___x_2066_ = lean_apply_4(v_toBind_2059_, lean_box(0), lean_box(0), v___x_2065_, v___f_2064_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog(lean_object* v_m_2067_, lean_object* v_inst_2068_, lean_object* v_inst_2069_, lean_object* v_x_2070_){
_start:
{
lean_object* v_toApplicative_2071_; lean_object* v_toFunctor_2072_; lean_object* v_toBind_2073_; lean_object* v_toPure_2074_; lean_object* v_map_2075_; lean_object* v_get_2076_; lean_object* v___f_2077_; lean_object* v___f_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v_toApplicative_2071_ = lean_ctor_get(v_inst_2068_, 0);
lean_inc_ref(v_toApplicative_2071_);
v_toFunctor_2072_ = lean_ctor_get(v_toApplicative_2071_, 0);
lean_inc_ref(v_toFunctor_2072_);
v_toBind_2073_ = lean_ctor_get(v_inst_2068_, 1);
lean_inc_n(v_toBind_2073_, 2);
lean_dec_ref(v_inst_2068_);
v_toPure_2074_ = lean_ctor_get(v_toApplicative_2071_, 1);
lean_inc(v_toPure_2074_);
lean_dec_ref(v_toApplicative_2071_);
v_map_2075_ = lean_ctor_get(v_toFunctor_2072_, 0);
lean_inc(v_map_2075_);
lean_dec_ref(v_toFunctor_2072_);
v_get_2076_ = lean_ctor_get(v_inst_2069_, 0);
lean_inc_n(v_get_2076_, 2);
lean_dec_ref(v_inst_2069_);
v___f_2077_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2078_ = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2078_, 0, v_toPure_2074_);
lean_closure_set(v___f_2078_, 1, v_toBind_2073_);
lean_closure_set(v___f_2078_, 2, v_get_2076_);
lean_closure_set(v___f_2078_, 3, v_x_2070_);
v___x_2079_ = lean_apply_4(v_map_2075_, lean_box(0), lean_box(0), v___f_2077_, v_get_2076_);
v___x_2080_ = lean_apply_4(v_toBind_2073_, lean_box(0), lean_box(0), v___x_2079_, v___f_2078_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__1(lean_object* v_iniPos_2081_, lean_object* v_a_2082_, lean_object* v_toPure_2083_, lean_object* v_log_2084_){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2085_ = lean_array_get_size(v_log_2084_);
v___x_2086_ = l_Array_extract___redArg(v_log_2084_, v_iniPos_2081_, v___x_2085_);
v___x_2087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2087_, 0, v_a_2082_);
lean_ctor_set(v___x_2087_, 1, v___x_2086_);
v___x_2088_ = lean_apply_2(v_toPure_2083_, lean_box(0), v___x_2087_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__1___boxed(lean_object* v_iniPos_2089_, lean_object* v_a_2090_, lean_object* v_toPure_2091_, lean_object* v_log_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l_Lake_withExtractLog___redArg___lam__1(v_iniPos_2089_, v_a_2090_, v_toPure_2091_, v_log_2092_);
lean_dec_ref(v_log_2092_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__0(lean_object* v_iniPos_2094_, lean_object* v_toPure_2095_, lean_object* v_toBind_2096_, lean_object* v_get_2097_, lean_object* v_a_2098_){
_start:
{
lean_object* v___f_2099_; lean_object* v___x_2100_; 
v___f_2099_ = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2099_, 0, v_iniPos_2094_);
lean_closure_set(v___f_2099_, 1, v_a_2098_);
lean_closure_set(v___f_2099_, 2, v_toPure_2095_);
v___x_2100_ = lean_apply_4(v_toBind_2096_, lean_box(0), lean_box(0), v_get_2097_, v___f_2099_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__2(lean_object* v_toPure_2101_, lean_object* v_toBind_2102_, lean_object* v_get_2103_, lean_object* v_x_2104_, lean_object* v_iniPos_2105_){
_start:
{
lean_object* v___f_2106_; lean_object* v___x_2107_; 
lean_inc(v_toBind_2102_);
v___f_2106_ = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2106_, 0, v_iniPos_2105_);
lean_closure_set(v___f_2106_, 1, v_toPure_2101_);
lean_closure_set(v___f_2106_, 2, v_toBind_2102_);
lean_closure_set(v___f_2106_, 3, v_get_2103_);
v___x_2107_ = lean_apply_4(v_toBind_2102_, lean_box(0), lean_box(0), v_x_2104_, v___f_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg(lean_object* v_inst_2108_, lean_object* v_inst_2109_, lean_object* v_x_2110_){
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
LEAN_EXPORT lean_object* l_Lake_withExtractLog(lean_object* v_m_2121_, lean_object* v_00_u03b1_2122_, lean_object* v_inst_2123_, lean_object* v_inst_2124_, lean_object* v_x_2125_){
_start:
{
lean_object* v_toApplicative_2126_; lean_object* v_toFunctor_2127_; lean_object* v_toBind_2128_; lean_object* v_toPure_2129_; lean_object* v_map_2130_; lean_object* v_get_2131_; lean_object* v___f_2132_; lean_object* v___f_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v_toApplicative_2126_ = lean_ctor_get(v_inst_2123_, 0);
lean_inc_ref(v_toApplicative_2126_);
v_toFunctor_2127_ = lean_ctor_get(v_toApplicative_2126_, 0);
lean_inc_ref(v_toFunctor_2127_);
v_toBind_2128_ = lean_ctor_get(v_inst_2123_, 1);
lean_inc_n(v_toBind_2128_, 2);
lean_dec_ref(v_inst_2123_);
v_toPure_2129_ = lean_ctor_get(v_toApplicative_2126_, 1);
lean_inc(v_toPure_2129_);
lean_dec_ref(v_toApplicative_2126_);
v_map_2130_ = lean_ctor_get(v_toFunctor_2127_, 0);
lean_inc(v_map_2130_);
lean_dec_ref(v_toFunctor_2127_);
v_get_2131_ = lean_ctor_get(v_inst_2124_, 0);
lean_inc_n(v_get_2131_, 2);
lean_dec_ref(v_inst_2124_);
v___f_2132_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2133_ = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2133_, 0, v_toPure_2129_);
lean_closure_set(v___f_2133_, 1, v_toBind_2128_);
lean_closure_set(v___f_2133_, 2, v_get_2131_);
lean_closure_set(v___f_2133_, 3, v_x_2125_);
v___x_2134_ = lean_apply_4(v_map_2130_, lean_box(0), lean_box(0), v___f_2132_, v_get_2131_);
v___x_2135_ = lean_apply_4(v_toBind_2128_, lean_box(0), lean_box(0), v___x_2134_, v___f_2133_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__1(lean_object* v_iniPos_2136_, lean_object* v_inst_2137_, lean_object* v_toPure_2138_, lean_object* v_a_2139_, lean_object* v_endPos_2140_){
_start:
{
uint8_t v___x_2141_; 
v___x_2141_ = lean_nat_dec_eq(v_iniPos_2136_, v_endPos_2140_);
if (v___x_2141_ == 0)
{
lean_object* v_throw_2142_; lean_object* v___x_2143_; 
lean_dec(v_a_2139_);
lean_dec(v_toPure_2138_);
v_throw_2142_ = lean_ctor_get(v_inst_2137_, 0);
lean_inc(v_throw_2142_);
lean_dec_ref(v_inst_2137_);
v___x_2143_ = lean_apply_2(v_throw_2142_, lean_box(0), v_iniPos_2136_);
return v___x_2143_;
}
else
{
lean_object* v___x_2144_; 
lean_dec_ref(v_inst_2137_);
lean_dec(v_iniPos_2136_);
v___x_2144_ = lean_apply_2(v_toPure_2138_, lean_box(0), v_a_2139_);
return v___x_2144_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__1___boxed(lean_object* v_iniPos_2145_, lean_object* v_inst_2146_, lean_object* v_toPure_2147_, lean_object* v_a_2148_, lean_object* v_endPos_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l_Lake_throwIfLogs___redArg___lam__1(v_iniPos_2145_, v_inst_2146_, v_toPure_2147_, v_a_2148_, v_endPos_2149_);
lean_dec(v_endPos_2149_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__0(lean_object* v_iniPos_2151_, lean_object* v_inst_2152_, lean_object* v_toPure_2153_, lean_object* v_toBind_2154_, lean_object* v___x_2155_, lean_object* v_a_2156_){
_start:
{
lean_object* v___f_2157_; lean_object* v___x_2158_; 
v___f_2157_ = lean_alloc_closure((void*)(l_Lake_throwIfLogs___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2157_, 0, v_iniPos_2151_);
lean_closure_set(v___f_2157_, 1, v_inst_2152_);
lean_closure_set(v___f_2157_, 2, v_toPure_2153_);
lean_closure_set(v___f_2157_, 3, v_a_2156_);
v___x_2158_ = lean_apply_4(v_toBind_2154_, lean_box(0), lean_box(0), v___x_2155_, v___f_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__2(lean_object* v_inst_2159_, lean_object* v_toPure_2160_, lean_object* v_toBind_2161_, lean_object* v___x_2162_, lean_object* v_x_2163_, lean_object* v_iniPos_2164_){
_start:
{
lean_object* v___f_2165_; lean_object* v___x_2166_; 
lean_inc(v_toBind_2161_);
v___f_2165_ = lean_alloc_closure((void*)(l_Lake_throwIfLogs___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2165_, 0, v_iniPos_2164_);
lean_closure_set(v___f_2165_, 1, v_inst_2159_);
lean_closure_set(v___f_2165_, 2, v_toPure_2160_);
lean_closure_set(v___f_2165_, 3, v_toBind_2161_);
lean_closure_set(v___f_2165_, 4, v___x_2162_);
v___x_2166_ = lean_apply_4(v_toBind_2161_, lean_box(0), lean_box(0), v_x_2163_, v___f_2165_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg(lean_object* v_inst_2167_, lean_object* v_inst_2168_, lean_object* v_inst_2169_, lean_object* v_x_2170_){
_start:
{
lean_object* v_toApplicative_2171_; lean_object* v_toFunctor_2172_; lean_object* v_toBind_2173_; lean_object* v_toPure_2174_; lean_object* v_map_2175_; lean_object* v_get_2176_; lean_object* v___f_2177_; lean_object* v___x_2178_; lean_object* v___f_2179_; lean_object* v___x_2180_; 
v_toApplicative_2171_ = lean_ctor_get(v_inst_2167_, 0);
lean_inc_ref(v_toApplicative_2171_);
v_toFunctor_2172_ = lean_ctor_get(v_toApplicative_2171_, 0);
lean_inc_ref(v_toFunctor_2172_);
v_toBind_2173_ = lean_ctor_get(v_inst_2167_, 1);
lean_inc_n(v_toBind_2173_, 2);
lean_dec_ref(v_inst_2167_);
v_toPure_2174_ = lean_ctor_get(v_toApplicative_2171_, 1);
lean_inc(v_toPure_2174_);
lean_dec_ref(v_toApplicative_2171_);
v_map_2175_ = lean_ctor_get(v_toFunctor_2172_, 0);
lean_inc(v_map_2175_);
lean_dec_ref(v_toFunctor_2172_);
v_get_2176_ = lean_ctor_get(v_inst_2168_, 0);
lean_inc(v_get_2176_);
lean_dec_ref(v_inst_2168_);
v___f_2177_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_2178_ = lean_apply_4(v_map_2175_, lean_box(0), lean_box(0), v___f_2177_, v_get_2176_);
lean_inc(v___x_2178_);
v___f_2179_ = lean_alloc_closure((void*)(l_Lake_throwIfLogs___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2179_, 0, v_inst_2169_);
lean_closure_set(v___f_2179_, 1, v_toPure_2174_);
lean_closure_set(v___f_2179_, 2, v_toBind_2173_);
lean_closure_set(v___f_2179_, 3, v___x_2178_);
lean_closure_set(v___f_2179_, 4, v_x_2170_);
v___x_2180_ = lean_apply_4(v_toBind_2173_, lean_box(0), lean_box(0), v___x_2178_, v___f_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs(lean_object* v_m_2181_, lean_object* v_00_u03b1_2182_, lean_object* v_inst_2183_, lean_object* v_inst_2184_, lean_object* v_inst_2185_, lean_object* v_x_2186_){
_start:
{
lean_object* v_toApplicative_2187_; lean_object* v_toFunctor_2188_; lean_object* v_toBind_2189_; lean_object* v_toPure_2190_; lean_object* v_map_2191_; lean_object* v_get_2192_; lean_object* v___f_2193_; lean_object* v___x_2194_; lean_object* v___f_2195_; lean_object* v___x_2196_; 
v_toApplicative_2187_ = lean_ctor_get(v_inst_2183_, 0);
lean_inc_ref(v_toApplicative_2187_);
v_toFunctor_2188_ = lean_ctor_get(v_toApplicative_2187_, 0);
lean_inc_ref(v_toFunctor_2188_);
v_toBind_2189_ = lean_ctor_get(v_inst_2183_, 1);
lean_inc_n(v_toBind_2189_, 2);
lean_dec_ref(v_inst_2183_);
v_toPure_2190_ = lean_ctor_get(v_toApplicative_2187_, 1);
lean_inc(v_toPure_2190_);
lean_dec_ref(v_toApplicative_2187_);
v_map_2191_ = lean_ctor_get(v_toFunctor_2188_, 0);
lean_inc(v_map_2191_);
lean_dec_ref(v_toFunctor_2188_);
v_get_2192_ = lean_ctor_get(v_inst_2184_, 0);
lean_inc(v_get_2192_);
lean_dec_ref(v_inst_2184_);
v___f_2193_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_2194_ = lean_apply_4(v_map_2191_, lean_box(0), lean_box(0), v___f_2193_, v_get_2192_);
lean_inc(v___x_2194_);
v___f_2195_ = lean_alloc_closure((void*)(l_Lake_throwIfLogs___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2195_, 0, v_inst_2185_);
lean_closure_set(v___f_2195_, 1, v_toPure_2190_);
lean_closure_set(v___f_2195_, 2, v_toBind_2189_);
lean_closure_set(v___f_2195_, 3, v___x_2194_);
lean_closure_set(v___f_2195_, 4, v_x_2186_);
v___x_2196_ = lean_apply_4(v_toBind_2189_, lean_box(0), lean_box(0), v___x_2194_, v___f_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__1(lean_object* v_throw_2197_, lean_object* v_iniPos_2198_, lean_object* v_x_2199_){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = lean_apply_2(v_throw_2197_, lean_box(0), v_iniPos_2198_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__1___boxed(lean_object* v_throw_2201_, lean_object* v_iniPos_2202_, lean_object* v_x_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lake_withLogErrorPos___redArg___lam__1(v_throw_2201_, v_iniPos_2202_, v_x_2203_);
lean_dec(v_x_2203_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__0(lean_object* v_inst_2205_, lean_object* v_self_2206_, lean_object* v_iniPos_2207_){
_start:
{
lean_object* v_throw_2208_; lean_object* v_tryCatch_2209_; lean_object* v___f_2210_; lean_object* v___x_2211_; 
v_throw_2208_ = lean_ctor_get(v_inst_2205_, 0);
lean_inc(v_throw_2208_);
v_tryCatch_2209_ = lean_ctor_get(v_inst_2205_, 1);
lean_inc(v_tryCatch_2209_);
lean_dec_ref(v_inst_2205_);
v___f_2210_ = lean_alloc_closure((void*)(l_Lake_withLogErrorPos___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2210_, 0, v_throw_2208_);
lean_closure_set(v___f_2210_, 1, v_iniPos_2207_);
v___x_2211_ = lean_apply_3(v_tryCatch_2209_, lean_box(0), v_self_2206_, v___f_2210_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg(lean_object* v_inst_2212_, lean_object* v_inst_2213_, lean_object* v_inst_2214_, lean_object* v_self_2215_){
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
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos(lean_object* v_m_2225_, lean_object* v_00_u03b1_2226_, lean_object* v_inst_2227_, lean_object* v_inst_2228_, lean_object* v_inst_2229_, lean_object* v_self_2230_){
_start:
{
lean_object* v_toApplicative_2231_; lean_object* v_toFunctor_2232_; lean_object* v_toBind_2233_; lean_object* v_map_2234_; lean_object* v_get_2235_; lean_object* v___f_2236_; lean_object* v___f_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v_toApplicative_2231_ = lean_ctor_get(v_inst_2227_, 0);
v_toFunctor_2232_ = lean_ctor_get(v_toApplicative_2231_, 0);
lean_inc_ref(v_toFunctor_2232_);
v_toBind_2233_ = lean_ctor_get(v_inst_2227_, 1);
lean_inc(v_toBind_2233_);
lean_dec_ref(v_inst_2227_);
v_map_2234_ = lean_ctor_get(v_toFunctor_2232_, 0);
lean_inc(v_map_2234_);
lean_dec_ref(v_toFunctor_2232_);
v_get_2235_ = lean_ctor_get(v_inst_2228_, 0);
lean_inc(v_get_2235_);
lean_dec_ref(v_inst_2228_);
v___f_2236_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2237_ = lean_alloc_closure((void*)(l_Lake_withLogErrorPos___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2237_, 0, v_inst_2229_);
lean_closure_set(v___f_2237_, 1, v_self_2230_);
v___x_2238_ = lean_apply_4(v_map_2234_, lean_box(0), lean_box(0), v___f_2236_, v_get_2235_);
v___x_2239_ = lean_apply_4(v_toBind_2233_, lean_box(0), lean_box(0), v___x_2238_, v___f_2237_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__1(lean_object* v_toPure_2240_, lean_object* v_x_2241_){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2242_ = lean_box(0);
v___x_2243_ = lean_apply_2(v_toPure_2240_, lean_box(0), v___x_2242_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__1___boxed(lean_object* v_toPure_2244_, lean_object* v_x_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_Lake_errorWithLog___redArg___lam__1(v_toPure_2244_, v_x_2245_);
lean_dec(v_x_2245_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__0(lean_object* v_throw_2247_, lean_object* v_iniPos_2248_, lean_object* v_____r_2249_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = lean_apply_2(v_throw_2247_, lean_box(0), v_iniPos_2248_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__2(lean_object* v_inst_2251_, lean_object* v_self_2252_, lean_object* v___f_2253_, lean_object* v_toBind_2254_, lean_object* v_iniPos_2255_){
_start:
{
lean_object* v_throw_2256_; lean_object* v_tryCatch_2257_; lean_object* v___f_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v_throw_2256_ = lean_ctor_get(v_inst_2251_, 0);
lean_inc(v_throw_2256_);
v_tryCatch_2257_ = lean_ctor_get(v_inst_2251_, 1);
lean_inc(v_tryCatch_2257_);
lean_dec_ref(v_inst_2251_);
v___f_2258_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2258_, 0, v_throw_2256_);
lean_closure_set(v___f_2258_, 1, v_iniPos_2255_);
v___x_2259_ = lean_apply_3(v_tryCatch_2257_, lean_box(0), v_self_2252_, v___f_2253_);
v___x_2260_ = lean_apply_4(v_toBind_2254_, lean_box(0), lean_box(0), v___x_2259_, v___f_2258_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg(lean_object* v_inst_2261_, lean_object* v_inst_2262_, lean_object* v_inst_2263_, lean_object* v_self_2264_){
_start:
{
lean_object* v_toApplicative_2265_; lean_object* v_toFunctor_2266_; lean_object* v_toBind_2267_; lean_object* v_toPure_2268_; lean_object* v_map_2269_; lean_object* v_get_2270_; lean_object* v___f_2271_; lean_object* v___f_2272_; lean_object* v___f_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v_toApplicative_2265_ = lean_ctor_get(v_inst_2261_, 0);
lean_inc_ref(v_toApplicative_2265_);
v_toFunctor_2266_ = lean_ctor_get(v_toApplicative_2265_, 0);
lean_inc_ref(v_toFunctor_2266_);
v_toBind_2267_ = lean_ctor_get(v_inst_2261_, 1);
lean_inc_n(v_toBind_2267_, 2);
lean_dec_ref(v_inst_2261_);
v_toPure_2268_ = lean_ctor_get(v_toApplicative_2265_, 1);
lean_inc(v_toPure_2268_);
lean_dec_ref(v_toApplicative_2265_);
v_map_2269_ = lean_ctor_get(v_toFunctor_2266_, 0);
lean_inc(v_map_2269_);
lean_dec_ref(v_toFunctor_2266_);
v_get_2270_ = lean_ctor_get(v_inst_2262_, 0);
lean_inc(v_get_2270_);
lean_dec_ref(v_inst_2262_);
v___f_2271_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2272_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2272_, 0, v_toPure_2268_);
v___f_2273_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2273_, 0, v_inst_2263_);
lean_closure_set(v___f_2273_, 1, v_self_2264_);
lean_closure_set(v___f_2273_, 2, v___f_2272_);
lean_closure_set(v___f_2273_, 3, v_toBind_2267_);
v___x_2274_ = lean_apply_4(v_map_2269_, lean_box(0), lean_box(0), v___f_2271_, v_get_2270_);
v___x_2275_ = lean_apply_4(v_toBind_2267_, lean_box(0), lean_box(0), v___x_2274_, v___f_2273_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog(lean_object* v_m_2276_, lean_object* v_00_u03b2_2277_, lean_object* v_inst_2278_, lean_object* v_inst_2279_, lean_object* v_inst_2280_, lean_object* v_self_2281_){
_start:
{
lean_object* v_toApplicative_2282_; lean_object* v_toFunctor_2283_; lean_object* v_toBind_2284_; lean_object* v_toPure_2285_; lean_object* v_map_2286_; lean_object* v_get_2287_; lean_object* v___f_2288_; lean_object* v___f_2289_; lean_object* v___f_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v_toApplicative_2282_ = lean_ctor_get(v_inst_2278_, 0);
lean_inc_ref(v_toApplicative_2282_);
v_toFunctor_2283_ = lean_ctor_get(v_toApplicative_2282_, 0);
lean_inc_ref(v_toFunctor_2283_);
v_toBind_2284_ = lean_ctor_get(v_inst_2278_, 1);
lean_inc_n(v_toBind_2284_, 2);
lean_dec_ref(v_inst_2278_);
v_toPure_2285_ = lean_ctor_get(v_toApplicative_2282_, 1);
lean_inc(v_toPure_2285_);
lean_dec_ref(v_toApplicative_2282_);
v_map_2286_ = lean_ctor_get(v_toFunctor_2283_, 0);
lean_inc(v_map_2286_);
lean_dec_ref(v_toFunctor_2283_);
v_get_2287_ = lean_ctor_get(v_inst_2279_, 0);
lean_inc(v_get_2287_);
lean_dec_ref(v_inst_2279_);
v___f_2288_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2289_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2289_, 0, v_toPure_2285_);
v___f_2290_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2290_, 0, v_inst_2280_);
lean_closure_set(v___f_2290_, 1, v_self_2281_);
lean_closure_set(v___f_2290_, 2, v___f_2289_);
lean_closure_set(v___f_2290_, 3, v_toBind_2284_);
v___x_2291_ = lean_apply_4(v_map_2286_, lean_box(0), lean_box(0), v___f_2288_, v_get_2287_);
v___x_2292_ = lean_apply_4(v_toBind_2284_, lean_box(0), lean_box(0), v___x_2291_, v___f_2290_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__0(lean_object* v_x_2293_){
_start:
{
lean_object* v_fst_2294_; 
v_fst_2294_ = lean_ctor_get(v_x_2293_, 0);
lean_inc(v_fst_2294_);
return v_fst_2294_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__0___boxed(lean_object* v_x_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lake_withLoggedIO___redArg___lam__0(v_x_2295_);
lean_dec_ref(v_x_2295_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__1(lean_object* v_buf_2297_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = lean_st_ref_get(v_buf_2297_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__1___boxed(lean_object* v_buf_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lake_withLoggedIO___redArg___lam__1(v_buf_2300_);
lean_dec(v_buf_2300_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__2(lean_object* v_toPure_2303_, lean_object* v_a_2304_, lean_object* v_____r_2305_){
_start:
{
lean_object* v___x_2306_; 
v___x_2306_ = lean_apply_2(v_toPure_2303_, lean_box(0), v_a_2304_);
return v___x_2306_;
}
}
static lean_object* _init_l_Lake_withLoggedIO___redArg___lam__3___closed__4(void){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2311_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___lam__3___closed__3));
v___x_2312_ = lean_unsigned_to_nat(46u);
v___x_2313_ = lean_unsigned_to_nat(193u);
v___x_2314_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___lam__3___closed__2));
v___x_2315_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___lam__3___closed__1));
v___x_2316_ = l_mkPanicMessageWithDecl(v___x_2315_, v___x_2314_, v___x_2313_, v___x_2312_, v___x_2311_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__3(lean_object* v___x_2317_, lean_object* v_inst_2318_, lean_object* v_toBind_2319_, lean_object* v___f_2320_, lean_object* v_toPure_2321_, lean_object* v_a_2322_, lean_object* v_buf_2323_){
_start:
{
lean_object* v___y_2325_; lean_object* v_data_2338_; uint8_t v___x_2339_; 
v_data_2338_ = lean_ctor_get(v_buf_2323_, 0);
lean_inc_ref(v_data_2338_);
lean_dec_ref(v_buf_2323_);
v___x_2339_ = lean_string_validate_utf8(v_data_2338_);
if (v___x_2339_ == 0)
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
lean_dec_ref(v_data_2338_);
v___x_2340_ = ((lean_object*)(l_Lake_instInhabitedLogEntry_default___closed__0));
v___x_2341_ = lean_obj_once(&l_Lake_withLoggedIO___redArg___lam__3___closed__4, &l_Lake_withLoggedIO___redArg___lam__3___closed__4_once, _init_l_Lake_withLoggedIO___redArg___lam__3___closed__4);
v___x_2342_ = l_panic___redArg(v___x_2340_, v___x_2341_);
v___y_2325_ = v___x_2342_;
goto v___jp_2324_;
}
else
{
lean_object* v___x_2343_; 
v___x_2343_ = lean_string_from_utf8_unchecked(v_data_2338_);
v___y_2325_ = v___x_2343_;
goto v___jp_2324_;
}
v___jp_2324_:
{
lean_object* v___x_2326_; uint8_t v___x_2327_; 
v___x_2326_ = lean_string_utf8_byte_size(v___y_2325_);
v___x_2327_ = lean_nat_dec_eq(v___x_2326_, v___x_2317_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; uint8_t v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
lean_dec(v_a_2322_);
lean_dec(v_toPure_2321_);
v___x_2328_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___lam__3___closed__0));
v___x_2329_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2329_, 0, v___y_2325_);
lean_ctor_set(v___x_2329_, 1, v___x_2317_);
lean_ctor_set(v___x_2329_, 2, v___x_2326_);
v___x_2330_ = l_String_Slice_trimAscii(v___x_2329_);
v___x_2331_ = l_String_Slice_toString(v___x_2330_);
lean_dec_ref(v___x_2330_);
v___x_2332_ = lean_string_append(v___x_2328_, v___x_2331_);
lean_dec_ref(v___x_2331_);
v___x_2333_ = 1;
v___x_2334_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2334_, 0, v___x_2332_);
lean_ctor_set_uint8(v___x_2334_, sizeof(void*)*1, v___x_2333_);
v___x_2335_ = lean_apply_1(v_inst_2318_, v___x_2334_);
v___x_2336_ = lean_apply_4(v_toBind_2319_, lean_box(0), lean_box(0), v___x_2335_, v___f_2320_);
return v___x_2336_;
}
else
{
lean_object* v___x_2337_; 
lean_dec_ref(v___y_2325_);
lean_dec(v___f_2320_);
lean_dec(v_toBind_2319_);
lean_dec(v_inst_2318_);
lean_dec(v___x_2317_);
v___x_2337_ = lean_apply_2(v_toPure_2321_, lean_box(0), v_a_2322_);
return v___x_2337_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__4(lean_object* v_toPure_2344_, lean_object* v___x_2345_, lean_object* v_inst_2346_, lean_object* v_toBind_2347_, lean_object* v_inst_2348_, lean_object* v___f_2349_, lean_object* v_a_2350_){
_start:
{
lean_object* v___f_2351_; lean_object* v___f_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
lean_inc(v_a_2350_);
lean_inc(v_toPure_2344_);
v___f_2351_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2351_, 0, v_toPure_2344_);
lean_closure_set(v___f_2351_, 1, v_a_2350_);
lean_inc(v_toBind_2347_);
v___f_2352_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__3), 7, 6);
lean_closure_set(v___f_2352_, 0, v___x_2345_);
lean_closure_set(v___f_2352_, 1, v_inst_2346_);
lean_closure_set(v___f_2352_, 2, v_toBind_2347_);
lean_closure_set(v___f_2352_, 3, v___f_2351_);
lean_closure_set(v___f_2352_, 4, v_toPure_2344_);
lean_closure_set(v___f_2352_, 5, v_a_2350_);
v___x_2353_ = lean_apply_2(v_inst_2348_, lean_box(0), v___f_2349_);
v___x_2354_ = lean_apply_4(v_toBind_2347_, lean_box(0), lean_box(0), v___x_2353_, v___f_2352_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__5(lean_object* v_stderr_2355_, lean_object* v_inst_2356_, lean_object* v_mapConst_2357_, lean_object* v_____r_2358_){
_start:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2359_ = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(v___x_2359_, 0, v_stderr_2355_);
v___x_2360_ = lean_apply_2(v_inst_2356_, lean_box(0), v___x_2359_);
v___x_2361_ = lean_box(0);
v___x_2362_ = lean_apply_4(v_mapConst_2357_, lean_box(0), lean_box(0), v___x_2361_, v___x_2360_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__6(lean_object* v___x_2363_, lean_object* v_x_2364_){
_start:
{
lean_inc(v___x_2363_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__6___boxed(lean_object* v___x_2365_, lean_object* v_x_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Lake_withLoggedIO___redArg___lam__6(v___x_2365_, v_x_2366_);
lean_dec(v_x_2366_);
lean_dec(v___x_2365_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__7(lean_object* v_toFunctor_2368_, lean_object* v_inst_2369_, lean_object* v_stdout_2370_, lean_object* v_toBind_2371_, lean_object* v_inst_2372_, lean_object* v_x_2373_, lean_object* v___f_2374_, lean_object* v___f_2375_, lean_object* v_stderr_2376_){
_start:
{
lean_object* v_map_2377_; lean_object* v_mapConst_2378_; lean_object* v___f_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___f_2385_; lean_object* v_y_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v_map_2377_ = lean_ctor_get(v_toFunctor_2368_, 0);
lean_inc(v_map_2377_);
v_mapConst_2378_ = lean_ctor_get(v_toFunctor_2368_, 1);
lean_inc_n(v_mapConst_2378_, 2);
lean_dec_ref(v_toFunctor_2368_);
lean_inc(v_inst_2369_);
v___f_2379_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__5), 4, 3);
lean_closure_set(v___f_2379_, 0, v_stderr_2376_);
lean_closure_set(v___f_2379_, 1, v_inst_2369_);
lean_closure_set(v___f_2379_, 2, v_mapConst_2378_);
v___x_2380_ = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(v___x_2380_, 0, v_stdout_2370_);
v___x_2381_ = lean_apply_2(v_inst_2369_, lean_box(0), v___x_2380_);
v___x_2382_ = lean_box(0);
v___x_2383_ = lean_apply_4(v_mapConst_2378_, lean_box(0), lean_box(0), v___x_2382_, v___x_2381_);
lean_inc(v_toBind_2371_);
v___x_2384_ = lean_apply_4(v_toBind_2371_, lean_box(0), lean_box(0), v___x_2383_, v___f_2379_);
v___f_2385_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__6___boxed), 2, 1);
lean_closure_set(v___f_2385_, 0, v___x_2384_);
v_y_2386_ = lean_apply_4(v_inst_2372_, lean_box(0), lean_box(0), v_x_2373_, v___f_2385_);
v___x_2387_ = lean_apply_4(v_map_2377_, lean_box(0), lean_box(0), v___f_2374_, v_y_2386_);
v___x_2388_ = lean_apply_4(v_toBind_2371_, lean_box(0), lean_box(0), v___x_2387_, v___f_2375_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__8(lean_object* v_toFunctor_2389_, lean_object* v_inst_2390_, lean_object* v_toBind_2391_, lean_object* v_inst_2392_, lean_object* v_x_2393_, lean_object* v___f_2394_, lean_object* v___f_2395_, lean_object* v___x_2396_, lean_object* v_stdout_2397_){
_start:
{
lean_object* v___f_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
lean_inc(v_toBind_2391_);
lean_inc(v_inst_2390_);
v___f_2398_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__7), 9, 8);
lean_closure_set(v___f_2398_, 0, v_toFunctor_2389_);
lean_closure_set(v___f_2398_, 1, v_inst_2390_);
lean_closure_set(v___f_2398_, 2, v_stdout_2397_);
lean_closure_set(v___f_2398_, 3, v_toBind_2391_);
lean_closure_set(v___f_2398_, 4, v_inst_2392_);
lean_closure_set(v___f_2398_, 5, v_x_2393_);
lean_closure_set(v___f_2398_, 6, v___f_2394_);
lean_closure_set(v___f_2398_, 7, v___f_2395_);
v___x_2399_ = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(v___x_2399_, 0, v___x_2396_);
v___x_2400_ = lean_apply_2(v_inst_2390_, lean_box(0), v___x_2399_);
v___x_2401_ = lean_apply_4(v_toBind_2391_, lean_box(0), lean_box(0), v___x_2400_, v___f_2398_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__9(lean_object* v_toPure_2402_, lean_object* v___x_2403_, lean_object* v_inst_2404_, lean_object* v_toBind_2405_, lean_object* v_inst_2406_, lean_object* v_toFunctor_2407_, lean_object* v_inst_2408_, lean_object* v_x_2409_, lean_object* v___f_2410_, lean_object* v_buf_2411_){
_start:
{
lean_object* v___f_2412_; lean_object* v___f_2413_; lean_object* v___x_2414_; lean_object* v___f_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
lean_inc(v_buf_2411_);
v___f_2412_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2412_, 0, v_buf_2411_);
lean_inc_n(v_inst_2406_, 2);
lean_inc_n(v_toBind_2405_, 2);
v___f_2413_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__4), 7, 6);
lean_closure_set(v___f_2413_, 0, v_toPure_2402_);
lean_closure_set(v___f_2413_, 1, v___x_2403_);
lean_closure_set(v___f_2413_, 2, v_inst_2404_);
lean_closure_set(v___f_2413_, 3, v_toBind_2405_);
lean_closure_set(v___f_2413_, 4, v_inst_2406_);
lean_closure_set(v___f_2413_, 5, v___f_2412_);
v___x_2414_ = l_IO_FS_Stream_ofBuffer(v_buf_2411_);
lean_inc_ref(v___x_2414_);
v___f_2415_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__8), 9, 8);
lean_closure_set(v___f_2415_, 0, v_toFunctor_2407_);
lean_closure_set(v___f_2415_, 1, v_inst_2406_);
lean_closure_set(v___f_2415_, 2, v_toBind_2405_);
lean_closure_set(v___f_2415_, 3, v_inst_2408_);
lean_closure_set(v___f_2415_, 4, v_x_2409_);
lean_closure_set(v___f_2415_, 5, v___f_2410_);
lean_closure_set(v___f_2415_, 6, v___f_2413_);
lean_closure_set(v___f_2415_, 7, v___x_2414_);
v___x_2416_ = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(v___x_2416_, 0, v___x_2414_);
v___x_2417_ = lean_apply_2(v_inst_2406_, lean_box(0), v___x_2416_);
v___x_2418_ = lean_apply_4(v_toBind_2405_, lean_box(0), lean_box(0), v___x_2417_, v___f_2415_);
return v___x_2418_;
}
}
static lean_object* _init_l_Lake_withLoggedIO___redArg___closed__1(void){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2420_ = lean_unsigned_to_nat(0u);
v___x_2421_ = l_ByteArray_empty;
v___x_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2421_);
lean_ctor_set(v___x_2422_, 1, v___x_2420_);
return v___x_2422_;
}
}
static lean_object* _init_l_Lake_withLoggedIO___redArg___closed__2(void){
_start:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2423_ = lean_obj_once(&l_Lake_withLoggedIO___redArg___closed__1, &l_Lake_withLoggedIO___redArg___closed__1_once, _init_l_Lake_withLoggedIO___redArg___closed__1);
v___x_2424_ = lean_alloc_closure((void*)(l_IO_mkRef___boxed), 3, 2);
lean_closure_set(v___x_2424_, 0, lean_box(0));
lean_closure_set(v___x_2424_, 1, v___x_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg(lean_object* v_inst_2425_, lean_object* v_inst_2426_, lean_object* v_inst_2427_, lean_object* v_inst_2428_, lean_object* v_x_2429_){
_start:
{
lean_object* v_toApplicative_2430_; lean_object* v_toBind_2431_; lean_object* v_toFunctor_2432_; lean_object* v_toPure_2433_; lean_object* v___f_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___f_2438_; lean_object* v___x_2439_; 
v_toApplicative_2430_ = lean_ctor_get(v_inst_2425_, 0);
lean_inc_ref(v_toApplicative_2430_);
v_toBind_2431_ = lean_ctor_get(v_inst_2425_, 1);
lean_inc_n(v_toBind_2431_, 2);
lean_dec_ref(v_inst_2425_);
v_toFunctor_2432_ = lean_ctor_get(v_toApplicative_2430_, 0);
lean_inc_ref(v_toFunctor_2432_);
v_toPure_2433_ = lean_ctor_get(v_toApplicative_2430_, 1);
lean_inc(v_toPure_2433_);
lean_dec_ref(v_toApplicative_2430_);
v___f_2434_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___closed__0));
v___x_2435_ = lean_unsigned_to_nat(0u);
v___x_2436_ = lean_obj_once(&l_Lake_withLoggedIO___redArg___closed__2, &l_Lake_withLoggedIO___redArg___closed__2_once, _init_l_Lake_withLoggedIO___redArg___closed__2);
lean_inc(v_inst_2426_);
v___x_2437_ = lean_apply_2(v_inst_2426_, lean_box(0), v___x_2436_);
v___f_2438_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__9), 10, 9);
lean_closure_set(v___f_2438_, 0, v_toPure_2433_);
lean_closure_set(v___f_2438_, 1, v___x_2435_);
lean_closure_set(v___f_2438_, 2, v_inst_2427_);
lean_closure_set(v___f_2438_, 3, v_toBind_2431_);
lean_closure_set(v___f_2438_, 4, v_inst_2426_);
lean_closure_set(v___f_2438_, 5, v_toFunctor_2432_);
lean_closure_set(v___f_2438_, 6, v_inst_2428_);
lean_closure_set(v___f_2438_, 7, v_x_2429_);
lean_closure_set(v___f_2438_, 8, v___f_2434_);
v___x_2439_ = lean_apply_4(v_toBind_2431_, lean_box(0), lean_box(0), v___x_2437_, v___f_2438_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO(lean_object* v_m_2440_, lean_object* v_00_u03b1_2441_, lean_object* v_inst_2442_, lean_object* v_inst_2443_, lean_object* v_inst_2444_, lean_object* v_inst_2445_, lean_object* v_x_2446_){
_start:
{
lean_object* v_toApplicative_2447_; lean_object* v_toBind_2448_; lean_object* v_toFunctor_2449_; lean_object* v_toPure_2450_; lean_object* v___f_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___f_2455_; lean_object* v___x_2456_; 
v_toApplicative_2447_ = lean_ctor_get(v_inst_2442_, 0);
lean_inc_ref(v_toApplicative_2447_);
v_toBind_2448_ = lean_ctor_get(v_inst_2442_, 1);
lean_inc_n(v_toBind_2448_, 2);
lean_dec_ref(v_inst_2442_);
v_toFunctor_2449_ = lean_ctor_get(v_toApplicative_2447_, 0);
lean_inc_ref(v_toFunctor_2449_);
v_toPure_2450_ = lean_ctor_get(v_toApplicative_2447_, 1);
lean_inc(v_toPure_2450_);
lean_dec_ref(v_toApplicative_2447_);
v___f_2451_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___closed__0));
v___x_2452_ = lean_unsigned_to_nat(0u);
v___x_2453_ = lean_obj_once(&l_Lake_withLoggedIO___redArg___closed__2, &l_Lake_withLoggedIO___redArg___closed__2_once, _init_l_Lake_withLoggedIO___redArg___closed__2);
lean_inc(v_inst_2443_);
v___x_2454_ = lean_apply_2(v_inst_2443_, lean_box(0), v___x_2453_);
v___f_2455_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__9), 10, 9);
lean_closure_set(v___f_2455_, 0, v_toPure_2450_);
lean_closure_set(v___f_2455_, 1, v___x_2452_);
lean_closure_set(v___f_2455_, 2, v_inst_2444_);
lean_closure_set(v___f_2455_, 3, v_toBind_2448_);
lean_closure_set(v___f_2455_, 4, v_inst_2443_);
lean_closure_set(v___f_2455_, 5, v_toFunctor_2449_);
lean_closure_set(v___f_2455_, 6, v_inst_2445_);
lean_closure_set(v___f_2455_, 7, v_x_2446_);
lean_closure_set(v___f_2455_, 8, v___f_2451_);
v___x_2456_ = lean_apply_4(v_toBind_2448_, lean_box(0), lean_box(0), v___x_2454_, v___f_2455_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_error___redArg___lam__3(lean_object* v_inst_2457_, lean_object* v___x_2458_, lean_object* v___f_2459_, lean_object* v_toBind_2460_, lean_object* v_iniPos_2461_){
_start:
{
lean_object* v_throw_2462_; lean_object* v_tryCatch_2463_; lean_object* v___f_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v_throw_2462_ = lean_ctor_get(v_inst_2457_, 0);
lean_inc(v_throw_2462_);
v_tryCatch_2463_ = lean_ctor_get(v_inst_2457_, 1);
lean_inc(v_tryCatch_2463_);
lean_dec_ref(v_inst_2457_);
v___f_2464_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2464_, 0, v_throw_2462_);
lean_closure_set(v___f_2464_, 1, v_iniPos_2461_);
v___x_2465_ = lean_apply_3(v_tryCatch_2463_, lean_box(0), v___x_2458_, v___f_2459_);
v___x_2466_ = lean_apply_4(v_toBind_2460_, lean_box(0), lean_box(0), v___x_2465_, v___f_2464_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_error___redArg(lean_object* v_inst_2467_, lean_object* v_inst_2468_, lean_object* v_inst_2469_, lean_object* v_inst_2470_, lean_object* v_msg_2471_){
_start:
{
lean_object* v_toApplicative_2472_; lean_object* v_toFunctor_2473_; lean_object* v_toBind_2474_; lean_object* v_toPure_2475_; lean_object* v_map_2476_; lean_object* v_get_2477_; lean_object* v___f_2478_; uint8_t v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___f_2482_; lean_object* v___f_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v_toApplicative_2472_ = lean_ctor_get(v_inst_2467_, 0);
lean_inc_ref(v_toApplicative_2472_);
v_toFunctor_2473_ = lean_ctor_get(v_toApplicative_2472_, 0);
lean_inc_ref(v_toFunctor_2473_);
v_toBind_2474_ = lean_ctor_get(v_inst_2467_, 1);
lean_inc_n(v_toBind_2474_, 2);
lean_dec_ref(v_inst_2467_);
v_toPure_2475_ = lean_ctor_get(v_toApplicative_2472_, 1);
lean_inc(v_toPure_2475_);
lean_dec_ref(v_toApplicative_2472_);
v_map_2476_ = lean_ctor_get(v_toFunctor_2473_, 0);
lean_inc(v_map_2476_);
lean_dec_ref(v_toFunctor_2473_);
v_get_2477_ = lean_ctor_get(v_inst_2469_, 0);
lean_inc(v_get_2477_);
lean_dec_ref(v_inst_2469_);
v___f_2478_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_2479_ = 3;
v___x_2480_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2480_, 0, v_msg_2471_);
lean_ctor_set_uint8(v___x_2480_, sizeof(void*)*1, v___x_2479_);
v___x_2481_ = lean_apply_1(v_inst_2468_, v___x_2480_);
v___f_2482_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2482_, 0, v_toPure_2475_);
v___f_2483_ = lean_alloc_closure((void*)(l_Lake_ELog_error___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2483_, 0, v_inst_2470_);
lean_closure_set(v___f_2483_, 1, v___x_2481_);
lean_closure_set(v___f_2483_, 2, v___f_2482_);
lean_closure_set(v___f_2483_, 3, v_toBind_2474_);
v___x_2484_ = lean_apply_4(v_map_2476_, lean_box(0), lean_box(0), v___f_2478_, v_get_2477_);
v___x_2485_ = lean_apply_4(v_toBind_2474_, lean_box(0), lean_box(0), v___x_2484_, v___f_2483_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_error(lean_object* v_m_2486_, lean_object* v_00_u03b1_2487_, lean_object* v_inst_2488_, lean_object* v_inst_2489_, lean_object* v_inst_2490_, lean_object* v_inst_2491_, lean_object* v_msg_2492_){
_start:
{
lean_object* v_toApplicative_2493_; lean_object* v_toFunctor_2494_; lean_object* v_toBind_2495_; lean_object* v_toPure_2496_; lean_object* v_map_2497_; lean_object* v_get_2498_; lean_object* v___f_2499_; uint8_t v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___f_2503_; lean_object* v___f_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v_toApplicative_2493_ = lean_ctor_get(v_inst_2488_, 0);
lean_inc_ref(v_toApplicative_2493_);
v_toFunctor_2494_ = lean_ctor_get(v_toApplicative_2493_, 0);
lean_inc_ref(v_toFunctor_2494_);
v_toBind_2495_ = lean_ctor_get(v_inst_2488_, 1);
lean_inc_n(v_toBind_2495_, 2);
lean_dec_ref(v_inst_2488_);
v_toPure_2496_ = lean_ctor_get(v_toApplicative_2493_, 1);
lean_inc(v_toPure_2496_);
lean_dec_ref(v_toApplicative_2493_);
v_map_2497_ = lean_ctor_get(v_toFunctor_2494_, 0);
lean_inc(v_map_2497_);
lean_dec_ref(v_toFunctor_2494_);
v_get_2498_ = lean_ctor_get(v_inst_2490_, 0);
lean_inc(v_get_2498_);
lean_dec_ref(v_inst_2490_);
v___f_2499_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_2500_ = 3;
v___x_2501_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2501_, 0, v_msg_2492_);
lean_ctor_set_uint8(v___x_2501_, sizeof(void*)*1, v___x_2500_);
v___x_2502_ = lean_apply_1(v_inst_2489_, v___x_2501_);
v___f_2503_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2503_, 0, v_toPure_2496_);
v___f_2504_ = lean_alloc_closure((void*)(l_Lake_ELog_error___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2504_, 0, v_inst_2491_);
lean_closure_set(v___f_2504_, 1, v___x_2502_);
lean_closure_set(v___f_2504_, 2, v___f_2503_);
lean_closure_set(v___f_2504_, 3, v_toBind_2495_);
v___x_2505_ = lean_apply_4(v_map_2497_, lean_box(0), lean_box(0), v___f_2499_, v_get_2498_);
v___x_2506_ = lean_apply_4(v_toBind_2495_, lean_box(0), lean_box(0), v___x_2505_, v___f_2504_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_monadError___redArg___lam__4(lean_object* v_inst_2507_, lean_object* v_inst_2508_, lean_object* v_inst_2509_, lean_object* v_inst_2510_, lean_object* v___f_2511_, lean_object* v_00_u03b1_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v_toApplicative_2514_; lean_object* v_toFunctor_2515_; lean_object* v_toBind_2516_; lean_object* v_toPure_2517_; lean_object* v_map_2518_; lean_object* v_get_2519_; uint8_t v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___f_2523_; lean_object* v___f_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v_toApplicative_2514_ = lean_ctor_get(v_inst_2507_, 0);
lean_inc_ref(v_toApplicative_2514_);
v_toFunctor_2515_ = lean_ctor_get(v_toApplicative_2514_, 0);
lean_inc_ref(v_toFunctor_2515_);
v_toBind_2516_ = lean_ctor_get(v_inst_2507_, 1);
lean_inc_n(v_toBind_2516_, 2);
lean_dec_ref(v_inst_2507_);
v_toPure_2517_ = lean_ctor_get(v_toApplicative_2514_, 1);
lean_inc(v_toPure_2517_);
lean_dec_ref(v_toApplicative_2514_);
v_map_2518_ = lean_ctor_get(v_toFunctor_2515_, 0);
lean_inc(v_map_2518_);
lean_dec_ref(v_toFunctor_2515_);
v_get_2519_ = lean_ctor_get(v_inst_2508_, 0);
lean_inc(v_get_2519_);
lean_dec_ref(v_inst_2508_);
v___x_2520_ = 3;
v___x_2521_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2521_, 0, v___y_2513_);
lean_ctor_set_uint8(v___x_2521_, sizeof(void*)*1, v___x_2520_);
v___x_2522_ = lean_apply_1(v_inst_2509_, v___x_2521_);
v___f_2523_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2523_, 0, v_toPure_2517_);
v___f_2524_ = lean_alloc_closure((void*)(l_Lake_ELog_error___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2524_, 0, v_inst_2510_);
lean_closure_set(v___f_2524_, 1, v___x_2522_);
lean_closure_set(v___f_2524_, 2, v___f_2523_);
lean_closure_set(v___f_2524_, 3, v_toBind_2516_);
v___x_2525_ = lean_apply_4(v_map_2518_, lean_box(0), lean_box(0), v___f_2511_, v_get_2519_);
v___x_2526_ = lean_apply_4(v_toBind_2516_, lean_box(0), lean_box(0), v___x_2525_, v___f_2524_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_monadError___redArg(lean_object* v_inst_2527_, lean_object* v_inst_2528_, lean_object* v_inst_2529_, lean_object* v_inst_2530_){
_start:
{
lean_object* v___f_2531_; lean_object* v___f_2532_; 
v___f_2531_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2532_ = lean_alloc_closure((void*)(l_Lake_ELog_monadError___redArg___lam__4), 7, 5);
lean_closure_set(v___f_2532_, 0, v_inst_2527_);
lean_closure_set(v___f_2532_, 1, v_inst_2529_);
lean_closure_set(v___f_2532_, 2, v_inst_2528_);
lean_closure_set(v___f_2532_, 3, v_inst_2530_);
lean_closure_set(v___f_2532_, 4, v___f_2531_);
return v___f_2532_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_monadError(lean_object* v_m_2533_, lean_object* v_inst_2534_, lean_object* v_inst_2535_, lean_object* v_inst_2536_, lean_object* v_inst_2537_){
_start:
{
lean_object* v___f_2538_; lean_object* v___f_2539_; 
v___f_2538_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2539_ = lean_alloc_closure((void*)(l_Lake_ELog_monadError___redArg___lam__4), 7, 5);
lean_closure_set(v___f_2539_, 0, v_inst_2534_);
lean_closure_set(v___f_2539_, 1, v_inst_2536_);
lean_closure_set(v___f_2539_, 2, v_inst_2535_);
lean_closure_set(v___f_2539_, 3, v_inst_2537_);
lean_closure_set(v___f_2539_, 4, v___f_2538_);
return v___f_2539_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_failure___redArg___lam__1(lean_object* v_inst_2540_, lean_object* v_____do__lift_2541_){
_start:
{
lean_object* v_throw_2542_; lean_object* v___x_2543_; 
v_throw_2542_ = lean_ctor_get(v_inst_2540_, 0);
lean_inc(v_throw_2542_);
lean_dec_ref(v_inst_2540_);
v___x_2543_ = lean_apply_2(v_throw_2542_, lean_box(0), v_____do__lift_2541_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_failure___redArg(lean_object* v_inst_2544_, lean_object* v_inst_2545_, lean_object* v_inst_2546_){
_start:
{
lean_object* v_toApplicative_2547_; lean_object* v_toFunctor_2548_; lean_object* v_toBind_2549_; lean_object* v_map_2550_; lean_object* v_get_2551_; lean_object* v___f_2552_; lean_object* v___f_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v_toApplicative_2547_ = lean_ctor_get(v_inst_2544_, 0);
v_toFunctor_2548_ = lean_ctor_get(v_toApplicative_2547_, 0);
lean_inc_ref(v_toFunctor_2548_);
v_toBind_2549_ = lean_ctor_get(v_inst_2544_, 1);
lean_inc(v_toBind_2549_);
lean_dec_ref(v_inst_2544_);
v_map_2550_ = lean_ctor_get(v_toFunctor_2548_, 0);
lean_inc(v_map_2550_);
lean_dec_ref(v_toFunctor_2548_);
v_get_2551_ = lean_ctor_get(v_inst_2545_, 0);
lean_inc(v_get_2551_);
lean_dec_ref(v_inst_2545_);
v___f_2552_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2553_ = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2553_, 0, v_inst_2546_);
v___x_2554_ = lean_apply_4(v_map_2550_, lean_box(0), lean_box(0), v___f_2552_, v_get_2551_);
v___x_2555_ = lean_apply_4(v_toBind_2549_, lean_box(0), lean_box(0), v___x_2554_, v___f_2553_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_failure(lean_object* v_m_2556_, lean_object* v_00_u03b1_2557_, lean_object* v_inst_2558_, lean_object* v_inst_2559_, lean_object* v_inst_2560_){
_start:
{
lean_object* v_toApplicative_2561_; lean_object* v_toFunctor_2562_; lean_object* v_toBind_2563_; lean_object* v_map_2564_; lean_object* v_get_2565_; lean_object* v___f_2566_; lean_object* v___f_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v_toApplicative_2561_ = lean_ctor_get(v_inst_2558_, 0);
v_toFunctor_2562_ = lean_ctor_get(v_toApplicative_2561_, 0);
lean_inc_ref(v_toFunctor_2562_);
v_toBind_2563_ = lean_ctor_get(v_inst_2558_, 1);
lean_inc(v_toBind_2563_);
lean_dec_ref(v_inst_2558_);
v_map_2564_ = lean_ctor_get(v_toFunctor_2562_, 0);
lean_inc(v_map_2564_);
lean_dec_ref(v_toFunctor_2562_);
v_get_2565_ = lean_ctor_get(v_inst_2559_, 0);
lean_inc(v_get_2565_);
lean_dec_ref(v_inst_2559_);
v___f_2566_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2567_ = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2567_, 0, v_inst_2560_);
v___x_2568_ = lean_apply_4(v_map_2564_, lean_box(0), lean_box(0), v___f_2566_, v_get_2565_);
v___x_2569_ = lean_apply_4(v_toBind_2563_, lean_box(0), lean_box(0), v___x_2568_, v___f_2567_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__0(lean_object* v_y_2570_, lean_object* v_____r_2571_){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2572_ = lean_box(0);
v___x_2573_ = lean_apply_1(v_y_2570_, v___x_2572_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__1(lean_object* v_errPos_2574_, lean_object* v_s_2575_){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2576_ = lean_box(0);
v___x_2577_ = l_Array_shrink___redArg(v_s_2575_, v_errPos_2574_);
v___x_2578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2576_);
lean_ctor_set(v___x_2578_, 1, v___x_2577_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__1___boxed(lean_object* v_errPos_2579_, lean_object* v_s_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l_Lake_ELog_orElse___redArg___lam__1(v_errPos_2579_, v_s_2580_);
lean_dec(v_errPos_2579_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__2(lean_object* v_inst_2582_, lean_object* v_toBind_2583_, lean_object* v___f_2584_, lean_object* v_errPos_2585_){
_start:
{
lean_object* v_modifyGet_2586_; lean_object* v___f_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v_modifyGet_2586_ = lean_ctor_get(v_inst_2582_, 2);
lean_inc(v_modifyGet_2586_);
lean_dec_ref(v_inst_2582_);
v___f_2587_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2587_, 0, v_errPos_2585_);
v___x_2588_ = lean_apply_2(v_modifyGet_2586_, lean_box(0), v___f_2587_);
v___x_2589_ = lean_apply_4(v_toBind_2583_, lean_box(0), lean_box(0), v___x_2588_, v___f_2584_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg(lean_object* v_inst_2590_, lean_object* v_inst_2591_, lean_object* v_inst_2592_, lean_object* v_x_2593_, lean_object* v_y_2594_){
_start:
{
lean_object* v_toBind_2595_; lean_object* v_tryCatch_2596_; lean_object* v___f_2597_; lean_object* v___f_2598_; lean_object* v___x_2599_; 
v_toBind_2595_ = lean_ctor_get(v_inst_2590_, 1);
lean_inc(v_toBind_2595_);
lean_dec_ref(v_inst_2590_);
v_tryCatch_2596_ = lean_ctor_get(v_inst_2592_, 1);
lean_inc(v_tryCatch_2596_);
lean_dec_ref(v_inst_2592_);
v___f_2597_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2597_, 0, v_y_2594_);
v___f_2598_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2598_, 0, v_inst_2591_);
lean_closure_set(v___f_2598_, 1, v_toBind_2595_);
lean_closure_set(v___f_2598_, 2, v___f_2597_);
v___x_2599_ = lean_apply_3(v_tryCatch_2596_, lean_box(0), v_x_2593_, v___f_2598_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse(lean_object* v_m_2600_, lean_object* v_00_u03b1_2601_, lean_object* v_inst_2602_, lean_object* v_inst_2603_, lean_object* v_inst_2604_, lean_object* v_x_2605_, lean_object* v_y_2606_){
_start:
{
lean_object* v_toBind_2607_; lean_object* v_tryCatch_2608_; lean_object* v___f_2609_; lean_object* v___f_2610_; lean_object* v___x_2611_; 
v_toBind_2607_ = lean_ctor_get(v_inst_2602_, 1);
lean_inc(v_toBind_2607_);
lean_dec_ref(v_inst_2602_);
v_tryCatch_2608_ = lean_ctor_get(v_inst_2604_, 1);
lean_inc(v_tryCatch_2608_);
lean_dec_ref(v_inst_2604_);
v___f_2609_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2609_, 0, v_y_2606_);
v___f_2610_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2610_, 0, v_inst_2603_);
lean_closure_set(v___f_2610_, 1, v_toBind_2607_);
lean_closure_set(v___f_2610_, 2, v___f_2609_);
v___x_2611_ = lean_apply_3(v_tryCatch_2608_, lean_box(0), v_x_2605_, v___f_2610_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__2(lean_object* v_toApplicative_2612_, lean_object* v_inst_2613_, lean_object* v___f_2614_, lean_object* v_toBind_2615_, lean_object* v___f_2616_, lean_object* v_00_u03b1_2617_){
_start:
{
lean_object* v_toFunctor_2618_; lean_object* v_map_2619_; lean_object* v_get_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v_toFunctor_2618_ = lean_ctor_get(v_toApplicative_2612_, 0);
lean_inc_ref(v_toFunctor_2618_);
lean_dec_ref(v_toApplicative_2612_);
v_map_2619_ = lean_ctor_get(v_toFunctor_2618_, 0);
lean_inc(v_map_2619_);
lean_dec_ref(v_toFunctor_2618_);
v_get_2620_ = lean_ctor_get(v_inst_2613_, 0);
lean_inc(v_get_2620_);
lean_dec_ref(v_inst_2613_);
v___x_2621_ = lean_apply_4(v_map_2619_, lean_box(0), lean_box(0), v___f_2614_, v_get_2620_);
v___x_2622_ = lean_apply_4(v_toBind_2615_, lean_box(0), lean_box(0), v___x_2621_, v___f_2616_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__0(lean_object* v___y_2623_, lean_object* v_____r_2624_){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2625_ = lean_box(0);
v___x_2626_ = lean_apply_1(v___y_2623_, v___x_2625_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__4(lean_object* v_inst_2627_, lean_object* v_inst_2628_, lean_object* v_toBind_2629_, lean_object* v_00_u03b1_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v_tryCatch_2633_; lean_object* v___f_2634_; lean_object* v___f_2635_; lean_object* v___x_2636_; 
v_tryCatch_2633_ = lean_ctor_get(v_inst_2627_, 1);
lean_inc(v_tryCatch_2633_);
lean_dec_ref(v_inst_2627_);
v___f_2634_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2634_, 0, v___y_2632_);
v___f_2635_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2635_, 0, v_inst_2628_);
lean_closure_set(v___f_2635_, 1, v_toBind_2629_);
lean_closure_set(v___f_2635_, 2, v___f_2634_);
v___x_2636_ = lean_apply_3(v_tryCatch_2633_, lean_box(0), v___y_2631_, v___f_2635_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg(lean_object* v_inst_2637_, lean_object* v_inst_2638_, lean_object* v_inst_2639_){
_start:
{
lean_object* v_toApplicative_2640_; lean_object* v_toBind_2641_; lean_object* v___f_2642_; lean_object* v___f_2643_; lean_object* v___f_2644_; lean_object* v___f_2645_; lean_object* v___x_2646_; 
v_toApplicative_2640_ = lean_ctor_get(v_inst_2637_, 0);
lean_inc_ref_n(v_toApplicative_2640_, 2);
v_toBind_2641_ = lean_ctor_get(v_inst_2637_, 1);
lean_inc_n(v_toBind_2641_, 2);
lean_dec_ref(v_inst_2637_);
v___f_2642_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
lean_inc_ref(v_inst_2639_);
v___f_2643_ = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2643_, 0, v_inst_2639_);
lean_inc_ref(v_inst_2638_);
v___f_2644_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2644_, 0, v_toApplicative_2640_);
lean_closure_set(v___f_2644_, 1, v_inst_2638_);
lean_closure_set(v___f_2644_, 2, v___f_2642_);
lean_closure_set(v___f_2644_, 3, v_toBind_2641_);
lean_closure_set(v___f_2644_, 4, v___f_2643_);
v___f_2645_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__4), 6, 3);
lean_closure_set(v___f_2645_, 0, v_inst_2639_);
lean_closure_set(v___f_2645_, 1, v_inst_2638_);
lean_closure_set(v___f_2645_, 2, v_toBind_2641_);
v___x_2646_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2646_, 0, v_toApplicative_2640_);
lean_ctor_set(v___x_2646_, 1, v___f_2644_);
lean_ctor_set(v___x_2646_, 2, v___f_2645_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative(lean_object* v_m_2647_, lean_object* v_inst_2648_, lean_object* v_inst_2649_, lean_object* v_inst_2650_){
_start:
{
lean_object* v_toApplicative_2651_; lean_object* v_toBind_2652_; lean_object* v___f_2653_; lean_object* v___f_2654_; lean_object* v___f_2655_; lean_object* v___f_2656_; lean_object* v___x_2657_; 
v_toApplicative_2651_ = lean_ctor_get(v_inst_2648_, 0);
lean_inc_ref_n(v_toApplicative_2651_, 2);
v_toBind_2652_ = lean_ctor_get(v_inst_2648_, 1);
lean_inc_n(v_toBind_2652_, 2);
lean_dec_ref(v_inst_2648_);
v___f_2653_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
lean_inc_ref(v_inst_2650_);
v___f_2654_ = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2654_, 0, v_inst_2650_);
lean_inc_ref(v_inst_2649_);
v___f_2655_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2655_, 0, v_toApplicative_2651_);
lean_closure_set(v___f_2655_, 1, v_inst_2649_);
lean_closure_set(v___f_2655_, 2, v___f_2653_);
lean_closure_set(v___f_2655_, 3, v_toBind_2652_);
lean_closure_set(v___f_2655_, 4, v___f_2654_);
v___f_2656_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__4), 6, 3);
lean_closure_set(v___f_2656_, 0, v_inst_2650_);
lean_closure_set(v___f_2656_, 1, v_inst_2649_);
lean_closure_set(v___f_2656_, 2, v_toBind_2652_);
v___x_2657_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2657_, 0, v_toApplicative_2651_);
lean_ctor_set(v___x_2657_, 1, v___f_2655_);
lean_ctor_set(v___x_2657_, 2, v___f_2656_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogLogTOfMonad___redArg(lean_object* v_inst_2658_){
_start:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2659_ = l_instMonadStateOfStateTOfMonad___redArg(v_inst_2658_);
v___x_2660_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(v___x_2660_, 0, lean_box(0));
lean_closure_set(v___x_2660_, 1, v___x_2659_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogLogTOfMonad(lean_object* v_m_2661_, lean_object* v_inst_2662_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l_Lake_instMonadLogLogTOfMonad___redArg(v_inst_2662_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run___redArg(lean_object* v_self_2664_, lean_object* v_log_2665_){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = lean_apply_1(v_self_2664_, v_log_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run(lean_object* v_m_2667_, lean_object* v_00_u03b1_2668_, lean_object* v_self_2669_, lean_object* v_log_2670_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = lean_apply_1(v_self_2669_, v_log_2670_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg___lam__0(lean_object* v_x_2672_){
_start:
{
lean_object* v_fst_2673_; 
v_fst_2673_ = lean_ctor_get(v_x_2672_, 0);
lean_inc(v_fst_2673_);
return v_fst_2673_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg___lam__0___boxed(lean_object* v_x_2674_){
_start:
{
lean_object* v_res_2675_; 
v_res_2675_ = l_Lake_LogT_run_x27___redArg___lam__0(v_x_2674_);
lean_dec_ref(v_x_2674_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg(lean_object* v_inst_2677_, lean_object* v_self_2678_, lean_object* v_log_2679_){
_start:
{
lean_object* v_map_2680_; lean_object* v___f_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v_map_2680_ = lean_ctor_get(v_inst_2677_, 0);
lean_inc(v_map_2680_);
lean_dec_ref(v_inst_2677_);
v___f_2681_ = ((lean_object*)(l_Lake_LogT_run_x27___redArg___closed__0));
v___x_2682_ = lean_apply_1(v_self_2678_, v_log_2679_);
v___x_2683_ = lean_apply_4(v_map_2680_, lean_box(0), lean_box(0), v___f_2681_, v___x_2682_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27(lean_object* v_m_2684_, lean_object* v_00_u03b1_2685_, lean_object* v_inst_2686_, lean_object* v_self_2687_, lean_object* v_log_2688_){
_start:
{
lean_object* v_map_2689_; lean_object* v___f_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v_map_2689_ = lean_ctor_get(v_inst_2686_, 0);
lean_inc(v_map_2689_);
lean_dec_ref(v_inst_2686_);
v___f_2690_ = ((lean_object*)(l_Lake_LogT_run_x27___redArg___closed__0));
v___x_2691_ = lean_apply_1(v_self_2687_, v_log_2688_);
v___x_2692_ = lean_apply_4(v_map_2689_, lean_box(0), lean_box(0), v___f_2690_, v___x_2691_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__1(lean_object* v_toPure_2693_, lean_object* v_fst_2694_, lean_object* v_____r_2695_){
_start:
{
lean_object* v___x_2696_; 
v___x_2696_ = lean_apply_2(v_toPure_2693_, lean_box(0), v_fst_2694_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__0(lean_object* v_toPure_2697_, lean_object* v_set_2698_, lean_object* v_toBind_2699_, lean_object* v_____x_2700_){
_start:
{
lean_object* v_fst_2701_; lean_object* v_snd_2702_; lean_object* v___f_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v_fst_2701_ = lean_ctor_get(v_____x_2700_, 0);
lean_inc(v_fst_2701_);
v_snd_2702_ = lean_ctor_get(v_____x_2700_, 1);
lean_inc(v_snd_2702_);
lean_dec_ref(v_____x_2700_);
v___f_2703_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2703_, 0, v_toPure_2697_);
lean_closure_set(v___f_2703_, 1, v_fst_2701_);
v___x_2704_ = lean_apply_1(v_set_2698_, v_snd_2702_);
v___x_2705_ = lean_apply_4(v_toBind_2699_, lean_box(0), lean_box(0), v___x_2704_, v___f_2703_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__2(lean_object* v_self_2706_, lean_object* v_inst_2707_, lean_object* v_toBind_2708_, lean_object* v___f_2709_, lean_object* v_____do__lift_2710_){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2711_ = lean_apply_1(v_self_2706_, v_____do__lift_2710_);
v___x_2712_ = lean_apply_2(v_inst_2707_, lean_box(0), v___x_2711_);
v___x_2713_ = lean_apply_4(v_toBind_2708_, lean_box(0), lean_box(0), v___x_2712_, v___f_2709_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg(lean_object* v_inst_2714_, lean_object* v_inst_2715_, lean_object* v_inst_2716_, lean_object* v_self_2717_){
_start:
{
lean_object* v_toApplicative_2718_; lean_object* v_toBind_2719_; lean_object* v_set_2720_; lean_object* v_modifyGet_2721_; lean_object* v_toPure_2722_; lean_object* v___f_2723_; lean_object* v___x_2724_; lean_object* v___f_2725_; lean_object* v___f_2726_; lean_object* v___x_2727_; 
v_toApplicative_2718_ = lean_ctor_get(v_inst_2714_, 0);
lean_inc_ref(v_toApplicative_2718_);
v_toBind_2719_ = lean_ctor_get(v_inst_2714_, 1);
lean_inc_n(v_toBind_2719_, 3);
lean_dec_ref(v_inst_2714_);
v_set_2720_ = lean_ctor_get(v_inst_2715_, 1);
lean_inc(v_set_2720_);
v_modifyGet_2721_ = lean_ctor_get(v_inst_2715_, 2);
lean_inc(v_modifyGet_2721_);
lean_dec_ref(v_inst_2715_);
v_toPure_2722_ = lean_ctor_get(v_toApplicative_2718_, 1);
lean_inc(v_toPure_2722_);
lean_dec_ref(v_toApplicative_2718_);
v___f_2723_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_2724_ = lean_apply_2(v_modifyGet_2721_, lean_box(0), v___f_2723_);
v___f_2725_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2725_, 0, v_toPure_2722_);
lean_closure_set(v___f_2725_, 1, v_set_2720_);
lean_closure_set(v___f_2725_, 2, v_toBind_2719_);
v___f_2726_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2726_, 0, v_self_2717_);
lean_closure_set(v___f_2726_, 1, v_inst_2716_);
lean_closure_set(v___f_2726_, 2, v_toBind_2719_);
lean_closure_set(v___f_2726_, 3, v___f_2725_);
v___x_2727_ = lean_apply_4(v_toBind_2719_, lean_box(0), lean_box(0), v___x_2724_, v___f_2726_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun(lean_object* v_n_2728_, lean_object* v_m_2729_, lean_object* v_00_u03b1_2730_, lean_object* v_inst_2731_, lean_object* v_inst_2732_, lean_object* v_inst_2733_, lean_object* v_inst_2734_, lean_object* v_self_2735_){
_start:
{
lean_object* v_toApplicative_2736_; lean_object* v_toBind_2737_; lean_object* v_set_2738_; lean_object* v_modifyGet_2739_; lean_object* v_toPure_2740_; lean_object* v___f_2741_; lean_object* v___x_2742_; lean_object* v___f_2743_; lean_object* v___f_2744_; lean_object* v___x_2745_; 
v_toApplicative_2736_ = lean_ctor_get(v_inst_2731_, 0);
lean_inc_ref(v_toApplicative_2736_);
v_toBind_2737_ = lean_ctor_get(v_inst_2731_, 1);
lean_inc_n(v_toBind_2737_, 3);
lean_dec_ref(v_inst_2731_);
v_set_2738_ = lean_ctor_get(v_inst_2732_, 1);
lean_inc(v_set_2738_);
v_modifyGet_2739_ = lean_ctor_get(v_inst_2732_, 2);
lean_inc(v_modifyGet_2739_);
lean_dec_ref(v_inst_2732_);
v_toPure_2740_ = lean_ctor_get(v_toApplicative_2736_, 1);
lean_inc(v_toPure_2740_);
lean_dec_ref(v_toApplicative_2736_);
v___f_2741_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_2742_ = lean_apply_2(v_modifyGet_2739_, lean_box(0), v___f_2741_);
v___f_2743_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2743_, 0, v_toPure_2740_);
lean_closure_set(v___f_2743_, 1, v_set_2738_);
lean_closure_set(v___f_2743_, 2, v_toBind_2737_);
v___f_2744_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2744_, 0, v_self_2735_);
lean_closure_set(v___f_2744_, 1, v_inst_2733_);
lean_closure_set(v___f_2744_, 2, v_toBind_2737_);
lean_closure_set(v___f_2744_, 3, v___f_2743_);
v___x_2745_ = lean_apply_4(v_toBind_2737_, lean_box(0), lean_box(0), v___x_2742_, v___f_2744_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___boxed(lean_object* v_n_2746_, lean_object* v_m_2747_, lean_object* v_00_u03b1_2748_, lean_object* v_inst_2749_, lean_object* v_inst_2750_, lean_object* v_inst_2751_, lean_object* v_inst_2752_, lean_object* v_self_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l_Lake_LogT_takeAndRun(v_n_2746_, v_m_2747_, v_00_u03b1_2748_, v_inst_2749_, v_inst_2750_, v_inst_2751_, v_inst_2752_, v_self_2753_);
lean_dec(v_inst_2752_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg___lam__2(lean_object* v_toPure_2755_, lean_object* v___x_2756_, lean_object* v_toBind_2757_, lean_object* v_inst_2758_, lean_object* v___f_2759_, lean_object* v_____x_2760_){
_start:
{
lean_object* v_fst_2761_; lean_object* v_snd_2762_; lean_object* v___f_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; uint8_t v___x_2766_; 
v_fst_2761_ = lean_ctor_get(v_____x_2760_, 0);
lean_inc(v_fst_2761_);
v_snd_2762_ = lean_ctor_get(v_____x_2760_, 1);
lean_inc(v_snd_2762_);
lean_dec_ref(v_____x_2760_);
lean_inc(v_toPure_2755_);
v___f_2763_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2763_, 0, v_toPure_2755_);
lean_closure_set(v___f_2763_, 1, v_fst_2761_);
v___x_2764_ = lean_array_get_size(v_snd_2762_);
v___x_2765_ = lean_box(0);
v___x_2766_ = lean_nat_dec_lt(v___x_2756_, v___x_2764_);
if (v___x_2766_ == 0)
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
lean_dec(v_snd_2762_);
lean_dec(v___f_2759_);
lean_dec_ref(v_inst_2758_);
v___x_2767_ = lean_apply_2(v_toPure_2755_, lean_box(0), v___x_2765_);
v___x_2768_ = lean_apply_4(v_toBind_2757_, lean_box(0), lean_box(0), v___x_2767_, v___f_2763_);
return v___x_2768_;
}
else
{
uint8_t v___x_2769_; 
v___x_2769_ = lean_nat_dec_le(v___x_2764_, v___x_2764_);
if (v___x_2769_ == 0)
{
if (v___x_2766_ == 0)
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
lean_dec(v_snd_2762_);
lean_dec(v___f_2759_);
lean_dec_ref(v_inst_2758_);
v___x_2770_ = lean_apply_2(v_toPure_2755_, lean_box(0), v___x_2765_);
v___x_2771_ = lean_apply_4(v_toBind_2757_, lean_box(0), lean_box(0), v___x_2770_, v___f_2763_);
return v___x_2771_;
}
else
{
size_t v___x_2772_; size_t v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
lean_dec(v_toPure_2755_);
v___x_2772_ = ((size_t)0ULL);
v___x_2773_ = lean_usize_of_nat(v___x_2764_);
v___x_2774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2758_, v___f_2759_, v_snd_2762_, v___x_2772_, v___x_2773_, v___x_2765_);
v___x_2775_ = lean_apply_4(v_toBind_2757_, lean_box(0), lean_box(0), v___x_2774_, v___f_2763_);
return v___x_2775_;
}
}
else
{
size_t v___x_2776_; size_t v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
lean_dec(v_toPure_2755_);
v___x_2776_ = ((size_t)0ULL);
v___x_2777_ = lean_usize_of_nat(v___x_2764_);
v___x_2778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2758_, v___f_2759_, v_snd_2762_, v___x_2776_, v___x_2777_, v___x_2765_);
v___x_2779_ = lean_apply_4(v_toBind_2757_, lean_box(0), lean_box(0), v___x_2778_, v___f_2763_);
return v___x_2779_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg___lam__2___boxed(lean_object* v_toPure_2780_, lean_object* v___x_2781_, lean_object* v_toBind_2782_, lean_object* v_inst_2783_, lean_object* v___f_2784_, lean_object* v_____x_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Lake_LogT_replayLog___redArg___lam__2(v_toPure_2780_, v___x_2781_, v_toBind_2782_, v_inst_2783_, v___f_2784_, v_____x_2785_);
lean_dec(v___x_2781_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg(lean_object* v_inst_2787_, lean_object* v_logger_2788_, lean_object* v_inst_2789_, lean_object* v_self_2790_){
_start:
{
lean_object* v_toApplicative_2791_; lean_object* v_toBind_2792_; lean_object* v_toPure_2793_; lean_object* v___f_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___f_2799_; lean_object* v___x_2800_; 
v_toApplicative_2791_ = lean_ctor_get(v_inst_2787_, 0);
v_toBind_2792_ = lean_ctor_get(v_inst_2787_, 1);
lean_inc_n(v_toBind_2792_, 2);
v_toPure_2793_ = lean_ctor_get(v_toApplicative_2791_, 1);
lean_inc(v_toPure_2793_);
v___f_2794_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2794_, 0, v_logger_2788_);
v___x_2795_ = lean_unsigned_to_nat(0u);
v___x_2796_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_2797_ = lean_apply_1(v_self_2790_, v___x_2796_);
v___x_2798_ = lean_apply_2(v_inst_2789_, lean_box(0), v___x_2797_);
v___f_2799_ = lean_alloc_closure((void*)(l_Lake_LogT_replayLog___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_2799_, 0, v_toPure_2793_);
lean_closure_set(v___f_2799_, 1, v___x_2795_);
lean_closure_set(v___f_2799_, 2, v_toBind_2792_);
lean_closure_set(v___f_2799_, 3, v_inst_2787_);
lean_closure_set(v___f_2799_, 4, v___f_2794_);
v___x_2800_ = lean_apply_4(v_toBind_2792_, lean_box(0), lean_box(0), v___x_2798_, v___f_2799_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog(lean_object* v_n_2801_, lean_object* v_m_2802_, lean_object* v_00_u03b1_2803_, lean_object* v_inst_2804_, lean_object* v_logger_2805_, lean_object* v_inst_2806_, lean_object* v_self_2807_){
_start:
{
lean_object* v_toApplicative_2808_; lean_object* v_toBind_2809_; lean_object* v_toPure_2810_; lean_object* v___f_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___f_2816_; lean_object* v___x_2817_; 
v_toApplicative_2808_ = lean_ctor_get(v_inst_2804_, 0);
v_toBind_2809_ = lean_ctor_get(v_inst_2804_, 1);
lean_inc_n(v_toBind_2809_, 2);
v_toPure_2810_ = lean_ctor_get(v_toApplicative_2808_, 1);
lean_inc(v_toPure_2810_);
v___f_2811_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2811_, 0, v_logger_2805_);
v___x_2812_ = lean_unsigned_to_nat(0u);
v___x_2813_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_2814_ = lean_apply_1(v_self_2807_, v___x_2813_);
v___x_2815_ = lean_apply_2(v_inst_2806_, lean_box(0), v___x_2814_);
v___f_2816_ = lean_alloc_closure((void*)(l_Lake_LogT_replayLog___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_2816_, 0, v_toPure_2810_);
lean_closure_set(v___f_2816_, 1, v___x_2812_);
lean_closure_set(v___f_2816_, 2, v_toBind_2809_);
lean_closure_set(v___f_2816_, 3, v_inst_2804_);
lean_closure_set(v___f_2816_, 4, v___f_2811_);
v___x_2817_ = lean_apply_4(v_toBind_2809_, lean_box(0), lean_box(0), v___x_2815_, v___f_2816_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogELogTOfMonad___redArg(lean_object* v_inst_2818_){
_start:
{
lean_object* v_toApplicative_2819_; lean_object* v_toPure_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v_toApplicative_2819_ = lean_ctor_get(v_inst_2818_, 0);
lean_inc_ref(v_toApplicative_2819_);
lean_dec_ref(v_inst_2818_);
v_toPure_2820_ = lean_ctor_get(v_toApplicative_2819_, 1);
lean_inc(v_toPure_2820_);
lean_dec_ref(v_toApplicative_2819_);
v___x_2821_ = l_Lake_EStateT_instMonadStateOfOfPure___redArg(v_toPure_2820_);
v___x_2822_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(v___x_2822_, 0, lean_box(0));
lean_closure_set(v___x_2822_, 1, v___x_2821_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogELogTOfMonad(lean_object* v_m_2823_, lean_object* v_inst_2824_){
_start:
{
lean_object* v___x_2825_; 
v___x_2825_ = l_Lake_instMonadLogELogTOfMonad___redArg(v_inst_2824_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__0(lean_object* v_x_2826_){
_start:
{
if (lean_obj_tag(v_x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2836_; 
v_a_2827_ = lean_ctor_get(v_x_2826_, 0);
v_a_2828_ = lean_ctor_get(v_x_2826_, 1);
v_isSharedCheck_2836_ = !lean_is_exclusive(v_x_2826_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2830_ = v_x_2826_;
v_isShared_2831_ = v_isSharedCheck_2836_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_inc(v_a_2827_);
lean_dec(v_x_2826_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2836_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2832_; lean_object* v___x_2834_; 
v___x_2832_ = lean_array_get_size(v_a_2827_);
lean_dec(v_a_2827_);
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 0, v___x_2832_);
v___x_2834_ = v___x_2830_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v___x_2832_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v_a_2828_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
else
{
lean_object* v_a_2837_; lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
v_a_2837_ = lean_ctor_get(v_x_2826_, 0);
v_a_2838_ = lean_ctor_get(v_x_2826_, 1);
v_isSharedCheck_2845_ = !lean_is_exclusive(v_x_2826_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v_x_2826_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_inc(v_a_2837_);
lean_dec(v_x_2826_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2837_);
lean_ctor_set(v_reuseFailAlloc_2844_, 1, v_a_2838_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__1(lean_object* v_a_2846_, lean_object* v_toPure_2847_, lean_object* v_____do__lift_2848_){
_start:
{
if (lean_obj_tag(v_____do__lift_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2857_; 
v_a_2849_ = lean_ctor_get(v_____do__lift_2848_, 1);
v_isSharedCheck_2857_ = !lean_is_exclusive(v_____do__lift_2848_);
if (v_isSharedCheck_2857_ == 0)
{
lean_object* v_unused_2858_; 
v_unused_2858_ = lean_ctor_get(v_____do__lift_2848_, 0);
lean_dec(v_unused_2858_);
v___x_2851_ = v_____do__lift_2848_;
v_isShared_2852_ = v_isSharedCheck_2857_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v_____do__lift_2848_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2857_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
lean_ctor_set_tag(v___x_2851_, 1);
lean_ctor_set(v___x_2851_, 0, v_a_2846_);
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2846_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
lean_object* v___x_2855_; 
v___x_2855_ = lean_apply_2(v_toPure_2847_, lean_box(0), v___x_2854_);
return v___x_2855_;
}
}
}
else
{
lean_object* v_a_2859_; lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2868_; 
lean_dec(v_a_2846_);
v_a_2859_ = lean_ctor_get(v_____do__lift_2848_, 0);
v_a_2860_ = lean_ctor_get(v_____do__lift_2848_, 1);
v_isSharedCheck_2868_ = !lean_is_exclusive(v_____do__lift_2848_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2862_ = v_____do__lift_2848_;
v_isShared_2863_ = v_isSharedCheck_2868_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_inc(v_a_2859_);
lean_dec(v_____do__lift_2848_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2868_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2859_);
lean_ctor_set(v_reuseFailAlloc_2867_, 1, v_a_2860_);
v___x_2865_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
lean_object* v___x_2866_; 
v___x_2866_ = lean_apply_2(v_toPure_2847_, lean_box(0), v___x_2865_);
return v___x_2866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__2(lean_object* v_toPure_2869_, lean_object* v___x_2870_, lean_object* v_____do__lift_2871_){
_start:
{
if (lean_obj_tag(v_____do__lift_2871_) == 0)
{
lean_object* v___x_2872_; 
v___x_2872_ = lean_apply_2(v_toPure_2869_, lean_box(0), v_____do__lift_2871_);
return v___x_2872_;
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2881_; 
v_a_2873_ = lean_ctor_get(v_____do__lift_2871_, 1);
v_isSharedCheck_2881_ = !lean_is_exclusive(v_____do__lift_2871_);
if (v_isSharedCheck_2881_ == 0)
{
lean_object* v_unused_2882_; 
v_unused_2882_ = lean_ctor_get(v_____do__lift_2871_, 0);
lean_dec(v_unused_2882_);
v___x_2875_ = v_____do__lift_2871_;
v_isShared_2876_ = v_isSharedCheck_2881_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v_____do__lift_2871_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2881_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2878_; 
if (v_isShared_2876_ == 0)
{
lean_ctor_set_tag(v___x_2875_, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2870_);
v___x_2878_ = v___x_2875_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2870_);
lean_ctor_set(v_reuseFailAlloc_2880_, 1, v_a_2873_);
v___x_2878_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
lean_object* v___x_2879_; 
v___x_2879_ = lean_apply_2(v_toPure_2869_, lean_box(0), v___x_2878_);
return v___x_2879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__3(lean_object* v_toPure_2883_, lean_object* v___x_2884_, lean_object* v_toBind_2885_, lean_object* v_____do__lift_2886_){
_start:
{
if (lean_obj_tag(v_____do__lift_2886_) == 0)
{
lean_object* v_a_2887_; lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2902_; 
v_a_2887_ = lean_ctor_get(v_____do__lift_2886_, 0);
v_a_2888_ = lean_ctor_get(v_____do__lift_2886_, 1);
v_isSharedCheck_2902_ = !lean_is_exclusive(v_____do__lift_2886_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2890_ = v_____do__lift_2886_;
v_isShared_2891_ = v_isSharedCheck_2902_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_inc(v_a_2887_);
lean_dec(v_____do__lift_2886_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2902_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___f_2892_; lean_object* v___x_2893_; lean_object* v___f_2894_; lean_object* v___x_2895_; lean_object* v___x_2897_; 
lean_inc_n(v_toPure_2883_, 2);
v___f_2892_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2892_, 0, v_a_2887_);
lean_closure_set(v___f_2892_, 1, v_toPure_2883_);
v___x_2893_ = lean_box(0);
v___f_2894_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2894_, 0, v_toPure_2883_);
lean_closure_set(v___f_2894_, 1, v___x_2893_);
v___x_2895_ = lean_array_push(v_a_2888_, v___x_2884_);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 1, v___x_2895_);
lean_ctor_set(v___x_2890_, 0, v___x_2893_);
v___x_2897_ = v___x_2890_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2893_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v___x_2895_);
v___x_2897_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2898_ = lean_apply_2(v_toPure_2883_, lean_box(0), v___x_2897_);
lean_inc(v_toBind_2885_);
v___x_2899_ = lean_apply_4(v_toBind_2885_, lean_box(0), lean_box(0), v___x_2898_, v___f_2894_);
v___x_2900_ = lean_apply_4(v_toBind_2885_, lean_box(0), lean_box(0), v___x_2899_, v___f_2892_);
return v___x_2900_;
}
}
}
else
{
lean_object* v_a_2903_; lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2912_; 
lean_dec(v_toBind_2885_);
lean_dec_ref(v___x_2884_);
v_a_2903_ = lean_ctor_get(v_____do__lift_2886_, 0);
v_a_2904_ = lean_ctor_get(v_____do__lift_2886_, 1);
v_isSharedCheck_2912_ = !lean_is_exclusive(v_____do__lift_2886_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2906_ = v_____do__lift_2886_;
v_isShared_2907_ = v_isSharedCheck_2912_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_inc(v_a_2903_);
lean_dec(v_____do__lift_2886_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2912_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2903_);
lean_ctor_set(v_reuseFailAlloc_2911_, 1, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
lean_object* v___x_2910_; 
v___x_2910_ = lean_apply_2(v_toPure_2883_, lean_box(0), v___x_2909_);
return v___x_2910_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__4(lean_object* v_toFunctor_2913_, lean_object* v_toPure_2914_, lean_object* v_toBind_2915_, lean_object* v___f_2916_, lean_object* v_00_u03b1_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v_map_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2933_; 
v_map_2920_ = lean_ctor_get(v_toFunctor_2913_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v_toFunctor_2913_);
if (v_isSharedCheck_2933_ == 0)
{
lean_object* v_unused_2934_; 
v_unused_2934_ = lean_ctor_get(v_toFunctor_2913_, 1);
lean_dec(v_unused_2934_);
v___x_2922_ = v_toFunctor_2913_;
v_isShared_2923_ = v_isSharedCheck_2933_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_map_2920_);
lean_dec(v_toFunctor_2913_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2933_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
uint8_t v___x_2924_; lean_object* v___x_2925_; lean_object* v___f_2926_; lean_object* v___x_2928_; 
v___x_2924_ = 3;
v___x_2925_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2925_, 0, v___y_2918_);
lean_ctor_set_uint8(v___x_2925_, sizeof(void*)*1, v___x_2924_);
lean_inc(v_toBind_2915_);
lean_inc(v_toPure_2914_);
v___f_2926_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__3), 4, 3);
lean_closure_set(v___f_2926_, 0, v_toPure_2914_);
lean_closure_set(v___f_2926_, 1, v___x_2925_);
lean_closure_set(v___f_2926_, 2, v_toBind_2915_);
lean_inc_ref(v___y_2919_);
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 1, v___y_2919_);
lean_ctor_set(v___x_2922_, 0, v___y_2919_);
v___x_2928_ = v___x_2922_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v___y_2919_);
lean_ctor_set(v_reuseFailAlloc_2932_, 1, v___y_2919_);
v___x_2928_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2929_ = lean_apply_2(v_toPure_2914_, lean_box(0), v___x_2928_);
v___x_2930_ = lean_apply_4(v_map_2920_, lean_box(0), lean_box(0), v___f_2916_, v___x_2929_);
v___x_2931_ = lean_apply_4(v_toBind_2915_, lean_box(0), lean_box(0), v___x_2930_, v___f_2926_);
return v___x_2931_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg(lean_object* v_inst_2936_){
_start:
{
lean_object* v_toApplicative_2937_; lean_object* v_toBind_2938_; lean_object* v_toFunctor_2939_; lean_object* v_toPure_2940_; lean_object* v___f_2941_; lean_object* v___f_2942_; 
v_toApplicative_2937_ = lean_ctor_get(v_inst_2936_, 0);
lean_inc_ref(v_toApplicative_2937_);
v_toBind_2938_ = lean_ctor_get(v_inst_2936_, 1);
lean_inc(v_toBind_2938_);
lean_dec_ref(v_inst_2936_);
v_toFunctor_2939_ = lean_ctor_get(v_toApplicative_2937_, 0);
lean_inc_ref(v_toFunctor_2939_);
v_toPure_2940_ = lean_ctor_get(v_toApplicative_2937_, 1);
lean_inc(v_toPure_2940_);
lean_dec_ref(v_toApplicative_2937_);
v___f_2941_ = ((lean_object*)(l_Lake_instMonadErrorELogTOfMonad___redArg___closed__0));
v___f_2942_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__4), 7, 4);
lean_closure_set(v___f_2942_, 0, v_toFunctor_2939_);
lean_closure_set(v___f_2942_, 1, v_toPure_2940_);
lean_closure_set(v___f_2942_, 2, v_toBind_2938_);
lean_closure_set(v___f_2942_, 3, v___f_2941_);
return v___f_2942_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad(lean_object* v_m_2943_, lean_object* v_inst_2944_){
_start:
{
lean_object* v___x_2945_; 
v___x_2945_ = l_Lake_instMonadErrorELogTOfMonad___redArg(v_inst_2944_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__1(lean_object* v___y_2946_, lean_object* v___x_2947_, lean_object* v_toPure_2948_, lean_object* v_____do__lift_2949_){
_start:
{
if (lean_obj_tag(v_____do__lift_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v___x_2951_; 
lean_dec(v_toPure_2948_);
v_a_2950_ = lean_ctor_get(v_____do__lift_2949_, 1);
lean_inc(v_a_2950_);
lean_dec_ref(v_____do__lift_2949_);
v___x_2951_ = lean_apply_2(v___y_2946_, v___x_2947_, v_a_2950_);
return v___x_2951_;
}
else
{
lean_object* v_a_2952_; lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2961_; 
lean_dec(v___y_2946_);
v_a_2952_ = lean_ctor_get(v_____do__lift_2949_, 0);
v_a_2953_ = lean_ctor_get(v_____do__lift_2949_, 1);
v_isSharedCheck_2961_ = !lean_is_exclusive(v_____do__lift_2949_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2955_ = v_____do__lift_2949_;
v_isShared_2956_ = v_isSharedCheck_2961_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_inc(v_a_2952_);
lean_dec(v_____do__lift_2949_);
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
v___x_2959_ = lean_apply_2(v_toPure_2948_, lean_box(0), v___x_2958_);
return v___x_2959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__0(lean_object* v_toPure_2962_, lean_object* v___y_2963_, lean_object* v_toBind_2964_, lean_object* v_____do__lift_2965_){
_start:
{
if (lean_obj_tag(v_____do__lift_2965_) == 0)
{
lean_object* v___x_2966_; 
lean_dec(v_toBind_2964_);
lean_dec(v___y_2963_);
v___x_2966_ = lean_apply_2(v_toPure_2962_, lean_box(0), v_____do__lift_2965_);
return v___x_2966_;
}
else
{
lean_object* v_a_2967_; lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2980_; 
v_a_2967_ = lean_ctor_get(v_____do__lift_2965_, 0);
v_a_2968_ = lean_ctor_get(v_____do__lift_2965_, 1);
v_isSharedCheck_2980_ = !lean_is_exclusive(v_____do__lift_2965_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2970_ = v_____do__lift_2965_;
v_isShared_2971_ = v_isSharedCheck_2980_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_inc(v_a_2967_);
lean_dec(v_____do__lift_2965_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2980_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2972_; lean_object* v___f_2973_; lean_object* v___x_2974_; lean_object* v___x_2976_; 
v___x_2972_ = lean_box(0);
lean_inc(v_toPure_2962_);
v___f_2973_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2973_, 0, v___y_2963_);
lean_closure_set(v___f_2973_, 1, v___x_2972_);
lean_closure_set(v___f_2973_, 2, v_toPure_2962_);
v___x_2974_ = l_Array_shrink___redArg(v_a_2968_, v_a_2967_);
lean_dec(v_a_2967_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set_tag(v___x_2970_, 0);
lean_ctor_set(v___x_2970_, 1, v___x_2974_);
lean_ctor_set(v___x_2970_, 0, v___x_2972_);
v___x_2976_ = v___x_2970_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2972_);
lean_ctor_set(v_reuseFailAlloc_2979_, 1, v___x_2974_);
v___x_2976_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2977_ = lean_apply_2(v_toPure_2962_, lean_box(0), v___x_2976_);
v___x_2978_ = lean_apply_4(v_toBind_2964_, lean_box(0), lean_box(0), v___x_2977_, v___f_2973_);
return v___x_2978_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__2(lean_object* v_toPure_2981_, lean_object* v_toBind_2982_, lean_object* v_00_u03b1_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v___f_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
lean_inc(v_toBind_2982_);
v___f_2987_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2987_, 0, v_toPure_2981_);
lean_closure_set(v___f_2987_, 1, v___y_2985_);
lean_closure_set(v___f_2987_, 2, v_toBind_2982_);
v___x_2988_ = lean_apply_1(v___y_2984_, v___y_2986_);
v___x_2989_ = lean_apply_4(v_toBind_2982_, lean_box(0), lean_box(0), v___x_2988_, v___f_2987_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__3(lean_object* v_toPure_2990_, lean_object* v_____do__lift_2991_){
_start:
{
if (lean_obj_tag(v_____do__lift_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3001_; 
v_a_2992_ = lean_ctor_get(v_____do__lift_2991_, 0);
v_a_2993_ = lean_ctor_get(v_____do__lift_2991_, 1);
v_isSharedCheck_3001_ = !lean_is_exclusive(v_____do__lift_2991_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2995_ = v_____do__lift_2991_;
v_isShared_2996_ = v_isSharedCheck_3001_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_inc(v_a_2992_);
lean_dec(v_____do__lift_2991_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3001_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
lean_ctor_set_tag(v___x_2995_, 1);
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2992_);
lean_ctor_set(v_reuseFailAlloc_3000_, 1, v_a_2993_);
v___x_2998_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
lean_object* v___x_2999_; 
v___x_2999_ = lean_apply_2(v_toPure_2990_, lean_box(0), v___x_2998_);
return v___x_2999_;
}
}
}
else
{
lean_object* v_a_3002_; lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3011_; 
v_a_3002_ = lean_ctor_get(v_____do__lift_2991_, 0);
v_a_3003_ = lean_ctor_get(v_____do__lift_2991_, 1);
v_isSharedCheck_3011_ = !lean_is_exclusive(v_____do__lift_2991_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3005_ = v_____do__lift_2991_;
v_isShared_3006_ = v_isSharedCheck_3011_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_inc(v_a_3002_);
lean_dec(v_____do__lift_2991_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3011_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_a_3002_);
lean_ctor_set(v_reuseFailAlloc_3010_, 1, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
lean_object* v___x_3009_; 
v___x_3009_ = lean_apply_2(v_toPure_2990_, lean_box(0), v___x_3008_);
return v___x_3009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__4(lean_object* v_toFunctor_3012_, lean_object* v_toPure_3013_, lean_object* v___f_3014_, lean_object* v_toBind_3015_, lean_object* v___f_3016_, lean_object* v_00_u03b1_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v_map_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3029_; 
v_map_3019_ = lean_ctor_get(v_toFunctor_3012_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v_toFunctor_3012_);
if (v_isSharedCheck_3029_ == 0)
{
lean_object* v_unused_3030_; 
v_unused_3030_ = lean_ctor_get(v_toFunctor_3012_, 1);
lean_dec(v_unused_3030_);
v___x_3021_ = v_toFunctor_3012_;
v_isShared_3022_ = v_isSharedCheck_3029_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_map_3019_);
lean_dec(v_toFunctor_3012_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3029_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
lean_inc_ref(v___y_3018_);
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 1, v___y_3018_);
lean_ctor_set(v___x_3021_, 0, v___y_3018_);
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___y_3018_);
lean_ctor_set(v_reuseFailAlloc_3028_, 1, v___y_3018_);
v___x_3024_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3025_ = lean_apply_2(v_toPure_3013_, lean_box(0), v___x_3024_);
v___x_3026_ = lean_apply_4(v_map_3019_, lean_box(0), lean_box(0), v___f_3014_, v___x_3025_);
v___x_3027_ = lean_apply_4(v_toBind_3015_, lean_box(0), lean_box(0), v___x_3026_, v___f_3016_);
return v___x_3027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg(lean_object* v_inst_3031_){
_start:
{
lean_object* v_toApplicative_3032_; lean_object* v_toBind_3033_; lean_object* v_toFunctor_3034_; lean_object* v_toPure_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3053_; 
v_toApplicative_3032_ = lean_ctor_get(v_inst_3031_, 0);
lean_inc_ref(v_toApplicative_3032_);
v_toBind_3033_ = lean_ctor_get(v_inst_3031_, 1);
lean_inc(v_toBind_3033_);
lean_dec_ref(v_inst_3031_);
v_toFunctor_3034_ = lean_ctor_get(v_toApplicative_3032_, 0);
v_toPure_3035_ = lean_ctor_get(v_toApplicative_3032_, 1);
v_isSharedCheck_3053_ = !lean_is_exclusive(v_toApplicative_3032_);
if (v_isSharedCheck_3053_ == 0)
{
lean_object* v_unused_3054_; lean_object* v_unused_3055_; lean_object* v_unused_3056_; 
v_unused_3054_ = lean_ctor_get(v_toApplicative_3032_, 4);
lean_dec(v_unused_3054_);
v_unused_3055_ = lean_ctor_get(v_toApplicative_3032_, 3);
lean_dec(v_unused_3055_);
v_unused_3056_ = lean_ctor_get(v_toApplicative_3032_, 2);
lean_dec(v_unused_3056_);
v___x_3037_ = v_toApplicative_3032_;
v_isShared_3038_ = v_isSharedCheck_3053_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_toPure_3035_);
lean_inc(v_toFunctor_3034_);
lean_dec(v_toApplicative_3032_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3053_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___f_3039_; lean_object* v___f_3040_; lean_object* v___f_3041_; lean_object* v___f_3042_; lean_object* v___f_3043_; lean_object* v___f_3044_; lean_object* v___f_3045_; lean_object* v___f_3046_; lean_object* v___x_3047_; lean_object* v___f_3048_; lean_object* v___x_3050_; 
v___f_3039_ = ((lean_object*)(l_Lake_instMonadErrorELogTOfMonad___redArg___closed__0));
lean_inc_n(v_toBind_3033_, 4);
lean_inc_n(v_toPure_3035_, 7);
v___f_3040_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__2), 6, 2);
lean_closure_set(v___f_3040_, 0, v_toPure_3035_);
lean_closure_set(v___f_3040_, 1, v_toBind_3033_);
v___f_3041_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3041_, 0, v_toPure_3035_);
lean_inc_ref_n(v_toFunctor_3034_, 2);
v___f_3042_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__4), 7, 5);
lean_closure_set(v___f_3042_, 0, v_toFunctor_3034_);
lean_closure_set(v___f_3042_, 1, v_toPure_3035_);
lean_closure_set(v___f_3042_, 2, v___f_3039_);
lean_closure_set(v___f_3042_, 3, v_toBind_3033_);
lean_closure_set(v___f_3042_, 4, v___f_3041_);
v___f_3043_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_3043_, 0, v_toPure_3035_);
lean_closure_set(v___f_3043_, 1, v_toBind_3033_);
v___f_3044_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_3044_, 0, v_toPure_3035_);
lean_closure_set(v___f_3044_, 1, v_toBind_3033_);
v___f_3045_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_3045_, 0, v_toPure_3035_);
lean_closure_set(v___f_3045_, 1, v___f_3043_);
v___f_3046_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_3046_, 0, v_toFunctor_3034_);
lean_closure_set(v___f_3046_, 1, v_toPure_3035_);
lean_closure_set(v___f_3046_, 2, v_toBind_3033_);
v___x_3047_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_3034_);
v___f_3048_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3048_, 0, v_toPure_3035_);
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 4, v___f_3044_);
lean_ctor_set(v___x_3037_, 3, v___f_3045_);
lean_ctor_set(v___x_3037_, 2, v___f_3046_);
lean_ctor_set(v___x_3037_, 1, v___f_3048_);
lean_ctor_set(v___x_3037_, 0, v___x_3047_);
v___x_3050_ = v___x_3037_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3047_);
lean_ctor_set(v_reuseFailAlloc_3052_, 1, v___f_3048_);
lean_ctor_set(v_reuseFailAlloc_3052_, 2, v___f_3046_);
lean_ctor_set(v_reuseFailAlloc_3052_, 3, v___f_3045_);
lean_ctor_set(v_reuseFailAlloc_3052_, 4, v___f_3044_);
v___x_3050_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
lean_object* v___x_3051_; 
v___x_3051_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3050_);
lean_ctor_set(v___x_3051_, 1, v___f_3042_);
lean_ctor_set(v___x_3051_, 2, v___f_3040_);
return v___x_3051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad(lean_object* v_m_3057_, lean_object* v_inst_3058_){
_start:
{
lean_object* v___x_3059_; 
v___x_3059_ = l_Lake_instAlternativeELogTOfMonad___redArg(v_inst_3058_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run___redArg(lean_object* v_self_3060_, lean_object* v_log_3061_){
_start:
{
lean_object* v___x_3062_; 
v___x_3062_ = lean_apply_1(v_self_3060_, v_log_3061_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run(lean_object* v_m_3063_, lean_object* v_00_u03b1_3064_, lean_object* v_self_3065_, lean_object* v_log_3066_){
_start:
{
lean_object* v___x_3067_; 
v___x_3067_ = lean_apply_1(v_self_3065_, v_log_3066_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x27___redArg(lean_object* v_inst_3069_, lean_object* v_self_3070_, lean_object* v_log_3071_){
_start:
{
lean_object* v_map_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v_map_3072_ = lean_ctor_get(v_inst_3069_, 0);
lean_inc(v_map_3072_);
lean_dec_ref(v_inst_3069_);
v___x_3073_ = ((lean_object*)(l_Lake_ELogT_run_x27___redArg___closed__0));
v___x_3074_ = lean_apply_1(v_self_3070_, v_log_3071_);
v___x_3075_ = lean_apply_4(v_map_3072_, lean_box(0), lean_box(0), v___x_3073_, v___x_3074_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x27(lean_object* v_m_3076_, lean_object* v_00_u03b1_3077_, lean_object* v_inst_3078_, lean_object* v_self_3079_, lean_object* v_log_3080_){
_start:
{
lean_object* v_map_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v_map_3081_ = lean_ctor_get(v_inst_3078_, 0);
lean_inc(v_map_3081_);
lean_dec_ref(v_inst_3078_);
v___x_3082_ = ((lean_object*)(l_Lake_ELogT_run_x27___redArg___closed__0));
v___x_3083_ = lean_apply_1(v_self_3079_, v_log_3080_);
v___x_3084_ = lean_apply_4(v_map_3081_, lean_box(0), lean_box(0), v___x_3082_, v___x_3083_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT___redArg(lean_object* v_inst_3086_, lean_object* v_self_3087_, lean_object* v_a_3088_){
_start:
{
lean_object* v_map_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v_map_3089_ = lean_ctor_get(v_inst_3086_, 0);
lean_inc(v_map_3089_);
lean_dec_ref(v_inst_3086_);
v___x_3090_ = ((lean_object*)(l_Lake_ELogT_toLogT___redArg___closed__0));
v___x_3091_ = lean_apply_1(v_self_3087_, v_a_3088_);
v___x_3092_ = lean_apply_4(v_map_3089_, lean_box(0), lean_box(0), v___x_3090_, v___x_3091_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT(lean_object* v_m_3093_, lean_object* v_00_u03b1_3094_, lean_object* v_inst_3095_, lean_object* v_self_3096_, lean_object* v_a_3097_){
_start:
{
lean_object* v_map_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v_map_3098_ = lean_ctor_get(v_inst_3095_, 0);
lean_inc(v_map_3098_);
lean_dec_ref(v_inst_3095_);
v___x_3099_ = ((lean_object*)(l_Lake_ELogT_toLogT___redArg___closed__0));
v___x_3100_ = lean_apply_1(v_self_3096_, v_a_3097_);
v___x_3101_ = lean_apply_4(v_map_3098_, lean_box(0), lean_box(0), v___x_3099_, v___x_3100_);
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT_x3f___redArg(lean_object* v_inst_3103_, lean_object* v_self_3104_, lean_object* v_a_3105_){
_start:
{
lean_object* v_map_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v_map_3106_ = lean_ctor_get(v_inst_3103_, 0);
lean_inc(v_map_3106_);
lean_dec_ref(v_inst_3103_);
v___x_3107_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3108_ = lean_apply_1(v_self_3104_, v_a_3105_);
v___x_3109_ = lean_apply_4(v_map_3106_, lean_box(0), lean_box(0), v___x_3107_, v___x_3108_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT_x3f(lean_object* v_m_3110_, lean_object* v_00_u03b1_3111_, lean_object* v_inst_3112_, lean_object* v_self_3113_, lean_object* v_a_3114_){
_start:
{
lean_object* v_map_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v_map_3115_ = lean_ctor_get(v_inst_3112_, 0);
lean_inc(v_map_3115_);
lean_dec_ref(v_inst_3112_);
v___x_3116_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3117_ = lean_apply_1(v_self_3113_, v_a_3114_);
v___x_3118_ = lean_apply_4(v_map_3115_, lean_box(0), lean_box(0), v___x_3116_, v___x_3117_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f___redArg(lean_object* v_inst_3119_, lean_object* v_self_3120_, lean_object* v_log_3121_){
_start:
{
lean_object* v_map_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v_map_3122_ = lean_ctor_get(v_inst_3119_, 0);
lean_inc(v_map_3122_);
lean_dec_ref(v_inst_3119_);
v___x_3123_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3124_ = lean_apply_1(v_self_3120_, v_log_3121_);
v___x_3125_ = lean_apply_4(v_map_3122_, lean_box(0), lean_box(0), v___x_3123_, v___x_3124_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f(lean_object* v_m_3126_, lean_object* v_00_u03b1_3127_, lean_object* v_inst_3128_, lean_object* v_self_3129_, lean_object* v_log_3130_){
_start:
{
lean_object* v_map_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v_map_3131_ = lean_ctor_get(v_inst_3128_, 0);
lean_inc(v_map_3131_);
lean_dec_ref(v_inst_3128_);
v___x_3132_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3133_ = lean_apply_1(v_self_3129_, v_log_3130_);
v___x_3134_ = lean_apply_4(v_map_3131_, lean_box(0), lean_box(0), v___x_3132_, v___x_3133_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f_x27___redArg(lean_object* v_inst_3136_, lean_object* v_self_3137_, lean_object* v_log_3138_){
_start:
{
lean_object* v_map_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v_map_3139_ = lean_ctor_get(v_inst_3136_, 0);
lean_inc(v_map_3139_);
lean_dec_ref(v_inst_3136_);
v___x_3140_ = ((lean_object*)(l_Lake_ELogT_run_x3f_x27___redArg___closed__0));
v___x_3141_ = lean_apply_1(v_self_3137_, v_log_3138_);
v___x_3142_ = lean_apply_4(v_map_3139_, lean_box(0), lean_box(0), v___x_3140_, v___x_3141_);
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f_x27(lean_object* v_m_3143_, lean_object* v_00_u03b1_3144_, lean_object* v_inst_3145_, lean_object* v_self_3146_, lean_object* v_log_3147_){
_start:
{
lean_object* v_map_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v_map_3148_ = lean_ctor_get(v_inst_3145_, 0);
lean_inc(v_map_3148_);
lean_dec_ref(v_inst_3145_);
v___x_3149_ = ((lean_object*)(l_Lake_ELogT_run_x3f_x27___redArg___closed__0));
v___x_3150_ = lean_apply_1(v_self_3146_, v_log_3147_);
v___x_3151_ = lean_apply_4(v_map_3148_, lean_box(0), lean_box(0), v___x_3149_, v___x_3150_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg___lam__0(lean_object* v_f_3152_, lean_object* v_____x_3153_){
_start:
{
lean_object* v_fst_3154_; lean_object* v_snd_3155_; lean_object* v___x_3156_; 
v_fst_3154_ = lean_ctor_get(v_____x_3153_, 0);
lean_inc(v_fst_3154_);
v_snd_3155_ = lean_ctor_get(v_____x_3153_, 1);
lean_inc(v_snd_3155_);
lean_dec_ref(v_____x_3153_);
v___x_3156_ = lean_apply_2(v_f_3152_, v_fst_3154_, v_snd_3155_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg___lam__1(lean_object* v_toPure_3157_, lean_object* v_toBind_3158_, lean_object* v___f_3159_, lean_object* v_____do__lift_3160_){
_start:
{
if (lean_obj_tag(v_____do__lift_3160_) == 0)
{
lean_object* v_a_3161_; lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3170_; 
lean_dec(v___f_3159_);
lean_dec(v_toBind_3158_);
v_a_3161_ = lean_ctor_get(v_____do__lift_3160_, 0);
v_a_3162_ = lean_ctor_get(v_____do__lift_3160_, 1);
v_isSharedCheck_3170_ = !lean_is_exclusive(v_____do__lift_3160_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3164_ = v_____do__lift_3160_;
v_isShared_3165_ = v_isSharedCheck_3170_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_inc(v_a_3161_);
lean_dec(v_____do__lift_3160_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3170_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3161_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
lean_object* v___x_3168_; 
v___x_3168_ = lean_apply_2(v_toPure_3157_, lean_box(0), v___x_3167_);
return v___x_3168_;
}
}
}
else
{
lean_object* v_a_3171_; lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3184_; 
v_a_3171_ = lean_ctor_get(v_____do__lift_3160_, 0);
v_a_3172_ = lean_ctor_get(v_____do__lift_3160_, 1);
v_isSharedCheck_3184_ = !lean_is_exclusive(v_____do__lift_3160_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3174_ = v_____do__lift_3160_;
v_isShared_3175_ = v_isSharedCheck_3184_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_inc(v_a_3171_);
lean_dec(v_____do__lift_3160_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3184_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3180_; 
v___x_3176_ = lean_array_get_size(v_a_3172_);
lean_inc(v_a_3171_);
v___x_3177_ = l_Array_extract___redArg(v_a_3172_, v_a_3171_, v___x_3176_);
v___x_3178_ = l_Array_shrink___redArg(v_a_3172_, v_a_3171_);
lean_dec(v_a_3171_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set_tag(v___x_3174_, 0);
lean_ctor_set(v___x_3174_, 1, v___x_3178_);
lean_ctor_set(v___x_3174_, 0, v___x_3177_);
v___x_3180_ = v___x_3174_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3177_);
lean_ctor_set(v_reuseFailAlloc_3183_, 1, v___x_3178_);
v___x_3180_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3181_ = lean_apply_2(v_toPure_3157_, lean_box(0), v___x_3180_);
v___x_3182_ = lean_apply_4(v_toBind_3158_, lean_box(0), lean_box(0), v___x_3181_, v___f_3159_);
return v___x_3182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg(lean_object* v_inst_3185_, lean_object* v_f_3186_, lean_object* v_self_3187_, lean_object* v_a_3188_){
_start:
{
lean_object* v_toApplicative_3189_; lean_object* v_toBind_3190_; lean_object* v_toPure_3191_; lean_object* v___f_3192_; lean_object* v___x_3193_; lean_object* v___f_3194_; lean_object* v___x_3195_; 
v_toApplicative_3189_ = lean_ctor_get(v_inst_3185_, 0);
lean_inc_ref(v_toApplicative_3189_);
v_toBind_3190_ = lean_ctor_get(v_inst_3185_, 1);
lean_inc_n(v_toBind_3190_, 2);
lean_dec_ref(v_inst_3185_);
v_toPure_3191_ = lean_ctor_get(v_toApplicative_3189_, 1);
lean_inc(v_toPure_3191_);
lean_dec_ref(v_toApplicative_3189_);
v___f_3192_ = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3192_, 0, v_f_3186_);
v___x_3193_ = lean_apply_1(v_self_3187_, v_a_3188_);
v___f_3194_ = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3194_, 0, v_toPure_3191_);
lean_closure_set(v___f_3194_, 1, v_toBind_3190_);
lean_closure_set(v___f_3194_, 2, v___f_3192_);
v___x_3195_ = lean_apply_4(v_toBind_3190_, lean_box(0), lean_box(0), v___x_3193_, v___f_3194_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog(lean_object* v_m_3196_, lean_object* v_00_u03b1_3197_, lean_object* v_inst_3198_, lean_object* v_f_3199_, lean_object* v_self_3200_, lean_object* v_a_3201_){
_start:
{
lean_object* v_toApplicative_3202_; lean_object* v_toBind_3203_; lean_object* v_toPure_3204_; lean_object* v___f_3205_; lean_object* v___x_3206_; lean_object* v___f_3207_; lean_object* v___x_3208_; 
v_toApplicative_3202_ = lean_ctor_get(v_inst_3198_, 0);
lean_inc_ref(v_toApplicative_3202_);
v_toBind_3203_ = lean_ctor_get(v_inst_3198_, 1);
lean_inc_n(v_toBind_3203_, 2);
lean_dec_ref(v_inst_3198_);
v_toPure_3204_ = lean_ctor_get(v_toApplicative_3202_, 1);
lean_inc(v_toPure_3204_);
lean_dec_ref(v_toApplicative_3202_);
v___f_3205_ = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3205_, 0, v_f_3199_);
v___x_3206_ = lean_apply_1(v_self_3200_, v_a_3201_);
v___f_3207_ = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3207_, 0, v_toPure_3204_);
lean_closure_set(v___f_3207_, 1, v_toBind_3203_);
lean_closure_set(v___f_3207_, 2, v___f_3205_);
v___x_3208_ = lean_apply_4(v_toBind_3203_, lean_box(0), lean_box(0), v___x_3206_, v___f_3207_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__1(lean_object* v_toPure_3209_, lean_object* v_a_3210_, lean_object* v_____r_3211_){
_start:
{
lean_object* v___x_3212_; 
v___x_3212_ = lean_apply_2(v_toPure_3209_, lean_box(0), v_a_3210_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__0(lean_object* v_inst_3213_, lean_object* v_a_3214_, lean_object* v_____r_3215_){
_start:
{
lean_object* v_throw_3216_; lean_object* v___x_3217_; 
v_throw_3216_ = lean_ctor_get(v_inst_3213_, 0);
lean_inc(v_throw_3216_);
lean_dec_ref(v_inst_3213_);
v___x_3217_ = lean_apply_2(v_throw_3216_, lean_box(0), v_a_3214_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__2(lean_object* v_toPure_3218_, lean_object* v_set_3219_, lean_object* v_toBind_3220_, lean_object* v_inst_3221_, lean_object* v_____do__lift_3222_){
_start:
{
if (lean_obj_tag(v_____do__lift_3222_) == 0)
{
lean_object* v_a_3223_; lean_object* v_a_3224_; lean_object* v___f_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
lean_dec_ref(v_inst_3221_);
v_a_3223_ = lean_ctor_get(v_____do__lift_3222_, 0);
lean_inc(v_a_3223_);
v_a_3224_ = lean_ctor_get(v_____do__lift_3222_, 1);
lean_inc(v_a_3224_);
lean_dec_ref(v_____do__lift_3222_);
v___f_3225_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3225_, 0, v_toPure_3218_);
lean_closure_set(v___f_3225_, 1, v_a_3223_);
v___x_3226_ = lean_apply_1(v_set_3219_, v_a_3224_);
v___x_3227_ = lean_apply_4(v_toBind_3220_, lean_box(0), lean_box(0), v___x_3226_, v___f_3225_);
return v___x_3227_;
}
else
{
lean_object* v_a_3228_; lean_object* v_a_3229_; lean_object* v___f_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
lean_dec(v_toPure_3218_);
v_a_3228_ = lean_ctor_get(v_____do__lift_3222_, 0);
lean_inc(v_a_3228_);
v_a_3229_ = lean_ctor_get(v_____do__lift_3222_, 1);
lean_inc(v_a_3229_);
lean_dec_ref(v_____do__lift_3222_);
v___f_3230_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3230_, 0, v_inst_3221_);
lean_closure_set(v___f_3230_, 1, v_a_3228_);
v___x_3231_ = lean_apply_1(v_set_3219_, v_a_3229_);
v___x_3232_ = lean_apply_4(v_toBind_3220_, lean_box(0), lean_box(0), v___x_3231_, v___f_3230_);
return v___x_3232_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__3(lean_object* v_self_3233_, lean_object* v_inst_3234_, lean_object* v_toBind_3235_, lean_object* v___f_3236_, lean_object* v_____do__lift_3237_){
_start:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3238_ = lean_apply_1(v_self_3233_, v_____do__lift_3237_);
v___x_3239_ = lean_apply_2(v_inst_3234_, lean_box(0), v___x_3238_);
v___x_3240_ = lean_apply_4(v_toBind_3235_, lean_box(0), lean_box(0), v___x_3239_, v___f_3236_);
return v___x_3240_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg(lean_object* v_inst_3241_, lean_object* v_inst_3242_, lean_object* v_inst_3243_, lean_object* v_inst_3244_, lean_object* v_self_3245_){
_start:
{
lean_object* v_toApplicative_3246_; lean_object* v_toBind_3247_; lean_object* v_set_3248_; lean_object* v_modifyGet_3249_; lean_object* v_toPure_3250_; lean_object* v___f_3251_; lean_object* v___x_3252_; lean_object* v___f_3253_; lean_object* v___f_3254_; lean_object* v___x_3255_; 
v_toApplicative_3246_ = lean_ctor_get(v_inst_3241_, 0);
lean_inc_ref(v_toApplicative_3246_);
v_toBind_3247_ = lean_ctor_get(v_inst_3241_, 1);
lean_inc_n(v_toBind_3247_, 3);
lean_dec_ref(v_inst_3241_);
v_set_3248_ = lean_ctor_get(v_inst_3242_, 1);
lean_inc(v_set_3248_);
v_modifyGet_3249_ = lean_ctor_get(v_inst_3242_, 2);
lean_inc(v_modifyGet_3249_);
lean_dec_ref(v_inst_3242_);
v_toPure_3250_ = lean_ctor_get(v_toApplicative_3246_, 1);
lean_inc(v_toPure_3250_);
lean_dec_ref(v_toApplicative_3246_);
v___f_3251_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_3252_ = lean_apply_2(v_modifyGet_3249_, lean_box(0), v___f_3251_);
v___f_3253_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3253_, 0, v_toPure_3250_);
lean_closure_set(v___f_3253_, 1, v_set_3248_);
lean_closure_set(v___f_3253_, 2, v_toBind_3247_);
lean_closure_set(v___f_3253_, 3, v_inst_3243_);
v___f_3254_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3254_, 0, v_self_3245_);
lean_closure_set(v___f_3254_, 1, v_inst_3244_);
lean_closure_set(v___f_3254_, 2, v_toBind_3247_);
lean_closure_set(v___f_3254_, 3, v___f_3253_);
v___x_3255_ = lean_apply_4(v_toBind_3247_, lean_box(0), lean_box(0), v___x_3252_, v___f_3254_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun(lean_object* v_n_3256_, lean_object* v_m_3257_, lean_object* v_00_u03b1_3258_, lean_object* v_inst_3259_, lean_object* v_inst_3260_, lean_object* v_inst_3261_, lean_object* v_inst_3262_, lean_object* v_self_3263_){
_start:
{
lean_object* v_toApplicative_3264_; lean_object* v_toBind_3265_; lean_object* v_set_3266_; lean_object* v_modifyGet_3267_; lean_object* v_toPure_3268_; lean_object* v___f_3269_; lean_object* v___x_3270_; lean_object* v___f_3271_; lean_object* v___f_3272_; lean_object* v___x_3273_; 
v_toApplicative_3264_ = lean_ctor_get(v_inst_3259_, 0);
lean_inc_ref(v_toApplicative_3264_);
v_toBind_3265_ = lean_ctor_get(v_inst_3259_, 1);
lean_inc_n(v_toBind_3265_, 3);
lean_dec_ref(v_inst_3259_);
v_set_3266_ = lean_ctor_get(v_inst_3260_, 1);
lean_inc(v_set_3266_);
v_modifyGet_3267_ = lean_ctor_get(v_inst_3260_, 2);
lean_inc(v_modifyGet_3267_);
lean_dec_ref(v_inst_3260_);
v_toPure_3268_ = lean_ctor_get(v_toApplicative_3264_, 1);
lean_inc(v_toPure_3268_);
lean_dec_ref(v_toApplicative_3264_);
v___f_3269_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_3270_ = lean_apply_2(v_modifyGet_3267_, lean_box(0), v___f_3269_);
v___f_3271_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3271_, 0, v_toPure_3268_);
lean_closure_set(v___f_3271_, 1, v_set_3266_);
lean_closure_set(v___f_3271_, 2, v_toBind_3265_);
lean_closure_set(v___f_3271_, 3, v_inst_3261_);
v___f_3272_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3272_, 0, v_self_3263_);
lean_closure_set(v___f_3272_, 1, v_inst_3262_);
lean_closure_set(v___f_3272_, 2, v_toBind_3265_);
lean_closure_set(v___f_3272_, 3, v___f_3271_);
v___x_3273_ = lean_apply_4(v_toBind_3265_, lean_box(0), lean_box(0), v___x_3270_, v___f_3272_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__2(lean_object* v_toPure_3274_, lean_object* v_x_3275_){
_start:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3276_ = lean_box(0);
v___x_3277_ = lean_apply_2(v_toPure_3274_, lean_box(0), v___x_3276_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__0(lean_object* v_a_3278_, lean_object* v_toPure_3279_, lean_object* v_x_3280_){
_start:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3281_, 0, v_a_3278_);
v___x_3282_ = lean_apply_2(v_toPure_3279_, lean_box(0), v___x_3281_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__1(lean_object* v_toPure_3283_, lean_object* v___x_3284_, lean_object* v_toSeqRight_3285_, lean_object* v_inst_3286_, lean_object* v___f_3287_, lean_object* v___f_3288_, lean_object* v___f_3289_, lean_object* v_____do__lift_3290_){
_start:
{
if (lean_obj_tag(v_____do__lift_3290_) == 0)
{
lean_object* v_a_3291_; lean_object* v_a_3292_; lean_object* v___f_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; uint8_t v___x_3296_; 
lean_dec(v___f_3289_);
lean_dec(v___f_3288_);
v_a_3291_ = lean_ctor_get(v_____do__lift_3290_, 0);
lean_inc(v_a_3291_);
v_a_3292_ = lean_ctor_get(v_____do__lift_3290_, 1);
lean_inc(v_a_3292_);
lean_dec_ref(v_____do__lift_3290_);
lean_inc(v_toPure_3283_);
v___f_3293_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3293_, 0, v_a_3291_);
lean_closure_set(v___f_3293_, 1, v_toPure_3283_);
v___x_3294_ = lean_array_get_size(v_a_3292_);
v___x_3295_ = lean_box(0);
v___x_3296_ = lean_nat_dec_lt(v___x_3284_, v___x_3294_);
if (v___x_3296_ == 0)
{
lean_object* v___x_3297_; lean_object* v___x_3298_; 
lean_dec(v_a_3292_);
lean_dec(v___f_3287_);
lean_dec_ref(v_inst_3286_);
v___x_3297_ = lean_apply_2(v_toPure_3283_, lean_box(0), v___x_3295_);
v___x_3298_ = lean_apply_4(v_toSeqRight_3285_, lean_box(0), lean_box(0), v___x_3297_, v___f_3293_);
return v___x_3298_;
}
else
{
uint8_t v___x_3299_; 
v___x_3299_ = lean_nat_dec_le(v___x_3294_, v___x_3294_);
if (v___x_3299_ == 0)
{
if (v___x_3296_ == 0)
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
lean_dec(v_a_3292_);
lean_dec(v___f_3287_);
lean_dec_ref(v_inst_3286_);
v___x_3300_ = lean_apply_2(v_toPure_3283_, lean_box(0), v___x_3295_);
v___x_3301_ = lean_apply_4(v_toSeqRight_3285_, lean_box(0), lean_box(0), v___x_3300_, v___f_3293_);
return v___x_3301_;
}
else
{
size_t v___x_3302_; size_t v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
lean_dec(v_toPure_3283_);
v___x_3302_ = ((size_t)0ULL);
v___x_3303_ = lean_usize_of_nat(v___x_3294_);
v___x_3304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3286_, v___f_3287_, v_a_3292_, v___x_3302_, v___x_3303_, v___x_3295_);
v___x_3305_ = lean_apply_4(v_toSeqRight_3285_, lean_box(0), lean_box(0), v___x_3304_, v___f_3293_);
return v___x_3305_;
}
}
else
{
size_t v___x_3306_; size_t v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
lean_dec(v_toPure_3283_);
v___x_3306_ = ((size_t)0ULL);
v___x_3307_ = lean_usize_of_nat(v___x_3294_);
v___x_3308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3286_, v___f_3287_, v_a_3292_, v___x_3306_, v___x_3307_, v___x_3295_);
v___x_3309_ = lean_apply_4(v_toSeqRight_3285_, lean_box(0), lean_box(0), v___x_3308_, v___f_3293_);
return v___x_3309_;
}
}
}
else
{
lean_object* v_a_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; uint8_t v___x_3313_; 
lean_dec(v___f_3287_);
v_a_3310_ = lean_ctor_get(v_____do__lift_3290_, 1);
lean_inc(v_a_3310_);
lean_dec_ref(v_____do__lift_3290_);
v___x_3311_ = lean_array_get_size(v_a_3310_);
v___x_3312_ = lean_box(0);
v___x_3313_ = lean_nat_dec_lt(v___x_3284_, v___x_3311_);
if (v___x_3313_ == 0)
{
lean_object* v___x_3314_; lean_object* v___x_3315_; 
lean_dec(v_a_3310_);
lean_dec(v___f_3289_);
lean_dec_ref(v_inst_3286_);
v___x_3314_ = lean_apply_2(v_toPure_3283_, lean_box(0), v___x_3312_);
v___x_3315_ = lean_apply_4(v_toSeqRight_3285_, lean_box(0), lean_box(0), v___x_3314_, v___f_3288_);
return v___x_3315_;
}
else
{
uint8_t v___x_3316_; 
v___x_3316_ = lean_nat_dec_le(v___x_3311_, v___x_3311_);
if (v___x_3316_ == 0)
{
if (v___x_3313_ == 0)
{
lean_object* v___x_3317_; lean_object* v___x_3318_; 
lean_dec(v_a_3310_);
lean_dec(v___f_3289_);
lean_dec_ref(v_inst_3286_);
v___x_3317_ = lean_apply_2(v_toPure_3283_, lean_box(0), v___x_3312_);
v___x_3318_ = lean_apply_4(v_toSeqRight_3285_, lean_box(0), lean_box(0), v___x_3317_, v___f_3288_);
return v___x_3318_;
}
else
{
size_t v___x_3319_; size_t v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
lean_dec(v_toPure_3283_);
v___x_3319_ = ((size_t)0ULL);
v___x_3320_ = lean_usize_of_nat(v___x_3311_);
v___x_3321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3286_, v___f_3289_, v_a_3310_, v___x_3319_, v___x_3320_, v___x_3312_);
v___x_3322_ = lean_apply_4(v_toSeqRight_3285_, lean_box(0), lean_box(0), v___x_3321_, v___f_3288_);
return v___x_3322_;
}
}
else
{
size_t v___x_3323_; size_t v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
lean_dec(v_toPure_3283_);
v___x_3323_ = ((size_t)0ULL);
v___x_3324_ = lean_usize_of_nat(v___x_3311_);
v___x_3325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3286_, v___f_3289_, v_a_3310_, v___x_3323_, v___x_3324_, v___x_3312_);
v___x_3326_ = lean_apply_4(v_toSeqRight_3285_, lean_box(0), lean_box(0), v___x_3325_, v___f_3288_);
return v___x_3326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed(lean_object* v_toPure_3327_, lean_object* v___x_3328_, lean_object* v_toSeqRight_3329_, lean_object* v_inst_3330_, lean_object* v___f_3331_, lean_object* v___f_3332_, lean_object* v___f_3333_, lean_object* v_____do__lift_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l_Lake_ELogT_replayLog_x3f___redArg___lam__1(v_toPure_3327_, v___x_3328_, v_toSeqRight_3329_, v_inst_3330_, v___f_3331_, v___f_3332_, v___f_3333_, v_____do__lift_3334_);
lean_dec(v___x_3328_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg(lean_object* v_inst_3336_, lean_object* v_logger_3337_, lean_object* v_inst_3338_, lean_object* v_self_3339_){
_start:
{
lean_object* v_toApplicative_3340_; lean_object* v_toBind_3341_; lean_object* v_toPure_3342_; lean_object* v_toSeqRight_3343_; lean_object* v___f_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___f_3349_; lean_object* v___f_3350_; lean_object* v___x_3351_; 
v_toApplicative_3340_ = lean_ctor_get(v_inst_3336_, 0);
v_toBind_3341_ = lean_ctor_get(v_inst_3336_, 1);
lean_inc(v_toBind_3341_);
v_toPure_3342_ = lean_ctor_get(v_toApplicative_3340_, 1);
lean_inc_n(v_toPure_3342_, 2);
v_toSeqRight_3343_ = lean_ctor_get(v_toApplicative_3340_, 4);
lean_inc(v_toSeqRight_3343_);
v___f_3344_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3344_, 0, v_logger_3337_);
v___x_3345_ = lean_unsigned_to_nat(0u);
v___x_3346_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3347_ = lean_apply_1(v_self_3339_, v___x_3346_);
v___x_3348_ = lean_apply_2(v_inst_3338_, lean_box(0), v___x_3347_);
v___f_3349_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3349_, 0, v_toPure_3342_);
lean_inc_ref(v___f_3344_);
v___f_3350_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_3350_, 0, v_toPure_3342_);
lean_closure_set(v___f_3350_, 1, v___x_3345_);
lean_closure_set(v___f_3350_, 2, v_toSeqRight_3343_);
lean_closure_set(v___f_3350_, 3, v_inst_3336_);
lean_closure_set(v___f_3350_, 4, v___f_3344_);
lean_closure_set(v___f_3350_, 5, v___f_3349_);
lean_closure_set(v___f_3350_, 6, v___f_3344_);
v___x_3351_ = lean_apply_4(v_toBind_3341_, lean_box(0), lean_box(0), v___x_3348_, v___f_3350_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f(lean_object* v_n_3352_, lean_object* v_m_3353_, lean_object* v_00_u03b1_3354_, lean_object* v_inst_3355_, lean_object* v_logger_3356_, lean_object* v_inst_3357_, lean_object* v_self_3358_){
_start:
{
lean_object* v_toApplicative_3359_; lean_object* v_toBind_3360_; lean_object* v_toPure_3361_; lean_object* v_toSeqRight_3362_; lean_object* v___f_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___f_3368_; lean_object* v___f_3369_; lean_object* v___x_3370_; 
v_toApplicative_3359_ = lean_ctor_get(v_inst_3355_, 0);
v_toBind_3360_ = lean_ctor_get(v_inst_3355_, 1);
lean_inc(v_toBind_3360_);
v_toPure_3361_ = lean_ctor_get(v_toApplicative_3359_, 1);
lean_inc_n(v_toPure_3361_, 2);
v_toSeqRight_3362_ = lean_ctor_get(v_toApplicative_3359_, 4);
lean_inc(v_toSeqRight_3362_);
v___f_3363_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3363_, 0, v_logger_3356_);
v___x_3364_ = lean_unsigned_to_nat(0u);
v___x_3365_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3366_ = lean_apply_1(v_self_3358_, v___x_3365_);
v___x_3367_ = lean_apply_2(v_inst_3357_, lean_box(0), v___x_3366_);
v___f_3368_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3368_, 0, v_toPure_3361_);
lean_inc_ref(v___f_3363_);
v___f_3369_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_3369_, 0, v_toPure_3361_);
lean_closure_set(v___f_3369_, 1, v___x_3364_);
lean_closure_set(v___f_3369_, 2, v_toSeqRight_3362_);
lean_closure_set(v___f_3369_, 3, v_inst_3355_);
lean_closure_set(v___f_3369_, 4, v___f_3363_);
lean_closure_set(v___f_3369_, 5, v___f_3368_);
lean_closure_set(v___f_3369_, 6, v___f_3363_);
v___x_3370_ = lean_apply_4(v_toBind_3360_, lean_box(0), lean_box(0), v___x_3367_, v___f_3369_);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg___lam__3(lean_object* v_toPure_3371_, lean_object* v_a_3372_, lean_object* v_x_3373_){
_start:
{
lean_object* v___x_3374_; 
v___x_3374_ = lean_apply_2(v_toPure_3371_, lean_box(0), v_a_3372_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg___lam__0(lean_object* v_toPure_3375_, lean_object* v___x_3376_, lean_object* v_toApplicative_3377_, lean_object* v_toSeqRight_3378_, lean_object* v_inst_3379_, lean_object* v___f_3380_, lean_object* v___f_3381_, lean_object* v___f_3382_, lean_object* v_____do__lift_3383_){
_start:
{
if (lean_obj_tag(v_____do__lift_3383_) == 0)
{
lean_object* v_a_3384_; lean_object* v_a_3385_; lean_object* v___f_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; uint8_t v___x_3389_; 
lean_dec(v___f_3382_);
lean_dec(v___f_3381_);
v_a_3384_ = lean_ctor_get(v_____do__lift_3383_, 0);
lean_inc(v_a_3384_);
v_a_3385_ = lean_ctor_get(v_____do__lift_3383_, 1);
lean_inc(v_a_3385_);
lean_dec_ref(v_____do__lift_3383_);
v___f_3386_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog___redArg___lam__3), 3, 2);
lean_closure_set(v___f_3386_, 0, v_toPure_3375_);
lean_closure_set(v___f_3386_, 1, v_a_3384_);
v___x_3387_ = lean_array_get_size(v_a_3385_);
v___x_3388_ = lean_box(0);
v___x_3389_ = lean_nat_dec_lt(v___x_3376_, v___x_3387_);
if (v___x_3389_ == 0)
{
lean_object* v_toPure_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
lean_dec(v_a_3385_);
lean_dec(v___f_3380_);
lean_dec_ref(v_inst_3379_);
v_toPure_3390_ = lean_ctor_get(v_toApplicative_3377_, 1);
lean_inc(v_toPure_3390_);
lean_dec_ref(v_toApplicative_3377_);
v___x_3391_ = lean_apply_2(v_toPure_3390_, lean_box(0), v___x_3388_);
v___x_3392_ = lean_apply_4(v_toSeqRight_3378_, lean_box(0), lean_box(0), v___x_3391_, v___f_3386_);
return v___x_3392_;
}
else
{
uint8_t v___x_3393_; 
v___x_3393_ = lean_nat_dec_le(v___x_3387_, v___x_3387_);
if (v___x_3393_ == 0)
{
if (v___x_3389_ == 0)
{
lean_object* v_toPure_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
lean_dec(v_a_3385_);
lean_dec(v___f_3380_);
lean_dec_ref(v_inst_3379_);
v_toPure_3394_ = lean_ctor_get(v_toApplicative_3377_, 1);
lean_inc(v_toPure_3394_);
lean_dec_ref(v_toApplicative_3377_);
v___x_3395_ = lean_apply_2(v_toPure_3394_, lean_box(0), v___x_3388_);
v___x_3396_ = lean_apply_4(v_toSeqRight_3378_, lean_box(0), lean_box(0), v___x_3395_, v___f_3386_);
return v___x_3396_;
}
else
{
size_t v___x_3397_; size_t v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
lean_dec_ref(v_toApplicative_3377_);
v___x_3397_ = ((size_t)0ULL);
v___x_3398_ = lean_usize_of_nat(v___x_3387_);
v___x_3399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3379_, v___f_3380_, v_a_3385_, v___x_3397_, v___x_3398_, v___x_3388_);
v___x_3400_ = lean_apply_4(v_toSeqRight_3378_, lean_box(0), lean_box(0), v___x_3399_, v___f_3386_);
return v___x_3400_;
}
}
else
{
size_t v___x_3401_; size_t v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
lean_dec_ref(v_toApplicative_3377_);
v___x_3401_ = ((size_t)0ULL);
v___x_3402_ = lean_usize_of_nat(v___x_3387_);
v___x_3403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3379_, v___f_3380_, v_a_3385_, v___x_3401_, v___x_3402_, v___x_3388_);
v___x_3404_ = lean_apply_4(v_toSeqRight_3378_, lean_box(0), lean_box(0), v___x_3403_, v___f_3386_);
return v___x_3404_;
}
}
}
else
{
lean_object* v_a_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; uint8_t v___x_3408_; 
lean_dec(v___f_3380_);
lean_dec(v_toPure_3375_);
v_a_3405_ = lean_ctor_get(v_____do__lift_3383_, 1);
lean_inc(v_a_3405_);
lean_dec_ref(v_____do__lift_3383_);
v___x_3406_ = lean_array_get_size(v_a_3405_);
v___x_3407_ = lean_box(0);
v___x_3408_ = lean_nat_dec_lt(v___x_3376_, v___x_3406_);
if (v___x_3408_ == 0)
{
lean_object* v_toPure_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
lean_dec(v_a_3405_);
lean_dec(v___f_3382_);
lean_dec_ref(v_inst_3379_);
v_toPure_3409_ = lean_ctor_get(v_toApplicative_3377_, 1);
lean_inc(v_toPure_3409_);
lean_dec_ref(v_toApplicative_3377_);
v___x_3410_ = lean_apply_2(v_toPure_3409_, lean_box(0), v___x_3407_);
v___x_3411_ = lean_apply_4(v_toSeqRight_3378_, lean_box(0), lean_box(0), v___x_3410_, v___f_3381_);
return v___x_3411_;
}
else
{
uint8_t v___x_3412_; 
v___x_3412_ = lean_nat_dec_le(v___x_3406_, v___x_3406_);
if (v___x_3412_ == 0)
{
if (v___x_3408_ == 0)
{
lean_object* v_toPure_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
lean_dec(v_a_3405_);
lean_dec(v___f_3382_);
lean_dec_ref(v_inst_3379_);
v_toPure_3413_ = lean_ctor_get(v_toApplicative_3377_, 1);
lean_inc(v_toPure_3413_);
lean_dec_ref(v_toApplicative_3377_);
v___x_3414_ = lean_apply_2(v_toPure_3413_, lean_box(0), v___x_3407_);
v___x_3415_ = lean_apply_4(v_toSeqRight_3378_, lean_box(0), lean_box(0), v___x_3414_, v___f_3381_);
return v___x_3415_;
}
else
{
size_t v___x_3416_; size_t v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
lean_dec_ref(v_toApplicative_3377_);
v___x_3416_ = ((size_t)0ULL);
v___x_3417_ = lean_usize_of_nat(v___x_3406_);
v___x_3418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3379_, v___f_3382_, v_a_3405_, v___x_3416_, v___x_3417_, v___x_3407_);
v___x_3419_ = lean_apply_4(v_toSeqRight_3378_, lean_box(0), lean_box(0), v___x_3418_, v___f_3381_);
return v___x_3419_;
}
}
else
{
size_t v___x_3420_; size_t v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
lean_dec_ref(v_toApplicative_3377_);
v___x_3420_ = ((size_t)0ULL);
v___x_3421_ = lean_usize_of_nat(v___x_3406_);
v___x_3422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3379_, v___f_3382_, v_a_3405_, v___x_3420_, v___x_3421_, v___x_3407_);
v___x_3423_ = lean_apply_4(v_toSeqRight_3378_, lean_box(0), lean_box(0), v___x_3422_, v___f_3381_);
return v___x_3423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg___lam__0___boxed(lean_object* v_toPure_3424_, lean_object* v___x_3425_, lean_object* v_toApplicative_3426_, lean_object* v_toSeqRight_3427_, lean_object* v_inst_3428_, lean_object* v___f_3429_, lean_object* v___f_3430_, lean_object* v___f_3431_, lean_object* v_____do__lift_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Lake_ELogT_replayLog___redArg___lam__0(v_toPure_3424_, v___x_3425_, v_toApplicative_3426_, v_toSeqRight_3427_, v_inst_3428_, v___f_3429_, v___f_3430_, v___f_3431_, v_____do__lift_3432_);
lean_dec(v___x_3425_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg(lean_object* v_inst_3434_, lean_object* v_inst_3435_, lean_object* v_logger_3436_, lean_object* v_inst_3437_, lean_object* v_self_3438_){
_start:
{
lean_object* v_toApplicative_3439_; lean_object* v_toApplicative_3440_; lean_object* v_toBind_3441_; lean_object* v_failure_3442_; lean_object* v_toPure_3443_; lean_object* v_toSeqRight_3444_; lean_object* v___f_3445_; lean_object* v___f_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___f_3451_; lean_object* v___x_3452_; 
v_toApplicative_3439_ = lean_ctor_get(v_inst_3434_, 0);
lean_inc_ref(v_toApplicative_3439_);
v_toApplicative_3440_ = lean_ctor_get(v_inst_3435_, 0);
lean_inc_ref(v_toApplicative_3440_);
v_toBind_3441_ = lean_ctor_get(v_inst_3435_, 1);
lean_inc(v_toBind_3441_);
v_failure_3442_ = lean_ctor_get(v_inst_3434_, 1);
lean_inc(v_failure_3442_);
lean_dec_ref(v_inst_3434_);
v_toPure_3443_ = lean_ctor_get(v_toApplicative_3439_, 1);
lean_inc(v_toPure_3443_);
v_toSeqRight_3444_ = lean_ctor_get(v_toApplicative_3439_, 4);
lean_inc(v_toSeqRight_3444_);
lean_dec_ref(v_toApplicative_3439_);
v___f_3445_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3445_, 0, v_logger_3436_);
v___f_3446_ = lean_alloc_closure((void*)(l_Lake_MonadLog_error___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3446_, 0, v_failure_3442_);
v___x_3447_ = lean_unsigned_to_nat(0u);
v___x_3448_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3449_ = lean_apply_1(v_self_3438_, v___x_3448_);
v___x_3450_ = lean_apply_2(v_inst_3437_, lean_box(0), v___x_3449_);
lean_inc_ref(v___f_3445_);
v___f_3451_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3451_, 0, v_toPure_3443_);
lean_closure_set(v___f_3451_, 1, v___x_3447_);
lean_closure_set(v___f_3451_, 2, v_toApplicative_3440_);
lean_closure_set(v___f_3451_, 3, v_toSeqRight_3444_);
lean_closure_set(v___f_3451_, 4, v_inst_3435_);
lean_closure_set(v___f_3451_, 5, v___f_3445_);
lean_closure_set(v___f_3451_, 6, v___f_3446_);
lean_closure_set(v___f_3451_, 7, v___f_3445_);
v___x_3452_ = lean_apply_4(v_toBind_3441_, lean_box(0), lean_box(0), v___x_3450_, v___f_3451_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog(lean_object* v_n_3453_, lean_object* v_m_3454_, lean_object* v_00_u03b1_3455_, lean_object* v_inst_3456_, lean_object* v_inst_3457_, lean_object* v_logger_3458_, lean_object* v_inst_3459_, lean_object* v_self_3460_){
_start:
{
lean_object* v_toApplicative_3461_; lean_object* v_toApplicative_3462_; lean_object* v_toBind_3463_; lean_object* v_failure_3464_; lean_object* v_toPure_3465_; lean_object* v_toSeqRight_3466_; lean_object* v___f_3467_; lean_object* v___f_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___f_3473_; lean_object* v___x_3474_; 
v_toApplicative_3461_ = lean_ctor_get(v_inst_3456_, 0);
lean_inc_ref(v_toApplicative_3461_);
v_toApplicative_3462_ = lean_ctor_get(v_inst_3457_, 0);
lean_inc_ref(v_toApplicative_3462_);
v_toBind_3463_ = lean_ctor_get(v_inst_3457_, 1);
lean_inc(v_toBind_3463_);
v_failure_3464_ = lean_ctor_get(v_inst_3456_, 1);
lean_inc(v_failure_3464_);
lean_dec_ref(v_inst_3456_);
v_toPure_3465_ = lean_ctor_get(v_toApplicative_3461_, 1);
lean_inc(v_toPure_3465_);
v_toSeqRight_3466_ = lean_ctor_get(v_toApplicative_3461_, 4);
lean_inc(v_toSeqRight_3466_);
lean_dec_ref(v_toApplicative_3461_);
v___f_3467_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3467_, 0, v_logger_3458_);
v___f_3468_ = lean_alloc_closure((void*)(l_Lake_MonadLog_error___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3468_, 0, v_failure_3464_);
v___x_3469_ = lean_unsigned_to_nat(0u);
v___x_3470_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3471_ = lean_apply_1(v_self_3460_, v___x_3470_);
v___x_3472_ = lean_apply_2(v_inst_3459_, lean_box(0), v___x_3471_);
lean_inc_ref(v___f_3467_);
v___f_3473_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3473_, 0, v_toPure_3465_);
lean_closure_set(v___f_3473_, 1, v___x_3469_);
lean_closure_set(v___f_3473_, 2, v_toApplicative_3462_);
lean_closure_set(v___f_3473_, 3, v_toSeqRight_3466_);
lean_closure_set(v___f_3473_, 4, v_inst_3457_);
lean_closure_set(v___f_3473_, 5, v___f_3467_);
lean_closure_set(v___f_3473_, 6, v___f_3468_);
lean_closure_set(v___f_3473_, 7, v___f_3467_);
v___x_3474_ = lean_apply_4(v_toBind_3463_, lean_box(0), lean_box(0), v___x_3472_, v___f_3473_);
return v___x_3474_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___redArg___lam__0(lean_object* v_val_3475_, uint8_t v_outLv_3476_, uint8_t v_val_3477_, lean_object* v_inst_3478_, lean_object* v_e_3479_){
_start:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3480_ = lean_box(v_outLv_3476_);
v___x_3481_ = lean_box(v_val_3477_);
v___x_3482_ = lean_alloc_closure((void*)(l_Lake_logToStream___boxed), 5, 4);
lean_closure_set(v___x_3482_, 0, v_e_3479_);
lean_closure_set(v___x_3482_, 1, v_val_3475_);
lean_closure_set(v___x_3482_, 2, v___x_3480_);
lean_closure_set(v___x_3482_, 3, v___x_3481_);
v___x_3483_ = lean_apply_2(v_inst_3478_, lean_box(0), v___x_3482_);
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___redArg___lam__0___boxed(lean_object* v_val_3484_, lean_object* v_outLv_3485_, lean_object* v_val_3486_, lean_object* v_inst_3487_, lean_object* v_e_3488_){
_start:
{
uint8_t v_outLv_boxed_3489_; uint8_t v_val_44__boxed_3490_; lean_object* v_res_3491_; 
v_outLv_boxed_3489_ = lean_unbox(v_outLv_3485_);
v_val_44__boxed_3490_ = lean_unbox(v_val_3486_);
v_res_3491_ = l_Lake_LogConfig_getLogger___redArg___lam__0(v_val_3484_, v_outLv_boxed_3489_, v_val_44__boxed_3490_, v_inst_3487_, v_e_3488_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___redArg(lean_object* v_inst_3492_, lean_object* v_self_3493_){
_start:
{
uint8_t v_outLv_3495_; uint8_t v_ansiMode_3496_; lean_object* v_out_3497_; lean_object* v___x_3498_; uint8_t v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___f_3502_; 
v_outLv_3495_ = lean_ctor_get_uint8(v_self_3493_, sizeof(void*)*1 + 1);
v_ansiMode_3496_ = lean_ctor_get_uint8(v_self_3493_, sizeof(void*)*1 + 2);
v_out_3497_ = lean_ctor_get(v_self_3493_, 0);
v___x_3498_ = l_Lake_OutStream_get(v_out_3497_);
lean_inc_ref(v___x_3498_);
v___x_3499_ = l_Lake_AnsiMode_isEnabled(v___x_3498_, v_ansiMode_3496_);
v___x_3500_ = lean_box(v_outLv_3495_);
v___x_3501_ = lean_box(v___x_3499_);
v___f_3502_ = lean_alloc_closure((void*)(l_Lake_LogConfig_getLogger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3502_, 0, v___x_3498_);
lean_closure_set(v___f_3502_, 1, v___x_3500_);
lean_closure_set(v___f_3502_, 2, v___x_3501_);
lean_closure_set(v___f_3502_, 3, v_inst_3492_);
return v___f_3502_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___redArg___boxed(lean_object* v_inst_3503_, lean_object* v_self_3504_, lean_object* v_a_3505_){
_start:
{
lean_object* v_res_3506_; 
v_res_3506_ = l_Lake_LogConfig_getLogger___redArg(v_inst_3503_, v_self_3504_);
lean_dec_ref(v_self_3504_);
return v_res_3506_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger(lean_object* v_m_3507_, lean_object* v_inst_3508_, lean_object* v_self_3509_){
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
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___boxed(lean_object* v_m_3519_, lean_object* v_inst_3520_, lean_object* v_self_3521_, lean_object* v_a_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = l_Lake_LogConfig_getLogger(v_m_3519_, v_inst_3520_, v_self_3521_);
lean_dec_ref(v_self_3521_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_instMonadLiftIO___lam__0(lean_object* v_00_u03b1_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
lean_object* v___x_3528_; 
v___x_3528_ = lean_apply_1(v___y_3525_, lean_box(0));
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; lean_object* v___x_3530_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3529_);
lean_dec_ref(v___x_3528_);
v___x_3530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3530_, 0, v_a_3529_);
lean_ctor_set(v___x_3530_, 1, v___y_3526_);
return v___x_3530_;
}
else
{
lean_object* v_a_3531_; lean_object* v___x_3532_; uint8_t v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
v_a_3531_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3531_);
lean_dec_ref(v___x_3528_);
v___x_3532_ = lean_io_error_to_string(v_a_3531_);
v___x_3533_ = 3;
v___x_3534_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3534_, 0, v___x_3532_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*1, v___x_3533_);
v___x_3535_ = lean_array_get_size(v___y_3526_);
v___x_3536_ = lean_array_push(v___y_3526_, v___x_3534_);
v___x_3537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3535_);
lean_ctor_set(v___x_3537_, 1, v___x_3536_);
return v___x_3537_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_instMonadLiftIO___lam__0___boxed(lean_object* v_00_u03b1_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_){
_start:
{
lean_object* v_res_3542_; 
v_res_3542_ = l_Lake_LogIO_instMonadLiftIO___lam__0(v_00_u03b1_3538_, v___y_3539_, v___y_3540_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg___lam__0(lean_object* v_val_3545_, uint8_t v___y_3546_, uint8_t v_val_3547_, lean_object* v_x_3548_, lean_object* v___y_3549_){
_start:
{
lean_object* v___x_3551_; 
v___x_3551_ = l_Lake_logToStream(v___y_3549_, v_val_3545_, v___y_3546_, v_val_3547_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed(lean_object* v_val_3552_, lean_object* v___y_3553_, lean_object* v_val_3554_, lean_object* v_x_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_){
_start:
{
uint8_t v___y_862__boxed_3558_; uint8_t v_val_863__boxed_3559_; lean_object* v_res_3560_; 
v___y_862__boxed_3558_ = lean_unbox(v___y_3553_);
v_val_863__boxed_3559_ = lean_unbox(v_val_3554_);
v_res_3560_ = l_Lake_LogIO_toBaseIO___redArg___lam__0(v_val_3552_, v___y_862__boxed_3558_, v_val_863__boxed_3559_, v_x_3555_, v___y_3556_);
lean_dec_ref(v___y_3556_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg(lean_object* v_self_3561_, lean_object* v_cfg_3562_){
_start:
{
lean_object* v___y_3565_; uint8_t v___y_3566_; lean_object* v___y_3569_; uint8_t v___y_3570_; lean_object* v___y_3571_; lean_object* v___x_3572_; lean_object* v___y_3574_; lean_object* v___y_3575_; uint8_t v___y_3576_; uint8_t v___y_3577_; lean_object* v___y_3599_; lean_object* v___y_3600_; uint8_t v___y_3601_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3572_ = l_instMonadBaseIO;
v___x_3603_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3604_ = lean_apply_2(v_self_3561_, v___x_3603_, lean_box(0));
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v_a_3605_; lean_object* v_a_3606_; uint8_t v_failLv_3607_; uint8_t v_outLv_3608_; lean_object* v___x_3609_; uint8_t v___x_3610_; uint8_t v___x_3611_; 
v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
lean_inc(v_a_3605_);
v_a_3606_ = lean_ctor_get(v___x_3604_, 1);
lean_inc(v_a_3606_);
lean_dec_ref(v___x_3604_);
v_failLv_3607_ = lean_ctor_get_uint8(v_cfg_3562_, sizeof(void*)*1);
v_outLv_3608_ = lean_ctor_get_uint8(v_cfg_3562_, sizeof(void*)*1 + 1);
v___x_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3609_, 0, v_a_3605_);
v___x_3610_ = l_Lake_Log_maxLv(v_a_3606_);
v___x_3611_ = l_Lake_instOrdLogLevel_ord(v_failLv_3607_, v___x_3610_);
if (v___x_3611_ == 2)
{
uint8_t v___x_3612_; 
v___x_3612_ = 0;
v___y_3574_ = v_a_3606_;
v___y_3575_ = v___x_3609_;
v___y_3576_ = v___x_3612_;
v___y_3577_ = v_outLv_3608_;
goto v___jp_3573_;
}
else
{
uint8_t v___x_3613_; 
v___x_3613_ = 1;
v___y_3599_ = v_a_3606_;
v___y_3600_ = v___x_3609_;
v___y_3601_ = v___x_3613_;
goto v___jp_3598_;
}
}
else
{
lean_object* v_a_3614_; lean_object* v___x_3615_; uint8_t v___x_3616_; 
v_a_3614_ = lean_ctor_get(v___x_3604_, 1);
lean_inc(v_a_3614_);
lean_dec_ref(v___x_3604_);
v___x_3615_ = lean_box(0);
v___x_3616_ = 1;
v___y_3599_ = v_a_3614_;
v___y_3600_ = v___x_3615_;
v___y_3601_ = v___x_3616_;
goto v___jp_3598_;
}
v___jp_3564_:
{
if (v___y_3566_ == 0)
{
return v___y_3565_;
}
else
{
lean_object* v___x_3567_; 
lean_dec(v___y_3565_);
v___x_3567_ = lean_box(0);
return v___x_3567_;
}
}
v___jp_3568_:
{
v___y_3565_ = v___y_3569_;
v___y_3566_ = v___y_3570_;
goto v___jp_3564_;
}
v___jp_3573_:
{
uint8_t v_ansiMode_3578_; lean_object* v_out_3579_; lean_object* v___x_3580_; uint8_t v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; uint8_t v___x_3584_; 
v_ansiMode_3578_ = lean_ctor_get_uint8(v_cfg_3562_, sizeof(void*)*1 + 2);
v_out_3579_ = lean_ctor_get(v_cfg_3562_, 0);
v___x_3580_ = l_Lake_OutStream_get(v_out_3579_);
lean_inc_ref(v___x_3580_);
v___x_3581_ = l_Lake_AnsiMode_isEnabled(v___x_3580_, v_ansiMode_3578_);
v___x_3582_ = lean_unsigned_to_nat(0u);
v___x_3583_ = lean_array_get_size(v___y_3574_);
v___x_3584_ = lean_nat_dec_lt(v___x_3582_, v___x_3583_);
if (v___x_3584_ == 0)
{
lean_dec_ref(v___x_3580_);
lean_dec_ref(v___y_3574_);
v___y_3565_ = v___y_3575_;
v___y_3566_ = v___y_3576_;
goto v___jp_3564_;
}
else
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___f_3587_; lean_object* v___x_3588_; uint8_t v___x_3589_; 
v___x_3585_ = lean_box(v___y_3577_);
v___x_3586_ = lean_box(v___x_3581_);
v___f_3587_ = lean_alloc_closure((void*)(l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_3587_, 0, v___x_3580_);
lean_closure_set(v___f_3587_, 1, v___x_3585_);
lean_closure_set(v___f_3587_, 2, v___x_3586_);
v___x_3588_ = lean_box(0);
v___x_3589_ = lean_nat_dec_le(v___x_3583_, v___x_3583_);
if (v___x_3589_ == 0)
{
if (v___x_3584_ == 0)
{
lean_dec_ref(v___f_3587_);
lean_dec_ref(v___y_3574_);
v___y_3565_ = v___y_3575_;
v___y_3566_ = v___y_3576_;
goto v___jp_3564_;
}
else
{
size_t v___x_3590_; size_t v___x_3591_; lean_object* v___x_652__overap_3592_; lean_object* v___x_3593_; 
v___x_3590_ = ((size_t)0ULL);
v___x_3591_ = lean_usize_of_nat(v___x_3583_);
v___x_652__overap_3592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3572_, v___f_3587_, v___y_3574_, v___x_3590_, v___x_3591_, v___x_3588_);
v___x_3593_ = lean_apply_1(v___x_652__overap_3592_, lean_box(0));
v___y_3569_ = v___y_3575_;
v___y_3570_ = v___y_3576_;
v___y_3571_ = v___x_3593_;
goto v___jp_3568_;
}
}
else
{
size_t v___x_3594_; size_t v___x_3595_; lean_object* v___x_656__overap_3596_; lean_object* v___x_3597_; 
v___x_3594_ = ((size_t)0ULL);
v___x_3595_ = lean_usize_of_nat(v___x_3583_);
v___x_656__overap_3596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3572_, v___f_3587_, v___y_3574_, v___x_3594_, v___x_3595_, v___x_3588_);
v___x_3597_ = lean_apply_1(v___x_656__overap_3596_, lean_box(0));
v___y_3569_ = v___y_3575_;
v___y_3570_ = v___y_3576_;
v___y_3571_ = v___x_3597_;
goto v___jp_3568_;
}
}
}
v___jp_3598_:
{
uint8_t v___x_3602_; 
v___x_3602_ = 0;
v___y_3574_ = v___y_3599_;
v___y_3575_ = v___y_3600_;
v___y_3576_ = v___y_3601_;
v___y_3577_ = v___x_3602_;
goto v___jp_3573_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg___boxed(lean_object* v_self_3617_, lean_object* v_cfg_3618_, lean_object* v_a_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l_Lake_LogIO_toBaseIO___redArg(v_self_3617_, v_cfg_3618_);
lean_dec_ref(v_cfg_3618_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO(lean_object* v_00_u03b1_3621_, lean_object* v_self_3622_, lean_object* v_cfg_3623_){
_start:
{
lean_object* v___y_3626_; uint8_t v___y_3627_; lean_object* v___y_3630_; uint8_t v___y_3631_; lean_object* v___y_3632_; lean_object* v___x_3633_; lean_object* v___y_3635_; lean_object* v___y_3636_; uint8_t v___y_3637_; uint8_t v___y_3638_; lean_object* v___y_3660_; lean_object* v___y_3661_; uint8_t v___y_3662_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3633_ = l_instMonadBaseIO;
v___x_3664_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3665_ = lean_apply_2(v_self_3622_, v___x_3664_, lean_box(0));
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v_a_3666_; lean_object* v_a_3667_; uint8_t v_failLv_3668_; uint8_t v_outLv_3669_; lean_object* v___x_3670_; uint8_t v___x_3671_; uint8_t v___x_3672_; 
v_a_3666_ = lean_ctor_get(v___x_3665_, 0);
lean_inc(v_a_3666_);
v_a_3667_ = lean_ctor_get(v___x_3665_, 1);
lean_inc(v_a_3667_);
lean_dec_ref(v___x_3665_);
v_failLv_3668_ = lean_ctor_get_uint8(v_cfg_3623_, sizeof(void*)*1);
v_outLv_3669_ = lean_ctor_get_uint8(v_cfg_3623_, sizeof(void*)*1 + 1);
v___x_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3670_, 0, v_a_3666_);
v___x_3671_ = l_Lake_Log_maxLv(v_a_3667_);
v___x_3672_ = l_Lake_instOrdLogLevel_ord(v_failLv_3668_, v___x_3671_);
if (v___x_3672_ == 2)
{
uint8_t v___x_3673_; 
v___x_3673_ = 0;
v___y_3635_ = v_a_3667_;
v___y_3636_ = v___x_3670_;
v___y_3637_ = v___x_3673_;
v___y_3638_ = v_outLv_3669_;
goto v___jp_3634_;
}
else
{
uint8_t v___x_3674_; 
v___x_3674_ = 1;
v___y_3660_ = v_a_3667_;
v___y_3661_ = v___x_3670_;
v___y_3662_ = v___x_3674_;
goto v___jp_3659_;
}
}
else
{
lean_object* v_a_3675_; lean_object* v___x_3676_; uint8_t v___x_3677_; 
v_a_3675_ = lean_ctor_get(v___x_3665_, 1);
lean_inc(v_a_3675_);
lean_dec_ref(v___x_3665_);
v___x_3676_ = lean_box(0);
v___x_3677_ = 1;
v___y_3660_ = v_a_3675_;
v___y_3661_ = v___x_3676_;
v___y_3662_ = v___x_3677_;
goto v___jp_3659_;
}
v___jp_3625_:
{
if (v___y_3627_ == 0)
{
return v___y_3626_;
}
else
{
lean_object* v___x_3628_; 
lean_dec(v___y_3626_);
v___x_3628_ = lean_box(0);
return v___x_3628_;
}
}
v___jp_3629_:
{
v___y_3626_ = v___y_3630_;
v___y_3627_ = v___y_3631_;
goto v___jp_3625_;
}
v___jp_3634_:
{
uint8_t v_ansiMode_3639_; lean_object* v_out_3640_; lean_object* v___x_3641_; uint8_t v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; uint8_t v___x_3645_; 
v_ansiMode_3639_ = lean_ctor_get_uint8(v_cfg_3623_, sizeof(void*)*1 + 2);
v_out_3640_ = lean_ctor_get(v_cfg_3623_, 0);
v___x_3641_ = l_Lake_OutStream_get(v_out_3640_);
lean_inc_ref(v___x_3641_);
v___x_3642_ = l_Lake_AnsiMode_isEnabled(v___x_3641_, v_ansiMode_3639_);
v___x_3643_ = lean_unsigned_to_nat(0u);
v___x_3644_ = lean_array_get_size(v___y_3635_);
v___x_3645_ = lean_nat_dec_lt(v___x_3643_, v___x_3644_);
if (v___x_3645_ == 0)
{
lean_dec_ref(v___x_3641_);
lean_dec_ref(v___y_3635_);
v___y_3626_ = v___y_3636_;
v___y_3627_ = v___y_3637_;
goto v___jp_3625_;
}
else
{
lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___f_3648_; lean_object* v___x_3649_; uint8_t v___x_3650_; 
v___x_3646_ = lean_box(v___y_3638_);
v___x_3647_ = lean_box(v___x_3642_);
v___f_3648_ = lean_alloc_closure((void*)(l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_3648_, 0, v___x_3641_);
lean_closure_set(v___f_3648_, 1, v___x_3646_);
lean_closure_set(v___f_3648_, 2, v___x_3647_);
v___x_3649_ = lean_box(0);
v___x_3650_ = lean_nat_dec_le(v___x_3644_, v___x_3644_);
if (v___x_3650_ == 0)
{
if (v___x_3645_ == 0)
{
lean_dec_ref(v___f_3648_);
lean_dec_ref(v___y_3635_);
v___y_3626_ = v___y_3636_;
v___y_3627_ = v___y_3637_;
goto v___jp_3625_;
}
else
{
size_t v___x_3651_; size_t v___x_3652_; lean_object* v___x_791__overap_3653_; lean_object* v___x_3654_; 
v___x_3651_ = ((size_t)0ULL);
v___x_3652_ = lean_usize_of_nat(v___x_3644_);
v___x_791__overap_3653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3633_, v___f_3648_, v___y_3635_, v___x_3651_, v___x_3652_, v___x_3649_);
v___x_3654_ = lean_apply_1(v___x_791__overap_3653_, lean_box(0));
v___y_3630_ = v___y_3636_;
v___y_3631_ = v___y_3637_;
v___y_3632_ = v___x_3654_;
goto v___jp_3629_;
}
}
else
{
size_t v___x_3655_; size_t v___x_3656_; lean_object* v___x_794__overap_3657_; lean_object* v___x_3658_; 
v___x_3655_ = ((size_t)0ULL);
v___x_3656_ = lean_usize_of_nat(v___x_3644_);
v___x_794__overap_3657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3633_, v___f_3648_, v___y_3635_, v___x_3655_, v___x_3656_, v___x_3649_);
v___x_3658_ = lean_apply_1(v___x_794__overap_3657_, lean_box(0));
v___y_3630_ = v___y_3636_;
v___y_3631_ = v___y_3637_;
v___y_3632_ = v___x_3658_;
goto v___jp_3629_;
}
}
}
v___jp_3659_:
{
uint8_t v___x_3663_; 
v___x_3663_ = 0;
v___y_3635_ = v___y_3660_;
v___y_3636_ = v___y_3661_;
v___y_3637_ = v___y_3662_;
v___y_3638_ = v___x_3663_;
goto v___jp_3634_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___boxed(lean_object* v_00_u03b1_3678_, lean_object* v_self_3679_, lean_object* v_cfg_3680_, lean_object* v_a_3681_){
_start:
{
lean_object* v_res_3682_; 
v_res_3682_ = l_Lake_LogIO_toBaseIO(v_00_u03b1_3678_, v_self_3679_, v_cfg_3680_);
lean_dec_ref(v_cfg_3680_);
return v_res_3682_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_captureLog___redArg(lean_object* v_inst_3683_, lean_object* v_self_3684_, lean_object* v_log_3685_){
_start:
{
lean_object* v_map_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; 
v_map_3686_ = lean_ctor_get(v_inst_3683_, 0);
lean_inc(v_map_3686_);
lean_dec_ref(v_inst_3683_);
v___x_3687_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3688_ = lean_apply_1(v_self_3684_, v_log_3685_);
v___x_3689_ = lean_apply_4(v_map_3686_, lean_box(0), lean_box(0), v___x_3687_, v___x_3688_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_captureLog(lean_object* v_m_3690_, lean_object* v_00_u03b1_3691_, lean_object* v_inst_3692_, lean_object* v_self_3693_, lean_object* v_log_3694_){
_start:
{
lean_object* v_map_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v_map_3695_ = lean_ctor_get(v_inst_3692_, 0);
lean_inc(v_map_3695_);
lean_dec_ref(v_inst_3692_);
v___x_3696_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3697_ = lean_apply_1(v_self_3693_, v_log_3694_);
v___x_3698_ = lean_apply_4(v_map_3695_, lean_box(0), lean_box(0), v___x_3696_, v___x_3697_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadError___lam__0(lean_object* v_00_u03b1_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_){
_start:
{
uint8_t v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3703_ = 3;
v___x_3704_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3704_, 0, v___y_3700_);
lean_ctor_set_uint8(v___x_3704_, sizeof(void*)*1, v___x_3703_);
lean_inc_ref(v___y_3701_);
v___x_3705_ = lean_apply_2(v___y_3701_, v___x_3704_, lean_box(0));
v___x_3706_ = lean_box(0);
v___x_3707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3706_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadError___lam__0___boxed(lean_object* v_00_u03b1_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_){
_start:
{
lean_object* v_res_3712_; 
v_res_3712_ = l_Lake_LoggerIO_instMonadError___lam__0(v_00_u03b1_3708_, v___y_3709_, v___y_3710_);
lean_dec_ref(v___y_3710_);
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftIO___lam__0(lean_object* v_00_u03b1_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
lean_object* v___x_3719_; 
v___x_3719_ = lean_apply_1(v___y_3716_, lean_box(0));
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
v_a_3720_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3722_ = v___x_3719_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3719_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3720_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
else
{
lean_object* v_a_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3740_; 
v_a_3728_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3730_ = v___x_3719_;
v_isShared_3731_ = v_isSharedCheck_3740_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_a_3728_);
lean_dec(v___x_3719_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3740_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3732_; uint8_t v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3738_; 
v___x_3732_ = lean_io_error_to_string(v_a_3728_);
v___x_3733_ = 3;
v___x_3734_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3734_, 0, v___x_3732_);
lean_ctor_set_uint8(v___x_3734_, sizeof(void*)*1, v___x_3733_);
lean_inc_ref(v___y_3717_);
v___x_3735_ = lean_apply_2(v___y_3717_, v___x_3734_, lean_box(0));
v___x_3736_ = lean_box(0);
if (v_isShared_3731_ == 0)
{
lean_ctor_set(v___x_3730_, 0, v___x_3736_);
v___x_3738_ = v___x_3730_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3736_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftIO___lam__0___boxed(lean_object* v_00_u03b1_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_){
_start:
{
lean_object* v_res_3745_; 
v_res_3745_ = l_Lake_LoggerIO_instMonadLiftIO___lam__0(v_00_u03b1_3741_, v___y_3742_, v___y_3743_);
lean_dec_ref(v___y_3743_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__0(lean_object* v_x_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_){
_start:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
lean_inc_ref(v___y_3750_);
v___x_3752_ = lean_apply_2(v___y_3750_, v___y_3749_, lean_box(0));
v___x_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3752_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__0___boxed(lean_object* v_x_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
lean_object* v_res_3758_; 
v_res_3758_ = l_Lake_LoggerIO_instMonadLiftLogIO___lam__0(v_x_3754_, v___y_3755_, v___y_3756_);
lean_dec_ref(v___y_3756_);
return v_res_3758_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__2(lean_object* v___x_3759_, lean_object* v___f_3760_, lean_object* v___f_3761_, lean_object* v_00_u03b1_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3769_ = lean_unsigned_to_nat(0u);
v___x_3770_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3771_ = lean_apply_2(v___y_3763_, v___x_3770_, lean_box(0));
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v_a_3772_; lean_object* v_a_3773_; lean_object* v___x_3774_; uint8_t v___x_3775_; 
lean_dec_ref(v___f_3761_);
v_a_3772_ = lean_ctor_get(v___x_3771_, 0);
lean_inc(v_a_3772_);
v_a_3773_ = lean_ctor_get(v___x_3771_, 1);
lean_inc(v_a_3773_);
lean_dec_ref(v___x_3771_);
v___x_3774_ = lean_array_get_size(v_a_3773_);
v___x_3775_ = lean_nat_dec_lt(v___x_3769_, v___x_3774_);
if (v___x_3775_ == 0)
{
lean_object* v___x_3776_; 
lean_dec(v_a_3773_);
lean_dec_ref(v___f_3760_);
lean_dec_ref(v___x_3759_);
v___x_3776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3776_, 0, v_a_3772_);
return v___x_3776_;
}
else
{
lean_object* v___x_3777_; uint8_t v___x_3778_; 
v___x_3777_ = lean_box(0);
v___x_3778_ = lean_nat_dec_le(v___x_3774_, v___x_3774_);
if (v___x_3778_ == 0)
{
if (v___x_3775_ == 0)
{
lean_object* v___x_3779_; 
lean_dec(v_a_3773_);
lean_dec_ref(v___f_3760_);
lean_dec_ref(v___x_3759_);
v___x_3779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3779_, 0, v_a_3772_);
return v___x_3779_;
}
else
{
size_t v___x_3780_; size_t v___x_3781_; lean_object* v___x_1796__overap_3782_; lean_object* v___x_3783_; 
v___x_3780_ = ((size_t)0ULL);
v___x_3781_ = lean_usize_of_nat(v___x_3774_);
v___x_1796__overap_3782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3759_, v___f_3760_, v_a_3773_, v___x_3780_, v___x_3781_, v___x_3777_);
lean_inc_ref(v___y_3764_);
v___x_3783_ = lean_apply_2(v___x_1796__overap_3782_, v___y_3764_, lean_box(0));
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3790_ == 0)
{
lean_object* v_unused_3791_; 
v_unused_3791_ = lean_ctor_get(v___x_3783_, 0);
lean_dec(v_unused_3791_);
v___x_3785_ = v___x_3783_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_dec(v___x_3783_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 0, v_a_3772_);
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3772_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
else
{
lean_object* v_a_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3799_; 
lean_dec(v_a_3772_);
v_a_3792_ = lean_ctor_get(v___x_3783_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3794_ = v___x_3783_;
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_a_3792_);
lean_dec(v___x_3783_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3797_; 
if (v_isShared_3795_ == 0)
{
v___x_3797_ = v___x_3794_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3792_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
}
else
{
size_t v___x_3800_; size_t v___x_3801_; lean_object* v___x_1805__overap_3802_; lean_object* v___x_3803_; 
v___x_3800_ = ((size_t)0ULL);
v___x_3801_ = lean_usize_of_nat(v___x_3774_);
v___x_1805__overap_3802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3759_, v___f_3760_, v_a_3773_, v___x_3800_, v___x_3801_, v___x_3777_);
lean_inc_ref(v___y_3764_);
v___x_3803_ = lean_apply_2(v___x_1805__overap_3802_, v___y_3764_, lean_box(0));
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3810_; 
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3810_ == 0)
{
lean_object* v_unused_3811_; 
v_unused_3811_ = lean_ctor_get(v___x_3803_, 0);
lean_dec(v_unused_3811_);
v___x_3805_ = v___x_3803_;
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
else
{
lean_dec(v___x_3803_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3808_; 
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 0, v_a_3772_);
v___x_3808_ = v___x_3805_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_a_3772_);
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
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3819_; 
lean_dec(v_a_3772_);
v_a_3812_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3814_ = v___x_3803_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3803_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3817_; 
if (v_isShared_3815_ == 0)
{
v___x_3817_ = v___x_3814_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3812_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
}
}
}
else
{
lean_object* v_a_3820_; lean_object* v___x_3821_; uint8_t v___x_3822_; 
lean_dec_ref(v___f_3760_);
v_a_3820_ = lean_ctor_get(v___x_3771_, 1);
lean_inc(v_a_3820_);
lean_dec_ref(v___x_3771_);
v___x_3821_ = lean_array_get_size(v_a_3820_);
v___x_3822_ = lean_nat_dec_lt(v___x_3769_, v___x_3821_);
if (v___x_3822_ == 0)
{
lean_object* v___x_3823_; lean_object* v___x_3824_; 
lean_dec(v_a_3820_);
lean_dec_ref(v___f_3761_);
lean_dec_ref(v___x_3759_);
v___x_3823_ = lean_box(0);
v___x_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3823_);
return v___x_3824_;
}
else
{
lean_object* v___x_3825_; uint8_t v___x_3826_; 
v___x_3825_ = lean_box(0);
v___x_3826_ = lean_nat_dec_le(v___x_3821_, v___x_3821_);
if (v___x_3826_ == 0)
{
if (v___x_3822_ == 0)
{
lean_dec(v_a_3820_);
lean_dec_ref(v___f_3761_);
lean_dec_ref(v___x_3759_);
goto v___jp_3766_;
}
else
{
size_t v___x_3827_; size_t v___x_3828_; lean_object* v___x_1826__overap_3829_; lean_object* v___x_3830_; 
v___x_3827_ = ((size_t)0ULL);
v___x_3828_ = lean_usize_of_nat(v___x_3821_);
v___x_1826__overap_3829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3759_, v___f_3761_, v_a_3820_, v___x_3827_, v___x_3828_, v___x_3825_);
lean_inc_ref(v___y_3764_);
v___x_3830_ = lean_apply_2(v___x_1826__overap_3829_, v___y_3764_, lean_box(0));
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_dec_ref(v___x_3830_);
goto v___jp_3766_;
}
else
{
lean_object* v_a_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3838_; 
v_a_3831_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3833_ = v___x_3830_;
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_a_3831_);
lean_dec(v___x_3830_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v___x_3836_; 
if (v_isShared_3834_ == 0)
{
v___x_3836_ = v___x_3833_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_a_3831_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
}
}
}
else
{
size_t v___x_3839_; size_t v___x_3840_; lean_object* v___x_1834__overap_3841_; lean_object* v___x_3842_; 
v___x_3839_ = ((size_t)0ULL);
v___x_3840_ = lean_usize_of_nat(v___x_3821_);
v___x_1834__overap_3841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3759_, v___f_3761_, v_a_3820_, v___x_3839_, v___x_3840_, v___x_3825_);
lean_inc_ref(v___y_3764_);
v___x_3842_ = lean_apply_2(v___x_1834__overap_3841_, v___y_3764_, lean_box(0));
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_dec_ref(v___x_3842_);
goto v___jp_3766_;
}
else
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3850_; 
v_a_3843_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3845_ = v___x_3842_;
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3842_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3848_; 
if (v_isShared_3846_ == 0)
{
v___x_3848_ = v___x_3845_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_a_3843_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
}
}
}
}
v___jp_3766_:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; 
v___x_3767_ = lean_box(0);
v___x_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3767_);
return v___x_3768_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__2___boxed(lean_object* v___x_3851_, lean_object* v___f_3852_, lean_object* v___f_3853_, lean_object* v_00_u03b1_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l_Lake_LoggerIO_instMonadLiftLogIO___lam__2(v___x_3851_, v___f_3852_, v___f_3853_, v_00_u03b1_3854_, v___y_3855_, v___y_3856_);
lean_dec_ref(v___y_3856_);
return v_res_3858_;
}
}
static lean_object* _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__1(void){
_start:
{
lean_object* v___x_3860_; 
v___x_3860_ = l_instMonadEIO(lean_box(0));
return v___x_3860_;
}
}
static lean_object* _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__2(void){
_start:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3861_ = lean_obj_once(&l_Lake_LoggerIO_instMonadLiftLogIO___closed__1, &l_Lake_LoggerIO_instMonadLiftLogIO___closed__1_once, _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__1);
v___x_3862_ = l_ReaderT_instMonad___redArg(v___x_3861_);
return v___x_3862_;
}
}
static lean_object* _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__3(void){
_start:
{
lean_object* v___f_3863_; lean_object* v___x_3864_; lean_object* v___f_3865_; 
v___f_3863_ = ((lean_object*)(l_Lake_LoggerIO_instMonadLiftLogIO___closed__0));
v___x_3864_ = lean_obj_once(&l_Lake_LoggerIO_instMonadLiftLogIO___closed__2, &l_Lake_LoggerIO_instMonadLiftLogIO___closed__2_once, _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__2);
v___f_3865_ = lean_alloc_closure((void*)(l_Lake_LoggerIO_instMonadLiftLogIO___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3865_, 0, v___x_3864_);
lean_closure_set(v___f_3865_, 1, v___f_3863_);
lean_closure_set(v___f_3865_, 2, v___f_3863_);
return v___f_3865_;
}
}
static lean_object* _init_l_Lake_LoggerIO_instMonadLiftLogIO(void){
_start:
{
lean_object* v___f_3866_; 
v___f_3866_ = lean_obj_once(&l_Lake_LoggerIO_instMonadLiftLogIO___closed__3, &l_Lake_LoggerIO_instMonadLiftLogIO___closed__3_once, _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__3);
return v___f_3866_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg___lam__0(lean_object* v_val_3867_, uint8_t v_outLv_3868_, uint8_t v_val_3869_, lean_object* v_e_3870_){
_start:
{
lean_object* v___x_3872_; 
v___x_3872_ = l_Lake_logToStream(v_e_3870_, v_val_3867_, v_outLv_3868_, v_val_3869_);
return v___x_3872_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg___lam__0___boxed(lean_object* v_val_3873_, lean_object* v_outLv_3874_, lean_object* v_val_3875_, lean_object* v_e_3876_, lean_object* v___y_3877_){
_start:
{
uint8_t v_outLv_boxed_3878_; uint8_t v_val_178__boxed_3879_; lean_object* v_res_3880_; 
v_outLv_boxed_3878_ = lean_unbox(v_outLv_3874_);
v_val_178__boxed_3879_ = lean_unbox(v_val_3875_);
v_res_3880_ = l_Lake_LoggerIO_toBaseIO___redArg___lam__0(v_val_3873_, v_outLv_boxed_3878_, v_val_178__boxed_3879_, v_e_3876_);
lean_dec_ref(v_e_3876_);
return v_res_3880_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg(lean_object* v_self_3881_, lean_object* v_cfg_3882_){
_start:
{
uint8_t v_outLv_3884_; uint8_t v_ansiMode_3885_; lean_object* v_out_3886_; lean_object* v___x_3887_; uint8_t v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___f_3891_; lean_object* v___x_3892_; 
v_outLv_3884_ = lean_ctor_get_uint8(v_cfg_3882_, sizeof(void*)*1 + 1);
v_ansiMode_3885_ = lean_ctor_get_uint8(v_cfg_3882_, sizeof(void*)*1 + 2);
v_out_3886_ = lean_ctor_get(v_cfg_3882_, 0);
v___x_3887_ = l_Lake_OutStream_get(v_out_3886_);
lean_inc_ref(v___x_3887_);
v___x_3888_ = l_Lake_AnsiMode_isEnabled(v___x_3887_, v_ansiMode_3885_);
v___x_3889_ = lean_box(v_outLv_3884_);
v___x_3890_ = lean_box(v___x_3888_);
v___f_3891_ = lean_alloc_closure((void*)(l_Lake_LoggerIO_toBaseIO___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3891_, 0, v___x_3887_);
lean_closure_set(v___f_3891_, 1, v___x_3889_);
lean_closure_set(v___f_3891_, 2, v___x_3890_);
v___x_3892_ = lean_apply_2(v_self_3881_, v___f_3891_, lean_box(0));
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3900_; 
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3895_ = v___x_3892_;
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3892_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3898_; 
if (v_isShared_3896_ == 0)
{
lean_ctor_set_tag(v___x_3895_, 1);
v___x_3898_ = v___x_3895_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v_a_3893_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
else
{
lean_object* v___x_3901_; 
lean_dec_ref(v___x_3892_);
v___x_3901_ = lean_box(0);
return v___x_3901_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg___boxed(lean_object* v_self_3902_, lean_object* v_cfg_3903_, lean_object* v_a_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l_Lake_LoggerIO_toBaseIO___redArg(v_self_3902_, v_cfg_3903_);
lean_dec_ref(v_cfg_3903_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO(lean_object* v_00_u03b1_3906_, lean_object* v_self_3907_, lean_object* v_cfg_3908_){
_start:
{
uint8_t v_outLv_3910_; uint8_t v_ansiMode_3911_; lean_object* v_out_3912_; lean_object* v___x_3913_; uint8_t v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___f_3917_; lean_object* v___x_3918_; 
v_outLv_3910_ = lean_ctor_get_uint8(v_cfg_3908_, sizeof(void*)*1 + 1);
v_ansiMode_3911_ = lean_ctor_get_uint8(v_cfg_3908_, sizeof(void*)*1 + 2);
v_out_3912_ = lean_ctor_get(v_cfg_3908_, 0);
v___x_3913_ = l_Lake_OutStream_get(v_out_3912_);
lean_inc_ref(v___x_3913_);
v___x_3914_ = l_Lake_AnsiMode_isEnabled(v___x_3913_, v_ansiMode_3911_);
v___x_3915_ = lean_box(v_outLv_3910_);
v___x_3916_ = lean_box(v___x_3914_);
v___f_3917_ = lean_alloc_closure((void*)(l_Lake_LoggerIO_toBaseIO___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3917_, 0, v___x_3913_);
lean_closure_set(v___f_3917_, 1, v___x_3915_);
lean_closure_set(v___f_3917_, 2, v___x_3916_);
v___x_3918_ = lean_apply_2(v_self_3907_, v___f_3917_, lean_box(0));
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v_a_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3926_; 
v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3921_ = v___x_3918_;
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_a_3919_);
lean_dec(v___x_3918_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3924_; 
if (v_isShared_3922_ == 0)
{
lean_ctor_set_tag(v___x_3921_, 1);
v___x_3924_ = v___x_3921_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3919_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
else
{
lean_object* v___x_3927_; 
lean_dec_ref(v___x_3918_);
v___x_3927_ = lean_box(0);
return v___x_3927_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___boxed(lean_object* v_00_u03b1_3928_, lean_object* v_self_3929_, lean_object* v_cfg_3930_, lean_object* v_a_3931_){
_start:
{
lean_object* v_res_3932_; 
v_res_3932_ = l_Lake_LoggerIO_toBaseIO(v_00_u03b1_3928_, v_self_3929_, v_cfg_3930_);
lean_dec_ref(v_cfg_3930_);
return v_res_3932_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg___lam__0(lean_object* v_val_3933_, lean_object* v_e_3934_){
_start:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; 
v___x_3936_ = lean_st_ref_take(v_val_3933_);
v___x_3937_ = lean_array_push(v___x_3936_, v_e_3934_);
v___x_3938_ = lean_st_ref_set(v_val_3933_, v___x_3937_);
return v___x_3938_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg___lam__0___boxed(lean_object* v_val_3939_, lean_object* v_e_3940_, lean_object* v___y_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l_Lake_LoggerIO_captureLog___redArg___lam__0(v_val_3939_, v_e_3940_);
lean_dec(v_val_3939_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg(lean_object* v_self_3943_){
_start:
{
lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v_val_3952_; lean_object* v___f_3963_; lean_object* v___x_3964_; 
v___x_3949_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3950_ = lean_st_mk_ref(v___x_3949_);
lean_inc(v___x_3950_);
v___f_3963_ = lean_alloc_closure((void*)(l_Lake_LoggerIO_captureLog___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3963_, 0, v___x_3950_);
v___x_3964_ = lean_apply_2(v_self_3943_, v___f_3963_, lean_box(0));
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3972_; 
v_a_3965_ = lean_ctor_get(v___x_3964_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3964_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3967_ = v___x_3964_;
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3964_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
if (v_isShared_3968_ == 0)
{
lean_ctor_set_tag(v___x_3967_, 1);
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
v___x_3970_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
v_val_3952_ = v___x_3970_;
goto v___jp_3951_;
}
}
}
else
{
lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3980_; 
v_a_3973_ = lean_ctor_get(v___x_3964_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3964_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3975_ = v___x_3964_;
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_a_3973_);
lean_dec(v___x_3964_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
lean_ctor_set_tag(v___x_3975_, 0);
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_a_3973_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
v_val_3952_ = v___x_3978_;
goto v___jp_3951_;
}
}
}
v___jp_3945_:
{
lean_object* v___x_3948_; 
v___x_3948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3948_, 0, v___y_3947_);
lean_ctor_set(v___x_3948_, 1, v___y_3946_);
return v___x_3948_;
}
v___jp_3951_:
{
lean_object* v___x_3953_; 
v___x_3953_ = lean_st_ref_get(v___x_3950_);
lean_dec(v___x_3950_);
if (lean_obj_tag(v_val_3952_) == 0)
{
lean_object* v___x_3954_; 
lean_dec_ref(v_val_3952_);
v___x_3954_ = lean_box(0);
v___y_3946_ = v___x_3953_;
v___y_3947_ = v___x_3954_;
goto v___jp_3945_;
}
else
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
v_a_3955_ = lean_ctor_get(v_val_3952_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v_val_3952_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v_val_3952_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v_val_3952_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
v___y_3946_ = v___x_3953_;
v___y_3947_ = v___x_3960_;
goto v___jp_3945_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg___boxed(lean_object* v_self_3981_, lean_object* v_a_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l_Lake_LoggerIO_captureLog___redArg(v_self_3981_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog(lean_object* v_00_u03b1_3984_, lean_object* v_self_3985_){
_start:
{
lean_object* v___x_3987_; 
v___x_3987_ = l_Lake_LoggerIO_captureLog___redArg(v_self_3985_);
return v___x_3987_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___boxed(lean_object* v_00_u03b1_3988_, lean_object* v_self_3989_, lean_object* v_a_3990_){
_start:
{
lean_object* v_res_3991_; 
v_res_3991_ = l_Lake_LoggerIO_captureLog(v_00_u03b1_3988_, v_self_3989_);
return v_res_3991_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f___redArg(lean_object* v_self_3992_){
_start:
{
lean_object* v___x_3994_; 
v___x_3994_ = l_Lake_LoggerIO_captureLog___redArg(v_self_3992_);
return v___x_3994_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f___redArg___boxed(lean_object* v_self_3995_, lean_object* v_a_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l_Lake_LoggerIO_run_x3f___redArg(v_self_3995_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f(lean_object* v_00_u03b1_3998_, lean_object* v_self_3999_){
_start:
{
lean_object* v___x_4001_; 
v___x_4001_ = l_Lake_LoggerIO_captureLog___redArg(v_self_3999_);
return v___x_4001_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f___boxed(lean_object* v_00_u03b1_4002_, lean_object* v_self_4003_, lean_object* v_a_4004_){
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l_Lake_LoggerIO_run_x3f(v_00_u03b1_4002_, v_self_4003_);
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27___redArg(lean_object* v_self_4006_, lean_object* v_logger_4007_){
_start:
{
lean_object* v___x_4009_; 
v___x_4009_ = lean_apply_2(v_self_4006_, v_logger_4007_, lean_box(0));
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4017_; 
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4012_ = v___x_4009_;
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_4009_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4015_; 
if (v_isShared_4013_ == 0)
{
lean_ctor_set_tag(v___x_4012_, 1);
v___x_4015_ = v___x_4012_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_a_4010_);
v___x_4015_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
return v___x_4015_;
}
}
}
else
{
lean_object* v___x_4018_; 
lean_dec_ref(v___x_4009_);
v___x_4018_ = lean_box(0);
return v___x_4018_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27___redArg___boxed(lean_object* v_self_4019_, lean_object* v_logger_4020_, lean_object* v_a_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l_Lake_LoggerIO_run_x3f_x27___redArg(v_self_4019_, v_logger_4020_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27(lean_object* v_00_u03b1_4023_, lean_object* v_self_4024_, lean_object* v_logger_4025_){
_start:
{
lean_object* v___x_4027_; 
v___x_4027_ = lean_apply_2(v_self_4024_, v_logger_4025_, lean_box(0));
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4030_ = v___x_4027_;
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4027_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4033_; 
if (v_isShared_4031_ == 0)
{
lean_ctor_set_tag(v___x_4030_, 1);
v___x_4033_ = v___x_4030_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_a_4028_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
}
}
}
else
{
lean_object* v___x_4036_; 
lean_dec_ref(v___x_4027_);
v___x_4036_ = lean_box(0);
return v___x_4036_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27___boxed(lean_object* v_00_u03b1_4037_, lean_object* v_self_4038_, lean_object* v_logger_4039_, lean_object* v_a_4040_){
_start:
{
lean_object* v_res_4041_; 
v_res_4041_ = l_Lake_LoggerIO_run_x3f_x27(v_00_u03b1_4037_, v_self_4038_, v_logger_4039_);
return v_res_4041_;
}
}
lean_object* runtime_initialize_Lean_Data_Json(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Error(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_EStateT(uint8_t builtin);
lean_object* runtime_initialize_Lean_Message(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Lift(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Log(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
