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
lean_object* l_instMonadEST(lean_object*, lean_object*);
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
lean_object* l_instMonadST(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___redArg(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lake_LogIO_toBaseIO___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LogIO_toBaseIO___redArg___closed__0;
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
uint8_t v_x_258__boxed_312_; uint8_t v_res_313_; lean_object* v_r_314_; 
v_x_258__boxed_312_ = lean_unbox(v_x_310_);
v_res_313_ = l_Lake_AnsiMode_isEnabled(v_out_309_, v_x_258__boxed_312_);
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
uint8_t v_minLv_boxed_1464_; uint8_t v_val_214__boxed_1465_; lean_object* v_res_1466_; 
v_minLv_boxed_1464_ = lean_unbox(v_minLv_1460_);
v_val_214__boxed_1465_ = lean_unbox(v_val_1461_);
v_res_1466_ = l_Lake_OutStream_getLogger___redArg___lam__0(v_val_1459_, v_minLv_boxed_1464_, v_val_214__boxed_1465_, v_inst_1462_, v_e_1463_);
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
v___x_1535_ = lean_apply_2(v_toPure_1533_, lean_box(0), v___y_1530_);
v___x_1536_ = lean_apply_4(v_toBind_1532_, lean_box(0), lean_box(0), v___x_1535_, v___f_1534_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg(lean_object* v_inst_1537_, lean_object* v_inst_1538_){
_start:
{
lean_object* v___f_1539_; 
v___f_1539_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1539_, 0, v_inst_1537_);
lean_closure_set(v___f_1539_, 1, v_inst_1538_);
return v___f_1539_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT(lean_object* v_n_1540_, lean_object* v_m_1541_, lean_object* v_inst_1542_, lean_object* v_inst_1543_){
_start:
{
lean_object* v___f_1544_; 
v___f_1544_ = lean_alloc_closure((void*)(l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1544_, 0, v_inst_1542_);
lean_closure_set(v___f_1544_, 1, v_inst_1543_);
return v___f_1544_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___redArg(lean_object* v_f_1545_, lean_object* v_self_1546_, lean_object* v_a_1547_){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = lean_apply_1(v_f_1545_, v_a_1547_);
v___x_1549_ = lean_apply_1(v_self_1546_, v___x_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods(lean_object* v_n_1550_, lean_object* v_m_1551_, lean_object* v_m_x27_1552_, lean_object* v_00_u03b1_1553_, lean_object* v_inst_1554_, lean_object* v_f_1555_, lean_object* v_self_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = lean_apply_1(v_f_1555_, v_a_1557_);
v___x_1559_ = lean_apply_1(v_self_1556_, v___x_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___boxed(lean_object* v_n_1560_, lean_object* v_m_1561_, lean_object* v_m_x27_1562_, lean_object* v_00_u03b1_1563_, lean_object* v_inst_1564_, lean_object* v_f_1565_, lean_object* v_self_1566_, lean_object* v_a_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Lake_MonadLogT_adaptMethods(v_n_1560_, v_m_1561_, v_m_x27_1562_, v_00_u03b1_1563_, v_inst_1564_, v_f_1565_, v_self_1566_, v_a_1567_);
lean_dec_ref(v_inst_1564_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog___redArg(lean_object* v_inst_1569_, lean_object* v_self_1570_){
_start:
{
lean_object* v___f_1571_; lean_object* v___x_1572_; 
v___f_1571_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1571_, 0, v_inst_1569_);
v___x_1572_ = lean_apply_1(v_self_1570_, v___f_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog(lean_object* v_m_1573_, lean_object* v_n_1574_, lean_object* v_00_u03b1_1575_, lean_object* v_inst_1576_, lean_object* v_self_1577_){
_start:
{
lean_object* v___f_1578_; lean_object* v___x_1579_; 
v___f_1578_ = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1578_, 0, v_inst_1576_);
v___x_1579_ = lean_apply_1(v_self_1577_, v___f_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonLog___lam__0(lean_object* v___x_1584_, lean_object* v_x_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Array_toJson___redArg(v___x_1584_, v_x_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonLog___lam__0(lean_object* v___x_1590_, lean_object* v_x_1591_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Array_fromJson_x3f___redArg(v___x_1590_, v_x_1591_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1592_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1592_);
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
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
v_a_1601_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1592_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1592_);
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
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
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
}
}
static lean_object* _init_l_Lake_Log_instInhabitedPos_default(void){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_unsigned_to_nat(0u);
return v___x_1612_;
}
}
static lean_object* _init_l_Lake_Log_instInhabitedPos(void){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = lean_unsigned_to_nat(0u);
return v___x_1613_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_instDecidableEqPos_decEq(lean_object* v_x_1614_, lean_object* v_x_1615_){
_start:
{
uint8_t v___x_1616_; 
v___x_1616_ = lean_nat_dec_eq(v_x_1614_, v_x_1615_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_instDecidableEqPos_decEq___boxed(lean_object* v_x_1617_, lean_object* v_x_1618_){
_start:
{
uint8_t v_res_1619_; lean_object* v_r_1620_; 
v_res_1619_ = l_Lake_Log_instDecidableEqPos_decEq(v_x_1617_, v_x_1618_);
lean_dec(v_x_1618_);
lean_dec(v_x_1617_);
v_r_1620_ = lean_box(v_res_1619_);
return v_r_1620_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_instDecidableEqPos(lean_object* v_x_1621_, lean_object* v_x_1622_){
_start:
{
uint8_t v___x_1623_; 
v___x_1623_ = lean_nat_dec_eq(v_x_1621_, v_x_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_instDecidableEqPos___boxed(lean_object* v_x_1624_, lean_object* v_x_1625_){
_start:
{
uint8_t v_res_1626_; lean_object* v_r_1627_; 
v_res_1626_ = l_Lake_Log_instDecidableEqPos(v_x_1624_, v_x_1625_);
lean_dec(v_x_1625_);
lean_dec(v_x_1624_);
v_r_1627_ = lean_box(v_res_1626_);
return v_r_1627_;
}
}
static lean_object* _init_l_Lake_instOfNatPos(void){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = lean_unsigned_to_nat(0u);
return v___x_1628_;
}
}
LEAN_EXPORT uint8_t l_Lake_instOrdPos___lam__0(lean_object* v_x1_1629_, lean_object* v_x2_1630_){
_start:
{
uint8_t v___x_1631_; 
v___x_1631_ = lean_nat_dec_lt(v_x1_1629_, v_x2_1630_);
if (v___x_1631_ == 0)
{
uint8_t v___x_1632_; 
v___x_1632_ = lean_nat_dec_eq(v_x1_1629_, v_x2_1630_);
if (v___x_1632_ == 0)
{
uint8_t v___x_1633_; 
v___x_1633_ = 2;
return v___x_1633_;
}
else
{
uint8_t v___x_1634_; 
v___x_1634_ = 1;
return v___x_1634_;
}
}
else
{
uint8_t v___x_1635_; 
v___x_1635_ = 0;
return v___x_1635_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instOrdPos___lam__0___boxed(lean_object* v_x1_1636_, lean_object* v_x2_1637_){
_start:
{
uint8_t v_res_1638_; lean_object* v_r_1639_; 
v_res_1638_ = l_Lake_instOrdPos___lam__0(v_x1_1636_, v_x2_1637_);
lean_dec(v_x2_1637_);
lean_dec(v_x1_1636_);
v_r_1639_ = lean_box(v_res_1638_);
return v_r_1639_;
}
}
static lean_object* _init_l_Lake_instLTPos(void){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = lean_box(0);
return v___x_1642_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableRelPosLt(lean_object* v_a_1643_, lean_object* v_b_1644_){
_start:
{
uint8_t v___x_1645_; 
v___x_1645_ = lean_nat_dec_lt(v_a_1643_, v_b_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableRelPosLt___boxed(lean_object* v_a_1646_, lean_object* v_b_1647_){
_start:
{
uint8_t v_res_1648_; lean_object* v_r_1649_; 
v_res_1648_ = l_Lake_instDecidableRelPosLt(v_a_1646_, v_b_1647_);
lean_dec(v_b_1647_);
lean_dec(v_a_1646_);
v_r_1649_ = lean_box(v_res_1648_);
return v_r_1649_;
}
}
static lean_object* _init_l_Lake_instLEPos(void){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = lean_box(0);
return v___x_1650_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableRelPosLe(lean_object* v_a_1651_, lean_object* v_b_1652_){
_start:
{
uint8_t v___x_1653_; 
v___x_1653_ = lean_nat_dec_le(v_a_1651_, v_b_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableRelPosLe___boxed(lean_object* v_a_1654_, lean_object* v_b_1655_){
_start:
{
uint8_t v_res_1656_; lean_object* v_r_1657_; 
v_res_1656_ = l_Lake_instDecidableRelPosLe(v_a_1654_, v_b_1655_);
lean_dec(v_b_1655_);
lean_dec(v_a_1654_);
v_r_1657_ = lean_box(v_res_1656_);
return v_r_1657_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMinPos___lam__0(lean_object* v_x_1658_, lean_object* v_y_1659_){
_start:
{
uint8_t v___x_1660_; 
v___x_1660_ = lean_nat_dec_le(v_x_1658_, v_y_1659_);
if (v___x_1660_ == 0)
{
lean_inc(v_y_1659_);
return v_y_1659_;
}
else
{
lean_inc(v_x_1658_);
return v_x_1658_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMinPos___lam__0___boxed(lean_object* v_x_1661_, lean_object* v_y_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Lake_instMinPos___lam__0(v_x_1661_, v_y_1662_);
lean_dec(v_y_1662_);
lean_dec(v_x_1661_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxPos___lam__0(lean_object* v_x_1666_, lean_object* v_y_1667_){
_start:
{
uint8_t v___x_1668_; 
v___x_1668_ = lean_nat_dec_le(v_x_1666_, v_y_1667_);
if (v___x_1668_ == 0)
{
lean_inc(v_x_1666_);
return v_x_1666_;
}
else
{
lean_inc(v_y_1667_);
return v_y_1667_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxPos___lam__0___boxed(lean_object* v_x_1669_, lean_object* v_y_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Lake_instMaxPos___lam__0(v_x_1669_, v_y_1670_);
lean_dec(v_y_1670_);
lean_dec(v_x_1669_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_size(lean_object* v_log_1678_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = lean_array_get_size(v_log_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_size___boxed(lean_object* v_log_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Lake_Log_size(v_log_1680_);
lean_dec_ref(v_log_1680_);
return v_res_1681_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_isEmpty(lean_object* v_log_1682_){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; uint8_t v___x_1685_; 
v___x_1683_ = lean_array_get_size(v_log_1682_);
v___x_1684_ = lean_unsigned_to_nat(0u);
v___x_1685_ = lean_nat_dec_eq(v___x_1683_, v___x_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_isEmpty___boxed(lean_object* v_log_1686_){
_start:
{
uint8_t v_res_1687_; lean_object* v_r_1688_; 
v_res_1687_ = l_Lake_Log_isEmpty(v_log_1686_);
lean_dec_ref(v_log_1686_);
v_r_1688_ = lean_box(v_res_1687_);
return v_r_1688_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_hasEntries(lean_object* v_log_1689_){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; 
v___x_1690_ = lean_array_get_size(v_log_1689_);
v___x_1691_ = lean_unsigned_to_nat(0u);
v___x_1692_ = lean_nat_dec_eq(v___x_1690_, v___x_1691_);
if (v___x_1692_ == 0)
{
uint8_t v___x_1693_; 
v___x_1693_ = 1;
return v___x_1693_;
}
else
{
uint8_t v___x_1694_; 
v___x_1694_ = 0;
return v___x_1694_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_hasEntries___boxed(lean_object* v_log_1695_){
_start:
{
uint8_t v_res_1696_; lean_object* v_r_1697_; 
v_res_1696_ = l_Lake_Log_hasEntries(v_log_1695_);
lean_dec_ref(v_log_1695_);
v_r_1697_ = lean_box(v_res_1696_);
return v_r_1697_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_endPos(lean_object* v_log_1698_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = lean_array_get_size(v_log_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_endPos___boxed(lean_object* v_log_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lake_Log_endPos(v_log_1700_);
lean_dec_ref(v_log_1700_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_push(lean_object* v_log_1702_, lean_object* v_e_1703_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = lean_array_push(v_log_1702_, v_e_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_append(lean_object* v_log_1705_, lean_object* v_o_1706_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Array_append___redArg(v_log_1705_, v_o_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_append___boxed(lean_object* v_log_1708_, lean_object* v_o_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lake_Log_append(v_log_1708_, v_o_1709_);
lean_dec_ref(v_o_1709_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_extract(lean_object* v_log_1713_, lean_object* v_start_1714_, lean_object* v_stop_1715_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l_Array_extract___redArg(v_log_1713_, v_start_1714_, v_stop_1715_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_extract___boxed(lean_object* v_log_1717_, lean_object* v_start_1718_, lean_object* v_stop_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lake_Log_extract(v_log_1717_, v_start_1718_, v_stop_1719_);
lean_dec_ref(v_log_1717_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_dropFrom(lean_object* v_log_1721_, lean_object* v_pos_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Array_shrink___redArg(v_log_1721_, v_pos_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_dropFrom___boxed(lean_object* v_log_1724_, lean_object* v_pos_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lake_Log_dropFrom(v_log_1724_, v_pos_1725_);
lean_dec(v_pos_1725_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_takeFrom(lean_object* v_log_1727_, lean_object* v_pos_1728_){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1729_ = lean_array_get_size(v_log_1727_);
v___x_1730_ = l_Array_extract___redArg(v_log_1727_, v_pos_1728_, v___x_1729_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_takeFrom___boxed(lean_object* v_log_1731_, lean_object* v_pos_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lake_Log_takeFrom(v_log_1731_, v_pos_1732_);
lean_dec_ref(v_log_1731_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_split(lean_object* v_log_1734_, lean_object* v_pos_1735_){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_inc_ref(v_log_1734_);
v___x_1736_ = l_Array_shrink___redArg(v_log_1734_, v_pos_1735_);
v___x_1737_ = lean_array_get_size(v_log_1734_);
v___x_1738_ = l_Array_extract___redArg(v_log_1734_, v_pos_1735_, v___x_1737_);
lean_dec_ref(v_log_1734_);
v___x_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1736_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(lean_object* v_as_1741_, size_t v_i_1742_, size_t v_stop_1743_, lean_object* v_b_1744_){
_start:
{
uint8_t v___x_1745_; 
v___x_1745_ = lean_usize_dec_eq(v_i_1742_, v_stop_1743_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; size_t v___x_1751_; size_t v___x_1752_; 
v___x_1746_ = lean_array_uget_borrowed(v_as_1741_, v_i_1742_);
v___x_1747_ = l_Lake_LogEntry_toString(v___x_1746_, v___x_1745_);
v___x_1748_ = lean_string_append(v_b_1744_, v___x_1747_);
lean_dec_ref(v___x_1747_);
v___x_1749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0___closed__0));
v___x_1750_ = lean_string_append(v___x_1748_, v___x_1749_);
v___x_1751_ = ((size_t)1ULL);
v___x_1752_ = lean_usize_add(v_i_1742_, v___x_1751_);
v_i_1742_ = v___x_1752_;
v_b_1744_ = v___x_1750_;
goto _start;
}
else
{
return v_b_1744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0___boxed(lean_object* v_as_1754_, lean_object* v_i_1755_, lean_object* v_stop_1756_, lean_object* v_b_1757_){
_start:
{
size_t v_i_boxed_1758_; size_t v_stop_boxed_1759_; lean_object* v_res_1760_; 
v_i_boxed_1758_ = lean_unbox_usize(v_i_1755_);
lean_dec(v_i_1755_);
v_stop_boxed_1759_ = lean_unbox_usize(v_stop_1756_);
lean_dec(v_stop_1756_);
v_res_1760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(v_as_1754_, v_i_boxed_1758_, v_stop_boxed_1759_, v_b_1757_);
lean_dec_ref(v_as_1754_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_toString(lean_object* v_log_1761_){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1762_ = ((lean_object*)(l_Lake_instInhabitedLogEntry_default___closed__0));
v___x_1763_ = lean_unsigned_to_nat(0u);
v___x_1764_ = lean_array_get_size(v_log_1761_);
v___x_1765_ = lean_nat_dec_lt(v___x_1763_, v___x_1764_);
if (v___x_1765_ == 0)
{
return v___x_1762_;
}
else
{
uint8_t v___x_1766_; 
v___x_1766_ = lean_nat_dec_le(v___x_1764_, v___x_1764_);
if (v___x_1766_ == 0)
{
if (v___x_1765_ == 0)
{
return v___x_1762_;
}
else
{
size_t v___x_1767_; size_t v___x_1768_; lean_object* v___x_1769_; 
v___x_1767_ = ((size_t)0ULL);
v___x_1768_ = lean_usize_of_nat(v___x_1764_);
v___x_1769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(v_log_1761_, v___x_1767_, v___x_1768_, v___x_1762_);
return v___x_1769_;
}
}
else
{
size_t v___x_1770_; size_t v___x_1771_; lean_object* v___x_1772_; 
v___x_1770_ = ((size_t)0ULL);
v___x_1771_ = lean_usize_of_nat(v___x_1764_);
v___x_1772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(v_log_1761_, v___x_1770_, v___x_1771_, v___x_1762_);
return v___x_1772_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_toString___boxed(lean_object* v_log_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lake_Log_toString(v_log_1773_);
lean_dec_ref(v_log_1773_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_replay___redArg___lam__0(lean_object* v_logger_1777_, lean_object* v_x_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = lean_apply_1(v_logger_1777_, v___y_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_replay___redArg(lean_object* v_inst_1781_, lean_object* v_logger_1782_, lean_object* v_log_1783_){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; uint8_t v___x_1787_; 
v___x_1784_ = lean_unsigned_to_nat(0u);
v___x_1785_ = lean_array_get_size(v_log_1783_);
v___x_1786_ = lean_box(0);
v___x_1787_ = lean_nat_dec_lt(v___x_1784_, v___x_1785_);
if (v___x_1787_ == 0)
{
lean_object* v_toApplicative_1788_; lean_object* v_toPure_1789_; lean_object* v___x_1790_; 
lean_dec_ref(v_log_1783_);
lean_dec(v_logger_1782_);
v_toApplicative_1788_ = lean_ctor_get(v_inst_1781_, 0);
lean_inc_ref(v_toApplicative_1788_);
lean_dec_ref(v_inst_1781_);
v_toPure_1789_ = lean_ctor_get(v_toApplicative_1788_, 1);
lean_inc(v_toPure_1789_);
lean_dec_ref(v_toApplicative_1788_);
v___x_1790_ = lean_apply_2(v_toPure_1789_, lean_box(0), v___x_1786_);
return v___x_1790_;
}
else
{
lean_object* v___f_1791_; uint8_t v___x_1792_; 
v___f_1791_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1791_, 0, v_logger_1782_);
v___x_1792_ = lean_nat_dec_le(v___x_1785_, v___x_1785_);
if (v___x_1792_ == 0)
{
if (v___x_1787_ == 0)
{
lean_object* v_toApplicative_1793_; lean_object* v_toPure_1794_; lean_object* v___x_1795_; 
lean_dec_ref(v___f_1791_);
lean_dec_ref(v_log_1783_);
v_toApplicative_1793_ = lean_ctor_get(v_inst_1781_, 0);
lean_inc_ref(v_toApplicative_1793_);
lean_dec_ref(v_inst_1781_);
v_toPure_1794_ = lean_ctor_get(v_toApplicative_1793_, 1);
lean_inc(v_toPure_1794_);
lean_dec_ref(v_toApplicative_1793_);
v___x_1795_ = lean_apply_2(v_toPure_1794_, lean_box(0), v___x_1786_);
return v___x_1795_;
}
else
{
size_t v___x_1796_; size_t v___x_1797_; lean_object* v___x_1798_; 
v___x_1796_ = ((size_t)0ULL);
v___x_1797_ = lean_usize_of_nat(v___x_1785_);
v___x_1798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1781_, v___f_1791_, v_log_1783_, v___x_1796_, v___x_1797_, v___x_1786_);
return v___x_1798_;
}
}
else
{
size_t v___x_1799_; size_t v___x_1800_; lean_object* v___x_1801_; 
v___x_1799_ = ((size_t)0ULL);
v___x_1800_ = lean_usize_of_nat(v___x_1785_);
v___x_1801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1781_, v___f_1791_, v_log_1783_, v___x_1799_, v___x_1800_, v___x_1786_);
return v___x_1801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_replay(lean_object* v_m_1802_, lean_object* v_inst_1803_, lean_object* v_logger_1804_, lean_object* v_log_1805_){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; 
v___x_1806_ = lean_unsigned_to_nat(0u);
v___x_1807_ = lean_array_get_size(v_log_1805_);
v___x_1808_ = lean_box(0);
v___x_1809_ = lean_nat_dec_lt(v___x_1806_, v___x_1807_);
if (v___x_1809_ == 0)
{
lean_object* v_toApplicative_1810_; lean_object* v_toPure_1811_; lean_object* v___x_1812_; 
lean_dec_ref(v_log_1805_);
lean_dec(v_logger_1804_);
v_toApplicative_1810_ = lean_ctor_get(v_inst_1803_, 0);
lean_inc_ref(v_toApplicative_1810_);
lean_dec_ref(v_inst_1803_);
v_toPure_1811_ = lean_ctor_get(v_toApplicative_1810_, 1);
lean_inc(v_toPure_1811_);
lean_dec_ref(v_toApplicative_1810_);
v___x_1812_ = lean_apply_2(v_toPure_1811_, lean_box(0), v___x_1808_);
return v___x_1812_;
}
else
{
lean_object* v___f_1813_; uint8_t v___x_1814_; 
v___f_1813_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1813_, 0, v_logger_1804_);
v___x_1814_ = lean_nat_dec_le(v___x_1807_, v___x_1807_);
if (v___x_1814_ == 0)
{
if (v___x_1809_ == 0)
{
lean_object* v_toApplicative_1815_; lean_object* v_toPure_1816_; lean_object* v___x_1817_; 
lean_dec_ref(v___f_1813_);
lean_dec_ref(v_log_1805_);
v_toApplicative_1815_ = lean_ctor_get(v_inst_1803_, 0);
lean_inc_ref(v_toApplicative_1815_);
lean_dec_ref(v_inst_1803_);
v_toPure_1816_ = lean_ctor_get(v_toApplicative_1815_, 1);
lean_inc(v_toPure_1816_);
lean_dec_ref(v_toApplicative_1815_);
v___x_1817_ = lean_apply_2(v_toPure_1816_, lean_box(0), v___x_1808_);
return v___x_1817_;
}
else
{
size_t v___x_1818_; size_t v___x_1819_; lean_object* v___x_1820_; 
v___x_1818_ = ((size_t)0ULL);
v___x_1819_ = lean_usize_of_nat(v___x_1807_);
v___x_1820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1803_, v___f_1813_, v_log_1805_, v___x_1818_, v___x_1819_, v___x_1808_);
return v___x_1820_;
}
}
else
{
size_t v___x_1821_; size_t v___x_1822_; lean_object* v___x_1823_; 
v___x_1821_ = ((size_t)0ULL);
v___x_1822_ = lean_usize_of_nat(v___x_1807_);
v___x_1823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1803_, v___f_1813_, v_log_1805_, v___x_1821_, v___x_1822_, v___x_1808_);
return v___x_1823_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_filter___lam__0(lean_object* v_f_1824_, lean_object* v_x1_1825_, lean_object* v_x2_1826_){
_start:
{
lean_object* v___x_1827_; uint8_t v___x_1828_; 
lean_inc_ref(v_x2_1826_);
v___x_1827_ = lean_apply_1(v_f_1824_, v_x2_1826_);
v___x_1828_ = lean_unbox(v___x_1827_);
if (v___x_1828_ == 0)
{
lean_dec_ref(v_x2_1826_);
return v_x1_1825_;
}
else
{
lean_object* v___x_1829_; 
v___x_1829_ = lean_array_push(v_x1_1825_, v_x2_1826_);
return v___x_1829_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_filter(lean_object* v_f_1849_, lean_object* v_log_1850_){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; uint8_t v___x_1855_; 
v___x_1851_ = lean_unsigned_to_nat(0u);
v___x_1852_ = lean_array_get_size(v_log_1850_);
v___x_1853_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_1854_ = ((lean_object*)(l_Lake_Log_filter___closed__9));
v___x_1855_ = lean_nat_dec_lt(v___x_1851_, v___x_1852_);
if (v___x_1855_ == 0)
{
lean_dec_ref(v_log_1850_);
lean_dec_ref(v_f_1849_);
return v___x_1853_;
}
else
{
lean_object* v___f_1856_; uint8_t v___x_1857_; 
v___f_1856_ = lean_alloc_closure((void*)(l_Lake_Log_filter___lam__0), 3, 1);
lean_closure_set(v___f_1856_, 0, v_f_1849_);
v___x_1857_ = lean_nat_dec_le(v___x_1852_, v___x_1852_);
if (v___x_1857_ == 0)
{
if (v___x_1855_ == 0)
{
lean_dec_ref(v___f_1856_);
lean_dec_ref(v_log_1850_);
return v___x_1853_;
}
else
{
size_t v___x_1858_; size_t v___x_1859_; lean_object* v___x_1860_; 
v___x_1858_ = ((size_t)0ULL);
v___x_1859_ = lean_usize_of_nat(v___x_1852_);
v___x_1860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1854_, v___f_1856_, v_log_1850_, v___x_1858_, v___x_1859_, v___x_1853_);
return v___x_1860_;
}
}
else
{
size_t v___x_1861_; size_t v___x_1862_; lean_object* v___x_1863_; 
v___x_1861_ = ((size_t)0ULL);
v___x_1862_ = lean_usize_of_nat(v___x_1852_);
v___x_1863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1854_, v___f_1856_, v_log_1850_, v___x_1861_, v___x_1862_, v___x_1853_);
return v___x_1863_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_Log_any___lam__0(lean_object* v_f_1864_, lean_object* v_x_1865_){
_start:
{
lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1866_ = lean_apply_1(v_f_1864_, v_x_1865_);
v___x_1867_ = lean_unbox(v___x_1866_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_any___lam__0___boxed(lean_object* v_f_1868_, lean_object* v_x_1869_){
_start:
{
uint8_t v_res_1870_; lean_object* v_r_1871_; 
v_res_1870_ = l_Lake_Log_any___lam__0(v_f_1868_, v_x_1869_);
v_r_1871_ = lean_box(v_res_1870_);
return v_r_1871_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_any(lean_object* v_f_1872_, lean_object* v_log_1873_){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; uint8_t v___x_1877_; 
v___x_1874_ = lean_unsigned_to_nat(0u);
v___x_1875_ = lean_array_get_size(v_log_1873_);
v___x_1876_ = ((lean_object*)(l_Lake_Log_filter___closed__9));
v___x_1877_ = lean_nat_dec_lt(v___x_1874_, v___x_1875_);
if (v___x_1877_ == 0)
{
lean_dec_ref(v_log_1873_);
lean_dec_ref(v_f_1872_);
return v___x_1877_;
}
else
{
if (v___x_1877_ == 0)
{
lean_dec_ref(v_log_1873_);
lean_dec_ref(v_f_1872_);
return v___x_1877_;
}
else
{
lean_object* v___f_1878_; size_t v___x_1879_; size_t v___x_1880_; lean_object* v___x_1881_; uint8_t v___x_1882_; 
v___f_1878_ = lean_alloc_closure((void*)(l_Lake_Log_any___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1878_, 0, v_f_1872_);
v___x_1879_ = ((size_t)0ULL);
v___x_1880_ = lean_usize_of_nat(v___x_1875_);
v___x_1881_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_1876_, v___f_1878_, v_log_1873_, v___x_1879_, v___x_1880_);
v___x_1882_ = lean_unbox(v___x_1881_);
lean_dec(v___x_1881_);
return v___x_1882_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_any___boxed(lean_object* v_f_1883_, lean_object* v_log_1884_){
_start:
{
uint8_t v_res_1885_; lean_object* v_r_1886_; 
v_res_1885_ = l_Lake_Log_any(v_f_1883_, v_log_1884_);
v_r_1886_ = lean_box(v_res_1885_);
return v_r_1886_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(lean_object* v_as_1887_, size_t v_i_1888_, size_t v_stop_1889_, uint8_t v_b_1890_){
_start:
{
uint8_t v___y_1892_; uint8_t v___x_1896_; 
v___x_1896_ = lean_usize_dec_eq(v_i_1888_, v_stop_1889_);
if (v___x_1896_ == 0)
{
lean_object* v___x_1897_; uint8_t v_level_1898_; uint8_t v___x_1899_; 
v___x_1897_ = lean_array_uget_borrowed(v_as_1887_, v_i_1888_);
v_level_1898_ = lean_ctor_get_uint8(v___x_1897_, sizeof(void*)*1);
v___x_1899_ = l_Lake_instOrdLogLevel_ord(v_b_1890_, v_level_1898_);
if (v___x_1899_ == 2)
{
if (v___x_1896_ == 0)
{
v___y_1892_ = v_b_1890_;
goto v___jp_1891_;
}
else
{
v___y_1892_ = v_level_1898_;
goto v___jp_1891_;
}
}
else
{
v___y_1892_ = v_level_1898_;
goto v___jp_1891_;
}
}
else
{
return v_b_1890_;
}
v___jp_1891_:
{
size_t v___x_1893_; size_t v___x_1894_; 
v___x_1893_ = ((size_t)1ULL);
v___x_1894_ = lean_usize_add(v_i_1888_, v___x_1893_);
v_i_1888_ = v___x_1894_;
v_b_1890_ = v___y_1892_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0___boxed(lean_object* v_as_1900_, lean_object* v_i_1901_, lean_object* v_stop_1902_, lean_object* v_b_1903_){
_start:
{
size_t v_i_boxed_1904_; size_t v_stop_boxed_1905_; uint8_t v_b_boxed_1906_; uint8_t v_res_1907_; lean_object* v_r_1908_; 
v_i_boxed_1904_ = lean_unbox_usize(v_i_1901_);
lean_dec(v_i_1901_);
v_stop_boxed_1905_ = lean_unbox_usize(v_stop_1902_);
lean_dec(v_stop_1902_);
v_b_boxed_1906_ = lean_unbox(v_b_1903_);
v_res_1907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(v_as_1900_, v_i_boxed_1904_, v_stop_boxed_1905_, v_b_boxed_1906_);
lean_dec_ref(v_as_1900_);
v_r_1908_ = lean_box(v_res_1907_);
return v_r_1908_;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_maxLv(lean_object* v_log_1909_){
_start:
{
uint8_t v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; uint8_t v___x_1913_; 
v___x_1910_ = 0;
v___x_1911_ = lean_unsigned_to_nat(0u);
v___x_1912_ = lean_array_get_size(v_log_1909_);
v___x_1913_ = lean_nat_dec_lt(v___x_1911_, v___x_1912_);
if (v___x_1913_ == 0)
{
return v___x_1910_;
}
else
{
uint8_t v___x_1914_; 
v___x_1914_ = lean_nat_dec_le(v___x_1912_, v___x_1912_);
if (v___x_1914_ == 0)
{
if (v___x_1913_ == 0)
{
return v___x_1910_;
}
else
{
size_t v___x_1915_; size_t v___x_1916_; uint8_t v___x_1917_; 
v___x_1915_ = ((size_t)0ULL);
v___x_1916_ = lean_usize_of_nat(v___x_1912_);
v___x_1917_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(v_log_1909_, v___x_1915_, v___x_1916_, v___x_1910_);
return v___x_1917_;
}
}
else
{
size_t v___x_1918_; size_t v___x_1919_; uint8_t v___x_1920_; 
v___x_1918_ = ((size_t)0ULL);
v___x_1919_ = lean_usize_of_nat(v___x_1912_);
v___x_1920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(v_log_1909_, v___x_1918_, v___x_1919_, v___x_1910_);
return v___x_1920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_maxLv___boxed(lean_object* v_log_1921_){
_start:
{
uint8_t v_res_1922_; lean_object* v_r_1923_; 
v_res_1922_ = l_Lake_Log_maxLv(v_log_1921_);
lean_dec_ref(v_log_1921_);
v_r_1923_ = lean_box(v_res_1922_);
return v_r_1923_;
}
}
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___redArg___lam__0(lean_object* v_e_1924_, lean_object* v_s_1925_){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1926_ = lean_box(0);
v___x_1927_ = lean_array_push(v_s_1925_, v_e_1924_);
v___x_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1926_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___redArg(lean_object* v_inst_1929_, lean_object* v_e_1930_){
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
LEAN_EXPORT lean_object* l_Lake_pushLogEntry(lean_object* v_m_1934_, lean_object* v_inst_1935_, lean_object* v_e_1936_){
_start:
{
lean_object* v_modifyGet_1937_; lean_object* v___f_1938_; lean_object* v___x_1939_; 
v_modifyGet_1937_ = lean_ctor_get(v_inst_1935_, 2);
lean_inc(v_modifyGet_1937_);
lean_dec_ref(v_inst_1935_);
v___f_1938_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1938_, 0, v_e_1936_);
v___x_1939_ = lean_apply_2(v_modifyGet_1937_, lean_box(0), v___f_1938_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_ofMonadState___redArg(lean_object* v_inst_1940_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(v___x_1941_, 0, lean_box(0));
lean_closure_set(v___x_1941_, 1, v_inst_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_ofMonadState(lean_object* v_m_1942_, lean_object* v_inst_1943_){
_start:
{
lean_object* v___x_1944_; 
v___x_1944_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(v___x_1944_, 0, lean_box(0));
lean_closure_set(v___x_1944_, 1, v_inst_1943_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog___redArg(lean_object* v_inst_1945_){
_start:
{
lean_object* v_get_1946_; 
v_get_1946_ = lean_ctor_get(v_inst_1945_, 0);
lean_inc(v_get_1946_);
return v_get_1946_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog___redArg___boxed(lean_object* v_inst_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lake_getLog___redArg(v_inst_1947_);
lean_dec_ref(v_inst_1947_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog(lean_object* v_m_1949_, lean_object* v_inst_1950_){
_start:
{
lean_object* v_get_1951_; 
v_get_1951_ = lean_ctor_get(v_inst_1950_, 0);
lean_inc(v_get_1951_);
return v_get_1951_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog___boxed(lean_object* v_m_1952_, lean_object* v_inst_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lake_getLog(v_m_1952_, v_inst_1953_);
lean_dec_ref(v_inst_1953_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg___lam__0(lean_object* v_x_1955_){
_start:
{
lean_object* v___x_1956_; 
v___x_1956_ = lean_array_get_size(v_x_1955_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg___lam__0___boxed(lean_object* v_x_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lake_getLogPos___redArg___lam__0(v_x_1957_);
lean_dec_ref(v_x_1957_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg(lean_object* v_inst_1960_, lean_object* v_inst_1961_){
_start:
{
lean_object* v_map_1962_; lean_object* v_get_1963_; lean_object* v___f_1964_; lean_object* v___x_1965_; 
v_map_1962_ = lean_ctor_get(v_inst_1960_, 0);
lean_inc(v_map_1962_);
lean_dec_ref(v_inst_1960_);
v_get_1963_ = lean_ctor_get(v_inst_1961_, 0);
lean_inc(v_get_1963_);
lean_dec_ref(v_inst_1961_);
v___f_1964_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_1965_ = lean_apply_4(v_map_1962_, lean_box(0), lean_box(0), v___f_1964_, v_get_1963_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos(lean_object* v_m_1966_, lean_object* v_inst_1967_, lean_object* v_inst_1968_){
_start:
{
lean_object* v_map_1969_; lean_object* v_get_1970_; lean_object* v___f_1971_; lean_object* v___x_1972_; 
v_map_1969_ = lean_ctor_get(v_inst_1967_, 0);
lean_inc(v_map_1969_);
lean_dec_ref(v_inst_1967_);
v_get_1970_ = lean_ctor_get(v_inst_1968_, 0);
lean_inc(v_get_1970_);
lean_dec_ref(v_inst_1968_);
v___f_1971_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_1972_ = lean_apply_4(v_map_1969_, lean_box(0), lean_box(0), v___f_1971_, v_get_1970_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLog___redArg___lam__0(lean_object* v_log_1973_){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1975_, 0, v_log_1973_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLog___redArg(lean_object* v_inst_1977_){
_start:
{
lean_object* v_modifyGet_1978_; lean_object* v___f_1979_; lean_object* v___x_1980_; 
v_modifyGet_1978_ = lean_ctor_get(v_inst_1977_, 2);
lean_inc(v_modifyGet_1978_);
lean_dec_ref(v_inst_1977_);
v___f_1979_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_1980_ = lean_apply_2(v_modifyGet_1978_, lean_box(0), v___f_1979_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLog(lean_object* v_m_1981_, lean_object* v_inst_1982_){
_start:
{
lean_object* v_modifyGet_1983_; lean_object* v___f_1984_; lean_object* v___x_1985_; 
v_modifyGet_1983_ = lean_ctor_get(v_inst_1982_, 2);
lean_inc(v_modifyGet_1983_);
lean_dec_ref(v_inst_1982_);
v___f_1984_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_1985_ = lean_apply_2(v_modifyGet_1983_, lean_box(0), v___f_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLogFrom___redArg___lam__0(lean_object* v_pos_1986_, lean_object* v_log_1987_){
_start:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1988_ = lean_array_get_size(v_log_1987_);
lean_inc(v_pos_1986_);
v___x_1989_ = l_Array_extract___redArg(v_log_1987_, v_pos_1986_, v___x_1988_);
v___x_1990_ = l_Array_shrink___redArg(v_log_1987_, v_pos_1986_);
lean_dec(v_pos_1986_);
v___x_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1989_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLogFrom___redArg(lean_object* v_inst_1992_, lean_object* v_pos_1993_){
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
LEAN_EXPORT lean_object* l_Lake_takeLogFrom(lean_object* v_m_1997_, lean_object* v_inst_1998_, lean_object* v_pos_1999_){
_start:
{
lean_object* v_modifyGet_2000_; lean_object* v___f_2001_; lean_object* v___x_2002_; 
v_modifyGet_2000_ = lean_ctor_get(v_inst_1998_, 2);
lean_inc(v_modifyGet_2000_);
lean_dec_ref(v_inst_1998_);
v___f_2001_ = lean_alloc_closure((void*)(l_Lake_takeLogFrom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2001_, 0, v_pos_1999_);
v___x_2002_ = lean_apply_2(v_modifyGet_2000_, lean_box(0), v___f_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg___lam__0(lean_object* v_pos_2003_, lean_object* v_s_2004_){
_start:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2005_ = lean_box(0);
v___x_2006_ = l_Array_shrink___redArg(v_s_2004_, v_pos_2003_);
v___x_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2005_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg___lam__0___boxed(lean_object* v_pos_2008_, lean_object* v_s_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Lake_dropLogFrom___redArg___lam__0(v_pos_2008_, v_s_2009_);
lean_dec(v_pos_2008_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg(lean_object* v_inst_2011_, lean_object* v_pos_2012_){
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
LEAN_EXPORT lean_object* l_Lake_dropLogFrom(lean_object* v_m_2016_, lean_object* v_inst_2017_, lean_object* v_pos_2018_){
_start:
{
lean_object* v_modifyGet_2019_; lean_object* v___f_2020_; lean_object* v___x_2021_; 
v_modifyGet_2019_ = lean_ctor_get(v_inst_2017_, 2);
lean_inc(v_modifyGet_2019_);
lean_dec_ref(v_inst_2017_);
v___f_2020_ = lean_alloc_closure((void*)(l_Lake_dropLogFrom___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2020_, 0, v_pos_2018_);
v___x_2021_ = lean_apply_2(v_modifyGet_2019_, lean_box(0), v___f_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__1(lean_object* v_iniPos_2022_, lean_object* v_toPure_2023_, lean_object* v_log_2024_){
_start:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2025_ = lean_array_get_size(v_log_2024_);
v___x_2026_ = l_Array_extract___redArg(v_log_2024_, v_iniPos_2022_, v___x_2025_);
v___x_2027_ = lean_apply_2(v_toPure_2023_, lean_box(0), v___x_2026_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__1___boxed(lean_object* v_iniPos_2028_, lean_object* v_toPure_2029_, lean_object* v_log_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_Lake_extractLog___redArg___lam__1(v_iniPos_2028_, v_toPure_2029_, v_log_2030_);
lean_dec_ref(v_log_2030_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__0(lean_object* v_toBind_2032_, lean_object* v_get_2033_, lean_object* v___f_2034_, lean_object* v_____r_2035_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = lean_apply_4(v_toBind_2032_, lean_box(0), lean_box(0), v_get_2033_, v___f_2034_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__2(lean_object* v_toPure_2037_, lean_object* v_toBind_2038_, lean_object* v_get_2039_, lean_object* v_x_2040_, lean_object* v_iniPos_2041_){
_start:
{
lean_object* v___f_2042_; lean_object* v___f_2043_; lean_object* v___x_2044_; 
v___f_2042_ = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2042_, 0, v_iniPos_2041_);
lean_closure_set(v___f_2042_, 1, v_toPure_2037_);
lean_inc(v_toBind_2038_);
v___f_2043_ = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2043_, 0, v_toBind_2038_);
lean_closure_set(v___f_2043_, 1, v_get_2039_);
lean_closure_set(v___f_2043_, 2, v___f_2042_);
v___x_2044_ = lean_apply_4(v_toBind_2038_, lean_box(0), lean_box(0), v_x_2040_, v___f_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg(lean_object* v_inst_2045_, lean_object* v_inst_2046_, lean_object* v_x_2047_){
_start:
{
lean_object* v_toApplicative_2048_; lean_object* v_toFunctor_2049_; lean_object* v_toBind_2050_; lean_object* v_toPure_2051_; lean_object* v_map_2052_; lean_object* v_get_2053_; lean_object* v___f_2054_; lean_object* v___f_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v_toApplicative_2048_ = lean_ctor_get(v_inst_2045_, 0);
lean_inc_ref(v_toApplicative_2048_);
v_toFunctor_2049_ = lean_ctor_get(v_toApplicative_2048_, 0);
lean_inc_ref(v_toFunctor_2049_);
v_toBind_2050_ = lean_ctor_get(v_inst_2045_, 1);
lean_inc(v_toBind_2050_);
lean_dec_ref(v_inst_2045_);
v_toPure_2051_ = lean_ctor_get(v_toApplicative_2048_, 1);
lean_inc(v_toPure_2051_);
lean_dec_ref(v_toApplicative_2048_);
v_map_2052_ = lean_ctor_get(v_toFunctor_2049_, 0);
lean_inc(v_map_2052_);
lean_dec_ref(v_toFunctor_2049_);
v_get_2053_ = lean_ctor_get(v_inst_2046_, 0);
lean_inc(v_get_2053_);
lean_dec_ref(v_inst_2046_);
v___f_2054_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
lean_inc(v_get_2053_);
lean_inc(v_toBind_2050_);
v___f_2055_ = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2055_, 0, v_toPure_2051_);
lean_closure_set(v___f_2055_, 1, v_toBind_2050_);
lean_closure_set(v___f_2055_, 2, v_get_2053_);
lean_closure_set(v___f_2055_, 3, v_x_2047_);
v___x_2056_ = lean_apply_4(v_map_2052_, lean_box(0), lean_box(0), v___f_2054_, v_get_2053_);
v___x_2057_ = lean_apply_4(v_toBind_2050_, lean_box(0), lean_box(0), v___x_2056_, v___f_2055_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog(lean_object* v_m_2058_, lean_object* v_inst_2059_, lean_object* v_inst_2060_, lean_object* v_x_2061_){
_start:
{
lean_object* v_toApplicative_2062_; lean_object* v_toFunctor_2063_; lean_object* v_toBind_2064_; lean_object* v_toPure_2065_; lean_object* v_map_2066_; lean_object* v_get_2067_; lean_object* v___f_2068_; lean_object* v___f_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v_toApplicative_2062_ = lean_ctor_get(v_inst_2059_, 0);
lean_inc_ref(v_toApplicative_2062_);
v_toFunctor_2063_ = lean_ctor_get(v_toApplicative_2062_, 0);
lean_inc_ref(v_toFunctor_2063_);
v_toBind_2064_ = lean_ctor_get(v_inst_2059_, 1);
lean_inc(v_toBind_2064_);
lean_dec_ref(v_inst_2059_);
v_toPure_2065_ = lean_ctor_get(v_toApplicative_2062_, 1);
lean_inc(v_toPure_2065_);
lean_dec_ref(v_toApplicative_2062_);
v_map_2066_ = lean_ctor_get(v_toFunctor_2063_, 0);
lean_inc(v_map_2066_);
lean_dec_ref(v_toFunctor_2063_);
v_get_2067_ = lean_ctor_get(v_inst_2060_, 0);
lean_inc(v_get_2067_);
lean_dec_ref(v_inst_2060_);
v___f_2068_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
lean_inc(v_get_2067_);
lean_inc(v_toBind_2064_);
v___f_2069_ = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2069_, 0, v_toPure_2065_);
lean_closure_set(v___f_2069_, 1, v_toBind_2064_);
lean_closure_set(v___f_2069_, 2, v_get_2067_);
lean_closure_set(v___f_2069_, 3, v_x_2061_);
v___x_2070_ = lean_apply_4(v_map_2066_, lean_box(0), lean_box(0), v___f_2068_, v_get_2067_);
v___x_2071_ = lean_apply_4(v_toBind_2064_, lean_box(0), lean_box(0), v___x_2070_, v___f_2069_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__1(lean_object* v_iniPos_2072_, lean_object* v_a_2073_, lean_object* v_toPure_2074_, lean_object* v_log_2075_){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2076_ = lean_array_get_size(v_log_2075_);
v___x_2077_ = l_Array_extract___redArg(v_log_2075_, v_iniPos_2072_, v___x_2076_);
v___x_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2078_, 0, v_a_2073_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
v___x_2079_ = lean_apply_2(v_toPure_2074_, lean_box(0), v___x_2078_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__1___boxed(lean_object* v_iniPos_2080_, lean_object* v_a_2081_, lean_object* v_toPure_2082_, lean_object* v_log_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Lake_withExtractLog___redArg___lam__1(v_iniPos_2080_, v_a_2081_, v_toPure_2082_, v_log_2083_);
lean_dec_ref(v_log_2083_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__0(lean_object* v_iniPos_2085_, lean_object* v_toPure_2086_, lean_object* v_toBind_2087_, lean_object* v_get_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v___f_2090_; lean_object* v___x_2091_; 
v___f_2090_ = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2090_, 0, v_iniPos_2085_);
lean_closure_set(v___f_2090_, 1, v_a_2089_);
lean_closure_set(v___f_2090_, 2, v_toPure_2086_);
v___x_2091_ = lean_apply_4(v_toBind_2087_, lean_box(0), lean_box(0), v_get_2088_, v___f_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__2(lean_object* v_toPure_2092_, lean_object* v_toBind_2093_, lean_object* v_get_2094_, lean_object* v_x_2095_, lean_object* v_iniPos_2096_){
_start:
{
lean_object* v___f_2097_; lean_object* v___x_2098_; 
lean_inc(v_toBind_2093_);
v___f_2097_ = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2097_, 0, v_iniPos_2096_);
lean_closure_set(v___f_2097_, 1, v_toPure_2092_);
lean_closure_set(v___f_2097_, 2, v_toBind_2093_);
lean_closure_set(v___f_2097_, 3, v_get_2094_);
v___x_2098_ = lean_apply_4(v_toBind_2093_, lean_box(0), lean_box(0), v_x_2095_, v___f_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg(lean_object* v_inst_2099_, lean_object* v_inst_2100_, lean_object* v_x_2101_){
_start:
{
lean_object* v_toApplicative_2102_; lean_object* v_toFunctor_2103_; lean_object* v_toBind_2104_; lean_object* v_toPure_2105_; lean_object* v_map_2106_; lean_object* v_get_2107_; lean_object* v___f_2108_; lean_object* v___f_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v_toApplicative_2102_ = lean_ctor_get(v_inst_2099_, 0);
lean_inc_ref(v_toApplicative_2102_);
v_toFunctor_2103_ = lean_ctor_get(v_toApplicative_2102_, 0);
lean_inc_ref(v_toFunctor_2103_);
v_toBind_2104_ = lean_ctor_get(v_inst_2099_, 1);
lean_inc(v_toBind_2104_);
lean_dec_ref(v_inst_2099_);
v_toPure_2105_ = lean_ctor_get(v_toApplicative_2102_, 1);
lean_inc(v_toPure_2105_);
lean_dec_ref(v_toApplicative_2102_);
v_map_2106_ = lean_ctor_get(v_toFunctor_2103_, 0);
lean_inc(v_map_2106_);
lean_dec_ref(v_toFunctor_2103_);
v_get_2107_ = lean_ctor_get(v_inst_2100_, 0);
lean_inc(v_get_2107_);
lean_dec_ref(v_inst_2100_);
v___f_2108_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
lean_inc(v_get_2107_);
lean_inc(v_toBind_2104_);
v___f_2109_ = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2109_, 0, v_toPure_2105_);
lean_closure_set(v___f_2109_, 1, v_toBind_2104_);
lean_closure_set(v___f_2109_, 2, v_get_2107_);
lean_closure_set(v___f_2109_, 3, v_x_2101_);
v___x_2110_ = lean_apply_4(v_map_2106_, lean_box(0), lean_box(0), v___f_2108_, v_get_2107_);
v___x_2111_ = lean_apply_4(v_toBind_2104_, lean_box(0), lean_box(0), v___x_2110_, v___f_2109_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog(lean_object* v_m_2112_, lean_object* v_00_u03b1_2113_, lean_object* v_inst_2114_, lean_object* v_inst_2115_, lean_object* v_x_2116_){
_start:
{
lean_object* v_toApplicative_2117_; lean_object* v_toFunctor_2118_; lean_object* v_toBind_2119_; lean_object* v_toPure_2120_; lean_object* v_map_2121_; lean_object* v_get_2122_; lean_object* v___f_2123_; lean_object* v___f_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v_toApplicative_2117_ = lean_ctor_get(v_inst_2114_, 0);
lean_inc_ref(v_toApplicative_2117_);
v_toFunctor_2118_ = lean_ctor_get(v_toApplicative_2117_, 0);
lean_inc_ref(v_toFunctor_2118_);
v_toBind_2119_ = lean_ctor_get(v_inst_2114_, 1);
lean_inc(v_toBind_2119_);
lean_dec_ref(v_inst_2114_);
v_toPure_2120_ = lean_ctor_get(v_toApplicative_2117_, 1);
lean_inc(v_toPure_2120_);
lean_dec_ref(v_toApplicative_2117_);
v_map_2121_ = lean_ctor_get(v_toFunctor_2118_, 0);
lean_inc(v_map_2121_);
lean_dec_ref(v_toFunctor_2118_);
v_get_2122_ = lean_ctor_get(v_inst_2115_, 0);
lean_inc(v_get_2122_);
lean_dec_ref(v_inst_2115_);
v___f_2123_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
lean_inc(v_get_2122_);
lean_inc(v_toBind_2119_);
v___f_2124_ = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2124_, 0, v_toPure_2120_);
lean_closure_set(v___f_2124_, 1, v_toBind_2119_);
lean_closure_set(v___f_2124_, 2, v_get_2122_);
lean_closure_set(v___f_2124_, 3, v_x_2116_);
v___x_2125_ = lean_apply_4(v_map_2121_, lean_box(0), lean_box(0), v___f_2123_, v_get_2122_);
v___x_2126_ = lean_apply_4(v_toBind_2119_, lean_box(0), lean_box(0), v___x_2125_, v___f_2124_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__1(lean_object* v_iniPos_2127_, lean_object* v_inst_2128_, lean_object* v_toPure_2129_, lean_object* v_a_2130_, lean_object* v_endPos_2131_){
_start:
{
uint8_t v___x_2132_; 
v___x_2132_ = lean_nat_dec_eq(v_iniPos_2127_, v_endPos_2131_);
if (v___x_2132_ == 0)
{
lean_object* v_throw_2133_; lean_object* v___x_2134_; 
lean_dec(v_a_2130_);
lean_dec(v_toPure_2129_);
v_throw_2133_ = lean_ctor_get(v_inst_2128_, 0);
lean_inc(v_throw_2133_);
lean_dec_ref(v_inst_2128_);
v___x_2134_ = lean_apply_2(v_throw_2133_, lean_box(0), v_iniPos_2127_);
return v___x_2134_;
}
else
{
lean_object* v___x_2135_; 
lean_dec_ref(v_inst_2128_);
lean_dec(v_iniPos_2127_);
v___x_2135_ = lean_apply_2(v_toPure_2129_, lean_box(0), v_a_2130_);
return v___x_2135_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__1___boxed(lean_object* v_iniPos_2136_, lean_object* v_inst_2137_, lean_object* v_toPure_2138_, lean_object* v_a_2139_, lean_object* v_endPos_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l_Lake_throwIfLogs___redArg___lam__1(v_iniPos_2136_, v_inst_2137_, v_toPure_2138_, v_a_2139_, v_endPos_2140_);
lean_dec(v_endPos_2140_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__0(lean_object* v_iniPos_2142_, lean_object* v_inst_2143_, lean_object* v_toPure_2144_, lean_object* v_toBind_2145_, lean_object* v___x_2146_, lean_object* v_a_2147_){
_start:
{
lean_object* v___f_2148_; lean_object* v___x_2149_; 
v___f_2148_ = lean_alloc_closure((void*)(l_Lake_throwIfLogs___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2148_, 0, v_iniPos_2142_);
lean_closure_set(v___f_2148_, 1, v_inst_2143_);
lean_closure_set(v___f_2148_, 2, v_toPure_2144_);
lean_closure_set(v___f_2148_, 3, v_a_2147_);
v___x_2149_ = lean_apply_4(v_toBind_2145_, lean_box(0), lean_box(0), v___x_2146_, v___f_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg___lam__2(lean_object* v_inst_2150_, lean_object* v_toPure_2151_, lean_object* v_toBind_2152_, lean_object* v___x_2153_, lean_object* v_x_2154_, lean_object* v_iniPos_2155_){
_start:
{
lean_object* v___f_2156_; lean_object* v___x_2157_; 
lean_inc(v_toBind_2152_);
v___f_2156_ = lean_alloc_closure((void*)(l_Lake_throwIfLogs___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2156_, 0, v_iniPos_2155_);
lean_closure_set(v___f_2156_, 1, v_inst_2150_);
lean_closure_set(v___f_2156_, 2, v_toPure_2151_);
lean_closure_set(v___f_2156_, 3, v_toBind_2152_);
lean_closure_set(v___f_2156_, 4, v___x_2153_);
v___x_2157_ = lean_apply_4(v_toBind_2152_, lean_box(0), lean_box(0), v_x_2154_, v___f_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs___redArg(lean_object* v_inst_2158_, lean_object* v_inst_2159_, lean_object* v_inst_2160_, lean_object* v_x_2161_){
_start:
{
lean_object* v_toApplicative_2162_; lean_object* v_toFunctor_2163_; lean_object* v_toBind_2164_; lean_object* v_toPure_2165_; lean_object* v_map_2166_; lean_object* v_get_2167_; lean_object* v___f_2168_; lean_object* v___x_2169_; lean_object* v___f_2170_; lean_object* v___x_2171_; 
v_toApplicative_2162_ = lean_ctor_get(v_inst_2158_, 0);
lean_inc_ref(v_toApplicative_2162_);
v_toFunctor_2163_ = lean_ctor_get(v_toApplicative_2162_, 0);
lean_inc_ref(v_toFunctor_2163_);
v_toBind_2164_ = lean_ctor_get(v_inst_2158_, 1);
lean_inc(v_toBind_2164_);
lean_dec_ref(v_inst_2158_);
v_toPure_2165_ = lean_ctor_get(v_toApplicative_2162_, 1);
lean_inc(v_toPure_2165_);
lean_dec_ref(v_toApplicative_2162_);
v_map_2166_ = lean_ctor_get(v_toFunctor_2163_, 0);
lean_inc(v_map_2166_);
lean_dec_ref(v_toFunctor_2163_);
v_get_2167_ = lean_ctor_get(v_inst_2159_, 0);
lean_inc(v_get_2167_);
lean_dec_ref(v_inst_2159_);
v___f_2168_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_2169_ = lean_apply_4(v_map_2166_, lean_box(0), lean_box(0), v___f_2168_, v_get_2167_);
lean_inc(v___x_2169_);
lean_inc(v_toBind_2164_);
v___f_2170_ = lean_alloc_closure((void*)(l_Lake_throwIfLogs___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2170_, 0, v_inst_2160_);
lean_closure_set(v___f_2170_, 1, v_toPure_2165_);
lean_closure_set(v___f_2170_, 2, v_toBind_2164_);
lean_closure_set(v___f_2170_, 3, v___x_2169_);
lean_closure_set(v___f_2170_, 4, v_x_2161_);
v___x_2171_ = lean_apply_4(v_toBind_2164_, lean_box(0), lean_box(0), v___x_2169_, v___f_2170_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Lake_throwIfLogs(lean_object* v_m_2172_, lean_object* v_00_u03b1_2173_, lean_object* v_inst_2174_, lean_object* v_inst_2175_, lean_object* v_inst_2176_, lean_object* v_x_2177_){
_start:
{
lean_object* v_toApplicative_2178_; lean_object* v_toFunctor_2179_; lean_object* v_toBind_2180_; lean_object* v_toPure_2181_; lean_object* v_map_2182_; lean_object* v_get_2183_; lean_object* v___f_2184_; lean_object* v___x_2185_; lean_object* v___f_2186_; lean_object* v___x_2187_; 
v_toApplicative_2178_ = lean_ctor_get(v_inst_2174_, 0);
lean_inc_ref(v_toApplicative_2178_);
v_toFunctor_2179_ = lean_ctor_get(v_toApplicative_2178_, 0);
lean_inc_ref(v_toFunctor_2179_);
v_toBind_2180_ = lean_ctor_get(v_inst_2174_, 1);
lean_inc(v_toBind_2180_);
lean_dec_ref(v_inst_2174_);
v_toPure_2181_ = lean_ctor_get(v_toApplicative_2178_, 1);
lean_inc(v_toPure_2181_);
lean_dec_ref(v_toApplicative_2178_);
v_map_2182_ = lean_ctor_get(v_toFunctor_2179_, 0);
lean_inc(v_map_2182_);
lean_dec_ref(v_toFunctor_2179_);
v_get_2183_ = lean_ctor_get(v_inst_2175_, 0);
lean_inc(v_get_2183_);
lean_dec_ref(v_inst_2175_);
v___f_2184_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_2185_ = lean_apply_4(v_map_2182_, lean_box(0), lean_box(0), v___f_2184_, v_get_2183_);
lean_inc(v___x_2185_);
lean_inc(v_toBind_2180_);
v___f_2186_ = lean_alloc_closure((void*)(l_Lake_throwIfLogs___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2186_, 0, v_inst_2176_);
lean_closure_set(v___f_2186_, 1, v_toPure_2181_);
lean_closure_set(v___f_2186_, 2, v_toBind_2180_);
lean_closure_set(v___f_2186_, 3, v___x_2185_);
lean_closure_set(v___f_2186_, 4, v_x_2177_);
v___x_2187_ = lean_apply_4(v_toBind_2180_, lean_box(0), lean_box(0), v___x_2185_, v___f_2186_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__1(lean_object* v_throw_2188_, lean_object* v_iniPos_2189_, lean_object* v_x_2190_){
_start:
{
lean_object* v___x_2191_; 
v___x_2191_ = lean_apply_2(v_throw_2188_, lean_box(0), v_iniPos_2189_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__1___boxed(lean_object* v_throw_2192_, lean_object* v_iniPos_2193_, lean_object* v_x_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_Lake_withLogErrorPos___redArg___lam__1(v_throw_2192_, v_iniPos_2193_, v_x_2194_);
lean_dec(v_x_2194_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__0(lean_object* v_inst_2196_, lean_object* v_self_2197_, lean_object* v_iniPos_2198_){
_start:
{
lean_object* v_throw_2199_; lean_object* v_tryCatch_2200_; lean_object* v___f_2201_; lean_object* v___x_2202_; 
v_throw_2199_ = lean_ctor_get(v_inst_2196_, 0);
lean_inc(v_throw_2199_);
v_tryCatch_2200_ = lean_ctor_get(v_inst_2196_, 1);
lean_inc(v_tryCatch_2200_);
lean_dec_ref(v_inst_2196_);
v___f_2201_ = lean_alloc_closure((void*)(l_Lake_withLogErrorPos___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2201_, 0, v_throw_2199_);
lean_closure_set(v___f_2201_, 1, v_iniPos_2198_);
v___x_2202_ = lean_apply_3(v_tryCatch_2200_, lean_box(0), v_self_2197_, v___f_2201_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg(lean_object* v_inst_2203_, lean_object* v_inst_2204_, lean_object* v_inst_2205_, lean_object* v_self_2206_){
_start:
{
lean_object* v_toApplicative_2207_; lean_object* v_toFunctor_2208_; lean_object* v_toBind_2209_; lean_object* v_map_2210_; lean_object* v_get_2211_; lean_object* v___f_2212_; lean_object* v___f_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v_toApplicative_2207_ = lean_ctor_get(v_inst_2203_, 0);
v_toFunctor_2208_ = lean_ctor_get(v_toApplicative_2207_, 0);
lean_inc_ref(v_toFunctor_2208_);
v_toBind_2209_ = lean_ctor_get(v_inst_2203_, 1);
lean_inc(v_toBind_2209_);
lean_dec_ref(v_inst_2203_);
v_map_2210_ = lean_ctor_get(v_toFunctor_2208_, 0);
lean_inc(v_map_2210_);
lean_dec_ref(v_toFunctor_2208_);
v_get_2211_ = lean_ctor_get(v_inst_2204_, 0);
lean_inc(v_get_2211_);
lean_dec_ref(v_inst_2204_);
v___f_2212_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2213_ = lean_alloc_closure((void*)(l_Lake_withLogErrorPos___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2213_, 0, v_inst_2205_);
lean_closure_set(v___f_2213_, 1, v_self_2206_);
v___x_2214_ = lean_apply_4(v_map_2210_, lean_box(0), lean_box(0), v___f_2212_, v_get_2211_);
v___x_2215_ = lean_apply_4(v_toBind_2209_, lean_box(0), lean_box(0), v___x_2214_, v___f_2213_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos(lean_object* v_m_2216_, lean_object* v_00_u03b1_2217_, lean_object* v_inst_2218_, lean_object* v_inst_2219_, lean_object* v_inst_2220_, lean_object* v_self_2221_){
_start:
{
lean_object* v_toApplicative_2222_; lean_object* v_toFunctor_2223_; lean_object* v_toBind_2224_; lean_object* v_map_2225_; lean_object* v_get_2226_; lean_object* v___f_2227_; lean_object* v___f_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v_toApplicative_2222_ = lean_ctor_get(v_inst_2218_, 0);
v_toFunctor_2223_ = lean_ctor_get(v_toApplicative_2222_, 0);
lean_inc_ref(v_toFunctor_2223_);
v_toBind_2224_ = lean_ctor_get(v_inst_2218_, 1);
lean_inc(v_toBind_2224_);
lean_dec_ref(v_inst_2218_);
v_map_2225_ = lean_ctor_get(v_toFunctor_2223_, 0);
lean_inc(v_map_2225_);
lean_dec_ref(v_toFunctor_2223_);
v_get_2226_ = lean_ctor_get(v_inst_2219_, 0);
lean_inc(v_get_2226_);
lean_dec_ref(v_inst_2219_);
v___f_2227_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2228_ = lean_alloc_closure((void*)(l_Lake_withLogErrorPos___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2228_, 0, v_inst_2220_);
lean_closure_set(v___f_2228_, 1, v_self_2221_);
v___x_2229_ = lean_apply_4(v_map_2225_, lean_box(0), lean_box(0), v___f_2227_, v_get_2226_);
v___x_2230_ = lean_apply_4(v_toBind_2224_, lean_box(0), lean_box(0), v___x_2229_, v___f_2228_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__1(lean_object* v_toPure_2231_, lean_object* v_x_2232_){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = lean_box(0);
v___x_2234_ = lean_apply_2(v_toPure_2231_, lean_box(0), v___x_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__1___boxed(lean_object* v_toPure_2235_, lean_object* v_x_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_Lake_errorWithLog___redArg___lam__1(v_toPure_2235_, v_x_2236_);
lean_dec(v_x_2236_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__0(lean_object* v_throw_2238_, lean_object* v_iniPos_2239_, lean_object* v_____r_2240_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = lean_apply_2(v_throw_2238_, lean_box(0), v_iniPos_2239_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__2(lean_object* v_inst_2242_, lean_object* v_self_2243_, lean_object* v___f_2244_, lean_object* v_toBind_2245_, lean_object* v_iniPos_2246_){
_start:
{
lean_object* v_throw_2247_; lean_object* v_tryCatch_2248_; lean_object* v___f_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v_throw_2247_ = lean_ctor_get(v_inst_2242_, 0);
lean_inc(v_throw_2247_);
v_tryCatch_2248_ = lean_ctor_get(v_inst_2242_, 1);
lean_inc(v_tryCatch_2248_);
lean_dec_ref(v_inst_2242_);
v___f_2249_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2249_, 0, v_throw_2247_);
lean_closure_set(v___f_2249_, 1, v_iniPos_2246_);
v___x_2250_ = lean_apply_3(v_tryCatch_2248_, lean_box(0), v_self_2243_, v___f_2244_);
v___x_2251_ = lean_apply_4(v_toBind_2245_, lean_box(0), lean_box(0), v___x_2250_, v___f_2249_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg(lean_object* v_inst_2252_, lean_object* v_inst_2253_, lean_object* v_inst_2254_, lean_object* v_self_2255_){
_start:
{
lean_object* v_toApplicative_2256_; lean_object* v_toFunctor_2257_; lean_object* v_toBind_2258_; lean_object* v_toPure_2259_; lean_object* v_map_2260_; lean_object* v_get_2261_; lean_object* v___f_2262_; lean_object* v___f_2263_; lean_object* v___f_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v_toApplicative_2256_ = lean_ctor_get(v_inst_2252_, 0);
lean_inc_ref(v_toApplicative_2256_);
v_toFunctor_2257_ = lean_ctor_get(v_toApplicative_2256_, 0);
lean_inc_ref(v_toFunctor_2257_);
v_toBind_2258_ = lean_ctor_get(v_inst_2252_, 1);
lean_inc(v_toBind_2258_);
lean_dec_ref(v_inst_2252_);
v_toPure_2259_ = lean_ctor_get(v_toApplicative_2256_, 1);
lean_inc(v_toPure_2259_);
lean_dec_ref(v_toApplicative_2256_);
v_map_2260_ = lean_ctor_get(v_toFunctor_2257_, 0);
lean_inc(v_map_2260_);
lean_dec_ref(v_toFunctor_2257_);
v_get_2261_ = lean_ctor_get(v_inst_2253_, 0);
lean_inc(v_get_2261_);
lean_dec_ref(v_inst_2253_);
v___f_2262_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2263_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2263_, 0, v_toPure_2259_);
lean_inc(v_toBind_2258_);
v___f_2264_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2264_, 0, v_inst_2254_);
lean_closure_set(v___f_2264_, 1, v_self_2255_);
lean_closure_set(v___f_2264_, 2, v___f_2263_);
lean_closure_set(v___f_2264_, 3, v_toBind_2258_);
v___x_2265_ = lean_apply_4(v_map_2260_, lean_box(0), lean_box(0), v___f_2262_, v_get_2261_);
v___x_2266_ = lean_apply_4(v_toBind_2258_, lean_box(0), lean_box(0), v___x_2265_, v___f_2264_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog(lean_object* v_m_2267_, lean_object* v_00_u03b2_2268_, lean_object* v_inst_2269_, lean_object* v_inst_2270_, lean_object* v_inst_2271_, lean_object* v_self_2272_){
_start:
{
lean_object* v_toApplicative_2273_; lean_object* v_toFunctor_2274_; lean_object* v_toBind_2275_; lean_object* v_toPure_2276_; lean_object* v_map_2277_; lean_object* v_get_2278_; lean_object* v___f_2279_; lean_object* v___f_2280_; lean_object* v___f_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v_toApplicative_2273_ = lean_ctor_get(v_inst_2269_, 0);
lean_inc_ref(v_toApplicative_2273_);
v_toFunctor_2274_ = lean_ctor_get(v_toApplicative_2273_, 0);
lean_inc_ref(v_toFunctor_2274_);
v_toBind_2275_ = lean_ctor_get(v_inst_2269_, 1);
lean_inc(v_toBind_2275_);
lean_dec_ref(v_inst_2269_);
v_toPure_2276_ = lean_ctor_get(v_toApplicative_2273_, 1);
lean_inc(v_toPure_2276_);
lean_dec_ref(v_toApplicative_2273_);
v_map_2277_ = lean_ctor_get(v_toFunctor_2274_, 0);
lean_inc(v_map_2277_);
lean_dec_ref(v_toFunctor_2274_);
v_get_2278_ = lean_ctor_get(v_inst_2270_, 0);
lean_inc(v_get_2278_);
lean_dec_ref(v_inst_2270_);
v___f_2279_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2280_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2280_, 0, v_toPure_2276_);
lean_inc(v_toBind_2275_);
v___f_2281_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2281_, 0, v_inst_2271_);
lean_closure_set(v___f_2281_, 1, v_self_2272_);
lean_closure_set(v___f_2281_, 2, v___f_2280_);
lean_closure_set(v___f_2281_, 3, v_toBind_2275_);
v___x_2282_ = lean_apply_4(v_map_2277_, lean_box(0), lean_box(0), v___f_2279_, v_get_2278_);
v___x_2283_ = lean_apply_4(v_toBind_2275_, lean_box(0), lean_box(0), v___x_2282_, v___f_2281_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__0(lean_object* v_x_2284_){
_start:
{
lean_object* v_fst_2285_; 
v_fst_2285_ = lean_ctor_get(v_x_2284_, 0);
lean_inc(v_fst_2285_);
return v_fst_2285_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__0___boxed(lean_object* v_x_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l_Lake_withLoggedIO___redArg___lam__0(v_x_2286_);
lean_dec_ref(v_x_2286_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__1(lean_object* v_buf_2288_){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = lean_st_ref_get(v_buf_2288_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__1___boxed(lean_object* v_buf_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lake_withLoggedIO___redArg___lam__1(v_buf_2291_);
lean_dec(v_buf_2291_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__2(lean_object* v_toPure_2294_, lean_object* v_a_2295_, lean_object* v_____r_2296_){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = lean_apply_2(v_toPure_2294_, lean_box(0), v_a_2295_);
return v___x_2297_;
}
}
static lean_object* _init_l_Lake_withLoggedIO___redArg___lam__3___closed__4(void){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2302_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___lam__3___closed__3));
v___x_2303_ = lean_unsigned_to_nat(46u);
v___x_2304_ = lean_unsigned_to_nat(193u);
v___x_2305_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___lam__3___closed__2));
v___x_2306_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___lam__3___closed__1));
v___x_2307_ = l_mkPanicMessageWithDecl(v___x_2306_, v___x_2305_, v___x_2304_, v___x_2303_, v___x_2302_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__3(lean_object* v___x_2308_, lean_object* v_inst_2309_, lean_object* v_toBind_2310_, lean_object* v___f_2311_, lean_object* v_toPure_2312_, lean_object* v_a_2313_, lean_object* v_buf_2314_){
_start:
{
lean_object* v___y_2316_; lean_object* v_data_2329_; uint8_t v___x_2330_; 
v_data_2329_ = lean_ctor_get(v_buf_2314_, 0);
lean_inc_ref(v_data_2329_);
lean_dec_ref(v_buf_2314_);
v___x_2330_ = lean_string_validate_utf8(v_data_2329_);
if (v___x_2330_ == 0)
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
lean_dec_ref(v_data_2329_);
v___x_2331_ = ((lean_object*)(l_Lake_instInhabitedLogEntry_default___closed__0));
v___x_2332_ = lean_obj_once(&l_Lake_withLoggedIO___redArg___lam__3___closed__4, &l_Lake_withLoggedIO___redArg___lam__3___closed__4_once, _init_l_Lake_withLoggedIO___redArg___lam__3___closed__4);
v___x_2333_ = l_panic___redArg(v___x_2331_, v___x_2332_);
v___y_2316_ = v___x_2333_;
goto v___jp_2315_;
}
else
{
lean_object* v___x_2334_; 
v___x_2334_ = lean_string_from_utf8_unchecked(v_data_2329_);
v___y_2316_ = v___x_2334_;
goto v___jp_2315_;
}
v___jp_2315_:
{
lean_object* v___x_2317_; uint8_t v___x_2318_; 
v___x_2317_ = lean_string_utf8_byte_size(v___y_2316_);
v___x_2318_ = lean_nat_dec_eq(v___x_2317_, v___x_2308_);
if (v___x_2318_ == 0)
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; uint8_t v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
lean_dec(v_a_2313_);
lean_dec(v_toPure_2312_);
v___x_2319_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___lam__3___closed__0));
v___x_2320_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2320_, 0, v___y_2316_);
lean_ctor_set(v___x_2320_, 1, v___x_2308_);
lean_ctor_set(v___x_2320_, 2, v___x_2317_);
v___x_2321_ = l_String_Slice_trimAscii(v___x_2320_);
v___x_2322_ = l_String_Slice_toString(v___x_2321_);
lean_dec_ref(v___x_2321_);
v___x_2323_ = lean_string_append(v___x_2319_, v___x_2322_);
lean_dec_ref(v___x_2322_);
v___x_2324_ = 1;
v___x_2325_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2325_, 0, v___x_2323_);
lean_ctor_set_uint8(v___x_2325_, sizeof(void*)*1, v___x_2324_);
v___x_2326_ = lean_apply_1(v_inst_2309_, v___x_2325_);
v___x_2327_ = lean_apply_4(v_toBind_2310_, lean_box(0), lean_box(0), v___x_2326_, v___f_2311_);
return v___x_2327_;
}
else
{
lean_object* v___x_2328_; 
lean_dec_ref(v___y_2316_);
lean_dec(v___f_2311_);
lean_dec(v_toBind_2310_);
lean_dec(v_inst_2309_);
lean_dec(v___x_2308_);
v___x_2328_ = lean_apply_2(v_toPure_2312_, lean_box(0), v_a_2313_);
return v___x_2328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__4(lean_object* v_toPure_2335_, lean_object* v___x_2336_, lean_object* v_inst_2337_, lean_object* v_toBind_2338_, lean_object* v_inst_2339_, lean_object* v___f_2340_, lean_object* v_a_2341_){
_start:
{
lean_object* v___f_2342_; lean_object* v___f_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
lean_inc(v_a_2341_);
lean_inc(v_toPure_2335_);
v___f_2342_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2342_, 0, v_toPure_2335_);
lean_closure_set(v___f_2342_, 1, v_a_2341_);
lean_inc(v_toBind_2338_);
v___f_2343_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__3), 7, 6);
lean_closure_set(v___f_2343_, 0, v___x_2336_);
lean_closure_set(v___f_2343_, 1, v_inst_2337_);
lean_closure_set(v___f_2343_, 2, v_toBind_2338_);
lean_closure_set(v___f_2343_, 3, v___f_2342_);
lean_closure_set(v___f_2343_, 4, v_toPure_2335_);
lean_closure_set(v___f_2343_, 5, v_a_2341_);
v___x_2344_ = lean_apply_2(v_inst_2339_, lean_box(0), v___f_2340_);
v___x_2345_ = lean_apply_4(v_toBind_2338_, lean_box(0), lean_box(0), v___x_2344_, v___f_2343_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__5(lean_object* v_stderr_2346_, lean_object* v_inst_2347_, lean_object* v_mapConst_2348_, lean_object* v_____r_2349_){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2350_ = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(v___x_2350_, 0, v_stderr_2346_);
v___x_2351_ = lean_apply_2(v_inst_2347_, lean_box(0), v___x_2350_);
v___x_2352_ = lean_box(0);
v___x_2353_ = lean_apply_4(v_mapConst_2348_, lean_box(0), lean_box(0), v___x_2352_, v___x_2351_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__6(lean_object* v___x_2354_, lean_object* v_x_2355_){
_start:
{
lean_inc(v___x_2354_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__6___boxed(lean_object* v___x_2356_, lean_object* v_x_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l_Lake_withLoggedIO___redArg___lam__6(v___x_2356_, v_x_2357_);
lean_dec(v_x_2357_);
lean_dec(v___x_2356_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__7(lean_object* v_toFunctor_2359_, lean_object* v_inst_2360_, lean_object* v_stdout_2361_, lean_object* v_toBind_2362_, lean_object* v_inst_2363_, lean_object* v_x_2364_, lean_object* v___f_2365_, lean_object* v___f_2366_, lean_object* v_stderr_2367_){
_start:
{
lean_object* v_map_2368_; lean_object* v_mapConst_2369_; lean_object* v___f_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___f_2376_; lean_object* v_y_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v_map_2368_ = lean_ctor_get(v_toFunctor_2359_, 0);
lean_inc(v_map_2368_);
v_mapConst_2369_ = lean_ctor_get(v_toFunctor_2359_, 1);
lean_inc(v_mapConst_2369_);
lean_dec_ref(v_toFunctor_2359_);
lean_inc(v_mapConst_2369_);
lean_inc(v_inst_2360_);
v___f_2370_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__5), 4, 3);
lean_closure_set(v___f_2370_, 0, v_stderr_2367_);
lean_closure_set(v___f_2370_, 1, v_inst_2360_);
lean_closure_set(v___f_2370_, 2, v_mapConst_2369_);
v___x_2371_ = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(v___x_2371_, 0, v_stdout_2361_);
v___x_2372_ = lean_apply_2(v_inst_2360_, lean_box(0), v___x_2371_);
v___x_2373_ = lean_box(0);
v___x_2374_ = lean_apply_4(v_mapConst_2369_, lean_box(0), lean_box(0), v___x_2373_, v___x_2372_);
lean_inc(v_toBind_2362_);
v___x_2375_ = lean_apply_4(v_toBind_2362_, lean_box(0), lean_box(0), v___x_2374_, v___f_2370_);
v___f_2376_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__6___boxed), 2, 1);
lean_closure_set(v___f_2376_, 0, v___x_2375_);
v_y_2377_ = lean_apply_4(v_inst_2363_, lean_box(0), lean_box(0), v_x_2364_, v___f_2376_);
v___x_2378_ = lean_apply_4(v_map_2368_, lean_box(0), lean_box(0), v___f_2365_, v_y_2377_);
v___x_2379_ = lean_apply_4(v_toBind_2362_, lean_box(0), lean_box(0), v___x_2378_, v___f_2366_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__8(lean_object* v_toFunctor_2380_, lean_object* v_inst_2381_, lean_object* v_toBind_2382_, lean_object* v_inst_2383_, lean_object* v_x_2384_, lean_object* v___f_2385_, lean_object* v___f_2386_, lean_object* v___x_2387_, lean_object* v_stdout_2388_){
_start:
{
lean_object* v___f_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
lean_inc(v_toBind_2382_);
lean_inc(v_inst_2381_);
v___f_2389_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__7), 9, 8);
lean_closure_set(v___f_2389_, 0, v_toFunctor_2380_);
lean_closure_set(v___f_2389_, 1, v_inst_2381_);
lean_closure_set(v___f_2389_, 2, v_stdout_2388_);
lean_closure_set(v___f_2389_, 3, v_toBind_2382_);
lean_closure_set(v___f_2389_, 4, v_inst_2383_);
lean_closure_set(v___f_2389_, 5, v_x_2384_);
lean_closure_set(v___f_2389_, 6, v___f_2385_);
lean_closure_set(v___f_2389_, 7, v___f_2386_);
v___x_2390_ = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(v___x_2390_, 0, v___x_2387_);
v___x_2391_ = lean_apply_2(v_inst_2381_, lean_box(0), v___x_2390_);
v___x_2392_ = lean_apply_4(v_toBind_2382_, lean_box(0), lean_box(0), v___x_2391_, v___f_2389_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__9(lean_object* v_toPure_2393_, lean_object* v___x_2394_, lean_object* v_inst_2395_, lean_object* v_toBind_2396_, lean_object* v_inst_2397_, lean_object* v_toFunctor_2398_, lean_object* v_inst_2399_, lean_object* v_x_2400_, lean_object* v___f_2401_, lean_object* v_buf_2402_){
_start:
{
lean_object* v___f_2403_; lean_object* v___f_2404_; lean_object* v___x_2405_; lean_object* v___f_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
lean_inc(v_buf_2402_);
v___f_2403_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2403_, 0, v_buf_2402_);
lean_inc(v_inst_2397_);
lean_inc(v_toBind_2396_);
v___f_2404_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__4), 7, 6);
lean_closure_set(v___f_2404_, 0, v_toPure_2393_);
lean_closure_set(v___f_2404_, 1, v___x_2394_);
lean_closure_set(v___f_2404_, 2, v_inst_2395_);
lean_closure_set(v___f_2404_, 3, v_toBind_2396_);
lean_closure_set(v___f_2404_, 4, v_inst_2397_);
lean_closure_set(v___f_2404_, 5, v___f_2403_);
v___x_2405_ = l_IO_FS_Stream_ofBuffer(v_buf_2402_);
lean_inc_ref(v___x_2405_);
lean_inc(v_toBind_2396_);
lean_inc(v_inst_2397_);
v___f_2406_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__8), 9, 8);
lean_closure_set(v___f_2406_, 0, v_toFunctor_2398_);
lean_closure_set(v___f_2406_, 1, v_inst_2397_);
lean_closure_set(v___f_2406_, 2, v_toBind_2396_);
lean_closure_set(v___f_2406_, 3, v_inst_2399_);
lean_closure_set(v___f_2406_, 4, v_x_2400_);
lean_closure_set(v___f_2406_, 5, v___f_2401_);
lean_closure_set(v___f_2406_, 6, v___f_2404_);
lean_closure_set(v___f_2406_, 7, v___x_2405_);
v___x_2407_ = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(v___x_2407_, 0, v___x_2405_);
v___x_2408_ = lean_apply_2(v_inst_2397_, lean_box(0), v___x_2407_);
v___x_2409_ = lean_apply_4(v_toBind_2396_, lean_box(0), lean_box(0), v___x_2408_, v___f_2406_);
return v___x_2409_;
}
}
static lean_object* _init_l_Lake_withLoggedIO___redArg___closed__1(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2411_ = lean_unsigned_to_nat(0u);
v___x_2412_ = l_ByteArray_empty;
v___x_2413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
lean_ctor_set(v___x_2413_, 1, v___x_2411_);
return v___x_2413_;
}
}
static lean_object* _init_l_Lake_withLoggedIO___redArg___closed__2(void){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = lean_obj_once(&l_Lake_withLoggedIO___redArg___closed__1, &l_Lake_withLoggedIO___redArg___closed__1_once, _init_l_Lake_withLoggedIO___redArg___closed__1);
v___x_2415_ = lean_alloc_closure((void*)(l_IO_mkRef___boxed), 3, 2);
lean_closure_set(v___x_2415_, 0, lean_box(0));
lean_closure_set(v___x_2415_, 1, v___x_2414_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg(lean_object* v_inst_2416_, lean_object* v_inst_2417_, lean_object* v_inst_2418_, lean_object* v_inst_2419_, lean_object* v_x_2420_){
_start:
{
lean_object* v_toApplicative_2421_; lean_object* v_toBind_2422_; lean_object* v_toFunctor_2423_; lean_object* v_toPure_2424_; lean_object* v___f_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___f_2429_; lean_object* v___x_2430_; 
v_toApplicative_2421_ = lean_ctor_get(v_inst_2416_, 0);
lean_inc_ref(v_toApplicative_2421_);
v_toBind_2422_ = lean_ctor_get(v_inst_2416_, 1);
lean_inc(v_toBind_2422_);
lean_dec_ref(v_inst_2416_);
v_toFunctor_2423_ = lean_ctor_get(v_toApplicative_2421_, 0);
lean_inc_ref(v_toFunctor_2423_);
v_toPure_2424_ = lean_ctor_get(v_toApplicative_2421_, 1);
lean_inc(v_toPure_2424_);
lean_dec_ref(v_toApplicative_2421_);
v___f_2425_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___closed__0));
v___x_2426_ = lean_unsigned_to_nat(0u);
v___x_2427_ = lean_obj_once(&l_Lake_withLoggedIO___redArg___closed__2, &l_Lake_withLoggedIO___redArg___closed__2_once, _init_l_Lake_withLoggedIO___redArg___closed__2);
lean_inc(v_inst_2417_);
v___x_2428_ = lean_apply_2(v_inst_2417_, lean_box(0), v___x_2427_);
lean_inc(v_toBind_2422_);
v___f_2429_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__9), 10, 9);
lean_closure_set(v___f_2429_, 0, v_toPure_2424_);
lean_closure_set(v___f_2429_, 1, v___x_2426_);
lean_closure_set(v___f_2429_, 2, v_inst_2418_);
lean_closure_set(v___f_2429_, 3, v_toBind_2422_);
lean_closure_set(v___f_2429_, 4, v_inst_2417_);
lean_closure_set(v___f_2429_, 5, v_toFunctor_2423_);
lean_closure_set(v___f_2429_, 6, v_inst_2419_);
lean_closure_set(v___f_2429_, 7, v_x_2420_);
lean_closure_set(v___f_2429_, 8, v___f_2425_);
v___x_2430_ = lean_apply_4(v_toBind_2422_, lean_box(0), lean_box(0), v___x_2428_, v___f_2429_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO(lean_object* v_m_2431_, lean_object* v_00_u03b1_2432_, lean_object* v_inst_2433_, lean_object* v_inst_2434_, lean_object* v_inst_2435_, lean_object* v_inst_2436_, lean_object* v_x_2437_){
_start:
{
lean_object* v_toApplicative_2438_; lean_object* v_toBind_2439_; lean_object* v_toFunctor_2440_; lean_object* v_toPure_2441_; lean_object* v___f_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___f_2446_; lean_object* v___x_2447_; 
v_toApplicative_2438_ = lean_ctor_get(v_inst_2433_, 0);
lean_inc_ref(v_toApplicative_2438_);
v_toBind_2439_ = lean_ctor_get(v_inst_2433_, 1);
lean_inc(v_toBind_2439_);
lean_dec_ref(v_inst_2433_);
v_toFunctor_2440_ = lean_ctor_get(v_toApplicative_2438_, 0);
lean_inc_ref(v_toFunctor_2440_);
v_toPure_2441_ = lean_ctor_get(v_toApplicative_2438_, 1);
lean_inc(v_toPure_2441_);
lean_dec_ref(v_toApplicative_2438_);
v___f_2442_ = ((lean_object*)(l_Lake_withLoggedIO___redArg___closed__0));
v___x_2443_ = lean_unsigned_to_nat(0u);
v___x_2444_ = lean_obj_once(&l_Lake_withLoggedIO___redArg___closed__2, &l_Lake_withLoggedIO___redArg___closed__2_once, _init_l_Lake_withLoggedIO___redArg___closed__2);
lean_inc(v_inst_2434_);
v___x_2445_ = lean_apply_2(v_inst_2434_, lean_box(0), v___x_2444_);
lean_inc(v_toBind_2439_);
v___f_2446_ = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__9), 10, 9);
lean_closure_set(v___f_2446_, 0, v_toPure_2441_);
lean_closure_set(v___f_2446_, 1, v___x_2443_);
lean_closure_set(v___f_2446_, 2, v_inst_2435_);
lean_closure_set(v___f_2446_, 3, v_toBind_2439_);
lean_closure_set(v___f_2446_, 4, v_inst_2434_);
lean_closure_set(v___f_2446_, 5, v_toFunctor_2440_);
lean_closure_set(v___f_2446_, 6, v_inst_2436_);
lean_closure_set(v___f_2446_, 7, v_x_2437_);
lean_closure_set(v___f_2446_, 8, v___f_2442_);
v___x_2447_ = lean_apply_4(v_toBind_2439_, lean_box(0), lean_box(0), v___x_2445_, v___f_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_error___redArg___lam__3(lean_object* v_inst_2448_, lean_object* v___x_2449_, lean_object* v___f_2450_, lean_object* v_toBind_2451_, lean_object* v_iniPos_2452_){
_start:
{
lean_object* v_throw_2453_; lean_object* v_tryCatch_2454_; lean_object* v___f_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v_throw_2453_ = lean_ctor_get(v_inst_2448_, 0);
lean_inc(v_throw_2453_);
v_tryCatch_2454_ = lean_ctor_get(v_inst_2448_, 1);
lean_inc(v_tryCatch_2454_);
lean_dec_ref(v_inst_2448_);
v___f_2455_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2455_, 0, v_throw_2453_);
lean_closure_set(v___f_2455_, 1, v_iniPos_2452_);
v___x_2456_ = lean_apply_3(v_tryCatch_2454_, lean_box(0), v___x_2449_, v___f_2450_);
v___x_2457_ = lean_apply_4(v_toBind_2451_, lean_box(0), lean_box(0), v___x_2456_, v___f_2455_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_error___redArg(lean_object* v_inst_2458_, lean_object* v_inst_2459_, lean_object* v_inst_2460_, lean_object* v_inst_2461_, lean_object* v_msg_2462_){
_start:
{
lean_object* v_toApplicative_2463_; lean_object* v_toFunctor_2464_; lean_object* v_toBind_2465_; lean_object* v_toPure_2466_; lean_object* v_map_2467_; lean_object* v_get_2468_; lean_object* v___f_2469_; uint8_t v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___f_2473_; lean_object* v___f_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v_toApplicative_2463_ = lean_ctor_get(v_inst_2458_, 0);
lean_inc_ref(v_toApplicative_2463_);
v_toFunctor_2464_ = lean_ctor_get(v_toApplicative_2463_, 0);
lean_inc_ref(v_toFunctor_2464_);
v_toBind_2465_ = lean_ctor_get(v_inst_2458_, 1);
lean_inc(v_toBind_2465_);
lean_dec_ref(v_inst_2458_);
v_toPure_2466_ = lean_ctor_get(v_toApplicative_2463_, 1);
lean_inc(v_toPure_2466_);
lean_dec_ref(v_toApplicative_2463_);
v_map_2467_ = lean_ctor_get(v_toFunctor_2464_, 0);
lean_inc(v_map_2467_);
lean_dec_ref(v_toFunctor_2464_);
v_get_2468_ = lean_ctor_get(v_inst_2460_, 0);
lean_inc(v_get_2468_);
lean_dec_ref(v_inst_2460_);
v___f_2469_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_2470_ = 3;
v___x_2471_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2471_, 0, v_msg_2462_);
lean_ctor_set_uint8(v___x_2471_, sizeof(void*)*1, v___x_2470_);
v___x_2472_ = lean_apply_1(v_inst_2459_, v___x_2471_);
v___f_2473_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2473_, 0, v_toPure_2466_);
lean_inc(v_toBind_2465_);
v___f_2474_ = lean_alloc_closure((void*)(l_Lake_ELog_error___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2474_, 0, v_inst_2461_);
lean_closure_set(v___f_2474_, 1, v___x_2472_);
lean_closure_set(v___f_2474_, 2, v___f_2473_);
lean_closure_set(v___f_2474_, 3, v_toBind_2465_);
v___x_2475_ = lean_apply_4(v_map_2467_, lean_box(0), lean_box(0), v___f_2469_, v_get_2468_);
v___x_2476_ = lean_apply_4(v_toBind_2465_, lean_box(0), lean_box(0), v___x_2475_, v___f_2474_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_error(lean_object* v_m_2477_, lean_object* v_00_u03b1_2478_, lean_object* v_inst_2479_, lean_object* v_inst_2480_, lean_object* v_inst_2481_, lean_object* v_inst_2482_, lean_object* v_msg_2483_){
_start:
{
lean_object* v_toApplicative_2484_; lean_object* v_toFunctor_2485_; lean_object* v_toBind_2486_; lean_object* v_toPure_2487_; lean_object* v_map_2488_; lean_object* v_get_2489_; lean_object* v___f_2490_; uint8_t v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___f_2494_; lean_object* v___f_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v_toApplicative_2484_ = lean_ctor_get(v_inst_2479_, 0);
lean_inc_ref(v_toApplicative_2484_);
v_toFunctor_2485_ = lean_ctor_get(v_toApplicative_2484_, 0);
lean_inc_ref(v_toFunctor_2485_);
v_toBind_2486_ = lean_ctor_get(v_inst_2479_, 1);
lean_inc(v_toBind_2486_);
lean_dec_ref(v_inst_2479_);
v_toPure_2487_ = lean_ctor_get(v_toApplicative_2484_, 1);
lean_inc(v_toPure_2487_);
lean_dec_ref(v_toApplicative_2484_);
v_map_2488_ = lean_ctor_get(v_toFunctor_2485_, 0);
lean_inc(v_map_2488_);
lean_dec_ref(v_toFunctor_2485_);
v_get_2489_ = lean_ctor_get(v_inst_2481_, 0);
lean_inc(v_get_2489_);
lean_dec_ref(v_inst_2481_);
v___f_2490_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___x_2491_ = 3;
v___x_2492_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2492_, 0, v_msg_2483_);
lean_ctor_set_uint8(v___x_2492_, sizeof(void*)*1, v___x_2491_);
v___x_2493_ = lean_apply_1(v_inst_2480_, v___x_2492_);
v___f_2494_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2494_, 0, v_toPure_2487_);
lean_inc(v_toBind_2486_);
v___f_2495_ = lean_alloc_closure((void*)(l_Lake_ELog_error___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2495_, 0, v_inst_2482_);
lean_closure_set(v___f_2495_, 1, v___x_2493_);
lean_closure_set(v___f_2495_, 2, v___f_2494_);
lean_closure_set(v___f_2495_, 3, v_toBind_2486_);
v___x_2496_ = lean_apply_4(v_map_2488_, lean_box(0), lean_box(0), v___f_2490_, v_get_2489_);
v___x_2497_ = lean_apply_4(v_toBind_2486_, lean_box(0), lean_box(0), v___x_2496_, v___f_2495_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_monadError___redArg___lam__4(lean_object* v_inst_2498_, lean_object* v_inst_2499_, lean_object* v_inst_2500_, lean_object* v_inst_2501_, lean_object* v___f_2502_, lean_object* v_00_u03b1_2503_, lean_object* v___y_2504_){
_start:
{
lean_object* v_toApplicative_2505_; lean_object* v_toFunctor_2506_; lean_object* v_toBind_2507_; lean_object* v_toPure_2508_; lean_object* v_map_2509_; lean_object* v_get_2510_; uint8_t v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___f_2514_; lean_object* v___f_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v_toApplicative_2505_ = lean_ctor_get(v_inst_2498_, 0);
lean_inc_ref(v_toApplicative_2505_);
v_toFunctor_2506_ = lean_ctor_get(v_toApplicative_2505_, 0);
lean_inc_ref(v_toFunctor_2506_);
v_toBind_2507_ = lean_ctor_get(v_inst_2498_, 1);
lean_inc(v_toBind_2507_);
lean_dec_ref(v_inst_2498_);
v_toPure_2508_ = lean_ctor_get(v_toApplicative_2505_, 1);
lean_inc(v_toPure_2508_);
lean_dec_ref(v_toApplicative_2505_);
v_map_2509_ = lean_ctor_get(v_toFunctor_2506_, 0);
lean_inc(v_map_2509_);
lean_dec_ref(v_toFunctor_2506_);
v_get_2510_ = lean_ctor_get(v_inst_2499_, 0);
lean_inc(v_get_2510_);
lean_dec_ref(v_inst_2499_);
v___x_2511_ = 3;
v___x_2512_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2512_, 0, v___y_2504_);
lean_ctor_set_uint8(v___x_2512_, sizeof(void*)*1, v___x_2511_);
v___x_2513_ = lean_apply_1(v_inst_2500_, v___x_2512_);
v___f_2514_ = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2514_, 0, v_toPure_2508_);
lean_inc(v_toBind_2507_);
v___f_2515_ = lean_alloc_closure((void*)(l_Lake_ELog_error___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2515_, 0, v_inst_2501_);
lean_closure_set(v___f_2515_, 1, v___x_2513_);
lean_closure_set(v___f_2515_, 2, v___f_2514_);
lean_closure_set(v___f_2515_, 3, v_toBind_2507_);
v___x_2516_ = lean_apply_4(v_map_2509_, lean_box(0), lean_box(0), v___f_2502_, v_get_2510_);
v___x_2517_ = lean_apply_4(v_toBind_2507_, lean_box(0), lean_box(0), v___x_2516_, v___f_2515_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_monadError___redArg(lean_object* v_inst_2518_, lean_object* v_inst_2519_, lean_object* v_inst_2520_, lean_object* v_inst_2521_){
_start:
{
lean_object* v___f_2522_; lean_object* v___f_2523_; 
v___f_2522_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2523_ = lean_alloc_closure((void*)(l_Lake_ELog_monadError___redArg___lam__4), 7, 5);
lean_closure_set(v___f_2523_, 0, v_inst_2518_);
lean_closure_set(v___f_2523_, 1, v_inst_2520_);
lean_closure_set(v___f_2523_, 2, v_inst_2519_);
lean_closure_set(v___f_2523_, 3, v_inst_2521_);
lean_closure_set(v___f_2523_, 4, v___f_2522_);
return v___f_2523_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_monadError(lean_object* v_m_2524_, lean_object* v_inst_2525_, lean_object* v_inst_2526_, lean_object* v_inst_2527_, lean_object* v_inst_2528_){
_start:
{
lean_object* v___f_2529_; lean_object* v___f_2530_; 
v___f_2529_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2530_ = lean_alloc_closure((void*)(l_Lake_ELog_monadError___redArg___lam__4), 7, 5);
lean_closure_set(v___f_2530_, 0, v_inst_2525_);
lean_closure_set(v___f_2530_, 1, v_inst_2527_);
lean_closure_set(v___f_2530_, 2, v_inst_2526_);
lean_closure_set(v___f_2530_, 3, v_inst_2528_);
lean_closure_set(v___f_2530_, 4, v___f_2529_);
return v___f_2530_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_failure___redArg___lam__1(lean_object* v_inst_2531_, lean_object* v_____do__lift_2532_){
_start:
{
lean_object* v_throw_2533_; lean_object* v___x_2534_; 
v_throw_2533_ = lean_ctor_get(v_inst_2531_, 0);
lean_inc(v_throw_2533_);
lean_dec_ref(v_inst_2531_);
v___x_2534_ = lean_apply_2(v_throw_2533_, lean_box(0), v_____do__lift_2532_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_failure___redArg(lean_object* v_inst_2535_, lean_object* v_inst_2536_, lean_object* v_inst_2537_){
_start:
{
lean_object* v_toApplicative_2538_; lean_object* v_toFunctor_2539_; lean_object* v_toBind_2540_; lean_object* v_map_2541_; lean_object* v_get_2542_; lean_object* v___f_2543_; lean_object* v___f_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v_toApplicative_2538_ = lean_ctor_get(v_inst_2535_, 0);
v_toFunctor_2539_ = lean_ctor_get(v_toApplicative_2538_, 0);
lean_inc_ref(v_toFunctor_2539_);
v_toBind_2540_ = lean_ctor_get(v_inst_2535_, 1);
lean_inc(v_toBind_2540_);
lean_dec_ref(v_inst_2535_);
v_map_2541_ = lean_ctor_get(v_toFunctor_2539_, 0);
lean_inc(v_map_2541_);
lean_dec_ref(v_toFunctor_2539_);
v_get_2542_ = lean_ctor_get(v_inst_2536_, 0);
lean_inc(v_get_2542_);
lean_dec_ref(v_inst_2536_);
v___f_2543_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2544_ = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2544_, 0, v_inst_2537_);
v___x_2545_ = lean_apply_4(v_map_2541_, lean_box(0), lean_box(0), v___f_2543_, v_get_2542_);
v___x_2546_ = lean_apply_4(v_toBind_2540_, lean_box(0), lean_box(0), v___x_2545_, v___f_2544_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_failure(lean_object* v_m_2547_, lean_object* v_00_u03b1_2548_, lean_object* v_inst_2549_, lean_object* v_inst_2550_, lean_object* v_inst_2551_){
_start:
{
lean_object* v_toApplicative_2552_; lean_object* v_toFunctor_2553_; lean_object* v_toBind_2554_; lean_object* v_map_2555_; lean_object* v_get_2556_; lean_object* v___f_2557_; lean_object* v___f_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v_toApplicative_2552_ = lean_ctor_get(v_inst_2549_, 0);
v_toFunctor_2553_ = lean_ctor_get(v_toApplicative_2552_, 0);
lean_inc_ref(v_toFunctor_2553_);
v_toBind_2554_ = lean_ctor_get(v_inst_2549_, 1);
lean_inc(v_toBind_2554_);
lean_dec_ref(v_inst_2549_);
v_map_2555_ = lean_ctor_get(v_toFunctor_2553_, 0);
lean_inc(v_map_2555_);
lean_dec_ref(v_toFunctor_2553_);
v_get_2556_ = lean_ctor_get(v_inst_2550_, 0);
lean_inc(v_get_2556_);
lean_dec_ref(v_inst_2550_);
v___f_2557_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
v___f_2558_ = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2558_, 0, v_inst_2551_);
v___x_2559_ = lean_apply_4(v_map_2555_, lean_box(0), lean_box(0), v___f_2557_, v_get_2556_);
v___x_2560_ = lean_apply_4(v_toBind_2554_, lean_box(0), lean_box(0), v___x_2559_, v___f_2558_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__0(lean_object* v_y_2561_, lean_object* v_____r_2562_){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2563_ = lean_box(0);
v___x_2564_ = lean_apply_1(v_y_2561_, v___x_2563_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__1(lean_object* v_errPos_2565_, lean_object* v_s_2566_){
_start:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2567_ = lean_box(0);
v___x_2568_ = l_Array_shrink___redArg(v_s_2566_, v_errPos_2565_);
v___x_2569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2567_);
lean_ctor_set(v___x_2569_, 1, v___x_2568_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__1___boxed(lean_object* v_errPos_2570_, lean_object* v_s_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_Lake_ELog_orElse___redArg___lam__1(v_errPos_2570_, v_s_2571_);
lean_dec(v_errPos_2570_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__2(lean_object* v_inst_2573_, lean_object* v_toBind_2574_, lean_object* v___f_2575_, lean_object* v_errPos_2576_){
_start:
{
lean_object* v_modifyGet_2577_; lean_object* v___f_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v_modifyGet_2577_ = lean_ctor_get(v_inst_2573_, 2);
lean_inc(v_modifyGet_2577_);
lean_dec_ref(v_inst_2573_);
v___f_2578_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2578_, 0, v_errPos_2576_);
v___x_2579_ = lean_apply_2(v_modifyGet_2577_, lean_box(0), v___f_2578_);
v___x_2580_ = lean_apply_4(v_toBind_2574_, lean_box(0), lean_box(0), v___x_2579_, v___f_2575_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg(lean_object* v_inst_2581_, lean_object* v_inst_2582_, lean_object* v_inst_2583_, lean_object* v_x_2584_, lean_object* v_y_2585_){
_start:
{
lean_object* v_toBind_2586_; lean_object* v_tryCatch_2587_; lean_object* v___f_2588_; lean_object* v___f_2589_; lean_object* v___x_2590_; 
v_toBind_2586_ = lean_ctor_get(v_inst_2581_, 1);
lean_inc(v_toBind_2586_);
lean_dec_ref(v_inst_2581_);
v_tryCatch_2587_ = lean_ctor_get(v_inst_2583_, 1);
lean_inc(v_tryCatch_2587_);
lean_dec_ref(v_inst_2583_);
v___f_2588_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2588_, 0, v_y_2585_);
v___f_2589_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2589_, 0, v_inst_2582_);
lean_closure_set(v___f_2589_, 1, v_toBind_2586_);
lean_closure_set(v___f_2589_, 2, v___f_2588_);
v___x_2590_ = lean_apply_3(v_tryCatch_2587_, lean_box(0), v_x_2584_, v___f_2589_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse(lean_object* v_m_2591_, lean_object* v_00_u03b1_2592_, lean_object* v_inst_2593_, lean_object* v_inst_2594_, lean_object* v_inst_2595_, lean_object* v_x_2596_, lean_object* v_y_2597_){
_start:
{
lean_object* v_toBind_2598_; lean_object* v_tryCatch_2599_; lean_object* v___f_2600_; lean_object* v___f_2601_; lean_object* v___x_2602_; 
v_toBind_2598_ = lean_ctor_get(v_inst_2593_, 1);
lean_inc(v_toBind_2598_);
lean_dec_ref(v_inst_2593_);
v_tryCatch_2599_ = lean_ctor_get(v_inst_2595_, 1);
lean_inc(v_tryCatch_2599_);
lean_dec_ref(v_inst_2595_);
v___f_2600_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2600_, 0, v_y_2597_);
v___f_2601_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2601_, 0, v_inst_2594_);
lean_closure_set(v___f_2601_, 1, v_toBind_2598_);
lean_closure_set(v___f_2601_, 2, v___f_2600_);
v___x_2602_ = lean_apply_3(v_tryCatch_2599_, lean_box(0), v_x_2596_, v___f_2601_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__2(lean_object* v_toApplicative_2603_, lean_object* v_inst_2604_, lean_object* v___f_2605_, lean_object* v_toBind_2606_, lean_object* v___f_2607_, lean_object* v_00_u03b1_2608_){
_start:
{
lean_object* v_toFunctor_2609_; lean_object* v_map_2610_; lean_object* v_get_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v_toFunctor_2609_ = lean_ctor_get(v_toApplicative_2603_, 0);
lean_inc_ref(v_toFunctor_2609_);
lean_dec_ref(v_toApplicative_2603_);
v_map_2610_ = lean_ctor_get(v_toFunctor_2609_, 0);
lean_inc(v_map_2610_);
lean_dec_ref(v_toFunctor_2609_);
v_get_2611_ = lean_ctor_get(v_inst_2604_, 0);
lean_inc(v_get_2611_);
lean_dec_ref(v_inst_2604_);
v___x_2612_ = lean_apply_4(v_map_2610_, lean_box(0), lean_box(0), v___f_2605_, v_get_2611_);
v___x_2613_ = lean_apply_4(v_toBind_2606_, lean_box(0), lean_box(0), v___x_2612_, v___f_2607_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__0(lean_object* v___y_2614_, lean_object* v_____r_2615_){
_start:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2616_ = lean_box(0);
v___x_2617_ = lean_apply_1(v___y_2614_, v___x_2616_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__4(lean_object* v_inst_2618_, lean_object* v_inst_2619_, lean_object* v_toBind_2620_, lean_object* v_00_u03b1_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v_tryCatch_2624_; lean_object* v___f_2625_; lean_object* v___f_2626_; lean_object* v___x_2627_; 
v_tryCatch_2624_ = lean_ctor_get(v_inst_2618_, 1);
lean_inc(v_tryCatch_2624_);
lean_dec_ref(v_inst_2618_);
v___f_2625_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2625_, 0, v___y_2623_);
v___f_2626_ = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2626_, 0, v_inst_2619_);
lean_closure_set(v___f_2626_, 1, v_toBind_2620_);
lean_closure_set(v___f_2626_, 2, v___f_2625_);
v___x_2627_ = lean_apply_3(v_tryCatch_2624_, lean_box(0), v___y_2622_, v___f_2626_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg(lean_object* v_inst_2628_, lean_object* v_inst_2629_, lean_object* v_inst_2630_){
_start:
{
lean_object* v_toApplicative_2631_; lean_object* v_toBind_2632_; lean_object* v___f_2633_; lean_object* v___f_2634_; lean_object* v___f_2635_; lean_object* v___f_2636_; lean_object* v___x_2637_; 
v_toApplicative_2631_ = lean_ctor_get(v_inst_2628_, 0);
lean_inc_ref(v_toApplicative_2631_);
v_toBind_2632_ = lean_ctor_get(v_inst_2628_, 1);
lean_inc(v_toBind_2632_);
lean_dec_ref(v_inst_2628_);
v___f_2633_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
lean_inc_ref(v_inst_2630_);
v___f_2634_ = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2634_, 0, v_inst_2630_);
lean_inc(v_toBind_2632_);
lean_inc_ref(v_inst_2629_);
lean_inc_ref(v_toApplicative_2631_);
v___f_2635_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2635_, 0, v_toApplicative_2631_);
lean_closure_set(v___f_2635_, 1, v_inst_2629_);
lean_closure_set(v___f_2635_, 2, v___f_2633_);
lean_closure_set(v___f_2635_, 3, v_toBind_2632_);
lean_closure_set(v___f_2635_, 4, v___f_2634_);
v___f_2636_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__4), 6, 3);
lean_closure_set(v___f_2636_, 0, v_inst_2630_);
lean_closure_set(v___f_2636_, 1, v_inst_2629_);
lean_closure_set(v___f_2636_, 2, v_toBind_2632_);
v___x_2637_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2637_, 0, v_toApplicative_2631_);
lean_ctor_set(v___x_2637_, 1, v___f_2635_);
lean_ctor_set(v___x_2637_, 2, v___f_2636_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative(lean_object* v_m_2638_, lean_object* v_inst_2639_, lean_object* v_inst_2640_, lean_object* v_inst_2641_){
_start:
{
lean_object* v_toApplicative_2642_; lean_object* v_toBind_2643_; lean_object* v___f_2644_; lean_object* v___f_2645_; lean_object* v___f_2646_; lean_object* v___f_2647_; lean_object* v___x_2648_; 
v_toApplicative_2642_ = lean_ctor_get(v_inst_2639_, 0);
lean_inc_ref(v_toApplicative_2642_);
v_toBind_2643_ = lean_ctor_get(v_inst_2639_, 1);
lean_inc(v_toBind_2643_);
lean_dec_ref(v_inst_2639_);
v___f_2644_ = ((lean_object*)(l_Lake_getLogPos___redArg___closed__0));
lean_inc_ref(v_inst_2641_);
v___f_2645_ = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2645_, 0, v_inst_2641_);
lean_inc(v_toBind_2643_);
lean_inc_ref(v_inst_2640_);
lean_inc_ref(v_toApplicative_2642_);
v___f_2646_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2646_, 0, v_toApplicative_2642_);
lean_closure_set(v___f_2646_, 1, v_inst_2640_);
lean_closure_set(v___f_2646_, 2, v___f_2644_);
lean_closure_set(v___f_2646_, 3, v_toBind_2643_);
lean_closure_set(v___f_2646_, 4, v___f_2645_);
v___f_2647_ = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__4), 6, 3);
lean_closure_set(v___f_2647_, 0, v_inst_2641_);
lean_closure_set(v___f_2647_, 1, v_inst_2640_);
lean_closure_set(v___f_2647_, 2, v_toBind_2643_);
v___x_2648_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2648_, 0, v_toApplicative_2642_);
lean_ctor_set(v___x_2648_, 1, v___f_2646_);
lean_ctor_set(v___x_2648_, 2, v___f_2647_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogLogTOfMonad___redArg(lean_object* v_inst_2649_){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = l_instMonadStateOfStateTOfMonad___redArg(v_inst_2649_);
v___x_2651_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(v___x_2651_, 0, lean_box(0));
lean_closure_set(v___x_2651_, 1, v___x_2650_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogLogTOfMonad(lean_object* v_m_2652_, lean_object* v_inst_2653_){
_start:
{
lean_object* v___x_2654_; 
v___x_2654_ = l_Lake_instMonadLogLogTOfMonad___redArg(v_inst_2653_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run___redArg(lean_object* v_self_2655_, lean_object* v_log_2656_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = lean_apply_1(v_self_2655_, v_log_2656_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run(lean_object* v_m_2658_, lean_object* v_00_u03b1_2659_, lean_object* v_self_2660_, lean_object* v_log_2661_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = lean_apply_1(v_self_2660_, v_log_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg___lam__0(lean_object* v_x_2663_){
_start:
{
lean_object* v_fst_2664_; 
v_fst_2664_ = lean_ctor_get(v_x_2663_, 0);
lean_inc(v_fst_2664_);
return v_fst_2664_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg___lam__0___boxed(lean_object* v_x_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Lake_LogT_run_x27___redArg___lam__0(v_x_2665_);
lean_dec_ref(v_x_2665_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg(lean_object* v_inst_2668_, lean_object* v_self_2669_, lean_object* v_log_2670_){
_start:
{
lean_object* v_map_2671_; lean_object* v___f_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v_map_2671_ = lean_ctor_get(v_inst_2668_, 0);
lean_inc(v_map_2671_);
lean_dec_ref(v_inst_2668_);
v___f_2672_ = ((lean_object*)(l_Lake_LogT_run_x27___redArg___closed__0));
v___x_2673_ = lean_apply_1(v_self_2669_, v_log_2670_);
v___x_2674_ = lean_apply_4(v_map_2671_, lean_box(0), lean_box(0), v___f_2672_, v___x_2673_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27(lean_object* v_m_2675_, lean_object* v_00_u03b1_2676_, lean_object* v_inst_2677_, lean_object* v_self_2678_, lean_object* v_log_2679_){
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
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__1(lean_object* v_toPure_2684_, lean_object* v_fst_2685_, lean_object* v_____r_2686_){
_start:
{
lean_object* v___x_2687_; 
v___x_2687_ = lean_apply_2(v_toPure_2684_, lean_box(0), v_fst_2685_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__0(lean_object* v_toPure_2688_, lean_object* v_set_2689_, lean_object* v_toBind_2690_, lean_object* v_____x_2691_){
_start:
{
lean_object* v_fst_2692_; lean_object* v_snd_2693_; lean_object* v___f_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v_fst_2692_ = lean_ctor_get(v_____x_2691_, 0);
lean_inc(v_fst_2692_);
v_snd_2693_ = lean_ctor_get(v_____x_2691_, 1);
lean_inc(v_snd_2693_);
lean_dec_ref(v_____x_2691_);
v___f_2694_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2694_, 0, v_toPure_2688_);
lean_closure_set(v___f_2694_, 1, v_fst_2692_);
v___x_2695_ = lean_apply_1(v_set_2689_, v_snd_2693_);
v___x_2696_ = lean_apply_4(v_toBind_2690_, lean_box(0), lean_box(0), v___x_2695_, v___f_2694_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__2(lean_object* v_self_2697_, lean_object* v_inst_2698_, lean_object* v_toBind_2699_, lean_object* v___f_2700_, lean_object* v_____do__lift_2701_){
_start:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2702_ = lean_apply_1(v_self_2697_, v_____do__lift_2701_);
v___x_2703_ = lean_apply_2(v_inst_2698_, lean_box(0), v___x_2702_);
v___x_2704_ = lean_apply_4(v_toBind_2699_, lean_box(0), lean_box(0), v___x_2703_, v___f_2700_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg(lean_object* v_inst_2705_, lean_object* v_inst_2706_, lean_object* v_inst_2707_, lean_object* v_self_2708_){
_start:
{
lean_object* v_toApplicative_2709_; lean_object* v_toBind_2710_; lean_object* v_set_2711_; lean_object* v_modifyGet_2712_; lean_object* v_toPure_2713_; lean_object* v___f_2714_; lean_object* v___x_2715_; lean_object* v___f_2716_; lean_object* v___f_2717_; lean_object* v___x_2718_; 
v_toApplicative_2709_ = lean_ctor_get(v_inst_2705_, 0);
lean_inc_ref(v_toApplicative_2709_);
v_toBind_2710_ = lean_ctor_get(v_inst_2705_, 1);
lean_inc(v_toBind_2710_);
lean_dec_ref(v_inst_2705_);
v_set_2711_ = lean_ctor_get(v_inst_2706_, 1);
lean_inc(v_set_2711_);
v_modifyGet_2712_ = lean_ctor_get(v_inst_2706_, 2);
lean_inc(v_modifyGet_2712_);
lean_dec_ref(v_inst_2706_);
v_toPure_2713_ = lean_ctor_get(v_toApplicative_2709_, 1);
lean_inc(v_toPure_2713_);
lean_dec_ref(v_toApplicative_2709_);
v___f_2714_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_2715_ = lean_apply_2(v_modifyGet_2712_, lean_box(0), v___f_2714_);
lean_inc(v_toBind_2710_);
v___f_2716_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2716_, 0, v_toPure_2713_);
lean_closure_set(v___f_2716_, 1, v_set_2711_);
lean_closure_set(v___f_2716_, 2, v_toBind_2710_);
lean_inc(v_toBind_2710_);
v___f_2717_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2717_, 0, v_self_2708_);
lean_closure_set(v___f_2717_, 1, v_inst_2707_);
lean_closure_set(v___f_2717_, 2, v_toBind_2710_);
lean_closure_set(v___f_2717_, 3, v___f_2716_);
v___x_2718_ = lean_apply_4(v_toBind_2710_, lean_box(0), lean_box(0), v___x_2715_, v___f_2717_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun(lean_object* v_n_2719_, lean_object* v_m_2720_, lean_object* v_00_u03b1_2721_, lean_object* v_inst_2722_, lean_object* v_inst_2723_, lean_object* v_inst_2724_, lean_object* v_inst_2725_, lean_object* v_self_2726_){
_start:
{
lean_object* v_toApplicative_2727_; lean_object* v_toBind_2728_; lean_object* v_set_2729_; lean_object* v_modifyGet_2730_; lean_object* v_toPure_2731_; lean_object* v___f_2732_; lean_object* v___x_2733_; lean_object* v___f_2734_; lean_object* v___f_2735_; lean_object* v___x_2736_; 
v_toApplicative_2727_ = lean_ctor_get(v_inst_2722_, 0);
lean_inc_ref(v_toApplicative_2727_);
v_toBind_2728_ = lean_ctor_get(v_inst_2722_, 1);
lean_inc(v_toBind_2728_);
lean_dec_ref(v_inst_2722_);
v_set_2729_ = lean_ctor_get(v_inst_2723_, 1);
lean_inc(v_set_2729_);
v_modifyGet_2730_ = lean_ctor_get(v_inst_2723_, 2);
lean_inc(v_modifyGet_2730_);
lean_dec_ref(v_inst_2723_);
v_toPure_2731_ = lean_ctor_get(v_toApplicative_2727_, 1);
lean_inc(v_toPure_2731_);
lean_dec_ref(v_toApplicative_2727_);
v___f_2732_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_2733_ = lean_apply_2(v_modifyGet_2730_, lean_box(0), v___f_2732_);
lean_inc(v_toBind_2728_);
v___f_2734_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2734_, 0, v_toPure_2731_);
lean_closure_set(v___f_2734_, 1, v_set_2729_);
lean_closure_set(v___f_2734_, 2, v_toBind_2728_);
lean_inc(v_toBind_2728_);
v___f_2735_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2735_, 0, v_self_2726_);
lean_closure_set(v___f_2735_, 1, v_inst_2724_);
lean_closure_set(v___f_2735_, 2, v_toBind_2728_);
lean_closure_set(v___f_2735_, 3, v___f_2734_);
v___x_2736_ = lean_apply_4(v_toBind_2728_, lean_box(0), lean_box(0), v___x_2733_, v___f_2735_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___boxed(lean_object* v_n_2737_, lean_object* v_m_2738_, lean_object* v_00_u03b1_2739_, lean_object* v_inst_2740_, lean_object* v_inst_2741_, lean_object* v_inst_2742_, lean_object* v_inst_2743_, lean_object* v_self_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l_Lake_LogT_takeAndRun(v_n_2737_, v_m_2738_, v_00_u03b1_2739_, v_inst_2740_, v_inst_2741_, v_inst_2742_, v_inst_2743_, v_self_2744_);
lean_dec(v_inst_2743_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg___lam__2(lean_object* v_toPure_2746_, lean_object* v___x_2747_, lean_object* v_toBind_2748_, lean_object* v_inst_2749_, lean_object* v___f_2750_, lean_object* v_____x_2751_){
_start:
{
lean_object* v_fst_2752_; lean_object* v_snd_2753_; lean_object* v___f_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; uint8_t v___x_2757_; 
v_fst_2752_ = lean_ctor_get(v_____x_2751_, 0);
lean_inc(v_fst_2752_);
v_snd_2753_ = lean_ctor_get(v_____x_2751_, 1);
lean_inc(v_snd_2753_);
lean_dec_ref(v_____x_2751_);
lean_inc(v_toPure_2746_);
v___f_2754_ = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2754_, 0, v_toPure_2746_);
lean_closure_set(v___f_2754_, 1, v_fst_2752_);
v___x_2755_ = lean_array_get_size(v_snd_2753_);
v___x_2756_ = lean_box(0);
v___x_2757_ = lean_nat_dec_lt(v___x_2747_, v___x_2755_);
if (v___x_2757_ == 0)
{
lean_object* v___x_2758_; lean_object* v___x_2759_; 
lean_dec(v_snd_2753_);
lean_dec(v___f_2750_);
lean_dec_ref(v_inst_2749_);
v___x_2758_ = lean_apply_2(v_toPure_2746_, lean_box(0), v___x_2756_);
v___x_2759_ = lean_apply_4(v_toBind_2748_, lean_box(0), lean_box(0), v___x_2758_, v___f_2754_);
return v___x_2759_;
}
else
{
uint8_t v___x_2760_; 
v___x_2760_ = lean_nat_dec_le(v___x_2755_, v___x_2755_);
if (v___x_2760_ == 0)
{
if (v___x_2757_ == 0)
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
lean_dec(v_snd_2753_);
lean_dec(v___f_2750_);
lean_dec_ref(v_inst_2749_);
v___x_2761_ = lean_apply_2(v_toPure_2746_, lean_box(0), v___x_2756_);
v___x_2762_ = lean_apply_4(v_toBind_2748_, lean_box(0), lean_box(0), v___x_2761_, v___f_2754_);
return v___x_2762_;
}
else
{
size_t v___x_2763_; size_t v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
lean_dec(v_toPure_2746_);
v___x_2763_ = ((size_t)0ULL);
v___x_2764_ = lean_usize_of_nat(v___x_2755_);
v___x_2765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2749_, v___f_2750_, v_snd_2753_, v___x_2763_, v___x_2764_, v___x_2756_);
v___x_2766_ = lean_apply_4(v_toBind_2748_, lean_box(0), lean_box(0), v___x_2765_, v___f_2754_);
return v___x_2766_;
}
}
else
{
size_t v___x_2767_; size_t v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
lean_dec(v_toPure_2746_);
v___x_2767_ = ((size_t)0ULL);
v___x_2768_ = lean_usize_of_nat(v___x_2755_);
v___x_2769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2749_, v___f_2750_, v_snd_2753_, v___x_2767_, v___x_2768_, v___x_2756_);
v___x_2770_ = lean_apply_4(v_toBind_2748_, lean_box(0), lean_box(0), v___x_2769_, v___f_2754_);
return v___x_2770_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg___lam__2___boxed(lean_object* v_toPure_2771_, lean_object* v___x_2772_, lean_object* v_toBind_2773_, lean_object* v_inst_2774_, lean_object* v___f_2775_, lean_object* v_____x_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_Lake_LogT_replayLog___redArg___lam__2(v_toPure_2771_, v___x_2772_, v_toBind_2773_, v_inst_2774_, v___f_2775_, v_____x_2776_);
lean_dec(v___x_2772_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg(lean_object* v_inst_2778_, lean_object* v_logger_2779_, lean_object* v_inst_2780_, lean_object* v_self_2781_){
_start:
{
lean_object* v_toApplicative_2782_; lean_object* v_toBind_2783_; lean_object* v_toPure_2784_; lean_object* v___f_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___f_2790_; lean_object* v___x_2791_; 
v_toApplicative_2782_ = lean_ctor_get(v_inst_2778_, 0);
v_toBind_2783_ = lean_ctor_get(v_inst_2778_, 1);
lean_inc(v_toBind_2783_);
v_toPure_2784_ = lean_ctor_get(v_toApplicative_2782_, 1);
lean_inc(v_toPure_2784_);
v___f_2785_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2785_, 0, v_logger_2779_);
v___x_2786_ = lean_unsigned_to_nat(0u);
v___x_2787_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_2788_ = lean_apply_1(v_self_2781_, v___x_2787_);
v___x_2789_ = lean_apply_2(v_inst_2780_, lean_box(0), v___x_2788_);
lean_inc(v_toBind_2783_);
v___f_2790_ = lean_alloc_closure((void*)(l_Lake_LogT_replayLog___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_2790_, 0, v_toPure_2784_);
lean_closure_set(v___f_2790_, 1, v___x_2786_);
lean_closure_set(v___f_2790_, 2, v_toBind_2783_);
lean_closure_set(v___f_2790_, 3, v_inst_2778_);
lean_closure_set(v___f_2790_, 4, v___f_2785_);
v___x_2791_ = lean_apply_4(v_toBind_2783_, lean_box(0), lean_box(0), v___x_2789_, v___f_2790_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog(lean_object* v_n_2792_, lean_object* v_m_2793_, lean_object* v_00_u03b1_2794_, lean_object* v_inst_2795_, lean_object* v_logger_2796_, lean_object* v_inst_2797_, lean_object* v_self_2798_){
_start:
{
lean_object* v_toApplicative_2799_; lean_object* v_toBind_2800_; lean_object* v_toPure_2801_; lean_object* v___f_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___f_2807_; lean_object* v___x_2808_; 
v_toApplicative_2799_ = lean_ctor_get(v_inst_2795_, 0);
v_toBind_2800_ = lean_ctor_get(v_inst_2795_, 1);
lean_inc(v_toBind_2800_);
v_toPure_2801_ = lean_ctor_get(v_toApplicative_2799_, 1);
lean_inc(v_toPure_2801_);
v___f_2802_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2802_, 0, v_logger_2796_);
v___x_2803_ = lean_unsigned_to_nat(0u);
v___x_2804_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_2805_ = lean_apply_1(v_self_2798_, v___x_2804_);
v___x_2806_ = lean_apply_2(v_inst_2797_, lean_box(0), v___x_2805_);
lean_inc(v_toBind_2800_);
v___f_2807_ = lean_alloc_closure((void*)(l_Lake_LogT_replayLog___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_2807_, 0, v_toPure_2801_);
lean_closure_set(v___f_2807_, 1, v___x_2803_);
lean_closure_set(v___f_2807_, 2, v_toBind_2800_);
lean_closure_set(v___f_2807_, 3, v_inst_2795_);
lean_closure_set(v___f_2807_, 4, v___f_2802_);
v___x_2808_ = lean_apply_4(v_toBind_2800_, lean_box(0), lean_box(0), v___x_2806_, v___f_2807_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogELogTOfMonad___redArg(lean_object* v_inst_2809_){
_start:
{
lean_object* v_toApplicative_2810_; lean_object* v_toPure_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v_toApplicative_2810_ = lean_ctor_get(v_inst_2809_, 0);
lean_inc_ref(v_toApplicative_2810_);
lean_dec_ref(v_inst_2809_);
v_toPure_2811_ = lean_ctor_get(v_toApplicative_2810_, 1);
lean_inc(v_toPure_2811_);
lean_dec_ref(v_toApplicative_2810_);
v___x_2812_ = l_Lake_EStateT_instMonadStateOfOfPure___redArg(v_toPure_2811_);
v___x_2813_ = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(v___x_2813_, 0, lean_box(0));
lean_closure_set(v___x_2813_, 1, v___x_2812_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogELogTOfMonad(lean_object* v_m_2814_, lean_object* v_inst_2815_){
_start:
{
lean_object* v___x_2816_; 
v___x_2816_ = l_Lake_instMonadLogELogTOfMonad___redArg(v_inst_2815_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__0(lean_object* v_x_2817_){
_start:
{
if (lean_obj_tag(v_x_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2827_; 
v_a_2818_ = lean_ctor_get(v_x_2817_, 0);
v_a_2819_ = lean_ctor_get(v_x_2817_, 1);
v_isSharedCheck_2827_ = !lean_is_exclusive(v_x_2817_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2821_ = v_x_2817_;
v_isShared_2822_ = v_isSharedCheck_2827_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_inc(v_a_2818_);
lean_dec(v_x_2817_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2827_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2823_; lean_object* v___x_2825_; 
v___x_2823_ = lean_array_get_size(v_a_2818_);
lean_dec(v_a_2818_);
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 0, v___x_2823_);
v___x_2825_ = v___x_2821_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2823_);
lean_ctor_set(v_reuseFailAlloc_2826_, 1, v_a_2819_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2836_; 
v_a_2828_ = lean_ctor_get(v_x_2817_, 0);
v_a_2829_ = lean_ctor_get(v_x_2817_, 1);
v_isSharedCheck_2836_ = !lean_is_exclusive(v_x_2817_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2831_ = v_x_2817_;
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_inc(v_a_2828_);
lean_dec(v_x_2817_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2834_; 
if (v_isShared_2832_ == 0)
{
v___x_2834_ = v___x_2831_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2828_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v_a_2829_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__1(lean_object* v_a_2837_, lean_object* v_toPure_2838_, lean_object* v_____do__lift_2839_){
_start:
{
if (lean_obj_tag(v_____do__lift_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2848_; 
v_a_2840_ = lean_ctor_get(v_____do__lift_2839_, 1);
v_isSharedCheck_2848_ = !lean_is_exclusive(v_____do__lift_2839_);
if (v_isSharedCheck_2848_ == 0)
{
lean_object* v_unused_2849_; 
v_unused_2849_ = lean_ctor_get(v_____do__lift_2839_, 0);
lean_dec(v_unused_2849_);
v___x_2842_ = v_____do__lift_2839_;
v_isShared_2843_ = v_isSharedCheck_2848_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v_____do__lift_2839_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2848_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
lean_ctor_set_tag(v___x_2842_, 1);
lean_ctor_set(v___x_2842_, 0, v_a_2837_);
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2837_);
lean_ctor_set(v_reuseFailAlloc_2847_, 1, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
lean_object* v___x_2846_; 
v___x_2846_ = lean_apply_2(v_toPure_2838_, lean_box(0), v___x_2845_);
return v___x_2846_;
}
}
}
else
{
lean_object* v_a_2850_; lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2859_; 
lean_dec(v_a_2837_);
v_a_2850_ = lean_ctor_get(v_____do__lift_2839_, 0);
v_a_2851_ = lean_ctor_get(v_____do__lift_2839_, 1);
v_isSharedCheck_2859_ = !lean_is_exclusive(v_____do__lift_2839_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2853_ = v_____do__lift_2839_;
v_isShared_2854_ = v_isSharedCheck_2859_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_inc(v_a_2850_);
lean_dec(v_____do__lift_2839_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2859_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2850_);
lean_ctor_set(v_reuseFailAlloc_2858_, 1, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
lean_object* v___x_2857_; 
v___x_2857_ = lean_apply_2(v_toPure_2838_, lean_box(0), v___x_2856_);
return v___x_2857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__2(lean_object* v_toPure_2860_, lean_object* v___x_2861_, lean_object* v_____do__lift_2862_){
_start:
{
if (lean_obj_tag(v_____do__lift_2862_) == 0)
{
lean_object* v___x_2863_; 
v___x_2863_ = lean_apply_2(v_toPure_2860_, lean_box(0), v_____do__lift_2862_);
return v___x_2863_;
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2872_; 
v_a_2864_ = lean_ctor_get(v_____do__lift_2862_, 1);
v_isSharedCheck_2872_ = !lean_is_exclusive(v_____do__lift_2862_);
if (v_isSharedCheck_2872_ == 0)
{
lean_object* v_unused_2873_; 
v_unused_2873_ = lean_ctor_get(v_____do__lift_2862_, 0);
lean_dec(v_unused_2873_);
v___x_2866_ = v_____do__lift_2862_;
v_isShared_2867_ = v_isSharedCheck_2872_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v_____do__lift_2862_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2872_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
lean_ctor_set_tag(v___x_2866_, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2861_);
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2861_);
lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
lean_object* v___x_2870_; 
v___x_2870_ = lean_apply_2(v_toPure_2860_, lean_box(0), v___x_2869_);
return v___x_2870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__3(lean_object* v_toPure_2874_, lean_object* v___x_2875_, lean_object* v_toBind_2876_, lean_object* v_____do__lift_2877_){
_start:
{
if (lean_obj_tag(v_____do__lift_2877_) == 0)
{
lean_object* v_a_2878_; lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2893_; 
v_a_2878_ = lean_ctor_get(v_____do__lift_2877_, 0);
v_a_2879_ = lean_ctor_get(v_____do__lift_2877_, 1);
v_isSharedCheck_2893_ = !lean_is_exclusive(v_____do__lift_2877_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2881_ = v_____do__lift_2877_;
v_isShared_2882_ = v_isSharedCheck_2893_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_inc(v_a_2878_);
lean_dec(v_____do__lift_2877_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2893_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___f_2883_; lean_object* v___x_2884_; lean_object* v___f_2885_; lean_object* v___x_2886_; lean_object* v___x_2888_; 
lean_inc(v_toPure_2874_);
v___f_2883_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2883_, 0, v_a_2878_);
lean_closure_set(v___f_2883_, 1, v_toPure_2874_);
v___x_2884_ = lean_box(0);
lean_inc(v_toPure_2874_);
v___f_2885_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2885_, 0, v_toPure_2874_);
lean_closure_set(v___f_2885_, 1, v___x_2884_);
v___x_2886_ = lean_array_push(v_a_2879_, v___x_2875_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 1, v___x_2886_);
lean_ctor_set(v___x_2881_, 0, v___x_2884_);
v___x_2888_ = v___x_2881_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v___x_2884_);
lean_ctor_set(v_reuseFailAlloc_2892_, 1, v___x_2886_);
v___x_2888_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2889_ = lean_apply_2(v_toPure_2874_, lean_box(0), v___x_2888_);
lean_inc(v_toBind_2876_);
v___x_2890_ = lean_apply_4(v_toBind_2876_, lean_box(0), lean_box(0), v___x_2889_, v___f_2885_);
v___x_2891_ = lean_apply_4(v_toBind_2876_, lean_box(0), lean_box(0), v___x_2890_, v___f_2883_);
return v___x_2891_;
}
}
}
else
{
lean_object* v_a_2894_; lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2903_; 
lean_dec(v_toBind_2876_);
lean_dec_ref(v___x_2875_);
v_a_2894_ = lean_ctor_get(v_____do__lift_2877_, 0);
v_a_2895_ = lean_ctor_get(v_____do__lift_2877_, 1);
v_isSharedCheck_2903_ = !lean_is_exclusive(v_____do__lift_2877_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2897_ = v_____do__lift_2877_;
v_isShared_2898_ = v_isSharedCheck_2903_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_inc(v_a_2894_);
lean_dec(v_____do__lift_2877_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2903_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2894_);
lean_ctor_set(v_reuseFailAlloc_2902_, 1, v_a_2895_);
v___x_2900_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
lean_object* v___x_2901_; 
v___x_2901_ = lean_apply_2(v_toPure_2874_, lean_box(0), v___x_2900_);
return v___x_2901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__4(lean_object* v_toFunctor_2904_, lean_object* v_toPure_2905_, lean_object* v_toBind_2906_, lean_object* v___f_2907_, lean_object* v_00_u03b1_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
lean_object* v_map_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2924_; 
v_map_2911_ = lean_ctor_get(v_toFunctor_2904_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v_toFunctor_2904_);
if (v_isSharedCheck_2924_ == 0)
{
lean_object* v_unused_2925_; 
v_unused_2925_ = lean_ctor_get(v_toFunctor_2904_, 1);
lean_dec(v_unused_2925_);
v___x_2913_ = v_toFunctor_2904_;
v_isShared_2914_ = v_isSharedCheck_2924_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_map_2911_);
lean_dec(v_toFunctor_2904_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2924_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
uint8_t v___x_2915_; lean_object* v___x_2916_; lean_object* v___f_2917_; lean_object* v___x_2919_; 
v___x_2915_ = 3;
v___x_2916_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2916_, 0, v___y_2909_);
lean_ctor_set_uint8(v___x_2916_, sizeof(void*)*1, v___x_2915_);
lean_inc(v_toBind_2906_);
lean_inc(v_toPure_2905_);
v___f_2917_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__3), 4, 3);
lean_closure_set(v___f_2917_, 0, v_toPure_2905_);
lean_closure_set(v___f_2917_, 1, v___x_2916_);
lean_closure_set(v___f_2917_, 2, v_toBind_2906_);
lean_inc_ref(v___y_2910_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 1, v___y_2910_);
lean_ctor_set(v___x_2913_, 0, v___y_2910_);
v___x_2919_ = v___x_2913_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v___y_2910_);
lean_ctor_set(v_reuseFailAlloc_2923_, 1, v___y_2910_);
v___x_2919_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2920_ = lean_apply_2(v_toPure_2905_, lean_box(0), v___x_2919_);
v___x_2921_ = lean_apply_4(v_map_2911_, lean_box(0), lean_box(0), v___f_2907_, v___x_2920_);
v___x_2922_ = lean_apply_4(v_toBind_2906_, lean_box(0), lean_box(0), v___x_2921_, v___f_2917_);
return v___x_2922_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg(lean_object* v_inst_2927_){
_start:
{
lean_object* v_toApplicative_2928_; lean_object* v_toBind_2929_; lean_object* v_toFunctor_2930_; lean_object* v_toPure_2931_; lean_object* v___f_2932_; lean_object* v___f_2933_; 
v_toApplicative_2928_ = lean_ctor_get(v_inst_2927_, 0);
lean_inc_ref(v_toApplicative_2928_);
v_toBind_2929_ = lean_ctor_get(v_inst_2927_, 1);
lean_inc(v_toBind_2929_);
lean_dec_ref(v_inst_2927_);
v_toFunctor_2930_ = lean_ctor_get(v_toApplicative_2928_, 0);
lean_inc_ref(v_toFunctor_2930_);
v_toPure_2931_ = lean_ctor_get(v_toApplicative_2928_, 1);
lean_inc(v_toPure_2931_);
lean_dec_ref(v_toApplicative_2928_);
v___f_2932_ = ((lean_object*)(l_Lake_instMonadErrorELogTOfMonad___redArg___closed__0));
v___f_2933_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__4), 7, 4);
lean_closure_set(v___f_2933_, 0, v_toFunctor_2930_);
lean_closure_set(v___f_2933_, 1, v_toPure_2931_);
lean_closure_set(v___f_2933_, 2, v_toBind_2929_);
lean_closure_set(v___f_2933_, 3, v___f_2932_);
return v___f_2933_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad(lean_object* v_m_2934_, lean_object* v_inst_2935_){
_start:
{
lean_object* v___x_2936_; 
v___x_2936_ = l_Lake_instMonadErrorELogTOfMonad___redArg(v_inst_2935_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__1(lean_object* v___y_2937_, lean_object* v___x_2938_, lean_object* v_toPure_2939_, lean_object* v_____do__lift_2940_){
_start:
{
if (lean_obj_tag(v_____do__lift_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2942_; 
lean_dec(v_toPure_2939_);
v_a_2941_ = lean_ctor_get(v_____do__lift_2940_, 1);
lean_inc(v_a_2941_);
lean_dec_ref(v_____do__lift_2940_);
v___x_2942_ = lean_apply_2(v___y_2937_, v___x_2938_, v_a_2941_);
return v___x_2942_;
}
else
{
lean_object* v_a_2943_; lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2952_; 
lean_dec(v___y_2937_);
v_a_2943_ = lean_ctor_get(v_____do__lift_2940_, 0);
v_a_2944_ = lean_ctor_get(v_____do__lift_2940_, 1);
v_isSharedCheck_2952_ = !lean_is_exclusive(v_____do__lift_2940_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2946_ = v_____do__lift_2940_;
v_isShared_2947_ = v_isSharedCheck_2952_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_inc(v_a_2943_);
lean_dec(v_____do__lift_2940_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2952_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2949_; 
if (v_isShared_2947_ == 0)
{
v___x_2949_ = v___x_2946_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2943_);
lean_ctor_set(v_reuseFailAlloc_2951_, 1, v_a_2944_);
v___x_2949_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
lean_object* v___x_2950_; 
v___x_2950_ = lean_apply_2(v_toPure_2939_, lean_box(0), v___x_2949_);
return v___x_2950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__0(lean_object* v_toPure_2953_, lean_object* v___y_2954_, lean_object* v_toBind_2955_, lean_object* v_____do__lift_2956_){
_start:
{
if (lean_obj_tag(v_____do__lift_2956_) == 0)
{
lean_object* v___x_2957_; 
lean_dec(v_toBind_2955_);
lean_dec(v___y_2954_);
v___x_2957_ = lean_apply_2(v_toPure_2953_, lean_box(0), v_____do__lift_2956_);
return v___x_2957_;
}
else
{
lean_object* v_a_2958_; lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2971_; 
v_a_2958_ = lean_ctor_get(v_____do__lift_2956_, 0);
v_a_2959_ = lean_ctor_get(v_____do__lift_2956_, 1);
v_isSharedCheck_2971_ = !lean_is_exclusive(v_____do__lift_2956_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2961_ = v_____do__lift_2956_;
v_isShared_2962_ = v_isSharedCheck_2971_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_inc(v_a_2958_);
lean_dec(v_____do__lift_2956_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2971_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2963_; lean_object* v___f_2964_; lean_object* v___x_2965_; lean_object* v___x_2967_; 
v___x_2963_ = lean_box(0);
lean_inc(v_toPure_2953_);
v___f_2964_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2964_, 0, v___y_2954_);
lean_closure_set(v___f_2964_, 1, v___x_2963_);
lean_closure_set(v___f_2964_, 2, v_toPure_2953_);
v___x_2965_ = l_Array_shrink___redArg(v_a_2959_, v_a_2958_);
lean_dec(v_a_2958_);
if (v_isShared_2962_ == 0)
{
lean_ctor_set_tag(v___x_2961_, 0);
lean_ctor_set(v___x_2961_, 1, v___x_2965_);
lean_ctor_set(v___x_2961_, 0, v___x_2963_);
v___x_2967_ = v___x_2961_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2963_);
lean_ctor_set(v_reuseFailAlloc_2970_, 1, v___x_2965_);
v___x_2967_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2968_ = lean_apply_2(v_toPure_2953_, lean_box(0), v___x_2967_);
v___x_2969_ = lean_apply_4(v_toBind_2955_, lean_box(0), lean_box(0), v___x_2968_, v___f_2964_);
return v___x_2969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__2(lean_object* v_toPure_2972_, lean_object* v_toBind_2973_, lean_object* v_00_u03b1_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
lean_object* v___f_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
lean_inc(v_toBind_2973_);
v___f_2978_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2978_, 0, v_toPure_2972_);
lean_closure_set(v___f_2978_, 1, v___y_2976_);
lean_closure_set(v___f_2978_, 2, v_toBind_2973_);
v___x_2979_ = lean_apply_1(v___y_2975_, v___y_2977_);
v___x_2980_ = lean_apply_4(v_toBind_2973_, lean_box(0), lean_box(0), v___x_2979_, v___f_2978_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__3(lean_object* v_toPure_2981_, lean_object* v_____do__lift_2982_){
_start:
{
if (lean_obj_tag(v_____do__lift_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2992_; 
v_a_2983_ = lean_ctor_get(v_____do__lift_2982_, 0);
v_a_2984_ = lean_ctor_get(v_____do__lift_2982_, 1);
v_isSharedCheck_2992_ = !lean_is_exclusive(v_____do__lift_2982_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2986_ = v_____do__lift_2982_;
v_isShared_2987_ = v_isSharedCheck_2992_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_inc(v_a_2983_);
lean_dec(v_____do__lift_2982_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2992_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
lean_ctor_set_tag(v___x_2986_, 1);
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_a_2983_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v_a_2984_);
v___x_2989_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
lean_object* v___x_2990_; 
v___x_2990_ = lean_apply_2(v_toPure_2981_, lean_box(0), v___x_2989_);
return v___x_2990_;
}
}
}
else
{
lean_object* v_a_2993_; lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3002_; 
v_a_2993_ = lean_ctor_get(v_____do__lift_2982_, 0);
v_a_2994_ = lean_ctor_get(v_____do__lift_2982_, 1);
v_isSharedCheck_3002_ = !lean_is_exclusive(v_____do__lift_2982_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2996_ = v_____do__lift_2982_;
v_isShared_2997_ = v_isSharedCheck_3002_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_inc(v_a_2993_);
lean_dec(v_____do__lift_2982_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3002_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2993_);
lean_ctor_set(v_reuseFailAlloc_3001_, 1, v_a_2994_);
v___x_2999_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
lean_object* v___x_3000_; 
v___x_3000_ = lean_apply_2(v_toPure_2981_, lean_box(0), v___x_2999_);
return v___x_3000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__4(lean_object* v_toFunctor_3003_, lean_object* v_toPure_3004_, lean_object* v___f_3005_, lean_object* v_toBind_3006_, lean_object* v___f_3007_, lean_object* v_00_u03b1_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v_map_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3020_; 
v_map_3010_ = lean_ctor_get(v_toFunctor_3003_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v_toFunctor_3003_);
if (v_isSharedCheck_3020_ == 0)
{
lean_object* v_unused_3021_; 
v_unused_3021_ = lean_ctor_get(v_toFunctor_3003_, 1);
lean_dec(v_unused_3021_);
v___x_3012_ = v_toFunctor_3003_;
v_isShared_3013_ = v_isSharedCheck_3020_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_map_3010_);
lean_dec(v_toFunctor_3003_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3020_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
lean_inc_ref(v___y_3009_);
if (v_isShared_3013_ == 0)
{
lean_ctor_set(v___x_3012_, 1, v___y_3009_);
lean_ctor_set(v___x_3012_, 0, v___y_3009_);
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___y_3009_);
lean_ctor_set(v_reuseFailAlloc_3019_, 1, v___y_3009_);
v___x_3015_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3016_ = lean_apply_2(v_toPure_3004_, lean_box(0), v___x_3015_);
v___x_3017_ = lean_apply_4(v_map_3010_, lean_box(0), lean_box(0), v___f_3005_, v___x_3016_);
v___x_3018_ = lean_apply_4(v_toBind_3006_, lean_box(0), lean_box(0), v___x_3017_, v___f_3007_);
return v___x_3018_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg(lean_object* v_inst_3022_){
_start:
{
lean_object* v_toApplicative_3023_; lean_object* v_toBind_3024_; lean_object* v_toFunctor_3025_; lean_object* v_toPure_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3044_; 
v_toApplicative_3023_ = lean_ctor_get(v_inst_3022_, 0);
lean_inc_ref(v_toApplicative_3023_);
v_toBind_3024_ = lean_ctor_get(v_inst_3022_, 1);
lean_inc(v_toBind_3024_);
lean_dec_ref(v_inst_3022_);
v_toFunctor_3025_ = lean_ctor_get(v_toApplicative_3023_, 0);
v_toPure_3026_ = lean_ctor_get(v_toApplicative_3023_, 1);
v_isSharedCheck_3044_ = !lean_is_exclusive(v_toApplicative_3023_);
if (v_isSharedCheck_3044_ == 0)
{
lean_object* v_unused_3045_; lean_object* v_unused_3046_; lean_object* v_unused_3047_; 
v_unused_3045_ = lean_ctor_get(v_toApplicative_3023_, 4);
lean_dec(v_unused_3045_);
v_unused_3046_ = lean_ctor_get(v_toApplicative_3023_, 3);
lean_dec(v_unused_3046_);
v_unused_3047_ = lean_ctor_get(v_toApplicative_3023_, 2);
lean_dec(v_unused_3047_);
v___x_3028_ = v_toApplicative_3023_;
v_isShared_3029_ = v_isSharedCheck_3044_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_toPure_3026_);
lean_inc(v_toFunctor_3025_);
lean_dec(v_toApplicative_3023_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3044_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___f_3030_; lean_object* v___f_3031_; lean_object* v___f_3032_; lean_object* v___f_3033_; lean_object* v___f_3034_; lean_object* v___f_3035_; lean_object* v___f_3036_; lean_object* v___f_3037_; lean_object* v___x_3038_; lean_object* v___f_3039_; lean_object* v___x_3041_; 
v___f_3030_ = ((lean_object*)(l_Lake_instMonadErrorELogTOfMonad___redArg___closed__0));
lean_inc(v_toBind_3024_);
lean_inc(v_toPure_3026_);
v___f_3031_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__2), 6, 2);
lean_closure_set(v___f_3031_, 0, v_toPure_3026_);
lean_closure_set(v___f_3031_, 1, v_toBind_3024_);
lean_inc(v_toPure_3026_);
v___f_3032_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3032_, 0, v_toPure_3026_);
lean_inc(v_toBind_3024_);
lean_inc(v_toPure_3026_);
lean_inc_ref(v_toFunctor_3025_);
v___f_3033_ = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__4), 7, 5);
lean_closure_set(v___f_3033_, 0, v_toFunctor_3025_);
lean_closure_set(v___f_3033_, 1, v_toPure_3026_);
lean_closure_set(v___f_3033_, 2, v___f_3030_);
lean_closure_set(v___f_3033_, 3, v_toBind_3024_);
lean_closure_set(v___f_3033_, 4, v___f_3032_);
lean_inc(v_toBind_3024_);
lean_inc(v_toPure_3026_);
v___f_3034_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_3034_, 0, v_toPure_3026_);
lean_closure_set(v___f_3034_, 1, v_toBind_3024_);
lean_inc(v_toBind_3024_);
lean_inc(v_toPure_3026_);
v___f_3035_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_3035_, 0, v_toPure_3026_);
lean_closure_set(v___f_3035_, 1, v_toBind_3024_);
lean_inc(v_toPure_3026_);
v___f_3036_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_3036_, 0, v_toPure_3026_);
lean_closure_set(v___f_3036_, 1, v___f_3034_);
lean_inc(v_toPure_3026_);
lean_inc_ref(v_toFunctor_3025_);
v___f_3037_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_3037_, 0, v_toFunctor_3025_);
lean_closure_set(v___f_3037_, 1, v_toPure_3026_);
lean_closure_set(v___f_3037_, 2, v_toBind_3024_);
v___x_3038_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_3025_);
v___f_3039_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3039_, 0, v_toPure_3026_);
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 4, v___f_3035_);
lean_ctor_set(v___x_3028_, 3, v___f_3036_);
lean_ctor_set(v___x_3028_, 2, v___f_3037_);
lean_ctor_set(v___x_3028_, 1, v___f_3039_);
lean_ctor_set(v___x_3028_, 0, v___x_3038_);
v___x_3041_ = v___x_3028_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v___x_3038_);
lean_ctor_set(v_reuseFailAlloc_3043_, 1, v___f_3039_);
lean_ctor_set(v_reuseFailAlloc_3043_, 2, v___f_3037_);
lean_ctor_set(v_reuseFailAlloc_3043_, 3, v___f_3036_);
lean_ctor_set(v_reuseFailAlloc_3043_, 4, v___f_3035_);
v___x_3041_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
lean_object* v___x_3042_; 
v___x_3042_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3041_);
lean_ctor_set(v___x_3042_, 1, v___f_3033_);
lean_ctor_set(v___x_3042_, 2, v___f_3031_);
return v___x_3042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad(lean_object* v_m_3048_, lean_object* v_inst_3049_){
_start:
{
lean_object* v___x_3050_; 
v___x_3050_ = l_Lake_instAlternativeELogTOfMonad___redArg(v_inst_3049_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run___redArg(lean_object* v_self_3051_, lean_object* v_log_3052_){
_start:
{
lean_object* v___x_3053_; 
v___x_3053_ = lean_apply_1(v_self_3051_, v_log_3052_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run(lean_object* v_m_3054_, lean_object* v_00_u03b1_3055_, lean_object* v_self_3056_, lean_object* v_log_3057_){
_start:
{
lean_object* v___x_3058_; 
v___x_3058_ = lean_apply_1(v_self_3056_, v_log_3057_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x27___redArg(lean_object* v_inst_3060_, lean_object* v_self_3061_, lean_object* v_log_3062_){
_start:
{
lean_object* v_map_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v_map_3063_ = lean_ctor_get(v_inst_3060_, 0);
lean_inc(v_map_3063_);
lean_dec_ref(v_inst_3060_);
v___x_3064_ = ((lean_object*)(l_Lake_ELogT_run_x27___redArg___closed__0));
v___x_3065_ = lean_apply_1(v_self_3061_, v_log_3062_);
v___x_3066_ = lean_apply_4(v_map_3063_, lean_box(0), lean_box(0), v___x_3064_, v___x_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x27(lean_object* v_m_3067_, lean_object* v_00_u03b1_3068_, lean_object* v_inst_3069_, lean_object* v_self_3070_, lean_object* v_log_3071_){
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
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT___redArg(lean_object* v_inst_3077_, lean_object* v_self_3078_, lean_object* v_a_3079_){
_start:
{
lean_object* v_map_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v_map_3080_ = lean_ctor_get(v_inst_3077_, 0);
lean_inc(v_map_3080_);
lean_dec_ref(v_inst_3077_);
v___x_3081_ = ((lean_object*)(l_Lake_ELogT_toLogT___redArg___closed__0));
v___x_3082_ = lean_apply_1(v_self_3078_, v_a_3079_);
v___x_3083_ = lean_apply_4(v_map_3080_, lean_box(0), lean_box(0), v___x_3081_, v___x_3082_);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT(lean_object* v_m_3084_, lean_object* v_00_u03b1_3085_, lean_object* v_inst_3086_, lean_object* v_self_3087_, lean_object* v_a_3088_){
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
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT_x3f___redArg(lean_object* v_inst_3094_, lean_object* v_self_3095_, lean_object* v_a_3096_){
_start:
{
lean_object* v_map_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v_map_3097_ = lean_ctor_get(v_inst_3094_, 0);
lean_inc(v_map_3097_);
lean_dec_ref(v_inst_3094_);
v___x_3098_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3099_ = lean_apply_1(v_self_3095_, v_a_3096_);
v___x_3100_ = lean_apply_4(v_map_3097_, lean_box(0), lean_box(0), v___x_3098_, v___x_3099_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT_x3f(lean_object* v_m_3101_, lean_object* v_00_u03b1_3102_, lean_object* v_inst_3103_, lean_object* v_self_3104_, lean_object* v_a_3105_){
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
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f___redArg(lean_object* v_inst_3110_, lean_object* v_self_3111_, lean_object* v_log_3112_){
_start:
{
lean_object* v_map_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v_map_3113_ = lean_ctor_get(v_inst_3110_, 0);
lean_inc(v_map_3113_);
lean_dec_ref(v_inst_3110_);
v___x_3114_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3115_ = lean_apply_1(v_self_3111_, v_log_3112_);
v___x_3116_ = lean_apply_4(v_map_3113_, lean_box(0), lean_box(0), v___x_3114_, v___x_3115_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f(lean_object* v_m_3117_, lean_object* v_00_u03b1_3118_, lean_object* v_inst_3119_, lean_object* v_self_3120_, lean_object* v_log_3121_){
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
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f_x27___redArg(lean_object* v_inst_3127_, lean_object* v_self_3128_, lean_object* v_log_3129_){
_start:
{
lean_object* v_map_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v_map_3130_ = lean_ctor_get(v_inst_3127_, 0);
lean_inc(v_map_3130_);
lean_dec_ref(v_inst_3127_);
v___x_3131_ = ((lean_object*)(l_Lake_ELogT_run_x3f_x27___redArg___closed__0));
v___x_3132_ = lean_apply_1(v_self_3128_, v_log_3129_);
v___x_3133_ = lean_apply_4(v_map_3130_, lean_box(0), lean_box(0), v___x_3131_, v___x_3132_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f_x27(lean_object* v_m_3134_, lean_object* v_00_u03b1_3135_, lean_object* v_inst_3136_, lean_object* v_self_3137_, lean_object* v_log_3138_){
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
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg___lam__0(lean_object* v_f_3143_, lean_object* v_____x_3144_){
_start:
{
lean_object* v_fst_3145_; lean_object* v_snd_3146_; lean_object* v___x_3147_; 
v_fst_3145_ = lean_ctor_get(v_____x_3144_, 0);
lean_inc(v_fst_3145_);
v_snd_3146_ = lean_ctor_get(v_____x_3144_, 1);
lean_inc(v_snd_3146_);
lean_dec_ref(v_____x_3144_);
v___x_3147_ = lean_apply_2(v_f_3143_, v_fst_3145_, v_snd_3146_);
return v___x_3147_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg___lam__1(lean_object* v_toPure_3148_, lean_object* v_toBind_3149_, lean_object* v___f_3150_, lean_object* v_____do__lift_3151_){
_start:
{
if (lean_obj_tag(v_____do__lift_3151_) == 0)
{
lean_object* v_a_3152_; lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3161_; 
lean_dec(v___f_3150_);
lean_dec(v_toBind_3149_);
v_a_3152_ = lean_ctor_get(v_____do__lift_3151_, 0);
v_a_3153_ = lean_ctor_get(v_____do__lift_3151_, 1);
v_isSharedCheck_3161_ = !lean_is_exclusive(v_____do__lift_3151_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3155_ = v_____do__lift_3151_;
v_isShared_3156_ = v_isSharedCheck_3161_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_inc(v_a_3152_);
lean_dec(v_____do__lift_3151_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3161_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3152_);
lean_ctor_set(v_reuseFailAlloc_3160_, 1, v_a_3153_);
v___x_3158_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
lean_object* v___x_3159_; 
v___x_3159_ = lean_apply_2(v_toPure_3148_, lean_box(0), v___x_3158_);
return v___x_3159_;
}
}
}
else
{
lean_object* v_a_3162_; lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3175_; 
v_a_3162_ = lean_ctor_get(v_____do__lift_3151_, 0);
v_a_3163_ = lean_ctor_get(v_____do__lift_3151_, 1);
v_isSharedCheck_3175_ = !lean_is_exclusive(v_____do__lift_3151_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3165_ = v_____do__lift_3151_;
v_isShared_3166_ = v_isSharedCheck_3175_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_inc(v_a_3162_);
lean_dec(v_____do__lift_3151_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3175_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3171_; 
v___x_3167_ = lean_array_get_size(v_a_3163_);
lean_inc(v_a_3162_);
v___x_3168_ = l_Array_extract___redArg(v_a_3163_, v_a_3162_, v___x_3167_);
v___x_3169_ = l_Array_shrink___redArg(v_a_3163_, v_a_3162_);
lean_dec(v_a_3162_);
if (v_isShared_3166_ == 0)
{
lean_ctor_set_tag(v___x_3165_, 0);
lean_ctor_set(v___x_3165_, 1, v___x_3169_);
lean_ctor_set(v___x_3165_, 0, v___x_3168_);
v___x_3171_ = v___x_3165_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v___x_3168_);
lean_ctor_set(v_reuseFailAlloc_3174_, 1, v___x_3169_);
v___x_3171_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3172_ = lean_apply_2(v_toPure_3148_, lean_box(0), v___x_3171_);
v___x_3173_ = lean_apply_4(v_toBind_3149_, lean_box(0), lean_box(0), v___x_3172_, v___f_3150_);
return v___x_3173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg(lean_object* v_inst_3176_, lean_object* v_f_3177_, lean_object* v_self_3178_, lean_object* v_a_3179_){
_start:
{
lean_object* v_toApplicative_3180_; lean_object* v_toBind_3181_; lean_object* v_toPure_3182_; lean_object* v___f_3183_; lean_object* v___x_3184_; lean_object* v___f_3185_; lean_object* v___x_3186_; 
v_toApplicative_3180_ = lean_ctor_get(v_inst_3176_, 0);
lean_inc_ref(v_toApplicative_3180_);
v_toBind_3181_ = lean_ctor_get(v_inst_3176_, 1);
lean_inc(v_toBind_3181_);
lean_dec_ref(v_inst_3176_);
v_toPure_3182_ = lean_ctor_get(v_toApplicative_3180_, 1);
lean_inc(v_toPure_3182_);
lean_dec_ref(v_toApplicative_3180_);
v___f_3183_ = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3183_, 0, v_f_3177_);
v___x_3184_ = lean_apply_1(v_self_3178_, v_a_3179_);
lean_inc(v_toBind_3181_);
v___f_3185_ = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3185_, 0, v_toPure_3182_);
lean_closure_set(v___f_3185_, 1, v_toBind_3181_);
lean_closure_set(v___f_3185_, 2, v___f_3183_);
v___x_3186_ = lean_apply_4(v_toBind_3181_, lean_box(0), lean_box(0), v___x_3184_, v___f_3185_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog(lean_object* v_m_3187_, lean_object* v_00_u03b1_3188_, lean_object* v_inst_3189_, lean_object* v_f_3190_, lean_object* v_self_3191_, lean_object* v_a_3192_){
_start:
{
lean_object* v_toApplicative_3193_; lean_object* v_toBind_3194_; lean_object* v_toPure_3195_; lean_object* v___f_3196_; lean_object* v___x_3197_; lean_object* v___f_3198_; lean_object* v___x_3199_; 
v_toApplicative_3193_ = lean_ctor_get(v_inst_3189_, 0);
lean_inc_ref(v_toApplicative_3193_);
v_toBind_3194_ = lean_ctor_get(v_inst_3189_, 1);
lean_inc(v_toBind_3194_);
lean_dec_ref(v_inst_3189_);
v_toPure_3195_ = lean_ctor_get(v_toApplicative_3193_, 1);
lean_inc(v_toPure_3195_);
lean_dec_ref(v_toApplicative_3193_);
v___f_3196_ = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3196_, 0, v_f_3190_);
v___x_3197_ = lean_apply_1(v_self_3191_, v_a_3192_);
lean_inc(v_toBind_3194_);
v___f_3198_ = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3198_, 0, v_toPure_3195_);
lean_closure_set(v___f_3198_, 1, v_toBind_3194_);
lean_closure_set(v___f_3198_, 2, v___f_3196_);
v___x_3199_ = lean_apply_4(v_toBind_3194_, lean_box(0), lean_box(0), v___x_3197_, v___f_3198_);
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__1(lean_object* v_toPure_3200_, lean_object* v_a_3201_, lean_object* v_____r_3202_){
_start:
{
lean_object* v___x_3203_; 
v___x_3203_ = lean_apply_2(v_toPure_3200_, lean_box(0), v_a_3201_);
return v___x_3203_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__0(lean_object* v_inst_3204_, lean_object* v_a_3205_, lean_object* v_____r_3206_){
_start:
{
lean_object* v_throw_3207_; lean_object* v___x_3208_; 
v_throw_3207_ = lean_ctor_get(v_inst_3204_, 0);
lean_inc(v_throw_3207_);
lean_dec_ref(v_inst_3204_);
v___x_3208_ = lean_apply_2(v_throw_3207_, lean_box(0), v_a_3205_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__2(lean_object* v_toPure_3209_, lean_object* v_set_3210_, lean_object* v_toBind_3211_, lean_object* v_inst_3212_, lean_object* v_____do__lift_3213_){
_start:
{
if (lean_obj_tag(v_____do__lift_3213_) == 0)
{
lean_object* v_a_3214_; lean_object* v_a_3215_; lean_object* v___f_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
lean_dec_ref(v_inst_3212_);
v_a_3214_ = lean_ctor_get(v_____do__lift_3213_, 0);
lean_inc(v_a_3214_);
v_a_3215_ = lean_ctor_get(v_____do__lift_3213_, 1);
lean_inc(v_a_3215_);
lean_dec_ref(v_____do__lift_3213_);
v___f_3216_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3216_, 0, v_toPure_3209_);
lean_closure_set(v___f_3216_, 1, v_a_3214_);
v___x_3217_ = lean_apply_1(v_set_3210_, v_a_3215_);
v___x_3218_ = lean_apply_4(v_toBind_3211_, lean_box(0), lean_box(0), v___x_3217_, v___f_3216_);
return v___x_3218_;
}
else
{
lean_object* v_a_3219_; lean_object* v_a_3220_; lean_object* v___f_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
lean_dec(v_toPure_3209_);
v_a_3219_ = lean_ctor_get(v_____do__lift_3213_, 0);
lean_inc(v_a_3219_);
v_a_3220_ = lean_ctor_get(v_____do__lift_3213_, 1);
lean_inc(v_a_3220_);
lean_dec_ref(v_____do__lift_3213_);
v___f_3221_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3221_, 0, v_inst_3212_);
lean_closure_set(v___f_3221_, 1, v_a_3219_);
v___x_3222_ = lean_apply_1(v_set_3210_, v_a_3220_);
v___x_3223_ = lean_apply_4(v_toBind_3211_, lean_box(0), lean_box(0), v___x_3222_, v___f_3221_);
return v___x_3223_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__3(lean_object* v_self_3224_, lean_object* v_inst_3225_, lean_object* v_toBind_3226_, lean_object* v___f_3227_, lean_object* v_____do__lift_3228_){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3229_ = lean_apply_1(v_self_3224_, v_____do__lift_3228_);
v___x_3230_ = lean_apply_2(v_inst_3225_, lean_box(0), v___x_3229_);
v___x_3231_ = lean_apply_4(v_toBind_3226_, lean_box(0), lean_box(0), v___x_3230_, v___f_3227_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg(lean_object* v_inst_3232_, lean_object* v_inst_3233_, lean_object* v_inst_3234_, lean_object* v_inst_3235_, lean_object* v_self_3236_){
_start:
{
lean_object* v_toApplicative_3237_; lean_object* v_toBind_3238_; lean_object* v_set_3239_; lean_object* v_modifyGet_3240_; lean_object* v_toPure_3241_; lean_object* v___f_3242_; lean_object* v___x_3243_; lean_object* v___f_3244_; lean_object* v___f_3245_; lean_object* v___x_3246_; 
v_toApplicative_3237_ = lean_ctor_get(v_inst_3232_, 0);
lean_inc_ref(v_toApplicative_3237_);
v_toBind_3238_ = lean_ctor_get(v_inst_3232_, 1);
lean_inc(v_toBind_3238_);
lean_dec_ref(v_inst_3232_);
v_set_3239_ = lean_ctor_get(v_inst_3233_, 1);
lean_inc(v_set_3239_);
v_modifyGet_3240_ = lean_ctor_get(v_inst_3233_, 2);
lean_inc(v_modifyGet_3240_);
lean_dec_ref(v_inst_3233_);
v_toPure_3241_ = lean_ctor_get(v_toApplicative_3237_, 1);
lean_inc(v_toPure_3241_);
lean_dec_ref(v_toApplicative_3237_);
v___f_3242_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_3243_ = lean_apply_2(v_modifyGet_3240_, lean_box(0), v___f_3242_);
lean_inc(v_toBind_3238_);
v___f_3244_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3244_, 0, v_toPure_3241_);
lean_closure_set(v___f_3244_, 1, v_set_3239_);
lean_closure_set(v___f_3244_, 2, v_toBind_3238_);
lean_closure_set(v___f_3244_, 3, v_inst_3234_);
lean_inc(v_toBind_3238_);
v___f_3245_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3245_, 0, v_self_3236_);
lean_closure_set(v___f_3245_, 1, v_inst_3235_);
lean_closure_set(v___f_3245_, 2, v_toBind_3238_);
lean_closure_set(v___f_3245_, 3, v___f_3244_);
v___x_3246_ = lean_apply_4(v_toBind_3238_, lean_box(0), lean_box(0), v___x_3243_, v___f_3245_);
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun(lean_object* v_n_3247_, lean_object* v_m_3248_, lean_object* v_00_u03b1_3249_, lean_object* v_inst_3250_, lean_object* v_inst_3251_, lean_object* v_inst_3252_, lean_object* v_inst_3253_, lean_object* v_self_3254_){
_start:
{
lean_object* v_toApplicative_3255_; lean_object* v_toBind_3256_; lean_object* v_set_3257_; lean_object* v_modifyGet_3258_; lean_object* v_toPure_3259_; lean_object* v___f_3260_; lean_object* v___x_3261_; lean_object* v___f_3262_; lean_object* v___f_3263_; lean_object* v___x_3264_; 
v_toApplicative_3255_ = lean_ctor_get(v_inst_3250_, 0);
lean_inc_ref(v_toApplicative_3255_);
v_toBind_3256_ = lean_ctor_get(v_inst_3250_, 1);
lean_inc(v_toBind_3256_);
lean_dec_ref(v_inst_3250_);
v_set_3257_ = lean_ctor_get(v_inst_3251_, 1);
lean_inc(v_set_3257_);
v_modifyGet_3258_ = lean_ctor_get(v_inst_3251_, 2);
lean_inc(v_modifyGet_3258_);
lean_dec_ref(v_inst_3251_);
v_toPure_3259_ = lean_ctor_get(v_toApplicative_3255_, 1);
lean_inc(v_toPure_3259_);
lean_dec_ref(v_toApplicative_3255_);
v___f_3260_ = ((lean_object*)(l_Lake_takeLog___redArg___closed__0));
v___x_3261_ = lean_apply_2(v_modifyGet_3258_, lean_box(0), v___f_3260_);
lean_inc(v_toBind_3256_);
v___f_3262_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3262_, 0, v_toPure_3259_);
lean_closure_set(v___f_3262_, 1, v_set_3257_);
lean_closure_set(v___f_3262_, 2, v_toBind_3256_);
lean_closure_set(v___f_3262_, 3, v_inst_3252_);
lean_inc(v_toBind_3256_);
v___f_3263_ = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3263_, 0, v_self_3254_);
lean_closure_set(v___f_3263_, 1, v_inst_3253_);
lean_closure_set(v___f_3263_, 2, v_toBind_3256_);
lean_closure_set(v___f_3263_, 3, v___f_3262_);
v___x_3264_ = lean_apply_4(v_toBind_3256_, lean_box(0), lean_box(0), v___x_3261_, v___f_3263_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__2(lean_object* v_toPure_3265_, lean_object* v_x_3266_){
_start:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3267_ = lean_box(0);
v___x_3268_ = lean_apply_2(v_toPure_3265_, lean_box(0), v___x_3267_);
return v___x_3268_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__0(lean_object* v_a_3269_, lean_object* v_toPure_3270_, lean_object* v_x_3271_){
_start:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3272_, 0, v_a_3269_);
v___x_3273_ = lean_apply_2(v_toPure_3270_, lean_box(0), v___x_3272_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__1(lean_object* v_toPure_3274_, lean_object* v___x_3275_, lean_object* v_toSeqRight_3276_, lean_object* v_inst_3277_, lean_object* v___f_3278_, lean_object* v___f_3279_, lean_object* v___f_3280_, lean_object* v_____do__lift_3281_){
_start:
{
if (lean_obj_tag(v_____do__lift_3281_) == 0)
{
lean_object* v_a_3282_; lean_object* v_a_3283_; lean_object* v___f_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; uint8_t v___x_3287_; 
lean_dec(v___f_3280_);
lean_dec(v___f_3279_);
v_a_3282_ = lean_ctor_get(v_____do__lift_3281_, 0);
lean_inc(v_a_3282_);
v_a_3283_ = lean_ctor_get(v_____do__lift_3281_, 1);
lean_inc(v_a_3283_);
lean_dec_ref(v_____do__lift_3281_);
lean_inc(v_toPure_3274_);
v___f_3284_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3284_, 0, v_a_3282_);
lean_closure_set(v___f_3284_, 1, v_toPure_3274_);
v___x_3285_ = lean_array_get_size(v_a_3283_);
v___x_3286_ = lean_box(0);
v___x_3287_ = lean_nat_dec_lt(v___x_3275_, v___x_3285_);
if (v___x_3287_ == 0)
{
lean_object* v___x_3288_; lean_object* v___x_3289_; 
lean_dec(v_a_3283_);
lean_dec(v___f_3278_);
lean_dec_ref(v_inst_3277_);
v___x_3288_ = lean_apply_2(v_toPure_3274_, lean_box(0), v___x_3286_);
v___x_3289_ = lean_apply_4(v_toSeqRight_3276_, lean_box(0), lean_box(0), v___x_3288_, v___f_3284_);
return v___x_3289_;
}
else
{
uint8_t v___x_3290_; 
v___x_3290_ = lean_nat_dec_le(v___x_3285_, v___x_3285_);
if (v___x_3290_ == 0)
{
if (v___x_3287_ == 0)
{
lean_object* v___x_3291_; lean_object* v___x_3292_; 
lean_dec(v_a_3283_);
lean_dec(v___f_3278_);
lean_dec_ref(v_inst_3277_);
v___x_3291_ = lean_apply_2(v_toPure_3274_, lean_box(0), v___x_3286_);
v___x_3292_ = lean_apply_4(v_toSeqRight_3276_, lean_box(0), lean_box(0), v___x_3291_, v___f_3284_);
return v___x_3292_;
}
else
{
size_t v___x_3293_; size_t v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
lean_dec(v_toPure_3274_);
v___x_3293_ = ((size_t)0ULL);
v___x_3294_ = lean_usize_of_nat(v___x_3285_);
v___x_3295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3277_, v___f_3278_, v_a_3283_, v___x_3293_, v___x_3294_, v___x_3286_);
v___x_3296_ = lean_apply_4(v_toSeqRight_3276_, lean_box(0), lean_box(0), v___x_3295_, v___f_3284_);
return v___x_3296_;
}
}
else
{
size_t v___x_3297_; size_t v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
lean_dec(v_toPure_3274_);
v___x_3297_ = ((size_t)0ULL);
v___x_3298_ = lean_usize_of_nat(v___x_3285_);
v___x_3299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3277_, v___f_3278_, v_a_3283_, v___x_3297_, v___x_3298_, v___x_3286_);
v___x_3300_ = lean_apply_4(v_toSeqRight_3276_, lean_box(0), lean_box(0), v___x_3299_, v___f_3284_);
return v___x_3300_;
}
}
}
else
{
lean_object* v_a_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; uint8_t v___x_3304_; 
lean_dec(v___f_3278_);
v_a_3301_ = lean_ctor_get(v_____do__lift_3281_, 1);
lean_inc(v_a_3301_);
lean_dec_ref(v_____do__lift_3281_);
v___x_3302_ = lean_array_get_size(v_a_3301_);
v___x_3303_ = lean_box(0);
v___x_3304_ = lean_nat_dec_lt(v___x_3275_, v___x_3302_);
if (v___x_3304_ == 0)
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
lean_dec(v_a_3301_);
lean_dec(v___f_3280_);
lean_dec_ref(v_inst_3277_);
v___x_3305_ = lean_apply_2(v_toPure_3274_, lean_box(0), v___x_3303_);
v___x_3306_ = lean_apply_4(v_toSeqRight_3276_, lean_box(0), lean_box(0), v___x_3305_, v___f_3279_);
return v___x_3306_;
}
else
{
uint8_t v___x_3307_; 
v___x_3307_ = lean_nat_dec_le(v___x_3302_, v___x_3302_);
if (v___x_3307_ == 0)
{
if (v___x_3304_ == 0)
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
lean_dec(v_a_3301_);
lean_dec(v___f_3280_);
lean_dec_ref(v_inst_3277_);
v___x_3308_ = lean_apply_2(v_toPure_3274_, lean_box(0), v___x_3303_);
v___x_3309_ = lean_apply_4(v_toSeqRight_3276_, lean_box(0), lean_box(0), v___x_3308_, v___f_3279_);
return v___x_3309_;
}
else
{
size_t v___x_3310_; size_t v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
lean_dec(v_toPure_3274_);
v___x_3310_ = ((size_t)0ULL);
v___x_3311_ = lean_usize_of_nat(v___x_3302_);
v___x_3312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3277_, v___f_3280_, v_a_3301_, v___x_3310_, v___x_3311_, v___x_3303_);
v___x_3313_ = lean_apply_4(v_toSeqRight_3276_, lean_box(0), lean_box(0), v___x_3312_, v___f_3279_);
return v___x_3313_;
}
}
else
{
size_t v___x_3314_; size_t v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
lean_dec(v_toPure_3274_);
v___x_3314_ = ((size_t)0ULL);
v___x_3315_ = lean_usize_of_nat(v___x_3302_);
v___x_3316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3277_, v___f_3280_, v_a_3301_, v___x_3314_, v___x_3315_, v___x_3303_);
v___x_3317_ = lean_apply_4(v_toSeqRight_3276_, lean_box(0), lean_box(0), v___x_3316_, v___f_3279_);
return v___x_3317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed(lean_object* v_toPure_3318_, lean_object* v___x_3319_, lean_object* v_toSeqRight_3320_, lean_object* v_inst_3321_, lean_object* v___f_3322_, lean_object* v___f_3323_, lean_object* v___f_3324_, lean_object* v_____do__lift_3325_){
_start:
{
lean_object* v_res_3326_; 
v_res_3326_ = l_Lake_ELogT_replayLog_x3f___redArg___lam__1(v_toPure_3318_, v___x_3319_, v_toSeqRight_3320_, v_inst_3321_, v___f_3322_, v___f_3323_, v___f_3324_, v_____do__lift_3325_);
lean_dec(v___x_3319_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg(lean_object* v_inst_3327_, lean_object* v_logger_3328_, lean_object* v_inst_3329_, lean_object* v_self_3330_){
_start:
{
lean_object* v_toApplicative_3331_; lean_object* v_toBind_3332_; lean_object* v_toPure_3333_; lean_object* v_toSeqRight_3334_; lean_object* v___f_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___f_3340_; lean_object* v___f_3341_; lean_object* v___x_3342_; 
v_toApplicative_3331_ = lean_ctor_get(v_inst_3327_, 0);
v_toBind_3332_ = lean_ctor_get(v_inst_3327_, 1);
lean_inc(v_toBind_3332_);
v_toPure_3333_ = lean_ctor_get(v_toApplicative_3331_, 1);
lean_inc(v_toPure_3333_);
v_toSeqRight_3334_ = lean_ctor_get(v_toApplicative_3331_, 4);
lean_inc(v_toSeqRight_3334_);
v___f_3335_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3335_, 0, v_logger_3328_);
v___x_3336_ = lean_unsigned_to_nat(0u);
v___x_3337_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3338_ = lean_apply_1(v_self_3330_, v___x_3337_);
v___x_3339_ = lean_apply_2(v_inst_3329_, lean_box(0), v___x_3338_);
lean_inc(v_toPure_3333_);
v___f_3340_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3340_, 0, v_toPure_3333_);
lean_inc_ref(v___f_3335_);
v___f_3341_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_3341_, 0, v_toPure_3333_);
lean_closure_set(v___f_3341_, 1, v___x_3336_);
lean_closure_set(v___f_3341_, 2, v_toSeqRight_3334_);
lean_closure_set(v___f_3341_, 3, v_inst_3327_);
lean_closure_set(v___f_3341_, 4, v___f_3335_);
lean_closure_set(v___f_3341_, 5, v___f_3340_);
lean_closure_set(v___f_3341_, 6, v___f_3335_);
v___x_3342_ = lean_apply_4(v_toBind_3332_, lean_box(0), lean_box(0), v___x_3339_, v___f_3341_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f(lean_object* v_n_3343_, lean_object* v_m_3344_, lean_object* v_00_u03b1_3345_, lean_object* v_inst_3346_, lean_object* v_logger_3347_, lean_object* v_inst_3348_, lean_object* v_self_3349_){
_start:
{
lean_object* v_toApplicative_3350_; lean_object* v_toBind_3351_; lean_object* v_toPure_3352_; lean_object* v_toSeqRight_3353_; lean_object* v___f_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___f_3359_; lean_object* v___f_3360_; lean_object* v___x_3361_; 
v_toApplicative_3350_ = lean_ctor_get(v_inst_3346_, 0);
v_toBind_3351_ = lean_ctor_get(v_inst_3346_, 1);
lean_inc(v_toBind_3351_);
v_toPure_3352_ = lean_ctor_get(v_toApplicative_3350_, 1);
lean_inc(v_toPure_3352_);
v_toSeqRight_3353_ = lean_ctor_get(v_toApplicative_3350_, 4);
lean_inc(v_toSeqRight_3353_);
v___f_3354_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3354_, 0, v_logger_3347_);
v___x_3355_ = lean_unsigned_to_nat(0u);
v___x_3356_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3357_ = lean_apply_1(v_self_3349_, v___x_3356_);
v___x_3358_ = lean_apply_2(v_inst_3348_, lean_box(0), v___x_3357_);
lean_inc(v_toPure_3352_);
v___f_3359_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3359_, 0, v_toPure_3352_);
lean_inc_ref(v___f_3354_);
v___f_3360_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_3360_, 0, v_toPure_3352_);
lean_closure_set(v___f_3360_, 1, v___x_3355_);
lean_closure_set(v___f_3360_, 2, v_toSeqRight_3353_);
lean_closure_set(v___f_3360_, 3, v_inst_3346_);
lean_closure_set(v___f_3360_, 4, v___f_3354_);
lean_closure_set(v___f_3360_, 5, v___f_3359_);
lean_closure_set(v___f_3360_, 6, v___f_3354_);
v___x_3361_ = lean_apply_4(v_toBind_3351_, lean_box(0), lean_box(0), v___x_3358_, v___f_3360_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg___lam__3(lean_object* v_toPure_3362_, lean_object* v_a_3363_, lean_object* v_x_3364_){
_start:
{
lean_object* v___x_3365_; 
v___x_3365_ = lean_apply_2(v_toPure_3362_, lean_box(0), v_a_3363_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg___lam__0(lean_object* v_toPure_3366_, lean_object* v___x_3367_, lean_object* v_toApplicative_3368_, lean_object* v_toSeqRight_3369_, lean_object* v_inst_3370_, lean_object* v___f_3371_, lean_object* v___f_3372_, lean_object* v___f_3373_, lean_object* v_____do__lift_3374_){
_start:
{
if (lean_obj_tag(v_____do__lift_3374_) == 0)
{
lean_object* v_a_3375_; lean_object* v_a_3376_; lean_object* v___f_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; uint8_t v___x_3380_; 
lean_dec(v___f_3373_);
lean_dec(v___f_3372_);
v_a_3375_ = lean_ctor_get(v_____do__lift_3374_, 0);
lean_inc(v_a_3375_);
v_a_3376_ = lean_ctor_get(v_____do__lift_3374_, 1);
lean_inc(v_a_3376_);
lean_dec_ref(v_____do__lift_3374_);
v___f_3377_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog___redArg___lam__3), 3, 2);
lean_closure_set(v___f_3377_, 0, v_toPure_3366_);
lean_closure_set(v___f_3377_, 1, v_a_3375_);
v___x_3378_ = lean_array_get_size(v_a_3376_);
v___x_3379_ = lean_box(0);
v___x_3380_ = lean_nat_dec_lt(v___x_3367_, v___x_3378_);
if (v___x_3380_ == 0)
{
lean_object* v_toPure_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; 
lean_dec(v_a_3376_);
lean_dec(v___f_3371_);
lean_dec_ref(v_inst_3370_);
v_toPure_3381_ = lean_ctor_get(v_toApplicative_3368_, 1);
lean_inc(v_toPure_3381_);
lean_dec_ref(v_toApplicative_3368_);
v___x_3382_ = lean_apply_2(v_toPure_3381_, lean_box(0), v___x_3379_);
v___x_3383_ = lean_apply_4(v_toSeqRight_3369_, lean_box(0), lean_box(0), v___x_3382_, v___f_3377_);
return v___x_3383_;
}
else
{
uint8_t v___x_3384_; 
v___x_3384_ = lean_nat_dec_le(v___x_3378_, v___x_3378_);
if (v___x_3384_ == 0)
{
if (v___x_3380_ == 0)
{
lean_object* v_toPure_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
lean_dec(v_a_3376_);
lean_dec(v___f_3371_);
lean_dec_ref(v_inst_3370_);
v_toPure_3385_ = lean_ctor_get(v_toApplicative_3368_, 1);
lean_inc(v_toPure_3385_);
lean_dec_ref(v_toApplicative_3368_);
v___x_3386_ = lean_apply_2(v_toPure_3385_, lean_box(0), v___x_3379_);
v___x_3387_ = lean_apply_4(v_toSeqRight_3369_, lean_box(0), lean_box(0), v___x_3386_, v___f_3377_);
return v___x_3387_;
}
else
{
size_t v___x_3388_; size_t v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
lean_dec_ref(v_toApplicative_3368_);
v___x_3388_ = ((size_t)0ULL);
v___x_3389_ = lean_usize_of_nat(v___x_3378_);
v___x_3390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3370_, v___f_3371_, v_a_3376_, v___x_3388_, v___x_3389_, v___x_3379_);
v___x_3391_ = lean_apply_4(v_toSeqRight_3369_, lean_box(0), lean_box(0), v___x_3390_, v___f_3377_);
return v___x_3391_;
}
}
else
{
size_t v___x_3392_; size_t v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
lean_dec_ref(v_toApplicative_3368_);
v___x_3392_ = ((size_t)0ULL);
v___x_3393_ = lean_usize_of_nat(v___x_3378_);
v___x_3394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3370_, v___f_3371_, v_a_3376_, v___x_3392_, v___x_3393_, v___x_3379_);
v___x_3395_ = lean_apply_4(v_toSeqRight_3369_, lean_box(0), lean_box(0), v___x_3394_, v___f_3377_);
return v___x_3395_;
}
}
}
else
{
lean_object* v_a_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; uint8_t v___x_3399_; 
lean_dec(v___f_3371_);
lean_dec(v_toPure_3366_);
v_a_3396_ = lean_ctor_get(v_____do__lift_3374_, 1);
lean_inc(v_a_3396_);
lean_dec_ref(v_____do__lift_3374_);
v___x_3397_ = lean_array_get_size(v_a_3396_);
v___x_3398_ = lean_box(0);
v___x_3399_ = lean_nat_dec_lt(v___x_3367_, v___x_3397_);
if (v___x_3399_ == 0)
{
lean_object* v_toPure_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
lean_dec(v_a_3396_);
lean_dec(v___f_3373_);
lean_dec_ref(v_inst_3370_);
v_toPure_3400_ = lean_ctor_get(v_toApplicative_3368_, 1);
lean_inc(v_toPure_3400_);
lean_dec_ref(v_toApplicative_3368_);
v___x_3401_ = lean_apply_2(v_toPure_3400_, lean_box(0), v___x_3398_);
v___x_3402_ = lean_apply_4(v_toSeqRight_3369_, lean_box(0), lean_box(0), v___x_3401_, v___f_3372_);
return v___x_3402_;
}
else
{
uint8_t v___x_3403_; 
v___x_3403_ = lean_nat_dec_le(v___x_3397_, v___x_3397_);
if (v___x_3403_ == 0)
{
if (v___x_3399_ == 0)
{
lean_object* v_toPure_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
lean_dec(v_a_3396_);
lean_dec(v___f_3373_);
lean_dec_ref(v_inst_3370_);
v_toPure_3404_ = lean_ctor_get(v_toApplicative_3368_, 1);
lean_inc(v_toPure_3404_);
lean_dec_ref(v_toApplicative_3368_);
v___x_3405_ = lean_apply_2(v_toPure_3404_, lean_box(0), v___x_3398_);
v___x_3406_ = lean_apply_4(v_toSeqRight_3369_, lean_box(0), lean_box(0), v___x_3405_, v___f_3372_);
return v___x_3406_;
}
else
{
size_t v___x_3407_; size_t v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
lean_dec_ref(v_toApplicative_3368_);
v___x_3407_ = ((size_t)0ULL);
v___x_3408_ = lean_usize_of_nat(v___x_3397_);
v___x_3409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3370_, v___f_3373_, v_a_3396_, v___x_3407_, v___x_3408_, v___x_3398_);
v___x_3410_ = lean_apply_4(v_toSeqRight_3369_, lean_box(0), lean_box(0), v___x_3409_, v___f_3372_);
return v___x_3410_;
}
}
else
{
size_t v___x_3411_; size_t v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
lean_dec_ref(v_toApplicative_3368_);
v___x_3411_ = ((size_t)0ULL);
v___x_3412_ = lean_usize_of_nat(v___x_3397_);
v___x_3413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3370_, v___f_3373_, v_a_3396_, v___x_3411_, v___x_3412_, v___x_3398_);
v___x_3414_ = lean_apply_4(v_toSeqRight_3369_, lean_box(0), lean_box(0), v___x_3413_, v___f_3372_);
return v___x_3414_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg___lam__0___boxed(lean_object* v_toPure_3415_, lean_object* v___x_3416_, lean_object* v_toApplicative_3417_, lean_object* v_toSeqRight_3418_, lean_object* v_inst_3419_, lean_object* v___f_3420_, lean_object* v___f_3421_, lean_object* v___f_3422_, lean_object* v_____do__lift_3423_){
_start:
{
lean_object* v_res_3424_; 
v_res_3424_ = l_Lake_ELogT_replayLog___redArg___lam__0(v_toPure_3415_, v___x_3416_, v_toApplicative_3417_, v_toSeqRight_3418_, v_inst_3419_, v___f_3420_, v___f_3421_, v___f_3422_, v_____do__lift_3423_);
lean_dec(v___x_3416_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg(lean_object* v_inst_3425_, lean_object* v_inst_3426_, lean_object* v_logger_3427_, lean_object* v_inst_3428_, lean_object* v_self_3429_){
_start:
{
lean_object* v_toApplicative_3430_; lean_object* v_toApplicative_3431_; lean_object* v_toBind_3432_; lean_object* v_failure_3433_; lean_object* v_toPure_3434_; lean_object* v_toSeqRight_3435_; lean_object* v___f_3436_; lean_object* v___f_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___f_3442_; lean_object* v___x_3443_; 
v_toApplicative_3430_ = lean_ctor_get(v_inst_3425_, 0);
lean_inc_ref(v_toApplicative_3430_);
v_toApplicative_3431_ = lean_ctor_get(v_inst_3426_, 0);
lean_inc_ref(v_toApplicative_3431_);
v_toBind_3432_ = lean_ctor_get(v_inst_3426_, 1);
lean_inc(v_toBind_3432_);
v_failure_3433_ = lean_ctor_get(v_inst_3425_, 1);
lean_inc(v_failure_3433_);
lean_dec_ref(v_inst_3425_);
v_toPure_3434_ = lean_ctor_get(v_toApplicative_3430_, 1);
lean_inc(v_toPure_3434_);
v_toSeqRight_3435_ = lean_ctor_get(v_toApplicative_3430_, 4);
lean_inc(v_toSeqRight_3435_);
lean_dec_ref(v_toApplicative_3430_);
v___f_3436_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3436_, 0, v_logger_3427_);
v___f_3437_ = lean_alloc_closure((void*)(l_Lake_MonadLog_error___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3437_, 0, v_failure_3433_);
v___x_3438_ = lean_unsigned_to_nat(0u);
v___x_3439_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3440_ = lean_apply_1(v_self_3429_, v___x_3439_);
v___x_3441_ = lean_apply_2(v_inst_3428_, lean_box(0), v___x_3440_);
lean_inc_ref(v___f_3436_);
v___f_3442_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3442_, 0, v_toPure_3434_);
lean_closure_set(v___f_3442_, 1, v___x_3438_);
lean_closure_set(v___f_3442_, 2, v_toApplicative_3431_);
lean_closure_set(v___f_3442_, 3, v_toSeqRight_3435_);
lean_closure_set(v___f_3442_, 4, v_inst_3426_);
lean_closure_set(v___f_3442_, 5, v___f_3436_);
lean_closure_set(v___f_3442_, 6, v___f_3437_);
lean_closure_set(v___f_3442_, 7, v___f_3436_);
v___x_3443_ = lean_apply_4(v_toBind_3432_, lean_box(0), lean_box(0), v___x_3441_, v___f_3442_);
return v___x_3443_;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog(lean_object* v_n_3444_, lean_object* v_m_3445_, lean_object* v_00_u03b1_3446_, lean_object* v_inst_3447_, lean_object* v_inst_3448_, lean_object* v_logger_3449_, lean_object* v_inst_3450_, lean_object* v_self_3451_){
_start:
{
lean_object* v_toApplicative_3452_; lean_object* v_toApplicative_3453_; lean_object* v_toBind_3454_; lean_object* v_failure_3455_; lean_object* v_toPure_3456_; lean_object* v_toSeqRight_3457_; lean_object* v___f_3458_; lean_object* v___f_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___f_3464_; lean_object* v___x_3465_; 
v_toApplicative_3452_ = lean_ctor_get(v_inst_3447_, 0);
lean_inc_ref(v_toApplicative_3452_);
v_toApplicative_3453_ = lean_ctor_get(v_inst_3448_, 0);
lean_inc_ref(v_toApplicative_3453_);
v_toBind_3454_ = lean_ctor_get(v_inst_3448_, 1);
lean_inc(v_toBind_3454_);
v_failure_3455_ = lean_ctor_get(v_inst_3447_, 1);
lean_inc(v_failure_3455_);
lean_dec_ref(v_inst_3447_);
v_toPure_3456_ = lean_ctor_get(v_toApplicative_3452_, 1);
lean_inc(v_toPure_3456_);
v_toSeqRight_3457_ = lean_ctor_get(v_toApplicative_3452_, 4);
lean_inc(v_toSeqRight_3457_);
lean_dec_ref(v_toApplicative_3452_);
v___f_3458_ = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3458_, 0, v_logger_3449_);
v___f_3459_ = lean_alloc_closure((void*)(l_Lake_MonadLog_error___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3459_, 0, v_failure_3455_);
v___x_3460_ = lean_unsigned_to_nat(0u);
v___x_3461_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3462_ = lean_apply_1(v_self_3451_, v___x_3461_);
v___x_3463_ = lean_apply_2(v_inst_3450_, lean_box(0), v___x_3462_);
lean_inc_ref(v___f_3458_);
v___f_3464_ = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3464_, 0, v_toPure_3456_);
lean_closure_set(v___f_3464_, 1, v___x_3460_);
lean_closure_set(v___f_3464_, 2, v_toApplicative_3453_);
lean_closure_set(v___f_3464_, 3, v_toSeqRight_3457_);
lean_closure_set(v___f_3464_, 4, v_inst_3448_);
lean_closure_set(v___f_3464_, 5, v___f_3458_);
lean_closure_set(v___f_3464_, 6, v___f_3459_);
lean_closure_set(v___f_3464_, 7, v___f_3458_);
v___x_3465_ = lean_apply_4(v_toBind_3454_, lean_box(0), lean_box(0), v___x_3463_, v___f_3464_);
return v___x_3465_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___redArg___lam__0(lean_object* v_val_3466_, uint8_t v_outLv_3467_, uint8_t v_val_3468_, lean_object* v_inst_3469_, lean_object* v_e_3470_){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3471_ = lean_box(v_outLv_3467_);
v___x_3472_ = lean_box(v_val_3468_);
v___x_3473_ = lean_alloc_closure((void*)(l_Lake_logToStream___boxed), 5, 4);
lean_closure_set(v___x_3473_, 0, v_e_3470_);
lean_closure_set(v___x_3473_, 1, v_val_3466_);
lean_closure_set(v___x_3473_, 2, v___x_3471_);
lean_closure_set(v___x_3473_, 3, v___x_3472_);
v___x_3474_ = lean_apply_2(v_inst_3469_, lean_box(0), v___x_3473_);
return v___x_3474_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___redArg___lam__0___boxed(lean_object* v_val_3475_, lean_object* v_outLv_3476_, lean_object* v_val_3477_, lean_object* v_inst_3478_, lean_object* v_e_3479_){
_start:
{
uint8_t v_outLv_boxed_3480_; uint8_t v_val_44__boxed_3481_; lean_object* v_res_3482_; 
v_outLv_boxed_3480_ = lean_unbox(v_outLv_3476_);
v_val_44__boxed_3481_ = lean_unbox(v_val_3477_);
v_res_3482_ = l_Lake_LogConfig_getLogger___redArg___lam__0(v_val_3475_, v_outLv_boxed_3480_, v_val_44__boxed_3481_, v_inst_3478_, v_e_3479_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___redArg(lean_object* v_inst_3483_, lean_object* v_self_3484_){
_start:
{
uint8_t v_outLv_3486_; uint8_t v_ansiMode_3487_; lean_object* v_out_3488_; lean_object* v___x_3489_; uint8_t v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___f_3493_; 
v_outLv_3486_ = lean_ctor_get_uint8(v_self_3484_, sizeof(void*)*1 + 1);
v_ansiMode_3487_ = lean_ctor_get_uint8(v_self_3484_, sizeof(void*)*1 + 2);
v_out_3488_ = lean_ctor_get(v_self_3484_, 0);
v___x_3489_ = l_Lake_OutStream_get(v_out_3488_);
lean_inc_ref(v___x_3489_);
v___x_3490_ = l_Lake_AnsiMode_isEnabled(v___x_3489_, v_ansiMode_3487_);
v___x_3491_ = lean_box(v_outLv_3486_);
v___x_3492_ = lean_box(v___x_3490_);
v___f_3493_ = lean_alloc_closure((void*)(l_Lake_LogConfig_getLogger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3493_, 0, v___x_3489_);
lean_closure_set(v___f_3493_, 1, v___x_3491_);
lean_closure_set(v___f_3493_, 2, v___x_3492_);
lean_closure_set(v___f_3493_, 3, v_inst_3483_);
return v___f_3493_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___redArg___boxed(lean_object* v_inst_3494_, lean_object* v_self_3495_, lean_object* v_a_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l_Lake_LogConfig_getLogger___redArg(v_inst_3494_, v_self_3495_);
lean_dec_ref(v_self_3495_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger(lean_object* v_m_3498_, lean_object* v_inst_3499_, lean_object* v_self_3500_){
_start:
{
uint8_t v_outLv_3502_; uint8_t v_ansiMode_3503_; lean_object* v_out_3504_; lean_object* v___x_3505_; uint8_t v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___f_3509_; 
v_outLv_3502_ = lean_ctor_get_uint8(v_self_3500_, sizeof(void*)*1 + 1);
v_ansiMode_3503_ = lean_ctor_get_uint8(v_self_3500_, sizeof(void*)*1 + 2);
v_out_3504_ = lean_ctor_get(v_self_3500_, 0);
v___x_3505_ = l_Lake_OutStream_get(v_out_3504_);
lean_inc_ref(v___x_3505_);
v___x_3506_ = l_Lake_AnsiMode_isEnabled(v___x_3505_, v_ansiMode_3503_);
v___x_3507_ = lean_box(v_outLv_3502_);
v___x_3508_ = lean_box(v___x_3506_);
v___f_3509_ = lean_alloc_closure((void*)(l_Lake_LogConfig_getLogger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3509_, 0, v___x_3505_);
lean_closure_set(v___f_3509_, 1, v___x_3507_);
lean_closure_set(v___f_3509_, 2, v___x_3508_);
lean_closure_set(v___f_3509_, 3, v_inst_3499_);
return v___f_3509_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogConfig_getLogger___boxed(lean_object* v_m_3510_, lean_object* v_inst_3511_, lean_object* v_self_3512_, lean_object* v_a_3513_){
_start:
{
lean_object* v_res_3514_; 
v_res_3514_ = l_Lake_LogConfig_getLogger(v_m_3510_, v_inst_3511_, v_self_3512_);
lean_dec_ref(v_self_3512_);
return v_res_3514_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_instMonadLiftIO___lam__0(lean_object* v_00_u03b1_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
lean_object* v___x_3519_; 
v___x_3519_ = lean_apply_1(v___y_3516_, lean_box(0));
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; lean_object* v___x_3521_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3520_);
lean_dec_ref(v___x_3519_);
v___x_3521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3521_, 0, v_a_3520_);
lean_ctor_set(v___x_3521_, 1, v___y_3517_);
return v___x_3521_;
}
else
{
lean_object* v_a_3522_; lean_object* v___x_3523_; uint8_t v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
v_a_3522_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3522_);
lean_dec_ref(v___x_3519_);
v___x_3523_ = lean_io_error_to_string(v_a_3522_);
v___x_3524_ = 3;
v___x_3525_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3525_, 0, v___x_3523_);
lean_ctor_set_uint8(v___x_3525_, sizeof(void*)*1, v___x_3524_);
v___x_3526_ = lean_array_get_size(v___y_3517_);
v___x_3527_ = lean_array_push(v___y_3517_, v___x_3525_);
v___x_3528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3526_);
lean_ctor_set(v___x_3528_, 1, v___x_3527_);
return v___x_3528_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_instMonadLiftIO___lam__0___boxed(lean_object* v_00_u03b1_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Lake_LogIO_instMonadLiftIO___lam__0(v_00_u03b1_3529_, v___y_3530_, v___y_3531_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg___lam__0(lean_object* v_val_3536_, uint8_t v___y_3537_, uint8_t v_val_3538_, lean_object* v_x_3539_, lean_object* v___y_3540_){
_start:
{
lean_object* v___x_3542_; 
v___x_3542_ = l_Lake_logToStream(v___y_3540_, v_val_3536_, v___y_3537_, v_val_3538_);
return v___x_3542_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed(lean_object* v_val_3543_, lean_object* v___y_3544_, lean_object* v_val_3545_, lean_object* v_x_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
uint8_t v___y_1161__boxed_3549_; uint8_t v_val_1162__boxed_3550_; lean_object* v_res_3551_; 
v___y_1161__boxed_3549_ = lean_unbox(v___y_3544_);
v_val_1162__boxed_3550_ = lean_unbox(v_val_3545_);
v_res_3551_ = l_Lake_LogIO_toBaseIO___redArg___lam__0(v_val_3543_, v___y_1161__boxed_3549_, v_val_1162__boxed_3550_, v_x_3546_, v___y_3547_);
lean_dec_ref(v___y_3547_);
return v_res_3551_;
}
}
static lean_object* _init_l_Lake_LogIO_toBaseIO___redArg___closed__0(void){
_start:
{
lean_object* v___x_3552_; 
v___x_3552_ = l_instMonadST(lean_box(0));
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg(lean_object* v_self_3553_, lean_object* v_cfg_3554_){
_start:
{
lean_object* v___y_3557_; uint8_t v___y_3558_; uint8_t v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___x_3564_; uint8_t v___y_3566_; lean_object* v___y_3567_; lean_object* v___y_3568_; uint8_t v___y_3569_; lean_object* v___y_3591_; lean_object* v___y_3592_; uint8_t v___y_3593_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3564_ = lean_obj_once(&l_Lake_LogIO_toBaseIO___redArg___closed__0, &l_Lake_LogIO_toBaseIO___redArg___closed__0_once, _init_l_Lake_LogIO_toBaseIO___redArg___closed__0);
v___x_3595_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3596_ = lean_apply_2(v_self_3553_, v___x_3595_, lean_box(0));
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v_a_3597_; lean_object* v_a_3598_; uint8_t v_failLv_3599_; uint8_t v_outLv_3600_; lean_object* v___x_3601_; uint8_t v___x_3602_; uint8_t v___x_3603_; 
v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
lean_inc(v_a_3597_);
v_a_3598_ = lean_ctor_get(v___x_3596_, 1);
lean_inc(v_a_3598_);
lean_dec_ref(v___x_3596_);
v_failLv_3599_ = lean_ctor_get_uint8(v_cfg_3554_, sizeof(void*)*1);
v_outLv_3600_ = lean_ctor_get_uint8(v_cfg_3554_, sizeof(void*)*1 + 1);
v___x_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3601_, 0, v_a_3597_);
v___x_3602_ = l_Lake_Log_maxLv(v_a_3598_);
v___x_3603_ = l_Lake_instOrdLogLevel_ord(v_failLv_3599_, v___x_3602_);
if (v___x_3603_ == 2)
{
uint8_t v___x_3604_; 
v___x_3604_ = 0;
v___y_3566_ = v___x_3604_;
v___y_3567_ = v___x_3601_;
v___y_3568_ = v_a_3598_;
v___y_3569_ = v_outLv_3600_;
goto v___jp_3565_;
}
else
{
uint8_t v___x_3605_; 
v___x_3605_ = 1;
v___y_3591_ = v_a_3598_;
v___y_3592_ = v___x_3601_;
v___y_3593_ = v___x_3605_;
goto v___jp_3590_;
}
}
else
{
lean_object* v_a_3606_; lean_object* v___x_3607_; uint8_t v___x_3608_; 
v_a_3606_ = lean_ctor_get(v___x_3596_, 1);
lean_inc(v_a_3606_);
lean_dec_ref(v___x_3596_);
v___x_3607_ = lean_box(0);
v___x_3608_ = 1;
v___y_3591_ = v_a_3606_;
v___y_3592_ = v___x_3607_;
v___y_3593_ = v___x_3608_;
goto v___jp_3590_;
}
v___jp_3556_:
{
if (v___y_3558_ == 0)
{
return v___y_3557_;
}
else
{
lean_object* v___x_3559_; 
lean_dec(v___y_3557_);
v___x_3559_ = lean_box(0);
return v___x_3559_;
}
}
v___jp_3560_:
{
v___y_3557_ = v___y_3562_;
v___y_3558_ = v___y_3561_;
goto v___jp_3556_;
}
v___jp_3565_:
{
uint8_t v_ansiMode_3570_; lean_object* v_out_3571_; lean_object* v___x_3572_; uint8_t v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; uint8_t v___x_3576_; 
v_ansiMode_3570_ = lean_ctor_get_uint8(v_cfg_3554_, sizeof(void*)*1 + 2);
v_out_3571_ = lean_ctor_get(v_cfg_3554_, 0);
v___x_3572_ = l_Lake_OutStream_get(v_out_3571_);
lean_inc_ref(v___x_3572_);
v___x_3573_ = l_Lake_AnsiMode_isEnabled(v___x_3572_, v_ansiMode_3570_);
v___x_3574_ = lean_unsigned_to_nat(0u);
v___x_3575_ = lean_array_get_size(v___y_3568_);
v___x_3576_ = lean_nat_dec_lt(v___x_3574_, v___x_3575_);
if (v___x_3576_ == 0)
{
lean_dec_ref(v___x_3572_);
lean_dec_ref(v___y_3568_);
v___y_3557_ = v___y_3567_;
v___y_3558_ = v___y_3566_;
goto v___jp_3556_;
}
else
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___f_3579_; lean_object* v___x_3580_; uint8_t v___x_3581_; 
v___x_3577_ = lean_box(v___y_3569_);
v___x_3578_ = lean_box(v___x_3573_);
v___f_3579_ = lean_alloc_closure((void*)(l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_3579_, 0, v___x_3572_);
lean_closure_set(v___f_3579_, 1, v___x_3577_);
lean_closure_set(v___f_3579_, 2, v___x_3578_);
v___x_3580_ = lean_box(0);
v___x_3581_ = lean_nat_dec_le(v___x_3575_, v___x_3575_);
if (v___x_3581_ == 0)
{
if (v___x_3576_ == 0)
{
lean_dec_ref(v___f_3579_);
lean_dec_ref(v___y_3568_);
v___y_3557_ = v___y_3567_;
v___y_3558_ = v___y_3566_;
goto v___jp_3556_;
}
else
{
size_t v___x_3582_; size_t v___x_3583_; lean_object* v___x_950__overap_3584_; lean_object* v___x_3585_; 
v___x_3582_ = ((size_t)0ULL);
v___x_3583_ = lean_usize_of_nat(v___x_3575_);
v___x_950__overap_3584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3564_, v___f_3579_, v___y_3568_, v___x_3582_, v___x_3583_, v___x_3580_);
v___x_3585_ = lean_apply_1(v___x_950__overap_3584_, lean_box(0));
v___y_3561_ = v___y_3566_;
v___y_3562_ = v___y_3567_;
v___y_3563_ = v___x_3585_;
goto v___jp_3560_;
}
}
else
{
size_t v___x_3586_; size_t v___x_3587_; lean_object* v___x_954__overap_3588_; lean_object* v___x_3589_; 
v___x_3586_ = ((size_t)0ULL);
v___x_3587_ = lean_usize_of_nat(v___x_3575_);
v___x_954__overap_3588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3564_, v___f_3579_, v___y_3568_, v___x_3586_, v___x_3587_, v___x_3580_);
v___x_3589_ = lean_apply_1(v___x_954__overap_3588_, lean_box(0));
v___y_3561_ = v___y_3566_;
v___y_3562_ = v___y_3567_;
v___y_3563_ = v___x_3589_;
goto v___jp_3560_;
}
}
}
v___jp_3590_:
{
uint8_t v___x_3594_; 
v___x_3594_ = 0;
v___y_3566_ = v___y_3593_;
v___y_3567_ = v___y_3592_;
v___y_3568_ = v___y_3591_;
v___y_3569_ = v___x_3594_;
goto v___jp_3565_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg___boxed(lean_object* v_self_3609_, lean_object* v_cfg_3610_, lean_object* v_a_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l_Lake_LogIO_toBaseIO___redArg(v_self_3609_, v_cfg_3610_);
lean_dec_ref(v_cfg_3610_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO(lean_object* v_00_u03b1_3613_, lean_object* v_self_3614_, lean_object* v_cfg_3615_){
_start:
{
lean_object* v___y_3618_; uint8_t v___y_3619_; uint8_t v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___x_3625_; uint8_t v___y_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; uint8_t v___y_3630_; lean_object* v___y_3652_; lean_object* v___y_3653_; uint8_t v___y_3654_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3625_ = lean_obj_once(&l_Lake_LogIO_toBaseIO___redArg___closed__0, &l_Lake_LogIO_toBaseIO___redArg___closed__0_once, _init_l_Lake_LogIO_toBaseIO___redArg___closed__0);
v___x_3656_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3657_ = lean_apply_2(v_self_3614_, v___x_3656_, lean_box(0));
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v_a_3658_; lean_object* v_a_3659_; uint8_t v_failLv_3660_; uint8_t v_outLv_3661_; lean_object* v___x_3662_; uint8_t v___x_3663_; uint8_t v___x_3664_; 
v_a_3658_ = lean_ctor_get(v___x_3657_, 0);
lean_inc(v_a_3658_);
v_a_3659_ = lean_ctor_get(v___x_3657_, 1);
lean_inc(v_a_3659_);
lean_dec_ref(v___x_3657_);
v_failLv_3660_ = lean_ctor_get_uint8(v_cfg_3615_, sizeof(void*)*1);
v_outLv_3661_ = lean_ctor_get_uint8(v_cfg_3615_, sizeof(void*)*1 + 1);
v___x_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3662_, 0, v_a_3658_);
v___x_3663_ = l_Lake_Log_maxLv(v_a_3659_);
v___x_3664_ = l_Lake_instOrdLogLevel_ord(v_failLv_3660_, v___x_3663_);
if (v___x_3664_ == 2)
{
uint8_t v___x_3665_; 
v___x_3665_ = 0;
v___y_3627_ = v___x_3665_;
v___y_3628_ = v___x_3662_;
v___y_3629_ = v_a_3659_;
v___y_3630_ = v_outLv_3661_;
goto v___jp_3626_;
}
else
{
uint8_t v___x_3666_; 
v___x_3666_ = 1;
v___y_3652_ = v_a_3659_;
v___y_3653_ = v___x_3662_;
v___y_3654_ = v___x_3666_;
goto v___jp_3651_;
}
}
else
{
lean_object* v_a_3667_; lean_object* v___x_3668_; uint8_t v___x_3669_; 
v_a_3667_ = lean_ctor_get(v___x_3657_, 1);
lean_inc(v_a_3667_);
lean_dec_ref(v___x_3657_);
v___x_3668_ = lean_box(0);
v___x_3669_ = 1;
v___y_3652_ = v_a_3667_;
v___y_3653_ = v___x_3668_;
v___y_3654_ = v___x_3669_;
goto v___jp_3651_;
}
v___jp_3617_:
{
if (v___y_3619_ == 0)
{
return v___y_3618_;
}
else
{
lean_object* v___x_3620_; 
lean_dec(v___y_3618_);
v___x_3620_ = lean_box(0);
return v___x_3620_;
}
}
v___jp_3621_:
{
v___y_3618_ = v___y_3623_;
v___y_3619_ = v___y_3622_;
goto v___jp_3617_;
}
v___jp_3626_:
{
uint8_t v_ansiMode_3631_; lean_object* v_out_3632_; lean_object* v___x_3633_; uint8_t v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; uint8_t v___x_3637_; 
v_ansiMode_3631_ = lean_ctor_get_uint8(v_cfg_3615_, sizeof(void*)*1 + 2);
v_out_3632_ = lean_ctor_get(v_cfg_3615_, 0);
v___x_3633_ = l_Lake_OutStream_get(v_out_3632_);
lean_inc_ref(v___x_3633_);
v___x_3634_ = l_Lake_AnsiMode_isEnabled(v___x_3633_, v_ansiMode_3631_);
v___x_3635_ = lean_unsigned_to_nat(0u);
v___x_3636_ = lean_array_get_size(v___y_3629_);
v___x_3637_ = lean_nat_dec_lt(v___x_3635_, v___x_3636_);
if (v___x_3637_ == 0)
{
lean_dec_ref(v___x_3633_);
lean_dec_ref(v___y_3629_);
v___y_3618_ = v___y_3628_;
v___y_3619_ = v___y_3627_;
goto v___jp_3617_;
}
else
{
lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___f_3640_; lean_object* v___x_3641_; uint8_t v___x_3642_; 
v___x_3638_ = lean_box(v___y_3630_);
v___x_3639_ = lean_box(v___x_3634_);
v___f_3640_ = lean_alloc_closure((void*)(l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_3640_, 0, v___x_3633_);
lean_closure_set(v___f_3640_, 1, v___x_3638_);
lean_closure_set(v___f_3640_, 2, v___x_3639_);
v___x_3641_ = lean_box(0);
v___x_3642_ = lean_nat_dec_le(v___x_3636_, v___x_3636_);
if (v___x_3642_ == 0)
{
if (v___x_3637_ == 0)
{
lean_dec_ref(v___f_3640_);
lean_dec_ref(v___y_3629_);
v___y_3618_ = v___y_3628_;
v___y_3619_ = v___y_3627_;
goto v___jp_3617_;
}
else
{
size_t v___x_3643_; size_t v___x_3644_; lean_object* v___x_1090__overap_3645_; lean_object* v___x_3646_; 
v___x_3643_ = ((size_t)0ULL);
v___x_3644_ = lean_usize_of_nat(v___x_3636_);
v___x_1090__overap_3645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3625_, v___f_3640_, v___y_3629_, v___x_3643_, v___x_3644_, v___x_3641_);
v___x_3646_ = lean_apply_1(v___x_1090__overap_3645_, lean_box(0));
v___y_3622_ = v___y_3627_;
v___y_3623_ = v___y_3628_;
v___y_3624_ = v___x_3646_;
goto v___jp_3621_;
}
}
else
{
size_t v___x_3647_; size_t v___x_3648_; lean_object* v___x_1093__overap_3649_; lean_object* v___x_3650_; 
v___x_3647_ = ((size_t)0ULL);
v___x_3648_ = lean_usize_of_nat(v___x_3636_);
v___x_1093__overap_3649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3625_, v___f_3640_, v___y_3629_, v___x_3647_, v___x_3648_, v___x_3641_);
v___x_3650_ = lean_apply_1(v___x_1093__overap_3649_, lean_box(0));
v___y_3622_ = v___y_3627_;
v___y_3623_ = v___y_3628_;
v___y_3624_ = v___x_3650_;
goto v___jp_3621_;
}
}
}
v___jp_3651_:
{
uint8_t v___x_3655_; 
v___x_3655_ = 0;
v___y_3627_ = v___y_3654_;
v___y_3628_ = v___y_3653_;
v___y_3629_ = v___y_3652_;
v___y_3630_ = v___x_3655_;
goto v___jp_3626_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___boxed(lean_object* v_00_u03b1_3670_, lean_object* v_self_3671_, lean_object* v_cfg_3672_, lean_object* v_a_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l_Lake_LogIO_toBaseIO(v_00_u03b1_3670_, v_self_3671_, v_cfg_3672_);
lean_dec_ref(v_cfg_3672_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_captureLog___redArg(lean_object* v_inst_3675_, lean_object* v_self_3676_, lean_object* v_log_3677_){
_start:
{
lean_object* v_map_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
v_map_3678_ = lean_ctor_get(v_inst_3675_, 0);
lean_inc(v_map_3678_);
lean_dec_ref(v_inst_3675_);
v___x_3679_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3680_ = lean_apply_1(v_self_3676_, v_log_3677_);
v___x_3681_ = lean_apply_4(v_map_3678_, lean_box(0), lean_box(0), v___x_3679_, v___x_3680_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_captureLog(lean_object* v_m_3682_, lean_object* v_00_u03b1_3683_, lean_object* v_inst_3684_, lean_object* v_self_3685_, lean_object* v_log_3686_){
_start:
{
lean_object* v_map_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; 
v_map_3687_ = lean_ctor_get(v_inst_3684_, 0);
lean_inc(v_map_3687_);
lean_dec_ref(v_inst_3684_);
v___x_3688_ = ((lean_object*)(l_Lake_ELogT_toLogT_x3f___redArg___closed__0));
v___x_3689_ = lean_apply_1(v_self_3685_, v_log_3686_);
v___x_3690_ = lean_apply_4(v_map_3687_, lean_box(0), lean_box(0), v___x_3688_, v___x_3689_);
return v___x_3690_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadError___lam__0(lean_object* v_00_u03b1_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_){
_start:
{
uint8_t v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3695_ = 3;
v___x_3696_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3696_, 0, v___y_3692_);
lean_ctor_set_uint8(v___x_3696_, sizeof(void*)*1, v___x_3695_);
v___x_3697_ = lean_apply_2(v___y_3693_, v___x_3696_, lean_box(0));
v___x_3698_ = lean_box(0);
v___x_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3698_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadError___lam__0___boxed(lean_object* v_00_u03b1_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
lean_object* v_res_3704_; 
v_res_3704_ = l_Lake_LoggerIO_instMonadError___lam__0(v_00_u03b1_3700_, v___y_3701_, v___y_3702_);
return v_res_3704_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftIO___lam__0(lean_object* v_00_u03b1_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v___x_3711_; 
v___x_3711_ = lean_apply_1(v___y_3708_, lean_box(0));
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v_a_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3719_; 
lean_dec_ref(v___y_3709_);
v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3714_ = v___x_3711_;
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v___x_3711_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3712_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
else
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3732_; 
v_a_3720_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3722_ = v___x_3711_;
v_isShared_3723_ = v_isSharedCheck_3732_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3711_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3732_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3724_; uint8_t v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3730_; 
v___x_3724_ = lean_io_error_to_string(v_a_3720_);
v___x_3725_ = 3;
v___x_3726_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3726_, 0, v___x_3724_);
lean_ctor_set_uint8(v___x_3726_, sizeof(void*)*1, v___x_3725_);
v___x_3727_ = lean_apply_2(v___y_3709_, v___x_3726_, lean_box(0));
v___x_3728_ = lean_box(0);
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 0, v___x_3728_);
v___x_3730_ = v___x_3722_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3728_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftIO___lam__0___boxed(lean_object* v_00_u03b1_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
lean_object* v_res_3737_; 
v_res_3737_ = l_Lake_LoggerIO_instMonadLiftIO___lam__0(v_00_u03b1_3733_, v___y_3734_, v___y_3735_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__0(lean_object* v_x_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_){
_start:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; 
v___x_3744_ = lean_apply_2(v___y_3742_, v___y_3741_, lean_box(0));
v___x_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3744_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__0___boxed(lean_object* v_x_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
lean_object* v_res_3750_; 
v_res_3750_ = l_Lake_LoggerIO_instMonadLiftLogIO___lam__0(v_x_3746_, v___y_3747_, v___y_3748_);
return v_res_3750_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__2(lean_object* v___x_3751_, lean_object* v___f_3752_, lean_object* v___f_3753_, lean_object* v_00_u03b1_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
v___x_3761_ = lean_unsigned_to_nat(0u);
v___x_3762_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3763_ = lean_apply_2(v___y_3755_, v___x_3762_, lean_box(0));
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_object* v_a_3764_; lean_object* v_a_3765_; lean_object* v___x_3766_; uint8_t v___x_3767_; 
lean_dec_ref(v___f_3753_);
v_a_3764_ = lean_ctor_get(v___x_3763_, 0);
lean_inc(v_a_3764_);
v_a_3765_ = lean_ctor_get(v___x_3763_, 1);
lean_inc(v_a_3765_);
lean_dec_ref(v___x_3763_);
v___x_3766_ = lean_array_get_size(v_a_3765_);
v___x_3767_ = lean_nat_dec_lt(v___x_3761_, v___x_3766_);
if (v___x_3767_ == 0)
{
lean_object* v___x_3768_; 
lean_dec(v_a_3765_);
lean_dec_ref(v___y_3756_);
lean_dec_ref(v___f_3752_);
lean_dec_ref(v___x_3751_);
v___x_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3768_, 0, v_a_3764_);
return v___x_3768_;
}
else
{
lean_object* v___x_3769_; uint8_t v___x_3770_; 
v___x_3769_ = lean_box(0);
v___x_3770_ = lean_nat_dec_le(v___x_3766_, v___x_3766_);
if (v___x_3770_ == 0)
{
if (v___x_3767_ == 0)
{
lean_object* v___x_3771_; 
lean_dec(v_a_3765_);
lean_dec_ref(v___y_3756_);
lean_dec_ref(v___f_3752_);
lean_dec_ref(v___x_3751_);
v___x_3771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3771_, 0, v_a_3764_);
return v___x_3771_;
}
else
{
size_t v___x_3772_; size_t v___x_3773_; lean_object* v___x_3335__overap_3774_; lean_object* v___x_3775_; 
v___x_3772_ = ((size_t)0ULL);
v___x_3773_ = lean_usize_of_nat(v___x_3766_);
v___x_3335__overap_3774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3751_, v___f_3752_, v_a_3765_, v___x_3772_, v___x_3773_, v___x_3769_);
v___x_3775_ = lean_apply_2(v___x_3335__overap_3774_, v___y_3756_, lean_box(0));
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3782_ == 0)
{
lean_object* v_unused_3783_; 
v_unused_3783_ = lean_ctor_get(v___x_3775_, 0);
lean_dec(v_unused_3783_);
v___x_3777_ = v___x_3775_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_dec(v___x_3775_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
if (v_isShared_3778_ == 0)
{
lean_ctor_set(v___x_3777_, 0, v_a_3764_);
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3764_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
else
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3791_; 
lean_dec(v_a_3764_);
v_a_3784_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3786_ = v___x_3775_;
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v___x_3775_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_a_3784_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
}
}
else
{
size_t v___x_3792_; size_t v___x_3793_; lean_object* v___x_3344__overap_3794_; lean_object* v___x_3795_; 
v___x_3792_ = ((size_t)0ULL);
v___x_3793_ = lean_usize_of_nat(v___x_3766_);
v___x_3344__overap_3794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3751_, v___f_3752_, v_a_3765_, v___x_3792_, v___x_3793_, v___x_3769_);
v___x_3795_ = lean_apply_2(v___x_3344__overap_3794_, v___y_3756_, lean_box(0));
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3802_; 
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3802_ == 0)
{
lean_object* v_unused_3803_; 
v_unused_3803_ = lean_ctor_get(v___x_3795_, 0);
lean_dec(v_unused_3803_);
v___x_3797_ = v___x_3795_;
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
else
{
lean_dec(v___x_3795_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v___x_3800_; 
if (v_isShared_3798_ == 0)
{
lean_ctor_set(v___x_3797_, 0, v_a_3764_);
v___x_3800_ = v___x_3797_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_a_3764_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
else
{
lean_object* v_a_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3811_; 
lean_dec(v_a_3764_);
v_a_3804_ = lean_ctor_get(v___x_3795_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3806_ = v___x_3795_;
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_a_3804_);
lean_dec(v___x_3795_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3809_; 
if (v_isShared_3807_ == 0)
{
v___x_3809_ = v___x_3806_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_a_3804_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
}
}
}
else
{
lean_object* v_a_3812_; lean_object* v___x_3813_; uint8_t v___x_3814_; 
lean_dec_ref(v___f_3752_);
v_a_3812_ = lean_ctor_get(v___x_3763_, 1);
lean_inc(v_a_3812_);
lean_dec_ref(v___x_3763_);
v___x_3813_ = lean_array_get_size(v_a_3812_);
v___x_3814_ = lean_nat_dec_lt(v___x_3761_, v___x_3813_);
if (v___x_3814_ == 0)
{
lean_object* v___x_3815_; lean_object* v___x_3816_; 
lean_dec(v_a_3812_);
lean_dec_ref(v___y_3756_);
lean_dec_ref(v___f_3753_);
lean_dec_ref(v___x_3751_);
v___x_3815_ = lean_box(0);
v___x_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3815_);
return v___x_3816_;
}
else
{
lean_object* v___x_3817_; uint8_t v___x_3818_; 
v___x_3817_ = lean_box(0);
v___x_3818_ = lean_nat_dec_le(v___x_3813_, v___x_3813_);
if (v___x_3818_ == 0)
{
if (v___x_3814_ == 0)
{
lean_dec(v_a_3812_);
lean_dec_ref(v___y_3756_);
lean_dec_ref(v___f_3753_);
lean_dec_ref(v___x_3751_);
goto v___jp_3758_;
}
else
{
size_t v___x_3819_; size_t v___x_3820_; lean_object* v___x_3365__overap_3821_; lean_object* v___x_3822_; 
v___x_3819_ = ((size_t)0ULL);
v___x_3820_ = lean_usize_of_nat(v___x_3813_);
v___x_3365__overap_3821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3751_, v___f_3753_, v_a_3812_, v___x_3819_, v___x_3820_, v___x_3817_);
v___x_3822_ = lean_apply_2(v___x_3365__overap_3821_, v___y_3756_, lean_box(0));
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_dec_ref(v___x_3822_);
goto v___jp_3758_;
}
else
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3830_; 
v_a_3823_ = lean_ctor_get(v___x_3822_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3825_ = v___x_3822_;
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3822_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_a_3823_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
}
}
else
{
size_t v___x_3831_; size_t v___x_3832_; lean_object* v___x_3373__overap_3833_; lean_object* v___x_3834_; 
v___x_3831_ = ((size_t)0ULL);
v___x_3832_ = lean_usize_of_nat(v___x_3813_);
v___x_3373__overap_3833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3751_, v___f_3753_, v_a_3812_, v___x_3831_, v___x_3832_, v___x_3817_);
v___x_3834_ = lean_apply_2(v___x_3373__overap_3833_, v___y_3756_, lean_box(0));
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_dec_ref(v___x_3834_);
goto v___jp_3758_;
}
else
{
lean_object* v_a_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3842_; 
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3837_ = v___x_3834_;
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_a_3835_);
lean_dec(v___x_3834_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3840_; 
if (v_isShared_3838_ == 0)
{
v___x_3840_ = v___x_3837_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_a_3835_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
}
}
}
v___jp_3758_:
{
lean_object* v___x_3759_; lean_object* v___x_3760_; 
v___x_3759_ = lean_box(0);
v___x_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3759_);
return v___x_3760_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_instMonadLiftLogIO___lam__2___boxed(lean_object* v___x_3843_, lean_object* v___f_3844_, lean_object* v___f_3845_, lean_object* v_00_u03b1_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
lean_object* v_res_3850_; 
v_res_3850_ = l_Lake_LoggerIO_instMonadLiftLogIO___lam__2(v___x_3843_, v___f_3844_, v___f_3845_, v_00_u03b1_3846_, v___y_3847_, v___y_3848_);
return v_res_3850_;
}
}
static lean_object* _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__1(void){
_start:
{
lean_object* v___x_3852_; 
v___x_3852_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_3852_;
}
}
static lean_object* _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__2(void){
_start:
{
lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3853_ = lean_obj_once(&l_Lake_LoggerIO_instMonadLiftLogIO___closed__1, &l_Lake_LoggerIO_instMonadLiftLogIO___closed__1_once, _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__1);
v___x_3854_ = l_ReaderT_instMonad___redArg(v___x_3853_);
return v___x_3854_;
}
}
static lean_object* _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__3(void){
_start:
{
lean_object* v___f_3855_; lean_object* v___x_3856_; lean_object* v___f_3857_; 
v___f_3855_ = ((lean_object*)(l_Lake_LoggerIO_instMonadLiftLogIO___closed__0));
v___x_3856_ = lean_obj_once(&l_Lake_LoggerIO_instMonadLiftLogIO___closed__2, &l_Lake_LoggerIO_instMonadLiftLogIO___closed__2_once, _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__2);
v___f_3857_ = lean_alloc_closure((void*)(l_Lake_LoggerIO_instMonadLiftLogIO___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3857_, 0, v___x_3856_);
lean_closure_set(v___f_3857_, 1, v___f_3855_);
lean_closure_set(v___f_3857_, 2, v___f_3855_);
return v___f_3857_;
}
}
static lean_object* _init_l_Lake_LoggerIO_instMonadLiftLogIO(void){
_start:
{
lean_object* v___f_3858_; 
v___f_3858_ = lean_obj_once(&l_Lake_LoggerIO_instMonadLiftLogIO___closed__3, &l_Lake_LoggerIO_instMonadLiftLogIO___closed__3_once, _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__3);
return v___f_3858_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg___lam__0(lean_object* v_val_3859_, uint8_t v_outLv_3860_, uint8_t v_val_3861_, lean_object* v_e_3862_){
_start:
{
lean_object* v___x_3864_; 
v___x_3864_ = l_Lake_logToStream(v_e_3862_, v_val_3859_, v_outLv_3860_, v_val_3861_);
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg___lam__0___boxed(lean_object* v_val_3865_, lean_object* v_outLv_3866_, lean_object* v_val_3867_, lean_object* v_e_3868_, lean_object* v___y_3869_){
_start:
{
uint8_t v_outLv_boxed_3870_; uint8_t v_val_309__boxed_3871_; lean_object* v_res_3872_; 
v_outLv_boxed_3870_ = lean_unbox(v_outLv_3866_);
v_val_309__boxed_3871_ = lean_unbox(v_val_3867_);
v_res_3872_ = l_Lake_LoggerIO_toBaseIO___redArg___lam__0(v_val_3865_, v_outLv_boxed_3870_, v_val_309__boxed_3871_, v_e_3868_);
lean_dec_ref(v_e_3868_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg(lean_object* v_self_3873_, lean_object* v_cfg_3874_){
_start:
{
uint8_t v_outLv_3876_; uint8_t v_ansiMode_3877_; lean_object* v_out_3878_; lean_object* v___x_3879_; uint8_t v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___f_3883_; lean_object* v___x_3884_; 
v_outLv_3876_ = lean_ctor_get_uint8(v_cfg_3874_, sizeof(void*)*1 + 1);
v_ansiMode_3877_ = lean_ctor_get_uint8(v_cfg_3874_, sizeof(void*)*1 + 2);
v_out_3878_ = lean_ctor_get(v_cfg_3874_, 0);
v___x_3879_ = l_Lake_OutStream_get(v_out_3878_);
lean_inc_ref(v___x_3879_);
v___x_3880_ = l_Lake_AnsiMode_isEnabled(v___x_3879_, v_ansiMode_3877_);
v___x_3881_ = lean_box(v_outLv_3876_);
v___x_3882_ = lean_box(v___x_3880_);
v___f_3883_ = lean_alloc_closure((void*)(l_Lake_LoggerIO_toBaseIO___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3883_, 0, v___x_3879_);
lean_closure_set(v___f_3883_, 1, v___x_3881_);
lean_closure_set(v___f_3883_, 2, v___x_3882_);
v___x_3884_ = lean_apply_2(v_self_3873_, v___f_3883_, lean_box(0));
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3892_; 
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3887_ = v___x_3884_;
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v___x_3884_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3890_; 
if (v_isShared_3888_ == 0)
{
lean_ctor_set_tag(v___x_3887_, 1);
v___x_3890_ = v___x_3887_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_a_3885_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
return v___x_3890_;
}
}
}
else
{
lean_object* v___x_3893_; 
lean_dec_ref(v___x_3884_);
v___x_3893_ = lean_box(0);
return v___x_3893_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg___boxed(lean_object* v_self_3894_, lean_object* v_cfg_3895_, lean_object* v_a_3896_){
_start:
{
lean_object* v_res_3897_; 
v_res_3897_ = l_Lake_LoggerIO_toBaseIO___redArg(v_self_3894_, v_cfg_3895_);
lean_dec_ref(v_cfg_3895_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO(lean_object* v_00_u03b1_3898_, lean_object* v_self_3899_, lean_object* v_cfg_3900_){
_start:
{
uint8_t v_outLv_3902_; uint8_t v_ansiMode_3903_; lean_object* v_out_3904_; lean_object* v___x_3905_; uint8_t v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___f_3909_; lean_object* v___x_3910_; 
v_outLv_3902_ = lean_ctor_get_uint8(v_cfg_3900_, sizeof(void*)*1 + 1);
v_ansiMode_3903_ = lean_ctor_get_uint8(v_cfg_3900_, sizeof(void*)*1 + 2);
v_out_3904_ = lean_ctor_get(v_cfg_3900_, 0);
v___x_3905_ = l_Lake_OutStream_get(v_out_3904_);
lean_inc_ref(v___x_3905_);
v___x_3906_ = l_Lake_AnsiMode_isEnabled(v___x_3905_, v_ansiMode_3903_);
v___x_3907_ = lean_box(v_outLv_3902_);
v___x_3908_ = lean_box(v___x_3906_);
v___f_3909_ = lean_alloc_closure((void*)(l_Lake_LoggerIO_toBaseIO___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3909_, 0, v___x_3905_);
lean_closure_set(v___f_3909_, 1, v___x_3907_);
lean_closure_set(v___f_3909_, 2, v___x_3908_);
v___x_3910_ = lean_apply_2(v_self_3899_, v___f_3909_, lean_box(0));
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3918_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3918_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3918_ == 0)
{
v___x_3913_ = v___x_3910_;
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___x_3910_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v___x_3916_; 
if (v_isShared_3914_ == 0)
{
lean_ctor_set_tag(v___x_3913_, 1);
v___x_3916_ = v___x_3913_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_a_3911_);
v___x_3916_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
return v___x_3916_;
}
}
}
else
{
lean_object* v___x_3919_; 
lean_dec_ref(v___x_3910_);
v___x_3919_ = lean_box(0);
return v___x_3919_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___boxed(lean_object* v_00_u03b1_3920_, lean_object* v_self_3921_, lean_object* v_cfg_3922_, lean_object* v_a_3923_){
_start:
{
lean_object* v_res_3924_; 
v_res_3924_ = l_Lake_LoggerIO_toBaseIO(v_00_u03b1_3920_, v_self_3921_, v_cfg_3922_);
lean_dec_ref(v_cfg_3922_);
return v_res_3924_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg___lam__0(lean_object* v_val_3925_, lean_object* v_e_3926_){
_start:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
v___x_3928_ = lean_st_ref_take(v_val_3925_);
v___x_3929_ = lean_array_push(v___x_3928_, v_e_3926_);
v___x_3930_ = lean_st_ref_set(v_val_3925_, v___x_3929_);
return v___x_3930_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg___lam__0___boxed(lean_object* v_val_3931_, lean_object* v_e_3932_, lean_object* v___y_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l_Lake_LoggerIO_captureLog___redArg___lam__0(v_val_3931_, v_e_3932_);
lean_dec(v_val_3931_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg(lean_object* v_self_3935_){
_start:
{
lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v_val_3944_; lean_object* v___f_3955_; lean_object* v___x_3956_; 
v___x_3941_ = ((lean_object*)(l_Lake_Log_empty___closed__0));
v___x_3942_ = lean_st_mk_ref(v___x_3941_);
lean_inc(v___x_3942_);
v___f_3955_ = lean_alloc_closure((void*)(l_Lake_LoggerIO_captureLog___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3955_, 0, v___x_3942_);
v___x_3956_ = lean_apply_2(v_self_3935_, v___f_3955_, lean_box(0));
if (lean_obj_tag(v___x_3956_) == 0)
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3964_; 
v_a_3957_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3959_ = v___x_3956_;
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3956_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3962_; 
if (v_isShared_3960_ == 0)
{
lean_ctor_set_tag(v___x_3959_, 1);
v___x_3962_ = v___x_3959_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_a_3957_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
v_val_3944_ = v___x_3962_;
goto v___jp_3943_;
}
}
}
else
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3972_; 
v_a_3965_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3967_ = v___x_3956_;
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3956_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
if (v_isShared_3968_ == 0)
{
lean_ctor_set_tag(v___x_3967_, 0);
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
v___x_3970_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
v_val_3944_ = v___x_3970_;
goto v___jp_3943_;
}
}
}
v___jp_3937_:
{
lean_object* v___x_3940_; 
v___x_3940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3940_, 0, v___y_3939_);
lean_ctor_set(v___x_3940_, 1, v___y_3938_);
return v___x_3940_;
}
v___jp_3943_:
{
lean_object* v___x_3945_; 
v___x_3945_ = lean_st_ref_get(v___x_3942_);
lean_dec(v___x_3942_);
if (lean_obj_tag(v_val_3944_) == 0)
{
lean_object* v___x_3946_; 
lean_dec_ref(v_val_3944_);
v___x_3946_ = lean_box(0);
v___y_3938_ = v___x_3945_;
v___y_3939_ = v___x_3946_;
goto v___jp_3937_;
}
else
{
lean_object* v_a_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3954_; 
v_a_3947_ = lean_ctor_get(v_val_3944_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v_val_3944_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3949_ = v_val_3944_;
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_a_3947_);
lean_dec(v_val_3944_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3952_; 
if (v_isShared_3950_ == 0)
{
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
v___y_3938_ = v___x_3945_;
v___y_3939_ = v___x_3952_;
goto v___jp_3937_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg___boxed(lean_object* v_self_3973_, lean_object* v_a_3974_){
_start:
{
lean_object* v_res_3975_; 
v_res_3975_ = l_Lake_LoggerIO_captureLog___redArg(v_self_3973_);
return v_res_3975_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog(lean_object* v_00_u03b1_3976_, lean_object* v_self_3977_){
_start:
{
lean_object* v___x_3979_; 
v___x_3979_ = l_Lake_LoggerIO_captureLog___redArg(v_self_3977_);
return v___x_3979_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___boxed(lean_object* v_00_u03b1_3980_, lean_object* v_self_3981_, lean_object* v_a_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l_Lake_LoggerIO_captureLog(v_00_u03b1_3980_, v_self_3981_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f___redArg(lean_object* v_self_3984_){
_start:
{
lean_object* v___x_3986_; 
v___x_3986_ = l_Lake_LoggerIO_captureLog___redArg(v_self_3984_);
return v___x_3986_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f___redArg___boxed(lean_object* v_self_3987_, lean_object* v_a_3988_){
_start:
{
lean_object* v_res_3989_; 
v_res_3989_ = l_Lake_LoggerIO_run_x3f___redArg(v_self_3987_);
return v_res_3989_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f(lean_object* v_00_u03b1_3990_, lean_object* v_self_3991_){
_start:
{
lean_object* v___x_3993_; 
v___x_3993_ = l_Lake_LoggerIO_captureLog___redArg(v_self_3991_);
return v___x_3993_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f___boxed(lean_object* v_00_u03b1_3994_, lean_object* v_self_3995_, lean_object* v_a_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l_Lake_LoggerIO_run_x3f(v_00_u03b1_3994_, v_self_3995_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27___redArg(lean_object* v_self_3998_, lean_object* v_logger_3999_){
_start:
{
lean_object* v___x_4001_; 
v___x_4001_ = lean_apply_2(v_self_3998_, v_logger_3999_, lean_box(0));
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4009_; 
v_a_4002_ = lean_ctor_get(v___x_4001_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4004_ = v___x_4001_;
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_4001_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
lean_ctor_set_tag(v___x_4004_, 1);
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_a_4002_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
else
{
lean_object* v___x_4010_; 
lean_dec_ref(v___x_4001_);
v___x_4010_ = lean_box(0);
return v___x_4010_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27___redArg___boxed(lean_object* v_self_4011_, lean_object* v_logger_4012_, lean_object* v_a_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l_Lake_LoggerIO_run_x3f_x27___redArg(v_self_4011_, v_logger_4012_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27(lean_object* v_00_u03b1_4015_, lean_object* v_self_4016_, lean_object* v_logger_4017_){
_start:
{
lean_object* v___x_4019_; 
v___x_4019_ = lean_apply_2(v_self_4016_, v_logger_4017_, lean_box(0));
if (lean_obj_tag(v___x_4019_) == 0)
{
lean_object* v_a_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4027_; 
v_a_4020_ = lean_ctor_get(v___x_4019_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_4019_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4022_ = v___x_4019_;
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_a_4020_);
lean_dec(v___x_4019_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4025_; 
if (v_isShared_4023_ == 0)
{
lean_ctor_set_tag(v___x_4022_, 1);
v___x_4025_ = v___x_4022_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_a_4020_);
v___x_4025_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
return v___x_4025_;
}
}
}
else
{
lean_object* v___x_4028_; 
lean_dec_ref(v___x_4019_);
v___x_4028_ = lean_box(0);
return v___x_4028_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27___boxed(lean_object* v_00_u03b1_4029_, lean_object* v_self_4030_, lean_object* v_logger_4031_, lean_object* v_a_4032_){
_start:
{
lean_object* v_res_4033_; 
v_res_4033_ = l_Lake_LoggerIO_run_x3f_x27(v_00_u03b1_4029_, v_self_4030_, v_logger_4031_);
return v_res_4033_;
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
